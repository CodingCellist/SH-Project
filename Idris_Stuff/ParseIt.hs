module ParseIt where

import Language.C
import Language.C.Data.Position
import Language.C.Data.Ident
import Data.ByteString.Char8 
import System.IO.Unsafe 
import Language.C.System.Preprocess 
import Language.C.System.GCC 
import Debug.Trace 
import Data.Either
import Data.Maybe
data Found = CLangTime (String, Int, Int) 
           | CLangEnergy (String, Int, Int)
           | Assert String 
           | None

getASTYolo :: CTranslUnit
getASTYolo = let Right res = unsafePerformIO $ parseCFile (newGCC "cc") Nothing [] "Yolo_for_teamplay/src/network.c"
             in res

getAST :: CTranslUnit
getAST = let Right res = unsafePerformIO $ parseCFile (newGCC "cc") Nothing [] "foo.c"
         in res

findStatement :: [ CStatement a ] -> [CStatement a]
findStatement [] = []
findStatement (s:statements) = Prelude.concatMap inStatement (s:statements)


inStatement :: CStatement a -> [CStatement a]
inStatement xx@(CCompound idents item x) = inBlock item
inStatement x@(CExpr _ _) = [x]
inStatement (CLabel _ s _ _) = inStatement s
inStatement (CCase expr s _) = inStatement s
inStatement (CCases _ _ s _) = inStatement s
inStatement (CDefault s _)   = inStatement s
inStatement (CIf _ s (Just s2) _) = inStatement s ++ inStatement s2
inStatement (CIf _ s Nothing _) = inStatement s
inStatement (CSwitch _ s _ ) = inStatement s
inStatement (CWhile _ s _ _) = inStatement s
inStatement (CFor _ _ _ s _) = inStatement s
inStatement (CGoto _ _) = []
inStatement (CGotoPtr _ _) = []
inStatement (CCont _)  = []
inStatement (CBreak _) = []
inStatement (CReturn _ _) = []
inStatement (CAsm _ _) = []

inBlock :: [CCompoundBlockItem a] -> [CStatement a]
inBlock [] = []
inBlock ((CBlockStmt statement):items) = inStatement statement ++ inBlock items
inBlock ((CNestedFunDef a ):items) = inFunDef a ++ inBlock items
inBlock (x:xs) = inBlock xs

inFunDef :: CFunctionDef a -> [CStatement a]
inFunDef (CFunDef _ _ _ s _) = inStatement s


getStatementsTrans :: CTranslationUnit a -> [CStatement a]
getStatementsTrans (CTranslUnit decs x) = Prelude.concatMap getStatementsExt decs

getStatementsExt :: CExternalDeclaration a -> [CStatement a]
getStatementsExt (CFDefExt a)  = [getStatementsFunDef a]
getStatementsExt _ = []

getStatementsFunDef :: CFunctionDef a -> CStatement a
getStatementsFunDef (CFunDef declspecs declarator declarations statement x) = statement

-- findTeamplayElements :: [ CStatement a ] -> [ (String, Int, Int) ]
findTeamplayElements [] = []
findTeamplayElements ((CExpr x y):stmts) = case inExpr (CExpr x y) of
						None -> findTeamplayElements stmts
						CLangTime x  -> printIdris (CLangTime x) ++ findTeamplayElements stmts
						CLangEnergy x -> printIdris (CLangEnergy x) ++ findTeamplayElements stmts
						Assert x -> "Assert darknet_assert $ Halt \n" ++ generateAssertion x  
findTeamplayElements (_:stmts) = findTeamplayElements stmts


inExpr :: (Show a) => CStatement a -> Found
inExpr x@(CExpr (Just (CCall (CVar (Ident "__teamplay_time" _ _) _ ) (l:ls) _)) _ ) = CLangTime $ getArgs (l:ls)
inExpr x@(CExpr (Just (CCall (CVar (Ident "__teamplay_energy" _ _) _ ) (l:ls) _)) _ ) = CLangEnergy $ getArgs (l:ls)
inExpr x@(CExpr (Just (CCall (CVar (Ident "__teamplay_worst_time" _ _) _ ) (l:ls) _)) _ ) = CLangTime $ getArgs (l:ls)
inExpr x@(CExpr (Just (CCall (CVar (Ident "__teamplay_worst_energy" _ _) _) (l:ls) _)) _) = CLangEnergy $ getArgs (l:ls)
inExpr x@(CExpr (Just (CCall (CVar (Ident "__teamplay_assert" _ _) _ ) [l] _)) _ ) = Assert $ parseExpr l 0
inExpr _ = None

getArgs ((CVar (Ident name _ _) _):(CConst (CIntConst x _)):(CConst (CIntConst y _)):[]) = (show name, read $ show x, read $ show y)
getArgs x = error (show x)


{- darknet_assert : Env -> Assertion
darknet_assert env = 
    let loop_cost      = (Var "loop_cost")
        fill_cpu_time  = (Var "fill_cpu_time")
        forward_time   = (Var "forward_time")
        netn           = (Var "net.n")
        worst          = (Mul (Plus fill_cpu_time forward_time) netn)
        loop_cost'     = eval env loop_cost
        worst'         = eval env worst
    in MkAssertion (LTE loop_cost worst (MkEvald loop_cost loop_cost') (MkEvald worst worst') (isLTE loop_cost' worst'))
-}

generateAssertion expr = "\n\n\tdarknet_assert : Env -> Assertion\n\tdarknet_assert env = " ++ expr

parseExpr (CBinary CEqOp e1 e2 _) count =  let p1 = "p" ++ (show count)
                                               p2 = "p" ++ (show (count + 1))
                                               p1' = p1 ++ "'"
                                               p2' = p2 ++ "'"
                                               branch1 = "\t\t " ++ p1 ++ " = " ++ parseExpr e1 (count+2) ++ "\n"
                                               branch2 = "\t\t " ++ p2  ++ " = " ++ parseExpr e2 (count +50)  ++ "\n"
                                               branch1' ="\t\t " ++ p1' ++ " = eval env " ++ p1 ++ "\n"
                                               branch2' ="\t\t " ++ p2' ++ " = eval env " ++ p2 ++ "\n"
                                           in "\n\t\tlet\n" ++ branch1 ++ branch2 ++ branch1' ++ branch2' ++ "\n\t\tin MkAssertion (Eq " ++ p1 ++ " " ++ p2 ++ " (MkEvald " ++ p1 ++ " " ++ p1' ++ ") " ++ "(MkEvald " ++ p2 ++ " " ++ p2' ++ ") " ++ "(Refl ))"



parseExpr (CBinary CGrOp e1 e2 _) count =  let p1 = "p" ++ (show count)
                                               p2 = "p" ++ (show (count + 1))
                                               p1' = p1 ++ "'"
                                               p2' = p2 ++ "'"
                                               branch1 = "\t\t " ++ p1 ++ " = " ++ parseExpr e1 (count+2) ++ "\n"
                                               branch2 = "\t\t " ++ p2  ++ " = " ++ parseExpr e2 (count +50)  ++ "\n"
                                               branch1' ="\t\t " ++ p1' ++ " = eval env " ++ p1 ++ "\n"
                                               branch2' ="\t\t " ++ p2' ++ " = eval env " ++ p2 ++ "\n"
                                           in "\n\t\tlet\n" ++ branch1 ++ branch2 ++ branch1' ++ branch2' ++ "\n\t\tin MkAssertion (GT " ++ p1 ++ " " ++ p2 ++ " (MkEvald " ++ p1 ++ " " ++ p1' ++ ") " ++ "(MkEvald " ++ p2 ++ " " ++ p2' ++ ") " ++ "(isLTE " ++ "(S " ++ p2' ++ " )"  ++ " " ++ p1' ++ " ))"

parseExpr (CBinary CGeqOp e1 e2 _) count =  let p1 = "p" ++ (show count)
                                                p2 = "p" ++ (show (count + 1))
                                                p1' = p1 ++ "'"
                                                p2' = p2 ++ "'"
                                                branch1 = "\t\t " ++ p1 ++ " = " ++ parseExpr e1 (count+2) ++ "\n"
                                                branch2 = "\t\t " ++ p2  ++ " = " ++ parseExpr e2 (count +50)  ++ "\n"
                                                branch1' ="\t\t " ++ p1' ++ " = eval env " ++ p1 ++ "\n"
                                                branch2' ="\t\t " ++ p2' ++ " = eval env " ++ p2 ++ "\n"
                                            in "\n\t\tlet\n" ++ branch1 ++ branch2 ++ branch1' ++ branch2' ++ "\n\t\tin MkAssertion (GTE " ++ p1 ++ " " ++ p2 ++ " (MkEvald " ++ p1 ++ " " ++ p1' ++ ") " ++ "(MkEvald " ++ p2 ++ " " ++ p2' ++ ") " ++ "(isLTE " ++ p2' ++ " " ++ p1' ++ " ))"


parseExpr (CBinary CLeOp e1 e2 _) count = let p1 = "p" ++ (show count)
                                              p2 = "p" ++ (show (count + 1))
                                              p1' = p1 ++ "'"
                                              p2' = p2 ++ "'"
                                              branch1 = "\t\t " ++ p1 ++ " = " ++ parseExpr e1 (count+2) ++ "\n"
                                              branch2 = "\t\t " ++ p2  ++ " = " ++ parseExpr e2 (count +50)  ++ "\n"
                                              branch1' ="\t\t " ++ p1' ++ " = eval env " ++ p1 ++ "\n"
                                              branch2' ="\t\t " ++ p2' ++ " = eval env " ++ p2 ++ "\n"
                                          in "\n\t\tlet\n" ++ branch1 ++ branch2 ++ branch1' ++ branch2' ++ "\n\t\tin MkAssertion (LT " ++ p1 ++ " " ++ p2 ++ " (MkEvald " ++ p1 ++ " " ++ p1' ++ ") " ++ "(MkEvald " ++ p2 ++ " " ++ p2' ++ ") " ++ "(isLTE " ++ "(S " ++ p1' ++ " )" ++ " " ++ p2' ++ " ))"

parseExpr (CBinary CLeqOp e1 e2 _) count = let p1 = "p" ++ (show count)
					       p2 = "p" ++ (show (count + 1))
 					       p1' = p1 ++ "'"
					       p2' = p2 ++ "'"
                                               branch1 = "\t\t " ++ p1 ++ " = " ++ parseExpr e1 (count+2) ++ "\n" 
					       branch2 = "\t\t " ++ p2  ++ " = " ++ parseExpr e2 (count +50)  ++ "\n"
					       branch1' ="\t\t " ++ p1' ++ " = eval env " ++ p1 ++ "\n"
					       branch2' ="\t\t " ++ p2' ++ " = eval env " ++ p2 ++ "\n"
				           in "\n\t\tlet\n" ++ branch1 ++ branch2 ++ branch1' ++ branch2' ++ "\n\t\tin MkAssertion (LTE " ++ p1 ++ " " ++ p2 ++ " (MkEvald " ++ p1 ++ " " ++ p1' ++ ") " ++ "(MkEvald " ++ p2 ++ " " ++ p2' ++ ") " ++ "(isLTE " ++ p1' ++ " " ++ p2' ++ " ))"

parseExpr (CBinary CMulOp e1 e2 _) count = "( Mul " ++ parseExpr e1 count ++ parseExpr e2 (count+20) ++ " ) " 
parseExpr (CBinary CAddOp e1 e2 _) count = "( Plus " ++ parseExpr e1 count  ++ parseExpr e2 (count+20)  ++ " ) "
parseExpr (CVar (Ident name _ _) _) count = "(Var " ++ show name ++ ") " 
parseExpr (CConst (CIntConst x _) ) count = "( Lit " ++ show x ++ " ) " 
parseExpr x _ = error (show x)

-- fact_darknet : CLang
-- fact_darknet =  DecVar "net.n" 107 $
--                Block "loop_cost" 303 $
--                For 0 107 (
--                            Block "fill_cpu_time" 1 $
--                            Stmt "forward_time" 8 Halt ) $
--                Assert darknet_assert $ Halt

generateIdris name str = "import Darknet\n\n\nmutual" ++ "\n\t" ++ name ++ " : CLang \n\t" ++ name ++ " = "  ++ str

printIdris (CLangTime (name, x, y)) = "BlockTime " ++ name ++ " " ++ show x ++ " $ " 
printIdris (CLangEnergy (name, x, y)) = "BlockEnergy " ++ name ++ " " ++ show x ++ " $ "




