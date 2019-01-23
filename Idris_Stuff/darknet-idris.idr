module Darknet

public export


{-

__teamplay_time("loop_cost");
for(i = 0; i < net.n; ++i){
        net.index = i;
        layer l = net.layers[i];
        if(l.delta){            
            __teamplay_worst_time("fill_cpu_time", net.n);
            fill_cpu(l.outputs * l.batch, 0, l.delta, 1);
        }
 
        __teamplay_worst_time("forward_time", net.n);
        l.forward(l, net);

        net.input = l.output;
        if(l.truth) {
            net.truth = l.output;
        }
    }

__teamplay_assert(loop_cost <= (fill_cpu_time + forward_time) * net.n);

// assume loop_cost = 12.158989
// fill_cpu_time    = 0.003713
// forward_time     = 0.325609
// net.n            = 107

}

-}

-- Envorinments are lists of dependent tuples of C type and a name/value pairs
Env : Type
Env = List (String, Nat)

data NumericExpression : Type where
    Lit    : (cost : Nat) -> NumericExpression -- assume normalisation 
    Var    : (name : String) -> NumericExpression
    NParen : NumericExpression -> NumericExpression
    Plus   : NumericExpression -> NumericExpression -> NumericExpression
    Sub    : NumericExpression -> NumericExpression -> NumericExpression
    Mul    : NumericExpression -> NumericExpression -> NumericExpression
    Div    : NumericExpression -> NumericExpression -> NumericExpression
    Mod    : NumericExpression -> NumericExpression -> NumericExpression

eval : Env -> NumericExpression -> Nat 
eval env (Lit Z) = Z
eval env (Lit (S cost)) = S cost
eval env (Var name) = case lookup name env of
                        Just value => value 
                        Nothing    => 0
eval env (NParen x) = eval env x
eval env (Plus x y) = (eval env x) `plus` (eval env y)
eval env (Sub x y) = (eval env x) `minus` (eval env y)
eval env (Mul x y) = (eval env x) `mult` (eval env y)
eval env (Div x y) = assert_total $ (eval env x) `div` (eval env y)
eval env (Mod x y) = assert_total $ (eval env x) `mod` (eval env y)

data Evald : NumericExpression -> Nat -> Type where
    MkEvald : (x : NumericExpression) -> (y : Nat) -> Evald x y


data BooleanExpression : Type where
    BParen : BooleanExpression -> BooleanExpression
    Not    : BooleanExpression -> BooleanExpression
    And    : BooleanExpression -> BooleanExpression -> BooleanExpression
    Or     : BooleanExpression -> BooleanExpression -> BooleanExpression

    Eq     : (x : NumericExpression) 
          -> (y : NumericExpression)
          -> Evald x x'
          -> Evald y y'
          -> (x' = y') 
          -> BooleanExpression


    NEq    : (x : NumericExpression) -> (y : NumericExpression) -> (x = y -> Void) -> BooleanExpression
    LT     : NumericExpression -> NumericExpression -> BooleanExpression

    LTE    :  {x' : Nat} -> {y' : Nat}
           -> (x : NumericExpression)
           -> (y : NumericExpression)
           -> Evald x x'
           -> Evald y y'
           -> Dec (x' `LTE` y')
           -> BooleanExpression
    
    GT     : NumericExpression -> NumericExpression -> BooleanExpression

    GTE    : {x' : Nat} -> {y' : Nat} 
           -> (x : NumericExpression) 
           -> (y : NumericExpression) 
           -> Evald x x' 
           -> Evald y y' 
           -> Dec (y' `LTE` x') 
           -> BooleanExpression

data Assertion : Type where
    MkAssertion    : BooleanExpression -> Assertion

-- fact_assert : Pred
-- fact_assert = EQ (Var "fact_cost") (Mul (Var "iter_cost") (Var "x"))

-- mkEq : (x : NumericExpression) -> (y : NumericExpression) -> (x = y) -> BooleanExpression
-- mkEq x y prf = Eq x y prf

-- prfHole : (x = y) -> Label x = Label y
-- prfHole Refl = Refl

-- proveLabel : (x = y) -> eval (Lit x) = eval (Lit y)
-- proveLabel Refl = Refl

impossibleSuccK : (S k = k) -> Void
impossibleSuccK Refl impossible

impossibleKSucc : (k = S k) -> Void
impossibleKSucc Refl impossible

impossibleZSucc : (0 = S k) -> Void
impossibleZSucc Refl impossible

impossibleSuccZ : (S k = 0) -> Void
impossibleSuccZ Refl impossible

contraSuccInjective : (x : Nat) -> (y : Nat) -> (contra : (x = y) -> Void) -> (S x = S y) -> Void
contraSuccInjective x y contra prf = contra $ succInjective x y prf

twoAreTheSame : (x : Nat) -> (y : Nat) -> Dec (x = y)
twoAreTheSame Z Z =  Yes Refl
twoAreTheSame Z (S k) =  No impossibleZSucc
twoAreTheSame (S k) Z  = No impossibleSuccZ
twoAreTheSame (S k) (S y) = case twoAreTheSame k y of
                                Yes Refl => Yes Refl
                                No contra => No (contraSuccInjective k y contra)


congGTE : {f : Nat -> Nat} -> (y : Nat) -> (x : Nat) -> (hell : GTE x y) -> (f y = y) -> (f x = x) -> LTE (f y) (f x)
congGTE y x hell Refl Refl  = hell

liftGTE : {f : Nat -> Nat} -> (x : Nat) -> (prf : GTE x y) -> Dec (f y = y)
liftGTE {f} x {y} prf = twoAreTheSame (f y) y

liftGTE2 : {f : Nat -> Nat} -> (x : Nat) -> Dec (f x = x)
liftGTE2 {f} x = twoAreTheSame (f x) x

{- proveGTE : (GTE x y) -> GTE (eval (Label x)) (eval (Label y))
proveGTE {y} {x} prfGTE = case (liftGTE {f = eval . Label} x prfGTE) of
                            Yes prf => case liftGTE2 {f = eval . Label} x of
                                            Yes prf2 => congGTE {f = (eval . Label)} y x prfGTE prf prf2
                                            No contra => ?here2
                            No contra => ?here
                            -}




--let res = case liftGTE x prf of
--                                   Yes prf2 => ?hole
--                       in  congGTE {f= (eval . Label)} y x prf res ?h2

-- congGTE {f= (eval . Label)} y x hell (liftGTE x hell) ?h2


fact_assert : Env -> Assertion
fact_assert env = let x = (Lit 8)
                      y = (Lit 8)
                      x' = eval [] x
                      y' = eval [] y
                  in MkAssertion (Eq x y (MkEvald x x') (MkEvald y y') ( Refl))


fact_assert_gte : Env -> Assertion
fact_assert_gte env =
    let x = (Lit 8)
        y = (Lit 7)
        x' = eval [] x
        y' = eval [] y
    in MkAssertion (GTE x y (MkEvald x x') 
                            (MkEvald y y')
                            (isLTE y' x') )




{-
        __teamplay_assert(loop_cost <= (fill_cpu_time + forward_time) * net.n);

        // assume loop_cost = 12.158989
        // fill_cpu_time    = 0.003713
        // forward_time     = 0.325609
        // net.n            = 107

        121.58989
        // fill_cpu_time    = 0003.713
        // forward_time     = 0325.609
        // net.n            = 107
-}

{- we model the C only on the parts that we need to model, blocks, statements, and loops. 
   the blocks and statements can be treat as a black box. -}


-- C statements
{- data CStmt : Type where
  Decl : (t : CTy) -> CVarDecl t -> CStmt -> CStmt
  For  : (t : CTy)
     -> CVarDecl t
     -> (pred : CExp CBool)
     -> (update : CExp t)
     -> (body : CStmt)
     -> (cont : CStmt)
     -> CStmt
  Assign : Name t -> CExp t -> CStmt -> CStmt
  Halt   : CStmt
  Assert : Pred -> CStmt -> CStmt


data Prog : Type -> State -> State -> Type where
	DecVar : (name : String) -> (val : Maybe Nat) -> Prog () st (addVal name val st)
	For    : (init : Nat) -> (bound : Nat) -> (bl : Prog () st1 st2) -> Prog () st1 st2
	BaVar  : (name : String) -> (cst : Nat) -> Prog () st (addVal name (Just val) st)
	BlVar  : (name : String) -> (cst : Nat) -> (bl : Prog () (addVal name (Just val) st0) st2) -> Prog () st0 st2
    Assert : Pred -> Prog () st st
-}

data Cost : Type where
    MkCost : Nat -> Cost

data CLang : Type where
    DecVar : (name : String) -> Nat -> CLang -> CLang
    Block : (name : String) -> Nat -> CLang -> CLang
    Stmt  : (name : String) -> Nat -> CLang -> CLang -- do we need a seperation between a block and a statement?
    For   : (init : Nat) -> (bound : Nat) -> (bl : CLang ) -> CLang -> CLang
    Assert : (Env -> Assertion) -> CLang -> CLang
    Halt   : CLang

{- fact_eg : Prog () [] [("iter_cost", Just 1), ("fact_cost", Just 8), ("x", Nothing)]
fact_eg = do
	DecVar "x" Nothing
	BlVar "fact_cost" 8 (For 1 8 (BaVar "iter_cost" 1))
    Assert fact_assert
-}

fact_eq : CLang
fact_eq = DecVar "x" 8 $
          Block "fact_cost" 8 $
          For 1 8 (Stmt "iter_cost" 1 Halt) $
          Assert fact_assert $ Halt

fact_gte : CLang
fact_gte = DecVar "x" 8 $
          Block "fact_cost" 8 $
          For 1 8 (Stmt "iter_cost" 1 Halt) $
          Assert fact_assert_gte  $ Halt

fact_assert_gte2 : Env -> Assertion
fact_assert_gte2 env =
              let x = (Var "fact_cost")
                  y = (Var "x")
                  x' = eval env x
                  y' = eval env y
              in MkAssertion (GTE x y (MkEvald x x') 
                                      (MkEvald y y')
                                      (isLTE y' x') )

fact_gte2 : CLang
fact_gte2 = DecVar "x" 7 $
            Block "fact_cost" 8 $
            For 1 8 (Stmt "iter_cost" 1 Halt) $
            Assert fact_assert_gte2  $ Halt

{-
__teamplay_time("loop_cost");
for(i = 0; i < net.n; ++i){
        net.index = i;
        layer l = net.layers[i];
        if(l.delta){            
            __teamplay_worst_time("fill_cpu_time", net.n);
            fill_cpu(l.outputs * l.batch, 0, l.delta, 1);
        }
 
        __teamplay_worst_time("forward_time", net.n);
        l.forward(l, net);

        net.input = l.output;
        if(l.truth) {
            net.truth = l.output;
        }
    }

// assume loop_cost = 12.158989
// fill_cpu_time    = 0.003713
// forward_time     = 0.325609
// net.n            = 107
-}

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


fact_darknet : CLang
fact_darknet =  DecVar "net.n" 107 $
                Block "loop_cost" 303 $
                For 0 107 (
                            Block "fill_cpu_time" 1 $
                            Stmt "forward_time" 8 Halt ) $
Assert darknet_assert $ Halt -}

-- fact_assert : Assertion
-- fact_assert = MkAssertion (Eq (Label 8) (Label 8) ( proveLabel Refl ))

-- store a variable and a cost in the environment
store : Env -> (String, Nat) -> Env
store env (name, cost) = (name, cost) :: env

-- for now, as assertions are "correct by construction", the certificate is the assertion

mkCertificate' : CLang -> (Env, List Assertion) -> (Env, List Assertion)
mkCertificate' (DecVar name y z) (env, a) = mkCertificate' z ( store env (name, y), a)
mkCertificate' (Block name y z) (env, a) = mkCertificate'  z (store env (name, y), a)
mkCertificate' (Stmt name y z) (env, a) = mkCertificate'  z (store env (name, y), a)
mkCertificate' (For init bound bl y) (env, a) = 
                            let (env', innerAsserts) = mkCertificate' bl (env, a) 
                            in mkCertificate' y (env', innerAsserts ++ a)
mkCertificate' (Assert y z) (env, a) = let res = y env in  mkCertificate' z (env, res :: a)
mkCertificate' Halt (env, a)  = (env, a) 

mkCertificate : CLang -> (Env, List Assertion)
mkCertificate arg = mkCertificate' arg ([], [])
