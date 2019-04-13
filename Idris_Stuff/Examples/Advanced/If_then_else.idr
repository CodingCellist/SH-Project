module Examples.Advanced.If_then_else

import Darknet

mutual
  if_then_else : CLang
  if_then_else = BlockEnergy "b1" 2
                 $ BlockEnergy "b2" 5
                 $ Assert if_then_else_assert
                 $ Halt

  if_then_else_assert : Env -> Assertion
  if_then_else_assert env =
    let
      p0 = Var "b1"
      p1 = Var "b2"
      p0' = eval env p0
      p1' = eval env p1
      prf = decEq p0' p1'
    in
      MkAssertion (Eq p0 p1 (MkEvald p0 p0') (MkEvald p1 p1') prf)

