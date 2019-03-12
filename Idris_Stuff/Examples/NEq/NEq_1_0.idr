import Darknet

mutual
  neq1_0 : CLang
  neq1_0 = Assert neq1_0_assert
            $ Halt
  
  neq1_0_assert : Env -> Assertion
  neq1_0_assert env = 
    let
      x = Lit 1
      y = Lit 0
      x' = eval env x
      y' = eval env y
      prf = isNEq x' y'
    in
      MkAssertion (NEq x y (MkEvald x x') (MkEvald y y') prf)

