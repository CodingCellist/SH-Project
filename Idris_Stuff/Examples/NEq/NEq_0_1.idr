import Darknet

mutual
  neq0_1 : CLang
  neq0_1 = Assert neq0_1_assert
            $ Halt
  
  neq0_1_assert : Env -> Assertion
  neq0_1_assert env = 
    let
      x = Lit 0
      y = Lit 1
      x' = eval env x
      y' = eval env y
      prf = isNEq x' y'
    in
      MkAssertion (NEq x y (MkEvald x x') (MkEvald y y') prf)

