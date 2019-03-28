import Darknet

mutual
  neq_2_5 : CLang
  neq_2_5 = Assert neq_2_5_assert
            $ Halt
  
  neq_2_5_assert : Env -> Assertion
  neq_2_5_assert env = 
    let
      x = Lit 2
      y = Lit 5
      x' = eval env x
      y' = eval env y
      prf = isNEq x' y'
    in
      MkAssertion (NEq x y (MkEvald x x') (MkEvald y y') prf)

