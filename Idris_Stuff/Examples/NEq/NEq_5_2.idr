import Darknet

mutual
  neq_5_2 : CLang
  neq_5_2 = Assert neq_5_2_assert
                $ Halt
  
  neq_5_2_assert : Env -> Assertion
  neq_5_2_assert env = 
    let
      x = Lit 5
      y = Lit 2
      x' = eval env x
      y' = eval env y
      prf = isNEq x' y'
    in
      MkAssertion (NEq x y (MkEvald x x') (MkEvald y y') prf)

