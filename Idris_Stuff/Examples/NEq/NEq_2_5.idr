import Darknet

mutual
  neq_smaller : CLang
  neq_smaller = Assert neq_smaller_assert
                  $ Halt
  
  neq_smaller_assert : Env -> Assertion
  neq_smaller_assert env = 
    let
      x = Lit 2
      y = Lit 5
      x' = eval env x
      y' = eval env y
      prf = isNEq x' y'
    in
      MkAssertion (NEq x y (MkEvald x x') (MkEvald y y') prf)

