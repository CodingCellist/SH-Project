import Darknet

mutual
  neq_larger : CLang
  neq_larger = Assert neq_larger_assert
                $ Halt
  
  neq_larger_assert : Env -> Assertion
  neq_larger_assert env = 
    let
      x = Lit 5
      y = Lit 2
      x' = eval env x
      y' = eval env y
      prf = isNEq x' y'
    in
      MkAssertion (NEq x y (MkEvald x x') (MkEvald y y') prf)

