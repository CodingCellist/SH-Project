import Darknet

mutual
  neq_false : CLang
  neq_false = Assert neq_false_assert
              $ Halt

  neq_false_assert : Env -> Assertion
  neq_false_assert env =
    let
      x = Lit 3
      y = Lit 3
      x' = eval env x
      y' = eval env y
      prf = isNEq x' y'
    in
      MkAssertion (NEq x y (MkEvald x x') (MkEvald y y') prf)

