import Darknet

mutual
  neq_0_0 : CLang
  neq_0_0 = Assert neq_0_0_assert
            $ Halt

  neq_0_0_assert : Env -> Assertion
  neq_0_0_assert env =
    let
      x = Lit 0
      y = Lit 0
      x' = eval env x
      y' = eval env y
      prf = isNEq x' y'
    in
      MkAssertion (NEq x y (MkEvald x x') (MkEvald y y') prf)

