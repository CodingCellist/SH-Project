import Darknet

mutual
  neq_3_3 : CLang
  neq_3_3 = Assert neq_3_3_assert
            $ Halt

  neq_3_3_assert : Env -> Assertion
  neq_3_3_assert env =
    let
      x = Lit 3
      y = Lit 3
      x' = eval env x
      y' = eval env y
      prf = isNEq x' y'
    in
      MkAssertion (NEq x y (MkEvald x x') (MkEvald y y') prf)

