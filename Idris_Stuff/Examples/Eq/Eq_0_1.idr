import Darknet

mutual
  eq_0_1 : CLang
  eq_0_1 = Assert eq_0_1_assert
            $ Halt

  eq_0_1_assert : Env -> Assertion
  eq_0_1_assert env =
    let
      x = Lit 0
      y = Lit 1
      x' = eval env x
      y' = eval env y
      prf = decEq x' y'
    in
      MkAssertion (Eq x y (MkEvald x x') (MkEvald y y') prf)

