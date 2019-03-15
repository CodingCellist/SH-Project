import Darknet

mutual
  eq_1_0 : CLang
  eq_1_0 = Assert eq_1_0_assert
            $ Halt

  eq_1_0_assert : Env -> Assertion
  eq_1_0_assert env =
    let
      x = Lit 1
      y = Lit 0
      x' = eval env x
      y' = eval env y
      prf = decEq x' y'
    in
      MkAssertion (Eq x y (MkEvald x x') (MkEvald y y') prf)

