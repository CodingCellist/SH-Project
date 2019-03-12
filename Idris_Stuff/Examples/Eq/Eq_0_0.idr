import Darknet

mutual
  eq_0_0 : CLang
  eq_0_0 = Assert eq_0_0_assert
          $ Halt

  eq_0_0_assert : Env -> Assertion
  eq_0_0_assert env =
    let
      x = Lit 0
      y = Lit 0
      x' = eval env x
      y' = eval env y
      prf = decEq x' y'
    in
      MkAssertion (Eq x y (MkEvald x x') (MkEvald y y') prf)

