import Darknet

mutual
  eq_1_3 : CLang
  eq_1_3 = Assert eq_1_3_assert
           $ Halt

  eq_1_3_assert : Env -> Assertion
  eq_1_3_assert env =
    let
      x = Lit 1
      y = Lit 3
      x' = eval env x
      y' = eval env y
      prf = decEq x' y'
    in
      MkAssertion (Eq x y (MkEvald x x') (MkEvald y y') prf)

