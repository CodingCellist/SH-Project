import Darknet

mutual
  eq_3_3 : CLang
  eq_3_3 = Assert eq_3_3_assert
           $ Halt

  eq_3_3_assert : Env -> Assertion
  eq_3_3_assert env =
    let
      x = Lit 3
      y = Lit 3
      x' = eval env x
      y' = eval env y
      prf = decEq x' y'
    in
      MkAssertion (Eq x y (MkEvald x x') (MkEvald y y') prf)

