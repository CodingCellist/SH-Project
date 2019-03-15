import Darknet

mutual
  eq_true : CLang
  eq_true = Assert eq_true_assert
            $ Halt

  eq_true_assert : Env -> Assertion
  eq_true_assert env =
    let
      x = Lit 3
      y = Lit 3
      x' = eval env x
      y' = eval env y
      prf = decEq x' y'
    in
      MkAssertion (Eq x y (MkEvald x x') (MkEvald y y') prf)

