import Darknet

mutual
  eq_false : CLang
  eq_false = Assert eq_false_assert
              $ Halt

  eq_false_assert : Env -> Assertion
  eq_false_assert env =
    let
      x = Lit 3
      y = Lit 1
      x' = eval env x
      y' = eval env y
      prf = decEq x' y'
    in
      MkAssertion (Eq x y (MkEvald x x') (MkEvald y y') prf)

