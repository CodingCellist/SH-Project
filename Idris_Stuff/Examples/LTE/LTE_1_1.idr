import Darknet

mutual
  lte_1_1 : CLang
  lte_1_1 = Assert lte_1_1_assert
            $ Halt

  lte_1_1_assert : Env -> Assertion
  lte_1_1_assert env =
    let
      x = Lit 1
      y = Lit 1
      x' = eval env x
      y' = eval env y
      prf = isLTE x' y'
    in
      MkAssertion (LTE x y (MkEvald x x') (MkEvald y y') prf)

