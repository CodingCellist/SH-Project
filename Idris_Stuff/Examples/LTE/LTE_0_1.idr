module Examples.LTE

import Darknet

mutual
  lte_0_1 : CLang
  lte_0_1 = Assert lte_0_1_assert
            $ Halt

  lte_0_1_assert : Env -> Assertion
  lte_0_1_assert env =
    let
      x = Lit 0
      y = Lit 1
      x' = eval env x
      y' = eval env y
      prf = isLTE x' y'
    in
      MkAssertion (LTE x y (MkEvald x x') (MkEvald y y') prf)

