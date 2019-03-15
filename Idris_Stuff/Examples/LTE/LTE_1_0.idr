module Examples.LTE

import Darknet

mutual
  lte_1_0 : CLang
  lte_1_0 = Assert lte_1_0_assert
            $ Halt

  lte_1_0_assert : Env -> Assertion
  lte_1_0_assert env =
    let
      x = Lit 1
      y = Lit 0
      x' = eval env x
      y' = eval env y
      prf = isLTE x' y'
    in
      MkAssertion (LTE x y (MkEvald x x') (MkEvald y y') prf)

