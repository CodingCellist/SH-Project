module Examples.LTE

import Darknet

mutual
  lte_3_1 : CLang
  lte_3_1 = Assert lte_3_1_assert
            $ Halt

  lte_3_1_assert : Env -> Assertion
  lte_3_1_assert env =
    let
      x = Lit 3
      y = Lit 1
      x' = eval env x
      y' = eval env y
      prf = isLTE x' y'
    in
      MkAssertion (LTE x y (MkEvald x x') (MkEvald y y') prf)

