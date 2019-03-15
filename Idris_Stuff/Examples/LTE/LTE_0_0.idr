module Examples.LTE

import Darknet

mutual
  lte_0_0 : CLang
  lte_0_0 = Assert lte_0_0_assert
            $ Halt

  lte_0_0_assert : Env -> Assertion
  lte_0_0_assert env =
    let
      x = Lit 0
      y = Lit 0
      x' = eval env x
      y' = eval env y
      prf = isLTE x' y'
    in
      MkAssertion (LTE x y (MkEvald x x') (MkEvald y y') prf)

