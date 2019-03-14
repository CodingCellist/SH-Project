module Examples.LTE

import Darknet

mutual
  lte_3_3 : CLang
  lte_3_3 = Assert lte_3_3_assert
            $ Halt

  lte_3_3_assert : Env -> Assertion
  lte_3_3_assert env =
    let
      x = Lit 3
      y = Lit 3
      x' = eval env x
      y' = eval env y
      prf = isLTE x' y'
    in
      MkAssertion (LTE x y (MkEvald x x') (MkEvald y y') prf)

