module Examples.GT

import Darknet

mutual
  gt_1_0 : CLang
  gt_1_0 = Assert gt_1_0_assert
            $ Halt

  gt_1_0_assert : Env -> Assertion
  gt_1_0_assert env =
    let
      x = Lit 1
      y = Lit 0
      x' = eval env x
      y' = eval env y
      prf = isLTE (S y') x'
    in
      MkAssertion (GT x y (MkEvald x x') (MkEvald y y') prf)

