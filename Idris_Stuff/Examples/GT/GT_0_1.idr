module Examples.GT

import Darknet

mutual
  gt_0_1 : CLang
  gt_0_1 = Assert gt_0_1_assert
            $ Halt

  gt_0_1_assert : Env -> Assertion
  gt_0_1_assert env =
    let
      x = Lit 0
      y = Lit 1
      x' = eval env x
      y' = eval env y
      prf = isLTE (S y') x'
    in
      MkAssertion (GT x y (MkEvald x x') (MkEvald y y') prf)

