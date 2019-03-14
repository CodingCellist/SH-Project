module Examples.GT

import Darknet

mutual
  gt_3_3 : CLang
  gt_3_3 = Assert gt_3_3_assert
            $ Halt

  gt_3_3_assert : Env -> Assertion
  gt_3_3_assert env =
    let
      x = Lit 3
      y = Lit 3
      x' = eval env x
      y' = eval env y
      prf = isLTE (S y') x'
    in
      MkAssertion (GT x y (MkEvald x x') (MkEvald y y') prf)

