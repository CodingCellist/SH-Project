module Examples.GTE

import Darknet

mutual
  gte_1_0 : CLang
  gte_1_0 = Assert gte_1_0_assert
            $ Halt

  gte_1_0_assert : Env -> Assertion
  gte_1_0_assert env =
    let
      x = Lit 1
      y = Lit 0
      x' = eval env x
      y' = eval env y
      prf = isLTE y' x'
    in
      MkAssertion (GTE x y (MkEvald x x') (MkEvald y y') prf)

