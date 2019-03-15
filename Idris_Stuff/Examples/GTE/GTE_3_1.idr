module Examples.GTE

import Darknet

mutual
  gte_3_1 : CLang
  gte_3_1 = Assert gte_3_1_assert
            $ Halt

  gte_3_1_assert : Env -> Assertion
  gte_3_1_assert env =
    let
      x = Lit 3
      y = Lit 1
      x' = eval env x
      y' = eval env y
      prf = isLTE y' x'
    in
      MkAssertion (GTE x y (MkEvald x x') (MkEvald y y') prf)

