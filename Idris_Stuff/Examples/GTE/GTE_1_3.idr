module Examples.GTE

import Darknet

mutual
  gte_1_3 : CLang
  gte_1_3 = Assert gte_1_3_assert
            $ Halt

  gte_1_3_assert : Env -> Assertion
  gte_1_3_assert env =
    let
      x = Lit 1
      y = Lit 3
      x' = eval env x
      y' = eval env y
      prf = isLTE y' x'
    in
      MkAssertion (GTE x y (MkEvald x x') (MkEvald y y') prf)

