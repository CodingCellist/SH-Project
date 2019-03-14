module Examples.GTE

import Darknet

mutual
  gte_3_3 : CLang
  gte_3_3 = Assert gte_3_3_assert
            $ Halt

  gte_3_3_assert : Env -> Assertion
  gte_3_3_assert env =
    let
      x = Lit 3
      y = Lit 3
      x' = eval env x
      y' = eval env y
      prf = isLTE y' x'
    in
      MkAssertion (GTE x y (MkEvald x x') (MkEvald y y') prf)

