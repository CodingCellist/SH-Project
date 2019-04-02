module Examples.Or

import Darknet
import Examples.False

mutual
  or_f_f : CLang
  or_f_f = Assert or_f_f_assert
            $ Halt

  or_f_f_assert : Env -> Assertion
  or_f_f_assert env =
    let
      f1 = b_false env
      f2 = b_false env
      f1' = beval env f1
      f2' = beval env f2
      prf = isOr f1' f2'
    in
      MkAssertion (Or f1 f2 (MkBEvald f1 f1') (MkBEvald f2 f2') prf)

