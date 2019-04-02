module Examples.And

import Darknet
import Examples.False

mutual
  and_f_f : CLang
  and_f_f = Assert and_f_f_assert
            $ Halt

  and_f_f_assert : Env -> Assertion
  and_f_f_assert env =
    let
      f1 = b_false env
      f2 = b_false env
      f1' = beval env f1
      f2' = beval env f2
      prf = isAnd f1' f2'
    in
      MkAssertion (And f1 f2 (MkBEvald f1 f1') (MkBEvald f2 f2') prf)

