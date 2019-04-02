module Examples.Or

import Darknet
import Examples.True
import Examples.False

mutual
  or_t_f : CLang
  or_t_f = Assert or_t_f_assert
            $ Halt

  or_t_f_assert : Env -> Assertion
  or_t_f_assert env =
    let
      t1 = b_true env
      f2 = b_false env
      t1' = beval env t1
      f2' = beval env f2
      prf = isOr t1' f2'
    in
      MkAssertion (Or t1 f2 (MkBEvald t1 t1') (MkBEvald f2 f2') prf)

