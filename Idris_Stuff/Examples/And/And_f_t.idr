module Examples.And

import Darknet
import Examples.True
import Examples.False

mutual
  and_f_t : CLang
  and_f_t = Assert and_f_t_assert
            $ Halt

  and_f_t_assert : Env -> Assertion
  and_f_t_assert env =
    let
      f1 = b_false env
      t2 = b_true env
      f1' = beval env f1
      t2' = beval env t2
      prf = isAnd f1' t2'
    in
      MkAssertion (And f1 t2 (MkBEvald f1 f1') (MkBEvald t2 t2') prf)

