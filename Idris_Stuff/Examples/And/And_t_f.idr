module Examples.And

import Darknet
import Examples.True
import Examples.False

mutual
  and_t_f : CLang
  and_t_f = Assert and_t_f_assert
            $ Halt

  and_t_f_assert : Env -> Assertion
  and_t_f_assert env =
    let
      t1 = b_true env
      f2 = b_false env
      t1' = True
      f2' = False
      prf = isAnd t1' f2'
    in
      MkAssertion (And t1 f2 (MkBEvald t1 t1') (MkBEvald f2 f2') prf)

