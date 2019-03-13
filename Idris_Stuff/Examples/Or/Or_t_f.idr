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
      t2 = b_false env
      t1' = True
      t2' = False
      prf = isOr t1' t2'
    in
      MkAssertion (Or t1 t2 (MkBEvald t1 t1') (MkBEvald t2 t2') prf)

