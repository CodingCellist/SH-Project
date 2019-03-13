module Examples.Or

import Darknet
import Examples.True
import Examples.False

mutual
  or_f_t : CLang
  or_f_t = Assert or_f_t_assert
            $ Halt

  or_f_t_assert : Env -> Assertion
  or_f_t_assert env =
    let
      t1 = b_false env
      t2 = b_true env
      t1' = False
      t2' = True
      prf = isOr t1' t2'
    in
      MkAssertion (Or t1 t2 (MkBEvald t1 t1') (MkBEvald t2 t2') prf)

