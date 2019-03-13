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
      f1 = b_false env
      t2 = b_true env
      f1' = False
      t2' = True
      prf = isOr f1' t2'
    in
      MkAssertion (Or f1 t2 (MkBEvald f1 f1') (MkBEvald t2 t2') prf)

