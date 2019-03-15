module Examples.Or

import Darknet
import Examples.True

mutual
  or_t_t : CLang
  or_t_t = Assert or_t_t_assert
            $ Halt

  or_t_t_assert : Env -> Assertion
  or_t_t_assert env =
    let
      t1 = b_true env
      t2 = b_true env
      t1' = True
      t2' = True
      prf = isOr t1' t2'
    in
      MkAssertion (Or t1 t2 (MkBEvald t1 t1') (MkBEvald t2 t2') prf)

