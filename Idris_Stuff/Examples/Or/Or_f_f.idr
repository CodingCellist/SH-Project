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
      t1 = b_false env
      t2 = b_false env
      t1' = False
      t2' = False
      prf = isOr t1' t2'
    in
      MkAssertion (Or t1 t2 (MkBEvald t1 t1') (MkBEvald t2 t2') prf)

