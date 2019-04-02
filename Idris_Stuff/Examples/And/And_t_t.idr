module Examples.And

import Darknet
import Examples.True

mutual
  and_t_t : CLang
  and_t_t = Assert and_t_t_assert
            $ Halt

  and_t_t_assert : Env -> Assertion
  and_t_t_assert env =
    let
      t1 = b_true env
      t2 = b_true env
      t1' = beval env t1
      t2' = beval env t2
      prf = isAnd t1' t2'
    in
      MkAssertion (And t1 t2 (MkBEvald t1 t1') (MkBEvald t2 t2') prf)

