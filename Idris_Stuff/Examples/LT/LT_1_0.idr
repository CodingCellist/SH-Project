module Examples.LT

import Darknet

mutual
  lt_1_0 : CLang
  lt_1_0 = Assert lt_1_0_assert
            $ Halt

  lt_1_0_assert : Env -> Assertion
  lt_1_0_assert env =
    let
      x = Lit 1
      y = Lit 0
      x' = eval env x
      y' = eval env y
      prf = isLTE (S x') y'
    in
      MkAssertion (LT x y (MkEvald x x') (MkEvald y y') prf)

