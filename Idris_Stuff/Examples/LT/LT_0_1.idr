module Examples.LT

import Darknet

mutual
  lt_0_1 : CLang
  lt_0_1 = Assert lt_0_1_assert
            $ Halt

  lt_0_1_assert : Env -> Assertion
  lt_0_1_assert env =
    let
      x = Lit 0
      y = Lit 1
      x' = eval env x
      y' = eval env y
      prf = isLTE (S x') y'
    in
      MkAssertion (LT x y (MkEvald x x') (MkEvald y y') prf)

