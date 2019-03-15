module Examples.LT

import Darknet

mutual
  lt_3_3 : CLang
  lt_3_3 = Assert lt_3_3_assert
            $ Halt

  lt_3_3_assert : Env -> Assertion
  lt_3_3_assert env =
    let
      x = Lit 3
      y = Lit 3
      x' = eval env x
      y' = eval env y
      prf = isLTE (S x') y'
    in
      MkAssertion (LT x y (MkEvald x x') (MkEvald y y') prf)

