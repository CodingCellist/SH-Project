import Darknet
import Examples.True

mutual
  not_true : CLang
  not_true = Assert not_true_assert
              $ Halt

  not_true_assert : Env -> Assertion
  not_true_assert env =
    let
      t = b_true env
      t' = True
      prf = isNot t'
    in
      MkAssertion (Not t (MkBEvald t t') prf)

