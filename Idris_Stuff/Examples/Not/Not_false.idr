import Darknet
import Examples.False

mutual
  not_false : CLang
  not_false = Assert not_false_assert
              $ Halt

  not_false_assert : Env -> Assertion
  not_false_assert env =
    let
      f = b_false env
      f' = beval env f
      prf = isNot f'
    in
      MkAssertion (Not f (MkBEvald f f') prf)

