import Darknet
import Examples.Not.False

mutual
  not_false : CLang
  not_false = Assert not_false_assert
              $ Halt

  not_false_assert : Env -> Assertion
  not_false_assert env =
    let
      f = False.b_false env
      f' = False
      prf = isNot f'
    in
      MkAssertion (Not f (MkBEvald f f') prf)

