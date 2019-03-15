module Examples.Advanced

import Darknet

mutual
  loop : CLang
  loop = BlockTime "measured" 300
         $ BlockTime "acc" (2 * 100)  -- dummy value illustrating 2 time units oven 100 iterations
         $ Assert loop_assert
         $ Halt

  loop_assert : Env -> Assertion
  loop_assert env =
    let
      p0 = Var "measured"
      p1 = Var "acc"
      p0' = eval env p0
      p1' = eval env p1
    in
      MkAssertion (LTE p1 p0 (MkEvald p1 p1') (MkEvald p0 p0') (isLTE p1' p0'))
  
