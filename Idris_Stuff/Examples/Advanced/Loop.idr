module Examples.Advanced

import Darknet

mutual
  loop : CLang
  loop = BlockTime "measured" 3
         $ BlockTime "acc" 2  -- dummy value illustrating 0.02 time
                              -- units over 100 iterations
         $ Assert loop_assert
         $ Halt

  loop_assert : Env -> Assertion
  loop_assert env =
    let
      p0 = Var "measured"
      p1 = Var "acc"
      p0' = eval env p0
      p1' = eval env p1
      prf = isLTE p1' p0'
    in
      MkAssertion
        (LTE p1 p0 (MkEvald p1 p1') (MkEvald p0 p0') prf)
  
