import Darknet


mutual
        fact_darknet : CLang
        fact_darknet = BlockEnergy "loop_energy" 100 $ BlockTime "loop_cost" 1005 $ BlockTime "fill_cpu_time" 1 $ BlockTime "forward_time" 8 $ Assert darknet_assert $ Halt


        darknet_assert : Env -> Assertion
        darknet_assert env =
                let
                 p0 = ( Mul (Var "loop_cost") (Var "loop_energy")  )
                 p1 = ( Mul ( Plus ( Plus (Var "fill_cpu_time") (Var "forward_time")  ) ( Lit 1 )  ) ( Lit 107 )  )
                 p0' = eval env p0
                 p1' = eval env p1

                in MkAssertion (Eq p0 p1 (MkEvald p0 p0') (MkEvald p1 p1') (Refl ))