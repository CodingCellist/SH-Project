import Darknet


mutual
	fact_darknet : CLang 
	fact_darknet = BlockTime "loop_cost" 303 $ BlockTime "fill_cpu_time" 1 $ BlockTime "forward_time" 8 $ Assert darknet_assert $ Halt 


	darknet_assert : Env -> Assertion
	darknet_assert env = 
		let
		 p0 = (Var "loop_cost" )
		 p1 = ( Mul ( Plus ( Plus (Var "fill_cpu_time" )(Var "forward_time" ) ) (Var "OVERHEAD" ) ) ( Lit 107 )  ) 
		 p0' = eval env p0
		 p1' = eval env p1

		in MkAssertion ( (NEq p0 p1 (MkEvald p0 p0') (MkEvald p1 p1') (isNEq p0' p1' )) ) 
