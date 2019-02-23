import Darknet

mutual 
  test_not : CLang
  test_not = Assert assert_not $ Halt

  assert_not : Env -> Assertion
  assert_not env =
    let
      n1 = Lit 1
      n2 = Lit 2
      n1' = eval env n1
      n2' = eval env n2
      false = NEq (n1) (n2) (MkEvald n1 n1') (MkEvald n2 n2') (isNEq n1' n2')

      b = false
      b' = False
      not = Darknet.Not b (MkBEvald b b') (isNot b') 
    in
      MkAssertion not

