import Darknet

mutual
  test_neq : CLang
  test_neq = Assert assert_neq $ Halt
  
  assert_neq : Env -> Assertion
  assert_neq env =
    let
      n1 = Lit 1
      n2 = Lit 2
      n1' = eval env n1
      n2' = eval env n2
      neq = NEq (n1) (n2) (MkEvald n1 n1') (MkEvald n2 n2') (isNEq n1' n2')
    in
      MkAssertion neq
  
