module Examples.Real_Life.Aes

import Darknet

mutual
  aes : CLang
  aes = StmtEnergy "addRoundKey0" 2
        $ StmtEnergy "subBytesAcc" 10
        $ StmtEnergy "shiftRowsAcc" 3
        $ StmtEnergy "mixColumnsAcc" 5
        $ StmtEnergy "addRoundKeyAcc" 19 
        $ StmtEnergy "subBytes" 1
        $ StmtEnergy "shiftRows" 7
        $ StmtEnergy "addRoundKeyNr" 3
        $ Assert aes_assert
        $ Halt


  aes_assert : Env -> Assertion
  aes_assert env =
    let
      p0 = Var "addRoundKey0"
      p1 = Var "subBytesAcc"
      p2 = Var "shiftRowsAcc"
      p3 = Var "mixColumnsAcc"
      p4 = Var "addRoundKeyAcc"
      p5 = Var "subBytes"
      p6 = Var "shiftRows"
      p7 = Var "addRoundKeyNr"
      p8 = Lit 50
      p8' = eval env p8
      sum = Plus (Plus (Plus (Plus (Plus
                 (Plus (Plus p7 p6)
                  p5) p4) p3) p2) p1) p0
      sum' = eval env sum
      prf = isLTE sum' p8'
    in
      MkAssertion (LTE sum p8 (MkEvald sum sum') (MkEvald p8 p8') prf)


