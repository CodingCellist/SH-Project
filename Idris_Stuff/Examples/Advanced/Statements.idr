module Examples.Advanced.Statements

import Darknet

mutual
  statements : CLang
  statements = StmtTime "rd_time" 3
               $ StmtTime "wr_time" 4
               $ StmtEnergy "wr_energy" 9
               $ Assert statements_assert
               $ Halt

  statements_assert : Env -> Assertion
  statements_assert env =
    let
      p0 = Var "rd_time"
      p1 = Var "wr_time"
      p2 = Var "wr_energy"
      p3 = Lit 10
      p0' = eval env p0
      p1' = eval env p1
      p2' = eval env p2
      p3' = eval env p3
      prf0 = isLTE (S p0') p1' -- wr_time > rd_time
      prf1 = isLTE p2' p3'     -- wr_energy <= 10
    in
      let
        bexpr0 = GT p1 p0
                    (MkEvald p1 p1') (MkEvald p0 p0')
                    prf0
        bexpr1 = LTE p2 p3
                     (MkEvald p2 p2') (MkEvald p3 p3')
                     prf1
        bexpr0' = beval env bexpr0
        bexpr1' = beval env bexpr1
        prf = isAnd bexpr0' bexpr1'
              -- ((wr_time > rd_time) && (wr_energy <= 10)
      in
        MkAssertion
          (And bexpr0 bexpr1
               (MkBEvald bexpr0 bexpr0')
               (MkBEvald bexpr1 bexpr1')
               prf)
        
        

