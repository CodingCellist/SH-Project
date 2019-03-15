module Examples

import Darknet

public export
b_true : Env -> BooleanExpression
b_true env =
  let
    x = Lit 1
    y = Lit 1
    x' = eval env x
    y' = eval env y
    prf = decEq x' y'
  in
    Eq x y (MkEvald x x') (MkEvald y y') prf

