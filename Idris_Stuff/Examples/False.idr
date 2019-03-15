module Examples.Not.False

import Darknet

public export
b_false : Env -> BooleanExpression
b_false env =
  let
    x = Lit 0
    y = Lit 1
    x' = eval env x
    y' = eval env y
    prf = decEq x' y'
  in
    Eq x y (MkEvald x x') (MkEvald y y') prf

