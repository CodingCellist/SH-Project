module PPContra

-- Basic Dec example from the book

zeroNotSuc : (0 = S k) -> Void
zeroNotSuc Refl impossible

sucNotZero : (S k = 0) -> Void
sucNotZero Refl impossible

noRec : (contra : (k = j) -> Void) -> (S k = S j) -> Void
noRec contra Refl = contra Refl

checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Dec (num1 = num2)
checkEqNat Z Z = Yes Refl
checkEqNat Z (S k) = No zeroNotSuc
checkEqNat (S k) Z = No sucNotZero
checkEqNat (S k) (S j) = case checkEqNat k j of
                              (Yes prf) => Yes (cong prf)
                              (No contra) => No (noRec contra)

-- Attempt at pretty-printing

-- very simple implementation
showContra : (contra : (num1 = num2) -> Void) -> String
showContra (sucNotZero) = "LHS is 0, RHS is > 0"
showContra (zeroNotSuc) = "LHS is > 1, RHS is 0"
-- can't match on this:
-- showContra (noRec sucNotZero) = ?incr_rhs
-- showContra (noRec zeroNotSuc) = ?incr_lhs

ppPrototype : Dec (num1 = num2) -> IO ()
ppPrototype (Yes prf) = putStrLn "Everything is fine."
ppPrototype (No contra) = putStrLn (showContra contra)

test : IO ()
test = ppPrototype (checkEqNat 3 2)


-- Working version for Nat (credit to Edwin Brady)

data Different : Nat -> Nat -> Type where
    ZNotS : Different Z (S k)
    SNotZ : Different (S k) Z
    RecDiff : Different k j -> Different (S k) (S j)

Show (Different k j) where
  show ZNotS = "First number smaller."
  show SNotZ = "Second number smaller"
  show (RecDiff x) = show x

toContra : Different x y -> (x = y) -> Void
toContra ZNotS = zeroNotSuc
toContra SNotZ = sucNotZero
toContra (RecDiff x) = noRec (toContra x)

natDiff : (n1 : Nat) -> (n2 : Nat) -> Either (Different n1 n2) (n1 = n2)
natDiff Z Z = Right Refl
natDiff Z (S k) = Left ZNotS
natDiff (S k) Z = Left SNotZ
natDiff (S k) (S j) = case natDiff k j of
                           Left diff => Left (RecDiff diff)
                           Right Refl => Right Refl

decNat' : (n1 : Nat) -> (n2 : Nat) -> Dec (n1 = n2)
decNat' n1 n2 = case natDiff n1 n2 of
                     Left diff => No (toContra diff)
                     Right prf => Yes prf

-- a more proper test
test' : (n1 : Nat) -> (n2 : Nat) -> String
test' n1 n2 = case natDiff n1 n2 of
                   Left diff => show diff
                   Right prf => "The two numbers are identical."
