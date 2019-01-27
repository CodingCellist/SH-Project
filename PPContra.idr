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

printContra : (contra : (num1 = num2) -> Void) -> String
printContra (sucNotZero) = "LHS is 0, RHS is 1"
printContra (zeroNotSuc) = "LHS is 1, RHS is 0"
printContra contra = ?printContra_rhs_2

ppPrototype : Dec (num1 = num2) -> IO ()
ppPrototype (Yes prf) = putStrLn "Everything is fine."
ppPrototype (No contra) = putStrLn (printContra contra)

test : IO ()
test = ppPrototype (checkEqNat 2 3)
