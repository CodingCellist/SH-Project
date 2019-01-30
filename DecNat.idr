-- Basic version

zNotS : (0 = S k) -> Void
zNotS Refl impossible

sNotZ : (S k = 0) -> Void
sNotZ Refl impossible

recDiff : (contra : (k = j) -> Void) -> (S k = S j) -> Void
recDiff contra Refl = contra Refl

decNat : (x : Nat) -> (y : Nat) -> Dec (x = y)
decNat Z Z = Yes Refl
decNat Z (S k) = No zNotS
decNat (S k) Z = No sNotZ
decNat (S k) (S j) 
    = case decNat k j of
           Yes Refl => Yes Refl
           No contra => No (recDiff contra)

-- Reflected as types

data Different : Nat -> Nat -> Type where
     ZNotS : Different Z (S k)
     SNotZ : Different (S k) Z
     RecDiff : Different x y -> Different (S x) (S y)

Show (Different x y) where
     show ZNotS = "First number smaller"
     show SNotZ = "First number bigger"
     show (RecDiff p) = show p

interface Diff t where
  data DiffPred : t -> t -> Type
  toContra : DiffPred x y -> (x = y) -> Void
  decDiff : (x : t) -> (y : t) -> Either (DiffPred x y) (x = y)

Diff Nat where
  DiffPred = Different

  toContra ZNotS = zNotS 
  toContra SNotZ = sNotZ 
  toContra (RecDiff p) = recDiff (toContra p)

  decDiff Z Z = Right Refl
  decDiff Z (S k) = Left ZNotS
  decDiff (S k) Z = Left SNotZ
  decDiff (S k) (S j) 
      = case decDiff k j of
             Left p => Left (RecDiff p)
             Right Refl => Right Refl

diffToDec : Diff t => (x : t) -> (y : t) -> Dec (x = y)
diffToDec x y
    = case decDiff x y of
           Left diff => No (toContra diff)
           Right prf => Yes prf

testDec : (x : Nat) -> (y : Nat) -> String
testDec x y
    = case decDiff x y of
           Left diff => show diff
           Right prf => "Same"


