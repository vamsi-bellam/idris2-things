module Proofs


import Data.HList
import Data.Vect
import Decidable.Equality

%default total

data ColType = I64 | Str | Boolean | Float

Schema : Type
Schema = List ColType

IdrisType : ColType -> Type
IdrisType I64     = Int64
IdrisType Str     = String
IdrisType Boolean = Bool
IdrisType Float   = Double

Row : Schema -> Type
Row = HList . map IdrisType

record Table where
  constructor MkTable
  schema : Schema
  size   : Nat
  rows   : Vect size (Row schema)

data SameColType : (c1, c2 : ColType) -> Type where
  SameCT : SameColType c1 c1

-- Above code pre-defined, taken from https://github.com/stefan-hoeck/idris2-tutorial/blob/main/src/Tutorial/Eq.md
-- Show that SameColType is a reflexive relation.

sctRefl: SameColType c1 c1
sctRefl = SameCT

-- Show that SameColType is a symmetric relation.
sctSym: SameColType c1 c2 -> SameColType c2 c1
sctSym SameCT = SameCT


-- Show that SameColType is a transitive relation.
sctTran: SameColType c1 c2 -> SameColType c2 c3 -> SameColType c1 c3
sctTran SameCT SameCT = SameCT

-- Let f be a function of type ColType -> a for an arbitrary type a. 
-- Show that from a value of type SameColType c1 c2 follows that f c1 and f c2 are equal.

f: ColType -> a 

sctCong: SameColType c1 c2 -> (f c1 = f c2)
sctCong SameCT = Refl

-- Implement a function for verifying that two natural numbers are identical. 
-- Try using cong in your implementation

sameNat: (n: Nat) -> (m: Nat) -> Maybe (n = m)
sameNat 0 0 = Just Refl
sameNat 0 (S k) = Nothing
sameNat (S k) 0 = Nothing
-- <$> is just map
sameNat (S k) (S j) = (\x => cong S x) <$> (sameNat k j)

-- Use the function from exercise 5 for zipping two Tables if they have the same number of rows.

appRows : {ts1 : _} -> Row ts1 -> Row ts2 -> Row (ts1 ++ ts2)
appRows {ts1 = []} Nil y = y
appRows {ts1 = _ :: _} (x :: xs) y = x :: (appRows xs y)

zipWith: (f: a -> b -> c)  -> Vect n a -> Vect n b -> Vect n c
zipWith f [] [] = []
zipWith f (x :: xs) (y :: ys) = (f x y) :: zipWith f xs ys

zipTables: Table -> Table -> Maybe Table
zipTables (MkTable s1 k xs) (MkTable s2 j ys) 
            = case (sameNat k j) of
                    Nothing => Nothing 
                    Just Refl => Just (MkTable _ _ (zipWith appRows xs ys))


schema1: Schema
schema1 = [Boolean, Boolean, Boolean]

table1: Table
table1 = (MkTable schema1 1 ([[True, True, False]]))

schema2: Schema
schema2 = [Str]

table2: Table
table2 = (MkTable schema2 1 ([["Vamsi"]]))

-- How it is combining schema 1 and schema 2, as I just kept _ in zipTables
table12: Maybe Table 
table12 = (zipTables table1 table2)

-- Programs as Proofs 

-- Proof that map id on an Either e returns the value unmodified.

mapEitherId: (e: Either a b) -> map (Prelude.id) e = e
mapEitherId (Left x) = Refl 
mapEitherId (Right x) = Refl

-- Proof that map id on a list returns the list unmodified.

mapListId: (l: List a) -> map (Prelude.id) l = l
mapListId [] = Refl
mapListId (x :: xs) = cong (x ::) $ (mapListId xs)



-- Implement function replaceVect:

replaceVect : (ix : Fin n) -> a -> Vect n a -> Vect n a
replaceVect FZ x (_ :: ys) = x :: ys
replaceVect (FS i) x (y :: ys) = y :: (replaceVect i x ys)

replaceVectProof: (ix : Fin n) -> (x : a) -> (v : Vect n a) -> index ix (replaceVect ix x v) = x
replaceVectProof FZ _ [] impossible
replaceVectProof (FS y) _ [] impossible
replaceVectProof FZ x (y :: xs) = Refl
replaceVectProof (FS z) x (y :: xs) = replaceVectProof z x xs

-- insertVect 

insertVect : (ix : Fin (S n)) -> a -> Vect n a -> Vect (S n) a
insertVect FZ x xs = x :: xs
insertVect (FS y) x (z :: xs) = z :: insertVect y x xs

insertVectProof: (ix : Fin (S n)) -> (x : a) -> (v : Vect n a) -> index ix (insertVect ix x v) = x
insertVectProof FZ x [] = Refl
insertVectProof FZ x (y :: xs) = Refl
insertVectProof (FS y) x (z :: xs) = insertVectProof y x xs

-- Didn't understood the No case in Dec 