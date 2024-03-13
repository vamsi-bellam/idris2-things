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


-- Show that SameColType is a interRelitive relation.
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

-- Adding 0 will erase the code after compilation. 
0 insertVectProof: (ix : Fin (S n)) -> (x : a) -> (v : Vect n a) -> index ix (insertVect ix x v) = x
insertVectProof FZ x [] = Refl
insertVectProof FZ x (y :: xs) = Refl
insertVectProof (FS y) x (z :: xs) = insertVectProof y x xs

-- f is something, if given proof thet List.length as = List.length bs gives void, 
-- p is a proof that as = bs, so only way to construct a proof that List.length 
-- as = List.length bs is using cong(which takes a fun and prof( a=b ) and gives f a = f b)
notSameLength : Not (List.length as = length bs) -> Not (as = bs)
notSameLength f p = f $ (cong List.length p)

-- a is essentially a proof
interface Uninhabited' a where 
  uninhabited': a -> Void


Uninhabited' (SameColType I64 Str) where 
  uninhabited' SameCT impossible


-- Show that if a = b cannot hold, then b = a cannot hold either.
symmetric: (a = b) -> (b = a)
symmetric Refl = Refl

symmetricOnNot: Not (a = b) -> Not (b = a)
symmetricOnNot f prf = f $ (symmetric prf)

-- Show that if a = b holds, and b = c cannot hold, then a = c cannot hold either.

interRel: a = b -> a = c -> b = c
interRel Refl Refl = Refl

abcRel: (a = b) -> Not (b = c) -> Not (a = c)
abcRel prf f prf1 = f $ (interRel prf prf1)

-- Implement Uninhabited for Crud i a. Try to be as general as possible.

data Crud : (i : Type) -> (a : Type) -> Type where
  Create : (value : a) -> Crud i a
  Update : (id : i) -> (value : a) -> Crud i a
  Read   : (id : i) -> Crud i a
  Delete : (id : i) -> Crud i a


Uninhabited i  => Uninhabited a  => Uninhabited (Crud i a) where 
  uninhabited (Create value) = uninhabited value
  uninhabited (Update id value) = uninhabited value
  uninhabited (Read id) = uninhabited id
  uninhabited (Delete id) = uninhabited id




-- Implement DecEq for ColType
DecEq ColType where
  decEq I64 I64 = Yes Refl
  decEq I64 Str = No $ (\case Refl impossible)
  decEq I64 Boolean = No $ (\case Refl impossible)
  decEq I64 Float = No $ (\case Refl impossible)
  decEq Str I64 = No $ (\case Refl impossible)
  decEq Str Str = Yes Refl
  decEq Str Boolean = No $ (\case Refl impossible)
  decEq Str Float = No $ (\case Refl impossible)
  decEq Boolean I64 = No $ (\case Refl impossible)
  decEq Boolean Str = No $ (\case Refl impossible)
  decEq Boolean Boolean = Yes Refl
  decEq Boolean Float = No $ (\case Refl impossible)
  decEq Float I64 = No $ (\case Refl impossible)
  decEq Float Str = No $ (\case Refl impossible)
  decEq Float Boolean = No $ (\case Refl impossible)
  decEq Float Float = Yes Refl


{-  Implementations such as the one from exercise 6 are cumbersome to write as 
    they require a quadratic number of pattern matches with relation to the 
    number of data constructors. Here is a trick how to make this more bearable.
    1.Implement a function ctNat, which assigns every value of type ColType a 
      unique natural number.
    2.Proof that ctNat is injective. Hint: You will need to pattern match on the
      ColType values, but four matches should be enough to satisfy the coverage 
      checker.
    3.In your implementation of DecEq for ColType, use decEq on the result of 
      applying both column types to ctNat, thus reducing it to only two lines of
      code.
  
    We will later talk about with rules: Special forms of dependent pattern 
    matches, that allow us to learn something about the shape of function arguments 
    by performing computations on them. These will allow us to use a similar 
    technique as shown here to implement DecEq requiring only n pattern matches 
    for arbitrary sum types with n data constructors.
 -}

ctNat: ColType -> Nat 
ctNat I64 = 0
ctNat Str = 1
ctNat Boolean = 2
ctNat Float = 3

ctNatInjective: (c1, c2: ColType) -> (ctNat c1 = ctNat c2) -> c1 = c2
ctNatInjective I64 I64 Refl = Refl
ctNatInjective Str Str Refl = Refl
ctNatInjective Boolean Boolean Refl = Refl
ctNatInjective Float Float Refl = Refl

namespace NewDecEq
  DecEq ColType where 
    decEq c1 c2 = case (decEq (ctNat c1) (ctNat c2) ) of 
                    (Yes prf) => Yes $ ctNatInjective c1 c2 prf
                    (No contra) => No $ (\x => contra $ (cong ctNat x))

data NotNil : (as : List a) -> Type where
  IsNotNil : NotNil (h :: t)

head1 : (as : List a) -> (0 _ : NotNil as) -> a
head1 (h :: _) _ = h
head1 [] IsNotNil impossible

nonEmpty : (as : List a) -> Dec (NotNil as)
nonEmpty (x :: xs) = Yes IsNotNil
nonEmpty []        = No (\case IsNotNil impossible)

headMaybe1 : List a -> Maybe a
headMaybe1 as = case nonEmpty as of
  Yes prf => Just $ head1 as prf
  No  _   => Nothing

head : (as : List a) -> {auto 0 prf : NotNil as} -> a
head (x :: _) = x
head [] impossible

headEx3 : Nat
headEx3 = Proofs.head [1,2,3]

-- errHead : Nat
-- errHead = Proofs.head []

headMaybe2 : List a -> Maybe a
headMaybe2 as = case nonEmpty as of
  Yes prf => Just $ Proofs.head as 
  No  _   => Nothing

-- Implement tail for lists.

tail : (as : List a) -> {auto 0 prf : NotNil as} -> List a
tail (_ :: xs) = xs
tail [] impossible


-- Implement functions for returning the largest and smallest element in a list.

-- even though this is not infinite recursion, compiler thinking it is..
-- If covering is removed, it gives above error
covering
largest: Ord a => (as: List a) -> (0 _: NotNil as) => a
largest (h :: []) = h
largest (h :: x :: xs) = if h > x then largest (h :: xs) else largest (x :: xs)


covering
smallest: Ord a => (as: List a) -> (0 _: NotNil as) => a
smallest (h :: []) = h
smallest (h :: x :: xs) = if h > x then smallest (x :: xs) else smallest (h :: xs)

-- Define a predicate for strictly positive natural numbers and use it to 
-- implement a safe and provably total division function on natural numbers.

data OnlyPosNat: Nat -> Type where 
  PosNats: OnlyPosNat (S k)

nonZero: (n: Nat) -> Dec (OnlyPosNat n)
nonZero 0 = No (\case PosNats impossible)
nonZero (S k) = Yes PosNats

divPos: (n, m: Nat) -> (0 _: (OnlyPosNat m)) => Nat
divPos 0 (S k) = 0
divPos (S k) (S j) = div (S k) (S j)
 
-- Define a predicate for a non-empty Maybe and use it to safely extract the value stored in a Just. 
-- Show that this predicate is decidable by implementing a corresponding conversion function.

data NonEmpty: Maybe a -> Type where 
  NE: NonEmpty (Just a)

getVal: (m: Maybe a) -> (0 _: (NonEmpty m)) => a
getVal (Just x) = x

isJust: (m: Maybe a) -> Dec (NonEmpty m)
isJust Nothing = No (\case NE impossible)
isJust (Just x) = Yes NE


-- Define and implement functions for safely extracting values from a Left and 
-- a Right by using suitable predicates. Show again that these predicates are decidable.

data OnlyLeft: (e: Either a b) -> Type where 
  OLeft: OnlyLeft (Left a)

getLeft: (e: Either a b) -> (0 _: OnlyLeft e) => a 
getLeft (Left x) = x

isLeft: (e: Either a b) -> Dec (OnlyLeft e)
isLeft (Left x) = Yes OLeft
isLeft (Right x) = No (\case OLeft impossible)


data OnlyRight: (e: Either a b) -> Type where 
  ORight: OnlyRight (Right b)

getRight: (e: Either a b) -> (0 _: OnlyRight e) => b
getRight (Right x) = x

isRight: (e: Either a b) -> Dec (OnlyRight e)
isRight (Left x) = No (\case ORight impossible)
isRight (Right x) = Yes ORight


