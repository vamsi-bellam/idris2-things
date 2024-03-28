import Data.Vect 

isUpperCase: (c: Char) -> Bool 
isUpperCase c = if (c == toUpper c) then True else False

data AllUppercase : List Char -> Type where
  NilAU : AllUppercase []
  ConsAU : {x : Char} -> {xs : List Char} -> isUpperCase x = True -> AllUppercase xs -> AllUppercase (x :: xs)

index: (c: Char) -> {auto p: (isUpperCase c) = True} -> Int 
index c = cast c - cast 'A'

makeSpecMap': (p: List Char) -> { auto fa : AllUppercase p} -> Vect (length p) (Int, Char)
makeSpecMap' [] {fa = NilAU } = []
makeSpecMap' (x :: xs) {fa = ConsAU a b} = (index x, x) :: makeSpecMap' xs

data UChar = A | B

converter: Char -> UChar
converter c = if c == 'A' then A else B

converter': (u: Char) -> (c: Char ** (isUpperCase c = True))
converter' u = case (converter u) of 
                  A => ('A' ** Refl)
                  B => ('B' ** Refl)

-- conv: (l: List Char) -> Vect (length l) ((c : Char ** ((isUpperCase c) = True)) ) 
-- conv [] = []
-- conv (x :: xs) = (converter' x) :: conv xs

makeSpecMap'':  (n: Nat) -> Vect n Char -> Vect n (Int, Char)
makeSpecMap'' Z [] = []
makeSpecMap'' (S k) (x :: xs) = let (fs ** sn)= converter' x in 
                                    (index fs, x) :: (makeSpecMap'' k xs)




-- test: Char -> Int 
-- test x = case converter x of 
--                 A => (index (converter' A))
--                 _ => ?k

isUpperCase': UChar -> Bool 
isUpperCase' c = True

pf: (c: UChar) -> Dec (isUpperCase' c = True )
pf A = Yes Refl
pf B = Yes Refl

             

-- AllUppercaseDec : (xs : List Char) -> Dec (AllUppercase xs)
-- AllUppercaseDec [] = Yes NilAU
-- AllUppercaseDec (x :: xs) = let r = conv xs in 
--                                         ?kj
-- AllUppercaseDec (x :: xs) = case (converter' (converter x)) of
--                                    ((fst ** pf)) => case (AllUppercaseDec xs) of 
--                                                         Yes prf => Yes (ConsAU (pf) prf)
--                                                         No contr => ?ll
                                 


cast': Int -> Char 
cast' i = cast i

tes: Char -> Int 


-- Rewrite ruless

addZeroRight : (n : Nat) -> n + 0 = n
addZeroRight 0 = Refl
addZeroRight (S k) = cong S (addZeroRight k)

replaceVect : Vect (n + 0) a -> Vect n a
replaceVect xs = replace {p = \k => Vect k a} (addZeroRight n) xs

rewriteVect : Vect (n + 0) a -> Vect n a
rewriteVect as = rewrite sym (addZeroRight n) in as

rightZero' :  List (Vect n Nat)
           -> List (Vect (n + 0) Nat)
           -> List (Vect n Nat)
rightZero' = (++)


