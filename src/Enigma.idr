module Enigma 
import Data.Vect

isUpperCase:  Char -> Bool 
isUpperCase c = if (c == toUpper c) then True else False

index: (c: Char) -> {auto p: (isUpperCase c) = True} -> Int 
index c = cast c - cast 'A'

data UChar = A | B

converter: Char -> UChar
converter c = if c == 'A' then A else B

converter': (u: Char) -> (c: Char ** (isUpperCase c = True))
converter' u = case (converter u) of 
                  A => ('A' ** Refl)
                  B => ('B' ** Refl)


mapi: (f: Int -> a -> b) -> List a -> List b 
mapi f ls = mapiaux f ls 0 where 
            mapiaux: (f: Int -> a -> b) -> List a -> Int -> List b 
            mapiaux f [] i = []
            mapiaux f (x :: xs) i = (f i x) :: (mapiaux f xs (i+1))


{- [map_r_to_l wiring top_letter input_pos] is the left-hand output position
 * at which current would appear when current enters at right-hand input
 * position [input_pos] to a rotor whose wiring specification is given by
 * [wiring].  The orientation of the rotor is given by [top_letter],
 * which is the top letter appearing to the operator in the rotor's
 * present orientation.
 * requires:
 *  - [wiring] is a valid wiring specification.
 *  - [top_letter] is in 'A'..'Z'
 *  - [input_pos] is in 0..25
 -}


data AllUppercase : List Char -> Type where
  NilAU : AllUppercase []
  ConsAU : {x : Char} -> {xs : List Char} -> isUpperCase x = True -> AllUppercase xs -> AllUppercase (x :: xs)


makeSpecMap:  (l: List Char) -> {auto pf: AllUppercase l} -> List (Int, Char)
makeSpecMap [] = []
makeSpecMap (x :: xs) {pf = ConsAU a b} = (index x, x) :: (makeSpecMap xs)


conv: (l: List Char) -> List ((c : Char ** ((isUpperCase c) = True)) ) 
conv [] = []
conv (x :: xs) = (converter' x) :: conv xs

conv': List ((c : Char ** ((isUpperCase c) = True)) ) -> List Char 
conv' [] = []
conv' (((fst ** snd)) :: xs) = fst :: (conv' xs)


cl: (l: List ((c : Char ** (isUpperCase c = True))) ) -> (AllUppercase (conv' l))
cl [] = NilAU
cl (((fst ** snd)) :: xs) = ConsAU snd (cl xs)
      
-- cll: (l: List Char) -> (AllUppercase l)        
-- cll [] = NilAU
-- cll (x :: xs) = ?cll_rhs_1

-- t: List Char -> List (Int, Char)
-- t [] = []
-- t l = (makeSpecMap l {pf= cll l})

isValidChar: Char -> Bool
isValidChar c = toUpper c >= 'A' && toUpper c <= 'Z' 


isValidList: List Char -> Bool
isValidList [] = True
isValidList (x :: xs) = (isValidChar x) && (isValidList xs)


mapRightToLeft : (l: List Char) -> {auto pf: AllUppercase l} -> 
                    (t: Char) -> {auto prf: isUpperCase t = True} -> Int -> Maybe Int
mapRightToLeft wiring topLetter inputPos = 
        let specificationMap = makeSpecMap wiring
            topLetterIndex = index topLetter
            forwardOffset: Int -> Int -> Int
            forwardOffset offset input = mod (offset + input)  26
            inputContact = forwardOffset topLetterIndex inputPos
            backWardOffset: Int -> Int -> Int
            backWardOffset offset input = mod (26 - offset + input) 26
        in ?ll


prog: (List Char) -> Char -> Maybe (List Char)
prog cs topLetter = if (isValidList cs && isValidChar topLetter) then Nothing 
          else 
          let ws = (conv cs)
              (t **  p) = (converter' topLetter)
              ks = (mapRightToLeft (conv' ws) {pf= cl ws} t 0)
          in ?kk

