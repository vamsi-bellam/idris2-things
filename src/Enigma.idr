module Enigma 
import Data.Vect

isUpperCase:  Char -> Bool 
isUpperCase c = if (c == toUpper c) then True else False


converter : (u : Char) -> (c : Char ** (isUpperCase c = True))
converter u =
  case u of
    'A' => ('A' ** Refl)
    'B' => ('B' ** Refl)
    'C' => ('C' ** Refl)
    'D' => ('D' ** Refl)
    'E' => ('E' ** Refl)
    'F' => ('F' ** Refl)
    'G' => ('G' ** Refl)
    'H' => ('H' ** Refl)
    'I' => ('I' ** Refl)
    'J' => ('J' ** Refl)
    'K' => ('K' ** Refl)
    'L' => ('L' ** Refl)
    'M' => ('M' ** Refl)
    'N' => ('N' ** Refl)
    'O' => ('O' ** Refl)
    'P' => ('P' ** Refl)
    'Q' => ('Q' ** Refl)
    'R' => ('R' ** Refl)
    'S' => ('S' ** Refl)
    'T' => ('T' ** Refl)
    'U' => ('U' ** Refl)
    'V' => ('V' ** Refl)
    'W' => ('W' ** Refl)
    'X' => ('X' ** Refl)
    'Y' => ('Y' ** Refl)
    _ => ('Z' ** Refl)


conv: (l: List Char) -> List ((c : Char ** ((isUpperCase c) = True)) ) 
conv [] = []
conv (x :: xs) = (converter x) :: conv xs

conv': List ((c : Char ** ((isUpperCase c) = True)) ) -> List Char 
conv' [] = []
conv' (((fst ** snd)) :: xs) = fst :: (conv' xs)


data AllUppercase : List Char -> Type where
  NilAU : AllUppercase []
  ConsAU : {x : Char} -> {xs : List Char} -> isUpperCase x = True -> AllUppercase xs -> AllUppercase (x :: xs)

  
cl: (l: List ((c : Char ** (isUpperCase c = True))) ) -> (AllUppercase (conv' l))
cl [] = NilAU
cl (((fst ** snd)) :: xs) = ConsAU snd (cl xs)


      


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

-- isBetween: (x: Int) -> ((x >= 0 && x <= 26) = True)
-- isBetween x = ?isBetween_rhs

-- index: (c: Char) -> {auto p: (isUpperCase c) = True} -> (x: Int ** ((x >= 0 && x <= 26) = True)) 
-- index c = let t = cast c - cast 'A' in (t ** ?lk)

index: (c: Char) -> {auto p: (isUpperCase c) = True} -> Int
index c = cast c - cast 'A' 

charToIndex:  (l: List Char) -> {auto upperCaseList: AllUppercase l} -> List Int
charToIndex [] = []
charToIndex (x :: xs) {upperCaseList = ConsAU a b} = index x :: (charToIndex xs)

getVal: Ord a => (key: a) -> (List (a, b)) -> Maybe b
getVal key [] = Nothing
getVal key ((k, v) :: xs) = if key == k then Just v else getVal key xs

mapi: (f: Int -> a -> b) -> List a -> List b 
mapi f ls = mapiaux f ls 0 where 
            mapiaux: (f: Int -> a -> b) -> List a -> Int -> List b 
            mapiaux f [] i = []
            mapiaux f (x :: xs) i = (f i x) :: (mapiaux f xs (i+1))

makeSpecMap: (wiring: List Char) -> {auto upperCaseList: AllUppercase wiring} -> List (Int, Int)
makeSpecMap wiring = mapi (\i, x  => (i, x)) $ charToIndex wiring

data Mode = RightToLeft | LeftToRight


mapFrom : Mode -> (wiring: List Char) -> {auto upperCaseList: AllUppercase wiring} -> 
          (topLetter: Char) -> {auto upperCase: isUpperCase topLetter = True} -> Int -> Maybe Int
mapFrom mode wiring topLetter inputPos = 
        let specificationMap = makeSpecMap wiring
            topLetterIndex = index topLetter
            forwardOffset: Int -> Int -> Int
            forwardOffset offset input = mod (offset + input)  26
            inputContact = forwardOffset topLetterIndex inputPos
            backWardOffset: Int -> Int -> Int
            backWardOffset offset input = mod (26 - offset + input) 26
            outputContact: Mode -> Maybe Int
            outputContact mode = case mode of 
                                 RightToLeft => getVal inputContact specificationMap
                                 LeftToRight => getVal inputContact $ map (\(a, b) => (b, a)) specificationMap
        in case outputContact mode of 
                Just v => Just $ backWardOffset topLetterIndex v
                Nothing => Nothing

mapRefl: (wiring: List Char) -> {auto upperCaseList: AllUppercase wiring} -> Int -> Maybe Int
mapRefl wiring i = getVal i $ makeSpecMap wiring



isValidChar: Char -> Bool
isValidChar c = toUpper c >= 'A' && toUpper c <= 'Z' 


isValidList: List Char -> Bool
isValidList [] = True
isValidList (x :: xs) = (isValidChar x) && (isValidList xs)

prog: String -> Char -> Maybe Int
prog cs topLetter = 
          let cis = unpack cs in 
          if (isValidList cis && isValidChar topLetter) then
            let ws = (conv cis)
                (t **  p) = (converter topLetter)
                ks = (mapFrom LeftToRight  (conv' ws) {upperCaseList = cl ws} t 10)
            in ks
          else Nothing

