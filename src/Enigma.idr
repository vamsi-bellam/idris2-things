module Enigma 
import Data.Vect


isUpperCase: (c: Char) -> Bool 
isUpperCase c = if (c == toUpper c) then True else False


data Uppercase : Char -> Type where
  MkUppercase : (c : Char) -> (isUpper c = True) -> Uppercase c

-- Function to get the ASCII code of an uppercase character
indexUppercase : (c : Char) -> Uppercase c -> Int
indexUppercase c (MkUppercase _ p) = cast c

-- data OnlyUpper: (c: Char) -> Type where 
--     OU: (c: Char) -> OnlyUpper (toUpper c)

-- ex: OnlyUpper 'A'
-- ex = OU 'A'

-- ind: (c: ) -> (0 _: OnlyUpper c) => Int 
-- ind c = cast c

{-
 * [index c] is the 0-based index of [c] in the alphabet.
 * requires: [c] is an uppercase letter in A..Z 
-}
index: (c: Char) -> Int 
index c = cast c - cast 'A'

data ValidString: Vect 1 Char -> Type where 
    VString: (cs : List Char) -> (p: 2 = 2) -> (case cs of 
                                                    h => ValidString ?k)



-- ex: ValidString ('A' :: ['B'])
-- ex = VString ['A', 'B']

-- isValidString: (s: String) -> Dec (ValidString (unpack s))
-- isValidString (x :: (y :: [])) = Yes (VString [x, y])

-- Not working
-- makeSpecMap': (p: List Char) -> Vect (length p) (Int, Char)
-- makeSpecMap' [] = []
-- makeSpecMap' (x :: xs) = (index x, x) :: makeSpecMap' xs

-- makeSpecMap': (p: List Char) -> Vect (length p) (Int, Char)
-- makeSpecMap' [] = []
-- makeSpecMap' (x :: xs) = (index x, x) :: makeSpecMap' xs



-- makeSpecMap: (s: String) ->  Vect (length s) (Int, Char)
-- makeSpecMap s = let chars = unpack s in (makeSpecMap' chars)

mapi: (f: Int -> a -> b) -> List a -> List b 
mapi f ls = mapiaux f ls 0 where 
            mapiaux: (f: Int -> a -> b) -> List a -> Int -> List b 
            mapiaux f [] i = []
            mapiaux f (x :: xs) i = (f i x) :: (mapiaux f xs (i+1))


getVal: Ord a => (key: a) -> (List (a, b)) -> Maybe b
getVal key [] = Nothing
getVal key ((k, v) :: xs) = if key == k then Just v else getVal key xs

makeSpecMap: (s: String) ->  List (Int, Int)
makeSpecMap s = mapi (\i, x  => (i, index x)) $ (unpack s)

-- Error
-- data Elem : (elem : a) -> (as : List (a, b)) -> Type where
--   Here  : Elem x ((x , _) :: xs)
--   There : Elem x xs -> Elem x (y :: xs)
         
-- getVal: (key: a) -> (mp: List (a, b)) -> (0 prf: Elem key mp) => b
-- getVal key [] impossible
-- getVal key (x :: xs) {prf = Here} = ?getVal_rhs_1 




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

 
mapRightToLeft : String -> Char -> Int -> Maybe Int
mapRightToLeft wiring topLetter inputPos = 
        let specificationMap = makeSpecMap wiring
            topLetterIndex = index topLetter
            forwardOffset: Int -> Int -> Int
            forwardOffset offset input = mod (offset + input)  26
            inputContact = forwardOffset topLetterIndex inputPos
            backWardOffset: Int -> Int -> Int
            backWardOffset offset input = mod (26 - offset + input) 26
        in case (getVal inputContact specificationMap) of 
                Just val => Just (backWardOffset topLetterIndex val)
                Nothing => Nothing



