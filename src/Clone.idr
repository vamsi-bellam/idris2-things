module Clone 
import Data.Vect
import Data.Fin

data UpperChars = A | B | C | D | E | F | G | H | I | J | K | L | M | N | O | P | 
                  Q | R | S | T | U | V | W | X | Y | Z

get : UpperChars  -> Nat
get A = 0
get B = 1
get C = 2
get D = 3
get E = 4
get F = 5
get G = 6
get H = 7
get I = 8
get J = 9
get K = 10
get L = 11
get M = 12
get N = 13
get O = 14
get P = 15
get Q = 16
get R = 17
get S = 18
get T = 19
get U = 20
get V = 21
get W = 22
get X = 23
get Y = 24
get Z = 25




mapi: {0 n: Nat} -> (f: Nat -> a -> b) -> Vect n a -> Vect n b 
mapi f ls = mapiaux f ls 0 where 
                    mapiaux: {0 n: Nat} -> (f: Nat -> a -> b) -> Vect n a -> Nat -> Vect n b 
                    mapiaux f [] k = []
                    mapiaux f (x :: xs) k = f k x :: mapiaux f xs (S k)
                  

makeSpecMap: (wiring: Vect 26 UpperChars)-> Vect 26 (Nat, Nat)
makeSpecMap wiring = mapi (\i, x => (i, get x)) wiring

at: Fin n -> Vect n (Nat, Nat) -> Nat 
at FZ ((_, x) :: xs) = x
at (FS k) (y :: xs) = at k xs

-- Write own version of mod

data Mode = RightToLeft | LeftToRight

mapFrom : Mode -> (wiring: Vect 26 UpperChars) -> (topLetter: UpperChars) -> Nat -> Nat
mapFrom mode wiring topLetter inputPos = 
        let specificationMap = makeSpecMap wiring
            topLetterIndex = get topLetter
            forwardOffset: Nat -> Nat -> Nat
            forwardOffset offset input = mod (offset + input)  26
            inputContact = forwardOffset topLetterIndex inputPos
            backWardOffset:  Nat -> Nat -> Nat
            backWardOffset offset input = mod (minus (26 + input) offset) 26
            outputContact: Mode -> Nat
            outputContact mode = case mode of 
                                      RightToLeft => at 1 specificationMap
                                      LeftToRight => at inputContact $ map (\(a, b) => (b, a)) specificationMap
        in backWardOffset topLetterIndex $ outputContact mode


mapRefl: (wiring: Vect 26 UpperChars) -> (pos: Nat) -> {auto pf: pos < 26 = True} -> Nat
mapRefl wiring pos = at pos $ makeSpecMap wiring

isValidChar: Char -> Bool
isValidChar c = toUpper c >= 'A' && toUpper c <= 'Z' 


isValidList: List Char -> Bool
isValidList [] = True
isValidList (x :: xs) = (isValidChar x) && (isValidList xs)

program: String -> Char -> Int -> Maybe Int
program cs topLetter pos = 
          let cis = unpack cs in 
          if (isValidList cis && isValidChar topLetter) then
            let ws = (allUppercase cis)
                (topLetter **  p) = (uppercaseEncoderWithProof topLetter)
                ks = (mapFrom LeftToRight  (getCharListFromAllUppercase ws) {uppercaseList = allUppercaseList ws} topLetter pos)
            in ks
          else Nothing

