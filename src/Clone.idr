module Clone 
import Data.Vect
import Data.Fin
-- TODO: Figure out why import Data.Vect.Sort not working from stdlib
import Sort



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
                  

WiringSpec: Type
WiringSpec = Vect 26 (Nat, Nat)

makeSpecMap: (wiring: Vect 26 UpperChars)-> WiringSpec
makeSpecMap wiring = mapi (\i, x => (i, get x)) wiring

revSpecMap: WiringSpec -> WiringSpec
revSpecMap wiringSpec = (sortBy (\(x1, _), (x2, _) => compare x1 x2) (map (\(a, b) => (b, a)) wiringSpec))


at: Fin n -> Vect n (Nat, Nat) -> Nat 
at FZ ((_, x) :: xs) = x
at (FS k) (y :: xs) = at k xs



mod'': (n: Nat) -> (m: Nat) -> {auto prf: GT m 0} -> (r: Nat ** LT r m)
mod'' n m = case (isLT n m) of 
                  Yes p => (n ** p)
                  No _ => (mod'' (minus n m) m)
                                      
data Mode = RightToLeft | LeftToRight

mapFrom : Mode -> (wiring: Vect 26 UpperChars) -> (topLetter: UpperChars) -> Nat -> Nat
mapFrom mode wiring topLetter inputPos = 
        let specificationMap = makeSpecMap wiring
            topLetterIndex = get topLetter
            forwardOffset: Nat -> Nat -> (r: Nat ** LT r 26) 
            forwardOffset offset input = mod'' (offset + input)  26
            inputContact = forwardOffset topLetterIndex inputPos
            backWardOffset:  Nat -> Nat -> Nat
            backWardOffset offset input = mod (minus (26 + input) offset) 26
            outputContact: Mode -> Nat
            outputContact mode = case mode of 
                                      RightToLeft => at (natToFinLT (fst inputContact) {prf= (snd inputContact)}) specificationMap
                                      -- The below impl is wrong
                                      LeftToRight => at (natToFinLT (fst inputContact) {prf= (snd inputContact)}) $ (revSpecMap specificationMap)
                                                        
        in backWardOffset topLetterIndex $ outputContact mode


mapRefl: (wiring: Vect 26 UpperChars) -> (pos: Nat) -> {auto pf: pos < 26 = True} -> Nat
mapRefl wiring pos = at 0 $ makeSpecMap wiring

isValidChar: Char -> Bool
isValidChar c = toUpper c >= 'A' && toUpper c <= 'Z' 


isValidList: List Char -> Bool
isValidList [] = True
isValidList (x :: xs) = (isValidChar x) && (isValidList xs)

charToUChar : Char -> Maybe UpperChars
charToUChar 'A' = Just A
charToUChar 'B' = Just B
charToUChar 'C' = Just C
charToUChar 'D' = Just D
charToUChar 'E' = Just E
charToUChar 'F' = Just F
charToUChar 'G' = Just G
charToUChar 'H' = Just H
charToUChar 'I' = Just I
charToUChar 'J' = Just J
charToUChar 'K' = Just K
charToUChar 'L' = Just L
charToUChar 'M' = Just M
charToUChar 'N' = Just N
charToUChar 'O' = Just O
charToUChar 'P' = Just P
charToUChar 'Q' = Just Q
charToUChar 'R' = Just R
charToUChar 'S' = Just S
charToUChar 'T' = Just T
charToUChar 'U' = Just U
charToUChar 'V' = Just V
charToUChar 'W' = Just W
charToUChar 'X' = Just X
charToUChar 'Y' = Just Y
charToUChar 'Z' = Just Z
charToUChar _   = Nothing


mapToUChars: Vect n Char -> Vect n (Maybe UpperChars)
mapToUChars [] = []
mapToUChars (x :: xs) = (charToUChar x) :: (mapToUChars xs)

toVectChars: Vect n (Maybe UpperChars) -> Maybe (Vect n UpperChars)
toVectChars [] = Just []
toVectChars (x :: xs) = case (x, toVectChars xs) of 
                              (Just v, Just vv) => Just (v :: vv)
                              _ => Nothing

toc: List Char -> Maybe (Vect 26 Char)
toc (a::b::c::d::e::f::g::h::i::j::k::l::m::n::o::p::q::r::s::t::u::v::w::x::y::z::[]) = Just [a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z]
toc _ = Nothing

toUpperChars: (l: List Char) -> Maybe (Vect 26 UpperChars)
toUpperChars cs = case (toc cs) of 
                      Just v => (toVectChars (mapToUChars v))
                      Nothing => Nothing

program: String -> Char -> Integer -> Maybe Nat
program cs topLetter pos = 
          case (toUpperChars (unpack cs), charToUChar topLetter) of 
                (Just wire, Just tl) => Just (mapFrom RightToLeft wire tl (integerToNat pos))
                _ => Nothing

