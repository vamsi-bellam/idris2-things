module Enigma 
import Data.Vect
import Data.Fin
-- TODO: Figure out why import Data.Vect.Sort not working from stdlib
-- For now, copied the module to local from official lib folder
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

makeSpecMap: (wiring: Vect 26 UpperChars) -> WiringSpec
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
                                      RightToLeft => at (natToFinLT (fst inputContact) 
                                                        {prf= (snd inputContact)}) 
                                                        specificationMap
                                      LeftToRight => at (natToFinLT (fst inputContact) 
                                                        {prf= (snd inputContact)}) 
                                                        (revSpecMap specificationMap)
                                                        
        in backWardOffset topLetterIndex $ outputContact mode


mapRefl: (wiring: Vect 26 UpperChars) -> (pos: Nat) -> {auto prf: LT pos 26} -> Nat
mapRefl wiring pos = at (natToFinLT pos) $ makeSpecMap wiring


charToUpperChars : Char -> Maybe UpperChars
charToUpperChars 'A' = Just A
charToUpperChars 'B' = Just B
charToUpperChars 'C' = Just C
charToUpperChars 'D' = Just D
charToUpperChars 'E' = Just E
charToUpperChars 'F' = Just F
charToUpperChars 'G' = Just G
charToUpperChars 'H' = Just H
charToUpperChars 'I' = Just I
charToUpperChars 'J' = Just J
charToUpperChars 'K' = Just K
charToUpperChars 'L' = Just L
charToUpperChars 'M' = Just M
charToUpperChars 'N' = Just N
charToUpperChars 'O' = Just O
charToUpperChars 'P' = Just P
charToUpperChars 'Q' = Just Q
charToUpperChars 'R' = Just R
charToUpperChars 'S' = Just S
charToUpperChars 'T' = Just T
charToUpperChars 'U' = Just U
charToUpperChars 'V' = Just V
charToUpperChars 'W' = Just W
charToUpperChars 'X' = Just X
charToUpperChars 'Y' = Just Y
charToUpperChars 'Z' = Just Z
charToUpperChars _   = Nothing


mapToUpperChars: Vect n Char -> Vect n (Maybe UpperChars)
mapToUpperChars [] = []
mapToUpperChars (x :: xs) = (charToUpperChars x) :: (mapToUpperChars xs)

toVectUpperChars: Vect n (Maybe UpperChars) -> Maybe (Vect n UpperChars)
toVectUpperChars [] = Just []
toVectUpperChars (x :: xs) = case (x, toVectUpperChars xs) of 
                              (Just v, Just vv) => Just (v :: vv)
                              _ => Nothing

toVectChar: List Char -> Maybe (Vect 26 Char)
toVectChar (a::b::c::d::e::f::g::h::i::j::k::l::m::n::o::p::q::r::s::t::u::v::w::x::y::z::[]) 
        = Just [a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z]
toVectChar _ = Nothing

toUpperChars: (l: List Char) -> Maybe (Vect 26 UpperChars)
toUpperChars cs = case (toVectChar cs) of 
                        Just v => (toVectUpperChars (mapToUpperChars v))
                        Nothing => Nothing

program: String -> Char -> Integer -> Maybe Nat
program cs topLetter pos = 
          case (toUpperChars (unpack cs), charToUpperChars topLetter) of 
                (Just wire, Just tl) => Just (mapFrom RightToLeft wire tl (integerToNat pos))
                _ => Nothing

main: IO ()
main = putStrLn ("Welcome to E Machine!!")

-- Read STDLIB of NAT, FIn and some others to understand proofs and style