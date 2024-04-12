module Enigma

import Data.Vect
import Data.Fin

-- this is from contrib package, so need to add it to depends in .ipkg file or use -p contrib during compile time
import Data.Vect.Sort

import UpperChars


mapi : {0 n : Nat} -> (f : Nat -> a -> b) -> Vect n a -> Vect n b 
mapi f ls = mapiaux f ls 0 where 
              mapiaux: {0 n: Nat} -> (f: Nat -> a -> b) -> Vect n a -> Nat -> Vect n b 
              mapiaux f [] k = []
              mapiaux f (x :: xs) k = f k x :: mapiaux f xs (S k)
                  

WiringSpec : Type
WiringSpec = Vect 26 (Nat, Nat)

makeSpecMap : (wiring: Vect 26 UpperChars) -> WiringSpec
makeSpecMap wiring = mapi (\i, x => (i, toIndex x)) wiring

revSpecMap : WiringSpec -> WiringSpec
revSpecMap wiringSpec = (sortBy (\(x1, _), (x2, _) => compare x1 x2) 
                          (map (\(a, b) => (b, a)) wiringSpec))


at : Fin n -> Vect n (Nat, Nat) -> Nat 
at FZ ((_, x) :: xs) = x
at (FS k) (y :: xs) = at k xs



mod'' : (n : Nat) -> (m : Nat) -> {auto prf : GT m 0} -> (r : Nat ** LT r m)
mod'' n m = case (isLT n m) of 
              Yes p => (n ** p)
              No _ => (mod'' (minus n m) m)
                                      
-- mod' : (n : Nat) -> (m : Nat) -> {0 auto prf : GT m 0} -> Nat

-- mod'_correct : (n : Nat) -> (m : Nat) -> {0 auto prf : GT m 0} -> LT (mod' n m) m

-- mod : (n : Nat) -> (m : Nat) -> {0 auto prf : GT m 0} -> Nat
-- mod n m = fst mod''

-- mod_correct = snd mod''

data Mode = RightToLeft | LeftToRight

mapFrom : Mode -> (wiring: Vect 26 UpperChars) -> (topLetter: UpperChars) -> 
          Nat -> Nat
mapFrom mode wiring topLetter inputPos = 
  let specificationMap = makeSpecMap wiring
      topLetterIndex = toIndex topLetter
      forwardOffset: Nat -> Nat -> (r: Nat ** LT r 26) 
      forwardOffset offset input = mod'' (offset + input)  26
      inputContact = forwardOffset topLetterIndex inputPos
      backWardOffset:  Nat -> Nat -> Nat
      backWardOffset offset input = fst (mod'' (minus (26 + input) offset) 26)
      outputContact: Mode -> Nat
      outputContact mode = case mode of 
                            RightToLeft => at (natToFinLT (fst inputContact) 
                                              {prf= (snd inputContact)}) 
                                              specificationMap
                            LeftToRight => at (natToFinLT (fst inputContact) 
                                              {prf= (snd inputContact)}) 
                                              (revSpecMap specificationMap)
                                                        
  in backWardOffset topLetterIndex $ outputContact mode


mapRefl : (wiring : Vect 26 UpperChars) -> (pos : Nat) -> {auto prf : LT pos 26} 
          -> Nat
mapRefl wiring pos = at (natToFinLT pos) $ makeSpecMap wiring

mapPlug : Vect n (Nat, Nat) -> {auto prf : LTE n 13} -> 
          (l: Nat) -> Nat
mapPlug [] l = l
mapPlug  {n = S x} ((a, b) :: xs) l {prf = LTESucc k} =
  if l == a then b 
  else if l == b then a 
  else (mapPlug xs l {prf = lteSuccRight k})

Wiring: Type
Wiring = Vect 26 UpperChars

record Rotor where 
  constructor MkRotor
  wiring : Wiring
  turnover : UpperChars

record OrientedRotor where 
  constructor MkOrientedRotor
  rotor : Rotor 
  topLetter : UpperChars

record Config n where 
  constructor MkConfig
  refl : Wiring
  rotors : List OrientedRotor
  plugBoard : Vect n (UpperChars, UpperChars)


mapRotorsFrom: Mode -> List OrientedRotor -> Nat -> Nat 
mapRotorsFrom mode rotors inputPos = 
  case mode of 
    RightToLeft => foldr (\(MkOrientedRotor rotor topLetter), 
      acc => (mapFrom RightToLeft rotor.wiring topLetter acc)) inputPos rotors
    LeftToRight => foldl (\acc, (MkOrientedRotor rotor topLetter) => 
      (mapFrom LeftToRight rotor.wiring topLetter acc)) inputPos rotors
  

cipherChar : {n: Nat} -> Config n -> {auto prf : LTE n 13} -> UpperChars -> UpperChars
cipherChar (MkConfig refl rotors plugBoard) ch = 
  let plugs = map (\(a, b) => (toIndex a , toIndex b)) plugBoard in 
    indexToUpperChars (mapPlug plugs
        (mapRotorsFrom LeftToRight rotors 
          (mapRefl refl (mapRotorsFrom RightToLeft rotors (mapPlug plugs (toIndex ch))))))


mapToUpperChars : Vect n Char -> Vect n (Maybe UpperChars)
mapToUpperChars [] = []
mapToUpperChars (x :: xs) = (charToUpperChars x) :: (mapToUpperChars xs)

toVectUpperChars : Vect n (Maybe UpperChars) -> Maybe (Vect n UpperChars)
toVectUpperChars [] = Just []
toVectUpperChars (x :: xs) = case (x, toVectUpperChars xs) of 
                                (Just v, Just vv) => Just (v :: vv)
                                _ => Nothing

-- use fromList of vect, and prove Length lis = 26 using boolean comparision
toVectChar : List Char -> Maybe (Vect 26 Char)
toVectChar (a::b::c::d::e::f::g::h::i::j::k::l::m::n::o::p::q::r::s::t::u::v::w::x::y::z::[]) 
  = Just [a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z]
toVectChar _ = Nothing

toUpperChars : (l : List Char) -> Maybe (Vect 26 UpperChars)
toUpperChars cs = case (toVectChar cs) of 
                    Just v => (toVectUpperChars (mapToUpperChars v))
                    Nothing => Nothing

program : String -> Char -> Integer -> Maybe Nat
program cs topLetter pos = 
          case (toUpperChars (unpack cs), charToUpperChars topLetter) of 
            (Just wire, Just tl) => Just (mapFrom RightToLeft wire tl (integerToNat pos))
            _ => Nothing

main : IO ()
main = putStrLn ("Welcome to E Machine!!")

-- at end try te cipher char property proof
