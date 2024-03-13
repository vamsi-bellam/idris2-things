-- module src.Examples is giving error, how to name nested modules
module Examples
import Data.Fin
import Data.Vect
import System.File

-- Things from basic examples page

-- we can give names to types like `isInt`
IntOrString: (isInt: Bool) -> Type

IntOrString True = Int 
IntOrString False = String 

-- Type of the below function changes depends on the argument isInt 
-- if isInt is True, then signature is like (Int -> String) else (String -> String)
showOrReverse: (isInt: Bool) -> IntOrString isInt -> String 
showOrReverse True x = show x
showOrReverse False x = reverse x 

-- main: IO ()
-- main = putStrLn (showOrReverse False "Hi")

-- -- Why is this not printing
-- main2: IO ()
-- main2 = putStrLn (showOrReverse True 23)


-- Basic primitive types


x: Int
x = 94

y: Int
y = if (x == 94) then 49 else 94

-- Nat already present in std lib prelude (which is by default imported in all idris files), 
-- so need to specify which one to use, otherwise throws error. 
-- data Nat = Z | S (Examples.Nat) 

add: Nat -> Nat -> Nat 
add Z y = y
add (S k) y = S (add k y)

natToNumbers: Nat -> Int 
natToNumbers Z = 0
natToNumbers (S k) =  1 + natToNumbers k

-- reverse : List a -> List a
-- reverse xs = reverseAcc [] xs where
--   reverseAcc : List a -> List a -> List a 
--   reverseAcc acc [] = acc
--   reverseAcc acc (x :: xs) = reverseAcc (x :: acc) xs 

-- An alternative using let 

reverse' : List a -> List a
reverse' xs = let reverseAcc' : List a -> List a -> List a 
                  reverseAcc' acc [] = acc
                  reverseAcc' acc (x :: xs) = reverseAcc' (x :: acc) xs 
              in reverseAcc' [] xs

-- even: Int -> Bool
-- even 0 = True
-- even n = odd (n-1) where
--   odd: Int -> Bool
--   odd 0 = False
--   odd n = even (n-1)

-- above thing can also be done with "mutual"

mutual 
  even: Int -> Bool
  even 0 = True
  even n = odd (n-1) 

  odd: Int -> Bool
  odd 0 = False
  odd n = even (n-1)


-- Dependent types 

isSingleton: Bool -> Type 
isSingleton True = Nat
isSingleton False = List Nat

mkSingle: (x: Bool) -> isSingleton x
mkSingle True = Z
mkSingle False = []


-- Vectors

-- data Vect: Int -> Type -> Type where
--   Nil: Vect 0 a
--   (::) : a -> Vect k a -> Vect (1 + k) a

-- (++) : Examples.Vect n a -> Examples.Vect m a -> Examples.Vect (n + m) a
-- (++) Nil       ys = ys
-- (++) (x :: xs) ys = x :: xs ++ ys



index: Fin n -> Vect n Int  -> Int
index FZ (x :: xs) = x
index (FS k) (x :: xs) = index k xs 

vects: Vect 5 Int
vects =  1 :: 2 :: 3 :: 4 :: 5 :: Nil

first: Int 
first = (index (FS 2)  vects)


greet: IO ()
greet = do putStrLn "What is your name"
           name <-  getLine 
           putStrLn ("Hello, " ++ name)

-- Only one main , naturally entrypoint of program
main: IO ()
main = putStrLn ((show first))


IfThenElse: Bool -> a -> a -> a 
IfThenElse True t e = t
IfThenElse False t e = e

task1: IO ()
task1 = (putStrLn "I am true block")

task2: IO ()
task2 = (putStrLn "I am false block")

-- Expecting both to print, but not happening => ans: IO itself is Lazy
oneOfTwo: Bool -> IO ()
oneOfTwo b = (IfThenElse b task1 task2)

-- Streams 

ones: Stream Int 
ones = 1 :: ones

makeUpTo: Int -> Stream Int -> List Int

makeUpTo 0 l = []
makeUpTo n (x :: xs) = x :: (makeUpTo (n-1) xs) 

-- Snoc lists

firstThree: SnocList Int 
firstThree = Lin :< 1 :< 2 :< 3

doubleOfThree: SnocList Int 
doubleOfThree = (mapMaybe (\x => Just (x*2)) firstThree)

printSnocList: SnocList Int -> IO ()
printSnocList Lin = putStrLn "End of list"
printSnocList (xs :< x) = do (putStrLn (show x))
                             (printSnocList xs)


highestScores: List (String, Int)
highestScores = [("ODI", 264), ("TEST", 400), ("T20I", 175)]

printHighestScore: List (String, Int) -> IO () 
printHighestScore [] = putStrLn  "End of List"
printHighestScore ((match, score) :: xs) = do (putStrLn ("Highest score in " ++ match ++ " is " ++ (show score)))
                                              printHighestScore xs

record Ranking where
    constructor MkRanking 
    odi, test, t20 : Int

data Role = Batter | Bowler | Allrounder

record Player where 
    constructor MkPlayer 
    firstName, lastName, country : String   
    ranking: Ranking
    age: Int
    role: Role


player1: Player 
player1 = (MkPlayer "Rohit" "Sharma" "India" ((MkRanking 2 5 9)) 36 Batter)

-- flip : (a -> b -> c) -> b -> a -> c
-- flip f x y = f y x

-- Expected age to have 33, but getting -33
player2: Player
player2 = {firstName := "Surya", lastName := "Yadav", ranking := (MkRanking  3 6 1), age $= flip (-) 3} player1

-- List comprehensions
pythag: Int -> List (Int, Int, Int)
pythag n = [ (x, y, z) | z <- [1..n], y <- [1..n], x <- [1..n], x*x + y*y == z*z ]

showRole: Role -> IO ()
showRole role = case role of 
                    Batter => putStrLn "Batter"
                    Bowler => putStrLn "Bowler"
                    Allrounder => (putStr "Allrounder")

interface Show' a where 
    show' : a -> String 




Show' Nat where
    show' Z = "Z"
    show' (S k) = "S" ++ (show' k)

-- Int inplace of Integer not working, also negative integers having some different type: Because of idris2 type inference
Show' Integer where 
    show' x = show x

showList: Show' a => List a -> String 
showList ls = "[" ++ showListHelper ls ++ "]" where 
    showListHelper: List a -> String
    showListHelper [] = ""
    showListHelper (hd :: tl) = let rest = (showListHelper tl) in 
                                if rest == "" then (show' hd) else ((show' hd) ++ "," ++ rest)

-- Extending interfaces 

interface Eq' a where
    (==) : a -> a -> Bool
    (/=) : a -> a -> Bool

    x /= y = not (x == y)
    x == y = not (x /= y)



data Ordering' = EQ | LT | GT 

-- Not implemented Eq' for Integer, hence taking the implementation from Prelude
interface Eq a => Ord' a where 
    compare: a -> a -> Ordering'


Ord' Integer where
     compare f s = if f > s then GT else if f < s then LT else EQ


intToNat: Nat -> Integer 
intToNat Z = 0 
intToNat (S k) = 1 + intToNat k


splitHalf: List a -> (List a , List a)
splitHalf ls = splitHelper ls [] [] ((div (intToNat (length ls)) 2)) where
    splitHelper: List a -> List a -> List a -> Integer -> (List a, List a)
    splitHelper [] first second _ = (reverse first, reverse second)
    splitHelper (hd :: tl) first second count = if count == 0 then splitHelper tl first (hd :: second) count 
                                                 else splitHelper tl (hd :: first) second (count - 1)

merge': (Ord' a) => List a -> List a -> List a 
merge' [] [] = []
merge' [] s = s 
merge' f [] = f 
-- @ is like "as" in Ocaml
merge' f@(hd1 :: tl1) s@(hd2 :: tl2) = case (compare hd1 hd2) of 
                                        -- below we have duplicated two lines, see if there is better like in Ocaml "|"
                                        EQ => (hd1 :: hd2 :: (merge' tl1 tl2))
                                        LT => (hd1 :: (merge' tl1 s))
                                        GT => (hd2 :: (merge' f tl2))


sort': Ord' a => List a -> List a
sort' [] = []
sort' [s] = [s]
sort' ls = let (firstHalf, secondHalf) = (splitHalf ls) in 
          (merge' (sort' firstHalf) (sort' secondHalf))

showAndSort: (Ord' a, Show' a) => List a -> String 
showAndSort ls = (showList (sort' ls))


-- Implementing Show' interface for List won't becauuse, List is function, but Show' interface just takes a single type 'a'


-- What is the use of this? who can use/implement this?
interface X where
    print: Int -> String



-- Functor
interface Functor' (f : Type -> Type) where 
    map': (a -> b) -> f a -> f b

Functor' List where
  map' f []      = []
  map' f (x :: xs) = f x :: map' f xs

interface Functor' f => Applicative' (0 f : Type -> Type) where 
    pure': a -> f a

-- Not working as expected, expected it to list value a to [a]
Applicative' List where
    pure' x = [x]


interface Applicative' f => Monad' (0 f: Type -> Type) where 
    (>>=): f a -> (a -> f b) -> f b 

data Option a = Nothing | Just a

Functor' Option where 
    map' f Nothing = Nothing
    map' f (Just x) = Just (f x)

Applicative' Option where 
    pure' = Just

Monad' Option where 
    Nothing >>= k = Nothing 
    (Just x) >>= k = k x


optAdd: Option Int -> Option Int -> Option Int 
-- optAdd x y = do x' <- x 
--                 y' <- y 
--                 pure' (x' +  y')
-- !e, an alternate syntax for do notationm where it evaluates and implicitly binds it
optAdd x y = (pure' (!x + !y))


-- Multiplicities 

-- 
append': Vect n a -> Vect m a -> Vect (n + m) a
append' xs ys = ?append_arg


duplicate: (1 x : a) -> (a, a)
-- This should not give error as per doc, bu getting error
-- duplicate x = (x, ?help)


data Lin : Type -> Type where 
    MkLin: (1 _ : a) -> Lin a 

data Unr : Type -> Type where
    MkUnr: a -> Unr a

getLin: (1 _ : Lin a) -> a 
getLin (MkLin x) = ?getLin_rhs_0

getUnt: (1 _: Unr a) -> a 
getUnt (MkUnr x) = ?gu

data DoorState = Open | Closed

data Door : DoorState -> Type where
     MkDoor : (doorId : Int) -> Door st

openDoor: (1 d: Door Closed) -> Door Open

closeDoor: (1 d: Door Open) -> Door Closed

id': Type -> Type
id' x = x



-- This is an ideal type signature, if given a vector and returns length of vector
-- Side Note: 2 is an Integer, but return type is Nat, still no error?
vlen: Vect n a -> Nat 
vlen xs = 2

-- This is where you are expecting the n as argument to function
vlen': (n : Nat) -> Vect n a -> Nat
vlen' n xs = n

-- Using curly braces means, you can stating that n (that appears in Vect) needed for usage at runtime
vlen'': {n : Nat} -> Vect n a -> Nat 
vlen'' xs = n

-- Same as above, but restircting the usage of n at runtime to 1 ( by default, its unlimited )
vlen''': {1 n : Nat} -> Vect n a -> Nat 
vlen''' xs = n


sample: Vect (S Z) Integer 
sample = 2 :: Nil


-- Pattern matching on Types 

showType: Type -> String 
showType Int = "Int"
showType String = "String"
showType (Nat -> a) = ?help
-- This gives error?
-- showType (Nat -> Integer -> a) = ?help2
showType _ = "Others"

-- Theorem Proving

data EqualNat: Nat -> Nat -> Type where 
    SameNat: (n: Nat) -> EqualNat n n 

-- Eventhough I have given type Nat, I am able to pass Int
twoEqualsTwo: EqualNat (1+1) 2
twoEqualsTwo = SameNat 2

data Equal': a -> b -> Type where
   -- using x in place of a showing shadowing wraning
    Refl': Equal' a a

twoPlusTwoBad: (Equal' (2+2) 4)
twoPlusTwoBad = Refl'

notTrue: Equal' (2+3) 6 -> Void 
notTrue Refl' impossible

checkEqNat: (m: Nat) -> (n: Nat) -> Maybe (Equal' m n)
checkEqNat Z  Z = Just Refl'
checkEqNat (S k)  Z = Nothing
checkEqNat Z  (S k) = Nothing
-- Just adding this `(checkEqNat k j)` won't work, 
-- becuase we want (S k) = (S j), but `(checkEqNat k j)` gives k = j
checkEqNat (S k)  (S j) = case (checkEqNat k j) of
                               Nothing => Nothing
                               -- in left Refl' is Refl' x, in right it is Refl' (S x)
                               (Just Refl') => Just Refl'



-- About with?
-- ** is for dependent types, where one value depends on other
filter': ( a -> Bool) -> Vect n a -> (p ** Vect p a)
filter' p [] = (_ ** [])
filter' p (x :: xs) with (filter' p xs)
    filter' p (x :: xs) | (_ ** xs') = if (p x) then (_ ** x :: xs') else (_ ** xs')





plusReducesR : (n:Nat) -> plus n Z = n
plusReducesR 0 = Refl
plusReducesR (S k) = cong S (plusReducesR k)
