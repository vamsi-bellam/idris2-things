module Examples
import Data.Fin
import Data.Vect
import System.File

-- Things from basic examples page

IntOrString: (isInt: Bool) -> Type

IntOrString True = Int 
IntOrString False = String 

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

reverse : List a -> List a
reverse xs = reverseAcc [] xs where
  reverseAcc : List a -> List a -> List a 
  reverseAcc acc [] = acc
  reverseAcc acc (x :: xs) = reverseAcc (x :: acc) xs 


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

-- Expecting both to print, but not happening
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