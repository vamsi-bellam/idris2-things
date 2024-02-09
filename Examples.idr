module Examples

||| Things from basic examples page

IntOrString: (isInt: Bool) -> Type

IntOrString True = Int 
IntOrString False = String 

showOrReverse: (isInt: Bool) -> IntOrString isInt -> String 
showOrReverse True x = show x
showOrReverse False x = reverse x 

main: IO ()
main = putStrLn (showOrReverse False "Hi")

||| Why is this not printing
main2: IO ()
main2 = putStrLn (showOrReverse True 23)


||| Basic primitive types


x: Int
x = 94

y: Int
y = if (x == 94) then 49 else 94

||| Nat already present in std lib prelude (which is by default imported in all idris files), 
||| so need to specify which one to use, otherwise throws error. 
data Nat = Z | S (Examples.Nat) 

add: Examples.Nat -> Examples.Nat -> Examples.Nat 
add Z y = y
add (S k) y = S (add k y)

natToNumbers: Examples.Nat -> Int 
natToNumbers Z = 0
natToNumbers (S k) =  1 + natToNumbers k
