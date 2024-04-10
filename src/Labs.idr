module Labs

-- Lab1 @ https://compose.ioc.ee/courses/2023/functional_programming/lab/lab_01.pdf

average : Integer -> Integer -> Integer
average i j = div (i + j) 2

small : Integer
small = 4

large : Integer
large = small * 6

medium : Integer 
medium = (average small large)

average' : Double -> Double -> Double 
average' i j = (i + j) / 2

-- Lab2 @ https://compose.ioc.ee/courses/2023/functional_programming/lab/lab_02.pdf

xor : Bool -> Bool -> Bool
xor True True = False 
xor False False = False 
xor False True = False 
xor True False = False 


data Prob = Definitely | Likely | Doubtful | Impossible

not : Prob -> Prob 
not Definitely = Impossible
not Likely = Doubtful
not Doubtful = Likely
not Impossible = Definitely

and : Prob -> Prob -> Prob
and _ Impossible = Impossible
and Impossible _ = Impossible
and Doubtful _ = Doubtful
and _ Doubtful = Doubtful
and Likely _ = Likely
and _ Likely = Likely
and Definitely Definitely = Definitely

mul : Nat -> Nat -> Nat
mul Z j = Z
mul (S Z) j = j
mul (S k) j = plus j (mul k j)

fact : Nat -> Nat 
fact Z = 1
fact x = x * (fact (minus x 1))

data Shape : Type where
  -- circle shape with given radius:
  Circle : (radius : Double) -> Shape
  -- rectangle shape with given width and height:
  Rectangle : (width : Double) -> (height : Double) -> Shape
  -- isosceles triangle shape with given base and height:
  IsosTriangle : (base : Double) -> (height : Double) -> Shape

area : Shape -> Double
area (Circle radius) = pi * radius * radius
area (Rectangle width height) = width * height
area (IsosTriangle base height) = (base * height) / 2
  
-- Lab3 @ https://compose.ioc.ee/courses/2023/functional_programming/lab/lab_03.pdf

swap_pair : Pair a b -> Pair b a
swap_pair (x, y) = (y, x)

swap_either : Either a b -> Either b a
swap_either (Left x) = Right x
swap_either (Right x) = Left x

reverse_list : List a -> List a
reverse_list [] = []
reverse_list (x :: xs) = reverse_list xs ++ [x]

data Tree : (a : Type) -> Type where
  -- a tree is either empty:
  Leaf : Tree a
  -- or it is a left subtree, a current element, and a right subtree:
  Node : (l : Tree a) -> (x : a) -> (r : Tree a) -> Tree a

size : Tree a -> Nat
size Leaf = 0
size (Node l x r) = plus 1 (plus (size l) (size r))

t1 : Tree Nat
t1 = Node (Node Leaf 1 (Node Leaf 3 Leaf)) 5 Leaf

n_to_lu : Nat -> List Unit
n_to_lu 0 = []
n_to_lu (S k) = () :: n_to_lu k


lu_to_n : List Unit -> Nat
lu_to_n [] = 0
lu_to_n (x :: xs) = S (lu_to_n xs)

-- Lab4 @ https://compose.ioc.ee/courses/2023/functional_programming/lab/lab_04.pdf

map_maybe : (a -> b) -> Maybe a -> Maybe b
map_maybe f Nothing = Nothing
map_maybe f (Just x) = Just (f x)

transform : (f : a -> a) -> (index : Nat) -> List a -> List a
transform f index [] = []
transform f 0 (x :: xs) = f x :: xs
transform f (S k) (x :: xs) = x :: (transform f k xs)


ignore_lowerCaseVowels : String -> String
ignore_lowerCaseVowels str = 
  let chs = (unpack str) 
      f_chs = List.filter (\x => not (elem x ['a', 'e', 'i', 'o', 'u'])) chs
  in 
  (foldl (\acc, ele => acc ++ (cast ele)) "" f_chs)

-- mult' : Nat -> Nat -> Nat
-- mult' m = foldl ?n ()

-- n_to_lu' : Nat -> List Unit 
-- n_to_lu' n = foldl (\acc, ele => () :: acc) [] n

lu_to_n' : List Unit -> Nat
lu_to_n' l = foldl (\acc, ele => S acc) Z l

-- continue after..