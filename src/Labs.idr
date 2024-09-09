module Labs
import Data.List
import Data.Colist
import Data.String
import System.File
import Data.Fin 
import Data.Vect
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
xor False True = True 
xor True False = True 


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
      -- Need this explicit type def to avoid amiguity with colist
      vowels : List Char
      vowels = ['a', 'e', 'i', 'o', 'u']
      f_chs = List.filter (\x => not (elem x vowels)) chs
  in 
  (foldl (\acc, ele => acc ++ (cast ele)) "" f_chs)


-- (a : t) and (t -> t) are constructor replacing terms
fold_nat : (a : t) -> (t -> t) -> Nat -> t
fold_nat a f Z = a
fold_nat a f (S k) = f (fold_nat a f k)

mult' : Nat -> Nat -> Nat
mult' m n = (fold_nat Z (\acc => plus n acc) m)

n_to_lu' : Nat -> List Unit 
n_to_lu' n = fold_nat [] (\acc => () :: acc) n

lu_to_n' : List Unit -> Nat
lu_to_n' l = foldl (\acc, ele => S acc) Z l

-- clever one, I couldn't get it.. :( (got solution from lecture5 video)
fold_bool : t -> t -> Bool -> t
fold_bool a f False = f
fold_bool a f True = a

-- Lab5 @ https://compose.ioc.ee/courses/2023/functional_programming/lab/lab_05.pdf

Show Shape where 
  show (Circle radius) = "Circle with radius " ++ show radius
  show (Rectangle width height) = "Rectangle with width " ++ show width ++ 
                                  " and height " ++ show height
  show (IsosTriangle base height) = "Triangle with base "  ++ show base ++ 
                                    " and height "++ show height

implementation [ setwise ] Eq a => Eq ( List a ) where
  x == y = (all (\n => (elem n y)) x) &&
           (all (\n => (elem n x)) y)                     


-- There are three ways to write interface
-- Just with name, or with interface keyword or implementation keyword?
-- Clarity: interface for declaring and implementation for implementing a declared interface

-- Take a look at PreOrder problem later

interface Preorder' a where 
  f : a -> a -> Bool

implementation [ divides ] Preorder' Integer where 
  f n m = mod n m == 0

data AExpr : Num n => Type -> Type where
  V : n -> AExpr n
  Plus : AExpr n -> AExpr n -> AExpr n
  Times : AExpr n -> AExpr n -> AExpr n

eval : Num n => AExpr n -> n
eval (V x) = x
eval (Plus x y) = eval x + eval y
eval (Times x y) = eval x * eval y

implementation Num n => Eq n => Eq (AExpr n) where
  (==) x y = eval x == eval y

implementation Num a => Ord a => Eq (AExpr a) => Ord (AExpr a) where 
  x < y = eval x < eval y

implementation Cast Integer Bool where 
  cast 0 = False 
  cast _ = True

-- This is a lossy cast as True casts to 1 but it could be any +ve number
implementation Cast Bool Integer where 
  cast False = 0 
  cast True = 1

-- Lab6 @ https://compose.ioc.ee/courses/2023/functional_programming/lab/lab_06.pdf

-- It implicity converting to ot via type def

coL : List a -> Colist a
coL [] = []
coL (x :: xs) = x :: coL xs

uncoL : Colist a -> List a
uncoL [] = []
uncoL (x :: y) = x :: (uncoL y)
-- can be also written as below, but Delay is implcitly infereed in left and 
-- added in right while constructing colist
-- uncoL (x :: (Delay xs)) = x :: (uncoL xs)

data  Conat : Type  where
	Zero  :  Conat
	Succ  :  Inf Conat -> Conat

length : Colist a -> Conat
length [] = Zero
length (x :: y) = Succ (length y)

filter : (a -> Bool) -> Colist a -> Colist a
filter f [] = []
filter f (x :: xs) = if f x then x :: (filter f xs) else filter f xs

unroll : (a -> a) -> a -> Stream a
unroll f x = let v = f x in v :: unroll f v

zipSL : (a -> b -> c) -> Stream a -> List b -> List c
zipSL f _ [] = []
zipSL f (x :: xs) (y :: ys) = f x y :: zipSL f xs ys


-- coN, uncoN and add defs taken from lecture video to implement mulC
coN  :  Nat -> Conat
coN Z  =  Zero
coN (S n)  =  Succ (coN n)

uncoN  :  Conat -> Nat
uncoN Zero  =  Z
uncoN (Succ n)  =  S (uncoN n)

add : Conat -> Conat -> Conat
add Zero n  =  n
add (Succ m) n  =  Succ (add m n)

mulC : Conat -> Conat -> Conat
mulC Zero Zero = Zero
mulC Zero (Succ x) = Zero
mulC (Succ x) Zero = Zero
mulC (Succ x) (Succ y) = add (Succ y) (mulC x (Succ y))

infinity : Conat
infinity = Succ infinity

implementation Num Conat where 
  (+) = add 
  (*) = mulC 
  fromInteger = coN . fromInteger

-- Lab7 @ https://compose.ioc.ee/courses/2023/functional_programming/lab/lab_07.pdf

concat_strings : IO String
concat_strings = putStrLn "Please enter the first sentence :" >>= 
                 \_ => getLine >>= 
                 \s1 => putStrLn "Please enter the first sentence :" >>= 
                 \_ => getLine >>= 
                 \s2 => pure (s1 ++ " " ++ s2)

-- do syntanx version
concat_strings' : IO String
concat_strings' = do 
                    putStrLn "Please enter the first sentence :"
                    s1 <- getLine 
                    putStrLn "Please enter the first sentence :" 
                    s2 <- getLine 
                    pure (s1 ++ " " ++  s2)
      

add_after : Integer -> IO ( Maybe Integer )
add_after x = do 
                putStrLn "Please enter a number :"
                x1 <- getLine
                case (parseInteger x1) of 
                  Just n => pure (Just (x + n))
                  Nothing => pure Nothing
                
count_words : IO Unit
count_words = do 
                putStrLn "Enter some text :"
                text <- getLine
                putStrLn ("You typed " ++ cast(length(words text)) ++ " words")

get_lines : IO ( List String )
get_lines = do 
              putStrLn "Please enter a sentence :"
              s <- getLine 
              if s == "done" then pure [] else 
                do 
                  rest <- get_lines
                  pure (s :: rest)

get_only_ints : IO ( List Integer )
get_only_ints = do 
                  putStrLn "Please enter an integer or \"done\":"
                  s <- getLine 
                  if s == "done" then pure [] else 
                    do 
                      case (parseInteger s) of 
                        Just num =>
                          do 
                            rest <- get_only_ints 
                            pure (num :: rest)
                        Nothing => get_only_ints


-- compile in the repl using :c <executable_name> <function_name> and then 
-- go to build/exec folder and create txt file and run ./<executable_name>
dictate : IO ()
dictate = do 
            sentences <- get_lines
            putStrLn "Enter the location :"
            loc <- getLine
            file <- (openFile loc ReadWrite)
            case file of 
              Left err => putStrLn "Failed to write to file ."
              Right hand => do 
                              conts <- writeFile loc (unwords sentences)
                              closeFile hand
                              case conts of 
                                Left err => putStrLn "Failed to write to file ."
                                Right res => pure res

-- Lab8 @ https://compose.ioc.ee/courses/2023/functional_programming/lab/lab_08.pdf


implementation Semigroup Bool where
  (<+>) = xor

implementation Monoid Bool where
  neutral = False


-- comp : (b -> c) -> (a -> b) -> a -> c
-- comp f g x = f (g x)

implementation Semigroup (a -> a) where
  f <+> g = f . g



implementation Monoid (a -> a) where 
  neutral = (\x => x)

multiply : Monoid a => Nat -> a -> a
multiply 0 x = neutral
multiply (S Z) x = x 
multiply (S k) x = x <+> (multiply k x)

consolidate : List (Maybe a) -> Maybe (List a)
consolidate [] = Just []
consolidate (x :: xs) = case (x, consolidate xs) of 
                          (Just x, Just y) => Just (x :: y)
                          (_, _) => Nothing

consolidate' : List (Maybe a) -> Maybe (List a)
consolidate' [] = Just []
consolidate' (Nothing :: xs) = Nothing
consolidate' ((Just x) :: xs) = map (x ::) (consolidate' xs)

map1 : Applicative t => (a -> b) -> t a -> t b
map1 f x = pure f <*> x

map0 : Applicative t => b -> t b
map0 f = pure f

map3 : Applicative t => (a -> b -> c -> d) -> t a -> t b -> t c -> t d
map3 f x y z = pure f <*> x <*> y <*> z 

join_list : List (List a) -> List a
join_list ls = join ls

-- Lab9 @ https://compose.ioc.ee/courses/2023/functional_programming/lab/lab_09.pdf 

bool_2_fin : Bool -> Fin 2
bool_2_fin False = FZ
bool_2_fin True = FS FZ

fin_2_bool : Fin 2 -> Bool 
fin_2_bool FZ = False
fin_2_bool (FS FZ) = True

map_vect : (a -> b) -> Vect n a -> Vect n b 
map_vect f [] = []
map_vect f (x :: xs) = f x :: map_vect f xs

as_top : (n : Nat) -> Fin (S n)
as_top 0 = FZ
as_top (S k) = FS (as_top k)


data Tuple : Vect n a -> Type where 
  Nil : Tuple []
  (::) : t -> Tuple ts -> Tuple (t :: ts)

two_tuple : Pair a b -> Tuple [a, b]
two_tuple x = [fst x, snd x]

ind_pair : Pair a b -> DPair a (\_ => b)
ind_pair x = (fst x ** snd x)


forget_length : Vect n a -> List a 
forget_length [] = []
forget_length (x :: xs) = x :: forget_length xs

learn_length : (xs : List a) -> Vect (length xs) a
learn_length [] = []
learn_length (x :: xs) = x :: learn_length xs

-- Lab10 @ https://compose.ioc.ee/courses/2023/functional_programming/lab/lab_10.pdf 

ary_op  :  Nat -> Type -> Type
ary_op Z a  =  a
ary_op (S n) a  =  a -> ary_op n a

majority3 : 3 `ary_op` Bool 
majority3 x y z = if x then y || z else y && z

list_majority : List Bool -> Bool
list_majority xs = list_majority' 0 xs where 
  list_majority' : Int -> List Bool -> Bool 
  list_majority' acc [] = acc >= 0
  list_majority' acc (x :: xs) = if x then list_majority' (acc + 1) xs 
                                else list_majority' (acc - 1) xs


infixr 6 >->
(>->) : (args : Vect n Type) -> (result : Type) -> Type
(>->) [] result = result
(>->) (x :: xs) result = x -> ( xs >-> result)



seven : [] >-> Nat
seven = 7

idty : [a] >-> a
idty x = x

compose : [(a -> b) , (b -> c)] >-> (a -> c)
compose f g x = g (f x)

mkLisTypes : (n : Nat) -> a -> Vect n a
mkLisTypes 0 a = []
mkLisTypes (S k) a = a :: mkLisTypes k a

ary_opp : (n : Nat) -> Type -> Type
n `ary_opp` a = (mkLisTypes n a) >-> a


addZeroRight : (n : Nat) -> n + 0 = n
addZeroRight 0 = Refl
addZeroRight (S k) = cong S (addZeroRight k)


weakened_by : Fin m -> (n : Nat) -> Fin (m + n)
weakened_by x 0 = rewrite addZeroRight m in x
weakened_by x (S k) = rewrite sym (plusSuccRightSucc m k) in FS (weakened_by x k)


-- as_fin : Nat -> (b : Nat) -> Maybe (Fin b)
-- as_fin k b = if k == b then Nothing else Just (as_top k)


-- Lab11 @ https://compose.ioc.ee/courses/2023/functional_programming/lab/lab_11.pdf 

data ( <=) : ( p : Nat ) -> ( n : Nat ) -> Type where
  LeZ : 0 <= n
  LeS : p <= n -> S p <= S n

leTrans : m <= n -> n <= p -> m <= p
leTrans LeZ y = LeZ
leTrans (LeS x) (LeS y) = LeS (leTrans x y)


lessS : (n : Nat) -> n <= S n 
lessS 0 = LeZ
lessS (S k) = LeS (lessS k)


leWeakRight : (m , n : Nat ) -> m <= n -> m <= S n
leWeakRight 0 n LeZ = LeZ
leWeakRight (S p) (S n) (LeS x) = LeS (leWeakRight p n x)


leWeakLeft : (m , n : Nat ) -> S m <= n -> m <= n
leWeakLeft 0 (S k) (LeS x) = LeZ
leWeakLeft (S j) (S k) (LeS x) = LeS (leWeakLeft j k x)


zeroPlusRight : (m , n : Nat ) -> m + 0 <= m + n
zeroPlusRight 0 n = LeZ
zeroPlusRight (S k) n = LeS (zeroPlusRight k n)

less : (n : Nat) -> n <= n
less 0 = LeZ
less (S k) = LeS (less k)

zeroPlusLeft : (m , n : Nat ) -> 0 + n <= m + n
zeroPlusLeft 0 n = less n
zeroPlusLeft (S k) 0 = LeZ
zeroPlusLeft (S k) (S j) = LeS (leTrans (lessS j) (zeroPlusLeft k (S j)))


succPlusRight : (m , n : Nat ) -> m + n <= m + S n
succPlusRight 0 n = lessS n
succPlusRight (S k) n = LeS (succPlusRight k n)


succPlusLeft : (m , n : Nat ) -> m + n <= S m + n
succPlusLeft 0 n = lessS n
succPlusLeft (S k) n = LeS (succPlusLeft k n)


lisLength : (xs, ys : List a) -> length xs <= length ys -> 
            length (x :: xs) <= length (x :: ys)
lisLength xs ys p = LeS p


data IsPrefix : ( xs : List a ) -> ( ys : List a ) -> Type where
  IsPrefixNil : IsPrefix [] ys
  IsPrefixCons : IsPrefix xs ys -> IsPrefix ( z :: xs ) ( z :: ys )

prefixLen : IsPrefix xs ys -> length xs <= length ys
prefixLen IsPrefixNil = LeZ
prefixLen (IsPrefixCons x) = LeS (prefixLen x)


induction : ( prop : Nat -> Type ) ->
  ( base_case : prop 0) ->
  ( induction_step : ( k : Nat ) -> prop k -> prop ( S k ) ) ->
  ( n : Nat ) -> prop n

lisInd : (prop : List a -> Type) -> 
  ( base_case : prop [] ) ->
  ( induction_step : (x : a) -> (xs : List a) -> prop xs -> prop (x :: xs) ) -> 
  ( ys : List a ) -> prop ys
lisInd prop base_case induction_step [] = base_case
lisInd prop base_case induction_step (y :: xs) = 
  induction_step y xs (lisInd prop base_case induction_step xs)

  


-- lisProp : (x : a) -> (xs : List a) -> length xs <= length (x :: xs)
-- lisProp x [] = LeZ
-- lisProp x ys = lisInd (\ n => length n <= length (x :: n)) (lisProp x []) lisIndStep ys where 
--   lisIndStep : (x : a) -> (xs : List a) -> length xs <= length (y :: xs) -> length (x :: xs) <= length (y :: (x :: xs))
--   lisIndStep x xs z = ?lisIndStep_rhs

-- Lab12 @ https://compose.ioc.ee/courses/2023/functional_programming/lab/lab_12.pdf 

-- defs for logic
And : Type -> Type -> Type
And = Pair

Or : Type -> Type -> Type
Or = Either


Implies : Type -> Type -> Type
Implies a b = a -> b

Exists : ( t : Type ) -> ( p : t -> Type ) -> Type
Exists = DPair

Forall : ( t : Type ) -> ( p : t -> Type ) -> Type
Forall t p = ( x : t ) -> p x


and_comm : And p q -> And q p
and_comm (x, y) = (y, x)


and_assoc : ( p `And ` q ) `And ` r -> p `And ` ( q `And ` r )
and_assoc ((x, z), y) = (x, (z, y))

or_comm : Or p q -> Or q p
or_comm (Left x) = Right x
or_comm (Right y) = Left y

and_distr : p `And ` ( q `Or ` r ) -> ( p `And ` q ) `Or ` ( p `And ` r )
and_distr (x, (Left y)) = Left (x, y)
and_distr (x, (Right y)) = Right (x, y)

modus_ponens : ( ( a ` Implies ` b ) `And ` a )-> b
modus_ponens (x, y) = x y


-- type interp (a, b) -> c , a -> b -> c
implies_implies : ( a `And ` b ) ` Implies ` c -> a ` Implies ` ( b ` Implies ` c )
implies_implies f = \x => \y => f (x, y)


implies_and : a ` Implies ` ( b `And ` c ) -> ( a ` Implies ` b ) `And ` ( a ` Implies ` c )
implies_and f = (\arg => fst (f arg), \arg => snd (f arg))

or_implies : ( a ` Implies ` c ) `And ` ( b ` Implies ` c ) -> ( a `Or ` b ) ` Implies ` c
or_implies x (Left a) = fst x a
or_implies x (Right b) = snd x b

contraposition : a ` Implies ` b -> Not b ` Implies ` Not a
contraposition f g = g . f


double_negation_intro : a -> Not ( Not a )
double_negation_intro x f = f x

-- converse of above proposition
cdni : Not ( Not a) -> a 
-- not provable
cdni f = ?cdni_rhs

triple_negation_elim : Not ( Not ( Not a ) ) -> Not a
triple_negation_elim f x = f (\arg => arg x)

exist_and : Exists t (\ x => p x `And` q x ) `Implies` ( Exists t p `And` Exists t q )
exist_and (a ** b) = ((a ** fst b), (a ** snd b))

not_exists : Exists t p -> Not ( Forall t (\ x => Not ( p x ) ) )
not_exists (fst ** snd) = \f => f fst snd

exists_forall_then_forall_exists : { p : a -> b -> Type }
-> Exists a (\x => Forall b (\ y => p x y ) ) `Implies` Forall b (\ y => Exists a (\ x => p x y ) )
exists_forall_then_forall_exists (fst ** snd) = \arg => (fst ** snd arg)
