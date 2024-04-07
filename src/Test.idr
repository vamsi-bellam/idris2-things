-- Just a test module to try out few things randomly
import Data.Vect 


-- Rewrite ruless

addZeroRight : (n : Nat) -> n + 0 = n
addZeroRight 0 = Refl
addZeroRight (S k) = cong S (addZeroRight k)

replaceVect : Vect (n + 0) a -> Vect n a
replaceVect xs = replace {p = \k => Vect k a} (addZeroRight n) xs

rewriteVect : Vect (n + 0) a -> Vect n a
rewriteVect as = rewrite sym (addZeroRight n) in as



-- Exercises 

plusSuccRightSucc': (left: Nat) -> (right: Nat) -> S (left + right) = left + S right
plusSuccRightSucc' 0 0 = Refl
plusSuccRightSucc' 0 (S k) = Refl
plusSuccRightSucc' (S k) 0 = cong S (plusSuccRightSucc' k 0)
plusSuccRightSucc' (S k) (S j) = cong S (plusSuccRightSucc' k (S j))

revOnto' : Vect m a -> Vect n a -> Vect (m + n) a
revOnto' xs []        = rewrite addZeroRight m in xs
revOnto' {n = S len} xs (x :: ys) =  rewrite sym (plusSuccRightSucc' m len) in revOnto' (x :: xs) ys


reverseVect' : Vect n a -> Vect n a
reverseVect' = revOnto' []

-- Proof that minus n n equals zero for all natural numbers n.
-- minus impl itself return 0 if second is large, so not sure whether proving that is actual proof
minus': (n: Nat) ->  (minus n n = 0)
minus' 0 = Refl
minus' (S k) = minus' k


iden: (n: Nat) -> (1 * n = n)
iden 0 = Refl
iden (S k) = cong S (iden k)



intrPrf: (m: Nat) -> (n: Nat) -> (m + S n = n + S m)
intrPrf 0 0 = Refl
intrPrf 0 (S k) = cong S (intrPrf 0 k)
intrPrf (S k) 0 = cong S (sym (intrPrf 0 k))
intrPrf (S k) (S j) = rewrite sym (plusSuccRightSucc' (S k) (S j)) in cong S (intrPrf (S k) j)

commut: (a: Nat) -> (b: Nat) -> ( a + b = b + a )
commut 0 0 = Refl
commut 0 (S k) = cong S (sym (addZeroRight k))
commut (S k) 0 = cong S (addZeroRight k)
commut (S k) (S j) = cong S (intrPrf k j)

mapAppend :  (f : a -> b)
          -> (xs : List a)
          -> (ys : List a)
          -> map f (xs ++ ys) = map f xs ++ map f ys
mapAppend f [] [] = Refl
mapAppend f [] (x :: xs) = Refl
mapAppend f (x :: xs) [] = ?mapAppend_rhs_2
mapAppend f (x :: xs) (y :: ys) = ?mapAppend_rhs_3
