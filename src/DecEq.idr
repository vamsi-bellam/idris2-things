module DecEq

data Tin = Sn 
data Copper = Cu

data Bronze: Type where 
    MkBronze: Tin -> Copper -> Bronze

data Equal': a -> b -> Type where 
    -- x is an implicit argument, we no need to provide while calling Refl
    Refl': {0 x: _} -> Equal' x x 

ex1: (Equal' 0 0)
-- {} is not necessary, idris can figure it out from type
ex1 = Refl' {x=0}

ex2: (Equal' 0 1)
ex2 = ?ex2_rhs

-- to hide the builtin things
%hide (===)
%hide Builtin.infix.(===)

infixl 6 ===

(===): a -> b -> Type
(===) = Equal'

ex1': 0 === 0
ex1' = Refl'

-- Although this seems correct, does it guarantee anything about values.. 
-- what if == is implemented incorrectly?
falseAttempt: ( 2 == 3) === False
falseAttempt =  Refl'

data Void': Type where 
-- No constructs, because we can't prove something false is true. 
-- Like we can't prove 1+1 = 3, we can just show 1+1 = 2.. 

data Dec': Type -> Type where 
    Yes: (prf: p) -> Dec' p
    No: (contra: p -> Void) -> Dec' p 

succNat: (m === n) -> (S m === S n)
succNat Refl' = Refl'

unSuccNat: (S m === S n) -> m === n
unSuccNat Refl' = Refl'


equalNats: (n: Nat) -> (m: Nat) -> (Dec' (n === m))
equalNats 0 0 = Yes Refl'
equalNats 0 (S k) = No (\case Refl' impossible)
equalNats (S k) 0 = No (\case Refl' impossible)
equalNats (S k) (S j) = case (equalNats k j) of
                             Yes p => Yes (succNat p)
                             -- c . unSuccNat is same as \arg => c (unSuccNat arg)
                             No c => No (c . unSuccNat)
