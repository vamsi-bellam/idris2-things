module Proofs

-- Definition of the plus from stdlib
-- plus : (x : Nat) -> (y : Nat) -> Nat
-- plus Z y = y
-- plus (S k) y = S (plus k y)

plusReduces : (n : Nat) -> plus Z n = n
plusReduces Z = Refl
plusReduces (S k) = Refl

plusReducesZ : (n : Nat) -> n = plus n Z
plusReducesZ Z = Refl
plusReducesZ (S k) = cong S (plusReducesZ k)

