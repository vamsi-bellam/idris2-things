module UpperChars

public export
data UpperChars = A | B | C | D | E | F | G | H | I | J | K | L | M | N | O | P | 
                Q | R | S | T | U | V | W | X | Y | Z
export
Eq UpperChars where
  A == A = True
  B == B = True
  C == C = True
  D == D = True
  E == E = True
  F == F = True
  G == G = True
  H == H = True
  I == I = True
  J == J = True
  K == K = True
  L == L = True
  M == M = True
  N == N = True
  O == O = True
  P == P = True
  Q == Q = True
  R == R = True
  S == S = True
  T == T = True
  U == U = True
  V == V = True
  W == W = True
  X == X = True
  Y == Y = True
  Z == Z = True
  _ == _ = False

export
toIndex : UpperChars  -> Nat
toIndex A = 0
toIndex B = 1
toIndex C = 2
toIndex D = 3
toIndex E = 4
toIndex F = 5
toIndex G = 6
toIndex H = 7
toIndex I = 8
toIndex J = 9
toIndex K = 10
toIndex L = 11
toIndex M = 12
toIndex N = 13
toIndex O = 14
toIndex P = 15
toIndex Q = 16
toIndex R = 17
toIndex S = 18
toIndex T = 19
toIndex U = 20
toIndex V = 21
toIndex W = 22
toIndex X = 23
toIndex Y = 24
toIndex Z = 25

export
nextChar : UpperChars  -> UpperChars
nextChar A = B
nextChar B = C
nextChar C = D
nextChar D = E
nextChar E = F
nextChar F = G
nextChar G = H
nextChar H = I
nextChar I = J
nextChar J = K
nextChar K = L
nextChar L = M
nextChar M = N
nextChar N = O
nextChar O = P
nextChar P = Q
nextChar Q = R
nextChar R = S
nextChar S = T
nextChar T = U
nextChar U = V
nextChar V = W
nextChar W = X
nextChar X = Y
nextChar Y = Z
nextChar Z = A

export
-- indexToUpperChars: (n: Nat) -> {auto prf : LT n 26} -> UpperChars
indexToUpperChars: (n: Nat) -> UpperChars
indexToUpperChars 0 = A
indexToUpperChars 1 = B
indexToUpperChars 2 = C
indexToUpperChars 3 = D
indexToUpperChars 4 = E
indexToUpperChars 5 = F
indexToUpperChars 6 = G
indexToUpperChars 7 = H
indexToUpperChars 8 = I
indexToUpperChars 9 = J
indexToUpperChars 10 = K
indexToUpperChars 11 = L
indexToUpperChars 12 = M
indexToUpperChars 13 = N
indexToUpperChars 14 = O
indexToUpperChars 15 = P
indexToUpperChars 16 = Q
indexToUpperChars 17 = R
indexToUpperChars 18 = S
indexToUpperChars 19 = T
indexToUpperChars 20 = U
indexToUpperChars 21 = V
indexToUpperChars 22 = W
indexToUpperChars 23 = X
indexToUpperChars 24 = Y
indexToUpperChars 25 = Z
-- TODO: Remove this possibility
indexToUpperChars _ = Z

export
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
