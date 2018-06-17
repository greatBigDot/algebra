||| Algebra.Monoid: A representation of monoids.
|||
||| A monoid is an associative unital magma (i.e., a unital semigroup).
||| Mathematically, one has a pair \\(\mathscr{N} = (N, \*)\\) satisfying:
|||
||| * \\((x*y)*z = x*(y*z)\\)
||| * \\(\exists e \in N [ \forall x \in N [ x*e = e*x = x ]]\\)
|||
||| Monoids strike a nice balance between generality and richness of structure;
||| many naturally-occuring magmas are indeed monoids. For example, consider the
||| set of functions \\(X \to X\\). This set always forms a monoid under
||| function composition (i.e., \\(\* \coloneqq \circ\\))! Everything has the
||| required type (the composition of two functions in \\(X \to X\\) is another
||| such function), the identity, of course, is the identity function
||| \\(\mathrm{id}\\), and function composition is always associative (applying
||| f, then applying (g then h) is the same as applying (f then g), then
||| applying h). Thus, we have a monoid.
|||
||| Another simple monoid is the set of strings over a given alphabet, with
||| string concatenation as the function (and the empty string \\(\varepsilon\\)
||| as the identity). Again, this obviously must be monoidal, since string
||| concatenation is clearly associative.
|||
||| TODO: add a little more
module Algebra.Monoid

import Algebra.Magma
import Algebra.Semigroup
import Data.ZZ

%default total
%hide Monoid


-- TODO: See if I'm doing "determining parameters" right.
public export
interface Monoid (N : Type) (op : N -> N -> N) (e : N) | N,op where
  assoc : {n,p,q : N} -> (n `op` (p `op` q)) = ((n `op` p) `op` q)
  idl : {n : N} -> (e `op` n = n)
  idr : {n : N} -> (n `op` e = n)

_e : Monoid n op e -> n
_e _ = e

-- export
-- e : (Monoid n op e) => n
-- e @{monoid} = _e monoid

-- otherwise it does that thing where it assumes it's an implicit type variable
ID : {a : Type} -> a -> a
ID = id

[FuncMonoid] Monoid.Monoid (a -> a) (.) ID where
  assoc = Refl
  idl   = Refl
  idr   = Refl

[ListMonoid] Monoid.Monoid (List a) (++) [] where
  assoc {n=[]} {p} {q}            = Refl
  assoc {n=(x::xs)} {p=ys} {q=zs} = cong (assoc @{ListMonoid})
  idl = Refl
  idr {n=[]}      = Refl
  idr {n=(x::xs)} = cong {f = (x::)} (idr @{ListMonoid} {n=xs})

[ZZAddMon] Monoid.Monoid ZZ (+) 0 where
  assoc {n} {p} {q} = plusAssociativeZ n p q
  idl {n} = plusZeroLeftNeutralZ n
  idr {n} = plusZeroRightNeutralZ n

[ZZMult] Monoid.Monoid ZZ (*) 1 where
  assoc {n} {p} {q} = multAssociativeZ n p q
  idl {n} = multOneLeftNeutralZ n
  idr {n} = multOneRightNeutralZ n

IF : {a : Type} -> Bool -> a -> a -> a
IF True  x _ = x
IF False _ y = y

If : {a,b : Type} -> (bool : Bool) -> a -> b -> IF bool a b
If True  x _ = x
If False _ y = y
{-
infixl 8 +++
(+++) : ZZ -> ZZ -> ZZ
(Pos  n) +++ (Pos  m) = Pos (n + m)
(Pos  n) +++ (NegS m) = If (n >= m+1)
                           (Pos (n-m-1))
                           (NegS (m-n))
(NegS n) +++ (Pos  m) = Pos m +++ NegS n
(NegS n) +++ (NegS m) = NegS (n+m+1)
-}
-- idl {n} = trans (plusCommutativeZ 0 n) (idr @{ZZAdd})

-- idk why this isn't working. try the forums, i guess.
[MonoidToSemigroup] Monoid nx opx idx => Semigroup.Semigroup nx opx where
  assoc = Monoid.assoc

-- M'sSemi : (ty : Type) -> (ty -> ty -> ty) -> Type
-- M'sSemi = Semigroup
--
-- -}
