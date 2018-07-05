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
||| Another simplr monoid is the set of strings over a given alphabet, with
||| string concatenation as the function (and the empty string
||| \\(\varepsilon\\)) as the identity. Again, this obviously must be monoidal,
||| since string concatenation is clearly associative.
|||
||| TODO: add a little more
module Algebra.Monoid

import Algebra.Magma
import Algebra.Semigroup


%default total

export
record Monoid where
  constructor MkMonoid'
  magma  : Magma
  ID     : Set {magma}
  {assoc : {s,t,u : Set {magma}} -> s |*| (t |*| u) = (s |*| t) |*| u}
  {idl   : {n : Set {magma}} -> (ID |*| n  = n)}
  {idr   : {n : Set {magma}} -> (n  |*| ID = n)}


MkMonoid : (set : Type) -> (op : set -> set -> set) -> (i : set)
             -> {auto assoc : {s,t,u : set} -> s `op` (t `op` u) = (s `op` t) `op` u}
             -> {auto idl   : {n : set} -> (i `op` n = n)}
             -> {auto idr   : {n : set} -> (n `op` i = n)}
             -> Monoid
MkMonoid set op i {assoc} {idl} {idr} = MkMonoid' (MkMagma set op) i {assoc} {idl} {idr}


FuncMonoid : {a : Type} -> Monoid
FuncMonoid {a} = MkMonoid (a -> a) (.) (id)

%hint
listIdr : {a : Type} -> {xs : List a} -> xs ++ [] = xs
listIdr {xs = []}      = Refl
listIdr {xs = (x::xr)} = cong listIdr

%hint
listAssoc : {a : Type} -> {xs,ys,zs : List a} -> xs ++ (ys ++ zs) = (xs ++ ys) ++ zs
listAssoc {xs=[]}      {ys} {zs} = Refl
listAssoc {xs=(x::xr)} {ys} {zs} = cong listAssoc

ListMonoid : {a : Type} -> Monoid
ListMonoid {a} = MkMonoid (List a) (++) []

MonoidToSemigroup : Monoid -> Semigroup
MonoidToSemigroup monoid = MkSemigroup Set (|*|) {assoc = assoc monoid}
--
{-
export
interface Magma N op => Monoid (N : Type) (op : N -> N -> N) (e : N) where
  assoc : {n,p,q : N} -> ((n `op` p) `op` q = n `op` (p `op` q))
  idl : {n : N} -> (n `op` e = n)
  idr : {n : N} -> (e `op` n = n)

_e : Monoid n op e -> n
_e _ = e

export
e : (Monoid n op e) => n
e @{monoid} = _e monoid

-- idk why this isn't working. try the forums, i guess.
-- Algebra.Monoid.Monoid n op ide => Algebra.Semigroup.Semigroup n op where
--   assoc = assoc
-}
 
