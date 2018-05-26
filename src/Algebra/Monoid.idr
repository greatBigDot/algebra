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
