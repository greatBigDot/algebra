||| Algebra.Semigroup: A representation of semigroups.
|||
||| A semigroup is an associative magma. In other words, it is a pair
||| \\(\mathscr{S}=(S:\mathscr{V},\*:S^2\to S)\\) satisfying the following
||| (rather short!) list of axioms:
|||
||| * \\((x\*y)\*z = x\*(y\*z)\\)
|||
||| In addition to interesting combinatorial questions (like those exhibited by
||| magmas; see `Algebra.Magma`), semigroups, with their richer structure, yield
||| more interesting behavior.
|||
||| TODO: expand

module Algebra.Semigroup

import Algebra.Magma
import Data.ZZ

%default total
-- %access public export    -- ugh...
%hide Semigroup


||| Semigroup: The interface representing semigroups.
|||
||| Minimally complete definition: `assoc`
|||
||| The requirement that a semigroup be a magma is just a declaration of the
||| signature of semigroups; namely, one set and one binary operation over it.
||| There is one law that must be obeyed: associativity. Note that you cannot
||| even construct a semigroup until you have proven that the magma is indeed
||| associative. Thus, the associativity is guaranteed by the typechecker; if a
||| function utilizing a type that claims to be a semigroup, you know that it
||| indeed must be one. mathematically speaking, iff  it typechecks. (Of course,
||| as usual, this only holds when all of one's proofs are total.)
public export
interface Semigroup (S : Type) (op : S -> S -> S) where
  assoc : {s,t,u : S} -> (s `op` (t `op` u)) = ((s `op` t) `op` u)

-- assoc' : {S : Type} -> Semigroup S => {s,t,u : S} -> (s `op` (t `op` u)) = ((s `op` t) `op` u)
-- assoc' = assoc
-- assoc' = assoc

[ZZSemiAdd] Semigroup.Semigroup ZZ (+) where
  assoc {s} {t} {u} = plusAssociativeZ s t u

[ZZSemiMult] Semigroup.Semigroup ZZ (*) where
  assoc {s} {t} {u} = multAssociativeZ s t u

[ListSemi] Semigroup.Semigroup (List a) (++) where
  assoc {s=[]} {t} {u}            = Refl
  assoc {s=(x::xs)} {t=ys} {u=zs} = cong (assoc @{ListSemi})

[FuncSemi] Semigroup.Semigroup (a -> a) (.) where
  assoc = Refl
