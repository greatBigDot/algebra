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

import Data.ZZ
import Algebra.Magma

%default total
%hide Semigroup

-- infixr 7 |*|

||| Semigroup: The record representing semigroups.
|||
||| The requirement that a semigroup be a magma is just a declaration of the
||| signature of semigroups; namely, one set and one binary operation over it.
||| There is one law that must be obeyed: associativity. Note that you cannot
||| even construct a semigroup until you have proven that the magma is indeed
||| associative. Thus, the associativity is guaranteed by the typechecker; if a
||| function utilizing a type that claims to be a semigroup, you know that it
||| indeed must be one. mathematically speaking, iff it typechecks. (Of course,
||| as usual, this only holds when all of one's proofs are total.)
export
record Semigroup where
  constructor MkSemigroup'
  magma : Magma
  { assoc : {s,t,u : Set {magma}} -> s |*| (t |*| u) = (s |*| t) |*| u }

export
MkSemigroup : (T : Type) -> (op : T -> T -> T) -> {auto assoc : {s,t,u : T} -> s `op` (t `op` u) = (s `op` t) `op` u} -> Semigroup
MkSemigroup t op {assoc} = MkSemigroup' (MkMagma t op) {assoc=assoc}
{-
public export
MkSemigroup : (T : Type) -> (op : T -> T -> T) -> {auto asc : {s,t,u : T} -> op s (op t u) = op (op s t) u} -> Semigroup
MkSemigroup set op {asc} = MkSemigroup' (MkMagma set op) asc
-}

-- toInteger : ZZ -> Integer
-- toInteger (Pos  n) = toIntegerNat n
-- toInteger (NegS n) = -(toIntegerNat (S n))

%hint
plusAssociative' : {a,b,c : Nat} -> a + (b + c) = (a + b) + c
plusAssociative' {a} {b} {c} = plusAssociative a b c

%hint
multAssociative' : {a,b,c : Nat} -> a * (b * c) = (a * b) * c
multAssociative' {a} {b} {c} = multAssociative a b c

%hint
plusAssociativeZ' : {a,b,c : ZZ} -> a + (b + c) = (a + b) + c
plusAssociativeZ' {a} {b} {c} = plusAssociativeZ a b c

%hint
multAssociativeZ' : {a,b,c : ZZ} -> a * (b * c) = (a * b) * c
multAssociativeZ' {a} {b} {c} = multAssociativeZ a b c


NatAddSemi : Semigroup
NatAddSemi = MkSemigroup Nat (+)
{-
export
NatAddMagma : Magma
NatAddMagma = MkMagma Nat (+)

-- export
-- NatAddSemi : Semigroup
-- NatAddSemi = MkSemigroup NatAddMagma

export NatMultSemi : Semigroup
NatMultSemi = MkSemigroup Nat (*)     -- what the hell

-- SemigroupToMagma : Semigroup -> Magma
-- SemigroupToMagma (

-- export IntAddSemi : Semigroup
-- IntAddSemi = MkSemigroup ZZ (+)

-- export IntMultSemi : Semigroup
-- IntMultSemi = MkSemigroup ZZ (*)
-- -}
