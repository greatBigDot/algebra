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
  assoc : {s,t,u : Set {magma}} -> (|*|) {magma} s ((|*|) {magma} t u) = (|*|) {magma} ((|*|) {magma} s t) u

toInteger : ZZ -> Integer
toInteger (Pos  n) = toIntegerNat n
toInteger (NegS n) = -(toIntegerNat (S n))

%hint
plusAssociative' : {a,b,c : Nat} -> a + (b + c) = (a + b) + c
plusAssociative' {a=a} {b=b} {c=c} = plusAssociative a b c

%hint
multAssociative' : {a,b,c : Nat} -> a * (b * c) = (a * b) * c
multAssociative' {a=a} {b=b} {c=c} = multAssociative a b c

%hint
plusAssociativeZ' : {a,b,c : ZZ} -> a + (b + c) = (a + b) + c
plusAssociativeZ' {a=a} {b=b} {c=c} = plusAssociativeZ a b c

%hint
multAssociativeZ' : {a,b,c : ZZ} -> a * (b * c) = (a * b) * c
multAssociativeZ' {a=a} {b=b} {c=c} = multAssociativeZ a b c

public export
MkSemigroup : (magma : Magma) -> {auto asc : {s,t,u : Set {magma}} -> s |*| (t |*| u) = (s |*| t) |*| u} -> Semigroup
MkSemigroup magma {asc} = MkSemigroup' magma asc

public export
MkSemigroupRaw : (T : Type) -> (op : T -> T -> T) -> {auto asc : {s,t,u : T} -> op s (op t u) = op (op s t) u} -> Semigroup
MkSemigroupRaw set op {asc} = MkSemigroup (MkMagma set op) {asc}

export
NatAddMagma : Magma
NatAddMagma = MkMagma Nat (+)

export
NatAddSemi : Semigroup
NatAddSemi = MkSemigroup NatAddMagma

export NatMultSemi : Semigroup
NatMultSemi = MkSemigroupRaw Nat (*)

export IntAddSemi : Semigroup
IntAddSemi = MkSemigroupRaw ZZ (+)

export IntMultSemi : Semigroup
IntMultSemi = MkSemigroupRaw ZZ (*)

-- Local Variables:
-- idris-load-packages: ("contrib" "prelude" "base")
-- End:
