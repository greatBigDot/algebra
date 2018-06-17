||| Algebra.Group: A representation of groups.
|||
||| A group is an associative unital invertible magma.
|||
||| It is very important, as it encapsulates the idea of symmetries.
|||
||| TODO: Add a real explanation
module Algebra.Group

-- import Algebra.Magma
import Algebra.Semigroup
import Algebra.Monoid
import Data.ZZ
import Data.Fin

%hide (*)
%default total

public export
interface Group (G : Type) (op : G -> G -> G) (e : G) (inv : G -> G) | N,op where
  assoc : {g,h,k : G} -> g `op` (h `op` k) = ((g `op` h) `op` k)
  idl   : {g : G} -> e `op` g = g
  idr   : {g : G} -> g `op` e = g
  invl  : {g : G} -> inv g `op` g = e
  invr  : {g : G} -> g `op` inv g = e

op' : Group g op e inv -> g -> g -> g
op' _ = op

-- infixl 8 *
export
(*) : Group g op e inv => g -> g -> g
(*) @{i} = op' i

e_G' : Group g _ e _ -> g
e_G' _ = e
inv_G' : Group g _ _ inv -> g -> g
inv_G' _ = inv

export
inv_G : Group g _ _ inv => g -> g
inv_G @{i} = inv_G' @{i}

export
e_G : Group g _ _ _ => g
e_G @{i} = e_G' i

infix 10 ^+
(^+) : Group grp _ _ _ => grp -> Nat -> grp
(^+) @{i} g Z     = e_G @{i}
(^+) @{i} g (S n) = (*) @{i} g ((^+) @{i} g n)

infix 10 ^
(^) : Group grp op e inv => grp -> ZZ -> grp
(^) @{i} g (Pos n)  = (^+) @{i} g n
(^) @{i} g (NegS n) = (^+) @{i} (inv_G @{i} g) (S n)

[ZZAdd] Group.Group ZZ (+) 0 (negate @{%implementation}) where
  assoc {g} {h} {k} = plusAssociativeZ g h k
  idl {g}  = plusZeroLeftNeutralZ g
  idr {g}  = plusZeroRightNeutralZ g
  invl {g} = plusNegateInverseRZ g
  invr {g} = plusNegateInverseLZ g

[GroupToMonoid] Group grp op e inv => Monoid.Monoid grp op e where
  assoc = Group.assoc
  idl   = Group.idl
  idr   = Group.idr

{-
[ModAdd] {n : Nat} -> Group (Fin n)

--  invr {g} =
{-
(^+) @{i} g (NegS Z)     = inv_G @{i} g
(^+) @{i} g (NegS (S n)) = (^^) @{i} g (NegS n) -- (inv_G @{i} g) (Pos (S n))
-}
-}
