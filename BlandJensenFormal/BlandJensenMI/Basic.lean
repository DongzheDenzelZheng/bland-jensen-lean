import Mathlib.Combinatorics.Matroid.Circuit
import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.Combinatorics.Matroid.Minor.Order
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import BlandJensenFormal.PhaseObstructionAlgebra

/-!
# Basic interfaces for the Bland--Jensen weak-orientability argument

This file supplies the definitions that are missing from Mathlib but are needed
to state the Bland--Jensen argument against Mathlib's `Matroid` API.

* `FiniteBasisPresentation` packages the finite basis conditions and constructs the
  corresponding Mathlib matroid.
* `Represents` says that a labelled vector family represents a matroid by
  agreement of independent sets.
* `RationallyRepresentable` specializes this definition to a finite-dimensional
  rational vector space.
* `WeaklyOrientable` is the Bland--Jensen sign-bit formulation of weak
  orientability: every two-element circuit--cocircuit intersection satisfies
  the required four-sign equation over `ZMod 2`.

No unproved bridge is hidden in these definitions.  In particular, this file
does not assert that rational representability implies weak orientability; that
theorem belongs later in the development.
-/

namespace BlandJensenFormal.BlandJensenMI

open Set
open BlandJensenFormal.PhaseObstructionAlgebra

universe u v

/-! ## Construction from a finite collection of bases -/

/-- A finite ground set together with a nonempty base predicate satisfying
basis exchange.  The fields match the hypotheses of
`Matroid.ofIsBaseOfFinite`. -/
structure FiniteBasisPresentation (α : Type u) where
  ground : Set α
  IsBase : Set α → Prop
  finite_ground : ground.Finite
  exists_isBase : ∃ B, IsBase B
  exchange : Matroid.ExchangeProperty IsBase
  subset_ground : ∀ ⦃B⦄, IsBase B → B ⊆ ground

namespace FiniteBasisPresentation

/-- The Mathlib matroid determined by a finite basis presentation. -/
def toMatroid (P : FiniteBasisPresentation α) : Matroid α :=
  Matroid.ofIsBaseOfFinite P.finite_ground P.IsBase P.exists_isBase
    P.exchange (fun _ hB ↦ P.subset_ground hB)

@[simp] theorem toMatroid_ground (P : FiniteBasisPresentation α) :
    P.toMatroid.E = P.ground :=
  rfl

@[simp] theorem toMatroid_isBase_iff (P : FiniteBasisPresentation α) (B : Set α) :
    P.toMatroid.IsBase B ↔ P.IsBase B :=
  Iff.rfl

instance (P : FiniteBasisPresentation α) : P.toMatroid.Finite :=
  Matroid.ofBaseOfFinite_finite P.finite_ground P.IsBase P.exists_isBase
    P.exchange (fun _ hB ↦ P.subset_ground hB)

end FiniteBasisPresentation

/-! ## Linear representations -/

/-- A labelled vector family `v` represents `M` over `K` when the independent
sets of `M` are exactly the subsets of the ground set on which `v` is linearly
independent.  Values of `v` outside `M.E` are deliberately irrelevant. -/
def Represents (K : Type u) {V : Type v} [DivisionRing K]
    [AddCommGroup V] [Module K V] {α : Type*}
    (M : Matroid α) (v : α → V) : Prop :=
  ∀ I : Set α,
    M.Indep I ↔ I ⊆ M.E ∧ LinearIndependent K (fun i : I ↦ v i)

theorem Represents.indep_iff {K : Type u} {V : Type v} [DivisionRing K]
    [AddCommGroup V] [Module K V] {α : Type*} {M : Matroid α} {v : α → V}
    (h : Represents K M v) (I : Set α) :
    M.Indep I ↔ I ⊆ M.E ∧ LinearIndependent K (fun i : I ↦ v i) :=
  h I

/-- Representability over a finite-dimensional rational coordinate space.
This universe-safe specialization is sufficient for all six representations
used in the `MIₙ` argument. -/
def RationallyRepresentable {α : Type*} (M : Matroid α) : Prop :=
  ∃ d : ℕ, ∃ v : α → (Fin d → ℚ), Represents ℚ M v

/-! ## Bland--Jensen weak orientability -/

/-- The affine four-sign equation attached to a circuit--cocircuit
intersection `{e,f}`.  A value in `F2 = ZMod 2` records a sign bit. -/
def BlandJensenEquation {α : Type*}
    (circuitSign cocircuitSign : Set α → α → F2)
    (C D : Set α) (e f : α) : Prop :=
  circuitSign C e + cocircuitSign D e +
      circuitSign C f + cocircuitSign D f = 1

/-- Bland--Jensen weak orientability of a matroid.

The two functions assign sign bits to all set--element pairs; only values on
actual circuit and cocircuit flags are constrained.  The defining equation is
required precisely when a circuit and a cocircuit meet in two distinct
elements. -/
def WeaklyOrientable {α : Type*} (M : Matroid α) : Prop :=
  ∃ circuitSign cocircuitSign : Set α → α → F2,
    ∀ (C D : Set α) (e f : α),
      M.IsCircuit C → M.IsCocircuit D → e ≠ f → C ∩ D = {e, f} →
        BlandJensenEquation circuitSign cocircuitSign C D e f

theorem WeaklyOrientable.equation {α : Type*} {M : Matroid α}
    (hM : WeaklyOrientable M) :
    ∃ circuitSign cocircuitSign : Set α → α → F2,
      ∀ (C D : Set α) (e f : α),
        M.IsCircuit C → M.IsCocircuit D → e ≠ f → C ∩ D = {e, f} →
          BlandJensenEquation circuitSign cocircuitSign C D e f :=
  hM

end BlandJensenFormal.BlandJensenMI
