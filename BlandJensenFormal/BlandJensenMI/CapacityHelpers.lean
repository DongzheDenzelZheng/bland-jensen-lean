import BlandJensenFormal.BlandJensenMI.Rado

/-!
# Reusable capacity lemmas

These small lemmas isolate routine moves in the six Rado audits: restriction
of an independent family, capacity of a family of fixed lines, and monotonic
dimension estimates for finite sums of subspaces.
-/

namespace BlandJensenFormal.BlandJensenMI

open Function Set Submodule

universe u v

/-- Restricting an independent family along an injective map preserves linear
independence. -/
theorem linearIndependent_comp_injective
    {K : Type u} {V : Type v} [Ring K] [AddCommGroup V] [Module K V]
    {ι κ : Type*} {v : κ → V} (h : LinearIndependent K v)
    (f : ι → κ) (hf : Function.Injective f) :
    LinearIndependent K (v ∘ f) :=
  h.comp f hf

/-- A linearly independent list of prescribed vectors witnesses Rado
capacity for the corresponding family of one-dimensional subspaces. -/
theorem hasRadoCapacity_span_singleton_of_linearIndependent
    {K : Type u} {V : Type v} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {ι : Type*} [Fintype ι] {v : ι → V}
    (h : LinearIndependent K v) :
    HasRadoCapacity K (fun i ↦ K ∙ v i) := by
  apply HasIndependentRepresentatives.hasRadoCapacity
  exact ⟨v, fun i ↦ Submodule.mem_span_singleton_self (v i), h⟩

/-- Capacity is preserved when the subspace family is changed pointwise by
equality. -/
theorem HasRadoCapacity.congr
    {K : Type u} {V : Type v} [Field K]
    [AddCommGroup V] [Module K V]
    {ι : Type*} {L L' : ι → Submodule K V}
    (h : HasRadoCapacity K L) (hEq : ∀ i, L i = L' i) :
    HasRadoCapacity K L' := by
  simpa only [show L = L' from funext hEq] using h

/-- If a subspace family fails a Rado inequality, no choice of one vector in
each subspace can be linearly independent. -/
theorem not_linearIndependent_of_not_hasRadoCapacity
    {K : Type u} {V : Type v} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {ι : Type*} [Fintype ι] {L : ι → Submodule K V}
    (hCapacity : ¬ HasRadoCapacity K L)
    {w : ι → V} (hw : ∀ i, w i ∈ L i) :
    ¬ LinearIndependent K w := by
  intro hLinear
  apply hCapacity
  exact HasIndependentRepresentatives.hasRadoCapacity
    ⟨w, hw, hLinear⟩

/-- A single finite selector with more indices than available dimension
certifies failure of Rado capacity. -/
theorem not_hasRadoCapacity_of_finrank_lt_card
    {K : Type u} {V : Type v} [Field K]
    [AddCommGroup V] [Module K V]
    {ι : Type*} {L : ι → Submodule K V}
    (J : Finset ι)
    (hJ : Module.finrank K (subspaceSum K L J) < J.card) :
    ¬ HasRadoCapacity K L := by
  intro hCapacity
  exact (Nat.not_le_of_lt hJ) (hCapacity J)

/-- A selected subspace contains each summand whose index belongs to the
finite selector. -/
theorem le_subspaceSum_of_mem
    {K : Type u} {V : Type v} [Field K]
    [AddCommGroup V] [Module K V]
    {ι : Type*} [DecidableEq ι] (L : ι → Submodule K V)
    {J : Finset ι} {i : ι} (hi : i ∈ J) :
    L i ≤ subspaceSum K L J := by
  exact Finset.le_sup (f := L) hi

end BlandJensenFormal.BlandJensenMI
