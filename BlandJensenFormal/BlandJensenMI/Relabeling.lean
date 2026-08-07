import BlandJensenFormal.BlandJensenMI.ExcludedMinor

/-!
# Relabelling invariance of rational representations

The symmetry reduction for the Bland--Jensen family changes only the labels
of the ground elements.  This file records that a representation transports
across an equivalence of ambient element types.  Keeping this bridge explicit
prevents the final excluded-minor argument from treating isomorphic minors as
definitionally equal.
-/

namespace BlandJensenFormal.BlandJensenMI

open Set Function

universe u v w

/-- A labelled vector representation transports across a bijective
relabelling. -/
theorem Represents.mapEquiv
    {K : Type u} {V : Type v} [DivisionRing K]
    [AddCommGroup V] [Module K V]
    {α : Type w} {β : Type*} {M : Matroid α} {v : α → V}
    (h : Represents K M v) (e : α ≃ β) :
    Represents K (M.mapEquiv e) (v ∘ e.symm) := by
  intro I
  rw [Matroid.mapEquiv_indep_iff, h]
  change
    (e.symm '' I ⊆ M.E ∧ LinearIndepOn K v (e.symm '' I)) ↔
      I ⊆ (M.mapEquiv e).E ∧ LinearIndepOn K (v ∘ e.symm) I
  rw [Matroid.mapEquiv_ground_eq, linearIndepOn_equiv e.symm]
  simp

/-- Rational representability is invariant under a bijective relabelling. -/
theorem RationallyRepresentable.mapEquiv
    {α : Type u} {β : Type v} {M : Matroid α}
    (h : RationallyRepresentable M) (e : α ≃ β) :
    RationallyRepresentable (M.mapEquiv e) := by
  obtain ⟨d, v, hv⟩ := h
  exact ⟨d, v ∘ e.symm, hv.mapEquiv e⟩

/-- Relabelling by an equivalence and then by its inverse returns the
original matroid. -/
theorem mapEquiv_then_symm {α : Type u} {β : Type v}
    (M : Matroid α) (e : α ≃ β) :
    (M.mapEquiv e).mapEquiv e.symm = M := by
  apply Matroid.ext_indep
  · simp
  · intro I hI
    simp

/-- Rational representability can also be pulled back across a bijective
relabelling. -/
theorem RationallyRepresentable.of_mapEquiv
    {α : Type u} {β : Type v} {M : Matroid α} (e : α ≃ β)
    (h : RationallyRepresentable (M.mapEquiv e)) :
    RationallyRepresentable M := by
  have hBack := h.mapEquiv e.symm
  rwa [mapEquiv_then_symm M e] at hBack

/-- Rational representability is exactly invariant under relabelling. -/
theorem rationallyRepresentable_mapEquiv_iff
    {α : Type u} {β : Type v} (M : Matroid α) (e : α ≃ β) :
    RationallyRepresentable (M.mapEquiv e) ↔
      RationallyRepresentable M :=
  ⟨RationallyRepresentable.of_mapEquiv e,
    fun h ↦ h.mapEquiv e⟩

end BlandJensenFormal.BlandJensenMI
