import BlandJensenFormal.BlandJensenMI.WeakOrientation
import Mathlib.Combinatorics.Matroid.Map
import Mathlib.Data.Set.Card

/-!
# Excluded-minor framework for weak orientability

This file contains only reusable infrastructure.  It proves that checking all
relevant one-element deletions and contractions is sufficient for proving that
a non-weakly-orientable matroid is an excluded minor.  It also records the
standard cardinality argument which turns an infinite family with strictly
increasing ground-set sizes into a proof that no finite excluded-minor list can
characterize the class.
-/

namespace BlandJensenFormal.BlandJensenMI

open Set

universe u v

/-! ## Excluded minors -/

/-- A matroid `M` is an excluded minor for a minor-closed predicate `P` when
`M` fails `P` but every strict minor of `M` satisfies `P`. -/
def IsExcludedMinorFor {α : Type u} (P : Matroid α → Prop) (M : Matroid α) : Prop :=
  ¬ P M ∧ ∀ ⦃N : Matroid α⦄, N <m M → P N

/-- Specialization of `IsExcludedMinorFor` to Bland--Jensen weak
orientability. -/
abbrev IsWeakOrientabilityExcludedMinor {α : Type u} (M : Matroid α) : Prop :=
  IsExcludedMinorFor WeaklyOrientable M

/-- A strict minor is already a minor of a suitable one-element deletion or
contraction.  The element can be chosen from the contracted/deleted sets in a
disjoint contraction--deletion presentation. -/
theorem Matroid.IsStrictMinor.exists_isMinor_contractElem_or_deleteElem
    {α : Type u} {M N : Matroid α} (hNM : N <m M) :
    ∃ e ∈ M.E,
      N ≤m Matroid.contract M {e} ∨ N ≤m Matroid.delete M {e} := by
  obtain ⟨C, D, hCE, hDE, hCD, hN⟩ :=
    hNM.isMinor.exists_eq_contract_delete_disjoint
  have hUnion : (C ∪ D).Nonempty := by
    by_contra hEmpty
    rw [not_nonempty_iff_eq_empty] at hEmpty
    have hC : C = ∅ := eq_empty_iff_forall_notMem.mpr fun x hx ↦ by
      exact (show x ∉ C ∪ D from by simp [hEmpty]) (Or.inl hx)
    have hD : D = ∅ := eq_empty_iff_forall_notMem.mpr fun x hx ↦ by
      exact (show x ∉ C ∪ D from by simp [hEmpty]) (Or.inr hx)
    apply hNM.ne
    simpa [hC, hD] using hN
  obtain ⟨e, heC | heD⟩ := hUnion
  · refine ⟨e, hCE heC, Or.inl ?_⟩
    refine ⟨C, D, ?_⟩
    rw [hN, Matroid.contract_contract]
    congr 2
    exact (union_eq_right.mpr (singleton_subset_iff.mpr heC)).symm
  · refine ⟨e, hDE heD, Or.inr ?_⟩
    refine ⟨C, D, ?_⟩
    rw [hN, ← Matroid.contract_delete_comm M
      (hCD.mono_right (singleton_subset_iff.mpr heD)),
      Matroid.delete_delete]
    congr 2
    exact (union_eq_right.mpr (singleton_subset_iff.mpr heD)).symm

/-- One-element tests suffice for excluded-minor minimality of a non-weakly
orientable matroid.

The hypotheses omit contraction of loops and deletion of coloops.  These are
the correct irredundant tests: contracting a loop equals deleting it, while
deleting a coloop equals contracting it. -/
theorem isWeakOrientabilityExcludedMinor_of_singleton_minors
    {α : Type u} {M : Matroid α}
    (hNotWeak : ¬ WeaklyOrientable M)
    (hContract : ∀ ⦃e : α⦄, M.IsNonloop e →
      WeaklyOrientable (Matroid.contract M {e}))
    (hDelete : ∀ ⦃e : α⦄, e ∈ M.E → ¬ M.IsColoop e →
      WeaklyOrientable (Matroid.delete M {e})) :
    IsWeakOrientabilityExcludedMinor M := by
  refine ⟨hNotWeak, ?_⟩
  intro N hNM
  obtain ⟨e, heE, hContractMinor | hDeleteMinor⟩ :=
    Matroid.IsStrictMinor.exists_isMinor_contractElem_or_deleteElem hNM
  · have hOne : WeaklyOrientable (Matroid.contract M {e}) := by
      rcases M.isLoop_or_isNonloop e heE with hLoop | hNonloop
      · have hEq : Matroid.contract M {e} = Matroid.delete M {e} :=
          M.contract_eq_delete_of_subset_loops
            (singleton_subset_iff.mpr hLoop)
        rw [hEq]
        exact hDelete heE hLoop.not_isColoop
      · exact hContract hNonloop
    exact hOne.of_isMinor hContractMinor
  · have hOne : WeaklyOrientable (Matroid.delete M {e}) := by
      by_cases hColoop : M.IsColoop e
      · have hEq : Matroid.contract M {e} = Matroid.delete M {e} :=
          M.contract_eq_delete_of_subset_coloops
            (singleton_subset_iff.mpr hColoop)
        rw [← hEq]
        exact hContract hColoop.isNonloop
      · exact hDelete heE hColoop
    exact hOne.of_isMinor hDeleteMinor

/-! ## Isomorphism and ground-set cardinality -/

/-- Matroid isomorphism expressed through Mathlib's `mapSetEquiv`: an
equivalence of ground-set subtypes transports one matroid to the other. -/
def MatroidIsomorphic {α : Type u} {β : Type v}
    (M : Matroid α) (N : Matroid β) : Prop :=
  ∃ e : M.E ≃ N.E, M.mapSetEquiv e = N

theorem MatroidIsomorphic.encard_ground_eq
    {α : Type u} {β : Type v} {M : Matroid α} {N : Matroid β}
    (hIso : MatroidIsomorphic M N) : M.E.encard = N.E.encard := by
  obtain ⟨e, _⟩ := hIso
  exact Set.encard_congr e

/-- Different ground-set cardinalities rule out matroid isomorphism. -/
theorem not_matroidIsomorphic_of_encard_ground_ne
    {α : Type u} {β : Type v} {M : Matroid α} {N : Matroid β}
    (hCard : M.E.encard ≠ N.E.encard) : ¬ MatroidIsomorphic M N :=
  fun hIso ↦ hCard hIso.encard_ground_eq

/-! ## Finite excluded-minor characterizations -/

/-- A finite excluded-minor characterization on a fixed ambient type is a
finite set containing, up to matroid isomorphism, exactly all excluded minors
for `P`. -/
def HasFiniteExcludedMinorCharacterization {α : Type u}
    (P : Matroid α → Prop) : Prop :=
  ∃ F : Set (Matroid α), F.Finite ∧
    ∀ M : Matroid α,
      IsExcludedMinorFor P M ↔ ∃ N ∈ F, MatroidIsomorphic M N

/-- A sequence of excluded minors whose ground-set cardinalities are strictly
increasing rules out a finite excluded-minor characterization. -/
theorem not_hasFiniteExcludedMinorCharacterization_of_strictMono_encard
    {α : Type u} {P : Matroid α → Prop} (family : ℕ → Matroid α)
    (hExcluded : ∀ n, IsExcludedMinorFor P (family n))
    (hCard : StrictMono (fun n ↦ (family n).E.encard)) :
    ¬ HasFiniteExcludedMinorCharacterization P := by
  rintro ⟨F, hFFinite, hComplete⟩
  have hRepresentative : ∀ n, ∃ N ∈ F, MatroidIsomorphic (family n) N :=
    fun n ↦ (hComplete (family n)).mp (hExcluded n)
  choose representative hRepresentativeMem hRepresentativeIso using hRepresentative
  have hRepresentativeInj : Function.Injective representative := by
    intro i j hij
    apply hCard.injective
    calc
      (family i).E.encard = (representative i).E.encard :=
        (hRepresentativeIso i).encard_ground_eq
      _ = (representative j).E.encard := by rw [hij]
      _ = (family j).E.encard :=
        (hRepresentativeIso j).encard_ground_eq.symm
  have hInfiniteRange : (Set.range representative).Infinite :=
    Set.infinite_range_of_injective hRepresentativeInj
  exact hInfiniteRange (hFFinite.subset (range_subset_iff.mpr hRepresentativeMem))

end BlandJensenFormal.BlandJensenMI
