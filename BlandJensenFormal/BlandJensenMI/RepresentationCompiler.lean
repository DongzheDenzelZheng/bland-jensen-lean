import BlandJensenFormal.BlandJensenMI.GenericRepresentation

/-!
# Compiling local subspace feasibility into a rational representation

The simultaneous generic-choice theorem works with a finite list of ordered
targets.  Matroid arguments are naturally phrased using unordered bases.  The
result below is the exact interface between the two: it enumerates every base,
chooses all of them simultaneously, and combines feasibility of bases with
forced dependence of nonbases to obtain agreement on every independent set.
-/

namespace BlandJensenFormal.BlandJensenMI

open Set Function

universe u

/-- Ordered enumerations of the `d`-element bases of `M`. -/
abbrev BaseEnumeration {α : Type u} (M : Matroid α) (d : ℕ) :=
  {t : Fin d ↪ α // M.IsBase (Set.range t)}

/-- Local feasibility for every base and parameter-independent dependence for
every nonbase can be compiled into one rational vector representation.

The fixed columns are kept literally equal to `q`; all other columns are
chosen in their prescribed subspaces.  The conclusion also returns those
constraints, so later arguments may inspect the constructed representation
without reopening the generic-choice proof. -/
theorem exists_representation_of_subspace_base_audit
    {α : Type u} [Fintype α] {M : Matroid α} {d : ℕ}
    (L : α → Submodule ℚ (Fin d → ℚ)) (fixed : Set α)
    (q : α → (Fin d → ℚ))
    (hq : ∀ e ∈ fixed, q e ∈ L e)
    (hReference : ∃ B₀ : Set α, M.IsBase B₀ ∧ B₀.ncard = d)
    (hBaseFeasible : ∀ (B : Set α), M.IsBase B → B.ncard = d →
      ∃ w : α → (Fin d → ℚ),
        (∀ e, w e ∈ L e) ∧
          (∀ e ∈ fixed, w e = q e) ∧
            LinearIndependent ℚ (fun b : B ↦ w b))
    (hNonbaseForced : ∀ (B : Set α), B ⊆ M.E → B.ncard = d →
      ¬ M.IsBase B → ∀ w : α → (Fin d → ℚ),
        (∀ e, w e ∈ L e) → (∀ e ∈ fixed, w e = q e) →
          ¬ LinearIndependent ℚ (fun b : B ↦ w b)) :
    ∃ v : α → (Fin d → ℚ),
      Represents ℚ M v ∧
        (∀ e, v e ∈ L e) ∧
          (∀ e ∈ fixed, v e = q e) := by
  classical
  let τ := BaseEnumeration M d
  letI : Fintype τ := Fintype.ofFinite τ
  let target : τ → (Fin d ↪ α) := fun t ↦ t.1
  have hTargetFeasible : ∀ t, ∃ w : α → (Fin d → ℚ),
      (∀ e, w e ∈ L e) ∧
        (∀ e ∈ fixed, w e = q e) ∧
          LinearIndependent ℚ (fun j ↦ w (target t j)) := by
    intro t
    have hcard : (Set.range (target t)).ncard = d := by
      rw [Set.ncard_range_of_injective (target t).injective]
      simp
    obtain ⟨w, hwL, hwq, hwLinear⟩ :=
      hBaseFeasible (Set.range (target t)) t.2 hcard
    refine ⟨w, hwL, hwq, ?_⟩
    let inclusion : Fin d → Set.range (target t) :=
      fun j ↦ ⟨target t j, Set.mem_range_self j⟩
    exact hwLinear.comp inclusion <| by
      intro i j hij
      exact (target t).injective (congrArg Subtype.val hij)
  obtain ⟨v, hvL, hvq, hvTargets⟩ :=
    exists_simultaneous_subspace_generic_assignment
      L fixed q hq target hTargetFeasible
  have hExactBases : ∀ B : Set α, B ⊆ M.E → B.ncard = d →
      (M.IsBase B ↔ LinearIndependent ℚ (fun b : B ↦ v b)) := by
    intro B hBE hBcard
    constructor
    · intro hB
      letI : Fintype B := B.toFinite.fintype
      have hFintypeCard : Fintype.card B = d := by
        rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
        exact hBcard
      let eB : Fin d ≃ B :=
        (Fintype.equivFinOfCardEq hFintypeCard).symm
      let tB : Fin d ↪ α :=
        eB.toEmbedding.trans (Function.Embedding.subtype B)
      have hRange : Set.range tB = B := by
        ext x
        constructor
        · rintro ⟨j, rfl⟩
          exact (eB j).property
        · intro hx
          exact ⟨eB.symm ⟨x, hx⟩, by
            simp [tB]
            rfl⟩
      let targetB : τ := ⟨tB, by simpa [hRange] using hB⟩
      apply (linearIndependent_equiv eB).mp
      simpa [target, targetB, tB, Function.comp_def] using hvTargets targetB
    · intro hLinear
      by_contra hNotBase
      exact hNonbaseForced B hBE hBcard hNotBase v hvL hvq hLinear
  refine ⟨v, ?_, hvL, hvq⟩
  exact rationalCoordinate_represents_of_exact_bases hReference hExactBases

end BlandJensenFormal.BlandJensenMI
