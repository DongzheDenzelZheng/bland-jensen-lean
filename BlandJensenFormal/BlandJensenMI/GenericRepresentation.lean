import BlandJensenFormal.BlandJensenMI.Basic
import BlandJensenFormal.BlandJensenMI.Rado
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Generic selections and a compiler from bases to linear representations

The first half upgrades separately feasible determinant constraints to one
common rational assignment while preserving prescribed subspace membership
and genuinely fixed columns.  The second half turns exact information about
the independent `d`-subsets into the full `Represents` predicate on all
subsets of a finite ground set.
-/

namespace BlandJensenFormal.BlandJensenMI

open Function Set Submodule
open MvPolynomial

universe u

/-! ## A polynomial parameterization of subspace-valued assignments -/

/-- One block of rational parameters for a basis of each allowed subspace. -/
abbrev SubspaceParameter {E : Type u} {d : ℕ}
    (L : E → Submodule ℚ (Fin d → ℚ)) :=
  Σ e : E, Fin (Module.finrank ℚ (L e))

/-- The assignment obtained from subspace-basis coordinates.  On `fixed` it
is definitionally the prescribed vector `q e`, not an arbitrary scalar
multiple. -/
noncomputable def subspaceGenericAssignment {E : Type u} {d : ℕ}
    (L : E → Submodule ℚ (Fin d → ℚ)) (fixed : Set E)
    (q : E → (Fin d → ℚ))
    (x : SubspaceParameter L → ℚ) (e : E) : Fin d → ℚ := by
  classical
  exact if he : e ∈ fixed then q e else
      ∑ i : Fin (Module.finrank ℚ (L e)),
        x ⟨e, i⟩ • (((Module.finBasis ℚ (L e)) i : L e) : Fin d → ℚ)

/-- Every generic assignment lies in its allowed subspace, provided the fixed
vectors do. -/
theorem subspaceGenericAssignment_mem {E : Type u} {d : ℕ}
    (L : E → Submodule ℚ (Fin d → ℚ)) (fixed : Set E)
    (q : E → (Fin d → ℚ))
    (hq : ∀ e ∈ fixed, q e ∈ L e)
    (x : SubspaceParameter L → ℚ) (e : E) :
    subspaceGenericAssignment L fixed q x e ∈ L e := by
  classical
  by_cases he : e ∈ fixed
  · simpa [subspaceGenericAssignment, he] using hq e he
  · simp only [subspaceGenericAssignment, dif_neg he]
    exact sum_mem fun i _ ↦ smul_mem (L e) _ (Module.finBasis ℚ (L e) i).property

/-- Fixed columns are exactly the prescribed vectors. -/
@[simp] theorem subspaceGenericAssignment_eq_fixed {E : Type u} {d : ℕ}
    (L : E → Submodule ℚ (Fin d → ℚ)) (fixed : Set E)
    (q : E → (Fin d → ℚ)) (x : SubspaceParameter L → ℚ)
    {e : E} (he : e ∈ fixed) :
    subspaceGenericAssignment L fixed q x e = q e := by
  simp [subspaceGenericAssignment, he]

/-- Conversely, every assignment satisfying the subspace and fixed-column
constraints is represented by a parameter point. -/
theorem exists_parameter_subspaceGenericAssignment_eq
    {E : Type u} {d : ℕ}
    (L : E → Submodule ℚ (Fin d → ℚ)) (fixed : Set E)
    (q v : E → (Fin d → ℚ))
    (hvL : ∀ e, v e ∈ L e) (hvFixed : ∀ e ∈ fixed, v e = q e) :
    ∃ x : SubspaceParameter L → ℚ,
      subspaceGenericAssignment L fixed q x = v := by
  classical
  let x : SubspaceParameter L → ℚ := fun z ↦
    (Module.finBasis ℚ (L z.1)).repr ⟨v z.1, hvL z.1⟩ z.2
  refine ⟨x, funext fun e ↦ ?_⟩
  by_cases he : e ∈ fixed
  · simpa [subspaceGenericAssignment, he] using (hvFixed e he).symm
  · have hsum := (Module.finBasis ℚ (L e)).sum_repr ⟨v e, hvL e⟩
    simp only [subspaceGenericAssignment, dif_neg he, x]
    have hsumMapped := congrArg (L e).subtype hsum
    simpa only [map_sum, map_smul, Submodule.coe_subtype] using hsumMapped

/-- Polynomial coordinate of `subspaceGenericAssignment`. -/
noncomputable def subspaceGenericEntry {E : Type u} {d : ℕ}
    (L : E → Submodule ℚ (Fin d → ℚ)) (fixed : Set E)
    (q : E → (Fin d → ℚ)) (e : E) (row : Fin d) :
    MvPolynomial (SubspaceParameter L) ℚ := by
  classical
  exact if he : e ∈ fixed then MvPolynomial.C (q e row) else
      ∑ i : Fin (Module.finrank ℚ (L e)),
        MvPolynomial.C ((((Module.finBasis ℚ (L e)) i : L e) : Fin d → ℚ) row) *
          MvPolynomial.X ⟨e, i⟩

/-- Evaluation of a generic-entry polynomial is the corresponding coordinate
of the generic assignment. -/
theorem eval_subspaceGenericEntry {E : Type u} {d : ℕ}
    (L : E → Submodule ℚ (Fin d → ℚ)) (fixed : Set E)
    (q : E → (Fin d → ℚ))
    (x : SubspaceParameter L → ℚ) (e : E) (row : Fin d) :
    MvPolynomial.eval x (subspaceGenericEntry L fixed q e row) =
      subspaceGenericAssignment L fixed q x e row := by
  classical
  by_cases he : e ∈ fixed
  · simp [subspaceGenericEntry, subspaceGenericAssignment, he]
  · simp [subspaceGenericEntry, subspaceGenericAssignment, he,
      Finset.sum_apply, mul_comm]

/-! ## Simultaneous generic assignment -/

/-- The coordinate matrix whose columns are a target `d`-tuple of a generic
assignment. -/
noncomputable def subspaceTargetMatrix {E : Type u} {d : ℕ}
    (L : E → Submodule ℚ (Fin d → ℚ)) (fixed : Set E)
    (q : E → (Fin d → ℚ)) (target : Fin d ↪ E)
    (x : SubspaceParameter L → ℚ) : Matrix (Fin d) (Fin d) ℚ :=
  fun row col ↦ subspaceGenericAssignment L fixed q x (target col) row

/-- Determinant polynomial of a target tuple. -/
noncomputable def subspaceTargetPolynomial {E : Type u} {d : ℕ}
    (L : E → Submodule ℚ (Fin d → ℚ)) (fixed : Set E)
    (q : E → (Fin d → ℚ)) (target : Fin d ↪ E) :
    MvPolynomial (SubspaceParameter L) ℚ :=
  Matrix.det fun row col ↦ subspaceGenericEntry L fixed q (target col) row

/-- Evaluation of the target determinant polynomial is the determinant of the
evaluated target matrix. -/
theorem eval_subspaceTargetPolynomial {E : Type u} {d : ℕ}
    (L : E → Submodule ℚ (Fin d → ℚ)) (fixed : Set E)
    (q : E → (Fin d → ℚ)) (target : Fin d ↪ E)
    (x : SubspaceParameter L → ℚ) :
    MvPolynomial.eval x (subspaceTargetPolynomial L fixed q target) =
      Matrix.det (subspaceTargetMatrix L fixed q target x) := by
  classical
  unfold subspaceTargetPolynomial
  rw [(MvPolynomial.eval x).map_det]
  congr 1
  ext row col
  exact eval_subspaceGenericEntry L fixed q x (target col) row

/-- For `d` vectors in rational `d`-space, linear independence is equivalent
to nonvanishing of the coordinate determinant. -/
theorem linearIndependent_target_iff_det_ne_zero
    {E : Type u} {d : ℕ} (v : E → (Fin d → ℚ)) (target : Fin d ↪ E) :
    LinearIndependent ℚ (fun j ↦ v (target j)) ↔
      Matrix.det (fun row col : Fin d ↦ v (target col) row) ≠ 0 := by
  let A : Matrix (Fin d) (Fin d) ℚ := fun row col ↦ v (target col) row
  constructor
  · intro hLinear
    have hCols : LinearIndependent ℚ A.col := by
      simpa [A, Matrix.col] using hLinear
    have hUnitA : IsUnit A := Matrix.linearIndependent_cols_iff_isUnit.mp hCols
    have hUnitDet : IsUnit A.det := A.isUnit_iff_isUnit_det.mp hUnitA
    simpa [A] using hUnitDet.ne_zero
  · intro hDet
    have hCols : LinearIndependent ℚ A.col :=
      Matrix.linearIndependent_cols_of_det_ne_zero (by simpa [A] using hDet)
    simpa [A, Matrix.col] using hCols

/-- **Simultaneous generic assignment.**

Suppose each target `d`-tuple separately has a linearly independent
assignment satisfying the subspace constraints and the exact fixed-column
equalities.  Then one common assignment satisfies all target constraints at
once.  No common feasibility hypothesis is assumed: it is produced by the
product-of-determinants argument over the infinite field `ℚ`. -/
theorem exists_simultaneous_subspace_generic_assignment
    {E : Type u} [Fintype E] {d : ℕ} {τ : Type*} [Fintype τ]
    (L : E → Submodule ℚ (Fin d → ℚ)) (fixed : Set E)
    (q : E → (Fin d → ℚ))
    (hq : ∀ e ∈ fixed, q e ∈ L e)
    (target : τ → (Fin d ↪ E))
    (hFeasible : ∀ t, ∃ v : E → (Fin d → ℚ),
      (∀ e, v e ∈ L e) ∧
        (∀ e ∈ fixed, v e = q e) ∧
          LinearIndependent ℚ (fun j ↦ v (target t j))) :
    ∃ v : E → (Fin d → ℚ),
      (∀ e, v e ∈ L e) ∧
        (∀ e ∈ fixed, v e = q e) ∧
          ∀ t, LinearIndependent ℚ (fun j ↦ v (target t j)) := by
  classical
  let A : τ → (SubspaceParameter L → ℚ) → Matrix (Fin d) (Fin d) ℚ :=
    fun t x ↦ subspaceTargetMatrix L fixed q (target t) x
  let p : τ → MvPolynomial (SubspaceParameter L) ℚ :=
    fun t ↦ subspaceTargetPolynomial L fixed q (target t)
  have hPoly : ∀ t x, MvPolynomial.eval x (p t) = Matrix.det (A t x) := by
    intro t x
    exact eval_subspaceTargetPolynomial L fixed q (target t) x
  have hDetFeasible : ∀ t, ∃ x : SubspaceParameter L → ℚ,
      Matrix.det (A t x) ≠ 0 := by
    intro t
    obtain ⟨v, hvL, hvFixed, hvLinear⟩ := hFeasible t
    obtain ⟨x, hx⟩ :=
      exists_parameter_subspaceGenericAssignment_eq L fixed q v hvL hvFixed
    refine ⟨x, ?_⟩
    have hDetV := (linearIndependent_target_iff_det_ne_zero v (target t)).mp hvLinear
    change Matrix.det (subspaceTargetMatrix L fixed q (target t) x) ≠ 0
    unfold subspaceTargetMatrix
    rw [hx]
    exact hDetV
  obtain ⟨x, hx⟩ :=
    simultaneous_rational_matrix_nonsingular A p hPoly hDetFeasible
  let v : E → (Fin d → ℚ) := subspaceGenericAssignment L fixed q x
  refine ⟨v, ?_, ?_, ?_⟩
  · intro e
    exact subspaceGenericAssignment_mem L fixed q hq x e
  · intro e he
    exact subspaceGenericAssignment_eq_fixed L fixed q x he
  · intro t
    apply (linearIndependent_target_iff_det_ne_zero v (target t)).mpr
    simpa [v, A, subspaceTargetMatrix] using hx t

/-! ## Compiling exact bases into `Represents` -/

/-- Exact information about all full-size bases compiles to agreement of all
independent sets.

The reference base fixes the matroid rank at `d` and, through the exact-bases
hypothesis, supplies a full-rank vector basis.  For the reverse implication on
an arbitrary linearly independent set `I`, `LinearIndepOn.extend` enlarges `I`
inside the finite ground set until it spans all ground vectors.  Full ground
span forces the extension to have cardinality `d`; the exact-bases hypothesis
then recognizes it as a matroid base containing `I`. -/
theorem represents_of_exact_bases_of_finrank_eq
    {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {α : Type u} [Fintype α]
    {M : Matroid α} {v : α → V} {d : ℕ}
    (hFinrank : Module.finrank K V = d)
    (hReference : ∃ B₀ : Set α, M.IsBase B₀ ∧ B₀.ncard = d)
    (hExactBases : ∀ B : Set α, B ⊆ M.E → B.ncard = d →
      (M.IsBase B ↔ LinearIndependent K (fun b : B ↦ v b))) :
    Represents K M v := by
  classical
  obtain ⟨B₀, hB₀, hB₀card⟩ := hReference
  have hLinearB₀ : LinearIndependent K (fun b : B₀ ↦ v b) :=
    (hExactBases B₀ hB₀.subset_ground hB₀card).mp hB₀
  have hB₀FintypeCard : Fintype.card B₀ = Module.finrank K V := by
    simp [← Nat.card_eq_fintype_card, hB₀card, hFinrank]
  have hSpanB₀ : Submodule.span K (v '' B₀) = ⊤ := by
    have hRange := hLinearB₀.span_eq_top_of_card_eq_finrank' hB₀FintypeCard
    have hRangeImage : Set.range (fun b : B₀ ↦ v b) = v '' B₀ := by
      apply Set.Subset.antisymm
      · rintro y ⟨b, rfl⟩
        exact ⟨b, b.property, rfl⟩
      · rintro y ⟨b, hb, rfl⟩
        exact ⟨⟨b, hb⟩, rfl⟩
    rwa [hRangeImage] at hRange
  have hGroundSpan : Submodule.span K (v '' M.E) = ⊤ := by
    apply top_unique
    rw [← hSpanB₀]
    exact Submodule.span_mono (image_mono hB₀.subset_ground)
  intro I
  constructor
  · intro hI
    obtain ⟨B, hB, hIB⟩ := hI.exists_isBase_superset
    have hBcard : B.ncard = d :=
      (hB.ncard_eq_ncard_of_isBase hB₀).trans hB₀card
    have hLinearB : LinearIndependent K (fun b : B ↦ v b) :=
      (hExactBases B hB.subset_ground hBcard).mp hB
    have hLinearI : LinearIndependent K (fun i : I ↦ v i) := by
      let inclusion : I → B := fun i ↦ ⟨i, hIB i.property⟩
      have hComp := hLinearB.comp inclusion
        (fun _ _ h ↦ Subtype.ext (congrArg (fun z : B ↦ (z : α)) h))
      simpa [inclusion, Function.comp_def] using hComp
    exact ⟨hI.subset_ground, hLinearI⟩
  · rintro ⟨hIE, hLinearI⟩
    have hLinearOnI : LinearIndepOn K v I := hLinearI
    let J : Set α := hLinearOnI.extend hIE
    have hIJ : I ⊆ J := hLinearOnI.subset_extend hIE
    have hJE : J ⊆ M.E := hLinearOnI.extend_subset hIE
    have hLinearOnJ : LinearIndepOn K v J :=
      hLinearOnI.linearIndepOn_extend hIE
    have hSpanJ : Submodule.span K (v '' J) = ⊤ := by
      rw [hLinearOnI.span_image_extend_eq_span_image hIE]
      exact hGroundSpan
    have hLinearJ : LinearIndependent K (fun j : J ↦ v j) := hLinearOnJ
    have hJcard : J.ncard = d := by
      have hDim := finrank_span_eq_card hLinearJ
      have hRangeImage : Set.range (fun j : J ↦ v j) = v '' J := by
        ext y
        simp
      rw [hRangeImage, hSpanJ, finrank_top] at hDim
      calc
        J.ncard = Fintype.card J := by
          simp [← Nat.card_eq_fintype_card]
        _ = Module.finrank K V := hDim.symm
        _ = d := hFinrank
    have hJBase : M.IsBase J :=
      (hExactBases J hJE hJcard).mpr hLinearJ
    exact hJBase.indep.subset hIJ

/-- Coordinate-space specialization.  Here the ambient dimension hypothesis
is discharged by `finrank (Fin d → ℚ) = d`. -/
theorem rationalCoordinate_represents_of_exact_bases
    {α : Type u} [Fintype α] {M : Matroid α} {d : ℕ}
    {v : α → (Fin d → ℚ)}
    (hReference : ∃ B₀ : Set α, M.IsBase B₀ ∧ B₀.ncard = d)
    (hExactBases : ∀ B : Set α, B ⊆ M.E → B.ncard = d →
      (M.IsBase B ↔ LinearIndependent ℚ (fun b : B ↦ v b))) :
    Represents ℚ M v := by
  apply represents_of_exact_bases_of_finrank_eq (d := d) (by simp)
    hReference hExactBases

end BlandJensenFormal.BlandJensenMI
