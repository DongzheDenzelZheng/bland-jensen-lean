import BlandJensenFormal.BlandJensenMI.Basic
import Mathlib.Combinatorics.Matroid.Minor.Contract
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Permanence properties of Bland--Jensen weak orientability

This file proves directly from the circuit--cocircuit sign-bit definition that
weak orientability is preserved by duality, contraction, deletion, and hence
by taking arbitrary matroid minors.  The contraction proof uses Mathlib's
circuit-lifting theorem: every circuit of `M / K` lifts to a circuit of `M`
contained in its union with `K`.
-/

namespace BlandJensenFormal.BlandJensenMI

open Set
open BlandJensenFormal.PhaseObstructionAlgebra

universe u

/-! ## Duality -/

/-- Bland--Jensen weak orientability is invariant under matroid duality. -/
theorem weaklyOrientable_dual_iff {α : Type u} (M : Matroid α) :
    WeaklyOrientable M✶ ↔ WeaklyOrientable M := by
  constructor
  · intro h
    simpa only [Matroid.dual_dual] using (show WeaklyOrientable M✶✶ from
      (by
        obtain ⟨circuitSign, cocircuitSign, hEq⟩ := h
        refine ⟨cocircuitSign, circuitSign, ?_⟩
        intro C D e f hC hD hef hCD
        have hD' : M✶.IsCircuit D := by
          simpa only [Matroid.dual_isCocircuit_iff] using hD
        have hDC : D ∩ C = {e, f} := by
          simpa only [inter_comm] using hCD
        simpa only [BlandJensenEquation, add_comm, add_left_comm, add_assoc] using
          hEq D C e f hD' hC hef hDC))
  · intro h
    obtain ⟨circuitSign, cocircuitSign, hEq⟩ := h
    refine ⟨cocircuitSign, circuitSign, ?_⟩
    intro C D e f hC hD hef hCD
    have hD' : M.IsCircuit D := by
      simpa only [Matroid.dual_isCocircuit_iff] using hD
    have hDC : D ∩ C = {e, f} := by
      simpa only [inter_comm] using hCD
    simpa only [BlandJensenEquation, add_comm, add_left_comm, add_assoc] using
      hEq D C e f hD' hC hef hDC

/-- Forward form of dual invariance. -/
theorem WeaklyOrientable.dual {α : Type u} {M : Matroid α}
    (hM : WeaklyOrientable M) : WeaklyOrientable M✶ :=
  (weaklyOrientable_dual_iff M).2 hM

/-! ## Contraction and deletion -/

/-- Weak orientability is preserved by contraction by an arbitrary set.

For a circuit `C` of `M / K`, choose a lifted circuit `C'` of `M` with
`C ⊆ C' ⊆ C ∪ K`.  Every cocircuit `D` of `M / K` is already a cocircuit of
`M` disjoint from `K`; consequently `C' ∩ D = C ∩ D`, so the original
Bland--Jensen equation applies without changing either of its two elements.
-/
theorem WeaklyOrientable.contract {α : Type u} {M : Matroid α}
    (hM : WeaklyOrientable M) (K : Set α) : WeaklyOrientable (Matroid.contract M K) := by
  classical
  obtain ⟨circuitSign, cocircuitSign, hEq⟩ := hM
  let circuitLift : Set α → Set α := fun C ↦
    if hC : (Matroid.contract M K).IsCircuit C then
      Classical.choose hC.exists_subset_isCircuit_of_contract
    else ∅
  have circuitLift_spec (C : Set α) (hC : (Matroid.contract M K).IsCircuit C) :
      M.IsCircuit (circuitLift C) ∧ C ⊆ circuitLift C ∧ circuitLift C ⊆ C ∪ K := by
    simp only [circuitLift, dif_pos hC]
    exact Classical.choose_spec hC.exists_subset_isCircuit_of_contract
  refine ⟨fun C e ↦ circuitSign (circuitLift C) e, cocircuitSign, ?_⟩
  intro C D e f hC hD hef hCD
  obtain ⟨hLiftCircuit, hCLift, hLiftCK⟩ := circuitLift_spec C hC
  obtain ⟨hDCocircuit, hDK⟩ := Matroid.contract_isCocircuit_iff.mp hD
  have hLiftInter : circuitLift C ∩ D = C ∩ D := by
    apply Set.Subset.antisymm
    · intro x hx
      have hxLift : x ∈ circuitLift C := hx.1
      have hxD : x ∈ D := hx.2
      have hxCK : x ∈ C ∨ x ∈ K := hLiftCK hxLift
      exact ⟨hxCK.resolve_right (fun hxK ↦ hDK.le_bot ⟨hxD, hxK⟩), hxD⟩
    · exact inter_subset_inter_left D hCLift
  exact hEq (circuitLift C) D e f hLiftCircuit hDCocircuit hef
    (hLiftInter.trans hCD)

/-- Weak orientability is preserved by deletion by an arbitrary set. -/
theorem WeaklyOrientable.delete {α : Type u} {M : Matroid α}
    (hM : WeaklyOrientable M) (D : Set α) : WeaklyOrientable (Matroid.delete M D) := by
  have hDualContract : WeaklyOrientable (Matroid.contract M✶ D) := hM.dual.contract D
  have hDualAgain : WeaklyOrientable (Matroid.contract M✶ D)✶ := hDualContract.dual
  simpa only [Matroid.dual_contract_dual] using hDualAgain

/-! ## Arbitrary minors -/

/-- Every minor of a weakly orientable matroid is weakly orientable. -/
theorem WeaklyOrientable.of_isMinor {α : Type u} {M N : Matroid α}
    (hM : WeaklyOrientable M) (hNM : N ≤m M) : WeaklyOrientable N := by
  obtain ⟨C, D, rfl⟩ := hNM
  exact (hM.contract C).delete D

/-! ## Linear representations: spans and closures -/

section Representation

variable {K V α : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {M : Matroid α} {v : α → V}

/-- Rephrasing `Represents` in Mathlib's `LinearIndepOn` notation. -/
theorem Represents.indep_iff_linearIndepOn (hRep : Represents K M v) (I : Set α) :
    M.Indep I ↔ I ⊆ M.E ∧ LinearIndepOn K v I := by
  simpa only [LinearIndepOn] using hRep I

/-- If `I` is a matroid basis of `X`, every vector labelled by an element of
`X` belongs to the linear span of the vectors labelled by `I`. -/
theorem Represents.mem_span_image_of_isBasis (hRep : Represents K M v)
    {I X : Set α} (hI : M.IsBasis I X) {x : α} (hx : x ∈ X) :
    v x ∈ Submodule.span K (v '' I) := by
  have hLI : LinearIndepOn K v I :=
    ((hRep.indep_iff_linearIndepOn I).mp hI.indep).2
  rw [hLI.mem_span_iff]
  intro hLIinsert
  have hInsert : M.Indep (insert x I) :=
    (hRep.indep_iff_linearIndepOn (insert x I)).mpr
      ⟨insert_subset (hI.subset_ground hx) hI.indep.subset_ground, hLIinsert⟩
  exact hI.mem_of_insert_indep hx hInsert

/-- Every circuit of a represented matroid carries a nontrivial linear
dependence whose support is exactly that circuit. -/
theorem Represents.exists_circuit_relation (hRep : Represents K M v)
    {C : Set α} (hC : M.IsCircuit C) :
    ∃ a : α →₀ K,
      Finsupp.linearCombination K v a = 0 ∧
        (∀ e ∈ C, a e ≠ 0) ∧ (a.support : Set α) = C := by
  classical
  have hNotLinear : ¬ LinearIndepOn K v C := by
    intro hLinear
    exact hC.not_indep <|
      (hRep.indep_iff_linearIndepOn C).mpr ⟨hC.subset_ground, hLinear⟩
  obtain ⟨a, haSupported, haRelation, haNonzero⟩ :=
    linearDepOn_iff'.mp hNotLinear
  have hSupportSubset : (a.support : Set α) ⊆ C := by
    exact haSupported
  have hSupportNotLinear : ¬ LinearIndepOn K v (a.support : Set α) := by
    apply linearDepOn_iff'.mpr
    exact ⟨a, a.mem_supported_support K, haRelation, haNonzero⟩
  have hSupportGround : (a.support : Set α) ⊆ M.E :=
    hSupportSubset.trans hC.subset_ground
  have hSupportNotIndep : ¬ M.Indep (a.support : Set α) := by
    intro hIndep
    exact hSupportNotLinear ((hRep.indep_iff_linearIndepOn _).mp hIndep).2
  have hSupportDep : M.Dep (a.support : Set α) :=
    (Matroid.not_indep_iff hSupportGround).mp hSupportNotIndep
  have hSupportEq : (a.support : Set α) = C :=
    hC.eq_of_dep_subset hSupportDep hSupportSubset
  refine ⟨a, haRelation, ?_, hSupportEq⟩
  intro e heC
  exact Finsupp.mem_support_iff.mp (hSupportEq.symm.subset heC)

/-- A matroid basis and the set it bases have the same vector span in every
linear representation. -/
theorem Represents.span_image_eq_of_isBasis (hRep : Represents K M v)
    {I X : Set α} (hI : M.IsBasis I X) :
    Submodule.span K (v '' I) = Submodule.span K (v '' X) := by
  apply le_antisymm
  · exact Submodule.span_mono (image_mono hI.subset)
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hRep.mem_span_image_of_isBasis hI hx

/-- In a represented matroid, matroid closure agrees on ground elements with
ordinary linear span. -/
theorem Represents.mem_closure_iff_mem_span (hRep : Represents K M v)
    {X : Set α} (hXE : X ⊆ M.E) {x : α} (hxE : x ∈ M.E) :
    x ∈ M.closure X ↔ v x ∈ Submodule.span K (v '' X) := by
  obtain ⟨I, hI⟩ := M.exists_isBasis X hXE
  have hLI : LinearIndepOn K v I :=
    ((hRep.indep_iff_linearIndepOn I).mp hI.indep).2
  rw [← hI.closure_eq_closure, ← hRep.span_image_eq_of_isBasis hI,
    hI.indep.mem_closure_iff', hLI.mem_span_iff, and_iff_right hxE]
  constructor
  · intro hMatroid hLinear
    apply hMatroid
    exact (hRep.indep_iff_linearIndepOn (insert x I)).mpr
      ⟨insert_subset hxE hI.indep.subset_ground, hLinear⟩
  · intro hLinear hMatroid
    apply hLinear
    exact ((hRep.indep_iff_linearIndepOn (insert x I)).mp hMatroid).2

/-- A supported set is matroid-spanning exactly when its representing vectors
span the same subspace as all ground-set vectors. -/
theorem Represents.spanning_iff_span_image_eq (hRep : Represents K M v)
    {X : Set α} (hXE : X ⊆ M.E) :
    M.Spanning X ↔
      Submodule.span K (v '' X) = Submodule.span K (v '' M.E) := by
  rw [Matroid.spanning_iff_closure_eq]
  constructor
  · intro hClosure
    apply le_antisymm
    · exact Submodule.span_mono (image_mono hXE)
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨x, hxE, rfl⟩
      apply (hRep.mem_closure_iff_mem_span hXE hxE).mp
      rw [hClosure]
      exact hxE
  · intro hSpan
    apply Set.Subset.antisymm (M.closure_subset_ground X)
    intro x hxE
    apply (hRep.mem_closure_iff_mem_span hXE hxE).mpr
    rw [hSpan]
    exact Submodule.subset_span (mem_image_of_mem v hxE)

/-- Removing one element from a cocircuit makes its complement spanning; in
equivalent form, adjoining any cocircuit element to the cocircuit complement
is spanning. -/
theorem Matroid.IsCocircuit.spanning_insert_compl {D : Set α}
    (hD : M.IsCocircuit D) {e : α} (heD : e ∈ D) :
    M.Spanning (insert e (M.E \ D)) := by
  have hMin := Matroid.isCocircuit_iff_minimal_compl_nonspanning.mp hD
  rw [minimal_iff_forall_ssubset] at hMin
  have hSpanDiff : M.Spanning (M.E \ (D \ {e})) :=
    not_not.mp (hMin.2 (diff_singleton_ssubset.mpr heD))
  have hSet : M.E \ (D \ {e}) = insert e (M.E \ D) := by
    ext x
    constructor
    · rintro ⟨hxE, hx⟩
      by_cases hxe : x = e
      · exact Or.inl hxe
      · exact Or.inr ⟨hxE, fun hxD ↦ hx ⟨hxD, hxe⟩⟩
    · rintro (rfl | ⟨hxE, hxD⟩)
      · exact ⟨hD.subset_ground heD, by simp⟩
      · exact ⟨hxE, fun hx ↦ hxD hx.1⟩
  rwa [hSet] at hSpanDiff

/-- A cocircuit of a represented matroid is the nonzero support, on the
ground set, of a linear functional.  This is the precise linear-algebraic
ingredient needed for orienting cocircuits. -/
theorem Represents.exists_cocircuit_covector (hRep : Represents K M v)
    {D : Set α} (hD : M.IsCocircuit D) :
    ∃ φ : V →ₗ[K] K,
      (∀ x ∈ M.E \ D, φ (v x) = 0) ∧ (∀ e ∈ D, φ (v e) ≠ 0) := by
  classical
  let H : Set α := M.E \ D
  have hHE : H ⊆ M.E := diff_subset
  have hHNotSpanning : ¬ M.Spanning H :=
    (Matroid.isCocircuit_iff_minimal_compl_nonspanning.mp hD).prop
  obtain ⟨d, hdD⟩ := hD.nonempty
  have hdE : d ∈ M.E := hD.subset_ground hdD
  have hInsertSubset (e : α) (heD : e ∈ D) : insert e H ⊆ M.E :=
    insert_subset (hD.subset_ground heD) hHE
  have hInsertSpanning (e : α) (heD : e ∈ D) : M.Spanning (insert e H) := by
    simpa only [H] using Matroid.IsCocircuit.spanning_insert_compl hD heD
  have hvdNotMem : v d ∉ Submodule.span K (v '' H) := by
    intro hvd
    have hSpanInsert :
        Submodule.span K (v '' insert d H) = Submodule.span K (v '' H) := by
      apply le_antisymm
      · refine Submodule.span_le.mpr ?_
        rintro _ ⟨x, hx, rfl⟩
        rcases hx with rfl | hxH
        · exact hvd
        · exact Submodule.subset_span (mem_image_of_mem v hxH)
      · exact Submodule.span_mono (image_mono (subset_insert d H))
    have hSpanInsertGround :
        Submodule.span K (v '' insert d H) = Submodule.span K (v '' M.E) :=
      (hRep.spanning_iff_span_image_eq (hInsertSubset d hdD)).mp
        (hInsertSpanning d hdD)
    apply hHNotSpanning
    apply (hRep.spanning_iff_span_image_eq hHE).mpr
    exact hSpanInsert.symm.trans hSpanInsertGround
  obtain ⟨φ, hφd, hSpanKer⟩ :=
    Submodule.exists_le_ker_of_notMem (K := K) hvdNotMem
  refine ⟨φ, ?_, ?_⟩
  · intro x hxH
    apply LinearMap.mem_ker.mp
    apply hSpanKer
    exact Submodule.subset_span (mem_image_of_mem v hxH)
  · intro e heD hφe
    have hSpanInsertGround :
        Submodule.span K (v '' insert e H) = Submodule.span K (v '' M.E) :=
      (hRep.spanning_iff_span_image_eq (hInsertSubset e heD)).mp
        (hInsertSpanning e heD)
    have hInsertKer : Submodule.span K (v '' insert e H) ≤ LinearMap.ker φ := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨x, hx, rfl⟩
      rcases hx with rfl | hxH
      · exact LinearMap.mem_ker.mpr hφe
      · apply hSpanKer
        exact Submodule.subset_span (mem_image_of_mem v hxH)
    apply hφd
    apply LinearMap.mem_ker.mp
    apply hInsertKer
    rw [hSpanInsertGround]
    exact Submodule.subset_span (mem_image_of_mem v hdE)

end Representation

/-! ## Sign bits over an ordered field -/

section SignBits

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The bit of the sign of an ordered-field element: negative is `1` and
nonnegative is `0`.  It is used only on nonzero coefficients below. -/
def negativeBit (x : K) : F2 := if x < 0 then 1 else 0

omit [IsStrictOrderedRing K] in
@[simp] theorem negativeBit_of_neg {x : K} (hx : x < 0) : negativeBit x = 1 := by
  simp [negativeBit, hx]

omit [IsStrictOrderedRing K] in
@[simp] theorem negativeBit_of_pos {x : K} (hx : 0 < x) : negativeBit x = 0 := by
  simp [negativeBit, not_lt.mpr hx.le]

/-- The sign bit turns multiplication of nonzero ordered-field elements into
addition modulo two. -/
theorem negativeBit_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    negativeBit (x * y) = negativeBit x + negativeBit y := by
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · rcases lt_or_gt_of_ne hy with hyneg | hypos
    · have hxy : 0 < x * y := mul_pos_of_neg_of_neg hxneg hyneg
      simp [negativeBit_of_neg hxneg, negativeBit_of_neg hyneg,
        negativeBit_of_pos hxy]
      decide
    · have hxy : x * y < 0 := mul_neg_of_neg_of_pos hxneg hypos
      simp [negativeBit_of_neg hxneg, negativeBit_of_pos hypos,
        negativeBit_of_neg hxy]
  · rcases lt_or_gt_of_ne hy with hyneg | hypos
    · have hxy : x * y < 0 := mul_neg_of_pos_of_neg hxpos hyneg
      simp [negativeBit_of_pos hxpos, negativeBit_of_neg hyneg,
        negativeBit_of_neg hxy]
    · have hxy : 0 < x * y := mul_pos hxpos hypos
      simp [negativeBit_of_pos hxpos, negativeBit_of_pos hypos,
        negativeBit_of_pos hxy]

/-- Two nonzero ordered-field elements summing to zero have opposite sign
bits. -/
theorem negativeBit_add_eq_one_of_add_eq_zero {x y : K}
    (hx : x ≠ 0) (hxy : x + y = 0) :
    negativeBit x + negativeBit y = 1 := by
  have hy : y = -x := by linarith
  subst y
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · have hnegx : 0 < -x := neg_pos.mpr hxneg
    simp [negativeBit_of_neg hxneg, negativeBit_of_pos hnegx]
  · have hnegx : -x < 0 := neg_lt_zero.mpr hxpos
    simp [negativeBit_of_pos hxpos, negativeBit_of_neg hnegx]

end SignBits

/-! ## Ordered-field representations are weakly orientable -/

/-- Every matroid represented over an ordered field is weakly orientable in
the Bland--Jensen sense.

For each circuit we choose its full-support minimal linear dependence.  For
each cocircuit we choose a linear functional which vanishes on its complement
and is nonzero on every cocircuit element.  Applying the latter functional to
the former dependence leaves exactly two nonzero summands whenever the
circuit--cocircuit intersection has size two.  Those products have opposite
signs, which is precisely the four-bit Bland--Jensen equation.
-/
theorem Represents.weaklyOrientable
    {K V α : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [AddCommGroup V] [Module K V] {M : Matroid α} {v : α → V}
    (hRep : Represents K M v) : WeaklyOrientable M := by
  classical
  let circuitRelation : Set α → (α →₀ K) := fun C ↦
    if hC : M.IsCircuit C then
      Classical.choose (hRep.exists_circuit_relation hC)
    else 0
  have circuitRelation_spec (C : Set α) (hC : M.IsCircuit C) :
      Finsupp.linearCombination K v (circuitRelation C) = 0 ∧
        (∀ e ∈ C, circuitRelation C e ≠ 0) ∧
          ((circuitRelation C).support : Set α) = C := by
    simp only [circuitRelation, dif_pos hC]
    exact Classical.choose_spec (hRep.exists_circuit_relation hC)
  let cocircuitCovector : Set α → (V →ₗ[K] K) := fun D ↦
    if hD : M.IsCocircuit D then
      Classical.choose (hRep.exists_cocircuit_covector hD)
    else 0
  have cocircuitCovector_spec (D : Set α) (hD : M.IsCocircuit D) :
      (∀ x ∈ M.E \ D, cocircuitCovector D (v x) = 0) ∧
        (∀ e ∈ D, cocircuitCovector D (v e) ≠ 0) := by
    simp only [cocircuitCovector, dif_pos hD]
    exact Classical.choose_spec (hRep.exists_cocircuit_covector hD)
  refine ⟨fun C e ↦ negativeBit (circuitRelation C e),
    fun D e ↦ negativeBit (cocircuitCovector D (v e)), ?_⟩
  intro C D e f hC hD hef hCD
  obtain ⟨hRelation, hCoeffNonzero, hSupport⟩ := circuitRelation_spec C hC
  obtain ⟨hCovectorZero, hCovectorNonzero⟩ := cocircuitCovector_spec D hD
  have heCD : e ∈ C ∩ D := by
    rw [hCD]
    simp
  have hfCD : f ∈ C ∩ D := by
    rw [hCD]
    simp
  have heSupport : e ∈ (circuitRelation C).support := by
    exact hSupport.symm.subset heCD.1
  have hfSupport : f ∈ (circuitRelation C).support := by
    exact hSupport.symm.subset hfCD.1
  have hSumAll :
      ∑ x ∈ (circuitRelation C).support,
          circuitRelation C x * cocircuitCovector D (v x) = 0 := by
    have hMapped := congrArg (fun w ↦ cocircuitCovector D w) hRelation
    simp only [map_zero] at hMapped
    rw [Finsupp.linearCombination_apply] at hMapped
    change cocircuitCovector D
      ((circuitRelation C).support.sum fun x ↦ circuitRelation C x • v x) = 0 at hMapped
    simpa only [map_sum, map_smul, smul_eq_mul] using hMapped
  have hTermZero (x : α) (hxSupport : x ∈ (circuitRelation C).support)
      (hxPair : x ∉ ({e, f} : Finset α)) :
      circuitRelation C x * cocircuitCovector D (v x) = 0 := by
    have hxC : x ∈ C := hSupport.subset hxSupport
    have hxNotD : x ∉ D := by
      intro hxD
      have hxPairSet : x ∈ ({e, f} : Set α) := by
        rw [← hCD]
        exact ⟨hxC, hxD⟩
      exact hxPair (by simpa using hxPairSet)
    rw [hCovectorZero x ⟨hC.subset_ground hxC, hxNotD⟩, mul_zero]
  have hPairSubset : ({e, f} : Finset α) ⊆ (circuitRelation C).support := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact heSupport
    · exact hfSupport
  have hTwoTerm :
      circuitRelation C e * cocircuitCovector D (v e) +
          circuitRelation C f * cocircuitCovector D (v f) = 0 := by
    calc
      circuitRelation C e * cocircuitCovector D (v e) +
          circuitRelation C f * cocircuitCovector D (v f) =
          ∑ x ∈ ({e, f} : Finset α),
            circuitRelation C x * cocircuitCovector D (v x) := by
              simp [hef]
      _ = ∑ x ∈ (circuitRelation C).support,
            circuitRelation C x * cocircuitCovector D (v x) := by
              exact Finset.sum_subset hPairSubset hTermZero
      _ = 0 := hSumAll
  have heCoeff : circuitRelation C e ≠ 0 := hCoeffNonzero e heCD.1
  have hfCoeff : circuitRelation C f ≠ 0 := hCoeffNonzero f hfCD.1
  have heCovector : cocircuitCovector D (v e) ≠ 0 :=
    hCovectorNonzero e heCD.2
  have hfCovector : cocircuitCovector D (v f) ≠ 0 :=
    hCovectorNonzero f hfCD.2
  have hOpposite := negativeBit_add_eq_one_of_add_eq_zero
    (mul_ne_zero heCoeff heCovector) hTwoTerm
  rw [negativeBit_mul heCoeff heCovector,
    negativeBit_mul hfCoeff hfCovector] at hOpposite
  simpa only [BlandJensenEquation, add_assoc] using hOpposite

/-- In particular, every rationally representable matroid is weakly
orientable. -/
theorem RationallyRepresentable.weaklyOrientable {α : Type*} {M : Matroid α}
    (hM : RationallyRepresentable M) : WeaklyOrientable M := by
  obtain ⟨d, v, hRep⟩ := hM
  exact hRep.weaklyOrientable

end BlandJensenFormal.BlandJensenMI
