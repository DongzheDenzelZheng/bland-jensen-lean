import BlandJensenFormal.BlandJensenMI.Obstruction
import Mathlib.Combinatorics.Matroid.Minor.Contract
import Mathlib.Combinatorics.Matroid.Map
import Mathlib.Tactic

/-!
# Single-element minors of the Bland--Jensen matroids `MIₙ`

The representative block element in this file is `x0 n`, the element with
block label `X` and internal index zero.  We first give explicit bases
witnessing that `x0`, `1`, and `4` are neither loops nor coloops.  We then
derive, from Mathlib's deletion and contraction base theorems, the six
literal basis predicates used in the rational-representability argument.
-/

namespace BlandJensenFormal.BlandJensenMI

open Set
open scoped Matroid

namespace Family

variable (n : ℕ)

/-! ## Explicit bases and loop/coloop status -/

/-- A displayed basis containing `x0` and omitting `1`. -/
def basisContainingX0WithoutOne : Set (Element n) :=
  C1exchange n (one n)

/-- A displayed basis omitting `x0`. -/
def basisWithoutX0 : Set (Element n) :=
  C2exchange n (y0 n)

/-- A displayed basis omitting `4`. -/
def basisWithoutFour : Set (Element n) :=
  C1exchange n (four n)

theorem basisContainingX0WithoutOne_isBase :
    IsBase n (basisContainingX0WithoutOne n) := by
  exact C1exchange_isBase n (by simp [C1])

theorem basisWithoutX0_isBase : IsBase n (basisWithoutX0 n) := by
  exact C2exchange_isBase n (Set.mem_union_right _ (y0_mem_Y n))

theorem basisWithoutFour_isBase : IsBase n (basisWithoutFour n) := by
  exact C1exchange_isBase n (by simp [C1])

@[simp] theorem x0_mem_basisContainingX0WithoutOne :
    x0 n ∈ basisContainingX0WithoutOne n := by
  exact Set.mem_insert_of_mem _
    ⟨Set.mem_union_right _ (x0_mem_X n), by simp [x0, one]⟩

@[simp] theorem one_not_mem_basisContainingX0WithoutOne :
    one n ∉ basisContainingX0WithoutOne n := by
  simp [basisContainingX0WithoutOne, C1exchange, C1, X, blockSet, one, two, four]

@[simp] theorem x0_not_mem_basisWithoutX0 : x0 n ∉ basisWithoutX0 n := by
  simp [basisWithoutX0, C2exchange, C2, Y, blockSet, x0, y0, two, three, four]

@[simp] theorem four_not_mem_basisWithoutFour : four n ∉ basisWithoutFour n := by
  simp [basisWithoutFour, C1exchange]

theorem x0_isNonloop : (MI n).IsNonloop (x0 n) := by
  have hB : (MI n).IsBase (basisContainingX0WithoutOne n) :=
    basisContainingX0WithoutOne_isBase n
  exact hB.indep.isNonloop_of_mem (x0_mem_basisContainingX0WithoutOne n)

theorem one_isNonloop : (MI n).IsNonloop (one n) := by
  have hB : (MI n).IsBase (canonicalBase n) := canonicalBase_isBase n
  exact hB.indep.isNonloop_of_mem (by simp [canonicalBase])

theorem four_isNonloop : (MI n).IsNonloop (four n) := by
  have hB : (MI n).IsBase (canonicalBase n) := canonicalBase_isBase n
  exact hB.indep.isNonloop_of_mem (by simp [canonicalBase])

theorem x0_not_isColoop : ¬ (MI n).IsColoop (x0 n) := by
  intro hx
  have hB : (MI n).IsBase (basisWithoutX0 n) := basisWithoutX0_isBase n
  exact x0_not_mem_basisWithoutX0 n (hx.mem_of_isBase hB)

theorem one_not_isColoop : ¬ (MI n).IsColoop (one n) := by
  intro h1
  have hB : (MI n).IsBase (basisContainingX0WithoutOne n) :=
    basisContainingX0WithoutOne_isBase n
  exact one_not_mem_basisContainingX0WithoutOne n (h1.mem_of_isBase hB)

theorem four_not_isColoop : ¬ (MI n).IsColoop (four n) := by
  intro h4
  have hB : (MI n).IsBase (basisWithoutFour n) := basisWithoutFour_isBase n
  exact four_not_mem_basisWithoutFour n (h4.mem_of_isBase hB)

private theorem singleton_coindep_of_isBase_notMem
    {e : Element n} {B : Set (Element n)}
    (hB : (MI n).IsBase B) (heB : e ∉ B) : (MI n).Coindep {e} := by
  rw [Matroid.coindep_iff_subset_compl_isBase]
  exact ⟨B, hB, by simp [heB]⟩

theorem x0_singleton_coindep : (MI n).Coindep {x0 n} := by
  apply singleton_coindep_of_isBase_notMem n
    (B := basisWithoutX0 n) (basisWithoutX0_isBase n)
  exact x0_not_mem_basisWithoutX0 n

theorem one_singleton_coindep : (MI n).Coindep {one n} := by
  apply singleton_coindep_of_isBase_notMem n
    (B := basisContainingX0WithoutOne n) (basisContainingX0WithoutOne_isBase n)
  exact one_not_mem_basisContainingX0WithoutOne n

theorem four_singleton_coindep : (MI n).Coindep {four n} := by
  apply singleton_coindep_of_isBase_notMem n
    (B := basisWithoutFour n) (basisWithoutFour_isBase n)
  exact four_not_mem_basisWithoutFour n

private theorem delete_singleton_isBase_iff_of_coindep
    {e : Element n} (he : (MI n).Coindep {e}) (B : Set (Element n)) :
    ((MI n) ＼ {e}).IsBase B ↔ IsBase n B ∧ e ∉ B := by
  simpa using (he.delete_isBase_iff (B := B))

private theorem contract_singleton_isBase_iff_of_nonloop
    {e : Element n} (he : (MI n).IsNonloop e) (B : Set (Element n)) :
    ((MI n) ／ {e}).IsBase B ↔ IsBase n (insert e B) ∧ e ∉ B := by
  simpa [union_singleton] using (he.indep.contract_isBase_iff (B := B))

/-! ## Elementary set rewrites used by the six predicates -/

private theorem ne_of_notMem_of_mem {B S : Set (Element n)} {e : Element n}
    (heB : e ∉ B) (heS : e ∈ S) : B ≠ S := by
  intro h
  exact heB (h.symm ▸ heS)

private theorem not_subset_diff_of_not_subset {B H : Set (Element n)} {e : Element n}
    (h : ¬ B ⊆ H) : ¬ B ⊆ H \ {e} :=
  fun h' ↦ h (h'.trans Set.diff_subset)

private theorem not_subset_of_not_subset_diff {B H : Set (Element n)} {e : Element n}
    (heB : e ∉ B) (h : ¬ B ⊆ H \ {e}) : ¬ B ⊆ H := by
  intro hBH
  apply h
  rw [Set.subset_diff]
  exact ⟨hBH, by simpa [Set.disjoint_singleton_right] using heB⟩

private theorem insert_eq_iff_eq_diff {B S : Set (Element n)} {e : Element n}
    (heB : e ∉ B) (heS : e ∈ S) : insert e B = S ↔ B = S \ {e} := by
  constructor
  · intro h
    have h' := congrArg (fun X : Set (Element n) ↦ X \ {e}) h
    simpa [heB] using h'
  · intro h
    rw [h, Set.insert_diff_singleton, Set.insert_eq_of_mem heS]

private theorem subset_insert_iff_of_notMem {B S : Set (Element n)} {e : Element n}
    (heS : e ∉ S) : S ⊆ insert e B ↔ S ⊆ B := by
  constructor
  · intro h x hxS
    rcases h hxS with hxe | hxB
    · exact (heS (hxe ▸ hxS)).elim
    · exact hxB
  · exact fun h ↦ h.trans (Set.subset_insert e B)

private theorem insert_subset_iff_subset_diff {B H : Set (Element n)} {e : Element n}
    (heB : e ∉ B) (heH : e ∈ H) : insert e B ⊆ H ↔ B ⊆ H \ {e} := by
  rw [Set.insert_subset_iff, Set.subset_diff]
  simp only [heH, true_and]
  constructor
  · intro hBH
    refine ⟨hBH, ?_⟩
    rw [Set.disjoint_left]
    intro x hxB hx
    have hxe : x = e := by simpa using hx
    exact heB (hxe ▸ hxB)
  · exact And.left

private theorem subset_delete_ground_iff_notMem {B : Set (Element n)} {e : Element n} :
    B ⊆ ((MI n) ＼ {e}).E ↔ e ∉ B := by
  rw [Matroid.delete_ground, MI_ground, ground, Set.subset_diff]
  constructor
  · intro h heB
    exact Set.disjoint_left.1 h.2 heB (by simp)
  · intro heB
    refine ⟨Set.subset_univ B, ?_⟩
    rw [Set.disjoint_left]
    intro x hxB hx
    have hxe : x = e := by simpa using hx
    exact heB (hxe ▸ hxB)

private theorem subset_contract_ground_iff_notMem {B : Set (Element n)} {e : Element n} :
    B ⊆ ((MI n) ／ {e}).E ↔ e ∉ B := by
  rw [Matroid.contract_ground, MI_ground, ground, Set.subset_diff]
  constructor
  · intro h heB
    exact Set.disjoint_left.1 h.2 heB (by simp)
  · intro heB
    refine ⟨Set.subset_univ B, ?_⟩
    rw [Set.disjoint_left]
    intro x hxB hx
    have hxe : x = e := by simpa using hx
    exact heB (hxe ▸ hxB)

/-! ## Deletion predicates -/

/-- Exact basis predicate for deletion of the fixed block representative
`x0 ∈ X`. -/
theorem delete_x0_isBase_iff (B : Set (Element n)) :
    (((MI n) ＼ {x0 n}).IsBase B) ↔
      B ⊆ ((MI n) ＼ {x0 n}).E ∧
      B.ncard = n + 3 ∧
      ¬ T n ⊆ B ∧
      B ≠ C2 n ∧ B ≠ C3 n ∧
      ¬ B ⊆ H1 n ∧
      ¬ B ⊆ H2 n \ {x0 n} ∧
      ¬ B ⊆ H3 n \ {x0 n} := by
  rw [delete_singleton_isBase_iff_of_coindep n (x0_singleton_coindep n)]
  constructor
  · rintro ⟨⟨hground, hcard, hT, hC1, hC2, hC3, hH1, hH2, hH3⟩, hxB⟩
    refine ⟨?_, hcard, hT, hC2, hC3, hH1,
      not_subset_diff_of_not_subset n hH2,
      not_subset_diff_of_not_subset n hH3⟩
    rw [Matroid.delete_ground, MI_ground, ground, Set.subset_diff]
    refine ⟨Set.subset_univ B, ?_⟩
    rw [Set.disjoint_left]
    intro x hxB' hx
    have hxx : x = x0 n := by simpa using hx
    exact hxB (hxx ▸ hxB')
  · rintro ⟨hminor, hcard, hT, hC2, hC3, hH1, hH2, hH3⟩
    have hxB : x0 n ∉ B := by
      intro hx
      exact (hminor hx).2 (by simp)
    refine ⟨⟨fun _ _ ↦ mem_ground n _, hcard, hT,
      ne_of_notMem_of_mem n hxB (Set.mem_union_right _ (x0_mem_X n)),
      hC2, hC3, hH1,
      not_subset_of_not_subset_diff n hxB hH2,
      not_subset_of_not_subset_diff n hxB hH3⟩, hxB⟩

/-- Exact basis predicate for deletion of the distinguished element `1`. -/
theorem delete_one_isBase_iff (B : Set (Element n)) :
    (((MI n) ＼ {one n}).IsBase B) ↔
      B ⊆ ((MI n) ＼ {one n}).E ∧
      B.ncard = n + 3 ∧
      B ≠ C2 n ∧ B ≠ C3 n ∧
      ¬ B ⊆ H1 n \ {one n} ∧
      ¬ B ⊆ H2 n ∧ ¬ B ⊆ H3 n := by
  rw [delete_singleton_isBase_iff_of_coindep n (one_singleton_coindep n)]
  constructor
  · rintro ⟨⟨hground, hcard, hT, hC1, hC2, hC3, hH1, hH2, hH3⟩, h1B⟩
    exact ⟨(subset_delete_ground_iff_notMem n).2 h1B,
      hcard, hC2, hC3, not_subset_diff_of_not_subset n hH1, hH2, hH3⟩
  · rintro ⟨hminor, hcard, hC2, hC3, hH1, hH2, hH3⟩
    have h1B : one n ∉ B := (subset_delete_ground_iff_notMem n).1 hminor
    refine ⟨⟨fun _ _ ↦ mem_ground n _, hcard, ?_, ?_, hC2, hC3,
      not_subset_of_not_subset_diff n h1B hH1, hH2, hH3⟩, h1B⟩
    · intro hT
      exact h1B (hT (one_mem_T n))
    · exact ne_of_notMem_of_mem n h1B (by simp [C1])

/-- Exact basis predicate for deletion of the distinguished element `4`. -/
theorem delete_four_isBase_iff (B : Set (Element n)) :
    (((MI n) ＼ {four n}).IsBase B) ↔
      B ⊆ ((MI n) ＼ {four n}).E ∧
      B.ncard = n + 3 ∧
      ¬ T n ⊆ B ∧
      ¬ B ⊆ H1 n ∧ ¬ B ⊆ H2 n ∧ ¬ B ⊆ H3 n := by
  rw [delete_singleton_isBase_iff_of_coindep n (four_singleton_coindep n)]
  constructor
  · rintro ⟨⟨hground, hcard, hT, hC1, hC2, hC3, hH1, hH2, hH3⟩, h4B⟩
    exact ⟨(subset_delete_ground_iff_notMem n).2 h4B,
      hcard, hT, hH1, hH2, hH3⟩
  · rintro ⟨hminor, hcard, hT, hH1, hH2, hH3⟩
    have h4B : four n ∉ B := (subset_delete_ground_iff_notMem n).1 hminor
    refine ⟨⟨fun _ _ ↦ mem_ground n _, hcard, hT,
      ne_of_notMem_of_mem n h4B (by simp [C1]),
      ne_of_notMem_of_mem n h4B (by simp [C2]),
      ne_of_notMem_of_mem n h4B (by simp [C3]),
      hH1, hH2, hH3⟩, h4B⟩

/-! ## Contraction predicates -/

private theorem insert_ne_of_notMem {B S : Set (Element n)} {e : Element n}
    (heS : e ∉ S) : insert e B ≠ S := by
  intro h
  exact heS (h ▸ Set.mem_insert e B)

private theorem insert_not_subset_of_notMem {B H : Set (Element n)} {e : Element n}
    (heH : e ∉ H) : ¬ insert e B ⊆ H := by
  intro h
  exact heH (h (Set.mem_insert e B))

private theorem subset_insert_iff_diff_subset {B S : Set (Element n)} {e : Element n} :
    S ⊆ insert e B ↔ S \ {e} ⊆ B := by
  constructor
  · intro h x hx
    rcases h hx.1 with hxe | hxB
    · exact (hx.2 (by simpa using hxe)).elim
    · exact hxB
  · intro h x hxS
    by_cases hxe : x = e
    · exact hxe ▸ Set.mem_insert e B
    · exact Set.mem_insert_of_mem e (h ⟨hxS, by simp [hxe]⟩)

theorem T_diff_one : T n \ {one n} = {two n, three n} := by
  ext e
  cases e with
  | special s => fin_cases s <;> simp [T, one, two, three]
  | block b i => simp [T, one, two, three]

/-- Exact basis predicate for contraction of the fixed block representative
`x0 ∈ X`. -/
theorem contract_x0_isBase_iff (B : Set (Element n)) :
    (((MI n) ／ {x0 n}).IsBase B) ↔
      B ⊆ ((MI n) ／ {x0 n}).E ∧
      B.ncard = n + 2 ∧
      ¬ T n ⊆ B ∧
      B ≠ C1 n \ {x0 n} ∧
      ¬ B ⊆ H2 n \ {x0 n} ∧
      ¬ B ⊆ H3 n \ {x0 n} := by
  rw [contract_singleton_isBase_iff_of_nonloop n (x0_isNonloop n)]
  constructor
  · rintro ⟨⟨hground, hinscard, hT, hC1, hC2, hC3, hH1, hH2, hH3⟩, hxB⟩
    have hcard : B.ncard = n + 2 := by
      rw [Set.ncard_insert_of_notMem hxB] at hinscard
      omega
    refine ⟨(subset_contract_ground_iff_notMem n).2 hxB, hcard,
      ?_, ?_, ?_, ?_⟩
    · intro hTB
      exact hT (hTB.trans (Set.subset_insert (x0 n) B))
    · intro hEq
      exact hC1 ((insert_eq_iff_eq_diff n hxB
        (Set.mem_union_right _ (x0_mem_X n))).2 hEq)
    · intro hsub
      exact hH2 ((insert_subset_iff_subset_diff n hxB
        (Set.mem_union_left _ (Set.mem_union_right _ (x0_mem_X n)))).2 hsub)
    · intro hsub
      exact hH3 ((insert_subset_iff_subset_diff n hxB
        (Set.mem_union_left _ (Set.mem_union_right _ (x0_mem_X n)))).2 hsub)
  · rintro ⟨hminor, hcard, hT, hC1, hH2, hH3⟩
    have hxB : x0 n ∉ B := (subset_contract_ground_iff_notMem n).1 hminor
    have hinscard : (insert (x0 n) B).ncard = n + 3 := by
      rw [Set.ncard_insert_of_notMem hxB, hcard]
    refine ⟨⟨fun _ _ ↦ mem_ground n _, hinscard, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hxB⟩
    · intro hTins
      apply hT
      exact (subset_insert_iff_of_notMem n (by
        simp [T, x0, one, two, three])).1 hTins
    · intro hEq
      apply hC1
      exact (insert_eq_iff_eq_diff n hxB
        (Set.mem_union_right _ (x0_mem_X n))).1 hEq
    · exact insert_ne_of_notMem n (by
        simp [C2, Y, blockSet, x0, two, four])
    · exact insert_ne_of_notMem n (by
        simp [C3, Z, blockSet, x0, three, four])
    · exact insert_not_subset_of_notMem n (by
        simp [H1, Y, Z, blockSet, x0, one])
    · intro hsub
      apply hH2
      exact (insert_subset_iff_subset_diff n hxB
        (Set.mem_union_left _ (Set.mem_union_right _ (x0_mem_X n)))).1 hsub
    · intro hsub
      apply hH3
      exact (insert_subset_iff_subset_diff n hxB
        (Set.mem_union_left _ (Set.mem_union_right _ (x0_mem_X n)))).1 hsub

/-- Exact basis predicate for contraction of the distinguished element `1`. -/
theorem contract_one_isBase_iff (B : Set (Element n)) :
    (((MI n) ／ {one n}).IsBase B) ↔
      B ⊆ ((MI n) ／ {one n}).E ∧
      B.ncard = n + 2 ∧
      ¬ ({two n, three n} : Set (Element n)) ⊆ B ∧
      B ≠ C1 n \ {one n} ∧
      ¬ B ⊆ H1 n \ {one n} := by
  rw [contract_singleton_isBase_iff_of_nonloop n (one_isNonloop n)]
  constructor
  · rintro ⟨⟨hground, hinscard, hT, hC1, hC2, hC3, hH1, hH2, hH3⟩, h1B⟩
    have hcard : B.ncard = n + 2 := by
      rw [Set.ncard_insert_of_notMem h1B] at hinscard
      omega
    refine ⟨(subset_contract_ground_iff_notMem n).2 h1B, hcard, ?_, ?_, ?_⟩
    · intro hpair
      apply hT
      apply (subset_insert_iff_diff_subset n).2
      rwa [T_diff_one n]
    · intro hEq
      exact hC1 ((insert_eq_iff_eq_diff n h1B (by simp [C1])).2 hEq)
    · intro hsub
      exact hH1 ((insert_subset_iff_subset_diff n h1B (by simp [H1])).2 hsub)
  · rintro ⟨hminor, hcard, hpair, hC1, hH1⟩
    have h1B : one n ∉ B := (subset_contract_ground_iff_notMem n).1 hminor
    have hinscard : (insert (one n) B).ncard = n + 3 := by
      rw [Set.ncard_insert_of_notMem h1B, hcard]
    refine ⟨⟨fun _ _ ↦ mem_ground n _, hinscard, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, h1B⟩
    · intro hTins
      apply hpair
      rw [← T_diff_one n]
      exact (subset_insert_iff_diff_subset n).1 hTins
    · intro hEq
      apply hC1
      exact (insert_eq_iff_eq_diff n h1B (by simp [C1])).1 hEq
    · exact insert_ne_of_notMem n (by
        simp [C2, Y, blockSet, one, two, four])
    · exact insert_ne_of_notMem n (by
        simp [C3, Z, blockSet, one, three, four])
    · intro hsub
      apply hH1
      exact (insert_subset_iff_subset_diff n h1B (by simp [H1])).1 hsub
    · exact insert_not_subset_of_notMem n (by
        simp [H2, X, Z, blockSet, one, two])
    · exact insert_not_subset_of_notMem n (by
        simp [H3, X, Y, blockSet, one, three])

/-- Exact basis predicate for contraction of the distinguished element `4`. -/
theorem contract_four_isBase_iff (B : Set (Element n)) :
    (((MI n) ／ {four n}).IsBase B) ↔
      B ⊆ ((MI n) ／ {four n}).E ∧
      B.ncard = n + 2 ∧
      ¬ T n ⊆ B ∧
      B ≠ C1 n \ {four n} ∧
      B ≠ C2 n \ {four n} ∧
      B ≠ C3 n \ {four n} := by
  rw [contract_singleton_isBase_iff_of_nonloop n (four_isNonloop n)]
  constructor
  · rintro ⟨⟨hground, hinscard, hT, hC1, hC2, hC3, hH1, hH2, hH3⟩, h4B⟩
    have hcard : B.ncard = n + 2 := by
      rw [Set.ncard_insert_of_notMem h4B] at hinscard
      omega
    refine ⟨(subset_contract_ground_iff_notMem n).2 h4B, hcard, ?_, ?_, ?_, ?_⟩
    · intro hTB
      exact hT (hTB.trans (Set.subset_insert (four n) B))
    · intro hEq
      exact hC1 ((insert_eq_iff_eq_diff n h4B (by simp [C1])).2 hEq)
    · intro hEq
      exact hC2 ((insert_eq_iff_eq_diff n h4B (by simp [C2])).2 hEq)
    · intro hEq
      exact hC3 ((insert_eq_iff_eq_diff n h4B (by simp [C3])).2 hEq)
  · rintro ⟨hminor, hcard, hT, hC1, hC2, hC3⟩
    have h4B : four n ∉ B := (subset_contract_ground_iff_notMem n).1 hminor
    have hinscard : (insert (four n) B).ncard = n + 3 := by
      rw [Set.ncard_insert_of_notMem h4B, hcard]
    refine ⟨⟨fun _ _ ↦ mem_ground n _, hinscard, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, h4B⟩
    · intro hTins
      apply hT
      exact (subset_insert_iff_of_notMem n (four_not_mem_T n)).1 hTins
    · intro hEq
      apply hC1
      exact (insert_eq_iff_eq_diff n h4B (by simp [C1])).1 hEq
    · intro hEq
      apply hC2
      exact (insert_eq_iff_eq_diff n h4B (by simp [C2])).1 hEq
    · intro hEq
      apply hC3
      exact (insert_eq_iff_eq_diff n h4B (by simp [C3])).1 hEq
    · exact insert_not_subset_of_notMem n (by
        simp [H1, Y, Z, blockSet, four, one])
    · exact insert_not_subset_of_notMem n (by
        simp [H2, X, Z, blockSet, four, two])
    · exact insert_not_subset_of_notMem n (by
        simp [H3, X, Y, blockSet, four, three])

/-! ## Relabelling symmetries -/

/-- The inclusion of the three moving distinguished labels into the four
distinguished labels. -/
def movingSpecial (b : Fin 3) : Element n :=
  .special (Fin.castSucc b)

/-- The circuit--hyperplane with block label `b`, written uniformly in the
three block labels. -/
def indexedCircuit (b : Fin 3) : Set (Element n) :=
  {e | e = movingSpecial n b ∨ e = four n ∨ ∃ i, e = .block b i}

/-- The hyperplane with distinguished label `b`, written uniformly in the
three block labels.  It contains that distinguished element and the two
blocks whose labels differ from `b`. -/
def indexedHyperplane (b : Fin 3) : Set (Element n) :=
  {e | e = movingSpecial n b ∨ ∃ c i, c ≠ b ∧ e = .block c i}

@[simp] theorem movingSpecial_zero : movingSpecial n 0 = one n := rfl
@[simp] theorem movingSpecial_one : movingSpecial n 1 = two n := rfl
@[simp] theorem movingSpecial_two : movingSpecial n 2 = three n := rfl

@[simp] theorem indexedCircuit_zero : indexedCircuit n 0 = C1 n := by
  ext e
  cases e with
  | special s => fin_cases s <;> simp [indexedCircuit, C1, X, blockSet, movingSpecial]
  | block b i => fin_cases b <;> simp [indexedCircuit, C1, X, blockSet, movingSpecial]

@[simp] theorem indexedCircuit_one : indexedCircuit n 1 = C2 n := by
  ext e
  cases e with
  | special s => fin_cases s <;> simp [indexedCircuit, C2, Y, blockSet, movingSpecial]
  | block b i => fin_cases b <;> simp [indexedCircuit, C2, Y, blockSet, movingSpecial]

@[simp] theorem indexedCircuit_two : indexedCircuit n 2 = C3 n := by
  ext e
  cases e with
  | special s => fin_cases s <;> simp [indexedCircuit, C3, Z, blockSet, movingSpecial]
  | block b i => fin_cases b <;> simp [indexedCircuit, C3, Z, blockSet, movingSpecial]

@[simp] theorem indexedHyperplane_zero : indexedHyperplane n 0 = H1 n := by
  ext e
  cases e with
  | special s => fin_cases s <;> simp [indexedHyperplane, H1, Y, Z, blockSet, movingSpecial]
  | block b i => fin_cases b <;> simp [indexedHyperplane, H1, Y, Z, blockSet, movingSpecial]

@[simp] theorem indexedHyperplane_one : indexedHyperplane n 1 = H2 n := by
  ext e
  cases e with
  | special s => fin_cases s <;> simp [indexedHyperplane, H2, X, Z, blockSet, movingSpecial]
  | block b i => fin_cases b <;> simp [indexedHyperplane, H2, X, Z, blockSet, movingSpecial]

@[simp] theorem indexedHyperplane_two : indexedHyperplane n 2 = H3 n := by
  ext e
  cases e with
  | special s => fin_cases s <;> simp [indexedHyperplane, H3, X, Y, blockSet, movingSpecial]
  | block b i => fin_cases b <;> simp [indexedHyperplane, H3, X, Y, blockSet, movingSpecial]

/-- The literal admissibility conditions expressed without privileging a
particular ordering of the three block labels. -/
theorem admissible_iff_indexed (B : Set (Element n)) :
    Admissible n B ↔
      ¬ T n ⊆ B ∧
      (∀ b : Fin 3, B ≠ indexedCircuit n b) ∧
      (∀ b : Fin 3, ¬ B ⊆ indexedHyperplane n b) := by
  constructor
  · rintro ⟨hT, hC1, hC2, hC3, hH1, hH2, hH3⟩
    refine ⟨hT, ?_, ?_⟩
    · intro b
      fin_cases b <;> simpa using ‹_›
    · intro b
      fin_cases b <;> simpa using ‹_›
  · rintro ⟨hT, hC, hH⟩
    exact ⟨hT, by simpa using hC 0, by simpa using hC 1,
      by simpa using hC 2, by simpa using hH 0,
      by simpa using hH 1, by simpa using hH 2⟩

/-- Uniform version of the basis presentation, convenient for applying the
full symmetry group. -/
theorem isBase_iff_indexed (B : Set (Element n)) :
    IsBase n B ↔
      B ⊆ ground n ∧ B.ncard = n + 3 ∧
      ¬ T n ⊆ B ∧
      (∀ b : Fin 3, B ≠ indexedCircuit n b) ∧
      (∀ b : Fin 3, ¬ B ⊆ indexedHyperplane n b) := by
  rw [IsBase, admissible_iff_indexed]

/-- Independent permutations of the internal indices in the three blocks. -/
def blockIndexPerm (σ : (b : Fin 3) → Equiv.Perm (Fin (n + 1))) :
    Equiv.Perm (Element n) where
  toFun
    | .special s => .special s
    | .block b i => .block b (σ b i)
  invFun
    | .special s => .special s
    | .block b i => .block b ((σ b).symm i)
  left_inv e := by cases e <;> simp
  right_inv e := by cases e <;> simp

@[simp] theorem blockIndexPerm_special
    (σ : (b : Fin 3) → Equiv.Perm (Fin (n + 1))) (s : Fin 4) :
    blockIndexPerm n σ (.special s) = .special s := rfl

@[simp] theorem blockIndexPerm_block
    (σ : (b : Fin 3) → Equiv.Perm (Fin (n + 1)))
    (b : Fin 3) (i : Fin (n + 1)) :
    blockIndexPerm n σ (.block b i) = .block b (σ b i) := rfl

/-- Extend a permutation of the first three distinguished labels by fixing
the fourth label. -/
def specialPerm (π : Equiv.Perm (Fin 3)) : Equiv.Perm (Fin 4) :=
  (finSumFinEquiv : Fin 3 ⊕ Fin 1 ≃ Fin 4).symm |>.trans
    ((Equiv.sumCongr π (Equiv.refl (Fin 1))).trans
      (finSumFinEquiv : Fin 3 ⊕ Fin 1 ≃ Fin 4))

@[simp] theorem specialPerm_castSucc (π : Equiv.Perm (Fin 3)) (b : Fin 3) :
    specialPerm π (Fin.castSucc b) = Fin.castSucc (π b) := by
  change
    (finSumFinEquiv : Fin 3 ⊕ Fin 1 ≃ Fin 4)
        ((Equiv.sumCongr π (Equiv.refl (Fin 1)))
          ((finSumFinEquiv : Fin 3 ⊕ Fin 1 ≃ Fin 4).symm (Fin.castAdd 1 b))) =
      Fin.castAdd 1 (π b)
  rw [finSumFinEquiv_symm_apply_castAdd]
  exact finSumFinEquiv_apply_left (π b)

@[simp] theorem specialPerm_last (π : Equiv.Perm (Fin 3)) :
    specialPerm π (3 : Fin 4) = 3 := by
  change specialPerm π (Fin.last 3) = Fin.last 3
  change
    (finSumFinEquiv : Fin 3 ⊕ Fin 1 ≃ Fin 4)
        ((Equiv.sumCongr π (Equiv.refl (Fin 1)))
          ((finSumFinEquiv : Fin 3 ⊕ Fin 1 ≃ Fin 4).symm (Fin.last 3))) =
      Fin.last 3
  rw [finSumFinEquiv_symm_last]
  rfl

/-- Simultaneously permute the three moving distinguished labels and the
three block labels, while fixing the fourth distinguished element. -/
def blockSpecialPerm (π : Equiv.Perm (Fin 3)) : Equiv.Perm (Element n) where
  toFun
    | .special s => .special (specialPerm π s)
    | .block b i => .block (π b) i
  invFun
    | .special s => .special ((specialPerm π).symm s)
    | .block b i => .block (π.symm b) i
  left_inv e := by cases e <;> simp
  right_inv e := by cases e <;> simp

@[simp] theorem blockSpecialPerm_movingSpecial
    (π : Equiv.Perm (Fin 3)) (b : Fin 3) :
    blockSpecialPerm n π (movingSpecial n b) = movingSpecial n (π b) := by
  simp [blockSpecialPerm, movingSpecial]

@[simp] theorem blockSpecialPerm_four (π : Equiv.Perm (Fin 3)) :
    blockSpecialPerm n π (four n) = four n := by
  simp [blockSpecialPerm, four]

@[simp] theorem blockSpecialPerm_block
    (π : Equiv.Perm (Fin 3)) (b : Fin 3) (i : Fin (n + 1)) :
    blockSpecialPerm n π (.block b i) = .block (π b) i := rfl

theorem mem_T_iff_exists_movingSpecial (e : Element n) :
    e ∈ T n ↔ ∃ b : Fin 3, e = movingSpecial n b := by
  constructor
  · intro he
    simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with he | he | he
    · exact ⟨0, by simpa using he⟩
    · exact ⟨1, by simpa using he⟩
    · exact ⟨2, by simpa using he⟩
  · rintro ⟨b, rfl⟩
    fin_cases b <;> simp [T]

private theorem image_eq_of_mem_iff {α : Type*} (f : α ≃ α) {S T : Set α}
    (h : ∀ x, f x ∈ T ↔ x ∈ S) : f '' S = T := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (h x).2 hx
  · intro hy
    refine ⟨f.symm y, ?_, by simp⟩
    exact (h (f.symm y)).1 (by simpa using hy)

@[simp] theorem blockIndexPerm_mem_T_iff
    (σ : (b : Fin 3) → Equiv.Perm (Fin (n + 1))) (e : Element n) :
    blockIndexPerm n σ e ∈ T n ↔ e ∈ T n := by
  cases e with
  | special s => fin_cases s <;> simp [T, one, two, three]
  | block b i => simp [T, one, two, three]

@[simp] theorem blockIndexPerm_mem_indexedCircuit_iff
    (σ : (b : Fin 3) → Equiv.Perm (Fin (n + 1)))
    (b : Fin 3) (e : Element n) :
    blockIndexPerm n σ e ∈ indexedCircuit n b ↔ e ∈ indexedCircuit n b := by
  cases e <;> simp [indexedCircuit, movingSpecial]

@[simp] theorem blockIndexPerm_mem_indexedHyperplane_iff
    (σ : (b : Fin 3) → Equiv.Perm (Fin (n + 1)))
    (b : Fin 3) (e : Element n) :
    blockIndexPerm n σ e ∈ indexedHyperplane n b ↔
      e ∈ indexedHyperplane n b := by
  cases e <;> simp [indexedHyperplane, movingSpecial]

theorem blockIndexPerm_image_T
    (σ : (b : Fin 3) → Equiv.Perm (Fin (n + 1))) :
    blockIndexPerm n σ '' T n = T n :=
  image_eq_of_mem_iff (blockIndexPerm n σ) (blockIndexPerm_mem_T_iff n σ)

theorem blockIndexPerm_image_indexedCircuit
    (σ : (b : Fin 3) → Equiv.Perm (Fin (n + 1))) (b : Fin 3) :
    blockIndexPerm n σ '' indexedCircuit n b = indexedCircuit n b :=
  image_eq_of_mem_iff (blockIndexPerm n σ)
    (blockIndexPerm_mem_indexedCircuit_iff n σ b)

theorem blockIndexPerm_image_indexedHyperplane
    (σ : (b : Fin 3) → Equiv.Perm (Fin (n + 1))) (b : Fin 3) :
    blockIndexPerm n σ '' indexedHyperplane n b = indexedHyperplane n b :=
  image_eq_of_mem_iff (blockIndexPerm n σ)
    (blockIndexPerm_mem_indexedHyperplane_iff n σ b)

@[simp] theorem blockSpecialPerm_mem_T_iff
    (π : Equiv.Perm (Fin 3)) (e : Element n) :
    blockSpecialPerm n π e ∈ T n ↔ e ∈ T n := by
  rw [mem_T_iff_exists_movingSpecial, mem_T_iff_exists_movingSpecial]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨π.symm b, ?_⟩
    apply (blockSpecialPerm n π).injective
    simpa using hb
  · rintro ⟨b, rfl⟩
    exact ⟨π b, by simp⟩

@[simp] theorem blockSpecialPerm_mem_indexedCircuit_iff
    (π : Equiv.Perm (Fin 3)) (b : Fin 3) (e : Element n) :
    blockSpecialPerm n π e ∈ indexedCircuit n (π b) ↔
      e ∈ indexedCircuit n b := by
  change
    (blockSpecialPerm n π e = movingSpecial n (π b) ∨
      blockSpecialPerm n π e = four n ∨
      ∃ i, blockSpecialPerm n π e = .block (π b) i) ↔
    (e = movingSpecial n b ∨ e = four n ∨ ∃ i, e = .block b i)
  constructor
  · rintro (he | he | ⟨i, he⟩)
    · left
      apply (blockSpecialPerm n π).injective
      simpa using he
    · right; left
      apply (blockSpecialPerm n π).injective
      exact he.trans (blockSpecialPerm_four n π).symm
    · right; right
      refine ⟨i, ?_⟩
      apply (blockSpecialPerm n π).injective
      simpa using he
  · rintro (rfl | rfl | ⟨i, rfl⟩)
    · exact Or.inl (by simp)
    · exact Or.inr (Or.inl (blockSpecialPerm_four n π))
    · exact Or.inr (Or.inr ⟨i, by simp⟩)

@[simp] theorem blockSpecialPerm_mem_indexedHyperplane_iff
    (π : Equiv.Perm (Fin 3)) (b : Fin 3) (e : Element n) :
    blockSpecialPerm n π e ∈ indexedHyperplane n (π b) ↔
      e ∈ indexedHyperplane n b := by
  change
    (blockSpecialPerm n π e = movingSpecial n (π b) ∨
      ∃ c i, c ≠ π b ∧ blockSpecialPerm n π e = .block c i) ↔
    (e = movingSpecial n b ∨ ∃ c i, c ≠ b ∧ e = .block c i)
  constructor
  · rintro (he | ⟨c, i, hcb, he⟩)
    · left
      apply (blockSpecialPerm n π).injective
      simpa using he
    · right
      refine ⟨π.symm c, i, ?_, ?_⟩
      · intro hEq
        apply hcb
        simpa using congrArg π hEq
      · apply (blockSpecialPerm n π).injective
        simpa using he
  · rintro (rfl | ⟨c, i, hcb, rfl⟩)
    · exact Or.inl (by simp)
    · right
      refine ⟨π c, i, ?_, by simp⟩
      exact fun hEq ↦ hcb (π.injective hEq)

theorem blockSpecialPerm_image_T (π : Equiv.Perm (Fin 3)) :
    blockSpecialPerm n π '' T n = T n :=
  image_eq_of_mem_iff (blockSpecialPerm n π) (blockSpecialPerm_mem_T_iff n π)

theorem blockSpecialPerm_image_indexedCircuit
    (π : Equiv.Perm (Fin 3)) (b : Fin 3) :
    blockSpecialPerm n π '' indexedCircuit n b = indexedCircuit n (π b) :=
  image_eq_of_mem_iff (blockSpecialPerm n π)
    (blockSpecialPerm_mem_indexedCircuit_iff n π b)

theorem blockSpecialPerm_image_indexedHyperplane
    (π : Equiv.Perm (Fin 3)) (b : Fin 3) :
    blockSpecialPerm n π '' indexedHyperplane n b = indexedHyperplane n (π b) :=
  image_eq_of_mem_iff (blockSpecialPerm n π)
    (blockSpecialPerm_mem_indexedHyperplane_iff n π b)

private theorem isBase_image_iff_of_indexed_symmetry
    (f : Equiv.Perm (Element n)) (q : Equiv.Perm (Fin 3))
    (hTimage : f '' T n = T n)
    (hCimage : ∀ b, f '' indexedCircuit n b = indexedCircuit n (q b))
    (hHimage : ∀ b, f '' indexedHyperplane n b = indexedHyperplane n (q b))
    (B : Set (Element n)) :
    IsBase n (f '' B) ↔ IsBase n B := by
  rw [isBase_iff_indexed, isBase_iff_indexed]
  constructor
  · rintro ⟨hground, hcard, hT, hC, hH⟩
    have hcard' : B.ncard = n + 3 := by
      simpa [Set.ncard_image_of_injective B f.injective] using hcard
    refine ⟨fun _ _ ↦ mem_ground n _, hcard', ?_, ?_, ?_⟩
    · intro hsub
      apply hT
      rw [← hTimage]
      exact Set.image_mono hsub
    · intro b hEq
      apply hC (q b)
      exact (congrArg (Set.image f) hEq).trans (hCimage b)
    · intro b hsub
      apply hH (q b)
      rw [← hHimage b]
      exact Set.image_mono hsub
  · rintro ⟨hground, hcard, hT, hC, hH⟩
    have hcard' : (f '' B).ncard = n + 3 := by
      simpa [Set.ncard_image_of_injective B f.injective] using hcard
    refine ⟨fun _ _ ↦ mem_ground n _, hcard', ?_, ?_, ?_⟩
    · intro hsub
      apply hT
      apply (Set.image_subset_image_iff f.injective).1
      simpa [hTimage] using hsub
    · intro b hEq
      apply hC (q.symm b)
      apply f.injective.image_injective
      calc
        f '' B = indexedCircuit n b := hEq
        _ = indexedCircuit n (q (q.symm b)) := by simp
        _ = f '' indexedCircuit n (q.symm b) := (hCimage (q.symm b)).symm
    · intro b hsub
      apply hH (q.symm b)
      apply (Set.image_subset_image_iff f.injective).1
      rw [hHimage]
      simpa using hsub

/-- The basis presentation is invariant under arbitrary, independent
permutations within the three blocks. -/
theorem blockIndexPerm_isBase_image_iff
    (σ : (b : Fin 3) → Equiv.Perm (Fin (n + 1))) (B : Set (Element n)) :
    IsBase n (blockIndexPerm n σ '' B) ↔ IsBase n B := by
  apply isBase_image_iff_of_indexed_symmetry n
    (blockIndexPerm n σ) (Equiv.refl (Fin 3))
  · exact blockIndexPerm_image_T n σ
  · intro b
    simpa using blockIndexPerm_image_indexedCircuit n σ b
  · intro b
    simpa using blockIndexPerm_image_indexedHyperplane n σ b

/-- The basis presentation is invariant under the simultaneous `S₃` action
on the moving distinguished labels and on the three blocks. -/
theorem blockSpecialPerm_isBase_image_iff
    (π : Equiv.Perm (Fin 3)) (B : Set (Element n)) :
    IsBase n (blockSpecialPerm n π '' B) ↔ IsBase n B := by
  exact isBase_image_iff_of_indexed_symmetry n
    (blockSpecialPerm n π) π
    (blockSpecialPerm_image_T n π)
    (blockSpecialPerm_image_indexedCircuit n π)
    (blockSpecialPerm_image_indexedHyperplane n π) B

/-- Internal block-index permutations act by automorphisms of `MIₙ`. -/
theorem MI_mapEquiv_blockIndexPerm
    (σ : (b : Fin 3) → Equiv.Perm (Fin (n + 1))) :
    (MI n).mapEquiv (blockIndexPerm n σ) = MI n := by
  apply Matroid.ext_isBase
  · simp [MI_ground, ground]
  · intro B hB
    simp only [Matroid.mapEquiv_isBase_iff, MI_isBase_iff]
    have h := blockIndexPerm_isBase_image_iff n σ
      ((blockIndexPerm n σ).symm '' B)
    simpa using h.symm

/-- Simultaneous permutations of the three moving labels and blocks act by
automorphisms of `MIₙ`. -/
theorem MI_mapEquiv_blockSpecialPerm (π : Equiv.Perm (Fin 3)) :
    (MI n).mapEquiv (blockSpecialPerm n π) = MI n := by
  apply Matroid.ext_isBase
  · simp [MI_ground, ground]
  · intro B hB
    simp only [Matroid.mapEquiv_isBase_iff, MI_isBase_iff]
    have h := blockSpecialPerm_isBase_image_iff n π
      ((blockSpecialPerm n π).symm '' B)
    simpa using h.symm

/-! ### Relabelling and minors -/

/-- Successive relabellings agree with relabelling by the composite
equivalence. -/
theorem mapEquiv_trans (M : Matroid (Element n))
    (f g : Equiv.Perm (Element n)) :
    (M.mapEquiv f).mapEquiv g = M.mapEquiv (f.trans g) := by
  apply Matroid.ext_isBase
  · simp only [Matroid.mapEquiv_ground_eq]
    rw [Set.image_image]
    rfl
  · intro B hB
    simp only [Matroid.mapEquiv_isBase_iff]
    rw [Set.image_image]
    rfl

private theorem disjoint_symm_image_iff (f : Equiv.Perm (Element n))
    (I D : Set (Element n)) :
    Disjoint (f.symm '' I) D ↔ Disjoint I (f '' D) := by
  rw [Set.disjoint_left, Set.disjoint_left]
  constructor
  · intro h x hxI hxD
    rcases hxD with ⟨d, hdD, hdx⟩
    apply h
    · refine ⟨x, hxI, ?_⟩
      simpa using (congrArg f.symm hdx).symm
    · exact hdD
  · intro h d hdI hdD
    rcases hdI with ⟨x, hxI, hxd⟩
    apply h hxI
    refine ⟨d, hdD, ?_⟩
    simpa using (congrArg f hxd).symm

/-- Deletion commutes with bijective relabelling. -/
theorem mapEquiv_delete (M : Matroid (Element n))
    (f : Equiv.Perm (Element n)) (D : Set (Element n)) :
    (M ＼ D).mapEquiv f = (M.mapEquiv f) ＼ (f '' D) := by
  apply Matroid.ext_indep
  · simp only [Matroid.mapEquiv_ground_eq, Matroid.delete_ground]
    exact Set.image_diff f.injective M.E D
  · intro I hI
    simp only [Matroid.mapEquiv_indep_iff, Matroid.delete_indep_iff]
    exact and_congr_right (fun _ ↦ disjoint_symm_image_iff n f I D)

/-- Duality commutes with bijective relabelling. -/
theorem mapEquiv_dual (M : Matroid (Element n))
    (f : Equiv.Perm (Element n)) :
    (M.mapEquiv f)✶ = M✶.mapEquiv f := by
  simp [Matroid.mapEquiv_eq_map]

/-- Contraction commutes with bijective relabelling. -/
theorem mapEquiv_contract (M : Matroid (Element n))
    (f : Equiv.Perm (Element n)) (C : Set (Element n)) :
    (M ／ C).mapEquiv f = (M.mapEquiv f) ／ (f '' C) := by
  rw [← Matroid.dual_inj]
  rw [mapEquiv_dual, Matroid.dual_contract, mapEquiv_delete,
    Matroid.dual_contract, mapEquiv_dual]

private theorem mapEquiv_trans_automorphism
    (M : Matroid (Element n)) (f g : Equiv.Perm (Element n))
    (hf : M.mapEquiv f = M) (hg : M.mapEquiv g = M) :
    M.mapEquiv (f.trans g) = M := by
  rw [← mapEquiv_trans, hf, hg]

private theorem delete_mapEquiv_eq_of_automorphism
    (M : Matroid (Element n)) (f : Equiv.Perm (Element n))
    (hf : M.mapEquiv f = M) {e r : Element n} (her : f e = r) :
    (M ＼ {e}).mapEquiv f = M ＼ {r} := by
  rw [mapEquiv_delete, hf]
  simp [her]

private theorem contract_mapEquiv_eq_of_automorphism
    (M : Matroid (Element n)) (f : Equiv.Perm (Element n))
    (hf : M.mapEquiv f = M) {e r : Element n} (her : f e = r) :
    (M ／ {e}).mapEquiv f = M ／ {r} := by
  rw [mapEquiv_contract, hf]
  simp [her]

/-! ### The three element orbits and the six representative minors -/

/-- Permute only the internal indices of block `b`, exchanging `i` with
zero. -/
def targetedIndexFamily (b : Fin 3) (i : Fin (n + 1)) :
    (c : Fin 3) → Equiv.Perm (Fin (n + 1)) :=
  fun c ↦ if c = b then Equiv.swap i 0 else Equiv.refl _

/-- An explicit automorphism sending the block element `(b,i)` to `x0`:
first exchange its internal index with zero, then exchange its block label
with `X`. -/
def blockToX0Perm (b : Fin 3) (i : Fin (n + 1)) :
    Equiv.Perm (Element n) :=
  (blockIndexPerm n (targetedIndexFamily n b i)).trans
    (blockSpecialPerm n (Equiv.swap b 0))

@[simp] theorem blockToX0Perm_apply (b : Fin 3) (i : Fin (n + 1)) :
    blockToX0Perm n b i (.block b i) = x0 n := by
  simp [blockToX0Perm, targetedIndexFamily, Equiv.trans_apply,
    Equiv.swap_apply_left, x0]

theorem MI_mapEquiv_blockToX0Perm (b : Fin 3) (i : Fin (n + 1)) :
    (MI n).mapEquiv (blockToX0Perm n b i) = MI n := by
  exact mapEquiv_trans_automorphism n (MI n)
    (blockIndexPerm n (targetedIndexFamily n b i))
    (blockSpecialPerm n (Equiv.swap b 0))
    (MI_mapEquiv_blockIndexPerm n (targetedIndexFamily n b i))
    (MI_mapEquiv_blockSpecialPerm n (Equiv.swap b 0))

@[simp] theorem blockSpecialSwap_apply_movingSpecial (b : Fin 3) :
    blockSpecialPerm n (Equiv.swap b 0) (movingSpecial n b) = one n := by
  rw [blockSpecialPerm_movingSpecial, Equiv.swap_apply_left]
  rfl

/-- Every element belongs to one of the three automorphism classes needed for
the minor reduction: block elements, the moving distinguished elements
`1,2,3`, and the fixed distinguished element `4`.  The statement supplies an
explicit automorphism carrying any element to the displayed representative. -/
theorem automorphism_orbit_classification (e : Element n) :
    (∃ f : Equiv.Perm (Element n),
        f e = x0 n ∧ (MI n).mapEquiv f = MI n) ∨
    (∃ f : Equiv.Perm (Element n),
        f e = one n ∧ (MI n).mapEquiv f = MI n) ∨
    (∃ f : Equiv.Perm (Element n),
        f e = four n ∧ (MI n).mapEquiv f = MI n) := by
  cases e with
  | block b i =>
      exact Or.inl ⟨blockToX0Perm n b i, blockToX0Perm_apply n b i,
        MI_mapEquiv_blockToX0Perm n b i⟩
  | special s =>
      fin_cases s
      · exact Or.inr <| Or.inl ⟨blockSpecialPerm n (Equiv.swap 0 0),
          by simpa [movingSpecial] using blockSpecialSwap_apply_movingSpecial n 0,
          MI_mapEquiv_blockSpecialPerm n (Equiv.swap 0 0)⟩
      · exact Or.inr <| Or.inl ⟨blockSpecialPerm n (Equiv.swap 1 0),
          by simpa [movingSpecial] using blockSpecialSwap_apply_movingSpecial n 1,
          MI_mapEquiv_blockSpecialPerm n (Equiv.swap 1 0)⟩
      · exact Or.inr <| Or.inl ⟨blockSpecialPerm n (Equiv.swap 2 0),
          by simpa [movingSpecial] using blockSpecialSwap_apply_movingSpecial n 2,
          MI_mapEquiv_blockSpecialPerm n (Equiv.swap 2 0)⟩
      · exact Or.inr <| Or.inr ⟨blockSpecialPerm n (Equiv.refl (Fin 3)),
          by simpa [four] using blockSpecialPerm_four n (Equiv.refl (Fin 3)),
          MI_mapEquiv_blockSpecialPerm n (Equiv.refl (Fin 3))⟩

/-- Every one-element deletion is a relabelling of one of the three displayed
deletion representatives. -/
theorem delete_orbit_classification (e : Element n) :
    (∃ f : Equiv.Perm (Element n),
        ((MI n) ＼ {e}).mapEquiv f = (MI n) ＼ {x0 n}) ∨
    (∃ f : Equiv.Perm (Element n),
        ((MI n) ＼ {e}).mapEquiv f = (MI n) ＼ {one n}) ∨
    (∃ f : Equiv.Perm (Element n),
        ((MI n) ＼ {e}).mapEquiv f = (MI n) ＼ {four n}) := by
  rcases automorphism_orbit_classification n e with h | h | h
  · rcases h with ⟨f, hfe, hf⟩
    exact Or.inl ⟨f, delete_mapEquiv_eq_of_automorphism n (MI n) f hf hfe⟩
  · rcases h with ⟨f, hfe, hf⟩
    exact Or.inr <| Or.inl
      ⟨f, delete_mapEquiv_eq_of_automorphism n (MI n) f hf hfe⟩
  · rcases h with ⟨f, hfe, hf⟩
    exact Or.inr <| Or.inr
      ⟨f, delete_mapEquiv_eq_of_automorphism n (MI n) f hf hfe⟩

/-- Every one-element contraction is a relabelling of one of the three
displayed contraction representatives. -/
theorem contract_orbit_classification (e : Element n) :
    (∃ f : Equiv.Perm (Element n),
        ((MI n) ／ {e}).mapEquiv f = (MI n) ／ {x0 n}) ∨
    (∃ f : Equiv.Perm (Element n),
        ((MI n) ／ {e}).mapEquiv f = (MI n) ／ {one n}) ∨
    (∃ f : Equiv.Perm (Element n),
        ((MI n) ／ {e}).mapEquiv f = (MI n) ／ {four n}) := by
  rcases automorphism_orbit_classification n e with h | h | h
  · rcases h with ⟨f, hfe, hf⟩
    exact Or.inl ⟨f, contract_mapEquiv_eq_of_automorphism n (MI n) f hf hfe⟩
  · rcases h with ⟨f, hfe, hf⟩
    exact Or.inr <| Or.inl
      ⟨f, contract_mapEquiv_eq_of_automorphism n (MI n) f hf hfe⟩
  · rcases h with ⟨f, hfe, hf⟩
    exact Or.inr <| Or.inr
      ⟨f, contract_mapEquiv_eq_of_automorphism n (MI n) f hf hfe⟩

end Family

end BlandJensenFormal.BlandJensenMI
