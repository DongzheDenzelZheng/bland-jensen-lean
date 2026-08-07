import BlandJensenFormal.BlandJensenMI.Family
import BlandJensenFormal.BlandJensenNineCell
import Mathlib.Tactic

/-!
# Circuits, cocircuits, and the Bland--Jensen obstruction for `MIₙ`

This file connects the explicit basis presentation of `MIₙ` to the standard
Mathlib circuit and cocircuit predicates.  In particular, no circuit or
cocircuit assertion is postulated: every one is derived from the basis
predicate in `Family.lean`.
-/

/-- A hyperplane is a maximal nonspanning subset of the ground set.  This is
equivalent to the usual definition as a maximal proper flat. -/
def _root_.Matroid.IsHyperplane {α : Type*} (M : Matroid α) (H : Set α) : Prop :=
  Maximal (fun X ↦ X ⊆ M.E ∧ ¬ M.Spanning X) H

namespace BlandJensenFormal.BlandJensenMI

open Set
open PhaseObstructionAlgebra

namespace Family

variable (n : ℕ)

/-! ## Elementary independence helpers -/

theorem indep_of_subset_isBase {I B : Set (Element n)}
    (hB : IsBase n B) (hIB : I ⊆ B) : (MI n).Indep I := by
  rw [Matroid.indep_iff]
  exact ⟨B, hB, hIB⟩

theorem not_indep_of_forbidden_subset {I : Set (Element n)}
    (hTI : T n ⊆ I) : ¬ (MI n).Indep I := by
  intro hI
  obtain ⟨B, hB, hIB⟩ := (Matroid.indep_iff.1 hI)
  exact IsBase.not_T_subset n hB (hTI.trans hIB)

/-! ## The small circuit `T` -/

private def base13 : Set (Element n) :=
  {one n, three n, four n} ∪ initialX n

private def base23 : Set (Element n) :=
  {two n, three n, four n} ∪ initialX n

private theorem base13_isBase : IsBase n (base13 n) := by
  refine ⟨fun _ _ ↦ mem_ground n _, ?_, ?_⟩
  · rw [base13, Set.ncard_union_eq]
    · simp [one, three, four, Nat.add_comm]
    rw [Set.disjoint_left]
    intro e he hX
    rcases he with (rfl | he)
    · exact special_not_mem_initialX n 0 hX
    rcases he with (rfl | he)
    · exact special_not_mem_initialX n 2 hX
    rcases he with (rfl | hfalse)
    exact special_not_mem_initialX n 3 hX
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hT
    have htwo := hT (two_mem_T n)
    simp [base13, initialX, one, two, three, four] at htwo
  · intro hEq
    have hthree : three n ∈ C1 n := hEq ▸ (show three n ∈ base13 n by simp [base13])
    simp [C1, X, blockSet, one, three, four] at hthree
  · intro hEq
    have hone : one n ∈ C2 n := hEq ▸ (show one n ∈ base13 n by simp [base13])
    simp [C2, Y, blockSet, one, two, four] at hone
  · intro hEq
    have hone : one n ∈ C3 n := hEq ▸ (show one n ∈ base13 n by simp [base13])
    simp [C3, Z, blockSet, one, three, four] at hone
  · intro hsub
    have hfour := hsub (show four n ∈ base13 n by simp [base13])
    simp [H1, Y, Z, blockSet, four] at hfour
  · intro hsub
    have hfour := hsub (show four n ∈ base13 n by simp [base13])
    simp [H2, X, Z, blockSet, four] at hfour
  · intro hsub
    have hfour := hsub (show four n ∈ base13 n by simp [base13])
    simp [H3, X, Y, blockSet, four] at hfour

private theorem base23_isBase : IsBase n (base23 n) := by
  refine ⟨fun _ _ ↦ mem_ground n _, ?_, ?_⟩
  · rw [base23, Set.ncard_union_eq]
    · simp [two, three, four, Nat.add_comm]
    rw [Set.disjoint_left]
    intro e he hX
    rcases he with (rfl | he)
    · exact special_not_mem_initialX n 1 hX
    rcases he with (rfl | he)
    · exact special_not_mem_initialX n 2 hX
    rcases he with (rfl | hfalse)
    exact special_not_mem_initialX n 3 hX
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hT
    have hone := hT (one_mem_T n)
    simp [base23, initialX, one, two, three, four] at hone
  · intro hEq
    have htwo : two n ∈ C1 n := hEq ▸ (show two n ∈ base23 n by simp [base23])
    simp [C1, X, blockSet, one, two, four] at htwo
  · intro hEq
    have hthree : three n ∈ C2 n := hEq ▸ (show three n ∈ base23 n by simp [base23])
    simp [C2, Y, blockSet, two, three, four] at hthree
  · intro hEq
    have htwo : two n ∈ C3 n := hEq ▸ (show two n ∈ base23 n by simp [base23])
    simp [C3, Z, blockSet, two, three, four] at htwo
  · intro hsub
    have hfour := hsub (show four n ∈ base23 n by simp [base23])
    simp [H1, Y, Z, blockSet, four] at hfour
  · intro hsub
    have hfour := hsub (show four n ∈ base23 n by simp [base23])
    simp [H2, X, Z, blockSet, four] at hfour
  · intro hsub
    have hfour := hsub (show four n ∈ base23 n by simp [base23])
    simp [H3, X, Y, blockSet, four] at hfour

theorem T_isCircuit : (MI n).IsCircuit (T n) := by
  rw [Matroid.isCircuit_iff_dep_forall_diff_singleton_indep]
  constructor
  · exact ⟨not_indep_of_forbidden_subset n Subset.rfl,
      fun _ _ ↦ mem_ground n _⟩
  intro e he
  simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at he
  rcases he with rfl | rfl | rfl
  · apply indep_of_subset_isBase n (base23_isBase n)
    rintro x ⟨hx, hxne⟩
    simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · simp at hxne
    · simp [base23]
    · simp [base23]
  · apply indep_of_subset_isBase n (base13_isBase n)
    rintro x ⟨hx, hxne⟩
    simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · simp [base13]
    · simp at hxne
    · simp [base13]
  · apply indep_of_subset_isBase n (canonicalBase_isBase n)
    rintro x ⟨hx, hxne⟩
    simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · simp [canonicalBase]
    · simp [canonicalBase]
    · simp at hxne

/-! ## The three rank-size circuits -/

def C1exchange (e : Element n) : Set (Element n) :=
  insert (two n) (C1 n \ {e})

def C2exchange (e : Element n) : Set (Element n) :=
  insert (three n) (C2 n \ {e})

def C3exchange (e : Element n) : Set (Element n) :=
  insert (one n) (C3 n \ {e})

private theorem mem_insert_diff_of_mem_of_ne {S : Set (Element n)}
    {x e f : Element n} (hxS : x ∈ S) (hxe : x ≠ e) :
    x ∈ insert f (S \ {e}) :=
  Set.mem_insert_of_mem f ⟨hxS, by simpa using hxe⟩

theorem C1exchange_isBase {e : Element n} (he : e ∈ C1 n) :
    IsBase n (C1exchange n e) := by
  refine ⟨fun _ _ ↦ mem_ground n _, ?_, ?_⟩
  · rw [C1exchange, Set.ncard_insert_of_notMem, Set.ncard_diff_singleton_of_mem he,
      ncard_C1]
    · omega
    simp [C1, X, blockSet, two, one, four]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hT
    have hthree := hT (three_mem_T n)
    simp [C1exchange, C1, X, blockSet, one, two, three, four] at hthree
  · intro hEq
    have htwo : two n ∈ C1 n := hEq ▸ (show two n ∈ C1exchange n e by simp [C1exchange])
    simp [C1, X, blockSet, one, two, four] at htwo
  · intro hEq
    by_cases he1 : e = one n
    · subst e
      have hx : x0 n ∈ C2 n := hEq ▸
        (mem_insert_diff_of_mem_of_ne n
          (Set.mem_union_right _ (x0_mem_X n)) (by simp [x0, one]))
      simp [C2, Y, blockSet, x0] at hx
    · have hone : one n ∈ C2 n := hEq ▸
        (mem_insert_diff_of_mem_of_ne n (by simp [C1]) (Ne.symm he1))
      simp [C2, Y, blockSet, one, two, four] at hone
  · intro hEq
    by_cases he1 : e = one n
    · subst e
      have hx : x0 n ∈ C3 n := hEq ▸
        (mem_insert_diff_of_mem_of_ne n
          (Set.mem_union_right _ (x0_mem_X n)) (by simp [x0, one]))
      simp [C3, Z, blockSet, x0] at hx
    · have hone : one n ∈ C3 n := hEq ▸
        (mem_insert_diff_of_mem_of_ne n (by simp [C1]) (Ne.symm he1))
      simp [C3, Z, blockSet, one, three, four] at hone
  · intro hsub
    have htwo := hsub (show two n ∈ C1exchange n e by simp [C1exchange])
    simp [H1, Y, Z, blockSet, two] at htwo
  · intro hsub
    by_cases he4 : e = four n
    · subst e
      have hone := hsub (show one n ∈ C1exchange n (four n) by
        exact mem_insert_diff_of_mem_of_ne n (by simp [C1]) (one_ne_four n))
      simp [H2, X, Z, blockSet, one, two] at hone
    · have hfour := hsub (show four n ∈ C1exchange n e by
        exact mem_insert_diff_of_mem_of_ne n (by simp [C1]) (Ne.symm he4))
      simp [H2, X, Z, blockSet, four, two] at hfour
  · intro hsub
    have htwo := hsub (show two n ∈ C1exchange n e by simp [C1exchange])
    simp [H3, X, Y, blockSet, two, three] at htwo

theorem C2exchange_isBase {e : Element n} (he : e ∈ C2 n) :
    IsBase n (C2exchange n e) := by
  refine ⟨fun _ _ ↦ mem_ground n _, ?_, ?_⟩
  · rw [C2exchange, Set.ncard_insert_of_notMem, Set.ncard_diff_singleton_of_mem he,
      ncard_C2]
    · omega
    simp [C2, Y, blockSet, three, two, four]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hT
    have hone := hT (one_mem_T n)
    simp [C2exchange, C2, Y, blockSet, one, two, three, four] at hone
  · intro hEq
    by_cases he2 : e = two n
    · subst e
      have hy : y0 n ∈ C1 n := hEq ▸
        (mem_insert_diff_of_mem_of_ne n
          (Set.mem_union_right _ (y0_mem_Y n)) (by simp [y0, two]))
      simp [C1, X, blockSet, y0] at hy
    · have htwo : two n ∈ C1 n := hEq ▸
        (mem_insert_diff_of_mem_of_ne n (by simp [C2]) (Ne.symm he2))
      simp [C1, X, blockSet, one, two, four] at htwo
  · intro hEq
    have hthree : three n ∈ C2 n := hEq ▸
      (show three n ∈ C2exchange n e by simp [C2exchange])
    simp [C2, Y, blockSet, two, three, four] at hthree
  · intro hEq
    by_cases he2 : e = two n
    · subst e
      have hy : y0 n ∈ C3 n := hEq ▸
        (mem_insert_diff_of_mem_of_ne n
          (Set.mem_union_right _ (y0_mem_Y n)) (by simp [y0, two]))
      simp [C3, Z, blockSet, y0] at hy
    · have htwo : two n ∈ C3 n := hEq ▸
        (mem_insert_diff_of_mem_of_ne n (by simp [C2]) (Ne.symm he2))
      simp [C3, Z, blockSet, two, three, four] at htwo
  · intro hsub
    by_cases he2 : e = two n
    · subst e
      have hfour := hsub (show four n ∈ C2exchange n (two n) by
        exact mem_insert_diff_of_mem_of_ne n (by simp [C2]) (two_ne_four n).symm)
      simp [H1, Y, Z, blockSet, four, one] at hfour
    · have htwo := hsub (show two n ∈ C2exchange n e by
        exact mem_insert_diff_of_mem_of_ne n (by simp [C2]) (Ne.symm he2))
      simp [H1, Y, Z, blockSet, two, one] at htwo
  · intro hsub
    have hthree := hsub (show three n ∈ C2exchange n e by simp [C2exchange])
    simp [H2, X, Z, blockSet, three, two] at hthree
  · intro hsub
    by_cases he4 : e = four n
    · subst e
      have htwo := hsub (show two n ∈ C2exchange n (four n) by
        exact mem_insert_diff_of_mem_of_ne n (by simp [C2]) (two_ne_four n))
      simp [H3, X, Y, blockSet, two, three] at htwo
    · have hfour := hsub (show four n ∈ C2exchange n e by
        exact mem_insert_diff_of_mem_of_ne n (by simp [C2]) (Ne.symm he4))
      simp [H3, X, Y, blockSet, four, three] at hfour

theorem C3exchange_isBase {e : Element n} (he : e ∈ C3 n) :
    IsBase n (C3exchange n e) := by
  refine ⟨fun _ _ ↦ mem_ground n _, ?_, ?_⟩
  · rw [C3exchange, Set.ncard_insert_of_notMem, Set.ncard_diff_singleton_of_mem he,
      ncard_C3]
    · omega
    simp [C3, Z, blockSet, one, three, four]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hT
    have htwo := hT (two_mem_T n)
    simp [C3exchange, C3, Z, blockSet, one, two, three, four] at htwo
  · intro hEq
    by_cases he3 : e = three n
    · subst e
      have hz : z0 n ∈ C1 n := hEq ▸
        (mem_insert_diff_of_mem_of_ne n
          (Set.mem_union_right _ (z0_mem_Z n)) (by simp [z0, three]))
      simp [C1, X, blockSet, z0] at hz
    · have hthree : three n ∈ C1 n := hEq ▸
        (mem_insert_diff_of_mem_of_ne n (by simp [C3]) (Ne.symm he3))
      simp [C1, X, blockSet, one, three, four] at hthree
  · intro hEq
    by_cases he3 : e = three n
    · subst e
      have hz : z0 n ∈ C2 n := hEq ▸
        (mem_insert_diff_of_mem_of_ne n
          (Set.mem_union_right _ (z0_mem_Z n)) (by simp [z0, three]))
      simp [C2, Y, blockSet, z0] at hz
    · have hthree : three n ∈ C2 n := hEq ▸
        (mem_insert_diff_of_mem_of_ne n (by simp [C3]) (Ne.symm he3))
      simp [C2, Y, blockSet, two, three, four] at hthree
  · intro hEq
    have hone : one n ∈ C3 n := hEq ▸
      (show one n ∈ C3exchange n e by simp [C3exchange])
    simp [C3, Z, blockSet, one, three, four] at hone
  · intro hsub
    by_cases he4 : e = four n
    · subst e
      have hthree := hsub (show three n ∈ C3exchange n (four n) by
        exact mem_insert_diff_of_mem_of_ne n (by simp [C3]) (three_ne_four n))
      simp [H1, Y, Z, blockSet, three, one] at hthree
    · have hfour := hsub (show four n ∈ C3exchange n e by
        exact mem_insert_diff_of_mem_of_ne n (by simp [C3]) (Ne.symm he4))
      simp [H1, Y, Z, blockSet, four, one] at hfour
  · intro hsub
    have hone := hsub (show one n ∈ C3exchange n e by simp [C3exchange])
    simp [H2, X, Z, blockSet, one, two] at hone
  · intro hsub
    have hone := hsub (show one n ∈ C3exchange n e by simp [C3exchange])
    simp [H3, X, Y, blockSet, one, three] at hone

theorem C1_isCircuit : (MI n).IsCircuit (C1 n) := by
  rw [Matroid.isCircuit_iff_dep_forall_diff_singleton_indep]
  constructor
  · refine ⟨?_, fun _ _ ↦ mem_ground n _⟩
    intro hI
    obtain ⟨B, hB, hsub⟩ := Matroid.indep_iff.1 hI
    have hEq := Set.eq_of_subset_of_ncard_le hsub (by
      rw [IsBase.ncard_eq n hB, ncard_C1])
    exact IsBase.ne_C1 n hB hEq.symm
  intro e he
  exact indep_of_subset_isBase n (C1exchange_isBase n he) (by simp [C1exchange])

theorem C2_isCircuit : (MI n).IsCircuit (C2 n) := by
  rw [Matroid.isCircuit_iff_dep_forall_diff_singleton_indep]
  constructor
  · refine ⟨?_, fun _ _ ↦ mem_ground n _⟩
    intro hI
    obtain ⟨B, hB, hsub⟩ := Matroid.indep_iff.1 hI
    have hEq := Set.eq_of_subset_of_ncard_le hsub (by
      rw [IsBase.ncard_eq n hB, ncard_C2])
    exact IsBase.ne_C2 n hB hEq.symm
  intro e he
  exact indep_of_subset_isBase n (C2exchange_isBase n he) (by simp [C2exchange])

theorem C3_isCircuit : (MI n).IsCircuit (C3 n) := by
  rw [Matroid.isCircuit_iff_dep_forall_diff_singleton_indep]
  constructor
  · refine ⟨?_, fun _ _ ↦ mem_ground n _⟩
    intro hI
    obtain ⟨B, hB, hsub⟩ := Matroid.indep_iff.1 hI
    have hEq := Set.eq_of_subset_of_ncard_le hsub (by
      rw [IsBase.ncard_eq n hB, ncard_C3])
    exact IsBase.ne_C3 n hB hEq.symm
  intro e he
  exact indep_of_subset_isBase n (C3exchange_isBase n he) (by simp [C3exchange])

/-! ## Bases witnessing the three cocircuits -/

private def core1 : Set (Element n) := insert (one n) (Y n)
private def core2 : Set (Element n) := insert (two n) (Z n)
private def core3 : Set (Element n) := insert (three n) (X n)

private def cocircuitWitness1 (d : Element n) : Set (Element n) :=
  insert d (core1 n)

private def cocircuitWitness2 (d : Element n) : Set (Element n) :=
  insert d (core2 n)

private def cocircuitWitness3 (d : Element n) : Set (Element n) :=
  insert d (core3 n)

private theorem core1_subset_H1 : core1 n ⊆ H1 n := by
  intro x hx
  rcases hx with rfl | hxY
  · simp [H1]
  · exact Set.mem_union_left _ (Set.mem_union_right _ hxY)

private theorem core2_subset_H2 : core2 n ⊆ H2 n := by
  intro x hx
  rcases hx with rfl | hxZ
  · simp [H2]
  · exact Set.mem_union_right _ hxZ

private theorem core3_subset_H3 : core3 n ⊆ H3 n := by
  intro x hx
  rcases hx with rfl | hxX
  · simp [H3]
  · exact Set.mem_union_left _ (Set.mem_union_right _ hxX)

private theorem cocircuitWitness1_isBase {d : Element n} (hd : d ∈ D1 n) :
    IsBase n (cocircuitWitness1 n d) := by
  have hdH : d ∉ H1 n := hd.2
  have hdcore : d ∉ core1 n := fun h ↦ hdH (core1_subset_H1 n h)
  have honeY : one n ∉ Y n := by simp [Y, blockSet, one]
  refine ⟨fun _ _ ↦ mem_ground n _, ?_, ?_⟩
  · rw [cocircuitWitness1, Set.ncard_insert_of_notMem hdcore, core1,
      Set.ncard_insert_of_notMem honeY, ncard_Y]
  apply admissible_insert_of_subset_H1 n (core1_subset_H1 n)
  · intro hsub
    have hone := hsub (show one n ∈ core1 n by simp [core1])
    simp [H2, X, Z, blockSet, one, two] at hone
  · intro hsub
    have hone := hsub (show one n ∈ core1 n by simp [core1])
    simp [H3, X, Y, blockSet, one, three] at hone
  exact hdH

private theorem cocircuitWitness2_isBase {d : Element n} (hd : d ∈ D2 n) :
    IsBase n (cocircuitWitness2 n d) := by
  have hdH : d ∉ H2 n := hd.2
  have hdcore : d ∉ core2 n := fun h ↦ hdH (core2_subset_H2 n h)
  have htwoZ : two n ∉ Z n := by simp [Z, blockSet, two]
  refine ⟨fun _ _ ↦ mem_ground n _, ?_, ?_⟩
  · rw [cocircuitWitness2, Set.ncard_insert_of_notMem hdcore, core2,
      Set.ncard_insert_of_notMem htwoZ, ncard_Z]
  apply admissible_insert_of_subset_H2 n
  · intro hsub
    have htwo := hsub (show two n ∈ core2 n by simp [core2])
    simp [H1, Y, Z, blockSet, two, one] at htwo
  · exact core2_subset_H2 n
  · intro hsub
    have htwo := hsub (show two n ∈ core2 n by simp [core2])
    simp [H3, X, Y, blockSet, two, three] at htwo
  exact hdH

private theorem cocircuitWitness3_isBase {d : Element n} (hd : d ∈ D3 n) :
    IsBase n (cocircuitWitness3 n d) := by
  have hdH : d ∉ H3 n := hd.2
  have hdcore : d ∉ core3 n := fun h ↦ hdH (core3_subset_H3 n h)
  have hthreeX : three n ∉ X n := by simp [X, blockSet, three]
  refine ⟨fun _ _ ↦ mem_ground n _, ?_, ?_⟩
  · rw [cocircuitWitness3, Set.ncard_insert_of_notMem hdcore, core3,
      Set.ncard_insert_of_notMem hthreeX, ncard_X]
  apply admissible_insert_of_subset_H3 n
  · intro hsub
    have hthree := hsub (show three n ∈ core3 n by simp [core3])
    simp [H1, Y, Z, blockSet, three, one] at hthree
  · intro hsub
    have hthree := hsub (show three n ∈ core3 n by simp [core3])
    simp [H2, X, Z, blockSet, three, two] at hthree
  · exact core3_subset_H3 n
  exact hdH

private theorem D1_inter_cocircuitWitness1 {d : Element n} (hd : d ∈ D1 n) :
    D1 n ∩ cocircuitWitness1 n d = {d} := by
  ext x
  constructor
  · rintro ⟨hxD, hxW⟩
    rcases hxW with rfl | hxcore
    · simp
    exact (hxD.2 (core1_subset_H1 n hxcore)).elim
  · intro hx
    have hxd : x = d := by simpa using hx
    subst x
    exact ⟨hd, Set.mem_insert _ _⟩

private theorem D2_inter_cocircuitWitness2 {d : Element n} (hd : d ∈ D2 n) :
    D2 n ∩ cocircuitWitness2 n d = {d} := by
  ext x
  constructor
  · rintro ⟨hxD, hxW⟩
    rcases hxW with rfl | hxcore
    · simp
    exact (hxD.2 (core2_subset_H2 n hxcore)).elim
  · intro hx
    have hxd : x = d := by simpa using hx
    subst x
    exact ⟨hd, Set.mem_insert _ _⟩

private theorem D3_inter_cocircuitWitness3 {d : Element n} (hd : d ∈ D3 n) :
    D3 n ∩ cocircuitWitness3 n d = {d} := by
  ext x
  constructor
  · rintro ⟨hxD, hxW⟩
    rcases hxW with rfl | hxcore
    · simp
    exact (hxD.2 (core3_subset_H3 n hxcore)).elim
  · intro hx
    have hxd : x = d := by simpa using hx
    subst x
    exact ⟨hd, Set.mem_insert _ _⟩

/-! ## The three cocircuits -/

theorem D1_isCocircuit : (MI n).IsCocircuit (D1 n) := by
  rw [Matroid.isCocircuit_iff_minimal]
  constructor
  · intro B hB
    obtain ⟨d, hdB, hdH⟩ := Set.not_subset.1 (IsBase.not_subset_H1 n hB)
    exact ⟨d, ⟨⟨mem_ground n d, hdH⟩, hdB⟩⟩
  · intro K hK hKD d hdD
    obtain ⟨x, hxK, hxB⟩ := hK (cocircuitWitness1 n d)
      (cocircuitWitness1_isBase n hdD)
    have hx : x ∈ D1 n ∩ cocircuitWitness1 n d := ⟨hKD hxK, hxB⟩
    have hxd : x = d := by
      rw [D1_inter_cocircuitWitness1 n hdD] at hx
      simpa using hx
    rwa [← hxd]

theorem D2_isCocircuit : (MI n).IsCocircuit (D2 n) := by
  rw [Matroid.isCocircuit_iff_minimal]
  constructor
  · intro B hB
    obtain ⟨d, hdB, hdH⟩ := Set.not_subset.1 (IsBase.not_subset_H2 n hB)
    exact ⟨d, ⟨⟨mem_ground n d, hdH⟩, hdB⟩⟩
  · intro K hK hKD d hdD
    obtain ⟨x, hxK, hxB⟩ := hK (cocircuitWitness2 n d)
      (cocircuitWitness2_isBase n hdD)
    have hx : x ∈ D2 n ∩ cocircuitWitness2 n d := ⟨hKD hxK, hxB⟩
    have hxd : x = d := by
      rw [D2_inter_cocircuitWitness2 n hdD] at hx
      simpa using hx
    rwa [← hxd]

theorem D3_isCocircuit : (MI n).IsCocircuit (D3 n) := by
  rw [Matroid.isCocircuit_iff_minimal]
  constructor
  · intro B hB
    obtain ⟨d, hdB, hdH⟩ := Set.not_subset.1 (IsBase.not_subset_H3 n hB)
    exact ⟨d, ⟨⟨mem_ground n d, hdH⟩, hdB⟩⟩
  · intro K hK hKD d hdD
    obtain ⟨x, hxK, hxB⟩ := hK (cocircuitWitness3 n d)
      (cocircuitWitness3_isBase n hdD)
    have hx : x ∈ D3 n ∩ cocircuitWitness3 n d := ⟨hKD hxK, hxB⟩
    have hxd : x = d := by
      rw [D3_inter_cocircuitWitness3 n hdD] at hx
      simpa using hx
    rwa [← hxd]

/-! ## The complementary hyperplanes -/

theorem H1_isHyperplane : (MI n).IsHyperplane (H1 n) := by
  rw [Matroid.IsHyperplane, maximal_iff]
  constructor
  · refine ⟨fun _ _ ↦ mem_ground n _, ?_⟩
    intro hsp
    obtain ⟨B, hB, hBH⟩ := hsp.exists_isBase_subset
    exact IsBase.not_subset_H1 n hB hBH
  · intro S hS hHS
    apply hHS.antisymm
    by_contra hnsub
    obtain ⟨d, hdS, hdH⟩ := Set.not_subset.1 hnsub
    have hdD : d ∈ D1 n := ⟨mem_ground n d, hdH⟩
    have hBS : cocircuitWitness1 n d ⊆ S := by
      intro x hx
      rcases hx with rfl | hxcore
      · exact hdS
      · exact hHS (core1_subset_H1 n hxcore)
    have hB : (MI n).IsBase (cocircuitWitness1 n d) :=
      cocircuitWitness1_isBase n hdD
    exact hS.2 (hB.spanning_of_superset hBS hS.1)

theorem H2_isHyperplane : (MI n).IsHyperplane (H2 n) := by
  rw [Matroid.IsHyperplane, maximal_iff]
  constructor
  · refine ⟨fun _ _ ↦ mem_ground n _, ?_⟩
    intro hsp
    obtain ⟨B, hB, hBH⟩ := hsp.exists_isBase_subset
    exact IsBase.not_subset_H2 n hB hBH
  · intro S hS hHS
    apply hHS.antisymm
    by_contra hnsub
    obtain ⟨d, hdS, hdH⟩ := Set.not_subset.1 hnsub
    have hdD : d ∈ D2 n := ⟨mem_ground n d, hdH⟩
    have hBS : cocircuitWitness2 n d ⊆ S := by
      intro x hx
      rcases hx with rfl | hxcore
      · exact hdS
      · exact hHS (core2_subset_H2 n hxcore)
    have hB : (MI n).IsBase (cocircuitWitness2 n d) :=
      cocircuitWitness2_isBase n hdD
    exact hS.2 (hB.spanning_of_superset hBS hS.1)

theorem H3_isHyperplane : (MI n).IsHyperplane (H3 n) := by
  rw [Matroid.IsHyperplane, maximal_iff]
  constructor
  · refine ⟨fun _ _ ↦ mem_ground n _, ?_⟩
    intro hsp
    obtain ⟨B, hB, hBH⟩ := hsp.exists_isBase_subset
    exact IsBase.not_subset_H3 n hB hBH
  · intro S hS hHS
    apply hHS.antisymm
    by_contra hnsub
    obtain ⟨d, hdS, hdH⟩ := Set.not_subset.1 hnsub
    have hdD : d ∈ D3 n := ⟨mem_ground n d, hdH⟩
    have hBS : cocircuitWitness3 n d ⊆ S := by
      intro x hx
      rcases hx with rfl | hxcore
      · exact hdS
      · exact hHS (core3_subset_H3 n hxcore)
    have hB : (MI n).IsBase (cocircuitWitness3 n d) :=
      cocircuitWitness3_isBase n hdD
    exact hS.2 (hB.spanning_of_superset hBS hS.1)

/-! ## The nine two-element circuit--cocircuit intersections -/

theorem C1_inter_D2 : C1 n ∩ D2 n = {one n, four n} := by
  ext e
  cases e with
  | special s => fin_cases s <;>
      simp [C1, D2, ground, H2, X, Z, blockSet, one, two, four]
  | block b i => fin_cases b <;> simp [C1, D2, ground, H2, X, Z]

theorem C1_inter_D3 : C1 n ∩ D3 n = {one n, four n} := by
  ext e
  cases e with
  | special s => fin_cases s <;>
      simp [C1, D3, ground, H3, X, Y, blockSet, one, three, four]
  | block b i => fin_cases b <;> simp [C1, D3, ground, H3, X, Y]

theorem C2_inter_D1 : C2 n ∩ D1 n = {two n, four n} := by
  ext e
  cases e with
  | special s => fin_cases s <;>
      simp [C2, D1, ground, H1, Y, Z, blockSet, one, two, four]
  | block b i => fin_cases b <;> simp [C2, D1, ground, H1, Y, Z]

theorem C2_inter_D3 : C2 n ∩ D3 n = {two n, four n} := by
  ext e
  cases e with
  | special s => fin_cases s <;>
      simp [C2, D3, ground, H3, X, Y, blockSet, two, three, four]
  | block b i => fin_cases b <;> simp [C2, D3, ground, H3, X, Y]

theorem C3_inter_D1 : C3 n ∩ D1 n = {three n, four n} := by
  ext e
  cases e with
  | special s => fin_cases s <;>
      simp [C3, D1, ground, H1, Y, Z, blockSet, one, three, four]
  | block b i => fin_cases b <;> simp [C3, D1, ground, H1, Y, Z]

theorem C3_inter_D2 : C3 n ∩ D2 n = {three n, four n} := by
  ext e
  cases e with
  | special s => fin_cases s <;>
      simp [C3, D2, ground, H2, X, Z, blockSet, two, three, four]
  | block b i => fin_cases b <;> simp [C3, D2, ground, H2, X, Z]

theorem T_inter_D1 : T n ∩ D1 n = {two n, three n} := by
  ext e
  cases e with
  | special s => fin_cases s <;>
      simp [T, D1, ground, H1, Y, Z, blockSet, one, two, three]
  | block b i => fin_cases b <;> simp [T, D1, ground, H1, Y, Z]

theorem T_inter_D2 : T n ∩ D2 n = {one n, three n} := by
  ext e
  cases e with
  | special s => fin_cases s <;>
      simp [T, D2, ground, H2, X, Z, blockSet, one, two, three]
  | block b i => fin_cases b <;> simp [T, D2, ground, H2, X, Z]

theorem T_inter_D3 : T n ∩ D3 n = {one n, two n} := by
  ext e
  cases e with
  | special s => fin_cases s <;>
      simp [T, D3, ground, H3, X, Y, blockSet, one, two, three]
  | block b i => fin_cases b <;> simp [T, D3, ground, H3, X, Y]

/-! ## The parameter-independent nine-cell obstruction -/

/-- Every member `MIₙ` fails the Bland--Jensen weak-orientability equations.
The contradiction is the explicit nine-row, eighteen-flag parity anomaly
verified in `BlandJensenNineCell.lean`. -/
theorem MI_not_weaklyOrientable : ¬ WeaklyOrientable (MI n) := by
  rintro ⟨circuitSign, cocircuitSign, hEq⟩
  have h0 := hEq (C1 n) (D2 n) (one n) (four n)
    (C1_isCircuit n) (D2_isCocircuit n) (one_ne_four n) (C1_inter_D2 n)
  have h1 := hEq (C1 n) (D3 n) (one n) (four n)
    (C1_isCircuit n) (D3_isCocircuit n) (one_ne_four n) (C1_inter_D3 n)
  have h2 := hEq (C2 n) (D1 n) (two n) (four n)
    (C2_isCircuit n) (D1_isCocircuit n) (two_ne_four n) (C2_inter_D1 n)
  have h3 := hEq (C2 n) (D3 n) (two n) (four n)
    (C2_isCircuit n) (D3_isCocircuit n) (two_ne_four n) (C2_inter_D3 n)
  have h4 := hEq (C3 n) (D1 n) (three n) (four n)
    (C3_isCircuit n) (D1_isCocircuit n) (three_ne_four n) (C3_inter_D1 n)
  have h5 := hEq (C3 n) (D2 n) (three n) (four n)
    (C3_isCircuit n) (D2_isCocircuit n) (three_ne_four n) (C3_inter_D2 n)
  have h6 := hEq (T n) (D1 n) (two n) (three n)
    (T_isCircuit n) (D1_isCocircuit n) (two_ne_three n) (T_inter_D1 n)
  have h7 := hEq (T n) (D2 n) (one n) (three n)
    (T_isCircuit n) (D2_isCocircuit n) (one_ne_three n) (T_inter_D2 n)
  have h8 := hEq (T n) (D3 n) (one n) (two n)
    (T_isCircuit n) (D3_isCocircuit n) (one_ne_two n) (T_inter_D3 n)
  let x : Fin 18 → F2 := ![
    circuitSign (C1 n) (one n), circuitSign (C1 n) (four n),
    circuitSign (C2 n) (two n), circuitSign (C2 n) (four n),
    circuitSign (C3 n) (three n), circuitSign (C3 n) (four n),
    circuitSign (T n) (one n), circuitSign (T n) (two n),
    circuitSign (T n) (three n), cocircuitSign (D1 n) (two n),
    cocircuitSign (D1 n) (three n), cocircuitSign (D1 n) (four n),
    cocircuitSign (D2 n) (one n), cocircuitSign (D2 n) (three n),
    cocircuitSign (D2 n) (four n), cocircuitSign (D3 n) (one n),
    cocircuitSign (D3 n) (two n), cocircuitSign (D3 n) (four n)]
  apply BlandJensenFormal.BlandJensenNineCell.no_flag_assignment
  refine ⟨x, ?_⟩
  intro c
  fin_cases c <;>
    simp [BlandJensenFormal.BlandJensenNineCell.incidence,
      BlandJensenFormal.BlandJensenNineCell.kappa, x,
      Fin.sum_univ_succ, add_assoc, add_comm, add_left_comm]
  · simpa [BlandJensenEquation, add_assoc, add_comm, add_left_comm] using h0
  · simpa [BlandJensenEquation, add_assoc, add_comm, add_left_comm] using h1
  · simpa [BlandJensenEquation, add_assoc, add_comm, add_left_comm] using h2
  · simpa [BlandJensenEquation, add_assoc, add_comm, add_left_comm] using h3
  · simpa [BlandJensenEquation, add_assoc, add_comm, add_left_comm] using h4
  · simpa [BlandJensenEquation, add_assoc, add_comm, add_left_comm] using h5
  · simpa [BlandJensenEquation, add_assoc, add_comm, add_left_comm] using h6
  · simpa [BlandJensenEquation, add_assoc, add_comm, add_left_comm] using h7
  · simpa [BlandJensenEquation, add_assoc, add_comm, add_left_comm] using h8

end Family

end BlandJensenFormal.BlandJensenMI
