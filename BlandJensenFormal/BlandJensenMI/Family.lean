import BlandJensenFormal.BlandJensenMI.Basic
import Mathlib.Tactic

/-!
# The Bland--Jensen family `MIₙ`: ground set and basis predicate

For `n : ℕ`, the ground set consists of four distinguished elements and
three disjoint blocks `X`, `Y`, and `Z`, each of size `n+1`.  This file gives
the literal basis predicate used by De Loera--Lee--Margulies--Miller.

The construction of the associated Mathlib matroid is intentionally deferred
until basis exchange has been proved.  Thus `IsBase` below is presently a
basis *presentation*, not an assertion smuggled into a `Matroid` value.
-/

namespace BlandJensenFormal.BlandJensenMI

open Set

/-- Elements of the ground set of `MIₙ`.  `special i` represents one of the
four distinguished elements; `block b j` is the `j`-th member of one of the
three blocks. -/
inductive Element (n : ℕ)
  | special : Fin 4 → Element n
  | block : Fin 3 → Fin (n + 1) → Element n
  deriving DecidableEq, Fintype

namespace Family

variable (n : ℕ)

/-- The element type is the disjoint union of four distinguished elements
and three blocks of size `n+1`. -/
def elementEquiv : Element n ≃ Fin 4 ⊕ (Fin 3 × Fin (n + 1)) where
  toFun
    | .special s => Sum.inl s
    | .block b i => Sum.inr (b, i)
  invFun
    | Sum.inl s => .special s
    | Sum.inr (b, i) => .block b i
  left_inv e := by cases e <;> rfl
  right_inv e := by rcases e with s | ⟨b, i⟩ <;> rfl

@[simp] theorem card_element : Fintype.card (Element n) = 3 * n + 7 := by
  rw [Fintype.card_congr (elementEquiv n)]
  simp
  omega

/-- Distinguished elements `1,2,3,4`. -/
@[simp] def one : Element n := .special 0
@[simp] def two : Element n := .special 1
@[simp] def three : Element n := .special 2
@[simp] def four : Element n := .special 3

@[simp] theorem one_ne_two : one n ≠ two n := by simp [one, two]
@[simp] theorem one_ne_three : one n ≠ three n := by simp [one, three]
@[simp] theorem one_ne_four : one n ≠ four n := by simp [one, four]
@[simp] theorem two_ne_three : two n ≠ three n := by simp [two, three]
@[simp] theorem two_ne_four : two n ≠ four n := by simp [two, four]
@[simp] theorem three_ne_four : three n ≠ four n := by simp [three, four]

/-- The block with label `b`. -/
def blockSet (b : Fin 3) : Set (Element n) :=
  Set.range (Element.block b)

/-- The three large blocks. -/
def X : Set (Element n) := blockSet n 0
def Y : Set (Element n) := blockSet n 1
def Z : Set (Element n) := blockSet n 2

/-- Every block embedding is injective. -/
theorem block_injective (b : Fin 3) : Function.Injective (Element.block b : Fin (n + 1) → Element n) := by
  intro i j h
  injection h

@[simp] theorem special_not_mem_blockSet (s : Fin 4) (b : Fin 3) :
    Element.special s ∉ blockSet n b := by
  simp [blockSet]

@[simp] theorem block_mem_blockSet_iff (b c : Fin 3) (i : Fin (n + 1)) :
    Element.block c i ∈ blockSet n b ↔ c = b := by
  simp [blockSet, eq_comm]

theorem blockSet_finite (b : Fin 3) : (blockSet n b).Finite :=
  Set.finite_range _

theorem ncard_blockSet (b : Fin 3) : (blockSet n b).ncard = n + 1 := by
  unfold blockSet
  rw [Set.ncard_range_of_injective (block_injective n b)]
  simp

@[simp] theorem ncard_X : (X n).ncard = n + 1 := ncard_blockSet n 0
@[simp] theorem ncard_Y : (Y n).ncard = n + 1 := ncard_blockSet n 1
@[simp] theorem ncard_Z : (Z n).ncard = n + 1 := ncard_blockSet n 2

/-- Different labelled blocks are disjoint. -/
theorem blockSet_disjoint {b c : Fin 3} (hbc : b ≠ c) :
    Disjoint (blockSet n b) (blockSet n c) := by
  rw [Set.disjoint_left]
  intro e heb hec
  obtain ⟨i, rfl⟩ := heb
  exact hbc ((block_mem_blockSet_iff n c b i).1 hec)

theorem X_disjoint_Y : Disjoint (X n) (Y n) := by
  exact blockSet_disjoint n (by decide)

theorem X_disjoint_Z : Disjoint (X n) (Z n) := by
  exact blockSet_disjoint n (by decide)

theorem Y_disjoint_Z : Disjoint (Y n) (Z n) := by
  exact blockSet_disjoint n (by decide)

/-- The finite ground set. -/
def ground : Set (Element n) := Set.univ

theorem ground_finite : (ground n).Finite := by
  simp [ground]

@[simp] theorem ncard_ground : (ground n).ncard = 3 * n + 7 := by
  rw [ground, Set.ncard_univ, Nat.card_eq_fintype_card, card_element]

@[simp] theorem encard_ground : (ground n).encard = (3 * n + 7 : ℕ) := by
  rw [ground, Set.encard_univ, ENat.card_eq_coe_fintype_card,
    Fintype.card_congr (elementEquiv n)]
  norm_cast
  simp
  omega

@[simp] theorem mem_ground (e : Element n) : e ∈ ground n := by
  simp [ground]

/-! ### Distinguished circuits and hyperplanes in the presentation -/

/-- The three-element set `T={1,2,3}`. -/
def T : Set (Element n) := {one n, two n, three n}

/-- The three declared circuit-hyperplanes `C₁,C₂,C₃`. -/
def C1 : Set (Element n) := {one n, four n} ∪ X n
def C2 : Set (Element n) := {two n, four n} ∪ Y n
def C3 : Set (Element n) := {three n, four n} ∪ Z n

/-- The three declared hyperplanes `H₁,H₂,H₃`. -/
def H1 : Set (Element n) := {one n} ∪ Y n ∪ Z n
def H2 : Set (Element n) := {two n} ∪ X n ∪ Z n
def H3 : Set (Element n) := {three n} ∪ X n ∪ Y n

/-- Complements of the three declared hyperplanes.  Once the matroid is
constructed and the hyperplane claims are proved, these become cocircuits. -/
def D1 : Set (Element n) := ground n \ H1 n
def D2 : Set (Element n) := ground n \ H2 n
def D3 : Set (Element n) := ground n \ H3 n

@[simp] theorem one_mem_T : one n ∈ T n := by simp [T]
@[simp] theorem two_mem_T : two n ∈ T n := by simp [T]
@[simp] theorem three_mem_T : three n ∈ T n := by simp [T]
@[simp] theorem four_not_mem_T : four n ∉ T n := by simp [T, one, two, three, four]

theorem ncard_T : (T n).ncard = 3 := by
  simp [T, one, two, three]

theorem pair_one_four_disjoint_X :
    Disjoint ({one n, four n} : Set (Element n)) (X n) := by
  rw [Set.disjoint_left]
  intro e hePair heX
  rcases hePair with (rfl | he)
  · exact special_not_mem_blockSet n 0 0 heX
  rcases he with (rfl | hfalse)
  · exact special_not_mem_blockSet n 3 0 heX

theorem pair_two_four_disjoint_Y :
    Disjoint ({two n, four n} : Set (Element n)) (Y n) := by
  rw [Set.disjoint_left]
  intro e hePair heY
  rcases hePair with (rfl | he)
  · exact special_not_mem_blockSet n 1 1 heY
  rcases he with (rfl | hfalse)
  · exact special_not_mem_blockSet n 3 1 heY

theorem pair_three_four_disjoint_Z :
    Disjoint ({three n, four n} : Set (Element n)) (Z n) := by
  rw [Set.disjoint_left]
  intro e hePair heZ
  rcases hePair with (rfl | he)
  · exact special_not_mem_blockSet n 2 2 heZ
  rcases he with (rfl | hfalse)
  · exact special_not_mem_blockSet n 3 2 heZ

@[simp] theorem ncard_C1 : (C1 n).ncard = n + 3 := by
  rw [C1, Set.ncard_union_eq (pair_one_four_disjoint_X n)]
  simp [one, four, Nat.add_comm, Nat.add_assoc]

@[simp] theorem ncard_C2 : (C2 n).ncard = n + 3 := by
  rw [C2, Set.ncard_union_eq (pair_two_four_disjoint_Y n)]
  simp [two, four, Nat.add_comm, Nat.add_assoc]

@[simp] theorem ncard_C3 : (C3 n).ncard = n + 3 := by
  rw [C3, Set.ncard_union_eq (pair_three_four_disjoint_Z n)]
  simp [three, four, Nat.add_comm, Nat.add_assoc]

/-- Fixed witnesses in the three nonempty large blocks. -/
@[simp] def x0 : Element n := .block 0 0
@[simp] def y0 : Element n := .block 1 0
@[simp] def z0 : Element n := .block 2 0

@[simp] theorem x0_mem_X : x0 n ∈ X n := by simp [x0, X]
@[simp] theorem y0_mem_Y : y0 n ∈ Y n := by simp [y0, Y]
@[simp] theorem z0_mem_Z : z0 n ∈ Z n := by simp [z0, Z]

/-- Pairwise intersections of the three declared hyperplanes. -/
theorem H1_inter_H2 : H1 n ∩ H2 n = Z n := by
  ext e
  cases e with
  | special s => fin_cases s <;> simp [H1, H2, X, Y, Z, blockSet, one, two]
  | block b i => fin_cases b <;> simp [H1, H2, X, Y, Z]

theorem H1_inter_H3 : H1 n ∩ H3 n = Y n := by
  ext e
  cases e with
  | special s => fin_cases s <;> simp [H1, H3, X, Y, Z, blockSet, one, three]
  | block b i => fin_cases b <;> simp [H1, H3, X, Y, Z]

theorem H2_inter_H3 : H2 n ∩ H3 n = X n := by
  ext e
  cases e with
  | special s => fin_cases s <;> simp [H2, H3, X, Y, Z, blockSet, two, three]
  | block b i => fin_cases b <;> simp [H2, H3, X, Y, Z]

/-- Pairwise intersections of the three distinguished rank-size sets. -/
theorem C1_inter_C2 : C1 n ∩ C2 n = {four n} := by
  ext e
  cases e with
  | special s => fin_cases s <;> simp [C1, C2, X, Y, blockSet, one, two, four]
  | block b i => fin_cases b <;> simp [C1, C2, X, Y]

theorem C1_inter_C3 : C1 n ∩ C3 n = {four n} := by
  ext e
  cases e with
  | special s => fin_cases s <;> simp [C1, C3, X, Z, blockSet, one, three, four]
  | block b i => fin_cases b <;> simp [C1, C3, X, Z]

theorem C2_inter_C3 : C2 n ∩ C3 n = {four n} := by
  ext e
  cases e with
  | special s => fin_cases s <;> simp [C2, C3, Y, Z, blockSet, two, three, four]
  | block b i => fin_cases b <;> simp [C2, C3, Y, Z]

/-- If `A` lies in `H`, adjoining one element cannot cover a set having two
distinct elements outside `H`. -/
theorem not_subset_insert_of_two_outside
    {A H S : Set (Element n)} {u v f : Element n}
    (hAH : A ⊆ H) (huS : u ∈ S) (hvS : v ∈ S)
    (huH : u ∉ H) (hvH : v ∉ H) (huv : u ≠ v) :
    ¬ S ⊆ insert f A := by
  intro hS
  have hu := hS huS
  have hv := hS hvS
  rw [Set.mem_insert_iff] at hu hv
  have huf : u = f := hu.resolve_right (fun huA ↦ huH (hAH huA))
  have hvf : v = f := hv.resolve_right (fun hvA ↦ hvH (hAH hvA))
  exact huv (huf.trans hvf.symm)

/-- The conditions, other than cardinality, imposed on a basis of `MIₙ`. -/
def Admissible (B : Set (Element n)) : Prop :=
  ¬ T n ⊆ B ∧
  B ≠ C1 n ∧ B ≠ C2 n ∧ B ≠ C3 n ∧
  ¬ B ⊆ H1 n ∧ ¬ B ⊆ H2 n ∧ ¬ B ⊆ H3 n

/-- The four possible non-hyperplane failures of an exchanged rank-size set. -/
def Exceptional (A : Set (Element n)) (f : Element n) : Prop :=
  T n ⊆ insert f A ∨ insert f A = C1 n ∨
    insert f A = C2 n ∨ insert f A = C3 n

theorem insert_eq_insert_of_notMem {A : Set (Element n)} {f g : Element n}
    (hfA : f ∉ A) (hfg : insert f A = insert g A) : f = g := by
  have hfmem : f ∈ insert g A := hfg ▸ Set.mem_insert f A
  rcases hfmem with h | h
  · exact h
  · exact (hfA h).elim

private theorem T_not_subset_insert_of_subset_C1 {A : Set (Element n)} {f : Element n}
    (hA : A ⊆ C1 n) : ¬ T n ⊆ insert f A := by
  exact not_subset_insert_of_two_outside n hA (two_mem_T n) (three_mem_T n)
    (by simp [C1, X, blockSet, two, four])
    (by simp [C1, X, blockSet, three, four]) (two_ne_three n)

private theorem T_not_subset_insert_of_subset_C2 {A : Set (Element n)} {f : Element n}
    (hA : A ⊆ C2 n) : ¬ T n ⊆ insert f A := by
  exact not_subset_insert_of_two_outside n hA (one_mem_T n) (three_mem_T n)
    (by simp [C2, Y, blockSet, one, two, four])
    (by simp [C2, Y, blockSet, three, four]) (one_ne_three n)

private theorem T_not_subset_insert_of_subset_C3 {A : Set (Element n)} {f : Element n}
    (hA : A ⊆ C3 n) : ¬ T n ⊆ insert f A := by
  exact not_subset_insert_of_two_outside n hA (one_mem_T n) (two_mem_T n)
    (by simp [C3, Z, blockSet, one, three, four])
    (by simp [C3, Z, blockSet, two, four]) (one_ne_two n)

private theorem C1_not_subset_insert_of_subset_C2 {A : Set (Element n)} {f : Element n}
    (hA : A ⊆ C2 n) : ¬ C1 n ⊆ insert f A := by
  exact not_subset_insert_of_two_outside n hA
    (u := one n) (v := x0 n)
    (by simp [C1]) (Set.mem_union_right _ (x0_mem_X n))
    (by simp [C2, Y, blockSet, one, two, four])
    (by simp [C2, Y, blockSet, x0])
    (by simp [one, x0])

private theorem C1_not_subset_insert_of_subset_C3 {A : Set (Element n)} {f : Element n}
    (hA : A ⊆ C3 n) : ¬ C1 n ⊆ insert f A := by
  exact not_subset_insert_of_two_outside n hA
    (u := one n) (v := x0 n)
    (by simp [C1]) (Set.mem_union_right _ (x0_mem_X n))
    (by simp [C3, Z, blockSet, one, three, four])
    (by simp [C3, Z, blockSet, x0])
    (by simp [one, x0])

private theorem C2_not_subset_insert_of_subset_C1 {A : Set (Element n)} {f : Element n}
    (hA : A ⊆ C1 n) : ¬ C2 n ⊆ insert f A := by
  exact not_subset_insert_of_two_outside n hA
    (u := two n) (v := y0 n)
    (by simp [C2]) (Set.mem_union_right _ (y0_mem_Y n))
    (by simp [C1, X, blockSet, one, two, four])
    (by simp [C1, X, blockSet, y0])
    (by simp [two, y0])

private theorem C2_not_subset_insert_of_subset_C3 {A : Set (Element n)} {f : Element n}
    (hA : A ⊆ C3 n) : ¬ C2 n ⊆ insert f A := by
  exact not_subset_insert_of_two_outside n hA
    (u := two n) (v := y0 n)
    (by simp [C2]) (Set.mem_union_right _ (y0_mem_Y n))
    (by simp [C3, Z, blockSet, two, three, four])
    (by simp [C3, Z, blockSet, y0])
    (by simp [two, y0])

private theorem C3_not_subset_insert_of_subset_C1 {A : Set (Element n)} {f : Element n}
    (hA : A ⊆ C1 n) : ¬ C3 n ⊆ insert f A := by
  exact not_subset_insert_of_two_outside n hA
    (u := three n) (v := z0 n)
    (by simp [C3]) (Set.mem_union_right _ (z0_mem_Z n))
    (by simp [C1, X, blockSet, one, three, four])
    (by simp [C1, X, blockSet, z0])
    (by simp [three, z0])

private theorem C3_not_subset_insert_of_subset_C2 {A : Set (Element n)} {f : Element n}
    (hA : A ⊆ C2 n) : ¬ C3 n ⊆ insert f A := by
  exact not_subset_insert_of_two_outside n hA
    (u := three n) (v := z0 n)
    (by simp [C3]) (Set.mem_union_right _ (z0_mem_Z n))
    (by simp [C2, Y, blockSet, two, three, four])
    (by simp [C2, Y, blockSet, z0])
    (by simp [three, z0])

/-- For a fixed `(r-1)`-set `A`, at most one new element can trigger one of
the circuit-type failures `T,C₁,C₂,C₃`. -/
theorem exceptional_unique {A : Set (Element n)} {f g : Element n}
    (hTA : ¬ T n ⊆ A) (hfA : f ∉ A)
    (hf : Exceptional n A f) (hg : Exceptional n A g) : f = g := by
  rcases hf with hTf | hC1f | hC2f | hC3f <;>
    rcases hg with hTg | hC1g | hC2g | hC3g
  · have hfT : f ∈ T n := by
      by_contra hfT
      apply hTA
      intro t ht
      rcases hTf ht with htf | htA
      · exact (hfT (htf ▸ ht)).elim
      · exact htA
    rcases hTg hfT with hfg | hfmem
    · exact hfg
    · exact (hfA hfmem).elim
  · exact (T_not_subset_insert_of_subset_C1 n (by simpa [hC1g] using subset_insert g A) hTf).elim
  · exact (T_not_subset_insert_of_subset_C2 n (by simpa [hC2g] using subset_insert g A) hTf).elim
  · exact (T_not_subset_insert_of_subset_C3 n (by simpa [hC3g] using subset_insert g A) hTf).elim
  · exact (T_not_subset_insert_of_subset_C1 n (by simpa [hC1f] using subset_insert f A) hTg).elim
  · exact insert_eq_insert_of_notMem n hfA (hC1f.trans hC1g.symm)
  · exact (C1_not_subset_insert_of_subset_C2 n
      (by simpa [hC2g] using subset_insert g A) hC1f.symm.subset).elim
  · exact (C1_not_subset_insert_of_subset_C3 n
      (by simpa [hC3g] using subset_insert g A) hC1f.symm.subset).elim
  · exact (T_not_subset_insert_of_subset_C2 n (by simpa [hC2f] using subset_insert f A) hTg).elim
  · exact (C2_not_subset_insert_of_subset_C1 n
      (by simpa [hC1g] using subset_insert g A) hC2f.symm.subset).elim
  · exact insert_eq_insert_of_notMem n hfA (hC2f.trans hC2g.symm)
  · exact (C2_not_subset_insert_of_subset_C3 n
      (by simpa [hC3g] using subset_insert g A) hC2f.symm.subset).elim
  · exact (T_not_subset_insert_of_subset_C3 n (by simpa [hC3f] using subset_insert f A) hTg).elim
  · exact (C3_not_subset_insert_of_subset_C1 n
      (by simpa [hC1g] using subset_insert g A) hC3f.symm.subset).elim
  · exact (C3_not_subset_insert_of_subset_C2 n
      (by simpa [hC2g] using subset_insert g A) hC3f.symm.subset).elim
  · exact insert_eq_insert_of_notMem n hfA (hC3f.trans hC3g.symm)

private theorem not_subset_H2_of_subset_H1 {A : Set (Element n)}
    (hcard : A.ncard = n + 2) (hA1 : A ⊆ H1 n) : ¬ A ⊆ H2 n := by
  intro hA2
  have hAZ : A ⊆ Z n := by
    rw [← H1_inter_H2 n]
    exact fun _ hx ↦ ⟨hA1 hx, hA2 hx⟩
  have hle := Set.ncard_le_ncard hAZ (blockSet_finite n 2)
  rw [hcard, ncard_Z] at hle
  omega

private theorem not_subset_H3_of_subset_H1 {A : Set (Element n)}
    (hcard : A.ncard = n + 2) (hA1 : A ⊆ H1 n) : ¬ A ⊆ H3 n := by
  intro hA3
  have hAY : A ⊆ Y n := by
    rw [← H1_inter_H3 n]
    exact fun _ hx ↦ ⟨hA1 hx, hA3 hx⟩
  have hle := Set.ncard_le_ncard hAY (blockSet_finite n 1)
  rw [hcard, ncard_Y] at hle
  omega

private theorem not_subset_H3_of_subset_H2 {A : Set (Element n)}
    (hcard : A.ncard = n + 2) (hA2 : A ⊆ H2 n) : ¬ A ⊆ H3 n := by
  intro hA3
  have hAX : A ⊆ X n := by
    rw [← H2_inter_H3 n]
    exact fun _ hx ↦ ⟨hA2 hx, hA3 hx⟩
  have hle := Set.ncard_le_ncard hAX (blockSet_finite n 0)
  rw [hcard, ncard_X] at hle
  omega

theorem admissible_insert_of_subset_H1 {A : Set (Element n)} {f : Element n}
    (hA1 : A ⊆ H1 n) (hA2 : ¬ A ⊆ H2 n) (hA3 : ¬ A ⊆ H3 n)
    (hf1 : f ∉ H1 n) : Admissible n (insert f A) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact not_subset_insert_of_two_outside n hA1 (two_mem_T n) (three_mem_T n)
      (by simp [H1, Y, Z, blockSet]) (by simp [H1, Y, Z, blockSet]) (two_ne_three n)
  · intro hEq
    exact (not_subset_insert_of_two_outside n hA1
      (u := four n) (v := x0 n)
      (by simp) (Set.mem_union_right _ (x0_mem_X n))
      (by simp [H1, Y, Z, blockSet]) (by simp [H1, Y, Z, blockSet, x0])
      (by simp [four, x0])) hEq.symm.subset
  · intro hEq
    exact (not_subset_insert_of_two_outside n hA1
      (u := two n) (v := four n)
      (by simp [C2]) (by simp [C2])
      (by simp [H1, Y, Z, blockSet]) (by simp [H1, Y, Z, blockSet])
      (two_ne_four n)) hEq.symm.subset
  · intro hEq
    exact (not_subset_insert_of_two_outside n hA1
      (u := three n) (v := four n)
      (by simp [C3]) (by simp [C3])
      (by simp [H1, Y, Z, blockSet]) (by simp [H1, Y, Z, blockSet])
      (three_ne_four n)) hEq.symm.subset
  · intro hsub
    exact hf1 (hsub (Set.mem_insert f A))
  · intro hsub
    exact hA2 (fun _ hx ↦ hsub (Set.mem_insert_of_mem f hx))
  · intro hsub
    exact hA3 (fun _ hx ↦ hsub (Set.mem_insert_of_mem f hx))

theorem admissible_insert_of_subset_H2 {A : Set (Element n)} {f : Element n}
    (hA1 : ¬ A ⊆ H1 n) (hA2 : A ⊆ H2 n) (hA3 : ¬ A ⊆ H3 n)
    (hf2 : f ∉ H2 n) : Admissible n (insert f A) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact not_subset_insert_of_two_outside n hA2 (one_mem_T n) (three_mem_T n)
      (by simp [H2, X, Z, blockSet]) (by simp [H2, X, Z, blockSet]) (one_ne_three n)
  · intro hEq
    exact (not_subset_insert_of_two_outside n hA2
      (u := one n) (v := four n)
      (by simp [C1]) (by simp [C1])
      (by simp [H2, X, Z, blockSet]) (by simp [H2, X, Z, blockSet])
      (one_ne_four n)) hEq.symm.subset
  · intro hEq
    exact (not_subset_insert_of_two_outside n hA2
      (u := four n) (v := y0 n)
      (by simp) (Set.mem_union_right _ (y0_mem_Y n))
      (by simp [H2, X, Z, blockSet]) (by simp [H2, X, Z, blockSet, y0])
      (by simp [four, y0])) hEq.symm.subset
  · intro hEq
    exact (not_subset_insert_of_two_outside n hA2
      (u := three n) (v := four n)
      (by simp [C3]) (by simp [C3])
      (by simp [H2, X, Z, blockSet]) (by simp [H2, X, Z, blockSet])
      (three_ne_four n)) hEq.symm.subset
  · intro hsub
    exact hA1 (fun _ hx ↦ hsub (Set.mem_insert_of_mem f hx))
  · intro hsub
    exact hf2 (hsub (Set.mem_insert f A))
  · intro hsub
    exact hA3 (fun _ hx ↦ hsub (Set.mem_insert_of_mem f hx))

theorem admissible_insert_of_subset_H3 {A : Set (Element n)} {f : Element n}
    (hA1 : ¬ A ⊆ H1 n) (hA2 : ¬ A ⊆ H2 n) (hA3 : A ⊆ H3 n)
    (hf3 : f ∉ H3 n) : Admissible n (insert f A) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact not_subset_insert_of_two_outside n hA3 (one_mem_T n) (two_mem_T n)
      (by simp [H3, X, Y, blockSet]) (by simp [H3, X, Y, blockSet]) (one_ne_two n)
  · intro hEq
    exact (not_subset_insert_of_two_outside n hA3
      (u := one n) (v := four n)
      (by simp [C1]) (by simp [C1])
      (by simp [H3, X, Y, blockSet]) (by simp [H3, X, Y, blockSet])
      (one_ne_four n)) hEq.symm.subset
  · intro hEq
    exact (not_subset_insert_of_two_outside n hA3
      (u := two n) (v := four n)
      (by simp [C2]) (by simp [C2])
      (by simp [H3, X, Y, blockSet]) (by simp [H3, X, Y, blockSet])
      (two_ne_four n)) hEq.symm.subset
  · intro hEq
    exact (not_subset_insert_of_two_outside n hA3
      (u := four n) (v := z0 n)
      (by simp) (Set.mem_union_right _ (z0_mem_Z n))
      (by simp [H3, X, Y, blockSet]) (by simp [H3, X, Y, blockSet, z0])
      (by simp [four, z0])) hEq.symm.subset
  · intro hsub
    exact hA1 (fun _ hx ↦ hsub (Set.mem_insert_of_mem f hx))
  · intro hsub
    exact hA2 (fun _ hx ↦ hsub (Set.mem_insert_of_mem f hx))
  · intro hsub
    exact hf3 (hsub (Set.mem_insert f A))

private theorem admissible_insert_of_no_hyperplane {A : Set (Element n)} {f : Element n}
    (hA1 : ¬ A ⊆ H1 n) (hA2 : ¬ A ⊆ H2 n) (hA3 : ¬ A ⊆ H3 n)
    (hE : ¬ Exceptional n A f) : Admissible n (insert f A) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h ↦ hE (Or.inl h)
  · exact fun h ↦ hE (Or.inr (Or.inl h))
  · exact fun h ↦ hE (Or.inr (Or.inr (Or.inl h)))
  · exact fun h ↦ hE (Or.inr (Or.inr (Or.inr h)))
  · exact fun h ↦ hA1 (fun _ hx ↦ h (Set.mem_insert_of_mem f hx))
  · exact fun h ↦ hA2 (fun _ hx ↦ h (Set.mem_insert_of_mem f hx))
  · exact fun h ↦ hA3 (fun _ hx ↦ h (Set.mem_insert_of_mem f hx))

/-- The first `n` elements of `X`; the unused last element makes this
definition uniform even when `n=0`. -/
def initialX : Set (Element n) :=
  Set.range (fun i : Fin n ↦ Element.block (0 : Fin 3) i.castSucc)

theorem initialX_injective :
    Function.Injective (fun i : Fin n ↦ Element.block (0 : Fin 3) i.castSucc) := by
  intro i j h
  apply Fin.castSucc_injective n
  simpa using h

@[simp] theorem ncard_initialX : (initialX n).ncard = n := by
  rw [initialX, Set.ncard_range_of_injective (initialX_injective n)]
  simp

@[simp] theorem special_not_mem_initialX (s : Fin 4) :
    Element.special s ∉ initialX n := by
  simp [initialX]

/-- A concrete admissible rank-size set.  It proves that the displayed basis
family is nonempty independently of the later exchange proof. -/
def canonicalBase : Set (Element n) :=
  {one n, two n, four n} ∪ initialX n

theorem special_triple_disjoint_initialX :
    Disjoint ({one n, two n, four n} : Set (Element n)) (initialX n) := by
  rw [Set.disjoint_left]
  intro e he hX
  rcases he with (rfl | he)
  · exact special_not_mem_initialX n 0 hX
  rcases he with (rfl | he)
  · exact special_not_mem_initialX n 1 hX
  rcases he with (rfl | hfalse)
  · exact special_not_mem_initialX n 3 hX

@[simp] theorem ncard_canonicalBase : (canonicalBase n).ncard = n + 3 := by
  rw [canonicalBase, Set.ncard_union_eq (special_triple_disjoint_initialX n)]
  simp [one, two, four, Nat.add_comm]

/-! ### Literal base predicate -/

/-- The basis presentation of `MIₙ` from Conjecture 5.3 of
De Loera--Lee--Margulies--Miller. -/
def IsBase (B : Set (Element n)) : Prop :=
  B ⊆ ground n ∧ B.ncard = n + 3 ∧ Admissible n B

/-- The basis predicate is nonempty.  This does not use basis exchange. -/
theorem canonicalBase_isBase : IsBase n (canonicalBase n) := by
  refine ⟨fun _ _ ↦ mem_ground n _, ncard_canonicalBase n, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hT
    have hthree : three n ∈ canonicalBase n := hT (three_mem_T n)
    simp [canonicalBase, initialX, one, two, three, four] at hthree
  · intro hEq
    have htwo : two n ∈ C1 n := hEq ▸ (show two n ∈ canonicalBase n by simp [canonicalBase])
    simp [C1, X, blockSet, one, two, four] at htwo
  · intro hEq
    have hone : one n ∈ C2 n := hEq ▸ (show one n ∈ canonicalBase n by simp [canonicalBase])
    simp [C2, Y, blockSet, one, two, four] at hone
  · intro hEq
    have hone : one n ∈ C3 n := hEq ▸ (show one n ∈ canonicalBase n by simp [canonicalBase])
    simp [C3, Z, blockSet, one, three, four] at hone
  · intro hsub
    have hfour : four n ∈ H1 n := hsub (by simp [canonicalBase])
    simp [H1, Y, Z, blockSet, one, four] at hfour
  · intro hsub
    have hfour : four n ∈ H2 n := hsub (by simp [canonicalBase])
    simp [H2, X, Z, blockSet, two, four] at hfour
  · intro hsub
    have hfour : four n ∈ H3 n := hsub (by simp [canonicalBase])
    simp [H3, X, Y, blockSet, three, four] at hfour

theorem exists_isBase : ∃ B, IsBase n B :=
  ⟨canonicalBase n, canonicalBase_isBase n⟩

theorem IsBase.subset_ground {B : Set (Element n)} (hB : IsBase n B) :
    B ⊆ ground n :=
  hB.1

theorem IsBase.ncard_eq {B : Set (Element n)} (hB : IsBase n B) :
    B.ncard = n + 3 :=
  hB.2.1

theorem IsBase.not_T_subset {B : Set (Element n)} (hB : IsBase n B) :
    ¬ T n ⊆ B :=
  hB.2.2.1

theorem IsBase.ne_C1 {B : Set (Element n)} (hB : IsBase n B) : B ≠ C1 n :=
  hB.2.2.2.1

theorem IsBase.ne_C2 {B : Set (Element n)} (hB : IsBase n B) : B ≠ C2 n :=
  hB.2.2.2.2.1

theorem IsBase.ne_C3 {B : Set (Element n)} (hB : IsBase n B) : B ≠ C3 n :=
  hB.2.2.2.2.2.1

theorem IsBase.not_subset_H1 {B : Set (Element n)} (hB : IsBase n B) :
    ¬ B ⊆ H1 n :=
  hB.2.2.2.2.2.2.1

theorem IsBase.not_subset_H2 {B : Set (Element n)} (hB : IsBase n B) :
    ¬ B ⊆ H2 n :=
  hB.2.2.2.2.2.2.2.1

theorem IsBase.not_subset_H3 {B : Set (Element n)} (hB : IsBase n B) :
    ¬ B ⊆ H3 n :=
  hB.2.2.2.2.2.2.2.2

private theorem exchanged_isBase {B : Set (Element n)} {e f : Element n}
    (hB : IsBase n B) (heB : e ∈ B) (hfB : f ∉ B)
    (hAd : Admissible n (insert f (B \ {e}))) :
    IsBase n (insert f (B \ {e})) := by
  refine ⟨fun _ _ ↦ mem_ground n _, ?_, hAd⟩
  have hfA : f ∉ B \ {e} := fun h ↦ hfB h.1
  rw [Set.ncard_insert_of_notMem hfA, Set.ncard_diff_singleton_of_mem heB,
    hB.ncard_eq]
  omega

theorem IsBase.not_exceptional {A : Set (Element n)} {f : Element n}
    (hB : IsBase n (insert f A)) : ¬ Exceptional n A f := by
  rintro (hT | hC1 | hC2 | hC3)
  · exact IsBase.not_T_subset n hB hT
  · exact IsBase.ne_C1 n hB hC1
  · exact IsBase.ne_C2 n hB hC2
  · exact IsBase.ne_C3 n hB hC3

/-- The displayed basis family satisfies the basis-exchange property for every
parameter `n`. -/
theorem isBase_exchange : Matroid.ExchangeProperty (IsBase n) := by
  classical
  intro B₁ B₂ hB₁ hB₂ e he
  let A : Set (Element n) := B₁ \ {e}
  have hAcard : A.ncard = n + 2 := by
    change (B₁ \ {e}).ncard = n + 2
    rw [Set.ncard_diff_singleton_of_mem he.1, IsBase.ncard_eq n hB₁]
    omega
  have hTA : ¬ T n ⊆ A := fun h ↦
    IsBase.not_T_subset n hB₁ (h.trans (by intro x hx; exact hx.1))
  by_cases hA1 : A ⊆ H1 n
  · have hA2 := not_subset_H2_of_subset_H1 n hAcard hA1
    have hA3 := not_subset_H3_of_subset_H1 n hAcard hA1
    obtain ⟨f, hfB₂, hfH1⟩ := Set.not_subset.1 (IsBase.not_subset_H1 n hB₂)
    have hfB₁ : f ∉ B₁ := by
      intro hfB₁
      by_cases hfe : f = e
      · subst f
        exact he.2 hfB₂
      · exact hfH1 (hA1 ⟨hfB₁, by simp [hfe]⟩)
    exact ⟨f, ⟨hfB₂, hfB₁⟩,
      exchanged_isBase n hB₁ he.1 hfB₁
        (admissible_insert_of_subset_H1 n hA1 hA2 hA3 hfH1)⟩
  · by_cases hA2 : A ⊆ H2 n
    · have hA3 := not_subset_H3_of_subset_H2 n hAcard hA2
      obtain ⟨f, hfB₂, hfH2⟩ := Set.not_subset.1 (IsBase.not_subset_H2 n hB₂)
      have hfB₁ : f ∉ B₁ := by
        intro hfB₁
        by_cases hfe : f = e
        · subst f
          exact he.2 hfB₂
        · exact hfH2 (hA2 ⟨hfB₁, by simp [hfe]⟩)
      exact ⟨f, ⟨hfB₂, hfB₁⟩,
        exchanged_isBase n hB₁ he.1 hfB₁
          (admissible_insert_of_subset_H2 n hA1 hA2 hA3 hfH2)⟩
    · by_cases hA3 : A ⊆ H3 n
      · obtain ⟨f, hfB₂, hfH3⟩ := Set.not_subset.1 (IsBase.not_subset_H3 n hB₂)
        have hfB₁ : f ∉ B₁ := by
          intro hfB₁
          by_cases hfe : f = e
          · subst f
            exact he.2 hfB₂
          · exact hfH3 (hA3 ⟨hfB₁, by simp [hfe]⟩)
        exact ⟨f, ⟨hfB₂, hfB₁⟩,
          exchanged_isBase n hB₁ he.1 hfB₁
            (admissible_insert_of_subset_H3 n hA1 hA2 hA3 hfH3)⟩
      · have hnsub : ¬ B₂ ⊆ B₁ := by
          intro hsub
          have hEq : B₂ = B₁ := Set.eq_of_subset_of_ncard_le hsub (by
            rw [IsBase.ncard_eq n hB₁, IsBase.ncard_eq n hB₂])
          exact he.2 (hEq.symm ▸ he.1)
        obtain ⟨f, hfB₂, hfB₁⟩ := Set.not_subset.1 hnsub
        have hfA : f ∉ A := fun h ↦ hfB₁ h.1
        by_cases hfE : Exceptional n A f
        · have hextra : ∃ g, g ∈ B₂ ∧ g ∉ B₁ ∧ g ≠ f := by
            by_contra hnone
            have huniq : ∀ g, g ∈ B₂ → g ∉ B₁ → g = f := by
              intro g hgB₂ hgB₁
              by_contra hgf
              exact hnone ⟨g, hgB₂, hgB₁, hgf⟩
            have hsub : B₂ ⊆ insert f A := by
              intro x hxB₂
              by_cases hxB₁ : x ∈ B₁
              · have hxe : x ≠ e := by
                  intro hxe
                  subst x
                  exact he.2 hxB₂
                exact Set.mem_insert_of_mem f ⟨hxB₁, by simp [hxe]⟩
              · rw [Set.mem_insert_iff]
                exact Or.inl (huniq x hxB₂ hxB₁)
            have hcard : (insert f A).ncard = n + 3 := by
              rw [Set.ncard_insert_of_notMem hfA, hAcard]
            have hEq : B₂ = insert f A := Set.eq_of_subset_of_ncard_le hsub (by
              rw [hcard, IsBase.ncard_eq n hB₂])
            have hCand : IsBase n (insert f A) := by
              rw [← hEq]
              exact hB₂
            exact IsBase.not_exceptional n hCand hfE
          obtain ⟨g, hgB₂, hgB₁, hgf⟩ := hextra
          have hgE : ¬ Exceptional n A g := by
            intro hgE
            exact hgf (exceptional_unique n hTA hfA hfE hgE).symm
          exact ⟨g, ⟨hgB₂, hgB₁⟩,
            exchanged_isBase n hB₁ he.1 hgB₁
              (admissible_insert_of_no_hyperplane n hA1 hA2 hA3 hgE)⟩
        · exact ⟨f, ⟨hfB₂, hfB₁⟩,
            exchanged_isBase n hB₁ he.1 hfB₁
              (admissible_insert_of_no_hyperplane n hA1 hA2 hA3 hfE)⟩

/-- The finite basis presentation defining `MIₙ`. -/
def presentation : FiniteBasisPresentation (Element n) where
  ground := ground n
  IsBase := IsBase n
  finite_ground := ground_finite n
  exists_isBase := exists_isBase n
  exchange := isBase_exchange n
  subset_ground := fun _ hB ↦ IsBase.subset_ground n hB

/-- The actual Mathlib matroid `MIₙ`. -/
def MI : Matroid (Element n) :=
  (presentation n).toMatroid

@[simp] theorem MI_ground : (MI n).E = ground n := rfl

@[simp] theorem ncard_MI_ground : (MI n).E.ncard = 3 * n + 7 := by
  rw [MI_ground, ncard_ground]

@[simp] theorem encard_MI_ground : (MI n).E.encard = (3 * n + 7 : ℕ) := by
  rw [MI_ground, encard_ground]

@[simp] theorem MI_isBase_iff (B : Set (Element n)) :
    (MI n).IsBase B ↔ IsBase n B := Iff.rfl

instance : (MI n).Finite := by
  rw [MI]
  infer_instance

end Family

end BlandJensenFormal.BlandJensenMI
