import BlandJensenFormal.BlandJensenMI.QuotientGeometry
import BlandJensenFormal.BlandJensenMI.Templates

/-!
# Linear independence of the fixed special columns

Capacity checks split into mixed subfamilies, which contain a large-block
subspace, and pure special subfamilies.  This file supplies the exact finite
linear algebra needed for the latter.  The statements are structural and do
not mention the minor base predicates.
-/

namespace BlandJensenFormal.BlandJensenMI.SpecialGeometry

open Function Set
open BlandJensenFormal.BlandJensenMI.Templates
open BlandJensenFormal.BlandJensenMI.QuotientGeometry

private theorem quotientInclusion_ker_eq_bot (n q : ℕ) :
    LinearMap.ker (quotientInclusion n q) = ⊥ := by
  ext x
  simp [quotientInclusion]

private theorem linearIndependent_restrict_of_subset_range
    {ι κ V : Type*} [AddCommGroup V] [Module ℚ V]
    (v : κ → V) (t : ι → κ) (ht : Function.Injective t)
    {S : Set κ} (hS : S ⊆ Set.range t)
    (hLinear : LinearIndependent ℚ (v ∘ t)) :
    LinearIndependent ℚ (fun s : S ↦ v s) := by
  exact ((linearIndepOn_range_iff ht v).2 hLinear).mono hS

private theorem comp_fin2 {α β : Type*} (f : α → β) (a b : α) :
    f ∘ ![a, b] = ![f a, f b] := by
  funext i
  fin_cases i <;> rfl

private theorem comp_fin3 {α β : Type*} (f : α → β) (a b c : α) :
    f ∘ ![a, b, c] = ![f a, f b, f c] := by
  funext i
  fin_cases i <;> rfl

namespace DeleteX

open Templates.DeleteX

theorem linearIndependent_two_three_four (n : ℕ) :
    LinearIndependent ℚ
      ![special n .Two, special n .Three, special n .Four] := by
  have hq : LinearIndependent ℚ
      ![quotientLabel .Two, quotientLabel .Three, quotientLabel .Four] :=
    (linearIndependent_vec3_iff_det3_ne_zero
      (quotientLabel .Two) (quotientLabel .Three)
        (quotientLabel .Four)).2 (by
          norm_num [quotientLabel,
            BlandJensenFormal.MIQuotientLabels.DeleteX.label,
            BlandJensenFormal.MIQuotientLabels.det3,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two])
  have hm := hq.map' (quotientInclusion n quotientDim)
    (quotientInclusion_ker_eq_bot n quotientDim)
  have hfun :
      (quotientInclusion n quotientDim) ∘
          ![quotientLabel .Two, quotientLabel .Three, quotientLabel .Four] =
        ![special n .Two, special n .Three, special n .Four] := by
    funext i
    fin_cases i <;> rfl
  rw [hfun] at hm
  exact hm

theorem linearIndependent_one_three_four (n : ℕ) :
    LinearIndependent ℚ
      ![special n .One, special n .Three, special n .Four] := by
  have hq : LinearIndependent ℚ
      ![quotientLabel .One, quotientLabel .Three, quotientLabel .Four] :=
    (linearIndependent_vec3_iff_det3_ne_zero
      (quotientLabel .One) (quotientLabel .Three)
        (quotientLabel .Four)).2 (by
          norm_num [quotientLabel,
            BlandJensenFormal.MIQuotientLabels.DeleteX.label,
            BlandJensenFormal.MIQuotientLabels.det3,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two])
  have hm := hq.map' (quotientInclusion n quotientDim)
    (quotientInclusion_ker_eq_bot n quotientDim)
  have hfun :
      (quotientInclusion n quotientDim) ∘
          ![quotientLabel .One, quotientLabel .Three, quotientLabel .Four] =
        ![special n .One, special n .Three, special n .Four] := by
    funext i
    fin_cases i <;> rfl
  rw [hfun] at hm
  exact hm

theorem linearIndependent_one_two_four (n : ℕ) :
    LinearIndependent ℚ
      ![special n .One, special n .Two, special n .Four] := by
  have hq : LinearIndependent ℚ
      ![quotientLabel .One, quotientLabel .Two, quotientLabel .Four] :=
    (linearIndependent_vec3_iff_det3_ne_zero
      (quotientLabel .One) (quotientLabel .Two)
        (quotientLabel .Four)).2 (by
          norm_num [quotientLabel,
            BlandJensenFormal.MIQuotientLabels.DeleteX.label,
            BlandJensenFormal.MIQuotientLabels.det3,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two])
  have hm := hq.map' (quotientInclusion n quotientDim)
    (quotientInclusion_ker_eq_bot n quotientDim)
  have hfun :
      (quotientInclusion n quotientDim) ∘
          ![quotientLabel .One, quotientLabel .Two, quotientLabel .Four] =
        ![special n .One, special n .Two, special n .Four] := by
    funext i
    fin_cases i <;> rfl
  rw [hfun] at hm
  exact hm

theorem linearIndependent_special_of_not_core_triple_subset
    (n : ℕ) {S : Set Special}
    (hT : ¬ ({.One, .Two, .Three} : Set Special) ⊆ S) :
    LinearIndependent ℚ (fun s : S ↦ special n s) := by
  have hmissing : .One ∉ S ∨ .Two ∉ S ∨ .Three ∉ S := by
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff] at hT
    tauto
  rcases hmissing with hOne | hTwo | hThree
  · apply linearIndependent_restrict_of_subset_range
      (special n) ![.Two, .Three, .Four] (by decide)
    · intro s hs
      cases s <;> simp_all
    · simpa only [comp_fin3] using linearIndependent_two_three_four n
  · apply linearIndependent_restrict_of_subset_range
      (special n) ![.One, .Three, .Four] (by decide)
    · intro s hs
      cases s <;> simp_all
    · simpa only [comp_fin3] using linearIndependent_one_three_four n
  · apply linearIndependent_restrict_of_subset_range
      (special n) ![.One, .Two, .Four] (by decide)
    · intro s hs
      cases s <;> simp_all
    · simpa only [comp_fin3] using linearIndependent_one_two_four n

end DeleteX

namespace DeleteOne

open Templates.DeleteOne

theorem linearIndependent_two_three_four (n : ℕ) :
    LinearIndependent ℚ
      ![special n .Two, special n .Three, special n .Four] := by
  have hq : LinearIndependent ℚ
      ![quotientLabel .Two, quotientLabel .Three, quotientLabel .Four] :=
    (linearIndependent_vec3_iff_det3_ne_zero
      (quotientLabel .Two) (quotientLabel .Three)
        (quotientLabel .Four)).2 (by
          norm_num [quotientLabel,
            BlandJensenFormal.MIQuotientLabels.DeleteOne.label,
            BlandJensenFormal.MIQuotientLabels.det3,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two])
  have hm := hq.map' (quotientInclusion n quotientDim)
    (quotientInclusion_ker_eq_bot n quotientDim)
  have hfun :
      (quotientInclusion n quotientDim) ∘
          ![quotientLabel .Two, quotientLabel .Three, quotientLabel .Four] =
        ![special n .Two, special n .Three, special n .Four] := by
    funext i
    fin_cases i <;> rfl
  rw [hfun] at hm
  exact hm

theorem linearIndependent_special (n : ℕ) :
    LinearIndependent ℚ (special n) := by
  apply (linearIndepOn_univ_iff).mp
  apply linearIndependent_restrict_of_subset_range
    (special n) ![.Two, .Three, .Four] (by decide)
  · intro s _
    cases s <;> simp
  · simpa only [comp_fin3] using linearIndependent_two_three_four n

end DeleteOne

namespace DeleteFour

open Templates.DeleteFour

theorem linearIndependent_one_two (n : ℕ) :
    LinearIndependent ℚ ![special n .One, special n .Two] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have h0 := congrArg (fun z : Ambient n quotientDim ↦ z.2 0) hab
  have h1 := congrArg (fun z : Ambient n quotientDim ↦ z.2 1) hab
  constructor
  · simpa [special, quotientLabel,
      BlandJensenFormal.MIQuotientLabels.DeleteFour.label] using h1
  · simpa [special, quotientLabel,
      BlandJensenFormal.MIQuotientLabels.DeleteFour.label] using h0

theorem linearIndependent_one_three (n : ℕ) :
    LinearIndependent ℚ ![special n .One, special n .Three] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have h0 := congrArg (fun z : Ambient n quotientDim ↦ z.2 0) hab
  have h1 := congrArg (fun z : Ambient n quotientDim ↦ z.2 1) hab
  have hb : b = 0 := by
    simpa [special, quotientLabel,
      BlandJensenFormal.MIQuotientLabels.DeleteFour.label] using h0
  subst b
  constructor
  · simpa [special, quotientLabel,
      BlandJensenFormal.MIQuotientLabels.DeleteFour.label] using h1
  · rfl

theorem linearIndependent_two_three (n : ℕ) :
    LinearIndependent ℚ ![special n .Two, special n .Three] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have h0 := congrArg (fun z : Ambient n quotientDim ↦ z.2 0) hab
  have h1 := congrArg (fun z : Ambient n quotientDim ↦ z.2 1) hab
  have hb : b = 0 := by
    simpa [special, quotientLabel,
      BlandJensenFormal.MIQuotientLabels.DeleteFour.label] using h1
  subst b
  constructor
  · simpa [special, quotientLabel,
      BlandJensenFormal.MIQuotientLabels.DeleteFour.label] using h0
  · rfl

theorem linearIndependent_special_of_not_core_triple_subset
    (n : ℕ) {S : Set Special}
    (hT : ¬ ({.One, .Two, .Three} : Set Special) ⊆ S) :
    LinearIndependent ℚ (fun s : S ↦ special n s) := by
  have hmissing : .One ∉ S ∨ .Two ∉ S ∨ .Three ∉ S := by
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff] at hT
    tauto
  rcases hmissing with hOne | hTwo | hThree
  · apply linearIndependent_restrict_of_subset_range
      (special n) ![.Two, .Three] (by decide)
    · intro s hs
      cases s <;> simp_all
    · simpa only [comp_fin2] using linearIndependent_two_three n
  · apply linearIndependent_restrict_of_subset_range
      (special n) ![.One, .Three] (by decide)
    · intro s hs
      cases s <;> simp_all
    · simpa only [comp_fin2] using linearIndependent_one_three n
  · apply linearIndependent_restrict_of_subset_range
      (special n) ![.One, .Two] (by decide)
    · intro s hs
      cases s <;> simp_all
    · simpa only [comp_fin2] using linearIndependent_one_two n

end DeleteFour

namespace ContractX

open Templates.ContractX

/-- For positive core dimension the perturbation on column `4` lifts every
pair of independent quotient directions to an independent triple. -/
theorem linearIndependent_two_three_four {n : ℕ} (hn : 0 < n) :
    LinearIndependent ℚ
      ![special n .Two, special n .Three, special n .Four] := by
  rw [Fintype.linearIndependent_iff]
  intro g hsum
  have hcore := congrArg
    (fun z : Ambient n quotientDim ↦ z.1 (⟨0, hn⟩ : Fin n)) hsum
  have hg2 : g 2 = 0 := by
    simpa [special, specialLift, coreDelta, hn, Fin.sum_univ_succ] using hcore
  have hq0 := congrArg
    (fun z : Ambient n quotientDim ↦ z.2 0) hsum
  have hq1 := congrArg
    (fun z : Ambient n quotientDim ↦ z.2 1) hsum
  have hg0 : g 0 = 0 := by
    simpa [special, specialLift, quotientLabel,
      BlandJensenFormal.MIQuotientLabels.ContractX.label,
      Fin.sum_univ_succ, hg2] using hq1
  have hg1 : g 1 = 0 := by
    simpa [special, specialLift, quotientLabel,
      BlandJensenFormal.MIQuotientLabels.ContractX.label,
      Fin.sum_univ_succ, hg2] using hq0
  intro i
  fin_cases i <;> assumption

theorem linearIndependent_one_two_four {n : ℕ} (hn : 0 < n) :
    LinearIndependent ℚ
      ![special n .One, special n .Two, special n .Four] := by
  rw [Fintype.linearIndependent_iff]
  intro g hsum
  have hcore := congrArg
    (fun z : Ambient n quotientDim ↦ z.1 (⟨0, hn⟩ : Fin n)) hsum
  have hg2 : g 2 = 0 := by
    simpa [special, specialLift, coreDelta, hn, Fin.sum_univ_succ] using hcore
  have hq0 := congrArg
    (fun z : Ambient n quotientDim ↦ z.2 0) hsum
  have hq1 := congrArg
    (fun z : Ambient n quotientDim ↦ z.2 1) hsum
  have hg0 : g 0 = 0 := by
    simpa [special, specialLift, quotientLabel,
      BlandJensenFormal.MIQuotientLabels.ContractX.label,
      Fin.sum_univ_succ, hg2] using hq0
  have hg1 : g 1 = 0 := by
    simpa [special, specialLift, quotientLabel,
      BlandJensenFormal.MIQuotientLabels.ContractX.label,
      Fin.sum_univ_succ, hg2, hg0] using hq1
  intro i
  fin_cases i <;> assumption

theorem linearIndependent_one_three_four {n : ℕ} (hn : 0 < n) :
    LinearIndependent ℚ
      ![special n .One, special n .Three, special n .Four] := by
  rw [Fintype.linearIndependent_iff]
  intro g hsum
  have hcore := congrArg
    (fun z : Ambient n quotientDim ↦ z.1 (⟨0, hn⟩ : Fin n)) hsum
  have hg2 : g 2 = 0 := by
    simpa [special, specialLift, coreDelta, hn, Fin.sum_univ_succ] using hcore
  have hq0 := congrArg
    (fun z : Ambient n quotientDim ↦ z.2 0) hsum
  have hq1 := congrArg
    (fun z : Ambient n quotientDim ↦ z.2 1) hsum
  have hg0 : g 0 = 0 := by
    simpa [special, specialLift, quotientLabel,
      BlandJensenFormal.MIQuotientLabels.ContractX.label,
      Fin.sum_univ_succ, hg2] using hq1
  have hg1 : g 1 = 0 := by
    simpa [special, specialLift, quotientLabel,
      BlandJensenFormal.MIQuotientLabels.ContractX.label,
      Fin.sum_univ_succ, hg2, hg0] using hq0
  intro i
  fin_cases i <;> assumption

theorem linearIndependent_one_two (n : ℕ) :
    LinearIndependent ℚ ![special n .One, special n .Two] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have h0 := congrArg (fun z : Ambient n quotientDim ↦ z.2 0) hab
  have h1 := congrArg (fun z : Ambient n quotientDim ↦ z.2 1) hab
  have ha : a = 0 := by
    simpa [special, specialLift, quotientLabel,
      BlandJensenFormal.MIQuotientLabels.ContractX.label] using h0
  subst a
  constructor
  · rfl
  · simpa [special, specialLift, quotientLabel,
      BlandJensenFormal.MIQuotientLabels.ContractX.label] using h1

theorem linearIndependent_one_three (n : ℕ) :
    LinearIndependent ℚ ![special n .One, special n .Three] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have h0 := congrArg (fun z : Ambient n quotientDim ↦ z.2 0) hab
  have h1 := congrArg (fun z : Ambient n quotientDim ↦ z.2 1) hab
  have ha : a = 0 := by
    simpa [special, specialLift, quotientLabel,
      BlandJensenFormal.MIQuotientLabels.ContractX.label] using h1
  subst a
  constructor
  · rfl
  · simpa [special, specialLift, quotientLabel,
      BlandJensenFormal.MIQuotientLabels.ContractX.label] using h0

theorem linearIndependent_two_three (n : ℕ) :
    LinearIndependent ℚ ![special n .Two, special n .Three] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have h0 := congrArg (fun z : Ambient n quotientDim ↦ z.2 0) hab
  have h1 := congrArg (fun z : Ambient n quotientDim ↦ z.2 1) hab
  constructor
  · simpa [special, specialLift, quotientLabel,
      BlandJensenFormal.MIQuotientLabels.ContractX.label] using h1
  · simpa [special, specialLift, quotientLabel,
      BlandJensenFormal.MIQuotientLabels.ContractX.label] using h0

theorem linearIndependent_two_four (n : ℕ) :
    LinearIndependent ℚ ![special n .Two, special n .Four] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have h0 := congrArg (fun z : Ambient n quotientDim ↦ z.2 0) hab
  have h1 := congrArg (fun z : Ambient n quotientDim ↦ z.2 1) hab
  have hb : b = 0 := by
    simpa [special, specialLift, quotientLabel,
      BlandJensenFormal.MIQuotientLabels.ContractX.label] using h0
  subst b
  constructor
  · simpa [special, specialLift, quotientLabel,
      BlandJensenFormal.MIQuotientLabels.ContractX.label] using h1
  · rfl

theorem linearIndependent_three_four (n : ℕ) :
    LinearIndependent ℚ ![special n .Three, special n .Four] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have h0 := congrArg (fun z : Ambient n quotientDim ↦ z.2 0) hab
  have h1 := congrArg (fun z : Ambient n quotientDim ↦ z.2 1) hab
  have hb : b = 0 := by
    simpa [special, specialLift, quotientLabel,
      BlandJensenFormal.MIQuotientLabels.ContractX.label] using h1
  subst b
  constructor
  · simpa [special, specialLift, quotientLabel,
      BlandJensenFormal.MIQuotientLabels.ContractX.label] using h0
  · rfl

theorem linearIndependent_special_of_not_core_triple_subset
    {n : ℕ} (hn : 0 < n) {S : Set Special}
    (hT : ¬ ({.One, .Two, .Three} : Set Special) ⊆ S) :
    LinearIndependent ℚ (fun s : S ↦ special n s) := by
  have hmissing : .One ∉ S ∨ .Two ∉ S ∨ .Three ∉ S := by
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff] at hT
    tauto
  rcases hmissing with hOne | hTwo | hThree
  · apply linearIndependent_restrict_of_subset_range
      (special n) ![.Two, .Three, .Four] (by decide)
    · intro s hs
      cases s <;> simp_all
    · simpa only [comp_fin3] using linearIndependent_two_three_four hn
  · apply linearIndependent_restrict_of_subset_range
      (special n) ![.One, .Three, .Four] (by decide)
    · intro s hs
      cases s <;> simp_all
    · simpa only [comp_fin3] using linearIndependent_one_three_four hn
  · apply linearIndependent_restrict_of_subset_range
      (special n) ![.One, .Two, .Four] (by decide)
    · intro s hs
      cases s <;> simp_all
    · simpa only [comp_fin3] using linearIndependent_one_two_four hn

end ContractX

namespace ContractOne

open Templates.ContractOne

theorem linearIndependent_two_four (n : ℕ) :
    LinearIndependent ℚ ![special n .Two, special n .Four] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have h0 := congrArg (fun z : Ambient n quotientDim ↦ z.2 0) hab
  have h1 := congrArg (fun z : Ambient n quotientDim ↦ z.2 1) hab
  have ha : a = 0 := by
    simpa [special, quotientLabel,
      BlandJensenFormal.MIQuotientLabels.ContractOne.label] using h0
  subst a
  constructor
  · rfl
  · simpa [special, quotientLabel,
      BlandJensenFormal.MIQuotientLabels.ContractOne.label] using h1

theorem linearIndependent_three_four (n : ℕ) :
    LinearIndependent ℚ ![special n .Three, special n .Four] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have h0 := congrArg (fun z : Ambient n quotientDim ↦ z.2 0) hab
  have h1 := congrArg (fun z : Ambient n quotientDim ↦ z.2 1) hab
  have ha : a = 0 := by
    simpa [special, quotientLabel,
      BlandJensenFormal.MIQuotientLabels.ContractOne.label] using h0
  subst a
  constructor
  · rfl
  · simpa [special, quotientLabel,
      BlandJensenFormal.MIQuotientLabels.ContractOne.label] using h1

theorem linearIndependent_special_of_not_pair_subset
    (n : ℕ) {S : Set Special}
    (hPair : ¬ ({.Two, .Three} : Set Special) ⊆ S) :
    LinearIndependent ℚ (fun s : S ↦ special n s) := by
  have hmissing : .Two ∉ S ∨ .Three ∉ S := by
    simp only [Set.pair_subset_iff] at hPair
    tauto
  rcases hmissing with hTwo | hThree
  · apply linearIndependent_restrict_of_subset_range
      (special n) ![.Three, .Four] (by decide)
    · intro s hs
      cases s <;> simp_all
    · simpa only [comp_fin2] using linearIndependent_three_four n
  · apply linearIndependent_restrict_of_subset_range
      (special n) ![.Two, .Four] (by decide)
    · intro s hs
      cases s <;> simp_all
    · simpa only [comp_fin2] using linearIndependent_two_four n

end ContractOne

namespace ContractFour

open Templates.ContractFour

theorem linearIndependent_one_two (n : ℕ) :
    LinearIndependent ℚ ![special n .One, special n .Two] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have h0 := congrArg (fun z : Ambient n quotientDim ↦ z.2 0) hab
  have h1 := congrArg (fun z : Ambient n quotientDim ↦ z.2 1) hab
  constructor
  · simpa [special, quotientLabel,
      BlandJensenFormal.MIQuotientLabels.ContractFour.label] using h0
  · simpa [special, quotientLabel,
      BlandJensenFormal.MIQuotientLabels.ContractFour.label] using h1

theorem linearIndependent_one_three (n : ℕ) :
    LinearIndependent ℚ ![special n .One, special n .Three] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have h0 := congrArg (fun z : Ambient n quotientDim ↦ z.2 0) hab
  have h1 := congrArg (fun z : Ambient n quotientDim ↦ z.2 1) hab
  have hb : b = 0 := by
    simpa [special, quotientLabel,
      BlandJensenFormal.MIQuotientLabels.ContractFour.label] using h1
  subst b
  constructor
  · simpa [special, quotientLabel,
      BlandJensenFormal.MIQuotientLabels.ContractFour.label] using h0
  · rfl

theorem linearIndependent_two_three (n : ℕ) :
    LinearIndependent ℚ ![special n .Two, special n .Three] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have h0 := congrArg (fun z : Ambient n quotientDim ↦ z.2 0) hab
  have h1 := congrArg (fun z : Ambient n quotientDim ↦ z.2 1) hab
  have hb : b = 0 := by
    simpa [special, quotientLabel,
      BlandJensenFormal.MIQuotientLabels.ContractFour.label] using h0
  subst b
  constructor
  · simpa [special, quotientLabel,
      BlandJensenFormal.MIQuotientLabels.ContractFour.label] using h1
  · rfl

theorem linearIndependent_special_of_not_core_triple_subset
    (n : ℕ) {S : Set Special}
    (hT : ¬ ({.One, .Two, .Three} : Set Special) ⊆ S) :
    LinearIndependent ℚ (fun s : S ↦ special n s) := by
  have hmissing : .One ∉ S ∨ .Two ∉ S ∨ .Three ∉ S := by
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff] at hT
    tauto
  rcases hmissing with hOne | hTwo | hThree
  · apply linearIndependent_restrict_of_subset_range
      (special n) ![.Two, .Three] (by decide)
    · intro s hs
      cases s <;> simp_all
    · simpa only [comp_fin2] using linearIndependent_two_three n
  · apply linearIndependent_restrict_of_subset_range
      (special n) ![.One, .Three] (by decide)
    · intro s hs
      cases s <;> simp_all
    · simpa only [comp_fin2] using linearIndependent_one_three n
  · apply linearIndependent_restrict_of_subset_range
      (special n) ![.One, .Two] (by decide)
    · intro s hs
      cases s <;> simp_all
    · simpa only [comp_fin2] using linearIndependent_one_two n

end ContractFour

end BlandJensenFormal.BlandJensenMI.SpecialGeometry
