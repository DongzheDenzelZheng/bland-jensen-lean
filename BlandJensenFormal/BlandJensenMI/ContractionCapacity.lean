import BlandJensenFormal.BlandJensenMI.Minors
import BlandJensenFormal.BlandJensenMI.TemplateInstances
import BlandJensenFormal.BlandJensenMI.QuotientCarrierAudit
import BlandJensenFormal.BlandJensenMI.ClassifiedGeometry
import BlandJensenFormal.BlandJensenMI.SpecialGeometry
import BlandJensenFormal.BlandJensenMI.CapacityHelpers
import BlandJensenFormal.BlandJensenMI.RepresentationCompiler

/-!
# Capacity audits for the three contraction templates

This file connects the exact basis predicates for contraction by `x₀`, `1`,
and `4` with their two-dimensional quotient templates.  All arguments are
uniform in `n`; the boundary case `n = 0` is treated explicitly where the
common-core perturbation in the `ContractX` template vanishes.
-/

namespace BlandJensenFormal.BlandJensenMI.ContractionCapacity

open Function Set Submodule
open scoped Matroid

/-! ## Common finite-selector bookkeeping -/

/-- The actual element set selected by a finset of elements of `B`. -/
def actualSet {n : ℕ} {B : Set (Element n)} (J : Finset B) :
    Set (Element n) := Subtype.val '' (J : Set B)

@[simp] theorem ncard_actualSet {n : ℕ} {B : Set (Element n)}
    (J : Finset B) : (actualSet J).ncard = J.card := by
  rw [actualSet, Set.ncard_image_of_injective _ Subtype.val_injective]
  simp

theorem actualSet_subset {n : ℕ} {B : Set (Element n)}
    (J : Finset B) : actualSet J ⊆ B := by
  rintro e ⟨b, -, rfl⟩
  exact b.property

theorem card_selector_le_of_ncard {n d : ℕ} {B : Set (Element n)}
    [Fintype B] (hBcard : B.ncard = d) (J : Finset B) : J.card ≤ d := by
  calc
    J.card ≤ Fintype.card B := Finset.card_le_univ J
    _ = B.ncard := by simp [← Nat.card_eq_fintype_card]
    _ = d := hBcard

/-- Equality in the preceding bound means that the selector is all of `B`. -/
theorem selector_eq_univ_of_card_eq {n d : ℕ} {B : Set (Element n)}
    [Fintype B] (hBcard : B.ncard = d) {J : Finset B}
    (hJcard : J.card = d) : J = Finset.univ := by
  apply Finset.eq_univ_of_card
  simpa [← Nat.card_eq_fintype_card, hBcard] using hJcard

/-! ## Contraction of `x₀` -/

namespace ContractX

abbrev Label := QuotientCarrierAudit.ContractX.Label

def blockLabelClass : Fin 3 → Label := ![.X, .Y, .Z]
def specialLabelClass : Fin 4 → Label := ![.One, .Two, .Three, .Four]

/-- Fixed quotient-label name attached to every actual element. -/
def labelClass (n : ℕ) : Element n → Label
  | .special s => specialLabelClass s
  | .block b _ => blockLabelClass b

def quotientLabel (n : ℕ) :
    Element n → Templates.QuotientSpace Templates.ContractX.quotientDim :=
  ClassifiedGeometry.quotientLabelOf
    Templates.ContractX.blockLabel (Templates.ContractX.special n)
    (TemplateInstances.ContractX.blockClass n)
    (TemplateInstances.ContractX.specialClass n)

/-- The element-level quotient label agrees with the audited finite label.
This remains true on the contracted element because both sides are zero. -/
theorem quotientLabel_eq_label (n : ℕ) (e : Element n) :
    quotientLabel n e = QuotientCarrierAudit.ContractX.label (labelClass n e) := by
  cases e with
  | special s => fin_cases s <;> rfl
  | block b i =>
      fin_cases b
      · by_cases hi : i = 0
        · subst i
          change (0 : Templates.QuotientSpace
            Templates.ContractX.quotientDim) =
              QuotientCarrierAudit.ContractX.label .X
          exact QuotientCarrierAudit.ContractX.zero_label.symm
        · simp [quotientLabel, ClassifiedGeometry.quotientLabelOf,
            TemplateInstances.ContractX.blockClass,
            TemplateInstances.ContractX.removedElement,
            TemplateInstances.ContractX.blockKind, labelClass, blockLabelClass,
            Family.x0, hi, Templates.ContractX.blockLabel,
            Templates.ContractX.quotientLabel,
            QuotientCarrierAudit.ContractX.label]
      · simp [quotientLabel, ClassifiedGeometry.quotientLabelOf,
          TemplateInstances.ContractX.blockClass,
          TemplateInstances.ContractX.removedElement,
          TemplateInstances.ContractX.blockKind, labelClass, blockLabelClass,
          Family.x0, Templates.ContractX.blockLabel,
          Templates.ContractX.quotientLabel,
          QuotientCarrierAudit.ContractX.label]
      · simp [quotientLabel, ClassifiedGeometry.quotientLabelOf,
          TemplateInstances.ContractX.blockClass,
          TemplateInstances.ContractX.removedElement,
          TemplateInstances.ContractX.blockKind, labelClass, blockLabelClass,
          Family.x0, Templates.ContractX.blockLabel,
          Templates.ContractX.quotientLabel,
          QuotientCarrierAudit.ContractX.label]

def selectedLabels {n : ℕ} {B : Set (Element n)} (J : Finset B) :
    Finset Label := J.image (fun b : B ↦ labelClass n (b : Element n))

theorem label_mem_selectedLabels {n : ℕ} {B : Set (Element n)}
    {J : Finset B} {b : B} (hb : b ∈ J) :
    labelClass n (b : Element n) ∈ selectedLabels J := by
  exact Finset.mem_image.mpr ⟨b, hb, rfl⟩

theorem quotient_image_eq {n : ℕ} {B : Set (Element n)} (J : Finset B) :
    (quotientLabel n ∘ fun b : B ↦ (b : Element n)) '' (J : Set B) =
      QuotientCarrierAudit.ContractX.label ''
        (selectedLabels J : Set Label) := by
  ext p
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [Function.comp_apply, quotientLabel_eq_label]
    exact ⟨labelClass n b, label_mem_selectedLabels hb, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hl
    exact ⟨b, hb, quotientLabel_eq_label n b⟩

theorem labelClass_eq_X_iff (n : ℕ) (e : Element n) :
    labelClass n e = .X ↔ e ∈ Family.X n := by
  cases e with
  | special s =>
      fin_cases s <;> simp [labelClass, specialLabelClass, Family.X,
        Family.blockSet]
  | block b i =>
      fin_cases b <;> simp [labelClass, blockLabelClass, Family.X,
        Family.blockSet]

/-- Removing the unique zero label does not change the quotient span. -/
theorem span_selectedLabels_erase_X (S : Finset Label) :
    Submodule.span ℚ
        (QuotientCarrierAudit.ContractX.label '' (S : Set Label)) =
      Submodule.span ℚ
        (QuotientCarrierAudit.ContractX.label ''
          (S.erase .X : Set Label)) := by
  by_cases hX : .X ∈ S
  · calc
      Submodule.span ℚ
          (QuotientCarrierAudit.ContractX.label '' (S : Set Label)) =
          Submodule.span ℚ
            (QuotientCarrierAudit.ContractX.label ''
              ((insert .X (S.erase .X) : Finset Label) : Set Label)) := by
            rw [Finset.insert_erase hX]
      _ = Submodule.span ℚ
            (QuotientCarrierAudit.ContractX.label ''
              (S.erase .X : Set Label)) :=
        QuotientCarrierAudit.ContractX.span_insert_zero_label _
  · simp [Finset.erase_eq_of_notMem hX]

/-- Actual support of a rank-one quotient carrier, with the zero-labelled
`X` block adjoined. -/
def carrierSupport (n : ℕ) :
    QuotientCarrierAudit.ContractX.Carrier → Set (Element n)
  | .b => Family.H3 n \ {Family.x0 n}
  | .c => Family.H2 n \ {Family.x0 n}
  | .bPlusC => Family.C1 n \ {Family.x0 n}

theorem mem_carrierSupport_of_label
    {n : ℕ} {e : Element n}
    (he : e ≠ Family.x0 n)
    (C : QuotientCarrierAudit.ContractX.Carrier)
    (hLabel : labelClass n e = .X ∨
      labelClass n e ∈ QuotientCarrierAudit.ContractX.carrier C) :
    e ∈ carrierSupport n C := by
  cases C <;> cases e with
  | special s =>
      fin_cases s <;>
        simp_all [carrierSupport, labelClass, specialLabelClass,
          QuotientCarrierAudit.ContractX.carrier, Family.H2, Family.H3,
          Family.C1, Family.X, Family.Y, Family.Z, Family.blockSet,
          Family.x0, Family.one, Family.two, Family.three, Family.four]
  | block b i =>
      fin_cases b <;>
        simp_all [carrierSupport, labelClass, blockLabelClass,
          QuotientCarrierAudit.ContractX.carrier, Family.H2, Family.H3,
          Family.C1, Family.X, Family.Y, Family.Z, Family.blockSet,
          Family.x0, Family.one, Family.two, Family.three, Family.four]

theorem label_of_mem_carrierSupport
    {n : ℕ} {e : Element n}
    (C : QuotientCarrierAudit.ContractX.Carrier)
    (he : e ∈ carrierSupport n C) :
    labelClass n e = .X ∨
      labelClass n e ∈ QuotientCarrierAudit.ContractX.carrier C := by
  cases C <;> cases e with
  | special s =>
      fin_cases s <;>
        simp_all [carrierSupport, labelClass, specialLabelClass,
          QuotientCarrierAudit.ContractX.carrier, Family.H2, Family.H3,
          Family.C1, Family.X, Family.Y, Family.Z, Family.blockSet,
          Family.x0, Family.one, Family.two, Family.three, Family.four]
  | block b i =>
      fin_cases b <;>
        simp_all [carrierSupport, labelClass, blockLabelClass,
          QuotientCarrierAudit.ContractX.carrier, Family.H2, Family.H3,
          Family.C1, Family.X, Family.Y, Family.Z, Family.blockSet,
          Family.x0, Family.one, Family.two, Family.three, Family.four]

theorem ncard_C1_diff_x0 (n : ℕ) :
    (Family.C1 n \ {Family.x0 n}).ncard = n + 2 := by
  rw [Set.ncard_diff_singleton_of_mem (by
    exact Set.mem_union_right _ (Family.x0_mem_X n)), Family.ncard_C1]
  omega

theorem C1_diff_x0_zero :
    Family.C1 0 \ {Family.x0 0} =
      ({Family.one 0, Family.four 0} : Set (Element 0)) := by
  ext e
  cases e with
  | special s =>
      fin_cases s <;>
        simp [Family.C1, Family.X, Family.blockSet, Family.one, Family.four,
          Family.x0]
  | block b i =>
      have hi : i = 0 := Fin.eq_zero i
      subst i
      fin_cases b <;>
        simp [Family.C1, Family.X, Family.blockSet, Family.one, Family.four,
          Family.x0]

/-- Template special attached to an actual special element.  The default on
blocks is irrelevant in pure-special selectors. -/
def specialValue (n : ℕ) : Element n → Templates.ContractX.Special
  | .special s => TemplateInstances.ContractX.specialKind s
  | .block _ _ => .One

def actualSpecial (n : ℕ) : Templates.ContractX.Special → Element n
  | .One => Family.one n
  | .Two => Family.two n
  | .Three => Family.three n
  | .Four => Family.four n

@[simp] theorem specialValue_actualSpecial (n : ℕ)
    (s : Templates.ContractX.Special) :
    specialValue n (actualSpecial n s) = s := by
  cases s <;> rfl

@[simp] theorem blockClass_actualSpecial (n : ℕ)
    (s : Templates.ContractX.Special) :
    TemplateInstances.ContractX.blockClass n (actualSpecial n s) = none := by
  cases s <;> rfl

theorem actualSpecial_ne_x0 (n : ℕ) (s : Templates.ContractX.Special) :
    actualSpecial n s ≠ Family.x0 n := by
  cases s <;> simp [actualSpecial, Family.one, Family.two, Family.three,
    Family.four, Family.x0]

theorem specialClass_eq_some_specialValue_of_blockClass_eq_none
    {n : ℕ} {e : Element n}
    (he : e ≠ Family.x0 n)
    (hBlock : TemplateInstances.ContractX.blockClass n e = none) :
    TemplateInstances.ContractX.specialClass n e = some (specialValue n e) := by
  cases e with
  | special s => rfl
  | block b i =>
      fin_cases b
      · have hi : i = 0 := by
          simpa [TemplateInstances.ContractX.blockClass,
            TemplateInstances.ContractX.removedElement, Family.x0] using hBlock
        subst i
        exact (he rfl).elim
      · simp [TemplateInstances.ContractX.blockClass,
          TemplateInstances.ContractX.removedElement,
          TemplateInstances.ContractX.blockKind, Family.x0] at hBlock
      · simp [TemplateInstances.ContractX.blockClass,
          TemplateInstances.ContractX.removedElement,
          TemplateInstances.ContractX.blockKind, Family.x0] at hBlock

theorem specialValue_injective_of_blockClass_eq_none
    {n : ℕ} {e f : Element n}
    (he : e ≠ Family.x0 n) (hf : f ≠ Family.x0 n)
    (heBlock : TemplateInstances.ContractX.blockClass n e = none)
    (hfBlock : TemplateInstances.ContractX.blockClass n f = none)
    (hValue : specialValue n e = specialValue n f) : e = f := by
  cases e with
  | special se =>
      cases f with
      | special sf =>
          fin_cases se <;> fin_cases sf <;> simp_all [specialValue,
            TemplateInstances.ContractX.specialKind]
      | block bf i =>
          have hs := specialClass_eq_some_specialValue_of_blockClass_eq_none
            hf hfBlock
          simp at hs
  | block be i =>
      have hs := specialClass_eq_some_specialValue_of_blockClass_eq_none
        he heBlock
      simp at hs

theorem eq_actualSpecial_specialValue_of_blockClass_eq_none
    {n : ℕ} {e : Element n}
    (he : e ≠ Family.x0 n)
    (hBlock : TemplateInstances.ContractX.blockClass n e = none) :
    e = actualSpecial n (specialValue n e) := by
  apply specialValue_injective_of_blockClass_eq_none he
    (actualSpecial_ne_x0 n _) hBlock (blockClass_actualSpecial n _)
  simp

/-- At `n = 0`, every special subset of size at most two is independent
unless it contains the coincident pair `{1,4}`. -/
theorem linearIndependent_special_zero_of_ncard_le_two
    {S : Set Templates.ContractX.Special}
    (hCard : S.ncard ≤ 2)
    (hOneFour : ¬ ({.One, .Four} : Set Templates.ContractX.Special) ⊆ S) :
    LinearIndependent ℚ
      (fun s : S ↦ Templates.ContractX.special 0 s) := by
  have restrict_pair
      (a b : Templates.ContractX.Special)
      (hab : a ≠ b)
      (hS : S ⊆ Set.range ![a, b])
      (hPair : LinearIndependent ℚ
        ![Templates.ContractX.special 0 a,
          Templates.ContractX.special 0 b]) :
      LinearIndependent ℚ
        (fun s : S ↦ Templates.ContractX.special 0 s) := by
    have hComp :
        (Templates.ContractX.special 0 ∘ ![a, b]) =
          ![Templates.ContractX.special 0 a,
            Templates.ContractX.special 0 b] := by
      funext i
      fin_cases i <;> rfl
    have hOn : LinearIndepOn ℚ (Templates.ContractX.special 0)
        (Set.range ![a, b]) :=
      (linearIndepOn_range_iff (by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all) _).2 (by
          rw [hComp]
          exact hPair)
    exact hOn.mono hS
  have hMissingOneOrFour : .One ∉ S ∨ .Four ∉ S := by
    simpa only [Set.pair_subset_iff, not_and_or] using hOneFour
  rcases hMissingOneOrFour with hOne | hFour
  · have hMissing : .Two ∉ S ∨ .Three ∉ S ∨ .Four ∉ S := by
      by_contra h
      push Not at h
      rcases h with ⟨hTwo, hThree, hFour⟩
      have hThree : ({.Two, .Three, .Four} : Set Templates.ContractX.Special) ⊆ S := by
        intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl | rfl <;> assumption
      have := Set.ncard_le_ncard hThree (Set.toFinite _)
      simp at this
      omega
    rcases hMissing with hTwo | hThree | hFour
    · apply restrict_pair .Three .Four (by decide)
      · intro s hs
        cases s <;> simp_all
      · exact SpecialGeometry.ContractX.linearIndependent_three_four 0
    · apply restrict_pair .Two .Four (by decide)
      · intro s hs
        cases s <;> simp_all
      · exact SpecialGeometry.ContractX.linearIndependent_two_four 0
    · apply restrict_pair .Two .Three (by decide)
      · intro s hs
        cases s <;> simp_all
      · exact SpecialGeometry.ContractX.linearIndependent_two_three 0
  · have hMissing : .One ∉ S ∨ .Two ∉ S ∨ .Three ∉ S := by
      by_contra h
      push Not at h
      rcases h with ⟨hOne, hTwo, hThree⟩
      have hThree : ({.One, .Two, .Three} : Set Templates.ContractX.Special) ⊆ S := by
        intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl | rfl <;> assumption
      have := Set.ncard_le_ncard hThree (Set.toFinite _)
      simp at this
      omega
    rcases hMissing with hOne | hTwo | hThree
    · apply restrict_pair .Two .Three (by decide)
      · intro s hs
        cases s <;> simp_all
      · exact SpecialGeometry.ContractX.linearIndependent_two_three 0
    · apply restrict_pair .One .Three (by decide)
      · intro s hs
        cases s <;> simp_all
      · exact SpecialGeometry.ContractX.linearIndependent_one_three 0
    · apply restrict_pair .One .Two (by decide)
      · intro s hs
        cases s <;> simp_all
      · exact SpecialGeometry.ContractX.linearIndependent_one_two 0

/-- Pure-special selectors of a contraction basis satisfy the Rado
inequality.  For positive core dimension the only special dependence is the
core triple.  At `n = 0`, the basis size drops to two and the additional
coincident pair `{1,4}` is excluded by the `C₁ \ x₀` basis condition. -/
theorem card_le_finrank_subspaceSum_of_forall_blockClass_none
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hB : ((Family.MI n) ／ {Family.x0 n}).IsBase B)
    (J : Finset B)
    (hPure : ∀ i ∈ J,
      TemplateInstances.ContractX.blockClass n (i : Element n) = none) :
    J.card ≤ Module.finrank ℚ
      (subspaceSum ℚ
        (fun b : B ↦ TemplateInstances.ContractX.ambientSubspace n b) J) := by
  rcases (Family.contract_x0_isBase_iff n B).mp hB with
    ⟨hGround, hBcard, hNotT, hNotC1, -, -⟩
  have hx0B : Family.x0 n ∉ B := by
    intro hx
    have hg := hGround hx
    simp [Matroid.contract_ground, Family.MI_ground, Family.ground] at hg
  let S : Set Templates.ContractX.Special :=
    Set.range (fun j : J ↦ specialValue n (j.1 : Element n))
  have special_mem_B (s : Templates.ContractX.Special) (hs : s ∈ S) :
      actualSpecial n s ∈ B := by
    obtain ⟨j, rfl⟩ := hs
    have hpure := hPure j.1 j.2
    rw [← eq_actualSpecial_specialValue_of_blockClass_eq_none
      (fun he ↦ hx0B (he ▸ j.1.property)) hpure]
    exact j.1.property
  have hSpecialT :
      ¬ ({.One, .Two, .Three} : Set Templates.ContractX.Special) ⊆ S := by
    intro hT
    apply hNotT
    intro e he
    simp only [Family.T, Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl
    · exact special_mem_B .One (hT (by simp))
    · exact special_mem_B .Two (hT (by simp))
    · exact special_mem_B .Three (hT (by simp))
  have hRawInjective : Function.Injective
      (fun j : J ↦ specialValue n (j.1 : Element n)) := by
    intro i j hij
    apply Subtype.ext
    apply Subtype.ext
    exact specialValue_injective_of_blockClass_eq_none
      (fun he ↦ hx0B (he ▸ i.1.property))
      (fun he ↦ hx0B (he ▸ j.1.property))
      (hPure i.1 i.2) (hPure j.1 j.2) hij
  have hSncard : S.ncard = J.card := by
    dsimp [S]
    rw [Set.ncard_range_of_injective hRawInjective]
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_coe J
  have hSpecialLinear : LinearIndependent ℚ
      (fun s : S ↦ Templates.ContractX.special n s) := by
    by_cases hn : n = 0
    · subst n
      apply linearIndependent_special_zero_of_ncard_le_two
      · rw [hSncard]
        have hJle := card_selector_le_of_ncard hBcard J
        omega
      · intro hOneFour
        have hPairSubset :
            ({Family.one 0, Family.four 0} : Set (Element 0)) ⊆ B := by
          intro e he
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
          rcases he with rfl | rfl
          · exact special_mem_B .One (hOneFour (by simp))
          · exact special_mem_B .Four (hOneFour (by simp))
        have hPairEqB :
            ({Family.one 0, Family.four 0} : Set (Element 0)) = B := by
          apply Set.eq_of_subset_of_ncard_le hPairSubset
          rw [hBcard]
          simp [Family.one, Family.four]
        apply hNotC1
        rw [← hPairEqB, C1_diff_x0_zero]
    · exact
        SpecialGeometry.ContractX.linearIndependent_special_of_not_core_triple_subset
          (Nat.pos_of_ne_zero hn) hSpecialT
  let f : J → S := fun j ↦
    ⟨specialValue n (j.1 : Element n), Set.mem_range_self j⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact hRawInjective (congrArg Subtype.val hij)
  have hActualLinear : LinearIndependent ℚ
      (fun j : J ↦ Templates.ContractX.special n
        (specialValue n (j.1 : Element n))) := by
    simpa [f, Function.comp_def] using hSpecialLinear.comp f hf
  let W := subspaceSum ℚ
    (fun b : B ↦ TemplateInstances.ContractX.ambientSubspace n b) J
  let v : J → W := fun j ↦
    ⟨Templates.ContractX.special n (specialValue n (j.1 : Element n)), by
      apply (Finset.le_sup
        (f := fun b : B ↦ TemplateInstances.ContractX.ambientSubspace n b)
        j.2)
      have hpure := hPure j.1 j.2
      have hspecial := specialClass_eq_some_specialValue_of_blockClass_eq_none
        (fun he ↦ hx0B (he ▸ j.1.property)) hpure
      simp [TemplateInstances.ContractX.ambientSubspace,
        TemplateInstances.ambientSubspaceOf, hpure, hspecial]⟩
  have hv : LinearIndependent ℚ v := by
    apply LinearIndependent.of_comp W.subtype
    simpa [v, Function.comp_def] using hActualLinear
  simpa [W] using hv.fintype_card_le_finrank

/-- Every mixed selector of an actual `M / x₀` basis satisfies its Rado
inequality.  The zero-labelled `X` block is handled separately from the three
nonzero rank-one carriers. -/
theorem card_le_finrank_subspaceSum_of_exists_block
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hB : ((Family.MI n) ／ {Family.x0 n}).IsBase B)
    (J : Finset B)
    (hBlock : ∃ i ∈ J, ∃ b,
      TemplateInstances.ContractX.blockClass n (i : Element n) = some b) :
    J.card ≤ Module.finrank ℚ
      (subspaceSum ℚ
        (fun b : B ↦ TemplateInstances.ContractX.ambientSubspace n b) J) := by
  rcases (Family.contract_x0_isBase_iff n B).mp hB with
    ⟨hGround, hBcard, -, hNotC1, hNotH2, hNotH3⟩
  have hx0B : Family.x0 n ∉ B := by
    intro hx
    have hg := hGround hx
    simp [Matroid.contract_ground, Family.MI_ground, Family.ground] at hg
  let R : Submodule ℚ (Templates.QuotientSpace Templates.ContractX.quotientDim) :=
    Submodule.span ℚ
      ((quotientLabel n ∘ fun b : B ↦ (b : Element n)) '' (J : Set B))
  have hdim : Module.finrank ℚ
      (subspaceSum ℚ
        (fun b : B ↦ TemplateInstances.ContractX.ambientSubspace n b) J) =
      n + Module.finrank ℚ R := by
    simpa [TemplateInstances.ContractX.ambientSubspace, quotientLabel, R] using
      (ClassifiedGeometry.finrank_subspaceSum_ambientSubspaceOf
        Templates.ContractX.blockLabel (Templates.ContractX.special n)
        (TemplateInstances.ContractX.blockClass n)
        (TemplateInstances.ContractX.specialClass n)
        (fun b : B ↦ (b : Element n)) hBlock)
  rw [hdim]
  by_contra hCapacity
  have hlt : n + Module.finrank ℚ R < J.card := Nat.lt_of_not_ge hCapacity
  have hJle : J.card ≤ n + 2 := card_selector_le_of_ncard hBcard J
  have hRankLe : Module.finrank ℚ R ≤ 1 := by omega
  by_cases hRankZero : Module.finrank ℚ R = 0
  · have hRbot : R = ⊥ := Submodule.finrank_eq_zero.mp hRankZero
    have hActualSubset : actualSet J ⊆ Family.X n \ {Family.x0 n} := by
      rintro e ⟨b, hbJ, rfl⟩
      have hqMem : quotientLabel n (b : Element n) ∈ R :=
        Submodule.subset_span ⟨b, hbJ, rfl⟩
      have hqZero : quotientLabel n (b : Element n) = 0 := by
        rw [hRbot] at hqMem
        simpa using hqMem
      have hLabelX : labelClass n (b : Element n) = .X :=
        (QuotientCarrierAudit.ContractX.label_eq_zero_iff _).mp <| by
          rw [← quotientLabel_eq_label]
          exact hqZero
      refine ⟨(labelClass_eq_X_iff n b).mp hLabelX, ?_⟩
      simp only [Set.mem_singleton_iff]
      intro hb0
      exact hx0B (hb0 ▸ b.property)
    have hCardLe : J.card ≤ n := by
      rw [← ncard_actualSet J]
      have h := Set.ncard_le_ncard hActualSubset (Set.toFinite _)
      rw [Set.ncard_diff_singleton_of_mem (Family.x0_mem_X n),
        Family.ncard_X] at h
      omega
    omega
  · have hRankOne : Module.finrank ℚ R = 1 := by omega
    have hJcard : J.card = n + 2 := by omega
    have hJuniv : J = Finset.univ :=
      selector_eq_univ_of_card_eq hBcard hJcard
    let S : Finset Label := selectedLabels J
    have hSpan : R = Submodule.span ℚ
        (QuotientCarrierAudit.ContractX.label '' (S : Set Label)) := by
      dsimp [R, S]
      rw [quotient_image_eq]
    have hEraseRank : Module.finrank ℚ
        (Submodule.span ℚ
          (QuotientCarrierAudit.ContractX.label ''
            (S.erase .X : Set Label))) ≤ 1 := by
      rw [← span_selectedLabels_erase_X S, ← hSpan, hRankOne]
    obtain ⟨C, hSC⟩ :=
      QuotientCarrierAudit.ContractX.contained_in_carrier_of_finrank_le_one
        (S.erase .X) (by simp) hEraseRank
    have hBSupport : B ⊆ carrierSupport n C := by
      intro e heB
      let b : B := ⟨e, heB⟩
      have hbJ : b ∈ J := by simp [hJuniv]
      have hLabelS : labelClass n e ∈ S := by
        exact label_mem_selectedLabels hbJ
      have hLabelCarrier : labelClass n e = .X ∨
          labelClass n e ∈ QuotientCarrierAudit.ContractX.carrier C := by
        by_cases hX : labelClass n e = .X
        · exact Or.inl hX
        · exact Or.inr (hSC (Finset.mem_erase.mpr ⟨hX, hLabelS⟩))
      exact mem_carrierSupport_of_label
        (fun he ↦ hx0B (he ▸ heB)) C hLabelCarrier
    cases C with
    | b => exact hNotH3 (by simpa [carrierSupport] using hBSupport)
    | c => exact hNotH2 (by simpa [carrierSupport] using hBSupport)
    | bPlusC =>
        apply hNotC1
        apply Set.eq_of_subset_of_ncard_le
          (by simpa [carrierSupport] using hBSupport)
        rw [ncard_C1_diff_x0, hBcard]

/-- Complete Rado audit for every basis of `MIₙ / x₀`. -/
theorem hasRadoCapacity_ambient_of_isBase
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hB : ((Family.MI n) ／ {Family.x0 n}).IsBase B) :
    HasRadoCapacity ℚ
      (fun b : B ↦ TemplateInstances.ContractX.ambientSubspace n b) := by
  classical
  intro J
  by_cases hBlock : ∃ i ∈ J, ∃ b,
      TemplateInstances.ContractX.blockClass n (i : Element n) = some b
  · exact card_le_finrank_subspaceSum_of_exists_block hB J hBlock
  · apply card_le_finrank_subspaceSum_of_forall_blockClass_none hB J
    intro i hi
    cases hClass : TemplateInstances.ContractX.blockClass n
        (i : Element n) with
    | none => rfl
    | some b => exact (hBlock ⟨i, hi, b, hClass⟩).elim

/-- Coordinate-space form consumed by the generic representation compiler. -/
theorem hasRadoCapacity_L_of_isBase
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hB : ((Family.MI n) ／ {Family.x0 n}).IsBase B) :
    HasRadoCapacity ℚ (fun b : B ↦ TemplateInstances.ContractX.L n b) :=
  (TemplateInstances.ContractX.hasRadoCapacity_L_iff_ambient B).mpr
    (hasRadoCapacity_ambient_of_isBase hB)

/-! ### Forced dependence of full-size nonbases -/

theorem q_one_eq_q_two_add_q_three (n : ℕ) :
    TemplateInstances.ContractX.q n (Family.one n) =
      TemplateInstances.ContractX.q n (Family.two n) +
        TemplateInstances.ContractX.q n (Family.three n) := by
  simpa [TemplateInstances.ContractX.q,
    TemplateInstances.coordinateFixedVectorOf,
    TemplateInstances.ContractX.ambientFixedVector,
    TemplateInstances.ambientFixedVectorOf,
    TemplateInstances.ContractX.specialClass,
    TemplateInstances.ContractX.specialKind] using
      congrArg (TemplateInstances.ambientCoordinateEquiv n
        Templates.ContractX.quotientDim)
        (Templates.ContractX.special_relation n)

theorem q_four_eq_q_one_zero :
    TemplateInstances.ContractX.q 0 (Family.four 0) =
      TemplateInstances.ContractX.q 0 (Family.one 0) := by
  change TemplateInstances.ambientCoordinateEquiv 0
      Templates.ContractX.quotientDim (Templates.ContractX.special 0 .Four) =
    TemplateInstances.ambientCoordinateEquiv 0
      Templates.ContractX.quotientDim (Templates.ContractX.special 0 .One)
  exact congrArg (TemplateInstances.ambientCoordinateEquiv 0
    Templates.ContractX.quotientDim)
    Templates.ContractX.special_four_eq_one_of_n_eq_zero

theorem not_linearIndependent_fin3_of_eq_add
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (v : Fin 3 → V) (h : v 0 = v 1 + v 2) :
    ¬ LinearIndependent ℚ v := by
  intro hLinear
  rw [Fintype.linearIndependent_iff] at hLinear
  let g : Fin 3 → ℚ := ![1, -1, -1]
  have hsum : ∑ i, g i • v i = 0 := by
    simp [g, Fin.sum_univ_succ, h]
    abel
  have hg := hLinear g hsum 0
  norm_num [g] at hg

theorem not_linearIndependent_fin2_of_eq
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (v : Fin 2 → V) (h : v 0 = v 1) :
    ¬ LinearIndependent ℚ v := by
  intro hLinear
  rw [Fintype.linearIndependent_iff] at hLinear
  let g : Fin 2 → ℚ := ![1, -1]
  have hsum : ∑ i, g i • v i = 0 := by
    simp [g, Fin.sum_univ_succ, h]
  have hg := hLinear g hsum 0
  norm_num [g] at hg

theorem not_linearIndependent_of_T_subset
    {n : ℕ} {B : Set (Element n)}
    (hT : Family.T n ⊆ B)
    (w : Element n → (Fin (n + Templates.ContractX.quotientDim) → ℚ))
    (hwq : ∀ e ∈ TemplateInstances.ContractX.fixedElements n,
      w e = TemplateInstances.ContractX.q n e) :
    ¬ LinearIndependent ℚ (fun b : B ↦ w b) := by
  have hOneB : Family.one n ∈ B := hT (by simp [Family.T])
  have hTwoB : Family.two n ∈ B := hT (by simp [Family.T])
  have hThreeB : Family.three n ∈ B := hT (by simp [Family.T])
  have hwOne := hwq (Family.one n) (by
    simp [TemplateInstances.ContractX.fixedElements,
      TemplateInstances.fixedElementsOf,
      TemplateInstances.ContractX.specialClass,
      Family.one])
  have hwTwo := hwq (Family.two n) (by
    simp [TemplateInstances.ContractX.fixedElements,
      TemplateInstances.fixedElementsOf,
      TemplateInstances.ContractX.specialClass,
      Family.two])
  have hwThree := hwq (Family.three n) (by
    simp [TemplateInstances.ContractX.fixedElements,
      TemplateInstances.fixedElementsOf,
      TemplateInstances.ContractX.specialClass,
      Family.three])
  let t : Fin 3 → B :=
    ![⟨Family.one n, hOneB⟩, ⟨Family.two n, hTwoB⟩,
      ⟨Family.three n, hThreeB⟩]
  have ht : Function.Injective t := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [t, Family.one, Family.two, Family.three]
  intro hLinear
  have hTriple := hLinear.comp t ht
  have hwRelation :
      w (Family.one n) = w (Family.two n) + w (Family.three n) := by
    rw [hwOne, hwTwo, hwThree]
    exact q_one_eq_q_two_add_q_three n
  apply not_linearIndependent_fin3_of_eq_add (fun i ↦ w (t i))
  · simpa [t] using hwRelation
  · exact hTriple

theorem not_linearIndependent_of_eq_C1_diff_x0_zero
    {B : Set (Element 0)}
    (hEq : B = Family.C1 0 \ {Family.x0 0})
    (w : Element 0 →
      (Fin (0 + Templates.ContractX.quotientDim) → ℚ))
    (hwq : ∀ e ∈ TemplateInstances.ContractX.fixedElements 0,
      w e = TemplateInstances.ContractX.q 0 e) :
    ¬ LinearIndependent ℚ (fun b : B ↦ w b) := by
  have hOneB : Family.one 0 ∈ B := by
    rw [hEq, C1_diff_x0_zero]
    simp
  have hFourB : Family.four 0 ∈ B := by
    rw [hEq, C1_diff_x0_zero]
    simp
  have hwOne := hwq (Family.one 0) (by
    simp [TemplateInstances.ContractX.fixedElements,
      TemplateInstances.fixedElementsOf,
      TemplateInstances.ContractX.specialClass,
      Family.one])
  have hwFour := hwq (Family.four 0) (by
    simp [TemplateInstances.ContractX.fixedElements,
      TemplateInstances.fixedElementsOf,
      TemplateInstances.ContractX.specialClass,
      Family.four])
  let t : Fin 2 → B :=
    ![⟨Family.one 0, hOneB⟩, ⟨Family.four 0, hFourB⟩]
  have ht : Function.Injective t := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [t, Family.one, Family.four]
  intro hLinear
  have hPair := hLinear.comp t ht
  have hwRelation : w (Family.one 0) = w (Family.four 0) := by
    rw [hwOne, hwFour]
    exact q_four_eq_q_one_zero.symm
  apply not_linearIndependent_fin2_of_eq (fun i ↦ w (t i))
  · simpa [t] using hwRelation
  · exact hPair

/-- A full-size set lying in one of the three rank-one quotient carriers
cannot satisfy the ambient Rado inequalities, provided it contains a
surviving large-block element. -/
theorem not_hasRadoCapacity_ambient_of_subset_carrierSupport
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hBcard : B.ncard = n + 2)
    (C : QuotientCarrierAudit.ContractX.Carrier)
    (hSupport : B ⊆ carrierSupport n C)
    (hBlock : ∃ i : B, ∃ b,
      TemplateInstances.ContractX.blockClass n (i : Element n) = some b) :
    ¬ HasRadoCapacity ℚ
      (fun b : B ↦ TemplateInstances.ContractX.ambientSubspace n b) := by
  let J : Finset B := Finset.univ
  obtain ⟨i, b, hib⟩ := hBlock
  have hBlockJ : ∃ i ∈ J, ∃ b,
      TemplateInstances.ContractX.blockClass n (i : Element n) = some b :=
    ⟨i, Finset.mem_univ i, b, hib⟩
  let R : Submodule ℚ
      (Templates.QuotientSpace Templates.ContractX.quotientDim) :=
    Submodule.span ℚ
      ((quotientLabel n ∘ fun b : B ↦ (b : Element n)) '' (J : Set B))
  let S : Finset Label := selectedLabels J
  have hSpan : R = Submodule.span ℚ
      (QuotientCarrierAudit.ContractX.label '' (S : Set Label)) := by
    dsimp [R, S]
    rw [quotient_image_eq]
  have hEraseSubset : S.erase .X ⊆
      QuotientCarrierAudit.ContractX.carrier C := by
    intro l hl
    have hlS : l ∈ S := Finset.mem_of_mem_erase hl
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hlS
    have hLabel := label_of_mem_carrierSupport C (hSupport j.property)
    exact hLabel.resolve_left (Finset.ne_of_mem_erase hl)
  have hRank : Module.finrank ℚ R ≤ 1 := by
    rw [hSpan, span_selectedLabels_erase_X]
    exact
      (QuotientCarrierAudit.ContractX.finrank_le_one_iff_contained_in_carrier
        (S.erase .X) (by simp)).2 ⟨C, hEraseSubset⟩
  have hdim : Module.finrank ℚ
      (subspaceSum ℚ
        (fun b : B ↦ TemplateInstances.ContractX.ambientSubspace n b) J) =
      n + Module.finrank ℚ R := by
    simpa [TemplateInstances.ContractX.ambientSubspace, quotientLabel, R] using
      (ClassifiedGeometry.finrank_subspaceSum_ambientSubspaceOf
        Templates.ContractX.blockLabel (Templates.ContractX.special n)
        (TemplateInstances.ContractX.blockClass n)
        (TemplateInstances.ContractX.specialClass n)
        (fun b : B ↦ (b : Element n)) hBlockJ)
  apply not_hasRadoCapacity_of_finrank_lt_card J
  rw [hdim]
  have hJcard : J.card = n + 2 := by
    simp [J, ← Nat.card_eq_fintype_card, hBcard]
  omega

theorem exists_blockClass_of_subset_H2_diff_x0
    {n : ℕ} {B : Set (Element n)}
    (hBcard : B.ncard = n + 2)
    (hSubset : B ⊆ Family.H2 n \ {Family.x0 n}) :
    ∃ i : B, ∃ b,
      TemplateInstances.ContractX.blockClass n (i : Element n) = some b := by
  by_contra hBlock
  have hClassNone (i : B) :
      TemplateInstances.ContractX.blockClass n (i : Element n) = none := by
    cases hClass : TemplateInstances.ContractX.blockClass n
        (i : Element n) with
    | none => rfl
    | some b => exact (hBlock ⟨i, b, hClass⟩).elim
  have hSingleton : B ⊆ ({Family.two n} : Set (Element n)) := by
    intro e he
    have hs := hSubset he
    have hc := hClassNone ⟨e, he⟩
    cases e with
    | special s =>
        fin_cases s <;>
          simp_all [Family.H2, Family.X, Family.Z, Family.blockSet,
            Family.two, Family.x0]
    | block b i =>
        fin_cases b <;>
          simp_all [TemplateInstances.ContractX.blockClass,
            TemplateInstances.ContractX.removedElement,
            TemplateInstances.ContractX.blockKind, Family.H2, Family.X,
            Family.Z, Family.blockSet, Family.two, Family.x0]
  have hCardLe := Set.ncard_le_ncard hSingleton (Set.toFinite _)
  rw [hBcard] at hCardLe
  simp [Family.two] at hCardLe

theorem exists_blockClass_of_subset_H3_diff_x0
    {n : ℕ} {B : Set (Element n)}
    (hBcard : B.ncard = n + 2)
    (hSubset : B ⊆ Family.H3 n \ {Family.x0 n}) :
    ∃ i : B, ∃ b,
      TemplateInstances.ContractX.blockClass n (i : Element n) = some b := by
  by_contra hBlock
  have hClassNone (i : B) :
      TemplateInstances.ContractX.blockClass n (i : Element n) = none := by
    cases hClass : TemplateInstances.ContractX.blockClass n
        (i : Element n) with
    | none => rfl
    | some b => exact (hBlock ⟨i, b, hClass⟩).elim
  have hSingleton : B ⊆ ({Family.three n} : Set (Element n)) := by
    intro e he
    have hs := hSubset he
    have hc := hClassNone ⟨e, he⟩
    cases e with
    | special s =>
        fin_cases s <;>
          simp_all [Family.H3, Family.X, Family.Y, Family.blockSet,
            Family.three, Family.x0]
    | block b i =>
        fin_cases b <;>
          simp_all [TemplateInstances.ContractX.blockClass,
            TemplateInstances.ContractX.removedElement,
            TemplateInstances.ContractX.blockKind, Family.H3, Family.X,
            Family.Y, Family.blockSet, Family.three, Family.x0]
  have hCardLe := Set.ncard_le_ncard hSingleton (Set.toFinite _)
  rw [hBcard] at hCardLe
  simp [Family.three] at hCardLe

theorem exists_blockClass_of_eq_C1_diff_x0_of_pos
    {n : ℕ} (hn : 0 < n) {B : Set (Element n)}
    (hEq : B = Family.C1 n \ {Family.x0 n}) :
    ∃ i : B, ∃ b,
      TemplateInstances.ContractX.blockClass n (i : Element n) = some b := by
  let k : Fin (n + 1) := ⟨1, by omega⟩
  let e : Element n := .block 0 k
  have heX : e ∈ Family.X n := ⟨k, rfl⟩
  have hkne : k ≠ 0 := by
    intro hk
    have := congrArg Fin.val hk
    simp [k] at this
  have hene : e ≠ Family.x0 n := by
    simp [e, Family.x0, hkne]
  have heB : e ∈ B := by
    rw [hEq]
    exact ⟨Set.mem_union_right _ heX, by simpa using hene⟩
  refine ⟨⟨e, heB⟩, .X, ?_⟩
  simp [TemplateInstances.ContractX.blockClass,
    TemplateInstances.ContractX.removedElement,
    TemplateInstances.ContractX.blockKind, e, Family.x0, hkne]

theorem not_linearIndependent_of_subset_H2_diff_x0
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hBcard : B.ncard = n + 2)
    (hSubset : B ⊆ Family.H2 n \ {Family.x0 n})
    (w : Element n → (Fin (n + Templates.ContractX.quotientDim) → ℚ))
    (hwL : ∀ e, w e ∈ TemplateInstances.ContractX.L n e) :
    ¬ LinearIndependent ℚ (fun b : B ↦ w b) := by
  have hBlock := exists_blockClass_of_subset_H2_diff_x0 hBcard hSubset
  have hNotAmbient := not_hasRadoCapacity_ambient_of_subset_carrierSupport
    hBcard .c (by simpa [carrierSupport] using hSubset) hBlock
  apply not_linearIndependent_of_not_hasRadoCapacity _ (fun b : B ↦ hwL b)
  intro hCapacityL
  exact hNotAmbient
    ((TemplateInstances.ContractX.hasRadoCapacity_L_iff_ambient B).mp
      hCapacityL)

theorem not_linearIndependent_of_subset_H3_diff_x0
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hBcard : B.ncard = n + 2)
    (hSubset : B ⊆ Family.H3 n \ {Family.x0 n})
    (w : Element n → (Fin (n + Templates.ContractX.quotientDim) → ℚ))
    (hwL : ∀ e, w e ∈ TemplateInstances.ContractX.L n e) :
    ¬ LinearIndependent ℚ (fun b : B ↦ w b) := by
  have hBlock := exists_blockClass_of_subset_H3_diff_x0 hBcard hSubset
  have hNotAmbient := not_hasRadoCapacity_ambient_of_subset_carrierSupport
    hBcard .b (by simpa [carrierSupport] using hSubset) hBlock
  apply not_linearIndependent_of_not_hasRadoCapacity _ (fun b : B ↦ hwL b)
  intro hCapacityL
  exact hNotAmbient
    ((TemplateInstances.ContractX.hasRadoCapacity_L_iff_ambient B).mp
      hCapacityL)

theorem not_linearIndependent_of_eq_C1_diff_x0_of_pos
    {n : ℕ} (hn : 0 < n) {B : Set (Element n)} [Fintype B]
    (hBcard : B.ncard = n + 2)
    (hEq : B = Family.C1 n \ {Family.x0 n})
    (w : Element n → (Fin (n + Templates.ContractX.quotientDim) → ℚ))
    (hwL : ∀ e, w e ∈ TemplateInstances.ContractX.L n e) :
    ¬ LinearIndependent ℚ (fun b : B ↦ w b) := by
  have hBlock := exists_blockClass_of_eq_C1_diff_x0_of_pos hn hEq
  have hNotAmbient := not_hasRadoCapacity_ambient_of_subset_carrierSupport
    hBcard .bPlusC (by simp [carrierSupport, hEq]) hBlock
  apply not_linearIndependent_of_not_hasRadoCapacity _ (fun b : B ↦ hwL b)
  intro hCapacityL
  exact hNotAmbient
    ((TemplateInstances.ContractX.hasRadoCapacity_L_iff_ambient B).mp
      hCapacityL)

/-- Every full-size ground subset which is not a basis is forced dependent by
the subspace constraints and the prescribed special columns. -/
theorem nonbase_forced
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hGround : B ⊆ ((Family.MI n) ／ {Family.x0 n}).E)
    (hBcard : B.ncard = n + 2)
    (hNotBase : ¬ ((Family.MI n) ／ {Family.x0 n}).IsBase B)
    (w : Element n → (Fin (n + Templates.ContractX.quotientDim) → ℚ))
    (hwL : ∀ e, w e ∈ TemplateInstances.ContractX.L n e)
    (hwq : ∀ e ∈ TemplateInstances.ContractX.fixedElements n,
      w e = TemplateInstances.ContractX.q n e) :
    ¬ LinearIndependent ℚ (fun b : B ↦ w b) := by
  by_cases hT : Family.T n ⊆ B
  · exact not_linearIndependent_of_T_subset hT w hwq
  by_cases hC1 : B = Family.C1 n \ {Family.x0 n}
  · by_cases hn : n = 0
    · subst n
      exact not_linearIndependent_of_eq_C1_diff_x0_zero hC1 w hwq
    · exact not_linearIndependent_of_eq_C1_diff_x0_of_pos
        (Nat.pos_of_ne_zero hn) hBcard hC1 w hwL
  by_cases hH2 : B ⊆ Family.H2 n \ {Family.x0 n}
  · exact not_linearIndependent_of_subset_H2_diff_x0 hBcard hH2 w hwL
  by_cases hH3 : B ⊆ Family.H3 n \ {Family.x0 n}
  · exact not_linearIndependent_of_subset_H3_diff_x0 hBcard hH3 w hwL
  exact (hNotBase ((Family.contract_x0_isBase_iff n B).2
    ⟨hGround, hBcard, hT, hC1, hH2, hH3⟩)).elim

/-! ### End-to-end representation -/

/-- The complete local audit compiled into one rational vector
representation, retaining the subspace and fixed-column certificates. -/
theorem exists_representation (n : ℕ) :
    ∃ v : Element n → (Fin (n + 2) → ℚ),
      Represents ℚ ((Family.MI n) ／ {Family.x0 n}) v ∧
        (∀ e, v e ∈ TemplateInstances.ContractX.L n e) ∧
          (∀ e ∈ TemplateInstances.ContractX.fixedElements n,
            v e = TemplateInstances.ContractX.q n e) := by
  apply exists_representation_of_subspace_base_audit
    (M := (Family.MI n) ／ {Family.x0 n})
    (d := n + 2)
    (TemplateInstances.ContractX.L n)
    (TemplateInstances.ContractX.fixedElements n)
    (TemplateInstances.ContractX.q n)
  · intro e he
    exact TemplateInstances.ContractX.q_mem_L he
  · obtain ⟨B₀, hB₀⟩ :=
      ((Family.MI n) ／ {Family.x0 n}).exists_isBase
    exact ⟨B₀, hB₀,
      ((Family.contract_x0_isBase_iff n B₀).mp hB₀).2.1⟩
  · intro B hB _
    letI : Fintype B := B.toFinite.fintype
    exact TemplateInstances.ContractX.feasible_assignment_on_candidate B
      (hasRadoCapacity_L_of_isBase hB)
  · intro B hGround hBcard hNotBase w hwL hwq
    letI : Fintype B := B.toFinite.fintype
    exact nonbase_forced hGround hBcard hNotBase w hwL hwq

/-- Public endpoint: contraction by the distinguished `X`-block element is
rationally representable for every parameter, including `n = 0`. -/
theorem rationallyRepresentable_contract_x0 (n : ℕ) :
    RationallyRepresentable ((Family.MI n) ／ {Family.x0 n}) := by
  obtain ⟨v, hv, -, -⟩ := exists_representation n
  exact ⟨n + 2, v, hv⟩

end ContractX

/-! ## Contraction of `1` -/

namespace ContractOne

abbrev Label := QuotientCarrierAudit.ContractOne.Label

def blockLabelClass : Fin 3 → Label := ![.X, .Y, .Z]
def specialLabelClass : Fin 4 → Option Label :=
  ![none, some .Two, some .Three, some .Four]

def labelClass (n : ℕ) : Element n → Label
  | .special s => (specialLabelClass s).getD .Two
  | .block b _ => blockLabelClass b

def quotientLabel (n : ℕ) :
    Element n → Templates.QuotientSpace Templates.ContractOne.quotientDim :=
  ClassifiedGeometry.quotientLabelOf
    Templates.ContractOne.blockLabel (Templates.ContractOne.special n)
    (TemplateInstances.ContractOne.blockClass n)
    (TemplateInstances.ContractOne.specialClass n)

theorem quotientLabel_eq_label
    (n : ℕ) {e : Element n} (he : e ≠ Family.one n) :
    quotientLabel n e = QuotientCarrierAudit.ContractOne.label (labelClass n e) := by
  cases e with
  | special s =>
      fin_cases s
      · exact (he rfl).elim
      · rfl
      · rfl
      · rfl
  | block b i => fin_cases b <;> rfl

def selectedLabels {n : ℕ} {B : Set (Element n)} (J : Finset B) :
    Finset Label := J.image (fun b : B ↦ labelClass n (b : Element n))

theorem label_mem_selectedLabels {n : ℕ} {B : Set (Element n)}
    {J : Finset B} {b : B} (hb : b ∈ J) :
    labelClass n (b : Element n) ∈ selectedLabels J :=
  Finset.mem_image.mpr ⟨b, hb, rfl⟩

theorem quotient_image_eq {n : ℕ} {B : Set (Element n)}
    (hOneB : Family.one n ∉ B) (J : Finset B) :
    (quotientLabel n ∘ fun b : B ↦ (b : Element n)) '' (J : Set B) =
      QuotientCarrierAudit.ContractOne.label ''
        (selectedLabels J : Set Label) := by
  ext p
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [Function.comp_apply, quotientLabel_eq_label n
      (fun he ↦ hOneB (he ▸ b.property))]
    exact ⟨labelClass n b, label_mem_selectedLabels hb, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hl
    exact ⟨b, hb, quotientLabel_eq_label n
      (fun he ↦ hOneB (he ▸ b.property))⟩

def carrierSupport (n : ℕ) :
    QuotientCarrierAudit.ContractOne.Carrier → Set (Element n)
  | .h => Family.H1 n \ {Family.one n}
  | .k => Family.C1 n \ {Family.one n}
  | .ell => {Family.two n, Family.three n}

theorem mem_carrierSupport_of_label
    {n : ℕ} {e : Element n} (he : e ≠ Family.one n)
    (C : QuotientCarrierAudit.ContractOne.Carrier)
    (hLabel : labelClass n e ∈ QuotientCarrierAudit.ContractOne.carrier C) :
    e ∈ carrierSupport n C := by
  cases C <;> cases e with
  | special s =>
      fin_cases s <;>
        simp_all [carrierSupport, labelClass, specialLabelClass,
          QuotientCarrierAudit.ContractOne.carrier, Family.C1,
          Family.X, Family.blockSet, Family.one,
          Family.two, Family.three, Family.four]
  | block b i =>
      fin_cases b <;>
        simp_all [carrierSupport, labelClass, blockLabelClass,
          QuotientCarrierAudit.ContractOne.carrier, Family.H1, Family.C1,
          Family.X, Family.Y, Family.Z, Family.blockSet, Family.one,
          Family.four]

theorem label_of_mem_carrierSupport
    {n : ℕ} {e : Element n}
    (C : QuotientCarrierAudit.ContractOne.Carrier)
    (he : e ∈ carrierSupport n C) :
    labelClass n e ∈ QuotientCarrierAudit.ContractOne.carrier C := by
  cases C <;> cases e with
  | special s =>
      fin_cases s <;>
        simp_all [carrierSupport, labelClass, specialLabelClass,
          QuotientCarrierAudit.ContractOne.carrier, Family.H1, Family.C1,
          Family.X, Family.Y, Family.Z, Family.blockSet, Family.one,
          Family.two, Family.three, Family.four]
  | block b i =>
      fin_cases b <;>
        simp_all [carrierSupport, labelClass, blockLabelClass,
          QuotientCarrierAudit.ContractOne.carrier, Family.H1, Family.C1,
          Family.X, Family.Y, Family.Z, Family.blockSet, Family.one,
          Family.two, Family.three, Family.four]

theorem ncard_C1_diff_one (n : ℕ) :
    (Family.C1 n \ {Family.one n}).ncard = n + 2 := by
  rw [Set.ncard_diff_singleton_of_mem (by simp [Family.C1]), Family.ncard_C1]
  omega

def specialValue (n : ℕ) : Element n → Templates.ContractOne.Special
  | .special 1 => .Two
  | .special 2 => .Three
  | .special 3 => .Four
  | _ => .Two

def actualSpecial (n : ℕ) : Templates.ContractOne.Special → Element n
  | .Two => Family.two n
  | .Three => Family.three n
  | .Four => Family.four n

@[simp] theorem specialValue_actualSpecial (n : ℕ)
    (s : Templates.ContractOne.Special) :
    specialValue n (actualSpecial n s) = s := by cases s <;> rfl

@[simp] theorem blockClass_actualSpecial (n : ℕ)
    (s : Templates.ContractOne.Special) :
    TemplateInstances.ContractOne.blockClass n (actualSpecial n s) = none := by
  cases s <;> rfl

theorem actualSpecial_ne_one (n : ℕ) (s : Templates.ContractOne.Special) :
    actualSpecial n s ≠ Family.one n := by
  cases s <;> simp [actualSpecial, Family.one, Family.two, Family.three,
    Family.four]

theorem specialClass_eq_some_specialValue_of_blockClass_eq_none
    {n : ℕ} {e : Element n} (he : e ≠ Family.one n)
    (hBlock : TemplateInstances.ContractOne.blockClass n e = none) :
    TemplateInstances.ContractOne.specialClass n e = some (specialValue n e) := by
  cases e with
  | special s =>
      fin_cases s
      · exact (he rfl).elim
      · rfl
      · rfl
      · rfl
  | block b i => simp at hBlock

theorem specialValue_injective_of_blockClass_eq_none
    {n : ℕ} {e f : Element n}
    (he : e ≠ Family.one n) (hf : f ≠ Family.one n)
    (heBlock : TemplateInstances.ContractOne.blockClass n e = none)
    (hfBlock : TemplateInstances.ContractOne.blockClass n f = none)
    (hValue : specialValue n e = specialValue n f) : e = f := by
  cases e with
  | special se =>
      cases f with
      | special sf =>
          fin_cases se <;> fin_cases sf <;>
            simp_all [specialValue, Family.one]
      | block bf i => simp at hfBlock
  | block be i => simp at heBlock

theorem eq_actualSpecial_specialValue_of_blockClass_eq_none
    {n : ℕ} {e : Element n} (he : e ≠ Family.one n)
    (hBlock : TemplateInstances.ContractOne.blockClass n e = none) :
    e = actualSpecial n (specialValue n e) := by
  apply specialValue_injective_of_blockClass_eq_none he
    (actualSpecial_ne_one n _) hBlock (blockClass_actualSpecial n _)
  simp

theorem card_le_finrank_subspaceSum_of_forall_blockClass_none
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hB : ((Family.MI n) ／ {Family.one n}).IsBase B)
    (J : Finset B)
    (hPure : ∀ i ∈ J,
      TemplateInstances.ContractOne.blockClass n (i : Element n) = none) :
    J.card ≤ Module.finrank ℚ
      (subspaceSum ℚ
        (fun b : B ↦ TemplateInstances.ContractOne.ambientSubspace n b) J) := by
  rcases (Family.contract_one_isBase_iff n B).mp hB with
    ⟨hGround, -, hNotPair, -, -⟩
  have hOneB : Family.one n ∉ B := by
    intro hOne
    have hg := hGround hOne
    simp [Matroid.contract_ground, Family.MI_ground, Family.ground] at hg
  let S : Set Templates.ContractOne.Special :=
    Set.range (fun j : J ↦ specialValue n (j.1 : Element n))
  have special_mem_B (s : Templates.ContractOne.Special) (hs : s ∈ S) :
      actualSpecial n s ∈ B := by
    obtain ⟨j, rfl⟩ := hs
    have hpure := hPure j.1 j.2
    rw [← eq_actualSpecial_specialValue_of_blockClass_eq_none
      (fun he ↦ hOneB (he ▸ j.1.property)) hpure]
    exact j.1.property
  have hSpecialPair :
      ¬ ({.Two, .Three} : Set Templates.ContractOne.Special) ⊆ S := by
    intro hPair
    apply hNotPair
    intro e he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl
    · exact special_mem_B .Two (hPair (by simp))
    · exact special_mem_B .Three (hPair (by simp))
  have hSpecialLinear : LinearIndependent ℚ
      (fun s : S ↦ Templates.ContractOne.special n s) :=
    SpecialGeometry.ContractOne.linearIndependent_special_of_not_pair_subset
      n hSpecialPair
  let f : J → S := fun j ↦
    ⟨specialValue n (j.1 : Element n), Set.mem_range_self j⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply Subtype.ext
    exact specialValue_injective_of_blockClass_eq_none
      (fun he ↦ hOneB (he ▸ i.1.property))
      (fun he ↦ hOneB (he ▸ j.1.property))
      (hPure i.1 i.2) (hPure j.1 j.2) (congrArg Subtype.val hij)
  have hActualLinear : LinearIndependent ℚ
      (fun j : J ↦ Templates.ContractOne.special n
        (specialValue n (j.1 : Element n))) := by
    simpa [f, Function.comp_def] using hSpecialLinear.comp f hf
  let W := subspaceSum ℚ
    (fun b : B ↦ TemplateInstances.ContractOne.ambientSubspace n b) J
  let v : J → W := fun j ↦
    ⟨Templates.ContractOne.special n (specialValue n (j.1 : Element n)), by
      apply (Finset.le_sup
        (f := fun b : B ↦ TemplateInstances.ContractOne.ambientSubspace n b)
        j.2)
      have hpure := hPure j.1 j.2
      have hspecial := specialClass_eq_some_specialValue_of_blockClass_eq_none
        (fun he ↦ hOneB (he ▸ j.1.property)) hpure
      simp [TemplateInstances.ContractOne.ambientSubspace,
        TemplateInstances.ambientSubspaceOf, hpure, hspecial]⟩
  have hv : LinearIndependent ℚ v := by
    apply LinearIndependent.of_comp W.subtype
    simpa [v, Function.comp_def] using hActualLinear
  simpa [W] using hv.fintype_card_le_finrank

theorem card_le_finrank_subspaceSum_of_exists_block
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hB : ((Family.MI n) ／ {Family.one n}).IsBase B)
    (J : Finset B)
    (hBlock : ∃ i ∈ J, ∃ b,
      TemplateInstances.ContractOne.blockClass n (i : Element n) = some b) :
    J.card ≤ Module.finrank ℚ
      (subspaceSum ℚ
        (fun b : B ↦ TemplateInstances.ContractOne.ambientSubspace n b) J) := by
  rcases (Family.contract_one_isBase_iff n B).mp hB with
    ⟨hGround, hBcard, hNotPair, hNotC1, hNotH1⟩
  have hOneB : Family.one n ∉ B := by
    intro hOne
    have hg := hGround hOne
    simp [Matroid.contract_ground, Family.MI_ground, Family.ground] at hg
  let R : Submodule ℚ
      (Templates.QuotientSpace Templates.ContractOne.quotientDim) :=
    Submodule.span ℚ
      ((quotientLabel n ∘ fun b : B ↦ (b : Element n)) '' (J : Set B))
  have hdim : Module.finrank ℚ
      (subspaceSum ℚ
        (fun b : B ↦ TemplateInstances.ContractOne.ambientSubspace n b) J) =
      n + Module.finrank ℚ R := by
    simpa [TemplateInstances.ContractOne.ambientSubspace, quotientLabel, R] using
      (ClassifiedGeometry.finrank_subspaceSum_ambientSubspaceOf
        Templates.ContractOne.blockLabel (Templates.ContractOne.special n)
        (TemplateInstances.ContractOne.blockClass n)
        (TemplateInstances.ContractOne.specialClass n)
        (fun b : B ↦ (b : Element n)) hBlock)
  rw [hdim]
  by_contra hCapacity
  have hlt : n + Module.finrank ℚ R < J.card := Nat.lt_of_not_ge hCapacity
  have hJle : J.card ≤ n + 2 := card_selector_le_of_ncard hBcard J
  have hRankLe : Module.finrank ℚ R ≤ 1 := by omega
  let S : Finset Label := selectedLabels J
  have hSpan : R = Submodule.span ℚ
      (QuotientCarrierAudit.ContractOne.label '' (S : Set Label)) := by
    dsimp [R, S]
    rw [quotient_image_eq hOneB]
  by_cases hRankZero : Module.finrank ℚ R = 0
  · have hRbot : R = ⊥ := Submodule.finrank_eq_zero.mp hRankZero
    obtain ⟨i, hi, -, -⟩ := hBlock
    have hqMem : quotientLabel n (i : Element n) ∈ R :=
      Submodule.subset_span ⟨i, hi, rfl⟩
    have hqZero : quotientLabel n (i : Element n) = 0 := by
      rw [hRbot] at hqMem
      simpa using hqMem
    have hLabelZero : QuotientCarrierAudit.ContractOne.label
        (labelClass n (i : Element n)) = 0 := by
      rw [← quotientLabel_eq_label n
        (fun he ↦ hOneB (he ▸ i.property))]
      exact hqZero
    exact QuotientCarrierAudit.ContractOne.label_ne_zero _ hLabelZero
  · have hRankOne : Module.finrank ℚ R = 1 := by omega
    have hJcard : J.card = n + 2 := by omega
    have hJuniv : J = Finset.univ :=
      selector_eq_univ_of_card_eq hBcard hJcard
    obtain ⟨C, hSC⟩ :=
      QuotientCarrierAudit.ContractOne.contained_in_carrier_of_finrank_le_one S
        (by rw [← hSpan, hRankOne])
    have hBSupport : B ⊆ carrierSupport n C := by
      intro e heB
      let b : B := ⟨e, heB⟩
      have hbJ : b ∈ J := by simp [hJuniv]
      exact mem_carrierSupport_of_label
        (fun he ↦ hOneB (he ▸ heB)) C
        (hSC (label_mem_selectedLabels hbJ))
    cases C with
    | h => exact hNotH1 (by simpa [carrierSupport] using hBSupport)
    | k =>
        apply hNotC1
        apply Set.eq_of_subset_of_ncard_le
          (by simpa [carrierSupport] using hBSupport)
        rw [ncard_C1_diff_one, hBcard]
    | ell =>
        apply hNotPair
        have hEq : B = ({Family.two n, Family.three n} : Set (Element n)) := by
          apply Set.eq_of_subset_of_ncard_le
            (by simpa [carrierSupport] using hBSupport)
          rw [hBcard]
          simp [Family.two, Family.three]
        rw [hEq]

theorem hasRadoCapacity_ambient_of_isBase
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hB : ((Family.MI n) ／ {Family.one n}).IsBase B) :
    HasRadoCapacity ℚ
      (fun b : B ↦ TemplateInstances.ContractOne.ambientSubspace n b) := by
  classical
  intro J
  by_cases hBlock : ∃ i ∈ J, ∃ b,
      TemplateInstances.ContractOne.blockClass n (i : Element n) = some b
  · exact card_le_finrank_subspaceSum_of_exists_block hB J hBlock
  · apply card_le_finrank_subspaceSum_of_forall_blockClass_none hB J
    intro i hi
    cases hClass : TemplateInstances.ContractOne.blockClass n
        (i : Element n) with
    | none => rfl
    | some b => exact (hBlock ⟨i, hi, b, hClass⟩).elim

theorem hasRadoCapacity_L_of_isBase
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hB : ((Family.MI n) ／ {Family.one n}).IsBase B) :
    HasRadoCapacity ℚ (fun b : B ↦ TemplateInstances.ContractOne.L n b) :=
  (TemplateInstances.ContractOne.hasRadoCapacity_L_iff_ambient B).mpr
    (hasRadoCapacity_ambient_of_isBase hB)

/-! ### Forced dependence of full-size nonbases -/

theorem q_two_eq_q_three (n : ℕ) :
    TemplateInstances.ContractOne.q n (Family.two n) =
      TemplateInstances.ContractOne.q n (Family.three n) := by
  simpa [TemplateInstances.ContractOne.q,
    TemplateInstances.coordinateFixedVectorOf,
    TemplateInstances.ContractOne.ambientFixedVector,
    TemplateInstances.ambientFixedVectorOf,
    TemplateInstances.ContractOne.specialClass,
    TemplateInstances.ContractOne.specialKind] using
      congrArg (TemplateInstances.ambientCoordinateEquiv n
        Templates.ContractOne.quotientDim)
        (Templates.ContractOne.special_relation n)

theorem not_linearIndependent_of_pair_subset
    {n : ℕ} {B : Set (Element n)}
    (hPair : ({Family.two n, Family.three n} : Set (Element n)) ⊆ B)
    (w : Element n → (Fin (n + Templates.ContractOne.quotientDim) → ℚ))
    (hwq : ∀ e ∈ TemplateInstances.ContractOne.fixedElements n,
      w e = TemplateInstances.ContractOne.q n e) :
    ¬ LinearIndependent ℚ (fun b : B ↦ w b) := by
  have hTwoB : Family.two n ∈ B := hPair (by simp)
  have hThreeB : Family.three n ∈ B := hPair (by simp)
  have hwTwo := hwq (Family.two n) (by
    simp [TemplateInstances.ContractOne.fixedElements,
      TemplateInstances.fixedElementsOf,
      TemplateInstances.ContractOne.specialClass,
      TemplateInstances.ContractOne.specialKind, Family.two])
  have hwThree := hwq (Family.three n) (by
    simp [TemplateInstances.ContractOne.fixedElements,
      TemplateInstances.fixedElementsOf,
      TemplateInstances.ContractOne.specialClass,
      TemplateInstances.ContractOne.specialKind, Family.three])
  let t : Fin 2 → B :=
    ![⟨Family.two n, hTwoB⟩, ⟨Family.three n, hThreeB⟩]
  have ht : Function.Injective t := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [t, Family.two, Family.three]
  intro hLinear
  have hPairLinear := hLinear.comp t ht
  have hwRelation : w (Family.two n) = w (Family.three n) := by
    rw [hwTwo, hwThree]
    exact q_two_eq_q_three n
  apply ContractX.not_linearIndependent_fin2_of_eq (fun i ↦ w (t i))
  · simpa [t] using hwRelation
  · exact hPairLinear

theorem not_hasRadoCapacity_ambient_of_subset_carrierSupport
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hBcard : B.ncard = n + 2)
    (C : QuotientCarrierAudit.ContractOne.Carrier)
    (hSupport : B ⊆ carrierSupport n C)
    (hBlock : ∃ i : B, ∃ b,
      TemplateInstances.ContractOne.blockClass n (i : Element n) = some b) :
    ¬ HasRadoCapacity ℚ
      (fun b : B ↦ TemplateInstances.ContractOne.ambientSubspace n b) := by
  let J : Finset B := Finset.univ
  obtain ⟨i, b, hib⟩ := hBlock
  have hBlockJ : ∃ i ∈ J, ∃ b,
      TemplateInstances.ContractOne.blockClass n (i : Element n) = some b :=
    ⟨i, Finset.mem_univ i, b, hib⟩
  let R : Submodule ℚ
      (Templates.QuotientSpace Templates.ContractOne.quotientDim) :=
    Submodule.span ℚ
      ((quotientLabel n ∘ fun b : B ↦ (b : Element n)) '' (J : Set B))
  let S : Finset Label := selectedLabels J
  have hOneB : Family.one n ∉ B := by
    intro hOne
    have hs := hSupport hOne
    cases C <;>
      simp [carrierSupport, Family.H1, Family.C1, Family.X, Family.Y,
        Family.Z, Family.blockSet, Family.one, Family.two, Family.three] at hs
  have hSpan : R = Submodule.span ℚ
      (QuotientCarrierAudit.ContractOne.label '' (S : Set Label)) := by
    dsimp [R, S]
    rw [quotient_image_eq hOneB]
  have hLabelSubset : S ⊆ QuotientCarrierAudit.ContractOne.carrier C := by
    intro l hl
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hl
    exact label_of_mem_carrierSupport C (hSupport j.property)
  have hRank : Module.finrank ℚ R ≤ 1 := by
    rw [hSpan]
    exact
      (QuotientCarrierAudit.ContractOne.finrank_le_one_iff_contained_in_carrier
        S).2 ⟨C, hLabelSubset⟩
  have hdim : Module.finrank ℚ
      (subspaceSum ℚ
        (fun b : B ↦ TemplateInstances.ContractOne.ambientSubspace n b) J) =
      n + Module.finrank ℚ R := by
    simpa [TemplateInstances.ContractOne.ambientSubspace, quotientLabel, R] using
      (ClassifiedGeometry.finrank_subspaceSum_ambientSubspaceOf
        Templates.ContractOne.blockLabel (Templates.ContractOne.special n)
        (TemplateInstances.ContractOne.blockClass n)
        (TemplateInstances.ContractOne.specialClass n)
        (fun b : B ↦ (b : Element n)) hBlockJ)
  apply not_hasRadoCapacity_of_finrank_lt_card J
  rw [hdim]
  have hJcard : J.card = n + 2 := by
    simp [J, ← Nat.card_eq_fintype_card, hBcard]
  omega

theorem exists_blockClass_of_eq_C1_diff_one
    {n : ℕ} {B : Set (Element n)}
    (hEq : B = Family.C1 n \ {Family.one n}) :
    ∃ i : B, ∃ b,
      TemplateInstances.ContractOne.blockClass n (i : Element n) = some b := by
  have hxB : Family.x0 n ∈ B := by
    rw [hEq]
    exact ⟨Set.mem_union_right _ (Family.x0_mem_X n), by
      simp [Family.x0, Family.one]⟩
  exact ⟨⟨Family.x0 n, hxB⟩, .X, by
    simp [TemplateInstances.ContractOne.blockClass,
      TemplateInstances.ContractOne.blockKind, Family.x0]⟩

theorem exists_blockClass_of_subset_H1_diff_one
    {n : ℕ} {B : Set (Element n)}
    (hBcard : B.ncard = n + 2)
    (hSubset : B ⊆ Family.H1 n \ {Family.one n}) :
    ∃ i : B, ∃ b,
      TemplateInstances.ContractOne.blockClass n (i : Element n) = some b := by
  by_contra hBlock
  have hEmpty : B = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro e he
    have hs := hSubset he
    cases hClass : TemplateInstances.ContractOne.blockClass n e with
    | some b => exact hBlock ⟨⟨e, he⟩, b, hClass⟩
    | none =>
        cases e with
        | special s =>
            fin_cases s <;>
              simp_all [Family.H1, Family.Y, Family.Z, Family.blockSet,
                Family.one]
        | block b i => simp at hClass
  rw [hEmpty] at hBcard
  simp at hBcard

theorem not_linearIndependent_of_eq_C1_diff_one
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hBcard : B.ncard = n + 2)
    (hEq : B = Family.C1 n \ {Family.one n})
    (w : Element n → (Fin (n + Templates.ContractOne.quotientDim) → ℚ))
    (hwL : ∀ e, w e ∈ TemplateInstances.ContractOne.L n e) :
    ¬ LinearIndependent ℚ (fun b : B ↦ w b) := by
  have hNotAmbient := not_hasRadoCapacity_ambient_of_subset_carrierSupport
    hBcard .k (by simp [carrierSupport, hEq])
      (exists_blockClass_of_eq_C1_diff_one hEq)
  apply not_linearIndependent_of_not_hasRadoCapacity _ (fun b : B ↦ hwL b)
  intro hCapacityL
  exact hNotAmbient
    ((TemplateInstances.ContractOne.hasRadoCapacity_L_iff_ambient B).mp
      hCapacityL)

theorem not_linearIndependent_of_subset_H1_diff_one
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hBcard : B.ncard = n + 2)
    (hSubset : B ⊆ Family.H1 n \ {Family.one n})
    (w : Element n → (Fin (n + Templates.ContractOne.quotientDim) → ℚ))
    (hwL : ∀ e, w e ∈ TemplateInstances.ContractOne.L n e) :
    ¬ LinearIndependent ℚ (fun b : B ↦ w b) := by
  have hNotAmbient := not_hasRadoCapacity_ambient_of_subset_carrierSupport
    hBcard .h (by simpa [carrierSupport] using hSubset)
      (exists_blockClass_of_subset_H1_diff_one hBcard hSubset)
  apply not_linearIndependent_of_not_hasRadoCapacity _ (fun b : B ↦ hwL b)
  intro hCapacityL
  exact hNotAmbient
    ((TemplateInstances.ContractOne.hasRadoCapacity_L_iff_ambient B).mp
      hCapacityL)

theorem nonbase_forced
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hGround : B ⊆ ((Family.MI n) ／ {Family.one n}).E)
    (hBcard : B.ncard = n + 2)
    (hNotBase : ¬ ((Family.MI n) ／ {Family.one n}).IsBase B)
    (w : Element n → (Fin (n + Templates.ContractOne.quotientDim) → ℚ))
    (hwL : ∀ e, w e ∈ TemplateInstances.ContractOne.L n e)
    (hwq : ∀ e ∈ TemplateInstances.ContractOne.fixedElements n,
      w e = TemplateInstances.ContractOne.q n e) :
    ¬ LinearIndependent ℚ (fun b : B ↦ w b) := by
  by_cases hPair : ({Family.two n, Family.three n} : Set (Element n)) ⊆ B
  · exact not_linearIndependent_of_pair_subset hPair w hwq
  by_cases hC1 : B = Family.C1 n \ {Family.one n}
  · exact not_linearIndependent_of_eq_C1_diff_one hBcard hC1 w hwL
  by_cases hH1 : B ⊆ Family.H1 n \ {Family.one n}
  · exact not_linearIndependent_of_subset_H1_diff_one hBcard hH1 w hwL
  exact (hNotBase ((Family.contract_one_isBase_iff n B).2
    ⟨hGround, hBcard, hPair, hC1, hH1⟩)).elim

theorem exists_representation (n : ℕ) :
    ∃ v : Element n → (Fin (n + 2) → ℚ),
      Represents ℚ ((Family.MI n) ／ {Family.one n}) v ∧
        (∀ e, v e ∈ TemplateInstances.ContractOne.L n e) ∧
          (∀ e ∈ TemplateInstances.ContractOne.fixedElements n,
            v e = TemplateInstances.ContractOne.q n e) := by
  apply exists_representation_of_subspace_base_audit
    (M := (Family.MI n) ／ {Family.one n})
    (d := n + 2)
    (TemplateInstances.ContractOne.L n)
    (TemplateInstances.ContractOne.fixedElements n)
    (TemplateInstances.ContractOne.q n)
  · intro e he
    exact TemplateInstances.ContractOne.q_mem_L he
  · obtain ⟨B₀, hB₀⟩ :=
      ((Family.MI n) ／ {Family.one n}).exists_isBase
    exact ⟨B₀, hB₀,
      ((Family.contract_one_isBase_iff n B₀).mp hB₀).2.1⟩
  · intro B hB _
    letI : Fintype B := B.toFinite.fintype
    exact TemplateInstances.ContractOne.feasible_assignment_on_candidate B
      (hasRadoCapacity_L_of_isBase hB)
  · intro B hGround hBcard hNotBase w hwL hwq
    letI : Fintype B := B.toFinite.fintype
    exact nonbase_forced hGround hBcard hNotBase w hwL hwq

theorem rationallyRepresentable_contract_one (n : ℕ) :
    RationallyRepresentable ((Family.MI n) ／ {Family.one n}) := by
  obtain ⟨v, hv, -, -⟩ := exists_representation n
  exact ⟨n + 2, v, hv⟩

end ContractOne

end BlandJensenFormal.BlandJensenMI.ContractionCapacity
