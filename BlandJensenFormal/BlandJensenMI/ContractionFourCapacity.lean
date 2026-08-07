import BlandJensenFormal.BlandJensenMI.ContractionCapacity

/-!
# Rational representation of `MIₙ / 4`

This file gives the complete Rado-capacity and forced-dependence audit for
contraction by the distinguished element `4`.  All arguments are uniform in
`n`; finite computation is confined to the fixed two-dimensional quotient
label configuration.
-/

namespace BlandJensenFormal.BlandJensenMI.ContractionFourCapacity

open Function Set Submodule
open scoped Matroid

namespace ContractFour

abbrev Label := QuotientCarrierAudit.ContractFour.Label

def blockLabelClass : Fin 3 → Label := ![.X, .Y, .Z]
def specialLabelClass : Fin 4 → Label := ![.One, .Two, .Three, .One]

/-- The value on the contracted element is an arbitrary default and is never
used for a ground-set element of the contraction. -/
def labelClass (n : ℕ) : Element n → Label
  | .special s => specialLabelClass s
  | .block b _ => blockLabelClass b

def quotientLabel (n : ℕ) :
    Element n → Templates.QuotientSpace Templates.ContractFour.quotientDim :=
  ClassifiedGeometry.quotientLabelOf
    Templates.ContractFour.blockLabel (Templates.ContractFour.special n)
    (TemplateInstances.ContractFour.blockClass n)
    (TemplateInstances.ContractFour.specialClass n)

theorem quotientLabel_eq_label (n : ℕ) {e : Element n}
    (he : e ≠ Family.four n) :
    quotientLabel n e =
      QuotientCarrierAudit.ContractFour.label (labelClass n e) := by
  cases e with
  | special s =>
      fin_cases s <;> simp_all [quotientLabel,
        ClassifiedGeometry.quotientLabelOf,
        TemplateInstances.ContractFour.blockClass,
        TemplateInstances.ContractFour.specialClass,
        TemplateInstances.ContractFour.specialKind,
        labelClass, specialLabelClass, Family.four,
        Templates.ContractFour.special, Templates.quotientInclusion,
        Templates.ContractFour.quotientLabel,
        QuotientCarrierAudit.ContractFour.label]
  | block b i =>
      fin_cases b <;> simp [quotientLabel,
        ClassifiedGeometry.quotientLabelOf,
        TemplateInstances.ContractFour.blockClass,
        TemplateInstances.ContractFour.blockKind,
        labelClass, blockLabelClass,
        Templates.ContractFour.blockLabel,
        Templates.ContractFour.quotientLabel,
        QuotientCarrierAudit.ContractFour.label]

def selectedLabels {n : ℕ} {B : Set (Element n)} (J : Finset B) :
    Finset Label := J.image (fun b : B ↦ labelClass n (b : Element n))

theorem label_mem_selectedLabels {n : ℕ} {B : Set (Element n)}
    {J : Finset B} {b : B} (hb : b ∈ J) :
    labelClass n (b : Element n) ∈ selectedLabels J :=
  Finset.mem_image.mpr ⟨b, hb, rfl⟩

theorem quotient_image_eq {n : ℕ} {B : Set (Element n)}
    (hfour : Family.four n ∉ B) (J : Finset B) :
    (quotientLabel n ∘ fun b : B ↦ (b : Element n)) '' (J : Set B) =
      QuotientCarrierAudit.ContractFour.label ''
        (selectedLabels J : Set Label) := by
  ext p
  constructor
  · rintro ⟨b, hb, rfl⟩
    change quotientLabel n (b : Element n) ∈ _
    rw [quotientLabel_eq_label n (fun h ↦ hfour (h ▸ b.property))]
    exact ⟨labelClass n b, label_mem_selectedLabels hb, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hl
    exact ⟨b, hb, quotientLabel_eq_label n
      (fun h ↦ hfour (h ▸ b.property))⟩

def carrierPreimage (n : ℕ)
    (C : QuotientCarrierAudit.ContractFour.Carrier) : Set (Element n) :=
  {e | e ≠ Family.four n ∧
    labelClass n e ∈ QuotientCarrierAudit.ContractFour.carrier C}

theorem carrierPreimage_a (n : ℕ) :
    carrierPreimage n .a = Family.C1 n \ {Family.four n} := by
  ext e
  cases e with
  | special s => fin_cases s <;> simp [carrierPreimage, labelClass,
      specialLabelClass, QuotientCarrierAudit.ContractFour.carrier,
      Family.C1, Family.X, Family.blockSet]
  | block b i => fin_cases b <;> simp [carrierPreimage, labelClass,
      blockLabelClass, QuotientCarrierAudit.ContractFour.carrier,
      Family.C1, Family.X, Family.blockSet]

theorem carrierPreimage_b (n : ℕ) :
    carrierPreimage n .b = Family.C2 n \ {Family.four n} := by
  ext e
  cases e with
  | special s => fin_cases s <;> simp [carrierPreimage, labelClass,
      specialLabelClass, QuotientCarrierAudit.ContractFour.carrier,
      Family.C2, Family.Y, Family.blockSet]
  | block b i => fin_cases b <;> simp [carrierPreimage, labelClass,
      blockLabelClass, QuotientCarrierAudit.ContractFour.carrier,
      Family.C2, Family.Y, Family.blockSet]

theorem carrierPreimage_aPlusB (n : ℕ) :
    carrierPreimage n .aPlusB = Family.C3 n \ {Family.four n} := by
  ext e
  cases e with
  | special s => fin_cases s <;> simp [carrierPreimage, labelClass,
      specialLabelClass, QuotientCarrierAudit.ContractFour.carrier,
      Family.C3, Family.Z, Family.blockSet]
  | block b i => fin_cases b <;> simp [carrierPreimage, labelClass,
      blockLabelClass, QuotientCarrierAudit.ContractFour.carrier,
      Family.C3, Family.Z, Family.blockSet]

theorem ncard_C1_diff_four (n : ℕ) :
    (Family.C1 n \ {Family.four n}).ncard = n + 2 := by
  rw [Set.ncard_diff_singleton_of_mem (by simp [Family.C1]), Family.ncard_C1]
  omega

theorem ncard_C2_diff_four (n : ℕ) :
    (Family.C2 n \ {Family.four n}).ncard = n + 2 := by
  rw [Set.ncard_diff_singleton_of_mem (by simp [Family.C2]), Family.ncard_C2]
  omega

theorem ncard_C3_diff_four (n : ℕ) :
    (Family.C3 n \ {Family.four n}).ncard = n + 2 := by
  rw [Set.ncard_diff_singleton_of_mem (by simp [Family.C3]), Family.ncard_C3]
  omega

theorem carrierPreimage_ncard (n : ℕ)
    (C : QuotientCarrierAudit.ContractFour.Carrier) :
    (carrierPreimage n C).ncard = n + 2 := by
  cases C with
  | a => rw [carrierPreimage_a, ncard_C1_diff_four]
  | b => rw [carrierPreimage_b, ncard_C2_diff_four]
  | aPlusB => rw [carrierPreimage_aPlusB, ncard_C3_diff_four]

theorem card_selector_le_of_ncard {n d : ℕ} {B : Set (Element n)}
    [Fintype B] (hBcard : B.ncard = d) (J : Finset B) : J.card ≤ d := by
  calc
    J.card ≤ Fintype.card B := Finset.card_le_univ J
    _ = B.ncard := by simp [← Nat.card_eq_fintype_card]
    _ = d := hBcard

theorem selector_eq_univ_of_card_eq {n d : ℕ} {B : Set (Element n)}
    [Fintype B] (hBcard : B.ncard = d) {J : Finset B}
    (hJcard : J.card = d) : J = Finset.univ := by
  apply Finset.eq_univ_of_card
  simpa [← Nat.card_eq_fintype_card, hBcard] using hJcard

theorem base_not_subset_carrierPreimage {n : ℕ} {B : Set (Element n)}
    (hB : ((Family.MI n) ／ {Family.four n}).IsBase B)
    (C : QuotientCarrierAudit.ContractFour.Carrier) :
    ¬ B ⊆ carrierPreimage n C := by
  rcases (Family.contract_four_isBase_iff n B).mp hB with
    ⟨-, hcard, -, hC1, hC2, hC3⟩
  intro hsub
  cases C with
  | a =>
      apply hC1
      exact Set.eq_of_subset_of_ncard_le
        (by simpa only [carrierPreimage_a] using hsub)
        (by rw [ncard_C1_diff_four, hcard]) (Set.toFinite _)
  | b =>
      apply hC2
      exact Set.eq_of_subset_of_ncard_le
        (by simpa only [carrierPreimage_b] using hsub)
        (by rw [ncard_C2_diff_four, hcard]) (Set.toFinite _)
  | aPlusB =>
      apply hC3
      exact Set.eq_of_subset_of_ncard_le
        (by simpa only [carrierPreimage_aPlusB] using hsub)
        (by rw [ncard_C3_diff_four, hcard]) (Set.toFinite _)

/-- Every mixed selector of a basis of `MIₙ / 4` satisfies its Rado
inequality. -/
theorem card_le_finrank_subspaceSum_of_exists_block
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hB : ((Family.MI n) ／ {Family.four n}).IsBase B)
    (J : Finset B)
    (hBlock : ∃ i ∈ J, ∃ b,
      TemplateInstances.ContractFour.blockClass n (i : Element n) = some b) :
    J.card ≤ Module.finrank ℚ
      (subspaceSum ℚ
        (fun b : B ↦ TemplateInstances.ContractFour.ambientSubspace n b) J) := by
  rcases (Family.contract_four_isBase_iff n B).mp hB with
    ⟨hGround, hBcard, -, -, -, -⟩
  have hfourB : Family.four n ∉ B := by
    intro hfour
    have hg := hGround hfour
    simp [Matroid.contract_ground, Family.MI_ground, Family.ground] at hg
  let R : Submodule ℚ
      (Templates.QuotientSpace Templates.ContractFour.quotientDim) :=
    Submodule.span ℚ
      ((quotientLabel n ∘ fun b : B ↦ (b : Element n)) '' (J : Set B))
  have hdim : Module.finrank ℚ
      (subspaceSum ℚ
        (fun b : B ↦ TemplateInstances.ContractFour.ambientSubspace n b) J) =
      n + Module.finrank ℚ R := by
    simpa [TemplateInstances.ContractFour.ambientSubspace, quotientLabel, R] using
      (ClassifiedGeometry.finrank_subspaceSum_ambientSubspaceOf
        Templates.ContractFour.blockLabel (Templates.ContractFour.special n)
        (TemplateInstances.ContractFour.blockClass n)
        (TemplateInstances.ContractFour.specialClass n)
        (fun b : B ↦ (b : Element n)) hBlock)
  rw [hdim]
  by_contra hCapacity
  have hlt : n + Module.finrank ℚ R < J.card :=
    Nat.lt_of_not_ge hCapacity
  have hJle : J.card ≤ n + 2 := card_selector_le_of_ncard hBcard J
  have hRankLe : Module.finrank ℚ R ≤ 1 := by omega
  by_cases hRankZero : Module.finrank ℚ R = 0
  · have hRbot : R = ⊥ := Submodule.finrank_eq_zero.mp hRankZero
    obtain ⟨i, hi, b, hib⟩ := hBlock
    have hqMem : quotientLabel n (i : Element n) ∈ R :=
      Submodule.subset_span ⟨i, hi, rfl⟩
    have hqZero : quotientLabel n (i : Element n) = 0 := by
      rw [hRbot] at hqMem
      simpa using hqMem
    have hLabelZero : QuotientCarrierAudit.ContractFour.label
        (labelClass n (i : Element n)) = 0 := by
      rw [← quotientLabel_eq_label n
        (fun he ↦ hfourB (he ▸ i.property))]
      exact hqZero
    exact QuotientCarrierAudit.ContractFour.label_ne_zero _ hLabelZero
  · have hRankOne : Module.finrank ℚ R = 1 := by omega
    have hJcard : J.card = n + 2 := by omega
    have hJuniv : J = Finset.univ :=
      selector_eq_univ_of_card_eq hBcard hJcard
    let S : Finset Label := selectedLabels J
    have hSpan : R = Submodule.span ℚ
        (QuotientCarrierAudit.ContractFour.label '' (S : Set Label)) := by
      dsimp [R, S]
      rw [quotient_image_eq hfourB]
    obtain ⟨C, hSC⟩ :=
      QuotientCarrierAudit.ContractFour.contained_in_carrier_of_finrank_le_one S
        (by rw [← hSpan, hRankOne])
    have hBcarrier : B ⊆ carrierPreimage n C := by
      intro e heB
      let b : B := ⟨e, heB⟩
      have hbJ : b ∈ J := by simp [hJuniv]
      exact ⟨fun he ↦ hfourB (he ▸ heB),
        hSC (label_mem_selectedLabels hbJ)⟩
    exact base_not_subset_carrierPreimage hB C hBcarrier

/-! ### Pure-special selectors -/

def specialValue (n : ℕ) : Element n → Templates.ContractFour.Special
  | .special s => ![.One, .Two, .Three, .One] s
  | .block _ _ => .One

def actualSpecial (n : ℕ) : Templates.ContractFour.Special → Element n
  | .One => Family.one n
  | .Two => Family.two n
  | .Three => Family.three n

@[simp] theorem specialValue_actualSpecial (n : ℕ)
    (s : Templates.ContractFour.Special) :
    specialValue n (actualSpecial n s) = s := by
  cases s <;> rfl

@[simp] theorem blockClass_actualSpecial (n : ℕ)
    (s : Templates.ContractFour.Special) :
    TemplateInstances.ContractFour.blockClass n (actualSpecial n s) = none := by
  cases s <;> rfl

theorem actualSpecial_ne_four (n : ℕ)
    (s : Templates.ContractFour.Special) :
    actualSpecial n s ≠ Family.four n := by
  cases s <;> simp [actualSpecial, Family.one, Family.two, Family.three,
    Family.four]

theorem specialClass_eq_some_specialValue_of_blockClass_eq_none
    {n : ℕ} {e : Element n}
    (he : e ≠ Family.four n)
    (hBlock : TemplateInstances.ContractFour.blockClass n e = none) :
    TemplateInstances.ContractFour.specialClass n e = some (specialValue n e) := by
  cases e with
  | special s =>
      fin_cases s <;> simp_all [specialValue,
        TemplateInstances.ContractFour.specialClass,
        TemplateInstances.ContractFour.specialKind, Family.four]
  | block b i =>
      simp [TemplateInstances.ContractFour.blockClass] at hBlock

theorem specialValue_injective_of_blockClass_eq_none
    {n : ℕ} {e f : Element n}
    (he : e ≠ Family.four n) (hf : f ≠ Family.four n)
    (heBlock : TemplateInstances.ContractFour.blockClass n e = none)
    (hfBlock : TemplateInstances.ContractFour.blockClass n f = none)
    (hValue : specialValue n e = specialValue n f) : e = f := by
  cases e with
  | special se =>
      cases f with
      | special sf =>
          fin_cases se <;> fin_cases sf <;> simp_all [specialValue,
            Family.four]
      | block bf i =>
          simp [TemplateInstances.ContractFour.blockClass] at hfBlock
  | block be i =>
      simp [TemplateInstances.ContractFour.blockClass] at heBlock

theorem eq_actualSpecial_specialValue_of_blockClass_eq_none
    {n : ℕ} {e : Element n}
    (he : e ≠ Family.four n)
    (hBlock : TemplateInstances.ContractFour.blockClass n e = none) :
    e = actualSpecial n (specialValue n e) := by
  apply specialValue_injective_of_blockClass_eq_none he
    (actualSpecial_ne_four n _) hBlock (blockClass_actualSpecial n _)
  simp

theorem card_le_finrank_subspaceSum_of_forall_blockClass_none
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hB : ((Family.MI n) ／ {Family.four n}).IsBase B)
    (J : Finset B)
    (hPure : ∀ i ∈ J,
      TemplateInstances.ContractFour.blockClass n (i : Element n) = none) :
    J.card ≤ Module.finrank ℚ
      (subspaceSum ℚ
        (fun b : B ↦ TemplateInstances.ContractFour.ambientSubspace n b) J) := by
  rcases (Family.contract_four_isBase_iff n B).mp hB with
    ⟨hGround, -, hNotT, -, -, -⟩
  have hfourB : Family.four n ∉ B := by
    intro hfour
    have hg := hGround hfour
    simp [Matroid.contract_ground, Family.MI_ground, Family.ground] at hg
  let S : Set Templates.ContractFour.Special :=
    Set.range (fun j : J ↦ specialValue n (j.1 : Element n))
  have special_mem_B (s : Templates.ContractFour.Special) (hs : s ∈ S) :
      actualSpecial n s ∈ B := by
    obtain ⟨j, rfl⟩ := hs
    have hpure := hPure j.1 j.2
    rw [← eq_actualSpecial_specialValue_of_blockClass_eq_none
      (fun he ↦ hfourB (he ▸ j.1.property)) hpure]
    exact j.1.property
  have hSpecialT :
      ¬ ({.One, .Two, .Three} : Set Templates.ContractFour.Special) ⊆ S := by
    intro hT
    apply hNotT
    intro e he
    simp only [Family.T, Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl
    · exact special_mem_B .One (hT (by simp))
    · exact special_mem_B .Two (hT (by simp))
    · exact special_mem_B .Three (hT (by simp))
  have hSpecialLinear : LinearIndependent ℚ
      (fun s : S ↦ Templates.ContractFour.special n s) :=
    SpecialGeometry.ContractFour.linearIndependent_special_of_not_core_triple_subset
      n hSpecialT
  let f : J → S := fun j ↦
    ⟨specialValue n (j.1 : Element n), Set.mem_range_self j⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply Subtype.ext
    apply specialValue_injective_of_blockClass_eq_none
      (fun he ↦ hfourB (he ▸ i.1.property))
      (fun he ↦ hfourB (he ▸ j.1.property))
      (hPure i.1 i.2) (hPure j.1 j.2)
    exact congrArg Subtype.val hij
  have hActualLinear : LinearIndependent ℚ
      (fun j : J ↦ Templates.ContractFour.special n
        (specialValue n (j.1 : Element n))) := by
    simpa [f, Function.comp_def] using hSpecialLinear.comp f hf
  let W := subspaceSum ℚ
    (fun b : B ↦ TemplateInstances.ContractFour.ambientSubspace n b) J
  let v : J → W := fun j ↦
    ⟨Templates.ContractFour.special n (specialValue n (j.1 : Element n)), by
      apply (Finset.le_sup
        (f := fun b : B ↦ TemplateInstances.ContractFour.ambientSubspace n b)
        j.2)
      have hpure := hPure j.1 j.2
      have hspecial := specialClass_eq_some_specialValue_of_blockClass_eq_none
        (fun he ↦ hfourB (he ▸ j.1.property)) hpure
      simp [TemplateInstances.ContractFour.ambientSubspace,
        TemplateInstances.ambientSubspaceOf, hpure, hspecial]⟩
  have hv : LinearIndependent ℚ v := by
    apply LinearIndependent.of_comp W.subtype
    simpa [v, Function.comp_def] using hActualLinear
  simpa [W] using hv.fintype_card_le_finrank

theorem hasRadoCapacity_ambient_of_isBase
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hB : ((Family.MI n) ／ {Family.four n}).IsBase B) :
    HasRadoCapacity ℚ
      (fun b : B ↦ TemplateInstances.ContractFour.ambientSubspace n b) := by
  classical
  intro J
  by_cases hBlock : ∃ i ∈ J, ∃ b,
      TemplateInstances.ContractFour.blockClass n (i : Element n) = some b
  · exact card_le_finrank_subspaceSum_of_exists_block hB J hBlock
  · apply card_le_finrank_subspaceSum_of_forall_blockClass_none hB J
    intro i hi
    cases hClass : TemplateInstances.ContractFour.blockClass n
        (i : Element n) with
    | none => rfl
    | some b => exact (hBlock ⟨i, hi, b, hClass⟩).elim

theorem hasRadoCapacity_L_of_isBase
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hB : ((Family.MI n) ／ {Family.four n}).IsBase B) :
    HasRadoCapacity ℚ
      (fun b : B ↦ TemplateInstances.ContractFour.L n b) :=
  (TemplateInstances.ContractFour.hasRadoCapacity_L_iff_ambient B).mpr
    (hasRadoCapacity_ambient_of_isBase hB)

/-! ### Forced dependence of full-size nonbases -/

theorem q_three_eq_q_one_add_q_two (n : ℕ) :
    TemplateInstances.ContractFour.q n (Family.three n) =
      TemplateInstances.ContractFour.q n (Family.one n) +
        TemplateInstances.ContractFour.q n (Family.two n) := by
  simpa [TemplateInstances.ContractFour.q,
    TemplateInstances.coordinateFixedVectorOf,
    TemplateInstances.ContractFour.ambientFixedVector,
    TemplateInstances.ambientFixedVectorOf,
    TemplateInstances.ContractFour.specialClass,
    TemplateInstances.ContractFour.specialKind] using
      congrArg (TemplateInstances.ambientCoordinateEquiv n
        Templates.ContractFour.quotientDim)
        (Templates.ContractFour.special_relation n)

theorem not_linearIndependent_of_T_subset
    {n : ℕ} {B : Set (Element n)}
    (hT : Family.T n ⊆ B)
    {w : Element n → (Fin (n + Templates.ContractFour.quotientDim) → ℚ)}
    (hwq : ∀ e ∈ TemplateInstances.ContractFour.fixedElements n,
      w e = TemplateInstances.ContractFour.q n e) :
    ¬ LinearIndependent ℚ (fun b : B ↦ w b) := by
  intro hLinear
  have hOneB : Family.one n ∈ B := hT (by simp [Family.T])
  have hTwoB : Family.two n ∈ B := hT (by simp [Family.T])
  have hThreeB : Family.three n ∈ B := hT (by simp [Family.T])
  have hOneFixed : Family.one n ∈
      TemplateInstances.ContractFour.fixedElements n := ⟨.One, rfl⟩
  have hTwoFixed : Family.two n ∈
      TemplateInstances.ContractFour.fixedElements n := ⟨.Two, rfl⟩
  have hThreeFixed : Family.three n ∈
      TemplateInstances.ContractFour.fixedElements n := ⟨.Three, rfl⟩
  have hwOne := hwq (Family.one n) hOneFixed
  have hwTwo := hwq (Family.two n) hTwoFixed
  have hwThree := hwq (Family.three n) hThreeFixed
  have hwRelation : w (Family.three n) =
      w (Family.one n) + w (Family.two n) := by
    rw [hwOne, hwTwo, hwThree]
    exact q_three_eq_q_one_add_q_two n
  let t : Fin 3 → B :=
    ![⟨Family.one n, hOneB⟩,
      ⟨Family.two n, hTwoB⟩,
      ⟨Family.three n, hThreeB⟩]
  have ht : Function.Injective t := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [t, Family.one, Family.two, Family.three]
  have hThreeLinear : LinearIndependent ℚ (fun i ↦ w (t i)) :=
    hLinear.comp t ht
  let g : Fin 3 → ℚ := ![1, 1, -1]
  have hsum : ∑ i, g i • w (t i) = 0 := by
    simp [g, t, Fin.sum_univ_succ]
    change w (Family.one n) +
      (w (Family.two n) + -w (Family.three n)) = 0
    rw [hwRelation]
    abel
  have hcoeff := (Fintype.linearIndependent_iff.mp hThreeLinear) g hsum 0
  norm_num [g] at hcoeff

theorem not_hasRadoCapacity_ambient_of_subset_carrier
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hBcard : B.ncard = n + 2)
    (C : QuotientCarrierAudit.ContractFour.Carrier)
    (hBC : B ⊆ carrierPreimage n C)
    (hBlock : ∃ i ∈ (Finset.univ : Finset B), ∃ b,
      TemplateInstances.ContractFour.blockClass n (i : Element n) = some b) :
    ¬ HasRadoCapacity ℚ
      (fun b : B ↦ TemplateInstances.ContractFour.ambientSubspace n b) := by
  have hfourB : Family.four n ∉ B := by
    intro hfour
    exact (hBC hfour).1 rfl
  let S : Finset Label := selectedLabels (Finset.univ : Finset B)
  have hSC : S ⊆ QuotientCarrierAudit.ContractFour.carrier C := by
    intro l hl
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hl
    exact (hBC e.property).2
  have hQrank : Module.finrank ℚ
      (Submodule.span ℚ
        (QuotientCarrierAudit.ContractFour.label '' (S : Set Label))) ≤ 1 :=
    (QuotientCarrierAudit.finrank_span_image_mono
      QuotientCarrierAudit.ContractFour.label hSC).trans
        (QuotientCarrierAudit.ContractFour.carrier_finrank_le_one C)
  have hAmbientDim : Module.finrank ℚ
      (subspaceSum ℚ
        (fun b : B ↦ TemplateInstances.ContractFour.ambientSubspace n b)
        Finset.univ) =
      n + Module.finrank ℚ
        (Submodule.span ℚ
          (QuotientCarrierAudit.ContractFour.label '' (S : Set Label))) := by
    have hdim :=
      ClassifiedGeometry.finrank_subspaceSum_ambientSubspaceOf
        Templates.ContractFour.blockLabel (Templates.ContractFour.special n)
        (TemplateInstances.ContractFour.blockClass n)
        (TemplateInstances.ContractFour.specialClass n)
        (fun b : B ↦ (b : Element n)) hBlock
    have hImage :
        (ClassifiedGeometry.quotientLabelOf
            Templates.ContractFour.blockLabel (Templates.ContractFour.special n)
            (TemplateInstances.ContractFour.blockClass n)
            (TemplateInstances.ContractFour.specialClass n) ∘
          fun b : B ↦ (b : Element n)) ''
            ((Finset.univ : Finset B) : Set B) =
          QuotientCarrierAudit.ContractFour.label '' (S : Set Label) := by
      simpa [quotientLabel, S] using
        quotient_image_eq hfourB (Finset.univ : Finset B)
    rw [hImage] at hdim
    simpa [TemplateInstances.ContractFour.ambientSubspace] using hdim
  intro hCapacity
  have hcap := hCapacity (Finset.univ : Finset B)
  rw [hAmbientDim] at hcap
  have hcard : (Finset.univ : Finset B).card = n + 2 := by
    simp [← Nat.card_eq_fintype_card, hBcard]
  omega

theorem not_linearIndependent_of_subset_carrier
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hBcard : B.ncard = n + 2)
    (C : QuotientCarrierAudit.ContractFour.Carrier)
    (hBC : B ⊆ carrierPreimage n C)
    (hBlock : ∃ i ∈ (Finset.univ : Finset B), ∃ b,
      TemplateInstances.ContractFour.blockClass n (i : Element n) = some b)
    (w : Element n → (Fin (n + Templates.ContractFour.quotientDim) → ℚ))
    (hwL : ∀ e, w e ∈ TemplateInstances.ContractFour.L n e) :
    ¬ LinearIndependent ℚ (fun b : B ↦ w b) := by
  apply not_linearIndependent_of_not_hasRadoCapacity _ (fun b : B ↦ hwL b)
  intro hCapacityL
  exact not_hasRadoCapacity_ambient_of_subset_carrier hBcard C hBC hBlock
    ((TemplateInstances.ContractFour.hasRadoCapacity_L_iff_ambient B).mp
      hCapacityL)

/-- Every full-size nonbasis is forced dependent by the template
constraints and prescribed special columns. -/
theorem nonbase_forced
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hGround : B ⊆ ((Family.MI n) ／ {Family.four n}).E)
    (hBcard : B.ncard = n + 2)
    (hNotBase : ¬ ((Family.MI n) ／ {Family.four n}).IsBase B)
    (w : Element n → (Fin (n + Templates.ContractFour.quotientDim) → ℚ))
    (hwL : ∀ e, w e ∈ TemplateInstances.ContractFour.L n e)
    (hwq : ∀ e ∈ TemplateInstances.ContractFour.fixedElements n,
      w e = TemplateInstances.ContractFour.q n e) :
    ¬ LinearIndependent ℚ (fun b : B ↦ w b) := by
  by_cases hT : Family.T n ⊆ B
  · exact not_linearIndependent_of_T_subset hT hwq
  by_cases hC1 : B = Family.C1 n \ {Family.four n}
  · have hBC : B ⊆ carrierPreimage n .a := by
      rw [carrierPreimage_a, hC1]
    let i : B := ⟨Family.x0 n, by
      rw [hC1]
      exact ⟨Set.mem_union_right _ (Family.x0_mem_X n), by simp⟩⟩
    have hBlock : ∃ i ∈ (Finset.univ : Finset B), ∃ b,
        TemplateInstances.ContractFour.blockClass n (i : Element n) = some b :=
      ⟨i, Finset.mem_univ i, .X, rfl⟩
    exact not_linearIndependent_of_subset_carrier
      hBcard .a hBC hBlock w hwL
  by_cases hC2 : B = Family.C2 n \ {Family.four n}
  · have hBC : B ⊆ carrierPreimage n .b := by
      rw [carrierPreimage_b, hC2]
    let i : B := ⟨Family.y0 n, by
      rw [hC2]
      exact ⟨Set.mem_union_right _ (Family.y0_mem_Y n), by simp⟩⟩
    have hBlock : ∃ i ∈ (Finset.univ : Finset B), ∃ b,
        TemplateInstances.ContractFour.blockClass n (i : Element n) = some b :=
      ⟨i, Finset.mem_univ i, .Y, rfl⟩
    exact not_linearIndependent_of_subset_carrier
      hBcard .b hBC hBlock w hwL
  by_cases hC3 : B = Family.C3 n \ {Family.four n}
  · have hBC : B ⊆ carrierPreimage n .aPlusB := by
      rw [carrierPreimage_aPlusB, hC3]
    let i : B := ⟨Family.z0 n, by
      rw [hC3]
      exact ⟨Set.mem_union_right _ (Family.z0_mem_Z n), by simp⟩⟩
    have hBlock : ∃ i ∈ (Finset.univ : Finset B), ∃ b,
        TemplateInstances.ContractFour.blockClass n (i : Element n) = some b :=
      ⟨i, Finset.mem_univ i, .Z, rfl⟩
    exact not_linearIndependent_of_subset_carrier
      hBcard .aPlusB hBC hBlock w hwL
  exact (hNotBase ((Family.contract_four_isBase_iff n B).mpr
    ⟨hGround, hBcard, hT, hC1, hC2, hC3⟩)).elim

/-! ### End-to-end representation -/

theorem exists_representation (n : ℕ) :
    ∃ v : Element n → (Fin (n + 2) → ℚ),
      Represents ℚ ((Family.MI n) ／ {Family.four n}) v ∧
        (∀ e, v e ∈ TemplateInstances.ContractFour.L n e) ∧
          (∀ e ∈ TemplateInstances.ContractFour.fixedElements n,
            v e = TemplateInstances.ContractFour.q n e) := by
  apply exists_representation_of_subspace_base_audit
    (M := (Family.MI n) ／ {Family.four n})
    (d := n + 2)
    (TemplateInstances.ContractFour.L n)
    (TemplateInstances.ContractFour.fixedElements n)
    (TemplateInstances.ContractFour.q n)
  · intro e he
    exact TemplateInstances.ContractFour.q_mem_L he
  · obtain ⟨B₀, hB₀⟩ :=
      ((Family.MI n) ／ {Family.four n}).exists_isBase
    exact ⟨B₀, hB₀,
      ((Family.contract_four_isBase_iff n B₀).mp hB₀).2.1⟩
  · intro B hB _
    letI : Fintype B := B.toFinite.fintype
    exact TemplateInstances.ContractFour.feasible_assignment_on_candidate B
      (hasRadoCapacity_L_of_isBase hB)
  · intro B hGround hBcard hNotBase w hwL hwq
    letI : Fintype B := B.toFinite.fintype
    exact nonbase_forced hGround hBcard hNotBase w hwL hwq

/-- Public endpoint: contraction by `4` is rationally representable for all
parameters, including `n = 0`. -/
theorem contract_four_rationallyRepresentable (n : ℕ) :
    RationallyRepresentable ((Family.MI n) ／ {Family.four n}) := by
  obtain ⟨v, hv, -, -⟩ := exists_representation n
  exact ⟨n + 2, v, hv⟩

end ContractFour

end BlandJensenFormal.BlandJensenMI.ContractionFourCapacity
