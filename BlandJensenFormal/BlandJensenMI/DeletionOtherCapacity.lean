import BlandJensenFormal.BlandJensenMI.DeletionCapacity

/-!
# Capacity audits for deletion of `1` and deletion of `4`

This file completes the two special-element deletion templates.  For each
minor it proves every Rado inequality for actual bases, proves that every
full-size nonbase is forced to be linearly dependent, and invokes the generic
representation compiler to obtain a rational representation.
-/

namespace BlandJensenFormal.BlandJensenMI

open Function Set Submodule
open scoped Matroid

namespace DeletionOtherCapacity

/-! ## Common finite-selector bookkeeping -/

def actualSet {n : ℕ} {B : Set (Element n)} (J : Finset B) :
    Set (Element n) := Subtype.val '' (J : Set B)

@[simp] theorem ncard_actualSet {n : ℕ} {B : Set (Element n)}
    (J : Finset B) : (actualSet J).ncard = J.card := by
  rw [actualSet, Set.ncard_image_of_injective _ Subtype.val_injective]
  simp

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

/-! ## Deletion of `1` -/

namespace DeleteOne

abbrev Label := QuotientCarrierAudit.DeleteOne.Label

def blockLabelClass : Fin 3 → Label := ![.A, .B, .C]

/-- The value at the removed label `1` is immaterial; actual selectors lie in
the deletion ground set. -/
def specialLabelClass : Fin 4 → Label := ![.Two, .Two, .Three, .Four]

def labelClass (n : ℕ) : Element n → Label
  | .special s => specialLabelClass s
  | .block b _ => blockLabelClass b

def quotientLabel (n : ℕ) :
    Element n → Templates.QuotientSpace Templates.DeleteOne.quotientDim :=
  ClassifiedGeometry.quotientLabelOf
    Templates.DeleteOne.blockLabel (Templates.DeleteOne.special n)
    (TemplateInstances.DeleteOne.blockClass n)
    (TemplateInstances.DeleteOne.specialClass n)

theorem quotientLabel_eq_label (n : ℕ) {e : Element n}
    (he : e ≠ Family.one n) :
    quotientLabel n e = QuotientCarrierAudit.DeleteOne.label (labelClass n e) := by
  cases e with
  | special s =>
      fin_cases s <;> simp_all [quotientLabel, ClassifiedGeometry.quotientLabelOf,
        TemplateInstances.DeleteOne.specialClass,
        TemplateInstances.DeleteOne.specialKind, labelClass, specialLabelClass,
        Templates.DeleteOne.special, Templates.quotientInclusion_apply,
        Templates.DeleteOne.quotientLabel,
        QuotientCarrierAudit.DeleteOne.label, Family.one]
  | block b i =>
      fin_cases b <;> rfl

def selectedLabels {n : ℕ} {B : Set (Element n)} (J : Finset B) :
    Finset Label := J.image (fun b : B ↦ labelClass n (b : Element n))

theorem label_mem_selectedLabels {n : ℕ} {B : Set (Element n)}
    {J : Finset B} {b : B} (hb : b ∈ J) :
    labelClass n (b : Element n) ∈ selectedLabels J := by
  exact Finset.mem_image.mpr ⟨b, hb, rfl⟩

theorem quotient_image_eq {n : ℕ} {B : Set (Element n)}
    (hremoved : Family.one n ∉ B) (J : Finset B) :
    (quotientLabel n ∘ fun b : B ↦ (b : Element n)) '' (J : Set B) =
      QuotientCarrierAudit.DeleteOne.label ''
        (selectedLabels J : Set Label) := by
  ext p
  constructor
  · rintro ⟨b, hb, rfl⟩
    change quotientLabel n b ∈ _
    rw [quotientLabel_eq_label n (fun h ↦ hremoved (h ▸ b.property))]
    exact ⟨labelClass n b, label_mem_selectedLabels hb, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hl
    exact ⟨b, hb, quotientLabel_eq_label n
      (fun h ↦ hremoved (h ▸ b.property))⟩

/-- Surviving elements carrying one fixed label. -/
def survivingFiber (n : ℕ) (l : Label) : Set (Element n) :=
  {e | e ≠ Family.one n ∧ labelClass n e = l}

theorem survivingFiber_ncard_le (n : ℕ) (l : Label) :
    (survivingFiber n l).ncard ≤ n + 1 := by
  cases l with
  | A =>
      have hset : survivingFiber n .A = Family.X n := by
        ext e
        cases e with
        | special s => fin_cases s <;> simp [survivingFiber, labelClass,
            specialLabelClass, Family.X, Family.blockSet, Family.one]
        | block b i => fin_cases b <;> simp [survivingFiber, labelClass,
            blockLabelClass, Family.X, Family.blockSet, Family.one]
      rw [hset, Family.ncard_X]
  | B =>
      have hset : survivingFiber n .B = Family.Y n := by
        ext e
        cases e with
        | special s => fin_cases s <;> simp [survivingFiber, labelClass,
            specialLabelClass, Family.Y, Family.blockSet, Family.one]
        | block b i => fin_cases b <;> simp [survivingFiber, labelClass,
            blockLabelClass, Family.Y, Family.blockSet, Family.one]
      rw [hset, Family.ncard_Y]
  | C =>
      have hset : survivingFiber n .C = Family.Z n := by
        ext e
        cases e with
        | special s => fin_cases s <;> simp [survivingFiber, labelClass,
            specialLabelClass, Family.Z, Family.blockSet, Family.one]
        | block b i => fin_cases b <;> simp [survivingFiber, labelClass,
            blockLabelClass, Family.Z, Family.blockSet, Family.one]
      rw [hset, Family.ncard_Z]
  | Two =>
      have hset : survivingFiber n .Two = {Family.two n} := by
        ext e
        cases e with
        | special s => fin_cases s <;> simp [survivingFiber, labelClass,
            specialLabelClass, Family.one, Family.two]
        | block b i => fin_cases b <;> simp [survivingFiber, labelClass,
            blockLabelClass, Family.one, Family.two]
      rw [hset]
      simp
  | Three =>
      have hset : survivingFiber n .Three = {Family.three n} := by
        ext e
        cases e with
        | special s => fin_cases s <;> simp [survivingFiber, labelClass,
            specialLabelClass, Family.one, Family.three]
        | block b i => fin_cases b <;> simp [survivingFiber, labelClass,
            blockLabelClass, Family.one, Family.three]
      rw [hset]
      simp
  | Four =>
      have hset : survivingFiber n .Four = {Family.four n} := by
        ext e
        cases e with
        | special s => fin_cases s <;> simp [survivingFiber, labelClass,
            specialLabelClass, Family.one, Family.four]
        | block b i => fin_cases b <;> simp [survivingFiber, labelClass,
            blockLabelClass, Family.one, Family.four]
      rw [hset]
      simp

theorem label_ne_zero (l : Label) :
    QuotientCarrierAudit.DeleteOne.label l ≠ 0 := by
  fin_cases l <;> intro h
  all_goals
    have h0 := congrFun h (0 : Fin 3)
    have h1 := congrFun h (1 : Fin 3)
    have h2 := congrFun h (2 : Fin 3)
    simp [QuotientCarrierAudit.DeleteOne.label,
      BlandJensenFormal.MIQuotientLabels.DeleteOne.label,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at h0 h1 h2

theorem card_le_n_add_one_of_selectedLabels_card_le_one
    {n : ℕ} {B : Set (Element n)} {J : Finset B}
    (hremoved : Family.one n ∉ B)
    (hJ : J.Nonempty) (hcard : (selectedLabels J).card ≤ 1) :
    J.card ≤ n + 1 := by
  obtain ⟨b, hb⟩ := hJ
  let l := labelClass n b
  have hsubset : actualSet J ⊆ survivingFiber n l := by
    rintro e ⟨c, hc, rfl⟩
    refine ⟨fun h ↦ hremoved (h ▸ c.property), ?_⟩
    have hcl := label_mem_selectedLabels hc
    have hbl := label_mem_selectedLabels hb
    exact Finset.card_le_one.mp hcard _ hcl _ hbl
  rw [← ncard_actualSet J]
  exact (Set.ncard_le_ncard hsubset (Set.toFinite _)).trans
    (survivingFiber_ncard_le n l)

def carrierPreimage (n : ℕ) (C : QuotientCarrierAudit.DeleteOne.Carrier) :
    Set (Element n) :=
  {e | e ≠ Family.one n ∧
    labelClass n e ∈ QuotientCarrierAudit.DeleteOne.carrier C}

theorem carrierPreimage_planeABThree (n : ℕ) :
    carrierPreimage n .planeABThree = Family.H3 n := by
  ext e
  cases e with
  | special s => fin_cases s <;> simp [carrierPreimage, labelClass,
      specialLabelClass, QuotientCarrierAudit.DeleteOne.carrier,
      Family.H3, Family.X, Family.Y, Family.blockSet, Family.one, Family.three]
  | block b i => fin_cases b <;> simp [carrierPreimage, labelClass,
      blockLabelClass, QuotientCarrierAudit.DeleteOne.carrier,
      Family.H3, Family.X, Family.Y, Family.blockSet, Family.one]

theorem carrierPreimage_planeACTwo (n : ℕ) :
    carrierPreimage n .planeACTwo = Family.H2 n := by
  ext e
  cases e with
  | special s => fin_cases s <;> simp [carrierPreimage, labelClass,
      specialLabelClass, QuotientCarrierAudit.DeleteOne.carrier,
      Family.H2, Family.X, Family.Z, Family.blockSet, Family.one, Family.two]
  | block b i => fin_cases b <;> simp [carrierPreimage, labelClass,
      blockLabelClass, QuotientCarrierAudit.DeleteOne.carrier,
      Family.H2, Family.X, Family.Z, Family.blockSet, Family.one]

theorem carrierPreimage_planeBTwoFour (n : ℕ) :
    carrierPreimage n .planeBTwoFour = Family.C2 n := by
  ext e
  cases e with
  | special s => fin_cases s <;> simp [carrierPreimage, labelClass,
      specialLabelClass, QuotientCarrierAudit.DeleteOne.carrier,
      Family.C2, Family.Y, Family.blockSet, Family.one, Family.two, Family.four]
  | block b i => fin_cases b <;> simp [carrierPreimage, labelClass,
      blockLabelClass, QuotientCarrierAudit.DeleteOne.carrier,
      Family.C2, Family.Y, Family.blockSet, Family.one]

theorem carrierPreimage_planeCThreeFour (n : ℕ) :
    carrierPreimage n .planeCThreeFour = Family.C3 n := by
  ext e
  cases e with
  | special s => fin_cases s <;> simp [carrierPreimage, labelClass,
      specialLabelClass, QuotientCarrierAudit.DeleteOne.carrier,
      Family.C3, Family.Z, Family.blockSet, Family.one, Family.three, Family.four]
  | block b i => fin_cases b <;> simp [carrierPreimage, labelClass,
      blockLabelClass, QuotientCarrierAudit.DeleteOne.carrier,
      Family.C3, Family.Z, Family.blockSet, Family.one]

theorem carrierPreimage_pairAFour (n : ℕ) :
    carrierPreimage n .pairAFour = {Family.four n} ∪ Family.X n := by
  ext e
  cases e with
  | special s => fin_cases s <;> simp [carrierPreimage, labelClass,
      specialLabelClass, QuotientCarrierAudit.DeleteOne.carrier,
      Family.X, Family.blockSet, Family.one, Family.four]
  | block b i => fin_cases b <;> simp [carrierPreimage, labelClass,
      blockLabelClass, QuotientCarrierAudit.DeleteOne.carrier,
      Family.X, Family.blockSet, Family.one]

theorem carrierPreimage_pairBC (n : ℕ) :
    carrierPreimage n .pairBC = Family.H1 n \ {Family.one n} := by
  ext e
  cases e with
  | special s => fin_cases s <;> simp [carrierPreimage, labelClass,
      specialLabelClass, QuotientCarrierAudit.DeleteOne.carrier,
      Family.H1, Family.Y, Family.Z, Family.blockSet, Family.one]
  | block b i => fin_cases b <;> simp [carrierPreimage, labelClass,
      blockLabelClass, QuotientCarrierAudit.DeleteOne.carrier,
      Family.H1, Family.Y, Family.Z, Family.blockSet, Family.one]

theorem carrierPreimage_pairTwoThree (n : ℕ) :
    carrierPreimage n .pairTwoThree = {Family.two n, Family.three n} := by
  ext e
  cases e with
  | special s => fin_cases s <;> simp [carrierPreimage, labelClass,
      specialLabelClass, QuotientCarrierAudit.DeleteOne.carrier,
      Family.one, Family.two, Family.three]
  | block b i => fin_cases b <;> simp [carrierPreimage, labelClass,
      blockLabelClass, QuotientCarrierAudit.DeleteOne.carrier, Family.one]

theorem base_not_subset_carrierPreimage {n : ℕ} {B : Set (Element n)}
    (hB : ((Family.MI n) ＼ {Family.one n}).IsBase B)
    (C : QuotientCarrierAudit.DeleteOne.Carrier) :
    ¬ B ⊆ carrierPreimage n C := by
  rcases (Family.delete_one_isBase_iff n B).mp hB with
    ⟨-, hcard, hC2, hC3, hH1, hH2, hH3⟩
  intro hsub
  cases C with
  | planeABThree => exact hH3 (by simpa [carrierPreimage_planeABThree] using hsub)
  | planeACTwo => exact hH2 (by simpa [carrierPreimage_planeACTwo] using hsub)
  | planeBTwoFour =>
      apply hC2
      exact Set.eq_of_subset_of_ncard_le
        (by simpa [carrierPreimage_planeBTwoFour] using hsub)
        (by simp [hcard]) (Set.toFinite _)
  | planeCThreeFour =>
      apply hC3
      exact Set.eq_of_subset_of_ncard_le
        (by simpa [carrierPreimage_planeCThreeFour] using hsub)
        (by simp [hcard]) (Set.toFinite _)
  | pairAFour =>
      have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [carrierPreimage_pairAFour, Set.ncard_union_eq] at hle
      · simp at hle
        omega
      · rw [Set.disjoint_left]
        intro e he hX
        have heq : e = Family.four n := by simpa using he
        subst e
        exact Family.special_not_mem_blockSet n 3 0 hX
  | pairBC => exact hH1 (by simpa [carrierPreimage_pairBC] using hsub)
  | pairTwoThree =>
      have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [carrierPreimage_pairTwoThree] at hle
      simp at hle
      omega

/-! ### Pure-special selectors -/

/-- Template special attached to a surviving actual special element.  The
value at the removed element and on blocks is irrelevant in the applications
below. -/
def specialValue (n : ℕ) : Element n → Templates.DeleteOne.Special
  | .special s => ![.Two, .Two, .Three, .Four] s
  | .block _ _ => .Two

def actualSpecial (n : ℕ) : Templates.DeleteOne.Special → Element n
  | .Two => Family.two n
  | .Three => Family.three n
  | .Four => Family.four n

@[simp] theorem specialValue_actualSpecial (n : ℕ)
    (s : Templates.DeleteOne.Special) :
    specialValue n (actualSpecial n s) = s := by
  cases s <;> rfl

@[simp] theorem blockClass_actualSpecial (n : ℕ)
    (s : Templates.DeleteOne.Special) :
    TemplateInstances.DeleteOne.blockClass n (actualSpecial n s) = none := by
  cases s <;> rfl

theorem actualSpecial_ne_one (n : ℕ) (s : Templates.DeleteOne.Special) :
    actualSpecial n s ≠ Family.one n := by
  cases s <;> simp [actualSpecial, Family.one, Family.two, Family.three,
    Family.four]

theorem specialClass_eq_some_specialValue_of_blockClass_eq_none
    {n : ℕ} {e : Element n}
    (he : e ≠ Family.one n)
    (hBlock : TemplateInstances.DeleteOne.blockClass n e = none) :
    TemplateInstances.DeleteOne.specialClass n e = some (specialValue n e) := by
  cases e with
  | special s =>
      fin_cases s
      · exact (he rfl).elim
      · rfl
      · rfl
      · rfl
  | block b i =>
      simp [TemplateInstances.DeleteOne.blockClass,
        TemplateInstances.DeleteOne.blockKind] at hBlock

theorem specialValue_injective_of_blockClass_eq_none
    {n : ℕ} {e f : Element n}
    (he : e ≠ Family.one n) (hf : f ≠ Family.one n)
    (heBlock : TemplateInstances.DeleteOne.blockClass n e = none)
    (hfBlock : TemplateInstances.DeleteOne.blockClass n f = none)
    (hValue : specialValue n e = specialValue n f) : e = f := by
  cases e with
  | special se =>
      cases f with
      | special sf =>
          fin_cases se <;> fin_cases sf <;>
            simp_all [specialValue, Family.one]
      | block bf i =>
          simp [TemplateInstances.DeleteOne.blockClass,
            TemplateInstances.DeleteOne.blockKind] at hfBlock
  | block be i =>
      simp [TemplateInstances.DeleteOne.blockClass,
        TemplateInstances.DeleteOne.blockKind] at heBlock

theorem eq_actualSpecial_specialValue_of_blockClass_eq_none
    {n : ℕ} {e : Element n}
    (he : e ≠ Family.one n)
    (hBlock : TemplateInstances.DeleteOne.blockClass n e = none) :
    e = actualSpecial n (specialValue n e) := by
  apply specialValue_injective_of_blockClass_eq_none he
    (actualSpecial_ne_one n _) hBlock (blockClass_actualSpecial n _)
  simp

/-- Every selector consisting only of fixed special elements satisfies its
Rado inequality. -/
theorem card_le_finrank_subspaceSum_of_forall_blockClass_none
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hB : ((Family.MI n) ＼ {Family.one n}).IsBase B)
    (J : Finset B)
    (hPure : ∀ i ∈ J,
      TemplateInstances.DeleteOne.blockClass n (i : Element n) = none) :
    J.card ≤ Module.finrank ℚ
      (subspaceSum ℚ
        (fun b : B ↦ TemplateInstances.DeleteOne.ambientSubspace n b) J) := by
  rcases (Family.delete_one_isBase_iff n B).mp hB with
    ⟨hGround, -, -, -, -, -, -⟩
  have hOneB : Family.one n ∉ B := by
    intro hOne
    exact (hGround hOne).2 (by simp)
  let f : J → Templates.DeleteOne.Special := fun j ↦
    specialValue n (j.1 : Element n)
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply Subtype.ext
    apply specialValue_injective_of_blockClass_eq_none
      (fun he ↦ hOneB (he ▸ i.1.property))
      (fun he ↦ hOneB (he ▸ j.1.property))
      (hPure i.1 i.2) (hPure j.1 j.2)
    exact hij
  have hActualLinear : LinearIndependent ℚ
      (fun j : J ↦ Templates.DeleteOne.special n
        (specialValue n (j.1 : Element n))) := by
    simpa [f, Function.comp_def] using
      (SpecialGeometry.DeleteOne.linearIndependent_special n).comp f hf
  let W := subspaceSum ℚ
    (fun b : B ↦ TemplateInstances.DeleteOne.ambientSubspace n b) J
  let v : J → W := fun j ↦
    ⟨Templates.DeleteOne.special n (specialValue n (j.1 : Element n)), by
      apply (Finset.le_sup
        (f := fun b : B ↦ TemplateInstances.DeleteOne.ambientSubspace n b)
        j.2)
      have hpure := hPure j.1 j.2
      have hspecial := specialClass_eq_some_specialValue_of_blockClass_eq_none
        (fun he ↦ hOneB (he ▸ j.1.property)) hpure
      simp [TemplateInstances.DeleteOne.ambientSubspace,
        TemplateInstances.ambientSubspaceOf, hpure, hspecial]⟩
  have hv : LinearIndependent ℚ v := by
    apply LinearIndependent.of_comp W.subtype
    simpa [v, Function.comp_def] using hActualLinear
  simpa [W] using hv.fintype_card_le_finrank

/-! ### Mixed selectors -/

/-- Every selector containing a large-block element satisfies its Rado
inequality.  The exact dimension formula reduces the claim to the fixed
three-dimensional quotient-label configuration. -/
theorem card_le_finrank_subspaceSum_of_exists_block
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hB : ((Family.MI n) ＼ {Family.one n}).IsBase B)
    (J : Finset B)
    (hBlock : ∃ i ∈ J, ∃ b,
      TemplateInstances.DeleteOne.blockClass n (i : Element n) = some b) :
    J.card ≤ Module.finrank ℚ
      (subspaceSum ℚ
        (fun b : B ↦ TemplateInstances.DeleteOne.ambientSubspace n b) J) := by
  rcases (Family.delete_one_isBase_iff n B).mp hB with
    ⟨hGround, hBcard, -, -, -, -, -⟩
  have hOneB : Family.one n ∉ B := by
    intro hOne
    exact (hGround hOne).2 (by simp)
  let R : Submodule ℚ
      (Templates.QuotientSpace Templates.DeleteOne.quotientDim) :=
    Submodule.span ℚ
      ((quotientLabel n ∘ fun b : B ↦ (b : Element n)) '' (J : Set B))
  have hdim : Module.finrank ℚ
      (subspaceSum ℚ
        (fun b : B ↦ TemplateInstances.DeleteOne.ambientSubspace n b) J) =
      n + Module.finrank ℚ R := by
    simpa [TemplateInstances.DeleteOne.ambientSubspace, quotientLabel, R] using
      (ClassifiedGeometry.finrank_subspaceSum_ambientSubspaceOf
        Templates.DeleteOne.blockLabel (Templates.DeleteOne.special n)
        (TemplateInstances.DeleteOne.blockClass n)
        (TemplateInstances.DeleteOne.specialClass n)
        (fun b : B ↦ (b : Element n)) hBlock)
  rw [hdim]
  by_contra hCapacity
  have hlt : n + Module.finrank ℚ R < J.card :=
    Nat.lt_of_not_ge hCapacity
  have hJle : J.card ≤ n + 3 := card_selector_le_of_ncard hBcard J
  have hRankLe : Module.finrank ℚ R ≤ 2 := by omega
  let S : Finset Label := selectedLabels J
  have hSpan : R = Submodule.span ℚ
      (QuotientCarrierAudit.DeleteOne.label '' (S : Set Label)) := by
    dsimp [R, S]
    rw [quotient_image_eq hOneB]
  by_cases hRankZero : Module.finrank ℚ R = 0
  · have hRbot : R = ⊥ := Submodule.finrank_eq_zero.mp hRankZero
    obtain ⟨i, hi, b, hib⟩ := hBlock
    have hqMem : quotientLabel n (i : Element n) ∈ R :=
      Submodule.subset_span ⟨i, hi, rfl⟩
    have hqZero : quotientLabel n (i : Element n) = 0 := by
      rw [hRbot] at hqMem
      simpa using hqMem
    have hLabelZero : QuotientCarrierAudit.DeleteOne.label
        (labelClass n (i : Element n)) = 0 := by
      rw [← quotientLabel_eq_label n
        (fun he ↦ hOneB (he ▸ i.property))]
      exact hqZero
    exact label_ne_zero _ hLabelZero
  · by_cases hRankOne : Module.finrank ℚ R ≤ 1
    · have hScard : S.card ≤ 1 :=
        (QuotientCarrierAudit.DeleteOne.finrank_le_one_iff_card_le_one S).mp
          (by rw [← hSpan]; exact hRankOne)
      obtain ⟨i, hi, -, -⟩ := hBlock
      have hJnonempty : J.Nonempty := ⟨i, hi⟩
      have hJsmall := card_le_n_add_one_of_selectedLabels_card_le_one
        hOneB hJnonempty hScard
      omega
    · have hRankTwo : Module.finrank ℚ R = 2 := by omega
      have hJcard : J.card = n + 3 := by omega
      have hJuniv : J = Finset.univ :=
        selector_eq_univ_of_card_eq hBcard hJcard
      obtain ⟨C, hSC⟩ :=
        QuotientCarrierAudit.DeleteOne.contained_in_carrier_of_finrank_le_two S
          (by rw [← hSpan, hRankTwo])
      have hBcarrier : B ⊆ carrierPreimage n C := by
        intro e heB
        let b : B := ⟨e, heB⟩
        have hbJ : b ∈ J := by simp [hJuniv]
        exact ⟨fun he ↦ hOneB (he ▸ heB),
          hSC (label_mem_selectedLabels hbJ)⟩
      exact base_not_subset_carrierPreimage hB C hBcarrier

/-- Complete Rado audit for every basis after deleting `1`. -/
theorem hasRadoCapacity_ambient_of_isBase
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hB : ((Family.MI n) ＼ {Family.one n}).IsBase B) :
    HasRadoCapacity ℚ
      (fun b : B ↦ TemplateInstances.DeleteOne.ambientSubspace n b) := by
  classical
  intro J
  by_cases hBlock : ∃ i ∈ J, ∃ b,
      TemplateInstances.DeleteOne.blockClass n (i : Element n) = some b
  · exact card_le_finrank_subspaceSum_of_exists_block hB J hBlock
  · apply card_le_finrank_subspaceSum_of_forall_blockClass_none hB J
    intro i hi
    cases hClass : TemplateInstances.DeleteOne.blockClass n
        (i : Element n) with
    | none => rfl
    | some b => exact (hBlock ⟨i, hi, b, hClass⟩).elim

/-- Coordinate-space Rado audit consumed by the representation compiler. -/
theorem hasRadoCapacity_L_of_isBase
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hB : ((Family.MI n) ＼ {Family.one n}).IsBase B) :
    HasRadoCapacity ℚ (fun b : B ↦ TemplateInstances.DeleteOne.L n b) :=
  (TemplateInstances.DeleteOne.hasRadoCapacity_L_iff_ambient B).mpr
    (hasRadoCapacity_ambient_of_isBase hB)

/-! ### Forced dependence of full-size nonbases -/

/-- Every allowed ambient subspace whose label belongs to a carrier is
contained in the inverse image of that carrier's quotient span. -/
theorem ambientSubspace_le_corePlus_carrier
    {n : ℕ} {e : Element n}
    (C : QuotientCarrierAudit.DeleteOne.Carrier)
    (he : e ∈ carrierPreimage n C) :
    TemplateInstances.DeleteOne.ambientSubspace n e ≤
      Templates.corePlus n Templates.DeleteOne.quotientDim
        (Submodule.span ℚ
          (QuotientCarrierAudit.DeleteOne.label ''
            (QuotientCarrierAudit.DeleteOne.carrier C : Set Label))) := by
  let P : Submodule ℚ
      (Templates.QuotientSpace Templates.DeleteOne.quotientDim) :=
    Submodule.span ℚ
      (QuotientCarrierAudit.DeleteOne.label ''
        (QuotientCarrierAudit.DeleteOne.carrier C : Set Label))
  have hLabel : quotientLabel n e ∈ P := by
    apply Submodule.subset_span
    exact ⟨labelClass n e, he.2,
      (quotientLabel_eq_label n he.1).symm⟩
  have hLine : ℚ ∙ quotientLabel n e ≤ P :=
    by
      rw [Submodule.span_singleton_le_iff_mem]
      exact hLabel
  intro x hx
  apply (Templates.mem_corePlus_iff n Templates.DeleteOne.quotientDim P x).2
  apply hLine
  have hMapMem : Templates.quotientProjection n
      Templates.DeleteOne.quotientDim x ∈
      (TemplateInstances.DeleteOne.ambientSubspace n e).map
        (Templates.quotientProjection n Templates.DeleteOne.quotientDim) :=
    ⟨x, hx, rfl⟩
  have hMapEq :
      (TemplateInstances.DeleteOne.ambientSubspace n e).map
          (Templates.quotientProjection n Templates.DeleteOne.quotientDim) =
        ℚ ∙ quotientLabel n e := by
    simpa [TemplateInstances.DeleteOne.ambientSubspace, quotientLabel] using
      (ClassifiedGeometry.map_ambientSubspaceOf_eq_span_quotientLabelOf
        Templates.DeleteOne.blockLabel (Templates.DeleteOne.special n)
        (TemplateInstances.DeleteOne.blockClass n)
        (TemplateInstances.DeleteOne.specialClass n) e)
  rw [hMapEq] at hMapMem
  exact hMapMem

theorem finrank_subspaceSum_ambient_univ_le_n_add_two_of_subset_carrier
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (C : QuotientCarrierAudit.DeleteOne.Carrier)
    (hBC : B ⊆ carrierPreimage n C) :
    Module.finrank ℚ
      (subspaceSum ℚ
        (fun b : B ↦ TemplateInstances.DeleteOne.ambientSubspace n b)
        Finset.univ) ≤ n + 2 := by
  let P : Submodule ℚ
      (Templates.QuotientSpace Templates.DeleteOne.quotientDim) :=
    Submodule.span ℚ
      (QuotientCarrierAudit.DeleteOne.label ''
        (QuotientCarrierAudit.DeleteOne.carrier C : Set Label))
  have hSum : subspaceSum ℚ
      (fun b : B ↦ TemplateInstances.DeleteOne.ambientSubspace n b)
      Finset.univ ≤ Templates.corePlus n Templates.DeleteOne.quotientDim P := by
    rw [subspaceSum, Finset.sup_le_iff]
    intro b hb
    exact ambientSubspace_le_corePlus_carrier C (hBC b.property)
  calc
    Module.finrank ℚ
        (subspaceSum ℚ
          (fun b : B ↦ TemplateInstances.DeleteOne.ambientSubspace n b)
          Finset.univ) ≤
        Module.finrank ℚ
          (Templates.corePlus n Templates.DeleteOne.quotientDim P) :=
      Submodule.finrank_mono hSum
    _ = n + Module.finrank ℚ P :=
      Templates.finrank_corePlus n Templates.DeleteOne.quotientDim P
    _ ≤ n + 2 := Nat.add_le_add_left
      (QuotientCarrierAudit.DeleteOne.carrier_finrank_le_two C) n

theorem finrank_subspaceSum_L_univ_le_n_add_two_of_subset_carrier
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (C : QuotientCarrierAudit.DeleteOne.Carrier)
    (hBC : B ⊆ carrierPreimage n C) :
    Module.finrank ℚ
      (subspaceSum ℚ (fun b : B ↦ TemplateInstances.DeleteOne.L n b)
        Finset.univ) ≤ n + 2 := by
  have hCoordinateDim : Module.finrank ℚ
      (subspaceSum ℚ (fun b : B ↦ TemplateInstances.DeleteOne.L n b)
        Finset.univ) =
      Module.finrank ℚ
        (subspaceSum ℚ
          (fun b : B ↦ TemplateInstances.DeleteOne.ambientSubspace n b)
          Finset.univ) := by
    simpa [TemplateInstances.DeleteOne.L] using
      (TemplateInstances.finrank_subspaceSum_coordinateSubspaceOf
        (TemplateInstances.DeleteOne.ambientSubspace n)
        (fun b : B ↦ (b : Element n)) Finset.univ)
  rw [hCoordinateDim]
  exact finrank_subspaceSum_ambient_univ_le_n_add_two_of_subset_carrier C hBC

theorem not_hasRadoCapacity_L_of_subset_carrier
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hBcard : B.ncard = n + 3)
    (C : QuotientCarrierAudit.DeleteOne.Carrier)
    (hBC : B ⊆ carrierPreimage n C) :
    ¬ HasRadoCapacity ℚ
      (fun b : B ↦ TemplateInstances.DeleteOne.L n b) := by
  apply not_hasRadoCapacity_of_finrank_lt_card (Finset.univ : Finset B)
  have hfin :=
    finrank_subspaceSum_L_univ_le_n_add_two_of_subset_carrier C hBC
  have hcard : (Finset.univ : Finset B).card = n + 3 := by
    simp [← Nat.card_eq_fintype_card, hBcard]
  omega

theorem not_linearIndependent_of_subset_carrier
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hBcard : B.ncard = n + 3)
    (C : QuotientCarrierAudit.DeleteOne.Carrier)
    (hBC : B ⊆ carrierPreimage n C)
    (w : Element n → (Fin (n + Templates.DeleteOne.quotientDim) → ℚ))
    (hwL : ∀ e, w e ∈ TemplateInstances.DeleteOne.L n e) :
    ¬ LinearIndependent ℚ (fun b : B ↦ w b) := by
  apply not_linearIndependent_of_not_hasRadoCapacity
    (not_hasRadoCapacity_L_of_subset_carrier hBcard C hBC)
  exact fun b : B ↦ hwL b

/-- Every full-size ground subset which is not a deletion basis is contained
in one of the seven quotient carriers and is therefore forced dependent. -/
theorem nonbase_forced_dependence
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hGround : B ⊆ ((Family.MI n) ＼ {Family.one n}).E)
    (hBcard : B.ncard = n + 3)
    (hNotBase : ¬ ((Family.MI n) ＼ {Family.one n}).IsBase B)
    (w : Element n → (Fin (n + Templates.DeleteOne.quotientDim) → ℚ))
    (hwL : ∀ e, w e ∈ TemplateInstances.DeleteOne.L n e) :
    ¬ LinearIndependent ℚ (fun b : B ↦ w b) := by
  have hCarrier : ∃ C : QuotientCarrierAudit.DeleteOne.Carrier,
      B ⊆ carrierPreimage n C := by
    by_cases hC2 : B = Family.C2 n
    · subst B
      exact ⟨.planeBTwoFour, by rw [carrierPreimage_planeBTwoFour]⟩
    by_cases hC3 : B = Family.C3 n
    · subst B
      exact ⟨.planeCThreeFour, by rw [carrierPreimage_planeCThreeFour]⟩
    by_cases hH1 : B ⊆ Family.H1 n \ {Family.one n}
    · exact ⟨.pairBC, by simpa [carrierPreimage_pairBC] using hH1⟩
    by_cases hH2 : B ⊆ Family.H2 n
    · exact ⟨.planeACTwo, by
        simpa [carrierPreimage_planeACTwo] using hH2⟩
    by_cases hH3 : B ⊆ Family.H3 n
    · exact ⟨.planeABThree, by
        simpa [carrierPreimage_planeABThree] using hH3⟩
    exfalso
    apply hNotBase
    exact (Family.delete_one_isBase_iff n B).mpr
      ⟨hGround, hBcard, hC2, hC3, hH1, hH2, hH3⟩
  obtain ⟨C, hBC⟩ := hCarrier
  exact not_linearIndependent_of_subset_carrier hBcard C hBC w hwL

/-! ### Representation endpoint -/

theorem rationallyRepresentable (n : ℕ) :
    RationallyRepresentable ((Family.MI n) ＼ {Family.one n}) := by
  refine ⟨n + 3, ?_⟩
  have hReference : ∃ B₀ : Set (Element n),
      ((Family.MI n) ＼ {Family.one n}).IsBase B₀ ∧
        B₀.ncard = n + 3 := by
    let B₀ := Family.basisContainingX0WithoutOne n
    have hOriginal : (Family.MI n).IsBase B₀ :=
      Family.basisContainingX0WithoutOne_isBase n
    have hDisjoint : Disjoint B₀ {Family.one n} := by
      rw [Set.disjoint_singleton_right]
      exact Family.one_not_mem_basisContainingX0WithoutOne n
    have hDeletion : ((Family.MI n) ＼ {Family.one n}).IsBase B₀ := by
      simpa using ((Family.one_singleton_coindep n).delete_isBase_iff
        (B := B₀)).2
          ⟨hOriginal, hDisjoint⟩
    exact ⟨B₀, hDeletion,
      Family.IsBase.ncard_eq n
        (Family.basisContainingX0WithoutOne_isBase n)⟩
  obtain ⟨v, hvRep, -, -⟩ :=
    exists_representation_of_subspace_base_audit
      (TemplateInstances.DeleteOne.L n)
      (TemplateInstances.DeleteOne.fixedElements n)
      (TemplateInstances.DeleteOne.q n)
      (fun e he ↦ TemplateInstances.DeleteOne.q_mem_L he)
      hReference
      (fun B hB _ ↦ by
        letI := B.toFinite.fintype
        exact
          TemplateInstances.DeleteOne.feasible_assignment_on_candidate_of_ambientCapacity
            B (hasRadoCapacity_ambient_of_isBase hB))
      (fun B hGround hCard hNotBase w hwL _ ↦ by
        letI := B.toFinite.fintype
        exact nonbase_forced_dependence hGround hCard hNotBase w hwL)
  exact ⟨v, hvRep⟩

end DeleteOne

/-! ## Deletion of `4` -/

namespace DeleteFour

abbrev Label := QuotientCarrierAudit.DeleteFour.Label

def blockLabelClass : Fin 3 → Label := ![.A, .B, .C]

/-- The value at the removed label `4` is immaterial. -/
def specialLabelClass : Fin 4 → Label := ![.One, .Two, .Three, .One]

def labelClass (n : ℕ) : Element n → Label
  | .special s => specialLabelClass s
  | .block b _ => blockLabelClass b

def quotientLabel (n : ℕ) :
    Element n → Templates.QuotientSpace Templates.DeleteFour.quotientDim :=
  ClassifiedGeometry.quotientLabelOf
    Templates.DeleteFour.blockLabel (Templates.DeleteFour.special n)
    (TemplateInstances.DeleteFour.blockClass n)
    (TemplateInstances.DeleteFour.specialClass n)

theorem quotientLabel_eq_label (n : ℕ) {e : Element n}
    (he : e ≠ Family.four n) :
    quotientLabel n e = QuotientCarrierAudit.DeleteFour.label (labelClass n e) := by
  cases e with
  | special s =>
      fin_cases s <;> simp_all [quotientLabel, ClassifiedGeometry.quotientLabelOf,
        TemplateInstances.DeleteFour.specialClass,
        TemplateInstances.DeleteFour.specialKind, labelClass, specialLabelClass,
        Templates.DeleteFour.special, Templates.quotientInclusion_apply,
        Templates.DeleteFour.quotientLabel,
        QuotientCarrierAudit.DeleteFour.label, Family.four]
  | block b i =>
      fin_cases b <;> rfl

def selectedLabels {n : ℕ} {B : Set (Element n)} (J : Finset B) :
    Finset Label := J.image (fun b : B ↦ labelClass n (b : Element n))

theorem label_mem_selectedLabels {n : ℕ} {B : Set (Element n)}
    {J : Finset B} {b : B} (hb : b ∈ J) :
    labelClass n (b : Element n) ∈ selectedLabels J := by
  exact Finset.mem_image.mpr ⟨b, hb, rfl⟩

theorem quotient_image_eq {n : ℕ} {B : Set (Element n)}
    (hremoved : Family.four n ∉ B) (J : Finset B) :
    (quotientLabel n ∘ fun b : B ↦ (b : Element n)) '' (J : Set B) =
      QuotientCarrierAudit.DeleteFour.label ''
        (selectedLabels J : Set Label) := by
  ext p
  constructor
  · rintro ⟨b, hb, rfl⟩
    change quotientLabel n b ∈ _
    rw [quotientLabel_eq_label n (fun h ↦ hremoved (h ▸ b.property))]
    exact ⟨labelClass n b, label_mem_selectedLabels hb, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hl
    exact ⟨b, hb, quotientLabel_eq_label n
      (fun h ↦ hremoved (h ▸ b.property))⟩

def survivingFiber (n : ℕ) (l : Label) : Set (Element n) :=
  {e | e ≠ Family.four n ∧ labelClass n e = l}

theorem survivingFiber_ncard_le (n : ℕ) (l : Label) :
    (survivingFiber n l).ncard ≤ n + 1 := by
  cases l with
  | A =>
      have hset : survivingFiber n .A = Family.X n := by
        ext e
        cases e with
        | special s => fin_cases s <;> simp [survivingFiber, labelClass,
            specialLabelClass, Family.X, Family.blockSet, Family.four]
        | block b i => fin_cases b <;> simp [survivingFiber, labelClass,
            blockLabelClass, Family.X, Family.blockSet, Family.four]
      rw [hset, Family.ncard_X]
  | B =>
      have hset : survivingFiber n .B = Family.Y n := by
        ext e
        cases e with
        | special s => fin_cases s <;> simp [survivingFiber, labelClass,
            specialLabelClass, Family.Y, Family.blockSet, Family.four]
        | block b i => fin_cases b <;> simp [survivingFiber, labelClass,
            blockLabelClass, Family.Y, Family.blockSet, Family.four]
      rw [hset, Family.ncard_Y]
  | C =>
      have hset : survivingFiber n .C = Family.Z n := by
        ext e
        cases e with
        | special s => fin_cases s <;> simp [survivingFiber, labelClass,
            specialLabelClass, Family.Z, Family.blockSet, Family.four]
        | block b i => fin_cases b <;> simp [survivingFiber, labelClass,
            blockLabelClass, Family.Z, Family.blockSet, Family.four]
      rw [hset, Family.ncard_Z]
  | One =>
      have hset : survivingFiber n .One = {Family.one n} := by
        ext e
        cases e with
        | special s => fin_cases s <;> simp [survivingFiber, labelClass,
            specialLabelClass, Family.one, Family.four]
        | block b i => fin_cases b <;> simp [survivingFiber, labelClass,
            blockLabelClass, Family.one, Family.four]
      rw [hset]
      simp
  | Two =>
      have hset : survivingFiber n .Two = {Family.two n} := by
        ext e
        cases e with
        | special s => fin_cases s <;> simp [survivingFiber, labelClass,
            specialLabelClass, Family.two, Family.four]
        | block b i => fin_cases b <;> simp [survivingFiber, labelClass,
            blockLabelClass, Family.two, Family.four]
      rw [hset]
      simp
  | Three =>
      have hset : survivingFiber n .Three = {Family.three n} := by
        ext e
        cases e with
        | special s => fin_cases s <;> simp [survivingFiber, labelClass,
            specialLabelClass, Family.three, Family.four]
        | block b i => fin_cases b <;> simp [survivingFiber, labelClass,
            blockLabelClass, Family.three, Family.four]
      rw [hset]
      simp

theorem label_ne_zero (l : Label) :
    QuotientCarrierAudit.DeleteFour.label l ≠ 0 := by
  fin_cases l <;> intro h
  all_goals
    have h0 := congrFun h (0 : Fin 3)
    have h1 := congrFun h (1 : Fin 3)
    have h2 := congrFun h (2 : Fin 3)
    simp [QuotientCarrierAudit.DeleteFour.label,
      BlandJensenFormal.MIQuotientLabels.DeleteFour.label,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at h0 h1 h2

theorem card_le_n_add_one_of_selectedLabels_card_le_one
    {n : ℕ} {B : Set (Element n)} {J : Finset B}
    (hremoved : Family.four n ∉ B)
    (hJ : J.Nonempty) (hcard : (selectedLabels J).card ≤ 1) :
    J.card ≤ n + 1 := by
  obtain ⟨b, hb⟩ := hJ
  let l := labelClass n b
  have hsubset : actualSet J ⊆ survivingFiber n l := by
    rintro e ⟨c, hc, rfl⟩
    refine ⟨fun h ↦ hremoved (h ▸ c.property), ?_⟩
    have hcl := label_mem_selectedLabels hc
    have hbl := label_mem_selectedLabels hb
    exact Finset.card_le_one.mp hcard _ hcl _ hbl
  rw [← ncard_actualSet J]
  exact (Set.ncard_le_ncard hsubset (Set.toFinite _)).trans
    (survivingFiber_ncard_le n l)

def carrierPreimage (n : ℕ) (C : QuotientCarrierAudit.DeleteFour.Carrier) :
    Set (Element n) :=
  {e | e ≠ Family.four n ∧
    labelClass n e ∈ QuotientCarrierAudit.DeleteFour.carrier C}

theorem carrierPreimage_planeABThree (n : ℕ) :
    carrierPreimage n .planeABThree = Family.H3 n := by
  ext e
  cases e with
  | special s => fin_cases s <;> simp [carrierPreimage, labelClass,
      specialLabelClass, QuotientCarrierAudit.DeleteFour.carrier,
      Family.H3, Family.X, Family.Y, Family.blockSet, Family.three, Family.four]
  | block b i => fin_cases b <;> simp [carrierPreimage, labelClass,
      blockLabelClass, QuotientCarrierAudit.DeleteFour.carrier,
      Family.H3, Family.X, Family.Y, Family.blockSet, Family.four]

theorem carrierPreimage_planeACTwo (n : ℕ) :
    carrierPreimage n .planeACTwo = Family.H2 n := by
  ext e
  cases e with
  | special s => fin_cases s <;> simp [carrierPreimage, labelClass,
      specialLabelClass, QuotientCarrierAudit.DeleteFour.carrier,
      Family.H2, Family.X, Family.Z, Family.blockSet, Family.two, Family.four]
  | block b i => fin_cases b <;> simp [carrierPreimage, labelClass,
      blockLabelClass, QuotientCarrierAudit.DeleteFour.carrier,
      Family.H2, Family.X, Family.Z, Family.blockSet, Family.four]

theorem carrierPreimage_planeBCOne (n : ℕ) :
    carrierPreimage n .planeBCOne = Family.H1 n := by
  ext e
  cases e with
  | special s => fin_cases s <;> simp [carrierPreimage, labelClass,
      specialLabelClass, QuotientCarrierAudit.DeleteFour.carrier,
      Family.H1, Family.Y, Family.Z, Family.blockSet, Family.one, Family.four]
  | block b i => fin_cases b <;> simp [carrierPreimage, labelClass,
      blockLabelClass, QuotientCarrierAudit.DeleteFour.carrier,
      Family.H1, Family.Y, Family.Z, Family.blockSet, Family.four]

theorem carrierPreimage_planeOneTwoThree (n : ℕ) :
    carrierPreimage n .planeOneTwoThree = Family.T n := by
  ext e
  cases e with
  | special s => fin_cases s <;> simp [carrierPreimage, labelClass,
      specialLabelClass, QuotientCarrierAudit.DeleteFour.carrier,
      Family.T, Family.four]
  | block b i => fin_cases b <;> simp [carrierPreimage, labelClass,
      blockLabelClass, QuotientCarrierAudit.DeleteFour.carrier,
      Family.T, Family.four]

theorem carrierPreimage_pairAOne (n : ℕ) :
    carrierPreimage n .pairAOne = {Family.one n} ∪ Family.X n := by
  ext e
  cases e with
  | special s => fin_cases s <;> simp [carrierPreimage, labelClass,
      specialLabelClass, QuotientCarrierAudit.DeleteFour.carrier,
      Family.X, Family.blockSet, Family.one, Family.four]
  | block b i => fin_cases b <;> simp [carrierPreimage, labelClass,
      blockLabelClass, QuotientCarrierAudit.DeleteFour.carrier,
      Family.X, Family.blockSet, Family.four]

theorem carrierPreimage_pairBTwo (n : ℕ) :
    carrierPreimage n .pairBTwo = {Family.two n} ∪ Family.Y n := by
  ext e
  cases e with
  | special s => fin_cases s <;> simp [carrierPreimage, labelClass,
      specialLabelClass, QuotientCarrierAudit.DeleteFour.carrier,
      Family.Y, Family.blockSet, Family.two, Family.four]
  | block b i => fin_cases b <;> simp [carrierPreimage, labelClass,
      blockLabelClass, QuotientCarrierAudit.DeleteFour.carrier,
      Family.Y, Family.blockSet, Family.four]

theorem carrierPreimage_pairCThree (n : ℕ) :
    carrierPreimage n .pairCThree = {Family.three n} ∪ Family.Z n := by
  ext e
  cases e with
  | special s => fin_cases s <;> simp [carrierPreimage, labelClass,
      specialLabelClass, QuotientCarrierAudit.DeleteFour.carrier,
      Family.Z, Family.blockSet, Family.three, Family.four]
  | block b i => fin_cases b <;> simp [carrierPreimage, labelClass,
      blockLabelClass, QuotientCarrierAudit.DeleteFour.carrier,
      Family.Z, Family.blockSet, Family.four]

theorem base_not_subset_carrierPreimage {n : ℕ} {B : Set (Element n)}
    (hB : ((Family.MI n) ＼ {Family.four n}).IsBase B)
    (C : QuotientCarrierAudit.DeleteFour.Carrier) :
    ¬ B ⊆ carrierPreimage n C := by
  rcases (Family.delete_four_isBase_iff n B).mp hB with
    ⟨-, hcard, hT, hH1, hH2, hH3⟩
  intro hsub
  cases C with
  | planeABThree => exact hH3 (by simpa [carrierPreimage_planeABThree] using hsub)
  | planeACTwo => exact hH2 (by simpa [carrierPreimage_planeACTwo] using hsub)
  | planeBCOne => exact hH1 (by simpa [carrierPreimage_planeBCOne] using hsub)
  | planeOneTwoThree =>
      have hBT : B ⊆ Family.T n := by
        simpa [carrierPreimage_planeOneTwoThree] using hsub
      have hle := Set.ncard_le_ncard hBT (Set.toFinite _)
      have hn : n = 0 := by
        rw [hcard, Family.ncard_T] at hle
        omega
      have heq : B = Family.T n :=
        Set.eq_of_subset_of_ncard_le hBT
          (by simp [hcard, Family.ncard_T, hn]) (Set.toFinite _)
      exact hT (by rw [heq])
  | pairAOne =>
      have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [carrierPreimage_pairAOne, Set.ncard_union_eq] at hle
      · simp at hle
        omega
      · rw [Set.disjoint_left]
        intro e he hX
        have heq : e = Family.one n := by simpa using he
        subst e
        exact Family.special_not_mem_blockSet n 0 0 hX
  | pairBTwo =>
      have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [carrierPreimage_pairBTwo, Set.ncard_union_eq] at hle
      · simp at hle
        omega
      · rw [Set.disjoint_left]
        intro e he hY
        have heq : e = Family.two n := by simpa using he
        subst e
        exact Family.special_not_mem_blockSet n 1 1 hY
  | pairCThree =>
      have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [carrierPreimage_pairCThree, Set.ncard_union_eq] at hle
      · simp at hle
        omega
      · rw [Set.disjoint_left]
        intro e he hZ
        have heq : e = Family.three n := by simpa using he
        subst e
        exact Family.special_not_mem_blockSet n 2 2 hZ

/-! ### Pure-special selectors -/

def specialValue (n : ℕ) : Element n → Templates.DeleteFour.Special
  | .special s => ![.One, .Two, .Three, .One] s
  | .block _ _ => .One

def actualSpecial (n : ℕ) : Templates.DeleteFour.Special → Element n
  | .One => Family.one n
  | .Two => Family.two n
  | .Three => Family.three n

@[simp] theorem specialValue_actualSpecial (n : ℕ)
    (s : Templates.DeleteFour.Special) :
    specialValue n (actualSpecial n s) = s := by
  cases s <;> rfl

@[simp] theorem blockClass_actualSpecial (n : ℕ)
    (s : Templates.DeleteFour.Special) :
    TemplateInstances.DeleteFour.blockClass n (actualSpecial n s) = none := by
  cases s <;> rfl

theorem actualSpecial_ne_four (n : ℕ) (s : Templates.DeleteFour.Special) :
    actualSpecial n s ≠ Family.four n := by
  cases s <;> simp [actualSpecial, Family.one, Family.two, Family.three,
    Family.four]

theorem specialClass_eq_some_specialValue_of_blockClass_eq_none
    {n : ℕ} {e : Element n}
    (he : e ≠ Family.four n)
    (hBlock : TemplateInstances.DeleteFour.blockClass n e = none) :
    TemplateInstances.DeleteFour.specialClass n e = some (specialValue n e) := by
  cases e with
  | special s =>
      fin_cases s
      · rfl
      · rfl
      · rfl
      · exact (he rfl).elim
  | block b i =>
      simp [TemplateInstances.DeleteFour.blockClass,
        TemplateInstances.DeleteFour.blockKind] at hBlock

theorem specialValue_injective_of_blockClass_eq_none
    {n : ℕ} {e f : Element n}
    (he : e ≠ Family.four n) (hf : f ≠ Family.four n)
    (heBlock : TemplateInstances.DeleteFour.blockClass n e = none)
    (hfBlock : TemplateInstances.DeleteFour.blockClass n f = none)
    (hValue : specialValue n e = specialValue n f) : e = f := by
  cases e with
  | special se =>
      cases f with
      | special sf =>
          fin_cases se <;> fin_cases sf <;>
            simp_all [specialValue, Family.four]
      | block bf i =>
          simp [TemplateInstances.DeleteFour.blockClass,
            TemplateInstances.DeleteFour.blockKind] at hfBlock
  | block be i =>
      simp [TemplateInstances.DeleteFour.blockClass,
        TemplateInstances.DeleteFour.blockKind] at heBlock

theorem eq_actualSpecial_specialValue_of_blockClass_eq_none
    {n : ℕ} {e : Element n}
    (he : e ≠ Family.four n)
    (hBlock : TemplateInstances.DeleteFour.blockClass n e = none) :
    e = actualSpecial n (specialValue n e) := by
  apply specialValue_injective_of_blockClass_eq_none he
    (actualSpecial_ne_four n _) hBlock (blockClass_actualSpecial n _)
  simp

theorem card_le_finrank_subspaceSum_of_forall_blockClass_none
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hB : ((Family.MI n) ＼ {Family.four n}).IsBase B)
    (J : Finset B)
    (hPure : ∀ i ∈ J,
      TemplateInstances.DeleteFour.blockClass n (i : Element n) = none) :
    J.card ≤ Module.finrank ℚ
      (subspaceSum ℚ
        (fun b : B ↦ TemplateInstances.DeleteFour.ambientSubspace n b) J) := by
  rcases (Family.delete_four_isBase_iff n B).mp hB with
    ⟨hGround, -, hNotT, -, -, -⟩
  have hFourB : Family.four n ∉ B := by
    intro hFour
    exact (hGround hFour).2 (by simp)
  let S : Set Templates.DeleteFour.Special :=
    Set.range (fun j : J ↦ specialValue n (j.1 : Element n))
  have special_mem_B (s : Templates.DeleteFour.Special) (hs : s ∈ S) :
      actualSpecial n s ∈ B := by
    obtain ⟨j, rfl⟩ := hs
    have hpure := hPure j.1 j.2
    rw [← eq_actualSpecial_specialValue_of_blockClass_eq_none
      (fun he ↦ hFourB (he ▸ j.1.property)) hpure]
    exact j.1.property
  have hSpecialT :
      ¬ ({.One, .Two, .Three} : Set Templates.DeleteFour.Special) ⊆ S := by
    intro hT
    apply hNotT
    intro e he
    simp only [Family.T, Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl
    · exact special_mem_B .One (hT (by simp))
    · exact special_mem_B .Two (hT (by simp))
    · exact special_mem_B .Three (hT (by simp))
  have hSpecialLinear : LinearIndependent ℚ
      (fun s : S ↦ Templates.DeleteFour.special n s) :=
    SpecialGeometry.DeleteFour.linearIndependent_special_of_not_core_triple_subset
      n hSpecialT
  let f : J → S := fun j ↦
    ⟨specialValue n (j.1 : Element n), Set.mem_range_self j⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply Subtype.ext
    apply specialValue_injective_of_blockClass_eq_none
      (fun he ↦ hFourB (he ▸ i.1.property))
      (fun he ↦ hFourB (he ▸ j.1.property))
      (hPure i.1 i.2) (hPure j.1 j.2)
    exact congrArg Subtype.val hij
  have hActualLinear : LinearIndependent ℚ
      (fun j : J ↦ Templates.DeleteFour.special n
        (specialValue n (j.1 : Element n))) := by
    simpa [f, Function.comp_def] using hSpecialLinear.comp f hf
  let W := subspaceSum ℚ
    (fun b : B ↦ TemplateInstances.DeleteFour.ambientSubspace n b) J
  let v : J → W := fun j ↦
    ⟨Templates.DeleteFour.special n (specialValue n (j.1 : Element n)), by
      apply (Finset.le_sup
        (f := fun b : B ↦ TemplateInstances.DeleteFour.ambientSubspace n b)
        j.2)
      have hpure := hPure j.1 j.2
      have hspecial := specialClass_eq_some_specialValue_of_blockClass_eq_none
        (fun he ↦ hFourB (he ▸ j.1.property)) hpure
      simp [TemplateInstances.DeleteFour.ambientSubspace,
        TemplateInstances.ambientSubspaceOf, hpure, hspecial]⟩
  have hv : LinearIndependent ℚ v := by
    apply LinearIndependent.of_comp W.subtype
    simpa [v, Function.comp_def] using hActualLinear
  simpa [W] using hv.fintype_card_le_finrank

theorem card_le_finrank_subspaceSum_of_exists_block
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hB : ((Family.MI n) ＼ {Family.four n}).IsBase B)
    (J : Finset B)
    (hBlock : ∃ i ∈ J, ∃ b,
      TemplateInstances.DeleteFour.blockClass n (i : Element n) = some b) :
    J.card ≤ Module.finrank ℚ
      (subspaceSum ℚ
        (fun b : B ↦ TemplateInstances.DeleteFour.ambientSubspace n b) J) := by
  rcases (Family.delete_four_isBase_iff n B).mp hB with
    ⟨hGround, hBcard, -, -, -, -⟩
  have hFourB : Family.four n ∉ B := by
    intro hFour
    exact (hGround hFour).2 (by simp)
  let R : Submodule ℚ
      (Templates.QuotientSpace Templates.DeleteFour.quotientDim) :=
    Submodule.span ℚ
      ((quotientLabel n ∘ fun b : B ↦ (b : Element n)) '' (J : Set B))
  have hdim : Module.finrank ℚ
      (subspaceSum ℚ
        (fun b : B ↦ TemplateInstances.DeleteFour.ambientSubspace n b) J) =
      n + Module.finrank ℚ R := by
    simpa [TemplateInstances.DeleteFour.ambientSubspace, quotientLabel, R] using
      (ClassifiedGeometry.finrank_subspaceSum_ambientSubspaceOf
        Templates.DeleteFour.blockLabel (Templates.DeleteFour.special n)
        (TemplateInstances.DeleteFour.blockClass n)
        (TemplateInstances.DeleteFour.specialClass n)
        (fun b : B ↦ (b : Element n)) hBlock)
  rw [hdim]
  by_contra hCapacity
  have hlt : n + Module.finrank ℚ R < J.card :=
    Nat.lt_of_not_ge hCapacity
  have hJle : J.card ≤ n + 3 := card_selector_le_of_ncard hBcard J
  have hRankLe : Module.finrank ℚ R ≤ 2 := by omega
  let S : Finset Label := selectedLabels J
  have hSpan : R = Submodule.span ℚ
      (QuotientCarrierAudit.DeleteFour.label '' (S : Set Label)) := by
    dsimp [R, S]
    rw [quotient_image_eq hFourB]
  by_cases hRankZero : Module.finrank ℚ R = 0
  · have hRbot : R = ⊥ := Submodule.finrank_eq_zero.mp hRankZero
    obtain ⟨i, hi, b, hib⟩ := hBlock
    have hqMem : quotientLabel n (i : Element n) ∈ R :=
      Submodule.subset_span ⟨i, hi, rfl⟩
    have hqZero : quotientLabel n (i : Element n) = 0 := by
      rw [hRbot] at hqMem
      simpa using hqMem
    have hLabelZero : QuotientCarrierAudit.DeleteFour.label
        (labelClass n (i : Element n)) = 0 := by
      rw [← quotientLabel_eq_label n
        (fun he ↦ hFourB (he ▸ i.property))]
      exact hqZero
    exact label_ne_zero _ hLabelZero
  · by_cases hRankOne : Module.finrank ℚ R ≤ 1
    · have hScard : S.card ≤ 1 :=
        (QuotientCarrierAudit.DeleteFour.finrank_le_one_iff_card_le_one S).mp
          (by rw [← hSpan]; exact hRankOne)
      obtain ⟨i, hi, -, -⟩ := hBlock
      have hJnonempty : J.Nonempty := ⟨i, hi⟩
      have hJsmall := card_le_n_add_one_of_selectedLabels_card_le_one
        hFourB hJnonempty hScard
      omega
    · have hRankTwo : Module.finrank ℚ R = 2 := by omega
      have hJcard : J.card = n + 3 := by omega
      have hJuniv : J = Finset.univ :=
        selector_eq_univ_of_card_eq hBcard hJcard
      obtain ⟨C, hSC⟩ :=
        QuotientCarrierAudit.DeleteFour.contained_in_carrier_of_finrank_le_two S
          (by rw [← hSpan, hRankTwo])
      have hBcarrier : B ⊆ carrierPreimage n C := by
        intro e heB
        let b : B := ⟨e, heB⟩
        have hbJ : b ∈ J := by simp [hJuniv]
        exact ⟨fun he ↦ hFourB (he ▸ heB),
          hSC (label_mem_selectedLabels hbJ)⟩
      exact base_not_subset_carrierPreimage hB C hBcarrier

theorem hasRadoCapacity_ambient_of_isBase
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hB : ((Family.MI n) ＼ {Family.four n}).IsBase B) :
    HasRadoCapacity ℚ
      (fun b : B ↦ TemplateInstances.DeleteFour.ambientSubspace n b) := by
  classical
  intro J
  by_cases hBlock : ∃ i ∈ J, ∃ b,
      TemplateInstances.DeleteFour.blockClass n (i : Element n) = some b
  · exact card_le_finrank_subspaceSum_of_exists_block hB J hBlock
  · apply card_le_finrank_subspaceSum_of_forall_blockClass_none hB J
    intro i hi
    cases hClass : TemplateInstances.DeleteFour.blockClass n
        (i : Element n) with
    | none => rfl
    | some b => exact (hBlock ⟨i, hi, b, hClass⟩).elim

theorem hasRadoCapacity_L_of_isBase
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hB : ((Family.MI n) ＼ {Family.four n}).IsBase B) :
    HasRadoCapacity ℚ (fun b : B ↦ TemplateInstances.DeleteFour.L n b) :=
  (TemplateInstances.DeleteFour.hasRadoCapacity_L_iff_ambient B).mpr
    (hasRadoCapacity_ambient_of_isBase hB)

/-! ### Forced dependence of full-size nonbases -/

theorem ambientSubspace_le_corePlus_carrier
    {n : ℕ} {e : Element n}
    (C : QuotientCarrierAudit.DeleteFour.Carrier)
    (he : e ∈ carrierPreimage n C) :
    TemplateInstances.DeleteFour.ambientSubspace n e ≤
      Templates.corePlus n Templates.DeleteFour.quotientDim
        (Submodule.span ℚ
          (QuotientCarrierAudit.DeleteFour.label ''
            (QuotientCarrierAudit.DeleteFour.carrier C : Set Label))) := by
  let P : Submodule ℚ
      (Templates.QuotientSpace Templates.DeleteFour.quotientDim) :=
    Submodule.span ℚ
      (QuotientCarrierAudit.DeleteFour.label ''
        (QuotientCarrierAudit.DeleteFour.carrier C : Set Label))
  have hLabel : quotientLabel n e ∈ P := by
    apply Submodule.subset_span
    exact ⟨labelClass n e, he.2,
      (quotientLabel_eq_label n he.1).symm⟩
  have hLine : ℚ ∙ quotientLabel n e ≤ P := by
    rw [Submodule.span_singleton_le_iff_mem]
    exact hLabel
  intro x hx
  apply (Templates.mem_corePlus_iff n Templates.DeleteFour.quotientDim P x).2
  apply hLine
  have hMapMem : Templates.quotientProjection n
      Templates.DeleteFour.quotientDim x ∈
      (TemplateInstances.DeleteFour.ambientSubspace n e).map
        (Templates.quotientProjection n Templates.DeleteFour.quotientDim) :=
    ⟨x, hx, rfl⟩
  have hMapEq :
      (TemplateInstances.DeleteFour.ambientSubspace n e).map
          (Templates.quotientProjection n Templates.DeleteFour.quotientDim) =
        ℚ ∙ quotientLabel n e := by
    simpa [TemplateInstances.DeleteFour.ambientSubspace, quotientLabel] using
      (ClassifiedGeometry.map_ambientSubspaceOf_eq_span_quotientLabelOf
        Templates.DeleteFour.blockLabel (Templates.DeleteFour.special n)
        (TemplateInstances.DeleteFour.blockClass n)
        (TemplateInstances.DeleteFour.specialClass n) e)
  rw [hMapEq] at hMapMem
  exact hMapMem

theorem finrank_subspaceSum_ambient_univ_le_n_add_two_of_subset_carrier
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (C : QuotientCarrierAudit.DeleteFour.Carrier)
    (hBC : B ⊆ carrierPreimage n C) :
    Module.finrank ℚ
      (subspaceSum ℚ
        (fun b : B ↦ TemplateInstances.DeleteFour.ambientSubspace n b)
        Finset.univ) ≤ n + 2 := by
  let P : Submodule ℚ
      (Templates.QuotientSpace Templates.DeleteFour.quotientDim) :=
    Submodule.span ℚ
      (QuotientCarrierAudit.DeleteFour.label ''
        (QuotientCarrierAudit.DeleteFour.carrier C : Set Label))
  have hSum : subspaceSum ℚ
      (fun b : B ↦ TemplateInstances.DeleteFour.ambientSubspace n b)
      Finset.univ ≤ Templates.corePlus n Templates.DeleteFour.quotientDim P := by
    rw [subspaceSum, Finset.sup_le_iff]
    intro b hb
    exact ambientSubspace_le_corePlus_carrier C (hBC b.property)
  calc
    Module.finrank ℚ
        (subspaceSum ℚ
          (fun b : B ↦ TemplateInstances.DeleteFour.ambientSubspace n b)
          Finset.univ) ≤
        Module.finrank ℚ
          (Templates.corePlus n Templates.DeleteFour.quotientDim P) :=
      Submodule.finrank_mono hSum
    _ = n + Module.finrank ℚ P :=
      Templates.finrank_corePlus n Templates.DeleteFour.quotientDim P
    _ ≤ n + 2 := Nat.add_le_add_left
      (QuotientCarrierAudit.DeleteFour.carrier_finrank_le_two C) n

theorem finrank_subspaceSum_L_univ_le_n_add_two_of_subset_carrier
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (C : QuotientCarrierAudit.DeleteFour.Carrier)
    (hBC : B ⊆ carrierPreimage n C) :
    Module.finrank ℚ
      (subspaceSum ℚ (fun b : B ↦ TemplateInstances.DeleteFour.L n b)
        Finset.univ) ≤ n + 2 := by
  have hCoordinateDim : Module.finrank ℚ
      (subspaceSum ℚ (fun b : B ↦ TemplateInstances.DeleteFour.L n b)
        Finset.univ) =
      Module.finrank ℚ
        (subspaceSum ℚ
          (fun b : B ↦ TemplateInstances.DeleteFour.ambientSubspace n b)
          Finset.univ) := by
    simpa [TemplateInstances.DeleteFour.L] using
      (TemplateInstances.finrank_subspaceSum_coordinateSubspaceOf
        (TemplateInstances.DeleteFour.ambientSubspace n)
        (fun b : B ↦ (b : Element n)) Finset.univ)
  rw [hCoordinateDim]
  exact finrank_subspaceSum_ambient_univ_le_n_add_two_of_subset_carrier C hBC

theorem not_hasRadoCapacity_L_of_subset_carrier
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hBcard : B.ncard = n + 3)
    (C : QuotientCarrierAudit.DeleteFour.Carrier)
    (hBC : B ⊆ carrierPreimage n C) :
    ¬ HasRadoCapacity ℚ
      (fun b : B ↦ TemplateInstances.DeleteFour.L n b) := by
  apply not_hasRadoCapacity_of_finrank_lt_card (Finset.univ : Finset B)
  have hfin :=
    finrank_subspaceSum_L_univ_le_n_add_two_of_subset_carrier C hBC
  have hcard : (Finset.univ : Finset B).card = n + 3 := by
    simp [← Nat.card_eq_fintype_card, hBcard]
  omega

theorem not_linearIndependent_of_subset_carrier
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hBcard : B.ncard = n + 3)
    (C : QuotientCarrierAudit.DeleteFour.Carrier)
    (hBC : B ⊆ carrierPreimage n C)
    (w : Element n → (Fin (n + Templates.DeleteFour.quotientDim) → ℚ))
    (hwL : ∀ e, w e ∈ TemplateInstances.DeleteFour.L n e) :
    ¬ LinearIndependent ℚ (fun b : B ↦ w b) := by
  apply not_linearIndependent_of_not_hasRadoCapacity
    (not_hasRadoCapacity_L_of_subset_carrier hBcard C hBC)
  exact fun b : B ↦ hwL b

/-- Coordinate form of the fixed relation `q₃ = q₁ - q₂`. -/
theorem q_three_eq_q_one_sub_q_two (n : ℕ) :
    TemplateInstances.DeleteFour.q n (Family.three n) =
      TemplateInstances.DeleteFour.q n (Family.one n) -
        TemplateInstances.DeleteFour.q n (Family.two n) := by
  simpa [TemplateInstances.DeleteFour.q,
    TemplateInstances.coordinateFixedVectorOf,
    TemplateInstances.DeleteFour.ambientFixedVector,
    TemplateInstances.ambientFixedVectorOf,
    TemplateInstances.DeleteFour.specialClass,
    TemplateInstances.DeleteFour.specialKind] using
      congrArg (TemplateInstances.ambientCoordinateEquiv n
        Templates.DeleteFour.quotientDim)
        (Templates.DeleteFour.special_relation n)

theorem not_linearIndependent_of_T_subset
    {n : ℕ} {B : Set (Element n)}
    (hT : Family.T n ⊆ B)
    {w : Element n → (Fin (n + Templates.DeleteFour.quotientDim) → ℚ)}
    (hwq : ∀ e ∈ TemplateInstances.DeleteFour.fixedElements n,
      w e = TemplateInstances.DeleteFour.q n e) :
    ¬ LinearIndependent ℚ (fun b : B ↦ w b) := by
  intro hLinear
  have hOneB : Family.one n ∈ B := hT (by simp [Family.T])
  have hTwoB : Family.two n ∈ B := hT (by simp [Family.T])
  have hThreeB : Family.three n ∈ B := hT (by simp [Family.T])
  have hOneFixed : Family.one n ∈
      TemplateInstances.DeleteFour.fixedElements n := ⟨.One, rfl⟩
  have hTwoFixed : Family.two n ∈
      TemplateInstances.DeleteFour.fixedElements n := ⟨.Two, rfl⟩
  have hThreeFixed : Family.three n ∈
      TemplateInstances.DeleteFour.fixedElements n := ⟨.Three, rfl⟩
  have hwOne := hwq (Family.one n) hOneFixed
  have hwTwo := hwq (Family.two n) hTwoFixed
  have hwThree := hwq (Family.three n) hThreeFixed
  have hwRelation : w (Family.three n) =
      w (Family.one n) - w (Family.two n) := by
    rw [hwOne, hwTwo, hwThree]
    exact q_three_eq_q_one_sub_q_two n
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
  let g : Fin 3 → ℚ := ![1, -1, -1]
  have hsum : ∑ i, g i • w (t i) = 0 := by
    simp [g, t, Fin.sum_univ_succ]
    change w (Family.one n) +
      (-w (Family.two n) + -w (Family.three n)) = 0
    rw [hwRelation]
    abel
  have hcoeff := (Fintype.linearIndependent_iff.mp hThreeLinear) g hsum 0
  norm_num [g] at hcoeff

/-- Every full-size ground subset which is not a basis after deleting `4` is
forced dependent.  The special-triple failure uses the prescribed column
relation; the three hyperplane failures use quotient-carrier dimension. -/
theorem nonbase_forced_dependence
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hGround : B ⊆ ((Family.MI n) ＼ {Family.four n}).E)
    (hBcard : B.ncard = n + 3)
    (hNotBase : ¬ ((Family.MI n) ＼ {Family.four n}).IsBase B)
    (w : Element n → (Fin (n + Templates.DeleteFour.quotientDim) → ℚ))
    (hwL : ∀ e, w e ∈ TemplateInstances.DeleteFour.L n e)
    (hwq : ∀ e ∈ TemplateInstances.DeleteFour.fixedElements n,
      w e = TemplateInstances.DeleteFour.q n e) :
    ¬ LinearIndependent ℚ (fun b : B ↦ w b) := by
  by_cases hT : Family.T n ⊆ B
  · exact not_linearIndependent_of_T_subset hT hwq
  by_cases hH1 : B ⊆ Family.H1 n
  · apply not_linearIndependent_of_subset_carrier hBcard .planeBCOne
      (by rw [carrierPreimage_planeBCOne]; exact hH1) w hwL
  by_cases hH2 : B ⊆ Family.H2 n
  · apply not_linearIndependent_of_subset_carrier hBcard .planeACTwo
      (by rw [carrierPreimage_planeACTwo]; exact hH2) w hwL
  by_cases hH3 : B ⊆ Family.H3 n
  · apply not_linearIndependent_of_subset_carrier hBcard .planeABThree
      (by rw [carrierPreimage_planeABThree]; exact hH3) w hwL
  exfalso
  apply hNotBase
  exact (Family.delete_four_isBase_iff n B).mpr
    ⟨hGround, hBcard, hT, hH1, hH2, hH3⟩

/-! ### Representation endpoint -/

theorem rationallyRepresentable (n : ℕ) :
    RationallyRepresentable ((Family.MI n) ＼ {Family.four n}) := by
  refine ⟨n + 3, ?_⟩
  have hReference : ∃ B₀ : Set (Element n),
      ((Family.MI n) ＼ {Family.four n}).IsBase B₀ ∧
        B₀.ncard = n + 3 := by
    let B₀ := Family.basisWithoutFour n
    have hOriginal : (Family.MI n).IsBase B₀ :=
      Family.basisWithoutFour_isBase n
    have hDisjoint : Disjoint B₀ {Family.four n} := by
      rw [Set.disjoint_singleton_right]
      exact Family.four_not_mem_basisWithoutFour n
    have hDeletion : ((Family.MI n) ＼ {Family.four n}).IsBase B₀ := by
      simpa using ((Family.four_singleton_coindep n).delete_isBase_iff
        (B := B₀)).2 ⟨hOriginal, hDisjoint⟩
    exact ⟨B₀, hDeletion,
      Family.IsBase.ncard_eq n (Family.basisWithoutFour_isBase n)⟩
  obtain ⟨v, hvRep, -, -⟩ :=
    exists_representation_of_subspace_base_audit
      (TemplateInstances.DeleteFour.L n)
      (TemplateInstances.DeleteFour.fixedElements n)
      (TemplateInstances.DeleteFour.q n)
      (fun e he ↦ TemplateInstances.DeleteFour.q_mem_L he)
      hReference
      (fun B hB _ ↦ by
        letI := B.toFinite.fintype
        exact
          TemplateInstances.DeleteFour.feasible_assignment_on_candidate_of_ambientCapacity
            B (hasRadoCapacity_ambient_of_isBase hB))
      (fun B hGround hCard hNotBase w hwL hwq ↦ by
        letI := B.toFinite.fintype
        exact nonbase_forced_dependence
          hGround hCard hNotBase w hwL hwq)
  exact ⟨v, hvRep⟩

end DeleteFour

end DeletionOtherCapacity

/-- Rational representability of the deletion of the distinguished element
`1`. -/
theorem delete_one_rationallyRepresentable (n : ℕ) :
    RationallyRepresentable ((Family.MI n) ＼ {Family.one n}) :=
  DeletionOtherCapacity.DeleteOne.rationallyRepresentable n

/-- Rational representability of the deletion of the distinguished element
`4`. -/
theorem delete_four_rationallyRepresentable (n : ℕ) :
    RationallyRepresentable ((Family.MI n) ＼ {Family.four n}) :=
  DeletionOtherCapacity.DeleteFour.rationallyRepresentable n

end BlandJensenFormal.BlandJensenMI
