import BlandJensenFormal.BlandJensenMI.Minors
import BlandJensenFormal.BlandJensenMI.TemplateInstances
import BlandJensenFormal.BlandJensenMI.QuotientCarrierAudit
import BlandJensenFormal.BlandJensenMI.CapacityHelpers
import BlandJensenFormal.BlandJensenMI.RepresentationCompiler
import BlandJensenFormal.BlandJensenMI.ClassifiedGeometry
import BlandJensenFormal.BlandJensenMI.SpecialGeometry

/-!
# Capacity audits for the three deletion templates

This file connects the exact deletion-basis predicates to the common-core
subspace templates.  It contains no bounded enumeration in the parameter
`n`: all finite computation concerns only the fixed two- and
three-dimensional quotient-label configurations.
-/

namespace BlandJensenFormal.BlandJensenMI.DeletionCapacity

open Function Set Submodule
open scoped Matroid

namespace DeleteX

abbrev Label := QuotientCarrierAudit.DeleteX.Label

def blockLabelClass : Fin 3 → Label := ![.A, .B, .C]

def specialLabelClass : Fin 4 → Label :=
  ![.One, .Two, .Three, .Four]

/-- Fixed finite label attached to every actual element.  The deleted element
is assigned its old block label; it never occurs in a deletion basis. -/
def labelClass (n : ℕ) : Element n → Label
  | .special s => specialLabelClass s
  | .block b _ => blockLabelClass b

def quotientLabel (n : ℕ) :
    Element n → Templates.QuotientSpace Templates.DeleteX.quotientDim :=
  ClassifiedGeometry.quotientLabelOf
    Templates.DeleteX.blockLabel (Templates.DeleteX.special n)
    (TemplateInstances.DeleteX.blockClass n)
    (TemplateInstances.DeleteX.specialClass n)

theorem quotientLabel_eq_label (n : ℕ) {e : Element n}
    (he : e ≠ Family.x0 n) :
    quotientLabel n e = QuotientCarrierAudit.DeleteX.label (labelClass n e) := by
  cases e with
  | special s =>
      fin_cases s <;> rfl
  | block b i =>
      fin_cases b
      · have hi : i ≠ 0 := by
          intro hi
          apply he
          subst i
          rfl
        simp [quotientLabel, ClassifiedGeometry.quotientLabelOf,
          TemplateInstances.DeleteX.blockClass,
          TemplateInstances.DeleteX.removedElement,
          TemplateInstances.DeleteX.blockKind,
          labelClass, blockLabelClass, Family.x0, hi,
          Templates.DeleteX.blockLabel, Templates.DeleteX.quotientLabel,
          QuotientCarrierAudit.DeleteX.label]
      · simp [quotientLabel, ClassifiedGeometry.quotientLabelOf,
          TemplateInstances.DeleteX.blockClass,
          TemplateInstances.DeleteX.removedElement,
          TemplateInstances.DeleteX.blockKind,
          labelClass, blockLabelClass, Family.x0,
          Templates.DeleteX.blockLabel, Templates.DeleteX.quotientLabel,
          QuotientCarrierAudit.DeleteX.label]
      · simp [quotientLabel, ClassifiedGeometry.quotientLabelOf,
          TemplateInstances.DeleteX.blockClass,
          TemplateInstances.DeleteX.removedElement,
          TemplateInstances.DeleteX.blockKind,
          labelClass, blockLabelClass, Family.x0,
          Templates.DeleteX.blockLabel, Templates.DeleteX.quotientLabel,
          QuotientCarrierAudit.DeleteX.label]

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

theorem selector_eq_univ_of_card_eq {n d : ℕ} {B : Set (Element n)}
    [Fintype B] (hBcard : B.ncard = d) {J : Finset B}
    (hJcard : J.card = d) : J = Finset.univ := by
  apply Finset.eq_univ_of_card
  simpa [← Nat.card_eq_fintype_card, hBcard] using hJcard

def selectedLabels {n : ℕ} {B : Set (Element n)} (J : Finset B) :
    Finset Label := J.image (fun b : B ↦ labelClass n (b : Element n))

theorem label_mem_selectedLabels {n : ℕ} {B : Set (Element n)}
    {J : Finset B} {b : B} (hb : b ∈ J) :
    labelClass n (b : Element n) ∈ selectedLabels J := by
  exact Finset.mem_image.mpr ⟨b, hb, rfl⟩

theorem quotient_image_eq {n : ℕ} {B : Set (Element n)}
    (hremoved : Family.x0 n ∉ B) (J : Finset B) :
    (quotientLabel n ∘ fun b : B ↦ (b : Element n)) '' (J : Set B) =
      QuotientCarrierAudit.DeleteX.label ''
        (selectedLabels J : Set Label) := by
  ext p
  constructor
  · rintro ⟨b, hb, rfl⟩
    change quotientLabel n b ∈ _
    rw [quotientLabel_eq_label n (fun h ↦ hremoved (h ▸ b.property))]
    exact ⟨labelClass n b, label_mem_selectedLabels hb, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hl
    exact ⟨b, hb, by
      change quotientLabel n (b : Element n) = _
      exact quotientLabel_eq_label n (fun h ↦ hremoved (h ▸ b.property))⟩

theorem labelClass_fiber_ncard_le (n : ℕ) (l : Label) :
    {e : Element n | labelClass n e = l}.ncard ≤ n + 1 := by
  cases l with
  | A =>
      have hset : {e : Element n | labelClass n e = .A} = Family.X n := by
        ext e
        cases e with
        | special s => fin_cases s <;> simp [labelClass, specialLabelClass, Family.X,
            Family.blockSet]
        | block b i => fin_cases b <;> simp [labelClass, blockLabelClass, Family.X,
            Family.blockSet]
      rw [hset, Family.ncard_X]
  | B =>
      have hset : {e : Element n | labelClass n e = .B} = Family.Y n := by
        ext e
        cases e with
        | special s => fin_cases s <;> simp [labelClass, specialLabelClass, Family.Y,
            Family.blockSet]
        | block b i => fin_cases b <;> simp [labelClass, blockLabelClass, Family.Y,
            Family.blockSet]
      rw [hset, Family.ncard_Y]
  | C =>
      have hset : {e : Element n | labelClass n e = .C} = Family.Z n := by
        ext e
        cases e with
        | special s => fin_cases s <;> simp [labelClass, specialLabelClass, Family.Z,
            Family.blockSet]
        | block b i => fin_cases b <;> simp [labelClass, blockLabelClass, Family.Z,
            Family.blockSet]
      rw [hset, Family.ncard_Z]
  | One =>
      have hset : {e : Element n | labelClass n e = .One} = {Family.one n} := by
        ext e
        cases e with
        | special s => fin_cases s <;> simp [labelClass, specialLabelClass,
            Family.one]
        | block b i => fin_cases b <;> simp [labelClass, blockLabelClass,
            Family.one]
      rw [hset]
      simp
  | Two =>
      have hset : {e : Element n | labelClass n e = .Two} = {Family.two n} := by
        ext e
        cases e with
        | special s => fin_cases s <;> simp [labelClass, specialLabelClass,
            Family.two]
        | block b i => fin_cases b <;> simp [labelClass, blockLabelClass,
            Family.two]
      rw [hset]
      simp
  | Three =>
      have hset : {e : Element n | labelClass n e = .Three} = {Family.three n} := by
        ext e
        cases e with
        | special s => fin_cases s <;> simp [labelClass, specialLabelClass,
            Family.three]
        | block b i => fin_cases b <;> simp [labelClass, blockLabelClass,
            Family.three]
      rw [hset]
      simp
  | Four =>
      have hset : {e : Element n | labelClass n e = .Four} = {Family.four n} := by
        ext e
        cases e with
        | special s => fin_cases s <;> simp [labelClass, specialLabelClass,
            Family.four]
        | block b i => fin_cases b <;> simp [labelClass, blockLabelClass,
            Family.four]
      rw [hset]
      simp

theorem label_ne_zero (l : Label) :
    QuotientCarrierAudit.DeleteX.label l ≠ 0 := by
  fin_cases l <;> intro h
  all_goals
    have h0 := congrFun h (0 : Fin 3)
    have h1 := congrFun h (1 : Fin 3)
    have h2 := congrFun h (2 : Fin 3)
    simp [QuotientCarrierAudit.DeleteX.label,
      BlandJensenFormal.MIQuotientLabels.DeleteX.label,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at h0 h1 h2

theorem card_le_n_add_one_of_selectedLabels_card_le_one
    {n : ℕ} {B : Set (Element n)} {J : Finset B}
    (hJ : J.Nonempty) (hcard : (selectedLabels J).card ≤ 1) :
    J.card ≤ n + 1 := by
  obtain ⟨b, hb⟩ := hJ
  let l := labelClass n b
  have hsubset : actualSet J ⊆ {e : Element n | labelClass n e = l} := by
    rintro e ⟨c, hc, rfl⟩
    have hcl := label_mem_selectedLabels hc
    have hbl := label_mem_selectedLabels hb
    exact (Finset.card_le_one.mp hcard _ hcl _ hbl)
  rw [← ncard_actualSet J]
  exact (Set.ncard_le_ncard hsubset <| Set.toFinite _).trans
    (labelClass_fiber_ncard_le n l)

/-- Actual elements whose fixed quotient label lies in a classified
two-dimensional carrier. -/
def carrierPreimage (n : ℕ) (C : QuotientCarrierAudit.DeleteX.Carrier) :
    Set (Element n) :=
  {e | labelClass n e ∈ QuotientCarrierAudit.DeleteX.carrier C}

theorem carrierPreimage_planeABThree (n : ℕ) :
    carrierPreimage n .planeABThree = Family.H3 n := by
  ext e
  cases e with
  | special s => fin_cases s <;> simp [carrierPreimage, labelClass,
      specialLabelClass, QuotientCarrierAudit.DeleteX.carrier,
      Family.H3, Family.X, Family.Y, Family.blockSet]
  | block b i => fin_cases b <;> simp [carrierPreimage, labelClass,
      blockLabelClass, QuotientCarrierAudit.DeleteX.carrier,
      Family.H3, Family.X, Family.Y, Family.blockSet]

theorem carrierPreimage_planeACTwo (n : ℕ) :
    carrierPreimage n .planeACTwo = Family.H2 n := by
  ext e
  cases e with
  | special s => fin_cases s <;> simp [carrierPreimage, labelClass,
      specialLabelClass, QuotientCarrierAudit.DeleteX.carrier,
      Family.H2, Family.X, Family.Z, Family.blockSet]
  | block b i => fin_cases b <;> simp [carrierPreimage, labelClass,
      blockLabelClass, QuotientCarrierAudit.DeleteX.carrier,
      Family.H2, Family.X, Family.Z, Family.blockSet]

theorem carrierPreimage_planeBCOne (n : ℕ) :
    carrierPreimage n .planeBCOne = Family.H1 n := by
  ext e
  cases e with
  | special s => fin_cases s <;> simp [carrierPreimage, labelClass,
      specialLabelClass, QuotientCarrierAudit.DeleteX.carrier,
      Family.H1, Family.Y, Family.Z, Family.blockSet]
  | block b i => fin_cases b <;> simp [carrierPreimage, labelClass,
      blockLabelClass, QuotientCarrierAudit.DeleteX.carrier,
      Family.H1, Family.Y, Family.Z, Family.blockSet]

theorem carrierPreimage_planeBTwoFour (n : ℕ) :
    carrierPreimage n .planeBTwoFour = Family.C2 n := by
  ext e
  cases e with
  | special s => fin_cases s <;> simp [carrierPreimage, labelClass,
      specialLabelClass, QuotientCarrierAudit.DeleteX.carrier,
      Family.C2, Family.Y, Family.blockSet]
  | block b i => fin_cases b <;> simp [carrierPreimage, labelClass,
      blockLabelClass, QuotientCarrierAudit.DeleteX.carrier,
      Family.C2, Family.Y, Family.blockSet]

theorem carrierPreimage_planeCThreeFour (n : ℕ) :
    carrierPreimage n .planeCThreeFour = Family.C3 n := by
  ext e
  cases e with
  | special s => fin_cases s <;> simp [carrierPreimage, labelClass,
      specialLabelClass, QuotientCarrierAudit.DeleteX.carrier,
      Family.C3, Family.Z, Family.blockSet]
  | block b i => fin_cases b <;> simp [carrierPreimage, labelClass,
      blockLabelClass, QuotientCarrierAudit.DeleteX.carrier,
      Family.C3, Family.Z, Family.blockSet]

theorem carrierPreimage_planeOneTwoThree (n : ℕ) :
    carrierPreimage n .planeOneTwoThree = Family.T n := by
  ext e
  cases e with
  | special s => fin_cases s <;> simp [carrierPreimage, labelClass,
      specialLabelClass, QuotientCarrierAudit.DeleteX.carrier, Family.T]
  | block b i => fin_cases b <;> simp [carrierPreimage, labelClass,
      blockLabelClass, QuotientCarrierAudit.DeleteX.carrier, Family.T]

theorem carrierPreimage_pairAOne (n : ℕ) :
    carrierPreimage n .pairAOne = {Family.one n} ∪ Family.X n := by
  ext e
  cases e with
  | special s => fin_cases s <;> simp [carrierPreimage, labelClass,
      specialLabelClass, QuotientCarrierAudit.DeleteX.carrier,
      Family.X, Family.blockSet]
  | block b i => fin_cases b <;> simp [carrierPreimage, labelClass,
      blockLabelClass, QuotientCarrierAudit.DeleteX.carrier,
      Family.X, Family.blockSet]

theorem carrierPreimage_pairAFour (n : ℕ) :
    carrierPreimage n .pairAFour = {Family.four n} ∪ Family.X n := by
  ext e
  cases e with
  | special s => fin_cases s <;> simp [carrierPreimage, labelClass,
      specialLabelClass, QuotientCarrierAudit.DeleteX.carrier,
      Family.X, Family.blockSet]
  | block b i => fin_cases b <;> simp [carrierPreimage, labelClass,
      blockLabelClass, QuotientCarrierAudit.DeleteX.carrier,
      Family.X, Family.blockSet]

theorem carrierPreimage_pairOneFour (n : ℕ) :
    carrierPreimage n .pairOneFour = {Family.one n, Family.four n} := by
  ext e
  cases e with
  | special s => fin_cases s <;> simp [carrierPreimage, labelClass,
      specialLabelClass, QuotientCarrierAudit.DeleteX.carrier]
  | block b i => fin_cases b <;> simp [carrierPreimage, labelClass,
      blockLabelClass, QuotientCarrierAudit.DeleteX.carrier]

theorem carrierPreimage_ncard_le_n_add_two (n : ℕ)
    (C : QuotientCarrierAudit.DeleteX.Carrier)
    (hsmall : C = .pairAOne ∨ C = .pairAFour ∨ C = .pairOneFour) :
    (carrierPreimage n C).ncard ≤ n + 2 := by
  rcases hsmall with rfl | rfl | rfl
  · rw [carrierPreimage_pairAOne,
      Set.ncard_union_eq]
    · simp
      omega
    · rw [Set.disjoint_left]
      intro e he hX
      have heq : e = Family.one n := by simpa using he
      subst e
      exact Family.special_not_mem_blockSet n 0 0 hX
  · rw [carrierPreimage_pairAFour,
      Set.ncard_union_eq]
    · simp
      omega
    · rw [Set.disjoint_left]
      intro e he hX
      have heq : e = Family.four n := by simpa using he
      subst e
      exact Family.special_not_mem_blockSet n 3 0 hX
  · rw [carrierPreimage_pairOneFour]
    simp

/-- A deletion basis cannot be supported on any quotient carrier of rank at
most two.  The six large carriers are exactly the forbidden sets in the
literal basis predicate; the remaining three carriers are too small. -/
theorem base_not_subset_carrierPreimage {n : ℕ} {B : Set (Element n)}
    (hB : ((Family.MI n) ＼ {Family.x0 n}).IsBase B)
    (C : QuotientCarrierAudit.DeleteX.Carrier) :
    ¬ B ⊆ carrierPreimage n C := by
  rcases (Family.delete_x0_isBase_iff n B).mp hB with
    ⟨hground, hcard, hT, hC2, hC3, hH1, hH2, hH3⟩
  have hxB : Family.x0 n ∉ B := by
    intro hx
    exact (hground hx).2 (by simp)
  have subset_diff_x0 {S : Set (Element n)} (hBS : B ⊆ S) :
      B ⊆ S \ {Family.x0 n} := by
    intro e he
    refine ⟨hBS he, ?_⟩
    intro hex
    have heq : e = Family.x0 n := by simpa using hex
    subst e
    exact hxB he
  intro hsub
  cases C with
  | planeABThree =>
      apply hH3
      apply subset_diff_x0
      simpa only [carrierPreimage_planeABThree] using hsub
  | planeACTwo =>
      apply hH2
      apply subset_diff_x0
      simpa only [carrierPreimage_planeACTwo] using hsub
  | planeBCOne =>
      apply hH1
      simpa only [carrierPreimage_planeBCOne] using hsub
  | planeBTwoFour =>
      apply hC2
      exact Set.eq_of_subset_of_ncard_le
        (by simpa only [carrierPreimage_planeBTwoFour] using hsub)
        (by simp [hcard]) (Set.toFinite _)
  | planeCThreeFour =>
      apply hC3
      exact Set.eq_of_subset_of_ncard_le
        (by simpa only [carrierPreimage_planeCThreeFour] using hsub)
        (by simp [hcard]) (Set.toFinite _)
  | planeOneTwoThree =>
      have hBT : B ⊆ Family.T n := by
        simpa only [carrierPreimage_planeOneTwoThree] using hsub
      have hle := Set.ncard_le_ncard hBT (Set.toFinite _)
      have hn : n = 0 := by
        rw [hcard, Family.ncard_T] at hle
        omega
      have heq : B = Family.T n :=
        Set.eq_of_subset_of_ncard_le hBT (by simp [hcard, Family.ncard_T, hn])
          (Set.toFinite _)
      exact hT (by rw [heq])
  | pairAOne =>
      have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
      have hsmall := carrierPreimage_ncard_le_n_add_two n .pairAOne (Or.inl rfl)
      omega
  | pairAFour =>
      have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
      have hsmall := carrierPreimage_ncard_le_n_add_two n .pairAFour
        (Or.inr (Or.inl rfl))
      omega
  | pairOneFour =>
      have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
      have hsmall := carrierPreimage_ncard_le_n_add_two n .pairOneFour
        (Or.inr (Or.inr rfl))
      omega

/-! ### Pure-special selectors -/

/-- Template special attached to an actual special element.  The default on
blocks is irrelevant once the block-classification is known to be `none`. -/
def specialValue (n : ℕ) : Element n → Templates.DeleteX.Special
  | .special s => TemplateInstances.DeleteX.specialKind s
  | .block _ _ => .One

def actualSpecial (n : ℕ) : Templates.DeleteX.Special → Element n
  | .One => Family.one n
  | .Two => Family.two n
  | .Three => Family.three n
  | .Four => Family.four n

@[simp] theorem specialValue_actualSpecial (n : ℕ)
    (s : Templates.DeleteX.Special) :
    specialValue n (actualSpecial n s) = s := by
  cases s <;> rfl

@[simp] theorem blockClass_actualSpecial (n : ℕ)
    (s : Templates.DeleteX.Special) :
    TemplateInstances.DeleteX.blockClass n (actualSpecial n s) = none := by
  cases s <;> rfl

theorem actualSpecial_ne_x0 (n : ℕ) (s : Templates.DeleteX.Special) :
    actualSpecial n s ≠ Family.x0 n := by
  cases s <;> simp [actualSpecial, Family.one, Family.two, Family.three,
    Family.four, Family.x0]

theorem specialClass_eq_some_specialValue_of_blockClass_eq_none
    {n : ℕ} {e : Element n}
    (he : e ≠ Family.x0 n)
    (hBlock : TemplateInstances.DeleteX.blockClass n e = none) :
    TemplateInstances.DeleteX.specialClass n e = some (specialValue n e) := by
  cases e with
  | special s => rfl
  | block b i =>
      fin_cases b
      · simp [TemplateInstances.DeleteX.blockClass,
          TemplateInstances.DeleteX.removedElement, Family.x0] at hBlock
        subst i
        exact (he rfl).elim
      · simp [TemplateInstances.DeleteX.blockClass,
          TemplateInstances.DeleteX.removedElement,
          TemplateInstances.DeleteX.blockKind, Family.x0] at hBlock
      · simp [TemplateInstances.DeleteX.blockClass,
          TemplateInstances.DeleteX.removedElement,
          TemplateInstances.DeleteX.blockKind, Family.x0] at hBlock

theorem specialValue_injective_of_blockClass_eq_none
    {n : ℕ} {e f : Element n}
    (he : e ≠ Family.x0 n) (hf : f ≠ Family.x0 n)
    (heBlock : TemplateInstances.DeleteX.blockClass n e = none)
    (hfBlock : TemplateInstances.DeleteX.blockClass n f = none)
    (hValue : specialValue n e = specialValue n f) : e = f := by
  cases e with
  | special se =>
      cases f with
      | special sf =>
          fin_cases se <;> fin_cases sf <;> simp_all [specialValue,
            TemplateInstances.DeleteX.specialKind]
      | block bf i =>
          have hfalse : False := by
            have h := specialClass_eq_some_specialValue_of_blockClass_eq_none
              hf hfBlock
            simp [TemplateInstances.DeleteX.specialClass] at h
          exact hfalse.elim
  | block be i =>
      have hfalse : False := by
        have h := specialClass_eq_some_specialValue_of_blockClass_eq_none
          he heBlock
        simp [TemplateInstances.DeleteX.specialClass] at h
      exact hfalse.elim

theorem eq_actualSpecial_specialValue_of_blockClass_eq_none
    {n : ℕ} {e : Element n}
    (he : e ≠ Family.x0 n)
    (hBlock : TemplateInstances.DeleteX.blockClass n e = none) :
    e = actualSpecial n (specialValue n e) := by
  apply specialValue_injective_of_blockClass_eq_none he
    (actualSpecial_ne_x0 n _) hBlock (blockClass_actualSpecial n _)
  simp

/-- Pure-special selectors of a deletion basis satisfy their Rado
inequality.  They inject into a special-label set avoiding the unique
dependent triple `{1,2,3}`. -/
theorem card_le_finrank_subspaceSum_of_forall_blockClass_none
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hB : ((Family.MI n) ＼ {Family.x0 n}).IsBase B)
    (J : Finset B)
    (hPure : ∀ i ∈ J,
      TemplateInstances.DeleteX.blockClass n (i : Element n) = none) :
    J.card ≤ Module.finrank ℚ
      (subspaceSum ℚ
        (fun b : B ↦ TemplateInstances.DeleteX.ambientSubspace n b) J) := by
  rcases (Family.delete_x0_isBase_iff n B).mp hB with
    ⟨hGround, -, hNotT, -, -, -, -, -⟩
  have hx0B : Family.x0 n ∉ B := by
    intro hx
    exact (hGround hx).2 (by simp)
  let S : Set Templates.DeleteX.Special :=
    Set.range (fun j : J ↦ specialValue n (j.1 : Element n))
  have special_mem_B (s : Templates.DeleteX.Special) (hs : s ∈ S) :
      actualSpecial n s ∈ B := by
    obtain ⟨j, rfl⟩ := hs
    have hpure := hPure j.1 j.2
    rw [← eq_actualSpecial_specialValue_of_blockClass_eq_none
      (fun he ↦ hx0B (he ▸ j.1.property)) hpure]
    exact j.1.property
  have hSpecialT :
      ¬ ({.One, .Two, .Three} : Set Templates.DeleteX.Special) ⊆ S := by
    intro hT
    apply hNotT
    intro e he
    simp only [Family.T, Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl
    · exact special_mem_B .One (hT (by simp))
    · exact special_mem_B .Two (hT (by simp))
    · exact special_mem_B .Three (hT (by simp))
  have hSpecialLinear : LinearIndependent ℚ
      (fun s : S ↦ Templates.DeleteX.special n s) :=
    SpecialGeometry.DeleteX.linearIndependent_special_of_not_core_triple_subset
      n hSpecialT
  let f : J → S := fun j ↦
    ⟨specialValue n (j.1 : Element n), Set.mem_range_self j⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply Subtype.ext
    apply specialValue_injective_of_blockClass_eq_none
      (fun he ↦ hx0B (he ▸ i.1.property))
      (fun he ↦ hx0B (he ▸ j.1.property))
      (hPure i.1 i.2) (hPure j.1 j.2)
    exact congrArg Subtype.val hij
  have hActualLinear : LinearIndependent ℚ
      (fun j : J ↦ Templates.DeleteX.special n
        (specialValue n (j.1 : Element n))) := by
    simpa [f, Function.comp_def] using hSpecialLinear.comp f hf
  let W := subspaceSum ℚ
    (fun b : B ↦ TemplateInstances.DeleteX.ambientSubspace n b) J
  let v : J → W := fun j ↦
    ⟨Templates.DeleteX.special n (specialValue n (j.1 : Element n)), by
      apply (Finset.le_sup
        (f := fun b : B ↦ TemplateInstances.DeleteX.ambientSubspace n b)
        j.2)
      have hpure := hPure j.1 j.2
      have hspecial := specialClass_eq_some_specialValue_of_blockClass_eq_none
        (fun he ↦ hx0B (he ▸ j.1.property)) hpure
      simp [TemplateInstances.DeleteX.ambientSubspace,
        TemplateInstances.ambientSubspaceOf, hpure, hspecial]⟩
  have hv : LinearIndependent ℚ v := by
    apply LinearIndependent.of_comp W.subtype
    simpa [v, Function.comp_def] using hActualLinear
  simpa [W] using hv.fintype_card_le_finrank

/-- Every mixed selector of a basis of `MIₙ \ x₀` satisfies its Rado
dimension inequality.  Failure would force quotient rank at most two: rank
one is too small to contain enough actual elements, while rank two forces the
whole basis into one of the nine classified carriers. -/
theorem card_le_finrank_subspaceSum_of_exists_block
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hB : ((Family.MI n) ＼ {Family.x0 n}).IsBase B)
    (J : Finset B)
    (hBlock : ∃ i ∈ J, ∃ b,
      TemplateInstances.DeleteX.blockClass n (i : Element n) = some b) :
    J.card ≤ Module.finrank ℚ
      (subspaceSum ℚ
        (fun b : B ↦ TemplateInstances.DeleteX.ambientSubspace n b) J) := by
  rcases (Family.delete_x0_isBase_iff n B).mp hB with
    ⟨hGround, hBcard, -, -, -, -, -, -⟩
  have hx0B : Family.x0 n ∉ B := by
    intro hx
    exact (hGround hx).2 (by simp)
  let R : Submodule ℚ
      (Templates.QuotientSpace Templates.DeleteX.quotientDim) :=
    Submodule.span ℚ
      ((quotientLabel n ∘ fun b : B ↦ (b : Element n)) '' (J : Set B))
  have hdim : Module.finrank ℚ
      (subspaceSum ℚ
        (fun b : B ↦ TemplateInstances.DeleteX.ambientSubspace n b) J) =
      n + Module.finrank ℚ R := by
    simpa [TemplateInstances.DeleteX.ambientSubspace, quotientLabel, R] using
      (ClassifiedGeometry.finrank_subspaceSum_ambientSubspaceOf
        Templates.DeleteX.blockLabel (Templates.DeleteX.special n)
        (TemplateInstances.DeleteX.blockClass n)
        (TemplateInstances.DeleteX.specialClass n)
        (fun b : B ↦ (b : Element n)) hBlock)
  rw [hdim]
  by_contra hCapacity
  have hlt : n + Module.finrank ℚ R < J.card :=
    Nat.lt_of_not_ge hCapacity
  have hJle : J.card ≤ n + 3 := card_selector_le_of_ncard hBcard J
  have hRankLe : Module.finrank ℚ R ≤ 2 := by omega
  let S : Finset Label := selectedLabels J
  have hSpan : R = Submodule.span ℚ
      (QuotientCarrierAudit.DeleteX.label '' (S : Set Label)) := by
    dsimp [R, S]
    rw [quotient_image_eq hx0B]
  by_cases hRankZero : Module.finrank ℚ R = 0
  · have hRbot : R = ⊥ := Submodule.finrank_eq_zero.mp hRankZero
    obtain ⟨i, hi, b, hib⟩ := hBlock
    have hqMem : quotientLabel n (i : Element n) ∈ R :=
      Submodule.subset_span ⟨i, hi, rfl⟩
    have hqZero : quotientLabel n (i : Element n) = 0 := by
      rw [hRbot] at hqMem
      simpa using hqMem
    have hLabelZero : QuotientCarrierAudit.DeleteX.label
        (labelClass n (i : Element n)) = 0 := by
      rw [← quotientLabel_eq_label n
        (fun he ↦ hx0B (he ▸ i.property))]
      exact hqZero
    exact label_ne_zero _ hLabelZero
  · by_cases hRankOne : Module.finrank ℚ R ≤ 1
    · have hScard : S.card ≤ 1 :=
        (QuotientCarrierAudit.DeleteX.finrank_le_one_iff_card_le_one S).mp
          (by rw [← hSpan]; exact hRankOne)
      obtain ⟨i, hi, -, -⟩ := hBlock
      have hJnonempty : J.Nonempty := ⟨i, hi⟩
      have hJsmall := card_le_n_add_one_of_selectedLabels_card_le_one
        hJnonempty hScard
      omega
    · have hRankTwo : Module.finrank ℚ R = 2 := by omega
      have hJcard : J.card = n + 3 := by omega
      have hJuniv : J = Finset.univ :=
        selector_eq_univ_of_card_eq hBcard hJcard
      obtain ⟨C, hSC⟩ :=
        QuotientCarrierAudit.DeleteX.contained_in_carrier_of_finrank_le_two S
          (by rw [← hSpan, hRankTwo])
      have hBcarrier : B ⊆ carrierPreimage n C := by
        intro e heB
        let b : B := ⟨e, heB⟩
        have hbJ : b ∈ J := by simp [hJuniv]
        exact hSC (label_mem_selectedLabels hbJ)
      exact base_not_subset_carrierPreimage hB C hBcarrier

/-- Complete Rado audit for every basis of `MIₙ \ x₀`. -/
theorem hasRadoCapacity_ambient_of_isBase
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hB : ((Family.MI n) ＼ {Family.x0 n}).IsBase B) :
    HasRadoCapacity ℚ
      (fun b : B ↦ TemplateInstances.DeleteX.ambientSubspace n b) := by
  classical
  intro J
  by_cases hBlock : ∃ i ∈ J, ∃ b,
      TemplateInstances.DeleteX.blockClass n (i : Element n) = some b
  · exact card_le_finrank_subspaceSum_of_exists_block hB J hBlock
  · apply card_le_finrank_subspaceSum_of_forall_blockClass_none hB J
    intro i hi
    cases hClass : TemplateInstances.DeleteX.blockClass n
        (i : Element n) with
    | none => rfl
    | some b => exact (hBlock ⟨i, hi, b, hClass⟩).elim

/-- Coordinate-space form consumed by the generic representation compiler. -/
theorem hasRadoCapacity_L_of_isBase
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hB : ((Family.MI n) ＼ {Family.x0 n}).IsBase B) :
    HasRadoCapacity ℚ (fun b : B ↦ TemplateInstances.DeleteX.L n b) :=
  (TemplateInstances.DeleteX.hasRadoCapacity_L_iff_ambient B).mpr
    (hasRadoCapacity_ambient_of_isBase hB)

/-! ### Forced dependence of full-size nonbases -/

theorem q_one_eq_q_two_sub_q_three (n : ℕ) :
    TemplateInstances.DeleteX.q n (Family.one n) =
      TemplateInstances.DeleteX.q n (Family.two n) -
        TemplateInstances.DeleteX.q n (Family.three n) := by
  simpa [TemplateInstances.DeleteX.q,
    TemplateInstances.coordinateFixedVectorOf,
    TemplateInstances.DeleteX.ambientFixedVector,
    TemplateInstances.ambientFixedVectorOf,
    TemplateInstances.DeleteX.specialClass,
    TemplateInstances.DeleteX.specialKind] using
      congrArg (TemplateInstances.ambientCoordinateEquiv n
        Templates.DeleteX.quotientDim)
        (Templates.DeleteX.special_relation n)

theorem not_linearIndependent_of_T_subset
    {n : ℕ} {B : Set (Element n)}
    (hT : Family.T n ⊆ B)
    {w : Element n → (Fin (n + Templates.DeleteX.quotientDim) → ℚ)}
    (hwq : ∀ e ∈ TemplateInstances.DeleteX.fixedElements n,
      w e = TemplateInstances.DeleteX.q n e) :
    ¬ LinearIndependent ℚ (fun b : B ↦ w b) := by
  intro hLinear
  have hOneB : Family.one n ∈ B := hT (by simp [Family.T])
  have hTwoB : Family.two n ∈ B := hT (by simp [Family.T])
  have hThreeB : Family.three n ∈ B := hT (by simp [Family.T])
  have hOneFixed : Family.one n ∈
      TemplateInstances.DeleteX.fixedElements n := by
    exact ⟨.One, rfl⟩
  have hTwoFixed : Family.two n ∈
      TemplateInstances.DeleteX.fixedElements n := by
    exact ⟨.Two, rfl⟩
  have hThreeFixed : Family.three n ∈
      TemplateInstances.DeleteX.fixedElements n := by
    exact ⟨.Three, rfl⟩
  have hwOne := hwq (Family.one n) hOneFixed
  have hwTwo := hwq (Family.two n) hTwoFixed
  have hwThree := hwq (Family.three n) hThreeFixed
  have hwRelation : w (Family.one n) =
      w (Family.two n) - w (Family.three n) := by
    rw [hwOne, hwTwo, hwThree]
    exact q_one_eq_q_two_sub_q_three n
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
  let g : Fin 3 → ℚ := ![1, -1, 1]
  have hsum : ∑ i, g i • w (t i) = 0 := by
    simp [g, t, Fin.sum_univ_succ]
    change w (Family.one n) +
      (-w (Family.two n) + w (Family.three n)) = 0
    rw [hwRelation]
    abel
  have hcoeff := (Fintype.linearIndependent_iff.mp hThreeLinear) g hsum 0
  norm_num [g] at hcoeff

/-- A full-size set lying in any carrier other than the pure-special
`{1,2,3}` carrier necessarily contains an actual large-block element. -/
theorem exists_block_of_subset_carrierPreimage
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hBcard : B.ncard = n + 3) (hx0B : Family.x0 n ∉ B)
    (C : QuotientCarrierAudit.DeleteX.Carrier)
    (hC : C ≠ .planeOneTwoThree)
    (hBC : B ⊆ carrierPreimage n C) :
    ∃ i : B, ∃ b,
      TemplateInstances.DeleteX.blockClass n (i : Element n) = some b := by
  by_contra hExists
  push Not at hExists
  have hNone (e : Element n) (heB : e ∈ B) :
      TemplateInstances.DeleteX.blockClass n e = none := by
    cases hClass : TemplateInstances.DeleteX.blockClass n e with
    | none => rfl
    | some b => exact (hExists ⟨e, heB⟩ b hClass).elim
  have hSpecial (e : Element n) (heB : e ∈ B) :
      ∃ s, e = actualSpecial n s := by
    exact ⟨specialValue n e,
      eq_actualSpecial_specialValue_of_blockClass_eq_none
        (fun he ↦ hx0B (he ▸ heB)) (hNone e heB)⟩
  have small_contradiction {U : Set (Element n)}
      (hBU : B ⊆ U) (hU : U.ncard ≤ 2) : False := by
    have hle := Set.ncard_le_ncard hBU (Set.toFinite _)
    omega
  cases C with
  | planeABThree =>
      apply small_contradiction (U := {Family.three n})
      · intro e heB
        obtain ⟨s, rfl⟩ := hSpecial e heB
        have hc := hBC heB
        cases s <;> simp_all [carrierPreimage, actualSpecial, labelClass,
          specialLabelClass, QuotientCarrierAudit.DeleteX.carrier]
      · simp

  | planeACTwo =>
      apply small_contradiction (U := {Family.two n})
      · intro e heB
        obtain ⟨s, rfl⟩ := hSpecial e heB
        have hc := hBC heB
        cases s <;> simp_all [carrierPreimage, actualSpecial, labelClass,
          specialLabelClass, QuotientCarrierAudit.DeleteX.carrier]
      · simp
  | planeBCOne =>
      apply small_contradiction (U := {Family.one n})
      · intro e heB
        obtain ⟨s, rfl⟩ := hSpecial e heB
        have hc := hBC heB
        cases s <;> simp_all [carrierPreimage, actualSpecial, labelClass,
          specialLabelClass, QuotientCarrierAudit.DeleteX.carrier]
      · simp
  | planeBTwoFour =>
      apply small_contradiction (U := {Family.two n, Family.four n})
      · intro e heB
        obtain ⟨s, rfl⟩ := hSpecial e heB
        have hc := hBC heB
        cases s <;> simp_all [carrierPreimage, actualSpecial, labelClass,
          specialLabelClass, QuotientCarrierAudit.DeleteX.carrier]
      · simp
  | planeCThreeFour =>
      apply small_contradiction (U := {Family.three n, Family.four n})
      · intro e heB
        obtain ⟨s, rfl⟩ := hSpecial e heB
        have hc := hBC heB
        cases s <;> simp_all [carrierPreimage, actualSpecial, labelClass,
          specialLabelClass, QuotientCarrierAudit.DeleteX.carrier]
      · simp
  | planeOneTwoThree => exact (hC rfl).elim
  | pairAOne =>
      apply small_contradiction (U := {Family.one n})
      · intro e heB
        obtain ⟨s, rfl⟩ := hSpecial e heB
        have hc := hBC heB
        cases s <;> simp_all [carrierPreimage, actualSpecial, labelClass,
          specialLabelClass, QuotientCarrierAudit.DeleteX.carrier]
      · simp
  | pairAFour =>
      apply small_contradiction (U := {Family.four n})
      · intro e heB
        obtain ⟨s, rfl⟩ := hSpecial e heB
        have hc := hBC heB
        cases s <;> simp_all [carrierPreimage, actualSpecial, labelClass,
          specialLabelClass, QuotientCarrierAudit.DeleteX.carrier]
      · simp
  | pairOneFour =>
      apply small_contradiction (U := {Family.one n, Family.four n})
      · intro e heB
        obtain ⟨s, rfl⟩ := hSpecial e heB
        have hc := hBC heB
        cases s <;> simp_all [carrierPreimage, actualSpecial, labelClass,
          specialLabelClass, QuotientCarrierAudit.DeleteX.carrier]
      · simp

/-- A full-size set contained in a non-special quotient carrier has total
allowed dimension at most `n+2`. -/
theorem finrank_subspaceSum_L_univ_le_n_add_two_of_subset_carrier
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hBcard : B.ncard = n + 3) (hx0B : Family.x0 n ∉ B)
    (C : QuotientCarrierAudit.DeleteX.Carrier)
    (hC : C ≠ .planeOneTwoThree)
    (hBC : B ⊆ carrierPreimage n C) :
    Module.finrank ℚ
      (subspaceSum ℚ (fun b : B ↦ TemplateInstances.DeleteX.L n b)
        Finset.univ) ≤ n + 2 := by
  obtain ⟨i, b, hib⟩ :=
    exists_block_of_subset_carrierPreimage hBcard hx0B C hC hBC
  have hBlock : ∃ i ∈ (Finset.univ : Finset B), ∃ b,
      TemplateInstances.DeleteX.blockClass n (i : Element n) = some b :=
    ⟨i, Finset.mem_univ i, b, hib⟩
  let S : Finset Label := selectedLabels (Finset.univ : Finset B)
  have hSC : S ⊆ QuotientCarrierAudit.DeleteX.carrier C := by
    intro l hl
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hl
    exact hBC e.property
  have hQrank : Module.finrank ℚ
      (Submodule.span ℚ
        (QuotientCarrierAudit.DeleteX.label '' (S : Set Label))) ≤ 2 :=
    (QuotientCarrierAudit.finrank_span_image_mono
      QuotientCarrierAudit.DeleteX.label hSC).trans
        (QuotientCarrierAudit.DeleteX.carrier_finrank_le_two C)
  have hAmbientDim : Module.finrank ℚ
      (subspaceSum ℚ
        (fun b : B ↦ TemplateInstances.DeleteX.ambientSubspace n b)
        Finset.univ) =
      n + Module.finrank ℚ
        (Submodule.span ℚ
          (QuotientCarrierAudit.DeleteX.label '' (S : Set Label))) := by
    have hdim :=
      ClassifiedGeometry.finrank_subspaceSum_ambientSubspaceOf
        Templates.DeleteX.blockLabel (Templates.DeleteX.special n)
        (TemplateInstances.DeleteX.blockClass n)
        (TemplateInstances.DeleteX.specialClass n)
        (fun b : B ↦ (b : Element n)) hBlock
    have hImage :
        (ClassifiedGeometry.quotientLabelOf
            Templates.DeleteX.blockLabel (Templates.DeleteX.special n)
            (TemplateInstances.DeleteX.blockClass n)
            (TemplateInstances.DeleteX.specialClass n) ∘
          fun b : B ↦ (b : Element n)) ''
            ((Finset.univ : Finset B) : Set B) =
          QuotientCarrierAudit.DeleteX.label '' (S : Set Label) := by
      simpa [quotientLabel, S] using
        quotient_image_eq hx0B (Finset.univ : Finset B)
    rw [hImage] at hdim
    simpa [TemplateInstances.DeleteX.ambientSubspace, quotientLabel, S] using hdim
  have hCoordinateDim : Module.finrank ℚ
      (subspaceSum ℚ (fun b : B ↦ TemplateInstances.DeleteX.L n b)
        Finset.univ) =
      Module.finrank ℚ
        (subspaceSum ℚ
          (fun b : B ↦ TemplateInstances.DeleteX.ambientSubspace n b)
          Finset.univ) := by
    simpa [TemplateInstances.DeleteX.L] using
      (TemplateInstances.finrank_subspaceSum_coordinateSubspaceOf
        (TemplateInstances.DeleteX.ambientSubspace n)
        (fun b : B ↦ (b : Element n)) Finset.univ)
  rw [hCoordinateDim, hAmbientDim]
  omega

theorem not_hasRadoCapacity_L_of_subset_carrier
    {n : ℕ} {B : Set (Element n)} [Fintype B]
    (hBcard : B.ncard = n + 3) (hx0B : Family.x0 n ∉ B)
    (C : QuotientCarrierAudit.DeleteX.Carrier)
    (hC : C ≠ .planeOneTwoThree)
    (hBC : B ⊆ carrierPreimage n C) :
    ¬ HasRadoCapacity ℚ
      (fun b : B ↦ TemplateInstances.DeleteX.L n b) := by
  apply not_hasRadoCapacity_of_finrank_lt_card (Finset.univ : Finset B)
  have hfin :=
    finrank_subspaceSum_L_univ_le_n_add_two_of_subset_carrier
      hBcard hx0B C hC hBC
  have hcard : (Finset.univ : Finset B).card = n + 3 := by
    simp [← Nat.card_eq_fintype_card, hBcard]
  omega

/-- Every full-size nonbasis is dependent for every assignment obeying the
template constraints. -/
theorem nonbase_forced_dependence
    {n : ℕ} (B : Set (Element n))
    (hGround : B ⊆ ((Family.MI n) ＼ {Family.x0 n}).E)
    (hBcard : B.ncard = n + 3)
    (hNotBase : ¬ ((Family.MI n) ＼ {Family.x0 n}).IsBase B)
    (w : Element n → (Fin (n + Templates.DeleteX.quotientDim) → ℚ))
    (hwL : ∀ e, w e ∈ TemplateInstances.DeleteX.L n e)
    (hwq : ∀ e ∈ TemplateInstances.DeleteX.fixedElements n,
      w e = TemplateInstances.DeleteX.q n e) :
    ¬ LinearIndependent ℚ (fun b : B ↦ w b) := by
  letI : Fintype B := B.toFinite.fintype
  have hx0B : Family.x0 n ∉ B := by
    intro hx
    exact (hGround hx).2 (by simp)
  have hForbidden :
      Family.T n ⊆ B ∨
      B = Family.C2 n ∨ B = Family.C3 n ∨
      B ⊆ Family.H1 n ∨
      B ⊆ Family.H2 n \ {Family.x0 n} ∨
      B ⊆ Family.H3 n \ {Family.x0 n} := by
    by_contra h
    push Not at h
    apply hNotBase
    exact (Family.delete_x0_isBase_iff n B).mpr
      ⟨hGround, hBcard, h.1, h.2.1, h.2.2.1, h.2.2.2.1,
        h.2.2.2.2.1, h.2.2.2.2.2⟩
  rcases hForbidden with hT | hC2 | hC3 | hH1 | hH2 | hH3
  · exact not_linearIndependent_of_T_subset hT hwq
  · have hBC : B ⊆ carrierPreimage n .planeBTwoFour := by
      rw [carrierPreimage_planeBTwoFour, hC2]
    exact not_linearIndependent_of_not_hasRadoCapacity
      (not_hasRadoCapacity_L_of_subset_carrier hBcard hx0B
        .planeBTwoFour (by decide) hBC)
      (fun b ↦ hwL b)
  · have hBC : B ⊆ carrierPreimage n .planeCThreeFour := by
      rw [carrierPreimage_planeCThreeFour, hC3]
    exact not_linearIndependent_of_not_hasRadoCapacity
      (not_hasRadoCapacity_L_of_subset_carrier hBcard hx0B
        .planeCThreeFour (by decide) hBC)
      (fun b ↦ hwL b)
  · have hBC : B ⊆ carrierPreimage n .planeBCOne := by
      rw [carrierPreimage_planeBCOne]
      exact hH1
    exact not_linearIndependent_of_not_hasRadoCapacity
      (not_hasRadoCapacity_L_of_subset_carrier hBcard hx0B
        .planeBCOne (by decide) hBC)
      (fun b ↦ hwL b)
  · have hBC : B ⊆ carrierPreimage n .planeACTwo := by
      rw [carrierPreimage_planeACTwo]
      exact hH2.trans Set.diff_subset
    exact not_linearIndependent_of_not_hasRadoCapacity
      (not_hasRadoCapacity_L_of_subset_carrier hBcard hx0B
        .planeACTwo (by decide) hBC)
      (fun b ↦ hwL b)
  · have hBC : B ⊆ carrierPreimage n .planeABThree := by
      rw [carrierPreimage_planeABThree]
      exact hH3.trans Set.diff_subset
    exact not_linearIndependent_of_not_hasRadoCapacity
      (not_hasRadoCapacity_L_of_subset_carrier hBcard hx0B
        .planeABThree (by decide) hBC)
      (fun b ↦ hwL b)

/-! ### End-to-end representation -/

/-- The complete deletion audit compiled into one rational vector
representation, retaining the subspace and fixed-column certificates. -/
theorem exists_representation_delete_x0 (n : ℕ) :
    ∃ v : Element n → (Fin (n + 3) → ℚ),
      Represents ℚ ((Family.MI n) ＼ {Family.x0 n}) v ∧
        (∀ e, v e ∈ TemplateInstances.DeleteX.L n e) ∧
          (∀ e ∈ TemplateInstances.DeleteX.fixedElements n,
            v e = TemplateInstances.DeleteX.q n e) := by
  apply exists_representation_of_subspace_base_audit
    (M := (Family.MI n) ＼ {Family.x0 n})
    (d := n + 3)
    (TemplateInstances.DeleteX.L n)
    (TemplateInstances.DeleteX.fixedElements n)
    (TemplateInstances.DeleteX.q n)
  · intro e he
    exact TemplateInstances.DeleteX.q_mem_L he
  · obtain ⟨B₀, hB₀⟩ :=
      ((Family.MI n) ＼ {Family.x0 n}).exists_isBase
    exact ⟨B₀, hB₀,
      ((Family.delete_x0_isBase_iff n B₀).mp hB₀).2.1⟩
  · intro B hB _
    letI : Fintype B := B.toFinite.fintype
    exact TemplateInstances.DeleteX.feasible_assignment_on_candidate B
      (hasRadoCapacity_L_of_isBase hB)
  · intro B hGround hBcard hNotBase w hwL hwq
    exact nonbase_forced_dependence B hGround hBcard hNotBase w hwL hwq

/-- Public endpoint: deletion of the distinguished `X`-block element is
rationally representable for every `n`, including `n = 0`. -/
theorem rationallyRepresentable_delete_x0 (n : ℕ) :
    RationallyRepresentable ((Family.MI n) ＼ {Family.x0 n}) := by
  obtain ⟨v, hv, -, -⟩ := exists_representation_delete_x0 n
  exact ⟨n + 3, v, hv⟩

end DeleteX

end BlandJensenFormal.BlandJensenMI.DeletionCapacity
