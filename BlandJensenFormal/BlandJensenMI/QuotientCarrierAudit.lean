import BlandJensenFormal.BlandJensenMI.QuotientGeometry

/-!
# Finite carrier audit for the six quotient-label configurations

The determinant certificates in `MIQuotientLabels` classify individual
dependent pairs and triples.  Capacity arguments need a slightly different
form: a classification of *all finite sets* of labels whose quotient span has
small dimension.  This file supplies that carrier form.

For deletion templates, every label set spanning a space of dimension at
most two is contained in one explicitly listed maximal coplanar carrier.  The
carriers consist of the planes displayed in the construction together with
the maximal two-label carriers that lie in no displayed three-label plane.
For contraction templates, every nonzero label set spanning at most a line is
contained in one explicit direction carrier.  The unique zero label in the
`M / x` template is treated separately.

Finite enumeration is discharged by kernel-reducible decision procedures.  The passage from
`finrank` to determinants is proved as ordinary linear algebra, through the
theorems in `QuotientGeometry`; it is not delegated to computation.
-/

namespace BlandJensenFormal.BlandJensenMI.QuotientCarrierAudit

open Set Submodule
open BlandJensenFormal.MIQuotientLabels
open BlandJensenFormal.BlandJensenMI.QuotientGeometry

/-! ## General bridges from span dimension to determinant certificates -/

theorem range_pair_eq {V : Type*} (x y : V) :
    Set.range (![x, y] : Fin 2 → V) = {x, y} := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hz
    rcases hz with (rfl | hz)
    · exact ⟨0, by simp⟩
    · have : z = y := hz
      subst z
      exact ⟨1, by simp⟩

theorem range_triple_eq {V : Type*} (x y z : V) :
    Set.range (![x, y, z] : Fin 3 → V) = {x, y, z} := by
  ext w
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hw
    rcases hw with (rfl | rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · exact ⟨2, by simp⟩

@[simp] theorem image_coe_finset_pair {α β : Type*} [DecidableEq α]
    (f : α → β) (i j : α) :
    f '' (({i, j} : Finset α) : Set α) = {f i, f j} := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    simp at ha
    rcases ha with rfl | rfl <;> simp
  · intro hx
    rcases hx with (rfl | hx)
    · exact ⟨i, by simp, rfl⟩
    · have : x = f j := hx
      subst x
      exact ⟨j, by simp, rfl⟩

@[simp] theorem image_coe_finset_triple {α β : Type*} [DecidableEq α]
    (f : α → β) (i j k : α) :
    f '' (({i, j, k} : Finset α) : Set α) = {f i, f j, f k} := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    simp at ha
    rcases ha with rfl | rfl | rfl <;> simp
  · intro hx
    rcases hx with (rfl | rfl | rfl)
    · exact ⟨i, by simp, rfl⟩
    · exact ⟨j, by simp, rfl⟩
    · exact ⟨k, by simp, rfl⟩

theorem finrank_span_pair_le_one_iff_det2_eq_zero (x y : Vec2) :
    Module.finrank ℚ (Submodule.span ℚ ({x, y} : Set Vec2)) ≤ 1 ↔
      det2 x y = 0 := by
  rw [← range_pair_eq]
  exact finrank_span_vec2_le_one_iff_det2_eq_zero x y

theorem finrank_span_triple_le_two_iff_det3_eq_zero (x y z : Vec3) :
    Module.finrank ℚ (Submodule.span ℚ ({x, y, z} : Set Vec3)) ≤ 2 ↔
      det3 x y z = 0 := by
  rw [← range_triple_eq]
  exact finrank_span_vec3_le_two_iff_det3_eq_zero x y z

theorem finrank_span_pair_le_two {V : Type*} [AddCommGroup V] [Module ℚ V]
    (x y : V) :
    Module.finrank ℚ (Submodule.span ℚ ({x, y} : Set V)) ≤ 2 := by
  rw [← range_pair_eq]
  simpa only [Set.finrank, Fintype.card_fin] using
    finrank_range_le_card (![x, y] : Fin 2 → V)

/-- Every triple chosen from a quotient-label set of span dimension at most
two has zero determinant. -/
theorem det3_eq_zero_of_mem_of_finrank_le_two {α : Type*}
    [DecidableEq α] (label : α → Vec3) (S : Finset α)
    (hfinrank : Module.finrank ℚ
      (Submodule.span ℚ (label '' (S : Set α))) ≤ 2)
    {i j k : α} (hi : i ∈ S) (hj : j ∈ S) (hk : k ∈ S) :
    det3 (label i) (label j) (label k) = 0 := by
  apply (finrank_span_vec3_le_two_iff_det3_eq_zero
    (label i) (label j) (label k)).mp
  refine (Submodule.finrank_mono (Submodule.span_mono ?_)).trans hfinrank
  intro v hv
  rw [range_triple_eq] at hv
  rcases hv with (rfl | rfl | rfl)
  · exact ⟨i, hi, rfl⟩
  · exact ⟨j, hj, rfl⟩
  · exact ⟨k, hk, rfl⟩

/-- Every pair chosen from a quotient-label set of span dimension at most one
has zero determinant. -/
theorem det2_eq_zero_of_mem_of_finrank_le_one {α : Type*}
    [DecidableEq α] (label : α → Vec2) (S : Finset α)
    (hfinrank : Module.finrank ℚ
      (Submodule.span ℚ (label '' (S : Set α))) ≤ 1)
    {i j : α} (hi : i ∈ S) (hj : j ∈ S) :
    det2 (label i) (label j) = 0 := by
  apply (finrank_span_vec2_le_one_iff_det2_eq_zero
    (label i) (label j)).mp
  refine (Submodule.finrank_mono (Submodule.span_mono ?_)).trans hfinrank
  intro v hv
  rw [range_pair_eq] at hv
  rcases hv with (rfl | rfl)
  · exact ⟨i, hi, rfl⟩
  · exact ⟨j, hj, rfl⟩

/-- If two three-dimensional vectors span at most a line, adjoining any third
vector gives a dependent triple. -/
theorem det3_eq_zero_of_finrank_span_pair_le_one (x y z : Vec3)
    (hpair : Module.finrank ℚ
      (Submodule.span ℚ ({x, y} : Set Vec3)) ≤ 1) :
    det3 x y z = 0 := by
  apply (finrank_span_triple_le_two_iff_det3_eq_zero x y z).mp
  rw [show ({x, y, z} : Set Vec3) = {x, y} ∪ {z} by
      ext w
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
      tauto,
    Submodule.span_union]
  have hsum := Submodule.finrank_add_le_finrank_add_finrank
    (Submodule.span ℚ ({x, y} : Set Vec3))
    (Submodule.span ℚ ({z} : Set Vec3))
  have hz : Module.finrank ℚ (Submodule.span ℚ ({z} : Set Vec3)) ≤ 1 := by
    simpa only [Set.finrank] using
      (finrank_span_le_card (R := ℚ) ({z} : Set Vec3))
  omega

/-- A finite set of labels with at most one element spans dimension at most
one. -/
theorem finrank_span_image_le_one_of_card_le_one {α : Type*}
    [DecidableEq α] (label : α → Vec3) (S : Finset α)
    (hcard : S.card ≤ 1) :
    Module.finrank ℚ
      (Submodule.span ℚ (label '' (S : Set α))) ≤ 1 := by
  classical
  have hspan := finrank_span_finset_le_card (R := ℚ) (S.image label)
  have himage : ((S.image label : Finset Vec3) : Set Vec3) =
      label '' (S : Set α) := by
    ext v
    simp [eq_comm]
  rw [himage] at hspan
  exact hspan.trans ((Finset.card_image_le).trans hcard)

/-- Generic low-line-rank criterion for a finite three-dimensional label
configuration whose distinct labels can always be completed to a nonzero
determinant triple. -/
theorem finrank_span_image_le_one_iff_card_le_one_of_pair_separated
    {α : Type*} [DecidableEq α] (label : α → Vec3)
    (hseparated : ∀ i j : α, i ≠ j →
      ∃ k : α, det3 (label i) (label j) (label k) ≠ 0)
    (S : Finset α) :
    Module.finrank ℚ
        (Submodule.span ℚ (label '' (S : Set α))) ≤ 1 ↔
      S.card ≤ 1 := by
  constructor
  · intro hfinrank
    apply Finset.card_le_one_iff.mpr
    intro i j hi hj
    by_contra hij
    obtain ⟨k, hdet⟩ := hseparated i j hij
    apply hdet
    apply det3_eq_zero_of_finrank_span_pair_le_one
    refine (Submodule.finrank_mono (Submodule.span_mono ?_)).trans hfinrank
    intro v hv
    rcases hv with (rfl | rfl)
    · exact ⟨i, hi, rfl⟩
    · exact ⟨j, hj, rfl⟩
  · exact finrank_span_image_le_one_of_card_le_one label S

/-- Span dimension is monotone under inclusion of finite label carriers. -/
theorem finrank_span_image_mono {α : Type*} [DecidableEq α]
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V]
    (label : α → V) {S C : Finset α} (hSC : S ⊆ C) :
    Module.finrank ℚ (Submodule.span ℚ (label '' (S : Set α))) ≤
      Module.finrank ℚ (Submodule.span ℚ (label '' (C : Set α))) := by
  apply Submodule.finrank_mono
  apply Submodule.span_mono
  exact Set.image_mono <| by simpa using hSC

/-! ## Deletion of an element of the `X` block -/

namespace DeleteX

abbrev Label := BlandJensenFormal.MIQuotientLabels.DeleteX.Label

def label : Label → Vec3 :=
  BlandJensenFormal.MIQuotientLabels.DeleteX.label

/-- Maximal coplanar carriers.  The first six are the planes displayed in the
construction.  The final three are the maximal pairs not lying in any of
those six planes. -/
inductive Carrier
  | planeABThree
  | planeACTwo
  | planeBCOne
  | planeBTwoFour
  | planeCThreeFour
  | planeOneTwoThree
  | pairAOne
  | pairAFour
  | pairOneFour
  deriving DecidableEq, Fintype, Repr

def carrier : Carrier → Finset Label
  | .planeABThree => {.A, .B, .Three}
  | .planeACTwo => {.A, .C, .Two}
  | .planeBCOne => {.B, .C, .One}
  | .planeBTwoFour => {.B, .Two, .Four}
  | .planeCThreeFour => {.C, .Three, .Four}
  | .planeOneTwoThree => {.One, .Two, .Three}
  | .pairAOne => {.A, .One}
  | .pairAFour => {.A, .Four}
  | .pairOneFour => {.One, .Four}

/-- The six planes displayed in the construction, separated from the three
exceptional maximal pairs. -/
inductive DisplayedPlane
  | ABThree | ACTwo | BCOne | BTwoFour | CThreeFour | OneTwoThree
  deriving DecidableEq, Fintype, Repr

def displayedCarrier : DisplayedPlane → Finset Label
  | .ABThree => {.A, .B, .Three}
  | .ACTwo => {.A, .C, .Two}
  | .BCOne => {.B, .C, .One}
  | .BTwoFour => {.B, .Two, .Four}
  | .CThreeFour => {.C, .Three, .Four}
  | .OneTwoThree => {.One, .Two, .Three}

def blockLabels : Finset Label := {.A, .B, .C}

def specialLabels : Finset Label := {.One, .Two, .Three, .Four}

/-- Purely finite completeness of the maximal-carrier list, expressed using
the literature's six listed dependent triples. -/
theorem listed_triples_contained_in_carrier :
    ∀ S : Finset Label,
      (∀ i ∈ S, ∀ j ∈ S, ∀ k ∈ S,
        PairwiseDistinct3 i j k →
          BlandJensenFormal.MIQuotientLabels.DeleteX.ListedDependent i j k) →
      ∃ C : Carrier, S ⊆ carrier C := by
  set_option maxRecDepth 10000 in
    decide

/-- Under either richness hypothesis used in the capacity proof, the small
two-label carriers are impossible; the containing carrier is one of the six
displayed planes. -/
theorem listed_triples_contained_in_displayed_plane_of_rich :
    ∀ S : Finset Label,
      (∀ i ∈ S, ∀ j ∈ S, ∀ k ∈ S,
        PairwiseDistinct3 i j k →
          BlandJensenFormal.MIQuotientLabels.DeleteX.ListedDependent i j k) →
      (3 ≤ S.card ∧ (2 ≤ (S ∩ blockLabels).card ∨
        (1 ≤ (S ∩ blockLabels).card ∧ 2 ≤ (S ∩ specialLabels).card))) →
      ∃ P : DisplayedPlane, S ⊆ displayedCarrier P := by
  intro S hdependent hrich
  obtain ⟨C, hC⟩ := listed_triples_contained_in_carrier S hdependent
  cases C with
  | planeABThree => exact ⟨.ABThree, hC⟩
  | planeACTwo => exact ⟨.ACTwo, hC⟩
  | planeBCOne => exact ⟨.BCOne, hC⟩
  | planeBTwoFour => exact ⟨.BTwoFour, hC⟩
  | planeCThreeFour => exact ⟨.CThreeFour, hC⟩
  | planeOneTwoThree => exact ⟨.OneTwoThree, hC⟩
  | pairAOne | pairAFour | pairOneFour =>
      have hcard := Finset.card_le_card hC
      simp [carrier] at hcard
      omega

/-- Every displayed or exceptional maximal carrier spans quotient dimension
at most two. -/
theorem carrier_finrank_le_two (C : Carrier) :
    Module.finrank ℚ
      (Submodule.span ℚ (label '' (carrier C : Set Label))) ≤ 2 := by
  cases C with
  | planeABThree =>
      rw [carrier, image_coe_finset_triple]
      exact (finrank_span_triple_le_two_iff_det3_eq_zero
        (label .A) (label .B) (label .Three)).2
        BlandJensenFormal.MIQuotientLabels.DeleteX.rich_plane_A_B_Three
  | planeACTwo =>
      rw [carrier, image_coe_finset_triple]
      exact (finrank_span_triple_le_two_iff_det3_eq_zero
        (label .A) (label .C) (label .Two)).2
        BlandJensenFormal.MIQuotientLabels.DeleteX.rich_plane_A_C_Two
  | planeBCOne =>
      rw [carrier, image_coe_finset_triple]
      exact (finrank_span_triple_le_two_iff_det3_eq_zero
        (label .B) (label .C) (label .One)).2
        BlandJensenFormal.MIQuotientLabels.DeleteX.rich_plane_B_C_One
  | planeBTwoFour =>
      rw [carrier, image_coe_finset_triple]
      exact (finrank_span_triple_le_two_iff_det3_eq_zero
        (label .B) (label .Two) (label .Four)).2
        BlandJensenFormal.MIQuotientLabels.DeleteX.rich_plane_B_Two_Four
  | planeCThreeFour =>
      rw [carrier, image_coe_finset_triple]
      exact (finrank_span_triple_le_two_iff_det3_eq_zero
        (label .C) (label .Three) (label .Four)).2
        BlandJensenFormal.MIQuotientLabels.DeleteX.rich_plane_C_Three_Four
  | planeOneTwoThree =>
      rw [carrier, image_coe_finset_triple]
      exact (finrank_span_triple_le_two_iff_det3_eq_zero
        (label .One) (label .Two) (label .Three)).2
        BlandJensenFormal.MIQuotientLabels.DeleteX.special_T_One_Two_Three
  | pairAOne =>
      rw [carrier, image_coe_finset_pair]
      exact finrank_span_pair_le_two (label .A) (label .One)
  | pairAFour =>
      rw [carrier, image_coe_finset_pair]
      exact finrank_span_pair_le_two (label .A) (label .Four)
  | pairOneFour =>
      rw [carrier, image_coe_finset_pair]
      exact finrank_span_pair_le_two (label .One) (label .Four)

/-- Carrier classification in the form directly consumed by capacity proofs. -/
theorem contained_in_carrier_of_finrank_le_two (S : Finset Label)
    (hfinrank : Module.finrank ℚ
      (Submodule.span ℚ (label '' (S : Set Label))) ≤ 2) :
    ∃ C : Carrier, S ⊆ carrier C := by
  apply listed_triples_contained_in_carrier S
  intro i hi j hj k hk hdistinct
  apply (BlandJensenFormal.MIQuotientLabels.DeleteX.det_zero_iff_listed
    i j k hdistinct).mp
  exact det3_eq_zero_of_mem_of_finrank_le_two label S hfinrank hi hj hk

theorem carrier_antichain :
    ∀ C D : Carrier, carrier C ⊆ carrier D → C = D := by
  decide

/-- Each listed carrier is maximal among label sets of quotient span dimension
at most two. -/
theorem carrier_maximal (C : Carrier) (S : Finset Label)
    (hCS : carrier C ⊆ S)
    (hfinrank : Module.finrank ℚ
      (Submodule.span ℚ (label '' (S : Set Label))) ≤ 2) :
    S = carrier C := by
  obtain ⟨D, hSD⟩ := contained_in_carrier_of_finrank_le_two S hfinrank
  have hCD : C = D := carrier_antichain C D (hCS.trans hSD)
  subst D
  exact Finset.Subset.antisymm hSD hCS

/-- Restricted carrier classification under the two richness conditions that
occur in the paper proof. -/
theorem contained_in_displayed_plane_of_finrank_le_two_of_rich
    (S : Finset Label)
    (hfinrank : Module.finrank ℚ
      (Submodule.span ℚ (label '' (S : Set Label))) ≤ 2)
    (hrich : 3 ≤ S.card ∧ (2 ≤ (S ∩ blockLabels).card ∨
      (1 ≤ (S ∩ blockLabels).card ∧ 2 ≤ (S ∩ specialLabels).card))) :
    ∃ P : DisplayedPlane, S ⊆ displayedCarrier P := by
  apply listed_triples_contained_in_displayed_plane_of_rich S
  · intro i hi j hj k hk hdistinct
    apply (BlandJensenFormal.MIQuotientLabels.DeleteX.det_zero_iff_listed
      i j k hdistinct).mp
    exact det3_eq_zero_of_mem_of_finrank_le_two label S hfinrank hi hj hk
  · exact hrich

/-- Any two distinct deletion labels can be completed by a third label to a
nonzero determinant triple. -/
theorem distinct_pair_extendable :
    ∀ i j : Label, i ≠ j →
      ∃ k : Label, det3 (label i) (label j) (label k) ≠ 0 := by
  intro i j hij
  have hfinite : ∀ i j : Label, i ≠ j →
      ∃ k : Label, PairwiseDistinct3 i j k ∧
        ¬ BlandJensenFormal.MIQuotientLabels.DeleteX.ListedDependent i j k := by
    decide
  obtain ⟨k, hdistinct, hnot_listed⟩ := hfinite i j hij
  refine ⟨k, ?_⟩
  intro hzero
  exact hnot_listed <|
    (BlandJensenFormal.MIQuotientLabels.DeleteX.det_zero_iff_listed
      i j k hdistinct).mp hzero

/-- A deletion-label set spans at most a line exactly when it has at most one
label. -/
theorem finrank_le_one_iff_card_le_one (S : Finset Label) :
    Module.finrank ℚ
        (Submodule.span ℚ (label '' (S : Set Label))) ≤ 1 ↔
      S.card ≤ 1 :=
  finrank_span_image_le_one_iff_card_le_one_of_pair_separated
    label distinct_pair_extendable S

end DeleteX

/-! ## Deletion of the special element `1` -/

namespace DeleteOne

abbrev Label := BlandJensenFormal.MIQuotientLabels.DeleteOne.Label

def label : Label → Vec3 :=
  BlandJensenFormal.MIQuotientLabels.DeleteOne.label

/-- Four displayed planes and the three maximal pairs that are contained in
no displayed plane. -/
inductive Carrier
  | planeABThree
  | planeACTwo
  | planeBTwoFour
  | planeCThreeFour
  | pairAFour
  | pairBC
  | pairTwoThree
  deriving DecidableEq, Fintype, Repr

def carrier : Carrier → Finset Label
  | .planeABThree => {.A, .B, .Three}
  | .planeACTwo => {.A, .C, .Two}
  | .planeBTwoFour => {.B, .Two, .Four}
  | .planeCThreeFour => {.C, .Three, .Four}
  | .pairAFour => {.A, .Four}
  | .pairBC => {.B, .C}
  | .pairTwoThree => {.Two, .Three}

inductive DisplayedPlane
  | ABThree | ACTwo | BTwoFour | CThreeFour
  deriving DecidableEq, Fintype, Repr

def displayedCarrier : DisplayedPlane → Finset Label
  | .ABThree => {.A, .B, .Three}
  | .ACTwo => {.A, .C, .Two}
  | .BTwoFour => {.B, .Two, .Four}
  | .CThreeFour => {.C, .Three, .Four}

def blockLabels : Finset Label := {.A, .B, .C}

def specialLabels : Finset Label := {.Two, .Three, .Four}

theorem listed_triples_contained_in_carrier :
    ∀ S : Finset Label,
      (∀ i ∈ S, ∀ j ∈ S, ∀ k ∈ S,
        PairwiseDistinct3 i j k →
          BlandJensenFormal.MIQuotientLabels.DeleteOne.ListedDependent i j k) →
      ∃ C : Carrier, S ⊆ carrier C := by
  decide

theorem listed_triples_contained_in_displayed_plane_of_rich :
    ∀ S : Finset Label,
      (∀ i ∈ S, ∀ j ∈ S, ∀ k ∈ S,
        PairwiseDistinct3 i j k →
          BlandJensenFormal.MIQuotientLabels.DeleteOne.ListedDependent i j k) →
      (3 ≤ S.card ∧ (2 ≤ (S ∩ blockLabels).card ∨
        (1 ≤ (S ∩ blockLabels).card ∧ 2 ≤ (S ∩ specialLabels).card))) →
      ∃ P : DisplayedPlane, S ⊆ displayedCarrier P := by
  intro S hdependent hrich
  obtain ⟨C, hC⟩ := listed_triples_contained_in_carrier S hdependent
  cases C with
  | planeABThree => exact ⟨.ABThree, hC⟩
  | planeACTwo => exact ⟨.ACTwo, hC⟩
  | planeBTwoFour => exact ⟨.BTwoFour, hC⟩
  | planeCThreeFour => exact ⟨.CThreeFour, hC⟩
  | pairAFour | pairBC | pairTwoThree =>
      have hcard := Finset.card_le_card hC
      simp [carrier] at hcard
      omega

theorem carrier_finrank_le_two (C : Carrier) :
    Module.finrank ℚ
      (Submodule.span ℚ (label '' (carrier C : Set Label))) ≤ 2 := by
  cases C with
  | planeABThree =>
      rw [carrier, image_coe_finset_triple]
      exact (finrank_span_triple_le_two_iff_det3_eq_zero
        (label .A) (label .B) (label .Three)).2
        BlandJensenFormal.MIQuotientLabels.DeleteOne.rich_plane_A_B_Three
  | planeACTwo =>
      rw [carrier, image_coe_finset_triple]
      exact (finrank_span_triple_le_two_iff_det3_eq_zero
        (label .A) (label .C) (label .Two)).2
        BlandJensenFormal.MIQuotientLabels.DeleteOne.rich_plane_A_C_Two
  | planeBTwoFour =>
      rw [carrier, image_coe_finset_triple]
      exact (finrank_span_triple_le_two_iff_det3_eq_zero
        (label .B) (label .Two) (label .Four)).2
        BlandJensenFormal.MIQuotientLabels.DeleteOne.rich_plane_B_Two_Four
  | planeCThreeFour =>
      rw [carrier, image_coe_finset_triple]
      exact (finrank_span_triple_le_two_iff_det3_eq_zero
        (label .C) (label .Three) (label .Four)).2
        BlandJensenFormal.MIQuotientLabels.DeleteOne.rich_plane_C_Three_Four
  | pairAFour =>
      rw [carrier, image_coe_finset_pair]
      exact finrank_span_pair_le_two (label .A) (label .Four)
  | pairBC =>
      rw [carrier, image_coe_finset_pair]
      exact finrank_span_pair_le_two (label .B) (label .C)
  | pairTwoThree =>
      rw [carrier, image_coe_finset_pair]
      exact finrank_span_pair_le_two (label .Two) (label .Three)

theorem contained_in_carrier_of_finrank_le_two (S : Finset Label)
    (hfinrank : Module.finrank ℚ
      (Submodule.span ℚ (label '' (S : Set Label))) ≤ 2) :
    ∃ C : Carrier, S ⊆ carrier C := by
  apply listed_triples_contained_in_carrier S
  intro i hi j hj k hk hdistinct
  apply (BlandJensenFormal.MIQuotientLabels.DeleteOne.det_zero_iff_listed
    i j k hdistinct).mp
  exact det3_eq_zero_of_mem_of_finrank_le_two label S hfinrank hi hj hk

theorem carrier_antichain :
    ∀ C D : Carrier, carrier C ⊆ carrier D → C = D := by
  decide

theorem carrier_maximal (C : Carrier) (S : Finset Label)
    (hCS : carrier C ⊆ S)
    (hfinrank : Module.finrank ℚ
      (Submodule.span ℚ (label '' (S : Set Label))) ≤ 2) :
    S = carrier C := by
  obtain ⟨D, hSD⟩ := contained_in_carrier_of_finrank_le_two S hfinrank
  have hCD : C = D := carrier_antichain C D (hCS.trans hSD)
  subst D
  exact Finset.Subset.antisymm hSD hCS

theorem contained_in_displayed_plane_of_finrank_le_two_of_rich
    (S : Finset Label)
    (hfinrank : Module.finrank ℚ
      (Submodule.span ℚ (label '' (S : Set Label))) ≤ 2)
    (hrich : 3 ≤ S.card ∧ (2 ≤ (S ∩ blockLabels).card ∨
      (1 ≤ (S ∩ blockLabels).card ∧ 2 ≤ (S ∩ specialLabels).card))) :
    ∃ P : DisplayedPlane, S ⊆ displayedCarrier P := by
  apply listed_triples_contained_in_displayed_plane_of_rich S
  · intro i hi j hj k hk hdistinct
    apply (BlandJensenFormal.MIQuotientLabels.DeleteOne.det_zero_iff_listed
      i j k hdistinct).mp
    exact det3_eq_zero_of_mem_of_finrank_le_two label S hfinrank hi hj hk
  · exact hrich

theorem distinct_pair_extendable :
    ∀ i j : Label, i ≠ j →
      ∃ k : Label, det3 (label i) (label j) (label k) ≠ 0 := by
  intro i j hij
  have hfinite : ∀ i j : Label, i ≠ j →
      ∃ k : Label, PairwiseDistinct3 i j k ∧
        ¬ BlandJensenFormal.MIQuotientLabels.DeleteOne.ListedDependent i j k := by
    decide
  obtain ⟨k, hdistinct, hnot_listed⟩ := hfinite i j hij
  refine ⟨k, ?_⟩
  intro hzero
  exact hnot_listed <|
    (BlandJensenFormal.MIQuotientLabels.DeleteOne.det_zero_iff_listed
      i j k hdistinct).mp hzero

theorem finrank_le_one_iff_card_le_one (S : Finset Label) :
    Module.finrank ℚ
        (Submodule.span ℚ (label '' (S : Set Label))) ≤ 1 ↔
      S.card ≤ 1 :=
  finrank_span_image_le_one_iff_card_le_one_of_pair_separated
    label distinct_pair_extendable S

end DeleteOne

/-! ## Deletion of the special element `4` -/

namespace DeleteFour

abbrev Label := BlandJensenFormal.MIQuotientLabels.DeleteFour.Label

def label : Label → Vec3 :=
  BlandJensenFormal.MIQuotientLabels.DeleteFour.label

/-- Four displayed planes and the three maximal pairs that are contained in
no displayed plane. -/
inductive Carrier
  | planeABThree
  | planeACTwo
  | planeBCOne
  | planeOneTwoThree
  | pairAOne
  | pairBTwo
  | pairCThree
  deriving DecidableEq, Fintype, Repr

def carrier : Carrier → Finset Label
  | .planeABThree => {.A, .B, .Three}
  | .planeACTwo => {.A, .C, .Two}
  | .planeBCOne => {.B, .C, .One}
  | .planeOneTwoThree => {.One, .Two, .Three}
  | .pairAOne => {.A, .One}
  | .pairBTwo => {.B, .Two}
  | .pairCThree => {.C, .Three}

inductive DisplayedPlane
  | ABThree | ACTwo | BCOne | OneTwoThree
  deriving DecidableEq, Fintype, Repr

def displayedCarrier : DisplayedPlane → Finset Label
  | .ABThree => {.A, .B, .Three}
  | .ACTwo => {.A, .C, .Two}
  | .BCOne => {.B, .C, .One}
  | .OneTwoThree => {.One, .Two, .Three}

def blockLabels : Finset Label := {.A, .B, .C}

def specialLabels : Finset Label := {.One, .Two, .Three}

theorem listed_triples_contained_in_carrier :
    ∀ S : Finset Label,
      (∀ i ∈ S, ∀ j ∈ S, ∀ k ∈ S,
        PairwiseDistinct3 i j k →
          BlandJensenFormal.MIQuotientLabels.DeleteFour.ListedDependent i j k) →
      ∃ C : Carrier, S ⊆ carrier C := by
  decide

theorem listed_triples_contained_in_displayed_plane_of_rich :
    ∀ S : Finset Label,
      (∀ i ∈ S, ∀ j ∈ S, ∀ k ∈ S,
        PairwiseDistinct3 i j k →
          BlandJensenFormal.MIQuotientLabels.DeleteFour.ListedDependent i j k) →
      (3 ≤ S.card ∧ (2 ≤ (S ∩ blockLabels).card ∨
        (1 ≤ (S ∩ blockLabels).card ∧ 2 ≤ (S ∩ specialLabels).card))) →
      ∃ P : DisplayedPlane, S ⊆ displayedCarrier P := by
  intro S hdependent hrich
  obtain ⟨C, hC⟩ := listed_triples_contained_in_carrier S hdependent
  cases C with
  | planeABThree => exact ⟨.ABThree, hC⟩
  | planeACTwo => exact ⟨.ACTwo, hC⟩
  | planeBCOne => exact ⟨.BCOne, hC⟩
  | planeOneTwoThree => exact ⟨.OneTwoThree, hC⟩
  | pairAOne | pairBTwo | pairCThree =>
      have hcard := Finset.card_le_card hC
      simp [carrier] at hcard
      omega

theorem carrier_finrank_le_two (C : Carrier) :
    Module.finrank ℚ
      (Submodule.span ℚ (label '' (carrier C : Set Label))) ≤ 2 := by
  cases C with
  | planeABThree =>
      rw [carrier, image_coe_finset_triple]
      exact (finrank_span_triple_le_two_iff_det3_eq_zero
        (label .A) (label .B) (label .Three)).2
        BlandJensenFormal.MIQuotientLabels.DeleteFour.rich_plane_A_B_Three
  | planeACTwo =>
      rw [carrier, image_coe_finset_triple]
      exact (finrank_span_triple_le_two_iff_det3_eq_zero
        (label .A) (label .C) (label .Two)).2
        BlandJensenFormal.MIQuotientLabels.DeleteFour.rich_plane_A_C_Two
  | planeBCOne =>
      rw [carrier, image_coe_finset_triple]
      exact (finrank_span_triple_le_two_iff_det3_eq_zero
        (label .B) (label .C) (label .One)).2
        BlandJensenFormal.MIQuotientLabels.DeleteFour.rich_plane_B_C_One
  | planeOneTwoThree =>
      rw [carrier, image_coe_finset_triple]
      exact (finrank_span_triple_le_two_iff_det3_eq_zero
        (label .One) (label .Two) (label .Three)).2
        BlandJensenFormal.MIQuotientLabels.DeleteFour.special_T_One_Two_Three
  | pairAOne =>
      rw [carrier, image_coe_finset_pair]
      exact finrank_span_pair_le_two (label .A) (label .One)
  | pairBTwo =>
      rw [carrier, image_coe_finset_pair]
      exact finrank_span_pair_le_two (label .B) (label .Two)
  | pairCThree =>
      rw [carrier, image_coe_finset_pair]
      exact finrank_span_pair_le_two (label .C) (label .Three)

theorem contained_in_carrier_of_finrank_le_two (S : Finset Label)
    (hfinrank : Module.finrank ℚ
      (Submodule.span ℚ (label '' (S : Set Label))) ≤ 2) :
    ∃ C : Carrier, S ⊆ carrier C := by
  apply listed_triples_contained_in_carrier S
  intro i hi j hj k hk hdistinct
  apply (BlandJensenFormal.MIQuotientLabels.DeleteFour.det_zero_iff_listed
    i j k hdistinct).mp
  exact det3_eq_zero_of_mem_of_finrank_le_two label S hfinrank hi hj hk

theorem carrier_antichain :
    ∀ C D : Carrier, carrier C ⊆ carrier D → C = D := by
  decide

theorem carrier_maximal (C : Carrier) (S : Finset Label)
    (hCS : carrier C ⊆ S)
    (hfinrank : Module.finrank ℚ
      (Submodule.span ℚ (label '' (S : Set Label))) ≤ 2) :
    S = carrier C := by
  obtain ⟨D, hSD⟩ := contained_in_carrier_of_finrank_le_two S hfinrank
  have hCD : C = D := carrier_antichain C D (hCS.trans hSD)
  subst D
  exact Finset.Subset.antisymm hSD hCS

theorem contained_in_displayed_plane_of_finrank_le_two_of_rich
    (S : Finset Label)
    (hfinrank : Module.finrank ℚ
      (Submodule.span ℚ (label '' (S : Set Label))) ≤ 2)
    (hrich : 3 ≤ S.card ∧ (2 ≤ (S ∩ blockLabels).card ∨
      (1 ≤ (S ∩ blockLabels).card ∧ 2 ≤ (S ∩ specialLabels).card))) :
    ∃ P : DisplayedPlane, S ⊆ displayedCarrier P := by
  apply listed_triples_contained_in_displayed_plane_of_rich S
  · intro i hi j hj k hk hdistinct
    apply (BlandJensenFormal.MIQuotientLabels.DeleteFour.det_zero_iff_listed
      i j k hdistinct).mp
    exact det3_eq_zero_of_mem_of_finrank_le_two label S hfinrank hi hj hk
  · exact hrich

theorem distinct_pair_extendable :
    ∀ i j : Label, i ≠ j →
      ∃ k : Label, det3 (label i) (label j) (label k) ≠ 0 := by
  intro i j hij
  have hfinite : ∀ i j : Label, i ≠ j →
      ∃ k : Label, PairwiseDistinct3 i j k ∧
        ¬ BlandJensenFormal.MIQuotientLabels.DeleteFour.ListedDependent i j k := by
    decide
  obtain ⟨k, hdistinct, hnot_listed⟩ := hfinite i j hij
  refine ⟨k, ?_⟩
  intro hzero
  exact hnot_listed <|
    (BlandJensenFormal.MIQuotientLabels.DeleteFour.det_zero_iff_listed
      i j k hdistinct).mp hzero

theorem finrank_le_one_iff_card_le_one (S : Finset Label) :
    Module.finrank ℚ
        (Submodule.span ℚ (label '' (S : Set Label))) ≤ 1 ↔
      S.card ≤ 1 :=
  finrank_span_image_le_one_iff_card_le_one_of_pair_separated
    label distinct_pair_extendable S

end DeleteFour

/-! ## Contraction of an element of the `X` block -/

namespace ContractX

abbrev Label := BlandJensenFormal.MIQuotientLabels.ContractX.Label

def label : Label → Vec2 :=
  BlandJensenFormal.MIQuotientLabels.ContractX.label

def lineClass : Label → Fin 3 :=
  BlandJensenFormal.MIQuotientLabels.ContractX.lineClass

/-- The three nonzero quotient directions. -/
inductive Carrier
  | b | c | bPlusC
  deriving DecidableEq, Fintype, Repr

def carrier : Carrier → Finset Label
  | .b => {.Y, .Three}
  | .c => {.Z, .Two}
  | .bPlusC => {.One, .Four}

/-- The `X` block is the unique zero quotient label. -/
theorem label_eq_zero_iff (i : Label) : label i = 0 ↔ i = .X := by
  fin_cases i <;> decide

@[simp] theorem zero_label : label .X = 0 :=
  (label_eq_zero_iff .X).2 rfl

theorem pairwise_lineClass_contained_in_carrier :
    ∀ S : Finset Label, .X ∉ S →
      (∀ i ∈ S, ∀ j ∈ S, lineClass i = lineClass j) →
      ∃ C : Carrier, S ⊆ carrier C := by
  set_option maxRecDepth 10000 in
    decide

theorem carrier_finrank_le_one (C : Carrier) :
    Module.finrank ℚ
      (Submodule.span ℚ (label '' (carrier C : Set Label))) ≤ 1 := by
  cases C with
  | b =>
      rw [carrier, image_coe_finset_pair]
      apply (finrank_span_pair_le_one_iff_det2_eq_zero _ _).2
      apply (BlandJensenFormal.MIQuotientLabels.ContractX.det_zero_iff_lineClass_eq
        .Y .Three (by decide)).2
      decide
  | c =>
      rw [carrier, image_coe_finset_pair]
      apply (finrank_span_pair_le_one_iff_det2_eq_zero _ _).2
      apply (BlandJensenFormal.MIQuotientLabels.ContractX.det_zero_iff_lineClass_eq
        .Z .Two (by decide)).2
      decide
  | bPlusC =>
      rw [carrier, image_coe_finset_pair]
      apply (finrank_span_pair_le_one_iff_det2_eq_zero _ _).2
      apply (BlandJensenFormal.MIQuotientLabels.ContractX.det_zero_iff_lineClass_eq
        .One .Four (by decide)).2
      decide

/-- Every nonzero low-rank quotient-label set lies in one of the three
direction carriers. -/
theorem contained_in_carrier_of_finrank_le_one (S : Finset Label)
    (hzero : .X ∉ S)
    (hfinrank : Module.finrank ℚ
      (Submodule.span ℚ (label '' (S : Set Label))) ≤ 1) :
    ∃ C : Carrier, S ⊆ carrier C := by
  apply pairwise_lineClass_contained_in_carrier S hzero
  intro i hi j hj
  apply (BlandJensenFormal.MIQuotientLabels.ContractX.det_zero_iff_lineClass_eq
    i j ⟨by exact fun h ↦ hzero (h ▸ hi), by exact fun h ↦ hzero (h ▸ hj)⟩).mp
  exact det2_eq_zero_of_mem_of_finrank_le_one label S hfinrank hi hj

/-- Exact carrier criterion for a label set not containing the zero label. -/
theorem finrank_le_one_iff_contained_in_carrier (S : Finset Label)
    (hzero : .X ∉ S) :
    Module.finrank ℚ
        (Submodule.span ℚ (label '' (S : Set Label))) ≤ 1 ↔
      ∃ C : Carrier, S ⊆ carrier C := by
  constructor
  · exact contained_in_carrier_of_finrank_le_one S hzero
  · rintro ⟨C, hSC⟩
    exact (finrank_span_image_mono label hSC).trans (carrier_finrank_le_one C)

/-- Inserting the unique zero label does not change the quotient span. -/
theorem span_insert_zero_label (S : Finset Label) :
    Submodule.span ℚ (label '' ((insert .X S : Finset Label) : Set Label)) =
      Submodule.span ℚ (label '' (S : Set Label)) := by
  rw [Finset.coe_insert, Set.image_insert_eq, zero_label,
    Submodule.span_insert_zero]

end ContractX

/-! ## Contraction of the special element `1` -/

namespace ContractOne

abbrev Label := BlandJensenFormal.MIQuotientLabels.ContractOne.Label

def label : Label → Vec2 :=
  BlandJensenFormal.MIQuotientLabels.ContractOne.label

def lineClass : Label → Fin 3 :=
  BlandJensenFormal.MIQuotientLabels.ContractOne.lineClass

inductive Carrier
  | h | k | ell
  deriving DecidableEq, Fintype, Repr

def carrier : Carrier → Finset Label
  | .h => {.Y, .Z}
  | .k => {.X, .Four}
  | .ell => {.Two, .Three}

theorem label_ne_zero (i : Label) : label i ≠ 0 := by
  fin_cases i <;> decide

theorem pairwise_lineClass_contained_in_carrier :
    ∀ S : Finset Label,
      (∀ i ∈ S, ∀ j ∈ S, lineClass i = lineClass j) →
      ∃ C : Carrier, S ⊆ carrier C := by
  decide

theorem carrier_finrank_le_one (C : Carrier) :
    Module.finrank ℚ
      (Submodule.span ℚ (label '' (carrier C : Set Label))) ≤ 1 := by
  cases C with
  | h =>
      rw [carrier, image_coe_finset_pair]
      apply (finrank_span_pair_le_one_iff_det2_eq_zero _ _).2
      apply (BlandJensenFormal.MIQuotientLabels.ContractOne.det_zero_iff_lineClass_eq
        .Y .Z).2
      decide
  | k =>
      rw [carrier, image_coe_finset_pair]
      apply (finrank_span_pair_le_one_iff_det2_eq_zero _ _).2
      apply (BlandJensenFormal.MIQuotientLabels.ContractOne.det_zero_iff_lineClass_eq
        .X .Four).2
      decide
  | ell =>
      rw [carrier, image_coe_finset_pair]
      apply (finrank_span_pair_le_one_iff_det2_eq_zero _ _).2
      apply (BlandJensenFormal.MIQuotientLabels.ContractOne.det_zero_iff_lineClass_eq
        .Two .Three).2
      decide

/-- Every quotient-label set spanning at most a line lies in one of the three
direction carriers. -/
theorem contained_in_carrier_of_finrank_le_one (S : Finset Label)
    (hfinrank : Module.finrank ℚ
      (Submodule.span ℚ (label '' (S : Set Label))) ≤ 1) :
    ∃ C : Carrier, S ⊆ carrier C := by
  apply pairwise_lineClass_contained_in_carrier S
  intro i hi j hj
  apply (BlandJensenFormal.MIQuotientLabels.ContractOne.det_zero_iff_lineClass_eq
    i j).mp
  exact det2_eq_zero_of_mem_of_finrank_le_one label S hfinrank hi hj

theorem finrank_le_one_iff_contained_in_carrier (S : Finset Label) :
    Module.finrank ℚ
        (Submodule.span ℚ (label '' (S : Set Label))) ≤ 1 ↔
      ∃ C : Carrier, S ⊆ carrier C := by
  constructor
  · exact contained_in_carrier_of_finrank_le_one S
  · rintro ⟨C, hSC⟩
    exact (finrank_span_image_mono label hSC).trans (carrier_finrank_le_one C)

end ContractOne

/-! ## Contraction of the special element `4` -/

namespace ContractFour

abbrev Label := BlandJensenFormal.MIQuotientLabels.ContractFour.Label

def label : Label → Vec2 :=
  BlandJensenFormal.MIQuotientLabels.ContractFour.label

def lineClass : Label → Fin 3 :=
  BlandJensenFormal.MIQuotientLabels.ContractFour.lineClass

inductive Carrier
  | a | b | aPlusB
  deriving DecidableEq, Fintype, Repr

def carrier : Carrier → Finset Label
  | .a => {.X, .One}
  | .b => {.Y, .Two}
  | .aPlusB => {.Z, .Three}

theorem label_ne_zero (i : Label) : label i ≠ 0 := by
  fin_cases i <;> decide

theorem pairwise_lineClass_contained_in_carrier :
    ∀ S : Finset Label,
      (∀ i ∈ S, ∀ j ∈ S, lineClass i = lineClass j) →
      ∃ C : Carrier, S ⊆ carrier C := by
  decide

theorem carrier_finrank_le_one (C : Carrier) :
    Module.finrank ℚ
      (Submodule.span ℚ (label '' (carrier C : Set Label))) ≤ 1 := by
  cases C with
  | a =>
      rw [carrier, image_coe_finset_pair]
      apply (finrank_span_pair_le_one_iff_det2_eq_zero _ _).2
      apply (BlandJensenFormal.MIQuotientLabels.ContractFour.det_zero_iff_lineClass_eq
        .X .One).2
      decide
  | b =>
      rw [carrier, image_coe_finset_pair]
      apply (finrank_span_pair_le_one_iff_det2_eq_zero _ _).2
      apply (BlandJensenFormal.MIQuotientLabels.ContractFour.det_zero_iff_lineClass_eq
        .Y .Two).2
      decide
  | aPlusB =>
      rw [carrier, image_coe_finset_pair]
      apply (finrank_span_pair_le_one_iff_det2_eq_zero _ _).2
      apply (BlandJensenFormal.MIQuotientLabels.ContractFour.det_zero_iff_lineClass_eq
        .Z .Three).2
      decide

theorem contained_in_carrier_of_finrank_le_one (S : Finset Label)
    (hfinrank : Module.finrank ℚ
      (Submodule.span ℚ (label '' (S : Set Label))) ≤ 1) :
    ∃ C : Carrier, S ⊆ carrier C := by
  apply pairwise_lineClass_contained_in_carrier S
  intro i hi j hj
  apply (BlandJensenFormal.MIQuotientLabels.ContractFour.det_zero_iff_lineClass_eq
    i j).mp
  exact det2_eq_zero_of_mem_of_finrank_le_one label S hfinrank hi hj

theorem finrank_le_one_iff_contained_in_carrier (S : Finset Label) :
    Module.finrank ℚ
        (Submodule.span ℚ (label '' (S : Set Label))) ≤ 1 ↔
      ∃ C : Carrier, S ⊆ carrier C := by
  constructor
  · exact contained_in_carrier_of_finrank_le_one S
  · rintro ⟨C, hSC⟩
    exact (finrank_span_image_mono label hSC).trans (carrier_finrank_le_one C)

end ContractFour

end BlandJensenFormal.BlandJensenMI.QuotientCarrierAudit
