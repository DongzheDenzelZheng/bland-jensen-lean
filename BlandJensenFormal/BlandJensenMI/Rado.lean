import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Data.Rat.Denumerable
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Independent representatives from finitely many subspaces

This file proves the finite subspace form of Rado's independent transversal
theorem over an arbitrary field.  Its rational specialization is the form
required by the representations in the Bland--Jensen construction.

For a finite family `L : ι → Submodule K V`, an independent choice
`v i ∈ L i` exists exactly when every subfamily indexed by `J` spans a
space of dimension at least `J.card`.

The sufficiency proof is by induction on the finite index type.  The union of
all tight subfamilies is again tight, by submodularity of dimension.  For the
distinguished subspace, choose a vector outside the sum indexed by that union.
Quotienting by the chosen line preserves all capacity inequalities, so the
induction hypothesis applies in the quotient.  Finally, representatives lift
from the quotient and linear independence lifts with them.
-/

namespace BlandJensenFormal.BlandJensenMI

open Function Set Submodule

universe u v w

section Definitions

variable (K : Type u) {V : Type v} [Field K] [AddCommGroup V] [Module K V]

/-- The sum of the subspaces whose indices lie in `J`. -/
def subspaceSum {ι : Type w} (L : ι → Submodule K V) (J : Finset ι) : Submodule K V :=
  J.sup L

@[simp] theorem subspaceSum_empty {ι : Type w} (L : ι → Submodule K V) :
    subspaceSum K L ∅ = ⊥ := by
  simp [subspaceSum]

@[simp] theorem subspaceSum_insert {ι : Type w} [DecidableEq ι]
    (L : ι → Submodule K V) (i : ι) (J : Finset ι) :
    subspaceSum K L (insert i J) = L i ⊔ subspaceSum K L J := by
  simp [subspaceSum]

@[simp] theorem subspaceSum_insertNone {ι : Type w} [DecidableEq ι]
    (L : Option ι → Submodule K V) (J : Finset ι) :
    subspaceSum K L J.insertNone =
      L none ⊔ subspaceSum K (fun i ↦ L (some i)) J := by
  simp [Finset.insertNone, subspaceSum, Function.comp_def]

/-- A linear map carries a finite sum of subspaces to the sum of their images. -/
theorem subspaceSum_map {ι : Type w} [DecidableEq ι] {V' : Type*}
    [AddCommGroup V'] [Module K V'] (f : V →ₗ[K] V')
    (L : ι → Submodule K V) (J : Finset ι) :
    subspaceSum K (fun i ↦ (L i).map f) J = (subspaceSum K L J).map f := by
  induction J using Finset.induction_on with
  | empty => simp
  | @insert i J hi ih => simp [ih, Submodule.map_sup]

@[simp] theorem subspaceSum_union {ι : Type w} [DecidableEq ι]
    (L : ι → Submodule K V) (A B : Finset ι) :
    subspaceSum K L (A ∪ B) = subspaceSum K L A ⊔ subspaceSum K L B := by
  simp [subspaceSum, Finset.sup_union]

/-- The sum indexed by an intersection is contained in the intersection of
the two corresponding sums. -/
theorem subspaceSum_inter_le_inf {ι : Type w} [DecidableEq ι]
    (L : ι → Submodule K V) (A B : Finset ι) :
    subspaceSum K L (A ∩ B) ≤ subspaceSum K L A ⊓ subspaceSum K L B := by
  refine le_inf ?_ ?_
  · exact Finset.sup_mono (Finset.inter_subset_left)
  · exact Finset.sup_mono (Finset.inter_subset_right)

/-- The dimension inequalities in Rado's independent-transversal theorem. -/
def HasRadoCapacity {ι : Type w} (L : ι → Submodule K V) : Prop :=
  ∀ J : Finset ι, J.card ≤ Module.finrank K (subspaceSum K L J)

/-- A choice of one vector in each subspace, with all chosen vectors linearly independent. -/
def HasIndependentRepresentatives {ι : Type w} (L : ι → Submodule K V) : Prop :=
  ∃ v : ι → V, (∀ i, v i ∈ L i) ∧ LinearIndependent K v

end Definitions

section Necessity

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]

/-- Independent representatives force all of Rado's dimension inequalities. -/
theorem HasIndependentRepresentatives.hasRadoCapacity {ι : Type w} [Fintype ι]
    {L : ι → Submodule K V} (h : HasIndependentRepresentatives K L) :
    HasRadoCapacity K L := by
  classical
  obtain ⟨v, hvL, hv⟩ := h
  intro J
  let S := subspaceSum K L J
  let w : J → S := fun i ↦
    ⟨v i, (Finset.le_sup (f := L) i.property) (hvL i)⟩
  have hwV : LinearIndependent K (fun i : J ↦ (w i : V)) :=
    hv.comp (fun i : J ↦ (i : ι)) Subtype.val_injective
  have hw : LinearIndependent K w := by
    apply LinearIndependent.of_comp S.subtype
    simpa [Function.comp_def, w] using hwV
  simpa [S] using hw.fintype_card_le_finrank

end Necessity

section Reindexing

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

/-- Rado capacity is unchanged by a bijective reindexing. -/
theorem HasRadoCapacity.comp_equiv {ι ι' : Type w} [Fintype ι] [Fintype ι']
    (e : ι ≃ ι') {L : ι' → Submodule K V} (h : HasRadoCapacity K L) :
    HasRadoCapacity K (L ∘ e) := by
  classical
  intro J
  have hJ := h (J.map e.toEmbedding)
  rw [subspaceSum, Finset.sup_map] at hJ
  simpa [subspaceSum, Function.comp_def] using hJ

/-- Independent representatives are unchanged by a bijective reindexing. -/
theorem HasIndependentRepresentatives.of_comp_equiv {ι ι' : Type w}
    (e : ι ≃ ι') {L : ι' → Submodule K V}
    (h : HasIndependentRepresentatives K (L ∘ e)) :
    HasIndependentRepresentatives K L := by
  obtain ⟨v, hvL, hv⟩ := h
  let v' : ι' → V := v ∘ e.symm
  refine ⟨v', ?_, ?_⟩
  · intro i
    simpa [v', Function.comp_def] using hvL (e.symm i)
  · apply (linearIndependent_equiv e).mp
    simpa [v', Function.comp_def] using hv

end Reindexing

section TightSubfamilies

variable {K : Type u} {V : Type v} [Field K]
variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The union of two tight subfamilies is tight.  This is the finite-dimensional
submodularity step behind Rado's theorem. -/
private theorem tight_union {ι : Type w} [Fintype ι] [DecidableEq ι]
    (L : ι → Submodule K V) (hcap : HasRadoCapacity K L)
    (A B : Finset ι)
    (hA : A.card = Module.finrank K (subspaceSum K L A))
    (hB : B.card = Module.finrank K (subspaceSum K L B)) :
    (A ∪ B).card = Module.finrank K (subspaceSum K L (A ∪ B)) := by
  classical
  let SA := subspaceSum K L A
  let SB := subspaceSum K L B
  let SI := subspaceSum K L (A ∩ B)
  have hcapU := hcap (A ∪ B)
  have hcapI := hcap (A ∩ B)
  have hSIle : SI ≤ SA ⊓ SB := by
    simpa [SA, SB, SI] using subspaceSum_inter_le_inf K L A B
  have hdimI : Module.finrank K SI ≤ Module.finrank K (↥(SA ⊓ SB)) :=
    Submodule.finrank_mono hSIle
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq SA SB
  have hsumU : subspaceSum K L (A ∪ B) = SA ⊔ SB := by
    simp [SA, SB]
  have hcard := Finset.card_union_add_card_inter A B
  have hA' : A.card = Module.finrank K SA := by simpa [SA] using hA
  have hB' : B.card = Module.finrank K SB := by simpa [SB] using hB
  have hcapI' : (A ∩ B).card ≤ Module.finrank K SI := by simpa [SI] using hcapI
  have hdim' :
      Module.finrank K (subspaceSum K L (A ∪ B)) +
          Module.finrank K (↥(SA ⊓ SB)) =
        Module.finrank K SA + Module.finrank K SB := by
    rw [hsumU]
    exact hdim
  omega

/-- A finite union of tight subfamilies is tight. -/
private theorem tight_finset_sup {ι : Type w} [Fintype ι] [DecidableEq ι]
    (L : ι → Submodule K V) (hcap : HasRadoCapacity K L)
    (s : Finset (Finset ι))
    (hs : ∀ J ∈ s,
      J.card = Module.finrank K (subspaceSum K L J)) :
    (s.sup id).card = Module.finrank K (subspaceSum K L (s.sup id)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sup_empty]
      change 0 = Module.finrank K (subspaceSum K L (∅ : Finset ι))
      rw [subspaceSum_empty]
      simp
  | @insert J s hJs ih =>
      rw [Finset.sup_insert]
      exact tight_union L hcap J (s.sup id) (hs J (by simp))
        (ih (fun I hI ↦ hs I (by simp [hI])))

end TightSubfamilies

section DistinguishedVector

variable {K : Type u} {V : Type v} [Field K]
variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The distinguished vector can in fact be chosen over an arbitrary field.
All tight subfamilies are contained in their (tight) finite union, so avoiding
one proper subspace is enough. -/
private theorem exists_distinguished_vector_any_field {ι : Type w} [Fintype ι]
    (L : Option ι → Submodule K V) (hcap : HasRadoCapacity K L) :
    ∃ x : V, x ∈ L none ∧
      ∀ J : Finset ι,
        J.card = Module.finrank K (subspaceSum K (fun i ↦ L (some i)) J) →
          x ∉ subspaceSum K (fun i ↦ L (some i)) J := by
  classical
  let Lr : ι → Submodule K V := fun i ↦ L (some i)
  have hcapr : HasRadoCapacity K Lr := by
    intro J
    have h := hcap (J.map Function.Embedding.some)
    rw [subspaceSum, Finset.sup_map] at h
    simpa [Lr, subspaceSum, Function.comp_def] using h
  let tightSets : Finset (Finset ι) :=
    Finset.univ.filter fun J ↦
      J.card = Module.finrank K (subspaceSum K Lr J)
  let U : Finset ι := tightSets.sup id
  have hmembers : ∀ J ∈ tightSets,
      J.card = Module.finrank K (subspaceSum K Lr J) := by
    intro J hJ
    simpa [tightSets] using hJ
  have hUtight : U.card = Module.finrank K (subspaceSum K Lr U) := by
    simpa [U] using tight_finset_sup Lr hcapr tightSets hmembers
  have hnotle : ¬ L none ≤ subspaceSum K Lr U := by
    intro hle
    have hdim := hcap U.insertNone
    have hsup : L none ⊔ subspaceSum K Lr U = subspaceSum K Lr U :=
      sup_eq_right.mpr hle
    rw [Finset.card_insertNone, subspaceSum_insertNone,
      show (fun i ↦ L (some i)) = Lr from rfl, hsup, ← hUtight] at hdim
    omega
  have hnotset : ¬ (L none : Set V) ⊆ (subspaceSum K Lr U : Set V) := hnotle
  obtain ⟨x, hxL, hxU⟩ := Set.not_subset_iff_exists_mem_notMem.mp hnotset
  refine ⟨x, hxL, ?_⟩
  intro J hJ hxJ
  have hJmem : J ∈ tightSets := by
    simp [tightSets, Lr, hJ]
  have hJU : J ⊆ U := by
    have hle : J ≤ tightSets.sup id := Finset.le_sup (f := id) hJmem
    simpa [U] using hle
  have hsumle : subspaceSum K Lr J ≤ subspaceSum K Lr U :=
    Finset.sup_mono hJU
  exact hxU (hsumle (by simpa [Lr] using hxJ))

end DistinguishedVector

section QuotientCapacity

variable {K : Type u} {V : Type v} [Field K]
variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- If the distinguished vector avoids all tight sums, quotienting by its line
preserves the Rado capacity inequalities for the remaining family. -/
private theorem quotient_hasRadoCapacity {ι : Type w} [Fintype ι]
    (L : Option ι → Submodule K V) (hcap : HasRadoCapacity K L)
    (x : V)
    (hxTight : ∀ J : Finset ι,
      J.card = Module.finrank K (subspaceSum K (fun i ↦ L (some i)) J) →
        x ∉ subspaceSum K (fun i ↦ L (some i)) J) :
    HasRadoCapacity K
      (fun i : ι ↦ (L (some i)).map (K ∙ x).mkQ) := by
  classical
  have hx0 : x ≠ 0 := by
    intro hx
    have hzero : (∅ : Finset ι).card =
        Module.finrank K (subspaceSum K (fun i ↦ L (some i)) ∅) := by
      rw [subspaceSum_empty]
      simp
    have havoid := hxTight ∅ hzero
    exact havoid (by simp [hx])
  intro J
  let S := subspaceSum K (fun i ↦ L (some i)) J
  let q : V →ₗ[K] V ⧸ (K ∙ x) := (K ∙ x).mkQ
  have hdim : J.card ≤ Module.finrank K S := by
    have h := hcap (J.map Function.Embedding.some)
    rw [subspaceSum, Finset.sup_map] at h
    simpa [S, subspaceSum, Function.comp_def] using h
  rw [subspaceSum_map]
  change J.card ≤ Module.finrank K (S.map q)
  by_cases htight : J.card = Module.finrank K S
  · have hxS : x ∉ S := hxTight J (by simpa [S] using htight)
    have hdisj : Disjoint S (K ∙ x) :=
      Submodule.disjoint_span_singleton_of_notMem hxS
    have hinj : Function.Injective (q.domRestrict S) := by
      apply LinearMap.injective_domRestrict_iff.mpr
      rw [Submodule.ker_mkQ]
      exact hdisj.eq_bot
    have hmap : Module.finrank K (S.map q) = Module.finrank K S := by
      rw [← LinearMap.range_domRestrict]
      exact LinearMap.finrank_range_of_inj hinj
    rw [hmap, ← htight]
  · have hstrict : J.card < Module.finrank K S := lt_of_le_of_ne hdim htight
    let f : S →ₗ[K] V ⧸ (K ∙ x) := q.domRestrict S
    have hker_le : (LinearMap.ker f).map S.subtype ≤ K ∙ x := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := hy
      have hzq : q z = 0 := by simpa [f] using hz
      simpa [q, ← LinearMap.mem_ker, Submodule.ker_mkQ] using hzq
    have hker_dim : Module.finrank K (LinearMap.ker f) ≤ 1 := by
      rw [← Submodule.finrank_map_subtype_eq S (LinearMap.ker f)]
      exact (Submodule.finrank_mono hker_le).trans_eq
        (finrank_span_singleton hx0)
    have hrank := f.finrank_range_add_finrank_ker
    rw [show LinearMap.range f = S.map q by simp [f]] at hrank
    omega

end QuotientCapacity

section QuotientLifting

variable {K : Type u} {V : Type v} [Field K]
variable [AddCommGroup V] [Module K V]

/-- An independent transversal in the quotient by `K ∙ x` lifts, together
with `x`, to an independent transversal indexed by `Option ι`. -/
private theorem lift_quotient_representatives {ι : Type w}
    (L : Option ι → Submodule K V) (x : V) (hxL : x ∈ L none) (hx0 : x ≠ 0)
    (w : ι → V ⧸ (K ∙ x))
    (hwL : ∀ i, w i ∈ (L (some i)).map (K ∙ x).mkQ)
    (hw : LinearIndependent K w) :
    HasIndependentRepresentatives K L := by
  classical
  have hex : ∀ i, ∃ y : V, y ∈ L (some i) ∧ (K ∙ x).mkQ y = w i := by
    intro i
    exact (Submodule.mem_map.mp (hwL i))
  choose y hyL hyq using hex
  have hyq_li : LinearIndependent K ((K ∙ x).mkQ ∘ y) := by
    have heq : (K ∙ x).mkQ ∘ y = w := by
      funext i
      exact hyq i
    simpa [heq] using hw
  let fx : PUnit.{w + 1} → (K ∙ x) :=
    fun _ ↦ ⟨x, Submodule.mem_span_singleton_self x⟩
  have hfx : LinearIndependent K fx := by
    rw [linearIndependent_unique_iff]
    intro h
    apply hx0
    have h' := congrArg Subtype.val h
    simpa [fx] using h'
  have hsum : LinearIndependent K (Sum.elim (fun z ↦ (fx z : V)) y) :=
    LinearIndependent.sumElim_of_quotient hfx y hyq_li
  let e : Option ι ≃ PUnit.{w + 1} ⊕ ι :=
    (Equiv.optionEquivSumPUnit.{w, w} ι).trans
      (Equiv.sumComm ι PUnit.{w + 1})
  let v : Option ι → V := fun o ↦ o.elim x y
  have hv : LinearIndependent K v := by
    have hcomp : LinearIndependent K ((Sum.elim (fun z ↦ (fx z : V)) y) ∘ e) :=
      (linearIndependent_equiv e).mpr hsum
    have heq : ((Sum.elim (fun z ↦ (fx z : V)) y) ∘ e) = v := by
      funext o
      cases o <;> rfl
    simpa only [heq] using hcomp
  refine ⟨v, ?_, hv⟩
  intro o
  cases o with
  | none => simpa [v] using hxL
  | some i => simpa [v] using hyL i

end QuotientLifting

section RadoTheorem

variable {K : Type u} [Field K]

/-- Sufficiency in Rado's theorem for a finite family of subspaces. -/
theorem hasIndependentRepresentatives_of_hasRadoCapacity
    {ι : Type w} [Fintype ι] {V : Type v}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (L : ι → Submodule K V) (hcap : HasRadoCapacity K L) :
    HasIndependentRepresentatives K L := by
  classical
  let P : ∀ (ι : Type w), [Fintype ι] → Prop := fun ι _ ↦
    ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (L : ι → Submodule K V),
      HasRadoCapacity K L → HasIndependentRepresentatives K L
  have hP : P ι := by
    apply Fintype.induction_empty_option
    · intro α β _ e ih V _ _ _ L hL
      letI : Fintype α := Fintype.ofEquiv β e.symm
      exact HasIndependentRepresentatives.of_comp_equiv e
        (ih V (L ∘ e) (HasRadoCapacity.comp_equiv e hL))
    · intro V _ _ _ L _
      refine ⟨fun i ↦ PEmpty.elim i, ?_, linearIndependent_empty_type⟩
      intro i
      exact PEmpty.elim i
    · intro α _ ih V _ _ _ L hL
      obtain ⟨x, hxL, hxTight⟩ := exists_distinguished_vector_any_field L hL
      have hx0 : x ≠ 0 := by
        intro hx
        have hzero : (∅ : Finset α).card =
            Module.finrank K (subspaceSum K (fun i ↦ L (some i)) ∅) := by
          rw [subspaceSum_empty]
          simp
        exact hxTight ∅ hzero (by simp [hx])
      let Lq : α → Submodule K (V ⧸ (K ∙ x)) :=
        fun i ↦ (L (some i)).map (K ∙ x).mkQ
      have hq : HasRadoCapacity K Lq :=
        quotient_hasRadoCapacity L hL x hxTight
      obtain ⟨w, hwL, hw⟩ := ih (V ⧸ (K ∙ x)) Lq hq
      exact lift_quotient_representatives L x hxL hx0 w hwL hw
  exact hP V L hcap

/-- Finite subspace Rado theorem over an arbitrary field. -/
theorem hasIndependentRepresentatives_iff_hasRadoCapacity
    {ι : Type w} [Fintype ι] {V : Type v}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (L : ι → Submodule K V) :
    HasIndependentRepresentatives K L ↔ HasRadoCapacity K L :=
  ⟨HasIndependentRepresentatives.hasRadoCapacity,
    hasIndependentRepresentatives_of_hasRadoCapacity L⟩

/-- The rational specialization used by the six Bland--Jensen minor
representations. -/
theorem rational_subspace_rado
    {ι : Type w} [Fintype ι] {V : Type v}
    [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (L : ι → Submodule ℚ V) :
    (∃ v : ι → V, (∀ i, v i ∈ L i) ∧ LinearIndependent ℚ v) ↔
      ∀ J : Finset ι,
        J.card ≤ Module.finrank ℚ (subspaceSum ℚ L J) :=
  hasIndependentRepresentatives_iff_hasRadoCapacity L

end RadoTheorem

section SimultaneousGenericSelection

open MvPolynomial

variable {R : Type u} [CommRing R] [IsDomain R] [Infinite R]

/-- A nonzero multivariate polynomial over an infinite integral domain has a
point at which it does not vanish. -/
theorem MvPolynomial.exists_eval_ne_zero {σ : Type w}
    (p : MvPolynomial σ R) (hp : p ≠ 0) :
    ∃ x : σ → R, MvPolynomial.eval x p ≠ 0 := by
  by_contra h
  push Not at h
  apply hp
  apply MvPolynomial.funext
  intro x
  simpa using h x

/-- Finitely many nonzero multivariate polynomials over an infinite integral
domain are simultaneously nonzero at some common point. -/
theorem MvPolynomial.exists_eval_ne_zero_forall
    {σ : Type w} {τ : Type*} (s : Finset τ)
    (p : τ → MvPolynomial σ R) (hp : ∀ i ∈ s, p i ≠ 0) :
    ∃ x : σ → R, ∀ i ∈ s, MvPolynomial.eval x (p i) ≠ 0 := by
  classical
  have hprod : s.prod p ≠ 0 := Finset.prod_ne_zero_iff.mpr hp
  obtain ⟨x, hx⟩ := MvPolynomial.exists_eval_ne_zero (s.prod p) hprod
  refine ⟨x, ?_⟩
  rw [MvPolynomial.eval_prod] at hx
  exact Finset.prod_ne_zero_iff.mp hx

/-- Individual nonvanishing witnesses for finitely many polynomial constraints
can be replaced by one common witness. -/
theorem MvPolynomial.exists_eval_ne_zero_forall_of_forall_exists
    {σ : Type w} {τ : Type*} [Fintype τ]
    (p : τ → MvPolynomial σ R)
    (h : ∀ i, ∃ x : σ → R, MvPolynomial.eval x (p i) ≠ 0) :
    ∃ x : σ → R, ∀ i, MvPolynomial.eval x (p i) ≠ 0 := by
  classical
  have hp : ∀ i, p i ≠ 0 := by
    intro i hi
    obtain ⟨x, hx⟩ := h i
    simp [hi] at hx
  obtain ⟨x, hx⟩ :=
    MvPolynomial.exists_eval_ne_zero_forall (Finset.univ : Finset τ) p
      (by simpa using hp)
  exact ⟨x, by simpa using hx⟩

/-- Rational specialization of simultaneous generic nonvanishing. -/
theorem simultaneous_rational_nonvanishing
    {σ : Type w} {τ : Type*} [Fintype τ]
    (p : τ → MvPolynomial σ ℚ)
    (h : ∀ i, ∃ x : σ → ℚ, MvPolynomial.eval x (p i) ≠ 0) :
    ∃ x : σ → ℚ, ∀ i, MvPolynomial.eval x (p i) ≠ 0 :=
  MvPolynomial.exists_eval_ne_zero_forall_of_forall_exists p h

/-- Determinant-facing form of simultaneous rational generic selection.
If every determinant is represented by a multivariate polynomial and each
constraint is feasible somewhere, then all matrices are nonsingular for one
common rational parameter assignment. -/
theorem simultaneous_rational_matrix_nonsingular
    {σ : Type w} {τ : Type*} [Fintype τ] {n : ℕ}
    (A : τ → (σ → ℚ) → Matrix (Fin n) (Fin n) ℚ)
    (p : τ → MvPolynomial σ ℚ)
    (hpoly : ∀ i x, MvPolynomial.eval x (p i) = Matrix.det (A i x))
    (hfeasible : ∀ i, ∃ x : σ → ℚ, Matrix.det (A i x) ≠ 0) :
    ∃ x : σ → ℚ, ∀ i, Matrix.det (A i x) ≠ 0 := by
  have hindividual : ∀ i, ∃ x : σ → ℚ, MvPolynomial.eval x (p i) ≠ 0 := by
    intro i
    obtain ⟨x, hx⟩ := hfeasible i
    exact ⟨x, by simpa [hpoly i x] using hx⟩
  obtain ⟨x, hx⟩ := simultaneous_rational_nonvanishing p hindividual
  exact ⟨x, fun i ↦ by simpa [hpoly i x] using hx i⟩

/-- Direct polynomial-matrix form used for determinant constraints.  If each
polynomial matrix can be made nonsingular by some rational specialization,
then one rational specialization makes every matrix in the finite family
nonsingular. -/
theorem simultaneous_rational_polynomial_matrix_nonsingular
    {σ : Type w} {τ : Type*} [Fintype τ] {n : ℕ}
    (A : τ → Matrix (Fin n) (Fin n) (MvPolynomial σ ℚ))
    (hfeasible : ∀ i, ∃ x : σ → ℚ,
      Matrix.det ((MvPolynomial.eval x).mapMatrix (A i)) ≠ 0) :
    ∃ x : σ → ℚ, ∀ i,
      Matrix.det ((MvPolynomial.eval x).mapMatrix (A i)) ≠ 0 := by
  let p : τ → MvPolynomial σ ℚ := fun i ↦ Matrix.det (A i)
  let Aeval : τ → (σ → ℚ) → Matrix (Fin n) (Fin n) ℚ :=
    fun i x ↦ (MvPolynomial.eval x).mapMatrix (A i)
  apply simultaneous_rational_matrix_nonsingular Aeval p
  · intro i x
    exact (RingHom.map_det (MvPolynomial.eval x) (A i))
  · exact hfeasible

end SimultaneousGenericSelection

end BlandJensenFormal.BlandJensenMI
