import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.Field.ZMod

/-!
# The finite-product kernel of the phase Nullstellensatz

For a finite set `S`, the algebra `S → k` is the algebra of `k`-valued
functions on `S`.  A finite family of functions has no common zero exactly
when it generates the unit ideal.  This is the finite-product half of the
hypercube phase Nullstellensatz.

Taking `S = Q → Bool` and `k = ℚ` gives the function algebra on the sign
cube `{+1,-1}^Q`.  The separate comparison

`\mathbb Q[t_q]/(t_q^2-1) \cong (Q → Bool) → \mathbb Q`

is proved in the accompanying mathematical note; it is not formalized in
this file.  No graph instance or extracted obstruction certificate is
checked here.
-/

namespace BlandJensenFormal.PhaseObstructionAlgebra

/-- A common zero of a family `L` of functions on `S`. -/
def HasCommonZero {A S k : Type*} [Zero k] (L : A → S → k) : Prop :=
  ∃ s, ∀ a, L a s = 0

/-- In a finite product of fields, pointwise Bézout coefficients exist exactly
when a finite family of functions has no common zero.

The reverse implication is constructive at each point: choose one nonzero
generator and use its inverse as the sole nonzero coefficient there. -/
theorem exists_pointwise_bezout_iff_no_common_zero
    {A S k : Type*} [Fintype A] [Field k] (L : A → S → k) :
    (∃ F : A → S → k, ∑ a, F a * L a = 1) ↔
      ¬ HasCommonZero L := by
  classical
  constructor
  · rintro ⟨F, hF⟩ ⟨s, hs⟩
    have hone := congrFun hF s
    have hzero : ∑ a, F a s * L a s = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      simp [hs a]
    simp only [Finset.sum_apply, Pi.mul_apply, Pi.one_apply] at hone
    rw [hzero] at hone
    exact zero_ne_one hone
  · intro hnozero
    have hnonzero : ∀ s, ∃ a, L a s ≠ 0 := by
      intro s
      by_contra h
      simp only [not_exists, not_not] at h
      exact hnozero ⟨s, h⟩
    choose pick hpick using hnonzero
    let F : A → S → k := fun a s ↦
      if pick s = a then (L a s)⁻¹ else 0
    refine ⟨F, funext fun s ↦ ?_⟩
    simp only [Finset.sum_apply, Pi.mul_apply, Pi.one_apply]
    rw [Finset.sum_eq_single (pick s)]
    · simp [F, hpick s]
    · intro b _ hb
      simp [F, Ne.symm hb]
    · intro hmissing
      exact (hmissing (Finset.mem_univ (pick s))).elim

/-- Ideal-theoretic form of the finite-product Nullstellensatz. -/
theorem span_eq_top_iff_no_common_zero
    {A S k : Type*} [Fintype A] [Field k] (L : A → S → k) :
    Ideal.span (Set.range L) = ⊤ ↔ ¬ HasCommonZero L := by
  rw [Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun]
  exact exists_pointwise_bezout_iff_no_common_zero L

/-- The sign cube indexed by `Q`; `true` represents `+1` and `false`
represents `-1`. -/
abbrev SignCube (Q : Type*) := Q → Bool

/-- Rational coordinate function on the sign cube. -/
def signCoordinate {Q : Type*} (q : Q) : SignCube Q → ℚ :=
  fun s ↦ if s q then 1 else -1

/-- Every sign coordinate satisfies the defining hypercube equation. -/
@[simp] theorem signCoordinate_sq {Q : Type*} (q : Q) (s : SignCube Q) :
    signCoordinate q s ^ 2 = 1 := by
  simp only [signCoordinate]
  split <;> norm_num

/-- The phase Nullstellensatz directly on the rational sign-cube function
algebra.  The cells may be linear forms, but the theorem is valid for
arbitrary functions. -/
theorem cube_phase_nullstellensatz
    {A Q : Type*} [Fintype A] (L : A → SignCube Q → ℚ) :
    Ideal.span (Set.range L) = ⊤ ↔
      ¬ ∃ s : SignCube Q, ∀ a, L a s = 0 :=
  span_eq_top_iff_no_common_zero L

/-! ## The support-four parity anomaly

A signed `2`-in-`4` cell has product `+1`.  After encoding signs as bits,
every support-four cell is therefore one affine equation `H x = kappa` over
`F₂`.  The next theorem is the exact dual obstruction used by a parity
certificate: a left-kernel vector pairing oddly with `kappa` rules out every
global phase assignment.
-/

abbrev F2 := ZMod 2

/-- A bit assignment solves the affine support-four parity system. -/
def SolvesParitySystem {C E : Type*} [Fintype E]
    (H : C → E → F2) (kappa : C → F2) (x : E → F2) : Prop :=
  ∀ c, ∑ e, H c e * x e = kappa c

/-- A left-kernel witness with odd pairing against the affine right-hand
side is a strict no-go certificate. -/
theorem no_parity_solution_of_anomaly
    {C E : Type*} [Fintype C] [Fintype E]
    (H : C → E → F2) (kappa : C → F2) (lambda : C → F2)
    (hleft : ∀ e, ∑ c, lambda c * H c e = 0)
    (hodd : ∑ c, lambda c * kappa c = 1) :
    ¬ ∃ x, SolvesParitySystem H kappa x := by
  rintro ⟨x, hx⟩
  have hzero : ∑ c, lambda c * kappa c = 0 := by
    calc
      ∑ c, lambda c * kappa c =
          ∑ c, lambda c * (∑ e, H c e * x e) := by
            apply Finset.sum_congr rfl
            intro c _
            rw [hx c]
      _ = ∑ c, ∑ e, (lambda c * H c e) * x e := by
            apply Finset.sum_congr rfl
            intro c _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro e _
            simp only [mul_assoc]
      _ = ∑ e, ∑ c, (lambda c * H c e) * x e :=
            Finset.sum_comm
      _ = ∑ e, (∑ c, lambda c * H c e) * x e := by
            apply Finset.sum_congr rfl
            intro e _
            rw [Finset.sum_mul]
      _ = 0 := by simp [hleft]
  rw [hodd] at hzero
  exact one_ne_zero hzero

/-- Switching variables changes `kappa` by a column-space element `H s`. -/
def switchedRightHandSide {C E : Type*} [Fintype E]
    (H : C → E → F2) (kappa : C → F2) (s : E → F2) : C → F2 :=
  fun c ↦ kappa c + ∑ e, H c e * s e

/-- The anomaly pairing is switching-invariant.  This is the elementary
representative-level form of the class `[kappa]` in `coker(H)`. -/
theorem anomaly_pairing_switchInvariant
    {C E : Type*} [Fintype C] [Fintype E]
    (H : C → E → F2) (kappa : C → F2) (lambda : C → F2)
    (s : E → F2)
    (hleft : ∀ e, ∑ c, lambda c * H c e = 0) :
    ∑ c, lambda c * switchedRightHandSide H kappa s c =
      ∑ c, lambda c * kappa c := by
  simp only [switchedRightHandSide, mul_add, Finset.sum_add_distrib]
  suffices hcross : ∑ c, lambda c * (∑ e, H c e * s e) = 0 by
    rw [hcross, add_zero]
  calc
    ∑ c, lambda c * (∑ e, H c e * s e) =
        ∑ c, ∑ e, (lambda c * H c e) * s e := by
          apply Finset.sum_congr rfl
          intro c _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e _
          simp only [mul_assoc]
    _ = ∑ e, ∑ c, (lambda c * H c e) * s e :=
          Finset.sum_comm
    _ = ∑ e, (∑ c, lambda c * H c e) * s e := by
          apply Finset.sum_congr rfl
          intro e _
          rw [Finset.sum_mul]
    _ = 0 := by simp [hleft]

end BlandJensenFormal.PhaseObstructionAlgebra
