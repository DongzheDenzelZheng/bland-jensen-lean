import BlandJensenFormal.BlandJensenMI.Basic

/-!
# Signed-set semantics for Bland--Jensen weak orientability

This module connects the source definition of a weak orientation, stated with
signed sets taking values in `{0, +1, -1}`, to the sign-bit predicate
`WeaklyOrientable` used by the rest of the formalization.

The encoding of a nonzero sign in `F2 = ZMod 2` is

* `+1 ↦ 0`, and
* `-1 ↦ 1`.

The main theorem `signedWeaklyOrientable_iff_weaklyOrientable` proves that the
two definitions are equivalent.  In particular, the sign-bit formulation does
not weaken the quantification over actual circuits and cocircuits or the
two-element circuit--cocircuit orthogonality condition.
-/

namespace BlandJensenFormal.BlandJensenMI

open Set
open BlandJensenFormal.PhaseObstructionAlgebra

universe u

/-! ## The three signs and their `F2` encoding -/

/-- A value of a signed set: zero, positive, or negative. -/
inductive SignValue where
  | zero
  | positive
  | negative
  deriving DecidableEq

namespace SignValue

/-- Reversal of a sign. -/
def negate : SignValue → SignValue
  | zero => zero
  | positive => negative
  | negative => positive

/-- Multiplication of signs, with zero absorbing. -/
def mul : SignValue → SignValue → SignValue
  | zero, _ => zero
  | _, zero => zero
  | positive, positive => positive
  | positive, negative => negative
  | negative, positive => negative
  | negative, negative => positive

/-- The bit of a sign, using `+1 ↦ 0` and `-1 ↦ 1`.
The value on zero is an irrelevant default. -/
def toBit : SignValue → F2
  | zero => 0
  | positive => 0
  | negative => 1

/-- The nonzero sign represented by a bit of `F2`. -/
def ofBit (b : F2) : SignValue :=
  if b = 0 then positive else negative

@[simp] theorem negate_zero : negate zero = zero := rfl
@[simp] theorem negate_positive : negate positive = negative := rfl
@[simp] theorem negate_negative : negate negative = positive := rfl

@[simp] theorem toBit_zero : toBit zero = 0 := rfl
@[simp] theorem toBit_positive : toBit positive = 0 := rfl
@[simp] theorem toBit_negative : toBit negative = 1 := rfl

@[simp] theorem ofBit_zero : ofBit 0 = positive := by
  simp [ofBit]

@[simp] theorem ofBit_one : ofBit 1 = negative := by
  simp [ofBit]

@[simp] theorem ofBit_ne_zero (b : F2) : ofBit b ≠ zero := by
  simp only [ofBit]
  split <;> simp

/-- `F2` has exactly the two values used by the sign encoding. -/
theorem f2_eq_zero_or_one (b : F2) : b = 0 ∨ b = 1 := by
  fin_cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The characteristic-two identity used by sign multiplication. -/
@[simp] theorem one_add_one_eq_zero : (1 : F2) + 1 = 0 := by
  exact CharTwo.add_self_eq_zero 1

/-- Decoding followed by encoding is the identity on `F2`. -/
@[simp] theorem toBit_ofBit (b : F2) : toBit (ofBit b) = b := by
  rcases f2_eq_zero_or_one b with rfl | rfl <;> simp

/-- Every nonzero three-valued sign is recovered from its bit. -/
theorem ofBit_toBit_of_ne_zero {s : SignValue} (hs : s ≠ zero) :
    ofBit (toBit s) = s := by
  cases s <;> simp_all

@[simp] theorem positive_ne_zero : positive ≠ zero := by
  simp

@[simp] theorem negative_ne_zero : negative ≠ zero := by
  simp

@[simp] theorem positive_ne_negative : positive ≠ negative := by
  simp

theorem mul_ne_zero_iff {x y : SignValue} :
    mul x y ≠ zero ↔ x ≠ zero ∧ y ≠ zero := by
  cases x <;> cases y <;> simp [mul]

/-- On nonzero signs, multiplication is addition of sign bits. -/
theorem toBit_mul_of_ne_zero {x y : SignValue}
    (hx : x ≠ zero) (hy : y ≠ zero) :
    toBit (mul x y) = toBit x + toBit y := by
  cases x <;> cases y <;> simp_all [mul, one_add_one_eq_zero]

/-- Nonzero signs are determined by their bits. -/
theorem eq_of_ne_zero_of_toBit_eq {x y : SignValue}
    (hx : x ≠ zero) (hy : y ≠ zero) (h : toBit x = toBit y) : x = y := by
  cases x <;> cases y <;> simp_all

theorem mul_eq_positive_iff {x y : SignValue}
    (hx : x ≠ zero) (hy : y ≠ zero) :
    mul x y = positive ↔ toBit x + toBit y = 0 := by
  constructor
  · intro h
    have hbit := congrArg toBit h
    simpa [toBit_mul_of_ne_zero hx hy] using hbit
  · intro h
    apply eq_of_ne_zero_of_toBit_eq
    · exact mul_ne_zero_iff.mpr ⟨hx, hy⟩
    · exact positive_ne_zero
    · calc
        toBit (mul x y) = toBit x + toBit y := toBit_mul_of_ne_zero hx hy
        _ = 0 := h
        _ = toBit positive := rfl

theorem mul_eq_negative_iff {x y : SignValue}
    (hx : x ≠ zero) (hy : y ≠ zero) :
    mul x y = negative ↔ toBit x + toBit y = 1 := by
  constructor
  · intro h
    have hbit := congrArg toBit h
    simpa [toBit_mul_of_ne_zero hx hy] using hbit
  · intro h
    apply eq_of_ne_zero_of_toBit_eq
    · exact mul_ne_zero_iff.mpr ⟨hx, hy⟩
    · exact negative_ne_zero
    · calc
        toBit (mul x y) = toBit x + toBit y := toBit_mul_of_ne_zero hx hy
        _ = 1 := h
        _ = toBit negative := rfl

end SignValue

/-! ## Signed sets and orthogonality -/

/-- A signed set on `α` is a function with values in `{0,+1,-1}`. -/
abbrev SignedSet (α : Type u) := α → SignValue

namespace SignedSet

/-- The support of a signed set. -/
def support {α : Type u} (X : SignedSet α) : Set α :=
  {e | X e ≠ SignValue.zero}

/-- Orthogonality of signed sets: the common support is empty, or their
coordinatewise products contain both signs. -/
def Orthogonal {α : Type u} (X Y : SignedSet α) : Prop :=
  support X ∩ support Y = ∅ ∨
    (∃ e, SignValue.mul (X e) (Y e) = SignValue.positive) ∧
      (∃ f, SignValue.mul (X f) (Y f) = SignValue.negative)

/-- The explicit form of orthogonality on a two-element common support. -/
def BinaryOrthogonal {α : Type u} (X Y : SignedSet α) (e f : α) : Prop :=
  (SignValue.mul (X e) (Y e) = SignValue.positive ∧
      SignValue.mul (X f) (Y f) = SignValue.negative) ∨
    (SignValue.mul (X e) (Y e) = SignValue.negative ∧
      SignValue.mul (X f) (Y f) = SignValue.positive)

private theorem mem_support_inter_of_mul_eq_positive {α : Type u}
    {X Y : SignedSet α} {e : α}
    (h : SignValue.mul (X e) (Y e) = SignValue.positive) :
    e ∈ support X ∩ support Y := by
  have hne : SignValue.mul (X e) (Y e) ≠ SignValue.zero := by
    rw [h]
    exact SignValue.positive_ne_zero
  exact SignValue.mul_ne_zero_iff.mp hne

private theorem mem_support_inter_of_mul_eq_negative {α : Type u}
    {X Y : SignedSet α} {e : α}
    (h : SignValue.mul (X e) (Y e) = SignValue.negative) :
    e ∈ support X ∩ support Y := by
  have hne : SignValue.mul (X e) (Y e) ≠ SignValue.zero := by
    rw [h]
    exact SignValue.negative_ne_zero
  exact SignValue.mul_ne_zero_iff.mp hne

/-- On a two-element common support, signed-set orthogonality says exactly
that the two nonzero products have opposite signs. -/
theorem orthogonal_iff_binaryOrthogonal {α : Type u}
    {X Y : SignedSet α} {e f : α}
    (hSupport : support X ∩ support Y = {e, f}) :
    Orthogonal X Y ↔ BinaryOrthogonal X Y e f := by
  constructor
  · intro hOrth
    rcases hOrth with hEmpty | ⟨⟨p, hp⟩, ⟨n, hn⟩⟩
    · have he : e ∈ support X ∩ support Y := by
        rw [hSupport]
        simp
      rw [hEmpty] at he
      simp at he
    · have hpMem := mem_support_inter_of_mul_eq_positive hp
      have hnMem := mem_support_inter_of_mul_eq_negative hn
      rw [hSupport] at hpMem hnMem
      have hpCases : p = e ∨ p = f := by simpa [eq_comm] using hpMem
      have hnCases : n = e ∨ n = f := by simpa [eq_comm] using hnMem
      rcases hpCases with rfl | rfl <;> rcases hnCases with rfl | rfl
      · exact False.elim (SignValue.positive_ne_negative (hp.symm.trans hn))
      · exact Or.inl ⟨hp, hn⟩
      · exact Or.inr ⟨hn, hp⟩
      · exact False.elim (SignValue.positive_ne_negative (hp.symm.trans hn))
  · rintro (⟨he, hf⟩ | ⟨he, hf⟩)
    · exact Or.inr ⟨⟨e, he⟩, ⟨f, hf⟩⟩
    · exact Or.inr ⟨⟨f, hf⟩, ⟨e, he⟩⟩

/-- Binary orthogonality is precisely the Bland--Jensen four-bit equation. -/
theorem binaryOrthogonal_iff_bitEquation {α : Type u}
    {X Y : SignedSet α} {e f : α}
    (hXe : X e ≠ SignValue.zero) (hYe : Y e ≠ SignValue.zero)
    (hXf : X f ≠ SignValue.zero) (hYf : Y f ≠ SignValue.zero) :
    BinaryOrthogonal X Y e f ↔
      SignValue.toBit (X e) + SignValue.toBit (Y e) +
        SignValue.toBit (X f) + SignValue.toBit (Y f) = 1 := by
  constructor
  · rintro (⟨he, hf⟩ | ⟨he, hf⟩)
    · have heBits := (SignValue.mul_eq_positive_iff hXe hYe).mp he
      have hfBits := (SignValue.mul_eq_negative_iff hXf hYf).mp hf
      calc
        SignValue.toBit (X e) + SignValue.toBit (Y e) +
              SignValue.toBit (X f) + SignValue.toBit (Y f) =
            (SignValue.toBit (X e) + SignValue.toBit (Y e)) +
              (SignValue.toBit (X f) + SignValue.toBit (Y f)) := by abel
        _ = 0 + 1 := by rw [heBits, hfBits]
        _ = 1 := zero_add 1
    · have heBits := (SignValue.mul_eq_negative_iff hXe hYe).mp he
      have hfBits := (SignValue.mul_eq_positive_iff hXf hYf).mp hf
      calc
        SignValue.toBit (X e) + SignValue.toBit (Y e) +
              SignValue.toBit (X f) + SignValue.toBit (Y f) =
            (SignValue.toBit (X e) + SignValue.toBit (Y e)) +
              (SignValue.toBit (X f) + SignValue.toBit (Y f)) := by abel
        _ = 1 + 0 := by rw [heBits, hfBits]
        _ = 1 := add_zero 1
  · intro hEquation
    rcases SignValue.f2_eq_zero_or_one
        (SignValue.toBit (X e) + SignValue.toBit (Y e)) with heBits | heBits <;>
      rcases SignValue.f2_eq_zero_or_one
        (SignValue.toBit (X f) + SignValue.toBit (Y f)) with hfBits | hfBits
    · have hFalse : (0 : F2) = 1 := by
        calc
          0 = 0 + 0 := (zero_add 0).symm
          _ = (SignValue.toBit (X e) + SignValue.toBit (Y e)) +
              (SignValue.toBit (X f) + SignValue.toBit (Y f)) := by
                rw [heBits, hfBits]
          _ = SignValue.toBit (X e) + SignValue.toBit (Y e) +
              SignValue.toBit (X f) + SignValue.toBit (Y f) := by abel
          _ = 1 := hEquation
      exact False.elim (zero_ne_one hFalse)
    · exact Or.inl ⟨
        (SignValue.mul_eq_positive_iff hXe hYe).mpr heBits,
        (SignValue.mul_eq_negative_iff hXf hYf).mpr hfBits⟩
    · exact Or.inr ⟨
        (SignValue.mul_eq_negative_iff hXe hYe).mpr heBits,
        (SignValue.mul_eq_positive_iff hXf hYf).mpr hfBits⟩
    · have hFalse : (0 : F2) = 1 := by
        calc
          0 = 1 + 1 := SignValue.one_add_one_eq_zero.symm
          _ = (SignValue.toBit (X e) + SignValue.toBit (Y e)) +
              (SignValue.toBit (X f) + SignValue.toBit (Y f)) := by
                rw [heBits, hfBits]
          _ = SignValue.toBit (X e) + SignValue.toBit (Y e) +
              SignValue.toBit (X f) + SignValue.toBit (Y f) := by abel
          _ = 1 := hEquation
      exact False.elim (zero_ne_one hFalse)

/-- Turn a set and a bit assignment into a signed set with exactly that
support. -/
noncomputable def ofBits {α : Type u} (S : Set α) (bits : α → F2) : SignedSet α := by
  classical
  exact fun e => if e ∈ S then SignValue.ofBit (bits e) else SignValue.zero

@[simp] theorem support_ofBits {α : Type u} (S : Set α) (bits : α → F2) :
    support (ofBits S bits) = S := by
  classical
  ext e
  by_cases he : e ∈ S <;> simp [support, ofBits, he]

@[simp] theorem ofBits_apply_of_mem {α : Type u} {S : Set α}
    (bits : α → F2) {e : α} (he : e ∈ S) :
    ofBits S bits e = SignValue.ofBit (bits e) := by
  classical
  simp [ofBits, he]

@[simp] theorem ofBits_apply_of_not_mem {α : Type u} {S : Set α}
    (bits : α → F2) {e : α} (he : e ∉ S) :
    ofBits S bits e = SignValue.zero := by
  classical
  simp [ofBits, he]

end SignedSet

/-! ## Equivalence of the source and sign-bit definitions -/

/-- Weak orientability stated literally with a signed set for every actual
circuit and cocircuit.  The chosen signed sets have the prescribed supports,
and every two-element circuit--cocircuit intersection is orthogonal. -/
def SignedWeaklyOrientable {α : Type u} (M : Matroid α) : Prop :=
  ∃ circuitSignature cocircuitSignature : Set α → SignedSet α,
    (∀ C : Set α, M.IsCircuit C →
      SignedSet.support (circuitSignature C) = C) ∧
    (∀ D : Set α, M.IsCocircuit D →
      SignedSet.support (cocircuitSignature D) = D) ∧
    ∀ (C D : Set α) (e f : α),
      M.IsCircuit C → M.IsCocircuit D → e ≠ f → C ∩ D = {e, f} →
        SignedSet.Orthogonal (circuitSignature C) (cocircuitSignature D)

/-- The literal signed-set definition of weak orientability is equivalent to
the `F2` Bland--Jensen system used throughout this development. -/
theorem signedWeaklyOrientable_iff_weaklyOrientable {α : Type u}
    (M : Matroid α) :
    SignedWeaklyOrientable M ↔ WeaklyOrientable M := by
  constructor
  · rintro ⟨circuitSignature, cocircuitSignature,
      hCircuitSupport, hCocircuitSupport, hOrthogonal⟩
    refine ⟨
      (fun C e => SignValue.toBit (circuitSignature C e)),
      (fun D e => SignValue.toBit (cocircuitSignature D e)), ?_⟩
    intro C D e f hC hD hef hCD
    have heCD : e ∈ C ∩ D := by
      rw [hCD]
      simp
    have hfCD : f ∈ C ∩ D := by
      rw [hCD]
      simp
    have hCe : circuitSignature C e ≠ SignValue.zero := by
      change e ∈ SignedSet.support (circuitSignature C)
      rw [hCircuitSupport C hC]
      exact heCD.1
    have hDe : cocircuitSignature D e ≠ SignValue.zero := by
      change e ∈ SignedSet.support (cocircuitSignature D)
      rw [hCocircuitSupport D hD]
      exact heCD.2
    have hCf : circuitSignature C f ≠ SignValue.zero := by
      change f ∈ SignedSet.support (circuitSignature C)
      rw [hCircuitSupport C hC]
      exact hfCD.1
    have hDf : cocircuitSignature D f ≠ SignValue.zero := by
      change f ∈ SignedSet.support (cocircuitSignature D)
      rw [hCocircuitSupport D hD]
      exact hfCD.2
    have hSupport :
        SignedSet.support (circuitSignature C) ∩
            SignedSet.support (cocircuitSignature D) = {e, f} := by
      rw [hCircuitSupport C hC, hCocircuitSupport D hD, hCD]
    have hBinary : SignedSet.BinaryOrthogonal
        (circuitSignature C) (cocircuitSignature D) e f :=
      (SignedSet.orthogonal_iff_binaryOrthogonal hSupport).mp
        (hOrthogonal C D e f hC hD hef hCD)
    unfold BlandJensenEquation
    exact (SignedSet.binaryOrthogonal_iff_bitEquation hCe hDe hCf hDf).mp hBinary
  · rintro ⟨circuitSign, cocircuitSign, hEquation⟩
    let circuitSignature : Set α → SignedSet α :=
      fun C => SignedSet.ofBits C (circuitSign C)
    let cocircuitSignature : Set α → SignedSet α :=
      fun D => SignedSet.ofBits D (cocircuitSign D)
    refine ⟨circuitSignature, cocircuitSignature, ?_, ?_, ?_⟩
    · intro C _
      simp [circuitSignature]
    · intro D _
      simp [cocircuitSignature]
    · intro C D e f hC hD hef hCD
      have heCD : e ∈ C ∩ D := by
        rw [hCD]
        simp
      have hfCD : f ∈ C ∩ D := by
        rw [hCD]
        simp
      have hCe : circuitSignature C e ≠ SignValue.zero := by
        simp [circuitSignature, heCD.1]
      have hDe : cocircuitSignature D e ≠ SignValue.zero := by
        simp [cocircuitSignature, heCD.2]
      have hCf : circuitSignature C f ≠ SignValue.zero := by
        simp [circuitSignature, hfCD.1]
      have hDf : cocircuitSignature D f ≠ SignValue.zero := by
        simp [cocircuitSignature, hfCD.2]
      have hBits :
          SignValue.toBit (circuitSignature C e) +
              SignValue.toBit (cocircuitSignature D e) +
              SignValue.toBit (circuitSignature C f) +
              SignValue.toBit (cocircuitSignature D f) = 1 := by
        simpa [circuitSignature, cocircuitSignature, heCD.1, heCD.2,
          hfCD.1, hfCD.2] using hEquation C D e f hC hD hef hCD
      have hBinary : SignedSet.BinaryOrthogonal
          (circuitSignature C) (cocircuitSignature D) e f :=
        (SignedSet.binaryOrthogonal_iff_bitEquation hCe hDe hCf hDf).mpr hBits
      apply (SignedSet.orthogonal_iff_binaryOrthogonal ?_).mpr hBinary
      simp [circuitSignature, cocircuitSignature, hCD]

end BlandJensenFormal.BlandJensenMI
