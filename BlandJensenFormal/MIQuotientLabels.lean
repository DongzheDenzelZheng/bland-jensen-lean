import Mathlib.Tactic

/-!
# Finite quotient-label kernels for the proposed `MI_n` representations

The proposed representations of the six one-element minor types reduce their
parameter-independent part to a finite configuration in a quotient of
dimension two or three.  This file checks that finite geometry exactly:

* for the three deletion templates, it classifies every determinant-zero
  triple of distinct rational quotient labels;
* for the three contraction templates, it classifies equality and
  projective collinearity of all two-dimensional quotient labels.

The block multiplicities depending on `n` have disappeared from these
statements.  They re-enter only in the generic-subspace/Rado argument outside
this file.  In particular, this file does **not** define the matroids `MI_n`,
does **not** formalize Rado's theorem, and does **not** prove representability
or minor-minimality of `MI_n`.
-/

namespace BlandJensenFormal.MIQuotientLabels

abbrev Vec2 := Fin 2 → ℚ
abbrev Vec3 := Fin 3 → ℚ

/-- The two-by-two determinant of two rational quotient labels. -/
def det2 (x y : Vec2) : ℚ :=
  x 0 * y 1 - x 1 * y 0

/-- The three-by-three determinant of three rational quotient labels. -/
def det3 (x y z : Vec3) : ℚ :=
  x 0 * (y 1 * z 2 - y 2 * z 1)
    - x 1 * (y 0 * z 2 - y 2 * z 0)
    + x 2 * (y 0 * z 1 - y 1 * z 0)

/- Integer-coordinate certificates let the kernel evaluate the finite
classification tables directly.  The public quotient labels remain rational;
`det3_intCast` is the exact bridge back to those mathematical definitions. -/
private abbrev IntVec3 := Fin 3 → ℤ

private def intDet3 (x y z : IntVec3) : ℤ :=
  x 0 * (y 1 * z 2 - y 2 * z 1)
    - x 1 * (y 0 * z 2 - y 2 * z 0)
    + x 2 * (y 0 * z 1 - y 1 * z 0)

private theorem det3_intCast (x y z : IntVec3) :
    det3 (fun p ↦ (x p : ℚ)) (fun p ↦ (y p : ℚ))
      (fun p ↦ (z p : ℚ)) = (intDet3 x y z : ℚ) := by
  simp [det3, intDet3]

/-- Pairwise distinctness for a labelled triple. -/
abbrev PairwiseDistinct3 {α : Type*} (i j k : α) : Prop :=
  i ≠ j ∧ i ≠ k ∧ j ≠ k

/-- Equality of unordered three-element label sets.  It is used only under
`PairwiseDistinct3`, so no multiplicity information is lost. -/
abbrev SameTriple {α : Type*} [DecidableEq α]
    (i j k x y z : α) : Prop :=
  ({i, j, k} : Finset α) = {x, y, z}

namespace DeleteX

/-- Quotient labels for deletion of an element of the `X` block. -/
inductive Label
  | A | B | C | One | Two | Three | Four
  deriving DecidableEq, Fintype, Repr

/-- The rational three-dimensional quotient configuration
`a,b,c,c-b,a+c,a+b,a+b+c`. -/
def label : Label → Vec3
  | .A => ![1, 0, 0]
  | .B => ![0, 1, 0]
  | .C => ![0, 0, 1]
  | .One => ![0, -1, 1]
  | .Two => ![1, 0, 1]
  | .Three => ![1, 1, 0]
  | .Four => ![1, 1, 1]

private def intLabel : Label → IntVec3
  | .A => ![1, 0, 0]
  | .B => ![0, 1, 0]
  | .C => ![0, 0, 1]
  | .One => ![0, -1, 1]
  | .Two => ![1, 0, 1]
  | .Three => ![1, 1, 0]
  | .Four => ![1, 1, 1]

private theorem label_eq_intCast (i : Label) :
    label i = fun p ↦ (intLabel i p : ℚ) := by
  funext p
  fin_cases i <;> fin_cases p <;>
    norm_num [label, intLabel, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

/-- The six and only six dependent triples of distinct quotient labels in the
`M \ x` template. -/
abbrev ListedDependent (i j k : Label) : Prop :=
  SameTriple i j k .A .B .Three ∨
  SameTriple i j k .A .C .Two ∨
  SameTriple i j k .B .C .One ∨
  SameTriple i j k .B .Two .Four ∨
  SameTriple i j k .C .Three .Four ∨
  SameTriple i j k .One .Two .Three

private theorem int_det_zero_iff_listed :
    ∀ i j k, PairwiseDistinct3 i j k →
      (intDet3 (intLabel i) (intLabel j) (intLabel k) = 0 ↔
        ListedDependent i j k) := by
  decide

/-- Exact finite-geometric completeness of the `M \ x` quotient table. -/
theorem det_zero_iff_listed :
    ∀ i j k, PairwiseDistinct3 i j k →
      (det3 (label i) (label j) (label k) = 0 ↔ ListedDependent i j k) := by
  intro i j k hdistinct
  rw [label_eq_intCast i, label_eq_intCast j, label_eq_intCast k,
    det3_intCast]
  exact_mod_cast int_det_zero_iff_listed i j k hdistinct

theorem rich_plane_A_B_Three :
    det3 (label .A) (label .B) (label .Three) = 0 := by
  norm_num [det3, label, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem rich_plane_A_C_Two :
    det3 (label .A) (label .C) (label .Two) = 0 := by
  norm_num [det3, label, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem rich_plane_B_C_One :
    det3 (label .B) (label .C) (label .One) = 0 := by
  norm_num [det3, label, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem rich_plane_B_Two_Four :
    det3 (label .B) (label .Two) (label .Four) = 0 := by
  norm_num [det3, label, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem rich_plane_C_Three_Four :
    det3 (label .C) (label .Three) (label .Four) = 0 := by
  norm_num [det3, label, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem special_T_One_Two_Three :
    det3 (label .One) (label .Two) (label .Three) = 0 := by
  norm_num [det3, label, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

/-- The tempting extra triple `a,c-b,a+b+c` is not dependent over `ℚ`;
its determinant is exactly `-2`.  This is the characteristic-two exception
that must not be silently discarded in the paper proof. -/
theorem exceptional_A_One_Four_det :
    det3 (label .A) (label .One) (label .Four) = -2 := by
  norm_num [det3, label, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

end DeleteX

namespace DeleteOne

/-- Quotient labels for deletion of the special element `1`. -/
inductive Label
  | A | B | C | Two | Three | Four
  deriving DecidableEq, Fintype, Repr

/-- The rational configuration `a,b,c,a+c,a+b,a+b+c`. -/
def label : Label → Vec3
  | .A => ![1, 0, 0]
  | .B => ![0, 1, 0]
  | .C => ![0, 0, 1]
  | .Two => ![1, 0, 1]
  | .Three => ![1, 1, 0]
  | .Four => ![1, 1, 1]

private def intLabel : Label → IntVec3
  | .A => ![1, 0, 0]
  | .B => ![0, 1, 0]
  | .C => ![0, 0, 1]
  | .Two => ![1, 0, 1]
  | .Three => ![1, 1, 0]
  | .Four => ![1, 1, 1]

private theorem label_eq_intCast (i : Label) :
    label i = fun p ↦ (intLabel i p : ℚ) := by
  funext p
  fin_cases i <;> fin_cases p <;>
    norm_num [label, intLabel, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

/-- The four and only four dependent triples of distinct quotient labels in
the `M \ 1` template. -/
abbrev ListedDependent (i j k : Label) : Prop :=
  SameTriple i j k .A .B .Three ∨
  SameTriple i j k .A .C .Two ∨
  SameTriple i j k .B .Two .Four ∨
  SameTriple i j k .C .Three .Four

private theorem int_det_zero_iff_listed :
    ∀ i j k, PairwiseDistinct3 i j k →
      (intDet3 (intLabel i) (intLabel j) (intLabel k) = 0 ↔
        ListedDependent i j k) := by
  decide

/-- Exact finite-geometric completeness of the `M \ 1` quotient table. -/
theorem det_zero_iff_listed :
    ∀ i j k, PairwiseDistinct3 i j k →
      (det3 (label i) (label j) (label k) = 0 ↔ ListedDependent i j k) := by
  intro i j k hdistinct
  rw [label_eq_intCast i, label_eq_intCast j, label_eq_intCast k,
    det3_intCast]
  exact_mod_cast int_det_zero_iff_listed i j k hdistinct

theorem rich_plane_A_B_Three :
    det3 (label .A) (label .B) (label .Three) = 0 := by
  norm_num [det3, label, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem rich_plane_A_C_Two :
    det3 (label .A) (label .C) (label .Two) = 0 := by
  norm_num [det3, label, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem rich_plane_B_Two_Four :
    det3 (label .B) (label .Two) (label .Four) = 0 := by
  norm_num [det3, label, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem rich_plane_C_Three_Four :
    det3 (label .C) (label .Three) (label .Four) = 0 := by
  norm_num [det3, label, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

end DeleteOne

namespace DeleteFour

/-- Quotient labels for deletion of the special element `4`. -/
inductive Label
  | A | B | C | One | Two | Three
  deriving DecidableEq, Fintype, Repr

/-- The rational configuration `a,b,c,b+c,a+c,b-a`. -/
def label : Label → Vec3
  | .A => ![1, 0, 0]
  | .B => ![0, 1, 0]
  | .C => ![0, 0, 1]
  | .One => ![0, 1, 1]
  | .Two => ![1, 0, 1]
  | .Three => ![-1, 1, 0]

private def intLabel : Label → IntVec3
  | .A => ![1, 0, 0]
  | .B => ![0, 1, 0]
  | .C => ![0, 0, 1]
  | .One => ![0, 1, 1]
  | .Two => ![1, 0, 1]
  | .Three => ![-1, 1, 0]

private theorem label_eq_intCast (i : Label) :
    label i = fun p ↦ (intLabel i p : ℚ) := by
  funext p
  fin_cases i <;> fin_cases p <;>
    norm_num [label, intLabel, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

/-- The four and only four dependent triples of distinct quotient labels in
the `M \ 4` template. -/
abbrev ListedDependent (i j k : Label) : Prop :=
  SameTriple i j k .A .B .Three ∨
  SameTriple i j k .A .C .Two ∨
  SameTriple i j k .B .C .One ∨
  SameTriple i j k .One .Two .Three

private theorem int_det_zero_iff_listed :
    ∀ i j k, PairwiseDistinct3 i j k →
      (intDet3 (intLabel i) (intLabel j) (intLabel k) = 0 ↔
        ListedDependent i j k) := by
  decide

/-- Exact finite-geometric completeness of the `M \ 4` quotient table. -/
theorem det_zero_iff_listed :
    ∀ i j k, PairwiseDistinct3 i j k →
      (det3 (label i) (label j) (label k) = 0 ↔ ListedDependent i j k) := by
  intro i j k hdistinct
  rw [label_eq_intCast i, label_eq_intCast j, label_eq_intCast k,
    det3_intCast]
  exact_mod_cast int_det_zero_iff_listed i j k hdistinct

theorem rich_plane_A_B_Three :
    det3 (label .A) (label .B) (label .Three) = 0 := by
  norm_num [det3, label, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem rich_plane_A_C_Two :
    det3 (label .A) (label .C) (label .Two) = 0 := by
  norm_num [det3, label, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem rich_plane_B_C_One :
    det3 (label .B) (label .C) (label .One) = 0 := by
  norm_num [det3, label, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem special_T_One_Two_Three :
    det3 (label .One) (label .Two) (label .Three) = 0 := by
  norm_num [det3, label, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

end DeleteFour

namespace ContractX

/-- Quotient labels for contraction of an element of the `X` block. -/
inductive Label
  | X | Y | Z | One | Two | Three | Four
  deriving DecidableEq, Fintype, Repr

/-- The two-dimensional quotient labels
`0,b,c,b+c,c,b,b+c`. -/
def label : Label → Vec2
  | .X => ![0, 0]
  | .Y => ![1, 0]
  | .Z => ![0, 1]
  | .One => ![1, 1]
  | .Two => ![0, 1]
  | .Three => ![1, 0]
  | .Four => ![1, 1]

/-- The three nonzero quotient directions: `b`, `c`, and `b+c`.
The value on `X` is arbitrary because `X` has zero quotient label. -/
def lineClass : Label → Fin 3
  | .X | .Y | .Three => 0
  | .Z | .Two => 1
  | .One | .Four => 2

theorem forced_label_equalities :
    label .Y = label .Three ∧
      label .Z = label .Two ∧ label .One = label .Four := by
  simp [label]

/-- Away from the zero `X` label, equality of labels is exactly equality of
the three displayed quotient directions. -/
theorem label_eq_iff_lineClass_eq :
    ∀ i j, i ≠ .X ∧ j ≠ .X →
      (label i = label j ↔ lineClass i = lineClass j) := by
  intro i j hne
  fin_cases i <;> fin_cases j
  all_goals norm_num at hne
  all_goals simp [label, lineClass]

/-- Away from the zero `X` label, vanishing of the two-by-two determinant is
exactly membership in the same one of the three rich quotient lines. -/
theorem det_zero_iff_lineClass_eq :
    ∀ i j, i ≠ .X ∧ j ≠ .X →
      (det2 (label i) (label j) = 0 ↔ lineClass i = lineClass j) := by
  intro i j hne
  fin_cases i <;> fin_cases j
  all_goals norm_num at hne
  all_goals simp [det2, label, lineClass,
    Matrix.cons_val_zero, Matrix.cons_val_one]

end ContractX

namespace ContractOne

/-- Quotient labels for contraction of the special element `1`. -/
inductive Label
  | X | Y | Z | Two | Three | Four
  deriving DecidableEq, Fintype, Repr

/-- Representatives for three distinct quotient lines `k,h,h,l,l,k`. -/
def label : Label → Vec2
  | .X => ![0, 1]
  | .Y => ![1, 0]
  | .Z => ![1, 0]
  | .Two => ![1, 1]
  | .Three => ![1, 1]
  | .Four => ![0, 1]

/-- Direction classes `h`, `k`, and `l`. -/
def lineClass : Label → Fin 3
  | .Y | .Z => 0
  | .X | .Four => 1
  | .Two | .Three => 2

theorem forced_label_equalities :
    label .Y = label .Z ∧
      label .X = label .Four ∧ label .Two = label .Three := by
  simp [label]

theorem label_eq_iff_lineClass_eq :
    ∀ i j, label i = label j ↔ lineClass i = lineClass j := by
  intro i j
  fin_cases i <;> fin_cases j
  all_goals simp [label, lineClass]

/-- The only projective coincidences are the three intended rich lines
`{Y,Z}`, `{X,4}`, and `{2,3}`. -/
theorem det_zero_iff_lineClass_eq :
    ∀ i j, det2 (label i) (label j) = 0 ↔ lineClass i = lineClass j := by
  intro i j
  fin_cases i <;> fin_cases j
  all_goals simp [det2, label, lineClass,
    Matrix.cons_val_zero, Matrix.cons_val_one]

end ContractOne

namespace ContractFour

/-- Quotient labels for contraction of the special element `4`. -/
inductive Label
  | X | Y | Z | One | Two | Three
  deriving DecidableEq, Fintype, Repr

/-- Representatives `a,b,a+b,a,b,a+b`. -/
def label : Label → Vec2
  | .X => ![1, 0]
  | .Y => ![0, 1]
  | .Z => ![1, 1]
  | .One => ![1, 0]
  | .Two => ![0, 1]
  | .Three => ![1, 1]

/-- Direction classes `a`, `b`, and `a+b`. -/
def lineClass : Label → Fin 3
  | .X | .One => 0
  | .Y | .Two => 1
  | .Z | .Three => 2

theorem forced_label_equalities :
    label .X = label .One ∧
      label .Y = label .Two ∧ label .Z = label .Three := by
  simp [label]

theorem label_eq_iff_lineClass_eq :
    ∀ i j, label i = label j ↔ lineClass i = lineClass j := by
  intro i j
  fin_cases i <;> fin_cases j
  all_goals simp [label, lineClass]

/-- The only projective coincidences are the three intended circuit lines
`{X,1}`, `{Y,2}`, and `{Z,3}`. -/
theorem det_zero_iff_lineClass_eq :
    ∀ i j, det2 (label i) (label j) = 0 ↔ lineClass i = lineClass j := by
  intro i j
  fin_cases i <;> fin_cases j
  all_goals simp [det2, label, lineClass,
    Matrix.cons_val_zero, Matrix.cons_val_one]

end ContractFour

end BlandJensenFormal.MIQuotientLabels
