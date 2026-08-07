import BlandJensenFormal.PhaseObstructionAlgebra

/-!
# The parameter-independent nine-cell Bland--Jensen anomaly

This file formalizes the closed parity core occurring in the proposed
`MI_n` weak-orientability obstruction.  It does **not** formalize the
matroids `MI_n`, the claims that the named sets are their circuits and
cocircuits, or any of the minor-minimality/representability arguments.

The nine rows are numbered as follows:

* `0 = (C₁,D₂)`, `1 = (C₁,D₃)`,
* `2 = (C₂,D₁)`, `3 = (C₂,D₃)`,
* `4 = (C₃,D₁)`, `5 = (C₃,D₂)`,
* `6 = (T,D₁)`, `7 = (T,D₂)`, `8 = (T,D₃)`.

The eighteen columns are the circuit/cocircuit flags:

* `0 = (C₁,1)`, `1 = (C₁,4)`,
  `2 = (C₂,2)`, `3 = (C₂,4)`,
  `4 = (C₃,3)`, `5 = (C₃,4)`;
* `6 = (T,1)`, `7 = (T,2)`, `8 = (T,3)`;
* `9 = (D₁,2)`, `10 = (D₁,3)`, `11 = (D₁,4)`,
  `12 = (D₂,1)`, `13 = (D₂,3)`, `14 = (D₂,4)`,
  `15 = (D₃,1)`, `16 = (D₃,2)`, `17 = (D₃,4)`.

For `i != j`, the cell `(C_j,D_i)` contains the four flags above the
intersection `C_j ∩ D_i = {j,4}`.  The cell `(T,D_i)` contains the four
flags above `T ∩ D_i = {1,2,3} \ {i}`.  Thus the displayed matrix is the
literal flag-incidence matrix of these nine cells, conditional only on
those intersection descriptions.  Every flag occurs exactly twice, while
all nine affine right-hand sides are one.  The all-one left-kernel vector
therefore has odd pairing with the right-hand side.
-/

namespace BlandJensenFormal.BlandJensenNineCell

open PhaseObstructionAlgebra

abbrev Cell := Fin 9
abbrev Flag := Fin 18
abbrev Bit := F2

/-- The explicit `9 × 18` incidence matrix in the numbering above. -/
def incidence : Cell → Flag → Bit :=
  ![
    ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0],
    ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1],
    ![0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
  ]

/-- Each of the eighteen flags occurs in exactly two selected cells. -/
theorem each_flag_has_degree_two :
    ∀ flag,
      (Finset.univ.filter (fun cell ↦ incidence cell flag = 1)).card = 2 := by
  decide

/-- The affine Bland--Jensen right-hand side is one on every selected cell. -/
def kappa : Cell → Bit := fun _ ↦ 1

/-- The anomaly witness selects all nine cells. -/
def lambda : Cell → Bit := fun _ ↦ 1

/-- Exact even-column condition for the all-one left-kernel witness. -/
theorem all_one_is_left_kernel :
    ∀ flag, ∑ cell, lambda cell * incidence cell flag = 0 := by
  decide

/-- Nine unit right-hand sides have odd total over `F₂`. -/
theorem all_one_pairing_is_odd :
    ∑ cell, lambda cell * kappa cell = 1 := by
  decide

/-- The parameter-independent nine-cell Bland--Jensen subsystem has no
global assignment of bits to its eighteen circuit/cocircuit flags. -/
theorem no_flag_assignment :
    ¬ ∃ x, SolvesParitySystem incidence kappa x :=
  no_parity_solution_of_anomaly incidence kappa lambda
    all_one_is_left_kernel all_one_pairing_is_odd

end BlandJensenFormal.BlandJensenNineCell
