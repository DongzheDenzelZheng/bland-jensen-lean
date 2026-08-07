import BlandJensenFormal.MIQuotientLabels
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Determinants and independence in the fixed quotient spaces

This file bridges the explicit `det2` and `det3` functions used by the finite
quotient-label audit to Mathlib's linear-independence API.  It contains no
matroid-specific assumptions and no parameter-dependent enumeration.
-/

namespace BlandJensenFormal.BlandJensenMI.QuotientGeometry

open BlandJensenFormal.MIQuotientLabels

/-- The explicit two-by-two determinant is the determinant of the matrix with
the two displayed vectors as columns. -/
theorem det2_eq_matrix_det (x y : Vec2) :
    det2 x y = Matrix.det (fun row col : Fin 2 ↦ ![x, y] col row) := by
  rw [Matrix.det_fin_two]
  simp [det2]
  ring

/-- The explicit three-by-three determinant is the determinant of the matrix
with the three displayed vectors as columns. -/
theorem det3_eq_matrix_det (x y z : Vec3) :
    det3 x y z = Matrix.det (fun row col : Fin 3 ↦ ![x, y, z] col row) := by
  rw [Matrix.det_fin_three]
  simp [det3]
  ring

/-- Two rational two-vectors are linearly independent exactly when their
explicit determinant is nonzero. -/
theorem linearIndependent_vec2_iff_det2_ne_zero (x y : Vec2) :
    LinearIndependent ℚ (![x, y] : Fin 2 → Vec2) ↔ det2 x y ≠ 0 := by
  let A : Matrix (Fin 2) (Fin 2) ℚ := fun row col ↦ ![x, y] col row
  have hcols : A.col = (![x, y] : Fin 2 → Vec2) := by
    funext col
    funext row
    rfl
  constructor
  · intro h
    have hunitA : IsUnit A :=
      Matrix.linearIndependent_cols_iff_isUnit.mp (hcols ▸ h)
    have hunitDet : IsUnit A.det := A.isUnit_iff_isUnit_det.mp hunitA
    rw [det2_eq_matrix_det]
    exact hunitDet.ne_zero
  · intro h
    have hdet : A.det ≠ 0 := by
      rwa [← det2_eq_matrix_det]
    rw [← hcols]
    exact Matrix.linearIndependent_cols_of_det_ne_zero hdet

/-- Three rational three-vectors are linearly independent exactly when their
explicit determinant is nonzero. -/
theorem linearIndependent_vec3_iff_det3_ne_zero (x y z : Vec3) :
    LinearIndependent ℚ (![x, y, z] : Fin 3 → Vec3) ↔ det3 x y z ≠ 0 := by
  let A : Matrix (Fin 3) (Fin 3) ℚ := fun row col ↦ ![x, y, z] col row
  have hcols : A.col = (![x, y, z] : Fin 3 → Vec3) := by
    funext col
    funext row
    rfl
  constructor
  · intro h
    have hunitA : IsUnit A :=
      Matrix.linearIndependent_cols_iff_isUnit.mp (hcols ▸ h)
    have hunitDet : IsUnit A.det := A.isUnit_iff_isUnit_det.mp hunitA
    rw [det3_eq_matrix_det]
    exact hunitDet.ne_zero
  · intro h
    have hdet : A.det ≠ 0 := by
      rwa [← det3_eq_matrix_det]
    rw [← hcols]
    exact Matrix.linearIndependent_cols_of_det_ne_zero hdet

/-- Full rank of a pair is equivalent to its explicit determinant being
nonzero. -/
theorem finrank_span_vec2_eq_two_iff_det2_ne_zero (x y : Vec2) :
    Module.finrank ℚ
        (Submodule.span ℚ (Set.range (![x, y] : Fin 2 → Vec2))) = 2 ↔
      det2 x y ≠ 0 := by
  constructor
  · intro hdim
    apply (linearIndependent_vec2_iff_det2_ne_zero x y).mp
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    simpa only [Fintype.card_fin, Set.finrank] using hdim.symm
  · intro hdet
    have hli := (linearIndependent_vec2_iff_det2_ne_zero x y).mpr hdet
    simpa only [Fintype.card_fin] using finrank_span_eq_card hli

/-- A pair spans at most a line exactly when its explicit determinant
vanishes. -/
theorem finrank_span_vec2_le_one_iff_det2_eq_zero (x y : Vec2) :
    Module.finrank ℚ
        (Submodule.span ℚ (Set.range (![x, y] : Fin 2 → Vec2))) ≤ 1 ↔
      det2 x y = 0 := by
  constructor
  · intro hle
    by_contra hdet
    have hfull := (finrank_span_vec2_eq_two_iff_det2_ne_zero x y).mpr hdet
    omega
  · intro hdet
    have hbound : Module.finrank ℚ
        (Submodule.span ℚ (Set.range (![x, y] : Fin 2 → Vec2))) ≤ 2 := by
      simpa only [Set.finrank, Fintype.card_fin] using
        finrank_range_le_card (![x, y] : Fin 2 → Vec2)
    have hnotfull : Module.finrank ℚ
        (Submodule.span ℚ (Set.range (![x, y] : Fin 2 → Vec2))) ≠ 2 := by
      intro hfull
      exact ((finrank_span_vec2_eq_two_iff_det2_ne_zero x y).mp hfull) hdet
    omega

/-- Full rank of a triple is equivalent to its explicit determinant being
nonzero. -/
theorem finrank_span_vec3_eq_three_iff_det3_ne_zero (x y z : Vec3) :
    Module.finrank ℚ
        (Submodule.span ℚ (Set.range (![x, y, z] : Fin 3 → Vec3))) = 3 ↔
      det3 x y z ≠ 0 := by
  constructor
  · intro hdim
    apply (linearIndependent_vec3_iff_det3_ne_zero x y z).mp
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    simpa only [Fintype.card_fin, Set.finrank] using hdim.symm
  · intro hdet
    have hli := (linearIndependent_vec3_iff_det3_ne_zero x y z).mpr hdet
    simpa only [Fintype.card_fin] using finrank_span_eq_card hli

/-- A triple spans at most a plane exactly when its explicit determinant
vanishes. -/
theorem finrank_span_vec3_le_two_iff_det3_eq_zero (x y z : Vec3) :
    Module.finrank ℚ
        (Submodule.span ℚ (Set.range (![x, y, z] : Fin 3 → Vec3))) ≤ 2 ↔
      det3 x y z = 0 := by
  constructor
  · intro hle
    by_contra hdet
    have hfull := (finrank_span_vec3_eq_three_iff_det3_ne_zero x y z).mpr hdet
    omega
  · intro hdet
    have hbound : Module.finrank ℚ
        (Submodule.span ℚ (Set.range (![x, y, z] : Fin 3 → Vec3))) ≤ 3 := by
      simpa only [Set.finrank, Fintype.card_fin] using
        finrank_range_le_card (![x, y, z] : Fin 3 → Vec3)
    have hnotfull : Module.finrank ℚ
        (Submodule.span ℚ (Set.range (![x, y, z] : Fin 3 → Vec3))) ≠ 3 := by
      intro hfull
      exact ((finrank_span_vec3_eq_three_iff_det3_ne_zero x y z).mp hfull) hdet
    omega

end BlandJensenFormal.BlandJensenMI.QuotientGeometry
