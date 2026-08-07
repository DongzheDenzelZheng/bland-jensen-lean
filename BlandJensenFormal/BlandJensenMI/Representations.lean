import BlandJensenFormal.BlandJensenMI.DeletionCapacity
import BlandJensenFormal.BlandJensenMI.DeletionOtherCapacity
import BlandJensenFormal.BlandJensenMI.ContractionCapacity
import BlandJensenFormal.BlandJensenMI.ContractionFourCapacity

/-!
# The six rational representative minors

This module exposes a uniform public interface for the six target-matroid
representation theorems.  Each field concerns the actual Mathlib deletion or
contraction of `Family.MI n`, rather than an auxiliary template matroid.
-/

namespace BlandJensenFormal.BlandJensenMI

open Family

/-- Rational representations of the six orbit representatives for
one-element deletions and contractions of `MI n`. -/
structure SixRepresentativeRationalRepresentations (n : ℕ) : Prop where
  deleteX :
    RationallyRepresentable (Matroid.delete (MI n) {x0 n})
  deleteOne :
    RationallyRepresentable (Matroid.delete (MI n) {one n})
  deleteFour :
    RationallyRepresentable (Matroid.delete (MI n) {four n})
  contractX :
    RationallyRepresentable (Matroid.contract (MI n) {x0 n})
  contractOne :
    RationallyRepresentable (Matroid.contract (MI n) {one n})
  contractFour :
    RationallyRepresentable (Matroid.contract (MI n) {four n})

/-- All six representative one-element minors are rationally representable,
uniformly for every parameter `n`. -/
theorem six_representative_rational_representations (n : ℕ) :
    SixRepresentativeRationalRepresentations n where
  deleteX :=
    DeletionCapacity.DeleteX.rationallyRepresentable_delete_x0 n
  deleteOne := delete_one_rationallyRepresentable n
  deleteFour := delete_four_rationallyRepresentable n
  contractX :=
    ContractionCapacity.ContractX.rationallyRepresentable_contract_x0 n
  contractOne :=
    ContractionCapacity.ContractOne.rationallyRepresentable_contract_one n
  contractFour :=
    ContractionFourCapacity.ContractFour.contract_four_rationallyRepresentable n

end BlandJensenFormal.BlandJensenMI
