import BlandJensenFormal.BlandJensenMI.Family
import BlandJensenFormal.BlandJensenMI.ExcludedMinor

/-!
# Cardinal separation of the Bland--Jensen family

The members `MI n` live on dependent element types.  Matroid isomorphism was
therefore defined across two possibly different ambient types.  The exact
ground-set count `3n+7` immediately separates all members of the family.
-/

namespace BlandJensenFormal.BlandJensenMI

open Family

/-- The ground-set cardinalities of `MI n` are strictly increasing. -/
theorem strictMono_encard_MI :
    StrictMono (fun n ↦ (MI n).E.encard) := by
  intro m n hmn
  simp only [encard_MI_ground, ENat.coe_lt_coe]
  omega

/-- Distinct indices give nonisomorphic members of the family. -/
theorem MI_not_matroidIsomorphic_of_ne {m n : ℕ} (hmn : m ≠ n) :
    ¬ MatroidIsomorphic (MI m) (MI n) := by
  apply not_matroidIsomorphic_of_encard_ground_ne
  intro hcard
  rw [encard_MI_ground, encard_MI_ground] at hcard
  have hNat : 3 * m + 7 = 3 * n + 7 := by
    exact ENat.coe_inj.mp hcard
  apply hmn
  omega

/-- Pairwise form of cardinal separation. -/
theorem pairwise_MI_not_matroidIsomorphic :
    Pairwise (fun m n ↦ ¬ MatroidIsomorphic (MI m) (MI n)) := by
  intro m n hmn
  exact MI_not_matroidIsomorphic_of_ne hmn

end BlandJensenFormal.BlandJensenMI
