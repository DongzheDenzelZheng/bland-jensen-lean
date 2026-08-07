import BlandJensenFormal.BlandJensenMI.InfiniteFamily
import BlandJensenFormal.BlandJensenMI.Minors
import BlandJensenFormal.BlandJensenMI.Obstruction
import BlandJensenFormal.BlandJensenMI.Relabeling

/-!
# Final reduction from six representatives to excluded minors

This module isolates the last logical step from the six rational
representations.  It is parameterized by those six results, so the symmetry,
minor closure, and cardinal-separation argument can be checked independently
of the capacity audits that construct the representations.
-/

namespace BlandJensenFormal.BlandJensenMI

open Family

/-- Rational representability of the three representative deletions implies
it for every one-element deletion. -/
theorem all_singleton_deletions_rationallyRepresentable (n : ℕ)
    (hX : RationallyRepresentable (Matroid.delete (MI n) {x0 n}))
    (hOne : RationallyRepresentable (Matroid.delete (MI n) {one n}))
    (hFour : RationallyRepresentable (Matroid.delete (MI n) {four n}))
    (e : Element n) :
    RationallyRepresentable (Matroid.delete (MI n) {e}) := by
  rcases delete_orbit_classification n e with h | h | h
  · obtain ⟨f, hf⟩ := h
    apply (rationallyRepresentable_mapEquiv_iff
      (Matroid.delete (MI n) {e}) f).mp
    rw [hf]
    exact hX
  · obtain ⟨f, hf⟩ := h
    apply (rationallyRepresentable_mapEquiv_iff
      (Matroid.delete (MI n) {e}) f).mp
    rw [hf]
    exact hOne
  · obtain ⟨f, hf⟩ := h
    apply (rationallyRepresentable_mapEquiv_iff
      (Matroid.delete (MI n) {e}) f).mp
    rw [hf]
    exact hFour

/-- Rational representability of the three representative contractions
implies it for every one-element contraction. -/
theorem all_singleton_contractions_rationallyRepresentable (n : ℕ)
    (hX : RationallyRepresentable (Matroid.contract (MI n) {x0 n}))
    (hOne : RationallyRepresentable (Matroid.contract (MI n) {one n}))
    (hFour : RationallyRepresentable (Matroid.contract (MI n) {four n}))
    (e : Element n) :
    RationallyRepresentable (Matroid.contract (MI n) {e}) := by
  rcases contract_orbit_classification n e with h | h | h
  · obtain ⟨f, hf⟩ := h
    apply (rationallyRepresentable_mapEquiv_iff
      (Matroid.contract (MI n) {e}) f).mp
    rw [hf]
    exact hX
  · obtain ⟨f, hf⟩ := h
    apply (rationallyRepresentable_mapEquiv_iff
      (Matroid.contract (MI n) {e}) f).mp
    rw [hf]
    exact hOne
  · obtain ⟨f, hf⟩ := h
    apply (rationallyRepresentable_mapEquiv_iff
      (Matroid.contract (MI n) {e}) f).mp
    rw [hf]
    exact hFour

/-- The six rational representative minors imply that `MI n` is an excluded
minor for weak orientability. -/
theorem MI_isWeakOrientabilityExcludedMinor_of_six_representatives (n : ℕ)
    (hDeleteX : RationallyRepresentable (Matroid.delete (MI n) {x0 n}))
    (hDeleteOne : RationallyRepresentable (Matroid.delete (MI n) {one n}))
    (hDeleteFour : RationallyRepresentable (Matroid.delete (MI n) {four n}))
    (hContractX : RationallyRepresentable (Matroid.contract (MI n) {x0 n}))
    (hContractOne : RationallyRepresentable (Matroid.contract (MI n) {one n}))
    (hContractFour : RationallyRepresentable (Matroid.contract (MI n) {four n})) :
    IsWeakOrientabilityExcludedMinor (MI n) := by
  apply isWeakOrientabilityExcludedMinor_of_singleton_minors
    (MI_not_weaklyOrientable n)
  · intro e _
    exact (all_singleton_contractions_rationallyRepresentable n
      hContractX hContractOne hContractFour e).weaklyOrientable
  · intro e _ _
    exact (all_singleton_deletions_rationallyRepresentable n
      hDeleteX hDeleteOne hDeleteFour e).weaklyOrientable

end BlandJensenFormal.BlandJensenMI
