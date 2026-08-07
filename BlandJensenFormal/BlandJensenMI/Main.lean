import BlandJensenFormal.BlandJensenMI.MainInfrastructure
import BlandJensenFormal.BlandJensenMI.PackagedFamily
import BlandJensenFormal.BlandJensenMI.Representations
import BlandJensenFormal.BlandJensenMI.SignedWeakOrientation

/-!
# Bland--Jensen excluded-minor theorem

This is the target-facing entry point.  It combines the nine-equation
non-weak-orientability certificate, the six exact rational representations,
the symmetry reduction, minor closure, and cardinal separation.
-/

namespace BlandJensenFormal.BlandJensenMI

open Family

/-- Every member of the De Loera--Lee--Margulies--Miller family is an
excluded minor for Bland--Jensen weak orientability. -/
theorem MI_isWeakOrientabilityExcludedMinor (n : ℕ) :
    IsWeakOrientabilityExcludedMinor (MI n) := by
  let h := six_representative_rational_representations n
  exact MI_isWeakOrientabilityExcludedMinor_of_six_representatives n
    h.deleteX h.deleteOne h.deleteFour
    h.contractX h.contractOne h.contractFour

/-- Uniform form of the excluded-minor theorem. -/
theorem all_MI_are_weakOrientabilityExcludedMinors :
    ∀ n : ℕ, IsWeakOrientabilityExcludedMinor (MI n) :=
  MI_isWeakOrientabilityExcludedMinor

/-- The family consists of excluded minors and is pairwise nonisomorphic. -/
theorem infinite_pairwise_nonisomorphic_excluded_minor_family :
    (∀ n : ℕ, IsWeakOrientabilityExcludedMinor (MI n)) ∧
      Pairwise (fun m n ↦ ¬ MatroidIsomorphic (MI m) (MI n)) :=
  ⟨all_MI_are_weakOrientabilityExcludedMinors,
    pairwise_MI_not_matroidIsomorphic⟩

/-- No finite family of packaged matroids can cover, up to isomorphism, all
excluded minors for weak orientability.  In particular there is no finite
excluded-minor characterization. -/
theorem bland_jensen_no_finite_excluded_minor_cover :
    ¬ HasFiniteWeakOrientabilityExcludedMinorCover.{0} :=
  not_hasFiniteWeakOrientabilityExcludedMinorCover_of_MI
    all_MI_are_weakOrientabilityExcludedMinors

/-- **Bland--Jensen's 1987 conjecture.**  There is no finite set `F` of
finite forbidden matroids such that a finite matroid is weakly orientable if
and only if it contains no member of `F` as a minor, where both membership in
the minor order and the forbidden matroids are understood up to matroid
isomorphism across carrier types. -/
theorem bland_jensen_no_finite_weakOrientability_forbiddenMinorCharacterization :
    ¬ ∃ F : Set MatroidPackage.{0},
      F.Finite ∧
      (∀ N ∈ F, N.IsFinite) ∧
      ∀ M : MatroidPackage.{0}, M.IsFinite →
        (WeaklyOrientable M.matroid ↔
          ∀ N ∈ F, ¬ N.IsMinorOf M) :=
  not_exists_finite_weakOrientability_forbiddenMinorCharacterization_of_MI
    all_MI_are_weakOrientabilityExcludedMinors

/-- Source-facing form of Bland--Jensen's conjecture.  This is the same final
forbidden-minor statement, now phrased directly with the literal signed-set
definition of weak orientability rather than the equivalent `F2` system. -/
theorem bland_jensen_no_finite_signedWeakOrientability_forbiddenMinorCharacterization :
    ¬ ∃ F : Set MatroidPackage.{0},
      F.Finite ∧
      (∀ N ∈ F, N.IsFinite) ∧
      ∀ M : MatroidPackage.{0}, M.IsFinite →
        (SignedWeaklyOrientable M.matroid ↔
          ∀ N ∈ F, ¬ N.IsMinorOf M) := by
  rintro ⟨F, hFinite, hForbiddenFinite, hCharacterizes⟩
  apply bland_jensen_no_finite_weakOrientability_forbiddenMinorCharacterization
  refine ⟨F, hFinite, hForbiddenFinite, ?_⟩
  intro M hM
  simpa only [signedWeaklyOrientable_iff_weaklyOrientable] using
    hCharacterizes M hM

end BlandJensenFormal.BlandJensenMI
