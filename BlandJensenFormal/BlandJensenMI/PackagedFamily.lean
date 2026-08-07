import BlandJensenFormal.BlandJensenMI.InfiniteFamily

/-!
# A universe-safe finite-cover statement for heterogeneous matroids

The matroids `MI n` have different element types.  Packaging a carrier type
together with its matroid lets the final theorem state, without identifying
those carriers, that no finite family can contain representatives of all
weak-orientability excluded-minor isomorphism classes.
-/

namespace BlandJensenFormal.BlandJensenMI

open Family

universe u

/-- A matroid together with its ambient carrier type. -/
structure MatroidPackage where
  carrier : Type u
  matroid : Matroid carrier

/-- Isomorphism of packaged matroids ignores the ambient carrier names. -/
def MatroidPackage.Isomorphic (P Q : MatroidPackage.{u}) : Prop :=
  MatroidIsomorphic P.matroid Q.matroid

/-- The ground-set cardinality of a packaged matroid. -/
noncomputable def MatroidPackage.groundEncard (P : MatroidPackage.{u}) : ℕ∞ :=
  P.matroid.E.encard

theorem MatroidPackage.Isomorphic.groundEncard_eq
    {P Q : MatroidPackage.{u}} (h : P.Isomorphic Q) :
    P.groundEncard = Q.groundEncard :=
  h.encard_ground_eq

/-- A packaged matroid is finite when its ground set is finite.  This is a
proposition rather than a typeclass so that finiteness can be carried through
heterogeneous packages without installing local instances. -/
def MatroidPackage.IsFinite (P : MatroidPackage.{u}) : Prop :=
  P.matroid.E.Finite

/-- `N.IsMinorOf M` means that an isomorphic copy of `N` is a minor of `M`.

Mathlib's minor relation compares matroids on one ambient type.  The witness
`N'` is the copy of `N` on the ambient type of `M`; the isomorphism makes this
definition independent of the names of the two carrier types. -/
def MatroidPackage.IsMinorOf (N M : MatroidPackage.{u}) : Prop :=
  ∃ N' : Matroid M.carrier,
    N' ≤m M.matroid ∧ MatroidIsomorphic N.matroid N'

/-- A family `F` is a forbidden-minor characterization of weak orientability
for finite matroids if every member of `F` is finite and a finite packaged
matroid is weakly orientable exactly when it has no member of `F` as a minor,
up to isomorphism. -/
def IsWeakOrientabilityForbiddenMinorCharacterization
    (F : Set MatroidPackage.{u}) : Prop :=
  (∀ N ∈ F, N.IsFinite) ∧
    ∀ M : MatroidPackage.{u}, M.IsFinite →
      (WeaklyOrientable M.matroid ↔
        ∀ N ∈ F, ¬ N.IsMinorOf M)

/-- There is a finite forbidden-minor characterization of weak orientability
in the class of finite matroids. -/
def HasFiniteWeakOrientabilityForbiddenMinorCharacterization : Prop :=
  ∃ F : Set MatroidPackage.{u}, F.Finite ∧
    IsWeakOrientabilityForbiddenMinorCharacterization F

/-- Packaged specialization of being an excluded minor for weak
orientability. -/
def MatroidPackage.IsWeakOrientabilityExcludedMinor
    (P : MatroidPackage.{u}) : Prop :=
  BlandJensenFormal.BlandJensenMI.IsWeakOrientabilityExcludedMinor P.matroid

/-- A finite cover contains, up to isomorphism, a representative of every
weak-orientability excluded minor. -/
def HasFiniteWeakOrientabilityExcludedMinorCover : Prop :=
  ∃ F : Set MatroidPackage.{u}, F.Finite ∧
    ∀ P : MatroidPackage.{u}, P.IsWeakOrientabilityExcludedMinor →
      ∃ Q ∈ F, P.Isomorphic Q

/-- The Bland--Jensen member `MI n`, retaining its own element type. -/
def packagedMI (n : ℕ) : MatroidPackage.{0} :=
  ⟨Element n, MI n⟩

@[simp] theorem packagedMI_groundEncard (n : ℕ) :
    (packagedMI n).groundEncard = (3 * n + 7 : ℕ) := by
  exact encard_MI_ground n

/-- Any proof that all `MI n` are excluded minors rules out a finite cover of
their isomorphism classes, and therefore rules out a finite excluded-minor
characterization. -/
theorem not_hasFiniteWeakOrientabilityExcludedMinorCover_of_MI
    (hExcluded : ∀ n, IsWeakOrientabilityExcludedMinor (MI n)) :
    ¬ HasFiniteWeakOrientabilityExcludedMinorCover.{0} := by
  rintro ⟨F, hFinite, hCover⟩
  have hRepresentative : ∀ n, ∃ Q ∈ F, (packagedMI n).Isomorphic Q := by
    intro n
    exact hCover (packagedMI n) (hExcluded n)
  choose representative hRepresentativeMem hRepresentativeIso using
    hRepresentative
  have hRepresentativeInjective : Function.Injective representative := by
    intro i j hij
    apply strictMono_encard_MI.injective
    calc
      (MI i).E.encard = (representative i).groundEncard :=
        (hRepresentativeIso i).groundEncard_eq
      _ = (representative j).groundEncard := by rw [hij]
      _ = (MI j).E.encard :=
        (hRepresentativeIso j).groundEncard_eq.symm
  have hInfiniteRange : (Set.range representative).Infinite :=
    Set.infinite_range_of_injective hRepresentativeInjective
  exact hInfiniteRange
    (hFinite.subset (Set.range_subset_iff.mpr hRepresentativeMem))

/-- An excluded-minor family `MI n` rules out a finite forbidden-minor
characterization in the standard sense: for every finite matroid `M`, weak
orientability is equivalent to avoiding every listed forbidden minor up to
isomorphism.

The conclusion is deliberately written with the defining biconditional
visible.  It is stronger than merely saying that no finite family covers the
already-known excluded minors. -/
theorem not_exists_finite_weakOrientability_forbiddenMinorCharacterization_of_MI
    (hExcluded : ∀ n, IsWeakOrientabilityExcludedMinor (MI n)) :
    ¬ ∃ F : Set MatroidPackage.{0},
      F.Finite ∧
      (∀ N ∈ F, N.IsFinite) ∧
      ∀ M : MatroidPackage.{0}, M.IsFinite →
        (WeaklyOrientable M.matroid ↔
          ∀ N ∈ F, ¬ N.IsMinorOf M) := by
  classical
  rintro ⟨F, hFinite, _hForbiddenFinite, hCharacterizes⟩
  have hRepresentative :
      ∀ n, ∃ Q ∈ F, Q.Isomorphic (packagedMI n) := by
    intro n
    have hMINotWeak : ¬ WeaklyOrientable (MI n) := (hExcluded n).1
    have hMINotAvoids :
        ¬ ∀ Q ∈ F, ¬ Q.IsMinorOf (packagedMI n) := by
      intro hAvoids
      exact hMINotWeak
        ((hCharacterizes (packagedMI n) (MI n).ground_finite).mpr hAvoids)
    push Not at hMINotAvoids
    obtain ⟨Q, hQF, N', hN'MI, hQN'⟩ := hMINotAvoids
    have hN'NotWeak : ¬ WeaklyOrientable N' := by
      intro hN'Weak
      have hN'Finite : N'.E.Finite :=
        (MI n).ground_finite.subset hN'MI.subset
      have hN'Avoids :=
        (hCharacterizes
          ({ carrier := Element n, matroid := N' } : MatroidPackage.{0})
          hN'Finite).mp hN'Weak
      exact hN'Avoids Q hQF ⟨N', Matroid.IsMinor.refl, hQN'⟩
    have hN'Eq : N' = MI n := by
      by_contra hne
      exact hN'NotWeak ((hExcluded n).2
        (Matroid.isStrictMinor_iff_isMinor_ne.mpr ⟨hN'MI, hne⟩))
    refine ⟨Q, hQF, ?_⟩
    change MatroidIsomorphic Q.matroid (MI n)
    rwa [← hN'Eq]
  choose representative hRepresentativeMem hRepresentativeIso using
    hRepresentative
  have hRepresentativeInjective : Function.Injective representative := by
    intro i j hij
    apply strictMono_encard_MI.injective
    calc
      (MI i).E.encard = (representative i).groundEncard :=
        (hRepresentativeIso i).groundEncard_eq.symm
      _ = (representative j).groundEncard := by rw [hij]
      _ = (MI j).E.encard :=
        (hRepresentativeIso j).groundEncard_eq
  have hInfiniteRange : (Set.range representative).Infinite :=
    Set.infinite_range_of_injective hRepresentativeInjective
  exact hInfiniteRange
    (hFinite.subset (Set.range_subset_iff.mpr hRepresentativeMem))

/-- Bundled form of
`not_exists_finite_weakOrientability_forbiddenMinorCharacterization_of_MI`. -/
theorem not_hasFiniteWeakOrientabilityForbiddenMinorCharacterization_of_MI
    (hExcluded : ∀ n, IsWeakOrientabilityExcludedMinor (MI n)) :
    ¬ HasFiniteWeakOrientabilityForbiddenMinorCharacterization.{0} := by
  simpa only [HasFiniteWeakOrientabilityForbiddenMinorCharacterization,
    IsWeakOrientabilityForbiddenMinorCharacterization] using
    not_exists_finite_weakOrientability_forbiddenMinorCharacterization_of_MI
      hExcluded

end BlandJensenFormal.BlandJensenMI
