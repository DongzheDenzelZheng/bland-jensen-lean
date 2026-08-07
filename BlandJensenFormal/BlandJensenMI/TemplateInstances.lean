import BlandJensenFormal.BlandJensenMI.Family
import BlandJensenFormal.BlandJensenMI.GenericRepresentation
import BlandJensenFormal.BlandJensenMI.Templates

/-!
# Element-level instances of the six common-core templates

This file connects the abstract common-core templates to the actual elements
of the Bland--Jensen family.  It has two logically separate parts.

* Product coordinates `Templates.Ambient n q` are identified linearly with
  the column space `Fin (n + q) → ℚ` used by the generic-representation
  compiler.  Linear independence and subspace membership are transported
  across this equivalence.
* For each of the six one-element-minor templates, every `Element n` is
  classified as a surviving large-block element, a surviving special
  element, or the omitted element.  This determines its allowed subspace,
  the set of fixed columns, and the prescribed fixed vector.

The final theorem is a reusable normalization bridge.  Rado's theorem first
chooses independent representatives from the allowed subspaces on one target
basis.  On every fixed line, the chosen nonzero representative is rescaled to
the prescribed vector.  Extending by prescribed fixed vectors and zeros then
produces exactly the individual feasibility witness expected by
`exists_simultaneous_subspace_generic_assignment`.

No statement here audits which subsets are bases of a deletion or
contraction; that belongs to the minor-specific layer.
-/

namespace BlandJensenFormal.BlandJensenMI.TemplateInstances

open Function Set Submodule

/-! ## Product coordinates versus column coordinates -/

/-- Concatenate the common-core and quotient coordinates into one column.
The first `n` coordinates are the common core and the last `q` coordinates
are the quotient label. -/
def ambientCoordinateEquiv (n q : ℕ) :
    Templates.Ambient n q ≃ₗ[ℚ] (Fin (n + q) → ℚ) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin q) ℚ ℚ).symm.trans
    (LinearEquiv.funCongrLeft ℚ ℚ
      (finSumFinEquiv : Fin n ⊕ Fin q ≃ Fin (n + q))).symm

@[simp] theorem ambientCoordinateEquiv_apply_castAdd
    (n q : ℕ) (x : Templates.Ambient n q) (i : Fin n) :
    ambientCoordinateEquiv n q x (Fin.castAdd q i) = x.1 i := by
  rcases x with ⟨x, y⟩
  simp [ambientCoordinateEquiv]

@[simp] theorem ambientCoordinateEquiv_apply_natAdd
    (n q : ℕ) (x : Templates.Ambient n q) (i : Fin q) :
    ambientCoordinateEquiv n q x (Fin.natAdd n i) = x.2 i := by
  rcases x with ⟨x, y⟩
  simp [ambientCoordinateEquiv]

/-- A family is linearly independent before concatenating coordinates iff it
is linearly independent afterwards. -/
theorem linearIndependent_ambientCoordinateEquiv_iff
    {I : Type*} {n q : ℕ} (v : I → Templates.Ambient n q) :
    LinearIndependent ℚ (fun i ↦ ambientCoordinateEquiv n q (v i)) ↔
      LinearIndependent ℚ v := by
  constructor
  · intro h
    rw [linearIndependent_iff'] at h ⊢
    intro s g hsum
    apply h s g
    calc
      ∑ i ∈ s, g i • ambientCoordinateEquiv n q (v i) =
          ambientCoordinateEquiv n q (∑ i ∈ s, g i • v i) := by
            simp
      _ = 0 := by rw [hsum, map_zero]
  · intro h
    rw [linearIndependent_iff'] at h ⊢
    intro s g hsum
    apply h s g
    apply (ambientCoordinateEquiv n q).injective
    simpa using hsum

/-- Membership in a subspace is preserved when both the vector and the
subspace are transported through the coordinate equivalence. -/
theorem ambientCoordinateEquiv_mem_map_iff
    {n q : ℕ} (S : Submodule ℚ (Templates.Ambient n q))
    (x : Templates.Ambient n q) :
    ambientCoordinateEquiv n q x ∈
        S.map (ambientCoordinateEquiv n q).toLinearMap ↔ x ∈ S := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hyx : y = x := (ambientCoordinateEquiv n q).injective hxy
    simpa [hyx] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- In particular, a one-dimensional fixed line is carried to the line
through the transported fixed vector. -/
theorem map_span_singleton_ambientCoordinateEquiv
    {n q : ℕ} (x : Templates.Ambient n q) :
    (ℚ ∙ x).map (ambientCoordinateEquiv n q).toLinearMap =
      ℚ ∙ ambientCoordinateEquiv n q x := by
  rw [Submodule.map_span]
  simp

/-! ## A generic fixed-line normalization bridge -/

/-- Rado capacity on one target, together with the assertion that every
fixed allowed subspace is precisely the line through its prescribed vector,
produces an individual feasibility witness for the generic-selection
compiler.

The target is an embedding, so no two selected columns collide.  Rado gives
an independent vector `w j` on each selected line.  Independence makes every
`w j` nonzero; hence on a fixed line its scalar coefficient relative to
`q (target j)` is nonzero and can be inverted. -/
theorem feasible_assignment_of_radoCapacity_of_fixed_lines
    {E : Type*} {I : Type*} [Fintype I] {V : Type*}
    [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (L : E → Submodule ℚ V) (fixed : Set E) (q : E → V)
    (target : I ↪ E)
    (hFixedLines : ∀ e ∈ fixed, L e = ℚ ∙ q e)
    (hCapacity : HasRadoCapacity ℚ (fun j ↦ L (target j))) :
    ∃ v : E → V,
      (∀ e, v e ∈ L e) ∧
        (∀ e ∈ fixed, v e = q e) ∧
          LinearIndependent ℚ (fun j ↦ v (target j)) := by
  classical
  obtain ⟨w, hwL, hwIndependent⟩ :=
    hasIndependentRepresentatives_of_hasRadoCapacity
      (fun j ↦ L (target j)) hCapacity
  let coefficient : I → ℚ := fun j ↦
    if hj : target j ∈ fixed then
      Classical.choose
        (Submodule.mem_span_singleton.mp
          (show w j ∈ ℚ ∙ q (target j) by
            rw [← hFixedLines (target j) hj]
            exact hwL j))
    else 1
  have coefficient_spec (j : I) (hj : target j ∈ fixed) :
      coefficient j • q (target j) = w j := by
    simp only [coefficient, dif_pos hj]
    exact Classical.choose_spec
      (Submodule.mem_span_singleton.mp
        (show w j ∈ ℚ ∙ q (target j) by
          rw [← hFixedLines (target j) hj]
          exact hwL j))
  have coefficient_ne_zero (j : I) : coefficient j ≠ 0 := by
    by_cases hj : target j ∈ fixed
    · intro hz
      have hwzero : w j = 0 := by
        rw [← coefficient_spec j hj, hz, zero_smul]
      exact hwIndependent.ne_zero j hwzero
    · simp [coefficient, hj]
  let unitCoefficient : I → ℚˣ := fun j ↦
    Units.mk0 (coefficient j) (coefficient_ne_zero j)
  let normalized : I → V :=
    (fun j ↦ (unitCoefficient j)⁻¹) • w
  have normalized_independent : LinearIndependent ℚ normalized := by
    exact hwIndependent.units_smul (fun j ↦ (unitCoefficient j)⁻¹)
  have normalized_mem (j : I) : normalized j ∈ L (target j) := by
    exact smul_mem _ _ (hwL j)
  have normalized_eq_fixed (j : I) (hj : target j ∈ fixed) :
      normalized j = q (target j) := by
    change (unitCoefficient j)⁻¹ • w j = q (target j)
    rw [← coefficient_spec j hj]
    change (↑((unitCoefficient j)⁻¹) : ℚ) •
      (coefficient j • q (target j)) = q (target j)
    rw [smul_smul]
    rw [show (↑((unitCoefficient j)⁻¹) : ℚ) * coefficient j = 1 by
      simpa [unitCoefficient] using inv_mul_cancel₀ (coefficient_ne_zero j)]
    exact one_smul ℚ (q (target j))
  let fallback : E → V := fun e ↦ if e ∈ fixed then q e else 0
  let v : E → V := Function.extend target normalized fallback
  refine ⟨v, ?_, ?_, ?_⟩
  · intro e
    by_cases he : ∃ j, target j = e
    · obtain ⟨j, rfl⟩ := he
      rw [show v (target j) = normalized j by
        exact target.injective.extend_apply normalized fallback j]
      exact normalized_mem j
    · rw [show v e = fallback e by
        exact Function.extend_apply' normalized fallback e he]
      by_cases hef : e ∈ fixed
      · simp only [fallback, if_pos hef]
        rw [hFixedLines e hef]
        exact Submodule.mem_span_singleton_self (q e)
      · simp [fallback, hef]
  · intro e hef
    by_cases he : ∃ j, target j = e
    · obtain ⟨j, rfl⟩ := he
      rw [show v (target j) = normalized j by
        exact target.injective.extend_apply normalized fallback j]
      exact normalized_eq_fixed j hef
    · rw [show v e = fallback e by
        exact Function.extend_apply' normalized fallback e he]
      simp [fallback, hef]
  · have hvTarget : (fun j ↦ v (target j)) = normalized := by
      funext j
      exact target.injective.extend_apply normalized fallback j
    simpa [hvTarget] using normalized_independent

/-- Set-indexed form matching the `hBaseFeasible` argument of the
representation compiler. -/
theorem feasible_assignment_on_set_of_radoCapacity_of_fixed_lines
    {E : Type*} {V : Type*}
    [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (L : E → Submodule ℚ V) (fixed : Set E) (q : E → V)
    (B : Set E) [Fintype B]
    (hFixedLines : ∀ e ∈ fixed, L e = ℚ ∙ q e)
    (hCapacity : HasRadoCapacity ℚ (fun b : B ↦ L b)) :
    ∃ v : E → V,
      (∀ e, v e ∈ L e) ∧
        (∀ e ∈ fixed, v e = q e) ∧
          LinearIndependent ℚ (fun b : B ↦ v b) := by
  simpa using feasible_assignment_of_radoCapacity_of_fixed_lines
    L fixed q
      ({ toFun := fun b : B ↦ (b : E)
         inj' := Subtype.val_injective } : B ↪ E)
      hFixedLines hCapacity

/-! The six concrete instances follow.  Each namespace exposes the same API:
`blockClass`, `specialClass`, `ambientSubspace`, `L`, `fixedElements`,
`ambientFixedVector`, and `q`. -/

/-! ## Common constructors for an element-level instance -/

/-- Build ambient allowed subspaces from the two partial classifications. -/
def ambientSubspaceOf {E Block Special : Type*} {n q : ℕ}
    (blockLabel : Block → Templates.QuotientSpace q)
    (specialVector : Special → Templates.Ambient n q)
    (blockClass : E → Option Block) (specialClass : E → Option Special) :
    E → Submodule ℚ (Templates.Ambient n q) := fun e ↦
  match blockClass e with
  | some b => Templates.largeBlockSubspace n q (blockLabel b)
  | none =>
      match specialClass e with
      | some s => ℚ ∙ specialVector s
      | none => ⊥

/-- The prescribed vector is the template vector on a surviving special
element and zero elsewhere. -/
def ambientFixedVectorOf {E Special : Type*} {n q : ℕ}
    (specialVector : Special → Templates.Ambient n q)
    (specialClass : E → Option Special) : E → Templates.Ambient n q :=
  fun e ↦ (specialClass e).elim 0 specialVector

/-- Precisely the elements classified as surviving special elements are
fixed by the generic construction. -/
def fixedElementsOf {E Special : Type*} (specialClass : E → Option Special) :
    Set E := {e | ∃ s, specialClass e = some s}

/-- Transport an ambient allowed-subspace family to concatenated column
coordinates. -/
def coordinateSubspaceOf {E : Type*} {n q : ℕ}
    (ambientSubspace : E → Submodule ℚ (Templates.Ambient n q)) :
    E → Submodule ℚ (Fin (n + q) → ℚ) := fun e ↦
  (ambientSubspace e).map (ambientCoordinateEquiv n q).toLinearMap

/-- Transport prescribed ambient vectors to concatenated column
coordinates. -/
def coordinateFixedVectorOf {E : Type*} {n q : ℕ}
    (ambientFixedVector : E → Templates.Ambient n q) :
    E → (Fin (n + q) → ℚ) := fun e ↦
  ambientCoordinateEquiv n q (ambientFixedVector e)

theorem ambientSubspaceOf_eq_largeBlockSubspace
    {E Block Special : Type*} {n q : ℕ}
    (blockLabel : Block → Templates.QuotientSpace q)
    (specialVector : Special → Templates.Ambient n q)
    (blockClass : E → Option Block) (specialClass : E → Option Special)
    {e : E} {b : Block} (h : blockClass e = some b) :
    ambientSubspaceOf blockLabel specialVector blockClass specialClass e =
      Templates.largeBlockSubspace n q (blockLabel b) := by
  simp [ambientSubspaceOf, h]

theorem ambientFixedVectorOf_eq_special
    {E Special : Type*} {n q : ℕ}
    (specialVector : Special → Templates.Ambient n q)
    (specialClass : E → Option Special)
    {e : E} {s : Special} (h : specialClass e = some s) :
    ambientFixedVectorOf specialVector specialClass e = specialVector s := by
  simp [ambientFixedVectorOf, h]

theorem ambientSubspaceOf_eq_fixedLine
    {E Block Special : Type*} {n q : ℕ}
    (blockLabel : Block → Templates.QuotientSpace q)
    (specialVector : Special → Templates.Ambient n q)
    (blockClass : E → Option Block) (specialClass : E → Option Special)
    (hExclusive : ∀ e s, specialClass e = some s → blockClass e = none)
    {e : E} (he : e ∈ fixedElementsOf specialClass) :
    ambientSubspaceOf blockLabel specialVector blockClass specialClass e =
      ℚ ∙ ambientFixedVectorOf specialVector specialClass e := by
  obtain ⟨s, hs⟩ := he
  simp [ambientSubspaceOf, ambientFixedVectorOf, hs, hExclusive e s hs]

theorem coordinateSubspaceOf_eq_largeBlockSubspace_map
    {E Block Special : Type*} {n q : ℕ}
    (blockLabel : Block → Templates.QuotientSpace q)
    (specialVector : Special → Templates.Ambient n q)
    (blockClass : E → Option Block) (specialClass : E → Option Special)
    {e : E} {b : Block} (h : blockClass e = some b) :
    coordinateSubspaceOf
        (ambientSubspaceOf blockLabel specialVector blockClass specialClass) e =
      (Templates.largeBlockSubspace n q (blockLabel b)).map
        (ambientCoordinateEquiv n q).toLinearMap := by
  rw [coordinateSubspaceOf,
    ambientSubspaceOf_eq_largeBlockSubspace
      blockLabel specialVector blockClass specialClass h]

theorem coordinateSubspaceOf_eq_fixedLine
    {E Block Special : Type*} {n q : ℕ}
    (blockLabel : Block → Templates.QuotientSpace q)
    (specialVector : Special → Templates.Ambient n q)
    (blockClass : E → Option Block) (specialClass : E → Option Special)
    (hExclusive : ∀ e s, specialClass e = some s → blockClass e = none)
    {e : E} (he : e ∈ fixedElementsOf specialClass) :
    coordinateSubspaceOf
        (ambientSubspaceOf blockLabel specialVector blockClass specialClass) e =
      ℚ ∙ coordinateFixedVectorOf
        (ambientFixedVectorOf specialVector specialClass) e := by
  rw [coordinateSubspaceOf,
    ambientSubspaceOf_eq_fixedLine
      blockLabel specialVector blockClass specialClass hExclusive he,
    map_span_singleton_ambientCoordinateEquiv]
  rfl

theorem coordinateFixedVectorOf_mem_coordinateSubspaceOf
    {E Block Special : Type*} {n q : ℕ}
    (blockLabel : Block → Templates.QuotientSpace q)
    (specialVector : Special → Templates.Ambient n q)
    (blockClass : E → Option Block) (specialClass : E → Option Special)
    (hExclusive : ∀ e s, specialClass e = some s → blockClass e = none)
    {e : E} (he : e ∈ fixedElementsOf specialClass) :
    coordinateFixedVectorOf
        (ambientFixedVectorOf specialVector specialClass) e ∈
      coordinateSubspaceOf
        (ambientSubspaceOf blockLabel specialVector blockClass specialClass) e := by
  rw [coordinateSubspaceOf_eq_fixedLine
    blockLabel specialVector blockClass specialClass hExclusive he]
  exact Submodule.mem_span_singleton_self _

/-- A finite sum of transported allowed subspaces is the transport of the
corresponding ambient sum. -/
theorem subspaceSum_coordinateSubspaceOf
    {E I : Type*} {n q : ℕ}
    (ambientSubspace : E → Submodule ℚ (Templates.Ambient n q))
    (index : I → E) (J : Finset I) :
    subspaceSum ℚ
        (fun i ↦ coordinateSubspaceOf ambientSubspace (index i)) J =
      (subspaceSum ℚ (fun i ↦ ambientSubspace (index i)) J).map
        (ambientCoordinateEquiv n q).toLinearMap := by
  classical
  simpa [coordinateSubspaceOf] using
    subspaceSum_map ℚ (ambientCoordinateEquiv n q).toLinearMap
      (fun i ↦ ambientSubspace (index i)) J

/-- The finite sums occurring in Rado's inequalities have the same dimension
in ambient product coordinates and concatenated column coordinates. -/
theorem finrank_subspaceSum_coordinateSubspaceOf
    {E I : Type*} {n q : ℕ}
    (ambientSubspace : E → Submodule ℚ (Templates.Ambient n q))
    (index : I → E) (J : Finset I) :
    Module.finrank ℚ
        (subspaceSum ℚ
          (fun i ↦ coordinateSubspaceOf ambientSubspace (index i)) J) =
      Module.finrank ℚ
        (subspaceSum ℚ (fun i ↦ ambientSubspace (index i)) J) := by
  rw [subspaceSum_coordinateSubspaceOf ambientSubspace index J]
  exact (ambientCoordinateEquiv n q).finrank_map_eq _

/-- Rado capacity is invariant under the ambient/column coordinate
equivalence.  This lets the six capacity audits use the common-core quotient
dimension formula from `Templates` and transport the result without loss. -/
theorem hasRadoCapacity_coordinateSubspaceOf_iff
    {E I : Type*} [Fintype I] {n q : ℕ}
    (ambientSubspace : E → Submodule ℚ (Templates.Ambient n q))
    (index : I → E) :
    HasRadoCapacity ℚ
        (fun i ↦ coordinateSubspaceOf ambientSubspace (index i)) ↔
      HasRadoCapacity ℚ (fun i ↦ ambientSubspace (index i)) := by
  constructor <;> intro h J
  · rw [← finrank_subspaceSum_coordinateSubspaceOf
      ambientSubspace index J]
    exact h J
  · rw [finrank_subspaceSum_coordinateSubspaceOf
      ambientSubspace index J]
    exact h J

/-! ## Deletion of the distinguished element `x₀ ∈ X` -/

namespace DeleteX

abbrev Block := Templates.DeleteX.Block
abbrev Special := Templates.DeleteX.Special
abbrev quotientDim := Templates.DeleteX.quotientDim

/-- The actual blocks `X,Y,Z` correspond respectively to template blocks
`A,B,C`. -/
def blockKind : Fin 3 → Block := ![.A, .B, .C]

/-- The four actual special elements retain their names. -/
def specialKind : Fin 4 → Special := ![.One, .Two, .Three, .Four]

/-- The representative deleted from the symmetric `X` block. -/
def removedElement (n : ℕ) : Element n := Family.x0 n

/-- Actual elements classified as surviving large-block elements. -/
def blockClass (n : ℕ) : Element n → Option Block
  | .special _ => none
  | e@(.block b _) =>
      if e = removedElement n then none else some (blockKind b)

/-- Actual elements classified as fixed special elements. -/
def specialClass (n : ℕ) : Element n → Option Special
  | .special s => some (specialKind s)
  | .block _ _ => none

def ambientSubspace (n : ℕ) :
    Element n → Submodule ℚ (Templates.Ambient n quotientDim) :=
  ambientSubspaceOf Templates.DeleteX.blockLabel (Templates.DeleteX.special n)
    (blockClass n) (specialClass n)

def ambientFixedVector (n : ℕ) :
    Element n → Templates.Ambient n quotientDim :=
  ambientFixedVectorOf (Templates.DeleteX.special n) (specialClass n)

/-- Allowed subspaces in the concatenated coordinate space used by the
generic representation compiler. -/
def L (n : ℕ) : Element n → Submodule ℚ (Fin (n + quotientDim) → ℚ) :=
  coordinateSubspaceOf (ambientSubspace n)

/-- The surviving special elements are precisely the fixed columns. -/
def fixedElements (n : ℕ) : Set (Element n) :=
  fixedElementsOf (specialClass n)

/-- Prescribed fixed columns in concatenated coordinates. -/
def q (n : ℕ) : Element n → (Fin (n + quotientDim) → ℚ) :=
  coordinateFixedVectorOf (ambientFixedVector n)

@[simp] theorem blockClass_special (n : ℕ) (s : Fin 4) :
    blockClass n (.special s) = none := rfl

@[simp] theorem specialClass_special (n : ℕ) (s : Fin 4) :
    specialClass n (.special s) = some (specialKind s) := rfl

@[simp] theorem specialClass_block (n : ℕ) (b : Fin 3) (i : Fin (n + 1)) :
    specialClass n (.block b i) = none := rfl

@[simp] theorem blockClass_removedElement (n : ℕ) :
    blockClass n (removedElement n) = none := by
  simp [blockClass, removedElement, Family.x0]

@[simp] theorem specialClass_removedElement (n : ℕ) :
    specialClass n (removedElement n) = none := by
  simp [removedElement, Family.x0]

theorem classes_exclusive (n : ℕ) (e : Element n) (s : Special)
    (h : specialClass n e = some s) : blockClass n e = none := by
  cases e with
  | special i => rfl
  | block b i => simp at h

theorem ambientSubspace_eq_largeBlockSubspace
    {n : ℕ} {e : Element n} {b : Block}
    (h : blockClass n e = some b) :
    ambientSubspace n e =
      Templates.largeBlockSubspace n quotientDim
        (Templates.DeleteX.blockLabel b) :=
  ambientSubspaceOf_eq_largeBlockSubspace _ _ _ _ h

theorem L_eq_largeBlockSubspace_map
    {n : ℕ} {e : Element n} {b : Block}
    (h : blockClass n e = some b) :
    L n e =
      (Templates.largeBlockSubspace n quotientDim
        (Templates.DeleteX.blockLabel b)).map
          (ambientCoordinateEquiv n quotientDim).toLinearMap :=
  coordinateSubspaceOf_eq_largeBlockSubspace_map _ _ _ _ h

theorem ambientFixedVector_eq_special
    {n : ℕ} {e : Element n} {s : Special}
    (h : specialClass n e = some s) :
    ambientFixedVector n e = Templates.DeleteX.special n s :=
  ambientFixedVectorOf_eq_special _ _ h

theorem q_eq_special
    {n : ℕ} {e : Element n} {s : Special}
    (h : specialClass n e = some s) :
    q n e = ambientCoordinateEquiv n quotientDim
      (Templates.DeleteX.special n s) := by
  rw [q, coordinateFixedVectorOf, ambientFixedVector_eq_special h]

@[simp] theorem ambientSubspace_removedElement (n : ℕ) :
    ambientSubspace n (removedElement n) = ⊥ := by
  simp [ambientSubspace, ambientSubspaceOf]

@[simp] theorem L_removedElement (n : ℕ) :
    L n (removedElement n) = ⊥ := by
  simp [L, coordinateSubspaceOf]

@[simp] theorem q_removedElement (n : ℕ) :
    q n (removedElement n) = 0 := by
  simp [q, coordinateFixedVectorOf, ambientFixedVector,
    ambientFixedVectorOf]

theorem L_fixed_eq_span_q {n : ℕ} {e : Element n}
    (he : e ∈ fixedElements n) : L n e = ℚ ∙ q n e :=
  coordinateSubspaceOf_eq_fixedLine _ _ _ _ (classes_exclusive n) he

theorem q_mem_L {n : ℕ} {e : Element n} (he : e ∈ fixedElements n) :
    q n e ∈ L n e :=
  coordinateFixedVectorOf_mem_coordinateSubspaceOf
    _ _ _ _ (classes_exclusive n) he

theorem hasRadoCapacity_L_iff_ambient {n : ℕ} (B : Set (Element n))
    [Fintype B] :
    HasRadoCapacity ℚ (fun b : B ↦ L n b) ↔
      HasRadoCapacity ℚ (fun b : B ↦ ambientSubspace n b) := by
  simpa [L] using hasRadoCapacity_coordinateSubspaceOf_iff
    (ambientSubspace n) (fun b : B ↦ (b : Element n))

/-- Direct `hBaseFeasible`-shaped consequence of a Rado capacity audit on a
candidate set. -/
theorem feasible_assignment_on_candidate {n : ℕ} (B : Set (Element n))
    [Fintype B]
    (hCapacity : HasRadoCapacity ℚ (fun b : B ↦ L n b)) :
    ∃ v : Element n → (Fin (n + quotientDim) → ℚ),
      (∀ e, v e ∈ L n e) ∧
        (∀ e ∈ fixedElements n, v e = q n e) ∧
          LinearIndependent ℚ (fun b : B ↦ v b) :=
  feasible_assignment_on_set_of_radoCapacity_of_fixed_lines
    (L n) (fixedElements n) (q n) B
      (fun e he ↦ L_fixed_eq_span_q (n := n) (e := e) he) hCapacity

theorem feasible_assignment_on_candidate_of_ambientCapacity
    {n : ℕ} (B : Set (Element n)) [Fintype B]
    (hCapacity : HasRadoCapacity ℚ
      (fun b : B ↦ ambientSubspace n b)) :
    ∃ v : Element n → (Fin (n + quotientDim) → ℚ),
      (∀ e, v e ∈ L n e) ∧
        (∀ e ∈ fixedElements n, v e = q n e) ∧
          LinearIndependent ℚ (fun b : B ↦ v b) :=
  feasible_assignment_on_candidate B
    ((hasRadoCapacity_L_iff_ambient B).mpr hCapacity)

end DeleteX

/-! ## Deletion of the special element `1` -/

namespace DeleteOne

abbrev Block := Templates.DeleteOne.Block
abbrev Special := Templates.DeleteOne.Special
abbrev quotientDim := Templates.DeleteOne.quotientDim

def blockKind : Fin 3 → Block := ![.A, .B, .C]

/-- Element `1` is omitted; `2,3,4` retain their names. -/
def specialKind : Fin 4 → Option Special :=
  ![none, some .Two, some .Three, some .Four]

def removedElement (n : ℕ) : Element n := Family.one n

def blockClass (n : ℕ) : Element n → Option Block
  | .special _ => none
  | .block b _ => some (blockKind b)

def specialClass (n : ℕ) : Element n → Option Special
  | .special s => specialKind s
  | .block _ _ => none

def ambientSubspace (n : ℕ) :
    Element n → Submodule ℚ (Templates.Ambient n quotientDim) :=
  ambientSubspaceOf Templates.DeleteOne.blockLabel (Templates.DeleteOne.special n)
    (blockClass n) (specialClass n)

def ambientFixedVector (n : ℕ) :
    Element n → Templates.Ambient n quotientDim :=
  ambientFixedVectorOf (Templates.DeleteOne.special n) (specialClass n)

def L (n : ℕ) : Element n → Submodule ℚ (Fin (n + quotientDim) → ℚ) :=
  coordinateSubspaceOf (ambientSubspace n)

def fixedElements (n : ℕ) : Set (Element n) :=
  fixedElementsOf (specialClass n)

def q (n : ℕ) : Element n → (Fin (n + quotientDim) → ℚ) :=
  coordinateFixedVectorOf (ambientFixedVector n)

@[simp] theorem blockClass_special (n : ℕ) (s : Fin 4) :
    blockClass n (.special s) = none := rfl

@[simp] theorem blockClass_block (n : ℕ) (b : Fin 3) (i : Fin (n + 1)) :
    blockClass n (.block b i) = some (blockKind b) := rfl

@[simp] theorem specialClass_special (n : ℕ) (s : Fin 4) :
    specialClass n (.special s) = specialKind s := rfl

@[simp] theorem specialClass_block (n : ℕ) (b : Fin 3) (i : Fin (n + 1)) :
    specialClass n (.block b i) = none := rfl

@[simp] theorem blockClass_removedElement (n : ℕ) :
    blockClass n (removedElement n) = none := by
  rfl

@[simp] theorem specialClass_removedElement (n : ℕ) :
    specialClass n (removedElement n) = none := by
  rfl

theorem classes_exclusive (n : ℕ) (e : Element n) (s : Special)
    (h : specialClass n e = some s) : blockClass n e = none := by
  cases e with
  | special i => rfl
  | block b i => simp at h

theorem ambientSubspace_eq_largeBlockSubspace
    {n : ℕ} {e : Element n} {b : Block}
    (h : blockClass n e = some b) :
    ambientSubspace n e =
      Templates.largeBlockSubspace n quotientDim
        (Templates.DeleteOne.blockLabel b) :=
  ambientSubspaceOf_eq_largeBlockSubspace _ _ _ _ h

theorem L_eq_largeBlockSubspace_map
    {n : ℕ} {e : Element n} {b : Block}
    (h : blockClass n e = some b) :
    L n e =
      (Templates.largeBlockSubspace n quotientDim
        (Templates.DeleteOne.blockLabel b)).map
          (ambientCoordinateEquiv n quotientDim).toLinearMap :=
  coordinateSubspaceOf_eq_largeBlockSubspace_map _ _ _ _ h

theorem ambientFixedVector_eq_special
    {n : ℕ} {e : Element n} {s : Special}
    (h : specialClass n e = some s) :
    ambientFixedVector n e = Templates.DeleteOne.special n s :=
  ambientFixedVectorOf_eq_special _ _ h

theorem q_eq_special
    {n : ℕ} {e : Element n} {s : Special}
    (h : specialClass n e = some s) :
    q n e = ambientCoordinateEquiv n quotientDim
      (Templates.DeleteOne.special n s) := by
  rw [q, coordinateFixedVectorOf, ambientFixedVector_eq_special h]

@[simp] theorem ambientSubspace_removedElement (n : ℕ) :
    ambientSubspace n (removedElement n) = ⊥ := by
  simp [ambientSubspace, ambientSubspaceOf]

@[simp] theorem L_removedElement (n : ℕ) :
    L n (removedElement n) = ⊥ := by
  simp [L, coordinateSubspaceOf]

@[simp] theorem q_removedElement (n : ℕ) :
    q n (removedElement n) = 0 := by
  simp [q, coordinateFixedVectorOf, ambientFixedVector,
    ambientFixedVectorOf]

theorem L_fixed_eq_span_q {n : ℕ} {e : Element n}
    (he : e ∈ fixedElements n) : L n e = ℚ ∙ q n e :=
  coordinateSubspaceOf_eq_fixedLine _ _ _ _ (classes_exclusive n) he

theorem q_mem_L {n : ℕ} {e : Element n} (he : e ∈ fixedElements n) :
    q n e ∈ L n e :=
  coordinateFixedVectorOf_mem_coordinateSubspaceOf
    _ _ _ _ (classes_exclusive n) he

theorem hasRadoCapacity_L_iff_ambient {n : ℕ} (B : Set (Element n))
    [Fintype B] :
    HasRadoCapacity ℚ (fun b : B ↦ L n b) ↔
      HasRadoCapacity ℚ (fun b : B ↦ ambientSubspace n b) := by
  simpa [L] using hasRadoCapacity_coordinateSubspaceOf_iff
    (ambientSubspace n) (fun b : B ↦ (b : Element n))

theorem feasible_assignment_on_candidate {n : ℕ} (B : Set (Element n))
    [Fintype B]
    (hCapacity : HasRadoCapacity ℚ (fun b : B ↦ L n b)) :
    ∃ v : Element n → (Fin (n + quotientDim) → ℚ),
      (∀ e, v e ∈ L n e) ∧
        (∀ e ∈ fixedElements n, v e = q n e) ∧
          LinearIndependent ℚ (fun b : B ↦ v b) :=
  feasible_assignment_on_set_of_radoCapacity_of_fixed_lines
    (L n) (fixedElements n) (q n) B
      (fun e he ↦ L_fixed_eq_span_q (n := n) (e := e) he) hCapacity

theorem feasible_assignment_on_candidate_of_ambientCapacity
    {n : ℕ} (B : Set (Element n)) [Fintype B]
    (hCapacity : HasRadoCapacity ℚ
      (fun b : B ↦ ambientSubspace n b)) :
    ∃ v : Element n → (Fin (n + quotientDim) → ℚ),
      (∀ e, v e ∈ L n e) ∧
        (∀ e ∈ fixedElements n, v e = q n e) ∧
          LinearIndependent ℚ (fun b : B ↦ v b) :=
  feasible_assignment_on_candidate B
    ((hasRadoCapacity_L_iff_ambient B).mpr hCapacity)

end DeleteOne

/-! ## Deletion of the special element `4` -/

namespace DeleteFour

abbrev Block := Templates.DeleteFour.Block
abbrev Special := Templates.DeleteFour.Special
abbrev quotientDim := Templates.DeleteFour.quotientDim

def blockKind : Fin 3 → Block := ![.A, .B, .C]

/-- Elements `1,2,3` survive and element `4` is omitted. -/
def specialKind : Fin 4 → Option Special :=
  ![some .One, some .Two, some .Three, none]

def removedElement (n : ℕ) : Element n := Family.four n

def blockClass (n : ℕ) : Element n → Option Block
  | .special _ => none
  | .block b _ => some (blockKind b)

def specialClass (n : ℕ) : Element n → Option Special
  | .special s => specialKind s
  | .block _ _ => none

def ambientSubspace (n : ℕ) :
    Element n → Submodule ℚ (Templates.Ambient n quotientDim) :=
  ambientSubspaceOf Templates.DeleteFour.blockLabel (Templates.DeleteFour.special n)
    (blockClass n) (specialClass n)

def ambientFixedVector (n : ℕ) :
    Element n → Templates.Ambient n quotientDim :=
  ambientFixedVectorOf (Templates.DeleteFour.special n) (specialClass n)

def L (n : ℕ) : Element n → Submodule ℚ (Fin (n + quotientDim) → ℚ) :=
  coordinateSubspaceOf (ambientSubspace n)

def fixedElements (n : ℕ) : Set (Element n) :=
  fixedElementsOf (specialClass n)

def q (n : ℕ) : Element n → (Fin (n + quotientDim) → ℚ) :=
  coordinateFixedVectorOf (ambientFixedVector n)

@[simp] theorem blockClass_special (n : ℕ) (s : Fin 4) :
    blockClass n (.special s) = none := rfl

@[simp] theorem blockClass_block (n : ℕ) (b : Fin 3) (i : Fin (n + 1)) :
    blockClass n (.block b i) = some (blockKind b) := rfl

@[simp] theorem specialClass_special (n : ℕ) (s : Fin 4) :
    specialClass n (.special s) = specialKind s := rfl

@[simp] theorem specialClass_block (n : ℕ) (b : Fin 3) (i : Fin (n + 1)) :
    specialClass n (.block b i) = none := rfl

@[simp] theorem blockClass_removedElement (n : ℕ) :
    blockClass n (removedElement n) = none := by
  rfl

@[simp] theorem specialClass_removedElement (n : ℕ) :
    specialClass n (removedElement n) = none := by
  rfl

theorem classes_exclusive (n : ℕ) (e : Element n) (s : Special)
    (h : specialClass n e = some s) : blockClass n e = none := by
  cases e with
  | special i => rfl
  | block b i => simp at h

theorem ambientSubspace_eq_largeBlockSubspace
    {n : ℕ} {e : Element n} {b : Block}
    (h : blockClass n e = some b) :
    ambientSubspace n e =
      Templates.largeBlockSubspace n quotientDim
        (Templates.DeleteFour.blockLabel b) :=
  ambientSubspaceOf_eq_largeBlockSubspace _ _ _ _ h

theorem L_eq_largeBlockSubspace_map
    {n : ℕ} {e : Element n} {b : Block}
    (h : blockClass n e = some b) :
    L n e =
      (Templates.largeBlockSubspace n quotientDim
        (Templates.DeleteFour.blockLabel b)).map
          (ambientCoordinateEquiv n quotientDim).toLinearMap :=
  coordinateSubspaceOf_eq_largeBlockSubspace_map _ _ _ _ h

theorem ambientFixedVector_eq_special
    {n : ℕ} {e : Element n} {s : Special}
    (h : specialClass n e = some s) :
    ambientFixedVector n e = Templates.DeleteFour.special n s :=
  ambientFixedVectorOf_eq_special _ _ h

theorem q_eq_special
    {n : ℕ} {e : Element n} {s : Special}
    (h : specialClass n e = some s) :
    q n e = ambientCoordinateEquiv n quotientDim
      (Templates.DeleteFour.special n s) := by
  rw [q, coordinateFixedVectorOf, ambientFixedVector_eq_special h]

@[simp] theorem ambientSubspace_removedElement (n : ℕ) :
    ambientSubspace n (removedElement n) = ⊥ := by
  simp [ambientSubspace, ambientSubspaceOf]

@[simp] theorem L_removedElement (n : ℕ) :
    L n (removedElement n) = ⊥ := by
  simp [L, coordinateSubspaceOf]

@[simp] theorem q_removedElement (n : ℕ) :
    q n (removedElement n) = 0 := by
  simp [q, coordinateFixedVectorOf, ambientFixedVector,
    ambientFixedVectorOf]

theorem L_fixed_eq_span_q {n : ℕ} {e : Element n}
    (he : e ∈ fixedElements n) : L n e = ℚ ∙ q n e :=
  coordinateSubspaceOf_eq_fixedLine _ _ _ _ (classes_exclusive n) he

theorem q_mem_L {n : ℕ} {e : Element n} (he : e ∈ fixedElements n) :
    q n e ∈ L n e :=
  coordinateFixedVectorOf_mem_coordinateSubspaceOf
    _ _ _ _ (classes_exclusive n) he

theorem hasRadoCapacity_L_iff_ambient {n : ℕ} (B : Set (Element n))
    [Fintype B] :
    HasRadoCapacity ℚ (fun b : B ↦ L n b) ↔
      HasRadoCapacity ℚ (fun b : B ↦ ambientSubspace n b) := by
  simpa [L] using hasRadoCapacity_coordinateSubspaceOf_iff
    (ambientSubspace n) (fun b : B ↦ (b : Element n))

theorem feasible_assignment_on_candidate {n : ℕ} (B : Set (Element n))
    [Fintype B]
    (hCapacity : HasRadoCapacity ℚ (fun b : B ↦ L n b)) :
    ∃ v : Element n → (Fin (n + quotientDim) → ℚ),
      (∀ e, v e ∈ L n e) ∧
        (∀ e ∈ fixedElements n, v e = q n e) ∧
          LinearIndependent ℚ (fun b : B ↦ v b) :=
  feasible_assignment_on_set_of_radoCapacity_of_fixed_lines
    (L n) (fixedElements n) (q n) B
      (fun e he ↦ L_fixed_eq_span_q (n := n) (e := e) he) hCapacity

theorem feasible_assignment_on_candidate_of_ambientCapacity
    {n : ℕ} (B : Set (Element n)) [Fintype B]
    (hCapacity : HasRadoCapacity ℚ
      (fun b : B ↦ ambientSubspace n b)) :
    ∃ v : Element n → (Fin (n + quotientDim) → ℚ),
      (∀ e, v e ∈ L n e) ∧
        (∀ e ∈ fixedElements n, v e = q n e) ∧
          LinearIndependent ℚ (fun b : B ↦ v b) :=
  feasible_assignment_on_candidate B
    ((hasRadoCapacity_L_iff_ambient B).mpr hCapacity)

end DeleteFour

/-! ## Contraction of the distinguished element `x₀ ∈ X` -/

namespace ContractX

abbrev Block := Templates.ContractX.Block
abbrev Special := Templates.ContractX.Special
abbrev quotientDim := Templates.ContractX.quotientDim

def blockKind : Fin 3 → Block := ![.X, .Y, .Z]
def specialKind : Fin 4 → Special := ![.One, .Two, .Three, .Four]

/-- The representative contracted from the symmetric `X` block. -/
def removedElement (n : ℕ) : Element n := Family.x0 n

def blockClass (n : ℕ) : Element n → Option Block
  | .special _ => none
  | e@(.block b _) =>
      if e = removedElement n then none else some (blockKind b)

def specialClass (n : ℕ) : Element n → Option Special
  | .special s => some (specialKind s)
  | .block _ _ => none

def ambientSubspace (n : ℕ) :
    Element n → Submodule ℚ (Templates.Ambient n quotientDim) :=
  ambientSubspaceOf Templates.ContractX.blockLabel (Templates.ContractX.special n)
    (blockClass n) (specialClass n)

def ambientFixedVector (n : ℕ) :
    Element n → Templates.Ambient n quotientDim :=
  ambientFixedVectorOf (Templates.ContractX.special n) (specialClass n)

def L (n : ℕ) : Element n → Submodule ℚ (Fin (n + quotientDim) → ℚ) :=
  coordinateSubspaceOf (ambientSubspace n)

def fixedElements (n : ℕ) : Set (Element n) :=
  fixedElementsOf (specialClass n)

def q (n : ℕ) : Element n → (Fin (n + quotientDim) → ℚ) :=
  coordinateFixedVectorOf (ambientFixedVector n)

@[simp] theorem blockClass_special (n : ℕ) (s : Fin 4) :
    blockClass n (.special s) = none := rfl

@[simp] theorem specialClass_special (n : ℕ) (s : Fin 4) :
    specialClass n (.special s) = some (specialKind s) := rfl

@[simp] theorem specialClass_block (n : ℕ) (b : Fin 3) (i : Fin (n + 1)) :
    specialClass n (.block b i) = none := rfl

@[simp] theorem blockClass_removedElement (n : ℕ) :
    blockClass n (removedElement n) = none := by
  simp [blockClass, removedElement, Family.x0]

@[simp] theorem specialClass_removedElement (n : ℕ) :
    specialClass n (removedElement n) = none := by
  simp [removedElement, Family.x0]

theorem classes_exclusive (n : ℕ) (e : Element n) (s : Special)
    (h : specialClass n e = some s) : blockClass n e = none := by
  cases e with
  | special i => rfl
  | block b i => simp at h

theorem ambientSubspace_eq_largeBlockSubspace
    {n : ℕ} {e : Element n} {b : Block}
    (h : blockClass n e = some b) :
    ambientSubspace n e =
      Templates.largeBlockSubspace n quotientDim
        (Templates.ContractX.blockLabel b) :=
  ambientSubspaceOf_eq_largeBlockSubspace _ _ _ _ h

theorem L_eq_largeBlockSubspace_map
    {n : ℕ} {e : Element n} {b : Block}
    (h : blockClass n e = some b) :
    L n e =
      (Templates.largeBlockSubspace n quotientDim
        (Templates.ContractX.blockLabel b)).map
          (ambientCoordinateEquiv n quotientDim).toLinearMap :=
  coordinateSubspaceOf_eq_largeBlockSubspace_map _ _ _ _ h

theorem ambientFixedVector_eq_special
    {n : ℕ} {e : Element n} {s : Special}
    (h : specialClass n e = some s) :
    ambientFixedVector n e = Templates.ContractX.special n s :=
  ambientFixedVectorOf_eq_special _ _ h

theorem q_eq_special
    {n : ℕ} {e : Element n} {s : Special}
    (h : specialClass n e = some s) :
    q n e = ambientCoordinateEquiv n quotientDim
      (Templates.ContractX.special n s) := by
  rw [q, coordinateFixedVectorOf, ambientFixedVector_eq_special h]

@[simp] theorem ambientSubspace_removedElement (n : ℕ) :
    ambientSubspace n (removedElement n) = ⊥ := by
  simp [ambientSubspace, ambientSubspaceOf]

@[simp] theorem L_removedElement (n : ℕ) :
    L n (removedElement n) = ⊥ := by
  simp [L, coordinateSubspaceOf]

@[simp] theorem q_removedElement (n : ℕ) :
    q n (removedElement n) = 0 := by
  simp [q, coordinateFixedVectorOf, ambientFixedVector,
    ambientFixedVectorOf]

theorem L_fixed_eq_span_q {n : ℕ} {e : Element n}
    (he : e ∈ fixedElements n) : L n e = ℚ ∙ q n e :=
  coordinateSubspaceOf_eq_fixedLine _ _ _ _ (classes_exclusive n) he

theorem q_mem_L {n : ℕ} {e : Element n} (he : e ∈ fixedElements n) :
    q n e ∈ L n e :=
  coordinateFixedVectorOf_mem_coordinateSubspaceOf
    _ _ _ _ (classes_exclusive n) he

theorem hasRadoCapacity_L_iff_ambient {n : ℕ} (B : Set (Element n))
    [Fintype B] :
    HasRadoCapacity ℚ (fun b : B ↦ L n b) ↔
      HasRadoCapacity ℚ (fun b : B ↦ ambientSubspace n b) := by
  simpa [L] using hasRadoCapacity_coordinateSubspaceOf_iff
    (ambientSubspace n) (fun b : B ↦ (b : Element n))

theorem feasible_assignment_on_candidate {n : ℕ} (B : Set (Element n))
    [Fintype B]
    (hCapacity : HasRadoCapacity ℚ (fun b : B ↦ L n b)) :
    ∃ v : Element n → (Fin (n + quotientDim) → ℚ),
      (∀ e, v e ∈ L n e) ∧
        (∀ e ∈ fixedElements n, v e = q n e) ∧
          LinearIndependent ℚ (fun b : B ↦ v b) :=
  feasible_assignment_on_set_of_radoCapacity_of_fixed_lines
    (L n) (fixedElements n) (q n) B
      (fun e he ↦ L_fixed_eq_span_q (n := n) (e := e) he) hCapacity

theorem feasible_assignment_on_candidate_of_ambientCapacity
    {n : ℕ} (B : Set (Element n)) [Fintype B]
    (hCapacity : HasRadoCapacity ℚ
      (fun b : B ↦ ambientSubspace n b)) :
    ∃ v : Element n → (Fin (n + quotientDim) → ℚ),
      (∀ e, v e ∈ L n e) ∧
        (∀ e ∈ fixedElements n, v e = q n e) ∧
          LinearIndependent ℚ (fun b : B ↦ v b) :=
  feasible_assignment_on_candidate B
    ((hasRadoCapacity_L_iff_ambient B).mpr hCapacity)

end ContractX

/-! ## Contraction of the special element `1` -/

namespace ContractOne

abbrev Block := Templates.ContractOne.Block
abbrev Special := Templates.ContractOne.Special
abbrev quotientDim := Templates.ContractOne.quotientDim

def blockKind : Fin 3 → Block := ![.X, .Y, .Z]
def specialKind : Fin 4 → Option Special :=
  ![none, some .Two, some .Three, some .Four]

def removedElement (n : ℕ) : Element n := Family.one n

def blockClass (n : ℕ) : Element n → Option Block
  | .special _ => none
  | .block b _ => some (blockKind b)

def specialClass (n : ℕ) : Element n → Option Special
  | .special s => specialKind s
  | .block _ _ => none

def ambientSubspace (n : ℕ) :
    Element n → Submodule ℚ (Templates.Ambient n quotientDim) :=
  ambientSubspaceOf Templates.ContractOne.blockLabel (Templates.ContractOne.special n)
    (blockClass n) (specialClass n)

def ambientFixedVector (n : ℕ) :
    Element n → Templates.Ambient n quotientDim :=
  ambientFixedVectorOf (Templates.ContractOne.special n) (specialClass n)

def L (n : ℕ) : Element n → Submodule ℚ (Fin (n + quotientDim) → ℚ) :=
  coordinateSubspaceOf (ambientSubspace n)

def fixedElements (n : ℕ) : Set (Element n) :=
  fixedElementsOf (specialClass n)

def q (n : ℕ) : Element n → (Fin (n + quotientDim) → ℚ) :=
  coordinateFixedVectorOf (ambientFixedVector n)

@[simp] theorem blockClass_special (n : ℕ) (s : Fin 4) :
    blockClass n (.special s) = none := rfl

@[simp] theorem blockClass_block (n : ℕ) (b : Fin 3) (i : Fin (n + 1)) :
    blockClass n (.block b i) = some (blockKind b) := rfl

@[simp] theorem specialClass_special (n : ℕ) (s : Fin 4) :
    specialClass n (.special s) = specialKind s := rfl

@[simp] theorem specialClass_block (n : ℕ) (b : Fin 3) (i : Fin (n + 1)) :
    specialClass n (.block b i) = none := rfl

@[simp] theorem blockClass_removedElement (n : ℕ) :
    blockClass n (removedElement n) = none := by
  rfl

@[simp] theorem specialClass_removedElement (n : ℕ) :
    specialClass n (removedElement n) = none := by
  rfl

theorem classes_exclusive (n : ℕ) (e : Element n) (s : Special)
    (h : specialClass n e = some s) : blockClass n e = none := by
  cases e with
  | special i => rfl
  | block b i => simp at h

theorem ambientSubspace_eq_largeBlockSubspace
    {n : ℕ} {e : Element n} {b : Block}
    (h : blockClass n e = some b) :
    ambientSubspace n e =
      Templates.largeBlockSubspace n quotientDim
        (Templates.ContractOne.blockLabel b) :=
  ambientSubspaceOf_eq_largeBlockSubspace _ _ _ _ h

theorem L_eq_largeBlockSubspace_map
    {n : ℕ} {e : Element n} {b : Block}
    (h : blockClass n e = some b) :
    L n e =
      (Templates.largeBlockSubspace n quotientDim
        (Templates.ContractOne.blockLabel b)).map
          (ambientCoordinateEquiv n quotientDim).toLinearMap :=
  coordinateSubspaceOf_eq_largeBlockSubspace_map _ _ _ _ h

theorem ambientFixedVector_eq_special
    {n : ℕ} {e : Element n} {s : Special}
    (h : specialClass n e = some s) :
    ambientFixedVector n e = Templates.ContractOne.special n s :=
  ambientFixedVectorOf_eq_special _ _ h

theorem q_eq_special
    {n : ℕ} {e : Element n} {s : Special}
    (h : specialClass n e = some s) :
    q n e = ambientCoordinateEquiv n quotientDim
      (Templates.ContractOne.special n s) := by
  rw [q, coordinateFixedVectorOf, ambientFixedVector_eq_special h]

@[simp] theorem ambientSubspace_removedElement (n : ℕ) :
    ambientSubspace n (removedElement n) = ⊥ := by
  simp [ambientSubspace, ambientSubspaceOf]

@[simp] theorem L_removedElement (n : ℕ) :
    L n (removedElement n) = ⊥ := by
  simp [L, coordinateSubspaceOf]

@[simp] theorem q_removedElement (n : ℕ) :
    q n (removedElement n) = 0 := by
  simp [q, coordinateFixedVectorOf, ambientFixedVector,
    ambientFixedVectorOf]

theorem L_fixed_eq_span_q {n : ℕ} {e : Element n}
    (he : e ∈ fixedElements n) : L n e = ℚ ∙ q n e :=
  coordinateSubspaceOf_eq_fixedLine _ _ _ _ (classes_exclusive n) he

theorem q_mem_L {n : ℕ} {e : Element n} (he : e ∈ fixedElements n) :
    q n e ∈ L n e :=
  coordinateFixedVectorOf_mem_coordinateSubspaceOf
    _ _ _ _ (classes_exclusive n) he

theorem hasRadoCapacity_L_iff_ambient {n : ℕ} (B : Set (Element n))
    [Fintype B] :
    HasRadoCapacity ℚ (fun b : B ↦ L n b) ↔
      HasRadoCapacity ℚ (fun b : B ↦ ambientSubspace n b) := by
  simpa [L] using hasRadoCapacity_coordinateSubspaceOf_iff
    (ambientSubspace n) (fun b : B ↦ (b : Element n))

theorem feasible_assignment_on_candidate {n : ℕ} (B : Set (Element n))
    [Fintype B]
    (hCapacity : HasRadoCapacity ℚ (fun b : B ↦ L n b)) :
    ∃ v : Element n → (Fin (n + quotientDim) → ℚ),
      (∀ e, v e ∈ L n e) ∧
        (∀ e ∈ fixedElements n, v e = q n e) ∧
          LinearIndependent ℚ (fun b : B ↦ v b) :=
  feasible_assignment_on_set_of_radoCapacity_of_fixed_lines
    (L n) (fixedElements n) (q n) B
      (fun e he ↦ L_fixed_eq_span_q (n := n) (e := e) he) hCapacity

theorem feasible_assignment_on_candidate_of_ambientCapacity
    {n : ℕ} (B : Set (Element n)) [Fintype B]
    (hCapacity : HasRadoCapacity ℚ
      (fun b : B ↦ ambientSubspace n b)) :
    ∃ v : Element n → (Fin (n + quotientDim) → ℚ),
      (∀ e, v e ∈ L n e) ∧
        (∀ e ∈ fixedElements n, v e = q n e) ∧
          LinearIndependent ℚ (fun b : B ↦ v b) :=
  feasible_assignment_on_candidate B
    ((hasRadoCapacity_L_iff_ambient B).mpr hCapacity)

end ContractOne

/-! ## Contraction of the special element `4` -/

namespace ContractFour

abbrev Block := Templates.ContractFour.Block
abbrev Special := Templates.ContractFour.Special
abbrev quotientDim := Templates.ContractFour.quotientDim

def blockKind : Fin 3 → Block := ![.X, .Y, .Z]
def specialKind : Fin 4 → Option Special :=
  ![some .One, some .Two, some .Three, none]

def removedElement (n : ℕ) : Element n := Family.four n

def blockClass (n : ℕ) : Element n → Option Block
  | .special _ => none
  | .block b _ => some (blockKind b)

def specialClass (n : ℕ) : Element n → Option Special
  | .special s => specialKind s
  | .block _ _ => none

def ambientSubspace (n : ℕ) :
    Element n → Submodule ℚ (Templates.Ambient n quotientDim) :=
  ambientSubspaceOf Templates.ContractFour.blockLabel (Templates.ContractFour.special n)
    (blockClass n) (specialClass n)

def ambientFixedVector (n : ℕ) :
    Element n → Templates.Ambient n quotientDim :=
  ambientFixedVectorOf (Templates.ContractFour.special n) (specialClass n)

def L (n : ℕ) : Element n → Submodule ℚ (Fin (n + quotientDim) → ℚ) :=
  coordinateSubspaceOf (ambientSubspace n)

def fixedElements (n : ℕ) : Set (Element n) :=
  fixedElementsOf (specialClass n)

def q (n : ℕ) : Element n → (Fin (n + quotientDim) → ℚ) :=
  coordinateFixedVectorOf (ambientFixedVector n)

@[simp] theorem blockClass_special (n : ℕ) (s : Fin 4) :
    blockClass n (.special s) = none := rfl

@[simp] theorem blockClass_block (n : ℕ) (b : Fin 3) (i : Fin (n + 1)) :
    blockClass n (.block b i) = some (blockKind b) := rfl

@[simp] theorem specialClass_special (n : ℕ) (s : Fin 4) :
    specialClass n (.special s) = specialKind s := rfl

@[simp] theorem specialClass_block (n : ℕ) (b : Fin 3) (i : Fin (n + 1)) :
    specialClass n (.block b i) = none := rfl

@[simp] theorem blockClass_removedElement (n : ℕ) :
    blockClass n (removedElement n) = none := by
  rfl

@[simp] theorem specialClass_removedElement (n : ℕ) :
    specialClass n (removedElement n) = none := by
  rfl

theorem classes_exclusive (n : ℕ) (e : Element n) (s : Special)
    (h : specialClass n e = some s) : blockClass n e = none := by
  cases e with
  | special i => rfl
  | block b i => simp at h

theorem ambientSubspace_eq_largeBlockSubspace
    {n : ℕ} {e : Element n} {b : Block}
    (h : blockClass n e = some b) :
    ambientSubspace n e =
      Templates.largeBlockSubspace n quotientDim
        (Templates.ContractFour.blockLabel b) :=
  ambientSubspaceOf_eq_largeBlockSubspace _ _ _ _ h

theorem L_eq_largeBlockSubspace_map
    {n : ℕ} {e : Element n} {b : Block}
    (h : blockClass n e = some b) :
    L n e =
      (Templates.largeBlockSubspace n quotientDim
        (Templates.ContractFour.blockLabel b)).map
          (ambientCoordinateEquiv n quotientDim).toLinearMap :=
  coordinateSubspaceOf_eq_largeBlockSubspace_map _ _ _ _ h

theorem ambientFixedVector_eq_special
    {n : ℕ} {e : Element n} {s : Special}
    (h : specialClass n e = some s) :
    ambientFixedVector n e = Templates.ContractFour.special n s :=
  ambientFixedVectorOf_eq_special _ _ h

theorem q_eq_special
    {n : ℕ} {e : Element n} {s : Special}
    (h : specialClass n e = some s) :
    q n e = ambientCoordinateEquiv n quotientDim
      (Templates.ContractFour.special n s) := by
  rw [q, coordinateFixedVectorOf, ambientFixedVector_eq_special h]

@[simp] theorem ambientSubspace_removedElement (n : ℕ) :
    ambientSubspace n (removedElement n) = ⊥ := by
  simp [ambientSubspace, ambientSubspaceOf]

@[simp] theorem L_removedElement (n : ℕ) :
    L n (removedElement n) = ⊥ := by
  simp [L, coordinateSubspaceOf]

@[simp] theorem q_removedElement (n : ℕ) :
    q n (removedElement n) = 0 := by
  simp [q, coordinateFixedVectorOf, ambientFixedVector,
    ambientFixedVectorOf]

theorem L_fixed_eq_span_q {n : ℕ} {e : Element n}
    (he : e ∈ fixedElements n) : L n e = ℚ ∙ q n e :=
  coordinateSubspaceOf_eq_fixedLine _ _ _ _ (classes_exclusive n) he

theorem q_mem_L {n : ℕ} {e : Element n} (he : e ∈ fixedElements n) :
    q n e ∈ L n e :=
  coordinateFixedVectorOf_mem_coordinateSubspaceOf
    _ _ _ _ (classes_exclusive n) he

theorem hasRadoCapacity_L_iff_ambient {n : ℕ} (B : Set (Element n))
    [Fintype B] :
    HasRadoCapacity ℚ (fun b : B ↦ L n b) ↔
      HasRadoCapacity ℚ (fun b : B ↦ ambientSubspace n b) := by
  simpa [L] using hasRadoCapacity_coordinateSubspaceOf_iff
    (ambientSubspace n) (fun b : B ↦ (b : Element n))

theorem feasible_assignment_on_candidate {n : ℕ} (B : Set (Element n))
    [Fintype B]
    (hCapacity : HasRadoCapacity ℚ (fun b : B ↦ L n b)) :
    ∃ v : Element n → (Fin (n + quotientDim) → ℚ),
      (∀ e, v e ∈ L n e) ∧
        (∀ e ∈ fixedElements n, v e = q n e) ∧
          LinearIndependent ℚ (fun b : B ↦ v b) :=
  feasible_assignment_on_set_of_radoCapacity_of_fixed_lines
    (L n) (fixedElements n) (q n) B
      (fun e he ↦ L_fixed_eq_span_q (n := n) (e := e) he) hCapacity

theorem feasible_assignment_on_candidate_of_ambientCapacity
    {n : ℕ} (B : Set (Element n)) [Fintype B]
    (hCapacity : HasRadoCapacity ℚ
      (fun b : B ↦ ambientSubspace n b)) :
    ∃ v : Element n → (Fin (n + quotientDim) → ℚ),
      (∀ e, v e ∈ L n e) ∧
        (∀ e ∈ fixedElements n, v e = q n e) ∧
          LinearIndependent ℚ (fun b : B ↦ v b) :=
  feasible_assignment_on_candidate B
    ((hasRadoCapacity_L_iff_ambient B).mpr hCapacity)

end ContractFour

end BlandJensenFormal.BlandJensenMI.TemplateInstances
