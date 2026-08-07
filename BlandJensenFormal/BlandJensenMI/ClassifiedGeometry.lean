import BlandJensenFormal.BlandJensenMI.TemplateInstances

/-!
# Common-core geometry for element-level template classifications

The six instances classify every surviving element as either a large-block
element or a fixed special element.  This file proves the common dimension
formula directly for an arbitrary finite selector of actual elements.  It
therefore retains multiplicities in cardinal inequalities while discarding
them only after passage to the finite set of quotient labels.
-/

namespace BlandJensenFormal.BlandJensenMI.ClassifiedGeometry

open Function Set Submodule
open Templates TemplateInstances

/-- Quotient label assigned to an actual element by two partial
classifications.  A block classification has priority, exactly as in
`ambientSubspaceOf`; an unclassified element receives the zero label. -/
def quotientLabelOf {E Block Special : Type*} {n q : ℕ}
    (blockLabel : Block → QuotientSpace q)
    (specialVector : Special → Ambient n q)
    (blockClass : E → Option Block) (specialClass : E → Option Special) :
    E → QuotientSpace q := fun e ↦
  match blockClass e with
  | some b => blockLabel b
  | none =>
      match specialClass e with
      | some s => quotientProjection n q (specialVector s)
      | none => 0

/-- The quotient image of each classified allowed subspace is precisely the
line through its element label. -/
theorem map_ambientSubspaceOf_eq_span_quotientLabelOf
    {E Block Special : Type*} {n q : ℕ}
    (blockLabel : Block → QuotientSpace q)
    (specialVector : Special → Ambient n q)
    (blockClass : E → Option Block) (specialClass : E → Option Special)
    (e : E) :
    (ambientSubspaceOf blockLabel specialVector blockClass specialClass e).map
        (quotientProjection n q) =
      ℚ ∙ quotientLabelOf blockLabel specialVector blockClass specialClass e := by
  cases hBlock : blockClass e with
  | some b =>
      rw [ambientSubspaceOf_eq_largeBlockSubspace
        blockLabel specialVector blockClass specialClass hBlock,
        quotientProjection_map_largeBlockSubspace]
      simp [quotientLabelOf, hBlock]
  | none =>
      cases hSpecial : specialClass e with
      | some s =>
          simp [ambientSubspaceOf, quotientLabelOf, hBlock, hSpecial,
            Submodule.map_span]
      | none =>
          simp [ambientSubspaceOf, quotientLabelOf, hBlock, hSpecial]

/-- Quotienting a finite sum of actual allowed subspaces retains exactly the
span of the labels of the selected actual elements. -/
theorem map_subspaceSum_ambientSubspaceOf
    {E I Block Special : Type*} [DecidableEq I] {n q : ℕ}
    (blockLabel : Block → QuotientSpace q)
    (specialVector : Special → Ambient n q)
    (blockClass : E → Option Block) (specialClass : E → Option Special)
    (index : I → E) (J : Finset I) :
    (subspaceSum ℚ
        (fun i ↦ ambientSubspaceOf blockLabel specialVector
          blockClass specialClass (index i)) J).map
        (quotientProjection n q) =
      Submodule.span ℚ
        (quotientLabelOf blockLabel specialVector blockClass specialClass ∘
          index '' (J : Set I)) := by
  rw [← subspaceSum_map]
  simp_rw [map_ambientSubspaceOf_eq_span_quotientLabelOf]
  exact subspaceSum_span_labels
    (quotientLabelOf blockLabel specialVector blockClass specialClass ∘ index) J

/-- Selecting at least one large-block element forces the whole common core
into the selected sum. -/
theorem core_le_subspaceSum_ambientSubspaceOf_of_exists_block
    {E I Block Special : Type*} [DecidableEq I] {n q : ℕ}
    (blockLabel : Block → QuotientSpace q)
    (specialVector : Special → Ambient n q)
    (blockClass : E → Option Block) (specialClass : E → Option Special)
    (index : I → E) {J : Finset I}
    (hBlock : ∃ i ∈ J, ∃ b, blockClass (index i) = some b) :
    core n q ≤ subspaceSum ℚ
      (fun i ↦ ambientSubspaceOf blockLabel specialVector
        blockClass specialClass (index i)) J := by
  obtain ⟨i, hi, b, hib⟩ := hBlock
  calc
    core n q ≤ largeBlockSubspace n q (blockLabel b) :=
      core_le_largeBlockSubspace n q (blockLabel b)
    _ = ambientSubspaceOf blockLabel specialVector
        blockClass specialClass (index i) := by
      symm
      exact ambientSubspaceOf_eq_largeBlockSubspace
        blockLabel specialVector blockClass specialClass hib
    _ ≤ subspaceSum ℚ
        (fun j ↦ ambientSubspaceOf blockLabel specialVector
          blockClass specialClass (index j)) J :=
      Finset.le_sup (f := fun j ↦ ambientSubspaceOf blockLabel specialVector
        blockClass specialClass (index j)) hi

/-- Exact common-core/quotient decomposition for a selector containing a
large-block element. -/
theorem subspaceSum_ambientSubspaceOf_eq_corePlus
    {E I Block Special : Type*} [DecidableEq I] {n q : ℕ}
    (blockLabel : Block → QuotientSpace q)
    (specialVector : Special → Ambient n q)
    (blockClass : E → Option Block) (specialClass : E → Option Special)
    (index : I → E) {J : Finset I}
    (hBlock : ∃ i ∈ J, ∃ b, blockClass (index i) = some b) :
    subspaceSum ℚ
        (fun i ↦ ambientSubspaceOf blockLabel specialVector
          blockClass specialClass (index i)) J =
      corePlus n q (Submodule.span ℚ
        (quotientLabelOf blockLabel specialVector blockClass specialClass ∘
          index '' (J : Set I))) := by
  rw [← map_subspaceSum_ambientSubspaceOf]
  exact (Submodule.comap_map_eq_self
    (core_le_subspaceSum_ambientSubspaceOf_of_exists_block
      blockLabel specialVector blockClass specialClass index hBlock)).symm

/-- Exact dimension formula on actual selected elements. -/
theorem finrank_subspaceSum_ambientSubspaceOf
    {E I Block Special : Type*} [DecidableEq I] {n q : ℕ}
    (blockLabel : Block → QuotientSpace q)
    (specialVector : Special → Ambient n q)
    (blockClass : E → Option Block) (specialClass : E → Option Special)
    (index : I → E) {J : Finset I}
    (hBlock : ∃ i ∈ J, ∃ b, blockClass (index i) = some b) :
    Module.finrank ℚ
        (subspaceSum ℚ
          (fun i ↦ ambientSubspaceOf blockLabel specialVector
            blockClass specialClass (index i)) J) =
      n + Module.finrank ℚ (Submodule.span ℚ
        (quotientLabelOf blockLabel specialVector blockClass specialClass ∘
          index '' (J : Set I))) := by
  rw [subspaceSum_ambientSubspaceOf_eq_corePlus
    blockLabel specialVector blockClass specialClass index hBlock,
    finrank_corePlus]

end BlandJensenFormal.BlandJensenMI.ClassifiedGeometry
