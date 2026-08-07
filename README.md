# Lean Formalization: Infinitely Many Excluded Minors for Weak Orientability

This repository contains a Lean 4 formalization of an infinite family of
pairwise nonisomorphic excluded minors for weak orientability of finite
matroids, and of the resulting nonexistence of a finite forbidden-minor
characterization.

The development uses Lean `4.29.0` and Mathlib `v4.29.0`. Exact direct and
transitive dependency revisions are recorded in `lake-manifest.json`.

## Formalized scope

The development formalizes:

1. the ground set, basis family, basis exchange, and cardinality of the
   De Loera--Lee--Margulies--Miller matroids `MI n`;
2. the literal signed circuit--cocircuit definition of weak orientability and
   its equivalence with the associated `F2` linear system;
3. the nine-equation parity obstruction for the actual matroid `MI n`;
4. exact rational representations of six actual one-element deletions and
   contractions, together with the symmetry reduction covering every element;
5. weak orientability of every proper minor and the excluded-minor theorem;
6. pairwise nonisomorphism of the family and the nonexistence of a finite
   forbidden-minor characterization, in both the signed-set and `F2` forms.

## Verification

Install `elan`, clone the repository, and run from its root:

```bash
lake exe cache get
./scripts/verify.sh
```

The cache command is optional and only reduces build time. The verification
script:

1. rejects `sorry`, `admit`, custom `axiom`, `native_decide`,
   `implemented_by`, and `unsafe` declarations in the project source;
2. builds `BlandJensenFormal.Main`;
3. runs `Audit/KernelAxiomGate.lean` on the public theorem roots.

For each public root, the kernel axiom report contains exactly
`[propext, Classical.choice, Quot.sound]` and no project-specific axioms.

## Main declarations

The following declarations are in namespace
`BlandJensenFormal.BlandJensenMI`:

- `signedWeaklyOrientable_iff_weaklyOrientable`;
- `MI_isWeakOrientabilityExcludedMinor`;
- `all_MI_are_weakOrientabilityExcludedMinors`;
- `infinite_pairwise_nonisomorphic_excluded_minor_family`;
- `bland_jensen_no_finite_excluded_minor_cover`;
- `bland_jensen_no_finite_weakOrientability_forbiddenMinorCharacterization`;
- `bland_jensen_no_finite_signedWeakOrientability_forbiddenMinorCharacterization`.

The public module entry point is `BlandJensenFormal.Main`, and the aggregate
library root is `BlandJensenFormal.lean`.

## Associated manuscript

The manuscript and corresponding formal-verification materials are available
at [OSF](https://osf.io/nvp4g/overview?view_only=7dada8f1565543a293a70f098847d177).
