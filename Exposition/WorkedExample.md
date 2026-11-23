# A worked example: the orbifold ℂ/ℤ₅ and the section z ↦ z²

Theorem 16.6.6 (p. 739) for Fredholm index 0, carried out on one small polyfold, from the ep-groupoid
to the value of the invariant. The Lean files are in `Polyfold/Examples/`; the namespace is
Polyfold.Examples.OrbifoldSquare unless a name says otherwise. Everything below is proved, with no
`sorry` and only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## The example

* **The ep-groupoid** `X5`: the action groupoid ℤ/5 ⋉ ℂ, with ζ = e^{2πi/5} acting by z ↦ ζz.
  It is effective (`isEffective_X5`); the isotropy group of 0 is ℤ/5 (`isotropyZeroEquiv`), and every
  other point has trivial isotropy (`isRegular_X5_iff`).
* **The strong bundle** `E5`: fibre ℂ, with the action of weight 2, ζ · (z, w) = (ζz, ζ²w).
* **The section** f(z) = (z, z²), equivariant because (ζz)² = ζ²z². It is sc-Fredholm of index 0
  (`isScFredholmSectionFunctor_sqSection`, `isIndexAt_sqSection`), and its solution set is {0}.
* **The polyfold bundle** `sqBundle` and the Fredholm section `sqFredholmSection` on the orbit space;
  the auxiliary norm n is the Euclidean norm of the fibre (`n5`), and U is all of Z.

## Why this example: multisections are needed

A single-valued equivariant perturbation cannot make f transversal. For an equivariant sc⁺-section s,
s(ζz) = ζ²s(z). At z = 0 this gives s(0) = ζ²s(0); weight 2 has no invariant vectors, so s(0) = 0
and 0 remains a solution. The linearization (f − s)′(0) = −Ds(0) is a real-linear map L of ℂ with
L(ζz) = ζ²L(z). Writing L(z) = az + b z̄, this asks a(ζ − ζ²) = 0 and b(ζ⁻¹ − ζ²) = 0; since
2 ≢ ±1 mod 5, both factors are non-zero, so L = 0, which is not onto.
In Lean: `linear_eq_zero_of_equivariant` and **`not_isTransversalAt_sectionMulti`** (for every
sc⁺-section functor s, the multisection of s is not transversal at 0).

A multisection is transversal. For c ≠ 0, the multisection λ_c has the five constant branches
ζ^{2j}c (j ∈ ℤ/5), each of weight 1/5 (`Λ5`, `t5`). It is an sc⁺-multisection
(`isScPlusMultisection_Λ5`), in general position (`isInGeneralPosition_Λ5`), and controlled by (n, Z)
for |c| ≤ 1 (`isControlledBy_t5`).

## What is proved

1. **The hypotheses of Theorem 16.6.6 for index 0 hold** (`theorem_16_6_6_hypotheses`): ∂Z = ∅, the
   solution set is compact, n is an auxiliary norm, Z is open, (n, Z) controls compactness, and the
   model of the orientation has tame germ data and index 0 (`CanonicalGermInput`). The theorem in its
   polyfold form is `theorem_16_6_6_sq`.
2. **λ_c is admissible** for 0 < |c| ≤ 1, and its perturbed solution set carries the canonical
   orientation of Theorem 15.4.1 (`exists_canonical_t5`). Any two admissible perturbations with the
   canonical orientation give the same count of a closed 0-form (`count_eq_of_isAdmissible`,
   `exists_unique_count`).
3. **The count is 2/5** for every admissible perturbation with the canonical orientation, on the
   constant form 1 (**`count_eq_two_fifths`**, **`count_eq_two_fifths_all`**), for the orientation
   `sqOrientationPos`: the continuous orientation that is positive at the complex-linear
   isomorphisms (f − f(y))′(y) = 2y, y ≠ 0.

## Why 2/5

Take c = 1. The perturbed solutions are the z with z² = ζ^{2j}, that is z = ±ζ^j: ten points, forming
two orbits, those of 1 and of −1 (`Λ5_sqSection_pos_iff_orbit`, `π_ne_π_neg`). Each point has trivial
isotropy (`isRegular_of_Λ5_pos`) and lies on exactly one branch, of weight 1/5 (`Λ5_sqSection_eq`).
At such a point the linearization is multiplication by 2z, complex linear, so the canonical orientation
has sign +1 there (`positiveZeros_sqOrientationRepPos`). Definition 9.5.6 for n = 0 then gives

  count = 1/5 + 1/5 = 2/5.

This agrees with the local degree 2 of z ↦ z² at 0 divided by the order 5 of the isotropy group; that
form of the answer is a remark, not a Lean statement.

## General lemmas added on the way

These hold for any strong bundle or ep-groupoid and are used by the example.

* **Counts over finitely many orbits** (Definition 9.5.6, p. 439, for n = 0):
  `Polyfold.EP.pointBranchedIntegral_eq_sum` and `Polyfold.SBLocalization.PointSolution.count_eq_sum`.
  If the orbit support is {|x| : x ∈ s} for a finite set s with distinct orbits, the integral of ω is
  Σ_{x∈s} (1/♯G_x) · signedWeight(T̂(x)) · ω(x).
* **d of a constant 0-form is 0**: `Polyfold.MPolyfold.extD_constForm` (and
  `Polyfold.EP.epFormsInftyD_constFormInfty` on ep-groupoids).
* **The sign of the canonical orientation in dimension 0** (Theorem 15.4.1, pp. 701–702).
  At a point y of a sheet of dimension 0, the sign is +1 if and only if o_y is positive at the
  isomorphism (f − s_i)′(y) (`Polyfold.SBLocalization.KernelBranching.frameSign_orTangent_eq_one_iff`).
  If o_y is positive at every branch through y, the signed weight of T̂(y) is Λ(f(y))
  (`Polyfold.SBLocalization.IsCanonicalFor.signedWeight_eq`). Positivity is carried along any
  sc-smooth path of isomorphisms (`Polyfold.isPosOr_iff_of_path`, by Theorems 6.6.11 and 6.6.13).

## Limits

* The example is finite-dimensional: ℂ with every level equal, so the sc-structure is constant. It
  exercises the definitions and theorems of Parts II and III on a polyfold with isotropy; it does not
  test the infinite-dimensional sc-calculus of Part I.
* The orientation `sqOrientationPos` is chosen as the continuous orientation positive at the
  complex-linear isomorphisms. The library also has `sqOrientation`, one of the two continuous
  orientations chosen without that normalization; that the two agree is not proved. Items 1 and 2 are
  stated for `sqOrientationRep` and repeated for `sqOrientationRepPos`
  (`canonicalGermInput_sqOrientationRepPos`, `exists_canonical_t5_pos`, `count_eq_of_isAdmissible_pos`).
  The value of the count for `sqOrientation` is not stated.

## Main declarations

| Declaration | File (`Polyfold/Examples/`) | Content |
|---|---|---|
| `X5`, `E5`, `A5`, `sqSection` | `OrbifoldSquareBundle` | ℤ/5 ⋉ ℂ, the weight-2 bundle, the section z ↦ z² |
| `isEffective_X5`, `isotropyZeroEquiv`, `isRegular_X5_iff`, `sqBundle`, `sqFredholmSection` | `OrbifoldSquareStructure` | effective, isotropy ℤ/5 at 0; the polyfold bundle and section |
| `linear_eq_zero_of_equivariant` | `OrbifoldSquareAlgebra` | an equivariant real-linear map of weight 1 → 2 is 0 |
| `not_isTransversalAt_sectionMulti` | `OrbifoldSquare` | no equivariant single-valued sc⁺-perturbation is transversal |
| `sqOrientationRep`, `canonicalGermInput_sqOrientationRep` | `OrbifoldSquareOrientation` | an orientation (Definition 16.6.5) with tame germ data and index 0 |
| `isAuxNorm_n5`, `controlsCompactness_n5`, `Λ5`, `t5`, `isInGeneralPosition_Λ5`, `isControlledBy_t5` | `OrbifoldSquarePerturbation` | the auxiliary norm; the five-branch multisection |
| `theorem_16_6_6_hypotheses`, `theorem_16_6_6_sq`, `exists_canonical_t5`, `count_eq_of_isAdmissible`, `exists_unique_count` | `OrbifoldSquare` | Theorem 16.6.6 for index 0 on the example |
| `count_t5`, `sqOne`, `d_sqOne` | `OrbifoldSquareCount` | the count as a sum over the two orbits; the closed form 1 |
| `sqOrientationPos`, `sqOrientationRepPos`, `positiveZeros_sqOrientationRepPos` | `OrbifoldSquareSign` | the orientation positive at the complex-linear isomorphisms; signs +1 |
| **`count_eq_two_fifths`**, **`count_eq_two_fifths_all`** | `OrbifoldSquareSign` | the count is 2/5 |
| `Polyfold.EP.pointBranchedIntegral_eq_sum`, `Polyfold.SBLocalization.PointSolution.count_eq_sum` | `PointCountFiniteSupport` | counts over finitely many orbits |
| `Polyfold.MPolyfold.extD_constForm` | `ConstantFormClosed` | d of a constant 0-form is 0 |
| `Polyfold.SubspaceFamily.cont_emptyRay` | `SignDimZeroLinear` | rank 0: the continuation keeps the empty-wedge ray |
| `Polyfold.IsPosOr`, `Polyfold.isPosOr_iff_of_path` | `SignDimZeroPush` | positivity at an isomorphism, carried along paths |
| `Polyfold.SBLocalization.KernelBranching.frameSign_orTangent_eq_one_iff`, `Polyfold.SBLocalization.IsCanonicalFor.signedWeight_eq` | `SignDimZeroFrames` | the sign of the canonical orientation in dimension 0 |
