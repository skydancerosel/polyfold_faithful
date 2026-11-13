import Polyfold.Chapter6.DetBundle

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), the opening of §6.6
(p. 262): **the classical case**.  Gap G.60, in part.

# The determinant line bundle of a classical Fredholm map

## The text, paraphrased

For a smooth map `f : U → F` on an open subset `U` of a Banach space `E` whose derivatives are
Fredholm, the determinant lines of the `Df(x)` form a continuous (even smooth) line bundle over
`U`; if `U` is contractible it has precisely two orientations, and an orientation of one line
determines an orientation of all the others.

## What is formalized

For `f` of class `C¹` on an open `U` with every `Df(x)`, `x ∈ U`, Fredholm:

* `derivFredholm`: `x ↦ Df(x)` as a continuous map `U → F(E, F)`;
* `ClassicalDet`: the pull-back of `DET(E, F)` along it, a topological line bundle over `U`
  (`classicalDet_vectorBundle`);
* `classicalDet_two_orientations`: if `U` is contractible, it has precisely two orientations, and
  every orientation of one line `det(Df(x₀))` extends to exactly one orientation of the bundle.

"Smooth" is weakened to `C¹`.  The smoothness of the bundle ("even smooth") is not formalized:
`DET(E, F)` is built as a topological vector bundle (Proposition 6.5.8).  The remark at the end of
§6.5 (p. 262) that `DET(E, F)` is not orientable is formalized, in a corrected form, in
`GapP1_DetNonOrientable`, `GapP1_DetNonOrientableEll2` and `GapP1_DetNonOrientableTransport`
(`isEmpty_lineOrientation_det_of_complexStructure`, `isEmpty_lineOrientation_det_hilbert`; for
finite-dimensional `E`, `F` there are two orientations,
`exists_two_lineOrientation_det_of_finiteDimensional`).
-/

open Bundle Topology Set

noncomputable section

namespace Polyfold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {f : E → F} {U : Set E}

/-- **`x ↦ Df(x)`** as a continuous map `U → F(E, F)` for `f` of class `C¹` on an open `U` with
Fredholm derivatives. -/
def derivFredholm (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    (hF : ∀ x ∈ U, (fderiv ℝ f x).IsFredholm) : C(U, FredholmOp E F) :=
  ⟨fun x => ⟨fderiv ℝ f x, hF x x.2⟩,
    (continuousOn_iff_continuous_domRestrict.1
      (hf.continuousOn_fderiv_of_isOpen hU le_rfl)).subtype_mk _⟩

/-- **The determinant line bundle of `f` (2021, p. 262)**: the lines `det(Df(x))`, `x ∈ U`, as the
pull-back of `DET(E, F)` along `x ↦ Df(x)`. -/
abbrev ClassicalDet (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    (hF : ∀ x ∈ U, (fderiv ℝ f x).IsFredholm) : U → Type _ :=
  (derivFredholm hU hf hF : U → FredholmOp E F) *ᵖ DetFiber

omit [CompleteSpace E] [CompleteSpace F] in
/-- The fibre over `x` is `det(Df(x))`. -/
theorem classicalDet_apply (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    (hF : ∀ x ∈ U, (fderiv ℝ f x).IsFredholm) (x : U) :
    ClassicalDet hU hf hF x = fredholmDet (fderiv ℝ f x) := rfl

/-- **(2021, p. 262)** The determinant lines of `f` form a topological line bundle over `U`. -/
theorem classicalDet_vectorBundle (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    (hF : ∀ x ∈ U, (fderiv ℝ f x).IsFredholm) :
    VectorBundle ℝ ℝ (ClassicalDet hU hf hF) :=
  inferInstance

/-- **(2021, p. 262)** If `U` is contractible, the determinant line bundle of `f` has precisely
two orientations, and an orientation of one line `det(Df(x₀))` determines exactly one orientation
of all the others. -/
theorem classicalDet_two_orientations (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    (hF : ∀ x ∈ U, (fderiv ℝ f x).IsFredholm) [ContractibleSpace U] :
    (∃ o₁ o₂ : LineOrientation (ClassicalDet hU hf hF), o₁ ≠ o₂ ∧
      ∀ o : LineOrientation (ClassicalDet hU hf hF), o = o₁ ∨ o = o₂) ∧
    ∀ (x₀ : U) (r : Module.Ray ℝ (ClassicalDet hU hf hF x₀)),
      ∃! o : LineOrientation (ClassicalDet hU hf hF), o x₀ = r := by
  have : LocallyPathConnectedSpace U := hU.locallyPathConnectedSpace
  refine ⟨exists_two_lineOrientation, fun x₀ r => ?_⟩
  obtain ⟨o, ho⟩ := exists_lineOrientation_apply_eq x₀ r
  exact ⟨o, ho, fun o' ho' => LineOrientation.eq_of_apply_eq x₀ (ho'.trans ho.symm)⟩

end Polyfold
