import Polyfold.Chapter18.AuxiliaryNormsDirect

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 18,
§18.1, pp. 847–848: the paragraph after **Definition 18.1.9** ("any sc-smooth model has reflexive
`(0, 1)`-fibers") read for the pieces of a model, and **Definition 18.1.11** compared with its
reading through the models under the hypotheses of the text.

# Reflexive fibres of a model and of its pieces

## The text, paraphrased

(Definition 18.1.9) `P : E → C` has reflexive `(0, 1)`-fibres if the `(0, 1)`-fibre over every
object is reflexive.  (After 18.1.9) "If `p : W → X` is a local model for `P` … `(W_x)_{(0,1)}` is a
reflexive Banach space.  In other words any sc-smooth model has reflexive `(0, 1)`-fibers."

## What is formalized

* `StrongBundle.hasReflexiveFibers_of_sigma`: **if `⊔ K_λ → ⊔ O_λ` has reflexive `(0, 1)`-fibres
  (Definition 5.1.4), so has every piece `K_λ → O_λ`**: a chart of the disjoint union around
  `(λ, x)` is restricted to the open summand `range (mk λ)` (`restrictInter`, which keeps `F`)
  and carried to `K_λ` along the inclusion of the piece (`sigmaMkLocalIso`, `transportChart`, which
  keeps the model `K ◁ F`); `hasReflexiveFibers_sigma_iff` with the converse
  `hasReflexiveFibers_sigma`.
* `StrongPolyfoldBundleConstruction.HasReflexiveFibersIn.hasReflexivePieces`,
  `hasReflexivePieces_iff`: the condition `HasReflexivePieces c` used for
  `isReflexiveAuxNormDirect_iff_hyp` is the reflexivity of the `(0, 1)`-fibres of the model `c`
  (Definition 18.1.9 read in a model, `HasReflexiveFibersIn`).
* **`isReflexiveAuxNormDirect_iff_of_hasReflexiveFibers`**: for a strong polyfold bundle with
  reflexive `(0, 1)`-fibres (Definition 18.1.9 in the models, `HasReflexiveFibers`), with a
  covering family, Definition 18.1.11 (direct form) and its reading through the models agree;
  **`isReflexiveAuxNormDirect_iff_of_hasReflexiveFibersIn`** with reflexivity in one covering
  model.  These are `isReflexiveAuxNormDirect_iff_hyp` with its hypothesis derived from the
  text's.

## Reading

Definition 18.1.9 is read in the models (`HasReflexiveFibers`, as in `AuxiliaryNorms.lean`); the
sentence after it is then the statement that the reflexivity passes to the pieces of a model,
which is what `hasReflexiveFibers_of_sigma` proves.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

namespace StrongBundle

section Sigma

variable {ι : Type*} {X : ι → Type u} [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)]
  [∀ i, ParacompactSpace (X i)] {PX : ∀ i, MPolyfold (X i)}
  {Y : ι → Type u} [∀ i, TopologicalSpace (Y i)] [∀ i, T2Space (Y i)]
  [∀ i, ParacompactSpace (Y i)] {p : ∀ i, Y i → X i}
  [∀ i x, AddCommGroup (p i ⁻¹' {x})] [∀ i x, Module ℝ (p i ⁻¹' {x})]
  {B : ∀ i, StrongBundle (PX i) (p i)}

/-- **Reflexive `(0, 1)`-fibres of a disjoint union give reflexive `(0, 1)`-fibres of every
piece** (Definition 5.1.4): a chart of `⊔ K_λ` around `(λ, x)` with reflexive `F₁`, restricted to
the summand `range (mk λ)` and carried to `K_λ` along the inclusion of the piece, is a chart of
`K_λ` around `x` with the same `F`. -/
theorem hasReflexiveFibers_of_sigma (h : (StrongBundle.sigma B).HasReflexiveFibers) (i : ι) :
    (B i).HasReflexiveFibers := by
  intro x
  obtain ⟨c, hc, hx, hF⟩ := h ⟨i, x⟩
  have hV : IsOpen (range (Sigma.mk i : X i → Σ j, X j)) := isOpen_range_sigmaMk
  have hc' := hc.restrictInter hV
  have hsub : (c.restrictInter hV).φ.source ⊆ range (Sigma.mk i) :=
    c.restrictInter_source_subset hV
  refine ⟨(sigmaMkLocalIso B i x).transportChart (c.restrictInter hV) hsub,
    (sigmaMkLocalIso B i x).isChart_transportChart _ hsub hc', ⟨mem_univ _, ?_⟩, hF⟩
  exact c.mem_restrictInter_source hV hx ⟨x, rfl⟩

/-- **A disjoint union has reflexive `(0, 1)`-fibres iff every piece has.** -/
theorem hasReflexiveFibers_sigma_iff :
    (StrongBundle.sigma B).HasReflexiveFibers ↔ ∀ i, (B i).HasReflexiveFibers :=
  ⟨hasReflexiveFibers_of_sigma, hasReflexiveFibers_sigma⟩

end Sigma

end StrongBundle

namespace GCT.VectorBundle.StrongPolyfoldBundleConstruction

variable {C : GCT.{u}} {V : C.VectorBundle} {S : C.PolyfoldConstruction}
  {Q : V.StrongPolyfoldBundleConstruction S}

open scoped ENNReal

/-- **Reflexive `(0, 1)`-fibres of the model `c` give reflexive `(0, 1)`-fibres of its strong
bundle uniformizers** (the paragraph after Definition 18.1.9). -/
theorem HasReflexiveFibersIn.hasReflexivePieces {c : Q.BundleCoveringFamily}
    (h : Q.HasReflexiveFibersIn c.Ψ) : Q.HasReflexivePieces c :=
  StrongBundle.hasReflexiveFibers_of_sigma h

/-- `HasReflexivePieces c` is the reflexivity of the `(0, 1)`-fibres of the model `c`. -/
theorem hasReflexivePieces_iff (c : Q.BundleCoveringFamily) :
    Q.HasReflexivePieces c ↔ Q.HasReflexiveFibersIn c.Ψ :=
  ⟨HasReflexivePieces.hasReflexiveFibersIn, HasReflexiveFibersIn.hasReflexivePieces⟩

/-- **Definition 18.1.11 and its reading through the models agree** when one covering model has
reflexive `(0, 1)`-fibres (Definition 18.1.9 in a model). -/
theorem isReflexiveAuxNormDirect_iff_of_hasReflexiveFibersIn (c : Q.BundleCoveringFamily)
    (hB : Q.HasReflexiveFibersIn c.Ψ) {N : V.EObj → ℝ≥0∞} :
    Q.IsReflexiveAuxNormDirect N ↔ Q.IsReflexiveAuxNormFunctor N :=
  isReflexiveAuxNormDirect_iff_hyp c hB.hasReflexivePieces

/-- **Definition 18.1.11 and its reading through the models agree for a strong polyfold bundle
with reflexive `(0, 1)`-fibres** (Definition 18.1.9, read in the models), given a covering
family: the hypothesis of `isReflexiveAuxNormDirect_iff_hyp` is the text's. -/
theorem isReflexiveAuxNormDirect_iff_of_hasReflexiveFibers (c : Q.BundleCoveringFamily)
    (hB : Q.HasReflexiveFibers) {N : V.EObj → ℝ≥0∞} :
    Q.IsReflexiveAuxNormDirect N ↔ Q.IsReflexiveAuxNormFunctor N :=
  isReflexiveAuxNormDirect_iff_of_hasReflexiveFibersIn c (hB c)

end GCT.VectorBundle.StrongPolyfoldBundleConstruction

end Polyfold
