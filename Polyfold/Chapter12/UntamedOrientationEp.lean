import Polyfold.Chapter6.UntamedOrientation
import Polyfold.Chapter8.NonVacuityBundle
import Polyfold.Chapter12.OrientationOrbit

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, §12.5:
**Definition 12.5.2** and **Theorem 12.5.3** (pp. 593–594; 2017: Theorem 12.11), read with the
2021 sc-Fredholm notion of Part I's **Definitions 3.1.16 = 3.6.4** (pp. 96, 135), whose germ data
need not sit in a tame chart.

# Theorem 12.5.3 with the 2021 (untamed) sc-Fredholm notion: the statement

## The text, paraphrased

(Theorem 12.5.3) For a strong bundle `(P : W → X, μ)` over a tame ep-groupoid and an sc-Fredholm
section functor `f`, the orientation space `O_f` over `X_∞` has a topology with the properties of
Theorem 6.6.17 (Hausdorff, `σ : O_f → X_∞` a local homeomorphism, the local propagation), and
the morphisms act on it.

## What is formalized

For the strong bundle `bundle : K → O` of `Chapter3/UntamedBundle.lean` over the trivial
ep-groupoid of the tame M-polyfold `O ≅ ℝ` (objects and morphisms `O`, all structure maps the
identity; `EpGroupoid.trivial`, `EpStrongBundle.trivial`) and the section functor `sec`:

* `isScFredholmSectionFunctor_sec`: `sec` is an sc-Fredholm section functor (Definition 8.3.4 (3)
  with Part I's Definitions 3.1.16 = 3.6.4).
* `not_theorem_12_5_3_conclusion`: no topology on `O_sec` has the properties of Theorem 6.6.17,
  so the conclusion of `theorem_12_5_3_hyp` does not hold.
* `theorem_12_5_3_untamed_not`: **the statement of `theorem_12_5_3_hyp` with an sc-Fredholm
  section functor in the sense of 2021 Definitions 3.1.16 = 3.6.4 in place of tame germ data
  (`IsScFredholmSectionTame`) does not hold as we read it**, for a tame strong bundle over a tame
  ep-groupoid whose object M-polyfold admits sc-smooth bump functions.

## What this says about the text

The topological part of Theorem 12.5.3 is Part I's Theorem 6.6.17 for the object bundle; the
example of `Chapter6/UntamedOrientation.lean` is an ep-groupoid with identity morphisms only, so
the hypothesis "germ data in tame charts" of `theorem_12_5_3_hyp` is used and is not a consequence
of the tameness of `X`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

namespace UntamedCorner

/-- `sec` is an sc-Fredholm section functor of `K → O` over the trivial ep-groupoid of `O`. -/
theorem isScFredholmSectionFunctor_sec :
    (EpStrongBundle.trivial bundle).IsScFredholmSectionFunctor sec :=
  ⟨⟨isScSmoothSection_sec, EpStrongBundle.isFunctorialSection_trivial isSection_sec⟩,
    isScFredholmSection_sec⟩

/-- **The conclusion of `theorem_12_5_3_hyp` (2021 Theorem 12.5.3, the topology of `O_f`) does not
hold for `sec` over the trivial ep-groupoid of `O`.** -/
theorem not_theorem_12_5_3_conclusion :
    haveI := paracompactSpace_rn_prod (EpGroupoid.trivial polyO).PObj
    haveI := paracompactSpace_rn_pullback (PX := (EpGroupoid.trivial polyO).PObj) bundle
    ¬ ∃ t : TopologicalSpace (OrSpace sec isScFredholmSectionFunctor_sec.2),
      IsOrientationTopology sec isScFredholmSectionFunctor_sec.2 t :=
  not_isOrientationTopology_sec

/-- **2021 Theorem 12.5.3, p. 594, read with the 2021 sc-Fredholm notion, does not hold as we read
it**: the statement of `theorem_12_5_3_hyp` (there is exactly one topology on `O_f` with the
properties of Theorem 6.6.17) for an sc-Fredholm section functor in the sense of Definition 8.3.4
(3) with Part I's Definitions 3.1.16 = 3.6.4 (germ data in any compatible chart), over a tame
ep-groupoid whose object M-polyfold admits sc-smooth bump functions, with a tame strong bundle.
The counterexample is `sec` over the trivial ep-groupoid of `O`.  With germ data in tame charts
the statement is `theorem_12_5_3_hyp`. -/
theorem theorem_12_5_3_untamed_not :
    ¬ ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
      (W : Type) [TopologicalSpace W] [T2Space W] [ParacompactSpace W] (P : W → Obj)
      [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] (B : StrongBundle X.PObj P)
      (E : EpStrongBundle X B) (f : Obj → W), X.IsTame → B.IsTameBundle →
      X.PObj.AdmitsBumpFunctions → ∀ hF : E.IsScFredholmSectionFunctor f,
      haveI := paracompactSpace_rn_prod X.PObj
      haveI := paracompactSpace_rn_pullback B
      ∃! t : TopologicalSpace (OrSpace f hF.2), IsOrientationTopology f hF.2 t := fun h =>
  not_theorem_12_5_3_conclusion (h Ob Ob (EpGroupoid.trivial polyO) Kt kproj bundle
    (EpStrongBundle.trivial bundle) sec (EpGroupoid.isTame_trivial polyO isTame_polyO)
    isTameBundle_bundle admitsBumpFunctions_polyO isScFredholmSectionFunctor_sec).exists

end UntamedCorner

end Polyfold
