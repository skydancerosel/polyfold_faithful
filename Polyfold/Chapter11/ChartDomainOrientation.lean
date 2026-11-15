import Polyfold.Chapter6.ChartOrientationSpace
import Polyfold.Chapter11.FaceIntersectionCounterexample

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §6.6,
pp. 219–230: **Theorems 6.6.11, 6.6.13 and 6.6.17** over the base domain of a strong bundle
chart, without sc-smooth bump functions.

# Orientations over the domain of a chart

## The text, paraphrased

The constructions of §6.6 are local: Proposition 6.6.3 writes the sc⁺-sections `s` and `q` in a
strong bundle chart, "assuming `X = U`", and the propagation of orientations takes place in the
neighbourhoods `U(x)` of Theorem 6.6.11.

## What is formalized

Let `P : Y → X` be a strong bundle over a tame M-polyfold, `f` an sc-Fredholm section with tame
germ data and `c` a chart of the atlas, `V = dom φ_c` its base domain (with a point `x ∈ V`).
The restriction `P|V` (`StrongBundle.restrictOpen`) has the chart `c|V` over its whole base, `V`
is tame, and `f|V` has tame germ data.  Hence, with no bump functions:

* `exists_chart_source_eq_univ_restrictOpen`: `P|V` has a chart of its atlas over the whole base
  (the hypothesis of the `_of_chart` theorems holds for every chart domain).
* `theorem_6_6_11_restrictOpen_chart`: Theorem 6.6.11 for `f|V`.
* `theorem_6_6_13_restrictOpen_chart`: Theorem 6.6.13 for `f|V`.
* `theorem_6_6_17_restrictOpen_chart`: Theorem 6.6.17 for `f|V`.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Function CategoryTheory

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- **The restriction of a strong bundle to the base domain of a chart has a chart over its whole
base**: for a chart `c` of the atlas of `P` and `V = dom φ_c`, the transported chart `c|V` is a
chart of the atlas of `P|V` with base domain `V`. -/
theorem exists_chart_source_eq_univ_restrictOpen {c : StrongBundleChart PX P}
    (hc : c ∈ B.atlas.charts) [Nonempty c.φ.source] [ParacompactSpace c.φ.source]
    [ParacompactSpace (pullbackSpace P (Subtype.val : c.φ.source → X))] :
    ∃ c' ∈ (B.restrictOpen c.φ.isOpen_source).atlas.charts, c'.φ.source = univ := by
  obtain ⟨v⟩ := ‹Nonempty c.φ.source›
  obtain ⟨y, hy⟩ := B.surjective v.1
  exact ⟨c.restrictTo B.continuous c.φ.isOpen_source subset_rfl ⟨(v, y), hy⟩,
    StrongBundle.restrictTo_mem_restrictOpen_atlas c.φ.isOpen_source (B.isChart_of_mem hc)
      subset_rfl _, eq_univ_of_forall fun w => w.2⟩

section Restrict

variable (hX : PX.IsTame) (hf : B.IsScFredholmSectionTame f) {c : StrongBundleChart PX P}
  (hc : c ∈ B.atlas.charts) {x₀ : X} (hx₀ : x₀ ∈ c.φ.source)

include hX hc hx₀

/-- **Theorem 6.6.11 over the base domain of a chart, without bump functions**: for a strong
bundle `P` over a tame `X`, an sc-Fredholm section `f` with tame germ data and a chart `c` of the
atlas with base domain `V ∋ x₀`, every smooth point of `V` has an open neighbourhood `U` in `V`
with the local propagation property for `f|V`. -/
theorem theorem_6_6_11_restrictOpen_chart :
    haveI : Nonempty c.φ.source := ⟨⟨x₀, hx₀⟩⟩
    haveI := PX.paracompactSpace_subtype c.φ.source
    haveI := paracompactSpace_pullbackSpace (f := (Subtype.val : c.φ.source → X))
      (PX.restrictOpen c.φ.isOpen_source) B
    haveI := paracompactSpace_rn_prod (PX.restrictOpen c.φ.isOpen_source)
    haveI := paracompactSpace_rn_pullback (B.restrictOpen c.φ.isOpen_source)
    ∀ v ∈ (PX.restrictOpen c.φ.isOpen_source).smoothSet,
      ∃ (c' : StrongBundleChart (PX.restrictOpen c.φ.isOpen_source)
          (pullbackProj P (Subtype.val : c.φ.source → X)))
        (hc' : (B.restrictOpen c.φ.isOpen_source).IsChart c') (U : Set c.φ.source),
        IsOpen U ∧ v ∈ U ∧
        HasLocalPropagation (restrictSection P c.φ.source f hf.isScSmooth.1)
          (hf.restrictOpen c.φ.isOpen_source).toIsScFredholmSection c' hc' U := by
  have : Nonempty c.φ.source := ⟨⟨x₀, hx₀⟩⟩
  have := PX.paracompactSpace_subtype c.φ.source
  have := paracompactSpace_pullbackSpace (f := (Subtype.val : c.φ.source → X))
    (PX.restrictOpen c.φ.isOpen_source) B
  have := paracompactSpace_rn_prod (PX.restrictOpen c.φ.isOpen_source)
  have := paracompactSpace_rn_pullback (B.restrictOpen c.φ.isOpen_source)
  have := paracompactSpace_rn_rn_prod (PX.restrictOpen c.φ.isOpen_source)
  have := paracompactSpace_rn_rn_pullback (B.restrictOpen c.φ.isOpen_source)
  intro v hv
  exact theorem_6_6_11_of_chart (MPolyfold.isTame_restrictOpen PX c.φ.isOpen_source hX)
    (exists_chart_source_eq_univ_restrictOpen hc) (hf.restrictOpen c.φ.isOpen_source) hv

/-- **Theorem 6.6.13 over the base domain of a chart, without bump functions**: for `P`, `f`,
`c`, `V` as in `theorem_6_6_11_restrictOpen_chart`, there is a unique functor `Γ_{f|V}` on the
category of smooth points of `V` and classes of sc-smooth paths in `V` with property (∗). -/
theorem theorem_6_6_13_restrictOpen_chart :
    haveI : Nonempty c.φ.source := ⟨⟨x₀, hx₀⟩⟩
    haveI := PX.paracompactSpace_subtype c.φ.source
    haveI := paracompactSpace_pullbackSpace (f := (Subtype.val : c.φ.source → X))
      (PX.restrictOpen c.φ.isOpen_source) B
    haveI := paracompactSpace_rn_prod (PX.restrictOpen c.φ.isOpen_source)
    haveI := paracompactSpace_rn_pullback (B.restrictOpen c.φ.isOpen_source)
    ∃! G : ∀ x y : PathCat (PX.restrictOpen c.φ.isOpen_source), (x ⟶ y) →
        (Orx (restrictSection P c.φ.source f hf.isScSmooth.1)
            (hf.restrictOpen c.φ.isOpen_source).toIsScFredholmSection x.pt x.smooth ≃
          Orx (restrictSection P c.φ.source f hf.isScSmooth.1)
            (hf.restrictOpen c.φ.isOpen_source).toIsScFredholmSection y.pt y.smooth),
      (∀ x, G x x (𝟙 x) = Equiv.refl _) ∧
      (∀ (x y z : PathCat (PX.restrictOpen c.φ.isOpen_source)) (a : x ⟶ y) (b : y ⟶ z),
        G x z (a ≫ b) = (G x y a).trans (G y z b)) ∧
      IsStarProperty (restrictSection P c.φ.source f hf.isScSmooth.1)
        (hf.restrictOpen c.φ.isOpen_source).toIsScFredholmSection G := by
  have : Nonempty c.φ.source := ⟨⟨x₀, hx₀⟩⟩
  have := PX.paracompactSpace_subtype c.φ.source
  have := paracompactSpace_pullbackSpace (f := (Subtype.val : c.φ.source → X))
    (PX.restrictOpen c.φ.isOpen_source) B
  exact theorem_6_6_13_of_chart (MPolyfold.isTame_restrictOpen PX c.φ.isOpen_source hX)
    (exists_chart_source_eq_univ_restrictOpen hc) (hf.restrictOpen c.φ.isOpen_source)

/-- **Theorem 6.6.17 over the base domain of a chart, without bump functions**: for a strong
bundle `P` over a tame `X`, an sc-Fredholm section `f` with tame germ data and a chart `c` of the
atlas with base domain `V ∋ x₀`, there is exactly one topology on the orientation space
`O_{f|V}` which is Hausdorff and has properties (1), (2) and (3). -/
theorem theorem_6_6_17_restrictOpen_chart :
    haveI : Nonempty c.φ.source := ⟨⟨x₀, hx₀⟩⟩
    haveI := PX.paracompactSpace_subtype c.φ.source
    haveI := paracompactSpace_pullbackSpace (f := (Subtype.val : c.φ.source → X))
      (PX.restrictOpen c.φ.isOpen_source) B
    haveI := paracompactSpace_rn_prod (PX.restrictOpen c.φ.isOpen_source)
    haveI := paracompactSpace_rn_pullback (B.restrictOpen c.φ.isOpen_source)
    ∃! t : TopologicalSpace (OrSpace (restrictSection P c.φ.source f hf.isScSmooth.1)
        (hf.restrictOpen c.φ.isOpen_source).toIsScFredholmSection),
      IsOrientationTopology (restrictSection P c.φ.source f hf.isScSmooth.1)
        (hf.restrictOpen c.φ.isOpen_source).toIsScFredholmSection t := by
  have : Nonempty c.φ.source := ⟨⟨x₀, hx₀⟩⟩
  have := PX.paracompactSpace_subtype c.φ.source
  have := paracompactSpace_pullbackSpace (f := (Subtype.val : c.φ.source → X))
    (PX.restrictOpen c.φ.isOpen_source) B
  exact theorem_6_6_17_of_chart (MPolyfold.isTame_restrictOpen PX c.φ.isOpen_source hX)
    (exists_chart_source_eq_univ_restrictOpen hc) (hf.restrictOpen c.φ.isOpen_source)

end Restrict

end Polyfold
