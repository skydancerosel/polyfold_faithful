import Polyfold.Chapter3.Book2021Germs
import Polyfold.Chapter3.RestrictOpenGerms

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Definition 3.1.11 (p. 96)
and Definition 3.6.3 (p. 135), the sc-Fredholm germ, with Definition 2.5.2 (p. 53), tame
retractions, and the proofs of Theorems 3.1.22 (p. 100) and 3.6.8 (pp. 136–138) *(2014 preprint:
Definitions 3.1.11, 3.6.3, 2.5.2 (preprint 3.11, 3.50, 2.34); Theorems 3.1.22, 3.6.8 (preprint 3.19, 3.54))*: **when do the untamed germ data of the 2021
definitions move to a tame chart?**  Gap G.79 (Findings, Chapter 3, items 199, 350–353, 373, 379).

# Germ data in a chart centred at an interior point of its quadrant are tame germ data

## The text, paraphrased

(Definition 3.6.3, 2021) `(f, x)` is an sc-Fredholm germ if there exists a strong bundle chart
`Φ : P⁻¹(V) → K` covering `φ : (V, x) → (O, 0)`, "where `K → O` is a strong local bundle containing
`0 ∈ O ⊂ U`", such that `Φ ∘ f ∘ φ⁻¹` has a filling `g` near `0` and a local sc⁺-section `s` with
`s(0) = g(0)` such that `g − s` is conjugated near `0` to a basic germ.  **The 2021 text no longer
asks the local bundle `K → O` to be tame** (the preprint's Definition 3.50 and the 2017 Definition
3.14 did).  (Theorem 3.6.8) "Let `f` be an sc-Fredholm section of a tame strong bundle `Y → X`";
its proof, p. 137, takes "a strong bundle chart of the tame strong bundle `P`" from the definition
of an sc-Fredholm germ, "covering the tame sc-smooth retraction `r`", and on p. 138 uses that "the
retract `O = r(U)` is, by assumption, tame" to pass from good position in `T₀O` to good position
in `E` through the sc-complement `ker Dr(0) ⊆ E₀`.  The phrase "tame strong bundle" is not defined
in the 2021 text (only "tame strong bundle retraction", p. 65, and "tame local strong bundle
retract", Definition 2.6.2).  (Definition 2.5.2) `r : U → U` is tame if `d_C(r(x)) = d_C(x)` on
`U` and every `T_xO`, `x ∈ O` smooth, has an sc-complement inside `E_x`.

## What is formalized

* **Interior points of a partial quadrant.**  `Polyfold.fst_ne_zero_of_mem_interior`: at a point
  of the interior of `C = T⁻¹([0, ∞)ⁿ ⊕ W)` no half-line coordinate vanishes;
  `degIndex_eq_zero_of_mem_interior` and `mem_interior_iff_degIndex_eq_zero`: for `x ∈ C`,
  `x ∈ int C ⟺ d_C(x) = 0`; `minimalSubspaceWith_eq_top_of_mem_interior`: `E_x = E` there.
* **Shrinking a strong bundle chart to an open set of the model**
  (`Polyfold.StrongBundleChart.shrink`): for `W ⊆ E₀` open with `r(U ∩ W) ⊆ W`, the chart
  `(Φ|P⁻¹(V ∩ φ⁻¹(W)), (U ∩ W) ◁ F, R)` over `φ|V ∩ φ⁻¹(W) : → O ∩ W`, with the same `R`, `Φ` and
  principal parts (`shrink_principal`).  It is compatible with every chart compatible with `c`
  (`Compatible.shrink_left`, `StrongBundle.IsChart.shrink`).  (`StrongBundleChart.restrict`,
  the restriction to an open subset of the base, keeps `U ∩ r⁻¹(W)`, which may contain boundary
  points of `C`; here `U` itself is cut down to `U ∩ W`.)
* **A chart whose domain lies in the interior of its quadrant is tame**
  (`StrongBundleChart.isTame_shrink_of_subset_interior`): `d_C ≡ 0` on `U ∩ W ⊆ int C`, and at a
  smooth `x ∈ O`, `E = T_xO ⊕ (1 − Dr(x))E` with `E_x = E`
  (`ScRetraction.isScSplitting_range_scDeriv`).
* **Main theorem** (`StrongBundle.isScFredholmGermTame_of_chart_interior`): germ data of
  Definition 3.1.11 (germ reading, `IsFillingGerm`, `IsScPlusGerm`, `IsConjugateToBasicGerm`) in a
  compatible chart `c` centred at `x₀` with `φ(x₀) = 0 ∈ int C` give **tame germ data at `x₀`**
  (`IsScFredholmGermTame`, the hypothesis of the §3.6 theorems): shrink `c` to
  `W = (U ∩ int C) ∩ r⁻¹(int C)` and restrict the germs (`IsFillingGerm.of_subset`,
  `IsScPlusGerm.of_subset`, `IsConjugateToBasicGerm.of_subset`).
* **Packaged**: `StrongBundle.IsScFredholmGermInterior` (the 2021 germ data in a chart with
  `0 ∈ int C`), with `IsScFredholmGermInterior.isScFredholmGermTame`,
  `.isScFredholmGerm2017`, `.isScFredholmGerm2021`, `.degIndex_eq_zero` (`d_X(x₀) = 0`), the
  reformulation `mem_interior_iff_chartDegIndex_eq_zero` (`0 ∈ int C ⟺ d(x₀, φ) = 0`), and
  `isScFredholmSectionTame_of_interior`: a 2021 sc-Fredholm section whose germ data are in such
  charts has tame germ data (`IsScFredholmSectionTame`), so the §3.6 theorems apply to it.
  Witness: `TrivialBundle.isScFredholmGermInterior_graphSection` (the translation charts of the
  trivial bundle have `C = ℝⁿ`).
* **The residual case of G.79 is sharpened** (`IsScFredholmGermTame.exists_chart_chartDegIndex_eq`,
  from Proposition 2.5.6, `degIndex_eq_chartDegIndex_of_isTameRetract`): tame germ data live in a
  chart with `d_C(0) = d_X(x₀)`, while the untamed germ data of Definition 3.1.11 may live in a
  chart with `d_C(0) > d_X(x₀)` (the corner example of `Book2021Germs.lean`: `d_C(0) = 1`,
  `d_X = 0`; `CornerFilling.zero_not_mem_interior`).  Germ data in a chart with `d_C(0) = 0`
  are tame germ data (this file); whether germ data in a chart with `d_C(0) ≥ 1` can be moved
  to a tame chart is what remains open.

## What the text leaves implicit, and the choices made (the findings)

* **What this settles.**  Theorem 3.1.22 is the case `d_X ≡ 0`.  If the chart of the germ data at
  `x₀` is itself centred at an interior point of its quadrant — `d_C(φ(x₀)) = 0`, as the text's
  "`C = [0, ∞)^k ⊕ ℝ^{n−k} ⊕ W`" allows with `k = 0` — the tameness the proof uses on p. 138 is
  automatic after shrinking the chart, and all §3.6 theorems hold for the 2021 definitions.
  The hypothesis `d_C(φ(x₀)) = 0` is strictly stronger than `d_X(x₀) = 0`: `d_X` is the minimum
  over charts (Definition 2.4.1), and the corner example has `d_X = 0` with `d_C(0) = 1`.
* **What stays open** (G.79, Findings item 353 (iii)): germ data in a chart with `0 ∈ ∂C`, in
  particular at every `x₀ ∈ ∂X`.  In such a chart tameness cannot be restored by changing `U` and
  `R` alone when `O` touches `∂C` (condition (1) of Definition 2.5.2 fails for the interior points
  of `C` that `r` sends into `O ∩ ∂C`), and a chart with a different model is related to `c` only
  through `K`, so the filling cannot be transported (item 353).  A proof would need an sc-smooth
  extension of `R` across `∂C` with the same image `K` (then this file applies to the extended
  chart) or a level-`0` inverse function theorem (item 379); a counterexample would need an
  invariant of germ data in charts with `0 ∈ int C` that the corner-type data violate.  Neither is
  available in the sc-calculus of the text.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

/-! ### Interior points of a partial quadrant -/

section Interior

variable {E : ScBanach} {n : ℕ} {W : ScBanach} {C : Set (E 0)}

/-- At an interior point `x` of the partial quadrant `C = T⁻¹([0, ∞)ⁿ ⊕ W)` no half-line coordinate
of `T(x)` vanishes: otherwise `x − t T⁻¹(e_i, 0) ∉ C` for every `t > 0`. -/
theorem fst_ne_zero_of_mem_interior (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (hT : C = T 0 ⁻¹' quadrant n W 0) {x : E 0} (hx : x ∈ interior C) (i : Fin n) :
    (T 0 x).1 i ≠ 0 := by
  intro hi
  set e : E 0 := (T 0).symm ((Pi.single i (1 : ℝ) : Fin n → ℝ), (0 : W 0)) with he
  have hTe : T 0 e = ((Pi.single i (1 : ℝ) : Fin n → ℝ), (0 : W 0)) := (T 0).apply_symm_apply _
  have hcont : Tendsto (fun t : ℝ => x - t • e) (𝓝 0) (𝓝 x) := by
    have : Tendsto (fun t : ℝ => x - t • e) (𝓝 0) (𝓝 (x - (0 : ℝ) • e)) :=
      tendsto_const_nhds.sub (tendsto_id.smul_const e)
    simpa using this
  have hev : ∀ᶠ t : ℝ in 𝓝 0, x - t • e ∈ C := hcont (mem_interior_iff_mem_nhds.1 hx)
  obtain ⟨t, htC, ht⟩ :=
    ((hev.filter_mono (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))).and self_mem_nhdsWithin).exists
  rw [hT] at htC
  have h1 : (T 0 (x - t • e)).1 i = (T 0 x).1 i - t * (T 0 e).1 i := by
    rw [map_sub, map_smul]; rfl
  have h2 := htC i
  rw [h1, hi, hTe] at h2
  simp only [Pi.single_eq_same, mul_one, zero_sub, Left.nonneg_neg_iff] at h2
  exact absurd ht (not_lt.2 h2)

/-- At an interior point of `C` the degeneracy index computed with `T` is `0`. -/
theorem degIndexWith_eq_zero_of_mem_interior (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (hT : C = T 0 ⁻¹' quadrant n W 0) {x : E 0} (hx : x ∈ interior C) :
    degIndexWith T x = 0 := by
  classical
  unfold degIndexWith quadrantDeg
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _
  exact fst_ne_zero_of_mem_interior T hT hx i

/-- **`d_C(x) = 0` at an interior point** of the partial quadrant `C`. -/
theorem degIndex_eq_zero_of_mem_interior (hC : IsPartialQuadrant E C) {x : E 0}
    (hx : x ∈ interior C) : degIndex E C x = 0 := by
  obtain ⟨n, W, T, hT⟩ := hC
  rw [degIndex_eq T hT (interior_subset hx)]
  exact degIndexWith_eq_zero_of_mem_interior T hT hx

/-- **`E_x = E` at an interior point** of `C` (Definition 2.5.1: no vanishing half-line
coordinate). -/
theorem minimalSubspaceWith_eq_top_of_mem_interior
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (hT : C = T 0 ⁻¹' quadrant n W 0)
    {x : E 0} (hx : x ∈ interior C) : minimalSubspaceWith T x = ⊤ := by
  rw [eq_top_iff]
  intro v _
  rw [mem_minimalSubspaceWith]
  intro i hi
  exact absurd hi (fst_ne_zero_of_mem_interior T hT hx i)

/-- Conversely, a point of `C` with all half-line coordinates positive is interior. -/
theorem mem_interior_of_degIndexWith_eq_zero (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (hT : C = T 0 ⁻¹' quadrant n W 0) {x : E 0} (hxC : x ∈ C) (hd : degIndexWith T x = 0) :
    x ∈ interior C := by
  classical
  have hpos : ∀ i, 0 < (T 0 x).1 i := by
    intro i
    have hle : 0 ≤ (T 0 x).1 i := by rw [hT] at hxC; exact hxC i
    refine lt_of_le_of_ne hle fun h => ?_
    unfold degIndexWith quadrantDeg at hd
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hd
    exact hd (Finset.mem_univ i) h.symm
  rw [mem_interior]
  refine ⟨{y | ∀ i, 0 < (T 0 y).1 i}, fun y hy => ?_, ?_, hpos⟩
  · rw [hT]; exact fun i => le_of_lt (hy i)
  · have : {y : E 0 | ∀ i, 0 < (T 0 y).1 i} = ⋂ i, {y | 0 < (T 0 y).1 i} := by
      ext y
      exact (mem_iInter (x := y) (s := fun i => {y : E 0 | 0 < (T 0 y).1 i})).symm
    rw [this]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt continuous_const (((continuous_apply i).comp continuous_fst).comp (T 0).continuous)

/-- **For `x ∈ C`: `x ∈ int C ⟺ d_C(x) = 0`.** -/
theorem mem_interior_iff_degIndex_eq_zero (hC : IsPartialQuadrant E C) {x : E 0} (hxC : x ∈ C) :
    x ∈ interior C ↔ degIndex E C x = 0 := by
  obtain ⟨n, W, T, hT⟩ := hC
  refine ⟨fun h => degIndex_eq_zero_of_mem_interior ⟨n, W, T, hT⟩ h, fun h => ?_⟩
  rw [degIndex_eq T hT hxC] at h
  exact mem_interior_of_degIndexWith_eq_zero T hT hxC h

end Interior

/-! ### Shrinking a strong bundle chart to an open subset of the model -/

universe u v

namespace StrongBundleChart

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  (c : StrongBundleChart PX P) {W : Set (c.φ.model.E 0)} (hW : IsOpen W)
  (hmaps : MapsTo (StrongRetr.r c.R) (c.U ∩ W) W)

/-- The base domain `V ∩ φ⁻¹(W)` of the shrunk chart. -/
def shrinkSource (W : Set (c.φ.model.E 0)) : Set X := c.φ.source ∩ c.φ ⁻¹' W

lemma shrinkSource_subset : c.shrinkSource W ⊆ c.φ.source := inter_subset_left

include hW in
lemma isOpen_shrinkSource : IsOpen (c.shrinkSource W) :=
  c.φ.continuousOn_toFun.isOpen_inter_preimage c.φ.isOpen_source hW

/-- `φ(V ∩ φ⁻¹(W)) = O ∩ W`. -/
lemma image_shrinkSource : c.φ '' c.shrinkSource W = c.φ.model.O ∩ W := by
  ext z
  constructor
  · rintro ⟨x, ⟨hx, hxW⟩, rfl⟩
    exact ⟨c.φ.mapsTo_model x hx, hxW⟩
  · rintro ⟨hzO, hzW⟩
    refine ⟨c.φ.symm z, ⟨c.φ.symm_mapsTo hzO, ?_⟩, c.φ.apply_symm_apply hzO⟩
    show c.φ (c.φ.symm z) ∈ W
    rw [c.φ.apply_symm_apply hzO]; exact hzW

include hW hmaps in
/-- The strong bundle retraction `R` of the chart, restricted to `(U ∩ W) ◁ F` (`r(U ∩ W) ⊆ W`). -/
theorem isStrongBundleRetraction_inter : IsStrongBundleRetraction (c.U ∩ W) c.R where
  mapsTo p hp := by
    refine ⟨?_, mem_univ _⟩
    have h1 := c.isRetraction.apply_fst hp.1.1 p.2
    rw [Prod.mk.eta] at h1
    rw [h1]
    exact ⟨StrongRetr.r_mem c.isRetraction hp.1.1, hmaps hp.1⟩
  fst_independent u hu := c.isRetraction.fst_independent u hu.1
  fiber_linear u hu := c.isRetraction.fiber_linear u hu.1
  preserves_filtration m k hk u hu := c.isRetraction.preserves_filtration m k hk u hu.1
  isScSmooth_zero := c.isRetraction.isScSmooth_zero.of_subset
    ((c.relOpen.inter_isOpen hW).prod_univ c.F).isScDomain
    (prod_mono inter_subset_left subset_rfl)
  isScSmooth_one := c.isRetraction.isScSmooth_one.of_subset
    ((c.relOpen.inter_isOpen hW).prod_univ c.F.shift).isScDomain
    (prod_mono inter_subset_left subset_rfl)
  idem p hp := c.isRetraction.idem p ⟨hp.1.1, mem_univ _⟩

/-- The retract of `r|U ∩ W` is `O ∩ W`. -/
lemma retract_inter :
    ((c.isStrongBundleRetraction_inter hW hmaps).baseRetraction
      (c.relOpen.inter_isOpen hW)).retract = c.φ.model.O ∩ W := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨c.r_mem_O hu.1, hmaps hu⟩
  · rintro ⟨hzO, hzW⟩
    have hzU : z ∈ c.U := StrongRetr.mem_U_of_mem_O c.isRetraction (c.r_image ▸ hzO)
    exact ⟨z, ⟨hzU, hzW⟩, StrongRetr.r_eq_self c.isRetraction (c.r_image ▸ hzO)⟩

/-- **The strong bundle chart shrunk to `(U ∩ W) ◁ F`**, for `W ⊆ E₀` open with `r(U ∩ W) ⊆ W`:
the base chart `φ|V ∩ φ⁻¹(W)` onto `O ∩ W`, the same strong bundle retraction `R` on the smaller
domain `U ∩ W`, and the same `Φ` on `P⁻¹(V ∩ φ⁻¹(W))`.  Unlike `StrongBundleChart.restrict`
(whose domain is `U ∩ r⁻¹(W)`), the domain `U ∩ W` lies in `W`. -/
def shrink : StrongBundleChart PX P where
  φ := c.φ.restrict (c.shrinkSource_subset (W := W)) (c.isOpen_shrinkSource hW)
  isChart := MPolyfold.IsChart.restrict PX c.isChart _ _
  F := c.F
  U := c.U ∩ W
  R := c.R
  relOpen := c.relOpen.inter_isOpen hW
  isRetraction := c.isStrongBundleRetraction_inter hW hmaps
  base_retract := (c.retract_inter hW hmaps).trans (c.image_shrinkSource (W := W)).symm
  toPartialEquiv := c.restrictPE (c.shrinkSource_subset (W := W)) (c.isOpen_shrinkSource hW)
  source_eq := rfl
  target_eq := by
    show c.R '' ((c.restrictBase (c.shrinkSource_subset (W := W))
      (c.isOpen_shrinkSource hW)).U ×ˢ univ) = c.R '' ((c.U ∩ W) ×ˢ univ)
    ext p
    rw [c.mem_restrict_K_iff, c.image_shrinkSource]
    constructor
    · rintro ⟨hK, hO, hpW⟩
      have hpU : p.1 ∈ c.U := StrongRetr.mem_U_of_mem_O c.isRetraction (c.r_image ▸ hO)
      exact ⟨p, ⟨⟨hpU, hpW⟩, mem_univ _⟩, c.R_eq_self_of_mem_K hK⟩
    · rintro ⟨q, hq, rfl⟩
      refine ⟨⟨q, ⟨hq.1.1, mem_univ _⟩, rfl⟩, ?_⟩
      have h1 := c.isRetraction.apply_fst hq.1.1 q.2
      rw [Prod.mk.eta] at h1
      rw [h1]
      exact ⟨c.r_mem_O hq.1.1, hmaps hq.1⟩
  continuousOn_toFun := c.continuousOn_toFun.mono fun y hy =>
    c.mem_source_of_mem_base (c.shrinkSource_subset hy)
  continuousOn_invFun := c.continuousOn_invFun.mono fun p hp => by
    rw [c.target_eq]; exact ((c.mem_restrict_K_iff _ _).1 hp).1
  covers y hy := c.covers y (c.mem_source_of_mem_base (c.shrinkSource_subset hy))
  fiber_linear x hx := c.fiber_linear x (c.shrinkSource_subset hx)

@[simp] lemma shrink_U : (c.shrink hW hmaps).U = c.U ∩ W := rfl

@[simp] lemma shrink_R : (c.shrink hW hmaps).R = c.R := rfl

@[simp] lemma shrink_F : (c.shrink hW hmaps).F = c.F := rfl

lemma shrink_φ_source : (c.shrink hW hmaps).φ.source = c.φ.source ∩ c.φ ⁻¹' W := rfl

lemma shrink_φ_apply (x : X) : (c.shrink hW hmaps).φ x = c.φ x := rfl

lemma shrink_apply (y : Y) : c.shrink hW hmaps y = c y := rfl

/-- The principal part of a section in the shrunk chart is that in the chart. -/
lemma shrink_principal (f : X → Y) : (c.shrink hW hmaps).principal f = c.principal f := rfl

variable {c} in
/-- Compatibility passes to the shrunk chart: its base chart, fibre model and `Φ` are those of
`c.restrict` to `V ∩ φ⁻¹(W)`, and compatibility (Definition 2.6.4) involves only these. -/
theorem Compatible.shrink_left {c' : StrongBundleChart PX P} (h : c.Compatible c') :
    (c.shrink hW hmaps).Compatible c' :=
  h.restrict_left (c.shrinkSource_subset (W := W)) (c.isOpen_shrinkSource hW)

/-- **A chart whose domain lies in the interior of its quadrant is tame** (Definition 2.5.2): on
`U ∩ W ⊆ int C` the degeneracy index is `0` (condition (1)), and at a smooth `x ∈ O`,
`E = T_xO ⊕ (1 − Dr(x))E` is an sc-splitting with `(1 − Dr(x))E ⊆ E_x = E` (condition (2)). -/
theorem isTame_shrink_of_subset_interior (hWint : W ⊆ interior c.φ.model.C) :
    ((c.shrink hW hmaps).isRetraction.baseRetraction (c.shrink hW hmaps).relOpen).IsTame := by
  intro n W' T hT
  set R' := (c.shrink hW hmaps).isRetraction.baseRetraction (c.shrink hW hmaps).relOpen with hR'
  have hC : IsPartialQuadrant c.φ.model.E c.φ.model.C := c.relOpen.isPartialQuadrant
  refine ⟨fun x hx => ?_, fun x hx hs => ?_⟩
  · have hx' : x ∈ c.U ∩ W := hx
    have h1 : degIndex c.φ.model.E c.φ.model.C (R' x) = 0 :=
      degIndex_eq_zero_of_mem_interior hC (hWint (hmaps hx'))
    have h2 : degIndex c.φ.model.E c.φ.model.C x = 0 :=
      degIndex_eq_zero_of_mem_interior hC (hWint hx'.2)
    show degIndex c.φ.model.E c.φ.model.C (R' x) = degIndex c.φ.model.E c.φ.model.C x
    exact h1.trans h2.symm
  · refine ⟨_, R'.isScSplitting_range_scDeriv hx hs, ?_⟩
    rw [minimalSubspaceWith_eq_top_of_mem_interior T hT ?_]
    · exact le_top
    · have := R'.lvlSet_retract_subset 1 hx
      rw [ScBanach.mem_lvlSet] at this
      exact hWint this.2

end StrongBundleChart

namespace StrongBundle

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- The shrunk chart of a chart of `P` is a chart of `P`. -/
theorem IsChart.shrink {c : StrongBundleChart PX P} (hc : B.IsChart c) {W : Set (c.φ.model.E 0)}
    (hW : IsOpen W) (hmaps : MapsTo (StrongRetr.r c.R) (c.U ∩ W) W) :
    B.IsChart (c.shrink hW hmaps) :=
  fun c' hc' => (hc c' hc').shrink_left hW hmaps

/-! ### Germ data in a chart centred at an interior point are tame germ data -/

open StrongRetr

/-- **Germ data in a chart centred at an interior point of its quadrant give tame germ data**
(Definition 3.1.11 ⟹ the hypothesis of Theorem 3.6.8).  If the compatible chart `c` of the germ
data has `φ(x₀) = 0 ∈ int C`, the chart shrunk to `W = (U ∩ int C) ∩ r⁻¹(int C)` is compatible,
centred at `x₀`, tame (`isTame_shrink_of_subset_interior`), and carries the restricted germ data
(`IsFillingGerm.of_subset`, `IsScPlusGerm.of_subset`, `IsConjugateToBasicGerm.of_subset`). -/
theorem isScFredholmGermTame_of_chart_interior {c : StrongBundleChart PX P} (hc : B.IsChart c)
    {x₀ : X} (hxs : x₀ ∈ PX.smoothSet) (hxV : x₀ ∈ c.φ.source) (hφ0 : c.φ x₀ = 0)
    (h0 : (0 : c.φ.model.E 0) ∈ c.U) {g : c.φ.model.E 0 → c.F 0} {s : c.φ.model.E 0 → c.F 1}
    (hfill : IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g)
    (hs : IsScPlusGerm c.φ.model.C c.U s) (hs0 : c.F.toBase 1 (s 0) = g 0)
    (hconj : IsConjugateToBasicGerm c.U (fun u => g u - c.F.toBase 1 (s u)))
    (hint : (0 : c.φ.model.E 0) ∈ interior c.φ.model.C) :
    B.IsScFredholmGermTame f x₀ := by
  -- the open set `W = (U ∩ int C) ∩ r⁻¹(int C)`
  have hUint : IsOpen (c.U ∩ interior c.φ.model.C) := by
    obtain ⟨OU, hOU, hUeq⟩ := c.relOpen.relOpen
    have : c.U ∩ interior c.φ.model.C = OU ∩ interior c.φ.model.C := by
      rw [hUeq]
      ext z
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, interior_subset h.2⟩, h.2⟩⟩
    rw [this]; exact hOU.inter isOpen_interior
  have hrcont : ContinuousOn (r c.R) (c.U ∩ interior c.φ.model.C) :=
    (c.isRetraction.baseRetraction c.relOpen).isSc1.isSc0.continuousOn_base.mono
      inter_subset_left
  set W : Set (c.φ.model.E 0) :=
    (c.U ∩ interior c.φ.model.C) ∩ r c.R ⁻¹' interior c.φ.model.C with hWdef
  have hW : IsOpen W := hrcont.isOpen_inter_preimage hUint isOpen_interior
  have hWint : W ⊆ interior c.φ.model.C := fun y hy => hy.1.2
  have hmaps : MapsTo (r c.R) (c.U ∩ W) W := by
    intro y hy
    have hyU : y ∈ c.U := hy.1
    have hrint : r c.R y ∈ interior c.φ.model.C := hy.2.2
    refine ⟨⟨r_mem c.isRetraction hyU, hrint⟩, ?_⟩
    show r c.R (r c.R y) ∈ interior c.φ.model.C
    rw [r_r c.isRetraction hyU]; exact hrint
  have h0O : (0 : c.φ.model.E 0) ∈ r c.R '' c.U := zero_mem_O_of_chart hxV hφ0
  have h0W : (0 : c.φ.model.E 0) ∈ W := by
    refine ⟨⟨h0, hint⟩, ?_⟩
    show r c.R 0 ∈ interior c.φ.model.C
    rw [r_eq_self c.isRetraction h0O]; exact hint
  -- the shrunk chart
  have h0' : (0 : (c.shrink hW hmaps).φ.model.E 0) ∈ (c.shrink hW hmaps).U := ⟨h0, h0W⟩
  have hsub : (c.shrink hW hmaps).U ⊆ c.U := inter_subset_left
  refine ⟨hxs, c.shrink hW hmaps,
    ⟨hc.shrink hW hmaps, c.isTame_shrink_of_subset_interior hW hmaps hWint⟩, ⟨hxV, ?_⟩, hφ0, h0',
    g, s, ?_, ?_, hs0, ?_⟩
  · show c.φ x₀ ∈ W
    rw [hφ0]; exact h0W
  · exact hfill.of_subset c.relOpen c.isRetraction (c.shrink hW hmaps).relOpen
      (c.shrink hW hmaps).isRetraction hsub h0 h0'
  · exact hs.of_subset c.relOpen (c.shrink hW hmaps).relOpen h0'
  · exact hconj.of_subset c.relOpen h0 (c.shrink hW hmaps).relOpen hsub h0'

variable (B) in
/-- **The 2021 sc-Fredholm germ data in a chart centred at an interior point of its quadrant**:
the data of `IsScFredholmGerm2021` (Definitions 3.1.11 = 3.6.3 with the 2021 filling) in a
compatible chart `c` with `φ(x₀) = 0 ∈ int C`, i.e. `d_C(φ(x₀)) = 0`
(`mem_interior_iff_chartDegIndex_eq_zero`). -/
def IsScFredholmGermInterior (f : X → Y) (x₀ : X) : Prop :=
  x₀ ∈ PX.smoothSet ∧
  ∃ (c : StrongBundleChart PX P) (_ : B.IsChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
    (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0) (s : c.φ.model.E 0 → c.F 1),
    IsFilling2021 c.relOpen c.isRetraction h0 (c.principal f) g ∧
    IsScPlusGerm c.φ.model.C c.U s ∧ c.F.toBase 1 (s 0) = g 0 ∧
    IsConjugateToBasicGerm c.U (fun u => g u - c.F.toBase 1 (s u)) ∧
    (0 : c.φ.model.E 0) ∈ interior c.φ.model.C

omit [T2Space Y] [ParacompactSpace Y] in
/-- The condition `φ(x₀) ∈ int C` on a chart is `d(x₀, φ) = d_C(φ(x₀)) = 0`. -/
theorem mem_interior_iff_chartDegIndex_eq_zero (c : StrongBundleChart PX P) {x₀ : X}
    (hxV : x₀ ∈ c.φ.source) :
    c.φ x₀ ∈ interior c.φ.model.C ↔ MPolyfold.chartDegIndex c.φ x₀ = 0 :=
  mem_interior_iff_degIndex_eq_zero c.relOpen.isPartialQuadrant (c.φ.apply_mem_C hxV)

/-- Interior germ data are 2021 germ data. -/
theorem IsScFredholmGermInterior.isScFredholmGerm2021 {x₀ : X}
    (h : B.IsScFredholmGermInterior f x₀) : B.IsScFredholmGerm2021 f x₀ := by
  obtain ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj, -⟩ := h
  exact ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj⟩

/-- **Interior germ data are tame germ data** (Definition 3.6.3, 2021 ⟹ its preprint/2017 form,
the hypothesis of the §3.6 theorems). -/
theorem IsScFredholmGermInterior.isScFredholmGermTame {x₀ : X}
    (h : B.IsScFredholmGermInterior f x₀) : B.IsScFredholmGermTame f x₀ := by
  obtain ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj, hint⟩ := h
  exact isScFredholmGermTame_of_chart_interior hc hs hxV hφ0 h0 hfill.isFillingGerm hsm hs0 hconj
    hint

/-- Interior germ data are 2017 germ data (2017 Definitions 3.7, 3.14 with a tame filling). -/
theorem IsScFredholmGermInterior.isScFredholmGerm2017 {x₀ : X}
    (h : B.IsScFredholmGermInterior f x₀) : B.IsScFredholmGerm2017 f x₀ :=
  isScFredholmGerm2017_iff.2 h.isScFredholmGermTame

/-- A point carrying interior germ data is an interior point of `X`: `d_X(x₀) ≤ d_C(φ(x₀)) = 0`
(Definition 2.4.1).  The converse fails: the corner example of `Book2021Germs.lean` has `d_X = 0`
and `d_C(0) = 1`. -/
theorem IsScFredholmGermInterior.degIndex_eq_zero {x₀ : X}
    (h : B.IsScFredholmGermInterior f x₀) : PX.degIndex x₀ = 0 := by
  obtain ⟨-, c, -, hxV, hφ0, -, -, -, -, -, -, -, hint⟩ := h
  have h1 : MPolyfold.chartDegIndex c.φ x₀ = 0 := by
    rw [← mem_interior_iff_chartDegIndex_eq_zero c hxV, hφ0]; exact hint
  exact Nat.eq_zero_of_le_zero ((PX.degIndex_le c.isChart hxV).trans_eq h1)

/-- **A 2021 sc-Fredholm section whose germ data are in interior charts has tame germ data**
(Definition 3.6.4, 2021 ⟹ `IsScFredholmSectionTame`, the hypothesis under which Theorems 3.1.22,
3.1.26, 3.6.8, 3.6.10, 3.6.11 and Chapter 5 are verified). -/
theorem isScFredholmSectionTame_of_interior (hf : B.IsScFredholmSection2021 f)
    (h : ∀ x ∈ PX.smoothSet, B.IsScFredholmGermInterior f x) : B.IsScFredholmSectionTame f :=
  { isScFredholmSection2021_iff.1 hf with
    germTame := fun x hx => (h x hx).isScFredholmGermTame }

/-- **Tame germ data realise the degeneracy index**: the tame chart of `IsScFredholmGermTame` has
`d_C(0) = d_X(x₀)` (Proposition 2.5.6, `degIndex_eq_chartDegIndex_of_isTameRetract`).  Germ data
of Definition 3.1.11 in a chart with `d_C(0) = 0` are tame germ data
(`isScFredholmGermTame_of_chart_interior`); the open case of G.79 is germ data in a chart with
`d_C(0) ≥ 1`. -/
theorem IsScFredholmGermTame.exists_chart_chartDegIndex_eq {x₀ : X}
    (h : B.IsScFredholmGermTame f x₀) :
    ∃ c : StrongBundleChart PX P, B.IsTameChart c ∧ x₀ ∈ c.φ.source ∧ c.φ x₀ = 0 ∧
      MPolyfold.chartDegIndex c.φ x₀ = PX.degIndex x₀ := by
  obtain ⟨-, c, hc, hxV, hφ0, -⟩ := h
  exact ⟨c, hc, hxV, hφ0, (PX.degIndex_eq_chartDegIndex_of_isTameRetract c.isChart
    ⟨_, c.base_retract, hc.2⟩ hxV).symm⟩

end StrongBundle

/-! ### Witnesses -/

namespace TrivialBundle

open scoped ContDiff

variable {n k : ℕ} {φ : (Fin n → ℝ) → (Fin k → ℝ)}

/-- **The hypothesis of `IsScFredholmGermInterior` is satisfiable**: the graph section of a `C^∞`
map in the trivial bundle `ℝⁿ × ℝᵏ → ℝⁿ`, in the translation chart `chart x₀` (model `C = ℝⁿ`,
identity retraction; the germ data of `germData_graphSection`). -/
theorem isScFredholmGermInterior_graphSection (hφ : ContDiff ℝ ∞ φ) (x₀ : Fin n → ℝ) :
    (bundle n k).IsScFredholmGermInterior (graphSection φ) x₀ := by
  obtain ⟨hfill, hs, hs0, hconj⟩ := germData_graphSection (k := k) hφ x₀
  have hc := isChart_chart (k := k) x₀
  refine ⟨by rw [rnPolyfold_smoothSet]; exact mem_univ x₀, chart x₀, hc, mem_univ x₀, sub_self x₀,
    mem_univ 0, loc φ x₀, fun _ => φ x₀,
    hfill.isFilling2021 (StrongBundle.zero_mem_O_of_chart (mem_univ x₀) (sub_self x₀)),
    ⟨ScNbhdGerm.ofSet (chart (k := k) x₀).relOpen.relOpen (mem_univ 0), fun _ hu => hu,
      hs.isScSmoothGerm (chart (k := k) x₀).isQuadrantLike (chart (k := k) x₀).relOpen.relOpen
        (mem_univ 0)⟩,
    hs0, hconj, ?_⟩
  show (0 : (rnSc n) 0) ∈ interior (univ : Set ((rnSc n) 0))
  rw [interior_univ]; exact mem_univ _

end TrivialBundle

namespace CornerFilling

/-- **The corner example is not covered**: its chart is centred at `0 ∈ ∂H`, `H = [0, ∞) × ℝ`
(`d_H(0) = 1`): the points `(−t, 0)`, `t > 0`, lie outside `H` and converge to `0`.  Whether its
untamed germ data (`isFilling2021_gc`) can be moved to a tame chart is the open case of G.79. -/
theorem zero_not_mem_interior : (0 : Ec 0) ∉ interior Hc := by
  intro h
  have hev : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
      (((fun _ => -t : Fin 1 → ℝ), (0 : Fin 1 → ℝ)) : Ec 0) ∈ Hc := by
    have hcont : Tendsto (fun t : ℝ => (((fun _ => -t : Fin 1 → ℝ), (0 : Fin 1 → ℝ)) : Ec 0))
        (𝓝 0) (𝓝 0) := by
      have : Tendsto (fun t : ℝ => (((fun _ => -t : Fin 1 → ℝ), (0 : Fin 1 → ℝ)) : Ec 0))
          (𝓝 0) (𝓝 (((fun _ => -(0 : ℝ) : Fin 1 → ℝ), (0 : Fin 1 → ℝ)) : Ec 0)) := by
        refine Tendsto.prodMk_nhds ?_ tendsto_const_nhds
        exact tendsto_pi_nhds.2 fun _ => tendsto_id.neg
      have h0 : (((fun _ => -(0 : ℝ) : Fin 1 → ℝ), (0 : Fin 1 → ℝ)) : Ec 0) = 0 :=
        Prod.ext (funext fun _ => neg_zero) rfl
      rwa [h0] at this
    exact hcont (mem_interior_iff_mem_nhds.1 h)
  obtain ⟨t, htH, ht⟩ :=
    ((hev.filter_mono (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))).and self_mem_nhdsWithin).exists
  have := htH 0
  change (0 : ℝ) ≤ -t at this
  exact absurd ht (not_lt.2 (by linarith))

end CornerFilling

end Polyfold
