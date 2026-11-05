import Polyfold.Chapter3.GoodPositionSc
import Polyfold.Chapter3.GlobalIFTNearbyOntoG

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.1 and §3.6:
**Definition 3.53 with the text's sc-complement** (Definition 3.21 as written) and **Theorems 3.54
(1), 3.23, 3.56, 3.57 and Corollary 3.24 with the text's notion of good position**, **in the
text's germ reading of Definition 3.11** (phase 2; the germ forms of `GoodPositionSc.lean`).

# Good position with an sc-complement, germ reading

## The text, paraphrased

(Definition 3.21) A finite-dimensional sc-subspace `N` is in good position to a partial quadrant
`C` if the interior of `N ∩ C` in `N` is nonempty and `N` has an sc-complement `P` with an `ε > 0`
such that `n ∈ C ⟺ n + p ∈ C` for `|p|₀ ≤ ε|n|₀`.  (Definition 3.53) An sc-Fredholm germ `(f, x)`
with `f(x) = 0` is in good position if `f'(x)` is onto and `ker f'(x)` is in good position to the
partial cone `C_xX`.  (Theorem 3.54 (1)) At every zero `y` near `x` the germ `(f, y)` is in good
position.  The germs of Definition 3.11 are those of Definitions 3.1–3.2: the filling and the
sc⁺-section are germs whose levels may shrink.

## What is formalized

* `Polyfold.IsGoodPositionAtScGerm hU hR h0 Dg₀`: **Definition 3.53 in the chart with the
  sc-complement, parametrised by the linearization `Dg₀ : E₀ → F₀`** (the value at `0` of a
  derivative family of the filling germ) in place of `scDeriv U g 0`; `isGoodPositionAtSc_iff_germ`
  (the project's `IsGoodPositionAtSc` is the case `Dg₀ = scDeriv U g 0`),
  `IsGoodPositionAtScGerm.isGoodPositionAtGerm` (forgetful), `IsGoodPositionAtScGerm.congr`,
  `IsGoodPositionAtScGerm.of_isSc1GermWith` (independence of the derivative family).
* `Polyfold.StrongBundle.IsGoodPositionGermSc f x₀`: **Definition 3.53 with the sc-complement for
  a section in a tame chart, germ reading** (the data of `IsGoodPositionGermTame` with
  `IsGoodPositionAtScGerm` at `Dg(0)`); the forgetful
  `IsGoodPositionGermSc.isGoodPositionGermTame` and the bridge
  `IsGoodPositionGermScWholeChart.isGoodPositionGermSc` (project ⇒ germ reading).
* `Polyfold.StrongBundle.IsGoodPositionGermTame.isGoodPositionGermSc`: **at a zero of an
  sc-Fredholm section with tame germ data (germ reading), good position with an algebraic
  complement gives good position with an sc-complement**, in the same tame chart;
  `isGoodPositionGermSc_iff`.
* `Polyfold.theorem_3_54_one_sc_of_tame`, `theorem_3_54_one_sc`, `theorem_3_54_sc`,
  `theorem_3_23_sc`: **Theorem 3.54 (1)** (and (2), and Theorem 3.23) **with the text's
  notion, germ reading**: every zero near `x₀` is in good position with an sc-complement.
  `forall_isGoodPositionGermSc_iff`, `theorem_3_57_sc`, `corollary_3_24_sc`,
  `theorem_3_56_sc`: the global theorems with the hypothesis "every zero is in good position"
  in the text's sense, germ reading.

## What the text leaves implicit, and the choices made (the findings)

* **The kernel at a zero is smooth, germ reading.**  The proof of `GoodPositionSc.lean` carries
  over: in the tame chart centred at the zero `y` given by the germ form of the nearby-kernel
  theorem applied at `y` itself (`theorem_3_54_nearby_kernel`, so the level-`1` points are
  `z₀₁ = 0` and `x₁ = 0`), `ker Dg(0) = Dψ'(0)(ker D(h + t)(0))` for the derivative family `Dg`
  of the filling germ on its germ `G_g`; the strong bundle isomorphism `Ψ'` is sc-smooth on the
  whole `U'` (it is not a germ in the germ reading), so `Dψ'(0)` maps smooth vectors to smooth
  vectors (`IsSc1.scDeriv_mem_smooth`) exactly as before.  Nothing else changes; the upgrade lemma
  `IsInGoodPosition.isInGoodPositionScIn` is chart-free.
* **`Dg(0)` is a parameter**, as in `IsGoodPositionAtGerm` (`GoodPositionGermG.lean`): the
  section-level notion asks for some derivative family on some germ `G ⊆ U`, and `Dg(0)` does not
  depend on the choice (`IsGoodPositionAtScGerm.of_isSc1GermWith`).
-/

open Set Filter Topology Function Module ContinuousLinearMap

noncomputable section

namespace Polyfold

/-! ### Definition 3.53 in the chart with the sc-complement, germ reading -/

section Def353ScGerm

variable {E F : ScBanach} {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

open StrongRetr

/-- **Definition 3.53 in the chart with the text's sc-complement, germ reading** (phase 2): for
the linearization `Dg₀ = Dg(0) : E₀ → F₀` of the filling germ `g` at the zero `0` (the value at
`0` of a derivative family of `g`, `IsSc1GermWith`), (1) `Tf̃(0) = Dg₀|_{T₀O} : T₀O → K₀` is onto,
and (2) `ker Dg₀` is in good position to the partial cone `C₀O = T₀O ∩ C` inside `T₀O = Dr(0)E`
with an **sc-complement** (`IsInGoodPositionScIn`, Definition 3.21 as written).  The project's
`IsGoodPositionAtSc hU hR h0 g` is the case `Dg₀ = scDeriv U g 0`
(`isGoodPositionAtSc_iff_germ`). -/
structure IsGoodPositionAtScGerm (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U) (Dg₀ : E 0 →L[ℝ] F 0) : Prop where
  surj : ∀ y ∈ rangeS (ρCLM hR h0), ∃ x ∈ rangeS (scDeriv U (r R) 0), Dg₀ x = y
  kernel : IsInGoodPositionScIn E (rangeS (scDeriv U (r R) 0)) C
    (LinearMap.ker (Dg₀ : E 0 →ₗ[ℝ] F 0))

/-- **The project's Definition 3.53 with the sc-complement, in the chart, is the germ one at
`Dg₀ = scDeriv U g 0`** (germ reading, phase 2). -/
theorem isGoodPositionAtSc_iff_germ {hU : IsRelOpenInQuadrant E C U}
    {hR : IsStrongBundleRetraction U R} {h0 : (0 : E 0) ∈ U} {g : E 0 → F 0} :
    IsGoodPositionAtSc hU hR h0 g ↔ IsGoodPositionAtScGerm hU hR h0 (scDeriv U g 0) :=
  ⟨fun h => ⟨h.surj, h.kernel⟩, fun h => ⟨h.surj, h.kernel⟩⟩

/-- Good position in the chart with an sc-complement is good position in the chart with an
algebraic complement (Definition 3.53 with Definition 3.21 as written ⟹ the project's form; germ
reading, phase 2). -/
theorem IsGoodPositionAtScGerm.isGoodPositionAtGerm {hU : IsRelOpenInQuadrant E C U}
    {hR : IsStrongBundleRetraction U R} {h0 : (0 : E 0) ∈ U} {Dg₀ : E 0 →L[ℝ] F 0}
    (h : IsGoodPositionAtScGerm hU hR h0 Dg₀) : IsGoodPositionAtGerm hU hR h0 Dg₀ :=
  ⟨h.surj, h.kernel.toIsInGoodPositionIn⟩

/-- `IsGoodPositionAtScGerm` depends only on the operator (Definition 3.53, germ reading; a
congruence for rewriting `Dg(0)`). -/
theorem IsGoodPositionAtScGerm.congr {hU : IsRelOpenInQuadrant E C U}
    {hR : IsStrongBundleRetraction U R} {h0 : (0 : E 0) ∈ U} {D D' : E 0 →L[ℝ] F 0}
    (h : IsGoodPositionAtScGerm hU hR h0 D) (hDD' : D = D') :
    IsGoodPositionAtScGerm hU hR h0 D' :=
  hDD' ▸ h

/-- **Definition 3.53 with the sc-complement does not depend on the derivative family** (germ
reading, phase 2): good position at `Dg(0)` for one derivative family `Dg` of `g` on a germ `G`
gives it at `Dg'(0)` for every derivative family `Dg'` of `g` on every germ `G'`
(`IsSc1GermWith.deriv_zero_eq`). -/
theorem IsGoodPositionAtScGerm.of_isSc1GermWith {hU : IsRelOpenInQuadrant E C U}
    {hR : IsStrongBundleRetraction U R} {h0 : (0 : E 0) ∈ U} (hC : IsQuadrantLike E C)
    {g : E 0 → F 0} {G G' : ScNbhdGerm E C} {Dg Dg' : E 1 → E 0 →L[ℝ] F 0}
    (hgp : IsGoodPositionAtScGerm hU hR h0 (Dg 0)) (hDg : IsSc1GermWith G g Dg)
    (hDg' : IsSc1GermWith G' g Dg') : IsGoodPositionAtScGerm hU hR h0 (Dg' 0) :=
  hgp.congr (hDg.deriv_zero_eq hC hDg')

end Def353ScGerm

section Bundle

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

open StrongRetr

namespace StrongBundle

variable (B) in
/-- **Definition 3.53 with the text's sc-complement, in a tame chart, germ reading** (phase 2):
`(f, x₀)` is an sc-Fredholm germ in good position in the sense of the text: the data of
`IsGoodPositionGermTame` (a tame strong bundle chart centred at `x₀`, a filling germ `g` of `f̂`,
an sc⁺-germ `s` with `s(0) = g(0)`, `g − s` conjugated to a basic germ, a derivative family `Dg`
of `g` on a germ `G ⊆ U`) with `Tf̃(0)` onto `K₀` and `ker Dg(0)` in good position to `C₀O` inside
`T₀O` with an **sc-complement** (`IsGoodPositionAtScGerm`).  The germ form of
`IsGoodPositionGermScWholeChart` (`IsGoodPositionGermScWholeChart.isGoodPositionGermSc`). -/
def IsGoodPositionGermSc (f : X → Y) (x₀ : X) : Prop :=
  x₀ ∈ PX.smoothSet ∧
  ∃ (c : StrongBundleChart PX P) (_ : B.IsTameChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
    (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0) (s : c.φ.model.E 0 → c.F 1),
    IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g ∧
    IsScPlusGerm c.φ.model.C c.U s ∧ c.F.toBase 1 (s 0) = g 0 ∧
    IsConjugateToBasicGerm c.U (fun u => g u - c.F.toBase 1 (s u)) ∧
    ∃ (G : ScNbhdGerm c.φ.model.E c.φ.model.C) (Dg : c.φ.model.E 1 → c.φ.model.E 0 →L[ℝ] c.F 0),
      G.U 0 ⊆ c.U ∧ IsSc1GermWith G g Dg ∧
      IsGoodPositionAtScGerm c.relOpen c.isRetraction h0 (Dg 0)

/-- Good position with an sc-complement is good position with an algebraic complement
(`IsGoodPositionGermTame`), in the same tame chart (Definition 3.53, germ reading, phase 2; the
germ form of `IsGoodPositionGermScWholeChart.isGoodPositionGermTame`). -/
theorem IsGoodPositionGermSc.isGoodPositionGermTame {x : X} (h : B.IsGoodPositionGermSc f x) :
    B.IsGoodPositionGermTame f x := by
  obtain ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj, G, Dg, hG, hDg, hgp⟩ := h
  exact ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj, G, Dg, hG, hDg,
    hgp.isGoodPositionAtGerm⟩

/-- **Project ⇒ germ reading** for Definition 3.53 with the sc-complement (phase 2): the data of
`IsGoodPositionGermScWholeChart` (`g`, `s` sc-smooth on the whole `U`) are germ data, with the germ `ofSet U`
and `Dg = scDeriv U g`. -/
theorem IsGoodPositionGermScWholeChart.isGoodPositionGermSc {x : X} (h : B.IsGoodPositionGermScWholeChart f x) :
    B.IsGoodPositionGermSc f x := by
  obtain ⟨hx, c, hc, hxV, hφ0, h0, g, s, hfill, hs, hs0, hconj, hgp⟩ := h
  exact ⟨hx, c, hc, hxV, hφ0, h0, g, s, hfill.isFillingGerm c.relOpen c.isRetraction h0,
    ⟨ScNbhdGerm.ofSet c.relOpen.relOpen h0, fun _ hu => hu,
      hs.isScSmoothGerm c.isQuadrantLike c.relOpen.relOpen h0⟩, hs0, hconj,
    ScNbhdGerm.ofSet c.relOpen.relOpen h0, scDeriv c.U g, fun _ hu => hu,
    hfill.isScSmooth.isSc1.isSc1GermWith_ofSet c.relOpen.relOpen h0,
    isGoodPositionAtSc_iff_germ.1 hgp⟩

set_option maxHeartbeats 1600000 in
-- the destructuring of `theorem_3_54_nearby_kernel` is large
/-- **At a zero, good position (algebraic complement) gives good position with the text's
sc-complement, germ reading** (phase 2; the germ form of
`IsGoodPositionGermTameWholeChart.isGoodPositionGermSc`, round-trip items V3.82, V3.85).  Let `f` be an
sc-Fredholm section with tame germ data in the germ reading and `(f, y)`, `f(y) = 0`, in good
position in a tame chart (`IsGoodPositionGermTame`).  In the tame chart centred at `y` of
`theorem_3_54_nearby_kernel` (applied at `y` itself, so `z₀₁ = 0`, `x₁ = 0`):
`ker Dg(0) = Dψ'(0)(ker D(h + t)(0))` for the derivative family `Dg` of the filling germ is
finite-dimensional and smooth (`Dψ'(0)` preserves smooth vectors, `IsSc1.scDeriv_mem_smooth`, `Ψ'`
being sc-smooth on the whole `U'`); `T₀O = Dr(0)E` is an sc-subspace and `(1 − Dr(0))E ⊆ E₀`
(Proposition 2.35, tame retraction); so `ker Dg(0)` is in good position to `C` in `E` and
`IsInGoodPosition.isInGoodPositionScIn` gives the sc-complement inside `T₀O`. -/
theorem IsGoodPositionGermTame.isGoodPositionGermSc (hf : B.IsScFredholmSectionTame f) {y : X}
    (hg : B.IsGoodPositionGermTame f y) (hy : IsZeroAt P f y) : B.IsGoodPositionGermSc f y := by
  classical
  obtain ⟨c, hc, hyV, h0, h0U, g, t₀, Gg, Dg, Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, hCt, U', hU',
    Ψ, Ψ', hΨ, hψ0, 𝒮, h', Bc, hh'𝒮, hsurj, hpos, Yc, V', σ, Vx, n', Wq, T, Vx₂, hfill, ht₀, ht₀0,
    hconj, hGg, hgsm, hDg, hgp, hYc, hYcc, hKsm, hV'rel, h0V', hσY, hσ1, hσC, hσ0, hDσ, hsol,
    hlift, hVxo, hyVx, hVxsub, hinj, hzero, himage, hT, hVx₂o, hyVx₂, hVx₂Vx, hker⟩ :=
    theorem_3_54_nearby_kernel hf.isScSmooth.1 hg hy
  obtain ⟨-, -, v, hv, z₀₁, x₁, hz₀₁, -, -, hx₁, -, -, hψφ, hfred, -, -, -, -, hkerEq, -, -, -⟩ :=
    hker y hyVx₂ hy
  have h0O : (0 : c.φ.model.E 0) ∈ r c.R '' c.U := by
    rw [c.r_image, ← h0]; exact c.φ.mapsTo_model y hyV
  -- the level-`1` points are `0`
  have hz0 : z₀₁ = 0 := c.φ.model.E.toBase_injective 1 (by rw [hz₀₁, h0, map_zero])
  have hx0 : x₁ = 0 := by
    apply (ScBanach.paramProd Pn W).toBase_injective 1
    rw [hx₁, ← hψφ, h0, hψ0, map_zero]
  subst hz0 hx0
  -- the kernel `N = ker Dg(0)`: finite-dimensional and smooth
  have hfinK := hfred.finite_ker
  have hNfin : FiniteDimensional ℝ (LinearMap.ker (Dg 0 : c.φ.model.E 0 →ₗ[ℝ] c.F 0)) := by
    rw [hkerEq]; infer_instance
  have h0U' : (0 : (ScBanach.paramProd Pn W) 0) ∈ U' := by
    have := (hΨ.toFun.mapsTo (show ((0 : c.φ.model.E 0), (0 : c.F 0)) ∈ c.U ×ˢ univ from
      ⟨h0U, mem_univ _⟩)).1
    rwa [show (Ψ (0, 0)).1 = IsStrongBundleMap.base Ψ 0 from rfl, hψ0] at this
  have hψ'1 : IsSc1 U' (IsStrongBundleMap.base Ψ') := (hΨ.invFun.base_isScSmooth hU').isSc1
  have hNs : LinearMap.ker (Dg 0 : c.φ.model.E 0 →ₗ[ℝ] c.F 0) ≤ c.φ.model.E.smooth := by
    rw [hkerEq]
    rintro _ ⟨w, hw, rfl⟩
    refine hψ'1.scDeriv_mem_smooth (by rw [map_zero]; exact h0U') ?_ (hKsm hw)
    rw [map_zero]; exact (ScBanach.paramProd Pn W).smooth.zero_mem
  -- `T₀O` is an sc-subspace and `(1 − Dr(0))E ⊆ E₀` (Proposition 2.35)
  have hRtT := hc.2 n' Wq T hT
  have h01 : (0 : c.φ.model.E 1) ∈
      c.φ.model.E.lvlSet (c.isRetraction.baseRetraction c.relOpen).retract 1 := by
    rw [ScBanach.mem_lvlSet, map_zero, c.base_retract]; exact c.r_image ▸ h0O
  have hs : (0 : c.φ.model.E 1) ∈ c.φ.model.E.smoothLvl 1 := by
    change c.φ.model.E.toBase 1 0 ∈ (c.φ.model.E.smooth : Set (c.φ.model.E 0))
    rw [map_zero]; exact c.φ.model.E.smooth.zero_mem
  obtain ⟨hK, hsplit⟩ := proposition_2_35 hT hRtT h01 hs
  rw [map_zero] at hK
  have hTsc : c.φ.model.E.IsScSubspace (rangeS (scDeriv c.U (r c.R) 0)) := hsplit.1
  -- good position in `E`, then the sc-complement inside `T₀O`
  have hgpE : IsInGoodPosition c.φ.model.E c.φ.model.C
      (LinearMap.ker (Dg 0 : c.φ.model.E 0 →ₗ[ℝ] c.F 0)) :=
    hgp.kernel.isInGoodPosition T hT (scDeriv c.U (r c.R) 0)
      (StrongRetr.scDeriv_r_idem c.relOpen c.isRetraction h0O) hK
  exact ⟨hf.toIsScFredholmSection.mem_smoothSet_of_isZeroAt hy, c, hc, hyV, h0, h0U, g, t₀,
    hfill, ht₀, ht₀0, hconj, Gg, Dg, hGg, hDg,
    ⟨hgp.surj, hgpE.isInGoodPositionScIn c.φ.model.isPartialQuadrant hTsc hgp.kernel.le hNs⟩⟩

/-- **At a zero of an sc-Fredholm section with tame germ data, the two notions of good position
agree, germ reading** (phase 2; the germ form of `isGoodPositionGermSc_iff_wholeChart`): Definition 3.53 with
the text's sc-complement (`IsGoodPositionGermSc`) and with an algebraic complement
(`IsGoodPositionGermTame`). -/
theorem isGoodPositionGermSc_iff (hf : B.IsScFredholmSectionTame f) {y : X}
    (hy : IsZeroAt P f y) : B.IsGoodPositionGermSc f y ↔ B.IsGoodPositionGermTame f y :=
  ⟨fun h => h.isGoodPositionGermTame, fun h => h.isGoodPositionGermSc hf hy⟩

end StrongBundle

/-! ### Theorem 3.54 (1) with the text's notion of good position, germ reading -/

/-- **Theorem 3.54 (1) with the text's notion in the conclusion, from the weaker hypothesis, germ
reading** (phase 2; the germ form of `theorem_3_54_one_sc_of_tame_wholeChart`): for an sc-Fredholm section
`f` with tame germ data in the germ reading (`IsScFredholmSectionTame`), `f(x₀) = 0` and `(f, x₀)`
in good position in a tame chart with an algebraic complement (`IsGoodPositionGermTame`), there is
an open `Vx ∋ x₀` such that at every zero `y ∈ Vx` the germ `(f, y)` is in good position with the
text's sc-complement (`IsGoodPositionGermSc`).  (`theorem_3_54_one'` and
`IsGoodPositionGermTame.isGoodPositionGermSc`; round-trip item V3.82.) -/
theorem theorem_3_54_one_sc_of_tame (hf : B.IsScFredholmSectionTame f) {x₀ : X}
    (hg : B.IsGoodPositionGermTame f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ Vx : Set X, IsOpen Vx ∧ x₀ ∈ Vx ∧
      ∀ y ∈ Vx, IsZeroAt P f y → B.IsGoodPositionGermSc f y := by
  obtain ⟨Vx, hVxo, hx₀Vx, hall⟩ := theorem_3_54_one' hf hg hx₀
  exact ⟨Vx, hVxo, hx₀Vx, fun y hy hy0 => (hall y hy hy0).isGoodPositionGermSc hf hy0⟩

/-- **Theorem 3.54 (1) with the text's notion of good position, germ reading** (phase 2; the germ
form of `theorem_3_54_one_sc_wholeChart`; Definition 3.53 with the sc-complement of Definition 3.21,
`IsGoodPositionGermSc`, in hypothesis and conclusion): for an sc-Fredholm section with tame germ
data in the germ reading, `f(x₀) = 0` and `(f, x₀)` in good position, there is an open `Vx ∋ x₀`
such that at every zero `y ∈ Vx` the germ `(f, y)` is in good position (round-trip item V3.82). -/
theorem theorem_3_54_one_sc (hf : B.IsScFredholmSectionTame f) {x₀ : X}
    (hg : B.IsGoodPositionGermSc f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ Vx : Set X, IsOpen Vx ∧ x₀ ∈ Vx ∧
      ∀ y ∈ Vx, IsZeroAt P f y → B.IsGoodPositionGermSc f y :=
  theorem_3_54_one_sc_of_tame hf hg.isGoodPositionGermTame hx₀

/-- **Theorem 3.54 (1) and (2) with the text's notion of good position, germ reading** (phase 2;
the germ form of `theorem_3_54_sc_wholeChart`): as `theorem_3_54'`, with (1) in the form "every zero
`y ∈ Vx` is in good position with an sc-complement" (`IsGoodPositionGermSc`); (2) the solution
set has regular data of Definition 3.25 (2) at `x₀` on a chart with source in `Vx`, of locally
constant dimension (round-trip item V3.85). -/
theorem theorem_3_54_sc (hf : B.IsScFredholmSectionTame f) {x₀ : X}
    (hg : B.IsGoodPositionGermSc f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ Vx : Set X, IsOpen Vx ∧ x₀ ∈ Vx ∧
      (∀ y ∈ Vx, IsZeroAt P f y → B.IsGoodPositionGermSc f y) ∧
      ∃ d : ℕ, ∃ D : PX.TangentGermChart (solutionSet P f) x₀ d, D.IsRegular ∧ D.φ.source ⊆ Vx ∧
        ∀ y ∈ solutionSet P f ∩ D.φ.source,
          ∀ (n' : ℕ) (_ : PX.TangentGermChart (solutionSet P f) y n'), n' = d := by
  obtain ⟨Vx, hVxo, hx₀Vx, hall, hrest⟩ := theorem_3_54' hf hg.isGoodPositionGermTame hx₀
  exact ⟨Vx, hVxo, hx₀Vx, fun y hy hy0 => (hall y hy hy0).isGoodPositionGermSc hf hy0, hrest⟩

/-- **Theorem 3.23 (implicit function theorem, boundary case) with the text's notion of good
position, germ reading** (phase 2; the germ form of `theorem_3_23_sc_wholeChart`): as `theorem_3_23'`,
with the hypothesis at `x` and the conclusion "every zero in `U` is in good position" in the sense
of Definition 3.53 with the sc-complement (`IsGoodPositionGermSc`). -/
theorem theorem_3_23_sc (hf : B.IsScFredholmSectionTame f) {x : X} (hx : IsZeroAt P f x)
    (hg : B.IsGoodPositionGermSc f x) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ (∀ y ∈ U, IsZeroAt P f y → B.IsGoodPositionGermSc f y) ∧
      (∀ y ∈ U, IsZeroAt P f y → y ∈ PX.smoothSet) ∧
      ∃ d : ℕ, ∃ hsub : PX.IsSubMPolyfold {y ∈ U | IsZeroAt P f y},
        haveI := PX.paracompactSpace_subtype {y ∈ U | IsZeroAt P f y}
        (MPolyfold.subPolyfold hsub).IsTame ∧
          (MPolyfold.subPolyfold hsub).IsManifoldWithCorners d := by
  obtain ⟨U, hUo, hxU, hall, hrest⟩ := theorem_3_23' hf hx hg.isGoodPositionGermTame
  exact ⟨U, hUo, hxU, fun y hy hy0 => (hall y hy hy0).isGoodPositionGermSc hf hy0, hrest⟩

/-! ### The global theorems with the text's notion of good position, germ reading -/

/-- **"Every zero is in good position" in the text's sense is the hypothesis of the germ-reading
theorems**, for an sc-Fredholm section with tame germ data in the germ reading (phase 2; the germ
form of `forall_isGoodPositionGermSc_iff_wholeChart`; `StrongBundle.isGoodPositionGermSc_iff`). -/
theorem forall_isGoodPositionGermSc_iff (hf : B.IsScFredholmSectionTame f) :
    (∀ x, IsZeroAt P f x → B.IsGoodPositionGermSc f x) ↔
      ∀ x, IsZeroAt P f x → B.IsGoodPositionGermTame f x :=
  ⟨fun h x hx => (h x hx).isGoodPositionGermTame,
    fun h x hx => (h x hx).isGoodPositionGermSc hf hx⟩

/-- **Theorem 3.57 with the text's notion of good position, germ reading** (phase 2; the germ form
of `theorem_3_57_sc_wholeChart`: `theorem_3_57` with the hypothesis `IsGoodPositionGermSc` at every
zero): the solution set is a sub-M-polyfold whose induced structure is tame and that of a
manifold with boundary with corners of locally constant dimension. -/
theorem theorem_3_57_sc (hf : B.IsScFredholmSection f)
    (hall : ∀ x, IsZeroAt P f x → B.IsGoodPositionGermSc f x)
    (hne : (solutionSet P f).Nonempty) :
    ∃ hsub : PX.IsSubMPolyfold (solutionSet P f),
      haveI := PX.paracompactSpace_subtype (solutionSet P f)
      (MPolyfold.subPolyfold hsub).IsTame ∧
        (MPolyfold.subPolyfold hsub).IsManifoldWithCornersLoc ∧
        ∀ x ∈ solutionSet P f, ∃ d : ℕ, ∃ D : PX.TangentGermChart (solutionSet P f) x d,
          D.IsRegular ∧ ∀ y ∈ solutionSet P f ∩ D.φ.source,
            ∀ (n' : ℕ) (_ : PX.TangentGermChart (solutionSet P f) y n'), n' = d :=
  theorem_3_57 hf (fun x hx => (hall x hx).isGoodPositionGermTame) hne

/-- **Corollary 3.24 with the text's notion of good position, germ reading** (phase 2; the germ
form of `corollary_3_24_sc_wholeChart`: `corollary_3_24` with the hypothesis `IsGoodPositionGermSc` at
every zero). -/
theorem corollary_3_24_sc (hf : B.IsScFredholmSection f)
    (hall : ∀ x, IsZeroAt P f x → B.IsGoodPositionGermSc f x)
    (hne : (solutionSet P f).Nonempty) :
    ∃ hsub : PX.IsSubMPolyfold (solutionSet P f),
      haveI := PX.paracompactSpace_subtype (solutionSet P f)
      (MPolyfold.subPolyfold hsub).IsTame ∧
        (MPolyfold.subPolyfold hsub).IsManifoldWithCornersLoc :=
  corollary_3_24 hf (fun x hx => (hall x hx).isGoodPositionGermTame) hne

/-- **Theorem 3.56 with the text's notion of good position, germ reading** (phase 2; the germ form
of `theorem_3_56_sc_wholeChart`: `theorem_3_56` with the hypothesis `IsGoodPositionGermSc` at every
zero; `∂X = ∅`). -/
theorem theorem_3_56_sc (hX : PX.IsWithoutBoundary) (hf : B.IsScFredholmSection f)
    (hall : ∀ x, IsZeroAt P f x → B.IsGoodPositionGermSc f x)
    (hne : (solutionSet P f).Nonempty) :
    ∃ hsub : PX.IsSubMPolyfold (solutionSet P f),
      haveI := PX.paracompactSpace_subtype (solutionSet P f)
      (MPolyfold.subPolyfold hsub).IsManifoldWithCornersLoc ∧
        (MPolyfold.subPolyfold hsub).IsWithoutBoundary :=
  theorem_3_56 hX hf (fun x hx => (hall x hx).isGoodPositionGermTame) hne

end Bundle

end Polyfold
