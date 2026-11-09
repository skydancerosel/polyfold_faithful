import Polyfold.Chapter3.GlobalIFTFull
import Polyfold.Chapter2.TameInvariance

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.6,
**Theorem 3.6.8 (preprint 3.54) (2) at the centre `x₀`**: the data of Definition 3.2.1 (preprint 3.25) (2) (the `d`-dimensional
tangent germ property) for the solution set `S = {y ∈ V | f(y) = 0}` at the zero `x₀`, in the
chart `ψ ∘ ϕ` of the proof of Theorem 3.6.8 (preprint 3.54).

# Theorem 3.6.8 (preprint 3.54) (2) at the centre

## The text, paraphrased

(Proof of Theorem 3.6.8 (preprint 3.54)) "`ψ ∘ ϕ({y ∈ V | f(y) = 0}) = {v + σ(v) | v ∈ V'}` ... Consequently,
abbreviating `d = dim ker f'(x)`, the solution set `S ⊆ V` possesses the `d`-dimensional tangent
germ property according to Definition 3.25. Therefore we can apply Theorem 3.27."

## What is formalized

* `Polyfold.MChart.compDiffeo`: **the chart `ψ ∘ ϕ`** of `X`, for a chart `ϕ : V → O` and an
  sc-diffeomorphism `ψ : U → U'` of relatively open subsets of partial quadrants with `O ⊆ U`,
  onto the retract `ψ(O) ⊆ C'`; `MChart.compDiffeo_isChart`: it is a chart of the M-polyfold
  structure (its transition maps to a chart `ϕ'` are `(ϕ' ∘ ϕ⁻¹) ∘ ψ⁻¹` and `ψ ∘ (ϕ ∘ ϕ'⁻¹)`).
* `Polyfold.theorem_3_6_8_tangentGermChart_wholeChart`: **the data of Definition 3.2.1 (preprint 3.25) (2) for `S` at `x₀`**
  (`MPolyfold.TangentGermChart`, `n = dim ker D(h + t)(0)`): the chart `ψ ∘ ϕ` onto the tame
  retract `ψ(O)` (`IsScDiffeoQuadrant.isTameRetract_image`), `N = ker D(h + t)(0)` (smooth,
  `ker_Dfs_le_smooth`) in good position to `C'` with the closed good complement `Y`, the relatively
  open `V' ⊆ N ∩ C'`, and `σ : V' → Y` with `ψ ∘ ϕ(S) = {v + σ(v) | v ∈ V'}`, an sc^∞-germ
  (`isScInftyGermAt_of_lifts`) with `σ(0) = 0`, `Dσ(0) = 0` — all from `theorem_3_6_8_graph_wholeChart`.
* `Polyfold.theorem_3_6_8_tangentGermChart_proj_wholeChart`: the same data with **condition (b) of
  `TangentGermChart.IsRegular`**, `π(ψ(O)) ⊆ C'` for the projection `π` along `Y`: the good
  complement of `theorem_3_6_8_graph_proj_wholeChart` is chosen so that the projection maps `C'` into
  `N ∩ C'` (`ProjectsInto`, `MPolyfold.TangentGermChart.π_mem_of_projectsInto`,
  `TangentGermChart.isRegular_of_projectsInto`; Findings 130–133).
* `Polyfold.theorem_3_6_8_tangentGermChart_proj_conj_wholeChart`: the same, with the data of Definition 3.6.6 (preprint 3.53)
  in the strong bundle chart from which `ψ ∘ ϕ` is built and `d = dim Pn − dim Q` for the
  conjugation there (`theorem_3_6_8_graph_proj_conj_wholeChart`): the dimension is the index `n − N`, which
  `GlobalIFTIndex.lean` identifies with the Fredholm index of `f'(x₀)` in every chart.

## Where the rest of Theorem 3.6.8 (preprint 3.54) (2) is

* **The data at the other points `y ∈ S`** (the text's "proceeding as above we can construct a map
  `σ`"): Definition 3.6.6 (preprint 3.53) at the nearby zeros is Theorem 3.6.8 (preprint 3.54) (1) (`theorem_3_6_8_one'_wholeChart`,
  `GlobalIFTNearbyOnto.lean`, with the chart independence of `LinearizationCharts.lean`), and this
  file's data at each such zero give the data there (`theorem_3_6_8_tangentGermChart_solutionSet_wholeChart`,
  `GlobalIFTTheorems.lean`).
* **Condition (a) of the regularity conditions `IsRegular` of Theorem 3.2.3 (preprint 3.27)** (Finding 82): `σ`
  sc-smooth on `V'` in the set sense, which goes beyond Theorem 3.5.11 (preprint 3.47) (1) (an sc^∞-germ in the
  `k`-dependent sense only), is obtained by re-centring at the nearby zeros
  (`TangentGermChart.exists_isRegular_of_locally`, `SolutionGermRecentre.lean`; Findings 150–151)
  and assembled in `theorem_3_6_8_two_wholeChart` (`GlobalIFTTheorems.lean`).  Condition (b),
  `π(ψ(O)) ⊆ C'` (Finding 83), is not a restriction for the solution set: the good complement can
  be chosen so that it holds (`theorem_3_6_8_tangentGermChart_proj_wholeChart`, Findings 130–133).
-/

open Set Filter Topology Function Module

noncomputable section

namespace Polyfold

/-! ### Sc-smooth maps on relatively open sets as maps between retracts -/

/-- An sc-smooth map `g` on a relatively open `U` is an sc-smooth map between retracts
`(O, C, E) → (O', C', E')` for every retract `O ⊆ U` mapped into `O'`. -/
theorem IsScSmooth.isScSmoothRetractMap_of_subset {E E' : ScBanach} {C : Set (E 0)} {C' : Set (E' 0)}
    {U O : Set (E 0)} {O' : Set (E' 0)} {g : E 0 → E' 0} (hU : IsRelOpenInQuadrant E C U)
    (hg : IsScSmooth U g) (hO : O ⊆ U) (hmaps : MapsTo g O O') :
    IsScSmoothRetractMap E C O E' C' O' g where
  mapsTo := hmaps
  comp_isScSmooth R hR := IsScSmooth.comp R.isScDomain hU.isScDomain hg R.isScSmooth
    fun y hy => hO (hR ▸ R.apply_mem_retract hy)

/-! ### The chart `ψ ∘ ϕ` -/

section CompDiffeo

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

variable (φ : MChart X) {E' : ScBanach} {C' : Set (E' 0)} {U : Set (φ.model.E 0)} {U' : Set (E' 0)}
  {hU : IsRelOpenInQuadrant φ.model.E φ.model.C U} {hU' : IsRelOpenInQuadrant E' C' U'}
  {ψ : φ.model.E 0 → E' 0} {ψ' : E' 0 → φ.model.E 0}

/-- **The chart `ψ ∘ ϕ`**: the composition of a chart `ϕ : V → O` with an sc-diffeomorphism
`ψ : U → U'` of relatively open subsets of partial quadrants with `O ⊆ U`, a chart onto the
retract `ψ(O) ⊆ C'`. -/
def MChart.compDiffeo (h : IsScDiffeoQuadrant hU hU' ψ ψ') (hOU : φ.model.O ⊆ U)
    (hret : IsScRetract E' C' (ψ '' φ.model.O)) : MChart X where
  model := ⟨E', C', ψ '' φ.model.O, hret⟩
  toPartialEquiv :=
    { toFun := ψ ∘ φ
      invFun := φ.symm ∘ ψ'
      source := φ.source
      target := ψ '' φ.model.O
      map_source' := fun x hx => ⟨φ x, φ.mapsTo_model x hx, rfl⟩
      map_target' := by
        rintro _ ⟨z, hz, rfl⟩
        simp only [Function.comp_apply]
        rw [h.left_inv z (hOU hz)]
        exact φ.symm_mapsTo hz
      left_inv' := fun x hx => by
        simp only [Function.comp_apply]
        rw [h.left_inv _ (hOU (φ.mapsTo_model x hx)), φ.symm_apply_apply hx]
      right_inv' := by
        rintro _ ⟨z, hz, rfl⟩
        simp only [Function.comp_apply]
        rw [h.left_inv z (hOU hz), φ.apply_symm_apply hz] }
  isOpen_source := φ.isOpen_source
  target_eq := rfl
  continuousOn_toFun := h.isScSmooth.isSc1.isSc0.continuousOn_base.comp φ.continuousOn_toFun
    fun x hx => hOU (φ.mapsTo_model x hx)
  continuousOn_invFun := by
    refine φ.continuousOn_invFun.comp (h.isScSmooth_inv.isSc1.isSc0.continuousOn_base.mono ?_) ?_
    · rintro _ ⟨z, hz, rfl⟩; exact h.mapsTo (hOU hz)
    · rintro _ ⟨z, hz, rfl⟩
      show ψ' (ψ z) ∈ φ.model.O
      rw [h.left_inv z (hOU hz)]; exact hz

variable {φ}

lemma MChart.compDiffeo_source (h : IsScDiffeoQuadrant hU hU' ψ ψ') (hOU : φ.model.O ⊆ U)
    (hret : IsScRetract E' C' (ψ '' φ.model.O)) : (φ.compDiffeo h hOU hret).source = φ.source := rfl

lemma MChart.compDiffeo_apply (h : IsScDiffeoQuadrant hU hU' ψ ψ') (hOU : φ.model.O ⊆ U)
    (hret : IsScRetract E' C' (ψ '' φ.model.O)) (x : X) : φ.compDiffeo h hOU hret x = ψ (φ x) := rfl

lemma MChart.compDiffeo_model_O (h : IsScDiffeoQuadrant hU hU' ψ ψ') (hOU : φ.model.O ⊆ U)
    (hret : IsScRetract E' C' (ψ '' φ.model.O)) :
    (φ.compDiffeo h hOU hret).model.O = ψ '' φ.model.O := rfl

/-- **The chart `ψ ∘ ϕ` is a chart of the M-polyfold structure**: the transition maps to a chart
`ϕ'` are `(ϕ' ∘ ϕ⁻¹) ∘ ψ⁻¹` and `ψ ∘ (ϕ ∘ ϕ'⁻¹)`, compositions of sc-smooth maps between
retracts. -/
theorem MChart.compDiffeo_isChart (hφ : P.IsChart φ) (h : IsScDiffeoQuadrant hU hU' ψ ψ')
    (hOU : φ.model.O ⊆ U) (hret : IsScRetract E' C' (ψ '' φ.model.O)) :
    P.IsChart (φ.compDiffeo h hOU hret) := by
  intro φ' hφ'
  have hcompat := MPolyfold.IsChart.compatible P hφ (P.isChart_of_mem hφ')
  have hov : (φ.compDiffeo h hOU hret).overlap φ' = ψ '' (φ.overlap φ') := by
    show (ψ ∘ φ) '' (φ.source ∩ φ'.source) = ψ '' (φ '' (φ.source ∩ φ'.source))
    rw [image_comp]
  have hovU : φ.overlap φ' ⊆ U := (φ.overlap_subset φ').trans hOU
  constructor
  · -- `(ψ ∘ ϕ) → ϕ'`: `(ϕ' ∘ ϕ⁻¹) ∘ ψ⁻¹`
    have h1 : IsScSmoothRetractMap E' C' (ψ '' φ.overlap φ') φ.model.E φ.model.C (φ.overlap φ') ψ' :=
      h.isScSmooth_inv.isScSmoothRetractMap_of_subset hU'
        (image_subset_iff.2 fun z hz => h.mapsTo (hovU hz)) (by
          rintro _ ⟨z, hz, rfl⟩
          show ψ' (ψ z) ∈ φ.overlap φ'
          rw [h.left_inv z (hovU hz)]; exact hz)
    have h2 := hcompat.1.comp h1 (φ.isScRetract_overlap φ')
    rw [hov]
    exact h2
  · -- `ϕ' → (ψ ∘ ϕ)`: `ψ ∘ (ϕ ∘ ϕ'⁻¹)`
    have h1 : IsScSmoothRetractMap φ.model.E φ.model.C (φ.overlap φ') E' C' (ψ '' φ.overlap φ') ψ :=
      h.isScSmooth.isScSmoothRetractMap_of_subset hU hovU (mapsTo_image ψ _)
    have h2 := h1.comp hcompat.2 (φ.isScRetract_overlap φ')
    rw [hov]
    exact h2

end CompDiffeo

/-! ### Condition (b) of `IsRegular` from the choice of the good complement -/

namespace MPolyfold.TangentGermChart

universe w

variable {Xw : Type w} [TopologicalSpace Xw] [T2Space Xw] [ParacompactSpace Xw]
  {PXw : MPolyfold Xw} {M : Set Xw} {x : Xw} {n : ℕ} (d : PXw.TangentGermChart M x n)

/-- **Condition (b) of `IsRegular` from the choice of the good complement**: if the projection onto
`N` along `Y` maps `C` into `C` (`ProjectsInto C N Y`), then `π(O) ⊆ C` (the retract `O` lies in
`C`). -/
theorem π_mem_of_projectsInto (h : ProjectsInto d.φ.model.C d.N d.Y) :
    ∀ z ∈ d.φ.model.O, (d.π z : d.φ.model.E 0) ∈ d.φ.model.C := by
  intro z hz
  obtain ⟨R, hR⟩ := d.φ.model.isScRetract
  have hzC : z ∈ d.φ.model.C := R.retract_subset_C (hR ▸ hz)
  exact h.projectionOnto_mem d.isTopCompl.isCompl hzC

/-- `IsRegular` from (a) the set-sense sc-smoothness of `δ` on `V` and (b') `ProjectsInto C N Y`. -/
theorem isRegular_of_projectsInto
    (hδ : IsScSmooth (E := ScBanach.const d.N) (F := d.φ.model.E) d.V d.δ)
    (h : ProjectsInto d.φ.model.C d.N d.Y) : d.IsRegular :=
  ⟨hδ, d.π_mem_of_projectsInto h⟩

end MPolyfold.TangentGermChart

/-! ### Theorem 3.6.8 (preprint 3.54) (2) at the centre: the data of Definition 3.2.1 (preprint 3.25) (2) for `S` at `x₀` -/

section Center

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

set_option maxHeartbeats 800000 in
/-- **Theorem 3.6.8 (preprint 3.54) (2) at the centre `x₀`, with the conjugation exposed**:
`theorem_3_6_8_tangentGermChart_proj_wholeChart` (a corollary of this theorem) together with the data of
Definition 3.6.6 (preprint 3.53) in the strong bundle chart `c` centred at `x₀` from which the chart `ψ ∘ ϕ` of the
tangent germ data is built (filled version `g`, sc⁺-section `s`, good position, conjugation data
`dc` of `g − s` to a basic germ) and `d = dim dc.Pn − dim dc.Q`: the dimension of the tangent germ
data is the index `n − N` of the conjugation (`theorem_3_6_8_graph_proj_conj_wholeChart`), which is the
Fredholm index of `f'(x₀)` (`proposition_3_6_5_local_index_wholeChart`; `GlobalIFTIndex.lean`, Finding 170). -/
theorem theorem_3_6_8_tangentGermChart_proj_conj_wholeChart (hf : IsSection P f) {x₀ : X}
    (hg : B.IsGoodPositionGermTameWholeChart f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ (Vx : Set X) (d : ℕ), IsOpen Vx ∧ x₀ ∈ Vx ∧
      (∃ D : PX.TangentGermChart {y ∈ Vx | IsZeroAt P f y} x₀ d,
        ∀ z ∈ D.φ.model.O, (D.π z : D.φ.model.E 0) ∈ D.φ.model.C) ∧
      ∃ (c : StrongBundleChart PX P) (_ : B.IsTameChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
        (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0)
        (s : c.φ.model.E 0 → c.F 1)
        (_ : IsFilledVersion c.relOpen c.isRetraction h0 (c.principal f) g)
        (_ : IsScSmooth (F := c.F.shift) c.U s) (_ : c.F.toBase 1 (s 0) = g 0)
        (_ : IsGoodPositionAt c.relOpen c.isRetraction h0 g)
        (dc : ConjugationData c.U fun u => g u - c.F.toBase 1 (s u)),
        (d : ℤ) = finrank ℝ dc.Pn - finrank ℝ dc.Q := by
  classical
  obtain ⟨c, hc, hxV, h0, Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, hCt, U', hU', ψ, hψsc, hψ0, hψU',
    ψ', hψ'sc, hψ'U, hψψ', hψ'ψ, 𝒮, h', Bc, hh', hsurj, hpos, Yc, V', σ, Vx, hconjd, hYc, hYcc,
    hYcp, hKsm, hV'rel, h0V', hσY, hσ1, hσC, hσ0, hDσ, hsol, hlift, hVxo, hx₀Vx, hVxsub, hinj, hzero,
    himage⟩ := theorem_3_6_8_graph_proj_conj_wholeChart hf hg hx₀
  have hKfin : FiniteDimensional ℝ (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) :=
    (𝒮.isFredholm_Dfs hCt hh').1.finite_ker
  -- the sc-diffeomorphism `ψ : U → U'` and the tame retract `ψ(O)`
  have hd : IsScDiffeoQuadrant c.relOpen hU' ψ ψ' := ⟨hψsc, hψ'sc, hψU', hψ'U, hψψ', hψ'ψ⟩
  have hOU : c.φ.model.O ⊆ c.U := fun z hz => by
    rw [← c.r_image] at hz
    obtain ⟨v, hv, rfl⟩ := hz
    exact StrongRetr.r_mem c.isRetraction hv
  have htameO : IsTameRetract (ScBanach.paramProd Pn W) (Ct ×ˢ univ) (ψ '' c.φ.model.O) := by
    have := hd.isTameRetract_image (c.isRetraction.baseRetraction c.relOpen) rfl hc.2
    rwa [c.base_retract] at this
  -- the chart `ψ ∘ ϕ`
  set χ := c.φ.compDiffeo hd hOU htameO.isScRetract with hχ
  have hDσ' : fderivWithin ℝ σ (Subtype.val ⁻¹' (Ct ×ˢ univ)) 0 = 0 := by
    obtain ⟨O, hO, hV'eq⟩ := hV'rel
    have h0O : (0 : LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) ∈ O := (hV'eq ▸ h0V').1
    rw [hV'eq, inter_comm, fderivWithin_inter (hO.mem_nhds h0O)] at hDσ
    exact hDσ
  refine ⟨Vx, finrank ℝ (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)), hVxo, hx₀Vx,
    ⟨?_, ?_⟩, c, hc, hxV, h0, hconjd⟩
  exact
    { φ := χ
      isChart := c.φ.compDiffeo_isChart c.isChart hd hOU htameO.isScRetract
      mem_source := hxV
      φ_zero := by show ψ (c.φ x₀) = 0; rw [h0, hψ0]
      tame := htameO
      N := LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)
      finiteDimensional := hKfin
      finrank_eq := rfl
      smooth := hKsm
      goodPosition := hpos
      Y := Yc
      goodComplement := hYc
      isClosed_Y := hYcc
      V := V'
      V_relOpen := hV'rel
      zero_mem_V := h0V'
      δ := σ
      δ_mem_Y := hσY
      continuousOn := hσC.continuousOn
      image_eq := by
        show (ψ ∘ c.φ) '' ({y ∈ Vx | IsZeroAt P f y} ∩ c.φ.source) = _
        rw [inter_eq_left.2 fun y hy => hVxsub hy.1]
        exact himage
      germ := by
        have := hKfin
        exact isScInftyGermAt_of_lifts (N := LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0))
          (E := ScBanach.paramProd Pn W) (D := Subtype.val ⁻¹' (Ct ×ˢ univ)) (σ := σ) fun k hk => by
          obtain ⟨Vk, h1, h2, -, σk, h3, h4⟩ := hlift k hk
          exact ⟨Vk, h1, h2, σk, h3, h4⟩
      δ_zero := hσ0
      fderivWithin_zero := hDσ' }
  -- condition (b) of `IsRegular`: `π(ψ(O)) ⊆ C'`, from the choice of `Y` (`ProjectsInto`)
  exact MPolyfold.TangentGermChart.π_mem_of_projectsInto _ hYcp

/-- **Theorem 3.6.8 (preprint 3.54) (2) at the centre `x₀` with condition (b) of `IsRegular`**: the data of
Definition 3.2.1 (preprint 3.25) (2) for the solution set `S = {y ∈ Vx | f(y) = 0}` at `x₀` of
`theorem_3_6_8_tangentGermChart_wholeChart` (a corollary of this theorem), with in addition
`π(O') ⊆ C'` for the projection `π` onto `N` along the good complement `Y` and the retract
`O' = ψ(O)` of the chart `ψ ∘ ϕ` — condition (b) of `TangentGermChart.IsRegular`.  It holds because
the good complement of `theorem_3_6_8_graph_proj_wholeChart` is chosen with `ProjectsInto C' N Y`
(`TangentGermChart.π_mem_of_projectsInto`; Findings 130–133).  Condition (a) of `IsRegular`
(`σ` sc-smooth on `V'` in the set sense) is not provided here (it is obtained by re-centring in
`theorem_3_6_8_two_wholeChart`).  (A corollary of `theorem_3_6_8_tangentGermChart_proj_conj_wholeChart`.) -/
theorem theorem_3_6_8_tangentGermChart_proj_wholeChart (hf : IsSection P f) {x₀ : X}
    (hg : B.IsGoodPositionGermTameWholeChart f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ (Vx : Set X) (d : ℕ), IsOpen Vx ∧ x₀ ∈ Vx ∧
      ∃ D : PX.TangentGermChart {y ∈ Vx | IsZeroAt P f y} x₀ d,
        ∀ z ∈ D.φ.model.O, (D.π z : D.φ.model.E 0) ∈ D.φ.model.C := by
  obtain ⟨Vx, d, h1, h2, hD, -⟩ := theorem_3_6_8_tangentGermChart_proj_conj_wholeChart hf hg hx₀
  exact ⟨Vx, d, h1, h2, hD⟩

/-- **Theorem 3.6.8 (preprint 3.54) (2) at the centre `x₀`: the data of Definition 3.2.1 (preprint 3.25) (2) for the solution set.**
For a section `f` of a strong bundle, `f(x₀) = 0` and `(f, x₀)` in good position in a tame chart
(`IsGoodPositionGermTameWholeChart`), there is an open neighbourhood `Vx` of `x₀` such that the solution set
`S = {y ∈ Vx | f(y) = 0}` has, at `x₀`, the data of Definition 3.2.1 (preprint 3.25) (2) with `n = dim ker f'(x₀)`
(`TangentGermChart`): the chart `ψ ∘ ϕ` onto the tame retract `(ψ(O), C', E')`
(`MChart.compDiffeo`, tame by `IsScDiffeoQuadrant.isTameRetract_image`), the smooth subspace
`N = ker D(h + t)(0)` in good position to `C'` with the closed good complement `Y`, the
relatively open `V' ⊆ N ∩ C'` and `σ : V' → Y` with `ψ ∘ ϕ(S) = {v + σ(v) | v ∈ V'}`, an sc^∞-germ
with `σ(0) = 0`, `Dσ(0) = 0` (`theorem_3_6_8_graph_wholeChart`).  The data at the other points of `S` and
condition (a) of the regularity conditions `IsRegular` of Theorem 3.2.3 (preprint 3.27) are not part of this
theorem: they are obtained in `theorem_3_6_8_two_wholeChart` (`GlobalIFTTheorems.lean`); condition (b) is
`theorem_3_6_8_tangentGermChart_proj_wholeChart`, of which this is a corollary.  That `n` is the Fredholm
index of `f'(x₀)` is `theorem_3_6_8_tangentGermChart_index_wholeChart` (`GlobalIFTIndex.lean`). -/
theorem theorem_3_6_8_tangentGermChart_wholeChart (hf : IsSection P f) {x₀ : X}
    (hg : B.IsGoodPositionGermTameWholeChart f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ (Vx : Set X) (d : ℕ), IsOpen Vx ∧ x₀ ∈ Vx ∧
      Nonempty (PX.TangentGermChart {y ∈ Vx | IsZeroAt P f y} x₀ d) := by
  obtain ⟨Vx, d, h1, h2, D, -⟩ := theorem_3_6_8_tangentGermChart_proj_wholeChart hf hg hx₀
  exact ⟨Vx, d, h1, h2, ⟨D⟩⟩

end Center

end Polyfold
