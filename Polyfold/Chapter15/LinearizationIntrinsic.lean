import Polyfold.Chapter15.Linearization
import Polyfold.Chapter3.LinearizationIntrinsic

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 15,
§15.1 (pp. 683–687): **Theorem 15.1.1** (2017: Theorem 15.1) with intrinsic operators
`T_xX → W_x`, independent of the local section structure **and of the chart**.

# `T(f, Λ)(x) ∈ GrF(x)` with intrinsic operators

## The text, paraphrased

(p. 683) `GrF(x)` consists of finite formal sums `∑ σ_L · L` of operators `L : T_xX → W_x`.
(Theorem 15.1.1) `T(f,Λ)(y) = ∑_{i : f(y) = sᵢ(y)} σᵢ · (f − sᵢ)'(y)` does not depend on the local
sc⁺-section structure `(sᵢ, σᵢ)`.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `GrF x = (T_xX →ₗ W_x) →₀ ℚ≥0` for `x ∈ X₁` (`T_xX = PX.tangentFiber x` with its linear
  structure, `W_x = P⁻¹(x)`).
* `toIntr c hx L : T_xX →ₗ W_x`, the operator `Φ_x⁻¹ ∘ L ∘ Tφ` read from an operator
  `L : E → F` of the chart `c` (`0` if `L ∘ Tφ` leaves `Φ_x(W_x)`).
* `linSumIntr c hx f s σ = ∑_{i : f(x) = sᵢ(x)} σᵢ · (f − sᵢ)'(x) ∈ GrF x`, through the chart `c`.
* `sectionSubOn f s O`: a global section equal to `f − s` on `O` (and to `f` elsewhere);
  `isScSmoothRetractMap_sectionSubOn`: its principal part is sc-smooth in every chart of `P`
  with domain in `O`; `toIntr_chart_independent`: at a zero of `f − s`, the intrinsic operator
  `(f − s)'(x) : T_xX → W_x` is the same through any two such charts (the chain rule
  `linAt_chart_change_key` of Part I, as in `StrongBundle.linIntr_chart_independent`).
* **`theorem_15_1_1_intrinsic`**: for an sc-Fredholm section functor `f` and two local section
  structures of `Λ` on `O`, `O'`, the formal sums in `GrF x` agree, through any two charts `c`,
  `c'` of `P` with domains in `O`, `O'` respectively, at every `x ∈ X₁` in both domains.

* **Definition 15.1.7**: `linearization f Λ x ∈ GrF x` (through `LocalLinData`, a structure and a
  chart); `linearization_eq` (Theorem 15.1.1 (2): any data give it), `nonempty_localLinData`
  (data exist for an sc⁺-multisection), `linearization_eq_zero` (Theorem 15.1.1 (1) and Remark
  15.1.2: `0` where `Λ(f(x)) = 0`).

## Elsewhere

The sc-Fredholm property of the operators is in `FredholmSummands`; the functor property
`T(f,Λ)(t φ) = φ_* T(f,Λ)(s φ)` is in `LinearizationFunctor` (`theorem_15_1_1_functor`).
-/

open Set Filter Topology Function Module

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongRetr MPolyfold Linearization15

variable {A : SEP.{u}}

/-! ### `GrF(x)` and intrinsic operators -/

/-- **`GrF(x)`** (2021 p. 683) at `x ∈ X₁`: finite formal sums with nonnegative rational
coefficients of linear operators `T_xX → W_x`. -/
abbrev GrF (x : A.X.PObj.Level 1) : Type _ :=
  (A.X.PObj.tangentFiber x →ₗ[ℝ] A.P ⁻¹' {A.X.PObj.levelVal 1 x}) →₀ ℚ≥0

/-- An operator `L : E → F` of the chart `c` along `T_xX`: `α ↦ L(Tφ α)`. -/
def chartOp (c : StrongBundleChart A.X.PObj A.P) {x : A.X.PObj.Level 1}
    (hx : A.X.PObj.levelVal 1 x ∈ c.φ.source) (L : c.φ.model.E 0 →L[ℝ] c.F 0) :
    A.X.PObj.tangentFiber x →ₗ[ℝ] c.F 0 :=
  (L : c.φ.model.E 0 →ₗ[ℝ] c.F 0) ∘ₗ (tangentFiberModel c.isChart hx).subtype ∘ₗ
    (tangentFiberLinearEquiv c.isChart hx).toLinearMap

theorem chartOp_apply (c : StrongBundleChart A.X.PObj A.P) {x : A.X.PObj.Level 1}
    (hx : A.X.PObj.levelVal 1 x ∈ c.φ.source) (L : c.φ.model.E 0 →L[ℝ] c.F 0)
    (α : A.X.PObj.tangentFiber x) :
    chartOp c hx L α = L (tangentFiberEquiv c.isChart hx α : c.φ.model.E 0) := rfl

open Classical in
/-- **The intrinsic operator `Φ_x⁻¹ ∘ L ∘ Tφ : T_xX → W_x`** of an operator `L : E → F` of the
chart `c` (`0` if `L ∘ Tφ` does not take values in `Φ_x(W_x)`). -/
def toIntr (c : StrongBundleChart A.X.PObj A.P) {x : A.X.PObj.Level 1}
    (hx : A.X.PObj.levelVal 1 x ∈ c.φ.source) (L : c.φ.model.E 0 →L[ℝ] c.F 0) :
    A.X.PObj.tangentFiber x →ₗ[ℝ] A.P ⁻¹' {A.X.PObj.levelVal 1 x} :=
  if h : ∀ α, chartOp c hx L α ∈ LinearMap.range (c.fiberLin hx) then
    (LinearEquiv.ofInjective (c.fiberLin hx) (c.fiberLin_injective hx)).symm.toLinearMap ∘ₗ
      (chartOp c hx L).codRestrict _ h
  else 0

theorem fiberLin_toIntr (c : StrongBundleChart A.X.PObj A.P) {x : A.X.PObj.Level 1}
    (hx : A.X.PObj.levelVal 1 x ∈ c.φ.source) {L : c.φ.model.E 0 →L[ℝ] c.F 0}
    (h : ∀ α, chartOp c hx L α ∈ LinearMap.range (c.fiberLin hx))
    (α : A.X.PObj.tangentFiber x) : c.fiberLin hx (toIntr c hx L α) = chartOp c hx L α := by
  rw [toIntr, dif_pos h]
  set e := LinearEquiv.ofInjective (c.fiberLin hx) (c.fiberLin_injective hx)
  have h' := congrArg Subtype.val (e.apply_symm_apply ((chartOp c hx L).codRestrict _ h α))
  rw [LinearEquiv.ofInjective_apply] at h'
  exact h'

/-- **The formal sum of Theorem 15.1.1 (2) in `GrF(x)`**, through the chart `c`:
`∑_{i : f(x) = sᵢ(x)} σᵢ · (f − sᵢ)'(x)` with
`(f − sᵢ)'(x) = Φ_x⁻¹ ∘ D((f̂ − ŝᵢ) ∘ r)(φ(x)) ∘ Tφ`. -/
def linSumIntr (c : StrongBundleChart A.X.PObj A.P) {x : A.X.PObj.Level 1}
    (hx : A.X.PObj.levelVal 1 x ∈ c.φ.source) (f : A.Obj → A.W) {k : ℕ}
    (s : Fin k → A.Obj → A.W) (σ : Fin k → ℚ≥0) : GrF x :=
  linSumModelMap c.U c.R (c.principal f) (fun i => c.principal (s i)) σ
    (levelLift c.φ 1 (A.X.PObj.levelVal 1 x)) (toIntr c hx)

/-! ### Independence of the local section structure -/

/-- **Theorem 15.1.1, structure independence in `GrF(x)`**: two local section structures of `Λ`
on `O`, `O'` give the same formal sum, through any chart of `P` with domain in `O ∩ O'`. -/
theorem linSumIntr_eq_of_isLocalRepOn {f : A.Obj → A.W} (hf : A.B.IsScSmoothSection f)
    {Λ : A.W → ℚ≥0} {O O' : Set A.Obj} {k l : ℕ} {s : Fin k → A.Obj → A.W}
    {σ : Fin k → ℚ≥0} {t : Fin l → A.Obj → A.W} {τ : Fin l → ℚ≥0}
    (hs : IsLocalRepOn A Λ O s σ) (ht : IsLocalRepOn A Λ O' t τ)
    {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c) (hsub : c.φ.source ⊆ O ∩ O')
    {x : A.X.PObj.Level 1} (hx : A.X.PObj.levelVal 1 x ∈ c.φ.source) :
    linSumIntr c hx f s σ = linSumIntr c hx f t τ := by
  have hO : r c.R '' c.U = c.φ.model.O := c.r_image
  have hz : c.φ.model.E.toBase 1 (levelLift c.φ 1 (A.X.PObj.levelVal 1 x)) ∈ c.φ.model.O := by
    rw [A.X.PObj.toBase_levelLift c.isChart hx (levelVal_mem x)]
    exact c.φ.mapsTo_model _ hx
  refine theorem_15_1_1_model_map c.relOpen c.isRetraction (isScSmooth_principal_comp_r hf hc)
    (fun i => (hs.2.1 i).isScSmooth_principal_comp_r hc fun x hx => (hsub hx).1)
    (fun j => (ht.2.1 j).isScSmooth_principal_comp_r hc fun x hx => (hsub hx).2)
    isOpen_univ (fun y hy _ v => ?_) (by rw [hO]; exact hz) (mem_univ _) _
  rw [hO] at hy
  rw [hs.count_eq (fun x hx => (hsub hx).1) hy v, ht.count_eq (fun x hx => (hsub hx).2) hy v]

/-! ### `f − s` as a global section -/

open Classical in
/-- **`f − s` on `O`**, extended by `f` off `O`: a global section (for sections `f` of `P` and
`s` of `P` over `O`), whose principal part in a chart with domain in `O` is `f̂ − ŝ`. -/
def sectionSubOn (f s : A.Obj → A.W) (O : Set A.Obj) : A.Obj → A.W := fun y =>
  if h : y ∈ O ∧ A.P (s y) = y ∧ A.P (f y) = y then
    (((⟨f y, h.2.2⟩ : A.P ⁻¹' {y}) - ⟨s y, h.2.1⟩ : A.P ⁻¹' {y}) : A.W)
  else f y

theorem isSection_sectionSubOn {f s : A.Obj → A.W} (hf : IsSection A.P f) (O : Set A.Obj) :
    IsSection A.P (sectionSubOn f s O) := fun y => by
  unfold sectionSubOn
  split_ifs with h
  · exact (((⟨f y, h.2.2⟩ : A.P ⁻¹' {y}) - ⟨s y, h.2.1⟩ : A.P ⁻¹' {y})).2
  · exact hf y

theorem principal_sectionSubOn {f s : A.Obj → A.W} (hf : IsSection A.P f) {O : Set A.Obj}
    (hsec : ∀ y ∈ O, A.P (s y) = y) {c : StrongBundleChart A.X.PObj A.P}
    (hsub : c.φ.source ⊆ O) {z : c.φ.model.E 0} (hz : z ∈ c.φ.model.O) :
    c.principal (sectionSubOn f s O) z = c.principal f z - c.principal s z := by
  have hzV : c.φ.symm z ∈ c.φ.source := c.φ.symm_mapsTo hz
  have h : c.φ.symm z ∈ O ∧ A.P (s (c.φ.symm z)) = c.φ.symm z ∧
      A.P (f (c.φ.symm z)) = c.φ.symm z := ⟨hsub hzV, hsec _ (hsub hzV), hf _⟩
  unfold StrongBundleChart.principal sectionSubOn
  rw [dif_pos h]
  exact c.snd_sub hzV _ _

/-- **The principal part of `f − s` is sc-smooth in a chart with domain in `O`** (the form
`(z, f̂(z) − ŝ(z)) : O → K` of Definition 2.6.6 read in the chart). -/
theorem isScSmoothRetractMap_sectionSubOn {f : A.Obj → A.W} (hf : A.B.IsScSmoothSection f)
    {s : A.Obj → A.W} {O : Set A.Obj} (hs : IsScPlusSectionOn A s O)
    {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c) (hsub : c.φ.source ⊆ O) :
    IsScSmoothRetractMap c.φ.model.E c.φ.model.C c.φ.model.O (c.φ.model.E.prod c.F)
      (c.φ.model.C ×ˢ univ) c.K (fun z => (z, c.principal (sectionSubOn f s O) z)) := by
  refine ⟨fun z hz => c.principal_mem_K (isSection_sectionSubOn hf.1 O) hz, fun R' hR' => ?_⟩
  have hUd : IsScDomain c.φ.model.E R'.U := R'.relOpen.isScDomain
  -- `f̂ ∘ R'` and `ŝ ∘ R'` are sc-smooth on `R'.U`
  have hF : IsScSmooth R'.U (c.principal f ∘ R') :=
    (((hf.isScSmoothRetractMap hc).comp_isScSmooth R' hR').snd hUd).congr hUd fun _ _ => rfl
  have hS : IsScSmooth R'.U (c.principal s ∘ R') := by
    obtain ⟨hsec, G, hG, hGsm⟩ := hs
    have h0 : A.X.PObj.IsScSmoothOn A.B.toMPolyfold0 s O :=
      (MPolyfold.IsScSmoothOn.comp A.B.isScSmoothMap_oneVal hGsm (mapsTo_univ _ _)).congr
        fun y hy => hG y hy
    have h := h0.smooth c.φ (c.toMChart A.B.continuous) c.isChart hc.toMChart c.φ.source
      c.φ.isOpen_source (fun x hx => ⟨hsub hx, hx⟩)
      (fun x hx => c.mem_source_of_proj (by rw [hsec x (hsub hx)]; exact hx))
    rw [c.φ.image_source] at h
    have h' : IsScSmoothRetractMap c.φ.model.E c.φ.model.C c.φ.model.O (c.φ.model.E.prod c.F)
        (c.φ.model.C ×ˢ univ) c.K (fun z => (z, c.principal s z)) :=
      h.congr fun z hz => apply_localSection hsec hsub hz
    exact ((h'.comp_isScSmooth R' hR').snd hUd).congr hUd fun _ _ => rfl
  have hpair := IsScSmooth.scPair hUd R'.isScSmooth (hF.sub hUd hS)
  refine hpair.congr hUd fun u hu => ?_
  have huO : R' u ∈ c.φ.model.O := hR' ▸ R'.mapsTo_retract hu
  change (R' u, c.principal f (R' u) - c.principal s (R' u)) =
    (R' u, c.principal (sectionSubOn f s O) (R' u))
  rw [principal_sectionSubOn hf.1 hs.1 hsub huO]

/-! ### Independence of the chart -/

/-- The derivative of `(f̂ − ŝ) ∘ r` is that of the principal part of `sectionSubOn f s O`
composed with `r` (they agree on `U`). -/
theorem scDeriv_sub_eq_sectionSubOn {f : A.Obj → A.W} (hf : A.B.IsScSmoothSection f)
    {s : A.Obj → A.W} {O : Set A.Obj} (hs : IsScPlusSectionOn A s O)
    {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c) (hsub : c.φ.source ⊆ O)
    {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z ∈ c.U) :
    scDeriv c.U ((fun y => c.principal f y - c.principal s y) ∘ r c.R) z =
      scDeriv c.U (c.principal (sectionSubOn f s O) ∘ r c.R) z := by
  have hUd := c.relOpen.isScDomain
  have h1 : IsSc1 c.U ((fun y => c.principal f y - c.principal s y) ∘ r c.R) :=
    ((isScSmooth_principal_comp_r hf hc).sub hUd (hs.isScSmooth_principal_comp_r hc hsub)).isSc1
  have h2 : IsSc1 c.U (c.principal (sectionSubOn f s O) ∘ r c.R) := by
    have := (isScSmoothRetractMap_sectionSubOn hf hs hc hsub).comp_isScSmooth
      (c.isRetraction.baseRetraction c.relOpen) c.base_retract
    exact ((this.snd hUd).congr hUd fun _ _ => rfl).isSc1
  refine scDeriv_eq_of_eqOn_relOpen c.relOpen h1 h2 subset_rfl subset_rfl (fun u hu => ?_) hz
  have huO : r c.R u ∈ c.φ.model.O := c.r_mem_O hu
  change c.principal f (r c.R u) - c.principal s (r c.R u) =
    c.principal (sectionSubOn f s O) (r c.R u)
  rw [principal_sectionSubOn hf.1 hs.1 hsub huO]

/-- At a zero of the global section `g`, the chart operator `D(ĝ ∘ r)(φ(x)) ∘ Tφ` takes values
in `Φ_x(W_x)` (as `StrongBundleChart.linChart_mem`, for a section sc-smooth in the chart). -/
theorem chartOp_mem_range {g : A.Obj → A.W} (hg : IsSection A.P g)
    {c : StrongBundleChart A.X.PObj A.P}
    (hgc : IsScSmoothRetractMap c.φ.model.E c.φ.model.C c.φ.model.O (c.φ.model.E.prod c.F)
      (c.φ.model.C ×ˢ univ) c.K (fun z => (z, c.principal g z)))
    {x : A.X.PObj.Level 1} (hx : A.X.PObj.levelVal 1 x ∈ c.φ.source)
    (h0 : IsZeroAt A.P g (A.X.PObj.levelVal 1 x)) (α : A.X.PObj.tangentFiber x) :
    chartOp c hx (scDeriv c.U (c.principal g ∘ r c.R) (levelLift c.φ 1 (A.X.PObj.levelVal 1 x))) α
      ∈ LinearMap.range (c.fiberLin hx) := by
  have hUd := c.relOpen.isScDomain
  have hg1 : IsSc1 c.U (c.principal g ∘ r c.R) := by
    have := hgc.comp_isScSmooth (c.isRetraction.baseRetraction c.relOpen) c.base_retract
    exact ((this.snd hUd).congr hUd fun _ _ => rfl).isSc1
  have ha : c.φ.model.E.toBase 1 (levelLift c.φ 1 (A.X.PObj.levelVal 1 x)) =
      c.φ (A.X.PObj.levelVal 1 x) :=
    A.X.PObj.toBase_levelLift c.isChart hx (levelVal_mem x)
  have hyO : c.φ (A.X.PObj.levelVal 1 x) ∈ c.φ.model.O := c.φ.mapsTo_model _ hx
  have hzO : c.φ.model.E.toBase 1 (levelLift c.φ 1 (A.X.PObj.levelVal 1 x)) ∈ r c.R '' c.U := by
    rw [c.r_image, ha]; exact hyO
  have hρ := rho_scDeriv_comp_r c.relOpen c.isRetraction hg1
    (fun x hx => c.principal_mem_K hg (c.r_image ▸ hx)) hzO
    (by rw [ha]; exact (c.isZeroAt_iff hg hx).1 h0)
    (tangentFiberEquiv c.isChart hx α : c.φ.model.E 0)
  rw [ρCLM_apply] at hρ
  apply c.mem_range_fiberLin hx
  have hK := c.mem_K_ρ hyO (chartOp c hx (scDeriv c.U (c.principal g ∘ r c.R)
    (levelLift c.φ 1 (A.X.PObj.levelVal 1 x))) α)
  rw [chartOp_apply, ← ha, hρ] at hK
  rw [chartOp_apply, ← ha]
  exact hK

/-- **The intrinsic operator `g'(x) : T_xX → W_x` at a zero does not depend on the chart**, for a
section `g` whose principal parts in the two charts are sc-smooth (Part I's
`StrongBundle.linIntr_chart_independent`, with chart-wise hypotheses only). -/
theorem toIntr_chart_independent {g : A.Obj → A.W} (hg : IsSection A.P g)
    {c c' : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c) (hc' : A.B.IsChart c')
    (hgc : IsScSmoothRetractMap c.φ.model.E c.φ.model.C c.φ.model.O (c.φ.model.E.prod c.F)
      (c.φ.model.C ×ˢ univ) c.K (fun z => (z, c.principal g z)))
    (hgc' : IsScSmoothRetractMap c'.φ.model.E c'.φ.model.C c'.φ.model.O (c'.φ.model.E.prod c'.F)
      (c'.φ.model.C ×ˢ univ) c'.K (fun z => (z, c'.principal g z)))
    {x : A.X.PObj.Level 1} (hx : A.X.PObj.levelVal 1 x ∈ c.φ.source)
    (hx' : A.X.PObj.levelVal 1 x ∈ c'.φ.source) (h0 : IsZeroAt A.P g (A.X.PObj.levelVal 1 x)) :
    toIntr c hx (scDeriv c.U (c.principal g ∘ r c.R) (levelLift c.φ 1 (A.X.PObj.levelVal 1 x))) =
      toIntr c' hx' (scDeriv c'.U (c'.principal g ∘ r c'.R)
        (levelLift c'.φ 1 (A.X.PObj.levelVal 1 x))) := by
  set y := A.X.PObj.levelVal 1 x with hy
  set a := levelLift c.φ 1 y with hadef
  set a' := levelLift c'.φ 1 y with ha'def
  have ha : c.φ.model.E.toBase 1 a = c.φ y :=
    A.X.PObj.toBase_levelLift c.isChart hx (levelVal_mem x)
  have ha' : c'.φ.model.E.toBase 1 a' = c'.φ y :=
    A.X.PObj.toBase_levelLift c'.isChart hx' (levelVal_mem x)
  have hyO : c.φ y ∈ c.φ.model.O := c.φ.mapsTo_model _ hx
  have hzO : c.φ.model.E.toBase 1 a ∈ r c.R '' c.U := by rw [c.r_image, ha]; exact hyO
  have hzU : c.φ.model.E.toBase 1 a ∈ c.U := mem_U_of_mem_O c.isRetraction hzO
  have hzOO : c.φ.model.E.toBase 1 a ∈ c.φ.model.O := by rw [ha]; exact hyO
  have hzV' : c.φ.symm (c.φ.model.E.toBase 1 a) ∈ c'.φ.source := by
    rw [ha, c.φ.symm_apply_apply hx]; exact hx'
  obtain ⟨Rw, hRw, ⟨W, hWo, hW⟩, key⟩ := linAt_chart_change_key c c' hg
    (StrongBundle.IsChart.transition_isScSmoothRetractMap hc hc') hgc hgc' hx hx' h0 ha ha'
    hzU hzOO hzV'
  have htrans : ∀ α : A.X.PObj.tangentFiber x,
      (tangentFiberEquiv c'.isChart hx' α : c'.φ.model.E 0) =
        scDeriv Rw.U (c.φ.transition c'.φ ∘ Rw) a (tangentFiberEquiv c.isChart hx α) := by
    intro α
    rw [tangentFiberEquiv_eq_transition c.isChart hx c'.isChart hx' α]
    set v := tangentFiberEquiv c.isChart hx α
    change transitionCLM c.isChart hx c'.isChart hx' v = _
    have hspec := transitionCLM_spec c.isChart hx c'.isChart hx' v.2
    have hp : ((a, (v : c.φ.model.E 0)) : c.φ.model.E.tangent 0) ∈
        retractTangent c.φ.model.E c.φ.model.C (c.φ.overlap c'.φ) := by
      rw [hW, retractTangent_inter_isOpen c.φ.model.isScRetract hWo]
      refine ⟨(mem_tangentFiberModel c.isChart hx).1 v.2, ?_, mem_univ _⟩
      change c.φ.model.E.toBase 1 a ∈ W
      have : c.φ y ∈ c.φ.overlap c'.φ := c.φ.mem_overlap c'.φ hx hx'
      rw [hW] at this
      rw [ha]; exact this.2
    have happ := retractTangentMap_apply ((c.isChart.compatible c'.isChart (P := A.X.PObj)).1)
      Rw hRw hp
    rw [happ] at hspec
    exact (congrArg Prod.snd hspec).symm
  have hr := chartOp_mem_range hg hgc hx h0
  have hr' := chartOp_mem_range hg hgc' hx' h0
  refine LinearMap.ext fun α => c'.fiberLin_injective hx' ?_
  rw [fiberLin_toIntr c' hx' hr', ← c.transitionFiberCLM_fiberLin c' hx hx' ha hzOO hzV',
    fiberLin_toIntr c hx hr, chartOp_apply, chartOp_apply, htrans α]
  exact (key _).symm

/-- `ŝ(φ(x)) = f̂(φ(x))` iff `s(x) = f(x)`, in a chart with domain in the domain of `s`. -/
theorem principal_eq_iff {f s : A.Obj → A.W} (hf : IsSection A.P f) {O : Set A.Obj}
    (hsec : ∀ y ∈ O, A.P (s y) = y) {c : StrongBundleChart A.X.PObj A.P}
    (hsub : c.φ.source ⊆ O) {y : A.Obj} (hy : y ∈ c.φ.source) :
    c.principal s (c.φ y) = c.principal f (c.φ y) ↔ s y = f y := by
  have hyO : c.φ y ∈ c.φ.model.O := c.φ.mapsTo_model _ hy
  have e1 := apply_localSection hsec hsub hyO
  have e2 := c.apply_section hf hyO
  rw [c.φ.symm_apply_apply hy] at e1 e2
  constructor
  · intro h
    refine c.toPartialEquiv.injOn (c.mem_source_of_proj (by rw [hsec y (hsub hy)]; exact hy))
      (c.mem_source_of_proj (by rw [hf y]; exact hy)) ?_
    rw [e1, e2, h]
  · intro h
    have := congrArg (fun w => (c w).2) h
    simp only [e1, e2] at this
    exact this

/-- **Chart independence of the formal sum**: for one local section structure `(sᵢ, σᵢ)` on `O`
and two charts of `P` with domains in `O`, the formal sums in `GrF(x)` agree. -/
theorem linSumIntr_chart_independent {f : A.Obj → A.W} (hf : A.B.IsScSmoothSection f)
    {Λ : A.W → ℚ≥0} {O : Set A.Obj} {k : ℕ} {s : Fin k → A.Obj → A.W} {σ : Fin k → ℚ≥0}
    (hs : IsLocalRepOn A Λ O s σ) {c c' : StrongBundleChart A.X.PObj A.P}
    (hc : A.B.IsChart c) (hc' : A.B.IsChart c') (hsub : c.φ.source ⊆ O)
    (hsub' : c'.φ.source ⊆ O) {x : A.X.PObj.Level 1}
    (hx : A.X.PObj.levelVal 1 x ∈ c.φ.source) (hx' : A.X.PObj.levelVal 1 x ∈ c'.φ.source) :
    linSumIntr c hx f s σ = linSumIntr c' hx' f s σ := by
  classical
  set y := A.X.PObj.levelVal 1 x with hy
  have ha : c.φ.model.E.toBase 1 (levelLift c.φ 1 y) = c.φ y :=
    A.X.PObj.toBase_levelLift c.isChart hx (levelVal_mem x)
  have ha' : c'.φ.model.E.toBase 1 (levelLift c'.φ 1 y) = c'.φ y :=
    A.X.PObj.toBase_levelLift c'.isChart hx' (levelVal_mem x)
  have hzU : c.φ.model.E.toBase 1 (levelLift c.φ 1 y) ∈ c.U := by
    rw [ha]; exact mem_U_of_mem_O c.isRetraction (c.r_image ▸ c.φ.mapsTo_model _ hx)
  have hzU' : c'.φ.model.E.toBase 1 (levelLift c'.φ 1 y) ∈ c'.U := by
    rw [ha']; exact mem_U_of_mem_O c'.isRetraction (c'.r_image ▸ c'.φ.mapsTo_model _ hx')
  unfold linSumIntr linSumModelMap
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsec := (hs.2.1 i).1
  have hcond : c.principal (s i) (c.φ.model.E.toBase 1 (levelLift c.φ 1 y)) =
      c.principal f (c.φ.model.E.toBase 1 (levelLift c.φ 1 y)) ↔ s i y = f y := by
    rw [ha]; exact principal_eq_iff hf.1 hsec hsub hx
  have hcond' : c'.principal (s i) (c'.φ.model.E.toBase 1 (levelLift c'.φ 1 y)) =
      c'.principal f (c'.φ.model.E.toBase 1 (levelLift c'.φ 1 y)) ↔ s i y = f y := by
    rw [ha']; exact principal_eq_iff hf.1 hsec hsub' hx'
  by_cases h : s i y = f y
  · rw [if_pos (hcond.2 h), if_pos (hcond'.2 h)]
    congr 1
    rw [scDeriv_sub_eq_sectionSubOn hf (hs.2.1 i) hc hsub hzU,
      scDeriv_sub_eq_sectionSubOn hf (hs.2.1 i) hc' hsub' hzU']
    refine toIntr_chart_independent (isSection_sectionSubOn hf.1 O) hc hc'
      (isScSmoothRetractMap_sectionSubOn hf (hs.2.1 i) hc hsub)
      (isScSmoothRetractMap_sectionSubOn hf (hs.2.1 i) hc' hsub') hx hx' ?_
    -- `f − s` vanishes at `y`
    have hyO : y ∈ O := hsub hx
    have hcy : c.principal (sectionSubOn f (s i) O) (c.φ y) = 0 := by
      rw [principal_sectionSubOn hf.1 hsec hsub (c.φ.mapsTo_model _ hx),
        (principal_eq_iff hf.1 hsec hsub hx).2 h, sub_self]
    exact (c.isZeroAt_iff (isSection_sectionSubOn hf.1 O) hx).2 hcy
  · rw [if_neg (mt hcond.1 h), if_neg (mt hcond'.1 h)]

/-- **Theorem 15.1.1 (2017: Theorem 15.1), pp. 684–687, with intrinsic operators**: for a strong
bundle over an ep-groupoid, an sc-Fredholm section functor `f` and two local sc⁺-section
structures `(sᵢ, σᵢ)` on `O`, `(tⱼ, τⱼ)` on `O'` of `Λ` (Definition 13.2.1), the formal sums
`∑_{i : f(x) = sᵢ(x)} σᵢ · (f − sᵢ)'(x)` and `∑_{j : f(x) = tⱼ(x)} τⱼ · (f − tⱼ)'(x)` in
`GrF(x) = (T_xX →ₗ W_x) →₀ ℚ≥0` agree at every `x ∈ X₁` (in particular at every smooth point),
computed through any chart `c` of `P` with domain in `O` and any chart `c'` with domain in `O'`. -/
theorem theorem_15_1_1_intrinsic {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    {Λ : A.W → ℚ≥0} {O O' : Set A.Obj} {k l : ℕ} {s : Fin k → A.Obj → A.W}
    {σ : Fin k → ℚ≥0} {t : Fin l → A.Obj → A.W} {τ : Fin l → ℚ≥0}
    (hs : IsLocalRepOn A Λ O s σ) (ht : IsLocalRepOn A Λ O' t τ) (hO : IsOpen O)
    (hO' : IsOpen O') {c c' : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c)
    (hc' : A.B.IsChart c') (hsub : c.φ.source ⊆ O) (hsub' : c'.φ.source ⊆ O')
    {x : A.X.PObj.Level 1} (hx : A.X.PObj.levelVal 1 x ∈ c.φ.source)
    (hx' : A.X.PObj.levelVal 1 x ∈ c'.φ.source) :
    linSumIntr c hx f s σ = linSumIntr c' hx' f t τ := by
  obtain ⟨⟨hsm, -⟩, -⟩ := hf
  -- a chart `c''` around `x` with domain in `O ∩ O'`
  set y := A.X.PObj.levelVal 1 x
  have hso : IsOpen (c.φ.source ∩ (O ∩ O')) := c.φ.isOpen_source.inter (hO.inter hO')
  set c'' := c.restrict inter_subset_left hso
  have hc'' : A.B.IsChart c'' := hc.restrict inter_subset_left hso
  have hsub'' : c''.φ.source ⊆ O ∩ O' := inter_subset_right
  have hx'' : y ∈ c''.φ.source := ⟨hx, hsub hx, hsub' hx'⟩
  rw [linSumIntr_chart_independent hsm hs hc hc'' hsub (fun z hz => (hsub'' hz).1) hx hx'',
    linSumIntr_eq_of_isLocalRepOn hsm hs ht hc'' hsub'' hx'',
    linSumIntr_chart_independent hsm ht hc'' hc' (fun z hz => (hsub'' hz).2) hsub' hx'' hx']

/-! ### Definition 15.1.7 -/

/-- The data computing `T(f,Λ)(x)`: a local section structure of `Λ` on an open `O` and a strong
bundle chart of `P` around `x` with domain in `O`. -/
structure LocalLinData (A : SEP.{u}) (Λ : A.W → ℚ≥0) (x : A.X.PObj.Level 1) where
  /-- The domain of the local section structure. -/
  O : Set A.Obj
  isOpen : IsOpen O
  /-- The number of branches. -/
  k : ℕ
  /-- The branches. -/
  s : Fin k → A.Obj → A.W
  /-- The weights. -/
  σ : Fin k → ℚ≥0
  rep : IsLocalRepOn A Λ O s σ
  /-- The chart. -/
  c : StrongBundleChart A.X.PObj A.P
  isChart : A.B.IsChart c
  sub : c.φ.source ⊆ O
  mem : A.X.PObj.levelVal 1 x ∈ c.φ.source

/-- The formal sum of the data. -/
def LocalLinData.sum {Λ : A.W → ℚ≥0} {x : A.X.PObj.Level 1} (d : LocalLinData A Λ x)
    (f : A.Obj → A.W) : GrF x :=
  linSumIntr d.c d.mem f d.s d.σ

/-- **Theorem 15.1.1 for the data**: any two data give the same formal sum. -/
theorem LocalLinData.sum_eq {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    {Λ : A.W → ℚ≥0} {x : A.X.PObj.Level 1} (d d' : LocalLinData A Λ x) : d.sum f = d'.sum f :=
  theorem_15_1_1_intrinsic hf d.rep d'.rep d.isOpen d'.isOpen d.isChart d'.isChart d.sub d'.sub
    d.mem d'.mem

/-- For an sc⁺-multisection, data exist at every `x ∈ X₁`. -/
theorem nonempty_localLinData {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ)
    (x : A.X.PObj.Level 1) : Nonempty (LocalLinData A Λ x) := by
  obtain ⟨O, k, s, σ, c, hO, -, hrep, hc, hx, hsub⟩ :=
    exists_chart_isLocalRepOn hΛ (A.X.PObj.levelVal 1 x)
  exact ⟨⟨O, hO, k, s, σ, hrep, c, hc, hsub, hx⟩⟩

open Classical in
/-- **Definition 15.1.7 (2017: Definition 15.1), p. 687**: the linearization
`T(f,Λ)(x) ∈ GrF(x)` of `Λ ∘ f` at `x ∈ X₁`: the formal sum
`∑_{i : f(x) = sᵢ(x)} σᵢ · (f − sᵢ)'(x)` of any local section structure (Theorem 15.1.1:
`linearization_eq`), `0` if there is none. -/
def linearization (f : A.Obj → A.W) (Λ : A.W → ℚ≥0) (x : A.X.PObj.Level 1) : GrF x :=
  if h : Nonempty (LocalLinData A Λ x) then h.some.sum f else 0

/-- **Theorem 15.1.1 (2)**: `T(f,Λ)(x)` is the formal sum of any local section structure of `Λ`
around `x`, read through any chart of `P` with domain in its domain. -/
theorem linearization_eq {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    {Λ : A.W → ℚ≥0} {x : A.X.PObj.Level 1} (d : LocalLinData A Λ x) :
    linearization f Λ x = d.sum f := by
  rw [linearization, dif_pos ⟨d⟩]
  exact LocalLinData.sum_eq hf _ d

/-- **Theorem 15.1.1 (1) and Remark 15.1.2**: `T(f,Λ)(x) = 0` where `Λ(f(x)) = 0`
(`x ∉ supp(Λ ∘ f)`): the formal sum of (2) is empty (positive weights). -/
theorem linearization_eq_zero {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    {Λ : A.W → ℚ≥0} {x : A.X.PObj.Level 1} (h0 : Λ (f (A.X.PObj.levelVal 1 x)) = 0) :
    linearization f Λ x = 0 := by
  classical
  rw [linearization]
  split_ifs with h
  · set d := h.some
    set y := A.X.PObj.levelVal 1 x
    have hsec : IsSection A.P f := hf.1.1.1
    have hyO : d.c.φ y ∈ d.c.φ.model.O := d.c.φ.mapsTo_model _ d.mem
    have ha : d.c.φ.model.E.toBase 1 (levelLift d.c.φ 1 y) = d.c.φ y :=
      A.X.PObj.toBase_levelLift d.c.isChart d.mem (levelVal_mem x)
    have hK : (d.c.φ y, d.c.principal f (d.c.φ y)) ∈ d.c.K := d.c.principal_mem_K hsec hyO
    have hw : d.c.toPartialEquiv.symm (d.c.φ y, d.c.principal f (d.c.φ y)) = f y := by
      rw [← d.c.apply_section' hsec d.mem]
      exact d.c.toPartialEquiv.left_inv (d.c.mem_source_of_proj (by rw [hsec]; exact d.mem))
    have hcount := d.rep.count_eq d.sub hyO (d.c.principal f (d.c.φ y))
    rw [if_pos hK, hw, h0] at hcount
    have hnone : ∀ i, d.c.principal (d.s i) (d.c.φ y) ≠ d.c.principal f (d.c.φ y) :=
      fun i hi => by
        have := (Finset.sum_eq_zero_iff.1 hcount) i (Finset.mem_univ i)
        rw [if_pos hi] at this
        exact (d.rep.1 i).ne' this
    change linSumModelMap _ _ _ _ _ _ _ = 0
    unfold linSumModelMap
    refine Finset.sum_eq_zero fun i _ => if_neg ?_
    rw [ha]; exact hnone i
  · rfl

end SBLocalization

end Polyfold
