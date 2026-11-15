import Polyfold.Chapter15.RelativeSeedFamilies
import Polyfold.Chapter15.GeneralPositionGoodSystem

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, proof of
**Theorem 15.3.9** (Transversal Extension Theorem; 2017: Theorem 15.5), steps (c)–(d),
pp. 698–699: the seeds of the local constructions relative to `Λ₀`.

# The seeds relative to `Λ₀`

## The text, paraphrased

At a point `x` of `supp(Λ₀ ∘ f)` the proof "argues as in Theorem 15.3.7": finitely many
sc⁺-sections `s_j`, supported near `x` and small, such that for every branch `s⁰_a` of `Λ₀`
through `f(x)` the images `(f − s⁰_a)'(x)(T^R_xX)` and the `s_j(x)` span `W_x`; this persists at
the points of `supp(Λ₀ ∘ f)` near `x`.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `exists_isScPlusSection_eqOn_nhds`: a local sc⁺-section on an open `O ∋ x` agrees near `x` with
  a global sc⁺-section (cut-off by an sc-smooth function equal to `1` near `x`).
* `isScFredholmSectionTame_subSec_univ`: `f − ŝ` is an sc-Fredholm section with tame germ data
  for a global sc⁺-section `ŝ` (Theorem 3.1.18).
* `subDeriv_subSec_univ_eq`, `isParamGP_subSec_iff_onto`: in a chart inside the set where
  `ŝ = s⁰`, Part I's properties (i)–(ii) for `f − ŝ` and sections `S_j` are the surjectivity of
  `(v, τ) ↦ (f − s⁰)'(y) v + Σ_j τ_j S_j(y)` on `T^R_yX × ℝ^ℓ`.
* `exists_open_onto_branch`: the openness of that surjectivity along `{f = s⁰}` (Part I's
  openness of general position for the parametrized section of `f − ŝ`).
* **`hasLocalParamSeedsRel`**: `HasLocalParamSeedsRel A f Λ₀ N` for tame `X` with sc-smooth bump
  functions, `f` an sc-Fredholm section functor with tame germ data, `Λ₀` an sc⁺-multisection and
  `N` an auxiliary norm.  The seeds are the union over the branches `s⁰_a` through `f(x)` of the
  sections of Part I's `exists_sections_isParamGP` for `f − ŝ_a`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15

variable {A : SEP.{u}}

/-! ### Local sc⁺-sections as germs of global ones -/

/-- **A local sc⁺-section agrees near a point with a global sc⁺-section**: for sc-smooth bump
functions on `X`, an sc⁺-section `s` on the open `O` and `x ∈ O`, there are a global sc⁺-section
`ŝ` and an open `N₁ ∋ x` in `O` with `ŝ = s` on `N₁` (`ŝ = β · s` for an sc-smooth `β` with
support in `O` and `β = 1` near `x`). -/
theorem exists_isScPlusSection_eqOn_nhds (hbump : A.X.PObj.AdmitsBumpFunctions)
    {s : A.Obj → A.W} {O : Set A.Obj} (hO : IsOpen O) (hs : IsScPlusSectionOn A s O)
    (hsec : IsSection A.P s) {x : A.Obj} (hx : x ∈ O) :
    ∃ ŝ : A.Obj → A.W, A.B.IsScPlusSection ŝ ∧ ∃ N₁ : Set A.Obj, IsOpen N₁ ∧ x ∈ N₁ ∧
      N₁ ⊆ O ∧ EqOn ŝ s N₁ := by
  obtain ⟨β₀, hβ₀, hβ₀x, hβ₀s⟩ := hbump x O hO hx
  have hβ₀c : Continuous β₀ := continuousOn_univ.1 hβ₀.continuousOn
  have hpos : 0 < |β₀ x| := abs_pos.2 hβ₀x
  let b : ContDiffBump (β₀ x) := ⟨|β₀ x| / 3, |β₀ x| / 2, by positivity, by linarith⟩
  set β : A.Obj → ℝ := (b : ℝ → ℝ) ∘ β₀ with hβdef
  have hβ : A.X.PObj.IsScSmoothMap realPolyfold β := hβ₀.comp_contDiff b.contDiff
  have hβsupp : tsupport β ⊆ O := by
    refine (closure_mono fun y hy => ?_).trans hβ₀s
    intro h0
    apply hy
    change b (β₀ y) = 0
    rw [h0]
    refine b.zero_of_le_dist ?_
    rw [Real.dist_eq, zero_sub, abs_neg]
    change |β₀ x| / 2 ≤ |β₀ x|
    linarith
  set N₁ : Set A.Obj := O ∩ β₀ ⁻¹' Metric.ball (β₀ x) (|β₀ x| / 3) with hN₁def
  have hN₁ : IsOpen N₁ := hO.inter (Metric.isOpen_ball.preimage hβ₀c)
  have hβ1 : ∀ y ∈ N₁, β y = 1 := fun y hy =>
    b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy.2)
  refine ⟨Polyfold.sectionSmul A.P β s, ?_, N₁, hN₁,
    ⟨hx, Metric.mem_ball_self (by positivity)⟩, inter_subset_left, fun y hy => ?_⟩
  · refine StrongBundle.isScPlusSection_of_locally hsec.sectionSmul fun y₀ => ?_
    by_cases hy₀ : y₀ ∈ O
    · obtain ⟨-, G, hG, hGs⟩ := hs.sectionSmul hO hsec hβ
      exact ⟨O, hO, hy₀, G, hGs, hG⟩
    · have hopen : IsOpen (tsupport β)ᶜ := (isClosed_tsupport β).isOpen_compl
      have h0 : IsScPlusSectionOn A (Polyfold.sectionSmul A.P β s) (tsupport β)ᶜ :=
        (isScPlusSectionOn_fiberZero hopen).congr fun y hy => by
          have hβy : β y = 0 := by
            by_contra h
            exact hy (subset_tsupport β h)
          rw [sectionSmul_apply hsec, hβy, zero_smul]
          rfl
      obtain ⟨-, G, hG, hGs⟩ := h0
      exact ⟨_, hopen, fun h => hy₀ (hβsupp h), G, hGs, hG⟩
  · rw [sectionSmul_apply hsec, hβ1 y hy, one_smul]

/-! ### The section `f − ŝ` for a global sc⁺-section -/

/-- **`f − ŝ` is an sc-Fredholm section with tame germ data**, for `f` one and a global
sc⁺-section `ŝ` (Part I's Theorem 3.1.18). -/
theorem isScFredholmSectionTame_subSec_univ {f : A.Obj → A.W}
    (hft : A.B.IsScFredholmSectionTame f) {ŝ : A.Obj → A.W} (hŝ : A.B.IsScPlusSection ŝ) :
    A.B.IsScFredholmSectionTame (subSec f ŝ univ) := by
  have e : extendZero univ ŝ = ŝ :=
    funext fun y => (extendZero_eqOn (fun y _ => hŝ.1 y) (mem_univ y)).symm
  unfold subSec
  rw [e]
  exact theorem_3_1_18_tame hft (hŝ.smul_left (isScSmoothMap_real_const (-1)))

section Branch

variable {f : A.Obj → A.W} (hft : A.B.IsScFredholmSectionTame f) {s₀ : A.Obj → A.W}
  {O₂ : Set A.Obj} (hs₀ : IsScPlusSectionOn A s₀ O₂) {ŝ : A.Obj → A.W}
  (hŝ : A.B.IsScPlusSection ŝ) {N₁ : Set A.Obj} (hN₁O : N₁ ⊆ O₂) (heq : EqOn ŝ s₀ N₁)

include hft hs₀ hŝ hN₁O heq in
/-- **The chart operator of `((f − ŝ) − 0)'` is that of `(f − s⁰)'`** in a chart inside the set
where `ŝ = s⁰`. -/
theorem subDeriv_subSec_univ_eq {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c)
    (hsub : c.φ.source ⊆ N₁) {z : c.φ.model.E 1} (hzU : c.φ.model.E.toBase 1 z ∈ c.U) :
    subDeriv c (subSec f ŝ univ) (fiberZero A.P) z = subDeriv c f s₀ z := by
  have hg := isScFredholmSectionTame_subSec_univ hft hŝ
  have h1 := isSc1_sub_comp_r hg.isScSmooth (isScPlusSectionOn_fiberZero (A := A) isOpen_univ) hc
    (subset_univ _)
  have h2 := isSc1_sub_comp_r hft.isScSmooth hs₀ hc (hsub.trans hN₁O)
  have hz : z ∈ c.φ.model.E.lvlSet c.U 1 := by rw [ScBanach.mem_lvlSet]; exact hzU
  unfold subDeriv
  refine scDeriv_eq_of_eqOn_relOpen c.relOpen h1 h2 subset_rfl subset_rfl (fun w hw => ?_) hz
  have hwO := c.r_mem_O hw
  have h0 : c.principal (fiberZero A.P) (r c.R w) = 0 :=
    c.snd_fiberZero (c.φ.symm_mapsTo hwO)
  have hp : c.principal ŝ (r c.R w) = c.principal s₀ (r c.R w) := by
    unfold StrongBundleChart.principal
    rw [heq (hsub (c.φ.symm_mapsTo hwO))]
  change c.principal (subSec f ŝ univ) (r c.R w) - c.principal (fiberZero A.P) (r c.R w) =
    c.principal f (r c.R w) - c.principal s₀ (r c.R w)
  rw [h0, sub_zero, principal_subSec hft.isScSmooth.1 (fun y _ => hŝ.1 y) (subset_univ _) hwO,
    hp]

include hft hs₀ hŝ hN₁O heq in
/-- **Part I's (i)–(ii) for `f − ŝ` are (15.1) for the operator `(f − s⁰)'(y)`**: at a point
`y ∈ X₁` with `f(y) = s⁰(y)`, in a chart `c` centred at `y` inside the set where `ŝ = s⁰`, for
sections `S_j`, `IsParamGP` holds for `f − ŝ` and the `S_j` iff
`(v, τ) ↦ (f − s⁰)'(y) v + Σ_j τ_j S_j(y)` maps `T^R_yX × ℝ^ℓ` onto `W_y`. -/
theorem isParamGP_subSec_iff_onto {ℓ : ℕ} {S : Fin ℓ → A.Obj → A.W}
    (hS : ∀ j, IsSection A.P (S j)) {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c)
    (hsub : c.φ.source ⊆ N₁) {y : A.X.PObj.Level 1} (hy : A.X.PObj.levelVal 1 y ∈ c.φ.source)
    (hφ0 : c.φ (A.X.PObj.levelVal 1 y) = 0)
    (hy0 : f (A.X.PObj.levelVal 1 y) = s₀ (A.X.PObj.levelVal 1 y)) {n : ℕ} {Wq : ScBanach}
    (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq)) :
    c.IsParamGP (subSec f ŝ univ) S T ↔
      ∀ w : A.P ⁻¹' {A.X.PObj.levelVal 1 y}, ∃ v ∈ reducedTangentFiber c.isChart hy T,
        ∃ τ : Fin ℓ → ℝ, toIntr c hy (subDeriv c f s₀
          (levelLift c.φ 1 (A.X.PObj.levelVal 1 y))) v +
            ∑ j, τ j • (⟨S j (A.X.PObj.levelVal 1 y), hS j _⟩ :
              A.P ⁻¹' {A.X.PObj.levelVal 1 y}) = w := by
  have hg := isScFredholmSectionTame_subSec_univ hft hŝ
  have hg0 : subSec f ŝ univ (A.X.PObj.levelVal 1 y) = fiberZero A.P (A.X.PObj.levelVal 1 y) :=
    (isZeroAt_subSec_iff hft.isScSmooth.1 (fun y _ => hŝ.1 y) (mem_univ _)).2
      (hy0.trans (heq (hsub hy)).symm)
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := hφ0 ▸ c.φ.mapsTo_model _ hy
  have hzU : c.φ.model.E.toBase 1 (levelLift c.φ 1 (A.X.PObj.levelVal 1 y)) ∈ c.U := by
    rw [A.X.PObj.toBase_levelLift c.isChart hy (levelVal_mem y), hφ0]
    exact mem_U_of_mem_O c.isRetraction (c.r_image ▸ h0O)
  rw [isParamGP_iff_onto_chart hg hS hc hy hφ0 hg0 T, ← onto_chart_iff hg hS hc hy hφ0 hg0 T,
    subDeriv_subSec_univ_eq hft hs₀ hŝ hN₁O heq hc hsub hzU]

/-- **(15.1) for the operator `(f − s⁰)'(y)` in every tame chart centred at `y` inside `N₁`**,
with the vectors `S_j(y)`. -/
def BranchOnto (f s₀ : A.Obj → A.W) (N₁ : Set A.Obj) {ℓ : ℕ} (S : Fin ℓ → A.Obj → A.W)
    (hS : ∀ j, IsSection A.P (S j)) (y : A.X.PObj.Level 1) : Prop :=
  ∀ (c : StrongBundleChart A.X.PObj A.P), A.B.IsTameChart c → c.φ.source ⊆ N₁ →
    ∀ (hy : A.X.PObj.levelVal 1 y ∈ c.φ.source), c.φ (A.X.PObj.levelVal 1 y) = 0 →
    ∀ (n : ℕ) (Wq : ScBanach) (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq)),
      c.φ.model.C = T 0 ⁻¹' quadrant n Wq 0 →
      ∀ w : A.P ⁻¹' {A.X.PObj.levelVal 1 y}, ∃ v ∈ reducedTangentFiber c.isChart hy T,
        ∃ τ : Fin ℓ → ℝ, toIntr c hy (subDeriv c f s₀
          (levelLift c.φ 1 (A.X.PObj.levelVal 1 y))) v +
            ∑ j, τ j • (⟨S j (A.X.PObj.levelVal 1 y), hS j _⟩ :
              A.P ⁻¹' {A.X.PObj.levelVal 1 y}) = w

set_option maxHeartbeats 800000 in
-- Part I's openness of general position for the parametrized section of `f − ŝ`
include hft hs₀ hŝ hN₁O heq in
/-- **The openness of (15.1) for one branch along `{f = s⁰}`**: if Part I's (i)–(ii) hold at `x`
for `f − ŝ` and global sc⁺-sections `S_j` in a tame chart centred at `x` inside `N₁`, then (15.1)
for `(f − s⁰)'(y)` with the vectors `S_j(y)` holds at every `y` near `x` with `f(y) = s⁰(y)`. -/
theorem exists_open_onto_branch (hX : A.X.IsTame) (hN₁ : IsOpen N₁) {ℓ : ℕ}
    {S : Fin ℓ → A.Obj → A.W} (hS : ∀ j, A.B.IsScPlusSection (S j)) {x : A.Obj}
    (hx0 : f x = s₀ x) {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsTameChart c)
    (hsub : c.φ.source ⊆ N₁) (hxc : x ∈ c.φ.source) (hφ0 : c.φ x = 0) {n : ℕ} {Wq : ScBanach}
    (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant n Wq 0) (hGP : c.IsParamGP (subSec f ŝ univ) S T) :
    ∃ Wa : Set A.Obj, IsOpen Wa ∧ x ∈ Wa ∧ ∀ y : A.X.PObj.Level 1,
      A.X.PObj.levelVal 1 y ∈ Wa → f (A.X.PObj.levelVal 1 y) = s₀ (A.X.PObj.levelVal 1 y) →
        BranchOnto f s₀ N₁ S (fun j => (hS j).1) y := by
  have := MPolyfold.paracompactSpace_prod (rnPolyfold ℓ) A.X.PObj
  have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin ℓ → ℝ) × A.Obj → A.Obj))
    ((rnPolyfold ℓ).prod A.X.PObj) A.B
  have hg := isScFredholmSectionTame_subSec_univ hft hŝ
  have hzg : ∀ y ∈ N₁, f y = s₀ y → IsZeroAt A.P (subSec f ŝ univ) y := fun y hyN hy0 =>
    (isZeroAt_subSec_iff hft.isScSmooth.1 (fun y _ => hŝ.1 y) (mem_univ _)).2
      (hy0.trans (heq hyN).symm)
  have hg0 := hzg x (hsub hxc) hx0
  have hgerm := isGeneralPositionGerm_paramSection_of_isParamGP hg hS hg0 hc hxc hφ0 T hT hGP
  have hzero : ∀ y : A.Obj, IsZeroAt A.P (subSec f ŝ univ) y →
      IsZeroAt (pullbackProj A.P Prod.snd)
        (paramSection (subSec f ŝ univ) hg.isScSmooth.1 S fun i => (hS i).1)
        ((0 : Fin ℓ → ℝ), y) := by
    intro y hy0
    rw [isZeroAt_paramSection_iff]
    change IsZeroAt A.P (paramSlice (subSec f ŝ univ) hg.isScSmooth.1 S (fun i => (hS i).1) 0) y
    rw [paramSlice_zero]
    exact hy0
  obtain ⟨W₀, hW₀o, h0W₀, -, hW₀⟩ := exists_isOpen_isGeneralPositionGerm (prod_rn_isTame hX)
    (theorem_3_1_21_tame hg hS) (hzero _ hg0) hgerm
  refine ⟨(fun y => ((0 : Fin ℓ → ℝ), y)) ⁻¹' W₀ ∩ N₁,
    (hW₀o.preimage (continuous_const.prodMk continuous_id)).inter hN₁, ⟨h0W₀, hsub hxc⟩,
    fun y hyW hy0 c' hc' hsub' hy hφ0' n' Wq' T' hT' => ?_⟩
  have hgy := hzg _ hyW.2 hy0
  obtain ⟨-, hgp, -⟩ := hW₀ _ hyW.1 (hzero _ hgy)
  have hGP' := isParamGP_of_isGeneralPositionGerm hg hS hgy hc' hy hφ0' T' hT' hgp
  exact (isParamGP_subSec_iff_onto hft hs₀ hŝ hN₁O heq (fun j => (hS j).1) hc'.1 hsub' hy hφ0'
    hy0 T').1 hGP'

end Branch

/-! ### The seeds -/

set_option maxHeartbeats 1600000 in
-- the union over the branches of `Λ₀` through `f(x)` of Part I's sections
/-- **The analytic input of the local constructions relative to `Λ₀` holds**
(`HasLocalParamSeedsRel`): for tame `X` with sc-smooth bump functions, `f` an sc-Fredholm section
functor with tame germ data, `Λ₀` an sc⁺-multisection and `N` an auxiliary norm.  *Proof*: around
`x ∈ supp(Λ₀ ∘ f)` take a local representation `(s⁰_a, σ⁰_a)` of `Λ₀` and global sc⁺-sections
`ŝ_a` equal to `s⁰_a` near `x`; for each branch through `f(x)`, Part I gives sections with
(i)–(ii) for `f − ŝ_a` at `x`; (i)–(ii) hold for the union of these families, and they are open
along the zeros of `f − ŝ_a`; near `x` every branch through `f(y)` passes through `f(x)`. -/
theorem hasLocalParamSeedsRel (hX : A.X.IsTame) (hbump : A.X.PObj.AdmitsBumpFunctions)
    {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) {Λ₀ : A.W → ℚ≥0} (hΛ₀ : IsScPlusMultisection A Λ₀)
    {N : A.B.One → ℝ} (hN : A.B.IsAuxNorm N) : HasLocalParamSeedsRel A f Λ₀ N := by
  classical
  intro x hx O hO hxO ε hε
  have hsecf : IsSection A.P f := hft.isScSmooth.1
  have hfc : Continuous f := continuousOn_univ.1 hft.isScSmooth.2.continuousOn
  have hxs : x ∈ A.X.PObj.smoothSet := mem_smoothSet_of_pos hft hΛ₀ hx
  obtain ⟨O₂, k₀, s₀', σ₀, hO₂, hxO₂, hrep₀'⟩ := hΛ₀.exists_isLocalRepOn x
  set s₀ : Fin k₀ → A.Obj → A.W := fun a => extendZero O₂ (s₀' a) with hs₀def
  have hs₀ : ∀ a, IsSection A.P (s₀ a) := fun a => isSection_extendZero O₂ _
  have hrep₀ : IsLocalRepOn A Λ₀ O₂ s₀ σ₀ := hrep₀'.extendZero
  have hext : ∀ a, ∃ ŝ : A.Obj → A.W, A.B.IsScPlusSection ŝ ∧ ∃ N₁ : Set A.Obj, IsOpen N₁ ∧
      x ∈ N₁ ∧ N₁ ⊆ O₂ ∧ EqOn ŝ (s₀ a) N₁ := fun a =>
    exists_isScPlusSection_eqOn_nhds hbump hO₂ (hrep₀.2.1 a) (hs₀ a) hxO₂
  choose ŝ hŝ N₁ hN₁ hxN₁ hN₁O heq using hext
  set M : Set A.Obj := O₂ ∩ ⋂ a, N₁ a with hMdef
  have hM : IsOpen M := hO₂.inter (isOpen_iInter_of_finite hN₁)
  have hxM : x ∈ M := ⟨hxO₂, mem_iInter.2 hxN₁⟩
  have hMN : ∀ a, M ⊆ N₁ a := fun a => inter_subset_right.trans (iInter_subset _ a)
  -- a tame chart centred at `x` inside `M`
  obtain ⟨-, c₀, hc₀, hxc₀, hφ0, -⟩ := hft.germTame x hxs
  set c := c₀.restrictInter hM with hcdef
  have hc : A.B.IsTameChart c := hc₀.restrictInter hM
  have hsubM : c.φ.source ⊆ M := c₀.restrictInter_source_subset hM
  have hxc : x ∈ c.φ.source := ⟨hxc₀, hxM⟩
  have hφ0c : c.φ x = 0 := hφ0
  obtain ⟨n, Wq, T, hT⟩ := c.φ.model.isPartialQuadrant
  have ha' : (0 : ℝ) < 2 / ε := div_pos two_pos hε
  -- the pointwise choice for each branch through `f(x)`
  have hpt : ∀ a, ∃ (k : ℕ) (s : Fin k → A.Obj → A.W) (_ : ∀ i, A.B.IsScPlusSection (s i)),
      (∀ i, sectionSupport A.P (s i) ⊆ O) ∧
      (∀ i y (hy : s i y ∈ A.B.oneSet), 2 / ε * N (A.B.oneMk (s i y) hy) ≤ 1) ∧
      (f x = s₀ a x → c.IsParamGP (subSec f (ŝ a) univ) s T) := by
    intro a
    by_cases hfa : f x = s₀ a x
    · have hg := isScFredholmSectionTame_subSec_univ hft (hŝ a)
      have hg0 : IsZeroAt A.P (subSec f (ŝ a) univ) x :=
        (isZeroAt_subSec_iff hsecf (fun y _ => (hŝ a).1 y) (mem_univ _)).2
          (hfa.trans (heq a (hxN₁ a)).symm)
      obtain ⟨k, s, hs, hsupp, hsN, hGP⟩ := exists_sections_isParamGP hbump
        (hN.const_mul ha') hg hg0 hc hxc hφ0c T hT hO hxO
      exact ⟨k, s, hs, hsupp, hsN, fun _ => hGP⟩
    · exact ⟨0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
        fun h => absurd h hfa⟩
  choose k s hs hsupp hsN hGP using hpt
  -- the united family
  set e := Fintype.equivFin (Σ a : Fin k₀, Fin (k a)) with hedef
  set S : Fin (Fintype.card (Σ a : Fin k₀, Fin (k a))) → A.Obj → A.W :=
    fun j => s (e.symm j).1 (e.symm j).2 with hSdef
  have hS : ∀ j, A.B.IsScPlusSection (S j) := fun j => hs _ _
  have hGPS : ∀ a, f x = s₀ a x → c.IsParamGP (subSec f (ŝ a) univ) S T := fun a hfa =>
    (hGP a hfa).comp (fun i => e ⟨a, i⟩) (fun i => by
      change s a i = s (e.symm (e ⟨a, i⟩)).1 (e.symm (e ⟨a, i⟩)).2
      rw [Equiv.symm_apply_apply])
  -- the openness for each branch
  have hopen : ∀ a, ∃ Wa : Set A.Obj, IsOpen Wa ∧ x ∈ Wa ∧ ∀ y : A.X.PObj.Level 1,
      A.X.PObj.levelVal 1 y ∈ Wa →
        f (A.X.PObj.levelVal 1 y) = s₀ a (A.X.PObj.levelVal 1 y) →
          BranchOnto f (s₀ a) (N₁ a) S (fun j => (hS j).1) y := by
    intro a
    by_cases hfa : f x = s₀ a x
    · exact exists_open_onto_branch hft (hrep₀.2.1 a) (hŝ a) (hN₁O a) (heq a) hX (hN₁ a) hS hfa
        hc (hsubM.trans (hMN a)) hxc hφ0c T hT (hGPS a hfa)
    · exact ⟨{y ∈ O₂ | f y ≠ s₀ a y}, isOpen_sep_ne hfc hO₂ (hrep₀.2.1 a).continuousOn,
        ⟨hxO₂, hfa⟩, fun y hy h => absurd h hy.2⟩
  choose Wa hWao hxWa hWa using hopen
  refine ⟨_, S, hS, fun j => hsupp _ _, fun j y => ?_, (⋂ a, Wa a) ∩ M,
    (isOpen_iInter_of_finite hWao).inter hM, ⟨mem_iInter.2 hxWa, hxM⟩, fun y hyW hpos => ?_⟩
  · have h1 := (hS j).mem_oneSet y
    rw [normW_of_mem N h1]
    have h2 := hsN _ _ y h1
    rw [div_mul_eq_mul_div, div_le_one hε] at h2
    linarith
  · have hys : A.X.PObj.levelVal 1 y ∈ A.X.PObj.smoothSet := mem_smoothSet_of_pos hft hΛ₀ hpos
    obtain ⟨-, c₁, hc₁, hyc₁, hφ1, -⟩ := hft.germTame _ hys
    set c' := c₁.restrictInter hM with hc'def
    have hc' : A.B.IsTameChart c' := hc₁.restrictInter hM
    have hsub' : c'.φ.source ⊆ M := c₁.restrictInter_source_subset hM
    have hyc' : A.X.PObj.levelVal 1 y ∈ c'.φ.source := ⟨hyc₁, hyW.2⟩
    have hφ1' : c'.φ (A.X.PObj.levelVal 1 y) = 0 := hφ1
    obtain ⟨n', Wq', T', hT'⟩ := c'.φ.model.isPartialQuadrant
    have hsubO : c'.φ.source ⊆ O₂ := hsub'.trans inter_subset_left
    intro L hL φ hφ hyφ m V Tφ hTφ w
    let d : LocalLinData A Λ₀ y := ⟨O₂, hO₂, k₀, s₀, σ₀, hrep₀, c', hc'.1, hsubO, hyc'⟩
    rw [linearization_eq hf d] at hL
    obtain ⟨a, hay, rfl⟩ := (mem_support_linSumIntr_iff hsecf hrep₀.1
      (fun b => (hrep₀.2.1 b).1) hsubO hyc' L).1 hL
    obtain ⟨u, hu, τ, hτ⟩ := hWa a y (mem_iInter.1 hyW.1 a) hay.symm c' hc'
      (hsub'.trans (hMN a)) hyc' hφ1' n' Wq' T' hT' w
    refine ⟨u, ?_, τ, hτ⟩
    rw [reducedTangentFiber_eq (hφ := hφ) (hx := hyφ) (T := Tφ) (hψ := c'.isChart)
      (hx' := hyc') (T' := T') hTφ hT']
    exact hu

end SBLocalization

end Polyfold
