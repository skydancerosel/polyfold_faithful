import Polyfold.Chapter15.P3W5GA_Seeds
import Polyfold.Chapter15.P3W5GB_ParametricGP

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, proof of
**Theorem 15.3.7** (General Position; 2017: Theorem 15.4), pp. 694–696: the parametrized
reduced surjectivity (15.1) is Part I's properties (i)–(ii) of the proof of Theorem 5.3.10.

# (15.1) and Part I's (i)–(ii)

## The text, paraphrased

At `x ∈ S_f` the proof picks smooth `w_1, …, w_ℓ ∈ W_x` such that `f'(x)(T^R_xX)` and the `w_j`
span `W_x` (15.1), extends them to small sc⁺-sections `s_j`, and uses that (15.1) with the
vectors `s_j(y)` persists at the points `y ∈ S_f` near `x` (by the implicit function theorem).
The text refers to Part I (Theorems 5.3.5, 5.3.10) for these steps.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `linAt_principal_eq_subDeriv`: in a chart of `W`, the chart linearization of `f` is the chart
  operator `D((f̂ − 0̂) ∘ r)` of `(f − 0)'`, the operator of `T(f, Λ₀)`.
* **`isParamOntoVec_iff_isParamGP`** (the bridge): at a zero `x ∈ X₁` of `f`, for global
  sections `s_j` and a chart `c` centred at `x`, (15.1) with the vectors `s_j(x)` holds iff
  Part I's properties (i)–(ii) (`StrongBundleChart.IsParamGP`) hold for `f` and the `s_j` in `c`.
  (i)–(ii) ask for `F'(0, x)` onto with kernel transversal to `ℝ^ℓ ⊕ T^R_xX`, (15.1) asks for
  `F'(0, x)` onto already on `ℝ^ℓ × T^R_xX`; the two are equivalent.
* **`hasPointwiseParamOnto`**: GA's `HasPointwiseParamOnto A f N`, from Part I's
  `exists_sections_isParamGP` (bump functions, auxiliary norm `(2/ε)·N`) and the bridge.
* **`hasParamOntoOpen`**: GA's `HasParamOntoOpen A f` for tame `X`, from the bridge, Part I's
  `isGeneralPositionGerm_paramSection_of_isParamGP` (general position of the parametrized
  section `F(t, y) = f(y) + Σ_j t_j s_j(y)` at `(0, x)`), Part I's openness of general position
  along the solution set (`exists_isOpen_isGeneralPositionGerm`, on the tame `ℝ^ℓ × X`), and
  Part I's converse `isParamGP_of_isGeneralPositionGerm` at the zeros `(0, y)` near `(0, x)`.
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

/-! ### The chart readings -/

/-- **The chart linearization of `f` is the chart operator of `(f − 0)'`**: in a chart `c` of
`W`, `D(f̂ ∘ r)(z) = D((f̂ − 0̂) ∘ r)(z)` on `T_zO`. -/
theorem linAt_principal_eq_subDeriv {f : A.Obj → A.W} (hf : A.B.IsScSmoothSection f)
    {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c) {z : c.φ.model.E 1}
    (hzU : c.φ.model.E.toBase 1 z ∈ c.U) (u : ↥(rangeS (scDeriv c.U (r c.R) z))) :
    linAt c.U c.R (c.principal f) z u = subDeriv c f (fiberZero A.P) z u := by
  rw [linAt_apply]
  have h1 : IsSc1 c.U (c.principal f ∘ r c.R) := hf.isSc1_principal_comp_r hc
  have h2 := isSc1_sub_comp_r hf (isScPlusSectionOn_fiberZero (A := A) isOpen_univ) hc
    (subset_univ _)
  have hz : z ∈ c.φ.model.E.lvlSet c.U 1 := by rw [ScBanach.mem_lvlSet]; exact hzU
  have e := scDeriv_eq_of_eqOn_relOpen c.relOpen h1 h2 subset_rfl subset_rfl (fun w hw => by
    change c.principal f (r c.R w) =
      c.principal f (r c.R w) - c.principal (fiberZero A.P) (r c.R w)
    have h0 : c.principal (fiberZero A.P) (r c.R w) = 0 :=
      c.snd_fiberZero (c.φ.symm_mapsTo (c.r_mem_O hw))
    rw [h0, sub_zero]) hz
  exact congrArg (fun L : c.φ.model.E 0 →L[ℝ] c.F 0 => L u) e

/-- The operator `(f − 0)'(x)` of `T(f, Λ₀)(x)`, read in a chart `c` around `x`, lies in the
support of `T(f, Λ₀)(x)` at a zero `x` of `f`, and it is the only operator there. -/
theorem mem_support_linearization_zero_iff {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) {c : StrongBundleChart A.X.PObj A.P}
    (hc : A.B.IsChart c) {x : A.X.PObj.Level 1} (hx : A.X.PObj.levelVal 1 x ∈ c.φ.source)
    (hx0 : f (A.X.PObj.levelVal 1 x) = fiberZero A.P (A.X.PObj.levelVal 1 x))
    (L : A.X.PObj.tangentFiber x →ₗ[ℝ] A.P ⁻¹' {A.X.PObj.levelVal 1 x}) :
    L ∈ (linearization f (zeroMultisection A) x).support ↔
      toIntr c hx (subDeriv c f (fiberZero A.P)
        (levelLift c.φ 1 (A.X.PObj.levelVal 1 x))) = L := by
  let d : LocalLinData A (zeroMultisection A) x :=
    ⟨univ, isOpen_univ, 1, fun _ => fiberZero A.P, fun _ => 1,
      isLocalRepOn_zeroMultisection isOpen_univ, c, hc, subset_univ _, hx⟩
  have key := mem_support_linSumIntr_iff (k := 1) (s := fun _ => fiberZero A.P)
    (σ := fun _ => (1 : ℚ≥0)) hf.1.1.1 (fun _ => one_pos)
    (fun _ z _ => isSection_fiberZero (P := A.P) z) (subset_univ _) hx L
  rw [linearization_eq hf d]
  refine key.trans ⟨fun ⟨_, _, hL⟩ => hL, fun hL => ⟨0, hx0.symm, hL⟩⟩

/-! ### The bridge -/

section Bridge

variable {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
  (hft : A.B.IsScFredholmSectionTame f) {ℓ : ℕ} {s : Fin ℓ → A.Obj → A.W}
  (hsec : ∀ j, IsSection A.P (s j)) {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c)
  {x : A.X.PObj.Level 1} (hx : A.X.PObj.levelVal 1 x ∈ c.φ.source)
  (hφ0 : c.φ (A.X.PObj.levelVal 1 x) = 0)
  (hx0 : f (A.X.PObj.levelVal 1 x) = fiberZero A.P (A.X.PObj.levelVal 1 x)) {n : ℕ}
  {Wq : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))

include hx hφ0 in
/-- The level-`1` point over `φ(x) = 0` is `0`. -/
theorem levelLift_eq_zero_of_centred :
    levelLift c.φ 1 (A.X.PObj.levelVal 1 x) = 0 := by
  apply c.φ.model.E.toBase_injective 1
  rw [A.X.PObj.toBase_levelLift c.isChart hx (levelVal_mem x), hφ0, map_zero]

include hc hft hφ0 hx0 in
/-- **The chart reading of (15.1)** in the chart `c` centred at `x`, with the vectors `s_j(x)`:
`(v, τ) ↦ D((f̂ − 0̂) ∘ r)(0) v + Σ_j τ_j ŝ_j(0)` maps `T_0O ∩ T^R_0O × ℝ^ℓ` onto `K_0`. -/
theorem onto_chart_iff :
    (∀ w : A.P ⁻¹' {A.X.PObj.levelVal 1 x}, ∃ v ∈ reducedTangentFiber c.isChart hx T,
      ∃ τ : Fin ℓ → ℝ, toIntr c hx (subDeriv c f (fiberZero A.P)
        (levelLift c.φ 1 (A.X.PObj.levelVal 1 x))) v +
          ∑ j, τ j • (⟨s j (A.X.PObj.levelVal 1 x), hsec j _⟩ :
            A.P ⁻¹' {A.X.PObj.levelVal 1 x}) = w) ↔
    (∀ k, ((0 : c.φ.model.E 0), k) ∈ c.K →
      ∃ (u : ↥(rangeS (scDeriv c.U (r c.R) 0))), (u : c.φ.model.E 0) ∈ minimalSubspaceWith T 0 ∧
        ∃ τ : Fin ℓ → ℝ, linAt c.U c.R (c.principal f) 0 u +
          ∑ j, τ j • c.principal (s j) 0 = k) := by
  classical
  have hz0 := levelLift_eq_zero_of_centred hx hφ0
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := hφ0 ▸ c.φ.mapsTo_model _ hx
  have h0U : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) ∈ c.U := by
    rw [map_zero]; exact mem_U_of_mem_O c.isRetraction (c.r_image ▸ h0O)
  have hs0 : IsScPlusSectionOn A (fiberZero A.P) univ := isScPlusSectionOn_fiberZero isOpen_univ
  have hcol : ∀ j, c.principal (s j) 0 = c.fiberLin hx
      ⟨s j (A.X.PObj.levelVal 1 x), hsec j _⟩ := fun j => by
    have e := principal_eq_fiberLin hx (hsec j (A.X.PObj.levelVal 1 x))
    rwa [hφ0] at e
  have hfl : ∀ α : A.X.PObj.tangentFiber x,
      c.fiberLin hx (toIntr c hx (subDeriv c f (fiberZero A.P)
        (levelLift c.φ 1 (A.X.PObj.levelVal 1 x))) α) =
        subDeriv c f (fiberZero A.P) 0 (tangentFiberEquiv c.isChart hx α : c.φ.model.E 0) :=
    fun α => by
      rw [fiberLin_toIntr_subDeriv hft.isScSmooth hs0 hc (subset_univ _) hx (hx0.trans rfl), hz0]
  have hrng : ∀ v : A.X.PObj.tangentFiber x,
      (tangentFiberEquiv c.isChart hx v : c.φ.model.E 0) ∈ rangeS (scDeriv c.U (r c.R) 0) :=
    fun v => by
      have := (c.mem_tangentFiberModel_iff_rangeS hx _).1 (tangentFiberEquiv c.isChart hx v).2
      rw [hz0] at this
      exact this
  have hred : ∀ v : A.X.PObj.tangentFiber x, v ∈ reducedTangentFiber c.isChart hx T ↔
      (tangentFiberEquiv c.isChart hx v : c.φ.model.E 0) ∈ minimalSubspaceWith T 0 := by
    intro v
    rw [reducedTangentFiber, Submodule.mem_comap, fiberCoord_eq_coe, hφ0]
  constructor
  · intro H k hk
    have hk' : (c.φ (A.X.PObj.levelVal 1 x), k) ∈ c.K := by rw [hφ0]; exact hk
    obtain ⟨w, rfl⟩ := c.mem_range_fiberLin hx hk'
    obtain ⟨v, hv, τ, he⟩ := H w
    refine ⟨⟨_, hrng v⟩, (hred v).1 hv, τ, ?_⟩
    rw [linAt_principal_eq_subDeriv hft.isScSmooth hc h0U]
    have := congrArg (c.fiberLin hx) he
    rw [map_add, map_sum] at this
    simp only [map_smul] at this
    rw [hfl] at this
    rw [← this]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [hcol j]
  · intro H w
    have hk : ((0 : c.φ.model.E 0), c.fiberLin hx w) ∈ c.K := by
      rw [← hφ0, ← c.apply_fiberLin hx w, ← c.image_source]
      exact ⟨_, c.fiberLin_src hx w, rfl⟩
    obtain ⟨u, hu, τ, he⟩ := H _ hk
    have huT : (u : c.φ.model.E 0) ∈ tangentFiberModel c.isChart hx :=
      (c.mem_tangentFiberModel_iff_rangeS hx _).2 (by rw [hz0]; exact u.2)
    set α := (tangentFiberEquiv c.isChart hx).symm ⟨u, huT⟩ with hα
    have hαu : (tangentFiberEquiv c.isChart hx α : c.φ.model.E 0) = u := by
      rw [hα, Equiv.apply_symm_apply]
    refine ⟨α, (hred α).2 (by rw [hαu]; exact hu), τ, c.fiberLin_injective hx ?_⟩
    rw [map_add, map_sum]
    simp only [map_smul]
    rw [hfl, hαu, ← he, linAt_principal_eq_subDeriv hft.isScSmooth hc h0U]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [hcol j]

include hc hft hφ0 hx0 hx hsec in
/-- **Part I's (i)–(ii) in the chart `c` are (15.1) read in `c`**: `IsParamGP` (`F'(0, x)` onto,
kernel transversal to `ℝ^ℓ ⊕ T^R`) is equivalent to `F'(0, x)` onto on `ℝ^ℓ × T^R`. -/
theorem isParamGP_iff_onto_chart :
    c.IsParamGP f s T ↔
    (∀ k, ((0 : c.φ.model.E 0), k) ∈ c.K →
      ∃ (u : ↥(rangeS (scDeriv c.U (r c.R) 0))), (u : c.φ.model.E 0) ∈ minimalSubspaceWith T 0 ∧
        ∃ τ : Fin ℓ → ℝ, linAt c.U c.R (c.principal f) 0 u +
          ∑ j, τ j • c.principal (s j) 0 = k) := by
  classical
  have hz0 := levelLift_eq_zero_of_centred hx hφ0
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := hφ0 ▸ c.φ.mapsTo_model _ hx
  have h0K : ∀ u : ↥(rangeS (scDeriv c.U (r c.R) 0)),
      ((0 : c.φ.model.E 0), linAt c.U c.R (c.principal f) 0 u) ∈ c.K := by
    intro u
    -- the chart linearization takes values in the fibre `K_0`
    have hfl0 : linAt c.U c.R (c.principal f) 0 u ∈ LinearMap.range (c.fiberLin hx) := by
      have hs0 : IsScPlusSectionOn A (fiberZero A.P) univ :=
        isScPlusSectionOn_fiberZero isOpen_univ
      have huT : (u : c.φ.model.E 0) ∈ tangentFiberModel c.isChart hx :=
        (c.mem_tangentFiberModel_iff_rangeS hx _).2 (by rw [hz0]; exact u.2)
      set α := (tangentFiberEquiv c.isChart hx).symm ⟨u, huT⟩ with hα
      have hαu : (tangentFiberEquiv c.isChart hx α : c.φ.model.E 0) = u := by
        rw [hα, Equiv.apply_symm_apply]
      refine ⟨toIntr c hx (subDeriv c f (fiberZero A.P)
        (levelLift c.φ 1 (A.X.PObj.levelVal 1 x))) α, ?_⟩
      rw [fiberLin_toIntr_subDeriv hft.isScSmooth hs0 hc (subset_univ _) hx (hx0.trans rfl), hz0,
        hαu, linAt_principal_eq_subDeriv hft.isScSmooth hc (by
          rw [map_zero]; exact mem_U_of_mem_O c.isRetraction (c.r_image ▸ h0O))]
    obtain ⟨w, hw⟩ := hfl0
    rw [← hw, ← hφ0, ← c.apply_fiberLin hx w, ← c.image_source]
    exact ⟨_, c.fiberLin_src hx w, rfl⟩
  constructor
  · rintro ⟨h1, h2⟩ k hk
    obtain ⟨u, a, hua⟩ := h1 k hk
    obtain ⟨u', a', hu'a', hmin⟩ := h2 u
    refine ⟨u - u', hmin, a - a', ?_⟩
    rw [map_sub, ← hua]
    have e : ∑ j, (a - a') j • c.principal (s j) 0 =
        ∑ j, a j • c.principal (s j) 0 - ∑ j, a' j • c.principal (s j) 0 := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [Pi.sub_apply, sub_smul]
    rw [e]
    have e' : linAt c.U c.R (c.principal f) 0 u' = -∑ j, a' j • c.principal (s j) 0 :=
      eq_neg_of_add_eq_zero_left hu'a'
    rw [e']
    abel
  · intro H
    refine ⟨fun k hk => ?_, fun w => ?_⟩
    · obtain ⟨u, -, τ, he⟩ := H k hk
      exact ⟨u, τ, he⟩
    · obtain ⟨u, hu, τ, he⟩ := H _ (h0K w)
      refine ⟨w - u, -τ, ?_, ?_⟩
      · rw [map_sub, ← he]
        have e : ∑ j, (-τ) j • c.principal (s j) 0 = -∑ j, τ j • c.principal (s j) 0 := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun j _ => by rw [Pi.neg_apply, neg_smul]
        rw [e]
        abel
      · change (w : c.φ.model.E 0) - ((w : c.φ.model.E 0) - (u : c.φ.model.E 0)) ∈ _
        rw [sub_sub_cancel]
        exact hu

include hf hc hft hφ0 hx0 hx in
/-- **The bridge** `IsParamOntoVec` ↔ Part I's `IsParamGP`: at a zero `x ∈ X₁` of the
sc-Fredholm section functor `f` (with tame germ data), for sections `s_j` and a chart `c` of `W`
centred at `x` with a presentation `T` of its partial quadrant, (15.1) with the vectors
`s_j(x)` (for every operator of `T(f, Λ₀)(x)` and every chart presentation of `T^R_xX`) holds
iff Part I's properties (i)–(ii) of the proof of Theorem 5.3.10 hold for `f` and the `s_j` in
`c`. -/
theorem isParamOntoVec_iff_isParamGP (hT : c.φ.model.C = T 0 ⁻¹' quadrant n Wq 0) :
    IsParamOntoVec f x (fun j => ⟨s j (A.X.PObj.levelVal 1 x), hsec j _⟩) ↔
      c.IsParamGP f s T := by
  rw [isParamGP_iff_onto_chart hft hsec hc hx hφ0 hx0 T,
    ← onto_chart_iff hft hsec hc hx hφ0 hx0 T]
  have hL := (mem_support_linearization_zero_iff hf hc hx hx0 _).2 rfl
  constructor
  · intro H
    exact H _ hL c.φ c.isChart hx n Wq T hT
  · intro H L hL' φ hφ hxφ m V T' hT' w
    obtain rfl := ((mem_support_linearization_zero_iff hf hc hx hx0 L).1 hL')
    have e := reducedTangentFiber_eq (hφ := c.isChart) (hx := hx) (T := T) (hψ := hφ)
      (hx' := hxφ) (T' := T') hT hT'
    rw [← e]
    exact H w

end Bridge

end SBLocalization

end Polyfold
