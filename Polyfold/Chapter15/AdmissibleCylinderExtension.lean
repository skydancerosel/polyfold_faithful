import Polyfold.Chapter15.AdmissibleRelativeStep
import Polyfold.Chapter15.CylinderExtensionBump

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, **Corollary
15.3.10 (3)** (p. 699; 2017: Corollary 15.1 (3)) and its proof (pp. 699–700), for perturbations
that are sc⁺ with `N(Λ) ≤ 1` and transversal, structurability not assumed.

# The cobordism of Corollary 15.3.10 (3) for transversal perturbations with `N(Λ) ≤ 1`

## The text, paraphrased

Two structurable regular perturbations `(Nⁱ, Uⁱ, Λⁱ)` of `f` (with `Nⁱ(Λⁱ) < 1`) are joined by a
structurable regular perturbation of `f̃(t, x) = (t, f(x))` on `[0, 1] × X` (Theorem 15.3.9 with
the boundary data `Λⁱ` over `{i} × X`).

## What is formalized (namespace `Polyfold.SBLocalization`)

* `IsTransversalPerturbation A f N U Λ`: `(N, U)` controls compactness, `Λ` is an
  sc⁺-multisection with dom-supp in `U`, `N(Λ) ≤ 1`, and `(f, Λ)` is transversal.  Every
  structurable regular perturbation is one (`IsRegularPerturbation.isTransversalPerturbation`).
* `isScPlusMultisection_cubePullMult`, `isScPlusMultisection_cylExtension`: the pull-back
  `pr^*Λ` and the extension `(β₀ ∘ t) ⊙ pr^*Λ⁰ ⊕ (β₁ ∘ t) ⊙ pr^*Λ¹` of the end data are
  sc⁺-multisections for sc⁺-multisections `Λ`, `Λⁱ`.
* `cylExtension_of_zero'`, `cylExtension_of_one'`, `pointwiseNorm_cylExtension_le`: the values
  over `t = 0, 1` and the bound `Ñ(Λ_ext) ≤ β₀ ∘ t + β₁ ∘ t` for the collar norm, which is `< 1`
  for `0 < t < 1`.
* **`corollary_15_3_10_3_transversal`**: for `d_X ≡ 0`, `|X|` paracompact, sc-smooth bump
  functions and `f` sc-Fredholm with tame germ data, two transversal perturbations
  `(Nⁱ, Uⁱ, Λⁱ)` are joined by a transversal perturbation `(Ñ, Ũ, Λ̃)` of `f̃` with `Λ̃ = Λⁱ` over
  `{i} × X`; `Λ̃ ∘ f̃` is a compact branched ep⁺-subgroupoid.

## Reading

The extension of the end data is explicit on the cylinder, so Theorem 14.1.9 (which needs
structurable data) is not used; the relative step is `theorem_15_3_7_relative_of_le` with the
continuous functor `h = (1 + β₀ ∘ t + β₁ ∘ t) / 2`, which leaves room for the parameter families
exactly off `{0, 1} × X`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold EpGroupoid SEP

variable {A : SEP.{u}}

variable (A) in
/-- **A transversal perturbation `(N, U, Λ)` of `f`** (the hypotheses on `Λ` in Theorem 15.4.3,
2021 p. 702, for `d_X ≡ 0`): `(N, U)` controls the compactness of `f`, `Λ` is an sc⁺-multisection
with dom-supp in `U` and `N(Λ) ≤ 1`, and `T(f, Λ)` is onto on `supp(Λ ∘ f)`.  Compared with
`IsRegularPerturbation`: `Λ` is not assumed structurable, and `N(Λ) = 1` is allowed. -/
def IsTransversalPerturbation (f : A.Obj → A.W) (N : A.B.One → ℝ) (U : Set A.Obj)
    (Λ : A.W → ℚ≥0) : Prop :=
  ControlsCompactness A f N U ∧ IsScPlusMultisection A Λ ∧ domSupp Λ ⊆ U ∧
    (∀ x, pointwiseNorm N Λ x ≤ 1) ∧ IsTransversal f Λ

/-- A structurable regular perturbation is a transversal perturbation. -/
theorem IsRegularPerturbation.isTransversalPerturbation {f : A.Obj → A.W} {N : A.B.One → ℝ}
    {U : Set A.Obj} {Λ : A.W → ℚ≥0} (h : IsRegularPerturbation A f N U Λ) :
    IsTransversalPerturbation A f N U Λ :=
  ⟨h.1, h.2.1.1, h.2.2.1, fun x => (h.2.2.2.1 x).le, h.2.2.2.2⟩

/-! ### The pull-back and the extension are sc⁺ -/

/-- **`pr^*Λ` is an sc⁺-multisection** on `W̃ → [0, 1] × X` for an sc⁺-multisection `Λ`: the
local sections are the lifts `(q, y) ↦ ((q, y), sᵢ(y))`. -/
theorem isScPlusMultisection_cubePullMult {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ) :
    IsScPlusMultisection (A.cubeSEP 1) (cubePullMult Λ) := by
  classical
  refine ⟨isWFunctor_cubePullMult hΛ.1, fun z => ?_⟩
  obtain ⟨O, k, s, σ, hO, hx, h⟩ := hΛ.exists_isLocalRepOn z.2
  have hOt : IsOpen {p : (A.cubeSEP 1).Obj | p.2 ∈ O} := hO.preimage continuous_snd
  refine hasLocalSectionStructure_of_isLocalRepOn hOt (show z ∈ {p | p.2 ∈ O} from hx)
    (s := fun i => cubeLiftSec (s i)) (σ := σ)
    ⟨h.1, fun i => isScPlusSectionOn_cubeLiftSec (h.2.1 i) hO, h.2.2.1, fun w hw => ?_⟩
  have hw2 : A.P (cubeVal w).2 ∈ O := by
    rw [P_cubeVal_snd]; exact hw
  rw [cubePullMult_apply, h.2.2.2 _ hw2]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hP : A.P (s i ((A.cubeSEP 1).P w).2) = ((A.cubeSEP 1).P w).2 := (h.2.1 i).1 _ hw
  have e : (w = cubeLiftSec (s i) ((A.cubeSEP 1).P w)) ↔
      ((cubeVal w).2 = s i (A.P (cubeVal w).2)) := by
    rw [eq_comm, cubeLiftSec_eq_iff hP rfl, P_cubeVal_snd, eq_comm]
    rfl
  simp only [e]

theorem isScPlusMultisection_smulFun_cubePull {Λ : A.W → ℚ≥0} (h : IsScPlusMultisection A Λ)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) :
    IsScPlusMultisection (A.cubeSEP 1)
      (multisectionSmulFun (fun p => g (cubeT p)) (cubePullMult Λ)) :=
  lemma_13_2_11 (fun _ => rfl) (isScSmoothMap_cylCut hg) (isScPlusMultisection_cubePullMult h)

/-- **The extension of the end data is an sc⁺-multisection** (Definition 13.2.9, Lemma
13.2.11). -/
theorem isScPlusMultisection_cylExtension {Λ₀ Λ₁ : A.W → ℚ≥0}
    (h₀ : IsScPlusMultisection A Λ₀) (h₁ : IsScPlusMultisection A Λ₁) :
    IsScPlusMultisection (A.cubeSEP 1) (cylExtension Λ₀ Λ₁) :=
  definition_13_2_9 (isScPlusMultisection_smulFun_cubePull h₀ contDiff_collarCut₀)
    (isScPlusMultisection_smulFun_cubePull h₁ contDiff_collarCut₁)

/-- **Over `t = 0` the extension is `Λ⁰`**, for sc⁺-multisections. -/
theorem cylExtension_of_zero' {Λ₀ Λ₁ : A.W → ℚ≥0} (h₀ : IsScPlusMultisection A Λ₀)
    {w : (A.cubeSEP 1).W} (hw : ((cubeVal w).1.1 0 : ℝ) = 0) :
    cylExtension Λ₀ Λ₁ w = Λ₀ (cubeVal w).2 := by
  have hz : ∀ w' : (A.cubeSEP 1).W, (A.cubeSEP 1).P w' = (A.cubeSEP 1).P w →
      multisectionSmulFun (fun p => collarCut₁ (cubeT p)) (cubePullMult Λ₁) w' =
        zeroMultisection (A.cubeSEP 1) w' := by
    intro w' hw'
    refine multisectionSmulFun_of_eq_zero (collarCut₁_eq_zero ?_)
    rw [hw']
    change ((cubeVal w).1.1 0 : ℝ) ≤ 5 / 6
    rw [hw]; norm_num
  have h1 : collarCut₀ (cubeT ((A.cubeSEP 1).P w)) = 1 := by
    refine collarCut₀_of_nonpos ?_
    change ((cubeVal w).1.1 0 : ℝ) ≤ 0
    rw [hw]
  unfold cylExtension
  rw [multisectionAdd_eq_left_of_fib (isScPlusMultisection_smulFun_cubePull h₀
    contDiff_collarCut₀) hz, multisectionSmulFun_of_eq_one h1]
  rfl

/-- **Over `t = 1` the extension is `Λ¹`**, for sc⁺-multisections. -/
theorem cylExtension_of_one' {Λ₀ Λ₁ : A.W → ℚ≥0} (h₁ : IsScPlusMultisection A Λ₁)
    {w : (A.cubeSEP 1).W} (hw : ((cubeVal w).1.1 0 : ℝ) = 1) :
    cylExtension Λ₀ Λ₁ w = Λ₁ (cubeVal w).2 := by
  have hz : ∀ w' : (A.cubeSEP 1).W, (A.cubeSEP 1).P w' = (A.cubeSEP 1).P w →
      multisectionSmulFun (fun p => collarCut₀ (cubeT p)) (cubePullMult Λ₀) w' =
        zeroMultisection (A.cubeSEP 1) w' := by
    intro w' hw'
    refine multisectionSmulFun_of_eq_zero (collarCut₀_eq_zero ?_)
    rw [hw']
    change 1 / 6 ≤ ((cubeVal w).1.1 0 : ℝ)
    rw [hw]; norm_num
  have h1 : collarCut₁ (cubeT ((A.cubeSEP 1).P w)) = 1 := by
    refine collarCut₁_of_one_le ?_
    change 1 ≤ ((cubeVal w).1.1 0 : ℝ)
    rw [hw]
  unfold cylExtension
  rw [multisectionAdd_comm, multisectionAdd_eq_left_of_fib (isScPlusMultisection_smulFun_cubePull
    h₁ contDiff_collarCut₁) hz, multisectionSmulFun_of_eq_one h1]
  rfl

/-! ### The cut-offs -/

theorem collarCut₀_nonneg (s : ℝ) : 0 ≤ collarCut₀ s := Real.smoothTransition.nonneg _

theorem collarCut₁_nonneg (s : ℝ) : 0 ≤ collarCut₁ s := Real.smoothTransition.nonneg _

theorem collarCut₀_le_one (s : ℝ) : collarCut₀ s ≤ 1 := Real.smoothTransition.le_one _

theorem collarCut₁_le_one (s : ℝ) : collarCut₁ s ≤ 1 := Real.smoothTransition.le_one _

/-- `β₀ + β₁ ≤ 1`. -/
theorem collarCut_add_le_one (s : ℝ) : collarCut₀ s + collarCut₁ s ≤ 1 := by
  by_cases h : s ≤ 5 / 6
  · rw [collarCut₁_eq_zero h, add_zero]; exact collarCut₀_le_one s
  · rw [collarCut₀_eq_zero (by linarith), zero_add]; exact collarCut₁_le_one s

/-- `β₀ + β₁ < 1` on `(0, 1)`. -/
theorem collarCut_add_lt_one {s : ℝ} (h0 : 0 < s) (h1 : s < 1) :
    collarCut₀ s + collarCut₁ s < 1 := by
  by_cases h : s ≤ 5 / 6
  · rw [collarCut₁_eq_zero h, add_zero]
    exact Real.smoothTransition.lt_one_of_lt_one (by linarith)
  · rw [collarCut₀_eq_zero (by linarith), zero_add]
    exact Real.smoothTransition.lt_one_of_lt_one (by linarith)

/-! ### The norm of the extension -/

/-- **`Ñ(Λ_ext) ≤ β₀ ∘ t + β₁ ∘ t`** for the collar norm, if `Nⁱ(Λⁱ) ≤ 1`. -/
theorem pointwiseNorm_cylExtension_le {N₀ N₁ : A.B.One → ℝ} (hN₀ : A.E.IsAuxNorm N₀)
    (hN₁ : A.E.IsAuxNorm N₁) {Λ₀ Λ₁ : A.W → ℚ≥0} (h₀ : IsScPlusMultisection A Λ₀)
    (h₁ : IsScPlusMultisection A Λ₁) (hn₀ : ∀ x, pointwiseNorm N₀ Λ₀ x ≤ 1)
    (hn₁ : ∀ x, pointwiseNorm N₁ Λ₁ x ≤ 1) (z : (A.cubeSEP 1).Obj) :
    pointwiseNorm (collarAuxNorm A N₀ N₁) (cylExtension Λ₀ Λ₁) z ≤
      collarCut₀ (cubeT z) + collarCut₁ (cubeT z) := by
  have hN : (A.cubeSEP 1).B.IsAuxNorm (collarAuxNorm A N₀ N₁) :=
    (isAuxNorm_collarAuxNorm hN₀ hN₁).isAuxNorm
  have hL₀ := isScPlusMultisection_cubePullMult h₀
  have hL₁ := isScPlusMultisection_cubePullMult h₁
  have hM₀ := isScPlusMultisection_smulFun_cubePull h₀ contDiff_collarCut₀
  have hM₁ := isScPlusMultisection_smulFun_cubePull h₁ contDiff_collarCut₁
  have hsum := pointwiseNorm_multisectionAdd_le hN hM₀ hM₁ z
  have e₀ := pointwiseNorm_smulFun_le hN hL₀ hM₀ z
  have e₁ := pointwiseNorm_smulFun_le hN hL₁ hM₁ z
  have p₀ := pointwiseNorm_nonneg hN (cubePullMult Λ₀) z
  have p₁ := pointwiseNorm_nonneg hN (cubePullMult Λ₁) z
  have c₀n := collarCut₀_nonneg (cubeT z)
  have c₁n := collarCut₁_nonneg (cubeT z)
  change pointwiseNorm _ (multisectionAdd _ _) z ≤ _
  by_cases ha : cubeT z ≤ 1 / 6
  · have c₁ : collarCut₁ (cubeT z) = 0 := collarCut₁_eq_zero (by linarith)
    rw [c₁, abs_zero, zero_mul] at e₁
    have k₀ := pointwiseNorm_cubePullMult_le_zero hN₀.isAuxNorm hN₁.isAuxNorm h₀ ha
    rw [abs_of_nonneg c₀n] at e₀
    have b₀ : collarCut₀ (cubeT z) * pointwiseNorm (collarAuxNorm A N₀ N₁) (cubePullMult Λ₀) z
        ≤ collarCut₀ (cubeT z) * 1 :=
      mul_le_mul_of_nonneg_left (k₀.trans (hn₀ z.2)) c₀n
    linarith
  · by_cases hb : 5 / 6 ≤ cubeT z
    · have c₀ : collarCut₀ (cubeT z) = 0 := collarCut₀_eq_zero (by linarith)
      rw [c₀, abs_zero, zero_mul] at e₀
      have k₁ := pointwiseNorm_cubePullMult_le_one hN₀.isAuxNorm hN₁.isAuxNorm h₁ hb
      rw [abs_of_nonneg c₁n] at e₁
      have b₁ : collarCut₁ (cubeT z) * pointwiseNorm (collarAuxNorm A N₀ N₁) (cubePullMult Λ₁) z
          ≤ collarCut₁ (cubeT z) * 1 :=
        mul_le_mul_of_nonneg_left (k₁.trans (hn₁ z.2)) c₁n
      linarith
    · have c₀ : collarCut₀ (cubeT z) = 0 := collarCut₀_eq_zero (by linarith)
      have c₁ : collarCut₁ (cubeT z) = 0 := collarCut₁_eq_zero (by linarith)
      rw [c₀, abs_zero, zero_mul] at e₀
      rw [c₁, abs_zero, zero_mul] at e₁
      linarith

/-- **`dom-supp(Λ_ext) ⊆ Ũ`** if `dom-supp(Λⁱ) ⊆ Uⁱ` (`domSupp_cylExtension_subset`). -/
theorem domSupp_cylExtension_subset' {Λ₀ Λ₁ : A.W → ℚ≥0} {U₀ U₁ : Set A.Obj}
    (h₀ : domSupp Λ₀ ⊆ U₀) (h₁ : domSupp Λ₁ ⊆ U₁) :
    domSupp (cylExtension Λ₀ Λ₁) ⊆ interpSet A U₀ U₁ :=
  domSupp_cylExtension_subset h₀ h₁

/-! ### Corollary 15.3.10 (3) -/

set_option maxHeartbeats 800000 in
-- the cylinder's ep-groupoid is unfolded in several places
/-- **2021 Corollary 15.3.10 (3), p. 699, for transversal perturbations with `N(Λ) ≤ 1`.**  Let
`d_X ≡ 0`, `|X|` be paracompact, `X` admit sc-smooth bump functions and `f` be sc-Fredholm with
tame germ data.  For transversal perturbations `(Nⁱ, Uⁱ, Λⁱ)`, `i = 0, 1` (sc⁺, `Nⁱ(Λⁱ) ≤ 1`,
dom-supp in `Uⁱ`, `(f, Λⁱ)` transversal; structurability is not assumed) there is a transversal
perturbation `(Ñ, Ũ, Λ̃)` of `f̃` on `[0, 1] × X`, with `Ñ = collarAuxNorm A N⁰ N¹` and
`Ũ = interpSet A U⁰ U¹`, such that `Λ̃ = Λⁱ` over `{i} × X`; `(f̃, Λ̃)` is in general position
and `Λ̃ ∘ f̃` is a compact branched ep⁺-subgroupoid. -/
theorem corollary_15_3_10_3_transversal
    (hd : ∀ x, A.X.PObj.degIndex x = 0) (hpara : A.X.HasParacompactOrbitSpace)
    (hbump : A.X.AdmitsBumpFunctionsPointwise) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {N₀ N₁ : A.B.One → ℝ} {U₀ U₁ : Set A.Obj}
    {Λ₀ Λ₁ : A.W → ℚ≥0} (hr₀ : IsTransversalPerturbation A f N₀ U₀ Λ₀)
    (hr₁ : IsTransversalPerturbation A f N₁ U₁ Λ₁) :
    ∃ Λ' : (A.cubeSEP 1).W → ℚ≥0,
      IsTransversalPerturbation (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf.1.1.1)
        (collarAuxNorm A N₀ N₁) (interpSet A U₀ U₁) Λ' ∧
      (∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (cubeVal w).2) ∧
      (∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (cubeVal w).2) ∧
      IsInGeneralPosition (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf.1.1.1) Λ' ∧
      (A.cubeSEP 1).X.IsBranchedEpSubgroupoid
        (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) ∧
      (A.cubeSEP 1).X.IsCompactBranched
        (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PMor
  have hX : A.X.IsTame := A.X.isTame_of_degIndex_eq_zero hd
  have hXC : (A.cubeSEP 1).X.IsTame := A.X.isTame_cubeProd 1 hX
  have hbumpC : (A.cubeSEP 1).X.PObj.AdmitsBumpFunctions :=
    admitsBumpFunctions_prod_cube (n := 1) (A.X.theorem_12_3_2_1.1 hbump)
  have hcc := controlsCompactness_collar hf.1.1.1 hr₀.1 hr₁.1
  have hfC := isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft
  have hftC : (A.cubeSEP 1).B.IsScFredholmSectionTame (cubeLiftEp (n := 1) f hf.1.1.1) :=
    isScFredholmSectionTame_cubeLiftEp (n := 1) hft
  have h𝒰 : Nonempty (A.cubeSEP 1).X.GoodSystem := by
    obtain ⟨-, D, -⟩ := isStructurable_zeroMultisection (A := A.cubeSEP 1)
      (A.X.hasParacompactOrbitSpace_cubeProd (n := 1) hpara)
    exact ⟨D.𝒰⟩
  have hE := isScPlusMultisection_cylExtension hr₀.2.1 hr₁.2.1
  have hEdom := domSupp_cylExtension_subset hr₀.2.2.1 hr₁.2.2.1
  have hEN := pointwiseNorm_cylExtension_le hr₀.1.1 hr₁.1.1 hr₀.2.1 hr₁.2.1 hr₀.2.2.2.1
    hr₁.2.2.2.1
  have hbonto := isBoundaryFaceOnto_cubeGlue hd hf hft hr₀.2.2.2.2 hr₁.2.2.2.2
  have hglue : ∀ w : (A.cubeSEP 1).W, (A.cubeSEP 1).P w ∈ (A.cubeSEP 1).X.PObj.boundary →
      cylExtension Λ₀ Λ₁ w = cubeGlue Λ₀ Λ₁ w := by
    intro w hw
    rcases (mem_boundary_cubeSEP_iff hX hd _).1 hw with h | h
    · rw [cylExtension_of_zero' hr₀.2.1 h, cubeGlue_of_zero h]
    · rw [cylExtension_of_one' hr₁.2.1 h, cubeGlue_of_one h]
  have hsec : IsSection (A.cubeSEP 1).P (cubeLiftEp (n := 1) f hf.1.1.1) := hfC.1.1.1
  have hbd : ∀ x : (A.cubeSEP 1).X.PObj.Level 1,
      (A.cubeSEP 1).X.PObj.levelVal 1 x ∈ (A.cubeSEP 1).X.PObj.boundary →
      0 < cylExtension Λ₀ Λ₁ (cubeLiftEp (n := 1) f hf.1.1.1
        ((A.cubeSEP 1).X.PObj.levelVal 1 x)) →
      IsReducedOntoAtPt (cubeLiftEp (n := 1) f hf.1.1.1) (cylExtension Λ₀ Λ₁) x := by
    intro x hx hpos
    have hPx : (A.cubeSEP 1).P (cubeLiftEp (n := 1) f hf.1.1.1
        ((A.cubeSEP 1).X.PObj.levelVal 1 x)) ∈ (A.cubeSEP 1).X.PObj.boundary := by
      rw [hsec]; exact hx
    exact hbonto _ hE hglue x hx (mem_smoothSet_of_pos hftC hE hpos)
      (by rw [← hglue _ hPx]; exact hpos)
  -- the functor `h = (1 + β₀ ∘ t + β₁ ∘ t) / 2`
  set h : (A.cubeSEP 1).Obj → ℝ :=
    fun z => (1 + (collarCut₀ (cubeT z) + collarCut₁ (cubeT z))) / 2 with hdef
  have hhc : Continuous h :=
    (continuous_const.add ((contDiff_collarCut₀.continuous.comp continuous_cubeT).add
      (contDiff_collarCut₁.continuous.comp continuous_cubeT))).div_const 2
  have hh1 : ∀ z, h z ≤ 1 := fun z => by
    have := collarCut_add_le_one (cubeT z)
    rw [hdef]; dsimp only; linarith
  have hNle : ∀ z, pointwiseNorm (collarAuxNorm A N₀ N₁) (cylExtension Λ₀ Λ₁) z ≤ h z :=
    fun z => by
      have := collarCut_add_le_one (cubeT z)
      have := hEN z
      rw [hdef]; dsimp only; linarith
  have hNlt : ∀ z ∉ (A.cubeSEP 1).X.PObj.boundary,
      pointwiseNorm (collarAuxNorm A N₀ N₁) (cylExtension Λ₀ Λ₁) z < h z := fun z hz => by
    have hz' := (not_congr (mem_boundary_cubeSEP_iff hX hd z)).1 hz
    rw [not_or] at hz'
    have t0 : (0 : ℝ) ≤ cubeT z := (z.1 0).2.1
    have t1 : cubeT z ≤ 1 := (z.1 0).2.2
    have t0' : (0 : ℝ) < cubeT z := lt_of_le_of_ne t0 (Ne.symm hz'.1)
    have t1' : cubeT z < 1 := lt_of_le_of_ne t1 hz'.2
    have := collarCut_add_lt_one t0' t1'
    have := hEN z
    rw [hdef]; dsimp only; linarith
  obtain ⟨Λ', hΛ', hbd', hdom', hN', htr', hgp'⟩ :=
    theorem_15_3_7_relative_of_le hXC hbumpC h𝒰 hfC hftC hcc hhc (fun _ => rfl) hh1 hE hEdom
      hNle hNlt hbd
  have hN1 : ∀ z, pointwiseNorm (collarAuxNorm A N₀ N₁) Λ' z ≤ 1 :=
    fun z => (hN' z).trans (hh1 z)
  obtain ⟨hbr, hcpt⟩ := theorem_15_3_7_in_particular_hyp hfC hftC hcc hΛ' hN1 hdom' hgp'
  have hbdry : ∀ w : (A.cubeSEP 1).W, ((cubeVal w).1.1 0 : ℝ) = 0 ∨ ((cubeVal w).1.1 0 : ℝ) = 1 →
      (A.cubeSEP 1).P w ∈ (A.cubeSEP 1).X.PObj.boundary := fun w hw =>
    (mem_boundary_cubeSEP_iff hX hd _).2 hw
  exact ⟨Λ', ⟨hcc, hΛ', hdom', hN1, htr'⟩,
    fun w hw => (hbd' w (hbdry w (Or.inl hw))).trans (cylExtension_of_zero' hr₀.2.1 hw),
    fun w hw => (hbd' w (hbdry w (Or.inr hw))).trans (cylExtension_of_one' hr₁.2.1 hw),
    hgp', hbr, hcpt⟩

end SBLocalization

end Polyfold
