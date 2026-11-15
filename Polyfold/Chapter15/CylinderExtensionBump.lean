import Polyfold.Chapter15.CylinderCollarNorm
import Polyfold.Chapter15.CylinderPullStructurable
import Polyfold.Chapter15.RelativeStepBump
import Polyfold.Chapter15.CylinderFaceOnto
import Polyfold.Chapter15.CylinderFaceOntoWitness
import Polyfold.Chapter14.BoundaryCommensurableSum

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), **Corollary 15.3.10 (3)**
(p. 699) and its proof (pp. 699–700), with sc-smooth bump functions (as in Corollary 15.3.10 (1))
and no partitions of unity.

# Corollary 15.3.10 (3) from bump functions

## The text, paraphrased

Given structurable regular perturbations `(Nⁱ, Uⁱ, Λⁱ)`, `i = 0, 1`, of `f`, apply Theorem
15.3.9 to `f̃(t, x) = (t, f(x))` on `W̃ → [0, 1] × X` with the boundary data `Λⁱ` over
`{i} × X`: a structurable `Λ̃` with `Λ̃ = Λⁱ` over `{i} × X`, `N(Λ̃) < 1`, transversal, and
`Λ̃ ∘ f̃` a compact branched ep⁺-subgroupoid.

## The route

Theorem 15.3.9 assumes sc-smooth partitions of unity; Corollary 15.3.10 does not.  The proof of
Theorem 15.3.9 uses them in step (b), the extension of the boundary data (Theorem 14.1.9).  On
`[0, 1] × X` with `d_X ≡ 0`, `∂([0, 1] × X) = {0, 1} × X`, and the boundary data extend
explicitly: `Λ_ext = (β₀ ∘ t) ⊙ pr^*Λ⁰ ⊕ (β₁ ∘ t) ⊙ pr^*Λ¹` with smooth cut-offs `β₀ = 1` near
`t = 0`, `β₀ = 0` for `t ≥ 1/6`, `β₁ = 0` for `t ≤ 5/6`, `β₁ = 1` near `t = 1`.  It is structurable
(`isStructurable_cubePullMult`, Lemma 13.3.14, Proposition 13.3.12).  Its norm is `< 1` for the
collar norm `Ñ` (`SEP.collarAuxNorm`, equal to `Nⁱ` near `{i} × X`).  Steps (c)–(d) then use bump
functions only (`theorem_15_3_7_relative_of_bump`), and the face condition at `{0, 1} × X` is
`isBoundaryFaceOnto_cubeGlue`.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `collarCut₀`, `collarCut₁` (from `Real.smoothTransition`), `isScSmoothMap_cylCut`.
* `cylExtension Λ⁰ Λ¹`; `isStructurable_cylExtension`, `cylExtension_of_zero`,
  `cylExtension_of_one`, `domSupp_cylExtension_subset`, `pointwiseNorm_cylExtension_lt`.
* **`corollary_15_3_10_3_collar`**: Corollary 15.3.10 (3) for `(Ñ, Ũ) = (collarAuxNorm, interpSet)`
  under `d_X ≡ 0`, `|X|` paracompact, sc-smooth bump functions, `f` sc-Fredholm with tame germ data
  (compactness of `|S_f|` is part of `(Nⁱ, Uⁱ)` controlling compactness).
* **`corollary_15_3_10_3_bump`**: the statement (2)–(3) as printed: there are `(Ñ, Ũ)` restricting
  to `(Nⁱ, Uⁱ)` over `{i} × X` and a structurable regular perturbation `(Ñ, Ũ, Λ̃)` of `f̃` with
  `Λ̃ = Λⁱ` over `{i} × X`.
* `corollary_15_3_10_3_collar_epSEP`, `corollary_15_3_10_3_collar_epSEP_nonempty`: the witness on
  `ℝ × ℝ → ℝ`, `f(x) = (x, x)` (non-zero fibres, `∂([0, 1] × ℝ) ≠ ∅`).
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

/-! ### The cut-offs in `t` -/

/-- `β₀(s) = χ(1 − 6s)` (`χ = Real.smoothTransition`): `1` for `s ≤ 0`, `0` for `s ≥ 1/6`. -/
def collarCut₀ (s : ℝ) : ℝ := Real.smoothTransition (1 - 6 * s)

/-- `β₁(s) = χ(6s − 5)`: `0` for `s ≤ 5/6`, `1` for `s ≥ 1`. -/
def collarCut₁ (s : ℝ) : ℝ := Real.smoothTransition (6 * s - 5)

theorem contDiff_collarCut₀ : ContDiff ℝ ∞ collarCut₀ :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp
    (contDiff_const.sub (contDiff_const.mul contDiff_id))

theorem contDiff_collarCut₁ : ContDiff ℝ ∞ collarCut₁ :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem collarCut₀_of_nonpos {s : ℝ} (hs : s ≤ 0) : collarCut₀ s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem collarCut₀_eq_zero {s : ℝ} (hs : 1 / 6 ≤ s) : collarCut₀ s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem collarCut₁_eq_zero {s : ℝ} (hs : s ≤ 5 / 6) : collarCut₁ s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem collarCut₁_of_one_le {s : ℝ} (hs : 1 ≤ s) : collarCut₁ s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem abs_collarCut₀_le (s : ℝ) : |collarCut₀ s| ≤ 1 := by
  unfold collarCut₀
  rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

theorem abs_collarCut₁_le (s : ℝ) : |collarCut₁ s| ≤ 1 := by
  unfold collarCut₁
  rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

/-- `(t, x) ↦ g(t)` is an sc-smooth function on `[0, 1] × X` for smooth `g`. -/
theorem isScSmoothMap_cylCut {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) :
    (A.cubeSEP 1).X.PObj.IsScSmoothMap realPolyfold fun p : (A.cubeSEP 1).Obj => g (cubeT p) := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have hq : ContDiff ℝ ∞ fun v : Fin 1 → ℝ => g (v 0) := hg.comp (contDiff_apply ℝ ℝ 0)
  exact (UnitCube.isScSmoothMap_cube_real_of_contDiff hq).comp
    (MPolyfold.isScSmoothMap_fst (cubePolyfold 1) A.X.PObj)

/-! ### Sums with a multisection that is trivial on a fibre -/

/-- `(Λ ⊕ Λ')(w) = Λ(w)` if `Λ'` is the trivial multisection on the fibre of `w`. -/
theorem multisectionAdd_eq_left_of_fib {B : SEP.{u}} {Λ Λ' : B.W → ℚ≥0}
    (hΛ : IsScPlusMultisection B Λ) {w : B.W}
    (h : ∀ w', B.P w' = B.P w → Λ' w' = zeroMultisection B w') :
    multisectionAdd Λ Λ' w = Λ w := by
  have e : multisectionAdd Λ Λ' w = multisectionAdd Λ (zeroMultisection B) w := by
    unfold multisectionAdd addAt
    refine finsum_congr fun p => ?_
    rw [h (p.2 : B.W) p.2.2]
  rw [e, multisectionAdd_zeroMultisection hΛ]

/-! ### The extension of the end data -/

/-- **The extension of the end data**: `(β₀ ∘ t) ⊙ pr^*Λ⁰ ⊕ (β₁ ∘ t) ⊙ pr^*Λ¹`. -/
def cylExtension (Λ₀ Λ₁ : A.W → ℚ≥0) : (A.cubeSEP 1).W → ℚ≥0 :=
  multisectionAdd (multisectionSmulFun (fun p => collarCut₀ (cubeT p)) (cubePullMult Λ₀))
    (multisectionSmulFun (fun p => collarCut₁ (cubeT p)) (cubePullMult Λ₁))

theorem isStructurable_smulFun_cubePull (hpara : A.X.HasParacompactOrbitSpace)
    {Λ : A.W → ℚ≥0} (h : IsStructurable A Λ) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) :
    IsStructurable (A.cubeSEP 1)
      (multisectionSmulFun (fun p => g (cubeT p)) (cubePullMult Λ)) :=
  lemma_13_3_14_fun (isStructurable_cubePullMult hpara h) (fun _ => rfl) (isScSmoothMap_cylCut hg)

/-- **The extension is structurable** (Proposition 13.3.12, Lemma 13.3.14). -/
theorem isStructurable_cylExtension (hpara : A.X.HasParacompactOrbitSpace)
    {Λ₀ Λ₁ : A.W → ℚ≥0} (h₀ : IsStructurable A Λ₀) (h₁ : IsStructurable A Λ₁) :
    IsStructurable (A.cubeSEP 1) (cylExtension Λ₀ Λ₁) :=
  proposition_13_3_12 (isStructurable_smulFun_cubePull hpara h₀ contDiff_collarCut₀)
    (isStructurable_smulFun_cubePull hpara h₁ contDiff_collarCut₁)

/-- **Over `t = 0` the extension is `Λ⁰`.** -/
theorem cylExtension_of_zero (hpara : A.X.HasParacompactOrbitSpace) {Λ₀ Λ₁ : A.W → ℚ≥0}
    (h₀ : IsStructurable A Λ₀) {w : (A.cubeSEP 1).W} (hw : ((cubeVal w).1.1 0 : ℝ) = 0) :
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
  rw [multisectionAdd_eq_left_of_fib (isStructurable_smulFun_cubePull hpara h₀
    contDiff_collarCut₀).1 hz, multisectionSmulFun_of_eq_one h1]
  rfl

/-- **Over `t = 1` the extension is `Λ¹`.** -/
theorem cylExtension_of_one (hpara : A.X.HasParacompactOrbitSpace) {Λ₀ Λ₁ : A.W → ℚ≥0}
    (h₁ : IsStructurable A Λ₁) {w : (A.cubeSEP 1).W} (hw : ((cubeVal w).1.1 0 : ℝ) = 1) :
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
  rw [multisectionAdd_comm, multisectionAdd_eq_left_of_fib (isStructurable_smulFun_cubePull hpara
    h₁ contDiff_collarCut₁).1 hz, multisectionSmulFun_of_eq_one h1]
  rfl

/-! ### The domain support -/

/-- `dom-supp(pr^*Λ) ⊆ [0, 1] × dom-supp(Λ)`. -/
theorem domSupp_cubePullMult_subset (Λ : A.W → ℚ≥0) :
    domSupp (cubePullMult Λ) ⊆ {p : (A.cubeSEP 1).Obj | p.2 ∈ domSupp Λ} := by
  refine closure_minimal ?_ (isClosed_closure.preimage continuous_snd)
  rintro z ⟨w, hw, hw0, hpos⟩
  have hw1 : (cubeVal w).1 = z := hw
  have hP : A.P (cubeVal w).2 = z.2 := by rw [P_cubeVal_snd, hw1]
  have hne : (cubeVal w).2 ≠ fiberZero A.P (A.P (cubeVal w).2) :=
    cubeVal_snd_ne_fiberZero (by rw [hw]; exact hw0)
  rw [hP] at hne
  exact subset_closure ⟨(cubeVal w).2, hP, hne, hpos⟩

/-- `dom-supp(β ⊙ Λ) ⊆ S ∩ dom-supp(Λ)` for a closed `S ⊇ {β ≠ 0}`. -/
theorem domSupp_smulFun_subset {B : SEP.{u}} {β : B.Obj → ℝ} (Λ : B.W → ℚ≥0) {S : Set B.Obj}
    (hS : IsClosed S) (hβ : ∀ x, β x ≠ 0 → x ∈ S) :
    domSupp (multisectionSmulFun β Λ) ⊆ S ∩ domSupp Λ := by
  refine closure_minimal ?_ (hS.inter isClosed_closure)
  rintro x ⟨w, rfl, hw0, hpos⟩
  refine ⟨hβ _ fun h0 => ?_, ?_⟩
  · rw [BoundaryCommData.multisectionSmulFun_eq_zero_of h0 hw0] at hpos
    exact lt_irrefl _ hpos
  · by_contra hx
    exact hw0 (eq_fiberZero_of_multisectionSmul_pos hx hpos)

/-- **`dom-supp(Λ_ext) ⊆ Ũ`** if `dom-supp(Λⁱ) ⊆ Uⁱ`. -/
theorem domSupp_cylExtension_subset {Λ₀ Λ₁ : A.W → ℚ≥0} {U₀ U₁ : Set A.Obj}
    (h₀ : domSupp Λ₀ ⊆ U₀) (h₁ : domSupp Λ₁ ⊆ U₁) :
    domSupp (cylExtension Λ₀ Λ₁) ⊆ interpSet A U₀ U₁ := by
  refine (domSupp_multisectionAdd_subset _ _).trans ?_
  rintro z (hz | hz)
  · obtain ⟨hzt, hzd⟩ := domSupp_smulFun_subset (S := {p : (A.cubeSEP 1).Obj | cubeT p ≤ 1 / 6})
      _ (isClosed_le continuous_cubeT continuous_const) (fun x hx => by
        by_contra h
        exact hx (collarCut₀_eq_zero (le_of_lt (not_le.1 h)))) hz
    have hz2 := domSupp_cubePullMult_subset Λ₀ hzd
    exact Or.inl ⟨show cubeT z < 2 / 3 by change cubeT z ≤ 1 / 6 at hzt; linarith, h₀ hz2⟩
  · obtain ⟨hzt, hzd⟩ := domSupp_smulFun_subset (S := {p : (A.cubeSEP 1).Obj | 5 / 6 ≤ cubeT p})
      _ (isClosed_le continuous_const continuous_cubeT) (fun x hx => by
        by_contra h
        exact hx (collarCut₁_eq_zero (le_of_lt (not_le.1 h)))) hz
    have hz2 := domSupp_cubePullMult_subset Λ₁ hzd
    exact Or.inr ⟨show 1 / 3 < cubeT z by change 5 / 6 ≤ cubeT z at hzt; linarith, h₁ hz2⟩

/-! ### The norm -/

/-- `Ñ(w) ≤ N⁰(w₂)` on the collar `t ≤ 1/6`, `Ñ(w) ≤ N¹(w₂)` on the collar `t ≥ 5/6`. -/
theorem normW_collarAuxNorm_le {N₀ N₁ : A.B.One → ℝ} (hN₀ : A.B.IsAuxNorm N₀)
    (hN₁ : A.B.IsAuxNorm N₁) {w : (A.cubeSEP 1).W} :
    (((cubeVal w).1.1 0 : ℝ) ≤ 1 / 6 →
      normW (collarAuxNorm A N₀ N₁) w ≤ normW N₀ (cubeVal w).2) ∧
    (5 / 6 ≤ ((cubeVal w).1.1 0 : ℝ) →
      normW (collarAuxNorm A N₀ N₁) w ≤ normW N₁ (cubeVal w).2) := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := A.B.paracompactSpace_pullback ((cubePolyfold 1).prod A.X.PObj) (A.X.cubeProj 1).obj
  by_cases hw : w ∈ (A.cubeSEP 1).B.oneSet
  · have hw' : (cubeVal w).2 ∈ A.B.oneSet :=
      (StrongBundle.pullback_mem_oneSet_iff (A.X.cubeProj 1).isScSmoothMap_obj w).1 hw
    have hv : A.B.oneVal (A.B.oneMk (cubeVal w).2 hw') =
        (cubeVal ((A.cubeSEP 1).B.oneVal ((A.cubeSEP 1).B.oneMk w hw))).2 := by
      rw [A.B.oneVal_oneMk, (A.cubeSEP 1).B.oneVal_oneMk]
    have ht : cubeTime ((A.cubeSEP 1).B.oneMk w hw) = ((cubeVal w).1.1 0 : ℝ) := by
      change ((cubeVal ((A.cubeSEP 1).B.oneVal ((A.cubeSEP 1).B.oneMk w hw))).1.1 0 : ℝ) = _
      rw [(A.cubeSEP 1).B.oneVal_oneMk]
    rw [normW_of_mem _ hw, normW_of_mem _ hw', normW_of_mem _ hw']
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [collarAuxNorm_of_cubeTime_le hN₀ (by rw [ht]; exact h), cubeAuxNorm_eq _ _ hv]
    · rw [collarAuxNorm_of_cubeTime_ge hN₁ (by rw [ht]; exact h), cubeAuxNorm_eq _ _ hv]
  · rw [normW, dif_neg hw]
    exact ⟨fun _ => normW_nonneg hN₀ _, fun _ => normW_nonneg hN₁ _⟩

/-- `Ñ(pr^*Λ)(z) ≤ N⁰(Λ)(z₂)` for `t(z) ≤ 1/6`. -/
theorem pointwiseNorm_cubePullMult_le_zero {N₀ N₁ : A.B.One → ℝ} (hN₀ : A.B.IsAuxNorm N₀)
    (hN₁ : A.B.IsAuxNorm N₁) {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ)
    {z : (A.cubeSEP 1).Obj} (hz : cubeT z ≤ 1 / 6) :
    pointwiseNorm (collarAuxNorm A N₀ N₁) (cubePullMult Λ) z ≤ pointwiseNorm N₀ Λ z.2 := by
  refine Real.sSup_le ?_ (pointwiseNorm_nonneg hN₀ Λ z.2)
  rintro _ ⟨w, ⟨hw, hpos⟩, rfl⟩
  have hw1 : (cubeVal w).1 = z := hw
  have ht : ((cubeVal w).1.1 0 : ℝ) ≤ 1 / 6 := by rw [hw1]; exact hz
  have hmem : (cubeVal w).2 ∈ suppAt Λ z.2 := ⟨by rw [P_cubeVal_snd, hw1], hpos⟩
  exact ((normW_collarAuxNorm_le hN₀ hN₁).1 ht).trans
    ((hΛ.isGreatest_pointwiseNorm N₀ z.2).2 (mem_image_of_mem _ hmem))

/-- `Ñ(pr^*Λ)(z) ≤ N¹(Λ)(z₂)` for `t(z) ≥ 5/6`. -/
theorem pointwiseNorm_cubePullMult_le_one {N₀ N₁ : A.B.One → ℝ} (hN₀ : A.B.IsAuxNorm N₀)
    (hN₁ : A.B.IsAuxNorm N₁) {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ)
    {z : (A.cubeSEP 1).Obj} (hz : 5 / 6 ≤ cubeT z) :
    pointwiseNorm (collarAuxNorm A N₀ N₁) (cubePullMult Λ) z ≤ pointwiseNorm N₁ Λ z.2 := by
  refine Real.sSup_le ?_ (pointwiseNorm_nonneg hN₁ Λ z.2)
  rintro _ ⟨w, ⟨hw, hpos⟩, rfl⟩
  have hw1 : (cubeVal w).1 = z := hw
  have ht : 5 / 6 ≤ ((cubeVal w).1.1 0 : ℝ) := by rw [hw1]; exact hz
  have hmem : (cubeVal w).2 ∈ suppAt Λ z.2 := ⟨by rw [P_cubeVal_snd, hw1], hpos⟩
  exact ((normW_collarAuxNorm_le hN₀ hN₁).2 ht).trans
    ((hΛ.isGreatest_pointwiseNorm N₁ z.2).2 (mem_image_of_mem _ hmem))

/-- **`Ñ(Λ_ext) < 1`** if `Nⁱ(Λⁱ) < 1`. -/
theorem pointwiseNorm_cylExtension_lt (hpara : A.X.HasParacompactOrbitSpace)
    {N₀ N₁ : A.B.One → ℝ} (hN₀ : A.E.IsAuxNorm N₀) (hN₁ : A.E.IsAuxNorm N₁)
    {Λ₀ Λ₁ : A.W → ℚ≥0} (h₀ : IsStructurable A Λ₀) (h₁ : IsStructurable A Λ₁)
    (hn₀ : ∀ x, pointwiseNorm N₀ Λ₀ x < 1) (hn₁ : ∀ x, pointwiseNorm N₁ Λ₁ x < 1)
    (z : (A.cubeSEP 1).Obj) :
    pointwiseNorm (collarAuxNorm A N₀ N₁) (cylExtension Λ₀ Λ₁) z < 1 := by
  have hN : (A.cubeSEP 1).B.IsAuxNorm (collarAuxNorm A N₀ N₁) :=
    (isAuxNorm_collarAuxNorm hN₀ hN₁).isAuxNorm
  have hL₀ := (isStructurable_cubePullMult hpara h₀).1
  have hL₁ := (isStructurable_cubePullMult hpara h₁).1
  have hM₀ := (isStructurable_smulFun_cubePull hpara h₀ contDiff_collarCut₀).1
  have hM₁ := (isStructurable_smulFun_cubePull hpara h₁ contDiff_collarCut₁).1
  have hsum := pointwiseNorm_multisectionAdd_le hN hM₀ hM₁ z
  have e₀ := pointwiseNorm_smulFun_le hN hL₀ hM₀ z
  have e₁ := pointwiseNorm_smulFun_le hN hL₁ hM₁ z
  have p₀ := pointwiseNorm_nonneg hN (cubePullMult Λ₀) z
  have p₁ := pointwiseNorm_nonneg hN (cubePullMult Λ₁) z
  change pointwiseNorm _ (multisectionAdd _ _) z < 1
  by_cases ha : cubeT z ≤ 1 / 6
  · have c₁ : collarCut₁ (cubeT z) = 0 := collarCut₁_eq_zero (by linarith)
    rw [c₁, abs_zero, zero_mul] at e₁
    have k₀ := pointwiseNorm_cubePullMult_le_zero hN₀.isAuxNorm hN₁.isAuxNorm h₀.1 ha
    have b₀ : |collarCut₀ (cubeT z)| * pointwiseNorm (collarAuxNorm A N₀ N₁) (cubePullMult Λ₀) z
        ≤ pointwiseNorm (collarAuxNorm A N₀ N₁) (cubePullMult Λ₀) z :=
      mul_le_of_le_one_left p₀ (abs_collarCut₀_le _)
    linarith [hn₀ z.2]
  · by_cases hb : 5 / 6 ≤ cubeT z
    · have c₀ : collarCut₀ (cubeT z) = 0 := collarCut₀_eq_zero (by linarith)
      rw [c₀, abs_zero, zero_mul] at e₀
      have k₁ := pointwiseNorm_cubePullMult_le_one hN₀.isAuxNorm hN₁.isAuxNorm h₁.1 hb
      have b₁ : |collarCut₁ (cubeT z)| * pointwiseNorm (collarAuxNorm A N₀ N₁) (cubePullMult Λ₁) z
          ≤ pointwiseNorm (collarAuxNorm A N₀ N₁) (cubePullMult Λ₁) z :=
        mul_le_of_le_one_left p₁ (abs_collarCut₁_le _)
      linarith [hn₁ z.2]
    · have c₀ : collarCut₀ (cubeT z) = 0 := collarCut₀_eq_zero (by linarith)
      have c₁ : collarCut₁ (cubeT z) = 0 := collarCut₁_eq_zero (by linarith)
      rw [c₀, abs_zero, zero_mul] at e₀
      rw [c₁, abs_zero, zero_mul] at e₁
      linarith

/-! ### Corollary 15.3.10 (3) -/

/-- **Corollary 15.3.10 (3), p. 699, from bump functions, with the collar norm**: for `d_X ≡ 0`,
`|X|` paracompact, `X` admitting sc-smooth bump functions, `f` sc-Fredholm with tame germ data, and
structurable regular perturbations `(Nⁱ, Uⁱ, Λⁱ)`, `i = 0, 1`, there is a
structurable regular perturbation `(Ñ, Ũ, Λ̃)` of `f̃` on `[0, 1] × X`, with
`Ñ = collarAuxNorm A N⁰ N¹` and `Ũ = interpSet A U⁰ U¹`, such that `Λ̃ = Λⁱ` over `{i} × X`; and
`Λ̃ ∘ f̃` is a compact branched ep⁺-subgroupoid.  No partitions of unity are assumed; the
compactness of `|S_f|` is part of `(Nⁱ, Uⁱ)` controlling compactness. -/
theorem corollary_15_3_10_3_collar
    (hd : ∀ x, A.X.PObj.degIndex x = 0) (hpara : A.X.HasParacompactOrbitSpace)
    (hbump : A.X.AdmitsBumpFunctionsPointwise) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {N₀ N₁ : A.B.One → ℝ} {U₀ U₁ : Set A.Obj}
    {Λ₀ Λ₁ : A.W → ℚ≥0} (hr₀ : IsRegularPerturbation A f N₀ U₀ Λ₀)
    (hr₁ : IsRegularPerturbation A f N₁ U₁ Λ₁) :
    ∃ Λ' : (A.cubeSEP 1).W → ℚ≥0,
      IsRegularPerturbation (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf.1.1.1)
        (collarAuxNorm A N₀ N₁) (interpSet A U₀ U₁) Λ' ∧
      (∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (cubeVal w).2) ∧
      (∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (cubeVal w).2) ∧
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
  have hE := isStructurable_cylExtension hpara hr₀.2.1 hr₁.2.1
  have hEdom := domSupp_cylExtension_subset hr₀.2.2.1 hr₁.2.2.1
  have hEN := pointwiseNorm_cylExtension_lt hpara hr₀.1.1 hr₁.1.1 hr₀.2.1 hr₁.2.1 hr₀.2.2.2.1
    hr₁.2.2.2.1
  have hbonto := isBoundaryFaceOnto_cubeGlue hd hf hft hr₀.2.2.2.2 hr₁.2.2.2.2
  have hglue : ∀ w : (A.cubeSEP 1).W, (A.cubeSEP 1).P w ∈ (A.cubeSEP 1).X.PObj.boundary →
      cylExtension Λ₀ Λ₁ w = cubeGlue Λ₀ Λ₁ w := by
    intro w hw
    rcases (mem_boundary_cubeSEP_iff hX hd _).1 hw with h | h
    · rw [cylExtension_of_zero hpara hr₀.2.1 h, cubeGlue_of_zero h]
    · rw [cylExtension_of_one hpara hr₁.2.1 h, cubeGlue_of_one h]
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
    exact hbonto _ hE.1 hglue x hx (mem_smoothSet_of_pos hftC hE.1 hpos)
      (by rw [← hglue _ hPx]; exact hpos)
  obtain ⟨Λ', hΛ', hbd', hdom', hN', htr', hgp'⟩ :=
    theorem_15_3_7_relative_of_bump hXC hbumpC hfC hftC hcc continuous_const (fun _ => rfl)
      (fun _ => ⟨one_pos, le_rfl⟩) hE hEdom hEN hbd
  obtain ⟨hbr, hcpt⟩ := theorem_15_3_7_in_particular_hyp hfC hftC hcc hΛ'.1
    (fun x => (hN' x).le) hdom' hgp'
  have hbdry : ∀ w : (A.cubeSEP 1).W, ((cubeVal w).1.1 0 : ℝ) = 0 ∨ ((cubeVal w).1.1 0 : ℝ) = 1 →
      (A.cubeSEP 1).P w ∈ (A.cubeSEP 1).X.PObj.boundary := fun w hw =>
    (mem_boundary_cubeSEP_iff hX hd _).2 hw
  exact ⟨Λ', ⟨hcc, hΛ', hdom', hN', htr'⟩,
    fun w hw => (hbd' w (hbdry w (Or.inl hw))).trans (cylExtension_of_zero hpara hr₀.2.1 hw),
    fun w hw => (hbd' w (hbdry w (Or.inr hw))).trans (cylExtension_of_one hpara hr₁.2.1 hw),
    hbr, hcpt⟩

/-- **2021 Corollary 15.3.10 (2)–(3), p. 699 (2017: Corollary 15.1 (2)–(3)), from bump
functions**: for `d_X ≡ 0`, `|X|` paracompact, `X` admitting sc-smooth bump functions, `f`
sc-Fredholm with tame germ data, and structurable regular perturbations
`(Nⁱ, Uⁱ, Λⁱ)`, `i = 0, 1`, there are an auxiliary norm `Ñ` of `W̃` restricting to `Nⁱ` over
`{i} × X`, a saturated open `Ũ` restricting to `Uⁱ`, and a structurable regular perturbation
`(Ñ, Ũ, Λ̃)` of `f̃` with `Λ̃ = Λⁱ` over `{i} × X`; `Λ̃ ∘ f̃` is a compact branched
ep⁺-subgroupoid, the compact cobordism between `Θ₀` and `Θ₁`. -/
theorem corollary_15_3_10_3_bump
    (hd : ∀ x, A.X.PObj.degIndex x = 0) (hpara : A.X.HasParacompactOrbitSpace)
    (hbump : A.X.AdmitsBumpFunctionsPointwise) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {N₀ N₁ : A.B.One → ℝ} {U₀ U₁ : Set A.Obj}
    {Λ₀ Λ₁ : A.W → ℚ≥0} (hr₀ : IsRegularPerturbation A f N₀ U₀ Λ₀)
    (hr₁ : IsRegularPerturbation A f N₁ U₁ Λ₁) :
    ∃ (Ñ : (A.cubeSEP 1).B.One → ℝ) (Ũ : Set (A.cubeSEP 1).Obj),
      (∀ w, cubeTime w = 0 → Ñ w = cubeAuxNorm 1 N₀ w) ∧
      (∀ w, cubeTime w = 1 → Ñ w = cubeAuxNorm 1 N₁ w) ∧
      (∀ (q : Fin 1 → unitInterval) (x : A.Obj), (q 0 : ℝ) = 0 → ((q, x) ∈ Ũ ↔ x ∈ U₀)) ∧
      (∀ (q : Fin 1 → unitInterval) (x : A.Obj), (q 0 : ℝ) = 1 → ((q, x) ∈ Ũ ↔ x ∈ U₁)) ∧
      ∃ Λ' : (A.cubeSEP 1).W → ℚ≥0,
        IsRegularPerturbation (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf.1.1.1) Ñ Ũ Λ' ∧
        (∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (cubeVal w).2) ∧
        (∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (cubeVal w).2) ∧
        (A.cubeSEP 1).X.IsBranchedEpSubgroupoid
          (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) ∧
        (A.cubeSEP 1).X.IsCompactBranched
          (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) :=
  ⟨collarAuxNorm A N₀ N₁, interpSet A U₀ U₁,
    fun _ hw => collarAuxNorm_of_cubeTime_eq_zero hr₀.1.1.isAuxNorm hw,
    fun _ hw => collarAuxNorm_of_cubeTime_eq_one hr₁.1.1.isAuxNorm hw,
    fun _ x hq => mem_interpSet_zero hq x, fun _ x hq => mem_interpSet_one hq x,
    corollary_15_3_10_3_collar hd hpara hbump hf hft hr₀ hr₁⟩

end SBLocalization

/-! ### The witness on `ℝ × ℝ → ℝ` -/

namespace TrivialBundle

open SBLocalization StrongBundle StrongRetr MPolyfold EpGroupoid SEP
  StrongBundleEquivalenceExamples

/-- **Corollary 15.3.10 (3) from bump functions on `ℝ × ℝ → ℝ`, `f(x) = (x, x)`**
(`corollary_15_3_10_3_collar` with the hypotheses of `corollary_15_3_10_1_hypotheses_epSEP`):
two structurable regular perturbations are joined by one on `[0, 1] × ℝ`. -/
theorem corollary_15_3_10_3_collar_epSEP {N₀ N₁ : (epSEP 1 1).B.One → ℝ}
    {U₀ U₁ : Set (epSEP 1 1).Obj} {Λ₀ Λ₁ : (epSEP 1 1).W → ℚ≥0}
    (hr₀ : IsRegularPerturbation (epSEP 1 1) diagSection N₀ U₀ Λ₀)
    (hr₁ : IsRegularPerturbation (epSEP 1 1) diagSection N₁ U₁ Λ₁) :
    ∃ Λ' : ((epSEP 1 1).cubeSEP 1).W → ℚ≥0,
      IsRegularPerturbation ((epSEP 1 1).cubeSEP 1)
        (cubeLiftEp (n := 1) diagSection isScFredholmSectionFunctor_diagSection.1.1.1)
        (SEP.collarAuxNorm (epSEP 1 1) N₀ N₁) (SEP.interpSet (epSEP 1 1) U₀ U₁) Λ' ∧
      (∀ w, ((SEP.cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (SEP.cubeVal w).2) ∧
      (∀ w, ((SEP.cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (SEP.cubeVal w).2) ∧
      ((epSEP 1 1).cubeSEP 1).X.IsBranchedEpSubgroupoid
        (fun z => (Λ' (cubeLiftEp (n := 1) diagSection
          isScFredholmSectionFunctor_diagSection.1.1.1 z) : ℚ)) ∧
      ((epSEP 1 1).cubeSEP 1).X.IsCompactBranched
        (fun z => (Λ' (cubeLiftEp (n := 1) diagSection
          isScFredholmSectionFunctor_diagSection.1.1.1 z) : ℚ)) := by
  obtain ⟨-, -, hd, hpara, hbump, hf, hft, -⟩ := corollary_15_3_10_1_hypotheses_epSEP
  exact corollary_15_3_10_3_collar hd hpara hbump hf hft hr₀ hr₁

/-- **The witness is not degenerate**: the fibres are non-zero, the cylinder has the boundary
points `(q, 0)` with `t(q) ∈ {0, 1}`, a structurable regular perturbation `(N, U, Λ)` of
`f(x) = (x, x)` exists (Corollary 15.3.10 (1)), and Corollary 15.3.10 (3) from bump functions
joins it to itself. -/
theorem corollary_15_3_10_3_collar_epSEP_nonempty :
    (∀ y : (epSEP 1 1).Obj, Nontrivial ((epSEP 1 1).P ⁻¹' {y})) ∧
    ((epSEP 1 1).cubeSEP 1).X.PObj.boundary.Nonempty ∧
    ∃ (N : (epSEP 1 1).B.One → ℝ) (U : Set (epSEP 1 1).Obj) (Λ : (epSEP 1 1).W → ℚ≥0),
      IsRegularPerturbation (epSEP 1 1) diagSection N U Λ ∧
      ∃ Λ' : ((epSEP 1 1).cubeSEP 1).W → ℚ≥0,
        IsRegularPerturbation ((epSEP 1 1).cubeSEP 1)
          (cubeLiftEp (n := 1) diagSection isScFredholmSectionFunctor_diagSection.1.1.1)
          (SEP.collarAuxNorm (epSEP 1 1) N N) (SEP.interpSet (epSEP 1 1) U U) Λ' ∧
        (∀ w, ((SEP.cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ (SEP.cubeVal w).2) ∧
        (∀ w, ((SEP.cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ (SEP.cubeVal w).2) := by
  obtain ⟨hfib, -, hd, -, -, -, -, -, -⟩ := corollary_15_3_10_1_hypotheses_epSEP
  obtain ⟨N, U, Λ, hr, -⟩ := corollary_15_3_10_1_epSEP
  obtain ⟨Λ', h1, h2, h3, -⟩ := corollary_15_3_10_3_collar_epSEP hr hr
  have hX : (epSEP 1 1).X.IsTame := (epSEP 1 1).X.isTame_of_degIndex_eq_zero hd
  refine ⟨hfib, ⟨(fun _ => 0, (0 : Fin 1 → ℝ)), (mem_boundary_cubeSEP_iff hX hd _).2
    (Or.inl rfl)⟩, N, U, Λ, hr, Λ', h1, h2, h3⟩

end TrivialBundle

end Polyfold
