import Polyfold.Chapter15.AdmissibleCylinderExtension

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, **Theorem 15.3.9**
(pp. 698–699, steps (c)–(d) of the proof) and **Corollary 15.3.10 (3)** (p. 699).

# The relative step and the cobordism of Corollary 15.3.10 (3) from local seeds

## The text, paraphrased

The proof of Theorem 15.3.9 perturbs a given `Λ₀` near the compact set `supp(Λ₀ ∘ f)`: at each of
its points finitely many sc⁺-sections with small support and small norm are chosen which fill the
cokernel ("argue as in Theorem 15.3.7"), finitely many of these local families cover the compact
set, and a generic small parameter gives the perturbation.

## What is formalized (namespace `Polyfold.SBLocalization`)

The sc-smooth bump functions of §15.3 enter the relative step only through the local seeds
`HasLocalParamSeedsRel A f Λ₀ N`, which are asked at the points of `supp(Λ₀ ∘ f)`.

* **`theorem_15_3_7_relative_of_seeds`**: the statement of `theorem_15_3_7_relative_of_le` with
  the seeds as hypothesis, in place of bump functions on `X`.
* **`corollary_15_3_10_3_transversal_of_seeds`**: the statement of
  `corollary_15_3_10_3_transversal` with the seeds of the explicit extension
  `(β₀ ∘ t) ⊙ pr^*Λ⁰ ⊕ (β₁ ∘ t) ⊙ pr^*Λ¹` on `[0, 1] × X` as hypothesis, in place of bump
  functions on `X`.

## Reading

The proofs are those of the two cited theorems; the seeds were obtained there from the bump
functions by `hasLocalParamSeedsRel`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter MeasureTheory
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP

section Step

variable {A : SEP.{u}} {f : A.Obj → A.W} {Λ₀ : A.W → ℚ≥0} {N : A.B.One → ℝ} {U : Set A.Obj}

/-- **Steps (c)–(d) of the proof of Theorem 15.3.9 (2021 pp. 698–699) from local seeds.**  Let
`X` be tame with a good system, `f` sc-Fredholm with tame germ data, `(N, U)` controlling
compactness, `h ≤ 1` a continuous functor, and `Λ₀` an sc⁺-multisection with dom-supp in `U`,
`N(Λ₀) ≤ h` on `X`, `N(Λ₀) < h` off `∂X`, `(f, Λ₀)` in general position at the points of
`supp(Λ₀ ∘ f) ∩ ∂X`, and with local seeds at the points of `supp(Λ₀ ∘ f)`.  Then there is an
sc⁺-multisection `Λ'` with `Λ' = Λ₀` over `∂X`, dom-supp in `U`, `N(Λ') ≤ h`, and `(f, Λ')`
transversal and in general position.  Bump functions on `X` are not assumed. -/
theorem theorem_15_3_7_relative_of_seeds (hX : A.X.IsTame)
    (H : HasLocalParamSeedsRel A f Λ₀ N) (h𝒰 : Nonempty A.X.GoodSystem)
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hcc : ControlsCompactness A f N U) {h : A.Obj → ℝ}
    (hc : Continuous h) (hfun : ∀ φ, h (A.X.src φ) = h (A.X.tgt φ)) (hh1 : ∀ x, h x ≤ 1)
    (hΛ₀ : IsScPlusMultisection A Λ₀) (hdom₀ : domSupp Λ₀ ⊆ U)
    (hN₀ : ∀ x, pointwiseNorm N Λ₀ x ≤ h x)
    (hN₀' : ∀ x ∉ A.X.PObj.boundary, pointwiseNorm N Λ₀ x < h x)
    (hbd : ∀ x : A.X.PObj.Level 1, A.X.PObj.levelVal 1 x ∈ A.X.PObj.boundary →
      0 < Λ₀ (f (A.X.PObj.levelVal 1 x)) → IsReducedOntoAtPt f Λ₀ x) :
    ∃ Λ' : A.W → ℚ≥0, IsScPlusMultisection A Λ' ∧
      (∀ w, A.P w ∈ A.X.PObj.boundary → Λ' w = Λ₀ w) ∧ domSupp Λ' ⊆ U ∧
      (∀ x, pointwiseNorm N Λ' x ≤ h x) ∧ IsTransversal f Λ' ∧ IsInGeneralPosition A f Λ' := by
  have hN : A.B.IsAuxNorm N := hcc.1.isAuxNorm
  have hfc : Continuous f := continuousOn_univ.1 hft.isScSmooth.2.continuousOn
  have hN1 : ∀ x, pointwiseNorm N Λ₀ x ≤ 1 := fun x => (hN₀ x).trans (hh1 x)
  have hloc : HasLocalGPFamiliesRel A f Λ₀ N (U ∩ A.X.PObj.boundaryᶜ)
      (fun x => h x - pointwiseNorm N Λ₀ x) := by
    refine hasLocalGPFamiliesRel_of_boundary h𝒰 hN (fun x hxb hpos => ?_)
      (exists_relGPFamily_of_seeds_of_le h𝒰 hf hcc hΛ₀ hdom₀ hc hfun hh1 hN₀ hN₀'
        H)
    have hx1 := mem_levelSet_one_of_pos hf hΛ₀ hpos
    exact exists_isOpen_isReducedOntoAtPt hX hf hft hΛ₀ hx1
      (hbd _ (by rw [A.X.PObj.levelVal_levelMk]; exact hxb)
        (by rw [A.X.PObj.levelVal_levelMk]; exact hpos))
  have hsard := hasParametricGeneralPositionRel hX hf hft hcc hΛ₀ hN1 hdom₀
  have hK := isCompact_image_supp_comp hf hfc hΛ₀ hcc hN1 hdom₀
  obtain ⟨Q, hSQ, ⟨F⟩⟩ := exists_relGPFamily_of_compact h𝒰 hN hK hloc
  have hFU : ∀ t, domSupp (F.Λ t) ⊆ U := fun t => (F.domSupp_subset t).trans inter_subset_left
  obtain ⟨ε, hε, hae⟩ := hsard F.ℓ F.Λ (fun t => (F.isStructurable t).1) F.isLinear
    (fun t x => (F.norm_le t x).trans (mul_le_mul_of_nonneg_left (by linarith [hh1 x])
      (Finset.sum_nonneg fun j _ => abs_nonneg _)))
    hFU (fun x hx => F.paramOnto x (hSQ hx) hx)
  have hr : (0 : ℝ) < min ε (1 / (F.ℓ + 1)) := lt_min hε (by positivity)
  obtain ⟨t, ht, hgp⟩ := exists_norm_lt_of_ae hr (min_le_left _ _) hae
  have hsum : ∑ j, |t j| < 1 := sum_abs_lt_one (ht.trans_le (min_le_right _ _))
  have hΛt := F.isStructurable t
  have hsc : IsScPlusMultisection A (multisectionAdd Λ₀ (F.Λ t)) :=
    definition_13_2_9 hΛ₀ hΛt.1
  refine ⟨multisectionAdd Λ₀ (F.Λ t), hsc, fun w hw => ?_,
    (domSupp_multisectionAdd_subset _ _).trans (union_subset hdom₀ (hFU t)), fun x => ?_,
    isTransversal_of_isInGeneralPosition hf hsc hgp, hgp⟩
  · refine multisectionAdd_eq_left_of_notMem_domSupp hΛ₀ hΛt.1 fun hd => ?_
    exact (F.domSupp_subset t hd).2 hw
  · refine (pointwiseNorm_multisectionAdd_le hN hΛ₀ hΛt.1 x).trans ?_
    have hm : 0 ≤ h x - pointwiseNorm N Λ₀ x := sub_nonneg.2 (hN₀ x)
    have h1 : pointwiseNorm N (F.Λ t) x ≤ h x - pointwiseNorm N Λ₀ x :=
      (F.norm_le t x).trans (mul_le_of_le_one_left hm hsum.le)
    linarith


end Step

section Cylinder

variable {A : SEP.{u}}

set_option maxHeartbeats 800000 in
-- the cylinder's ep-groupoid is unfolded in several places
/-- **2021 Corollary 15.3.10 (3), p. 699, for transversal perturbations with `N(Λ) ≤ 1`, from
local seeds on the cylinder.**  Let `d_X ≡ 0`, `|X|` be paracompact and `f` be sc-Fredholm with
tame germ data.  Let `(Nⁱ, Uⁱ, Λⁱ)`, `i = 0, 1`, be transversal perturbations, and let the
explicit extension `(β₀ ∘ t) ⊙ pr^*Λ⁰ ⊕ (β₁ ∘ t) ⊙ pr^*Λ¹` have local seeds at the points of its
solution set.  Then there is a transversal perturbation `(Ñ, Ũ, Λ̃)` of `f̃` on `[0, 1] × X` with
`Λ̃ = Λⁱ` over `{i} × X`; `(f̃, Λ̃)` is in general position and `Λ̃ ∘ f̃` is a compact branched
ep⁺-subgroupoid.  Bump functions on `X` are not assumed. -/
theorem corollary_15_3_10_3_transversal_of_seeds
    (hd : ∀ x, A.X.PObj.degIndex x = 0) (hpara : A.X.HasParacompactOrbitSpace)
    {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {N₀ N₁ : A.B.One → ℝ} {U₀ U₁ : Set A.Obj}
    {Λ₀ Λ₁ : A.W → ℚ≥0} (hr₀ : IsTransversalPerturbation A f N₀ U₀ Λ₀)
    (hr₁ : IsTransversalPerturbation A f N₁ U₁ Λ₁)
    (H : HasLocalParamSeedsRel (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf.1.1.1)
      (cylExtension Λ₀ Λ₁) (collarAuxNorm A N₀ N₁)) :
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
    theorem_15_3_7_relative_of_seeds hXC H h𝒰 hfC hftC hcc hhc (fun _ => rfl) hh1 hE hEdom
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

end Cylinder

end SBLocalization

end Polyfold
