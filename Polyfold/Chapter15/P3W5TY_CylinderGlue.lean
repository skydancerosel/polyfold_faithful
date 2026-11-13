import Polyfold.Chapter15.P3W5TY_Cylinder
import Polyfold.Chapter14.P3W4GL_NormControl

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, pp. 699–700:
the boundary data of **Corollary 15.3.10 (3)** glued from the two regular perturbations
`(Nⁱ, Uⁱ, Λⁱ)` (gap TX-4, in part).

# The glued boundary multisection on `{0, 1} × X`

## The text, paraphrased

The proof of (3) applies Theorem 15.3.9 on `[0, 1] × X` to the multisection over
`∂([0, 1] × X) = {0, 1} × X` that is `Λⁱ` over `{i} × X`; it is `(Ñ, Ũ)`-admissible because the
`(Nⁱ, Uⁱ, Λⁱ)` are regular perturbations, and the face condition holds by their transversality.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `cubeGlue Λ⁰ Λ¹ : W̃ → ℚ⁺`, `Λ¹` over `t = 1` and `Λ⁰` elsewhere (only the values over
  `{0, 1} × X` enter); `cubeGlue_of_zero`, `cubeGlue_of_one`.
* `boundaryDomSupp_cubeGlue_subset`: `dom-supp(Λ_∂) ⊆ Ũ` from `dom-supp(Λⁱ) ⊆ Uⁱ`.
* `pointwiseNorm_cubeGlue_le_zero/one`: `Ñ(Λ_∂)(i, x) ≤ Nⁱ(Λⁱ)(x)`.
* **`corollary_15_3_10_3_glue_hyp`**: Corollary 15.3.10 (3) for two structurable regular
  perturbations `(Nⁱ, Uⁱ, Λⁱ)`, from Theorem 15.3.9 on `[0, 1] × X`, with the two remaining
  hypotheses on the glued data: `Λ_∂` structurable over `{0, 1} × X` and the face condition.
* `corollary_15_3_10_3_glue_witness`: both remaining hypotheses hold on `ℝⁿ × ℝ⁰ → ℝⁿ` for
  `Λ⁰ = Λ¹ = 0` and every section `f`.
* The last paragraph of the proof (p. 700): `controlsCompactness_max` (`(max{N, N'}, U ∩ U')`
  controls compactness) and `IsRegularPerturbation.of_max_left/right` (a regular perturbation
  for it is one for `(N, U)` and for `(N', U')`).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold EpGroupoid SEP

variable {A : SEP.{u}}

open Classical in
/-- **The glued boundary data** `Λ_∂` on `W̃ → [0, 1] × X`: `Λ¹` over `t = 1`, `Λ⁰` elsewhere
(the values off `{0, 1} × X` are not used). -/
def cubeGlue (Λ₀ Λ₁ : A.W → ℚ≥0) (w : (A.cubeSEP 1).W) : ℚ≥0 :=
  if ((cubeVal w).1.1 0 : ℝ) = 1 then Λ₁ (cubeVal w).2 else Λ₀ (cubeVal w).2

theorem cubeGlue_of_zero {Λ₀ Λ₁ : A.W → ℚ≥0} {w : (A.cubeSEP 1).W}
    (h : ((cubeVal w).1.1 0 : ℝ) = 0) : cubeGlue Λ₀ Λ₁ w = Λ₀ (cubeVal w).2 := by
  unfold cubeGlue
  rw [if_neg (by rw [h]; norm_num)]

theorem cubeGlue_of_one {Λ₀ Λ₁ : A.W → ℚ≥0} {w : (A.cubeSEP 1).W}
    (h : ((cubeVal w).1.1 0 : ℝ) = 1) : cubeGlue Λ₀ Λ₁ w = Λ₁ (cubeVal w).2 := by
  unfold cubeGlue
  rw [if_pos h]

/-- The `W`-component of `w ∈ W̃` lies over the `X`-component of `P̃(w)`. -/
theorem P_cubeVal_snd {n : ℕ} (w : (A.cubeSEP n).W) : A.P (cubeVal w).2 = (cubeVal w).1.2 :=
  (show pullbackSpace A.P (Prod.snd : (Fin n → unitInterval) × A.Obj → A.Obj) from w).2

/-- The zero of the fibre of `W̃` over `z` is `(z, 0_{z₂})`. -/
theorem cubeVal_fiberZero {n : ℕ} (z : (A.cubeSEP n).Obj) :
    cubeVal (fiberZero (A.cubeSEP n).P z) = (z, fiberZero A.P z.2) := rfl

theorem cubeVal_snd_ne_fiberZero {n : ℕ} {w : (A.cubeSEP n).W}
    (hw : w ≠ fiberZero (A.cubeSEP n).P ((A.cubeSEP n).P w)) :
    (cubeVal w).2 ≠ fiberZero A.P (A.P (cubeVal w).2) := by
  intro h
  refine hw (Subtype.ext (Prod.ext rfl ?_))
  change (cubeVal w).2 = (cubeVal (fiberZero (A.cubeSEP n).P ((A.cubeSEP n).P w))).2
  rw [cubeVal_fiberZero, h, P_cubeVal_snd]
  rfl

/-- **`dom-supp(Λ_∂) ⊆ Ũ`** if `dom-supp(Λⁱ) ⊆ Uⁱ` and `∂([0, 1] × X) ⊆ {0, 1} × X`. -/
theorem boundaryDomSupp_cubeGlue_subset {Λ₀ Λ₁ : A.W → ℚ≥0} {U₀ U₁ : Set A.Obj}
    (h₀ : domSupp Λ₀ ⊆ U₀) (h₁ : domSupp Λ₁ ⊆ U₁)
    (hbd : ∀ z ∈ (A.cubeSEP 1).X.PObj.boundary, (z.1 0 : ℝ) = 0 ∨ (z.1 0 : ℝ) = 1) :
    boundaryDomSupp (cubeGlue Λ₀ Λ₁) ⊆ interpSet A U₀ U₁ := by
  have hq : Continuous fun q : Fin 1 → unitInterval => (q 0 : ℝ) :=
    continuous_subtype_val.comp (continuous_apply 0)
  set T₀ : Set (Fin 1 → unitInterval) := {q | (q 0 : ℝ) = 0}
  set T₁ : Set (Fin 1 → unitInterval) := {q | (q 0 : ℝ) = 1}
  have hT₀ : IsClosed T₀ := isClosed_eq hq continuous_const
  have hT₁ : IsClosed T₁ := isClosed_eq hq continuous_const
  have hsub : {z | z ∈ (A.cubeSEP 1).X.PObj.boundary ∧ ∃ w, (A.cubeSEP 1).P w = z ∧
      w ≠ fiberZero (A.cubeSEP 1).P z ∧ 0 < cubeGlue Λ₀ Λ₁ w} ⊆
      T₀ ×ˢ domSupp Λ₀ ∪ T₁ ×ˢ domSupp Λ₁ := by
    rintro z ⟨hz, w, rfl, hw0, hpos⟩
    have hne := cubeVal_snd_ne_fiberZero hw0
    have hP := P_cubeVal_snd w
    rcases hbd _ hz with h | h
    · rw [cubeGlue_of_zero h] at hpos
      exact Or.inl ⟨h, subset_closure ⟨(cubeVal w).2, hP, hP ▸ hne, hpos⟩⟩
    · rw [cubeGlue_of_one h] at hpos
      exact Or.inr ⟨h, subset_closure ⟨(cubeVal w).2, hP, hP ▸ hne, hpos⟩⟩
  have hcl : IsClosed (T₀ ×ˢ domSupp Λ₀ ∪ T₁ ×ˢ domSupp Λ₁) :=
    (hT₀.prod isClosed_closure).union (hT₁.prod isClosed_closure)
  rintro ⟨q, x⟩ hz
  rcases closure_minimal hsub hcl hz with ⟨hq', hx⟩ | ⟨hq', hx⟩
  · exact (mem_interpSet_zero hq' x).2 (h₀ hx)
  · exact (mem_interpSet_one hq' x).2 (h₁ hx)

/-- `Ñ(w) ≤ Nⁱ(w₂)` over `t = i`. -/
theorem normW_interpAuxNorm_le {N₀ N₁ : A.B.One → ℝ} (hN₀ : A.B.IsAuxNorm N₀)
    (hN₁ : A.B.IsAuxNorm N₁) {w : (A.cubeSEP 1).W} :
    (((cubeVal w).1.1 0 : ℝ) = 0 → normW (interpAuxNorm A N₀ N₁) w ≤ normW N₀ (cubeVal w).2) ∧
    (((cubeVal w).1.1 0 : ℝ) = 1 → normW (interpAuxNorm A N₀ N₁) w ≤ normW N₁ (cubeVal w).2) := by
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
    · rw [interpAuxNorm_of_cubeTime_eq_zero hN₀ (ht.trans h), cubeAuxNorm_eq _ _ hv]
    · rw [interpAuxNorm_of_cubeTime_eq_one hN₁ (ht.trans h), cubeAuxNorm_eq _ _ hv]
  · rw [normW, dif_neg hw]
    exact ⟨fun _ => normW_nonneg hN₀ _, fun _ => normW_nonneg hN₁ _⟩

/-- **`Ñ(Λ_∂)(0, x) ≤ N⁰(Λ⁰)(x)`.** -/
theorem pointwiseNorm_cubeGlue_le_zero {N₀ N₁ : A.B.One → ℝ} (hN₀ : A.B.IsAuxNorm N₀)
    (hN₁ : A.B.IsAuxNorm N₁) {Λ₀ Λ₁ : A.W → ℚ≥0} (hΛ₀ : IsScPlusMultisection A Λ₀)
    {z : (A.cubeSEP 1).Obj} (hz : (z.1 0 : ℝ) = 0) :
    pointwiseNorm (interpAuxNorm A N₀ N₁) (cubeGlue Λ₀ Λ₁) z ≤ pointwiseNorm N₀ Λ₀ z.2 := by
  refine Real.sSup_le ?_ (pointwiseNorm_nonneg hN₀ Λ₀ z.2)
  rintro _ ⟨w, ⟨hw, hpos⟩, rfl⟩
  have hw1 : (cubeVal w).1 = z := hw
  have ht : ((cubeVal w).1.1 0 : ℝ) = 0 := by rw [hw1]; exact hz
  rw [cubeGlue_of_zero ht] at hpos
  have hmem : (cubeVal w).2 ∈ suppAt Λ₀ z.2 := ⟨by rw [P_cubeVal_snd, hw1], hpos⟩
  exact ((normW_interpAuxNorm_le hN₀ hN₁).1 ht).trans
    ((hΛ₀.isGreatest_pointwiseNorm N₀ z.2).2 (mem_image_of_mem _ hmem))

/-- **`Ñ(Λ_∂)(1, x) ≤ N¹(Λ¹)(x)`.** -/
theorem pointwiseNorm_cubeGlue_le_one {N₀ N₁ : A.B.One → ℝ} (hN₀ : A.B.IsAuxNorm N₀)
    (hN₁ : A.B.IsAuxNorm N₁) {Λ₀ Λ₁ : A.W → ℚ≥0} (hΛ₁ : IsScPlusMultisection A Λ₁)
    {z : (A.cubeSEP 1).Obj} (hz : (z.1 0 : ℝ) = 1) :
    pointwiseNorm (interpAuxNorm A N₀ N₁) (cubeGlue Λ₀ Λ₁) z ≤ pointwiseNorm N₁ Λ₁ z.2 := by
  refine Real.sSup_le ?_ (pointwiseNorm_nonneg hN₁ Λ₁ z.2)
  rintro _ ⟨w, ⟨hw, hpos⟩, rfl⟩
  have hw1 : (cubeVal w).1 = z := hw
  have ht : ((cubeVal w).1.1 0 : ℝ) = 1 := by rw [hw1]; exact hz
  rw [cubeGlue_of_one ht] at hpos
  have hmem : (cubeVal w).2 ∈ suppAt Λ₁ z.2 := ⟨by rw [P_cubeVal_snd, hw1], hpos⟩
  exact ((normW_interpAuxNorm_le hN₀ hN₁).2 ht).trans
    ((hΛ₁.isGreatest_pointwiseNorm N₁ z.2).2 (mem_image_of_mem _ hmem))

/-- **Corollary 15.3.10 (3), p. 699, for two structurable regular perturbations**, from
Theorem 15.3.9 on `[0, 1] × X`: let `d_X ≡ 0`, `|X|` paracompact, `[0, 1] × X` admit sc-smooth
partitions of unity, `f` sc-Fredholm with tame germ data and compact `|S_f|`, and `(Nⁱ, Uⁱ, Λⁱ)`
structurable regular perturbations (`i = 0, 1`).  If the glued boundary data `Λ_∂ = cubeGlue Λ⁰ Λ¹`
are structurable over `{0, 1} × X` and satisfy the face condition (the two hypotheses left of
TX's six on `Λ_∂`), there is a structurable regular perturbation `(Ñ, Ũ, Λ̃)` of `f̃` with
`Λ̃ = Λⁱ` over `{i} × X`, and `Λ̃ ∘ f̃` is a compact branched ep⁺-subgroupoid. -/
theorem corollary_15_3_10_3_glue_hyp (h159 : theorem_15_3_9_statement (A.cubeSEP 1))
    (hd : ∀ x, A.X.PObj.degIndex x = 0) (hpara : A.X.HasParacompactOrbitSpace)
    (hPUC : (A.cubeSEP 1).X.PObj.AdmitsScPartitionsOfUnity) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hS : A.E.HasCompactSolutionSetEp f) {N₀ N₁ : A.B.One → ℝ} {U₀ U₁ : Set A.Obj}
    {Λ₀ Λ₁ : A.W → ℚ≥0} (hr₀ : IsRegularPerturbation A f N₀ U₀ Λ₀)
    (hr₁ : IsRegularPerturbation A f N₁ U₁ Λ₁)
    (hbs : IsBoundaryStructurable (A.cubeSEP 1) (cubeGlue Λ₀ Λ₁))
    (hbonto : IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue Λ₀ Λ₁)) :
    ∃ Λ' : (A.cubeSEP 1).W → ℚ≥0,
      IsRegularPerturbation (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf.1.1.1)
        (interpAuxNorm A N₀ N₁) (interpSet A U₀ U₁) Λ' ∧
      (∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (cubeVal w).2) ∧
      (∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (cubeVal w).2) ∧
      (A.cubeSEP 1).X.IsBranchedEpSubgroupoid
        (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) ∧
      (A.cubeSEP 1).X.IsCompactBranched
        (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) := by
  have hX : A.X.IsTame := A.X.isTame_of_degIndex_eq_zero hd
  have hbd : ∀ z ∈ (A.cubeSEP 1).X.PObj.boundary, (z.1 0 : ℝ) = 0 ∨ (z.1 0 : ℝ) = 1 :=
    fun z hz => (mem_boundary_cubeSEP_iff hX hd z).1 hz
  have hN₀ := hr₀.1.1.isAuxNorm
  have hN₁ := hr₁.1.1.isAuxNorm
  refine corollary_15_3_10_3_ty h159 hd hpara hPUC hf hft hS hr₀.1 hr₁.1 (cubeGlue Λ₀ Λ₁)
    (fun w h => cubeGlue_of_zero h) (fun w h => cubeGlue_of_one h) hbs
    (boundaryDomSupp_cubeGlue_subset hr₀.2.2.1 hr₁.2.2.1 hbd) (fun z hz => ?_) hbonto
  rcases hbd z hz with h | h
  · exact (pointwiseNorm_cubeGlue_le_zero hN₀ hN₁ hr₀.2.1.1 h).trans_lt (hr₀.2.2.2.1 z.2)
  · exact (pointwiseNorm_cubeGlue_le_one hN₀ hN₁ hr₁.2.1.1 h).trans_lt (hr₁.2.2.2.1 z.2)

/-- **The two remaining hypotheses of `corollary_15_3_10_3_glue_hyp` are satisfiable**: on
`ℝⁿ × ℝ⁰ → ℝⁿ` (`epSEP n 0`), for `Λ⁰ = Λ¹ = 0` and every section `f`, the glued data are the
zero multisection of `W̃`, structurable over `∂([0, 1] × X)`, and the face condition holds (the
fibres are `0`). -/
theorem corollary_15_3_10_3_glue_witness (n : ℕ)
    (f : (StrongBundleEquivalenceExamples.epSEP n 0).Obj →
      (StrongBundleEquivalenceExamples.epSEP n 0).W)
    (hf : IsSection (StrongBundleEquivalenceExamples.epSEP n 0).P f) :
    IsBoundaryStructurable ((StrongBundleEquivalenceExamples.epSEP n 0).cubeSEP 1)
      (cubeGlue (zeroMultisection _) (zeroMultisection _)) ∧
    IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf)
      (cubeGlue (zeroMultisection (StrongBundleEquivalenceExamples.epSEP n 0))
        (zeroMultisection _)) := by
  set A := StrongBundleEquivalenceExamples.epSEP n 0
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PMor
  have hP : Injective A.P := injective_epSEP_zero_P n
  have hPC : Injective (A.cubeSEP 1).P := injective_cubeSEP_P hP
  have e : cubeGlue (zeroMultisection A) (zeroMultisection A) = zeroMultisection (A.cubeSEP 1) := by
    funext w
    rw [zeroMultisection_eq_one_of_injective hPC]
    unfold cubeGlue
    split_ifs <;> exact zeroMultisection_eq_one_of_injective hP _
  rw [e]
  have hparaC : (A.cubeSEP 1).X.HasParacompactOrbitSpace :=
    A.X.hasParacompactOrbitSpace_cubeProd 1
      (EpGroupoid.hasParacompactOrbitSpace_trivial (rnPolyfold n))
  exact ⟨isBoundaryStructurable_zero (A.X.isTame_cubeProd 1 (EpGroupoid.isTame_trivial_rn n))
    hparaC, isBoundaryFaceOnto_of_injective hPC _ _⟩

/-! ### The last paragraph of the proof: `(N'', U'') = (max{N, N'}, U ∩ U')` -/

/-- `max{N, N'}` of two auxiliary norms of `(W, μ)` is one (Definition 8.3.5). -/
theorem isAuxNorm_max_ty {N N' : A.B.One → ℝ} (h : A.E.IsAuxNorm N) (h' : A.E.IsAuxNorm N') :
    A.E.IsAuxNorm fun w => max (N w) (N' w) :=
  ⟨h.isAuxNorm.max h'.isAuxNorm, fun a b φ hk hab => by
    simp only [h.map_μ a b φ hk hab, h'.map_μ a b φ hk hab]⟩

/-- **The last paragraph of the proof of Corollary 15.3.10, p. 700**: if `(N, U)` and
`(N', U')` control the compactness of `f`, so does `(max{N, N'}, U ∩ U')`. -/
theorem controlsCompactness_max {f : A.Obj → A.W} {N N' : A.B.One → ℝ} {U U' : Set A.Obj}
    (h : ControlsCompactness A f N U) (h' : ControlsCompactness A f N' U') :
    ControlsCompactness A f (fun w => max (N w) (N' w)) (U ∩ U') := by
  refine ⟨isAuxNorm_max_ty h.1 h'.1, h.2.1.inter h'.2.1, A.X.isSaturated_iff.2 fun φ hφ =>
    ⟨A.X.isSaturated_iff.1 h.2.2.1 φ hφ.1, A.X.isSaturated_iff.1 h'.2.2.1 φ hφ.2⟩,
    subset_inter h.2.2.2.1 h'.2.2.2.1, ?_⟩
  refine h.2.2.2.2.of_isClosed_subset isClosed_closure (closure_mono (image_mono ?_))
  rintro x ⟨hx, hy, hle⟩
  exact ⟨hx.1, hy, (le_max_left _ _).trans hle⟩

/-- `N(Λ) ≤ max{N, N'}(Λ)` pointwise for an sc⁺-multisection. -/
theorem pointwiseNorm_le_max_left {N N' : A.B.One → ℝ} {Λ : A.W → ℚ≥0}
    (hΛ : IsScPlusMultisection A Λ) (x : A.Obj) :
    pointwiseNorm N Λ x ≤ pointwiseNorm (fun w => max (N w) (N' w)) Λ x := by
  obtain ⟨w, hw, hwN⟩ := (hΛ.isGreatest_pointwiseNorm N x).1
  rw [← hwN]
  refine le_trans ?_ ((hΛ.isGreatest_pointwiseNorm _ x).2 (mem_image_of_mem _ hw))
  unfold normW
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

/-- **"`Λ''` is controlled by `(N, U)`"** (p. 700): a structurable regular perturbation for
`(max{N, N'}, U ∩ U')` is one for `(N, U)`, when `(N, U)` controls compactness. -/
theorem IsRegularPerturbation.of_max_left {f : A.Obj → A.W} {N N' : A.B.One → ℝ}
    {U U' : Set A.Obj} {Λ : A.W → ℚ≥0} (h : ControlsCompactness A f N U)
    (hr : IsRegularPerturbation A f (fun w => max (N w) (N' w)) (U ∩ U') Λ) :
    IsRegularPerturbation A f N U Λ :=
  ⟨h, hr.2.1, hr.2.2.1.trans inter_subset_left,
    fun x => (pointwiseNorm_le_max_left hr.2.1.1 x).trans_lt (hr.2.2.2.1 x), hr.2.2.2.2⟩

/-- **"`Λ''` is controlled by `(N', U')`"** (p. 700). -/
theorem IsRegularPerturbation.of_max_right {f : A.Obj → A.W} {N N' : A.B.One → ℝ}
    {U U' : Set A.Obj} {Λ : A.W → ℚ≥0} (h' : ControlsCompactness A f N' U')
    (hr : IsRegularPerturbation A f (fun w => max (N w) (N' w)) (U ∩ U') Λ) :
    IsRegularPerturbation A f N' U' Λ := by
  have e : (fun w => max (N w) (N' w)) = fun w => max (N' w) (N w) :=
    funext fun w => max_comm _ _
  rw [e, inter_comm] at hr
  exact hr.of_max_left h'

end SBLocalization

end Polyfold
