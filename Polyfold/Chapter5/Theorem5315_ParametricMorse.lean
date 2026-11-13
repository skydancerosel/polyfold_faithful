import Mathlib

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §5.3, the last step of
the proof of **Theorem 5.3.15** (p. 228; 2017: Theorem 5.8; preprint: Theorem 5.22): "the
parameterized version of Sard's theorem".  Gap G.48.

# The parametrized Sard step of the Morse-type theorem

## The text, paraphrased

(Proof of Theorem 5.3.15, pp. 224, 228) If the map `(λ, y) ↦ d(t ∘ Φ_λ)(y) ∈ T*_yS` is
transversal to the zero section along `{0} × S`, then by the parametrized version of Sard's
theorem there are parameters `λ` arbitrarily close to `0` for which `y ↦ d(t ∘ Φ_λ)(y)` is
transversal to the zero section, that is, `t ∘ Φ_λ` is a Morse function.

## What is formalized

The statement in a chart, for finite-dimensional real normed spaces `Λ` (parameters), `E`, `F`.

* `ae_forall_injective_of_surjective` (**parametric transversality, equal dimensions**): let
  `G : Λ × E → F` be `C¹` on an open `W`, `dim E = dim F`, with `G'(p)` onto at every zero
  `p ∈ W`.  Then for almost every `λ` the partial derivative `∂_zG(λ, z)` is injective (hence
  invertible) at every zero `(λ, z) ∈ W`.
* `HasOnlyMorseCriticalPointsOn h U`: at every critical point `z ∈ U` of `h : E → ℝ` the Hessian
  `D(Dh)(z) : E → E*` is injective.
* `ae_hasOnlyMorseCriticalPointsOn` (**the step of the proof**): let `g : Λ × E → ℝ` be `C²` on
  an open `W` and let `(λ, z) ↦ ∂_zg(λ, z) ∈ E*` have a surjective derivative at each of its zeros
  in `W`.  Then for almost every `λ` the function `g(λ, ·)` has only Morse-type critical points
  on the slice `{z | (λ, z) ∈ W}`.
* `ae_hasOnlyMorseCriticalPointsOn_add_linear` (satisfiability, and the classical corollary):
  for `h` of class `C²` on an open `U ⊆ E`, `h + ℓ` has only Morse-type critical points on `U`
  for almost every `ℓ ∈ E*`.

## How it is proved

Only the Sard lemma in equal dimensions is needed
(`MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`): near a zero `p₀` of `G`,
`Φ = (G, T)` with a linear `T : Λ × E → Λ` is a local diffeomorphism onto an open subset of
`F × Λ` (inverse function theorem); the zero set is the image of `μ ↦ Φ⁻¹(0, μ)`, and
`λ ∘ Φ⁻¹(0, ·) : Λ → Λ` has a singular derivative exactly where `∂_zG` is singular.  Countably
many such neighbourhoods cover the zero set.
-/

open Set Function MeasureTheory Module Topology Filter

noncomputable section

namespace Polyfold

section ParametricTransversality

variable {Λ E F : Type*} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] [FiniteDimensional ℝ Λ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- A surjective `L : Λ × E → F` with `dim E = dim F` is completed by a linear `T : Λ × E → Λ` to
an isomorphism `(L, T) : Λ × E → F × Λ` (`T` is a projection onto `ker L ≅ Λ`). -/
lemma exists_clm_prod_equiv (L : Λ × E →L[ℝ] F) (hL : Surjective L)
    (hEF : finrank ℝ E = finrank ℝ F) :
    ∃ (T : Λ × E →L[ℝ] Λ) (e : (Λ × E) ≃L[ℝ] F × Λ), ∀ v, e v = (L v, T v) := by
  set K := LinearMap.ker (L : Λ × E →ₗ[ℝ] F) with hK
  have hdim : finrank ℝ K = finrank ℝ Λ := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (L : Λ × E →ₗ[ℝ] F)
    rw [LinearMap.range_eq_top.2 hL, finrank_top, Module.finrank_prod] at h1
    change finrank ℝ F + finrank ℝ K = finrank ℝ Λ + finrank ℝ E at h1
    omega
  let e₀ : K ≃ₗ[ℝ] Λ := LinearEquiv.ofFinrankEq K Λ hdim
  obtain ⟨Q, hQ⟩ := K.exists_isCompl
  let T₀ : Λ × E →ₗ[ℝ] Λ := e₀.toLinearMap ∘ₗ K.projectionOnto Q hQ
  let A : Λ × E →ₗ[ℝ] F × Λ := (L : Λ × E →ₗ[ℝ] F).prod T₀
  have hinj : Injective A := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h1 : L v = 0 := congrArg Prod.fst hv
    have h2 : T₀ v = 0 := congrArg Prod.snd hv
    have hvK : v ∈ K := h1
    have h3 : K.projectionOnto Q hQ v = ⟨v, hvK⟩ :=
      Submodule.projectionOnto_apply_left hQ ⟨v, hvK⟩
    have h4 : e₀ ⟨v, hvK⟩ = 0 := by rw [← h3]; exact h2
    exact congrArg Subtype.val (e₀.map_eq_zero_iff.1 h4)
  have hd : finrank ℝ (Λ × E) = finrank ℝ (F × Λ) := by
    rw [Module.finrank_prod, Module.finrank_prod, hEF, add_comm]
  exact ⟨LinearMap.toContinuousLinearMap T₀,
    (A.linearEquivOfInjective hinj hd).toContinuousLinearEquiv, fun v => rfl⟩

variable [MeasurableSpace Λ] [BorelSpace Λ] (μ : Measure Λ) [μ.IsAddHaarMeasure]

/-- **The local step**: near a point `p₀` where `G'(p₀)` is onto, the parameters `λ` of the zeros
`(λ, z)` of `G` at which `∂_zG` is not injective form a null set (inverse function theorem for
`(G, T)` and the Sard lemma in equal dimensions). -/
lemma exists_isOpen_measure_image_fst_eq_zero {W : Set (Λ × E)} (hW : IsOpen W)
    {G : Λ × E → F} (hG : ContDiffOn ℝ 1 G W) (hEF : finrank ℝ E = finrank ℝ F)
    {p₀ : Λ × E} (hp₀ : p₀ ∈ W) (hsurj : Surjective (fderiv ℝ G p₀)) :
    ∃ O : Set (Λ × E), IsOpen O ∧ p₀ ∈ O ∧
      μ (Prod.fst '' {q | q ∈ O ∧ q ∈ W ∧ G q = 0 ∧
        ¬ Injective fun w : E => fderiv ℝ G q (0, w)}) = 0 := by
  obtain ⟨T, e, he⟩ := exists_clm_prod_equiv (fderiv ℝ G p₀) hsurj hEF
  have hGat : ContDiffAt ℝ 1 G p₀ := hG.contDiffAt (hW.mem_nhds hp₀)
  set Φ : Λ × E → F × Λ := fun q => (G q, T q) with hΦ
  have hΦd : ∀ q ∈ W, HasFDerivAt Φ ((fderiv ℝ G q).prod T) q := fun q hq =>
    (((hG.contDiffAt (hW.mem_nhds hq)).differentiableAt one_ne_zero).hasFDerivAt).prodMk
      T.hasFDerivAt
  have hecoe : (e : Λ × E →L[ℝ] F × Λ) = (fderiv ℝ G p₀).prod T :=
    ContinuousLinearMap.ext fun v => he v
  have hstrict : HasStrictFDerivAt Φ (e : Λ × E →L[ℝ] F × Λ) p₀ := by
    have hc : ContDiffAt ℝ 1 Φ p₀ := hGat.prodMk T.contDiff.contDiffAt
    exact hc.hasStrictFDerivAt' (hecoe ▸ hΦd p₀ hp₀) one_ne_zero
  set φ := hstrict.toOpenPartialHomeomorph Φ with hφ
  have hφcoe : (φ : Λ × E → F × Λ) = Φ := hstrict.toOpenPartialHomeomorph_coe
  -- `(G'(q), T)` is invertible for `q` near `p₀`
  have hcont : ContinuousAt (fun q => (fderiv ℝ G q).prod T) p₀ := by
    have hfun : (fun q => (fderiv ℝ G q).prod T) = fun q =>
        (ContinuousLinearMap.inl ℝ F Λ).comp (fderiv ℝ G q) +
          (ContinuousLinearMap.inr ℝ F Λ).comp T := by
      funext q; ext v <;> simp
    rw [hfun]
    exact (continuousAt_const.clm_comp (hGat.continuousAt_fderiv one_ne_zero)).add
      continuousAt_const
  have hev : ∀ᶠ q in 𝓝 p₀, (fderiv ℝ G q).prod T ∈
      range ((↑) : ((Λ × E) ≃L[ℝ] F × Λ) → (Λ × E) →L[ℝ] F × Λ) :=
    hcont.preimage_mem_nhds (ContinuousLinearEquiv.isOpen.mem_nhds ⟨e, hecoe⟩)
  obtain ⟨N₀, hN₀, hN₀o, hpN₀⟩ := eventually_nhds_iff.1 (hev.and (hW.eventually_mem hp₀))
  refine ⟨φ.source ∩ N₀, φ.open_source.inter hN₀o,
    ⟨hstrict.mem_toOpenPartialHomeomorph_source, hpN₀⟩, ?_⟩
  set s : Set Λ := {m | ((0 : F), m) ∈ φ.target ∧ φ.symm (0, m) ∈ N₀ ∧
    ¬ Injective fun w : E => fderiv ℝ G (φ.symm (0, m)) (0, w)} with hs
  set h : Λ → Λ := fun m => (φ.symm ((0 : F), m)).1 with hh
  set h' : Λ → Λ →L[ℝ] Λ := fun m => (ContinuousLinearMap.fst ℝ Λ E).comp
    ((fderiv ℝ φ.symm (0, m)).comp (ContinuousLinearMap.inr ℝ F Λ)) with hh'
  have key : ∀ m ∈ s, HasFDerivAt h (h' m) m ∧ (h' m).det = 0 := by
    rintro m ⟨hmt, hmN, hbad⟩
    obtain ⟨⟨e', he'⟩, hqW⟩ := hN₀ (φ.symm (0, m)) hmN
    have hd1 : HasFDerivAt φ (e' : Λ × E →L[ℝ] F × Λ) (φ.symm (0, m)) := by
      rw [hφcoe, he']; exact hΦd _ hqW
    have hd2 : HasFDerivAt φ.symm (e'.symm : F × Λ →L[ℝ] Λ × E) (0, m) :=
      φ.hasFDerivAt_symm hmt hd1
    have hd3 : HasFDerivAt h (h' m) m := by
      have h1 : HasFDerivAt (fun m' : Λ => φ.symm ((0 : F), m'))
          ((fderiv ℝ φ.symm (0, m)).comp (ContinuousLinearMap.inr ℝ F Λ)) m := by
        rw [hd2.fderiv]
        exact hd2.comp m (hasFDerivAt_prodMk_right (0 : F) m)
      exact (ContinuousLinearMap.fst ℝ Λ E).hasFDerivAt.comp m h1
    refine ⟨hd3, ?_⟩
    -- a non-zero `w` with `G'(q)(0, w) = 0`
    obtain ⟨w, hw0, hw⟩ : ∃ w : E, w ≠ 0 ∧ fderiv ℝ G (φ.symm (0, m)) (0, w) = 0 := by
      by_contra hcon
      push Not at hcon
      refine hbad fun a b hab => ?_
      have h0 : fderiv ℝ G (φ.symm (0, m)) (0, a - b) = 0 := by
        have h1 : ((0 : Λ), a - b) = (0, a) - (0, b) := by simp
        rw [h1, map_sub]; exact sub_eq_zero.2 hab
      by_contra hne
      exact hcon (a - b) (sub_ne_zero.2 hne) h0
    have he'w : e' ((0 : Λ), w) = (0, T (0, w)) := by
      have h1 : (e' : Λ × E →L[ℝ] F × Λ) (0, w) =
          ((fderiv ℝ G (φ.symm (0, m))).prod T) (0, w) := by rw [he']
      rw [ContinuousLinearMap.prod_apply, hw] at h1
      exact h1
    have hu : T ((0 : Λ), w) ≠ 0 := by
      intro h0
      rw [h0] at he'w
      have h1 : ((0 : Λ), w) = 0 := e'.map_eq_zero_iff.1 he'w
      exact hw0 (congrArg Prod.snd h1)
    have hker : h' m (T (0, w)) = 0 := by
      have h1 : e'.symm ((0 : F), T (0, w)) = ((0 : Λ), w) := by
        rw [← he'w, e'.symm_apply_apply]
      change ((fderiv ℝ φ.symm (0, m)) ((0 : F), T (0, w))).1 = 0
      rw [hd2.fderiv]
      change (e'.symm ((0 : F), T (0, w))).1 = 0
      rw [h1]
    have hkb : LinearMap.ker (h' m : Λ →ₗ[ℝ] Λ) ≠ ⊥ := fun hb =>
      hu (LinearMap.ker_eq_bot'.1 hb _ hker)
    exact LinearMap.det_eq_zero_iff_ker_ne_bot.2 hkb
  have hnull : μ (h '' s) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
      (fun m hm => (key m hm).1.hasFDerivWithinAt) (fun m hm => (key m hm).2)
  refine measure_mono_null ?_ hnull
  rintro _ ⟨q, ⟨⟨hqs, hqN⟩, -, hq0, hqbad⟩, rfl⟩
  have hφq : φ q = (0, T q) := by rw [hφcoe, hΦ]; simp only [hq0]
  have hsymm : φ.symm (0, T q) = q := by rw [← hφq]; exact φ.left_inv hqs
  refine ⟨T q, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [← hφq]; exact φ.map_source hqs
  · rw [hsymm]; exact hqN
  · rw [hsymm]; exact hqbad
  · change (φ.symm (0, T q)).1 = q.1
    rw [hsymm]

/-- **Parametric transversality in equal dimensions** (the "parameterized version of Sard's
theorem" of the proof of 2021 Theorem 5.3.15, p. 228): let `G : Λ × E → F` be `C¹` on the open
set `W`, `dim E = dim F`, and let `G'(p) : Λ × E → F` be onto at every zero `p ∈ W` of `G`.  Then
for almost every parameter `λ`, at every zero `(λ, z) ∈ W` the partial derivative
`∂_zG(λ, z) : E → F` is injective. -/
theorem ae_forall_injective_of_surjective {W : Set (Λ × E)} (hW : IsOpen W) {G : Λ × E → F}
    (hG : ContDiffOn ℝ 1 G W) (hEF : finrank ℝ E = finrank ℝ F)
    (hsurj : ∀ p ∈ W, G p = 0 → Surjective (fderiv ℝ G p)) :
    ∀ᵐ lam ∂μ, ∀ z : E, (lam, z) ∈ W → G (lam, z) = 0 →
      Injective fun w : E => fderiv ℝ G (lam, z) (0, w) := by
  set Z : Set (Λ × E) := {p | p ∈ W ∧ G p = 0} with hZ
  choose! O hOo hpO hOnull using fun (p : Λ × E) (hp : p ∈ Z) =>
    exists_isOpen_measure_image_fst_eq_zero μ hW hG hEF hp.1 (hsurj p hp.1 hp.2)
  obtain ⟨Tc, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable (fun p : Z => O p)
    (fun p => hOo p p.2)
  have hbad : {lam | ¬ ∀ z : E, (lam, z) ∈ W → G (lam, z) = 0 →
      Injective fun w : E => fderiv ℝ G (lam, z) (0, w)} ⊆
      ⋃ p ∈ Tc, Prod.fst '' {q | q ∈ O (p : Λ × E) ∧ q ∈ W ∧ G q = 0 ∧
        ¬ Injective fun w : E => fderiv ℝ G q (0, w)} := by
    intro lam hlam
    rw [mem_ofPred_eq] at hlam
    push Not at hlam
    obtain ⟨z, hzW, hz0, hzbad⟩ := hlam
    have hmem : (lam, z) ∈ ⋃ p : Z, O p :=
      mem_iUnion.2 ⟨⟨(lam, z), hzW, hz0⟩, hpO _ ⟨hzW, hz0⟩⟩
    rw [← hTU] at hmem
    obtain ⟨p, hpT, hp⟩ := mem_iUnion₂.1 hmem
    exact mem_iUnion₂.2 ⟨p, hpT, (lam, z), ⟨hp, hzW, hz0, hzbad⟩, rfl⟩
  rw [ae_iff]
  exact measure_mono_null hbad ((measure_biUnion_null_iff hTc).2 fun p _ => hOnull p p.2)

end ParametricTransversality

section Morse

variable {Λ E : Type*} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] [FiniteDimensional ℝ Λ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Only Morse-type critical points** (2021 Theorem 5.3.15 (2), p. 223, in a chart): at every
critical point `z ∈ U` of `h : E → ℝ` the Hessian `D(Dh)(z) : E → E*` is injective (so
non-degenerate, `E` being finite-dimensional). -/
def HasOnlyMorseCriticalPointsOn (h : E → ℝ) (U : Set E) : Prop :=
  ∀ z ∈ U, fderiv ℝ h z = 0 → Injective (fderiv ℝ (fderiv ℝ h) z)

/-- The dual of a finite-dimensional space has the same dimension. -/
lemma finrank_clm_real : finrank ℝ (E →L[ℝ] ℝ) = finrank ℝ E := by
  rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E) (F' := ℝ)).finrank_eq,
    Module.finrank_linearMap, Module.finrank_self, mul_one]

omit [FiniteDimensional ℝ Λ] [FiniteDimensional ℝ E] in
/-- The partial derivative `∂_zg(λ, z) = Dg(λ, z) ∘ (0, ·)` is the derivative of the slice. -/
lemma fderiv_slice_eq {g : Λ × E → ℝ} {lam : Λ} {z : E} (hg : DifferentiableAt ℝ g (lam, z)) :
    fderiv ℝ (fun z' => g (lam, z')) z =
      (fderiv ℝ g (lam, z)).comp (ContinuousLinearMap.inr ℝ Λ E) :=
  (hg.hasFDerivAt.comp z (hasFDerivAt_prodMk_right lam z)).fderiv

variable [MeasurableSpace Λ] [BorelSpace Λ] (μ : Measure Λ) [μ.IsAddHaarMeasure]

/-- **The parametrized Sard step of 2021 Theorem 5.3.15** (pp. 224, 228; preprint Theorem 5.22):
let `g : Λ × E → ℝ` be `C²` on the open set `W` and let the map `(λ, z) ↦ ∂_zg(λ, z) ∈ E*` (the
text's `(λ, y) ↦ d(t ∘ Φ_λ)(y)`, in a chart) have a surjective derivative at each of its zeros in
`W` (transversality to the zero section).  Then for almost every `λ` the function `g(λ, ·)` has
only Morse-type critical points on the slice `{z | (λ, z) ∈ W}`. -/
theorem ae_hasOnlyMorseCriticalPointsOn {W : Set (Λ × E)} (hW : IsOpen W) {g : Λ × E → ℝ}
    (hg : ContDiffOn ℝ 2 g W)
    (htr : ∀ p ∈ W, (fderiv ℝ g p).comp (ContinuousLinearMap.inr ℝ Λ E) = 0 →
      Surjective (fderiv ℝ (fun q => (fderiv ℝ g q).comp (ContinuousLinearMap.inr ℝ Λ E)) p)) :
    ∀ᵐ lam ∂μ, HasOnlyMorseCriticalPointsOn (fun z => g (lam, z)) {z | (lam, z) ∈ W} := by
  set C : ((Λ × E) →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ E (Λ × E) ℝ).flip (ContinuousLinearMap.inr ℝ Λ E) with hC
  set G : Λ × E → (E →L[ℝ] ℝ) := fun q =>
    (fderiv ℝ g q).comp (ContinuousLinearMap.inr ℝ Λ E) with hGdef
  have hG : ContDiffOn ℝ 1 G W :=
    C.contDiff.comp_contDiffOn (hg.fderiv_of_isOpen hW (by norm_num))
  have hdiff : ∀ p ∈ W, DifferentiableAt ℝ g p := fun p hp =>
    (hg.contDiffAt (hW.mem_nhds hp)).differentiableAt (by norm_num)
  filter_upwards [ae_forall_injective_of_surjective μ hW hG finrank_clm_real.symm htr]
    with lam hlam z hz hcrit
  have hz' : (lam, z) ∈ W := hz
  have hcrit' : G (lam, z) = 0 := by rw [← hcrit]; exact (fderiv_slice_eq (hdiff _ hz')).symm
  have hinj := hlam z hz' hcrit'
  -- the Hessian of the slice is `∂_zG(λ, z)`
  have hWz : ∀ᶠ z' in 𝓝 z, (lam, z') ∈ W :=
    (Continuous.prodMk_right lam).continuousAt.preimage_mem_nhds (hW.mem_nhds hz')
  have heq : (fderiv ℝ fun z' => g (lam, z')) =ᶠ[𝓝 z] fun z' => G (lam, z') :=
    hWz.mono fun z' hz'W => fderiv_slice_eq (hdiff _ hz'W)
  have hGd : DifferentiableAt ℝ G (lam, z) :=
    (hG.contDiffAt (hW.mem_nhds hz')).differentiableAt one_ne_zero
  have hhess : fderiv ℝ (fderiv ℝ fun z' => g (lam, z')) z =
      (fderiv ℝ G (lam, z)).comp (ContinuousLinearMap.inr ℝ Λ E) := by
    rw [heq.fderiv_eq]
    exact (hGd.hasFDerivAt.comp z (hasFDerivAt_prodMk_right lam z)).fderiv
  rw [hhess]
  exact hinj

end Morse

section Linear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace (E →L[ℝ] ℝ)] [BorelSpace (E →L[ℝ] ℝ)]

/-- **Satisfiability of the transversality hypothesis, and the classical corollary**: for a `C²`
function `h` on an open `U ⊆ E` and almost every linear form `ℓ ∈ E*`, the function `h + ℓ` has
only Morse-type critical points on `U`.  (Here `g(ℓ, z) = h(z) + ℓ(z)` and
`D(∂_zg)(ℓ, z)(δℓ, 0) = δℓ`.) -/
theorem ae_hasOnlyMorseCriticalPointsOn_add_linear (μ : Measure (E →L[ℝ] ℝ))
    [μ.IsAddHaarMeasure] {U : Set E} (hU : IsOpen U) {h : E → ℝ} (hh : ContDiffOn ℝ 2 h U) :
    ∀ᵐ ℓ ∂μ, HasOnlyMorseCriticalPointsOn (fun z => h z + ℓ z) U := by
  set W : Set ((E →L[ℝ] ℝ) × E) := Prod.snd ⁻¹' U with hWdef
  have hW : IsOpen W := hU.preimage continuous_snd
  set g : (E →L[ℝ] ℝ) × E → ℝ := fun q => h q.2 + q.1 q.2 with hgdef
  have hev : ContDiff ℝ 2 fun q : (E →L[ℝ] ℝ) × E => q.1 q.2 :=
    isBoundedBilinearMap_apply.contDiff
  have hg : ContDiffOn ℝ 2 g W :=
    (hh.comp contDiff_snd.contDiffOn fun q hq => hq).add hev.contDiffOn
  have hmain := ae_hasOnlyMorseCriticalPointsOn μ hW hg (fun p hp _ => ?_)
  · filter_upwards [hmain] with ℓ hℓ
    exact hℓ
  -- the derivative of `q ↦ ∂_zg(q)` in the direction `(δℓ, 0)` is `δℓ`
  set G : (E →L[ℝ] ℝ) × E → (E →L[ℝ] ℝ) := fun q =>
    (fderiv ℝ g q).comp (ContinuousLinearMap.inr ℝ (E →L[ℝ] ℝ) E) with hGdef
  have hGd : DifferentiableAt ℝ G p := by
    have hC : ContDiffOn ℝ 1 (fderiv ℝ g) W := hg.fderiv_of_isOpen hW (by norm_num)
    exact (((ContinuousLinearMap.compL ℝ E ((E →L[ℝ] ℝ) × E) ℝ).flip
      (ContinuousLinearMap.inr ℝ (E →L[ℝ] ℝ) E)).differentiableAt).comp p
        ((hC.contDiffAt (hW.mem_nhds hp)).differentiableAt one_ne_zero)
  have hdiff : ∀ q ∈ W, DifferentiableAt ℝ g q := fun q hq =>
    (hg.contDiffAt (hW.mem_nhds hq)).differentiableAt (by norm_num)
  -- along `s ↦ (p.1 + s • δℓ, p.2)`: `G = G(p) + s • δℓ`
  intro δ
  refine ⟨(δ, 0), ?_⟩
  have hline : ∀ s : ℝ, G (p.1 + s • δ, p.2) = G p + s • δ := by
    intro s
    have hq : (p.1 + s • δ, p.2) ∈ W := hp
    have h1 : fderiv ℝ (fun z' => g (p.1 + s • δ, z')) p.2 = G (p.1 + s • δ, p.2) :=
      fderiv_slice_eq (hdiff _ hq)
    have h2 : fderiv ℝ (fun z' => g (p.1, z')) p.2 = G p := fderiv_slice_eq (hdiff _ hp)
    have h3 : (fun z' => g (p.1 + s • δ, z')) = fun z' => g (p.1, z') + (s • δ) z' := by
      funext z'
      simp only [hgdef, add_apply]
      ring
    have hd : DifferentiableAt ℝ (g ∘ fun z' => (p.1, z')) p.2 :=
      (hdiff _ hp).comp p.2 (hasFDerivAt_prodMk_right p.1 p.2).differentiableAt
    rw [← h1, h3, ← h2]
    exact ((hd.hasFDerivAt).add (s • δ).hasFDerivAt).fderiv
  have hcurve : HasDerivAt (fun s : ℝ => G (p.1 + s • δ, p.2)) δ 0 := by
    have h1 : (fun s : ℝ => G (p.1 + s • δ, p.2)) = fun s => G p + s • δ := funext hline
    rw [h1]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const δ).const_add (G p)
  have hpath : HasDerivAt (fun s : ℝ => (p.1 + s • δ, p.2)) ((δ, (0 : E))) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => p.1 + s • δ) δ 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const δ).const_add p.1
    exact h1.prodMk (hasDerivAt_const 0 p.2)
  have hp0 : (p.1 + (0 : ℝ) • δ, p.2) = p := by simp
  have hcomp : HasDerivAt (fun s : ℝ => G (p.1 + s • δ, p.2)) (fderiv ℝ G p (δ, 0)) 0 := by
    have hGd' : HasFDerivAt G (fderiv ℝ G p) (p.1 + (0 : ℝ) • δ, p.2) := by
      rw [hp0]; exact hGd.hasFDerivAt
    exact hGd'.comp_hasDerivAt 0 hpath
  exact hcomp.unique hcurve

end Linear

end Polyfold
