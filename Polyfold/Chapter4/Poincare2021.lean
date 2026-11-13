import Polyfold.Chapter3.ParamPerturbation

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §4.5.3, proof of
**Lemma 4.5.2** (p. 202–203): the analytic input, **sc-smoothness of a parametric integral**.
Part of gap G.80.

# Parametric integrals of sc^k maps

## The text, paraphrased

(Proof of Lemma 4.5.2) The primitive of a closed form `ω` on a convex set is
`τ(y)(v) = ∫₀¹ t^{k-1} ω(ty)(y, v) dt`; the text uses without comment that `τ` is again
sc-smooth, i.e. that an integral over `t ∈ [0, 1]` of an sc-smooth family is sc-smooth.

## What is formalized

* `isSck_intervalIntegral`: if `g : [0, 1] × U → F` is sc^k (on the sc-domain `[0,1] × U` of
  `ℝ ⊕ E`, `ℝ` with its constant sc-structure), then `x ↦ ∫₀¹ g(t, x) dt` is sc^k on `U`;
  `isScSmooth_intervalIntegral` for sc-smooth `g`.
* `scDeriv_intervalIntegral`: its derivative is the integral of the partial derivative,
  `D(∫ g)(x) v = ∫₀¹ Dg(t, x)(0, v) dt` (differentiation under the integral).
* The classical inputs on the levels: `continuousOn_intervalIntegral_Icc` (continuity of a
  parametric integral) and `hasFDerivWithinAt_intervalIntegral` (differentiation under the
  integral, within a set which is locally convex).

## The proof

By induction on `k`, through the tangent map.  On level `m` the level map of `∫ g` is
`∫ g_m(t, ·) dt` (sc⁰).  The level operators of `∫ g` are `v ↦ ∫ Dg_m(t, x)(0, v) dt` (bounded
by Banach–Steinhaus); the derivative of `∫ g` on `U_{m+1}` follows from the mean value inequality
on the convex pieces of `U_{m+1}` and the uniform continuity of `Dg_m ∘ ι` (in the operator norm,
Proposition 1.2.1) on `[0, 1] × {x}` (sc¹, by Proposition 1.2.1).  Finally
`T(∫ g) = ∫ Tg ∘ J`, `J(t, (x, v)) = ((t, x), (0, v))` an sc-operator, and `Tg ∘ J` is sc^k on
`[0, 1] × TU` (chain rule).
-/

open Set Function Filter Topology MeasureTheory

noncomputable section

namespace Polyfold

/-! ### Classical inputs: parametric integrals over `[0, 1]` -/

section Classical

variable {X W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

lemma projIcc_eq_of_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (projIcc (0 : ℝ) 1 zero_le_one t : ℝ) = t := by
  rw [projIcc_of_mem _ ht]

lemma uIcc_zero_one : uIcc (0 : ℝ) 1 = Icc 0 1 := uIcc_of_le zero_le_one

omit [CompleteSpace W] in
/-- **Continuity of a parametric integral**: if `G` is continuous on `[0, 1] × A`, then
`x ↦ ∫₀¹ G(t, x) dt` is continuous on `A`. -/
theorem continuousOn_intervalIntegral_Icc [TopologicalSpace X] {G : ℝ × X → W} {A : Set X}
    (hG : ContinuousOn G (Icc 0 1 ×ˢ A)) :
    ContinuousOn (fun x => ∫ t in (0 : ℝ)..1, G (t, x)) A := by
  rw [continuousOn_iff_continuous_domRestrict]
  let f : A → ℝ → W := fun x t => G ((projIcc (0 : ℝ) 1 zero_le_one t : ℝ), (x : X))
  have hf : Continuous (uncurry f) :=
    hG.comp_continuous (by fun_prop) fun p => ⟨(projIcc (0 : ℝ) 1 zero_le_one p.2).2, p.1.2⟩
  refine (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf 0 1).congr
    fun x => intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_zero_one] at ht
  simp only [f, projIcc_eq_of_mem ht]

omit [NormedSpace ℝ W] [CompleteSpace W] in
lemma intervalIntegrable_of_continuousOn_Icc {G : ℝ → W} (hG : ContinuousOn G (Icc 0 1)) :
    IntervalIntegrable G volume 0 1 :=
  (uIcc_zero_one ▸ hG).intervalIntegrable

omit [CompleteSpace W] in
/-- A family of operators which is strongly continuous on `[0, 1]` integrates to an operator:
`v ↦ ∫₀¹ B(t) v dt` is continuous linear (Banach–Steinhaus). -/
theorem exists_clm_intervalIntegral [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {B : ℝ → X →L[ℝ] W} (hB : ∀ v, ContinuousOn (fun t => B t v) (Icc 0 1)) :
    ∃ L : X →L[ℝ] W, ∀ v, L v = ∫ t in (0 : ℝ)..1, B t v := by
  have hint : ∀ v, IntervalIntegrable (fun t => B t v) volume 0 1 := fun v =>
    intervalIntegrable_of_continuousOn_Icc (hB v)
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun t : Icc (0 : ℝ) 1 => B t) fun v => by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hB v)
    exact ⟨C, fun t => hC t t.2⟩
  let L : X →ₗ[ℝ] W :=
    { toFun := fun v => ∫ t in (0 : ℝ)..1, B t v
      map_add' := fun v w => by
        simp only [map_add]
        exact intervalIntegral.integral_add (hint v) (hint w)
      map_smul' := fun c v => by
        simp only [map_smul, RingHom.id_apply]
        exact intervalIntegral.integral_smul c _ }
  refine ⟨L.mkContinuous C fun v => ?_, fun v => rfl⟩
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (f := fun t => B t v) (C := C * ‖v‖) fun t ht => by
      rw [uIoc_of_le zero_le_one] at ht
      exact ((B t).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (hC ⟨t, Ioc_subset_Icc_self ht⟩) (norm_nonneg v))
  change ‖∫ t in (0 : ℝ)..1, B t v‖ ≤ C * ‖v‖
  simpa using h

omit [CompleteSpace W] in
/-- **Differentiation under the integral, within a locally convex set**: let `A = O ∩ K` with
`O` open and `K` convex, and let `G(t, ·)` have derivative `G'(t, y)` within `A` at every
`y ∈ A`, `t ∈ [0, 1]`, with `G` and `G'` (operator norm) continuous on `[0, 1] × A`.  Then
`y ↦ ∫₀¹ G(t, y) dt` has derivative `∫₀¹ G'(t, x) dt` within `A` at `x ∈ A`. -/
theorem hasFDerivWithinAt_intervalIntegral [NormedAddCommGroup X] [NormedSpace ℝ X]
    {G : ℝ × X → W} {G' : ℝ × X → X →L[ℝ] W} {A O K : Set X} (hA : A = O ∩ K) (hO : IsOpen O)
    (hK : Convex ℝ K)
    (hG : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y ∈ A, HasFDerivWithinAt (fun z => G (t, z)) (G' (t, y)) A y)
    (hGc : ContinuousOn G (Icc 0 1 ×ˢ A)) (hG' : ContinuousOn G' (Icc 0 1 ×ˢ A)) {x : X}
    (hx : x ∈ A) {L : X →L[ℝ] W} (hL : ∀ v, L v = ∫ t in (0 : ℝ)..1, G' (t, x) v) :
    HasFDerivWithinAt (fun y => ∫ t in (0 : ℝ)..1, G (t, y)) L A x := by
  refine HasFDerivWithinAt.of_isLittleO (Asymptotics.isLittleO_iff.2 fun c hc => ?_)
  have hB : ContinuousOn (fun p : X × ℝ => G' ((projIcc (0 : ℝ) 1 zero_le_one p.2 : ℝ), p.1))
      (A ×ˢ univ) :=
    hG'.comp (by fun_prop) fun p hp => ⟨(projIcc (0 : ℝ) 1 zero_le_one p.2).2, hp.1⟩
  obtain ⟨δ, hδ, hδ'⟩ := exists_delta_of_continuousOn
    (B := fun y w => G' ((projIcc (0 : ℝ) 1 zero_le_one w : ℝ), y)) hB hx isCompact_Icc hc
  have hxO : x ∈ O := (hA ▸ hx).1
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.1 hO x hxO
  have hev : ∀ᶠ y in 𝓝[A] x, y ∈ Metric.ball x (min δ r) :=
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x (lt_min hδ hr))
  filter_upwards [hev, self_mem_nhdsWithin] with y hy hyA
  set S := K ∩ Metric.ball x (min δ r) with hS
  have hSA : S ⊆ A := fun z hz => hA ▸
    ⟨hrO (Metric.ball_subset_ball (min_le_right δ r) hz.2), hz.1⟩
  have hSc : Convex ℝ S := hK.inter (convex_ball x _)
  have hxS : x ∈ S := ⟨(hA ▸ hx).2, Metric.mem_ball_self (lt_min hδ hr)⟩
  have hyS : y ∈ S := ⟨(hA ▸ hyA).2, hy⟩
  have hpt : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖G (t, y) - G (t, x) - G' (t, x) (y - x)‖ ≤ c * ‖y - x‖ := fun t ht =>
    hSc.norm_image_sub_le_of_norm_hasFDerivWithin_le' (f := fun z => G (t, z))
      (fun z hz => (hG t ht z (hSA hz)).mono hSA)
      (fun z hz => by
        have h := hδ' z (hSA hz) (by
          have := hz.2; rw [Metric.mem_ball, dist_eq_norm] at this
          exact this.trans_le (min_le_left δ r)) t ht
        simpa only [projIcc_eq_of_mem ht] using h) hxS hyS
  have hcont : ∀ z ∈ A, ContinuousOn (fun t => G (t, z)) (Icc 0 1) := fun z hz =>
    hGc.comp (by fun_prop) fun t ht => ⟨ht, hz⟩
  have hcont' : ContinuousOn (fun t => G' (t, x) (y - x)) (Icc 0 1) :=
    (hG'.comp (by fun_prop) fun t ht => ⟨ht, hx⟩).clm_apply continuousOn_const
  have heq : (∫ t in (0 : ℝ)..1, G (t, y)) - (∫ t in (0 : ℝ)..1, G (t, x)) - L (y - x) =
      ∫ t in (0 : ℝ)..1, (G (t, y) - G (t, x) - G' (t, x) (y - x)) := by
    rw [hL, intervalIntegral.integral_sub
      ((intervalIntegrable_of_continuousOn_Icc (hcont y hyA)).sub
        (intervalIntegrable_of_continuousOn_Icc (hcont x hx)))
      (intervalIntegrable_of_continuousOn_Icc hcont'),
      intervalIntegral.integral_sub (intervalIntegrable_of_continuousOn_Icc (hcont y hyA))
        (intervalIntegrable_of_continuousOn_Icc (hcont x hx))]
  rw [heq]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (f := fun t => G (t, y) - G (t, x) - G' (t, x) (y - x)) (C := c * ‖y - x‖) fun t ht => by
      rw [uIoc_of_le zero_le_one] at ht
      exact hpt t (Ioc_subset_Icc_self ht)
  simpa using h

end Classical

/-! ### The sc-domain `[0, 1] × U` of `ℝ ⊕ E` -/

variable {E F : ScBanach}

lemma lvlSet_Icc_prod (U : Set (E 0)) (m : ℕ) :
    ((ScBanach.const ℝ).prod E).lvlSet (Icc (0 : ℝ) 1 ×ˢ U) m = Icc (0 : ℝ) 1 ×ˢ E.lvlSet U m := by
  ext p
  rw [ScBanach.mem_lvlSet, ScBanach.prod_toBase, ScBanach.const_toBase]
  rfl

lemma mk_mem_lvlSet_Icc_prod {U : Set (E 0)} {m : ℕ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {x : E m} (hx : x ∈ E.lvlSet U m) :
    ((t, x) : ((ScBanach.const ℝ).prod E) m) ∈
      ((ScBanach.const ℝ).prod E).lvlSet (Icc (0 : ℝ) 1 ×ˢ U) m := by
  rw [lvlSet_Icc_prod]; exact ⟨ht, hx⟩

lemma toBase_param_mk {m : ℕ} (t : ℝ) (x : E m) :
    ((ScBanach.const ℝ).prod E).toBase m ((t, x) : ((ScBanach.const ℝ).prod E) m) =
      ((t, E.toBase m x) : ((ScBanach.const ℝ).prod E) 0) := by
  rw [ScBanach.prod_toBase, ScBanach.const_toBase]

/-- `[0, 1] × U` is an sc-domain of `ℝ ⊕ E` if `U` is one of `E`. -/
theorem IsScDomain.Icc_prod {U : Set (E 0)} (hU : IsScDomain E U) :
    IsScDomain ((ScBanach.const ℝ).prod E) (Icc (0 : ℝ) 1 ×ˢ U) where
  relOpenConvex m := by
    obtain ⟨O, C, hO, hC, hUm⟩ := hU.relOpenConvex m
    refine ⟨univ ×ˢ O, Icc 0 1 ×ˢ C, isOpen_univ.prod hO, (convex_Icc 0 1).prod hC, ?_⟩
    rw [lvlSet_Icc_prod, hUm, prod_inter_prod, univ_inter]
  uniqueDiffWithinAt m p hp := by
    rw [lvlSet_Icc_prod] at hp ⊢
    exact (uniqueDiffOn_Icc zero_lt_one _ hp.1).prod (hU.uniqueDiffWithinAt m _ hp.2)

/-! ### sc⁰ -/

section Sc0

variable {U : Set (E 0)} {g : ((ScBanach.const ℝ).prod E) 0 → F 0}

lemma continuousOn_levelMap_param (hg : IsSc0 _ F (Icc (0 : ℝ) 1 ×ˢ U) g) {m : ℕ} {x : E m}
    (hx : x ∈ E.lvlSet U m) :
    ContinuousOn (fun t : ℝ => levelMap g m ((t, x) : ((ScBanach.const ℝ).prod E) m))
      (Icc 0 1) :=
  (hg.continuousOn m).comp (by fun_prop) fun _ ht => mk_mem_lvlSet_Icc_prod ht hx

lemma toBase_intervalIntegral_levelMap (hg : IsSc0 _ F (Icc (0 : ℝ) 1 ×ˢ U) g) {m : ℕ}
    {x : E m} (hx : x ∈ E.lvlSet U m) :
    F.toBase m (∫ t in (0 : ℝ)..1, levelMap g m ((t, x) : ((ScBanach.const ℝ).prod E) m)) =
      ∫ t in (0 : ℝ)..1, g (t, E.toBase m x) := by
  rw [← (F.toBase m).intervalIntegral_comp_comm
    (intervalIntegrable_of_continuousOn_Icc (continuousOn_levelMap_param hg hx))]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_zero_one] at ht
  change F.toBase m (levelMap g m _) = g _
  rw [hg.toBase_levelMap (mk_mem_lvlSet_Icc_prod ht hx), toBase_param_mk]

/-- The level maps of `∫₀¹ g(t, ·) dt` are the integrals of the level maps of `g`. -/
theorem levelMap_intervalIntegral (hg : IsSc0 _ F (Icc (0 : ℝ) 1 ×ˢ U) g) {m : ℕ} {x : E m}
    (hx : x ∈ E.lvlSet U m) :
    levelMap (fun y => ∫ t in (0 : ℝ)..1, g (t, y)) m x =
      ∫ t in (0 : ℝ)..1, levelMap g m ((t, x) : ((ScBanach.const ℝ).prod E) m) :=
  levelMap_eq_of_toBase_eq (toBase_intervalIntegral_levelMap hg hx)

/-- **sc⁰ of a parametric integral.** -/
theorem IsSc0.intervalIntegral (hg : IsSc0 _ F (Icc (0 : ℝ) 1 ×ˢ U) g) :
    IsSc0 E F U fun x => ∫ t in (0 : ℝ)..1, g (t, x) where
  mem_range _ _ hx := ⟨_, toBase_intervalIntegral_levelMap hg hx⟩
  continuousOn m := by
    have hc : ContinuousOn (fun p : ℝ × E m => levelMap g m (p : ((ScBanach.const ℝ).prod E) m))
        (Icc 0 1 ×ˢ E.lvlSet U m) := lvlSet_Icc_prod U m ▸ hg.continuousOn m
    exact (continuousOn_intervalIntegral_Icc hc).congr fun x hx => levelMap_intervalIntegral hg hx

end Sc0

/-! ### sc¹ -/

section Sc1

variable {U : Set (E 0)} {g : ((ScBanach.const ℝ).prod E) 0 → F 0}
  {Dl : ∀ m, ((ScBanach.const ℝ).prod E) (m + 1) → ((ScBanach.const ℝ).prod E) m →L[ℝ] F m}

variable (Dl) in
open scoped Classical in
/-- The level operators of `∫₀¹ g(t, ·) dt`, from level operators `Dl` of `g`:
`v ↦ ∫₀¹ Dl_m(t, x)(0, v) dt` (`0` if this is not an operator). -/
def intervalIntegralDl (m : ℕ) (x : E (m + 1)) : E m →L[ℝ] F m :=
  if h : ∃ L : E m →L[ℝ] F m, ∀ v, L v = ∫ t in (0 : ℝ)..1,
      Dl m ((t, x) : ((ScBanach.const ℝ).prod E) (m + 1)) ((0, v) : ((ScBanach.const ℝ).prod E) m)
  then h.choose else 0

theorem intervalIntegralDl_apply (hL : IsSc1Levels (Icc (0 : ℝ) 1 ×ˢ U) g Dl)
    {m : ℕ} {x : E (m + 1)} (hx : x ∈ E.lvlSet U (m + 1)) (v : E m) :
    intervalIntegralDl Dl m x v = ∫ t in (0 : ℝ)..1,
      Dl m ((t, x) : ((ScBanach.const ℝ).prod E) (m + 1))
        ((0, v) : ((ScBanach.const ℝ).prod E) m) := by
  have h : ∃ L : E m →L[ℝ] F m, ∀ v, L v = ∫ t in (0 : ℝ)..1,
      Dl m ((t, x) : ((ScBanach.const ℝ).prod E) (m + 1))
        ((0, v) : ((ScBanach.const ℝ).prod E) m) :=
    exists_clm_intervalIntegral (B := fun t => (Dl m
      ((t, x) : ((ScBanach.const ℝ).prod E) (m + 1))).comp (ContinuousLinearMap.inr ℝ ℝ (E m)))
      fun v => by
        have hf : Continuous fun t : ℝ => ((((t, x) : ((ScBanach.const ℝ).prod E) (m + 1)),
            ((0, v) : ((ScBanach.const ℝ).prod E) m)) :
              ((ScBanach.const ℝ).prod E) (m + 1) × ((ScBanach.const ℝ).prod E) m) :=
          (continuous_id.prodMk continuous_const).prodMk continuous_const
        exact (hL.continuousOn m).comp hf.continuousOn fun t ht =>
          ⟨mk_mem_lvlSet_Icc_prod ht hx, mem_univ _⟩
  rw [intervalIntegralDl, dif_pos h]
  exact h.choose_spec v

/-- **The level conditions of Proposition 1.2.1 for `∫₀¹ g(t, ·) dt`.** -/
theorem isSc1Levels_intervalIntegral (hU : IsScDomain E U) (hg0 : IsSc0 _ F (Icc (0 : ℝ) 1 ×ˢ U) g)
    (hL : IsSc1Levels (Icc (0 : ℝ) 1 ×ˢ U) g Dl) :
    IsSc1Levels U (fun x => ∫ t in (0 : ℝ)..1, g (t, x)) (intervalIntegralDl Dl) where
  hasFDerivWithinAt m x hx := by
    obtain ⟨O, K, hO, hK, hA⟩ := hU.relOpenConvex (m + 1)
    have key := hasFDerivWithinAt_intervalIntegral (X := E (m + 1)) (W := F m)
      (G := fun p => levelMap g m (((ScBanach.const ℝ).prod E).incl m
        ((p.1, p.2) : ((ScBanach.const ℝ).prod E) (m + 1))))
      (G' := fun p => ((Dl m ((p.1, p.2) : ((ScBanach.const ℝ).prod E) (m + 1))).comp
          (((ScBanach.const ℝ).prod E).incl m)).comp (ContinuousLinearMap.inr ℝ ℝ (E (m + 1))))
      hA hO hK (fun t ht y hy => by
        have h1 := hL.hasFDerivWithinAt m ((t, y) : ((ScBanach.const ℝ).prod E) (m + 1))
          (mk_mem_lvlSet_Icc_prod ht hy)
        exact h1.comp y ((hasFDerivWithinAt_const t y _).prodMk (hasFDerivWithinAt_id y _))
          fun z hz => mk_mem_lvlSet_Icc_prod ht hz)
      (by
        rw [← lvlSet_Icc_prod]
        exact (hg0.continuousOn m).comp
          (((ScBanach.const ℝ).prod E).incl m).continuous.continuousOn fun p hp => hp)
      (by
        rw [← lvlSet_Icc_prod]
        exact (hL.continuousOn_clm m).clm_comp continuousOn_const)
      hx (L := (intervalIntegralDl Dl m x).comp (E.incl m))
      fun v => intervalIntegralDl_apply hL hx (E.incl m v)
    exact HasFDerivWithinAt.congr' key
      (fun y hy => levelMap_intervalIntegral hg0 (m := m) (x := E.incl m y) hy) hx
  continuousOn m := by
    have hc : ContinuousOn (fun s : ℝ × (E (m + 1) × E m) =>
        Dl m ((s.1, s.2.1) : ((ScBanach.const ℝ).prod E) (m + 1))
          ((0, s.2.2) : ((ScBanach.const ℝ).prod E) m))
        (Icc 0 1 ×ˢ (E.lvlSet U (m + 1) ×ˢ univ)) := by
      have hf : Continuous fun s : ℝ × (E (m + 1) × E m) =>
          ((((s.1, s.2.1) : ((ScBanach.const ℝ).prod E) (m + 1)),
          ((0, s.2.2) : ((ScBanach.const ℝ).prod E) m)) :
            ((ScBanach.const ℝ).prod E) (m + 1) × ((ScBanach.const ℝ).prod E) m) :=
        (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
          (continuous_const.prodMk (continuous_snd.comp continuous_snd))
      exact (hL.continuousOn m).comp hf.continuousOn fun s hs =>
        ⟨mk_mem_lvlSet_Icc_prod hs.1 hs.2.1, mem_univ _⟩
    exact (continuousOn_intervalIntegral_Icc hc).congr fun p hp =>
      intervalIntegralDl_apply hL hp.1 p.2

/-- **sc¹ of a parametric integral**, with derivative `v ↦ ∫₀¹ Dg(t, x)(0, v) dt`. -/
theorem isSc1With_intervalIntegral (hU : IsScDomain E U) (hg0 : IsSc0 _ F (Icc (0 : ℝ) 1 ×ˢ U) g)
    (hL : IsSc1Levels (Icc (0 : ℝ) 1 ×ˢ U) g Dl) :
    IsSc1With U (fun x => ∫ t in (0 : ℝ)..1, g (t, x)) (intervalIntegralDl Dl 0) :=
  (isSc1Levels_intervalIntegral hU hg0 hL).isSc1With hU hg0.intervalIntegral

lemma isSc1Levels_param (hU : IsScDomain E U) (hg : IsSc1 (Icc (0 : ℝ) 1 ×ˢ U) g) :
    IsSc1Levels (Icc (0 : ℝ) 1 ×ˢ U) g
      fun m => levelDeriv (scDeriv (Icc (0 : ℝ) 1 ×ˢ U) g) m :=
  hg.isSc1With_scDeriv.isSc1Levels hU.Icc_prod

/-- **Differentiation under the integral sign** (sc-version): for `x ∈ U₁`,
`D(∫₀¹ g(t, ·) dt)(x) v = ∫₀¹ Dg(t, x)(0, v) dt`. -/
theorem scDeriv_intervalIntegral (hU : IsScDomain E U) (hg : IsSc1 (Icc (0 : ℝ) 1 ×ˢ U) g)
    {x : E 1} (hx : x ∈ E.lvlSet U 1) (v : E 0) :
    scDeriv U (fun x => ∫ t in (0 : ℝ)..1, g (t, x)) x v = ∫ t in (0 : ℝ)..1,
      scDeriv (Icc (0 : ℝ) 1 ×ˢ U) g ((t, x) : ((ScBanach.const ℝ).prod E) 1)
        ((0, v) : ((ScBanach.const ℝ).prod E) 0) := by
  have hL := isSc1Levels_param hU hg
  rw [IsSc1.scDeriv_eqOn (isSc1With_intervalIntegral hU hg.isSc0 hL) (hU.uniqueDiffWithinAt 1) hx,
    intervalIntegralDl_apply hL hx]
  simp only [levelDeriv_zero]

end Sc1

/-! ### The tangent map and the induction -/

variable (E) in
/-- The sc-operator `J : ℝ ⊕ TE → T(ℝ ⊕ E)`, `J(t, (x, v)) = ((t, x), (0, v))`. -/
def paramTangentOp : ScOperator ((ScBanach.const ℝ).prod E.tangent)
    ((ScBanach.const ℝ).prod E).tangent where
  lvl m :=
    ((ContinuousLinearMap.fst ℝ ℝ (E (m + 1) × E m)).prod
      ((ContinuousLinearMap.fst ℝ (E (m + 1)) (E m)).comp
        (ContinuousLinearMap.snd ℝ ℝ (E (m + 1) × E m)))).prod
    ((0 : (ℝ × (E (m + 1) × E m)) →L[ℝ] ℝ).prod
      ((ContinuousLinearMap.snd ℝ (E (m + 1)) (E m)).comp
        (ContinuousLinearMap.snd ℝ ℝ (E (m + 1) × E m))))
  incl_comm _ _ := rfl

lemma paramTangentOp_apply (p : ((ScBanach.const ℝ).prod E.tangent) 0) :
    paramTangentOp E 0 p = ((((p.1, p.2.1) : ((ScBanach.const ℝ).prod E) 1),
      ((0, p.2.2) : ((ScBanach.const ℝ).prod E) 0)) : ((ScBanach.const ℝ).prod E).tangent 0) :=
  rfl

lemma mapsTo_paramTangentOp (U : Set (E 0)) :
    MapsTo (paramTangentOp E 0) (Icc (0 : ℝ) 1 ×ˢ E.tangentSet U)
      (((ScBanach.const ℝ).prod E).tangentSet (Icc (0 : ℝ) 1 ×ˢ U)) := fun _ hp =>
  mk_mem_lvlSet_Icc_prod (m := 1) hp.1 hp.2

variable {U : Set (E 0)} {g : ((ScBanach.const ℝ).prod E) 0 → F 0}

/-- **The tangent map of a parametric integral**: on `TU`,
`T(∫₀¹ g(t, ·) dt) = ∫₀¹ (Tg ∘ J)(t, ·) dt`. -/
theorem tangentMap_intervalIntegral_eqOn (hU : IsScDomain E U)
    (hg : IsSc1 (Icc (0 : ℝ) 1 ×ˢ U) g) :
    EqOn (tangentMap U fun x => ∫ t in (0 : ℝ)..1, g (t, x))
      (fun p => ∫ t in (0 : ℝ)..1,
        (tangentMap (Icc (0 : ℝ) 1 ×ˢ U) g ∘ paramTangentOp E 0) (t, p))
      (E.tangentSet U) := by
  intro p hp
  have hL := isSc1Levels_param hU hg
  rw [IsSc1.tangentMap_eqOn (isSc1With_intervalIntegral hU hg.isSc0 hL)
    (hU.uniqueDiffWithinAt 1) hp]
  have hc : ContinuousOn (fun t : ℝ =>
      (tangentMap (Icc (0 : ℝ) 1 ×ˢ U) g ∘ paramTangentOp E 0) (t, p)) (Icc 0 1) := by
    refine hg.tangentMap_isSc0.continuousOn_base.comp ?_ fun t ht =>
      mapsTo_paramTangentOp U ⟨ht, hp⟩
    exact ((paramTangentOp E 0).continuous.comp
      (continuous_id.prodMk continuous_const)).continuousOn
  have hI := intervalIntegrable_of_continuousOn_Icc hc
  refine Prod.ext ?_ ?_
  · refine (levelMap_intervalIntegral hg.isSc0 hp).trans ?_
    exact (ContinuousLinearMap.fst ℝ (F 1) (F 0)).intervalIntegral_comp_comm hI
  · refine (intervalIntegralDl_apply hL hp p.2).trans ?_
    refine Eq.trans ?_ ((ContinuousLinearMap.snd ℝ (F 1) (F 0)).intervalIntegral_comp_comm hI)
    refine intervalIntegral.integral_congr fun t _ => ?_
    exact congrArg (fun L : ((ScBanach.const ℝ).prod E) 0 →L[ℝ] F 0 =>
      L ((0, p.2) : ((ScBanach.const ℝ).prod E) 0)) (levelDeriv_zero _ _)

/-- **Lemma 4.5.2, analytic input** (sc-smoothness of a parametric integral, used without
comment in the proof on p. 202–203): if `g` is sc^k on `[0, 1] × U ⊆ ℝ ⊕ E`, `U` an
sc-domain, then `x ↦ ∫₀¹ g(t, x) dt` is sc^k on `U`. -/
theorem isSck_intervalIntegral : ∀ (k : ℕ) {E F : ScBanach} {U : Set (E 0)}
    {g : ((ScBanach.const ℝ).prod E) 0 → F 0}, IsScDomain E U →
    IsSck k ((ScBanach.const ℝ).prod E) F (Icc (0 : ℝ) 1 ×ˢ U) g →
    IsSck k E F U fun x => ∫ t in (0 : ℝ)..1, g (t, x)
  | 0, _, _, _, _, _, hg => IsSc0.intervalIntegral hg
  | k + 1, E, _, U, _, hU, hg => by
    refine ⟨(isSc1With_intervalIntegral hU hg.1.isSc0 (isSc1Levels_param hU hg.1)).isSc1, ?_⟩
    have hJ := IsSck.comp hU.tangentSet.Icc_prod hU.Icc_prod.tangentSet hg.2
      ((paramTangentOp E).isScSmooth hU.tangentSet.Icc_prod k) (mapsTo_paramTangentOp U)
    exact IsSck.congr hU.tangentSet (tangentMap_intervalIntegral_eqOn hU hg.1).symm
      (isSck_intervalIntegral k hU.tangentSet hJ)

/-- **Sc-smoothness of a parametric integral**: if `g` is sc-smooth on `[0, 1] × U`, then
`x ↦ ∫₀¹ g(t, x) dt` is sc-smooth on `U`. -/
theorem isScSmooth_intervalIntegral (hU : IsScDomain E U)
    (hg : IsScSmooth (Icc (0 : ℝ) 1 ×ˢ U) g) :
    IsScSmooth U fun x => ∫ t in (0 : ℝ)..1, g (t, x) :=
  fun k => isSck_intervalIntegral k hU (hg k)

end Polyfold
