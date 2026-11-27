import GWMemoir.GluingUniformEst

/-!
# Memoir §4.3: the projection `π_a`, uniformly in `a`

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §4.3, pp. 107–108 (with the
projection `π_a` of p. 50).

`π_a = Φ_a⁻¹ ∘ (⊕_a, 0) ∘ Φ_a` (`piLvl`).  By Proposition 4.14 (`memoir_proposition_4_14_off`) a bound
`‖π_a x‖ ≤ C ‖x‖` uniform in `a` follows once the map `(q, p) ↦ (q, 0)` on `G^a_m` is bounded for the
norm `guGSq`, uniformly in `a`.  In the coordinates of `guGSq` this map is
`(c, h, w) ↦ (c + [h]_a, h - [h]_a χ_Z, 0)` with `[h]_a` the circle mean at `R/2` (`TZ`), so it is
bounded exactly when the mean is controlled by the norm on `Z_a`, together with the norm of the
constant `χ_Z` (`gZ`):

`|[h]_a|² (1 + |χ_Z|²_{Z_a}) ≤ K |h|²_{Z_a}`     (`TraceBound`).

`pi_uniform_of_traceBound` proves the uniform bound on `π_a` from `TraceBound`.
`TZ_sq_le`: `|[h]_a|² e^{δ_m R} ≤ K |h|²_{Z_a}` (the weight of (4.7) is `≥ e^{δ_m (R/2 - 1)}` on
`[R/2 - 1, R/2]`), so `TraceBound` follows from `|χ_Z|²_{Z_a} ≤ K e^{δ_m R}` (`ConstBound`,
`traceBound_of_constBound`).  `ConstBound` is proved for `δ_m > 0` in `GWMemoir.GluingUniformConst`.
-/

open Set Filter Topology MeasureTheory Finset
open scoped ENNReal NNReal
open Polyfold Polyfold.CylinderSobolev

namespace GWMemoir.Neck

/-- An infimum bound: `X ≤ a ⨅ f + b ⨅ g` from the bounds on each pair. -/
lemma le_mul_iInf_add_mul_iInf {ι κ : Sort*} [Nonempty ι] [Nonempty κ] {f : ι → ℝ≥0∞}
    {g : κ → ℝ≥0∞} {a b X : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    (h : ∀ i j, X ≤ a * f i + b * g j) : X ≤ a * (⨅ i, f i) + b * ⨅ j, g j := by
  rw [ENNReal.mul_iInf (fun h => absurd h ha), ENNReal.mul_iInf (fun h => absurd h hb),
    ENNReal.iInf_add]
  refine le_iInf fun i => ?_
  rw [ENNReal.add_iInf]
  exact le_iInf fun j => h i j

section Sq

variable {k : ℕ} {d : ℝ} {hd : 0 ≤ d}

/-- `|u - t v|² ≤ 2 |u|² + 2 t² |v|²` for the weighted squared norms. -/
lemma guSq_sub_smul_le {ω : ℝ → ℝ} (hω : Measurable ω) (t : ℝ) (u v : H k hd) :
    guSq ω (u - t • v) ≤ 2 * guSq ω u + 2 * ENNReal.ofReal (t ^ 2) * guSq ω v := by
  rw [guSq, guSq, guSq, Finset.mul_sum, mul_assoc, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun p _ => ?_
  have h1 := guDv_lin hω 1 (-t) u v p
  rw [one_smul, neg_smul, ← sub_eq_add_neg, enorm_one, one_mul, enorm_neg] at h1
  have ht : ‖t‖ₑ ^ 2 = ENNReal.ofReal (t ^ 2) := by
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg t), sq_abs]
  calc guDv ω (u - t • v) p ^ 2 ≤ (guDv ω u p + ‖t‖ₑ * guDv ω v p) ^ 2 := pow_le_pow_left' h1 2
    _ ≤ 2 * (guDv ω u p ^ 2 + (‖t‖ₑ * guDv ω v p) ^ 2) := ennreal_add_sq_le _ _
    _ = 2 * guDv ω u p ^ 2 + 2 * (ENNReal.ofReal (t ^ 2) * guDv ω v p ^ 2) := by
      rw [mul_pow, ht, mul_add]

end Sq

section Trace

/-- A pairing with a kernel on the slab `[σ - 1, σ] × S¹`, by a weighted `L²` norm: if `|g| ≤ M`
and `ω ≥ c > 0` on `[σ - 1, σ]`, then `|⟨g, f⟩| ≤ (M / c) ‖ω f‖`. -/
lemma enorm_pairing_trK_le {σ : ℝ} {g : ℝ → ℝ} (hg : Continuous g) {M c : ℝ} (hM0 : 0 ≤ M)
    (hc : 0 < c) (hM : ∀ s ∈ Icc (σ - 1) σ, |g s| ≤ M) {ω : ℝ → ℝ} (hω : Measurable ω)
    (hωc : ∀ s ∈ Icc (σ - 1) σ, c ≤ ω s) (f : Lp ℝ 2 cyl) :
    ENNReal.ofReal |pairing (trK σ g) (memLp_trK σ hg) f| ≤
      ENNReal.ofReal (M / c) * eLpNorm (fun x : ℝ × ℝ => ω x.1 * f x) 2 cyl := by
  set S := Icc (σ - 1) σ ×ˢ (univ : Set ℝ)
  have hS : MeasurableSet S := measurableSet_Icc.prod MeasurableSet.univ
  set φ : ℝ × ℝ → ℝ := S.indicator fun _ => M / c
  have hMc : 0 ≤ M / c := div_nonneg hM0 hc.le
  have hφ : eLpNorm φ 2 cyl = ENNReal.ofReal (M / c) := by
    rw [eLpNorm_indicator_const hS (by norm_num) (by norm_num), cyl_slab, sub_sub_cancel,
      ENNReal.ofReal_one, ENNReal.one_rpow, mul_one, Real.enorm_eq_ofReal hMc]
  rw [pairing_apply, ← Real.enorm_eq_ofReal_abs, ← hφ]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [← eLpNorm_one_eq_lintegral_enorm]
  refine (eLpNorm_mono (g := φ • fun x : ℝ × ℝ => ω x.1 * f x) fun x => ?_).trans
    (eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1)
      ((hω.comp measurable_fst).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
      (aestronglyMeasurable_const.indicator hS))
  simp only [Pi.mul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul, trK, φ]
  by_cases hx : x.1 ∈ Icc (σ - 1) σ
  · have hxS : x ∈ S := ⟨hx, mem_univ _⟩
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hxS, abs_of_nonneg hMc]
    have hw : c ≤ |ω x.1| := (hωc _ hx).trans (le_abs_self _)
    calc |f x| * |g x.1| ≤ |f x| * M := mul_le_mul_of_nonneg_left (hM _ hx) (abs_nonneg _)
      _ = M / c * (c * |f x|) := by field_simp
      _ ≤ M / c * (|ω x.1| * |f x|) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hw (abs_nonneg _)) hMc
  · rw [Set.indicator_of_notMem hx, abs_zero, mul_zero]
    positivity

end Trace

section Pi

variable (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

/-- The estimate of the circle mean `[h]_a` (at `s = R/2`) by the norm on `Z_a`, together with the
norm of the constant `χ_Z`: `|[h]_a|² (1 + |χ_Z|²_{Z_a}) ≤ K |h|²_{Z_a}`, uniformly in `R ≥ 2`. -/
def TraceBound (m : ℕ) : Prop :=
  ∃ K, 0 ≤ K ∧ ∀ R (hR2 : 2 ≤ R) (h : (scFin δ h0 hmono R) m),
    ENNReal.ofReal (TZ δ h0 hmono hR2 m h ^ 2) *
        (1 + guZSq 3 δ h0 hmono R m (gZ δ h0 hmono (R := R) m)) ≤
      ENNReal.ofReal K * guZSq 3 δ h0 hmono R m h

variable {δ h0 hmono}

/-- `|h - t g|²_{Z_a} ≤ 2 |h|²_{Z_a} + 2 t² |g|²_{Z_a}`. -/
lemma guZSq_sub_smul_le {ℓ : ℕ} {R : ℝ} {m : ℕ} (t : ℝ) (h g : (scFinOff ℓ δ h0 hmono R) m) :
    guZSq ℓ δ h0 hmono R m (h - t • g) ≤
      2 * guZSq ℓ δ h0 hmono R m h + 2 * ENNReal.ofReal (t ^ 2) * guZSq ℓ δ h0 hmono R m g := by
  obtain ⟨u0, hu0⟩ := Submodule.mkQ_surjective _ h
  obtain ⟨v0, hv0⟩ := Submodule.mkQ_surjective _ g
  have : Nonempty {u : H (ℓ + m) (δ_nonneg δ h0 hmono m) // qZo ℓ δ h0 hmono (R := R) m u = h} :=
    ⟨⟨u0, hu0⟩⟩
  have : Nonempty {u : H (ℓ + m) (δ_nonneg δ h0 hmono m) // qZo ℓ δ h0 hmono (R := R) m u = g} :=
    ⟨⟨v0, hv0⟩⟩
  refine le_mul_iInf_add_mul_iInf (by norm_num)
    (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top) fun u v => ?_
  refine (guZSq_le (u.1 - t • v.1) ?_).trans (guSq_sub_smul_le (measurable_guZ _ _) t _ _)
  rw [map_sub, map_smul, u.2, v.2]

/-- `[χ_Z]_a = 1`. -/
lemma TZ_gZ {R : ℝ} (hR2 : 2 ≤ R) (m : ℕ) :
    TZ δ h0 hmono hR2 m (gZ δ h0 hmono (R := R) m) = 1 := by
  change trH (hm3 m) (R / 2) (toH (3 + m) (δ_nonneg δ h0 hmono m) (isTest_chiZ R)) = 1
  rw [trH_toH_s]
  exact chiZ_one ⟨by linarith, by linarith⟩

/-- The norm `guGSq` of `(⊕_a, 0)(y) = (q, 0)`. -/
lemma guGSq_gIn {R : ℝ} (hR2 : 2 ≤ R) (m : ℕ) (v : (scFin δ h0 hmono R) m) :
    guGSq δ h0 hmono hR2 m (gIn δ h0 hmono (R := R) m v) =
      ENNReal.ofReal (TZ δ h0 hmono hR2 m v ^ 2) +
        guZSq 3 δ h0 hmono R m (v - TZ δ h0 hmono hR2 m v • gZ δ h0 hmono (R := R) m) := by
  have hc : cPsi δ h0 hmono hR2 m (gIn δ h0 hmono (R := R) m v) = TZ δ h0 hmono hR2 m v := by
    change TZ δ h0 hmono hR2 m v - 0 = _
    rw [sub_zero]
  unfold guGSq
  rw [hc]
  change _ + (_ + guSq (guC (δ m) R) (0 : H (3 + m) (δ_nonneg δ h0 hmono m))) = _
  rw [guSq_zero (measurable_guC _ _), add_zero]
  rfl

/-- The map `(q, p) ↦ (q, 0)` on `G^a_m` is bounded for `guGSq`, uniformly in `R`, given
`TraceBound`. -/
lemma guGSq_gIn_le (m : ℕ) (hT : TraceBound δ h0 hmono m) : ∃ A, 0 ≤ A ∧
    ∀ R (hR2 : 2 ≤ R) (y : (scG δ h0 hmono R) m),
      guGSq δ h0 hmono hR2 m (gIn δ h0 hmono (R := R) m (qrV δ h0 hmono m y)) ≤
        ENNReal.ofReal A * guGSq δ h0 hmono hR2 m y := by
  obtain ⟨K, hK, hT⟩ := hT
  refine ⟨4 * K + 2, by positivity, fun R hR2 y => ?_⟩
  set v := qrV δ h0 hmono m y
  set c := cPsi δ h0 hmono hR2 m y
  set g := gZ δ h0 hmono (R := R) m
  set h := v - c • g with hh
  set t := TZ δ h0 hmono hR2 m h
  have hv : TZ δ h0 hmono hR2 m v = t + c := by
    have : t = TZ δ h0 hmono hR2 m v - c := by
      change TZ δ h0 hmono hR2 m (v - c • g) = _
      rw [map_sub, map_smul, TZ_gZ hR2 m, smul_eq_mul, mul_one]
    rw [this]; ring
  have hres : v - TZ δ h0 hmono hR2 m v • g = h - t • g := by
    rw [hv, hh, add_smul]; abel
  rw [guGSq_gIn hR2 m v, hres, hv]
  set Z := guZSq 3 δ h0 hmono R m h
  set G := guZSq 3 δ h0 hmono R m g
  set T := ENNReal.ofReal (t ^ 2)
  set W := guSq (guC (δ m) R) (qrW δ h0 hmono m y)
  have hy : guGSq δ h0 hmono hR2 m y = ENNReal.ofReal (c ^ 2) + (Z + W) := rfl
  have hTK := hT R hR2 h
  have hT1 : T ≤ ENNReal.ofReal K * Z :=
    (le_mul_of_one_le_right bot_le le_self_add).trans hTK
  have hT2 : T * G ≤ ENNReal.ofReal K * Z :=
    (mul_le_mul_right (le_add_self) T).trans hTK
  have hsq : ENNReal.ofReal ((t + c) ^ 2) ≤ 2 * T + 2 * ENNReal.ofReal (c ^ 2) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (t - c)])
  have hZ := guZSq_sub_smul_le (h0 := h0) (hmono := hmono) (ℓ := 3) (R := R) (m := m) t h g
  have hA : ENNReal.ofReal (4 * K + 2) = 4 * ENNReal.ofReal K + 2 := by
    rw [ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_mul (by norm_num)]
    norm_num
  rw [hy, hA]
  calc ENNReal.ofReal ((t + c) ^ 2) + guZSq 3 δ h0 hmono R m (h - t • g)
      ≤ (2 * T + 2 * ENNReal.ofReal (c ^ 2)) + (2 * Z + 2 * T * G) := add_le_add hsq hZ
    _ ≤ (2 * (ENNReal.ofReal K * Z) + 2 * ENNReal.ofReal (c ^ 2)) +
        (2 * Z + 2 * (ENNReal.ofReal K * Z)) := by
      rw [mul_assoc 2 T G]
      gcongr
    _ ≤ (4 * ENNReal.ofReal K + 2) * (ENNReal.ofReal (c ^ 2) + (Z + W)) := by
      have e : (2 * (ENNReal.ofReal K * Z) + 2 * ENNReal.ofReal (c ^ 2)) +
          (2 * Z + 2 * (ENNReal.ofReal K * Z)) =
          (4 * ENNReal.ofReal K + 2) * Z + 2 * ENNReal.ofReal (c ^ 2) := by ring
      rw [e, mul_add, mul_add]
      have h2 : 2 * ENNReal.ofReal (c ^ 2) ≤ (4 * ENNReal.ofReal K + 2) * ENNReal.ofReal (c ^ 2) :=
        mul_le_mul_left le_add_self _
      calc (4 * ENNReal.ofReal K + 2) * Z + 2 * ENNReal.ofReal (c ^ 2)
          ≤ (4 * ENNReal.ofReal K + 2) * Z + (4 * ENNReal.ofReal K + 2) * ENNReal.ofReal (c ^ 2) :=
            add_le_add le_rfl h2
        _ ≤ (4 * ENNReal.ofReal K + 2) * ENNReal.ofReal (c ^ 2) +
            ((4 * ENNReal.ofReal K + 2) * Z + (4 * ENNReal.ofReal K + 2) * W) := by
          rw [add_comm]; gcongr; exact le_self_add


/-- The circle mean on `Z_a` by the weighted norm (4.7): `|[h]_a|² e^{δ_m R} ≤ K |h|²_{Z_a}`,
uniformly in `R ≥ 2` (the weight of (4.7) is `≥ e^{δ_m (R/2 - 1)}` on `[R/2 - 1, R/2]`). -/
lemma TZ_sq_le (m : ℕ) : ∃ K, 0 ≤ K ∧ ∀ R (hR2 : 2 ≤ R) (h : (scFin δ h0 hmono R) m),
    ENNReal.ofReal (TZ δ h0 hmono hR2 m h ^ 2) * ENNReal.ofReal (Real.exp (δ m * R)) ≤
      ENNReal.ofReal K * guZSq 3 δ h0 hmono R m h := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 0)).exists_bound_of_continuousOn
    continuous_deriv_trCut.continuousOn
  set d := δ m
  have hd : 0 ≤ d := δ_nonneg δ h0 hmono m
  set N := Fintype.card (idx (3 + m))
  set B := 2 * (1 + |M|)
  have hB : 0 ≤ B := by positivity
  refine ⟨B ^ 2 * Real.exp (2 * d) * N, by positivity, fun R hR2 h => ?_⟩
  obtain ⟨u0, hu0⟩ := Submodule.mkQ_surjective _ h
  have : Nonempty {u : H (3 + m) (δ_nonneg δ h0 hmono m) // qZo 3 δ h0 hmono (R := R) m u = h} :=
    ⟨⟨u0, hu0⟩⟩
  unfold guZSq
  rw [ENNReal.mul_iInf (fun h => absurd h ENNReal.ofReal_ne_top)]
  refine le_iInf fun u => ?_
  obtain ⟨u, rfl⟩ := u
  set c := Real.exp (d * (R / 2 - 1))
  have hc : 0 < c := Real.exp_pos _
  have hωc : ∀ s ∈ Icc (R / 2 - 1) (R / 2), c ≤ guZ d R s := fun s hs => by
    refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (le_min ?_ ?_) hd)
    · exact hs.1.trans (le_abs_self s)
    · linarith [neg_le_abs (s - R), hs.2]
  have hω := measurable_guZ d R
  have hK1 : ∀ s ∈ Icc (R / 2 - 1) (R / 2), |trCut (s - R / 2)| ≤ 1 + |M| := fun s _ => by
    have h1 := Real.smoothTransition.le_one (2 * (s - R / 2) + 2)
    have h2 := Real.smoothTransition.nonneg (2 * (s - R / 2) + 2)
    rw [trCut, abs_of_nonneg h2]; linarith [abs_nonneg M]
  have hK0 : ∀ s ∈ Icc (R / 2 - 1) (R / 2), |deriv trCut (s - R / 2)| ≤ 1 + |M| := fun s hs => by
    have := hM (s - R / 2) ⟨by linarith [hs.1], by linarith [hs.2]⟩
    rw [Real.norm_eq_abs] at this
    linarith [le_abs_self M]
  have e1 := enorm_pairing_trK_le (contDiff_trCut.continuous.comp (continuous_sub_right (R / 2)))
    (by positivity) hc hK1 hω hωc (dvCLM (3 + m) (δ_nonneg δ h0 hmono m) (p10 (hm3 m)) u)
  have e0 := enorm_pairing_trK_le (continuous_deriv_trCut.comp (continuous_sub_right (R / 2)))
    (by positivity) hc hK0 hω hωc (valCLM (3 + m) (δ_nonneg δ h0 hmono m) u)
  have g1 : eLpNorm (fun x : ℝ × ℝ =>
      guZ d R x.1 * dvCLM (3 + m) (δ_nonneg δ h0 hmono m) (p10 (hm3 m)) u x) 2 cyl =
      guDv (guZ d R) u (p10 (hm3 m)) := by
    unfold guDv
    refine eLpNorm_congr_ae ?_
    filter_upwards [coeFn_dvCLM (p10 (hm3 m)) u] with x hx
    rw [hx]
  have g0 : eLpNorm (fun x : ℝ × ℝ =>
      guZ d R x.1 * valCLM (3 + m) (δ_nonneg δ h0 hmono m) u x) 2 cyl =
      guDv (guZ d R) u (idx0 (3 + m)) := by
    unfold guDv
    refine eLpNorm_congr_ae ?_
    filter_upwards [dv_idx0 (H.toSub u)] with x hx
    rw [hx, valCLM_apply]
  rw [g1] at e1
  rw [g0] at e0
  have htr : TZ δ h0 hmono hR2 m (qZo 3 δ h0 hmono (R := R) m u) =
      pairing (trK (R / 2) fun s => trCut (s - R / 2))
          (memLp_trK (R / 2) (contDiff_trCut.continuous.comp (continuous_sub_right (R / 2))))
          (dvCLM (3 + m) (δ_nonneg δ h0 hmono m) (p10 (hm3 m)) u) +
        pairing (trK (R / 2) fun s => deriv trCut (s - R / 2))
          (memLp_trK (R / 2) (continuous_deriv_trCut.comp (continuous_sub_right (R / 2))))
          (valCLM (3 + m) (δ_nonneg δ h0 hmono m) u) := rfl
  set S := guSum (guZ d R) u
  have hs1 : guDv (guZ d R) u (p10 (hm3 m)) ≤ S :=
    Finset.single_le_sum (f := fun p => guDv (guZ d R) u p) (fun _ _ => bot_le) (Finset.mem_univ _)
  have hs0 : guDv (guZ d R) u (idx0 (3 + m)) ≤ S :=
    Finset.single_le_sum (f := fun p => guDv (guZ d R) u p) (fun _ _ => bot_le) (Finset.mem_univ _)
  have hlin : ENNReal.ofReal |TZ δ h0 hmono hR2 m (qZo 3 δ h0 hmono (R := R) m u)| ≤
      ENNReal.ofReal (B / c) * S := by
    rw [htr]
    calc _ ≤ ENNReal.ofReal (|pairing (trK (R / 2) fun s => trCut (s - R / 2))
            (memLp_trK (R / 2) (contDiff_trCut.continuous.comp (continuous_sub_right (R / 2))))
            (dvCLM (3 + m) (δ_nonneg δ h0 hmono m) (p10 (hm3 m)) u)| +
          |pairing (trK (R / 2) fun s => deriv trCut (s - R / 2))
            (memLp_trK (R / 2) (continuous_deriv_trCut.comp (continuous_sub_right (R / 2))))
            (valCLM (3 + m) (δ_nonneg δ h0 hmono m) u)|) :=
          ENNReal.ofReal_le_ofReal (abs_add_le _ _)
      _ ≤ ENNReal.ofReal ((1 + |M|) / c) * S + ENNReal.ofReal ((1 + |M|) / c) * S := by
          rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
          exact add_le_add (e1.trans (mul_le_mul_right hs1 _)) (e0.trans (mul_le_mul_right hs0 _))
      _ = ENNReal.ofReal (B / c) * S := by
          rw [← two_mul, ← mul_assoc, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
            ← ENNReal.ofReal_mul (by norm_num), mul_div_assoc]
  have hsq : ENNReal.ofReal (TZ δ h0 hmono hR2 m (qZo 3 δ h0 hmono (R := R) m u) ^ 2) ≤
      ENNReal.ofReal (B / c) ^ 2 * ((N : ℝ≥0∞) * guSq (guZ d R) u) := by
    rw [← sq_abs, ENNReal.ofReal_pow (abs_nonneg _)]
    exact (pow_le_pow_left' hlin 2).trans (by rw [mul_pow]; exact mul_le_mul_right (guSum_sq_le _ _) _)
  have hc2 : c ^ 2 * Real.exp (2 * d) = Real.exp (d * R) := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hK : ENNReal.ofReal (B / c) ^ 2 * (N : ℝ≥0∞) * ENNReal.ofReal (Real.exp (d * R)) =
      ENNReal.ofReal (B ^ 2 * Real.exp (2 * d) * N) := by
    rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ← hc2]
    congr 1
    field_simp
  calc _ ≤ ENNReal.ofReal (B / c) ^ 2 * ((N : ℝ≥0∞) * guSq (guZ d R) u) *
        ENNReal.ofReal (Real.exp (d * R)) := mul_le_mul_left hsq _
    _ = ENNReal.ofReal (B ^ 2 * Real.exp (2 * d) * N) * guSq (guZ d R) u := by
      rw [← hK]; ring

variable (δ h0 hmono) in
/-- The norm of the constant `χ_Z` on `Z_a`: `|χ_Z|²_{Z_a} ≤ K e^{δ_m R}`, uniformly in `R ≥ 2`. -/
def ConstBound (m : ℕ) : Prop :=
  ∃ K, 0 ≤ K ∧ ∀ R, 2 ≤ R →
    guZSq 3 δ h0 hmono R m (gZ δ h0 hmono (R := R) m) ≤
      ENNReal.ofReal K * ENNReal.ofReal (Real.exp (δ m * R))

/-- `TraceBound` from `ConstBound`. -/
theorem traceBound_of_constBound (m : ℕ) (hN : ConstBound δ h0 hmono m) :
    TraceBound δ h0 hmono m := by
  obtain ⟨K1, hK1, h1⟩ := TZ_sq_le (δ := δ) (h0 := h0) (hmono := hmono) m
  obtain ⟨K2, hK2, h2⟩ := hN
  refine ⟨K1 + K2 * K1, by positivity, fun R hR2 h => ?_⟩
  have hd : 0 ≤ δ m * R := mul_nonneg (δ_nonneg δ h0 hmono m) (by linarith)
  set T := ENNReal.ofReal (TZ δ h0 hmono hR2 m h ^ 2)
  set E := ENNReal.ofReal (Real.exp (δ m * R))
  set Z := guZSq 3 δ h0 hmono R m h
  have hE : 1 ≤ E := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (Real.one_le_exp hd)
  have hTZ := h1 R hR2 h
  rw [mul_add, mul_one, ENNReal.ofReal_add hK1 (by positivity), ENNReal.ofReal_mul hK2, add_mul,
    mul_assoc]
  refine add_le_add ((le_mul_of_one_le_right bot_le hE).trans hTZ) ?_
  calc T * guZSq 3 δ h0 hmono R m (gZ δ h0 hmono (R := R) m) ≤ T * (ENNReal.ofReal K2 * E) :=
        mul_le_mul_right (h2 R hR2) _
    _ = ENNReal.ofReal K2 * (T * E) := by ring
    _ ≤ ENNReal.ofReal K2 * (ENNReal.ofReal K1 * Z) := mul_le_mul_right hTZ _

variable {β : ℝ → ℝ} (hβ : IsCutoff β)

/-- **The projection `π_a`, uniformly in `a`** (Memoir pp. 50, 108): given `TraceBound`, there is
`C > 0` with `‖π_a x‖ ≤ C ‖x‖` for all `R ≥ 2` and twists `ϑ`. -/
theorem pi_uniform_of_traceBound (m : ℕ) (hT : TraceBound δ h0 hmono m) :
    ∃ C, 0 < C ∧ ∀ R (hR2 : 2 ≤ R) ϑ (x : (scPair δ h0 hmono) m),
      ‖piLvl δ h0 hmono hβ hR2 ϑ m x‖ ≤ C * ‖x‖ := by
  obtain ⟨C, hC, h414⟩ := memoir_proposition_4_14_off hβ (δ := δ) (h0 := h0) (hmono := hmono) m
  obtain ⟨A, hA, hgIn⟩ := guGSq_gIn_le m hT
  refine ⟨C * Real.sqrt (A + 1), by positivity, fun R hR2 ϑ x => ?_⟩
  set y := Phi δ h0 hmono hβ hR2 ϑ m x
  have hpi : Phi δ h0 hmono hβ hR2 ϑ m (piLvl δ h0 hmono hβ hR2 ϑ m x) =
      gIn δ h0 hmono (R := R) m (qrV δ h0 hmono m y) := phi_piLvl δ h0 hmono hβ hR2 ϑ m x
  have h1 := (h414 R hR2 ϑ (piLvl δ h0 hmono hβ hR2 ϑ m x)).1
  rw [hpi] at h1
  have h2 := (h414 R hR2 ϑ x).2
  have hA1 : ENNReal.ofReal A ≤ ENNReal.ofReal (A + 1) := ENNReal.ofReal_le_ofReal (by linarith)
  have key : ENNReal.ofReal (‖piLvl δ h0 hmono hβ hR2 ϑ m x‖ ^ 2) ≤
      ENNReal.ofReal (C ^ 2 * (A + 1) * ‖x‖ ^ 2) := by
    calc _ ≤ ENNReal.ofReal C * guGSq δ h0 hmono hR2 m
          (gIn δ h0 hmono (R := R) m (qrV δ h0 hmono m y)) := h1
      _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (A + 1) * (ENNReal.ofReal C *
          ENNReal.ofReal (‖x‖ ^ 2))) :=
        mul_le_mul_right ((hgIn R hR2 y).trans (mul_le_mul hA1 h2 bot_le bot_le)) _
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul hC.le]
        congr 1; ring
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at key
  have e : (C * Real.sqrt (A + 1) * ‖x‖) ^ 2 = C ^ 2 * (A + 1) * ‖x‖ ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 (e ▸ key)

/-- The same in terms of the gluing parameter: for every `0 < |a| < 1/2`. -/
theorem pi_uniform_of_traceBound_a (m : ℕ) (hT : TraceBound δ h0 hmono m) :
    ∃ C, 0 < C ∧ ∀ {a : ℂ} (ha0 : a ≠ 0) (ha : ‖a‖ < 1 / 2) (x : (scPair δ h0 hmono) m),
      ‖piLvl δ h0 hmono hβ (two_le_glLength ha0 ha) (glTwist a) m x‖ ≤ C * ‖x‖ := by
  obtain ⟨C, hC, h⟩ := pi_uniform_of_traceBound hβ m hT
  exact ⟨C, hC, fun ha0 ha x => h _ _ _ x⟩

end Pi

end GWMemoir.Neck
