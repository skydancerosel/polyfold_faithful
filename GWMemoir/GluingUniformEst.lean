import GWMemoir.GluingUniform

/-!
# Memoir §4.3, Propositions 4.13 and 4.14: the total gluing estimates, uniform in `a`

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §4.3, pp. 107–108.

The memoir recalls these two estimates from its reference [28] (Theorems 2.26 and 2.23 there);
here they are proved, with the norms of `GWMemoir.GluingUniform`.

**The norms.**  On level `m` (weight `δ_m`, offset `ℓ`: `ℓ + m` derivatives), for
`(q, p) ∈ Ĝ^a_m = H^{ℓ+m}(Z_a) ⊕ H^{ℓ+m,δ_m}(C_a)`,
`|(q, p)|²_{Ĝ^a_m} = e^{δ_m R} (‖q‖²_{ℓ+m,-δ_m} + ‖p‖²_{ℓ+m,δ_m})` with the centred norms (4.7), (4.8)
(`guGHatSq`).  The part on `Z_a` is taken, as for the other restriction spaces of
`GWMemoir.HalfCylinders`, as the infimum over the representatives on `ℝ × S¹` of the weighted norm
with weight `guZ`, which on `[0, R]` is the weight of (4.7) (`guZSq`, `memoirNormSq47_le`).  For
`(q, p) ∈ G^a_m` (`p = (1 - 2β_a) p_∞ + p̂`, `p̂ = w`):
`|(q, p)|²_{G^a_m} = |[q]_a - p_∞|² + e^{δ_m R} (‖q - [q]_a + p_∞‖²_{3+m,-δ_m} + ‖p̂‖²_{3+m,δ_m})`
(`guGSq`).

**Readings** (p. 108).
* The memoir prints `e^{δ_m R}` in front of the `Z_a` term only.  The estimates are proved with the
  factor in front of both terms, as in the use of the estimates on p. 172, (5.51):
  `e^{δ_m R_k/2} ‖⊖_{a_k}(y_k)‖_{m+2,δ_m} ≤ |Φ_{a_k}(y_k)|_{G^{a_k}_m}`.  With the factor on the first
  term only, the upper bounds still hold (the printed norm is smaller); the lower bounds do not
  hold as we read it: for `ξ⁺` supported in `R ≤ s ≤ R + 1` and `ξ⁻ = 0`, `|ξ|_F ≈ e^{δR} ‖ξ⁺(· + R)‖`
  while the printed norm of `Φ̂_a ξ` is `≈ e^{δR/2} ‖ξ⁺(· + R)‖`.
* The `G^a_m` norm carries the index `m + 2`; the level is `H^{3+m}`, and it is read as `m + 3`.

**Statements.**  `memoir_proposition_4_13` (with `ℓ`; `ℓ = 2` is the memoir's), and
`memoir_proposition_4_14`: for every `m` there is `C > 0` such that for every `0 < |a| < 1/2`
(`R = φ(|a|)`, `ϑ` the twist of `a`) `C⁻¹ |ξ|² ≤ |Φ̂_a ξ|² ≤ C |ξ|²`, i.e. the memoir's
inequalities with `C_m = √C`.  `piHat_uniform`: `‖π̂_a ξ‖ ≤ C ‖ξ‖` with `C`
independent of `a`.
-/

open Set Filter Topology MeasureTheory Finset
open scoped ENNReal NNReal
open Polyfold Polyfold.CylinderSobolev

set_option linter.unusedSectionVars false

noncomputable section

namespace GWMemoir.Neck

/-! ## 1. The eight pieces of `Φ̂_a` and `Φ̂_a⁻¹`, with constants independent of `R` -/

lemma measurable_guE_sub (d R : ℝ) : Measurable fun s => guE d (s - R) :=
  ((continuous_guE d).comp (continuous_id.sub continuous_const)).measurable

lemma guE_shift (d R s : ℝ) : |guE d s| ≤ |(fun s => guE d (s - R)) (s - -R)| := by
  simp only [sub_neg_eq_add, add_sub_cancel_right, le_refl]

section Pieces

variable {β : ℝ → ℝ} (hβ : IsCutoff β) {k : ℕ} {d : ℝ} (hd : 0 ≤ d) {hd' : 0 ≤ d}
include hβ hd

/-- `ξ⁺ ↦ β_a ξ⁺`, from `e^{d|s|}` to `guZ`. -/
lemma guAP : ∃ K, 0 ≤ K ∧ ∀ R (u : H k hd'),
    guSum (guZ d R) (mulHL _ (m1 hβ R k) u) ≤ ENNReal.ofReal K * guSum (guE d) u := by
  obtain ⟨C, hC0, hC⟩ := bound_Fβa hβ (F := fun b => b) contDiff_id k
  refine ⟨multK k (C * Real.exp (d * 0)), multK_nonneg k (by positivity), fun R u => ?_⟩
  exact guSum_mulHL (measurable_guE d) _ (by positivity) (multHyp hC0 (by positivity) (hC R)
    (fun s => (guZ_pos d R s).le) fun i _ s => Or.inr (w1 hd)) u

/-- `ξ⁻ ↦ (1 - β_a) τ ξ⁻`, from `e^{d|s|}` to `guZ`. -/
lemma guAN : ∃ K, 0 ≤ K ∧ ∀ R ϑ (u : H k hd'),
    guSum (guZ d R) (mulHL _ (m2 hβ R k) (shH R ϑ u)) ≤ ENNReal.ofReal K * guSum (guE d) u := by
  obtain ⟨C, hC0, hC⟩ := bound_Fβa hβ (F := fun b => 1 - b) (contDiff_const.sub contDiff_id) k
  refine ⟨multK k (C * Real.exp (d * 0)), multK_nonneg k (by positivity), fun R ϑ u => ?_⟩
  refine (guSum_mulHL (measurable_guE_sub d R) _ (by positivity) (multHyp hC0 (by positivity)
    (hC R) (fun s => (guZ_pos d R s).le) fun i _ s => Or.inr (w2 hd)) _).trans ?_
  exact mul_le_mul_right (guSum_shH (measurable_guE d) (fun s => le_refl _) ϑ u) _

/-- `ξ⁺ ↦ (β_a - 1) ξ⁺`, from `e^{d|s|}` to `guC`. -/
lemma guBP : ∃ K, 0 ≤ K ∧ ∀ R, 2 ≤ R → ∀ (u : H k hd'),
    guSum (guC d R) (mulHL _ (m5 hβ R k) u) ≤ ENNReal.ofReal K * guSum (guE d) u := by
  obtain ⟨C, hC0, hC⟩ := bound_Fβa hβ (F := fun b => b - 1) (contDiff_id.sub contDiff_const) k
  refine ⟨multK k (C * Real.exp (d * 2)), multK_nonneg k (by positivity), fun R hR u => ?_⟩
  refine guSum_mulHL (measurable_guE d) _ (by positivity) (multHyp hC0 (by positivity) (hC R)
    (fun s => (guC_pos d R s).le) fun i _ s => ?_) u
  rcases lt_or_ge s (R / 2 - 1) with hs | hs
  · exact Or.inl (iteratedDeriv_Fβa_lo hβ (F := fun b => b - 1) (by norm_num) hs i)
  · exact Or.inr (w3 hd hR hs)

/-- `ξ⁻ ↦ β_a τ ξ⁻`, from `e^{d|s|}` to `guC`. -/
lemma guBN : ∃ K, 0 ≤ K ∧ ∀ R, 2 ≤ R → ∀ ϑ (u : H k hd'),
    guSum (guC d R) (mulHL _ (m1 hβ R k) (shH R ϑ u)) ≤ ENNReal.ofReal K * guSum (guE d) u := by
  obtain ⟨C, hC0, hC⟩ := bound_Fβa hβ (F := fun b => b) contDiff_id k
  refine ⟨multK k (C * Real.exp (d * 2)), multK_nonneg k (by positivity), fun R hR ϑ u => ?_⟩
  refine (guSum_mulHL (measurable_guE_sub d R) _ (by positivity) (multHyp hC0 (by positivity)
    (hC R) (fun s => (guC_pos d R s).le) fun i _ s => ?_) _).trans
    (mul_le_mul_right (guSum_shH (measurable_guE d) (fun s => le_refl _) ϑ u) _)
  rcases lt_or_ge (R / 2 + 1) s with hs | hs
  · exact Or.inl (iteratedDeriv_Fβa_hi hβ (F := fun b => b) rfl hs i)
  · exact Or.inr (w4 hd hR hs)

/-- `v ↦ (β_a/γ_a) v`, from `guZ` to `e^{d|s|}`. -/
lemma guPP : ∃ K, 0 ≤ K ∧ ∀ R, 2 ≤ R → ∀ (u : H k hd'),
    guSum (guE d) (mulHL _ (m3 hβ R k) u) ≤ ENNReal.ofReal K * guSum (guZ d R) u := by
  obtain ⟨C, hC0, hC⟩ := bound_Fβa hβ contDiff_F3 k
  refine ⟨multK k (C * Real.exp (d * 2)), multK_nonneg k (by positivity), fun R hR u => ?_⟩
  refine guSum_mulHL (measurable_guZ d R) _ (by positivity) (multHyp hC0 (by positivity) (hC R)
    (fun s => (guE_pos d s).le) fun i _ s => ?_) u
  rcases lt_or_ge (R / 2 + 1) s with hs | hs
  · exact Or.inl (iteratedDeriv_Fβa_hi hβ F3_zero hs i)
  · exact Or.inr (w5 hd hR hs)

/-- `w ↦ ((1 - β_a)/γ_a) w`, from `guC` to `e^{d|s|}`. -/
lemma guWP : ∃ K, 0 ≤ K ∧ ∀ R, 2 ≤ R → ∀ (u : H k hd'),
    guSum (guE d) (mulHL _ (m4 hβ R k) u) ≤ ENNReal.ofReal K * guSum (guC d R) u := by
  obtain ⟨C, hC0, hC⟩ := bound_Fβa hβ contDiff_F4 k
  refine ⟨multK k (C * Real.exp (d * 0)), multK_nonneg k (by positivity), fun R hR u => ?_⟩
  refine guSum_mulHL (measurable_guC d R) _ (by positivity) (multHyp hC0 (by positivity) (hC R)
    (fun s => (guE_pos d s).le) fun i _ s => ?_) u
  rcases lt_or_ge s (R / 2 - 1) with hs | hs
  · exact Or.inl (iteratedDeriv_Fβa_lo hβ F4_one hs i)
  · exact Or.inr (w6 hd hR hs)

/-- `v ↦ τ⁻¹((1 - β_a)/γ_a) v`, from `guZ` to `e^{d|s|}`. -/
lemma guPN : ∃ K, 0 ≤ K ∧ ∀ R, 2 ≤ R → ∀ ϑ (u : H k hd'),
    guSum (guE d) (shH (-R) (-ϑ) (mulHL _ (m4 hβ R k) u)) ≤
      ENNReal.ofReal K * guSum (guZ d R) u := by
  obtain ⟨C, hC0, hC⟩ := bound_Fβa hβ contDiff_F4 k
  refine ⟨multK k (C * Real.exp (d * 2)), multK_nonneg k (by positivity), fun R hR ϑ u => ?_⟩
  refine (guSum_shH (measurable_guE_sub d R) (guE_shift d R) (-ϑ) _).trans ?_
  refine guSum_mulHL (measurable_guZ d R) _ (by positivity) (multHyp hC0 (by positivity) (hC R)
    (fun s => (guE_pos d _).le) fun i _ s => ?_) u
  rcases lt_or_ge s (R / 2 - 1) with hs | hs
  · exact Or.inl (iteratedDeriv_Fβa_lo hβ F4_one hs i)
  · exact Or.inr (w7 hd hR hs)

/-- `w ↦ τ⁻¹(β_a/γ_a) w`, from `guC` to `e^{d|s|}`. -/
lemma guWN : ∃ K, 0 ≤ K ∧ ∀ R, 2 ≤ R → ∀ ϑ (u : H k hd'),
    guSum (guE d) (shH (-R) (-ϑ) (mulHL _ (m3 hβ R k) u)) ≤
      ENNReal.ofReal K * guSum (guC d R) u := by
  obtain ⟨C, hC0, hC⟩ := bound_Fβa hβ contDiff_F3 k
  refine ⟨multK k (C * Real.exp (d * 0)), multK_nonneg k (by positivity), fun R hR ϑ u => ?_⟩
  refine (guSum_shH (measurable_guE_sub d R) (guE_shift d R) (-ϑ) _).trans ?_
  refine guSum_mulHL (measurable_guC d R) _ (by positivity) (multHyp hC0 (by positivity) (hC R)
    (fun s => (guE_pos d _).le) fun i _ s => ?_) u
  rcases lt_or_ge (R / 2 + 1) s with hs | hs
  · exact Or.inl (iteratedDeriv_Fβa_hi hβ F3_zero hs i)
  · exact Or.inr (w8 hd hR hs)

end Pieces

/-! ## 2. The norm of `Ĝ^a_m` and Proposition 4.13 -/

lemma ofReal_lin {x y K1 K2 K : ℝ} {N : ℕ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hK1 : 0 ≤ K1)
    (hK2 : 0 ≤ K2) (h1 : K1 ≤ K) (h2 : K2 ≤ K) {X Y : ℝ≥0∞} (hX : X ≤ N * ENNReal.ofReal x)
    (hY : Y ≤ N * ENNReal.ofReal y) :
    ENNReal.ofReal K1 * X + ENNReal.ofReal K2 * Y ≤ ENNReal.ofReal (K * N * (x + y)) := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have e : ∀ {K' z : ℝ}, 0 ≤ K' → 0 ≤ z →
      ENNReal.ofReal K' * ((N : ℝ≥0∞) * ENNReal.ofReal z) = ENNReal.ofReal (K' * N * z) := by
    intro K' z hK' hz
    rw [ENNReal.ofReal_mul (mul_nonneg hK' hN), ENNReal.ofReal_mul hK', ENNReal.ofReal_natCast,
      mul_assoc]
  calc ENNReal.ofReal K1 * X + ENNReal.ofReal K2 * Y
      ≤ ENNReal.ofReal K1 * (N * ENNReal.ofReal x) + ENNReal.ofReal K2 * (N * ENNReal.ofReal y) :=
        add_le_add (mul_le_mul_right hX _) (mul_le_mul_right hY _)
    _ = ENNReal.ofReal (K1 * N * x + K2 * N * y) := by
        rw [e hK1 hx, e hK2 hy, ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
        nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 h1) hN) hx,
          mul_nonneg (mul_nonneg (sub_nonneg.2 h2) hN) hy])

lemma card_idx_pos (k : ℕ) : 0 < Fintype.card (idx k) := Fintype.card_pos_iff.2 ⟨idx0 k⟩

section Hat

variable (ℓ : ℕ) (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

/-- The squared norm on `H^{ℓ+m}(Z_a)`: (4.7) with weight `-δ_m`, times `e^{δ_m R}`, as the
restriction norm (infimum over the representatives on `ℝ × S¹`, weight `guZ`). -/
def guZSq (R : ℝ) (m : ℕ) (v : (scFinOff ℓ δ h0 hmono R) m) : ℝ≥0∞ :=
  ⨅ u : {u : H (ℓ + m) (δ_nonneg δ h0 hmono m) // qZo ℓ δ h0 hmono (R := R) m u = v},
    guSq (guZ (δ m) R) u.1

/-- The squared norm of `Ĝ^a_m = H^{ℓ+m}(Z_a) ⊕ H^{ℓ+m,δ_m}(C_a)` (Memoir p. 108, for `ℓ = 2`):
`|(q, p)|² = e^{δ_m R} (‖q‖²_{ℓ+m,-δ_m} + ‖p‖²_{ℓ+m,δ_m})`, the factor `e^{δ_m R}` in front of both
terms (see the readings above). -/
def guGHatSq (R : ℝ) (m : ℕ) (y : (scGHat ℓ δ h0 hmono R) m) : ℝ≥0∞ :=
  guZSq ℓ δ h0 hmono R m y.1 + guSq (guC (δ m) R) y.2

variable {ℓ δ h0 hmono}

lemma guZSq_le {R : ℝ} {m : ℕ} {v : (scFinOff ℓ δ h0 hmono R) m}
    (u : H (ℓ + m) (δ_nonneg δ h0 hmono m)) (hu : qZo ℓ δ h0 hmono (R := R) m u = v) :
    guZSq ℓ δ h0 hmono R m v ≤ guSq (guZ (δ m) R) u :=
  iInf_le_of_le ⟨u, hu⟩ le_rfl

/-- The norm is finite. -/
lemma guGHatSq_lt_top {R : ℝ} (hR : 0 ≤ R) {m : ℕ} (y : (scGHat ℓ δ h0 hmono R) m) :
    guGHatSq ℓ δ h0 hmono R m y < ⊤ := by
  obtain ⟨u, hu⟩ := Submodule.mkQ_surjective _ y.1
  have hd := δ_nonneg δ h0 hmono m
  refine ENNReal.add_lt_top.2 ⟨(guZSq_le u hu).trans_lt (guSq_lt_top zero_le_one (fun s => ?_) u),
    guSq_lt_top (Real.exp_pos (δ m * R)).le (fun s => ?_) _⟩
  · rw [one_mul, abs_of_pos (guZ_pos _ _ _), abs_of_pos (guE_pos _ _)]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (min_le_left _ _) hd)
  · rw [abs_of_pos (guC_pos _ _ _), abs_of_pos (guE_pos _ _), guC, guE, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left (max_le ?_ ?_) hd
    · linarith [le_abs_self s]
    · linarith [neg_abs_le s]

variable {β : ℝ → ℝ} (hβ : IsCutoff β)

/-- The upper bound on representatives. -/
lemma hat_upper_reps (m : ℕ) : ∃ A, 0 ≤ A ∧ ∀ R (hR2 : 2 ≤ R) ϑ
    (a b : H (ℓ + m) (δ_nonneg δ h0 hmono m)),
    guGHatSq ℓ δ h0 hmono R m (PhiHat ℓ δ h0 hmono hβ hR2 ϑ m
      (qPo ℓ δ h0 hmono m a, qNo ℓ δ h0 hmono m b)) ≤ ENNReal.ofReal (A * (‖a‖ + ‖b‖) ^ 2) := by
  have hd := δ_nonneg δ h0 hmono m
  obtain ⟨K1, hK1, h1⟩ := guAP hβ hd (k := ℓ + m) (hd' := hd)
  obtain ⟨K2, hK2, h2⟩ := guAN hβ hd (k := ℓ + m) (hd' := hd)
  obtain ⟨K3, hK3, h3⟩ := guBP hβ hd (k := ℓ + m) (hd' := hd)
  obtain ⟨K4, hK4, h4⟩ := guBN hβ hd (k := ℓ + m) (hd' := hd)
  set N := Fintype.card (idx (ℓ + m))
  set K := K1 + K2 + K3 + K4
  refine ⟨2 * (K * N) ^ 2, by positivity, fun R hR2 ϑ a b => ?_⟩
  have hna := guSum_guE_le a
  have hnb := guSum_guE_le b
  set T := ENNReal.ofReal (K * N * (‖a‖ + ‖b‖))
  have hZ : guSum (guZ (δ m) R)
      (mulHL _ (m1 hβ R (ℓ + m)) a + mulHL _ (m2 hβ R (ℓ + m)) (shH R ϑ b)) ≤ T :=
    (guSum_add (measurable_guZ _ _) _ _).trans ((add_le_add (h1 R a) (h2 R ϑ b)).trans
      (ofReal_lin (norm_nonneg _) (norm_nonneg _) hK1 hK2 (by linarith) (by linarith) hna hnb))
  have hC : guSum (guC (δ m) R)
      (mulHL _ (m5 hβ R (ℓ + m)) a + mulHL _ (m1 hβ R (ℓ + m)) (shH R ϑ b)) ≤ T :=
    (guSum_add (measurable_guC _ _) _ _).trans ((add_le_add (h3 R hR2 a) (h4 R hR2 ϑ b)).trans
      (ofReal_lin (norm_nonneg _) (norm_nonneg _) hK3 hK4 (by linarith) (by linarith) hna hnb))
  have hT : T ^ 2 + T ^ 2 = ENNReal.ofReal (2 * (K * N) ^ 2 * (‖a‖ + ‖b‖) ^ 2) := by
    rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_add (by positivity)
      (by positivity)]
    congr 1; ring
  rw [← hT]
  refine add_le_add ((guZSq_le _ rfl).trans ((guSq_le_guSum_sq _ _).trans
    (pow_le_pow_left' hZ 2))) ((guSq_le_guSum_sq _ _).trans (pow_le_pow_left' hC 2))

/-- The lower bound. -/
lemma hat_lower (m : ℕ) : ∃ A, 0 < A ∧ ∀ R (hR2 : 2 ≤ R) ϑ (ξ : (scFHat ℓ δ h0 hmono) m),
    ENNReal.ofReal (‖ξ‖ ^ 2) ≤
      ENNReal.ofReal A * guGHatSq ℓ δ h0 hmono R m (PhiHat ℓ δ h0 hmono hβ hR2 ϑ m ξ) := by
  have hd := δ_nonneg δ h0 hmono m
  obtain ⟨K1, hK1, h1⟩ := guPP hβ hd (k := ℓ + m) (hd' := hd)
  obtain ⟨K2, hK2, h2⟩ := guWP hβ hd (k := ℓ + m) (hd' := hd)
  obtain ⟨K3, hK3, h3⟩ := guPN hβ hd (k := ℓ + m) (hd' := hd)
  obtain ⟨K4, hK4, h4⟩ := guWN hβ hd (k := ℓ + m) (hd' := hd)
  set N := Fintype.card (idx (ℓ + m))
  have hN : (0 : ℝ) < N := Nat.cast_pos.2 (card_idx_pos _)
  set K := K1 + K2 + K3 + K4 + 1
  set c : ℝ := 2 * K ^ 2 * N
  have hc : 0 < c := by positivity
  refine ⟨2 * c, by positivity, fun R hR2 ϑ ξ => ?_⟩
  set y := PhiHat ℓ δ h0 hmono hβ hR2 ϑ m ξ
  -- the generic step: a bound by `K (‖u‖_Z + ‖w‖_C)` for every representative `u`
  have key : ∀ (X : ℝ≥0∞), (∀ u, qZo ℓ δ h0 hmono (R := R) m u = y.1 →
      X ≤ ENNReal.ofReal K * guSum (guZ (δ m) R) u + ENNReal.ofReal K * guSum (guC (δ m) R) y.2) →
      X ^ 2 ≤ ENNReal.ofReal c * guGHatSq ℓ δ h0 hmono R m y := by
    intro X hX
    have : ∀ u : {u : H (ℓ + m) (δ_nonneg δ h0 hmono m) // qZo ℓ δ h0 hmono (R := R) m u = y.1},
        X ^ 2 ≤ ENNReal.ofReal c * (guSq (guZ (δ m) R) u.1 + guSq (guC (δ m) R) y.2) := by
      rintro ⟨u, hu⟩
      calc X ^ 2 ≤ (ENNReal.ofReal K * guSum (guZ (δ m) R) u +
            ENNReal.ofReal K * guSum (guC (δ m) R) y.2) ^ 2 := pow_le_pow_left' (hX u hu) 2
        _ ≤ 2 * ((ENNReal.ofReal K * guSum (guZ (δ m) R) u) ^ 2 +
            (ENNReal.ofReal K * guSum (guC (δ m) R) y.2) ^ 2) := ennreal_add_sq_le _ _
        _ = 2 * ENNReal.ofReal K ^ 2 * (guSum (guZ (δ m) R) u ^ 2 +
            guSum (guC (δ m) R) y.2 ^ 2) := by ring
        _ ≤ 2 * ENNReal.ofReal K ^ 2 * ((N : ℝ≥0∞) * guSq (guZ (δ m) R) u +
            (N : ℝ≥0∞) * guSq (guC (δ m) R) y.2) :=
            mul_le_mul_right (add_le_add (guSum_sq_le _ _) (guSum_sq_le _ _)) _
        _ = ENNReal.ofReal c * (guSq (guZ (δ m) R) u + guSq (guC (δ m) R) y.2) := by
            rw [← mul_add, ← mul_assoc]
            congr 1
            rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (by positivity),
              ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
              ← ENNReal.ofReal_mul (by positivity)]
    refine (le_iInf this).trans_eq ?_
    rw [guGHatSq, guZSq, ENNReal.iInf_add, ENNReal.mul_iInf_of_ne (by positivity)
      ENNReal.ofReal_ne_top]
  have hK1' : K1 ≤ K := by linarith
  have hK2' : K2 ≤ K := by linarith
  have hK3' : K3 ≤ K := by linarith
  have hK4' : K4 ≤ K := by linarith
  have hP : ENNReal.ofReal (‖ξ.1‖ ^ 2) ≤ ENNReal.ofReal c * guGHatSq ℓ δ h0 hmono R m y := by
    rw [ENNReal.ofReal_pow (norm_nonneg _)]
    refine key _ fun u hu => ?_
    have e : ξ.1 = qPo ℓ δ h0 hmono m
        (mulHL _ (m3 hβ R (ℓ + m)) u - mulHL _ (m4 hβ R (ℓ + m)) y.2) := by
      conv_lhs => rw [← psiHat_phiHat ℓ δ h0 hmono hβ hR2 ϑ m ξ]
      change PPh ℓ δ h0 hmono hβ hR2 m y.1 - WPh ℓ δ h0 hmono hβ (R := R) m y.2 = _
      rw [← hu, map_sub]; rfl
    rw [e]
    refine (ENNReal.ofReal_le_ofReal (Submodule.Quotient.norm_mk_le _ _)).trans
      ((ofReal_norm_le_guSum _).trans ((guSum_sub (measurable_guE _) _ _).trans ?_))
    exact add_le_add ((h1 R hR2 u).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hK1') _))
      ((h2 R hR2 _).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hK2') _))
  have hNg : ENNReal.ofReal (‖ξ.2‖ ^ 2) ≤ ENNReal.ofReal c * guGHatSq ℓ δ h0 hmono R m y := by
    rw [ENNReal.ofReal_pow (norm_nonneg _)]
    refine key _ fun u hu => ?_
    have e : ξ.2 = qNo ℓ δ h0 hmono m
        (shH (-R) (-ϑ) (mulHL _ (m4 hβ R (ℓ + m)) u) +
          shH (-R) (-ϑ) (mulHL _ (m3 hβ R (ℓ + m)) y.2)) := by
      conv_lhs => rw [← psiHat_phiHat ℓ δ h0 hmono hβ hR2 ϑ m ξ]
      change PNh ℓ δ h0 hmono hβ hR2 ϑ m y.1 + WNh ℓ δ h0 hmono hβ (R := R) ϑ m y.2 = _
      rw [← hu, map_add]; rfl
    rw [e]
    refine (ENNReal.ofReal_le_ofReal (Submodule.Quotient.norm_mk_le _ _)).trans
      ((ofReal_norm_le_guSum _).trans ((guSum_add (measurable_guE _) _ _).trans ?_))
    exact add_le_add ((h3 R hR2 ϑ u).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hK3') _))
      ((h4 R hR2 ϑ _).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hK4') _))
  calc ENNReal.ofReal (‖ξ‖ ^ 2) ≤ ENNReal.ofReal (‖ξ.1‖ ^ 2) + ENNReal.ofReal (‖ξ.2‖ ^ 2) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hn : ‖ξ‖ = max ‖ξ.1‖ ‖ξ.2‖ := rfl
        rw [hn]
        rcases le_total ‖ξ.1‖ ‖ξ.2‖ with h | h
        · rw [max_eq_right h]; nlinarith [sq_nonneg ‖ξ.1‖]
        · rw [max_eq_left h]; nlinarith [sq_nonneg ‖ξ.2‖]
    _ ≤ ENNReal.ofReal c * guGHatSq ℓ δ h0 hmono R m y +
        ENNReal.ofReal c * guGHatSq ℓ δ h0 hmono R m y := add_le_add hP hNg
    _ = _ := by
        rw [← two_mul, ← mul_assoc, ← ENNReal.ofReal_ofNat 2,
          ← ENNReal.ofReal_mul (by norm_num)]

end Hat

section HatThm

variable (ℓ : ℕ) (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)
variable {β : ℝ → ℝ} (hβ : IsCutoff β)

lemma monotoneOn_sq_add {A b : ℝ} (hA : 0 ≤ A) (hb : 0 ≤ b) :
    MonotoneOn (fun t => A * (t + b) ^ 2) (Ici 0) := fun x hx y _ hxy =>
  mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [mem_Ici.1 hx]) (by linarith) 2) hA

lemma monotoneOn_add_sq {A b : ℝ} (hA : 0 ≤ A) (hb : 0 ≤ b) :
    MonotoneOn (fun t => A * (b + t) ^ 2) (Ici 0) := fun x hx y _ hxy =>
  mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [mem_Ici.1 hx]) (by linarith) 2) hA

/-- **Proposition 4.13** at offset `ℓ` (Memoir p. 108, Total Hat-Gluing Estimate): for every `m`
there is `C > 0`, independent of `R ≥ 2` and `ϑ`, with
`C⁻¹ |ξ|²_{F_m} ≤ |Φ̂_a ξ|²_{Ĝ^a_m} ≤ C |ξ|²_{F_m}` for all `ξ ∈ F_m`. -/
theorem memoir_proposition_4_13_off (m : ℕ) : ∃ C, 0 < C ∧ ∀ R (hR2 : 2 ≤ R) ϑ
    (ξ : (scFHat ℓ δ h0 hmono) m),
    ENNReal.ofReal (‖ξ‖ ^ 2) ≤
        ENNReal.ofReal C * guGHatSq ℓ δ h0 hmono R m (PhiHat ℓ δ h0 hmono hβ hR2 ϑ m ξ) ∧
      guGHatSq ℓ δ h0 hmono R m (PhiHat ℓ δ h0 hmono hβ hR2 ϑ m ξ) ≤
        ENNReal.ofReal C * ENNReal.ofReal (‖ξ‖ ^ 2) := by
  obtain ⟨A, hA, hup⟩ := hat_upper_reps hβ (ℓ := ℓ) (δ := δ) (h0 := h0) (hmono := hmono) m
  obtain ⟨B, hB, hlow⟩ := hat_lower hβ (ℓ := ℓ) (δ := δ) (h0 := h0) (hmono := hmono) m
  refine ⟨4 * A + B, by positivity, fun R hR2 ϑ ξ => ⟨(hlow R hR2 ϑ ξ).trans
    (mul_le_mul_left (ENNReal.ofReal_le_ofReal (by linarith)) _), ?_⟩⟩
  set X := guGHatSq ℓ δ h0 hmono R m (PhiHat ℓ δ h0 hmono hβ hR2 ϑ m ξ)
  have h1 : ∀ b, qNo ℓ δ h0 hmono m b = ξ.2 → X ≤ ENNReal.ofReal (A * (‖ξ.1‖ + ‖b‖) ^ 2) := by
    intro b hb
    refine le_ofReal_of_reps (S := LPo ℓ δ h0 hmono m) ξ.1 (f := fun t => A * (t + ‖b‖) ^ 2)
      (by fun_prop) (monotoneOn_sq_add hA (norm_nonneg _)) fun a ha => ?_
    have e : ξ = (qPo ℓ δ h0 hmono m a, qNo ℓ δ h0 hmono m b) := Prod.ext ha.symm hb.symm
    have hX : X = guGHatSq ℓ δ h0 hmono R m (PhiHat ℓ δ h0 hmono hβ hR2 ϑ m
        (qPo ℓ δ h0 hmono m a, qNo ℓ δ h0 hmono m b)) := by rw [← e]
    rw [hX]
    exact hup R hR2 ϑ a b
  have h2 : X ≤ ENNReal.ofReal (A * (‖ξ.1‖ + ‖ξ.2‖) ^ 2) :=
    le_ofReal_of_reps (S := LNo ℓ δ h0 hmono m) ξ.2 (f := fun t => A * (‖ξ.1‖ + t) ^ 2)
      (by fun_prop) (monotoneOn_add_sq hA (norm_nonneg _)) h1
  have hn : ‖ξ‖ = max ‖ξ.1‖ ‖ξ.2‖ := rfl
  refine h2.trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e1 : ‖ξ.1‖ ≤ ‖ξ‖ := hn ▸ le_max_left _ _
  have e2 : ‖ξ.2‖ ≤ ‖ξ‖ := hn ▸ le_max_right _ _
  have : (‖ξ.1‖ + ‖ξ.2‖) ^ 2 ≤ 4 * ‖ξ‖ ^ 2 := by nlinarith [norm_nonneg ξ.1, norm_nonneg ξ.2]
  nlinarith [sq_nonneg ‖ξ‖]

/-- **Proposition 4.13** (Memoir p. 108), for the memoir's `F = H^{2,δ₀}(ℝ⁺ × S¹) ⊕
H^{2,δ₀}(ℝ⁻ × S¹)` (`ℓ = 2`): for every `m` there is `C_m > 0`, independent of the gluing
parameter, with `C_m⁻¹ |ξ|_{F_m} ≤ |Φ̂_a ξ|_{Ĝ^a_m} ≤ C_m |ξ|_{F_m}` for `0 < |a| < 1/2`
(here in squares: `C = C_m²`). -/
theorem memoir_proposition_4_13 (m : ℕ) : ∃ C, 0 < C ∧ ∀ {a : ℂ} (ha0 : a ≠ 0) (ha : ‖a‖ < 1 / 2)
    (ξ : (scFHat 2 δ h0 hmono) m),
    ENNReal.ofReal (‖ξ‖ ^ 2) ≤ ENNReal.ofReal C * guGHatSq 2 δ h0 hmono (glLength a) m
        (PhiHat 2 δ h0 hmono hβ (two_le_glLength ha0 ha) (glTwist a) m ξ) ∧
      guGHatSq 2 δ h0 hmono (glLength a) m
          (PhiHat 2 δ h0 hmono hβ (two_le_glLength ha0 ha) (glTwist a) m ξ) ≤
        ENNReal.ofReal C * ENNReal.ofReal (‖ξ‖ ^ 2) := by
  obtain ⟨C, hC, h⟩ := memoir_proposition_4_13_off 2 δ h0 hmono hβ m
  exact ⟨C, hC, fun ha0 ha ξ => h _ _ _ ξ⟩

/-- **Uniform bound on `π̂_a`**: `‖π̂_a ξ‖_{F_m} ≤ C ‖ξ‖_{F_m}` with `C` independent of `R ≥ 2`
and `ϑ`. -/
theorem piHat_uniform (m : ℕ) : ∃ C, 0 < C ∧ ∀ R (hR2 : 2 ≤ R) ϑ (ξ : (scFHat ℓ δ h0 hmono) m),
    ‖piHatLvl ℓ δ h0 hmono hβ hR2 ϑ m ξ‖ ≤ C * ‖ξ‖ := by
  obtain ⟨C, hC, h⟩ := memoir_proposition_4_13_off ℓ δ h0 hmono hβ m
  refine ⟨C, hC, fun R hR2 ϑ ξ => ?_⟩
  set η := piHatLvl ℓ δ h0 hmono hβ hR2 ϑ m ξ
  have h1 := (h R hR2 ϑ η).1
  rw [phiHat_piHatLvl] at h1
  have h2 : guGHatSq ℓ δ h0 hmono R m ((PhiHat ℓ δ h0 hmono hβ hR2 ϑ m ξ).1, 0) ≤
      guGHatSq ℓ δ h0 hmono R m (PhiHat ℓ δ h0 hmono hβ hR2 ϑ m ξ) := by
    unfold guGHatSq
    refine add_le_add le_rfl ?_
    have e : guSq (guC (δ m) R) (0 : (scCylOff ℓ δ h0 hmono) m) = 0 := guSq_zero (measurable_guC _ _)
    exact e.le.trans bot_le
  have h3 : ENNReal.ofReal (‖η‖ ^ 2) ≤ ENNReal.ofReal ((C * ‖ξ‖) ^ 2) := by
    refine h1.trans ((mul_le_mul_right h2 _).trans ((mul_le_mul_right (h R hR2 ϑ ξ).2 _).trans ?_))
    rw [← ENNReal.ofReal_mul hC.le, ← ENNReal.ofReal_mul hC.le]
    exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))
  have h4 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h4

end HatThm

/-! ## 3. The norm of `G^a_m` and Proposition 4.14 -/

section Total

variable (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)
variable {β : ℝ → ℝ} (hβ : IsCutoff β)

/-- The squared norm of `G^a_m = H^{3+m}(Z_a) ⊕ H^{3+m,δ_m}_c(C_a)` (Memoir p. 108), at
`y = (q, c', w)`, `p = (1 - 2β_a) c' + w`: `|[q]_a - p_∞|² + e^{δ_m R} (‖q - [q]_a + p_∞‖²_{3+m,-δ_m} +
‖p̂‖²_{3+m,δ_m})`, with `[q]_a = TZ q` the mean value over `{R/2} × S¹`, `p_∞ = c'`,
`p̂ = w`; `[q]_a - p_∞ = cPsi y`.  The memoir prints the index `m + 2`; it is read as `m + 3`, the
level of `H^{3+m}`. -/
def guGSq {R : ℝ} (hR2 : 2 ≤ R) (m : ℕ) (y : (scG δ h0 hmono R) m) : ℝ≥0∞ :=
  ENNReal.ofReal (cPsi δ h0 hmono hR2 m y ^ 2) +
    (guZSq 3 δ h0 hmono R m (qrV δ h0 hmono m y -
        cPsi δ h0 hmono hR2 m y • gZ δ h0 hmono (R := R) m) +
      guSq (guC (δ m) R) (qrW δ h0 hmono m y))

variable {δ h0 hmono}

/-- On the image of `Φ_a`: `|Φ_a(c, r⁺, r⁻)|²_{G^a_m} = |c|² + |Φ̂_a(r⁺, r⁻)|²_{Ĝ^a_m}`, the hat gluing
at offset `3`. -/
lemma guGSq_phi {R : ℝ} (hR2 : 2 ≤ R) (ϑ : ℝ) (m : ℕ) (x : (scPair δ h0 hmono) m) :
    guGSq δ h0 hmono hR2 m (Phi δ h0 hmono hβ hR2 ϑ m x) =
      ENNReal.ofReal (x.1 ^ 2) + guGHatSq 3 δ h0 hmono R m (PhiHat 3 δ h0 hmono hβ hR2 ϑ m x.2) := by
  have hc : cPsi δ h0 hmono hR2 m (Phi δ h0 hmono hβ hR2 ϑ m x) = x.1 :=
    congrArg Prod.fst (psi_phi hβ hR2 ϑ m x)
  obtain ⟨c, p, q⟩ := x
  unfold guGSq guGHatSq
  rw [hc]
  congr 2
  change guZSq 3 δ h0 hmono R m (c • gZ δ h0 hmono (R := R) m + AP δ h0 hmono hβ m p +
    AN δ h0 hmono hβ ϑ m q - c • gZ δ h0 hmono (R := R) m) = _
  have e : c • gZ δ h0 hmono (R := R) m + AP δ h0 hmono hβ m p + AN δ h0 hmono hβ ϑ m q -
      c • gZ δ h0 hmono (R := R) m = AP δ h0 hmono hβ m p + AN δ h0 hmono hβ ϑ m q := by abel
  exact congrArg (guZSq 3 δ h0 hmono R m) e

theorem memoir_proposition_4_14_off (m : ℕ) : ∃ C, 0 < C ∧ ∀ R (hR2 : 2 ≤ R) ϑ
    (x : (scPair δ h0 hmono) m),
    ENNReal.ofReal (‖x‖ ^ 2) ≤
        ENNReal.ofReal C * guGSq δ h0 hmono hR2 m (Phi δ h0 hmono hβ hR2 ϑ m x) ∧
      guGSq δ h0 hmono hR2 m (Phi δ h0 hmono hβ hR2 ϑ m x) ≤
        ENNReal.ofReal C * ENNReal.ofReal (‖x‖ ^ 2) := by
  obtain ⟨C, hC, h⟩ := memoir_proposition_4_13_off 3 δ h0 hmono hβ m
  refine ⟨C + 1, by positivity, fun R hR2 ϑ x => ?_⟩
  rw [guGSq_phi hβ hR2 ϑ m x]
  obtain ⟨h1, h2⟩ := h R hR2 ϑ x.2
  have hn : ‖x‖ = max ‖x.1‖ ‖x.2‖ := rfl
  have e1 : x.1 ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [← sq_abs, ← Real.norm_eq_abs]
    exact pow_le_pow_left₀ (norm_nonneg _) (hn ▸ le_max_left _ _) 2
  have e2 : ‖x.2‖ ^ 2 ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hn ▸ le_max_right _ _) 2
  have hC1 : ENNReal.ofReal C ≤ ENNReal.ofReal (C + 1) := ENNReal.ofReal_le_ofReal (by linarith)
  have h11 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (C + 1) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  constructor
  · calc ENNReal.ofReal (‖x‖ ^ 2) ≤ ENNReal.ofReal (x.1 ^ 2) + ENNReal.ofReal (‖x.2‖ ^ 2) := by
          rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hn, Real.norm_eq_abs]
          rcases le_total |x.1| ‖x.2‖ with h | h
          · rw [max_eq_right h]; nlinarith [sq_nonneg x.1]
          · rw [max_eq_left h, sq_abs]; nlinarith [sq_nonneg ‖x.2‖]
      _ ≤ ENNReal.ofReal (C + 1) * ENNReal.ofReal (x.1 ^ 2) +
          ENNReal.ofReal (C + 1) * guGHatSq 3 δ h0 hmono R m (PhiHat 3 δ h0 hmono hβ hR2 ϑ m x.2) :=
          add_le_add (le_mul_of_one_le_left bot_le h11) (h1.trans (mul_le_mul_left hC1 _))
      _ = _ := by rw [mul_add]
  · calc ENNReal.ofReal (x.1 ^ 2) + guGHatSq 3 δ h0 hmono R m (PhiHat 3 δ h0 hmono hβ hR2 ϑ m x.2)
        ≤ ENNReal.ofReal (x.1 ^ 2) + ENNReal.ofReal C * ENNReal.ofReal (‖x.2‖ ^ 2) :=
          add_le_add le_rfl h2
      _ = ENNReal.ofReal (x.1 ^ 2 + C * ‖x.2‖ ^ 2) := by
          rw [ENNReal.ofReal_add (sq_nonneg _) (by positivity), ENNReal.ofReal_mul hC.le]
      _ ≤ ENNReal.ofReal ((C + 1) * ‖x‖ ^ 2) := ENNReal.ofReal_le_ofReal (by nlinarith)
      _ = _ := ENNReal.ofReal_mul (by positivity)

/-- **Proposition 4.14** (Memoir p. 108, Total Gluing Estimate): for every `m` there is
`C_m > 0`, independent of the gluing parameter, with
`C_m⁻¹ |(η⁺, η⁻)|_{E_m} ≤ |Φ_a(η⁺, η⁻)|_{G^a_m} ≤ C_m |(η⁺, η⁻)|_{E_m}` for `0 < |a| < 1/2`
(here in squares: `C = C_m²`; `E_m` with its norm `max(|c|, ‖r⁺‖, ‖r⁻‖)`). -/
theorem memoir_proposition_4_14 (m : ℕ) : ∃ C, 0 < C ∧ ∀ {a : ℂ} (ha0 : a ≠ 0)
    (ha : ‖a‖ < 1 / 2) (x : (scPair δ h0 hmono) m),
    ENNReal.ofReal (‖x‖ ^ 2) ≤ ENNReal.ofReal C * guGSq δ h0 hmono (two_le_glLength ha0 ha) m
        (Phi δ h0 hmono hβ (two_le_glLength ha0 ha) (glTwist a) m x) ∧
      guGSq δ h0 hmono (two_le_glLength ha0 ha) m
          (Phi δ h0 hmono hβ (two_le_glLength ha0 ha) (glTwist a) m x) ≤
        ENNReal.ofReal C * ENNReal.ofReal (‖x‖ ^ 2) := by
  obtain ⟨C, hC, h⟩ := memoir_proposition_4_14_off hβ (δ := δ) (h0 := h0) (hmono := hmono) m
  exact ⟨C, hC, fun ha0 ha x => h _ _ _ x⟩

end Total

end GWMemoir.Neck
