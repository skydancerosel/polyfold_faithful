import GWMemoir.HalfCylinders

/-!
# Memoir §2.4: gluings and anti-gluings (the formal part, continuous maps)

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §2.4, pp. 43–49.

The memoir first carries out the gluing and anti-gluing constructions for continuous maps of
half-cylinders into `ℝ²ⁿ` ("for this part we can use any gluing profile", p. 43).  This file does
that part, for maps into any real Banach space `V` (`V = ℝ²ⁿ` in the memoir).

* `expProfile`: the exponential gluing profile `φ(r) = e^{1/r} - e`; `glLength a = φ(|a|)` and
  `glTwist a = ϑ` with `a = |a| e^{-2πiϑ}`; `four_lt_glLength`: `R > 4` for `0 < |a| < 1/2`.
* `IsCutoff β`: the conditions (2.1) on the cut-off; `stdCutoff` satisfies them.
* The domains: `ℝ⁺ × S¹` (`HalfP`), `ℝ⁻ × S¹` (`HalfN`), `Z_a = [0,R] × S¹` (`Zcyl R`), and the
  infinite cylinder `C_a` in its coordinates `[s,t]`, i.e. `ℝ × S¹`; `S¹ = ℝ/ℤ`.
* `glue` (`⊕_a`), `anti` (`⊖_a`), `av` (`av_a`), `antiHat` (`⊖̂_a`), and the spaces `E`
  (`pairSp`), `E⁺_a` (`plusSp`), `E⁻_a` (`minusSp`).
* In `GWMemoir.GluingLemma248`: **Lemma 2.48**, `Φ_a = (⊕_a, ⊖_a) : E → E⁺_a ⊕ E⁻_a` is a
  bijection (`totalGlue_bijective`), with the inverse (2.6), (2.7) (`memoir_eq_2_6_2_7`).
* In `GWMemoir.GluingSplicing`: `memoir_lemma_2_48` in terms of `a`, the decomposition (2.8)
  (`memoir_eq_2_8`), the projection `π_a` onto `ker ⊖_a` along `ker ⊕_a` (`piA`) and its formulas
  (2.10), (2.11); the hat versions on `F` (`hatSp`): `memoir_hat_gluing_iso`, `piHat` and (2.12);
  Proposition 2.51.

All of this holds for `R ≥ 2`, the only property of the gluing length used.  For `a = 0` the memoir
sets `Φ₀ = (id, 0)` and `π₀ = id`; that case is not repeated here.
-/

open Set Filter Topology MeasureTheory
open scoped ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace GWMemoir.Neck

/-! ## 1. The gluing profile, the cut-off and the gluing parameters -/

/-- The exponential gluing profile `φ(r) = e^{1/r} - e`, `r ∈ (0,1]` (Memoir §2.4, p. 43;
Definition 2.1, p. 11). -/
def expProfile (r : ℝ) : ℝ := Real.exp r⁻¹ - Real.exp 1

/-- The gluing length `R = φ(|a|)` of a gluing parameter `a` (Memoir p. 43). -/
def glLength (a : ℂ) : ℝ := expProfile ‖a‖

/-- The twist `ϑ` of a gluing parameter, `a = |a| e^{-2πiϑ}` (Memoir p. 43). -/
def glTwist (a : ℂ) : ℝ := -Complex.arg a / (2 * Real.pi)

theorem glTwist_spec (a : ℂ) :
    a = (‖a‖ : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * (glTwist a : ℂ)) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have : -2 * (Real.pi : ℂ) * Complex.I * ((-Complex.arg a / (2 * Real.pi) : ℝ) : ℂ) =
      (Complex.arg a : ℂ) * Complex.I := by
    push_cast; field_simp
  rw [glTwist, this, Complex.norm_mul_exp_arg_mul_I]

/-- For `0 < |a| < 1/2` the gluing length exceeds `4` (`e² - e > 4`). -/
theorem four_lt_glLength {a : ℂ} (h0 : a ≠ 0) (h : ‖a‖ < 1 / 2) : 4 < glLength a := by
  have hpos : 0 < ‖a‖ := norm_pos_iff.2 h0
  have h2 : 2 < ‖a‖⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) hpos]; linarith
  have he : Real.exp 2 < Real.exp ‖a‖⁻¹ := Real.exp_lt_exp.2 h2
  have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h1 := Real.exp_one_gt_d9
  unfold glLength expProfile
  nlinarith

/-- The conditions (2.1) on the cut-off `β : ℝ → [0,1]` (Memoir p. 45): smooth, `β(-s) + β(s) = 1`,
`β(s) = 1` for `s ≤ -1`, `β' < 0` on `(-1,1)`. -/
structure IsCutoff (β : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ β
  mem : ∀ s, β s ∈ Icc (0 : ℝ) 1
  symm : ∀ s, β (-s) + β s = 1
  one_of_le : ∀ s, s ≤ -1 → β s = 1
  deriv_neg : ∀ s ∈ Ioo (-1 : ℝ) 1, deriv β s < 0

namespace IsCutoff

variable {β : ℝ → ℝ} (hβ : IsCutoff β)
include hβ

lemma zero_of_ge {s : ℝ} (hs : 1 ≤ s) : β s = 0 := by
  have h1 := hβ.symm s
  have h2 := hβ.one_of_le (-s) (by linarith)
  linarith

lemma half : β 0 = 1 / 2 := by
  have := hβ.symm 0
  rw [neg_zero] at this
  linarith

lemma continuous : Continuous β := hβ.smooth.continuous

end IsCutoff

lemma smoothTransition_add_one_sub (x : ℝ) :
    Real.smoothTransition x + Real.smoothTransition (1 - x) = 1 := by
  unfold Real.smoothTransition
  rw [sub_sub_cancel, add_comm (expNegInvGlue (1 - x)) (expNegInvGlue x), ← add_div,
    div_self (Real.smoothTransition.pos_denom x).ne']

lemma expNegInvGlue_of_pos {x : ℝ} (hx : 0 < x) : expNegInvGlue x = Real.exp (-x⁻¹) := by
  simp [expNegInvGlue, not_le.2 hx]

/-- The derivative of the smooth transition is positive on `(0,1)`. -/
lemma smoothTransition_hasDerivAt_pos {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    ∃ d, 0 < d ∧ HasDerivAt Real.smoothTransition d x := by
  set f : ℝ → ℝ := fun y => Real.exp (-y⁻¹)
  set g : ℝ → ℝ := fun y => Real.exp (-(1 - y)⁻¹)
  have hx1 : (1 - x) ≠ 0 := by linarith
  have hf : HasDerivAt f (Real.exp (-x⁻¹) * -(-(x ^ 2)⁻¹)) x :=
    ((hasDerivAt_inv h0.ne').neg).exp
  have hg0 : HasDerivAt (fun y => (1 - y)) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub 1
  have hg : HasDerivAt g (Real.exp (-(1 - x)⁻¹) * -(-((1 - x) ^ 2)⁻¹ * -1)) x :=
    (((hasDerivAt_inv hx1).comp x hg0).neg).exp
  have hpos : 0 < f x + g x := by positivity
  have hdiv := hf.div (hf.add hg) hpos.ne'
  refine ⟨_, ?_, hdiv.congr_of_eventuallyEq ?_⟩
  · apply div_pos _ (by positivity)
    have e1 : 0 < Real.exp (-x⁻¹) := Real.exp_pos _
    have e2 : 0 < Real.exp (-(1 - x)⁻¹) := Real.exp_pos _
    have i1 : 0 < (x ^ 2)⁻¹ := by positivity
    have i2 : 0 < ((1 - x) ^ 2)⁻¹ := inv_pos.2 (by positivity)
    simp only [Pi.add_apply, f, g]
    nlinarith [mul_pos (mul_pos e1 i1) e2, mul_pos (mul_pos e2 i2) e1]
  · filter_upwards [Ioo_mem_nhds h0 h1] with y hy
    simp only [Real.smoothTransition, f, g, Pi.div_apply, Pi.add_apply]
    rw [expNegInvGlue_of_pos hy.1, expNegInvGlue_of_pos (by linarith [hy.2])]

/-- The standard cut-off `β(s) = st((1 - s)/2)`, `st` the smooth transition of Mathlib. -/
def stdCutoff (s : ℝ) : ℝ := Real.smoothTransition ((1 - s) / 2)

/-- `stdCutoff` satisfies (2.1): the cut-off functions of the memoir exist. -/
theorem isCutoff_stdCutoff : IsCutoff stdCutoff where
  smooth := (Real.smoothTransition.contDiff (n := ⊤)).comp (by fun_prop)
  mem s := ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  symm s := by
    unfold stdCutoff
    have : (1 - s) / 2 = 1 - (1 - -s) / 2 := by ring
    rw [this]; exact smoothTransition_add_one_sub _
  one_of_le s hs := Real.smoothTransition.one_of_one_le (by linarith)
  deriv_neg s hs := by
    obtain ⟨d, hd, hD⟩ := smoothTransition_hasDerivAt_pos (x := (1 - s) / 2)
      (by linarith [hs.2]) (by linarith [hs.1])
    have hin : HasDerivAt (fun s : ℝ => (1 - s) / 2) (-(1 / 2)) s := by
      have := ((hasDerivAt_id s).const_sub 1).div_const 2
      simpa [neg_div] using this
    have := hD.comp s hin
    rw [show stdCutoff = Real.smoothTransition ∘ (fun s : ℝ => (1 - s) / 2) from rfl,
      this.deriv]
    nlinarith

/-! ## 2. The translated cut-off `β_a` and `γ_a` -/

variable (β : ℝ → ℝ) (R ϑ : ℝ)

/-- `β_a(s) = β(s - R/2)` (2.2). -/
def βa (s : ℝ) : ℝ := β (s - R / 2)

/-- `γ_a = β_a² + (1 - β_a)²`, the determinant of the matrix (2.5). -/
def γa (s : ℝ) : ℝ := βa β R s ^ 2 + (1 - βa β R s) ^ 2

variable {β R}

lemma βa_one (hβ : IsCutoff β) {s : ℝ} (hs : s ≤ R / 2 - 1) : βa β R s = 1 :=
  hβ.one_of_le _ (by linarith)

lemma βa_zero (hβ : IsCutoff β) {s : ℝ} (hs : R / 2 + 1 ≤ s) : βa β R s = 0 :=
  hβ.zero_of_ge (by linarith)

lemma βa_half (hβ : IsCutoff β) : βa β R (R / 2) = 1 / 2 := by
  simp only [βa, sub_self]; exact hβ.half

lemma γa_pos (s : ℝ) : 0 < γa β R s := by
  unfold γa; nlinarith [sq_nonneg (2 * βa β R s - 1)]

lemma γa_ne (s : ℝ) : γa β R s ≠ 0 := (γa_pos s).ne'

lemma γa_of_βa_zero {s : ℝ} (h : βa β R s = 0) : γa β R s = 1 := by simp [γa, h]

lemma γa_of_βa_one {s : ℝ} (h : βa β R s = 1) : γa β R s = 1 := by simp [γa, h]

lemma continuous_βa (hβ : IsCutoff β) : Continuous (βa β R) :=
  hβ.continuous.comp (continuous_id.sub continuous_const)

lemma continuous_γa (hβ : IsCutoff β) : Continuous (γa β R) := by
  unfold γa; have := continuous_βa (R := R) hβ; fun_prop

/-- `β_a(s + R) = 1 - β_a(-s)` and `γ_a(s + R) = γ_a(-s)` (Memoir p. 49). -/
lemma βa_add_R (hβ : IsCutoff β) (s : ℝ) : βa β R (s + R) = 1 - βa β R (-s) := by
  have := hβ.symm (s + R / 2)
  simp only [βa]
  rw [show s + R - R / 2 = s + R / 2 by ring, show -s - R / 2 = -(s + R / 2) by ring]
  linarith

lemma γa_add_R (hβ : IsCutoff β) (s : ℝ) : γa β R (s + R) = γa β R (-s) := by
  simp only [γa, βa_add_R hβ]; ring

/-! ## 3. Pointwise algebra of the matrix (2.5) -/

section Algebra

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma gam_ne (b : ℝ) : b ^ 2 + (1 - b) ^ 2 ≠ 0 := by nlinarith [sq_nonneg (2 * b - 1)]

lemma alg_P (b : ℝ) (P N : V) :
    (b ^ 2 + (1 - b) ^ 2)⁻¹ • (b • (b • P + (1 - b) • N) - (1 - b) • (-(1 - b) • P + b • N)) =
      P := by
  have e : (b ^ 2 + (1 - b) ^ 2)⁻¹ • (b • (b • P + (1 - b) • N) - (1 - b) • (-(1 - b) • P + b • N))
      = ((b ^ 2 + (1 - b) ^ 2)⁻¹ * (b ^ 2 + (1 - b) ^ 2)) • P + (0 : ℝ) • N := by module
  rw [e, inv_mul_cancel₀ (gam_ne b)]; simp

lemma alg_N (b : ℝ) (P N : V) :
    (b ^ 2 + (1 - b) ^ 2)⁻¹ • ((1 - b) • (b • P + (1 - b) • N) + b • (-(1 - b) • P + b • N)) =
      N := by
  have e : (b ^ 2 + (1 - b) ^ 2)⁻¹ • ((1 - b) • (b • P + (1 - b) • N) + b • (-(1 - b) • P + b • N))
      = (0 : ℝ) • P + ((b ^ 2 + (1 - b) ^ 2)⁻¹ * (b ^ 2 + (1 - b) ^ 2)) • N := by module
  rw [e, inv_mul_cancel₀ (gam_ne b)]; simp

lemma alg_v (b : ℝ) (v w : V) :
    b • ((b ^ 2 + (1 - b) ^ 2)⁻¹ • (b • v - (1 - b) • w)) +
      (1 - b) • ((b ^ 2 + (1 - b) ^ 2)⁻¹ • ((1 - b) • v + b • w)) = v := by
  have e : b • ((b ^ 2 + (1 - b) ^ 2)⁻¹ • (b • v - (1 - b) • w)) +
      (1 - b) • ((b ^ 2 + (1 - b) ^ 2)⁻¹ • ((1 - b) • v + b • w))
      = ((b ^ 2 + (1 - b) ^ 2)⁻¹ * (b ^ 2 + (1 - b) ^ 2)) • v + (0 : ℝ) • w := by module
  rw [e, inv_mul_cancel₀ (gam_ne b)]; simp

lemma alg_w (b : ℝ) (v w : V) :
    -(1 - b) • ((b ^ 2 + (1 - b) ^ 2)⁻¹ • (b • v - (1 - b) • w)) +
      b • ((b ^ 2 + (1 - b) ^ 2)⁻¹ • ((1 - b) • v + b • w)) = w := by
  have e : -(1 - b) • ((b ^ 2 + (1 - b) ^ 2)⁻¹ • (b • v - (1 - b) • w)) +
      b • ((b ^ 2 + (1 - b) ^ 2)⁻¹ • ((1 - b) • v + b • w))
      = (0 : ℝ) • v + ((b ^ 2 + (1 - b) ^ 2)⁻¹ * (b ^ 2 + (1 - b) ^ 2)) • w := by module
  rw [e, inv_mul_cancel₀ (gam_ne b)]; simp

end Algebra


variable {ϑ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ## 5. Gluing, anti-gluing and the averages -/

section Glue

variable (β R ϑ)

/-- The glued map `⊕_a(h⁺,h⁻)([s,t]) = β_a(s) h⁺(s,t) + (1 - β_a(s)) h⁻(s - R, t - ϑ)` on `Z_a`
(Memoir p. 45). -/
def glue (h : (HalfP → V) × (HalfN → V)) : Zcyl R → V := fun z =>
  βa β R z.1.1 • extP h.1 (z.1.1, z.2) + (1 - βa β R z.1.1) • extN h.2 (sh R ϑ (z.1.1, z.2))

/-- The hat anti-glued map `⊖̂_a(h⁺,h⁻)[s,t] = -(1 - β_a) h⁺(s,t) + β_a h⁻(s - R, t - ϑ)` on `C_a`
(Memoir p. 47). -/
def antiHat (h : (HalfP → V) × (HalfN → V)) : ℝ × S1 → V := fun x =>
  -(1 - βa β R x.1) • extP h.1 x + βa β R x.1 • extN h.2 (sh R ϑ x)

/-- The circle average `∫_{S¹} f(σ, t) dt`. -/
def circ (f : ℝ × S1 → V) (σ : ℝ) : V := ∫ t, f (σ, t)

/-- `av_a(h⁺,h⁻) = ½([h⁺]_R + [h⁻]_R)`, `[h^±]_R = ∫_{S¹} h^±(±R/2, t) dt` (Memoir p. 46). -/
def av (h : (HalfP → V) × (HalfN → V)) : V :=
  (1 / 2 : ℝ) • (circ (extP h.1) (R / 2) + circ (extN h.2) (-(R / 2)))

/-- The anti-glued map `⊖_a(h⁺,h⁻)[s,t] = -(1 - β_a)(h⁺(s,t) - av_a) + β_a (h⁻(s - R, t - ϑ) - av_a)`
on `C_a` (Memoir p. 46). -/
def anti (h : (HalfP → V) × (HalfN → V)) : ℝ × S1 → V := fun x =>
  -(1 - βa β R x.1) • (extP h.1 x - av R h) + βa β R x.1 • (extN h.2 (sh R ϑ x) - av R h)

/-- The solution operator of the system (2.5): formulas (2.6) and (2.7) with `w̃` in place of `w`. -/
def coreInv (hR : 0 ≤ R) (v : Zcyl R → V) (w : ℝ × S1 → V) : (HalfP → V) × (HalfN → V) :=
  (fun z => (γa β R z.1.1)⁻¹ •
      (βa β R z.1.1 • extZ hR v (z.1.1, z.2) - (1 - βa β R z.1.1) • w (z.1.1, z.2)),
   fun z => (γa β R (ush R ϑ (z.1.1, z.2)).1)⁻¹ •
      ((1 - βa β R (ush R ϑ (z.1.1, z.2)).1) • extZ hR v (ush R ϑ (z.1.1, z.2)) +
        βa β R (ush R ϑ (z.1.1, z.2)).1 • w (ush R ϑ (z.1.1, z.2))))

variable {β R ϑ}

lemma anti_eq (h : (HalfP → V) × (HalfN → V)) (x : ℝ × S1) :
    anti β R ϑ h x = antiHat β R ϑ h x - (2 * βa β R x.1 - 1) • av R h := by
  simp only [anti, antiHat]; module

lemma coreInv_fst (hR : 0 ≤ R) (v : Zcyl R → V) (w : ℝ × S1 → V) {s : ℝ} (hs : 0 ≤ s) (t : S1) :
    extP (coreInv β R ϑ hR v w).1 (s, t) = (γa β R s)⁻¹ •
      (βa β R s • extZ hR v (s, t) - (1 - βa β R s) • w (s, t)) := by
  rw [extP_of_nonneg _ hs]; rfl

lemma coreInv_snd (hR : 0 ≤ R) (v : Zcyl R → V) (w : ℝ × S1 → V) {s : ℝ} (hs : s ≤ R) (t : S1) :
    extN (coreInv β R ϑ hR v w).2 (sh R ϑ (s, t)) = (γa β R s)⁻¹ •
      ((1 - βa β R s) • extZ hR v (s, t) + βa β R s • w (s, t)) := by
  have hs' : s - R ≤ 0 := by linarith
  simp only [sh]
  rw [extN_of_nonpos _ hs']
  simp [coreInv, ush]

lemma γa_def (s : ℝ) : γa β R s = βa β R s ^ 2 + (1 - βa β R s) ^ 2 := rfl

variable (hβ : IsCutoff β) (hR2 : 2 ≤ R)
include hβ hR2

/-- `⊕_a` of the solution is `v`: the first row of (2.5). -/
theorem glue_coreInv (v : Zcyl R → V) (w : ℝ × S1 → V) :
    glue β R ϑ (coreInv β R ϑ (by linarith) v w) = v := by
  funext z
  obtain ⟨⟨s, hs⟩, t⟩ := z
  simp only [glue]
  rw [coreInv_fst _ v w hs.1, coreInv_snd _ v w hs.2, extZ_of_mem _ v hs, γa_def]
  exact alg_v _ _ _

/-- `⊖̂_a` of the solution is `w`: the second row of (2.5). -/
theorem antiHat_coreInv (v : Zcyl R → V) (w : ℝ × S1 → V) :
    antiHat β R ϑ (coreInv β R ϑ (by linarith) v w) = w := by
  funext x
  obtain ⟨s, t⟩ := x
  simp only [antiHat]
  rcases lt_or_ge s 0 with hs | hs
  · have hb : βa β R s = 1 := βa_one hβ (by linarith)
    rw [coreInv_snd _ v w (by linarith), γa_of_βa_one hb, hb]; simp
  rcases lt_or_ge R s with hs' | hs'
  · have hb : βa β R s = 0 := βa_zero hβ (by linarith)
    rw [coreInv_fst _ v w hs, γa_of_βa_zero hb, hb]; simp
  rw [coreInv_fst _ v w hs, coreInv_snd _ v w hs', γa_def]
  exact alg_w _ _ _

/-- The solution operator applied to `(⊕_a h, ⊖̂_a h)` gives back `h`. -/
theorem coreInv_glue (h : (HalfP → V) × (HalfN → V)) :
    coreInv β R ϑ (by linarith) (glue β R ϑ h) (antiHat β R ϑ h) = h := by
  have hR : (0 : ℝ) ≤ R := by linarith
  refine Prod.ext (funext fun z => ?_) (funext fun z => ?_)
  · obtain ⟨⟨s, hs⟩, t⟩ := z
    have hs0 : (0 : ℝ) ≤ s := hs
    change (γa β R s)⁻¹ • (βa β R s • extZ hR (glue β R ϑ h) (s, t) -
      (1 - βa β R s) • antiHat β R ϑ h (s, t)) = h.1 (⟨s, hs⟩, t)
    rw [← extP_of_nonneg h.1 hs0]
    rcases lt_or_ge R s with hs' | hs'
    · have hb : βa β R s = 0 := βa_zero hβ (by linarith)
      simp only [antiHat]
      rw [γa_of_βa_zero hb, hb]; simp
    rw [extZ_of_mem hR _ ⟨hs0, hs'⟩, γa_def]
    simp only [glue, antiHat]
    exact alg_P _ _ _
  · obtain ⟨⟨s, hs⟩, t⟩ := z
    have hs0 : s ≤ 0 := hs
    change (γa β R (s + R))⁻¹ • ((1 - βa β R (s + R)) • extZ hR (glue β R ϑ h) (s + R, t + ϑ) +
      βa β R (s + R) • antiHat β R ϑ h (s + R, t + ϑ)) = h.2 (⟨s, hs⟩, t)
    have hsh : sh R ϑ (s + R, t + (ϑ : S1)) = (s, t) := by simp [sh]
    rw [← extN_of_nonpos h.2 hs0, ← hsh]
    rcases lt_or_ge (s + R) 0 with hs' | hs'
    · have hb : βa β R (s + R) = 1 := βa_one hβ (by linarith)
      simp only [antiHat]
      rw [γa_of_βa_one hb, hb]; simp
    rw [extZ_of_mem hR _ ⟨hs', by linarith⟩, γa_def]
    simp only [glue, antiHat]
    exact alg_N _ _ _

end Glue

/-! ## 6. The spaces `E`, `E⁺_a`, `E⁻_a` -/

section Spaces

variable (V)

/-- `E`: pairs `(h⁺,h⁻)` of continuous maps `h^± : ℝ^± × S¹ → V` with a common asymptotic
constant, `lim_{s→∞} h⁺(s,t) = h⁺(∞) = h⁻(-∞) = lim_{s→-∞} h⁻(s,t)` uniformly in `t`
(Memoir p. 45). -/
def pairSp : Submodule ℝ ((HalfP → V) × (HalfN → V)) where
  carrier := {h | Continuous h.1 ∧ Continuous h.2 ∧ ∃ c, LimTop (extP h.1) c ∧ LimBot (extN h.2) c}
  add_mem' := by
    rintro h k ⟨h1, h2, c, hc1, hc2⟩ ⟨k1, k2, d, hd1, hd2⟩
    exact ⟨h1.add k1, h2.add k2, c + d, hc1.add hd1, hc2.add hd2⟩
  zero_mem' := ⟨continuous_const, continuous_const, 0, LimTop.zero, LimBot.zero⟩
  smul_mem' := by
    rintro r h ⟨h1, h2, c, hc1, hc2⟩
    exact ⟨h1.const_smul r, h2.const_smul r, r • c, hc1.smul r, hc2.smul r⟩

/-- `E⁺_a`: the continuous maps `v : Z_a → V` (Memoir p. 47). -/
def plusSp (R : ℝ) : Submodule ℝ (Zcyl R → V) where
  carrier := {v | Continuous v}
  add_mem' := Continuous.add
  zero_mem' := continuous_const
  smul_mem' r _ h := h.const_smul r

/-- `E⁻_a`: the continuous maps `w : C_a → V` with antipodal asymptotic constants
`w(-∞) = -w(∞)` (Memoir p. 47). -/
def minusSp : Submodule ℝ (ℝ × S1 → V) where
  carrier := {w | Continuous w ∧ ∃ c, LimTop w c ∧ LimBot w (-c)}
  add_mem' := by
    rintro w w' ⟨h1, c, hc1, hc2⟩ ⟨k1, d, hd1, hd2⟩
    exact ⟨h1.add k1, c + d, hc1.add hd1, by rw [neg_add]; exact hc2.add hd2⟩
  zero_mem' := ⟨continuous_const, 0, LimTop.zero, by rw [neg_zero]; exact LimBot.zero⟩
  smul_mem' := by
    rintro r w ⟨h1, c, hc1, hc2⟩
    exact ⟨h1.const_smul r, r • c, hc1.smul r, by rw [← smul_neg]; exact hc2.smul r⟩

variable {V}

lemma integrable_circ {f : ℝ × S1 → V} (hf : Continuous f) (σ : ℝ) :
    Integrable (fun t : S1 => f (σ, t)) :=
  (hf.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma circ_add {f g : ℝ × S1 → V} (hf : Continuous f) (hg : Continuous g) (σ : ℝ) :
    circ (f + g) σ = circ f σ + circ g σ :=
  integral_add (integrable_circ hf σ) (integrable_circ hg σ)

lemma circ_smul (f : ℝ × S1 → V) (r : ℝ) (σ : ℝ) : circ (r • f) σ = r • circ f σ :=
  integral_smul r _

variable (β R ϑ)

/-- `⊕_a`, linear on all pairs of maps. -/
def glueLin : ((HalfP → V) × (HalfN → V)) →ₗ[ℝ] (Zcyl R → V) where
  toFun := glue β R ϑ
  map_add' h k := by
    funext z; simp only [glue, extP, extN, Prod.fst_add, Prod.snd_add, Pi.add_apply]; module
  map_smul' r h := by
    funext z; simp only [glue, extP, extN, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply,
      RingHom.id_apply]; module

/-- `⊖̂_a`, linear on all pairs of maps. -/
def antiHatLin : ((HalfP → V) × (HalfN → V)) →ₗ[ℝ] (ℝ × S1 → V) where
  toFun := antiHat β R ϑ
  map_add' h k := by
    funext z; simp only [antiHat, extP, extN, Prod.fst_add, Prod.snd_add, Pi.add_apply]; module
  map_smul' r h := by
    funext z; simp only [antiHat, extP, extN, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply,
      RingHom.id_apply]; module

/-- `av_a` on `E`. -/
def avL : pairSp V →ₗ[ℝ] V where
  toFun h := av R h.1
  map_add' h k := by
    obtain ⟨h1, h2, -⟩ := h.2
    obtain ⟨k1, k2, -⟩ := k.2
    simp only [av, Submodule.coe_add, Prod.fst_add, Prod.snd_add]
    have e1 : extP ((h : (HalfP → V) × (HalfN → V)).1 + (k : (HalfP → V) × (HalfN → V)).1) =
        extP (h : (HalfP → V) × (HalfN → V)).1 + extP (k : (HalfP → V) × (HalfN → V)).1 := rfl
    have e2 : extN ((h : (HalfP → V) × (HalfN → V)).2 + (k : (HalfP → V) × (HalfN → V)).2) =
        extN (h : (HalfP → V) × (HalfN → V)).2 + extN (k : (HalfP → V) × (HalfN → V)).2 := rfl
    rw [e1, e2, circ_add (continuous_extP h1) (continuous_extP k1),
      circ_add (continuous_extN h2) (continuous_extN k2)]
    module
  map_smul' r h := by
    simp only [av, Submodule.coe_smul, Prod.smul_fst, Prod.smul_snd, RingHom.id_apply]
    have e1 : extP (r • (h : (HalfP → V) × (HalfN → V)).1) =
        r • extP (h : (HalfP → V) × (HalfN → V)).1 := rfl
    have e2 : extN (r • (h : (HalfP → V) × (HalfN → V)).2) =
        r • extN (h : (HalfP → V) × (HalfN → V)).2 := rfl
    rw [e1, e2, circ_smul, circ_smul]
    module

variable {β R ϑ}
variable (hβ : IsCutoff β)
include hβ

lemma continuous_glue {h : (HalfP → V) × (HalfN → V)} (h1 : Continuous h.1) (h2 : Continuous h.2) :
    Continuous (glue β R ϑ h) := by
  have hb : Continuous fun z : Zcyl R => βa β R z.1.1 :=
    (continuous_βa hβ).comp (continuous_subtype_val.comp continuous_fst)
  have hz : Continuous fun z : Zcyl R => (z.1.1, z.2) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  exact (hb.smul ((continuous_extP h1).comp hz)).add
    ((continuous_const.sub hb).smul ((continuous_extN h2).comp (continuous_sh.comp hz)))

lemma continuous_antiHat {h : (HalfP → V) × (HalfN → V)} (h1 : Continuous h.1)
    (h2 : Continuous h.2) : Continuous (antiHat β R ϑ h) := by
  have hb : Continuous fun x : ℝ × S1 => βa β R x.1 := (continuous_βa hβ).comp continuous_fst
  exact ((continuous_const.sub hb).neg.smul (continuous_extP h1)).add
    (hb.smul ((continuous_extN h2).comp continuous_sh))

end Spaces

end GWMemoir.Neck
