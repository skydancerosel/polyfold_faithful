import GWMemoir.GluingSplicing
import GWMemoir.NeckOperators

/-!
# Memoir §2.4, Theorem 2.49(1): the total glued map at the Sobolev levels, for a fixed `a`

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, §2.4, pp. 49–50.

For a gluing parameter `0 < |a| < 1/2` (`R = φ(|a|)`, `a = |a| e^{-2πiϑ}`), the memoir's total
glued map `Φ_a = (⊕_a, ⊖_a) : E → G^a` on the levels
`E_m = H^{3+m,δ_m}_c(ℝ^± × S¹)`, `G^a_m = H^{3+m}(Z_a) ⊕ H^{3+m,δ_m}_c(C_a)`.

We write `h^± = c + r^±` (`r^± ∈ H^{3+m,δ_m}(ℝ^± × S¹)`) and an element of `H^{3+m,δ_m}_c(C_a)` as
`(1 - 2β_a) c' + w` (`w ∈ H^{3+m,δ_m}(C_a)`, Memoir p. 50).  Then, with `τ r(s,t) = r(s - R, t - ϑ)`
and `[r]_σ = ∫_{S¹} r(σ, t) dt`,
* `⊕_a(h) = c + β_a r⁺ + (1 - β_a) τ r⁻` on `Z_a`,
* `⊖_a(h) = (1 - 2β_a) c' + (β_a - 1) r⁺ + β_a τ r⁻` with `c' = av_a(h) - c = ½([r⁺]_{R/2} + [r⁻]_{-R/2})`.

This is `Phi m` (`phi_apply`).  Its inverse `Psi m` is the Sobolev form of (2.6), (2.7); the
identities `identA`–`identD` are the two compositions on representatives.  The sc-isomorphism
itself, `memoir_theorem_2_49_one`, is in `GWMemoir.GluingIso`.

The maps are real-valued; the `ℝ²ⁿ`-valued spaces are `2n`-fold products, on which `Φ_a` acts
componentwise.  `Z_a` and the half-cylinders carry the restriction spaces of `GWMemoir.HalfCylinders`.
-/

open Set Filter Topology MeasureTheory
open scoped ContDiff
open Polyfold Polyfold.CylinderSobolev

set_option linter.unusedSectionVars false

noncomputable section

namespace GWMemoir.Neck

/-! ## 1. Multipliers built from `β_a`; localizers; the cut-off on `Z_a` -/

lemma hasCompactSupport_deriv_of_locConst {χ : ℝ → ℝ} {a b : ℝ}
    (h : ∀ s ∉ Icc a b, ∀ᶠ y in 𝓝 s, χ y = χ s) : HasCompactSupport (deriv χ) :=
  HasCompactSupport.intro isCompact_Icc fun s hs =>
    (Filter.EventuallyEq.deriv_eq (f := fun _ => χ s) (h s hs)).trans (deriv_const s _)

variable {β : ℝ → ℝ} {R : ℝ}

lemma βa_locConst (hβ : IsCutoff β) {s : ℝ} (hs : s ∉ Icc (R / 2 - 2) (R / 2 + 2)) :
    ∀ᶠ y in 𝓝 s, βa β R y = βa β R s := by
  simp only [mem_Icc, not_and_or, not_le] at hs
  rcases hs with hs | hs
  · filter_upwards [Iio_mem_nhds (show s < R / 2 - 1 by linarith)] with y hy
    rw [βa_one hβ (le_of_lt hy), βa_one hβ (by linarith)]
  · filter_upwards [Ioi_mem_nhds (show R / 2 + 1 < s by linarith)] with y hy
    rw [βa_zero hβ (le_of_lt hy), βa_zero hβ (by linarith)]

/-- `F(β_a(s))` is a multiplier for every smooth `F`. -/
lemma multβ (hβ : IsCutoff β) (R : ℝ) {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (m : ℕ) :
    Mult m fun s => F (βa β R s) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hF.continuous.continuousOn
  refine mult_of_deriv (χ := fun s => F (βa β R s))
    (hF.comp (hβ.smooth.comp (contDiff_id.sub contDiff_const))) (C := C) (fun s => ?_) ?_ m
  · have := hC _ (hβ.mem (s - R / 2)); rwa [Real.norm_eq_abs] at this
  · exact hasCompactSupport_deriv_of_locConst (a := R / 2 - 2) (b := R / 2 + 2) fun s hs =>
      (βa_locConst hβ hs).mono fun y hy => by
        show F (βa β R y) = F (βa β R s); rw [hy]

/-- The four coefficient functions of (2.5)–(2.7), as functions of `b = β_a(s)`. -/
def F3 (b : ℝ) : ℝ := b / (b ^ 2 + (1 - b) ^ 2)
def F4 (b : ℝ) : ℝ := (1 - b) / (b ^ 2 + (1 - b) ^ 2)

lemma contDiff_gam : ContDiff ℝ ∞ fun b : ℝ => b ^ 2 + (1 - b) ^ 2 := by fun_prop

lemma contDiff_F3 : ContDiff ℝ ∞ F3 := contDiff_id.div contDiff_gam fun b => gam_ne b
lemma contDiff_F4 : ContDiff ℝ ∞ F4 :=
  (contDiff_const.sub contDiff_id).div contDiff_gam fun b => gam_ne b

lemma F3_half : F3 (1 / 2) = 1 := by norm_num [F3]
lemma F4_half : F4 (1 / 2) = 1 := by norm_num [F4]
lemma F3_zero : F3 0 = 0 := by simp [F3]
lemma F4_one : F4 1 = 0 := by simp [F4]

section Mults

variable (hβ : IsCutoff β) (R : ℝ) (m : ℕ)
include hβ

lemma m1 : Mult m fun s => βa β R s := multβ hβ R (F := id) contDiff_id m
lemma m2 : Mult m fun s => 1 - βa β R s :=
  multβ hβ R (F := fun b => 1 - b) (contDiff_const.sub contDiff_id) m
lemma m5 : Mult m fun s => βa β R s - 1 :=
  multβ hβ R (F := fun b => b - 1) (contDiff_id.sub contDiff_const) m
lemma m3 : Mult m fun s => F3 (βa β R s) := multβ hβ R contDiff_F3 m
lemma m4 : Mult m fun s => F4 (βa β R s) := multβ hβ R contDiff_F4 m

end Mults

lemma st_abs_le (x : ℝ) : |Real.smoothTransition x| ≤ 1 :=
  abs_le.2 ⟨by linarith [Real.smoothTransition.nonneg x], Real.smoothTransition.le_one x⟩

lemma st_ev_zero {s : ℝ} (hs : s < 0) : ∀ᶠ y in 𝓝 s, Real.smoothTransition y = 0 := by
  filter_upwards [Iio_mem_nhds hs] with y hy using Real.smoothTransition.zero_of_nonpos (le_of_lt hy)

lemma st_ev_one {s : ℝ} (hs : 1 < s) : ∀ᶠ y in 𝓝 s, Real.smoothTransition y = 1 := by
  filter_upwards [Ioi_mem_nhds hs] with y hy using Real.smoothTransition.one_of_one_le (le_of_lt hy)

/-- Localizers: `ηP` vanishes off `(0,∞)`, `ηN` off `(-∞,0)`, `ηZ` off `(0,R)`. -/
def ηP (s : ℝ) : ℝ := Real.smoothTransition s
def ηN (s : ℝ) : ℝ := Real.smoothTransition (-s)
def ηZ (R s : ℝ) : ℝ := Real.smoothTransition s * Real.smoothTransition (R - s)

lemma mult_ηP (m : ℕ) : Mult m ηP :=
  mult_of_deriv (χ := ηP) (Real.smoothTransition.contDiff (n := ⊤)) st_abs_le
    (hasCompactSupport_deriv_of_locConst (a := 0) (b := 1) fun s hs => by
      simp only [mem_Icc, not_and_or, not_le] at hs
      rcases hs with hs | hs
      · filter_upwards [st_ev_zero hs] with y hy
        simp only [ηP, hy, Real.smoothTransition.zero_of_nonpos hs.le]
      · filter_upwards [st_ev_one hs] with y hy
        simp only [ηP, hy, Real.smoothTransition.one_of_one_le hs.le]) m

lemma mult_ηN (m : ℕ) : Mult m ηN :=
  mult_of_deriv (χ := ηN) ((Real.smoothTransition.contDiff (n := ⊤)).comp contDiff_neg)
    (fun s => st_abs_le _)
    (hasCompactSupport_deriv_of_locConst (a := -1) (b := 0) fun s hs => by
      simp only [mem_Icc, not_and_or, not_le] at hs
      rcases hs with hs | hs
      · have h1 : 1 < -s := by linarith
        filter_upwards [(continuous_neg.tendsto s).eventually (st_ev_one (s := -s) h1)] with y hy
        simp only [ηN, hy, Real.smoothTransition.one_of_one_le h1.le]
      · have h1 : -s < 0 := by linarith
        filter_upwards [(continuous_neg.tendsto s).eventually (st_ev_zero (s := -s) h1)] with y hy
        simp only [ηN, hy, Real.smoothTransition.zero_of_nonpos h1.le]) m

lemma mult_ηZ (R : ℝ) (m : ℕ) : Mult m (ηZ R) :=
  mult_of_deriv (χ := ηZ R) ((Real.smoothTransition.contDiff (n := ⊤)).mul
      ((Real.smoothTransition.contDiff (n := ⊤)).comp (contDiff_const.sub contDiff_id)))
    (C := 1) (fun s => by
      rw [ηZ, abs_mul]
      exact mul_le_one₀ (st_abs_le _) (abs_nonneg _) (st_abs_le _))
    (hasCompactSupport_deriv_of_locConst (a := 0) (b := R) fun s hs => by
      simp only [mem_Icc, not_and_or, not_le] at hs
      rcases hs with hs | hs
      · filter_upwards [st_ev_zero hs] with y hy
        simp only [ηZ, hy, Real.smoothTransition.zero_of_nonpos hs.le, zero_mul]
      · have h1 : R - s < 0 := by linarith
        filter_upwards [(Continuous.tendsto (f := fun y : ℝ => R - y) (by fun_prop) s).eventually
          (st_ev_zero (s := R - s) h1)] with y hy
        simp only [ηZ, hy, Real.smoothTransition.zero_of_nonpos h1.le, mul_zero]) m

/-- The cut-off `χ_Z(s) = 1` on `[0, R]` (used for the constant `c` on `Z_a`). -/
def chiZ (R : ℝ) : ℝ → ℝ := (exists_win (ρ := |R| + 1) (by positivity)).choose

lemma chiZ_spec (R : ℝ) : ContDiff ℝ ∞ (chiZ R) ∧ (∀ s, |R| + 1 + 2 ≤ |s| → chiZ R s = 0) ∧
    ∀ s ∈ Icc (-(|R| + 1)) (|R| + 1), chiZ R s = 1 :=
  (exists_win (ρ := |R| + 1) (by positivity)).choose_spec

lemma isTest_chiZ (R : ℝ) : IsTest fun x : ℝ × ℝ => chiZ R x.1 :=
  isTest_of_s (chiZ_spec R).1 (chiZ_spec R).2.1

lemma chiZ_one {s : ℝ} (hs : s ∈ Icc (0 : ℝ) R) : chiZ R s = 1 :=
  (chiZ_spec R).2.2 s ⟨by linarith [abs_nonneg R, hs.1], by linarith [le_abs_self R, hs.2]⟩

/-! ## 2. Vanishing on `I × S¹` -/

section Van

variable {m : ℕ} {δ : ℝ} {hδ : 0 ≤ δ}

/-- `f` vanishes on `I × S¹`. -/
def Van (I : Set ℝ) (f : Lp ℝ 2 cyl) : Prop := ∀ᵐ x ∂cyl, x.1 ∈ I → f x = 0

lemma van_mulHL {I J : Set ℝ} {u : H m hδ} (h : Van I (valCLM m hδ u)) {f : ℝ → ℝ} (hf : Mult m f)
    (hJ : ∀ s ∈ J, s ∉ I → f s = 0) : Van J (valCLM m hδ (mulHL f hf u)) := by
  filter_upwards [val_mulHL f hf u, h] with x h1 h2 hx
  rw [h1]
  by_cases hI : x.1 ∈ I
  · rw [h2 hI, mul_zero]
  · rw [hJ _ hx hI, zero_mul]

lemma van_shH {I J : Set ℝ} {u : H m hδ} (h : Van I (valCLM m hδ u)) (R ϑ : ℝ)
    (hJ : ∀ s ∈ J, s - R ∈ I) : Van J (valCLM m hδ (shH R ϑ u)) := by
  have h' := (measurePreserving_shT R ϑ).quasiMeasurePreserving.ae h
  filter_upwards [val_shH R ϑ u, h'] with x h1 h2 hx
  rw [h1]; exact h2 (hJ _ hx)

lemma eq_zero_of_van_univ {u : H m hδ} (h : Van univ (valCLM m hδ u)) : u = 0 := by
  apply valCLM_injective
  rw [map_zero]
  apply Lp.ext
  filter_upwards [h, Lp.coeFn_zero ℝ 2 cyl] with x h1 h2
  rw [h1 (mem_univ _), h2]; rfl

end Van

/-! ## 3. The levels: the maps `Phi m` and `Psi m` -/

section Levels

variable (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)

/-- The level-`m` vanishing subspaces. -/
abbrev LP (m : ℕ) := (scCyl δ h0 hmono).levelSub (vanishH δ h0 hmono (Ioi 0) measurableSet_Ioi) m
abbrev LN (m : ℕ) := (scCyl δ h0 hmono).levelSub (vanishH δ h0 hmono (Iio 0) measurableSet_Iio) m
abbrev LZ (R : ℝ) (m : ℕ) :=
  (scCyl δ h0 hmono).levelSub (vanishH δ h0 hmono (Ioo 0 R) measurableSet_Ioo) m

variable {δ h0 hmono}

lemma memL {I : Set ℝ} {hI : MeasurableSet I} {m : ℕ} {u : (scCyl δ h0 hmono) m} :
    u ∈ (scCyl δ h0 hmono).levelSub (vanishH δ h0 hmono I hI) m ↔
      Van I (valCLM (3 + m) (δ_nonneg δ h0 hmono m) u) :=
  (mem_levelSub_vanishH δ h0 hmono).trans mem_vanishLp

lemma hm3 (m : ℕ) : 1 ≤ 3 + m := by omega

variable (hβ : IsCutoff β) (hR2 : 2 ≤ R) (ϑ : ℝ) (m : ℕ)

variable (δ h0 hmono)

/-- `[r⁺]_{R/2}/2` on `H^{3+m,δ_m}(ℝ⁺ × S¹)`. -/
def TP : (scHalfPos δ h0 hmono) m →L[ℝ] ℝ :=
  (LP δ h0 hmono m).liftQL ((1 / 2 : ℝ) • trH (hm3 m) (R / 2)) fun u hu => by
    have := trH_eq_zero_of_vanish (hm3 m) (R / 2) (mult_ηP _)
      (fun s hs => Real.smoothTransition.zero_of_nonpos (not_lt.1 hs))
      (Real.smoothTransition.one_of_one_le (by linarith)) (memL.1 hu)
    change (1 / 2 : ℝ) • trH (hm3 m) (R / 2) u = 0
    rw [this, smul_zero]

/-- `[r⁻]_{-R/2}/2` on `H^{3+m,δ_m}(ℝ⁻ × S¹)`. -/
def TN : (scHalfNeg δ h0 hmono) m →L[ℝ] ℝ :=
  (LN δ h0 hmono m).liftQL ((1 / 2 : ℝ) • trH (hm3 m) (-(R / 2))) fun u hu => by
    have := trH_eq_zero_of_vanish (hm3 m) (-(R / 2)) (mult_ηN _)
      (fun s hs => Real.smoothTransition.zero_of_nonpos (by simp only [mem_Iio, not_lt] at hs; linarith))
      (by simp only [ηN, neg_neg]; exact Real.smoothTransition.one_of_one_le (by linarith))
      (memL.1 hu)
    change (1 / 2 : ℝ) • trH (hm3 m) (-(R / 2)) u = 0
    rw [this, smul_zero]

/-- `[v]_{R/2}` on `H^{3+m}(Z_a)`. -/
def TZ : (scFin δ h0 hmono R) m →L[ℝ] ℝ :=
  (LZ δ h0 hmono R m).liftQL (trH (hm3 m) (R / 2)) fun u hu =>
    trH_eq_zero_of_vanish (hm3 m) (R / 2) (mult_ηZ R _)
      (fun s hs => by
        simp only [mem_Ioo, not_and_or, not_lt] at hs
        rcases hs with hs | hs
        · simp [ηZ, Real.smoothTransition.zero_of_nonpos hs]
        · simp [ηZ, Real.smoothTransition.zero_of_nonpos (show R - s ≤ 0 by linarith)])
      (by simp only [ηZ]; rw [Real.smoothTransition.one_of_one_le (by linarith),
        Real.smoothTransition.one_of_one_le (by linarith), one_mul])
      (memL.1 hu)

/-- `r⁺ ↦ [β_a r⁺]_{Z_a}`. -/
def AP : (scHalfPos δ h0 hmono) m →L[ℝ] (scFin δ h0 hmono R) m :=
  (LP δ h0 hmono m).liftQL ((LZ δ h0 hmono R m).mkQL.comp (mulHL _ (m1 hβ R (3 + m)))) fun _ hu =>
    (Submodule.Quotient.mk_eq_zero _).2 (memL.2 (van_mulHL (memL.1 hu) _ fun _ hs hs' =>
      absurd hs.1 hs'))

/-- `r⁻ ↦ [(1 - β_a) τ r⁻]_{Z_a}`. -/
def AN : (scHalfNeg δ h0 hmono) m →L[ℝ] (scFin δ h0 hmono R) m :=
  (LN δ h0 hmono m).liftQL ((LZ δ h0 hmono R m).mkQL.comp
      ((mulHL _ (m2 hβ R (3 + m))).comp (shH R ϑ))) fun u hu =>
    (Submodule.Quotient.mk_eq_zero _).2 (memL.2 (van_mulHL (I := Iio R)
      (van_shH (memL.1 hu) R ϑ fun s hs => by simp only [mem_Iio] at hs ⊢; linarith) _
      fun s hs hs' => absurd hs.2 hs'))

/-- `r⁺ ↦ (β_a - 1) r⁺` on `C_a`. -/
def BP : (scHalfPos δ h0 hmono) m →L[ℝ] (scCyl δ h0 hmono) m :=
  (LP δ h0 hmono m).liftQL (mulHL _ (m5 hβ R (3 + m))) fun u hu =>
    eq_zero_of_van_univ (van_mulHL (memL.1 hu) _ fun s _ hs => by
      simp only [mem_Ioi, not_lt] at hs
      rw [βa_one hβ (by linarith), sub_self])

/-- `r⁻ ↦ β_a τ r⁻` on `C_a`. -/
def BN : (scHalfNeg δ h0 hmono) m →L[ℝ] (scCyl δ h0 hmono) m :=
  (LN δ h0 hmono m).liftQL ((mulHL _ (m1 hβ R (3 + m))).comp (shH R ϑ)) fun u hu =>
    eq_zero_of_van_univ (van_mulHL (I := Iio R)
      (van_shH (memL.1 hu) R ϑ fun s hs => by simp only [mem_Iio] at hs ⊢; linarith) _
      fun s _ hs => by
        simp only [mem_Iio, not_lt] at hs
        exact βa_zero hβ (by linarith))

/-- `v ↦ [(β_a/γ_a) v]_{ℝ⁺}`. -/
def PP : (scFin δ h0 hmono R) m →L[ℝ] (scHalfPos δ h0 hmono) m :=
  (LZ δ h0 hmono R m).liftQL ((LP δ h0 hmono m).mkQL.comp (mulHL _ (m3 hβ R (3 + m))))
    fun u hu => (Submodule.Quotient.mk_eq_zero _).2 (memL.2 (van_mulHL (memL.1 hu) _
      fun s hs hs' => by
        simp only [mem_Ioi] at hs
        simp only [mem_Ioo, not_and_or, not_lt] at hs'
        rcases hs' with h | h
        · exact absurd hs (not_lt.2 h)
        · rw [βa_zero hβ (by linarith), F3_zero]))

/-- `v ↦ [τ⁻¹((1 - β_a)/γ_a) v]_{ℝ⁻}`. -/
def PN : (scFin δ h0 hmono R) m →L[ℝ] (scHalfNeg δ h0 hmono) m :=
  (LZ δ h0 hmono R m).liftQL ((LN δ h0 hmono m).mkQL.comp
      ((shH (-R) (-ϑ)).comp (mulHL _ (m4 hβ R (3 + m))))) fun u hu =>
    (Submodule.Quotient.mk_eq_zero _).2 (memL.2 (van_shH (I := Iio R)
      (van_mulHL (memL.1 hu) _ fun s hs hs' => by
        simp only [mem_Iio] at hs
        simp only [mem_Ioo, not_and_or, not_lt] at hs'
        rcases hs' with h | h
        · rw [βa_one hβ (by linarith), F4_one]
        · exact absurd hs (not_lt.2 h)) (-R) (-ϑ)
      fun s hs => by simp only [mem_Iio] at hs ⊢; linarith))

/-- The class of the cut-off `χ_Z` in `H^{3+m}(Z_a)`: the constant `1` on `Z_a`. -/
def gZ : (scFin δ h0 hmono R) m :=
  (LZ δ h0 hmono R m).mkQL (toH (3 + m) (δ_nonneg δ h0 hmono m) (isTest_chiZ R))

/-- The projections of `E_m = ℝ ⊕ H(ℝ⁺ × S¹) ⊕ H(ℝ⁻ × S¹)`. -/
def prC : (scPair δ h0 hmono) m →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ _ _
def prP : (scPair δ h0 hmono) m →L[ℝ] (scHalfPos δ h0 hmono) m :=
  (ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)
def prN : (scPair δ h0 hmono) m →L[ℝ] (scHalfNeg δ h0 hmono) m :=
  (ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)

/-- The projections of `G^a_m = H(Z_a) ⊕ ℝ ⊕ H(C_a)`. -/
def qrV : (scG δ h0 hmono R) m →L[ℝ] (scFin δ h0 hmono R) m := ContinuousLinearMap.fst ℝ _ _
def qrC : (scG δ h0 hmono R) m →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ((scCyl δ h0 hmono) m)).comp
    (ContinuousLinearMap.snd ℝ ((scFin δ h0 hmono R) m) (ℝ × (scCyl δ h0 hmono) m))
def qrW : (scG δ h0 hmono R) m →L[ℝ] (scCyl δ h0 hmono) m :=
  (ContinuousLinearMap.snd ℝ ℝ ((scCyl δ h0 hmono) m)).comp
    (ContinuousLinearMap.snd ℝ ((scFin δ h0 hmono R) m) (ℝ × (scCyl δ h0 hmono) m))

/-- The level `m` of the total glued map: `(c, r⁺, r⁻) ↦
(c + β_a r⁺ + (1 - β_a) τ r⁻, (½([r⁺]_{R/2} + [r⁻]_{-R/2}), (β_a - 1) r⁺ + β_a τ r⁻))`. -/
def Phi : (scPair δ h0 hmono) m →L[ℝ] (scG δ h0 hmono R) m :=
  ((prC δ h0 hmono m).smulRight (gZ δ h0 hmono (R := R) m) +
      (AP δ h0 hmono hβ m).comp (prP δ h0 hmono m) +
      (AN δ h0 hmono hβ ϑ m).comp (prN δ h0 hmono m)).prod
    (((TP δ h0 hmono hR2 m).comp (prP δ h0 hmono m) +
        (TN δ h0 hmono hR2 m).comp (prN δ h0 hmono m)).prod
      ((BP δ h0 hmono hβ hR2 m).comp (prP δ h0 hmono m) +
        (BN δ h0 hmono hβ hR2 ϑ m).comp (prN δ h0 hmono m)))

lemma phi_apply (c : ℝ) (p : (scHalfPos δ h0 hmono) m) (q : (scHalfNeg δ h0 hmono) m) :
    Phi δ h0 hmono hβ hR2 ϑ m (c, p, q) =
      (c • gZ δ h0 hmono (R := R) m + AP δ h0 hmono hβ m p + AN δ h0 hmono hβ ϑ m q,
        TP δ h0 hmono hR2 m p + TN δ h0 hmono hR2 m q,
        BP δ h0 hmono hβ hR2 m p + BN δ h0 hmono hβ hR2 ϑ m q) := rfl

/-- `c(v, c', w) = [v]_{R/2} - c'`. -/
def cPsi : (scG δ h0 hmono R) m →L[ℝ] ℝ :=
  (TZ δ h0 hmono hR2 m).comp (qrV δ h0 hmono m) - qrC δ h0 hmono m

/-- `[(β_a/γ_a) χ_Z]_{ℝ⁺}` and `[τ⁻¹((1 - β_a)/γ_a) χ_Z]_{ℝ⁻}`. -/
def eP : (scHalfPos δ h0 hmono) m :=
  (LP δ h0 hmono m).mkQL
    (mulHL _ (m3 hβ R (3 + m)) (toH (3 + m) (δ_nonneg δ h0 hmono m) (isTest_chiZ R)))
def eN : (scHalfNeg δ h0 hmono) m :=
  (LN δ h0 hmono m).mkQL (shH (-R) (-ϑ)
    (mulHL _ (m4 hβ R (3 + m)) (toH (3 + m) (δ_nonneg δ h0 hmono m) (isTest_chiZ R))))

/-- `w ↦ [((1 - β_a)/γ_a) w]_{ℝ⁺}` and `w ↦ [τ⁻¹(β_a/γ_a) w]_{ℝ⁻}`. -/
def WP : (scCyl δ h0 hmono) m →L[ℝ] (scHalfPos δ h0 hmono) m :=
  (LP δ h0 hmono m).mkQL.comp (mulHL _ (m4 hβ R (3 + m)))
def WN : (scCyl δ h0 hmono) m →L[ℝ] (scHalfNeg δ h0 hmono) m :=
  (LN δ h0 hmono m).mkQL.comp ((shH (-R) (-ϑ)).comp (mulHL _ (m3 hβ R (3 + m))))

/-- The inverse of `Phi m`, the Sobolev form of (2.6), (2.7): `c = [v]_{R/2} - c'`,
`r⁺ = (β_a/γ_a)(v - c) - ((1 - β_a)/γ_a) w`, `r⁻ = τ⁻¹(((1 - β_a)/γ_a)(v - c) + (β_a/γ_a) w)`. -/
def Psi : (scG δ h0 hmono R) m →L[ℝ] (scPair δ h0 hmono) m :=
  (cPsi δ h0 hmono hR2 m).prod
    (((PP δ h0 hmono hβ hR2 m).comp (qrV δ h0 hmono m) -
        (cPsi δ h0 hmono hR2 m).smulRight (eP δ h0 hmono hβ (R := R) m) -
        (WP δ h0 hmono hβ (R := R) m).comp (qrW δ h0 hmono m)).prod
      ((PN δ h0 hmono hβ hR2 ϑ m).comp (qrV δ h0 hmono m) -
        (cPsi δ h0 hmono hR2 m).smulRight (eN δ h0 hmono hβ (R := R) ϑ m) +
        (WN δ h0 hmono hβ (R := R) ϑ m).comp (qrW δ h0 hmono m)))

lemma psi_apply (v : (scFin δ h0 hmono R) m) (c' : ℝ) (w : (scCyl δ h0 hmono) m) :
    Psi δ h0 hmono hβ hR2 ϑ m (v, c', w) =
      (TZ δ h0 hmono hR2 m v - c',
        PP δ h0 hmono hβ hR2 m v - (TZ δ h0 hmono hR2 m v - c') • eP δ h0 hmono hβ (R := R) m -
          WP δ h0 hmono hβ (R := R) m w,
        PN δ h0 hmono hβ hR2 ϑ m v - (TZ δ h0 hmono hR2 m v - c') • eN δ h0 hmono hβ (R := R) ϑ m +
          WN δ h0 hmono hβ (R := R) ϑ m w) := rfl

end Levels

/-! ## 4. `Psi m` inverts `Phi m` -/

section Comb

variable {m : ℕ} {δ : ℝ} {hδ : 0 ≤ δ}

lemma comb_sub {f g f' g' : ℝ → ℝ} (hf : Mult m f) (hg : Mult m g) (hf' : Mult m f')
    (hg' : Mult m g') {k : ℝ} (e : ∀ s, f s * g s - f' s * g' s = k) (u : H m hδ) :
    mulHL f hf (mulHL g hg u) - mulHL f' hf' (mulHL g' hg' u) = k • u := by
  apply valCLM_injective
  rw [map_sub, map_smul]
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (valCLM m hδ (mulHL f hf (mulHL g hg u)))
      (valCLM m hδ (mulHL f' hf' (mulHL g' hg' u))), Lp.coeFn_smul k (valCLM m hδ u),
    val_mulHL f hf (mulHL g hg u), val_mulHL g hg u, val_mulHL f' hf' (mulHL g' hg' u),
    val_mulHL g' hg' u] with x h1 h2 h3 h4 h5 h6
  rw [h1, h2, Pi.sub_apply, Pi.smul_apply, h3, h4, h5, h6, ← e x.1, smul_eq_mul]; ring

lemma comb_add {f g f' g' : ℝ → ℝ} (hf : Mult m f) (hg : Mult m g) (hf' : Mult m f')
    (hg' : Mult m g') {k : ℝ} (e : ∀ s, f s * g s + f' s * g' s = k) (u : H m hδ) :
    mulHL f hf (mulHL g hg u) + mulHL f' hf' (mulHL g' hg' u) = k • u := by
  apply valCLM_injective
  rw [map_add, map_smul]
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (valCLM m hδ (mulHL f hf (mulHL g hg u)))
      (valCLM m hδ (mulHL f' hf' (mulHL g' hg' u))), Lp.coeFn_smul k (valCLM m hδ u),
    val_mulHL f hf (mulHL g hg u), val_mulHL g hg u, val_mulHL f' hf' (mulHL g' hg' u),
    val_mulHL g' hg' u] with x h1 h2 h3 h4 h5 h6
  rw [h1, h2, Pi.add_apply, Pi.smul_apply, h3, h4, h5, h6, ← e x.1, smul_eq_mul]; ring

end Comb

lemma gam_pos' (b : ℝ) : 0 < b ^ 2 + (1 - b) ^ 2 := by nlinarith [sq_nonneg (2 * b - 1)]

lemma e31_45 (b : ℝ) : F3 b * b - F4 b * (b - 1) = 1 := by
  have := gam_pos' b; simp only [F3, F4]; field_simp; try ring
lemma e32_41 (b : ℝ) : F3 b * (1 - b) - F4 b * b = 0 := by simp only [F3, F4]; ring
lemma e41_35 (b : ℝ) : F4 b * b + F3 b * (b - 1) = 0 := by simp only [F3, F4]; ring
lemma e42_31 (b : ℝ) : F4 b * (1 - b) + F3 b * b = 1 := by
  have := gam_pos' b; simp only [F3, F4]; field_simp; try ring
lemma e13_24 (b : ℝ) : b * F3 b + (1 - b) * F4 b = 1 := by
  have := gam_pos' b; simp only [F3, F4]; field_simp; try ring
lemma e23_14 (b : ℝ) : (1 - b) * F3 b - b * F4 b = 0 := by simp only [F3, F4]; ring
lemma e53_14 (b : ℝ) : (b - 1) * F3 b + b * F4 b = 0 := by simp only [F3, F4]; ring
lemma e13_54 (b : ℝ) : b * F3 b - (b - 1) * F4 b = 1 := by
  have := gam_pos' b; simp only [F3, F4]; field_simp; try ring

section Proofs

variable {δ : ℕ → ℝ} {h0 : 0 ≤ δ 0} {hmono : StrictMono δ}
variable (hβ : IsCutoff β) (hR2 : 2 ≤ R) (ϑ : ℝ) (m : ℕ)
include hβ hR2

local notation "Hm" => H (3 + m) (δ_nonneg δ h0 hmono m)
local notation "χm" => toH (3 + m) (δ_nonneg δ h0 hmono m) (isTest_chiZ R)

lemma βa_half' : βa β R (R / 2) = 1 / 2 := βa_half hβ

lemma chiZ_half : chiZ R (R / 2) = 1 := chiZ_one ⟨by linarith, by linarith⟩

/-- `[χ_Z]_{R/2} = 1`. -/
lemma trH_chi : trH (hm3 m) (R / 2) χm = 1 := by
  rw [trH_toH_s]; exact chiZ_half hβ hR2

/-- `Psi ∘ Phi = id` on representatives: the `r⁺` component. -/
lemma identA (c : ℝ) (a b : Hm) :
    mulHL _ (m3 hβ R (3 + m)) (c • χm + mulHL _ (m1 hβ R (3 + m)) a +
        mulHL _ (m2 hβ R (3 + m)) (shH R ϑ b)) - c • mulHL _ (m3 hβ R (3 + m)) χm -
      mulHL _ (m4 hβ R (3 + m)) (mulHL _ (m5 hβ R (3 + m)) a +
        mulHL _ (m1 hβ R (3 + m)) (shH R ϑ b)) = a := by
  simp only [map_add, map_smul]
  have h1 := comb_sub (m3 hβ R (3 + m)) (m1 hβ R (3 + m)) (m4 hβ R (3 + m)) (m5 hβ R (3 + m))
    (fun s => e31_45 (βa β R s)) a
  have h2 := comb_sub (m3 hβ R (3 + m)) (m2 hβ R (3 + m)) (m4 hβ R (3 + m)) (m1 hβ R (3 + m))
    (fun s => e32_41 (βa β R s)) (shH R ϑ b)
  linear_combination (norm := module) h1 + h2

/-- `Psi ∘ Phi = id` on representatives: the `r⁻` component, before `τ⁻¹`. -/
lemma identB (c : ℝ) (a b : Hm) :
    mulHL _ (m4 hβ R (3 + m)) (c • χm + mulHL _ (m1 hβ R (3 + m)) a +
        mulHL _ (m2 hβ R (3 + m)) (shH R ϑ b)) - c • mulHL _ (m4 hβ R (3 + m)) χm +
      mulHL _ (m3 hβ R (3 + m)) (mulHL _ (m5 hβ R (3 + m)) a +
        mulHL _ (m1 hβ R (3 + m)) (shH R ϑ b)) = shH R ϑ b := by
  simp only [map_add, map_smul]
  have h1 := comb_add (m4 hβ R (3 + m)) (m1 hβ R (3 + m)) (m3 hβ R (3 + m)) (m5 hβ R (3 + m))
    (fun s => e41_35 (βa β R s)) a
  have h2 := comb_add (m4 hβ R (3 + m)) (m2 hβ R (3 + m)) (m3 hβ R (3 + m)) (m1 hβ R (3 + m))
    (fun s => e42_31 (βa β R s)) (shH R ϑ b)
  linear_combination (norm := module) h1 + h2

/-- `Phi ∘ Psi = id` on representatives: the `Z_a` component. -/
lemma identC (c : ℝ) (v w : Hm) :
    c • χm + mulHL _ (m1 hβ R (3 + m)) (mulHL _ (m3 hβ R (3 + m)) v -
        c • mulHL _ (m3 hβ R (3 + m)) χm - mulHL _ (m4 hβ R (3 + m)) w) +
      mulHL _ (m2 hβ R (3 + m)) (mulHL _ (m4 hβ R (3 + m)) v -
        c • mulHL _ (m4 hβ R (3 + m)) χm + mulHL _ (m3 hβ R (3 + m)) w) = v := by
  simp only [map_add, map_sub, map_smul]
  have h1 := comb_add (m1 hβ R (3 + m)) (m3 hβ R (3 + m)) (m2 hβ R (3 + m)) (m4 hβ R (3 + m))
    (fun s => e13_24 (βa β R s)) v
  have h2 := comb_add (m1 hβ R (3 + m)) (m3 hβ R (3 + m)) (m2 hβ R (3 + m)) (m4 hβ R (3 + m))
    (fun s => e13_24 (βa β R s)) χm
  have h3 := comb_sub (m2 hβ R (3 + m)) (m3 hβ R (3 + m)) (m1 hβ R (3 + m)) (m4 hβ R (3 + m))
    (fun s => e23_14 (βa β R s)) w
  linear_combination (norm := module) h1 - c • h2 + h3

/-- `Phi ∘ Psi = id` on representatives: the `C_a` component. -/
lemma identD (c : ℝ) (v w : Hm) :
    mulHL _ (m5 hβ R (3 + m)) (mulHL _ (m3 hβ R (3 + m)) v -
        c • mulHL _ (m3 hβ R (3 + m)) χm - mulHL _ (m4 hβ R (3 + m)) w) +
      mulHL _ (m1 hβ R (3 + m)) (mulHL _ (m4 hβ R (3 + m)) v -
        c • mulHL _ (m4 hβ R (3 + m)) χm + mulHL _ (m3 hβ R (3 + m)) w) = w := by
  simp only [map_add, map_sub, map_smul]
  have h1 := comb_add (m5 hβ R (3 + m)) (m3 hβ R (3 + m)) (m1 hβ R (3 + m)) (m4 hβ R (3 + m))
    (fun s => e53_14 (βa β R s)) v
  have h2 := comb_add (m5 hβ R (3 + m)) (m3 hβ R (3 + m)) (m1 hβ R (3 + m)) (m4 hβ R (3 + m))
    (fun s => e53_14 (βa β R s)) χm
  have h3 := comb_sub (m1 hβ R (3 + m)) (m3 hβ R (3 + m)) (m5 hβ R (3 + m)) (m4 hβ R (3 + m))
    (fun s => e13_54 (βa β R s)) w
  linear_combination (norm := module) h1 - c • h2 + h3

end Proofs

end GWMemoir.Neck
