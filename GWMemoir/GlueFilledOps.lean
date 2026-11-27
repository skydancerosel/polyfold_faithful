import GWMemoir.GlueFilledFibre
import GWMemoir.GlueFilledReflect

/-!
# The filled section at the nodal constant map: the operators on the blocks

HWZ, *Applications of Polyfold Theory I*, Memoirs AMS 248, no. 1179, (4.4)–(4.6) (pp. 103–104)
and (4.18) (p. 116), at `u ≡ q` on two spheres joined at a node (`twoSpheres`).  For a node pair
`jx`, `jy` (the necks at `inl e₂` and `inr e₂`) and gluing parameters `R`, `ϑ` we write, in the
memoir's coordinate `s` on the glued cylinder,
* on the section blocks (block coordinate `= s`): `r⁺ = w_{jx,k}`, `τr⁻ = w_{jy,k}(R - s, ϑ - t)`,
  `c' = ½([r⁺]_{R/2} + [τr⁻]_{R/2})`;
* on the fibre blocks (polar coordinate `= s + s₀`): `ξ⁺ = G_{jx,k}(s + s₀, t)`,
  `τξ⁻ = -G_{jy,k}(R + s₀ - s, ϑ - t)` (the reflection reverses `ds`).

Then
* `glTheta`: `1 - π̂_a` on the node pair, `(ξ⁺, τξ⁻) ↦ (F₄(β_a)((1 - β_a)ξ⁺ - β_a τξ⁻),
  F₃(β_a)(-(1 - β_a)ξ⁺ + β_a τξ⁻))`, an idempotent (`glTheta_idem`);
* `glKL`: the commutator term `K_a h = ½ ⊡̂_a⁻¹(β_a'(r⁺ - τr⁻), β_a'(r⁺ + τr⁻ - 2c'))`, from the
  level-`n` section blocks to the level-`(n+1)` fibre blocks;
* `glHat`, `glAnti`: `⊕̂_a`, `⊖̂_a` on the fibre blocks; `glHat_theta`, `glAnti_theta`,
  `glHat_K`, `glAnti_K`: the pointwise identities behind the equations (4.18).

All of them agree with level `0` along the inclusions and are carried by `s ≥ σ` in the polar
coordinates of every neck once `σ + 2 < R/2 + s₀` (`isFar_glTheta`, `isFar_glKL`).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology NNReal
open Set Function Filter MeasureTheory
open Polyfold Polyfold.CylinderSobolev

noncomputable section

namespace GWMemoir.Neck

/-! ## 1. Vanishing, multipliers -/

section Van

variable {m : ℕ} {δ : ℝ} {hδ : 0 ≤ δ}

lemma van_add {I : Set ℝ} {f g : Lp ℝ 2 cyl} (hf : Van I f) (hg : Van I g) : Van I (f + g) := by
  filter_upwards [hf, hg, Lp.coeFn_add f g] with x h1 h2 h3 hx
  rw [h3, Pi.add_apply, h1 hx, h2 hx, add_zero]

lemma van_neg {I : Set ℝ} {f : Lp ℝ 2 cyl} (hf : Van I f) : Van I (-f) := by
  filter_upwards [hf, Lp.coeFn_neg f] with x h1 h2 hx
  rw [h2, Pi.neg_apply, h1 hx, neg_zero]

lemma van_smul {I : Set ℝ} {f : Lp ℝ 2 cyl} (c : ℝ) (hf : Van I f) : Van I (c • f) := by
  filter_upwards [hf, Lp.coeFn_smul c f] with x h1 h2 hx
  rw [h2, Pi.smul_apply, h1 hx, smul_zero]

lemma van_zero (I : Set ℝ) : Van I (0 : Lp ℝ 2 cyl) := by
  filter_upwards [Lp.coeFn_zero ℝ 2 cyl] with x h1 _
  rw [h1]; rfl

lemma van_of_ae {I : Set ℝ} {f : Lp ℝ 2 cyl} {φ : ℝ × ℝ → ℝ} (h : (f : ℝ × ℝ → ℝ) =ᵐ[cyl] φ)
    (hφ : ∀ x : ℝ × ℝ, x.1 ∈ I → φ x = 0) : Van I f := by
  filter_upwards [h] with x h1 hx
  rw [h1, hφ x hx]

lemma van_mono {I J : Set ℝ} {f : Lp ℝ 2 cyl} (hf : Van I f) (hJ : J ⊆ I) : Van J f := by
  filter_upwards [hf] with x h1 hx
  exact h1 (hJ hx)

lemma van_reflH {I J : Set ℝ} {u : H m hδ} (h : Van I (valCLM m hδ u)) (c ϑ : ℝ)
    (hJ : ∀ s ∈ J, c - s ∈ I) : Van J (valCLM m hδ (reflH c ϑ u)) := by
  have h' := (measurePreserving_rfT c ϑ).quasiMeasurePreserving.ae h
  filter_upwards [val_reflH c ϑ u, h'] with x h1 h2 hx
  rw [h1]; exact h2 (hJ _ hx)

lemma val_mulHL_add {p r : ℝ → ℝ} (hp : Mult m p) (hr : Mult m r) (u v : H m hδ) :
    (valCLM m hδ (mulHL p hp u + mulHL r hr v) : ℝ × ℝ → ℝ) =ᵐ[cyl]
      fun x => p x.1 * valCLM m hδ u x + r x.1 * valCLM m hδ v x := by
  rw [map_add]
  filter_upwards [Lp.coeFn_add (valCLM m hδ (mulHL p hp u)) (valCLM m hδ (mulHL r hr v)),
    val_mulHL p hp u, val_mulHL r hr v] with x h1 h2 h3
  rw [h1, Pi.add_apply, h2, h3]

/-- Two pointwise `2 × 2` multiplications compose to their pointwise product. -/
lemma comb22 {f g p p' r r' a b : ℝ → ℝ} (hf : Mult m f) (hg : Mult m g) (hp : Mult m p)
    (hp' : Mult m p') (hr : Mult m r) (hr' : Mult m r') (ha : Mult m a) (hb : Mult m b)
    (e1 : ∀ s, f s * p s + g s * r s = a s) (e2 : ∀ s, f s * p' s + g s * r' s = b s)
    (u v : H m hδ) :
    mulHL f hf (mulHL p hp u + mulHL p' hp' v) + mulHL g hg (mulHL r hr u + mulHL r' hr' v) =
      mulHL a ha u + mulHL b hb v := by
  apply valCLM_injective
  apply Lp.ext
  filter_upwards [val_mulHL_add hf hg (mulHL p hp u + mulHL p' hp' v) (mulHL r hr u + mulHL r' hr' v),
    val_mulHL_add hp hp' u v, val_mulHL_add hr hr' u v, val_mulHL_add ha hb u v]
    with x h1 h2 h3 h4
  rw [h1, h2, h3, h4, ← e1, ← e2]
  ring

end Van

/-! ### Multipliers built from `β_a` -/

section Mults

lemma mult_of_hasCompactSupport {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (m : ℕ) : Mult m χ := by
  obtain ⟨C, hC⟩ := hχ.continuous.bounded_above_of_compact_support hc
  exact mult_of_deriv hχ (C := C) (fun s => by simpa [Real.norm_eq_abs] using hC s) hc.deriv m

variable {β : ℝ → ℝ} {R : ℝ}

/-- `β_a'`. -/
def dβa (β : ℝ → ℝ) (R : ℝ) : ℝ → ℝ := deriv (βa β R)

lemma contDiff_βa (hβ : IsCutoff β) : ContDiff ℝ ∞ (βa β R) :=
  hβ.smooth.comp (contDiff_id.sub contDiff_const)

lemma contDiff_dβa (hβ : IsCutoff β) : ContDiff ℝ ∞ (dβa β R) :=
  (contDiff_infty_iff_deriv.1 (contDiff_βa hβ)).2

lemma dβa_eq_zero (hβ : IsCutoff β) {s : ℝ} (hs : s ∉ Icc (R / 2 - 2) (R / 2 + 2)) :
    dβa β R s = 0 :=
  (Filter.EventuallyEq.deriv_eq (f := fun _ => βa β R s) (βa_locConst hβ hs)).trans
    (deriv_const s _)

/-- `F(β_a) β_a'`, compactly supported in `|s - R/2| ≤ 2`. -/
def kq (β : ℝ → ℝ) (R : ℝ) (F : ℝ → ℝ) (s : ℝ) : ℝ := F (βa β R s) * dβa β R s

variable {F : ℝ → ℝ}

lemma contDiff_kq (hβ : IsCutoff β) (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (kq β R F) :=
  (hF.comp (contDiff_βa hβ)).mul (contDiff_dβa hβ)

lemma kq_eq_zero (hβ : IsCutoff β) {s : ℝ} (hs : s ∉ Icc (R / 2 - 2) (R / 2 + 2)) :
    kq β R F s = 0 := by
  simp only [kq, dβa_eq_zero hβ hs, mul_zero]

lemma hasCompactSupport_kq (hβ : IsCutoff β) : HasCompactSupport (kq β R F) :=
  HasCompactSupport.intro isCompact_Icc fun _ hs => kq_eq_zero hβ hs

lemma mult_kq (hβ : IsCutoff β) (hF : ContDiff ℝ ∞ F) (m : ℕ) : Mult m (kq β R F) :=
  mult_of_hasCompactSupport (contDiff_kq hβ hF) (hasCompactSupport_kq hβ) m

lemma isTest_kq (hβ : IsCutoff β) (hF : ContDiff ℝ ∞ F) :
    IsTest fun x : ℝ × ℝ => kq β R F x.1 :=
  isTest_of_s (contDiff_kq hβ hF) (R := |R / 2| + 3) fun s hs => kq_eq_zero hβ fun h => by
    have h1 := neg_abs_le (R / 2)
    have h2 := le_abs_self (R / 2)
    have : |s| ≤ |R / 2| + 2 := abs_le.2 ⟨by linarith [h.1], by linarith [h.2]⟩
    linarith

/-- The entries of `1 - π̂_a`, as functions of `b = β_a`. -/
def hatG1 (b : ℝ) : ℝ := F4 b * (1 - b)
def hatG2 (b : ℝ) : ℝ := -(F4 b * b)
def hatG3 (b : ℝ) : ℝ := -(F3 b * (1 - b))
def hatG4 (b : ℝ) : ℝ := F3 b * b

lemma contDiff_hatG1 : ContDiff ℝ ∞ hatG1 := contDiff_F4.mul (contDiff_const.sub contDiff_id)
lemma contDiff_hatG2 : ContDiff ℝ ∞ hatG2 := (contDiff_F4.mul contDiff_id).neg
lemma contDiff_hatG3 : ContDiff ℝ ∞ hatG3 := (contDiff_F3.mul (contDiff_const.sub contDiff_id)).neg
lemma contDiff_hatG4 : ContDiff ℝ ∞ hatG4 := contDiff_F3.mul contDiff_id

lemma hatG_idem (b : ℝ) :
    (hatG1 b * hatG1 b + hatG2 b * hatG3 b = hatG1 b ∧
      hatG1 b * hatG2 b + hatG2 b * hatG4 b = hatG2 b) ∧
    (hatG3 b * hatG1 b + hatG4 b * hatG3 b = hatG3 b ∧
      hatG3 b * hatG2 b + hatG4 b * hatG4 b = hatG4 b) := by
  have hγ := (gam_pos' b).ne'
  simp only [hatG1, hatG2, hatG3, hatG4, F3, F4]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> field_simp <;> ring

lemma hatG_glue (b : ℝ) :
    (b * hatG1 b + (1 - b) * hatG3 b = 0 ∧ b * hatG2 b + (1 - b) * hatG4 b = 0) ∧
    ((b - 1) * hatG1 b + b * hatG3 b = b - 1 ∧ (b - 1) * hatG2 b + b * hatG4 b = b) := by
  have hγ := (gam_pos' b).ne'
  simp only [hatG1, hatG2, hatG3, hatG4, F3, F4]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> field_simp <;> ring

/-- The coefficients of `K_a`, as functions of `b = β_a` (times `β_a'`). -/
def kG1 (b : ℝ) : ℝ := (F3 b - F4 b) / 2
def kG2 (b : ℝ) : ℝ := -((F3 b + F4 b) / 2)
def kG4 (b : ℝ) : ℝ := (F3 b + F4 b) / 2
def kG6 (b : ℝ) : ℝ := -F3 b

lemma contDiff_kG1 : ContDiff ℝ ∞ kG1 := (contDiff_F3.sub contDiff_F4).div_const _
lemma contDiff_kG2 : ContDiff ℝ ∞ kG2 := ((contDiff_F3.add contDiff_F4).div_const _).neg
lemma contDiff_kG4 : ContDiff ℝ ∞ kG4 := (contDiff_F3.add contDiff_F4).div_const _
lemma contDiff_kG6 : ContDiff ℝ ∞ kG6 := contDiff_F3.neg

lemma kG_glue (b : ℝ) :
    (b * kG1 b + (1 - b) * kG4 b = 1 / 2 ∧ b * kG2 b + (1 - b) * kG1 b = -(1 / 2) ∧
      b * F4 b + (1 - b) * kG6 b = 0) ∧
    ((b - 1) * kG1 b + b * kG4 b = 1 / 2 ∧ (b - 1) * kG2 b + b * kG1 b = 1 / 2 ∧
      (b - 1) * F4 b + b * kG6 b = -1) := by
  have hγ := (gam_pos' b).ne'
  simp only [kG1, kG2, kG4, kG6, F3, F4]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;> field_simp <;> ring

end Mults

end GWMemoir.Neck

namespace GWMemoir

open Neck (βa F3 F4 multβ IsCutoff shH reflH mulHL trH Van van_shH van_reflH)

/-! ## 2. Level compatibility of differences -/

section ValEqMore

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {q : Q} {A : SectionAtlas (E := E) twoSpheres (fun _ => q)}
  {δ : ℕ → ℝ} {h0 : 0 ≤ δ 0} {hmono : StrictMono δ}
variable {k l : ℕ} {d e : ℝ} {hd : 0 ≤ d} {he : 0 ≤ e} {n : ℕ}

lemma valEqF_neg {T : (fibreBlocks A δ h0 hmono) n →L[ℝ] H k hd}
    {T0 : (fibreBlocks A δ h0 hmono) 0 →L[ℝ] H l he} (h : ValEqF n T T0) :
    ValEqF n (-T) (-T0) := fun v => by
  rw [neg_apply, neg_apply, map_neg, map_neg, h v]

lemma valEqB_neg {T : (blocks A δ h0 hmono) n →L[ℝ] H k hd}
    {T0 : (blocks A δ h0 hmono) 0 →L[ℝ] H l he} (h : ValEqB n T T0) :
    ValEqB n (-T) (-T0) := fun v => by
  rw [neg_apply, neg_apply, map_neg, map_neg, h v]

lemma valEq_mulHW {χ : ℝ → ℝ} {d' e' : ℝ} {hd' : 0 ≤ d'} {he' : 0 ≤ e'}
    (h1 : Mult k χ) (h2 : Mult l χ) (hc : HasCompactSupport χ) :
    ValEq (mulHW (hδ := hd) (hδ' := hd') χ h1 hc) (mulHW (hδ := he) (hδ' := he') χ h2 hc) :=
  fun u u0 h => by
    rw [val_mulHW, val_mulHW, h]
    exact Lp.ext ((coeFn_mulχ χ h1 _).trans (coeFn_mulχ χ h2 _).symm)

end ValEqMore

/-! ## 3. The fibre side: `1 - π̂_a` on the node pair, `⊕̂_a`, `⊖̂_a` -/

section Fibre

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
variable {q : Q} {A : SectionAtlas (E := E) twoSpheres (fun _ => q)}
  (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ)
  {β : ℝ → ℝ} (hβ : IsCutoff β) (R ϑ : ℝ) (jx jy : Fin A.nn) (n : ℕ)

/-- The neck block `(j, k)` of the level-`n` fibre blocks. -/
def glFibNeck (jk : Fin A.nn × Fin (Module.finrank ℝ E)) :
    (fibreBlocks A δ h0 hmono) n →L[ℝ] H (2 + n) (Neck.δ_nonneg δ h0 hmono n) :=
  (ContinuousLinearMap.proj jk).comp (ContinuousLinearMap.snd ℝ _ _)

/-- `ξ⁺ = G_{jx,k}(s + s₀, t)`, in the memoir's coordinate on the glued cylinder. -/
def glP (k : Fin (Module.finrank ℝ E)) :
    (fibreBlocks A δ h0 hmono) n →L[ℝ] H (2 + n) (Neck.δ_nonneg δ h0 hmono n) :=
  (shH (-A.s0 jx) 0).comp (glFibNeck δ h0 hmono n (jx, k))

/-- `τξ⁻ = -G_{jy,k}(R + s₀ - s, ϑ - t)`. -/
def glN (k : Fin (Module.finrank ℝ E)) :
    (fibreBlocks A δ h0 hmono) n →L[ℝ] H (2 + n) (Neck.δ_nonneg δ h0 hmono n) :=
  -((reflH (R + A.s0 jy) ϑ).comp (glFibNeck δ h0 hmono n (jy, k)))

/-- The `+` component of `(1 - π̂_a)(ξ⁺, ξ⁻)`. -/
def glTP (k : Fin (Module.finrank ℝ E)) :
    (fibreBlocks A δ h0 hmono) n →L[ℝ] H (2 + n) (Neck.δ_nonneg δ h0 hmono n) :=
  (mulHL _ (multβ hβ R Neck.contDiff_hatG1 (2 + n))).comp (glP δ h0 hmono jx n k) +
    (mulHL _ (multβ hβ R Neck.contDiff_hatG2 (2 + n))).comp (glN δ h0 hmono R ϑ jy n k)

/-- The `τ(·)⁻` component of `(1 - π̂_a)(ξ⁺, ξ⁻)`. -/
def glTN (k : Fin (Module.finrank ℝ E)) :
    (fibreBlocks A δ h0 hmono) n →L[ℝ] H (2 + n) (Neck.δ_nonneg δ h0 hmono n) :=
  (mulHL _ (multβ hβ R Neck.contDiff_hatG3 (2 + n))).comp (glP δ h0 hmono jx n k) +
    (mulHL _ (multβ hβ R Neck.contDiff_hatG4 (2 + n))).comp (glN δ h0 hmono R ϑ jy n k)

/-- The neck block `(j, k)` of `1 - π̂_a`. -/
def glThetaBlk (jk : Fin A.nn × Fin (Module.finrank ℝ E)) :
    (fibreBlocks A δ h0 hmono) n →L[ℝ] H (2 + n) (Neck.δ_nonneg δ h0 hmono n) :=
  if jk.1 = jx then (shH (A.s0 jx) 0).comp (glTP δ h0 hmono hβ R ϑ jx jy n jk.2)
  else if jk.1 = jy then -((reflH (R + A.s0 jy) ϑ).comp (glTN δ h0 hmono hβ R ϑ jx jy n jk.2))
  else 0

/-- **`1 - π̂_a` on the node pair**, on the level-`n` fibre blocks: `0` on the disc blocks and
on the other necks; on the necks `jx`, `jy` the two components above, carried back to the
polar coordinates. -/
def glTheta : (fibreBlocks A δ h0 hmono) n →L[ℝ] (fibreBlocks A δ h0 hmono) n :=
  (0 : (fibreBlocks A δ h0 hmono) n →L[ℝ] _).prod
    (ContinuousLinearMap.pi fun jk => glThetaBlk δ h0 hmono hβ R ϑ jx jy n jk)

/-- `⊕̂_a(ξ⁺, ξ⁻) = β_a ξ⁺ + (1 - β_a) τξ⁻` (Memoir p. 51). -/
def glHat (k : Fin (Module.finrank ℝ E)) :
    (fibreBlocks A δ h0 hmono) n →L[ℝ] H (2 + n) (Neck.δ_nonneg δ h0 hmono n) :=
  (mulHL _ (Neck.m1 hβ R (2 + n))).comp (glP δ h0 hmono jx n k) +
    (mulHL _ (Neck.m2 hβ R (2 + n))).comp (glN δ h0 hmono R ϑ jy n k)

/-- `⊖̂_a(ξ⁺, ξ⁻) = -(1 - β_a) ξ⁺ + β_a τξ⁻` (Memoir p. 51). -/
def glAnti (k : Fin (Module.finrank ℝ E)) :
    (fibreBlocks A δ h0 hmono) n →L[ℝ] H (2 + n) (Neck.δ_nonneg δ h0 hmono n) :=
  (mulHL _ (Neck.m5 hβ R (2 + n))).comp (glP δ h0 hmono jx n k) +
    (mulHL _ (Neck.m1 hβ R (2 + n))).comp (glN δ h0 hmono R ϑ jy n k)

variable {δ h0 hmono hβ R ϑ jx jy n}

lemma glTheta_fst (y : (fibreBlocks A δ h0 hmono) n) :
    (glTheta δ h0 hmono hβ R ϑ jx jy n y).1 = 0 := rfl

lemma glTheta_x (y : (fibreBlocks A δ h0 hmono) n) (k : Fin (Module.finrank ℝ E)) :
    (glTheta δ h0 hmono hβ R ϑ jx jy n y).2 (jx, k) =
      shH (A.s0 jx) 0 (glTP δ h0 hmono hβ R ϑ jx jy n k y) := by
  change glThetaBlk δ h0 hmono hβ R ϑ jx jy n (jx, k) y = _
  rw [glThetaBlk, if_pos rfl]; rfl

lemma glTheta_y (hxy : jx ≠ jy) (y : (fibreBlocks A δ h0 hmono) n) (k : Fin (Module.finrank ℝ E)) :
    (glTheta δ h0 hmono hβ R ϑ jx jy n y).2 (jy, k) =
      -reflH (R + A.s0 jy) ϑ (glTN δ h0 hmono hβ R ϑ jx jy n k y) := by
  change glThetaBlk δ h0 hmono hβ R ϑ jx jy n (jy, k) y = _
  rw [glThetaBlk, if_neg (Ne.symm hxy), if_pos rfl]; rfl

lemma glTheta_other {j : Fin A.nn} (hx : j ≠ jx) (hy : j ≠ jy) (y : (fibreBlocks A δ h0 hmono) n)
    (k : Fin (Module.finrank ℝ E)) : (glTheta δ h0 hmono hβ R ϑ jx jy n y).2 (j, k) = 0 := by
  change glThetaBlk δ h0 hmono hβ R ϑ jx jy n (j, k) y = _
  rw [glThetaBlk, if_neg hx, if_neg hy]; rfl

lemma glP_theta (y : (fibreBlocks A δ h0 hmono) n) (k : Fin (Module.finrank ℝ E)) :
    glP δ h0 hmono jx n k (glTheta δ h0 hmono hβ R ϑ jx jy n y) =
      glTP δ h0 hmono hβ R ϑ jx jy n k y := by
  change shH (-A.s0 jx) 0 ((glTheta δ h0 hmono hβ R ϑ jx jy n y).2 (jx, k)) = _
  rw [glTheta_x]
  have := Neck.shH_shH (m := 2 + n) (hδ := Neck.δ_nonneg δ h0 hmono n) (A.s0 jx) 0
    (glTP δ h0 hmono hβ R ϑ jx jy n k y)
  rwa [neg_zero] at this

lemma glN_theta (hxy : jx ≠ jy) (y : (fibreBlocks A δ h0 hmono) n) (k : Fin (Module.finrank ℝ E)) :
    glN δ h0 hmono R ϑ jy n k (glTheta δ h0 hmono hβ R ϑ jx jy n y) =
      glTN δ h0 hmono hβ R ϑ jx jy n k y := by
  change -reflH (R + A.s0 jy) ϑ ((glTheta δ h0 hmono hβ R ϑ jx jy n y).2 (jy, k)) = _
  rw [glTheta_y hxy, map_neg, neg_neg, Neck.reflH_reflH]

/-- **`1 - π̂_a` is idempotent.** -/
theorem glTheta_idem (hxy : jx ≠ jy) (y : (fibreBlocks A δ h0 hmono) n) :
    glTheta δ h0 hmono hβ R ϑ jx jy n (glTheta δ h0 hmono hβ R ϑ jx jy n y) =
      glTheta δ h0 hmono hβ R ϑ jx jy n y := by
  have hP : ∀ k, glTP δ h0 hmono hβ R ϑ jx jy n k (glTheta δ h0 hmono hβ R ϑ jx jy n y) =
      glTP δ h0 hmono hβ R ϑ jx jy n k y := fun k => by
    change mulHL _ _ (glP δ h0 hmono jx n k _) + mulHL _ _ (glN δ h0 hmono R ϑ jy n k _) = _
    rw [glP_theta, glN_theta hxy]
    exact Neck.comb22 _ _ _ _ _ _ _ _ (fun s => (Neck.hatG_idem _).1.1)
      (fun s => (Neck.hatG_idem _).1.2) _ _
  have hN : ∀ k, glTN δ h0 hmono hβ R ϑ jx jy n k (glTheta δ h0 hmono hβ R ϑ jx jy n y) =
      glTN δ h0 hmono hβ R ϑ jx jy n k y := fun k => by
    change mulHL _ _ (glP δ h0 hmono jx n k _) + mulHL _ _ (glN δ h0 hmono R ϑ jy n k _) = _
    rw [glP_theta, glN_theta hxy]
    exact Neck.comb22 _ _ _ _ _ _ _ _ (fun s => (Neck.hatG_idem _).2.1)
      (fun s => (Neck.hatG_idem _).2.2) _ _
  refine Prod.ext rfl (funext fun ⟨j, k⟩ => ?_)
  by_cases hx : j = jx
  · subst hx
    rw [glTheta_x, glTheta_x, hP]
  by_cases hy : j = jy
  · subst hy
    rw [glTheta_y hxy, glTheta_y hxy, hN]
  · rw [glTheta_other hx hy, glTheta_other hx hy]

/-! ### Along the inclusions, and the far part -/

lemma valEqF_glFibNeck (jk : Fin A.nn × Fin (Module.finrank ℝ E)) :
    ValEqF n (glFibNeck δ h0 hmono n jk) (glFibNeck δ h0 hmono 0 jk) :=
  fun v => (val_fibreNeck_toBase δ h0 hmono n v jk).symm

lemma valEqF_glTP (k : Fin (Module.finrank ℝ E)) :
    ValEqF n (glTP δ h0 hmono hβ R ϑ jx jy n k) (glTP δ h0 hmono hβ R ϑ jx jy 0 k) :=
  ((valEq_mulHL _ _).compF ((valEq_shH _ _).compF (valEqF_glFibNeck _))).add
    ((valEq_mulHL _ _).compF (valEqF_neg ((valEq_reflH _ _).compF (valEqF_glFibNeck _))))

lemma valEqF_glTN (k : Fin (Module.finrank ℝ E)) :
    ValEqF n (glTN δ h0 hmono hβ R ϑ jx jy n k) (glTN δ h0 hmono hβ R ϑ jx jy 0 k) :=
  ((valEq_mulHL _ _).compF ((valEq_shH _ _).compF (valEqF_glFibNeck _))).add
    ((valEq_mulHL _ _).compF (valEqF_neg ((valEq_reflH _ _).compF (valEqF_glFibNeck _))))

/-- `1 - π̂_a` on level `n` agrees with level `0` along the inclusions. -/
theorem toBase_glTheta (hxy : jx ≠ jy) (y : (fibreBlocks A δ h0 hmono) n) :
    (fibreBlocks A δ h0 hmono).toBase n (glTheta δ h0 hmono hβ R ϑ jx jy n y) =
      glTheta δ h0 hmono hβ R ϑ jx jy 0 ((fibreBlocks A δ h0 hmono).toBase n y) := by
  refine fibre_ext_val δ h0 hmono (fun o => ?_) (fun ⟨j, k⟩ => ?_)
  · rw [fibre_toBase_fst]
    exact (map_zero (valCLM (2 + n) (Neck.δ_nonneg δ h0 hmono n))).trans
      (map_zero (valCLM 2 (Neck.δ_nonneg δ h0 hmono 0))).symm
  rw [val_fibreNeck_toBase]
  by_cases hx : j = jx
  · subst hx
    rw [glTheta_x, glTheta_x]
    exact valEq_shH _ _ _ _ (valEqF_glTP k y)
  by_cases hy : j = jy
  · subst hy
    rw [glTheta_y hxy, glTheta_y hxy]
    exact (valEqF_neg ((valEq_reflH _ _).compF (valEqF_glTN k))) y
  · rw [glTheta_other hx hy, glTheta_other hx hy]
    exact (map_zero (valCLM (2 + n) (Neck.δ_nonneg δ h0 hmono n))).trans
      (map_zero (valCLM 2 (Neck.δ_nonneg δ h0 hmono 0))).symm

lemma van_glTP (y : (fibreBlocks A δ h0 hmono) n) (k : Fin (Module.finrank ℝ E)) :
    Van (Iic (R / 2 - 1)) (valCLM _ _ (glTP δ h0 hmono hβ R ϑ jx jy n k y)) :=
  Neck.van_of_ae (Neck.val_mulHL_add _ _ (glP δ h0 hmono jx n k y) (glN δ h0 hmono R ϑ jy n k y))
    fun x hx => by
      simp only [Neck.hatG1, Neck.hatG2, Neck.βa_one hβ (show x.1 ≤ R / 2 - 1 from hx),
        Neck.F4_one]
      ring

lemma van_glTN (y : (fibreBlocks A δ h0 hmono) n) (k : Fin (Module.finrank ℝ E)) :
    Van (Ici (R / 2 + 1)) (valCLM _ _ (glTN δ h0 hmono hβ R ϑ jx jy n k y)) :=
  Neck.van_of_ae (Neck.val_mulHL_add _ _ (glP δ h0 hmono jx n k y) (glN δ h0 hmono R ϑ jy n k y))
    fun x hx => by
      simp only [Neck.hatG3, Neck.hatG4, Neck.βa_zero hβ (show R / 2 + 1 ≤ x.1 from hx),
        Neck.F3_zero]
      ring

/-- **`1 - π̂_a` is carried by the far part of the necks**: `(ξ⁺)` vanishes on `s ≤ R/2 - 1` and
`(τξ⁻)` on `s ≥ R/2 + 1`. -/
theorem isFar_glTheta (hxy : jx ≠ jy) {σ : ℝ} (hσ : ∀ j, σ + 2 < R / 2 + A.s0 j)
    (y : (fibreBlocks A δ h0 hmono) 0) : IsFar σ (glTheta δ h0 hmono hβ R ϑ jx jy 0 y) := by
  refine ⟨rfl, fun ⟨j, k⟩ => ?_⟩
  by_cases hx : j = jx
  · subst hx
    rw [glTheta_x]
    exact van_shH (van_glTP y k) _ 0 fun s hs => by
      simp only [mem_Iic] at hs ⊢; linarith [hσ j]
  by_cases hy : j = jy
  · subst hy
    rw [glTheta_y hxy]
    change Van _ (valCLM _ _ (-_))
    rw [map_neg]
    exact Neck.van_neg (van_reflH (van_glTN y k) _ _ fun s hs => by
      simp only [mem_Iic] at hs; simp only [mem_Ici]; linarith [hσ j])
  · rw [glTheta_other hx hy]
    change Van _ (valCLM (2 + 0) (Neck.δ_nonneg δ h0 hmono 0) 0)
    rw [map_zero]
    exact Neck.van_zero _

/-! ### `⊕̂_a` and `⊖̂_a` after `1 + (1 - π̂_a)` -/

/-- `⊕̂_a ∘ (1 - π̂_a) = 0`. -/
theorem glHat_theta (hxy : jx ≠ jy) (y : (fibreBlocks A δ h0 hmono) n)
    (k : Fin (Module.finrank ℝ E)) :
    glHat δ h0 hmono hβ R ϑ jx jy n k (glTheta δ h0 hmono hβ R ϑ jx jy n y) = 0 := by
  change mulHL _ _ (glP δ h0 hmono jx n k _) + mulHL _ _ (glN δ h0 hmono R ϑ jy n k _) = _
  rw [glP_theta, glN_theta hxy]
  apply valCLM_injective
  apply Lp.ext
  filter_upwards [Neck.val_mulHL_add (Neck.m1 hβ R (2 + n)) (Neck.m2 hβ R (2 + n))
      (glTP δ h0 hmono hβ R ϑ jx jy n k y) (glTN δ h0 hmono hβ R ϑ jx jy n k y),
    Neck.val_mulHL_add _ _ (glP δ h0 hmono jx n k y) (glN δ h0 hmono R ϑ jy n k y),
    Neck.val_mulHL_add (multβ hβ R Neck.contDiff_hatG3 (2 + n))
      (multβ hβ R Neck.contDiff_hatG4 (2 + n)) (glP δ h0 hmono jx n k y)
      (glN δ h0 hmono R ϑ jy n k y),
    Lp.coeFn_zero ℝ 2 cyl] with x h1 h2 h3 h4
  rw [map_zero, h4, h1]
  change _ = (0 : ℝ)
  have e := (Neck.hatG_glue (βa β R x.1)).1
  rw [show (valCLM _ _ (glTP δ h0 hmono hβ R ϑ jx jy n k y) : ℝ × ℝ → ℝ) x = _ from h2,
    show (valCLM _ _ (glTN δ h0 hmono hβ R ϑ jx jy n k y) : ℝ × ℝ → ℝ) x = _ from h3]
  linear_combination (valCLM _ _ (glP δ h0 hmono jx n k y) x) * e.1 +
    (valCLM _ _ (glN δ h0 hmono R ϑ jy n k y) x) * e.2

/-- `⊖̂_a ∘ (1 - π̂_a) = ⊖̂_a`. -/
theorem glAnti_theta (hxy : jx ≠ jy) (y : (fibreBlocks A δ h0 hmono) n)
    (k : Fin (Module.finrank ℝ E)) :
    glAnti δ h0 hmono hβ R ϑ jx jy n k (glTheta δ h0 hmono hβ R ϑ jx jy n y) =
      glAnti δ h0 hmono hβ R ϑ jx jy n k y := by
  change mulHL _ _ (glP δ h0 hmono jx n k _) + mulHL _ _ (glN δ h0 hmono R ϑ jy n k _) = _
  rw [glP_theta, glN_theta hxy]
  exact Neck.comb22 _ _ _ _ _ _ _ _ (fun s => (Neck.hatG_glue _).2.1)
    (fun s => (Neck.hatG_glue _).2.2) _ _

/-- With `S = 1 + (1 - π̂_a)`: `⊕̂_a S = ⊕̂_a`. -/
theorem glHat_add_theta (hxy : jx ≠ jy) (y : (fibreBlocks A δ h0 hmono) n)
    (k : Fin (Module.finrank ℝ E)) :
    glHat δ h0 hmono hβ R ϑ jx jy n k (y + glTheta δ h0 hmono hβ R ϑ jx jy n y) =
      glHat δ h0 hmono hβ R ϑ jx jy n k y := by
  rw [map_add, glHat_theta hxy, add_zero]

/-- With `S = 1 + (1 - π̂_a)`: `⊖̂_a S = 2 ⊖̂_a`. -/
theorem glAnti_add_theta (hxy : jx ≠ jy) (y : (fibreBlocks A δ h0 hmono) n)
    (k : Fin (Module.finrank ℝ E)) :
    glAnti δ h0 hmono hβ R ϑ jx jy n k (y + glTheta δ h0 hmono hβ R ϑ jx jy n y) =
      (2 : ℝ) • glAnti δ h0 hmono hβ R ϑ jx jy n k y := by
  rw [map_add, glAnti_theta hxy, two_smul]

end Fibre

end GWMemoir
