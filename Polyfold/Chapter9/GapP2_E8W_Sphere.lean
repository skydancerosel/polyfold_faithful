import Polyfold.Chapter3.NonVacuityCorner

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, Theorems 9.5.17 and 9.5.18 (Stokes), the witness of their hypotheses:
the analytic part.  Numbers and pages are the 2021 text's.

# The unit sphere of `ℝ³ = ℝ × ℝ²` and the radial retraction

On `V = ℝ × ℝ²` (the model space `ℝ ⊕ ℝ²` of the half-space `[0, ∞) × ℝ²`):

* `inner3`, `nsq` (`|v|²`), `ell a` (`v ↦ ⟨a, v⟩` as a continuous linear form);
* the radial retraction `rho v = v / |v|` (`C^∞` on `v ≠ 0`, `contDiffOn_rho`), which maps the
  half-space into itself and the punctured space onto the unit sphere;
* its derivative at `|a| = 1`: `h ↦ h − ⟨a, h⟩ a` (`hasFDerivAt_rho`), an idempotent with range
  `ker ⟨a, ·⟩` (`range_rhoDeriv`) and kernel `ℝa` (`ker_rhoDeriv`); `finrank ker ⟨a, ·⟩ = 2`;
* the tangent frame `frameVec a i = eᵢ − aᵢ/(1+t) (a + e_t)` (`i = x, y`, `a = (t, x, y)`) of
  the sphere at `a` with `t > −1` (the image of `e_x, e_y` under the rotation taking `e_t` to
  `a`): tangent (`ell_frameVec`), linearly independent (`linearIndependent_frameVec`),
  continuous (`continuousOn_frameVec`).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology Module Submodule
open scoped ContDiff

noncomputable section

namespace Polyfold

namespace E8W

/-- The model space `ℝ × ℝ²`. -/
abbrev V3 : Type := (Fin 1 → ℝ) × (Fin 2 → ℝ)

/-- The first coordinate `t`. -/
def ct : V3 →L[ℝ] ℝ := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).comp
  (ContinuousLinearMap.fst ℝ _ _)

/-- The second coordinate `x`. -/
def cx : V3 →L[ℝ] ℝ := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).comp
  (ContinuousLinearMap.snd ℝ _ _)

/-- The third coordinate `y`. -/
def cy : V3 →L[ℝ] ℝ := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).comp
  (ContinuousLinearMap.snd ℝ _ _)

@[simp] theorem ct_apply (v : V3) : ct v = v.1 0 := rfl
@[simp] theorem cx_apply (v : V3) : cx v = v.2 0 := rfl
@[simp] theorem cy_apply (v : V3) : cy v = v.2 1 := rfl

/-- A vector of `ℝ × ℝ²` is determined by its three coordinates. -/
theorem ext3 {v w : V3} (h0 : v.1 0 = w.1 0) (h1 : v.2 0 = w.2 0) (h2 : v.2 1 = w.2 1) :
    v = w :=
  Prod.ext (funext fun i => by rw [Subsingleton.elim i 0]; exact h0)
    (funext fun i => by fin_cases i; exacts [h1, h2])

/-- The vector `(t, x, y)`. -/
def mk3 (t x y : ℝ) : V3 := (fun _ => t, ![x, y])

@[simp] theorem mk3_fst (t x y : ℝ) : (mk3 t x y).1 0 = t := rfl
@[simp] theorem mk3_snd0 (t x y : ℝ) : (mk3 t x y).2 0 = x := rfl
@[simp] theorem mk3_snd1 (t x y : ℝ) : (mk3 t x y).2 1 = y := rfl

/-- The standard inner product `⟨v, w⟩`. -/
def inner3 (v w : V3) : ℝ := v.1 0 * w.1 0 + v.2 0 * w.2 0 + v.2 1 * w.2 1

/-- `|v|² = ⟨v, v⟩`. -/
def nsq (v : V3) : ℝ := inner3 v v

theorem nsq_eq (v : V3) : nsq v = v.1 0 ^ 2 + v.2 0 ^ 2 + v.2 1 ^ 2 := by
  simp only [nsq, inner3]; ring

theorem nsq_nonneg (v : V3) : 0 ≤ nsq v := by
  rw [nsq_eq]; positivity

theorem continuous_nsq : Continuous nsq := by
  have : nsq = fun v : V3 => ct v ^ 2 + cx v ^ 2 + cy v ^ 2 := funext nsq_eq
  rw [this]; fun_prop

/-- The linear form `⟨a, ·⟩`. -/
def ell (a : V3) : V3 →L[ℝ] ℝ := a.1 0 • ct + a.2 0 • cx + a.2 1 • cy

@[simp] theorem ell_apply (a v : V3) : ell a v = inner3 a v := by
  simp [ell, inner3]

/-- The unit sphere `{|v| = 1}`. -/
def sphere3 : Set V3 := {v | nsq v = 1}

/-- The punctured space `{v ≠ 0}`, as `{0 < |v|²}`. -/
def punct3 : Set V3 := {v | 0 < nsq v}

theorem isOpen_punct3 : IsOpen punct3 := isOpen_lt continuous_const continuous_nsq

theorem isClosed_sphere3 : IsClosed sphere3 := isClosed_eq continuous_nsq continuous_const

theorem sphere3_subset_punct3 : sphere3 ⊆ punct3 := fun v hv => by
  change 0 < nsq v; rw [show nsq v = 1 from hv]; exact one_pos

/-- The radial retraction `v ↦ v / |v|`. -/
def rho (v : V3) : V3 := (√(nsq v))⁻¹ • v

theorem nsq_smul (c : ℝ) (v : V3) : nsq (c • v) = c ^ 2 * nsq v := by
  simp only [nsq_eq, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]; ring

theorem rho_mem_sphere3 {v : V3} (hv : v ∈ punct3) : rho v ∈ sphere3 := by
  have hq : 0 < nsq v := hv
  change nsq ((√(nsq v))⁻¹ • v) = 1
  rw [nsq_smul, inv_pow, Real.sq_sqrt hq.le, inv_mul_cancel₀ hq.ne']

theorem rho_eq_self {v : V3} (hv : v ∈ sphere3) : rho v = v := by
  have hq : nsq v = 1 := hv
  simp only [rho, hq, Real.sqrt_one, inv_one, one_smul]

theorem rho_idem {v : V3} (hv : v ∈ punct3) : rho (rho v) = rho v :=
  rho_eq_self (rho_mem_sphere3 hv)

theorem rho_image : rho '' punct3 = sphere3 := by
  refine Subset.antisymm ?_ fun v hv => ⟨v, sphere3_subset_punct3 hv, rho_eq_self hv⟩
  rintro _ ⟨v, hv, rfl⟩
  exact rho_mem_sphere3 hv

/-- `rho v` is a nonnegative multiple of `v`. -/
theorem rho_fst (v : V3) : (rho v).1 0 = (√(nsq v))⁻¹ * v.1 0 := rfl

theorem inv_sqrt_pos {v : V3} (hv : v ∈ punct3) : 0 < (√(nsq v))⁻¹ :=
  inv_pos.2 (Real.sqrt_pos.2 hv)

theorem contDiffOn_rho : ContDiffOn ℝ ∞ rho punct3 := by
  intro v hv
  have hq : nsq v ≠ 0 := (show 0 < nsq v from hv).ne'
  have h1 : ContDiffAt ℝ ∞ nsq v := by
    have : nsq = fun v : V3 => ct v ^ 2 + cx v ^ 2 + cy v ^ 2 := funext nsq_eq
    rw [this]; fun_prop
  have h2 : ContDiffAt ℝ ∞ (fun v => √(nsq v)) v := h1.sqrt hq
  have h3 : ContDiffAt ℝ ∞ (fun v => (√(nsq v))⁻¹) v :=
    h2.inv (Real.sqrt_ne_zero'.2 (show 0 < nsq v from hv))
  exact (h3.smul contDiffAt_id).contDiffWithinAt

/-- The derivative of `rho` at `|a| = 1`: `h ↦ h − ⟨a, h⟩ a`. -/
def rhoDeriv (a : V3) : V3 →L[ℝ] V3 := ContinuousLinearMap.id ℝ V3 - (ell a).smulRight a

@[simp] theorem rhoDeriv_apply (a h : V3) : rhoDeriv a h = h - inner3 a h • a := by
  simp [rhoDeriv]

theorem hasFDerivAt_nsq (a : V3) : HasFDerivAt nsq ((2 : ℝ) • ell a) a := by
  have e : nsq = fun v : V3 => ct v ^ 2 + cx v ^ 2 + cy v ^ 2 := funext nsq_eq
  rw [e]
  have h := (((ct.hasFDerivAt (x := a)).pow 2).add ((cx.hasFDerivAt (x := a)).pow 2)).add
    ((cy.hasFDerivAt (x := a)).pow 2)
  refine h.congr_fderiv ?_
  ext h <;> simp [ell] <;> ring

theorem hasFDerivAt_rho {a : V3} (ha : a ∈ sphere3) : HasFDerivAt rho (rhoDeriv a) a := by
  have hq : nsq a = 1 := ha
  have hS := (hasFDerivAt_nsq a).sqrt (by simp [hq])
  have hI := (hasDerivAt_inv (by simp [hq])).comp_hasFDerivAt a hS
  have hR := hI.smul (hasFDerivAt_id a)
  refine hR.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun h => ?_
  have e1 : √(nsq a) = 1 := by rw [hq, Real.sqrt_one]
  refine ext3 ?_ ?_ ?_ <;> simp [e1, inner3] <;> ring

theorem inner3_self_of_mem {a : V3} (ha : a ∈ sphere3) : inner3 a a = 1 := ha

theorem inner3_sub_smul (a h : V3) (c : ℝ) :
    inner3 a (h - c • a) = inner3 a h - c * inner3 a a := by
  simp only [inner3, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

theorem inner3_rhoDeriv {a : V3} (ha : a ∈ sphere3) (h : V3) : inner3 a (rhoDeriv a h) = 0 := by
  rw [rhoDeriv_apply, inner3_sub_smul, inner3_self_of_mem ha, mul_one, sub_self]

theorem rhoDeriv_idem {a : V3} (ha : a ∈ sphere3) (h : V3) :
    rhoDeriv a (rhoDeriv a h) = rhoDeriv a h := by
  conv_lhs => rw [rhoDeriv_apply, inner3_rhoDeriv ha h, zero_smul, sub_zero]

/-- The range of the derivative at `|a| = 1` is `a^⊥ = ker ⟨a, ·⟩`. -/
theorem range_rhoDeriv {a : V3} (ha : a ∈ sphere3) :
    LinearMap.range (rhoDeriv a : V3 →ₗ[ℝ] V3) = LinearMap.ker (ell a : V3 →ₗ[ℝ] ℝ) := by
  ext v
  simp only [LinearMap.mem_range, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ell_apply]
  constructor
  · rintro ⟨h, rfl⟩; exact inner3_rhoDeriv ha h
  · intro hv
    exact ⟨v, by rw [rhoDeriv_apply, hv, zero_smul, sub_zero]⟩

/-- The kernel of the derivative at `|a| = 1` is `ℝa`. -/
theorem ker_rhoDeriv {a v : V3} (hv : rhoDeriv a v = 0) :
    v = inner3 a v • a := by
  rw [rhoDeriv_apply, sub_eq_zero] at hv; exact hv

theorem finrank_V3 : finrank ℝ V3 = 3 := by
  rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun]

/-- `dim a^⊥ = 2` for `a ≠ 0`. -/
theorem finrank_ker_ell {a : V3} (ha : a ∈ sphere3) :
    finrank ℝ (LinearMap.ker (ell a : V3 →ₗ[ℝ] ℝ)) = 2 := by
  have hq : inner3 a a = 1 := ha
  have hsurj : LinearMap.range (ell a : V3 →ₗ[ℝ] ℝ) = ⊤ := by
    refine eq_top_iff.2 fun c _ => ⟨c • a, ?_⟩
    simp only [ContinuousLinearMap.coe_coe, map_smul, ell_apply, hq, smul_eq_mul, mul_one]
  have h := LinearMap.finrank_range_add_finrank_ker (ell a : V3 →ₗ[ℝ] ℝ)
  rw [hsurj, finrank_top, Module.finrank_self, finrank_V3] at h
  omega

/-! ### A tangent frame of the sphere on `t > −1` -/

/-- `e_x` (`i = 0`) and `e_y` (`i = 1`). -/
def eVec (i : Fin 2) : V3 := (0, Pi.single i 1)

/-- The frame `frameVec a i = eᵢ − aᵢ/(1+t) (a + e_t)` at `a = (t, x, y)`. -/
def frameVec (a : V3) (i : Fin 2) : V3 :=
  eVec i - (a.2 i / (1 + a.1 0)) • (a + mk3 1 0 0)

theorem ell_frameVec {a : V3} (ha : a ∈ sphere3) (ht : 0 < 1 + a.1 0) (i : Fin 2) :
    inner3 a (frameVec a i) = 0 := by
  have hq : a.1 0 ^ 2 + a.2 0 ^ 2 + a.2 1 ^ 2 = 1 := by rw [← nsq_eq]; exact ha
  have hne : (1 + a.1 0) ≠ 0 := ht.ne'
  fin_cases i <;>
  · simp only [inner3, frameVec, eVec, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_add, Prod.snd_add, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
      Pi.zero_apply, mk3, Pi.single_apply]
    simp
    field_simp
    linear_combination (-(a.2 _)) * hq

theorem linearIndependent_frameVec {a : V3} (ht : 0 < 1 + a.1 0) :
    LinearIndependent ℝ (frameVec a) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hne : (1 + a.1 0) ≠ 0 := ht.ne'
  have h0 := congrArg (fun v : V3 => v.1 0) hc
  have h1 := congrArg (fun v : V3 => v.2 0) hc
  have h2 := congrArg (fun v : V3 => v.2 1) hc
  simp only [Fin.sum_univ_two, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, Prod.snd_zero, Pi.zero_apply,
    frameVec, eVec, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, mk3, Pi.single_apply] at h0 h1 h2
  simp at h0 h1 h2
  field_simp at h0 h1 h2
  -- `h0`: `c₀ x + c₁ y = 0`; then `h1`, `h2` give `c₀ = c₁ = 0`
  have hs : c 0 * a.2 0 + c 1 * a.2 1 = 0 := by
    have := h0
    nlinarith [this]
  have e0 : c 0 * (1 + a.1 0) = 0 := by linear_combination h1 + a.2 0 * hs
  have e1 : c 1 * (1 + a.1 0) = 0 := by linear_combination h2 + a.2 1 * hs
  intro i
  fin_cases i
  · exact (mul_eq_zero.1 e0).resolve_right hne
  · exact (mul_eq_zero.1 e1).resolve_right hne

theorem continuousOn_frameVec (i : Fin 2) :
    ContinuousOn (fun a : V3 => frameVec a i) {a | 0 < 1 + a.1 0} := by
  have hd : ContinuousOn (fun a : V3 => a.2 i / (1 + a.1 0)) {a | 0 < 1 + a.1 0} :=
    ContinuousOn.div (by fun_prop) (by fun_prop) fun a ha => (show 0 < 1 + a.1 0 from ha).ne'
  exact continuousOn_const.sub (hd.smul (continuous_id.add continuous_const).continuousOn)

end E8W

end Polyfold
