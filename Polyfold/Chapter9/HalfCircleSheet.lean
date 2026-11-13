import Polyfold.Chapter9.HemisphereSheet

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, Theorems 9.5.17 and 9.5.18 (Stokes) for `n = 1`, gap G.110: the sheet
of a witness with boundary.  Numbers and pages are the 2021 text's.

# The closed right half-circle as a tame `1`-dimensional submanifold of `[0, ∞) × ℝ`

This is E8W's hemisphere one dimension lower.  `X = [0, ∞) × ℝ` is the M-polyfold
`quadrantPolyfold 1 ℝ` (`Pa`), with boundary `{t = 0}`.  The half-circle
`arc = {p ∈ X | |p| = 1}` is compact, and:

* it is a smooth submanifold (Definition 4.2.1): the image of the sc⁺-retraction `p ↦ p / |p|`
  of `X ∖ {0}` (`arcData`); in the chart `id` its tangent space at `a` is `a^⊥`
  (`tangentSpace_arc`), so it is `1`-dimensional (`isSubmanifoldOfDim_arc`);
* it is a tame sub-M-polyfold (2021 Definition 2.5.19, `isTameSubMPolyfold_arc`): the retraction
  keeps `d_X`, and `ℝa ⊆ T^R_aX` is an sc-complement of `T_a arc = a^⊥`;
* its boundary stratum `∂₁ arc = {d = 1}` is the pair of end points `{t = 0} = {(0, ±1)}`
  (`boundaryStratum_arc`).

The frame `f(a) = e_x − x/(1+t) (a + e_t)` (`frameVec`) is E8W's, and equals `(−x, t)` on the
circle.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology Module Submodule
open scoped ContDiff

noncomputable section

namespace Polyfold

open MPolyfold

namespace K2Arc

/-! ### The plane `ℝ × ℝ` and the radial retraction -/

/-- The model space `ℝ × ℝ`. -/
abbrev V2 : Type := (Fin 1 → ℝ) × (Fin 1 → ℝ)

/-- The first coordinate `t`. -/
def ct : V2 →L[ℝ] ℝ := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).comp
  (ContinuousLinearMap.fst ℝ _ _)

/-- The second coordinate `x`. -/
def cx : V2 →L[ℝ] ℝ := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).comp
  (ContinuousLinearMap.snd ℝ _ _)

@[simp] theorem ct_apply (v : V2) : ct v = v.1 0 := rfl
@[simp] theorem cx_apply (v : V2) : cx v = v.2 0 := rfl

/-- A vector of `ℝ × ℝ` is determined by its two coordinates. -/
theorem ext2 {v w : V2} (h0 : v.1 0 = w.1 0) (h1 : v.2 0 = w.2 0) : v = w :=
  Prod.ext (funext fun i => by rw [Subsingleton.elim i 0]; exact h0)
    (funext fun i => by rw [Subsingleton.elim i 0]; exact h1)

/-- The vector `(t, x)`. -/
def mk2 (t x : ℝ) : V2 := (fun _ => t, fun _ => x)

@[simp] theorem mk2_fst (t x : ℝ) : (mk2 t x).1 0 = t := rfl
@[simp] theorem mk2_snd (t x : ℝ) : (mk2 t x).2 0 = x := rfl

/-- The standard inner product `⟨v, w⟩`. -/
def inner2 (v w : V2) : ℝ := v.1 0 * w.1 0 + v.2 0 * w.2 0

/-- `|v|² = ⟨v, v⟩`. -/
def nsq (v : V2) : ℝ := inner2 v v

theorem nsq_eq (v : V2) : nsq v = v.1 0 ^ 2 + v.2 0 ^ 2 := by
  simp only [nsq, inner2]; ring

theorem continuous_nsq : Continuous nsq := by
  have : nsq = fun v : V2 => ct v ^ 2 + cx v ^ 2 := funext nsq_eq
  rw [this]; fun_prop

/-- The linear form `⟨a, ·⟩`. -/
def ell (a : V2) : V2 →L[ℝ] ℝ := a.1 0 • ct + a.2 0 • cx

@[simp] theorem ell_apply (a v : V2) : ell a v = inner2 a v := by
  simp [ell, inner2]

/-- The unit circle `{|v| = 1}`. -/
def circle2 : Set V2 := {v | nsq v = 1}

/-- The punctured plane `{0 < |v|²}`. -/
def punct2 : Set V2 := {v | 0 < nsq v}

theorem isOpen_punct2 : IsOpen punct2 := isOpen_lt continuous_const continuous_nsq

theorem isClosed_circle2 : IsClosed circle2 := isClosed_eq continuous_nsq continuous_const

theorem circle2_subset_punct2 : circle2 ⊆ punct2 := fun v hv => by
  change 0 < nsq v; rw [show nsq v = 1 from hv]; exact one_pos

/-- The radial retraction `v ↦ v / |v|`. -/
def rho (v : V2) : V2 := (√(nsq v))⁻¹ • v

theorem nsq_smul (c : ℝ) (v : V2) : nsq (c • v) = c ^ 2 * nsq v := by
  simp only [nsq_eq, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]; ring

theorem rho_mem_circle2 {v : V2} (hv : v ∈ punct2) : rho v ∈ circle2 := by
  have hq : 0 < nsq v := hv
  change nsq ((√(nsq v))⁻¹ • v) = 1
  rw [nsq_smul, inv_pow, Real.sq_sqrt hq.le, inv_mul_cancel₀ hq.ne']

theorem rho_eq_self {v : V2} (hv : v ∈ circle2) : rho v = v := by
  have hq : nsq v = 1 := hv
  simp only [rho, hq, Real.sqrt_one, inv_one, one_smul]

theorem rho_idem {v : V2} (hv : v ∈ punct2) : rho (rho v) = rho v :=
  rho_eq_self (rho_mem_circle2 hv)

theorem inv_sqrt_pos {v : V2} (hv : v ∈ punct2) : 0 < (√(nsq v))⁻¹ :=
  inv_pos.2 (Real.sqrt_pos.2 hv)

theorem contDiffOn_rho : ContDiffOn ℝ ∞ rho punct2 := by
  intro v hv
  have hq : nsq v ≠ 0 := (show 0 < nsq v from hv).ne'
  have h1 : ContDiffAt ℝ ∞ nsq v := by
    have : nsq = fun v : V2 => ct v ^ 2 + cx v ^ 2 := funext nsq_eq
    rw [this]; fun_prop
  have h2 : ContDiffAt ℝ ∞ (fun v => √(nsq v)) v := h1.sqrt hq
  have h3 : ContDiffAt ℝ ∞ (fun v => (√(nsq v))⁻¹) v :=
    h2.inv (Real.sqrt_ne_zero'.2 (show 0 < nsq v from hv))
  exact (h3.smul contDiffAt_id).contDiffWithinAt

/-- The derivative of `rho` at `|a| = 1`: `h ↦ h − ⟨a, h⟩ a`. -/
def rhoDeriv (a : V2) : V2 →L[ℝ] V2 := ContinuousLinearMap.id ℝ V2 - (ell a).smulRight a

@[simp] theorem rhoDeriv_apply (a h : V2) : rhoDeriv a h = h - inner2 a h • a := by
  simp [rhoDeriv]

theorem hasFDerivAt_nsq (a : V2) : HasFDerivAt nsq ((2 : ℝ) • ell a) a := by
  have e : nsq = fun v : V2 => ct v ^ 2 + cx v ^ 2 := funext nsq_eq
  rw [e]
  have h := ((ct.hasFDerivAt (x := a)).pow 2).add ((cx.hasFDerivAt (x := a)).pow 2)
  refine h.congr_fderiv ?_
  ext h <;> simp [ell] <;> ring

theorem hasFDerivAt_rho {a : V2} (ha : a ∈ circle2) : HasFDerivAt rho (rhoDeriv a) a := by
  have hq : nsq a = 1 := ha
  have hS := (hasFDerivAt_nsq a).sqrt (by simp [hq])
  have hI := (hasDerivAt_inv (by simp [hq])).comp_hasFDerivAt a hS
  have hR := hI.smul (hasFDerivAt_id a)
  refine hR.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun h => ?_
  have e1 : √(nsq a) = 1 := by rw [hq, Real.sqrt_one]
  refine ext2 ?_ ?_ <;> simp [e1, inner2] <;> ring

theorem inner2_sub_smul (a h : V2) (c : ℝ) :
    inner2 a (h - c • a) = inner2 a h - c * inner2 a a := by
  simp only [inner2, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

theorem inner2_rhoDeriv {a : V2} (ha : a ∈ circle2) (h : V2) : inner2 a (rhoDeriv a h) = 0 := by
  rw [rhoDeriv_apply, inner2_sub_smul, show inner2 a a = 1 from ha, mul_one, sub_self]

theorem rhoDeriv_idem {a : V2} (ha : a ∈ circle2) (h : V2) :
    rhoDeriv a (rhoDeriv a h) = rhoDeriv a h := by
  conv_lhs => rw [rhoDeriv_apply, inner2_rhoDeriv ha h, zero_smul, sub_zero]

/-- The range of the derivative at `|a| = 1` is `a^⊥ = ker ⟨a, ·⟩`. -/
theorem range_rhoDeriv {a : V2} (ha : a ∈ circle2) :
    LinearMap.range (rhoDeriv a : V2 →ₗ[ℝ] V2) = LinearMap.ker (ell a : V2 →ₗ[ℝ] ℝ) := by
  ext v
  simp only [LinearMap.mem_range, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ell_apply]
  constructor
  · rintro ⟨h, rfl⟩; exact inner2_rhoDeriv ha h
  · intro hv
    exact ⟨v, by rw [rhoDeriv_apply, hv, zero_smul, sub_zero]⟩

/-- The kernel of the derivative at `|a| = 1` is `ℝa`. -/
theorem ker_rhoDeriv {a v : V2} (hv : rhoDeriv a v = 0) : v = inner2 a v • a := by
  rw [rhoDeriv_apply, sub_eq_zero] at hv; exact hv

theorem finrank_V2 : finrank ℝ V2 = 2 := by
  rw [Module.finrank_prod, Module.finrank_fin_fun]

/-- `dim a^⊥ = 1` for `|a| = 1`. -/
theorem finrank_ker_ell {a : V2} (ha : a ∈ circle2) :
    finrank ℝ (LinearMap.ker (ell a : V2 →ₗ[ℝ] ℝ)) = 1 := by
  have hq : inner2 a a = 1 := ha
  have hsurj : LinearMap.range (ell a : V2 →ₗ[ℝ] ℝ) = ⊤ := by
    refine eq_top_iff.2 fun c _ => ⟨c • a, ?_⟩
    simp only [ContinuousLinearMap.coe_coe, map_smul, ell_apply, hq, smul_eq_mul, mul_one]
  have h := LinearMap.finrank_range_add_finrank_ker (ell a : V2 →ₗ[ℝ] ℝ)
  rw [hsurj, finrank_top, Module.finrank_self, finrank_V2] at h
  omega

/-! ### A tangent frame of the circle on `t > −1` -/

/-- The frame `f(a) = e_x − x/(1+t) (a + e_t) = (−x, 1 − x²/(1+t))` at `a = (t, x)`. -/
def frameVec (a : V2) (_ : Fin 1) : V2 := mk2 (-(a.2 0)) (1 - a.2 0 ^ 2 / (1 + a.1 0))

theorem ell_frameVec {a : V2} (ha : a ∈ circle2) (ht : 0 < 1 + a.1 0) (i : Fin 1) :
    inner2 a (frameVec a i) = 0 := by
  have hq : a.1 0 ^ 2 + a.2 0 ^ 2 = 1 := by rw [← nsq_eq]; exact ha
  have hne : (1 + a.1 0) ≠ 0 := ht.ne'
  simp only [inner2, frameVec, mk2]
  field_simp
  linear_combination (-(a.2 0)) * hq

theorem linearIndependent_frameVec (a : V2) :
    LinearIndependent ℝ (frameVec a) := by
  rw [linearIndependent_unique_iff]
  intro h
  have h0 := congrArg (fun v : V2 => v.1 0) h
  have h1 := congrArg (fun v : V2 => v.2 0) h
  simp only [frameVec, mk2, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, neg_eq_zero] at h0 h1
  rw [h0] at h1
  norm_num at h1

theorem continuousOn_frameVec (i : Fin 1) :
    ContinuousOn (fun a : V2 => frameVec a i) {a | 0 < 1 + a.1 0} := by
  have hd : ContinuousOn (fun a : V2 => a.2 0 ^ 2 / (1 + a.1 0)) {a | 0 < 1 + a.1 0} :=
    ContinuousOn.div (by fun_prop) (by fun_prop) fun a ha => (show 0 < 1 + a.1 0 from ha).ne'
  refine ContinuousOn.prodMk (continuousOn_pi.2 fun _ => ?_) (continuousOn_pi.2 fun _ => ?_)
  · exact (continuous_neg.comp ((continuous_apply 0).comp continuous_snd)).continuousOn
  · exact continuousOn_const.sub hd

/-! ### The half-plane M-polyfold -/

/-- The sc-Banach space `ℝ` with the constant structure. -/
abbrev W1 : ScBanach := ScBanach.const (Fin 1 → ℝ)

/-- The model sc-Banach space `ℝ ⊕ ℝ`. -/
abbrev E2 : ScBanach := (ScBanach.const (Fin 1 → ℝ)).prod W1

/-- The half-plane `[0, ∞) × ℝ`. -/
abbrev Q2 : Set (E2 0) := quadrant 1 W1 0

/-- **The half-plane `X = [0, ∞) × ℝ` as an M-polyfold**, with boundary `{t = 0}`. -/
abbrev Pa : MPolyfold Q2 := quadrantPolyfold 1 W1

theorem relOpen_Q2 : IsRelOpenInQuadrant E2 Q2 Q2 := isRelOpenInQuadrant_quadrant 1 W1

/-- The chart `id` of `X`. -/
abbrev chartA : MChart Q2 :=
  (LocalModel.ofRelOpen relOpen_Q2).selfChart (quadrant_nonempty 1 W1)

theorem isChart_chartA : Pa.IsChart chartA :=
  relOpen_Q2.selfChart_isChart (quadrant_nonempty 1 W1)

theorem chartA_symm_val {v : E2 0} (hv : v ∈ Q2) : ((chartA.symm v : Q2) : E2 0) = v :=
  chartA.toPartialEquiv.right_inv hv

theorem bijective_toBase_E2 (m : ℕ) : Bijective (E2.toBase m) :=
  bijective_toBase_prod (bijective_toBase_const _) (bijective_toBase_const _) m

/-- A vector of `ℝ ⊕ ℝ` read on level `1`. -/
def lev1 (v : V2) : E2 1 := v

theorem toBase_lev1 (v : V2) : E2.toBase 1 (lev1 v) = v := by
  rw [ScBanach.prod_toBase]
  exact Prod.ext (ScBanach.const_toBase _ 1 _) (ScBanach.const_toBase _ 1 _)

theorem mem_smooth_E2 (v : E2 0) : v ∈ E2.smooth :=
  E2.mem_smooth_iff.2 fun j => (bijective_toBase_E2 j).2 v

/-- `X` has a corner structure (Definition 4.1). -/
theorem Pa_hasCornerStructure : Pa.HasCornerStructure := by
  refine hasCornerStructure_iff.2 fun x => ?_
  have hfin : FiniteDimensional ℝ (E2 0) := by
    change FiniteDimensional ℝ ((Fin 1 → ℝ) × (Fin 1 → ℝ)); infer_instance
  obtain ⟨χ', hχ', hsrc, hc, -⟩ := MChart.exists_isCornerChart_of_finiteDimensional isChart_chartA
    relOpen_Q2 hfin
  exact ⟨χ', hχ', hsrc ▸ mem_univ x, hc⟩

theorem Pa_mem_smoothSet (p : Q2) : p ∈ Pa.smoothSet :=
  (mem_smoothSet_iff_of_isChart isChart_chartA (mem_univ p)).2 (mem_smooth_E2 _)

theorem Pa_mem_levelSet (m : ℕ) (p : Q2) : p ∈ Pa.levelSet m :=
  Pa.smoothSet_subset_levelSet m (Pa_mem_smoothSet p)

theorem Pa_isScSmoothMap_toLevelOne (x₀ : Pa.Level 1) :
    Pa.IsScSmoothMap Pa.shift (Pa.toLevelOne x₀) := by
  have hc := hasCornerStructure_iff.1 Pa_hasCornerStructure
  refine (isScSmoothMap_toLevelOne_of_cover x₀ fun x => ?_).2
  obtain ⟨χ, hχ, hx, hcorner⟩ := hc x
  exact ⟨χ, hχ, hx, hcorner.isScPlusRetract⟩

/-- `d_X(p)` is the number of vanishing `t`-coordinates of `p`. -/
theorem Pa_degIndex (p : Q2) :
    Pa.degIndex p = (Finset.univ.filter fun i : Fin 1 => p.1.1 i = 0).card := by
  rw [show Pa.degIndex p = TameBoundaryExample.dq 1 W1 p from rfl, TameBoundaryExample.dq_eq]
  rfl

theorem Pa_degIndex_le (p : Q2) : Pa.degIndex p ≤ 1 := by
  rw [Pa_degIndex]
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem Pa_mem_boundary_iff (p : Q2) : p ∈ Pa.boundary ↔ p.1.1 0 = 0 := by
  change 1 ≤ Pa.degIndex p ↔ _
  rw [Pa_degIndex, Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff]
  simp

/-- **A `C^∞` map `f` on an open `G ⊆ ℝ²` mapping `X` into `X` is sc-smooth on `X ∩ G`.** -/
theorem isScSmoothOn_of_contDiffOn {G : Set V2} (hG : IsOpen G) {f : V2 → V2}
    (hf : ContDiffOn ℝ ∞ f G) (hQ : ∀ v ∈ Q2, f v ∈ Q2) :
    Pa.IsScSmoothOn Pa (fun p : Q2 => (⟨f p.1, hQ p.1 p.2⟩ : Q2)) {p | p.1 ∈ G} := by
  have hGo : IsOpen {p : Q2 | p.1 ∈ G} := hG.preimage continuous_subtype_val
  have hU : IsRelOpenInQuadrant E2 Q2 (G ∩ Q2) :=
    ⟨relOpen_Q2.isPartialQuadrant, G, hG, rfl⟩
  have hcont : ContinuousOn (fun p : Q2 => f p.1) {p | p.1 ∈ G} :=
    hf.continuousOn.comp continuous_subtype_val.continuousOn fun _ hp => hp
  refine IsScSmoothOn.of_exists_charts hGo (Topology.IsInducing.subtypeVal.continuousOn_iff.2 hcont)
    fun x hx => ⟨chartA, chartA, {p | p.1 ∈ G}, isChart_chartA, isChart_chartA, hGo, hx,
      fun p hp => ⟨hp, mem_univ _⟩, fun _ _ => mem_univ _, ?_⟩
  have himg : chartA '' {p : Q2 | p.1 ∈ G} = G ∩ Q2 := by
    ext v
    constructor
    · rintro ⟨p, hp, rfl⟩; exact ⟨hp, p.2⟩
    · intro hv; exact ⟨⟨v, hv.2⟩, hv.1, rfl⟩
  have hval : ∀ u ∈ G ∩ Q2,
      (chartA ∘ (fun p : Q2 => (⟨f p.1, hQ p.1 p.2⟩ : Q2)) ∘ chartA.symm) u = f u := by
    intro u hu
    change f ((chartA.symm u : Q2) : E2 0) = f u
    rw [chartA_symm_val hu.2]
  rw [himg]
  refine (isScSmoothRetractMap_iff_exists hU.isScRetract).2
    ⟨fun u hu => ?_, ScRetraction.id hU, image_id _, ?_⟩
  · rw [hval u hu]; exact hQ u hu.2
  · refine (isScSmooth_of_bijective_toBase bijective_toBase_E2 bijective_toBase_E2
      hU.isScDomain (f := f) (hf.mono inter_subset_left)).congr hU.isScDomain fun u hu => ?_
    exact (hval u hu).symm

/-! ### The half-circle and its retraction -/

theorem rho_mem_Q2 {v : E2 0} (hv : v ∈ Q2) : rho v ∈ Q2 := fun i => by
  rw [Subsingleton.elim i 0]
  change 0 ≤ (√(nsq v))⁻¹ * v.1 0
  exact mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) (hv 0)

/-- **The closed right half-circle** `{p ∈ [0, ∞) × ℝ | |p| = 1}`. -/
def arc : Set Q2 := {p | nsq p.1 = 1}

/-- The open set `X ∖ {0}`. -/
def Va : Set Q2 := {p | p.1 ∈ punct2}

theorem isOpen_Va : IsOpen Va := isOpen_punct2.preimage continuous_subtype_val

theorem arc_subset_Va : arc ⊆ Va := fun _ hp => circle2_subset_punct2 hp

theorem isClosed_arc : IsClosed arc := isClosed_circle2.preimage continuous_subtype_val

/-- The radial retraction of `X`. -/
def sA (p : Q2) : Q2 := ⟨rho p.1, rho_mem_Q2 p.2⟩

theorem sA_mem_arc {p : Q2} (hp : p ∈ Va) : sA p ∈ arc := rho_mem_circle2 hp

theorem sA_eq_self {p : Q2} (hp : p ∈ arc) : sA p = p := Subtype.ext (rho_eq_self hp)

theorem sA_image : sA '' Va = arc ∩ Va := by
  refine Subset.antisymm ?_ fun p hp => ⟨p, hp.2, sA_eq_self hp.1⟩
  rintro _ ⟨p, hp, rfl⟩
  exact ⟨sA_mem_arc hp, arc_subset_Va (sA_mem_arc hp)⟩

/-- **The radial retraction is an sc⁺-retraction of `X` on `X ∖ {0}`** (Definition 4.1.4). -/
theorem sA_isScPlusRetractionOn : Pa.IsScPlusRetractionOn sA Va where
  isScSmoothOn := isScSmoothOn_of_contDiffOn isOpen_punct2 contDiffOn_rho fun _ hv => rho_mem_Q2 hv
  mapsTo _ hp := arc_subset_Va (sA_mem_arc hp)
  idem _ hp := sA_eq_self (sA_mem_arc hp)
  mem_levelSet _ _ := Pa_mem_levelSet 1 _
  isScSmoothOn_one x₀ := IsScSmoothOn.comp (Pa_isScSmoothMap_toLevelOne x₀)
    (isScSmoothOn_of_contDiffOn isOpen_punct2 contDiffOn_rho fun _ hv => rho_mem_Q2 hv)
    (mapsTo_univ _ _)

/-- The data `(X ∖ {0}, p ↦ p/|p|)` of the half-circle (Definition 4.2.1). -/
def arcData : Pa.SubmanifoldData arc :=
  ⟨Va, sA, isOpen_Va, sA_isScPlusRetractionOn, sA_image⟩

/-- **The half-circle is a smooth finite-dimensional submanifold of `X`** (Definition 4.2.1). -/
theorem isSmoothSubmanifold_arc : Pa.IsSmoothSubmanifold arc := fun _ ha =>
  ⟨Va, isOpen_Va, arc_subset_Va ha, sA, sA_isScPlusRetractionOn, sA_image⟩

/-! ### The tangent spaces -/

/-- The radial retraction in the chart `id`, as an sc-smooth retraction of `ℝ ⊕ ℝ`. -/
def rhoRet : ScRetraction E2 Q2 where
  U := punct2 ∩ Q2
  toFun := rho
  relOpen := ⟨relOpen_Q2.isPartialQuadrant, punct2, isOpen_punct2, rfl⟩
  mapsTo _ hv := ⟨circle2_subset_punct2 (rho_mem_circle2 hv.1), rho_mem_Q2 hv.2⟩
  isScSmooth := isScSmooth_of_bijective_toBase bijective_toBase_E2 bijective_toBase_E2
    (IsRelOpenInQuadrant.isScDomain ⟨relOpen_Q2.isPartialQuadrant, punct2, isOpen_punct2, rfl⟩)
    (contDiffOn_rho.mono inter_subset_left)
  idem _ hv := rho_idem hv.1

theorem rhoRet_retract : rhoRet.retract = circle2 ∩ Q2 := by
  refine Subset.antisymm ?_ fun v hv => ⟨v, ⟨circle2_subset_punct2 hv.1, hv.2⟩, rho_eq_self hv.1⟩
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨rho_mem_circle2 hv.1, rho_mem_Q2 hv.2⟩

theorem chartA_image_arc {W : Set Q2} (hW : arc ⊆ W) : chartA '' (W ∩ arc) = rhoRet.retract := by
  rw [rhoRet_retract, inter_eq_right.2 hW]
  ext v
  constructor
  · rintro ⟨p, hp, rfl⟩; exact ⟨hp, p.2⟩
  · intro hv; exact ⟨⟨v, hv.2⟩, hv.1, rfl⟩

theorem shrink_arcData : arcData.toSubData.shrink chartA = Va := by
  refine Subset.antisymm (fun p hp => hp.1.1) fun p hp =>
    ⟨⟨hp, mem_univ _⟩, arc_subset_Va (sA_mem_arc hp), mem_univ _⟩

theorem chartA_image_shrink : chartA '' (arcData.toSubData.shrink chartA ∩ arc) =
    rhoRet.retract := by
  rw [shrink_arcData]; exact chartA_image_arc arc_subset_Va

/-- **The tangent space of the half-circle** at `a`, in the chart `id`: `a^⊥`. -/
theorem tangentSpace_arc {a : V2} (ha : a ∈ circle2 ∩ Q2) :
    tangentSpace E2 Q2 rhoRet.retract (lev1 a) =
      (LinearMap.ker (ell a : V2 →ₗ[ℝ] ℝ) : Set V2) := by
  have hz : lev1 a ∈ E2.lvlSet rhoRet.retract 1 := by
    rw [ScBanach.mem_lvlSet, toBase_lev1, rhoRet_retract]; exact ha
  have hD : scDeriv rhoRet.U rhoRet (lev1 a) = rhoDeriv a := by
    refine scDeriv_eq_of_hasFDerivAt rhoRet.relOpen rhoRet.isSc1
      (by rw [ScBanach.mem_lvlSet] at hz ⊢; exact rhoRet.retract_subset hz) ?_
    rw [toBase_lev1]; exact hasFDerivAt_rho ha.1
  rw [tangentSpace_eq_coe_submodule rhoRet hz, hD]
  exact congrArg _ (range_rhoDeriv ha.1)

/-- **The half-circle is a `1`-dimensional submanifold of `X`** (Remark 9.1.1). -/
theorem isSubmanifoldOfDim_arc : Pa.IsSubmanifoldOfDim arc 1 := by
  refine ⟨isSmoothSubmanifold_arc, fun a ha => ?_⟩
  have hQ : IsScRetract chartA.model.E chartA.model.C (chartA '' (Va ∩ arc)) := by
    rw [chartA_image_arc arc_subset_Va]; exact rhoRet.isScRetract
  refine hasDimAt_of_finrank isSmoothSubmanifold_arc ha isChart_chartA isOpen_Va
    (subset_univ _) hQ (arc_subset_Va ha) (z := lev1 a.1) (toBase_lev1 a.1) ?_
  erw [chartA_image_arc arc_subset_Va, tangentSpace_arc ⟨ha, a.2⟩, span_eq]
  exact finrank_ker_ell ha

/-! ### Tameness -/

/-- The projection `h ↦ h − ⟨a, h⟩a` as an sc-operator of `ℝ ⊕ ℝ`. -/
def projOp (a : V2) : ScOperator E2 E2 where
  lvl _ := rhoDeriv a
  incl_comm _ _ := rfl

/-- **2021 Definition 2.5.19 (3) for the half-circle**: in the chart `id`, `T_a arc = a^⊥` has
the sc-complement `ℝa` in `T_aX = ℝ²`, and `ℝa ⊆ T^R_aX`. -/
theorem hasReducedComplementAt_arc {a : V2} (ha : a ∈ circle2 ∩ Q2) :
    HasReducedComplementAt Q2 Q2 rhoRet.retract (ScIso.refl E2) (lev1 a) := by
  have hU := relOpen_Q2
  have hidem : ∀ h, projOp a 0 (projOp a 0 h) = projOp a 0 h := rhoDeriv_idem ha.1
  have hS := ScBanach.isScSplitting_of_idem (projOp a) hidem
  have hzU : lev1 a ∈ E2.lvlSet Q2 1 := by rw [ScBanach.mem_lvlSet, toBase_lev1]; exact ha.2
  refine ⟨LinearMap.range (projOp a 0 : E2 0 →ₗ[ℝ] E2 0), ⊤,
    LinearMap.ker (projOp a 0 : E2 0 →ₗ[ℝ] E2 0), ?_, ?_, ?_, hS.2.1, fun m => ?_⟩
  · rw [tangentSpace_arc ha]
    exact congrArg (fun S : Submodule ℝ V2 => (S : Set V2)) (range_rhoDeriv ha.1)
  · have hret : (ScRetraction.id hU).retract = Q2 := image_id _
    have hz0 : lev1 a ∈ E2.lvlSet (ScRetraction.id hU).retract 1 := by rw [hret]; exact hzU
    have h := tangentSpace_eq_coe_submodule (ScRetraction.id hU) hz0
    rw [hret] at h
    have hD : scDeriv (ScRetraction.id hU).U (ScRetraction.id hU) (lev1 a) =
        ContinuousLinearMap.id ℝ (E2 0) :=
      IsSc1.scDeriv_eqOn (isSc1With_id _) (hU.isScDomain.uniqueDiffWithinAt 1) hzU
    have hrange : LinearMap.range (scDeriv (ScRetraction.id hU).U (ScRetraction.id hU)
        (lev1 a) : E2 0 →ₗ[ℝ] E2 0) = ⊤ := by
      rw [hD]; exact LinearMap.range_id
    rw [h, hrange]
  · intro v hv
    have hv' : rhoDeriv a v = 0 := hv
    refine ⟨Submodule.mem_top, (mem_minimalSubspaceWith _).2 fun i hi => ?_⟩
    rw [Subsingleton.elim i 0] at hi ⊢
    have hi' : a.1 0 = 0 := by
      have := hi; rw [toBase_lev1] at this; exact this
    change v.1 0 = 0
    rw [ker_rhoDeriv hv']
    change inner2 a v * a.1 0 = 0
    rw [hi', mul_zero]
  · have hc := hS.2.2 m
    refine ⟨hc.disjoint, ?_⟩
    rw [hc.sup_eq_top]
    exact (Submodule.comap_top _).symm

/-- The data of 2021 Definition 2.5.19 for the half-circle: the radial retraction keeps `d_X`. -/
def arcTameData : Pa.TameSubData arc :=
  { arcData.toSubData with
    degIndex_apply := fun p hp => by
      change Pa.degIndex (sA p) = Pa.degIndex p
      rw [Pa_degIndex, Pa_degIndex]
      congr 1
      refine Finset.filter_congr fun i _ => ?_
      rw [Subsingleton.elim i 0]
      change (√(nsq p.1))⁻¹ * p.1.1 0 = 0 ↔ p.1.1 0 = 0
      exact ⟨fun h => (mul_eq_zero.1 h).resolve_left (inv_sqrt_pos hp).ne',
        fun h => by rw [h, mul_zero]⟩
    complement := fun y hy _ => ⟨chartA, 1, W1, ScIso.refl _, lev1 y.1, isChart_chartA,
      mem_univ _, by ext; rfl, toBase_lev1 _, by
        change HasReducedComplementAt Q2 Q2
          (chartA '' (arcData.toSubData.shrink chartA ∩ arc)) (ScIso.refl E2) (lev1 y.1)
        erw [chartA_image_shrink]
        exact hasReducedComplementAt_arc ⟨hy.1, y.2⟩⟩ }

/-- **The half-circle is a tame sub-M-polyfold of `X`** (2021 Definition 2.5.19). -/
theorem isTameSubMPolyfold_arc : Pa.IsTameSubMPolyfold arc :=
  ⟨quadrantPolyfold_isTame 1 W1, fun _ hy => ⟨arcTameData, arc_subset_Va hy⟩⟩

/-- **The structure induced on the half-circle is tame** (2021 Definition 2.5.18). -/
theorem hasTameInducedStructure_arc : Pa.HasTameInducedStructure arc :=
  isTameSubMPolyfold_arc.hasTameInducedStructure

/-! ### The boundary: the two end points -/

/-- At an end point `e_t ∈ T_a arc` is not in `T^R_aX`. -/
theorem not_isTangentReducedAt_arc {p : Q2} (hp : p ∈ arc) (h0 : p.1.1 0 = 0) :
    ¬ Pa.IsTangentReducedAt arc p := by
  intro h
  have hred := h.isReducedChart arcData isChart_chartA (ScIso.refl _) (by ext; rfl)
    (arc_subset_Va hp) (mem_univ _) (toBase_lev1 p.1)
  have hv : mk2 1 0 ∈ tangentSpace E2 Q2
      (chartA '' (arcData.toSubData.shrink chartA ∩ arc)) (lev1 p.1) := by
    erw [chartA_image_shrink, tangentSpace_arc ⟨hp, p.2⟩]
    change ell p.1 (mk2 1 0) = 0
    simp [inner2, h0]
  have h1 := (mem_minimalSubspaceWith _).1 (hred hv) 0 (by
    change (E2.toBase 1 (lev1 p.1)).1 0 = 0
    rw [toBase_lev1]; exact h0)
  exact one_ne_zero h1

theorem mem_submanifoldBoundary_arc {p : Q2} (hp : p ∈ arc) (h0 : p.1.1 0 = 0) :
    p ∈ Pa.submanifoldBoundary arc :=
  (mem_submanifoldBoundary_iff isSmoothSubmanifold_arc).2
    ⟨hp, (Pa_mem_boundary_iff p).2 h0, not_isTangentReducedAt_arc hp h0⟩

/-- The end points `{p ∈ arc | t(p) = 0} = {(0, ±1)}`. -/
def arcEnds : Set Q2 := {p | p ∈ arc ∧ p.1.1 0 = 0}

/-- **The stratum `∂₁ arc = {d = 1}` is the pair of end points.** -/
theorem boundaryStratum_arc : Pa.boundaryStratum arc = arcEnds := by
  ext p
  constructor
  · intro hb
    have hb' := (mem_boundaryStratum_iff_subDegIndex isSmoothSubmanifold_arc
      hasTameInducedStructure_arc hb.1).1 hb
    refine ⟨hb.1, (Pa_mem_boundary_iff p).1 ?_⟩
    have := subDegIndex_le isSmoothSubmanifold_arc.isSubMPolyfold ⟨p, hb.1⟩
    rw [hb'] at this
    exact this
  · rintro ⟨hp, h0⟩
    refine (mem_boundaryStratum_iff_subDegIndex isSmoothSubmanifold_arc
      hasTameInducedStructure_arc hp).2 ?_
    have h1 := (mem_submanifoldBoundary_iff_subDegIndex isSmoothSubmanifold_arc hp).1
      (mem_submanifoldBoundary_arc hp h0)
    have h2 := (subDegIndex_le isSmoothSubmanifold_arc.isSubMPolyfold ⟨p, hp⟩).trans
      (Pa_degIndex_le p)
    omega

/-! ### Compactness -/

theorem abs_le_one_of_mem_circle2 {v : V2} (hv : v ∈ circle2) : |v.1 0| ≤ 1 ∧ |v.2 0| ≤ 1 := by
  have hq : v.1 0 ^ 2 + v.2 0 ^ 2 = 1 := by rw [← nsq_eq]; exact hv
  refine ⟨?_, ?_⟩ <;> rw [← sq_le_one_iff_abs_le_one] <;>
    nlinarith [sq_nonneg (v.1 0), sq_nonneg (v.2 0)]

theorem isCompact_circle2 : IsCompact circle2 := by
  refine Metric.isCompact_of_isClosed_isBounded isClosed_circle2
    (isBounded_iff_forall_norm_le.2 ⟨1, fun v hv => ?_⟩)
  obtain ⟨h0, h1⟩ := abs_le_one_of_mem_circle2 hv
  refine norm_prod_le_iff.2 ⟨(pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_,
    (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_⟩
  · rw [Subsingleton.elim i 0, Real.norm_eq_abs]; exact h0
  · rw [Subsingleton.elim i 0, Real.norm_eq_abs]; exact h1

theorem image_val_arc : Subtype.val '' arc = circle2 ∩ Q2 := by
  ext v
  constructor
  · rintro ⟨p, hp, rfl⟩; exact ⟨hp, p.2⟩
  · intro hv; exact ⟨⟨v, hv.2⟩, hv.1, rfl⟩

/-- **The half-circle is compact.** -/
theorem isCompact_arc : IsCompact arc := by
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, image_val_arc]
  exact isCompact_circle2.inter_right (quadrant_isClosed 1 W1 0)

/-- The end point `(0, 1)`. -/
def pt1 : Q2 := ⟨mk2 0 1, fun i => by rw [Subsingleton.elim i 0]; exact le_rfl⟩

theorem pt1_mem_arcEnds : pt1 ∈ arcEnds :=
  ⟨by change nsq (mk2 0 1) = 1; rw [nsq_eq]; simp, rfl⟩

end K2Arc

end Polyfold
