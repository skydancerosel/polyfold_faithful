import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_73

/-!
Round trip for V3_73 (the re-centring lemma, proof of Theorem 3.27, p. 84).  `A` is the
conjunction of the types of `Polyfold.recentre_contDiffOn_levels` (universe `u` at `0`),
`Polyfold.finrank_le_of_interior_image_nonempty`, `Polyfold.exists_contDiffOn_inverse` (universes
`u_1, u_2` at `0`), `Polyfold.InvDataW.contDiffOn_inv` and
`Polyfold.scDeriv_apply_toBase_deriv_eq_of_fixed` (universe `u_1` at `0`).

**B is false** (`not_B`), as its author predicted.  B claims, for every datum `(φ, N, Y, V, δ)`
of Definition 3.25 at every `x ∈ M`, every `v₀ ∈ V` and every datum `(ψ, N', Y', V', τ)` at
`x₀ = φ⁻¹(v₀ + δ(v₀))`, that `k(w) = πφψ⁻¹(w + τ(w))` has an invertible linearization at `0`, is a
local diffeomorphism, and that `δ` is an sc^∞-germ near `v₀`.  Definition 3.25 controls `δ` only
near `0`.  The counter-model (section `CE`, shared with V3_74): `X = ℝ²` (tame),
`M = {(t³, t)}` (it has the `1`-dimensional tangent germ property in the blind form), and at
`(1, 1)` the datum `N = ℝ(3, 1)`, `Y = ℝ(0, 1)`, `V = N`, `δ(v) = (∛(1 + v₁) − 1 − v₁/3)(0, 1)`;
at `v₀ = −(1/3)(3, 1)` (so `x₀ = (0, 0)`, where `M` is tangent to `Y`) `δ` is not differentiable,
so B's third conjunct fails for any datum at `x₀` (one exists by the tangent germ property).  (The
first conjunct fails there as well, informally: `M` is tangent to `Y` at `x₀`, so `Dk(0) = 0`; this
is not formalized, the third conjunct suffices.)

Hence `¬(A → B)` and `B → A` only ex falso.  The project's `A` is the corrected lemma (Finding 82):
`recentre_contDiffOn_levels` *assumes* that the first graph map `σ₁` is `C¹` on its whole domain
`V₁` (the hypothesis that makes the linearization of `k` invertible) and gets the regularity of
`σ₁` near `v₀` and `dim K₁ = dim K₂`; the other conjuncts are its analytic tools (a Sard-type
dimension bound, a `C^k` inverse function lemma on relatively open sets, the inverse-function
machinery `InvDataW`, and a tangent-space identity for retracts), none of which B states.
-/

namespace RoundTrip.V3_73
open Polyfold

/-- The project's statement: the listed theorems, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.recentre_contDiffOn_levels.{0} ∧
    type_of% @Polyfold.finrank_le_of_interior_image_nonempty.{0, 0} ∧
    type_of% @Polyfold.exists_contDiffOn_inverse.{0, 0} ∧
    type_of% @Polyfold.InvDataW.contDiffOn_inv.{0} ∧
    type_of% @Polyfold.scDeriv_apply_toBase_deriv_eq_of_fixed.{0}

theorem A_holds : A :=
  ⟨@Polyfold.recentre_contDiffOn_levels.{0}, @Polyfold.finrank_le_of_interior_image_nonempty.{0, 0},
    @Polyfold.exists_contDiffOn_inverse.{0, 0}, @Polyfold.InvDataW.contDiffOn_inv.{0},
    @Polyfold.scDeriv_apply_toBase_deriv_eq_of_fixed.{0}⟩

namespace CE
open Set Filter Topology
open scoped ContDiff

/-- The real cube root. -/
noncomputable def cbrt (x : ℝ) : ℝ :=
  if 0 ≤ x then x ^ ((3 : ℕ) : ℝ)⁻¹ else -((-x) ^ ((3 : ℕ) : ℝ)⁻¹)

theorem cbrt_pow (t : ℝ) : cbrt (t ^ 3) = t := by
  unfold cbrt
  rcases le_or_gt 0 t with ht | ht
  · rw [if_pos (by positivity)]
    exact Real.pow_rpow_inv_natCast ht (by norm_num)
  · have h3 : t ^ 3 < 0 := Odd.pow_neg (by decide) ht
    rw [if_neg (not_le.2 h3)]
    have : -(t ^ 3) = (-t) ^ 3 := by ring
    rw [this, Real.pow_rpow_inv_natCast (by linarith) (by norm_num), neg_neg]

theorem cbrt_cube (x : ℝ) : cbrt x ^ 3 = x := by
  unfold cbrt
  split_ifs with hx
  · exact Real.rpow_inv_natCast_pow hx (by norm_num)
  · have : (-((-x) ^ ((3 : ℕ) : ℝ)⁻¹)) ^ 3 = -(((-x) ^ ((3 : ℕ) : ℝ)⁻¹) ^ 3) := by ring
    rw [this, Real.rpow_inv_natCast_pow (by linarith) (by norm_num), neg_neg]

theorem continuous_cbrt : Continuous cbrt := by
  have h1 : Continuous fun x : ℝ => x ^ ((3 : ℕ) : ℝ)⁻¹ := Real.continuous_rpow_const (by positivity)
  refine Continuous.if_le h1 (continuous_neg.comp (h1.comp continuous_neg)) continuous_const
    continuous_id fun x hx => ?_
  subst hx
  rw [neg_zero, Real.zero_rpow (by positivity), neg_zero]

theorem cbrt_eq_rpow {x : ℝ} (hx : 0 < x) : cbrt x = x ^ ((3 : ℕ) : ℝ)⁻¹ := by
  unfold cbrt; rw [if_pos hx.le]

theorem contDiffOn_cbrt : ContDiffOn ℝ ∞ cbrt (Ioi 0) := by
  intro x hx
  have : ContDiffAt ℝ ∞ (fun x : ℝ => x ^ ((3 : ℕ) : ℝ)⁻¹) x :=
    Real.contDiffAt_rpow_const_of_ne (ne_of_gt hx)
  exact this.contDiffWithinAt.congr (fun y hy => cbrt_eq_rpow hy) (cbrt_eq_rpow hx)

theorem hasDerivAt_cbrt_one : HasDerivAt cbrt (1 / 3) 1 := by
  have h := Real.hasDerivAt_rpow_const (x := 1) (p := ((3 : ℕ) : ℝ)⁻¹) (Or.inl one_ne_zero)
  have heq : cbrt =ᶠ[𝓝 1] fun x : ℝ => x ^ ((3 : ℕ) : ℝ)⁻¹ := by
    filter_upwards [Ioi_mem_nhds (zero_lt_one' ℝ)] with y hy using cbrt_eq_rpow hy
  have := h.congr_of_eventuallyEq heq
  have e : ((3 : ℕ) : ℝ)⁻¹ * (1 : ℝ) ^ (((3 : ℕ) : ℝ)⁻¹ - 1) = 1 / 3 := by norm_num
  rw [e] at this
  exact this

theorem cbrt_one : cbrt 1 = 1 := by
  have := cbrt_pow 1
  simpa using this


/-! ### Linear algebra in `ℝ²` with the constant sc-structure -/

abbrev E2 := Fin 2 → ℝ

lemma levelSub_const (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (A : Submodule ℝ V) (m : ℕ) : (ScBanach.const V).levelSub A m = A := by
  ext x; rw [ScBanach.mem_levelSub, ScBanach.const_toBase]

lemma le_smooth_const (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (A : Submodule ℝ V) : A ≤ (ScBanach.const V).smooth := by
  intro x _
  exact (ScScale.mem_smooth_iff _).2 fun m => ⟨x, ScBanach.const_toBase V m x⟩

lemma isScSplitting_const (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A B : Submodule ℝ V) (h : IsCompl A B) :
    (ScBanach.const V).IsScSplitting A B := by
  refine ⟨(ScBanach.proposition_1_1_7_iff (ScBanach.const V) A).2 (le_smooth_const V A),
    (ScBanach.proposition_1_1_7_iff (ScBanach.const V) B).2 (le_smooth_const V B), fun m => ?_⟩
  rw [levelSub_const, levelSub_const]; exact h

lemma isCompl_span (u e : E2) (hdet : u 0 * e 1 - u 1 * e 0 ≠ 0) :
    IsCompl (ℝ ∙ u) (ℝ ∙ e) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 hx'
    have h0 := congrFun hb 0
    have h1 := congrFun hb 1
    simp only [Pi.smul_apply, smul_eq_mul] at h0 h1
    have : a * (u 0 * e 1 - u 1 * e 0) = 0 := by linear_combination (-e 1) * h0 + e 0 * h1
    rcases mul_eq_zero.1 this with ha | ha
    · rw [ha, zero_smul]
    · exact absurd ha hdet
  · rw [codisjoint_iff, eq_top_iff]
    intro p _
    rw [Submodule.mem_sup]
    refine ⟨((p 0 * e 1 - p 1 * e 0) / (u 0 * e 1 - u 1 * e 0)) • u,
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u),
      ((u 0 * p 1 - u 1 * p 0) / (u 0 * e 1 - u 1 * e 0)) • e,
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e), ?_⟩
    funext i
    fin_cases i <;>
    · simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hdet]
      ring

/-- The coordinate `v ↦ v i` on a subspace of `ℝ²`. -/
noncomputable def coordL (N : Submodule ℝ E2) (i : Fin 2) : N →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).comp N.subtypeL

@[simp] lemma coordL_apply (N : Submodule ℝ E2) (i : Fin 2) (v : N) :
    coordL N i v = (v : E2) i := rfl

lemma hasFDerivAt_comp_smul {N : Submodule ℝ E2} (L : N →L[ℝ] ℝ) {g : ℝ → ℝ}
    (hg : HasDerivAt g 0 0) (e : E2) :
    HasFDerivAt (fun v => g (L v) • e) (0 : N →L[ℝ] E2) 0 := by
  have h' : HasFDerivAt (fun s => g s • e)
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) ((0 : ℝ) • e)) (L 0) := by
    rw [map_zero]; exact (hg.smul_const e).hasFDerivAt
  have := h'.comp (0 : N) L.hasFDerivAt
  refine this.congr_fderiv ?_
  ext v
  simp

/-! ### The M-polyfold `ℝ²` and the curve `M = {(t³, t)}` -/

/-- The curve `M = {(t³, t) | t ∈ ℝ}`: a smooth embedded curve with a vertical tangent at `0`. -/
def M : Set E2 := {p | p 0 = p 1 ^ 3}

/-- The line `ℝu ⊆ ℝ²`. -/
def Nsp (u : E2) : Submodule ℝ E2 := ℝ ∙ u

theorem fd (u : E2) : FiniteDimensional ℝ (Nsp u) := FiniteDimensional.finiteDimensional_submodule _

theorem mem_Nsp {u v : E2} : v ∈ Nsp u ↔ ∃ s : ℝ, s • u = v := Submodule.mem_span_singleton

theorem self_mem_Nsp (u : E2) : u ∈ Nsp u := Submodule.mem_span_singleton_self u

/-- Data of Definition 3.25 (2) in the blind form, in a translation chart of `ℝ²`, from a
transversal pair of lines `ℝu`, `ℝe` and a map `δ` that is smooth near `0` with `Dδ(0) = 0`. -/
theorem isGermData_mk (a u e : E2) (hu : u ≠ 0) (hdet : u 0 * e 1 - u 1 * e 0 ≠ 0)
    (δ : Nsp u → E2) (U : Set (Nsp u)) (hUo : IsOpen U) (h0U : (0 : Nsp u) ∈ U)
    (hδY : ∀ v, δ v ∈ Nsp e) (hcont : Continuous δ) (hsm : ContDiffOn ℝ ∞ δ U)
    (hd0 : HasFDerivAt δ (0 : Nsp u →L[ℝ] E2) 0) (hδ0 : δ 0 = 0)
    (himg : (fun p => p - a) '' M = range (fun v : Nsp u => (v : E2) + δ v)) :
    @IsGermData _ _ _ _ (rnPolyfold 2) M 1 a (rnChart 2 a) (Nsp u) (Nsp e) (fd u) univ δ := by
  have hU : ∃ O : Set (Nsp u), IsOpen O ∧ U = O ∩ univ := ⟨U, hUo, (inter_univ U).symm⟩
  have hrel : IsRelOpenInQuadrant (ScBanach.const (Nsp u)) univ U :=
    ⟨isPartialQuadrant_univ _, U, hUo, (inter_univ U).symm⟩
  have hsc : IsScSmooth (E := ScBanach.const (Nsp u)) (F := ScBanach.const E2) U δ :=
    IsScSmooth.of_contDiffOn_finiteDimensional hrel.isScDomain hsm
  have hG := hsc.isScSmoothGerm (isQuadrantLike_univ _) hU h0U
  obtain ⟨D, hD⟩ := (hG 1).1
  have hD0 : D 0 = 0 := by
    have h1 := hD.hasFDerivWithinAt 0 ((ScNbhdGerm.ofSet hU h0U).zero_mem 1)
    have hn : (ScNbhdGerm.ofSet hU h0U).U 1 ∈ 𝓝 (0 : (ScBanach.const (Nsp u)) 1) := by
      rw [ScNbhdGerm.ofSet_U, ScBanach.lvlSet_const]; exact hUo.mem_nhds h0U
    have h2 := h1.hasFDerivAt hn
    have he : (δ ∘ (ScBanach.const (Nsp u)).toBase 1) = δ :=
      funext fun v => congrArg δ (ScBanach.const_toBase (Nsp u) 1 v)
    rw [he] at h2
    have h3 := h2.unique hd0
    refine ContinuousLinearMap.ext fun v => ?_
    have := congrArg (fun T : Nsp u →L[ℝ] E2 => T v) h3
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] at this
    rwa [ScBanach.const_toBase] at this
  have hgc : IsGoodComplementB (ScBanach.const E2) univ (Nsp u) (Nsp e) :=
    ⟨fun _ => isScSplitting_const _ _ _ (isCompl_span u e hdet),
      fun h => absurd (le_smooth_const _ _) h, 1, one_pos,
      fun _ _ _ _ _ => iff_of_true (mem_univ _) (mem_univ _)⟩
  have hint : (interior (univ : Set (Nsp u))).Nonempty := by
    rw [interior_univ]; exact univ_nonempty
  have himg' : (fun p => p - a) '' (M ∩ univ) = (fun v : Nsp u => (v : E2) + δ v) '' univ := by
    rw [inter_univ, image_univ, himg]
  exact ⟨isChart_rnChart a, mem_univ a, sub_self a,
    ⟨ScRetraction.id (rn_relOpen_univ 2), image_id _, ScRetraction.id_isTame _⟩,
    finrank_span_singleton hu, le_smooth_const _ _, hint, hgc,
    ⟨univ, isOpen_univ, (inter_univ _).symm⟩, mem_univ _,
    fun v _ => hδY v, hcont.continuousOn, himg', hδ0,
    ScNbhdGerm.ofSet hU h0U, fun v _ => mem_univ v, hG, D, hD, hD0⟩

/-! ### The data at the points of `M` (good data: complement `ℝ(1, 0)`) -/

/-- The tangent direction `(3t₀², 1)` of `M` at `(t₀³, t₀)`. -/
def uf (t₀ : ℝ) : E2 := ![3 * t₀ ^ 2, 1]

/-- The horizontal line `ℝ(1, 0)`. -/
def e0 : E2 := ![1, 0]

/-- `δ(s(3t₀², 1)) = (3t₀s² + s³, 0)`: `M` near `(t₀³, t₀)` as a graph over its tangent line. -/
noncomputable def δf (t₀ : ℝ) : Nsp (uf t₀) → E2 :=
  fun v => (3 * t₀ * coordL _ 1 v ^ 2 + coordL _ 1 v ^ 3) • e0

theorem hasDerivAt_fam (t₀ : ℝ) : HasDerivAt (fun s : ℝ => 3 * t₀ * s ^ 2 + s ^ 3) 0 0 := by
  have := ((hasDerivAt_pow 2 (0 : ℝ)).const_mul (3 * t₀)).add (hasDerivAt_pow 3 (0 : ℝ))
  exact this.congr_deriv (by norm_num)

theorem germData_fam (x : E2) (hx : x ∈ M) :
    @IsGermData _ _ _ _ (rnPolyfold 2) M 1 x (rnChart 2 x) (Nsp (uf (x 1))) (Nsp e0) (fd _) univ
      (δf (x 1)) := by
  have hx' : x 0 = x 1 ^ 3 := hx
  have hgc : ContDiff ℝ ∞ (fun s : ℝ => 3 * x 1 * s ^ 2 + s ^ 3) := by fun_prop
  refine isGermData_mk x (uf (x 1)) e0 (fun h => by simpa [uf] using congrFun h 1)
    (by simp [uf, e0]) (δf (x 1)) univ isOpen_univ (mem_univ _)
    (fun v => Submodule.smul_mem _ _ (self_mem_Nsp e0))
    ((hgc.continuous.comp (coordL _ 1).continuous).smul continuous_const)
    ((hgc.comp (coordL _ 1).contDiff).smul contDiff_const).contDiffOn
    (hasFDerivAt_comp_smul (coordL _ 1) (hasDerivAt_fam (x 1)) e0) (by simp [δf]) ?_
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hp' : p 0 = p 1 ^ 3 := hp
    set w : Nsp (uf (x 1)) := ⟨(p 1 - x 1) • uf (x 1), Submodule.smul_mem _ _ (self_mem_Nsp _)⟩
      with hw
    have hcw : coordL _ 1 w = p 1 - x 1 := by rw [coordL_apply, hw]; simp [uf]
    refine ⟨w, ?_⟩
    funext i
    fin_cases i
    · simp only [δf, hcw]
      simp [hw, uf, e0]
      linear_combination -hp' + hx'
    · simp only [δf, hcw]
      simp [hw, uf, e0]
  · rintro ⟨v, rfl⟩
    obtain ⟨s, hs⟩ := mem_Nsp.1 v.2
    have hc : coordL _ 1 v = s := by
      rw [coordL_apply, ← hs]; simp [uf]
    refine ⟨x + ((v : E2) + δf (x 1) v), ?_, by simp⟩
    show (x + ((v : E2) + δf (x 1) v)) 0 = ((x + ((v : E2) + δf (x 1) v)) 1) ^ 3
    simp only [δf, hc, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← hs]
    simp [uf, e0, hx']
    ring

theorem hasTangentGermPropertyB_M : HasTangentGermPropertyB (rnPolyfold 2) M 1 :=
  ⟨by rw [TrivialBundle.rnPolyfold_smoothSet]; exact subset_univ _,
    fun x hx => ⟨rnChart 2 x, Nsp (uf (x 1)), Nsp e0, fd _, univ, δf (x 1), germData_fam x hx⟩⟩

/-! ### The bad datum at `(1, 1)`: complement `ℝ(0, 1)`, which is tangent to `M` at `(0, 0)` -/

/-- The point `(1, 1) ∈ M`. -/
def a1 : E2 := ![1, 1]

/-- The tangent direction `(3, 1)` of `M` at `(1, 1)`. -/
def ub : E2 := ![3, 1]

/-- The vertical line `ℝ(0, 1)`. -/
def eb : E2 := ![0, 1]

/-- `g(r) = ∛(1 + r) − 1 − r/3`. -/
noncomputable def gb (r : ℝ) : ℝ := cbrt (1 + r) - 1 - r / 3

/-- `δ(v) = g(v₁)·(0, 1)` (`v₁` the first coordinate of `v ∈ ℝ(3, 1)`): `M − (1, 1)` is the graph of
`δ` over `ℝ(3, 1)` along the vertical. -/
noncomputable def δb : Nsp ub → E2 := fun v => gb (coordL _ 0 v) • eb

theorem hasDerivAt_gb : HasDerivAt gb 0 0 := by
  have h1 : HasDerivAt (fun s : ℝ => 1 + s) 1 0 := (hasDerivAt_id' 0).const_add 1
  have h2 : HasDerivAt cbrt (1 / 3) ((fun s : ℝ => 1 + s) 0) := by
    simpa using hasDerivAt_cbrt_one
  have h3 := ((h2.comp 0 h1).sub_const 1).sub ((hasDerivAt_id' 0).div_const 3)
  exact h3.congr_deriv (by norm_num)

theorem continuous_gb : Continuous gb :=
  ((continuous_cbrt.comp (continuous_const.add continuous_id)).sub continuous_const).sub
    (continuous_id.div_const 3)

theorem contDiffOn_gb : ContDiffOn ℝ ∞ gb {r | 0 < 1 + r} := by
  have h : ContDiffOn ℝ ∞ (fun r : ℝ => cbrt (1 + r)) {r | 0 < 1 + r} :=
    contDiffOn_cbrt.comp (contDiff_const.add contDiff_id).contDiffOn fun r hr => hr
  exact (h.sub contDiffOn_const).sub (contDiffOn_id.div_const 3)

/-- `M − (1, 1)` is the graph of `δ` over `ℝ(3, 1)` along `ℝ(0, 1)`. -/
theorem image_bad : (fun p => p - a1) '' M = range (fun v : Nsp ub => (v : E2) + δb v) := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hp' : p 0 = p 1 ^ 3 := hp
    set w : Nsp ub := ⟨((p 0 - 1) / 3) • ub, Submodule.smul_mem _ _ (self_mem_Nsp _)⟩ with hw
    have hcw : coordL _ 0 w = p 0 - 1 := by rw [coordL_apply, hw]; simp [ub]
    have hg : gb (p 0 - 1) = p 1 - 1 - (p 0 - 1) / 3 := by
      rw [gb, show 1 + (p 0 - 1) = p 1 ^ 3 by rw [hp']; ring, cbrt_pow]
    refine ⟨w, ?_⟩
    funext i
    fin_cases i
    · simp only [δb, hcw, hg]
      simp [hw, ub, eb, a1]
    · simp only [δb, hcw, hg]
      simp [hw, ub, eb, a1]
  · rintro ⟨v, rfl⟩
    obtain ⟨s, hs⟩ := mem_Nsp.1 v.2
    have hc : coordL _ 0 v = 3 * s := by
      rw [coordL_apply, ← hs]; simp [ub]; ring
    refine ⟨a1 + ((v : E2) + δb v), ?_, by simp⟩
    show (a1 + ((v : E2) + δb v)) 0 = ((a1 + ((v : E2) + δb v)) 1) ^ 3
    simp only [δb, hc, gb, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← hs]
    simp only [a1, ub, eb, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, mul_zero,
      add_zero, mul_one]
    have : (1 + (s + (cbrt (1 + 3 * s) - 1 - 3 * s / 3))) = cbrt (1 + 3 * s) := by ring
    rw [this, cbrt_cube]
    ring


theorem germData_bad :
    @IsGermData _ _ _ _ (rnPolyfold 2) M 1 a1 (rnChart 2 a1) (Nsp ub) (Nsp eb) (fd _) univ δb := by
  have hUo : IsOpen {v : Nsp ub | 0 < 1 + coordL _ 0 v} :=
    isOpen_lt continuous_const (continuous_const.add (coordL _ 0).continuous)
  refine isGermData_mk a1 ub eb (fun h => by simpa [ub] using congrFun h 1)
    (by simp [ub, eb]) δb {v | 0 < 1 + coordL _ 0 v} hUo (by simp)
    (fun v => Submodule.smul_mem _ _ (self_mem_Nsp eb))
    ((continuous_gb.comp (coordL _ 0).continuous).smul continuous_const)
    ((contDiffOn_gb.comp (coordL _ 0).contDiff.contDiffOn fun v hv => hv).smul contDiffOn_const)
    (hasFDerivAt_comp_smul (coordL _ 0) hasDerivAt_gb eb) (by simp [δb, gb, cbrt_one]) image_bad
/-- The point `v₀ = −(1/3)(3, 1) ∈ ℝ(3, 1)`, where `1 + v₀₁ = 0`. -/
noncomputable def v₀ : Nsp ub := ⟨(-1 / 3 : ℝ) • ub, Submodule.smul_mem _ _ (self_mem_Nsp _)⟩

/-- **`δ` is not an sc-smooth germ near `v₀`**: along `w(t) = (t³/3)(3, 1)` (with `w'(0) = 0`),
`δ(v₀ + w(t)) = (t − 1 − (t³ − 1)/3)(0, 1)` has derivative `(0, 1) ≠ 0` at `t = 0`, which a germ
differentiable at `0` cannot have. -/
theorem not_smoothGerm (G : ScNbhdGerm (ScBanach.const (Nsp ub)) univ) :
    ¬ IsScSmoothGerm (E := ScBanach.const (Nsp ub)) (F := ScBanach.const E2) G
      (fun w => δb (v₀ + w)) := by
  intro hsm
  obtain ⟨D, hD⟩ := (hsm 1).1
  have h1 := hD.hasFDerivWithinAt _ (G.zero_mem 1)
  obtain ⟨O, hO, hGO⟩ := G.relOpen 1
  rw [ScBanach.lvlSet_const, inter_univ] at hGO
  have hz := G.zero_mem 1
  rw [hGO] at hz
  have h2 := h1.hasFDerivAt (by rw [hGO]; exact hO.mem_nhds hz)
  set u' : Nsp ub := ⟨ub, self_mem_Nsp ub⟩ with hu'
  set γ : ℝ → Nsp ub := fun t => (t ^ 3 / 3) • u' with hγ
  have hγd : HasDerivAt γ 0 0 := by
    have := ((hasDerivAt_pow 3 (0 : ℝ)).div_const 3).smul_const u'
    exact this.congr_deriv (by simp)
  have h3 := h2.comp_hasDerivAt_of_eq 0 hγd (by simp [hγ])
  have h4 : HasDerivAt (fun t : ℝ => (t - 1 - (t ^ 3 - 1) / 3) • eb) ((1 : ℝ) • eb) 0 := by
    have := (((hasDerivAt_id' (0 : ℝ)).sub_const 1).sub
      (((hasDerivAt_pow 3 (0 : ℝ)).sub_const 1).div_const 3)).smul_const eb
    exact this.congr_deriv (by simp)
  have h5 := h3.unique (h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_))
  · have := congrFun h5 1
    simp [eb] at this
  · simp only [Function.comp_apply]
    rw [ScBanach.const_toBase]
    have hc : coordL _ 0 (v₀ + γ t) = -1 + t ^ 3 := by
      have e1 : ((v₀ + γ t : Nsp ub) : E2) = (-1 / 3 : ℝ) • ub + (t ^ 3 / 3) • ub := rfl
      rw [coordL_apply, e1]
      simp [ub]
    simp only [δb, hc, gb]
    rw [show 1 + (-1 + t ^ 3) = t ^ 3 by ring, cbrt_pow]
    congr 1
    ring

theorem not_germNear :
    ¬ @IsScInftyGermNear (rnChart 2 a1).model.E (Nsp ub) (fd _) (rnChart 2 a1).model.C univ δb v₀ := by
  rintro ⟨G, -, hsm⟩
  exact not_smoothGerm G hsm

/-- The point `x₀ = φ⁻¹(v₀ + δ(v₀))` (`= (0, 0)`) lies on `M`. -/
theorem x0_mem : (rnChart 2 a1).toPartialEquiv.symm ((v₀ : E2) + δb v₀) ∈ M := by
  obtain ⟨p, hp, hpe⟩ : (v₀ : E2) + δb v₀ ∈ (fun p => p - a1) '' M := by
    rw [image_bad]; exact ⟨v₀, rfl⟩
  have : (rnChart 2 a1).toPartialEquiv.symm ((v₀ : E2) + δb v₀) = p := by
    rw [← hpe]; show p - a1 + a1 = p; abel
  rw [this]; exact hp

/-- **`B` is false**: in the tame M-polyfold `ℝ²`, the curve `M = {(t³, t)}` has the
`1`-dimensional tangent germ property, and the data `(φ, ℝ(3, 1), ℝ(0, 1), ℝ(3, 1), δ)` at
`(1, 1)` satisfy Definition 3.25, but `δ` is not an sc^∞-germ near `v₀ = −(1/3)(3, 1)`. -/
theorem not_B1 : ¬ (∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
      (PX : MPolyfold X) (M : Set X) (n : ℕ),
      PX.IsTame → HasTangentGermPropertyB PX M n →
      ∀ (x : X) (φ : MChart X) (N Yc : Submodule ℝ (φ.model.E.lvl 0)) [FiniteDimensional ℝ N]
        (V : Set N) (δ : N → φ.model.E.lvl 0),
        IsGermData PX M n x φ N Yc V δ →
        ∀ v₀ ∈ V, IsScInftyGermNear φ.model.E N φ.model.C V δ v₀) := by
  intro h
  exact not_germNear (@h E2 _ _ _ (rnPolyfold 2) M 1 rnPolyfold_isTame hasTangentGermPropertyB_M
    a1 (rnChart 2 a1) (Nsp ub) (Nsp eb) (fd _) univ δb germData_bad v₀ (mem_univ _))

end CE

/-- **B is false**: for the curve `M = {(t³, t)}` in `ℝ²`, the datum at `(1, 1)` with vertical
complement, `v₀ = −(1/3)(3, 1)` and any datum at `x₀ = (0, 0)`, `δ` is not an sc^∞-germ near
`v₀`. -/
theorem not_B : ¬ B := by
  intro hB
  obtain ⟨ψ, N', Y', fd', V', τ, hd'⟩ := CE.hasTangentGermPropertyB_M.2 _ CE.x0_mem
  exact CE.not_germNear (@hB CE.E2 _ _ _ (rnPolyfold 2) CE.M 1 rnPolyfold_isTame
    CE.hasTangentGermPropertyB_M CE.a1 (rnChart 2 CE.a1) (CE.Nsp CE.ub) (CE.Nsp CE.eb) (CE.fd _)
    Set.univ CE.δb CE.germData_bad CE.v₀ (Set.mem_univ _) ψ N' Y' fd' V' τ hd').2.2

/-- `B → A`, ex falso (B is false). -/
theorem B_to_A : B → A := fun hB => (not_B hB).elim

#rt_check RoundTrip.V3_73.B_to_A [Polyfold.recentre_contDiffOn_levels,
  Polyfold.finrank_le_of_interior_image_nonempty, Polyfold.exists_contDiffOn_inverse,
  Polyfold.InvDataW.contDiffOn_inv, Polyfold.scDeriv_apply_toBase_deriv_eq_of_fixed]
#rt_check RoundTrip.V3_73.not_B [Polyfold.recentre_contDiffOn_levels,
  Polyfold.finrank_le_of_interior_image_nonempty, Polyfold.exists_contDiffOn_inverse,
  Polyfold.InvDataW.contDiffOn_inv, Polyfold.scDeriv_apply_toBase_deriv_eq_of_fixed]
#rt_overlap RoundTrip.V3_73.B_to_A [Polyfold.recentre_contDiffOn_levels,
  Polyfold.finrank_le_of_interior_image_nonempty, Polyfold.exists_contDiffOn_inverse,
  Polyfold.InvDataW.contDiffOn_inv, Polyfold.scDeriv_apply_toBase_deriv_eq_of_fixed]

end RoundTrip.V3_73
