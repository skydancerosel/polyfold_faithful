import Polyfold.Chapter3.Counterexamples2021
import Polyfold.Chapter3.NonVacuity

/-!
# The re-centring step of Theorem 3.2.3 read literally: a counterexample

The proof of 2021 Theorem 3.2.3, p. 107 (2017: Theorem 3.6; preprint: Theorem 3.27, p. 84),
shows that the chart `π ∘ φ` of a set `M` with the tangent germ property (2021 Definition 3.2.1,
p. 104; preprint 3.25) is compatible by re-centring: for data `(φ, N, Y, V, δ)` at `x ∈ M`, a point
`v₀ ∈ V` and data `(ψ, N', Y', V', τ)` at `x₀ = φ⁻¹(v₀ + δ(v₀))`, the map
`k(w) = π φ ψ⁻¹(w + τ(w))` is said to have an invertible linearization at `0`, so that `δ` is an
sc^∞-germ near **every** `v₀ ∈ V`.  Definition 3.2.1 controls `δ` only near `0`, and this step
**does not hold as we read it**.  The counter-model, machine-checked in the round trip
(`RoundTrip/Items/V3_73.lean` and `V3_74.lean`, `not_B`) and copied here into the library:

* `X = ℝ²` (`rnPolyfold 2`, tame), `M = {(t³, t) | t ∈ ℝ}`, a smooth embedded curve with vertical
  tangent at `(0, 0)`, which has the `1`-dimensional tangent germ property
  (`CE.hasTangentGermPropertyLit_M`: at `(t₀³, t₀)` the translation chart, `N = ℝ(3t₀², 1)`,
  `Y = ℝ(1, 0)`, `V = N`, `δ(s(3t₀², 1)) = (3t₀s² + s³, 0)`);
* the datum at `(1, 1)` with `N = ℝ(3, 1)`, `Y = ℝ(0, 1)` (vertical, tangent to `M` at `(0, 0)`),
  `V = N` and `δ(v) = (∛(1 + v₁) − 1 − v₁/3)(0, 1)` (`CE.germData_bad`): smooth near `0` with
  `Dδ(0) = 0`, but not differentiable at `v₀ = −(1/3)(3, 1)` (`CE.not_germNear`).

The notions are those of the round trip's literal reading (`IsGoodComplementLit`, `IsGermDataLit`,
`HasTangentGermPropertyLit`, `IsScInftyGermNear`): every clause of Definition 3.2.1 written out,
with the good complement of 2021 Definition 3.1.24 (p. 102; preprint 3.21) as an sc-complement.

## What is formalized

* `not_theorem_3_2_3_germNearEveryPoint`: the claim "`δ` is an sc^∞-germ near every
  `v₀ ∈ V`" of the proof of Theorem 3.2.3 (and of the proof of Theorem 3.6.8, preprint 3.54,
  which proceeds "as above"), for every datum of Definition 3.2.1 of a tame `X`, does not hold as
  we read it.  This certifies the literal step behind rows **V3.24** (added hypothesis (a) of
  `IsRegular`) and **V3.74** (Findings, Chapter 3, item 82).
* `not_theorem_3_2_3_recentreStep`: the re-centring step as stated in the proof (invertible
  linearization of `k`, local diffeomorphism, and `δ` regular near `v₀`, for every pair of data)
  does not hold as we read it.  This certifies row **V3.73**.

The project's corrected forms are `recentre_contDiffOn_levels` (V3.73: it assumes the first graph
map `C¹` on its whole domain) and `MPolyfold.TangentGermChart.exists_isRegular_of_locally` (V3.74:
regularity on shrunk data under condition (b)).
-/

open Set Filter Topology Function
open scoped ContDiff

noncomputable section

namespace Polyfold

namespace Recentre2021

/-- **2021 Definition 3.1.24, p. 102 (preprint Definition 3.21)**, the good complement read
literally: `P` is an sc-complement of `N` (a closed topological complement if `N` is not smooth)
with the `ε`-property. -/
def IsGoodComplementLit (E : ScBanach) (C : Set (E.lvl 0)) (N P : Submodule ℝ (E.lvl 0)) : Prop :=
  (N ≤ E.smooth → E.IsScSplitting N P) ∧
  (¬ N ≤ E.smooth → IsCompl N P ∧ IsClosed (P : Set (E.lvl 0))) ∧
  ∃ ε > (0 : ℝ), ∀ n ∈ N, ∀ p ∈ P, ‖p‖ ≤ ε * ‖n‖ → (n ∈ C ↔ n + p ∈ C)

/-- **2021 Definition 3.2.1 (2), p. 104 (preprint Definition 3.25 (2))**, read literally:
`(φ, N, Y, V, δ)` are data of the `n`-dimensional tangent germ property of `M` at `x`. -/
def IsGermDataLit {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (PX : MPolyfold X) (M : Set X) (n : ℕ) (x : X) (φ : MChart X)
    (N Yc : Submodule ℝ (φ.model.E.lvl 0)) [FiniteDimensional ℝ N] (V : Set N)
    (δ : N → φ.model.E.lvl 0) : Prop :=
  PX.IsChart φ ∧ x ∈ φ.source ∧ φ.toPartialEquiv x = 0 ∧
  IsTameRetract φ.model.E φ.model.C φ.model.O ∧
  Module.finrank ℝ N = n ∧ N ≤ φ.model.E.smooth ∧
  (interior ((Subtype.val : N → φ.model.E.lvl 0) ⁻¹' φ.model.C)).Nonempty ∧
  IsGoodComplementLit φ.model.E φ.model.C N Yc ∧
  (∃ O' : Set N, IsOpen O' ∧ V = O' ∩ (Subtype.val ⁻¹' φ.model.C)) ∧ (0 : N) ∈ V ∧
  (∀ v ∈ V, δ v ∈ Yc) ∧ ContinuousOn δ V ∧
  -- (i)
  φ.toPartialEquiv '' (M ∩ φ.source) = (fun v : N => (v : φ.model.E.lvl 0) + δ v) '' V ∧
  -- (ii)
  δ 0 = 0 ∧
  ∃ G : ScNbhdGerm (ScBanach.const N) ((Subtype.val : N → φ.model.E.lvl 0) ⁻¹' φ.model.C),
    (∀ v ∈ G.U 0, v ∈ V) ∧ IsScSmoothGerm (F := φ.model.E) G δ ∧
    ∃ D : (ScBanach.const N).lvl 1 → (ScBanach.const N).lvl 0 →L[ℝ] φ.model.E.lvl 0,
      IsSc1GermWith G δ D ∧ D 0 = 0

/-- **2021 Definition 3.2.1, p. 104 (preprint Definition 3.25)**, read literally: `M ⊆ X` has the
`n`-dimensional tangent germ property. -/
def HasTangentGermPropertyLit {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (PX : MPolyfold X) (M : Set X) (n : ℕ) : Prop :=
  M ⊆ PX.smoothSet ∧
  ∀ x ∈ M, ∃ (φ : MChart X) (N Yc : Submodule ℝ (φ.model.E.lvl 0)) (_ : FiniteDimensional ℝ N)
    (V : Set N) (δ : N → φ.model.E.lvl 0), IsGermDataLit PX M n x φ N Yc V δ

/-- The projection `π : E → N` along `Y`: the `v ∈ N` with `z − v ∈ Y` (junk `0` if none). -/
noncomputable def projN {E : Type} [AddCommGroup E] [Module ℝ E] (N Yc : Submodule ℝ E) (z : E) :
    N := by
  classical
  exact if h : ∃ v : N, z - (v : E) ∈ Yc then h.choose else 0

/-- The re-centring map `k(w) = π φ ψ⁻¹(w + τ(w))`, `N' → N`. -/
noncomputable def kmap {X : Type} [TopologicalSpace X] (φ ψ : MChart X)
    (N Yc : Submodule ℝ (φ.model.E.lvl 0)) (N' : Submodule ℝ (ψ.model.E.lvl 0))
    (τ : N' → ψ.model.E.lvl 0) (w : N') : N :=
  projN N Yc (φ.toPartialEquiv (ψ.toPartialEquiv.symm ((w : ψ.model.E.lvl 0) + τ w)))

/-- `δ` is an sc^∞-germ near `v₀`: the translated germ `w ↦ δ(v₀ + w)` is an sc-smooth germ
(2021 Definition 3.1.2; preprint 3.2) on a germ of neighbourhoods of `0` in
`{w | v₀ + w ∈ N ∩ C}` inside `V − v₀`. -/
def IsScInftyGermNear (E : ScBanach) (N : Submodule ℝ (E.lvl 0)) [FiniteDimensional ℝ N]
    (C : Set (E.lvl 0)) (V : Set N) (δ : N → E.lvl 0) (v₀ : N) : Prop :=
  ∃ G : ScNbhdGerm (ScBanach.const N) {w : N | ((v₀ + w : N) : E.lvl 0) ∈ C},
    (∀ w : N, w ∈ G.U 0 → v₀ + w ∈ V) ∧
    IsScSmoothGerm (F := E) G (fun w : N => δ (v₀ + w))

/-- **The re-centring step of the proof of 2021 Theorem 3.2.3, p. 107 (preprint Theorem 3.27,
p. 84)**, read literally: for data `(φ, N, Y, V, δ)` at `x ∈ M`, `v₀ ∈ V`
and data `(ψ, N', Y', V', τ)` at `x₀ = φ⁻¹(v₀ + δ(v₀))`, the map `k(w) = πφψ⁻¹(w + τ(w))` has an
invertible linearization at `0`, is a local diffeomorphism near `0 ↦ v₀`, and `δ` is an
sc^∞-germ near `v₀`. -/
def Theorem_3_2_3_RecentreStep : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    (M : Set X) (n : ℕ),
    PX.IsTame → HasTangentGermPropertyLit PX M n →
    ∀ (x : X) (φ : MChart X) (N Yc : Submodule ℝ (φ.model.E.lvl 0)) [FiniteDimensional ℝ N]
      (V : Set N) (δ : N → φ.model.E.lvl 0),
      IsGermDataLit PX M n x φ N Yc V δ →
    ∀ v₀ ∈ V,
    ∀ (ψ : MChart X) (N' Y' : Submodule ℝ (ψ.model.E.lvl 0)) [FiniteDimensional ℝ N']
      (V' : Set N') (τ : N' → ψ.model.E.lvl 0),
      IsGermDataLit PX M n (φ.toPartialEquiv.symm ((v₀ : φ.model.E.lvl 0) + δ v₀)) ψ N' Y' V' τ →
      -- invertible linearization at `0`
      (∃ Λ : N' ≃L[ℝ] N, HasFDerivWithinAt (kmap φ ψ N Yc N' τ) (Λ : N' →L[ℝ] N) V' 0) ∧
      -- local diffeomorphism `(W', 0) → (W, v₀)`
      (∃ (W' : Set N') (W : Set N) (κ : N → N'),
        (∃ O' : Set N', IsOpen O' ∧ W' = O' ∩ (Subtype.val ⁻¹' ψ.model.C)) ∧
        (0 : N') ∈ W' ∧ W' ⊆ V' ∧
        (∀ w ∈ W', ψ.toPartialEquiv.symm ((w : ψ.model.E.lvl 0) + τ w) ∈ φ.source) ∧
        (∃ O : Set N, IsOpen O ∧ W = O ∩ (Subtype.val ⁻¹' φ.model.C)) ∧
        v₀ ∈ W ∧ W ⊆ V ∧
        Set.BijOn (kmap φ ψ N Yc N' τ) W' W ∧ Set.InvOn κ (kmap φ ψ N Yc N' τ) W' W ∧
        ContDiffOn ℝ 1 (kmap φ ψ N Yc N' τ) W' ∧ ContDiffOn ℝ 1 κ W ∧
        ∀ ℓ : ℕ,
          (∃ A' : Set N', (∃ O' : Set N', IsOpen O' ∧ A' = O' ∩ W') ∧ (0 : N') ∈ A' ∧
            ContDiffOn ℝ ℓ (kmap φ ψ N Yc N' τ) A') ∧
          (∃ A : Set N, (∃ O : Set N, IsOpen O ∧ A = O ∩ W) ∧ v₀ ∈ A ∧ ContDiffOn ℝ ℓ κ A)) ∧
      -- `δ` is an sc^∞-germ (regular) near `v₀`
      IsScInftyGermNear φ.model.E N φ.model.C V δ v₀


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
  have h1 : Continuous fun x : ℝ => x ^ ((3 : ℕ) : ℝ)⁻¹ :=
    Real.continuous_rpow_const (by positivity)
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

/-- Data of Definition 3.2.1 (2) (preprint 3.25 (2)) in the literal reading, in a translation
chart of `ℝ²`, from a
transversal pair of lines `ℝu`, `ℝe` and a map `δ` that is smooth near `0` with `Dδ(0) = 0`. -/
theorem isGermData_mk (a u e : E2) (hu : u ≠ 0) (hdet : u 0 * e 1 - u 1 * e 0 ≠ 0)
    (δ : Nsp u → E2) (U : Set (Nsp u)) (hUo : IsOpen U) (h0U : (0 : Nsp u) ∈ U)
    (hδY : ∀ v, δ v ∈ Nsp e) (hcont : Continuous δ) (hsm : ContDiffOn ℝ ∞ δ U)
    (hd0 : HasFDerivAt δ (0 : Nsp u →L[ℝ] E2) 0) (hδ0 : δ 0 = 0)
    (himg : (fun p => p - a) '' M = range (fun v : Nsp u => (v : E2) + δ v)) :
    @IsGermDataLit _ _ _ _ (rnPolyfold 2) M 1 a (rnChart 2 a) (Nsp u) (Nsp e) (fd u) univ δ := by
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
    simp only [ContinuousLinearMap.comp_apply, zero_apply] at this
    rwa [ScBanach.const_toBase] at this
  have hgc : IsGoodComplementLit (ScBanach.const E2) univ (Nsp u) (Nsp e) :=
    ⟨fun _ => Counterexamples2021.isScSplitting_const _ _ _
      (Counterexamples2021.isCompl_span_pair u e hdet),
      fun h => absurd (Counterexamples2021.le_smooth_const _ _) h, 1, one_pos,
      fun _ _ _ _ _ => iff_of_true (mem_univ _) (mem_univ _)⟩
  have hint : (interior (univ : Set (Nsp u))).Nonempty := by
    rw [interior_univ]; exact univ_nonempty
  have himg' : (fun p => p - a) '' (M ∩ univ) = (fun v : Nsp u => (v : E2) + δ v) '' univ := by
    rw [inter_univ, image_univ, himg]
  exact ⟨isChart_rnChart a, mem_univ a, sub_self a,
    ⟨ScRetraction.id (rn_relOpen_univ 2), image_id _, ScRetraction.id_isTame _⟩,
    finrank_span_singleton hu, Counterexamples2021.le_smooth_const _ _, hint, hgc,
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
    @IsGermDataLit _ _ _ _ (rnPolyfold 2) M 1 x (rnChart 2 x) (Nsp (uf (x 1))) (Nsp e0) (fd _) univ
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
    change (x + ((v : E2) + δf (x 1) v)) 0 = ((x + ((v : E2) + δf (x 1) v)) 1) ^ 3
    simp only [δf, hc, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← hs]
    simp [uf, e0, hx']
    ring

theorem hasTangentGermPropertyLit_M : HasTangentGermPropertyLit (rnPolyfold 2) M 1 :=
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
    change (a1 + ((v : E2) + δb v)) 0 = ((a1 + ((v : E2) + δb v)) 1) ^ 3
    simp only [δb, hc, gb, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← hs]
    simp only [a1, ub, eb, Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero,
      add_zero, mul_one]
    have : (1 + (s + (cbrt (1 + 3 * s) - 1 - 3 * s / 3))) = cbrt (1 + 3 * s) := by ring
    rw [this, cbrt_cube]
    ring


theorem germData_bad :
    @IsGermDataLit _ _ _ _ (rnPolyfold 2) M 1 a1 (rnChart 2 a1) (Nsp ub) (Nsp eb) (fd _) univ
      δb := by
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
    ¬ @IsScInftyGermNear (rnChart 2 a1).model.E (Nsp ub) (fd _) (rnChart 2 a1).model.C univ δb
      v₀ := by
  rintro ⟨G, -, hsm⟩
  exact not_smoothGerm G hsm

/-- The point `x₀ = φ⁻¹(v₀ + δ(v₀))` (`= (0, 0)`) lies on `M`. -/
theorem x0_mem : (rnChart 2 a1).toPartialEquiv.symm ((v₀ : E2) + δb v₀) ∈ M := by
  obtain ⟨p, hp, hpe⟩ : (v₀ : E2) + δb v₀ ∈ (fun p => p - a1) '' M := by
    rw [image_bad]; exact ⟨v₀, rfl⟩
  have : (rnChart 2 a1).toPartialEquiv.symm ((v₀ : E2) + δb v₀) = p := by
    rw [← hpe]; change p - a1 + a1 = p; abel
  rw [this]; exact hp

end CE

/-- **The claim "`δ` is an sc^∞-germ near every `v₀ ∈ V`"** of the proof of 2021 Theorem 3.2.3,
p. 107 (preprint Theorem 3.27, p. 84), read literally: for every set `M` with the tangent germ
property in a tame `X`, every datum `(φ, N, Y, V, δ)` of Definition 3.2.1 at a point of `M`, and
every `v₀ ∈ V`. -/
def Theorem_3_2_3_GermNearEveryPoint : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (PX : MPolyfold X) (M : Set X) (n : ℕ),
    PX.IsTame → HasTangentGermPropertyLit PX M n →
    ∀ (x : X) (φ : MChart X) (N Yc : Submodule ℝ (φ.model.E.lvl 0)) [FiniteDimensional ℝ N]
      (V : Set N) (δ : N → φ.model.E.lvl 0),
      IsGermDataLit PX M n x φ N Yc V δ →
      ∀ v₀ ∈ V, IsScInftyGermNear φ.model.E N φ.model.C V δ v₀

/-- **The step "`δ` is an sc^∞-germ near every `v₀ ∈ V`" of the proof of 2021 Theorem 3.2.3,
p. 107 (preprint Theorem 3.27, p. 84), does not hold as we read it** (rows V3.24, V3.74): in the
tame M-polyfold `ℝ²`, the curve `M = {(t³, t)}` has the `1`-dimensional tangent germ property, and
the data `(φ, ℝ(3, 1), ℝ(0, 1), ℝ(3, 1), δ)` at `(1, 1)` satisfy Definition 3.2.1, but `δ` is not
an sc^∞-germ near `v₀ = −(1/3)(3, 1)`. -/
theorem not_theorem_3_2_3_germNearEveryPoint : ¬ Theorem_3_2_3_GermNearEveryPoint := by
  intro h
  exact CE.not_germNear (@h CE.E2 _ _ _ (rnPolyfold 2) CE.M 1 rnPolyfold_isTame
    CE.hasTangentGermPropertyLit_M CE.a1 (rnChart 2 CE.a1) (CE.Nsp CE.ub) (CE.Nsp CE.eb) (CE.fd _)
    univ CE.δb CE.germData_bad CE.v₀ (mem_univ _))

/-- **The re-centring step of the proof of 2021 Theorem 3.2.3, p. 107 (preprint Theorem 3.27,
p. 84), does not hold as we read it** (row V3.73): for the curve `M = {(t³, t)}` in `ℝ²`, the
datum at `(1, 1)` with vertical complement, `v₀ = −(1/3)(3, 1)` and any datum at
`x₀ = φ⁻¹(v₀ + δ(v₀)) = (0, 0)` (one exists by the tangent germ property), `δ` is not an
sc^∞-germ near `v₀`. -/
theorem not_theorem_3_2_3_recentreStep : ¬ Theorem_3_2_3_RecentreStep := by
  intro hB
  obtain ⟨ψ, N', Y', fd', V', τ, hd'⟩ := CE.hasTangentGermPropertyLit_M.2 _ CE.x0_mem
  exact CE.not_germNear (@hB CE.E2 _ _ _ (rnPolyfold 2) CE.M 1 rnPolyfold_isTame
    CE.hasTangentGermPropertyLit_M CE.a1 (rnChart 2 CE.a1) (CE.Nsp CE.ub) (CE.Nsp CE.eb) (CE.fd _)
    univ CE.δb CE.germData_bad CE.v₀ (mem_univ _) ψ N' Y' fd' V' τ hd').2.2

end Recentre2021

end Polyfold
