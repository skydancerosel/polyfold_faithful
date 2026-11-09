import Polyfold.Chapter9.BoundaryPosition
import Polyfold.Chapter3.TameGermData

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.2 "The Tangent and Boundary of `Θ`": the direction (2) ⇒ (1) of
**Lemma 9.2.13** and the direction "`x ∈ ∂M` ⇒ `T_xM ⊄ T_x^R X`" of **Remark 9.2.14** (2021
Lemma 9.2.13 and Remark 9.2.14, p. 419, proof pp. 419–420; 2017: Lemma 9.9 and Remark 9.5,
p. 307).  Numbers and pages are the 2021 text's, the 2017 ones in parentheses.  The other
directions are in `Polyfold.Chapter9.BoundaryPosition`.

# A submanifold with reduced tangent space has degeneracy index zero

## The text, paraphrased

(Lemma 9.2.13) For a finite-dimensional submanifold `M` of an M-polyfold `X`, (1) `x ∈ M ∩ ∂X`
with `d_M(x) = 0` and (2) `T_xM ⊆ T_x^R X` are equivalent.  (Remark 9.2.14) So `x ∈ ∂M` iff
`x ∈ ∂X` and `T_xM ⊄ T_x^R X`.  *Proof of (2) ⇒ (1)* (text): locally `X = O`, `x = 0`,
`C = [0,∞)ᵏ ⊕ W`, and `M = s(U)` for an sc⁺-retraction `s`.  As `T_0M ⊆ {0} ⊕ W`, `s` is
defined on small vectors of `T_0M`, `s(h) = h + A(h)` with `A(0) = 0`, `DA(0) = 0`.  For the
projection `P` onto `T_0M` along a complement `Y`, `Ψ = 1 + PA` has `DΨ(0) = 1`; put
`s̃ = s ∘ Ψ⁻¹`.  The map `(h, y) ↦ s̃(h) + y` is a local sc-diffeomorphism of `T_0M × Y` near `0`;
with its inverse `F`, `s̃ ∘ P ∘ F` is an sc⁺-retraction of an open subset of `E` with image `M`
near `0`, so `M` near `0` is an sc⁺-retract in `E` with `C = E`, and `d_M(0) = 0`.

## What is formalized

* **Lemma 9.2.13, (2) ⇒ `d_M(x) = 0`, at every `x ∈ M`**:
  `MPolyfold.subDegIndex_eq_zero_of_isTangentReducedAt`.  The direction as printed, read for
  `x ∈ M ∩ ∂X`: `MPolyfold.lemma_9_2_13_two_one`.  The lemma at a point of `M ∩ ∂X`:
  `MPolyfold.lemma_9_2_13_iff`; at every point of `M` (`d_M(x) = 0 ⟺ T_xM ⊆ T_x^R X`):
  `MPolyfold.subDegIndex_eq_zero_iff`.
* **Remark 9.2.14**: `MPolyfold.remark_9_2_14_not_isTangentReducedAt` (`x ∈ ∂M` gives `x ∈ ∂X`
  and `T_xM ⊄ T_x^R X`), the reformulation `MPolyfold.remark_9_2_14_iff`
  (`x ∈ ∂M ⟺ x ∈ ∂X ∧ T_xM ⊄ T_x^R X`), and `MPolyfold.remark_9_2_14_not_mem_boundary_iff`
  (for `x ∈ M ∩ ∂X`: `x ∉ ∂M ⟺ T_xM ⊆ T_x^R X`).
* In charts: `MPolyfold.degIndex_eq_zero_of_isReducedTangentAt` (a point of an M-polyfold whose
  chart model is an sc⁺-retract `O` with `T_zO ⊆ E_z` has degeneracy index `0`), from
  `ScRetraction.IsScPlus.exists_flat` (the new chart) and
  `ScRetraction.IsScPlus.exists_injOn_proj` (the step "image `M` near `0`").
* Auxiliary: `smoothLiftL`, `ScRetraction.IsScPlus.range_scDeriv_le_smooth` (`T_zO ⊆ E_∞` for
  an sc⁺-retract), `ScRetraction.exists_ball_add_mem_U`, `ScRetraction.contDiffOn_lvl_add`,
  `ScRetraction.toBase_levelMap_add`, `ScRetraction.hasFDerivAt_add`.

## What the text leaves implicit, and the choices made

* The hypothesis `x ∈ ∂X` is not used: (2) gives `d_M(x) = 0` at every point of `M`; only the
  clause `x ∈ ∂X` of (1) needs it (`not_lemma_9_2_13_two_one`).
* `T_xM ⊆ T_x^R X` is `MPolyfold.IsTangentReducedAt` (in some chart; chart independent) and
  `d_M` is `MPolyfold.subDegIndex`, as in `BoundaryPosition`.  In the chart of `M` induced by a
  chart `φ` of `X` the model `φ(W ∩ M)` is an sc⁺-retract (`isScPlusRetract_image`) in the
  partial quadrant of `φ`.
* The text's `x = 0` with `C = [0,∞)ᵏ ⊕ W` is here a level-`1` point `z` of the model and a
  presentation `C = T⁻¹([0,∞)ⁿ ⊕ W)`; `T_zM ⊆ E_z` gives `z + h ∈ U` for small `h ∈ T_zM`
  (`exists_ball_add_mem_U`: vanishing coordinates stay `0`, positive ones stay positive).
* Instead of the retraction `s̃ ∘ P ∘ F` of an open subset of `E`, the proof builds a chart of
  `M` modelled on an open subset `V` of `N = T_zM` itself (local model `(V, N, N)`, no
  boundary): `χ(u) = p(u) − p(z)` on `M ∩ G`, with inverse `Γ = s ∘ (z + ·) ∘ Ψ⁻¹`,
  `Ψ(h) = p(s(z + h)) − p(z)`.  The complement `Y` and the map `F` are not needed.  The new
  chart belongs to the induced atlas by `MChart.compRetract_isChart`, and its degeneracy index
  is `0` by `TrivialBundle.univ_degIndex_eq_zero`; this is the step "this implies `d_M(0) = 0`".
* **"has image `M` (near `0`)"** is supplied by `exists_injOn_proj`: `p` is injective on `M`
  near `z`.  For `u, u' ∈ M` near `z` with `p u = p u'`, `w = u' − u` on level `1` satisfies
  `(1 − p)w = w` and `(1 − p) Ds(z) w = 0`, so the mean value estimate of the sc⁺-retraction
  (`exists_mvt`, the estimate of Lemma 4.11 at `z`) gives `‖w‖₁ ≤ ‖1 − p‖ θ ‖w‖₁ ≤ ½ ‖w‖₁`;
  level-`1` closeness to `z` is the continuity of `s : U → E₁`.  As `Γ(χ(u))` and `u` have the
  same projection, `Γ(χ(u)) = u`, so `Γ(V) = M ∩ G`.
* "`Ψ` is classically smooth": `T_zM ⊆ E_∞` (`range_scDeriv_le_smooth`: `Ds(z)` is sc⁺ and the
  identity on its range), so `h ↦ s(z + h)` is `C^∞` on every level along continuous lifts
  `N → E_m` (Proposition 1.18).  `Ψ⁻¹` comes from Mathlib's inverse function theorem in the
  finite-dimensional `N` and is `C^∞` where `DΨ` is invertible; `Γ` is sc-smooth by
  Proposition 1.19.  The text's sc-projection `P` is any continuous projection `p : E → N`;
  `χ` is sc-smooth since `N` is finite-dimensional.

## Not formalized

* A witness at a boundary point: the hypotheses of `lemma_9_2_13_two_one` (`x ∈ M ∩ ∂X` and
  `T_xM ⊆ T_x^R X`, e.g. `M = {0}` in `[0, ∞)`) are not exhibited, for want of a smooth-set and
  submanifold API for `quadrantPolyfold`.  The hypothesis of
  `subDegIndex_eq_zero_of_isTangentReducedAt` is satisfied by the points of `ℝⁿ`
  (`not_lemma_9_2_13_two_one`; the `example` at the end of this file).
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Function Metric Module
open scoped ContDiff

noncomputable section

namespace Polyfold

section Analytic

variable {E : ScBanach} {C : Set (E 0)} {n : ℕ} {W : ScBanach}

/-- The continuous lift `N → E_m` of a finite-dimensional smooth subspace `N ⊆ E_∞`. -/
def smoothLiftL {N : Submodule ℝ (E 0)} [FiniteDimensional ℝ N] (hN : N ≤ E.smooth) (m : ℕ) :
    N →L[ℝ] E m :=
  LinearMap.toContinuousLinearMap (finSmoothLift hN m)

@[simp] lemma toBase_smoothLiftL {N : Submodule ℝ (E 0)} [FiniteDimensional ℝ N]
    (hN : N ≤ E.smooth) (m : ℕ) (v : N) : E.toBase m (smoothLiftL hN m v) = v :=
  toBase_finSmoothLift hN m v

/-- The tangent space `T_zO = Dt(z)E` of an sc⁺-retract at a point of `O` is a smooth subspace
(`Dt(z)` is an sc⁺-operator at the smooth point `z`, Lemma 4.7). -/
theorem ScRetraction.IsScPlus.range_scDeriv_le_smooth {t : ScRetraction E C} (ht : t.IsScPlus)
    {z : E 1} (hz : E.toBase 1 z ∈ t.retract) :
    LinearMap.range (scDeriv t.U t z : E 0 →ₗ[ℝ] E 0) ≤ E.smooth := by
  have hzU : z ∈ E.lvlSet t.U 1 := t.retract_subset hz
  have hs : z ∈ E.smoothLvl 1 := lemma_4_1_7_i ht hz
  obtain ⟨S, hS⟩ := ht.exists_scPlus_deriv t.isScDomain hzU hs
  intro v hv
  have hfix : scDeriv t.U t z v = v := by
    obtain ⟨u, rfl⟩ := hv
    exact congrArg (fun L : E 0 →L[ℝ] E 0 => L u) (t.scDeriv_comp_self hz)
  rw [ScScale.mem_smooth_iff]
  intro m
  induction m with
  | zero => exact ⟨v, rfl⟩
  | succ m ih =>
    obtain ⟨y, hy⟩ := ih
    have := (S.isScPlus (isScDomain_univ E)).mem_range_succ m (x := y) (mem_univ _)
    rw [hy, hS, hfix] at this
    exact this

/-- For `e ∈ U ⊆ C` and a subspace `N ⊆ E_e`, the points `e + h`, `h ∈ N` small, lie in `U`: the
coordinates vanishing at `e` vanish along `N`, the others stay positive. -/
theorem ScRetraction.exists_ball_add_mem_U (t : ScRetraction E C)
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (hT : C = T 0 ⁻¹' quadrant n W 0)
    {e : E 0} (he : e ∈ t.U) {N : Submodule ℝ (E 0)} (hN : N ≤ minimalSubspaceWith T e) :
    ∃ δ > 0, ∀ h : N, ‖h‖ < δ → e + (h : E 0) ∈ t.U := by
  obtain ⟨O, hO, hUO⟩ := t.relOpen.relOpen
  have he' : e ∈ O ∩ C := hUO ▸ he
  have heC : T 0 e ∈ quadrant n W 0 := by have := he'.2; rwa [hT] at this
  have hcont : Continuous fun h : N => e + (h : E 0) := continuous_const.add continuous_subtype_val
  have hlim : Tendsto (fun h : N => e + (h : E 0)) (𝓝 0) (𝓝 e) := by
    simpa using hcont.tendsto 0
  have h1 : ∀ᶠ h : N in 𝓝 0, e + (h : E 0) ∈ O := hlim.eventually (hO.mem_nhds he'.1)
  have h2 : ∀ i : Fin n, ∀ᶠ h : N in 𝓝 0, 0 ≤ (T 0 (e + (h : E 0))).1 i := by
    intro i
    have heq : ∀ h : N, (T 0 (e + (h : E 0))).1 i = (T 0 e).1 i + (T 0 h).1 i := fun h => by
      simp only [map_add, Prod.fst_add, Pi.add_apply]
    by_cases hi : (T 0 e).1 i = 0
    · exact Eventually.of_forall fun h => by
        rw [heq, hi, (mem_minimalSubspaceWith T).1 (hN h.2) i hi, add_zero]
    · have hpos : 0 < (T 0 e).1 i := lt_of_le_of_ne (heC i) (Ne.symm hi)
      have hc : Continuous fun h : N => (T 0 (e + (h : E 0))).1 i :=
        (continuous_apply i).comp (continuous_fst.comp ((T 0).continuous.comp hcont))
      have hl : Tendsto (fun h : N => (T 0 (e + (h : E 0))).1 i) (𝓝 0) (𝓝 ((T 0 e).1 i)) := by
        simpa using hc.tendsto 0
      exact (hl.eventually (lt_mem_nhds hpos)).mono fun h hh => hh.le
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (h1.and (eventually_all.2 h2))
  refine ⟨δ, hδ, fun h hh => ?_⟩
  obtain ⟨hO', hC'⟩ := hball (show dist h 0 < δ by rwa [dist_zero_right])
  rw [hUO]
  exact ⟨hO', by rw [hT]; exact fun i => hC' i⟩

/-- **The restriction of `t` to the affine space `e + N` is `C^∞` into every level**: for a
smooth `e` (lifts `e_m ∈ E_m`) and a finite-dimensional smooth subspace `N`, on a set `B ⊆ N`
with `e + B ⊆ U`, `h ↦ t(e + h) ∈ E_m` is `C^∞` (Proposition 1.18, `t : U_{m+k} → E_m` is
`C^k`, composed with the affine lift `N → E_{m+k}`). -/
theorem ScRetraction.contDiffOn_lvl_add (t : ScRetraction E C) {N : Submodule ℝ (E 0)}
    [FiniteDimensional ℝ N] (hNs : N ≤ E.smooth) {e : E 0} (eL : ∀ m, E m)
    (heL : ∀ m, E.toBase m (eL m) = e) {B : Set N} (hB : ∀ h ∈ B, e + (h : E 0) ∈ t.U)
    (m : ℕ) :
    ContDiffOn ℝ ∞ (fun h : N => levelMap t m (eL m + smoothLiftL hNs m h)) B := by
  rw [contDiffOn_infty]
  intro k
  have h1 := t.isScSmooth.contDiffOn_levels t.isScDomain m k
  have hA : ContDiff ℝ k (fun h : N => eL (m + k) + smoothLiftL hNs (m + k) h) :=
    contDiff_const.add (smoothLiftL hNs (m + k)).contDiff
  have hmaps : MapsTo (fun h : N => eL (m + k) + smoothLiftL hNs (m + k) h) B
      (E.lvlSet t.U (m + k)) := fun h hh => by
    rw [ScBanach.mem_lvlSet, map_add, heL, toBase_smoothLiftL]
    exact hB h hh
  refine (h1.comp hA.contDiffOn hmaps).congr fun h _ => ?_
  simp only [Function.comp_apply]
  congr 1
  apply E.toBase_injective m
  rw [E.toBase_inclK, map_add, map_add, heL, heL, toBase_smoothLiftL, toBase_smoothLiftL]

/-- The level-`m` values of `h ↦ t(e + h)` lie over `t(e + h)`. -/
theorem ScRetraction.toBase_levelMap_add (t : ScRetraction E C) {N : Submodule ℝ (E 0)}
    [FiniteDimensional ℝ N] (hNs : N ≤ E.smooth) {e : E 0} (eL : ∀ m, E m)
    (heL : ∀ m, E.toBase m (eL m) = e) {h : N} (hh : e + (h : E 0) ∈ t.U) (m : ℕ) :
    E.toBase m (levelMap t m (eL m + smoothLiftL hNs m h)) = t (e + h) := by
  have hx : eL m + smoothLiftL hNs m h ∈ E.lvlSet t.U m := by
    rw [ScBanach.mem_lvlSet, map_add, heL, toBase_smoothLiftL]; exact hh
  rw [t.isSc1.isSc0.toBase_levelMap hx, map_add, heL, toBase_smoothLiftL]

/-- **The derivative of `h ↦ t(e + h)` at `0`** is `Dt(z)|_N` (`e = ι₁ z`): Definition 1.14 (2)
at `z`, composed with the affine lift `h ↦ z + h` into `E₁`. -/
theorem ScRetraction.hasFDerivAt_add (t : ScRetraction E C) {N : Submodule ℝ (E 0)}
    [FiniteDimensional ℝ N] (hNs : N ≤ E.smooth) {z : E 1} (hzU : z ∈ E.lvlSet t.U 1)
    {B : Set N} (hB : B ∈ 𝓝 (0 : N)) (hBU : ∀ h ∈ B, E.toBase 1 z + (h : E 0) ∈ t.U) :
    HasFDerivAt (fun h : N => t (E.toBase 1 z + h)) ((scDeriv t.U t z).comp N.subtypeL) 0 := by
  have hD := t.isSc1.isSc1With_scDeriv.hasFDerivWithinAt z hzU
  set A : N → E 1 := fun h => z + smoothLiftL hNs 1 h with hAdef
  have hA : HasFDerivWithinAt A (smoothLiftL hNs 1) B 0 :=
    ((smoothLiftL hNs 1).hasFDerivAt.const_add z).hasFDerivWithinAt
  have hA0 : A 0 = z := by simp [hAdef]
  have hmaps : MapsTo A B (E.lvlSet t.U 1) := fun h hh => by
    rw [ScBanach.mem_lvlSet, hAdef]
    simp only [map_add, toBase_smoothLiftL]
    exact hBU h hh
  rw [← hA0] at hD
  have h2 := (hD.comp (0 : N) hA hmaps).hasFDerivAt hB
  have hfun : (fun h : N => t (E.toBase 1 z + h)) = (t ∘ E.toBase 1) ∘ A := by
    funext h
    simp [hAdef, map_add]
  have hL : (scDeriv t.U t z).comp N.subtypeL =
      ((scDeriv t.U t (A 0)).comp (E.toBase 1)).comp (smoothLiftL hNs 1) := by
    rw [hA0]
    ext h
    simp
  rw [hfun, hL]
  exact h2

/-- **Local injectivity of the projection on an sc⁺-retract** (the step "image `M` near `0`",
the level-`1` contraction of Lemma 4.11 at the point `z` instead of `0`): for `N = Dt(z)E` and a
continuous projection `p : E → N`, there is an open `G ∋ ι₁ z` such that two points of `O ∩ G`
with the same projection coincide.  On level `1`, `w = u' − u` satisfies `(1 − p)w = w` and
`(1 − p)Dt(z)w = 0`, so `‖w‖₁ ≤ ‖1 − p‖ ‖w − Dt(z)w‖₁ ≤ ‖1 − p‖θ‖w‖₁` by the mean value estimate;
the level-`1` control of `O ∩ G` is the continuity of `t : U → E₁` (the sc⁺ property). -/
theorem ScRetraction.IsScPlus.exists_injOn_proj {t : ScRetraction E C} (ht : t.IsScPlus)
    {z : E 1} (hz : E.toBase 1 z ∈ t.retract) {N : Submodule ℝ (E 0)} [FiniteDimensional ℝ N]
    (hNs : N ≤ E.smooth) (hN : N = LinearMap.range (scDeriv t.U t z : E 0 →ₗ[ℝ] E 0))
    (p : E 0 →L[ℝ] N) (hp : ∀ v : N, p v = v) :
    ∃ G : Set (E 0), IsOpen G ∧ E.toBase 1 z ∈ G ∧
      ∀ u ∈ t.retract ∩ G, ∀ u' ∈ t.retract ∩ G, p u = p u' → u = u' := by
  have hzU : z ∈ E.lvlSet t.U 1 := t.retract_subset hz
  set L1 := smoothLiftL hNs 1 with hL1
  set q : E 1 →L[ℝ] E 1 := ContinuousLinearMap.id ℝ (E 1) - L1.comp (p.comp (E.toBase 1)) with hq
  set K := ‖q‖ with hK
  have hK0 : 0 ≤ K := norm_nonneg _
  set θ : ℝ := 1 / (2 * (K + 1)) with hθdef
  have hθ : 0 < θ := by positivity
  have hKθ : K * θ ≤ 1 / 2 := by
    rw [hθdef, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨r, hr, -, -, hmvt⟩ := ht.exists_mvt 0 (u₀ := z) hzU hθ
  have hcont : ContinuousOn t.liftOne t.U := ht.isScSmooth_liftOne.isSc1.isSc0.continuousOn_base
  have heU : E.toBase 1 z ∈ t.U := hzU
  obtain ⟨δ₀, hδ₀, hδ₀'⟩ := Metric.continuousWithinAt_iff.1 (hcont _ heU) r hr
  have hlz : t.liftOne (E.toBase 1 z) = z := by
    change E.liftOne (t (E.toBase 1 z)) = z
    rw [t.apply_eq_self_of_mem_retract hz, E.liftOne_toBase]
  refine ⟨ball (E.toBase 1 z) δ₀, isOpen_ball, mem_ball_self hδ₀, ?_⟩
  have key : ∀ u ∈ t.retract ∩ ball (E.toBase 1 z) δ₀,
      E.toBase 1 (t.liftOne u) = u ∧ t.liftOne u ∈ E.lvlSet C 1 ∧ ‖t.liftOne u - z‖ < r ∧
        t.lvlMap 0 (t.liftOne u) = t.liftOne u := by
    rintro u ⟨huO, huB⟩
    have huU := t.retract_subset huO
    have h1 : E.toBase 1 (t.liftOne u) = u := by
      change E.toBase 1 (E.liftOne (t u)) = u
      rw [ht.toBase_lift huU, t.apply_eq_self_of_mem_retract huO]
    refine ⟨h1, ?_, ?_, ?_⟩
    · have h1' : E.toBase 1 (t.liftOne u) ∈ t.U := by rw [h1]; exact huU
      exact t.lvlSet_U_subset_lvlSet_C 1 h1'
    · have := hδ₀' huU huB
      rwa [hlz, dist_eq_norm] at this
    · exact ht.lvlMap_eq_self 0 (by rw [h1]; exact huO)
  intro u hu u' hu' hpu
  obtain ⟨h1, hC1, hr1, hfix1⟩ := key u hu
  obtain ⟨h1', hC1', hr1', hfix1'⟩ := key u' hu'
  set w := t.liftOne u' - t.liftOne u with hw
  have hm := hmvt _ hC1 _ hC1' hr1 hr1'
  rw [hfix1, hfix1'] at hm
  have hqw : q w = w := by
    have hpw : p (E.toBase 1 w) = 0 := by rw [hw, map_sub, h1, h1', map_sub, hpu, sub_self]
    simp [hq, hpw]
  have hqD : q (t.lvlDeriv 0 z w) = 0 := by
    have hDw : E.toBase 1 (t.lvlDeriv 0 z w) = scDeriv t.U t z (E.toBase 1 w) :=
      ht.toBase_lvlDeriv 0 hzU w
    have hmem : E.toBase 1 (t.lvlDeriv 0 z w) ∈ N := by
      rw [hDw, hN]; exact ⟨_, rfl⟩
    have hL : L1 (p (E.toBase 1 (t.lvlDeriv 0 z w))) = t.lvlDeriv 0 z w := by
      apply E.toBase_injective 1
      rw [hL1, toBase_smoothLiftL, hp ⟨_, hmem⟩]
    simp only [hq, sub_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply]
    rw [hL, sub_self]
  have hle : ‖w‖ ≤ K * θ * ‖w‖ := by
    calc ‖w‖ = ‖q (w - t.lvlDeriv 0 z w)‖ := by rw [map_sub, hqw, hqD, sub_zero]
      _ ≤ K * ‖w - t.lvlDeriv 0 z w‖ := q.le_opNorm _
      _ ≤ K * (θ * ‖w‖) := mul_le_mul_of_nonneg_left hm hK0
      _ = K * θ * ‖w‖ := by ring
  have hw0 : w = 0 := by
    have hn := norm_nonneg w
    have : ‖w‖ ≤ 0 := by nlinarith
    exact norm_le_zero_iff.1 this
  have heq : t.liftOne u' = t.liftOne u := sub_eq_zero.1 hw0
  rw [← h1, ← h1', heq]

/-- **The chart without boundary of an sc⁺-retract along a reduced tangent space** (the
construction of the proof of 2021 Lemma 9.2.13, (2) ⇒ (1), with the step "image `M` near `0`"
supplied): let `t` be an sc⁺-retraction onto `O = t(U)` in the partial quadrant
`C = T⁻¹([0,∞)ⁿ ⊕ W)`, `z ∈ O₁` with `N = T_zO = Dt(z)E ⊆ E_z`.  Then there are an open `G ∋ z`
in `E`, an open `V` in `N` and mutually inverse sc-smooth maps `χ : (O ∩ G, C, E) → (V, N, N)`
and `Γ : (V, N, N) → (O ∩ G, C, E)` between the retracts: `χ(u) = p(u) − p(z)` for a continuous
projection `p : E → N`, and `Γ = t ∘ (z + ·) ∘ Ψ⁻¹` with `Ψ(h) = p(t(z + h)) − p(z)` (`DΨ(0) = 1`,
the inverse function theorem in the finite-dimensional `N`; `z + h ∈ U` for small `h` since
`N ⊆ E_z`).  `Γ(V) = O ∩ G` is the local injectivity of `p` on `O`
(`exists_injOn_proj`). -/
theorem ScRetraction.IsScPlus.exists_flat {t : ScRetraction E C} (ht : t.IsScPlus)
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (hT : C = T 0 ⁻¹' quadrant n W 0)
    {z : E 1} (hz : E.toBase 1 z ∈ t.retract) {N : Submodule ℝ (E 0)} [FiniteDimensional ℝ N]
    (hN : N = LinearMap.range (scDeriv t.U t z : E 0 →ₗ[ℝ] E 0))
    (hred : N ≤ minimalSubspaceWith T (E.toBase 1 z)) :
    ∃ (G : Set (E 0)) (V : Set N) (χ : E 0 → N) (Γ : N → E 0),
      IsOpen G ∧ E.toBase 1 z ∈ G ∧ IsOpen V ∧
      IsScSmoothRetractMap E C (t.retract ∩ G) (ScBanach.const N) univ V χ ∧
      IsScSmoothRetractMap (ScBanach.const N) univ V E C (t.retract ∩ G) Γ ∧
      (∀ u ∈ t.retract ∩ G, Γ (χ u) = u) ∧ (∀ v ∈ V, χ (Γ v) = v) := by
  set e := E.toBase 1 z with he_def
  have hzU : z ∈ E.lvlSet t.U 1 := t.retract_subset hz
  have heU : e ∈ t.U := hzU
  have hte : t e = e := t.apply_eq_self_of_mem_retract hz
  have hNs : N ≤ E.smooth := hN ▸ ht.range_scDeriv_le_smooth hz
  have hDN : ∀ v ∈ N, scDeriv t.U t z v = v := by
    rw [hN]
    rintro _ ⟨u, rfl⟩
    exact congrArg (fun L : E 0 →L[ℝ] E 0 => L u) (t.scDeriv_comp_self hz)
  obtain ⟨p, hp⟩ := Submodule.ClosedComplemented.of_finiteDimensional N
  have hes : e ∈ E.smooth := lemma_4_1_7_i ht hz
  choose eL heL using (E.mem_smooth_iff.1 hes)
  obtain ⟨δ, hδ, hδU⟩ := t.exists_ball_add_mem_U T hT heU hred
  set B : Set N := ball (0 : N) δ with hBdef
  have hBn : B ∈ 𝓝 (0 : N) := ball_mem_nhds 0 hδ
  have hBU : ∀ h ∈ B, e + (h : E 0) ∈ t.U := fun h hh =>
    hδU h (by rwa [hBdef, mem_ball_zero_iff] at hh)
  have hF : ∀ m, ContDiffOn ℝ ∞ (fun h : N => levelMap t m (eL m + smoothLiftL hNs m h)) B :=
    t.contDiffOn_lvl_add hNs eL heL hBU
  have hFb : ∀ m, ∀ h ∈ B, E.toBase m (levelMap t m (eL m + smoothLiftL hNs m h)) = t (e + h) :=
    fun m h hh => t.toBase_levelMap_add hNs eL heL (hBU h hh) m
  have hF0 : ContDiffOn ℝ ∞ (fun h : N => t (e + h)) B :=
    ((E.toBase 0).contDiff.comp_contDiffOn (hF 0)).congr fun h hh => (hFb 0 h hh).symm
  set Ψ : N → N := fun h => p (t (e + h)) - p e with hΨdef
  have hΨ : ContDiffOn ℝ ∞ Ψ B := (p.contDiff.comp_contDiffOn hF0).sub contDiffOn_const
  have hΨ0 : Ψ 0 = 0 := by simp [hΨdef, hte]
  have hΨ' : HasFDerivAt Ψ ((ContinuousLinearEquiv.refl ℝ N : N ≃L[ℝ] N) : N →L[ℝ] N) 0 := by
    have h1 := t.hasFDerivAt_add hNs hzU hBn hBU
    have h2 := (p.hasFDerivAt.comp (0 : N) h1).sub_const (p e)
    have hL : ((ContinuousLinearEquiv.refl ℝ N : N ≃L[ℝ] N) : N →L[ℝ] N) =
        p.comp ((scDeriv t.U t z).comp N.subtypeL) := by
      ext v
      simp [hDN v v.2, hp]
    rw [hL]
    exact h2
  have hΨat : ContDiffAt ℝ ∞ Ψ 0 := hΨ.contDiffAt hBn
  set H := hΨat.toOpenPartialHomeomorph Ψ hΨ' (by simp) with hHdef
  have hH : ∀ h, H h = Ψ h := fun _ => rfl
  have h0src : (0 : N) ∈ H.source := hΨat.mem_toOpenPartialHomeomorph_source hΨ' _
  -- the local injectivity of `p` on `O`
  obtain ⟨G₀, hG₀, heG₀, hinj⟩ := ht.exists_injOn_proj hz hNs hN p hp
  have hG₀n : (fun h : N => t (e + h)) ⁻¹' G₀ ∈ 𝓝 (0 : N) := by
    have hc : ContinuousAt (fun h : N => t (e + h)) 0 := hF0.continuousOn.continuousAt hBn
    refine hc.preimage_mem_nhds ?_
    simp only [ZeroMemClass.coe_zero, add_zero, hte]
    exact hG₀.mem_nhds heG₀
  -- the derivative of `Ψ` is invertible near `0`
  have hfd : ContinuousOn (fderiv ℝ Ψ) B := hΨ.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)
  have hInv : fderiv ℝ Ψ ⁻¹' range (ContinuousLinearEquiv.toContinuousLinearMap :
      (N ≃L[ℝ] N) → N →L[ℝ] N) ∈ 𝓝 (0 : N) := by
    have h := (ContinuousLinearEquiv.refl ℝ N).nhds
    rw [← hΨ'.fderiv] at h
    exact (hfd.continuousAt hBn).preimage_mem_nhds h
  obtain ⟨S, hSsub, hSo, h0S⟩ := _root_.mem_nhds_iff.1
    (inter_mem (inter_mem (inter_mem (H.open_source.mem_nhds h0src) hBn) hG₀n) hInv)
  set V : Set N := H.target ∩ H.symm ⁻¹' S with hVdef
  have hVo : IsOpen V := H.isOpen_inter_preimage_symm hSo
  have hVS : ∀ v ∈ V, H.symm v ∈ S := fun v hv => hv.2
  have hVB : ∀ v ∈ V, H.symm v ∈ B := fun v hv => (hSsub (hVS v hv)).1.1.2
  have hVG : ∀ v ∈ V, t (e + H.symm v) ∈ G₀ := fun v hv => (hSsub (hVS v hv)).1.2
  -- `H⁻¹` is `C^∞` on `V`
  have hsymm : ContDiffOn ℝ ∞ H.symm V := by
    intro v hv
    obtain ⟨e', he'⟩ := (hSsub (hVS v hv)).2
    have hB' : B ∈ 𝓝 (H.symm v) := isOpen_ball.mem_nhds (hVB v hv)
    have hcd : ContDiffAt ℝ ∞ Ψ (H.symm v) := hΨ.contDiffAt hB'
    have hd : HasFDerivAt Ψ (fderiv ℝ Ψ (H.symm v)) (H.symm v) :=
      (hcd.differentiableAt (by simp)).hasFDerivAt
    rw [← he'] at hd
    exact (H.contDiffAt_symm hv.1 hd hcd).contDiffWithinAt
  set Γ : N → E 0 := fun v => t (e + H.symm v) with hΓdef
  set χ : E 0 → N := fun u => p u - p e with hχdef
  have hχΓ : ∀ v ∈ V, χ (Γ v) = v := fun v hv => by
    change Ψ (H.symm v) = v
    rw [← hH]; exact H.right_inv hv.1
  have hVrel : IsRelOpenInQuadrant (ScBanach.const N) univ V :=
    ⟨isPartialQuadrant_univ _, V, hVo, (inter_univ V).symm⟩
  -- `Γ` is sc-smooth on `V`
  have hΓsm : IsScSmooth (E := ScBanach.const N) (F := E) V Γ := by
    have hlev : ∀ m, ∀ v ∈ V,
        E.toBase m (levelMap t m (eL m + smoothLiftL hNs m (H.symm v))) = Γ v :=
      fun m v hv => hFb m _ (hVB v hv)
    refine IsScSmooth.of_contDiffOn_levels hVrel.isScDomain (fun m v hv => ?_) fun m => ?_
    · rw [ScBanach.lvlSet_const] at hv
      rw [ScBanach.const_toBase]
      exact ⟨_, hlev m v hv⟩
    · rw [ScBanach.lvlSet_const]
      refine ((hF m).comp hsymm fun v hv => hVB v hv).congr fun v hv => ?_
      refine levelMap_eq_of_toBase_eq ?_
      rw [ScBanach.const_toBase]
      exact hlev m v hv
  have hχsm : IsScSmooth (E := E) (F := ScBanach.const N) univ χ :=
    IsScSmooth.of_contDiffOn_finiteDimensional (isScDomain_univ _)
      (p.contDiff.sub contDiff_const).contDiffOn
  set G : Set (E 0) := G₀ ∩ χ ⁻¹' V with hGdef
  have hGo : IsOpen G := hG₀.inter (hVo.preimage (p.continuous.sub continuous_const))
  have heV : χ e = 0 := sub_self _
  have h0V : (0 : N) ∈ V := by
    refine ⟨?_, ?_⟩
    · have := hΨat.image_mem_toOpenPartialHomeomorph_target hΨ' (by simp)
      rwa [hΨ0] at this
    · have : H.symm (H 0) = 0 := H.left_inv h0src
      rw [mem_preimage, ← hΨ0, ← hH, this]
      exact h0S
  have heG : e ∈ G := ⟨heG₀, by rw [mem_preimage, heV]; exact h0V⟩
  have hΓmem : ∀ v ∈ V, Γ v ∈ t.retract ∩ G := fun v hv =>
    ⟨t.apply_mem_retract (hBU _ (hVB v hv)), hVG v hv, by rw [mem_preimage, hχΓ v hv]; exact hv⟩
  have hΓχ : ∀ u ∈ t.retract ∩ G, Γ (χ u) = u := by
    rintro u ⟨huO, huG₀, huV⟩
    have h1 := hΓmem (χ u) huV
    refine hinj _ ⟨h1.1, h1.2.1⟩ u ⟨huO, huG₀⟩ ?_
    have h2 := hχΓ (χ u) huV
    simp only [hχdef] at h2
    exact sub_left_injective h2
  refine ⟨G, V, χ, Γ, hGo, heG, hVo, ⟨fun u hu => hu.2.2, fun R _ => ?_⟩,
    ⟨fun v hv => hΓmem v hv, fun S hS => ?_⟩, hΓχ, hχΓ⟩
  · exact IsScSmooth.comp R.isScDomain (isScDomain_univ _) hχsm R.isScSmooth (mapsTo_univ _ _)
  · have hmaps : MapsTo S S.U V := fun v hv => hS ▸ S.apply_mem_retract hv
    exact IsScSmooth.comp (E := ScBanach.const N) (F := ScBanach.const N) (G := E)
      S.isScDomain hVrel.isScDomain hΓsm S.isScSmooth hmaps

end Analytic

namespace MPolyfold

universe u

section Flat

variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}

/-- **A point whose chart model is an sc⁺-retract with `T_zO ⊆ E_z` has degeneracy index `0`**:
the chart `χ ∘ ψ` on `ψ⁻¹(G)` (`MChart.compRetract` of the restriction of `ψ` with the
sc-diffeomorphism `χ : O ∩ G → V` of `exists_flat`) is a chart of `Y` modelled on the open subset
`V` of the finite-dimensional space `N` without boundary (`C = N`), so
`d_Y(y) = d_N(χ(ψ y)) = 0`. -/
theorem degIndex_eq_zero_of_isReducedTangentAt {ψ : MChart Y} (hψ : Q.IsChart ψ) {y : Y}
    (hy : y ∈ ψ.source) (hplus : IsScPlusRetract ψ.model.E ψ.model.C ψ.model.O) {n : ℕ}
    {W : ScBanach} (T : ScIso ψ.model.E ((ScBanach.const (Fin n → ℝ)).prod W))
    (hT : ψ.model.C = T 0 ⁻¹' quadrant n W 0) {z : ψ.model.E 1}
    (hz : ψ.model.E.toBase 1 z = ψ y)
    (hred : IsReducedTangentAt ψ.model.E ψ.model.C ψ.model.O T z) : Q.degIndex y = 0 := by
  obtain ⟨t, htO, ht⟩ := hplus
  have hzt : ψ.model.E.toBase 1 z ∈ t.retract := by rw [htO, hz]; exact ψ.mapsTo_model y hy
  have hz1 : z ∈ ψ.model.E.lvlSet t.retract 1 := hzt
  have := lemma_4_1_7_ii ht hzt
  have hred' : LinearMap.range (scDeriv t.U t z : ψ.model.E 0 →ₗ[ℝ] ψ.model.E 0) ≤
      minimalSubspaceWith T (ψ.model.E.toBase 1 z) := by
    intro v hv
    apply hred
    rw [← htO, tangentSpace_eq_coe_submodule t hz1]
    exact hv
  obtain ⟨G, V, χ, Γ, hG, hzG, hV, hχ, hΓ, hΓχ, hχΓ⟩ := ht.exists_flat T hT hzt rfl hred'
  rw [htO] at hχ hΓ hΓχ
  set s : Set Y := ψ.source ∩ ψ ⁻¹' G with hs
  have hso : IsOpen s := ψ.continuousOn_toFun.isOpen_inter_preimage ψ.isOpen_source hG
  have hss : s ⊆ ψ.source := fun _ h => h.1
  have himg : ψ '' s = ψ.model.O ∩ G := by rw [hs, image_inter_preimage, ψ.image_source]
  have hVrel : IsRelOpenInQuadrant (ScBanach.const (LinearMap.range
      (scDeriv t.U t z : ψ.model.E 0 →ₗ[ℝ] ψ.model.E 0))) univ V :=
    ⟨isPartialQuadrant_univ _, V, hV, (inter_univ V).symm⟩
  let κ : MChart Y := (ψ.restrict hss hso).compRetract (LocalModel.ofRelOpen hVrel) (f := χ)
    (g := Γ) (by rw [← himg] at hχ; exact hχ) (by rw [← himg] at hΓ; exact hΓ)
    (by rw [← himg] at hΓχ; exact hΓχ) hχΓ
  have hκ : Q.IsChart κ :=
    MChart.compRetract_isChart _ _ _ _ (MPolyfold.IsChart.restrict Q hψ hss hso)
  have hyκ : y ∈ κ.source := ⟨hy, by rw [mem_preimage, ← hz]; exact hzG⟩
  have h0 : chartDegIndex κ y = 0 := TrivialBundle.univ_degIndex_eq_zero _ _
  exact Nat.le_zero.1 (h0 ▸ Q.degIndex_le hκ hyκ)

end Flat

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- **2021 Lemma 9.2.13, (2) ⇒ (1)** at every point of `M`: `T_aM ⊆ T_a^R X` implies `d_M(a) = 0`.
*Proof*: in the chart of `M` induced by a chart `φ` of `X` in which the condition holds, the model
`φ(W ∩ M)` is an sc⁺-retract (`isScPlusRetract_image`), with the partial quadrant of `φ`, and
`T_zQ ⊆ E_z`; `degIndex_eq_zero_of_isReducedTangentAt`. -/
theorem subDegIndex_eq_zero_of_isTangentReducedAt {A : Set X} (hA : P.IsSmoothSubmanifold A)
    {a : A} (h : P.IsTangentReducedAt A a) : P.subDegIndex hA.isSubMPolyfold a = 0 := by
  obtain ⟨-, d, φ, n, W, T, z, ha, hφ, haφ, hT, hz, hred⟩ := h
  let := P.paracompactSpace_subtype A
  have hψ := subPolyfold_isChart hA.isSubMPolyfold d.toSubData hφ a
  have haψ : a ∈ (subChart d.toSubData hφ a).source := d.toSubData.mem_shrink φ a.2 ha haφ
  have hplus := d.isScPlusRetract_image hφ (P.levelMk 1 a (d.mem_levelSet_one a.2 ha))
  exact degIndex_eq_zero_of_isReducedTangentAt hψ haψ hplus T hT hz hred


/-- **2021 Lemma 9.2.13, (2) ⇒ (1)**, p. 419 (2017: Lemma 9.9), read for `x ∈ M ∩ ∂X` (the text's
proof places `x = 0` in `∂O`; as printed the direction does not hold as we read it,
`not_lemma_9_2_13_two_one`): `T_xM ⊆ T_x^R X` gives (1), `x ∈ M ∩ ∂X` with `d_M(x) = 0`. -/
theorem lemma_9_2_13_two_one {A : Set X} (hA : P.IsSmoothSubmanifold A) {a : A}
    (hb : a.1 ∈ P.boundary) (h : P.IsTangentReducedAt A a) :
    a.1 ∈ P.boundary ∧ P.subDegIndex hA.isSubMPolyfold a = 0 :=
  ⟨hb, subDegIndex_eq_zero_of_isTangentReducedAt hA h⟩

/-- **2021 Lemma 9.2.13** at a point `x ∈ M ∩ ∂X`: (1) `x ∈ M ∩ ∂X` with `d_M(x) = 0` iff
(2) `T_xM ⊆ T_x^R X` (`lemma_9_2_13` and `lemma_9_2_13_two_one`). -/
theorem lemma_9_2_13_iff {A : Set X} (hA : P.IsSmoothSubmanifold A) {a : A}
    (hb : a.1 ∈ P.boundary) :
    (a.1 ∈ P.boundary ∧ P.subDegIndex hA.isSubMPolyfold a = 0) ↔ P.IsTangentReducedAt A a :=
  ⟨lemma_9_2_13 hA, lemma_9_2_13_two_one hA hb⟩

/-- **2021 Lemma 9.2.13 at every point of `M`**: `d_M(x) = 0` iff `T_xM ⊆ T_x^R X` (the reading
consistent with `not_lemma_9_2_13_two_one`; off `∂X` both sides hold,
`lemma_9_2_13_of_not_mem_boundary`). -/
theorem subDegIndex_eq_zero_iff {A : Set X} (hA : P.IsSmoothSubmanifold A) (a : A) :
    P.subDegIndex hA.isSubMPolyfold a = 0 ↔ P.IsTangentReducedAt A a := by
  refine ⟨fun h0 => ?_, subDegIndex_eq_zero_of_isTangentReducedAt hA⟩
  by_cases hb : a.1 ∈ P.boundary
  · exact lemma_9_2_13 hA ⟨hb, h0⟩
  · exact (lemma_9_2_13_of_not_mem_boundary hA hb).1

/-- **2021 Remark 9.2.14, p. 419 (2017: Remark 9.5), "⇒"**: `x ∈ ∂M` gives `x ∈ ∂X`
(`remark_9_2_14_mem_boundary`) and `T_xM ⊄ T_x^R X` (Lemma 9.2.13 (2) ⇒ (1),
`subDegIndex_eq_zero_of_isTangentReducedAt`). -/
theorem remark_9_2_14_not_isTangentReducedAt {A : Set X} (hA : P.IsSmoothSubmanifold A) {a : A}
    (h : 1 ≤ P.subDegIndex hA.isSubMPolyfold a) :
    a.1 ∈ P.boundary ∧ ¬ P.IsTangentReducedAt A a := by
  refine ⟨remark_9_2_14_mem_boundary hA.isSubMPolyfold h, fun hT => ?_⟩
  have := subDegIndex_eq_zero_of_isTangentReducedAt hA hT
  omega

/-- **2021 Remark 9.2.14, the reformulation**: `x ∈ ∂M` iff `x ∈ ∂X` and `T_xM ⊄ T_x^R X`
(`∂M` the boundary of the induced structure, `mem_boundary_subPolyfold_iff`). -/
theorem remark_9_2_14_iff {A : Set X} (hA : P.IsSmoothSubmanifold A) (a : A) :
    (letI := P.paracompactSpace_subtype A; a ∈ (subPolyfold hA.isSubMPolyfold).boundary) ↔
      a.1 ∈ P.boundary ∧ ¬ P.IsTangentReducedAt A a :=
  (mem_boundary_subPolyfold_iff hA.isSubMPolyfold a).trans
    ⟨remark_9_2_14_not_isTangentReducedAt hA, remark_9_2_14 hA⟩

/-- **2021 Remark 9.2.14, first part**: for `x ∈ M ∩ ∂X`, `x ∉ ∂M` holds precisely when
`T_xM ⊆ T_x^R X`. -/
theorem remark_9_2_14_not_mem_boundary_iff {A : Set X} (hA : P.IsSmoothSubmanifold A) {a : A}
    (hb : a.1 ∈ P.boundary) :
    (letI := P.paracompactSpace_subtype A; a ∉ (subPolyfold hA.isSubMPolyfold).boundary) ↔
      P.IsTangentReducedAt A a :=
  (remark_9_2_14_iff hA a).not.trans
    ⟨fun h => by_contra fun hT => h ⟨hb, hT⟩, fun hT h => h.2 hT⟩

/-- The hypothesis of `subDegIndex_eq_zero_of_isTangentReducedAt` is satisfiable: a point of
`ℝⁿ` (`not_lemma_9_2_13_two_one`). -/
example (n : ℕ) (p : Fin n → ℝ) :
    (rnPolyfold n).subDegIndex (rnPolyfold_isSmoothSubmanifold_singleton n p).isSubMPolyfold
      ⟨p, mem_singleton p⟩ = 0 :=
  subDegIndex_eq_zero_of_isTangentReducedAt (rnPolyfold_isSmoothSubmanifold_singleton n p)
    (not_lemma_9_2_13_two_one n p).1

end MPolyfold

end Polyfold
