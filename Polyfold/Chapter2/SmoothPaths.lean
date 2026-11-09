import Polyfold.Chapter2.LocalTopology
import Polyfold.Chapter6.OrientationSpace
import Polyfold.Chapter7.SmoothPointsDense

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §2.2, Lemma 2.2.1
(p. 30) and Theorem 2.2.4 (p. 32), §2.3, Proposition 2.3.7 (p. 36), used in §7.4 (pp. 331–340),
Appendix 7.6.4 (p. 349) and §6.6 (Theorem 6.6.17, p. 275).

# Smooth points of connected open sets are path-connected in `X_∞`

## The text, paraphrased

(Lemma 2.2.1, p. 30) For `U ⊆ C` relatively open and connected, every level `U_k`, `k ∈ ℕ ∪ {∞}`,
is path-connected: a path in `U₀` is replaced by a polygon through smooth points in overlapping
convex sets `B_ε(σ(tᵢ)) ∩ C`.  (Theorem 2.2.4, Proposition 2.3.7) Retracts and M-polyfolds are
locally path-connected.  In §7.4 the text uses, for a connected open `U ⊆ X`, that `U ∩ X_∞` is
connected (proofs of Propositions 7.4.8 and 7.4.10, p. 334 and p. 336), and in Appendix 7.6.4
(p. 349) that `U(x) ∩ X_m` is connected for the natural representations `U(x)`; Theorem 6.6.17 (2)
needs small open `U ∋ x` with `U ∩ X_∞` connected.  None of these is proved in the text.

## What is formalized

* `MPolyfold.exists_nhds_joinedIn_smooth` (**the local lemma**): for `U ⊆ X` open and `u ∈ U`
  there is an open `N` with `u ∈ N ⊆ U` such that any two smooth points of `N` are joined in
  `U ∩ X_∞` by a path which is continuous for the topology of `X_∞` (Theorem 2.3.10).  The path is
  the retracted segment `t ↦ φ⁻¹(r(φ(x) + ρ(t)(φ(y) − φ(x))))` of `chartSegPath`: the segment lies
  in a ball `B_δ(φ(u))` with `B_δ(φ(u)) ∩ C ⊆ U_r` and `r(B_δ(φ(u)) ∩ U_r) ⊆ φ(U ∩ V)`; it is an
  sc-smooth path (`isScSmoothMap_chartSegPath`), hence continuous into `X_∞`
  (`continuous_smoothMk_comp`).
* `MPolyfold.isPathConnected_smoothVal_preimage` (**the global step**): for `U ⊆ X` open and
  connected, `U ∩ X_∞` is path-connected in `X_∞`.  The set of points of `U` all of whose nearby
  smooth points are joined to a fixed smooth `x₀ ∈ U` is open, and closed in `U` by the local lemma
  and the density of `X_∞` (`MPolyfold.dense_smoothSet`), so it is `U`.
* `MPolyfold.isPreconnected_smoothVal_preimage`, and on the levels
  `MPolyfold.isPreconnected_levelVal_preimage`: `U ∩ X_m` is connected in `X_m` for every `m`
  (the image of `U ∩ X_∞` is connected and dense in `U ∩ X_m`, by `MPolyfold.denseSmooth`).

These make the hypotheses `MPolyfold.SmoothConnected` (Chapter 7, `Zhou.lean`),
`MPolyfold.HasConnectedSmoothNbhds` (Chapter 6, `OrientationSpace.lean`),
`EpGroupoid.NaturalRep.LevelConnected` and `EpGroupoid.HasConnectedDenseLevelOneReps`
(`ZhouLevels.lean`, `ReducedCriterion.lean`) theorems; see `Chapter7/SmoothConnectedReps.lean`
(gaps G.85 and G.90 of the report).

## What the text leaves implicit, and the choices made

* The polygon of Lemma 2.2.1 is not needed: a chain argument on the connected set `U` replaces it,
  and each link is one retracted segment between two smooth points of a small chart ball.
* `X_∞` carries the initial topology of the inclusions `X_∞ → X_m` (`MPolyfold.SmoothLevel`,
  Theorem 2.3.10); the paths are sc-smooth, which is more than the continuity used.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u

/-- A continuous map `(Fin 1 → ℝ) → Y` with values in `F` joins its values at `pt1 0` and
`pt1 1` inside `F`. -/
theorem joinedIn_of_continuous_pt1 {Y : Type*} [TopologicalSpace Y] {F : Set Y}
    {γ : (Fin 1 → ℝ) → Y} (hγ : Continuous γ) (hF : ∀ t, γ t ∈ F) :
    JoinedIn F (γ (pt1 0)) (γ (pt1 1)) :=
  JoinedIn.ofLine (f := fun t : ℝ => γ (pt1 t))
    (hγ.comp (continuous_pi fun _ => continuous_id)).continuousOn rfl rfl
    (by rintro _ ⟨t, -, rfl⟩; exact hF _)

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

/-- **The local lemma**: for `U ⊆ X` open and `u ∈ U` there is an open `N` with `u ∈ N ⊆ U` such
that any two smooth points `x, y ∈ N` are joined, inside `U ∩ X_∞` and for the topology of `X_∞`,
by the retracted segment from `φ(x)` to `φ(y)` in a chart `φ` around `u` (Lemma 2.2.1 for one
convex piece, followed by the retraction `r`). -/
theorem exists_nhds_joinedIn_smooth {U : Set X} (hU : IsOpen U) {u : X} (hu : u ∈ U) :
    ∃ N : Set X, IsOpen N ∧ u ∈ N ∧ N ⊆ U ∧
      ∀ x y : P.SmoothLevel, P.smoothVal x ∈ N → P.smoothVal y ∈ N →
        JoinedIn (P.smoothVal ⁻¹' U) x y := by
  obtain ⟨φ, hφ, huφ⟩ := P.exists_isChart_mem_source u
  obtain ⟨R, hR⟩ := φ.model.isScRetract
  set u₀ := φ u with hu₀def
  have hOR : ∀ {v}, v ∈ φ.model.O → v ∈ R.retract := fun hv => hR ▸ hv
  have hu₀O : u₀ ∈ φ.model.O := φ.mapsTo_model u huφ
  have hu₀U : u₀ ∈ R.U := R.retract_subset (hOR hu₀O)
  have hRu₀ : R u₀ = u₀ := R.apply_eq_self_of_mem_retract (hOR hu₀O)
  -- `φ(U ∩ V) = O ∩ W₀`
  obtain ⟨W₀, hW₀, hW₀eq⟩ := φ.exists_isOpen_image_eq (s := U ∩ φ.source) inter_subset_right
    (hU.inter φ.isOpen_source)
  have hu₀W₀ : u₀ ∈ W₀ := by
    have : φ u ∈ φ '' (U ∩ φ.source) := ⟨u, ⟨hu, huφ⟩, rfl⟩
    rw [hW₀eq] at this
    exact this.2
  -- `r` is continuous at `u₀` on level `0`: `r(B_{δ₁}(u₀) ∩ U_r) ⊆ W₀`
  have hcont : ContinuousWithinAt R R.U u₀ := R.isSc1.isSc0.continuousOn_base u₀ hu₀U
  obtain ⟨δ₁, hδ₁, hδ₁W⟩ := Metric.mem_nhdsWithin_iff.1 (hcont (hW₀.mem_nhds (by rwa [hRu₀])))
  -- `B_{δ₂}(u₀) ∩ C ⊆ U_r`
  obtain ⟨δ₂, hδ₂, hδ₂U⟩ := R.relOpen.exists_ball_inter_subset hu₀U
  set δ := min δ₁ δ₂ with hδdef
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  have hUC : R.U ⊆ φ.model.C := by
    obtain ⟨O', -, h⟩ := R.relOpen.relOpen
    rw [h]
    exact inter_subset_right
  have hCconv : Convex ℝ φ.model.C := R.relOpen.isPartialQuadrant.convex
  set N := φ.source ∩ φ ⁻¹' Metric.ball u₀ δ ∩ U with hNdef
  have hNo : IsOpen N :=
    (φ.continuousOn_toFun.isOpen_inter_preimage φ.isOpen_source Metric.isOpen_ball).inter hU
  refine ⟨N, hNo, ⟨⟨huφ, Metric.mem_ball_self hδ⟩, hu⟩, inter_subset_right, ?_⟩
  intro x y hx hy
  have hκ : ∀ p : Fin 1 → ℝ, Real.smoothTransition (p 0) ∈ Icc (0 : ℝ) 1 := fun p =>
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  set a := φ (P.smoothVal x) with hadef
  set b := φ (P.smoothVal y) with hbdef
  have haO : a ∈ φ.model.O := φ.mapsTo_model _ hx.1.1
  have hbO : b ∈ φ.model.O := φ.mapsTo_model _ hy.1.1
  -- the segment from `a` to `b` lies in `B_δ(u₀) ∩ U_r`
  have hseg : ∀ p : Fin 1 → ℝ,
      a + Real.smoothTransition (p 0) • (b - a) ∈ Metric.ball u₀ δ ∩ R.U := fun p => by
    have hball : a + Real.smoothTransition (p 0) • (b - a) ∈ Metric.ball u₀ δ :=
      (convex_ball u₀ δ).add_smul_sub_mem hx.1.2 hy.1.2 (hκ p)
    refine ⟨hball, hδ₂U ⟨Metric.ball_subset_ball (min_le_right _ _) hball, ?_⟩⟩
    exact hCconv.add_smul_sub_mem (hUC (R.retract_subset (hOR haO)))
      (hUC (R.retract_subset (hOR hbO))) (hκ p)
  have hsegU : ∀ p : Fin 1 → ℝ, a + Real.smoothTransition (p 0) • (b - a) ∈ R.U :=
    fun p => (hseg p).2
  -- `r(segment) ⊆ O ∩ W₀ = φ(U ∩ V)`, so the retracted segment read in the chart lies in `U`
  have hRseg : ∀ p : Fin 1 → ℝ, chartSegPath φ R a b p ∈ U := fun p => by
    have h1 : R (a + Real.smoothTransition (p 0) • (b - a)) ∈ φ.model.O :=
      hR ▸ R.apply_mem_retract (hsegU p)
    have h2 : R (a + Real.smoothTransition (p 0) • (b - a)) ∈ W₀ :=
      hδ₁W ⟨Metric.ball_subset_ball (min_le_left _ _) (hseg p).1, (hseg p).2⟩
    have : R (a + Real.smoothTransition (p 0) • (b - a)) ∈ φ '' (U ∩ φ.source) := by
      rw [hW₀eq]
      exact ⟨h1, h2⟩
    obtain ⟨z, hz, hzeq⟩ := this
    change φ.symm (R (a + Real.smoothTransition (p 0) • (b - a))) ∈ U
    rw [← hzeq, φ.symm_apply_apply hz.2]
    exact hz.1
  have hsm : ∀ {z}, z ∈ φ.source → z ∈ P.smoothSet → φ z ∈ φ.model.E.smooth := fun hz hzs =>
    φ.model.E.mem_smooth_iff.2 fun m => (P.mem_levelSet_iff hφ hz).1 (mem_iInter.1 hzs m)
  -- the retracted segment is an sc-smooth path, hence continuous into `X_∞`
  have hγs : (rnPolyfold 1).IsScSmoothMap P (chartSegPath φ R a b) :=
    isScSmoothMap_chartSegPath hφ hR (hsm hx.1.1 (P.smoothVal_mem x))
      (hsm hy.1.1 (P.smoothVal_mem y)) hsegU
  have hJ := joinedIn_of_continuous_pt1 (continuous_smoothMk_comp hγs)
    (F := P.smoothVal ⁻¹' U) fun t => hRseg t
  -- its end points are `x` and `y`
  have h0 : P.smoothMk (chartSegPath φ R a b (pt1 0)) (mem_smoothSet_of_isScSmoothMap hγs _) =
      x := by
    apply Subtype.ext
    change φ.symm (R (a + Real.smoothTransition ((pt1 0 : Fin 1 → ℝ) 0) • (b - a))) =
      P.smoothVal x
    rw [pt1_apply, Real.smoothTransition.zero, zero_smul, add_zero,
      R.apply_eq_self_of_mem_retract (hOR haO), hadef, φ.symm_apply_apply hx.1.1]
  have h1 : P.smoothMk (chartSegPath φ R a b (pt1 1)) (mem_smoothSet_of_isScSmoothMap hγs _) =
      y := by
    apply Subtype.ext
    change φ.symm (R (a + Real.smoothTransition ((pt1 1 : Fin 1 → ℝ) 0) • (b - a))) =
      P.smoothVal y
    rw [pt1_apply, Real.smoothTransition.one, one_smul, add_sub_cancel,
      R.apply_eq_self_of_mem_retract (hOR hbO), hbdef, φ.symm_apply_apply hy.1.1]
  rwa [h0, h1] at hJ

/-- **The global step** (the fact used in the proofs of 2021 Propositions 7.4.8 and 7.4.10, and
Lemma 2.2.1 for `k = ∞` transported to an M-polyfold): for a connected open `U ⊆ X`, the smooth
points `U ∩ X_∞` form a path-connected subset of `X_∞` (topology of Theorem 2.3.10). -/
theorem isPathConnected_smoothVal_preimage {U : Set X} (hU : IsOpen U) (hc : IsConnected U) :
    IsPathConnected (P.smoothVal ⁻¹' U) := by
  -- a smooth point `x₀` of `U`
  obtain ⟨x₀', hx₀s, hx₀U⟩ := P.dense_smoothSet.exists_mem_open hU hc.nonempty
  set x₀ := P.smoothMk x₀' hx₀s with hx₀def
  -- the points of `U` all of whose nearby smooth points are joined to `x₀`
  set A : Set X := {u | ∃ N : Set X, IsOpen N ∧ u ∈ N ∧
    ∀ y : P.SmoothLevel, P.smoothVal y ∈ N → JoinedIn (P.smoothVal ⁻¹' U) y x₀} with hAdef
  have hAo : IsOpen A := isOpen_iff_forall_mem_open.2 fun u ⟨N, hNo, huN, hN⟩ =>
    ⟨N, fun v hv => ⟨N, hNo, hv, hN⟩, hNo, huN⟩
  have hUA : U ⊆ A := by
    refine hc.isPreconnected.subset_of_closure_inter_subset hAo ⟨x₀', hx₀U, ?_⟩ ?_
    · obtain ⟨N, hNo, huN, -, hN⟩ := P.exists_nhds_joinedIn_smooth hU hx₀U
      exact ⟨N, hNo, huN, fun y hy => hN y x₀ hy huN⟩
    · rintro u ⟨hucl, huU⟩
      obtain ⟨N, hNo, huN, -, hN⟩ := P.exists_nhds_joinedIn_smooth hU huU
      obtain ⟨u', hu'N, N', hN'o, hu'N', hN'⟩ := mem_closure_iff.1 hucl N hNo huN
      obtain ⟨z', hz's, hz'⟩ :=
        P.dense_smoothSet.exists_mem_open (hNo.inter hN'o) ⟨u', hu'N, hu'N'⟩
      exact ⟨N, hNo, huN, fun y hy =>
        (hN y (P.smoothMk z' hz's) hy hz'.1).trans (hN' _ hz'.2)⟩
  refine ⟨x₀, hx₀U, fun y hy => ?_⟩
  obtain ⟨N, -, hyN, hN⟩ := hUA hy
  exact (hN y hyN).symm

/-- For a connected open `U ⊆ X`, `U ∩ X_∞` is connected in `X_∞`. -/
theorem isPreconnected_smoothVal_preimage {U : Set X} (hU : IsOpen U) (hc : IsConnected U) :
    IsPreconnected (P.smoothVal ⁻¹' U) :=
  (P.isPathConnected_smoothVal_preimage hU hc).isConnected.isPreconnected

/-- **On every level** (Lemma 2.2.1 for `k ∈ ℕ`, transported; the choice of `U(x)` in the proof
of 2021 Proposition 7.4.18 and in Appendix 7.6.4): for a connected open `U ⊆ X` and every `m`,
`U ∩ X_m` is connected in `X_m`.  It contains the connected image of `U ∩ X_∞`, which is dense in
it by `MPolyfold.denseSmooth`. -/
theorem isPreconnected_levelVal_preimage (m : ℕ) {U : Set X} (hU : IsOpen U)
    (hc : IsConnected U) : IsPreconnected {z : P.Level m | P.levelVal m z ∈ U} := by
  have h1 : IsPreconnected ((fun x => P.smoothIncl x m) '' (P.smoothVal ⁻¹' U)) :=
    (P.isPreconnected_smoothVal_preimage hU hc).image _ (P.continuous_smoothIncl m).continuousOn
  refine h1.subset_closure ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact hx
  · intro z hz
    have hzo : IsOpen {z : P.Level m | P.levelVal m z ∈ U} := hU.preimage (continuous_levelVal m)
    refine closure_mono ?_ ((P.denseSmooth m).open_subset_closure_inter hzo hz)
    rintro w ⟨hwU, hws⟩
    exact ⟨P.smoothMk (P.levelVal m w) hws, hwU, P.level_ext rfl⟩

end MPolyfold

end Polyfold
