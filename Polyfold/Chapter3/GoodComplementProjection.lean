import Polyfold.Chapter3.LocalSolvability

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.2 (Definition
3.21, the proof of Theorem 3.2.3 (preprint 3.27)), §3.5 (Theorem 3.5.6 (preprint 3.43), Lemma 3.5.10 (preprint 3.46)) and Appendix 3.8.1 (the normal
form of Proposition 3.1.25 (preprint 3.22)): **good complements whose projection maps the partial quadrant into
itself**, and Theorem 3.5.6 (preprint 3.43) with such a complement.

# Good complements with a projection into the partial quadrant

## The text, paraphrased

(Proof of Theorem 3.2.3 (preprint 3.27)) "The subset `Σ = {v + y ∈ C | v ∈ V, y ∈ Y}` is relatively open in `C`",
and the retraction `t(v + w) = v + δ(v)` is defined on `Σ ∩ O`.  (Proof of Theorem 3.5.6 (preprint 3.43),
Appendix 3.8.2, Lemma 3.5.10 (preprint 3.46)) a good complement `Z` of `K̃ = ker DH(0)` in `ℝⁿ'` is obtained by
projecting a good complement `Y'` of `K'`, and `Z ⊕ W` is a good complement of
`K' = {(α, Dδ(0)α) | α ∈ K̃}`.

## What is formalized

* `Polyfold.ProjectsInto C N Y`: the projection onto `N` along `Y` maps `C` into `C`, stated without
  the projection (`z ∈ C`, `k ∈ N`, `z − k ∈ Y` imply `k ∈ C`); `ProjectsInto.projectionOnto_mem`,
  `projectsInto_of_projectionOnto_mem`; transport by linear isomorphisms `S` with `S(C) = C'`
  (`ProjectsInto.map`, `ProjectsInto.mapL`).
* `Polyfold.exists_proj_quadCone` (in coordinates `C = {ℓ_i ≥ 0}`), `exists_proj_goodComplement`,
  `exists_goodComplement_projectsInto`: **the finite-dimensional lemma (Finding 83)**: a
  finite-dimensional `N` in good position to a partial quadrant `C` in an sc-Banach space `E` has a
  closed good complement `Y = ker π` with `π(C) ⊆ N ∩ C` for the projection `π` onto `N` along `Y`.
  The choice of coordinates is `exists_coordSet`, the estimate `exists_coord_ge`.
* `Polyfold.IsGoodComplement.prod_top_graph`: for **any** good complement `Z` of `K̃` in `ℝⁿ'`,
  `Z ⊕ W` is a good complement of `K' = graph(L|K̃)` in `ℝⁿ' ⊕ W` (constant `ε/(‖L‖ + 1)`), and
  `ProjectsInto.prod_top_graph` (the property passes from `(K̃, Z)` to `(K', Z ⊕ W)`).
* `Polyfold.ShiftedBasicData.exists_sol_of_goodComplement`: the data of the proof of Theorem 3.5.6 (preprint 3.43)
  exist with a prescribed good complement `Z` of `K̃`; `ShiftedBasicData.exists_sol_proj`: with a
  `Z` whose projection maps `C̃` into `K̃ ∩ C̃`.
* `Polyfold.theorem_3_5_6_proj`: **Theorem 3.5.6 (preprint 3.43)** (`theorem_3_5_6_closed`) with the additional
  conclusion `ProjectsInto (C̃ ⊕ W) K' Y`.  The consequences for Theorem 3.5.11 (preprint 3.47)
  (`theorem_3_5_11_proj`, `LocalSolvabilityClosed.lean`), the graph description of Theorem 3.6.8 (preprint 3.54)
  (`theorem_3_6_8_graph_proj_wholeChart`, `GlobalIFT.lean`) and the tangent germ chart at the centre
  (`theorem_3_6_8_tangentGermChart_proj_wholeChart`, condition (b) of `TangentGermChart.IsRegular`,
  `GlobalIFTCenter.lean`) are proved where the old statements are (those are now corollaries).

## What the text leaves implicit, and the choices made (the findings)

* **Condition (b) of `IsRegular` is a choice of the good complement, not a restriction on the
  set** (Finding 130).  For a general good complement the projection need not map `C` into `C`
  (Finding 83: `C = [0,∞)³`, `N = ℝ(1,1,1)`, `Y = {x + y − z = 0}`), and then the text's claim that
  `Σ` is relatively open in `C` fails.  For the solution set of an sc-Fredholm section the good
  complement is produced by the proof (Theorem 3.5.6 (preprint 3.43), Lemma 3.5.10 (preprint 3.46)) and can be chosen with the
  projection property from the start, so no re-graphing over another complement is needed.
* **The construction and its cases** (Finding 131).  With `Σ` the indices vanishing at some nonzero
  point of `N ∩ C` and `Q = (ℓ_i)_{i ∈ Σ} : N → ℝ^Σ` (onto by Lemma 3.8.8 (preprint 3.65)), `π(z) =
  p_N(z) + g(ℓ_Σ(z − p_N(z)))` for a continuous projection `p_N` onto `N` and a right inverse `g`
  of `Q`: `ℓ_i ∘ π = ℓ_i` for `i ∈ Σ`, so `π(C) ⊆ {n ∈ N | ℓ_i(n) ≥ 0, i ∈ Σ} = N ∩ C`.  This
  needs `N ∩ C = {ℓ_i ≥ 0, i ∈ Σ}`, which holds when `Σ ≠ ∅` (`mem_quadCone_of_vanIdx`) and when
  `N ∩ C = N`, but not in the remaining case `Σ = ∅`, `N ∩ C ≠ N` (`N` a line, `N ∩ C` a half-line
  on which all coordinates are positive): there `ℝ^Σ = 0`, the formula gives an arbitrary
  projection, and e.g. for `C = [0,∞)²`, `N = ℝ(1,1)` the projection along `(1,2)` maps `(0,1)` to
  `−(1,1)`.  In that case one coordinate `j₀` is kept (`S = {j₀}`, `π(z) = (ℓ_{j₀}(z)/ℓ_{j₀}(y))y`).
  The good-complement estimate for `ker π`: the coordinates in `S` vanish on `ker π`, and for
  `i ∉ S` `ℓ_i(n) ≥ c|n|` on `N ∩ C` (compactness of the unit sphere of `N`).
-/

open Set Filter Topology Function Module

noncomputable section

namespace Polyfold

/-! ### The projection property -/

section Projects

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **The projection onto `N` along `Y` maps `C` into `C`**, stated without naming the projection:
whenever `z ∈ C`, `k ∈ N` and `z − k ∈ Y`, then `k ∈ C`.  (For `E = N ⊕ Y` this says
`π(C) ⊆ C` for the projection `π : E → N` along `Y`, `ProjectsInto.projectionOnto_mem`.) -/
def ProjectsInto (C : Set V) (N Y : Submodule ℝ V) : Prop :=
  ∀ z ∈ C, ∀ k ∈ N, z - k ∈ Y → k ∈ C

/-- The projection `π : E → N` along `Y` maps `C` into `C`. -/
lemma ProjectsInto.projectionOnto_mem {C : Set V} {N Y : Submodule ℝ V} (h : ProjectsInto C N Y)
    (hNY : IsCompl N Y) {z : V} (hz : z ∈ C) : (N.projectionOnto Y hNY z : V) ∈ C :=
  h z hz _ (Submodule.coe_mem _) (by
    rw [← Submodule.projectionOnto_apply_eq_zero_iff hNY, map_sub,
      Submodule.projectionOnto_apply_left, sub_self])

/-- Conversely, `π(C) ⊆ C` for the projection along a complement `Y` gives `ProjectsInto`. -/
lemma projectsInto_of_projectionOnto_mem {C : Set V} {N Y : Submodule ℝ V} (hNY : IsCompl N Y)
    (h : ∀ z ∈ C, (N.projectionOnto Y hNY z : V) ∈ C) : ProjectsInto C N Y := by
  intro z hz k hk hzk
  have h1 : N.projectionOnto Y hNY (z - k) = 0 :=
    (Submodule.projectionOnto_apply_eq_zero_iff hNY).2 hzk
  rw [map_sub, sub_eq_zero, Submodule.projectionOnto_apply_of_mem_left hNY hk] at h1
  have := h z hz
  rwa [h1] at this

/-- `ProjectsInto` is carried by linear isomorphisms `S` with `S(C) = C'`. -/
lemma ProjectsInto.map {V' : Type*} [AddCommGroup V'] [Module ℝ V'] {C : Set V} {C' : Set V'}
    (S : V ≃ₗ[ℝ] V') (hS : ∀ x, x ∈ C ↔ S x ∈ C') {N Y : Submodule ℝ V}
    (h : ProjectsInto C N Y) :
    ProjectsInto C' (N.map (S : V →ₗ[ℝ] V')) (Y.map (S : V →ₗ[ℝ] V')) := by
  rintro z' hz' _ ⟨k, hk, rfl⟩ ⟨y, hy, hyz⟩
  have hz : S.symm z' ∈ C := by rw [hS, S.apply_symm_apply]; exact hz'
  have hzk : S.symm z' - k ∈ Y := by
    have : S.symm z' - k = y := by
      apply S.injective
      rw [map_sub, S.apply_symm_apply]
      exact hyz.symm
    rw [this]; exact hy
  exact (hS k).1 (h _ hz k hk hzk)

/-- `ProjectsInto.map` for a continuous linear isomorphism. -/
lemma ProjectsInto.mapL {V' : Type*} [AddCommGroup V'] [Module ℝ V'] [TopologicalSpace V]
    [TopologicalSpace V'] {C : Set V} {C' : Set V'} (S : V ≃L[ℝ] V') (hS : ∀ x, x ∈ C ↔ S x ∈ C')
    {N Y : Submodule ℝ V} (h : ProjectsInto C N Y) :
    ProjectsInto C' (N.map (S : V →ₗ[ℝ] V')) (Y.map (S : V →ₗ[ℝ] V')) :=
  h.map S.toLinearEquiv hS

end Projects

/-! ### The finite-dimensional lemma, in coordinates -/

section Core

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ}
  (ℓ : Fin n → V →ₗ[ℝ] ℝ) (N : Submodule ℝ V)

/-- The coordinates in a set `S` of indices: `Q_S : N → ℝ^S`, `Q_S(x)_i = ℓ_i(x)` (for `S = Σ`
this is the map `Q` of the proof of Proposition 3.1.25 (preprint 3.22), `sigmaCoord`). -/
def coordOn (S : Finset (Fin n)) : N →ₗ[ℝ] (S → ℝ) := LinearMap.pi fun i => restrFun ℓ N i.1

@[simp] lemma coordOn_apply (S : Finset (Fin n)) (x : N) (i : S) :
    coordOn ℓ N S x i = ℓ i.1 (x : V) := rfl

lemma sigmaCoord_eq_coordOn : sigmaCoord ℓ N = coordOn ℓ N (vanIdx ℓ N) := rfl

/-- If `0` is an interior point of the cone `N ∩ C` in `N`, the cone is all of `N`. -/
lemma mem_quadCone_of_zero_mem_interior (h0 : (0 : N) ∈ interior (quadCone ℓ N)) (x : N) :
    x ∈ quadCone ℓ N := by
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), t • x ∈ quadCone ℓ N := by
    have hc : Continuous fun t : ℝ => t • x := by fun_prop
    exact (hc.continuousAt (x := 0)).preimage_mem_nhds
      (by simpa using mem_interior_iff_mem_nhds.1 h0)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 hev
  have h := hδ' (y := δ / 2)
    (by rw [dist_zero_right, Real.norm_of_nonneg (by positivity)]; linarith)
  have := smul_mem_quadCone ℓ N h (t := (δ / 2)⁻¹) (by positivity)
  rwa [smul_smul, inv_mul_cancel₀ (by positivity), one_smul] at this

/-- **The segment argument of `mem_quadCone_of_vanIdx` for an arbitrary set `S` of
coordinates**: if every coordinate outside `S` is positive at the nonzero points of the cone, and
some coordinate `i₀ ∈ S` is positive at a point `y` of the cone, then `x ∈ N` lies in the cone as
soon as its coordinates in `S` are `≥ 0`.  (Move from `x` towards `y` along `x + s·y`: the first
point of the cone met on the way is nonzero, so its coordinates outside `S` are positive, and it
was not the first.) -/
lemma mem_quadCone_of_coordSet [FiniteDimensional ℝ N] {S : Finset (Fin n)}
    (hpos : ∀ i ∉ S, ∀ x ∈ quadCone ℓ N, x ≠ 0 → 0 < ℓ i (x : V))
    {i₀ : Fin n} (hi₀ : i₀ ∈ S) {y : N} (hyD : y ∈ quadCone ℓ N) (hy0 : 0 < ℓ i₀ (y : V))
    {x : N} (hx : ∀ i ∈ S, 0 ≤ ℓ i (x : V)) : x ∈ quadCone ℓ N := by
  classical
  have hyne : y ≠ 0 := fun h => by rw [h] at hy0; simp at hy0
  set T : Set ℝ := Ici (0 : ℝ) ∩ (fun s : ℝ => x + s • y) ⁻¹' quadCone ℓ N with hT
  have hcoord : ∀ (s : ℝ) (j : Fin n),
      ℓ j ((x + s • y : N) : V) = ℓ j (x : V) + s * ℓ j (y : V) := by
    intro s j
    rw [Submodule.coe_add, Submodule.coe_smul, map_add, map_smul, smul_eq_mul]
  have hT_ne : T.Nonempty := by
    have hev : ∀ᶠ s in atTop, ∀ j, j ∉ S → 0 ≤ ℓ j (x : V) + s * ℓ j (y : V) := by
      rw [eventually_all]
      intro j
      by_cases hj : j ∈ S
      · exact Eventually.of_forall fun _ h => absurd hj h
      · have hpos' := hpos j hj y hyD hyne
        filter_upwards [eventually_ge_atTop (-ℓ j (x : V) / ℓ j (y : V))] with s hs _
        rw [div_le_iff₀ hpos'] at hs
        linarith
    obtain ⟨s, hs0, hs⟩ := ((eventually_ge_atTop (0 : ℝ)).and hev).exists
    refine ⟨s, hs0, fun j => ?_⟩
    rw [hcoord]
    by_cases hj : j ∈ S
    · exact add_nonneg (hx j hj) (mul_nonneg hs0 (hyD j))
    · exact hs j hj
  have hT_closed : IsClosed T := by
    rw [hT]
    exact isClosed_Ici.inter ((quadCone_isClosed ℓ N).preimage
      (by fun_prop : Continuous fun s : ℝ => x + s • y))
  have hT_bdd : BddBelow T := ⟨0, fun s hs => hs.1⟩
  have hsT : sInf T ∈ T := hT_closed.csInf_mem hT_ne hT_bdd
  have hs_eq : sInf T = 0 := by
    by_contra hne
    have hpos0 : 0 < sInf T := lt_of_le_of_ne hsT.1 (Ne.symm hne)
    have hz0 : x + sInf T • y ≠ 0 := by
      intro hz
      have h1 := hx i₀ hi₀
      have h2 := hcoord (sInf T) i₀
      rw [hz, Submodule.coe_zero, map_zero] at h2
      nlinarith
    have hev : ∀ᶠ s in 𝓝 (sInf T), ∀ j, j ∉ S → 0 < ℓ j ((x + s • y : N) : V) := by
      rw [eventually_all]
      intro j
      by_cases hj : j ∈ S
      · exact Eventually.of_forall fun _ h => absurd hj h
      · have hpos' := hpos j hj _ hsT.2 hz0
        have hc : Continuous fun s : ℝ => ℓ j ((x + s • y : N) : V) :=
          (continuous_restrFun ℓ N j).comp (by fun_prop : Continuous fun s : ℝ => x + s • y)
        exact ((hc.tendsto (sInf T)).eventually_const_lt hpos').mono fun s hs _ => hs
    obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 hev
    set s₁ : ℝ := max 0 (sInf T - δ / 2) with hs₁
    have hs₁lt : s₁ < sInf T := max_lt hpos0 (by linarith)
    have hdist : dist s₁ (sInf T) < δ := by
      rw [Real.dist_eq, abs_sub_comm, abs_of_pos (by linarith)]
      linarith [le_max_right 0 (sInf T - δ / 2)]
    have hs₁T : s₁ ∈ T := by
      refine ⟨show (0 : ℝ) ≤ s₁ from le_max_left _ _, fun j => ?_⟩
      by_cases hj : j ∈ S
      · rw [hcoord]; exact add_nonneg (hx j hj) (mul_nonneg (le_max_left _ _) (hyD j))
      · exact (hδ' hdist j hj).le
    exact absurd (csInf_le hT_bdd hs₁T) (not_le.2 hs₁lt)
  have := hsT.2
  rw [hs_eq] at this
  simpa using this

/-- **The choice of coordinates for the projection.**  For `N` in good position there is a set
`S` of coordinates with (1) `Q_S : N → ℝ^S` onto, (2) `N ∩ C = {x ∈ N | ℓ_i(x) ≥ 0, i ∈ S}`,
(3) every coordinate outside `S` is positive at the nonzero points of `N ∩ C`.  `S = Σ` (the
indices vanishing at some nonzero point of `N ∩ C`) except in the case `Σ = ∅`, `N ∩ C ≠ N`,
where `N` is a line and `S = {j₀}` is any single coordinate. -/
lemma exists_coordSet [FiniteDimensional ℝ N] (P : Submodule ℝ V) (hNP : IsCompl N P)
    {ε : ℝ} (hε : 0 < ε)
    (hgood : ∀ x ∈ N, ∀ p ∈ P, ‖p‖ ≤ ε * ‖x‖ →
      ((∀ i, 0 ≤ ℓ i x) ↔ ∀ i, 0 ≤ ℓ i (x + p)))
    (hℓ : ∀ (s : Finset (Fin n)) (k : Fin n → ℝ), ∃ v : V, ∀ i ∈ s, ℓ i v = k i)
    (hint : (interior (quadCone ℓ N)).Nonempty) :
    ∃ S : Finset (Fin n), Surjective (coordOn ℓ N S) ∧
      (∀ x : N, (∀ i ∈ S, 0 ≤ ℓ i (x : V)) → x ∈ quadCone ℓ N) ∧
      (∀ i ∉ S, ∀ x ∈ quadCone ℓ N, x ≠ 0 → 0 < ℓ i (x : V)) := by
  classical
  have hsurj := sigmaCoord_surjective ℓ N P hNP hε hgood hℓ
  have hpos : ∀ i ∉ vanIdx ℓ N, ∀ x ∈ quadCone ℓ N, x ≠ 0 → 0 < ℓ i (x : V) :=
    fun i hi x hx hx0 => pos_of_not_mem_vanIdx ℓ N hx hx0 hi
  by_cases hDN : ∀ x : N, x ∈ quadCone ℓ N
  · exact ⟨vanIdx ℓ N, hsurj, fun x _ => hDN x, hpos⟩
  by_cases hS : (vanIdx ℓ N).Nonempty
  · exact ⟨vanIdx ℓ N, hsurj, fun x hx => mem_quadCone_of_vanIdx ℓ N hS hsurj hint hx, hpos⟩
  -- `Σ = ∅` and `N ∩ C ≠ N`: a single coordinate `j₀` (`N` is a line)
  rw [Finset.not_nonempty_iff_eq_empty] at hS
  push Not at hDN
  obtain ⟨x₁, hx₁⟩ := hDN
  obtain ⟨j₀, -⟩ : ∃ j₀ : Fin n, ℓ j₀ (x₁ : V) < 0 := by
    simp only [mem_quadCone, not_forall, not_le] at hx₁; exact hx₁
  obtain ⟨y, hy⟩ := hint
  have hyD : y ∈ quadCone ℓ N := interior_subset hy
  have hyne : y ≠ 0 := by
    rintro rfl
    exact hx₁ (mem_quadCone_of_zero_mem_interior ℓ N hy x₁)
  have hnot : ∀ i, i ∉ vanIdx ℓ N := fun i => by rw [hS]; exact Finset.notMem_empty i
  have hpos' : ∀ i ∉ ({j₀} : Finset (Fin n)), ∀ x ∈ quadCone ℓ N, x ≠ 0 → 0 < ℓ i (x : V) :=
    fun i _ => hpos i (hnot i)
  have hy0 : 0 < ℓ j₀ (y : V) := hpos j₀ (hnot j₀) y hyD hyne
  refine ⟨{j₀}, fun k => ?_, fun x hx => mem_quadCone_of_coordSet ℓ N (S := {j₀}) hpos'
    (Finset.mem_singleton_self j₀) hyD hy0 hx, hpos'⟩
  refine ⟨(k ⟨j₀, Finset.mem_singleton_self j₀⟩ / ℓ j₀ (y : V)) • y, ?_⟩
  funext i
  obtain ⟨i, hi⟩ := i
  rw [Finset.mem_singleton] at hi
  subst hi
  rw [coordOn_apply, Submodule.coe_smul, map_smul, smul_eq_mul, div_mul_cancel₀ _ hy0.ne']

/-- A coordinate which is positive at the nonzero points of the cone `N ∩ C` is bounded below by
a multiple of the norm there: `ℓ_i(x) ≥ c|x|` (compactness of the unit sphere of `N`). -/
lemma exists_coord_ge [FiniteDimensional ℝ N] {i : Fin n}
    (hpos : ∀ x ∈ quadCone ℓ N, x ≠ 0 → 0 < ℓ i (x : V)) :
    ∃ c > 0, ∀ x ∈ quadCone ℓ N, c * ‖x‖ ≤ ℓ i (x : V) := by
  set K : Set N := Metric.sphere 0 1 ∩ quadCone ℓ N with hK
  have hKc : IsCompact K := (isCompact_sphere 0 1).inter_right (quadCone_isClosed ℓ N)
  have hcont : ContinuousOn (fun x : N => ℓ i (x : V)) K :=
    (continuous_restrFun ℓ N i).continuousOn
  obtain ⟨c, hc, hcK⟩ := hKc.exists_forall_le' hcont (a := 0) fun x hx => hpos x hx.2 (by
    rintro rfl
    have h1 := hx.1
    rw [mem_sphere_zero_iff_norm, norm_zero] at h1
    exact zero_ne_one h1)
  refine ⟨c, hc, fun x hx => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  · have hn : 0 < ‖x‖ := norm_pos_iff.2 hx0
    have hmem : ‖x‖⁻¹ • x ∈ K := by
      refine ⟨?_, smul_mem_quadCone ℓ N hx (by positivity)⟩
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_of_nonneg (by positivity),
        inv_mul_cancel₀ hn.ne']
    have h1 := hcK _ hmem
    rw [Submodule.coe_smul, map_smul, smul_eq_mul] at h1
    rw [mul_comm]
    exact (le_inv_mul_iff₀ hn).1 h1

/-- A positive lower bound for finitely many positive numbers. -/
lemma exists_pos_le_of_finite {ι : Type*} [Finite ι] (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ ε > 0, ∀ i, ε ≤ f i := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun i => (IsEmpty.false i).elim⟩
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_min f
    exact ⟨f i₀, hf i₀, hi₀⟩

/-- **The finite-dimensional lemma (Finding 83), in coordinates.**  Let `ℓ_1, …, ℓ_n` be
continuous, jointly onto `ℝⁿ`, `C = {ℓ_i ≥ 0}`, and let the finite-dimensional `N` be in good
position to `C` (good complement `P`, constant `ε`; `N ∩ C` with nonempty interior in `N`).  Then
there is a continuous projection `π : V → N` (`π = id` on `N`) mapping `C` into `N ∩ C` whose
kernel is again a good complement of `N`.

Construction: with `S` from `exists_coordSet`, a continuous projection `p_N : V → N` and a linear
right inverse `g` of `Q_S : N → ℝ^S`, `π(z) = p_N(z) + g(ℓ_S(z − p_N(z)))`; then `ℓ_i ∘ π = ℓ_i`
for `i ∈ S`, so `π(C) ⊆ {ℓ_i ≥ 0, i ∈ S} ∩ N = N ∩ C`.  On `ker π` the coordinates in `S` vanish,
and for `i ∉ S`, `ℓ_i(n) ≥ c|n|` on `N ∩ C`, so `|p| ≤ ε'|n|` with `ε' ≤ c/(‖ℓ_i‖ + 1)` keeps
`ℓ_i(n + p) ≥ 0`. -/
theorem exists_proj_quadCone [FiniteDimensional ℝ N] (hcont : ∀ i, Continuous (ℓ i))
    (P : Submodule ℝ V) (hNP : IsCompl N P) {ε : ℝ} (hε : 0 < ε)
    (hgood : ∀ x ∈ N, ∀ p ∈ P, ‖p‖ ≤ ε * ‖x‖ →
      ((∀ i, 0 ≤ ℓ i x) ↔ ∀ i, 0 ≤ ℓ i (x + p)))
    (hℓ : ∀ (s : Finset (Fin n)) (k : Fin n → ℝ), ∃ v : V, ∀ i ∈ s, ℓ i v = k i)
    (hint : (interior (quadCone ℓ N)).Nonempty) :
    ∃ π : V →L[ℝ] N, (∀ x : N, π x = x) ∧
      (∀ z : V, (∀ i, 0 ≤ ℓ i z) → π z ∈ quadCone ℓ N) ∧
      ∃ ε' > 0, ∀ x ∈ N, ∀ p ∈ LinearMap.ker (π : V →ₗ[ℝ] N), ‖p‖ ≤ ε' * ‖x‖ →
        ((∀ i, 0 ≤ ℓ i x) ↔ ∀ i, 0 ≤ ℓ i (x + p)) := by
  classical
  obtain ⟨S, hsurjS, hD, hpos⟩ := exists_coordSet ℓ N P hNP hε hgood hℓ hint
  -- a continuous projection `p_N : V → N` and a linear right inverse `g` of `Q_S`
  obtain ⟨pN, hpN⟩ := Submodule.ClosedComplemented.of_finiteDimensional N
  obtain ⟨g, hg⟩ := (coordOn ℓ N S).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 hsurjS)
  have hgk : ∀ k, coordOn ℓ N S (g k) = k := fun k => LinearMap.congr_fun hg k
  let ℓc : Fin n → V →L[ℝ] ℝ := fun i => ⟨ℓ i, hcont i⟩
  let ℓS : V →L[ℝ] (S → ℝ) := ContinuousLinearMap.pi fun i : S => ℓc i.1
  let gc : (S → ℝ) →L[ℝ] N := LinearMap.toContinuousLinearMap g
  let π : V →L[ℝ] N :=
    pN + gc.comp (ℓS.comp (ContinuousLinearMap.id ℝ V - N.subtypeL.comp pN))
  have hπ : ∀ z, π z = pN z + g (fun i : S => ℓ i.1 (z - pN z)) := fun z => rfl
  have hπN : ∀ x : N, π x = x := fun x => by
    rw [hπ, hpN x, sub_self]
    have : (fun i : S => ℓ i.1 (0 : V)) = 0 := funext fun i => map_zero _
    rw [this, map_zero, add_zero]
  have hπS : ∀ z, ∀ i ∈ S, ℓ i (π z : V) = ℓ i z := fun z i hi => by
    have h1 := congrFun (hgk (fun i : S => ℓ i.1 (z - pN z))) ⟨i, hi⟩
    rw [coordOn_apply] at h1
    rw [hπ, Submodule.coe_add, map_add, h1, map_sub, add_sub_cancel]
  -- the constants
  have hcge : ∀ i, ∃ c > 0, i ∉ S → ∀ x ∈ quadCone ℓ N, c * ‖x‖ ≤ ℓ i (x : V) := fun i => by
    by_cases hi : i ∈ S
    · exact ⟨1, one_pos, fun h => absurd hi h⟩
    · obtain ⟨c, hc, h⟩ := exists_coord_ge ℓ N (hpos i hi)
      exact ⟨c, hc, fun _ => h⟩
  choose c hc hcx using hcge
  obtain ⟨ε', hε', hε'le⟩ :=
    exists_pos_le_of_finite (fun i => c i / (‖ℓc i‖ + 1)) (fun i => by have := hc i; positivity)
  refine ⟨π, hπN, fun z hz => hD _ fun i hi => by rw [hπS z i hi]; exact hz i, ε', hε',
    fun x hx p hp hle => ?_⟩
  have hp0 : π p = 0 := hp
  have hpS : ∀ i ∈ S, ℓ i p = 0 := fun i hi => by
    have := hπS p i hi
    rw [hp0, Submodule.coe_zero, map_zero] at this
    exact this.symm
  constructor
  · intro hxC i
    rw [map_add]
    by_cases hi : i ∈ S
    · rw [hpS i hi, add_zero]; exact hxC i
    · have h1 : c i * ‖x‖ ≤ ℓ i x := hcx i hi ⟨x, hx⟩ hxC
      have h2 : -(‖ℓc i‖ * ‖p‖) ≤ ℓ i p := by
        have h3 : ‖ℓc i p‖ ≤ ‖ℓc i‖ * ‖p‖ := (ℓc i).le_opNorm p
        have h4 : |ℓ i p| ≤ ‖ℓc i‖ * ‖p‖ := by
          rw [← Real.norm_eq_abs]; exact h3
        linarith [neg_abs_le (ℓ i p)]
      have hA : 0 ≤ ‖ℓc i‖ := norm_nonneg _
      have h5 : ‖ℓc i‖ * ‖p‖ ≤ c i * ‖x‖ := by
        have hfrac : ‖ℓc i‖ / (‖ℓc i‖ + 1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
        have hcx0 : 0 ≤ c i * ‖x‖ := by have := hc i; positivity
        calc ‖ℓc i‖ * ‖p‖ ≤ ‖ℓc i‖ * (ε' * ‖x‖) := by gcongr
          _ ≤ ‖ℓc i‖ * (c i / (‖ℓc i‖ + 1) * ‖x‖) := by gcongr; exact hε'le i
          _ = c i * ‖x‖ * (‖ℓc i‖ / (‖ℓc i‖ + 1)) := by ring
          _ ≤ c i * ‖x‖ * 1 := by gcongr
          _ = c i * ‖x‖ := mul_one _
      linarith
  · intro hxp
    refine hD ⟨x, hx⟩ fun i hi => ?_
    have := hxp i
    rwa [map_add, hpS i hi, add_zero] at this

end Core

/-! ### The finite-dimensional lemma for partial quadrants -/

section ScLevel

variable {E : ScBanach}

lemma continuous_coordFun {n : ℕ} {W : ScBanach}
    (T : E 0 ≃L[ℝ] ((ScBanach.const (Fin n → ℝ)).prod W) 0) (i : Fin n) :
    Continuous (coordFun T i) :=
  show Continuous fun x => (T x).1 i from
    (continuous_apply i).comp (continuous_fst.comp T.continuous)

/-- **The finite-dimensional lemma (Finding 83), with the projection.**  If the finite-dimensional
subspace `N` is in good position to the partial quadrant `C` in `E`, there is a continuous
projection `π : E₀ → N` (`π = id` on `N`) with `π(C) ⊆ N ∩ C` whose kernel is a good complement
of `N` (closed, as the kernel of a continuous map). -/
theorem exists_proj_goodComplement {C : Set (E 0)} (hC : IsPartialQuadrant E C)
    {N : Submodule ℝ (E 0)} [FiniteDimensional ℝ N] (hN : IsInGoodPosition E C N) :
    ∃ π : E 0 →L[ℝ] N, (∀ x : N, π x = x) ∧ (∀ z ∈ C, (π z : E 0) ∈ C) ∧
      IsGoodComplement E C N (LinearMap.ker (π : E 0 →ₗ[ℝ] N)) := by
  obtain ⟨n, W, T, rfl⟩ := hC
  obtain ⟨P, hP⟩ := hN.exists_goodComplement
  obtain ⟨ε, hε, hgood⟩ := hP.exists_eps
  obtain ⟨π, hπN, hπC, ε', hε', hgood'⟩ := exists_proj_quadCone (coordFun (T 0)) N
    (continuous_coordFun (T 0)) P hP.isCompl hε hgood (coordFun_surj (T 0)) hN.interior_nonempty
  exact ⟨π, hπN, fun z hz => hπC z hz,
    ⟨(ContinuousLinearMap.isTopCompl_of_proj hπN).isCompl, ε', hε', hgood'⟩⟩

/-- **The finite-dimensional lemma (Finding 83).**  If the finite-dimensional subspace `N` is in
good position to the partial quadrant `C` in `E`, then `N` has a closed good complement `Y` such
that the projection onto `N` along `Y` maps `C` into `N ∩ C` (`ProjectsInto C N Y`).  The text's
Definition 3.1.24 (preprint 3.21) (and Proposition 3.22) does not need this; it is what makes condition (b) of
`TangentGermChart.IsRegular` available (see `theorem_3_6_8_tangentGermChart_proj_wholeChart`). -/
theorem exists_goodComplement_projectsInto {C : Set (E 0)} (hC : IsPartialQuadrant E C)
    {N : Submodule ℝ (E 0)} [FiniteDimensional ℝ N] (hN : IsInGoodPosition E C N) :
    ∃ Y : Submodule ℝ (E 0), IsGoodComplement E C N Y ∧ IsClosed (Y : Set (E 0)) ∧
      ProjectsInto C N Y := by
  obtain ⟨π, hπN, hπC, hY⟩ := exists_proj_goodComplement hC hN
  refine ⟨LinearMap.ker (π : E 0 →ₗ[ℝ] N), hY, π.isClosed_ker, ?_⟩
  intro z hz k hk hzk
  have h1 : π (z - k) = 0 := hzk
  rw [map_sub, sub_eq_zero, hπN ⟨k, hk⟩] at h1
  have := hπC z hz
  rwa [h1] at this

end ScLevel

/-! ### Theorem 3.5.6 (preprint 3.43) with a prescribed good complement -/

section Graph

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {W : ScBanach} {Ct : Set P}

/-- **Any good complement `Z` of `K̃` gives the good complement `Z ⊕ W` of
`K' = {(α, Lα) | α ∈ K̃}`** with respect to `C' = C̃ ⊕ W`, with constant `ε/(‖L‖ + 1)` (the
second half of the proof of Lemma 3.5.10 (preprint 3.46), `lemma_3_5_10`, for an arbitrary good complement `Z`). -/
theorem IsGoodComplement.prod_top_graph {L : P →L[ℝ] W 0} {Kt Z : Submodule ℝ P}
    (hZ : IsGoodComplement (ScBanach.const P) Ct Kt Z) :
    IsGoodComplement (ScBanach.paramProd P W) (Ct ×ˢ univ) (Kt.map (graphMap L)) (Z.prod ⊤) := by
  obtain ⟨ε', hε'pos, hkey⟩ := hZ.exists_eps
  have hKZ := hZ.isCompl
  refine ⟨?_, ?_⟩
  · -- `K' ⊕ (Z ⊕ W) = ℝⁿ' ⊕ W`
    refine IsCompl.of_eq ?_ ?_
    · rw [eq_bot_iff]
      intro x ⟨hxK, hxZ⟩
      obtain ⟨α, hα, rfl⟩ := hxK
      have hαZ : α ∈ Z := (Submodule.mem_prod.1 hxZ).1
      have : α = 0 := (Submodule.disjoint_def.1 hKZ.disjoint) α hα hαZ
      rw [this]; simp
    · rw [eq_top_iff]
      intro x _
      obtain ⟨α, hα, z, hz, hαz⟩ :=
        Submodule.mem_sup.1 (hKZ.sup_eq_top ▸ Submodule.mem_top (x := x.1))
      refine Submodule.mem_sup.2
        ⟨graphMap L α, ⟨α, hα, rfl⟩, (z, x.2 - L α), ⟨hz, Submodule.mem_top⟩, ?_⟩
      rw [graphMap_apply]
      ext
      · simpa using hαz
      · simp
  · -- the estimate
    refine ⟨ε' / (‖L‖ + 1), by positivity, ?_⟩
    rintro _ ⟨α, hα, rfl⟩ p hp hle
    have hp1 : p.1 ∈ Z := (Submodule.mem_prod.1 hp).1
    have hα' : ‖graphMap L α‖ ≤ (‖L‖ + 1) * ‖α‖ := by
      rw [graphMap_apply, Prod.norm_mk]
      refine max_le (by nlinarith [norm_nonneg α, norm_nonneg L]) ?_
      calc ‖L α‖ ≤ ‖L‖ * ‖α‖ := L.le_opNorm α
        _ ≤ (‖L‖ + 1) * ‖α‖ := by gcongr; linarith
    have hz : ‖p.1‖ ≤ ε' * ‖α‖ := by
      calc ‖p.1‖ ≤ ‖p‖ := norm_fst_le p
        _ ≤ ε' / (‖L‖ + 1) * ‖graphMap L α‖ := hle
        _ ≤ ε' / (‖L‖ + 1) * ((‖L‖ + 1) * ‖α‖) := by gcongr
        _ = ε' * ‖α‖ := by field_simp
    have := hkey α hα p.1 hp1 hz
    rw [graphMap_mem_prod_iff, this]
    simp [graphMap_apply]

omit [FiniteDimensional ℝ P] in
/-- `ProjectsInto` passes from `(K̃, Z)` in `ℝⁿ'` to `(K', Z ⊕ W)` in `ℝⁿ' ⊕ W`, with respect to
`C̃` and `C̃ ⊕ W`: the projection along `Z ⊕ W` is `(a, w) ↦ (π_Z a, L π_Z a)`. -/
theorem ProjectsInto.prod_top_graph {L : P →L[ℝ] W 0} {Kt Z : Submodule ℝ P}
    (h : ProjectsInto Ct Kt Z) :
    ProjectsInto (Ct ×ˢ (univ : Set (W 0))) (Kt.map (graphMap L)) (Z.prod ⊤) := by
  rintro z hz _ ⟨α, hα, rfl⟩ hzk
  have h1 : z.1 - α ∈ Z := (Submodule.mem_prod.1 hzk).1
  rw [graphMap_mem_prod_iff]
  exact h z.1 hz.1 α hα h1

end Graph

namespace ShiftedBasicData

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {W : ScBanach} {Ct : Set P}
  {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
  (𝒟 : ShiftedBasicData Ct W Q)

/-- **The data of the proof of Theorem 3.5.6 (preprint 3.43) with a prescribed good complement**: for the
derivative data `𝒱` and *any* good complement `Z` of `K̃ = ker DH(0)` in `ℝⁿ'`, the data `Sol`
exist with this `Z` (`exists_sol` takes the `Z` of Lemma 3.5.10 (preprint 3.46); Lemma 3.5.10 (preprint 3.46) is needed only for the
good position of `K̃`, and `Z ⊕ W` is a good complement of `K'` by
`IsGoodComplement.prod_top_graph`). -/
theorem exists_sol_of_goodComplement (hC : IsPartialQuadrant (ScBanach.const P) Ct)
    (hsurj : Surjective 𝒟.Dg)
    (hpos : IsInGoodPosition (ScBanach.paramProd P W) (Ct ×ˢ univ) 𝒟.K') (𝒱 : 𝒟.Deriv)
    {Z : Submodule ℝ P}
    (hZ : IsGoodComplement (ScBanach.const P) Ct (LinearMap.ker (𝒱.DH₀ : P →ₗ[ℝ] Q)) Z) :
    ∃ 𝒮 : 𝒟.Sol, 𝒮.toDeriv = 𝒱 ∧ 𝒮.Z = Z := by
  classical
  have hCq := hC.isQuadrantLike
  have hker : 𝒟.K' = (LinearMap.ker (𝒱.DH₀ : P →ₗ[ℝ] Q)).map (graphMap 𝒱.L) := 𝒱.ker_Dg_eq hCq
  have hpos' : IsInGoodPosition (ScBanach.paramProd P W) (Ct ×ˢ univ)
      ((LinearMap.ker (𝒱.DH₀ : P →ₗ[ℝ] Q)).map (graphMap 𝒱.L)) := hker ▸ hpos
  have hY := hZ.prod_top_graph (L := 𝒱.L) (W := W)
  have hKpos := lemma_3_5_10_isInGoodPosition hpos'
  have hU : IsRelOpenInQuadrant (ScBanach.const P) Ct 𝒱.V₁ := ⟨hC, 𝒱.relOpen⟩
  have hDH : fderivWithin ℝ 𝒟.H 𝒱.V₁ 0 = 𝒱.DH₀ := 𝒱.fderivWithin_H hCq
  obtain ⟨V', σ, ε, σ₀, hV'rel, hV'0, hσC, hσ0, hDσ, hsol, hε, hσ₀, hbound, huniq⟩ :=
    theorem_3_8_22 hU 𝒱.zero_mem (j := 1) le_rfl 𝒱.H_contDiffOn 𝒟.H_zero
      (by rw [hDH]; exact 𝒱.DH₀_surjective hCq hsurj) (by rw [hDH]) hKpos hZ
  exact ⟨⟨𝒱, hker, Z, hZ, hker ▸ hY, V', hV'rel, hV'0, σ, hσC, hσ0, hDσ, hsol, ε, hε, σ₀, hσ₀,
    hbound, huniq⟩, rfl, rfl⟩

/-- **The data of the proof of Theorem 3.5.6 (preprint 3.43) with a good complement `Z` of `K̃` whose projection
maps `C̃` into `K̃ ∩ C̃`** (`exists_goodComplement_projectsInto` in `ℝⁿ'`, then
`exists_sol_of_goodComplement`). -/
theorem exists_sol_proj (hC : IsPartialQuadrant (ScBanach.const P) Ct) (hsurj : Surjective 𝒟.Dg)
    (hpos : IsInGoodPosition (ScBanach.paramProd P W) (Ct ×ˢ univ) 𝒟.K') :
    ∃ 𝒮 : 𝒟.Sol, ProjectsInto Ct 𝒮.Kt 𝒮.Z := by
  obtain ⟨𝒱⟩ := 𝒟.exists_deriv hC.isQuadrantLike
  have hker := 𝒱.ker_Dg_eq hC.isQuadrantLike
  have hpos' : IsInGoodPosition (ScBanach.paramProd P W) (Ct ×ˢ univ)
      ((LinearMap.ker (𝒱.DH₀ : P →ₗ[ℝ] Q)).map (graphMap 𝒱.L)) := hker ▸ hpos
  obtain ⟨Z, hZ, -, hZp⟩ :=
    exists_goodComplement_projectsInto hC (lemma_3_5_10_isInGoodPosition hpos')
  obtain ⟨𝒮, h1, h2⟩ := 𝒟.exists_sol_of_goodComplement hC hsurj hpos 𝒱 hZ
  refine ⟨𝒮, ?_⟩
  change ProjectsInto Ct (LinearMap.ker (𝒮.toDeriv.DH₀ : P →ₗ[ℝ] Q)) 𝒮.Z
  rw [h1, h2]
  exact hZp

/-- **Theorem 3.5.6 (preprint 3.43) with a good complement whose projection maps the partial quadrant into itself**:
`theorem_3_5_6_closed` with the additional conclusion `ProjectsInto (C̃ ⊕ W) K' Y`, i.e. the
projection onto `K' = ker Dg(0)` along `Y = Z ⊕ W` maps `C' = C̃ ⊕ W` into `K' ∩ C'`.  The good
complement is that of `exists_sol_proj`. -/
theorem _root_.Polyfold.theorem_3_5_6_proj (hC : IsPartialQuadrant (ScBanach.const P) Ct)
    (𝒟 : ShiftedBasicData Ct W Q) (hsurj : Surjective 𝒟.Dg)
    (hpos : IsInGoodPosition (ScBanach.paramProd P W) (Ct ×ˢ univ) 𝒟.K')
    (hreg : ∀ ε > 0, ∃ r > 0, ∀ x ∈ 𝒟.G₀.U 0, 𝒟.g x = 0 → ‖x‖ < r →
      ∃ w₁ : W 1, W.toBase 1 w₁ = x.2 ∧ ‖w₁‖ < ε) :
    ∃ (Y : Submodule ℝ (P × W 0)) (V : Set 𝒟.K') (τ : 𝒟.K' → P × W 0),
      IsGoodComplement (ScBanach.paramProd P W) (Ct ×ˢ univ) 𝒟.K' Y ∧
      IsClosed (Y : Set (P × W 0)) ∧ ProjectsInto (Ct ×ˢ univ) 𝒟.K' Y ∧
      (∃ O : Set 𝒟.K', IsOpen O ∧ V = O ∩ Subtype.val ⁻¹' (Ct ×ˢ univ)) ∧ (0 : 𝒟.K') ∈ V ∧
      (∀ y, τ y ∈ Y) ∧ (∀ y, (τ y).2 ∈ range (W.toBase 1)) ∧
      ContDiffOn ℝ 1 τ V ∧ τ 0 = 0 ∧ fderivWithin ℝ τ V 0 = 0 ∧
      (∀ y ∈ V, (y : P × W 0) + τ y ∈ 𝒟.G₀.U 0 ∧ 𝒟.g ((y : P × W 0) + τ y) = 0) ∧
      (∀ k : ℕ, 1 ≤ k → ∃ Vk : Set 𝒟.K',
        (∃ O : Set 𝒟.K', IsOpen O ∧ Vk = O ∩ Subtype.val ⁻¹' (Ct ×ˢ univ)) ∧
        (0 : 𝒟.K') ∈ Vk ∧ Vk ⊆ V ∧
        ∃ τk : 𝒟.K' → (ScBanach.paramProd P W) k, ContDiffOn ℝ k τk Vk ∧
          ∀ y ∈ Vk, (ScBanach.paramProd P W).toBase k (τk y) = τ y) ∧
      ∃ U'' : Set (P × W 0), IsOpen U'' ∧ (0 : P × W 0) ∈ U'' ∧
        ∀ x ∈ U'' ∩ 𝒟.G₀.U 0, 𝒟.g x = 0 → ∃ y ∈ V, x = (y : P × W 0) + τ y := by
  obtain ⟨𝒮, hZp⟩ := 𝒟.exists_sol_proj hC hsurj hpos
  refine ⟨𝒮.Z.prod ⊤, 𝒮.V, 𝒮.τ, 𝒮.hY, ?_, ?_, 𝒮.V_relOpen, 𝒮.zero_mem_V, 𝒮.τ_mem_Y,
    𝒮.snd_τ_mem_range, 𝒮.τ_contDiffOn, 𝒮.τ_zero, 𝒮.fderivWithin_τ hC.isQuadrantLike hpos,
    fun _ hy => 𝒮.sol_mem_and_eq_zero hy,
    fun k hk => 𝒮.exists_contDiffOn_level hC hsurj hpos k hk, 𝒮.exists_eq_add_τ hreg⟩
  · rw [Submodule.prod_coe, Submodule.top_coe]
    exact 𝒮.Z.closed_of_finiteDimensional.prod isClosed_univ
  · rw [𝒮.hker]
    exact hZp.prod_top_graph

end ShiftedBasicData

end Polyfold
