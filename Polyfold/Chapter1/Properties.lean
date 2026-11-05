import Polyfold.Chapter1.ChainRule

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §1.2,
Propositions 1.16–1.19 and Corollary 1.20 (quoted there from [25] = arXiv 1002.3381,
Propositions 2.1–2.4 and Corollary 2.5, whose proofs are in §2.1 of that paper).

# Properties of sc-differentiability: the parts formalized

## The text, paraphrased

(Proposition 1.16) An sc⁰ map `f : U → F` is sc¹ iff (1) for every `m ≥ 1`, `f : U_m → F_{m−1}` is
`C¹`, so that `df : U_m → L(E_m, F_{m−1})` is continuous, and (2) for every `m ≥ 1` and
`x ∈ U_m`, `df(x)` extends to a bounded `Df(x) : E_{m−1} → F_{m−1}` with
`U_m ⊕ E_{m−1} → F_{m−1}`, `(x, h) ↦ Df(x)h` continuous.  In particular `Df(x) : E → F` is an
sc-operator at smooth points `x`.  (Proposition 1.17) If `f : U → V` is sc^k then `f : U¹ → V¹` is
sc^k.  (Proposition 1.18) If `f` is sc^k then `f : U_{m+k} → V_m` is `C^k`, and `f : U_{m+l} → V_m`
is `C^l` for `0 ≤ l ≤ k`.  (Proposition 1.19) If `f : U_{m+l} → F_m` is `C^{l+1}` for all `m` and
`0 ≤ l ≤ k`, then `f` is sc^{k+1}.  (Corollary 1.20) If `f : U → ℝᴺ` has `f : U_l → ℝᴺ` of class
`C^{l+1}` for `0 ≤ l ≤ k`, then `f` is sc^{k+1}.

## What is formalized

* `IsSc1With.exists_delta_deriv`: the uniform continuity of `x ↦ Df(x)` on compact subsets of
  `E₀` (the "compact-open continuity" behind all these statements).
* `IsSc1With.continuousOn_deriv_clm` and `IsSc1With.contDiffOn_base`: for an sc¹ map,
  `x ↦ Df(x)|_{E₁}` is continuous `U₁ → L(E₁, F₀)` in the operator norm, and `f : U₁ → F₀` is
  `C¹`: **Proposition 1.16 (1) for `m = 1`, equivalently Proposition 1.18 for `k = 1`, `m = 0`**.
  The proof is the compactness argument of [25, Proposition 2.1].
* `Polyfold.proposition_1_19_zero` (**Proposition 1.19 for `k = 0`**): if `f` is sc⁰ and
  `f : U_m → F_m` is `C¹` for every `m`, then `f` is sc¹, with `Df(x) = df(x)`.
* `Polyfold.corollary_1_20_zero` (**Corollary 1.20 for `k = 0`**): if `f : U → ℝᴺ` (or any
  finite-dimensional target with its constant sc-structure) is `C¹` on every level, then `f` is sc¹.
* `Polyfold.IsSc1With.scOperator_deriv`: at a smooth point `x ∈ U_∞`, `Df(x)` is an sc-operator
  (the "in particular" after Proposition 1.16), given the level-wise description of `Df`.

## What is formalized elsewhere

* The statements on all levels — Proposition 1.16 for every `m` (as an iff), Proposition 1.17,
  Proposition 1.18 (`f : U_{m+k} → F_m` is `C^k`), and Propositions 1.19 / Corollary 1.20 for all
  `k` under the hypothesis "`f : U_m → F_m` is `C^{k+1}` for every `m`" — are in
  `Polyfold/Chapter1/Levels.lean`, built on the base cases of this file.  The text's weaker
  hypothesis of Proposition 1.19 for `k ≥ 1` (`f : U_{m+l} → F_m` of class `C^{l+1}`, `l ≤ k`) is
  not formalized; see the module docstring there.

## What the text leaves implicit

* In Proposition 1.16 (2), `Df(x)` for `x ∈ U_m` is "the" bounded extension of `df(x)` from
  `E_m` to `E_{m−1}`: it is unique because `E_m` is dense in `E_{m−1}`, and it is the same
  operator as the `Df(x)` of Definition 1.14 (restricted to `E_{m−1}`), which is how it is read
  here (`IsSc1With.exists_delta_deriv` works with the `D` of Definition 1.14).
* Proposition 1.19's derivative `Df(x)` is `df(x)`, the derivative of `f : U₀ → F₀` at `x ∈ U₁`;
  the lifts to the levels are the derivatives of `f : U_m → F_m`, and their compatibility with
  `df(x)` uses the uniqueness of derivatives within `U_m` (so a hypothesis `IsScDomain E U`).
-/

open Set Filter Topology Function Metric

noncomputable section

namespace Polyfold

variable {E F : ScBanach} {U : Set (E 0)} {f : E 0 → F 0} {D : E 1 → E 0 →L[ℝ] F 0}

namespace IsSc1With

/-- Uniform continuity of `x ↦ Df(x)` on compact subsets of `E₀`: for `x ∈ U₁`, `K ⊆ E₀` compact
and `c > 0`, `‖Df(x')w − Df(x)w‖ ≤ c` for all `x' ∈ U₁` near `x` and all `w ∈ K`. -/
theorem exists_delta_deriv (h : IsSc1With U f D) {x : E 1} (hx : x ∈ E.lvlSet U 1) {K : Set (E 0)}
    (hK : IsCompact K) {c : ℝ} (hc : 0 < c) :
    ∃ δ > 0, ∀ x' ∈ E.lvlSet U 1, ‖x' - x‖ < δ → ∀ w ∈ K, ‖D x' w - D x w‖ ≤ c := by
  let Θ : E.lvlSet U 1 × E 0 → F 0 := fun q => D q.1.1 q.2 - D x q.2
  have hΘ : Continuous Θ := by
    have h1 : Continuous fun q : E.lvlSet U 1 × E 0 => D q.1.1 q.2 := by
      refine h.continuousOn_deriv.comp_continuous
        (f := fun q : E.lvlSet U 1 × E 0 => ((q.1.1 : E 1), q.2)) ?_ ?_
      · fun_prop
      · intro q; exact q.1.2
    exact h1.sub ((D x).continuous.comp continuous_snd)
  have key : ∀ᶠ y in 𝓝 (⟨x, hx⟩ : E.lvlSet U 1), ∀ w ∈ K, ‖Θ (y, w)‖ ≤ c := by
    refine hK.eventually_forall_of_forall_eventually (P := fun y w => ‖Θ (y, w)‖ ≤ c) fun w _ => ?_
    have h0 : Θ (⟨x, hx⟩, w) = 0 := by simp [Θ]
    have := hΘ.continuousAt.eventually_mem (x := (⟨x, hx⟩, w))
      (s := Metric.closedBall 0 c) (by rw [h0]; exact Metric.closedBall_mem_nhds 0 hc)
    exact this.mono fun q hq => by simpa using hq
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 key
  refine ⟨δ, hδ, fun x' hx' hxδ w hw => ?_⟩
  have := hδ' (y := ⟨x', hx'⟩) (by rw [Subtype.dist_eq, dist_eq_norm]; exact hxδ) w hw
  simpa [Θ] using this

/-- For an sc¹ map, `x ↦ Df(x)|_{E₁}` is continuous `U₁ → L(E₁, F₀)` in the operator norm
(Proposition 1.16 (1), `m = 1`: the continuity of `df`). -/
theorem continuousOn_deriv_clm (h : IsSc1With U f D) :
    ContinuousOn (fun x => (D x).comp (E.toBase 1)) (E.lvlSet U 1) := by
  intro x hx
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨K, hK, hKsub⟩ :=
    (E.incl_isCompactOperator 0).image_closedBall_subset_compact (f := (E.incl 0 : E 1 →ₗ[ℝ] E 0)) 1
  obtain ⟨δ, hδ, hδ'⟩ := h.exists_delta_deriv hx hK (half_pos hε)
  refine ⟨δ, hδ, fun x' hx' hxx' => ?_⟩
  rw [dist_eq_norm] at hxx' ⊢
  refine lt_of_le_of_lt ?_ (half_lt_self hε)
  rw [← ContinuousLinearMap.sub_comp]
  refine ContinuousLinearMap.opNorm_le_bound _ (half_pos hε).le fun v => ?_
  by_cases hv : v = 0
  · simp [hv]
  have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hunit : E.toBase 1 (‖v‖⁻¹ • v) ∈ K :=
    hKsub ⟨‖v‖⁻¹ • v, by
      rw [mem_closedBall, dist_zero_right, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hvn.ne'],
      rfl⟩
  have := hδ' x' hx' hxx' _ hunit
  rw [map_smul, map_smul, map_smul, ← smul_sub, norm_smul, norm_inv, norm_norm,
    ← div_eq_inv_mul, div_le_iff₀ hvn] at this
  simpa [ContinuousLinearMap.comp_apply, sub_apply] using this

/-- **Proposition 1.16 (1) for `m = 1` / Proposition 1.18 for `k = 1`, `m = 0`**: an sc¹ map
`f : U → F` is `C¹` as a map `U₁ → F₀`, with derivative `Df(x)|_{E₁}`. -/
theorem contDiffOn_base (h : IsSc1With U f D) : ContDiffOn ℝ 1 (f ∘ E.toBase 1) (E.lvlSet U 1) := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_hasFDerivWithinAt (by simp)]
  intro x hx
  refine ⟨E.lvlSet U 1, ?_, fun h0 => absurd h0 (by simp), fun y => (D y).comp (E.toBase 1),
    fun y hy => h.hasFDerivWithinAt y hy, ?_⟩
  · rw [insert_eq_of_mem hx]; exact self_mem_nhdsWithin
  · rw [contDiffOn_zero]; exact h.continuousOn_deriv_clm

/-- At a smooth point `x ∈ U_∞`, `Df(x) : E → F` is an sc-operator (the remark after
Proposition 1.16). -/
theorem scOperator_deriv (h : IsSc1With U f D) {x : E 1} (hx : x ∈ E.lvlSet U 1)
    (hs : x ∈ E.smoothLvl 1) : IsScOperator (D x) := by
  intro m
  -- lift `x` to level `m + 1`
  obtain ⟨y, hy⟩ := (E.mem_smoothLvl_iff).1 hs (m + 1)
  rw [E.shift_toBase] at hy
  have hyx : E.shift.toBase m y = x := E.toBase_injective 1 hy
  have hyU : y ∈ E.lvlSet U (m + 1) := by
    rw [ScBanach.mem_lvlSet, E.shift_toBase, hyx]; exact hx
  have hmem : ∀ v : E m, ((y, v) : E.tangent m) ∈ E.tangent.lvlSet (E.tangentSet U) m :=
    fun v => by rw [ScBanach.mem_lvlSet_tangentSet]; exact hyU
  -- the level-`m` map is the second component of the level-`m` tangent map
  set Tm : E m → F m := fun v => (levelMap (tangentMapWith f D) m ((y, v) : E.tangent m)).2 with hTm
  have hTm' : ∀ v, F.toBase m (Tm v) = D x (E.toBase m v) := by
    intro v
    have := congrArg Prod.snd (h.tangent_isSc0.toBase_levelMap (hmem v))
    rw [ScBanach.tangent_toBase, ScBanach.tangent_toBase] at this
    change F.toBase m (Tm v) = (D (E.shift.toBase m y) (E.toBase m v)) at this
    rw [this, hyx]
  have hcont : Continuous Tm := by
    have := (h.tangent_isSc0.continuousOn m).comp_continuous
      (f := fun v : E m => ((y, v) : E.tangent m)) (by fun_prop) hmem
    exact continuous_snd.comp this
  refine ⟨{ toFun := Tm
            map_add' := fun v w => F.toBase_injective m (by
              rw [map_add, hTm', hTm', hTm', map_add, map_add])
            map_smul' := fun a v => F.toBase_injective m (by
              rw [map_smul, hTm', hTm', map_smul, map_smul]; rfl)
            cont := hcont }, hTm'⟩

end IsSc1With

/-- **Proposition 1.19 for `k = 0`**: if `f : U → F` is sc⁰ and `f : U_m → F_m` is `C¹` for every
`m` (on a domain `U` with unique differentiability), then `f` is sc¹, with derivative
`Df(x) = df(x)` the derivative of `f : U₀ → F₀`. -/
theorem proposition_1_19_zero (hU : IsScDomain E U) (hf : IsSc0 E F U f)
    (h : ∀ m, ContDiffOn ℝ 1 (levelMap f m) (E.lvlSet U m)) :
    IsSc1With U f fun x => fderivWithin ℝ f U (E.toBase 1 x) := by
  have hf0 : levelMap f 0 = f := funext (levelMap_zero f)
  have hdiff : ∀ m, ∀ x ∈ E.lvlSet U m,
      HasFDerivWithinAt (levelMap f m) (fderivWithin ℝ (levelMap f m) (E.lvlSet U m) x)
        (E.lvlSet U m) x := fun m x hx =>
    ((h m).differentiableOn one_ne_zero x hx).hasFDerivWithinAt
  -- compatibility of the level derivatives with `df`
  have hcompat : ∀ m, ∀ x ∈ E.lvlSet U m, ∀ v : E m,
      F.toBase m (fderivWithin ℝ (levelMap f m) (E.lvlSet U m) x v) =
        fderivWithin ℝ f U (E.toBase m x) (E.toBase m v) := by
    intro m x hx v
    have h1 : HasFDerivWithinAt (F.toBase m ∘ levelMap f m)
        ((F.toBase m).comp (fderivWithin ℝ (levelMap f m) (E.lvlSet U m) x)) (E.lvlSet U m) x :=
      (F.toBase m).hasFDerivAt.comp_hasFDerivWithinAt x (hdiff m x hx)
    have h2 : HasFDerivWithinAt (f ∘ E.toBase m)
        ((fderivWithin ℝ f U (E.toBase m x)).comp (E.toBase m)) (E.lvlSet U m) x := by
      have := hdiff 0 (E.toBase m x) hx
      rw [hf0, ScBanach.lvlSet_zero] at this
      exact this.comp x (E.toBase m).hasFDerivWithinAt (E.mapsTo_toBase_lvlSet U m)
    have h1' : HasFDerivWithinAt (f ∘ E.toBase m)
        ((F.toBase m).comp (fderivWithin ℝ (levelMap f m) (E.lvlSet U m) x)) (E.lvlSet U m) x :=
      h1.congr (fun y hy => (hf.toBase_levelMap hy).symm) (hf.toBase_levelMap hx).symm
    have := (hU.uniqueDiffWithinAt m x hx).eq h1' h2
    exact congrArg (fun L : E m →L[ℝ] F 0 => L v) this
  refine ⟨hf, fun x hx => ?_, ?_⟩
  · -- condition (2): the derivative of `f : U₁ → F₀`
    have := hdiff 0 (E.toBase 1 x) hx
    rw [hf0, ScBanach.lvlSet_zero] at this
    exact this.comp x (E.toBase 1).hasFDerivWithinAt (E.mapsTo_toBase_lvlSet U 1)
  · -- condition (3): the tangent map is sc⁰
    have hTf' : ∀ m, ∀ p ∈ E.tangent.lvlSet (E.tangentSet U) m,
        F.tangent.toBase m ((levelMap f (m + 1) p.1,
            fderivWithin ℝ (levelMap f m) (E.lvlSet U m) (E.incl m p.1) p.2) : F.tangent m) =
          tangentMapWith f (fun x => fderivWithin ℝ f U (E.toBase 1 x)) (E.tangent.toBase m p) := by
      intro m p hp
      rw [ScBanach.mem_lvlSet_tangentSet] at hp
      rw [ScBanach.tangent_toBase, ScBanach.tangent_toBase]
      change ((F.shift.toBase m (levelMap f (m + 1) p.1), F.toBase m _) : F.tangent 0) =
        (levelMap f 1 (E.shift.toBase m p.1), fderivWithin ℝ f U (E.toBase 1 (E.shift.toBase m p.1))
          (E.toBase m p.2))
      have hp1 : E.shift.toBase m p.1 ∈ E.lvlSet U 1 := by
        rw [ScBanach.mem_lvlSet, ← E.shift_toBase]; exact hp
      refine Prod.ext ?_ ?_
      · apply F.toBase_injective 1
        rw [← F.shift_toBase, hf.toBase_levelMap hp, hf.toBase_levelMap hp1, E.shift_toBase]
      · rw [hcompat m _ (by exact hp) p.2, ← E.shift_toBase]
        rfl
    have hTf : ∀ m, ∀ p ∈ E.tangent.lvlSet (E.tangentSet U) m,
        levelMap (tangentMapWith f fun x => fderivWithin ℝ f U (E.toBase 1 x)) m p =
          ((levelMap f (m + 1) p.1,
            fderivWithin ℝ (levelMap f m) (E.lvlSet U m) (E.incl m p.1) p.2) : F.tangent m) :=
      fun m p hp => levelMap_eq_of_toBase_eq (hTf' m p hp)
    refine ⟨fun m p hp => ⟨_, hTf' m p hp⟩, fun m => ?_⟩
    refine ContinuousOn.congr ?_ (hTf m)
    rw [ScBanach.lvlSet_tangentSet]
    refine ContinuousOn.prodMk ?_ ?_
    · exact (hf.continuousOn (m + 1)).comp continuousOn_fst fun p hp => hp.1
    · have hcont : ContinuousOn (fun p : E.tangent m =>
          fderivWithin ℝ (levelMap f m) (E.lvlSet U m) (E.incl m p.1))
          (E.lvlSet U (m + 1) ×ˢ univ) :=
        ((h m).continuousOn_fderivWithin (hU.uniqueDiffWithinAt m) le_rfl).comp
          ((E.incl m).continuous.comp_continuousOn continuousOn_fst) fun p hp => hp.1
      exact hcont.clm_apply continuousOn_snd

/-- **Corollary 1.20 for `k = 0`**: a map `f : U → V` into a finite-dimensional space (with its
constant sc-structure) which is `C¹` on every level `U_m` is sc¹. -/
theorem corollary_1_20_zero {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (hU : IsScDomain E U) {f : E 0 → (ScBanach.const V) 0}
    (h : ∀ m, ContDiffOn ℝ 1 (f ∘ E.toBase m) (E.lvlSet U m)) : IsSc1 U f := by
  have hlvl : ∀ m, levelMap f m = f ∘ E.toBase m := fun m => funext fun x =>
    levelMap_eq_of_toBase_eq (ScBanach.const_toBase V m _)
  have hf : IsSc0 E (ScBanach.const V) U f :=
    ⟨fun m x _ => ⟨f (E.toBase m x), ScBanach.const_toBase V m _⟩,
      fun m => by rw [hlvl]; exact (h m).continuousOn⟩
  exact ⟨_, proposition_1_19_zero hU hf fun m => by rw [hlvl]; exact h m⟩

end Polyfold
