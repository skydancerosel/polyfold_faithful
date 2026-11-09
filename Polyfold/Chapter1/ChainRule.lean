import Polyfold.Chapter1.ScSmooth

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §1.3,
Theorem 1.3.1 (preprint 1.21) (the chain rule), with the proof of Appendix §1.4.2, and its consequences for sc^k and
sc-smooth maps.

# Theorem 1.3.1 (preprint 1.21): the sc-chain rule

## The text, paraphrased

(Theorem 1.3.1 (preprint 1.21)) Let `U ⊂ C ⊂ E`, `V ⊂ D ⊂ F`, `W ⊂ Q ⊂ G` be relatively open subsets of partial
quadrants in sc-Banach spaces and `f : U → V`, `g : V → W` sc¹.  Then `g ∘ f : U → W` is sc¹ and
`T(g ∘ f) = Tg ∘ Tf`.  (§1.4.2) *Proof*: fix `x ∈ U₁` and `h ∈ E₁` small with `x + h ∈ U₁`.  Then
`g(f(x+h)) − g(f(x)) − Dg(f(x))Df(x)h` is the sum of two integrals over the segment
`y_t = t f(x+h) + (1−t) f(x) ⊂ V₁`: `∫₀¹ Dg(y_t)[f(x+h) − f(x) − Df(x)h] dt`, which is `o(|h|₁)`
because `(y, k) ↦ Dg(y)k` is continuous on `V₁ ⊕ F₀` and `y_t → f(x)` in `F₁` uniformly in `t`, and
`∫₀¹ [Dg(y_t) − Dg(f(x))] Df(x)h dt`, which is `o(|h|₁)` because `{Df(x) h/|h|₁}` has compact
closure in `F₀` (the inclusion `E₁ → E₀` is compact), so that `Dg(y_t) → Dg(f(x))` uniformly on it.
Hence `D(g ∘ f)(x) = Dg(f(x)) ∘ Df(x)`, `T(g ∘ f)` is sc⁰ and `T(g ∘ f) = Tg ∘ Tf`.

## What is formalized

* `Polyfold.IsSc1With.comp`: if `g` is sc¹ on `V` with derivatives `Dg`, `f` is sc¹ on `U` with
  derivatives `Df`, `f(U) ⊆ V`, and `V₁` is open-in-convex, then `g ∘ f` is sc¹ on `U` with
  derivatives `x ↦ Dg(f(x)) ∘ Df(x)`.
* `Polyfold.theorem_1_3_1` (**Theorem 1.3.1 (preprint 1.21)**): for `U`, `V` relatively open in partial quadrants
  (`IsRelOpenInQuadrant`), `g ∘ f` is sc¹ and `T(g ∘ f) = Tg ∘ Tf` on `TU`.
  `Polyfold.theorem_1_3_1'` is the same for `IsScDomain` hypotheses (the form that iterates).
* `Polyfold.IsSck.comp`, `Polyfold.IsScSmooth.comp`: the composition of sc^k (sc-smooth) maps
  is sc^k (sc-smooth), by induction on `k` with `IsScDomain.tangentSet`.
* `Polyfold.IsSck.congr`: sc^k depends only on the values on `U`.

## What the text leaves implicit, and the choices made

* The two integrals of the text are replaced by the one-variable mean value inequality
  (`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`) applied to
  `t ↦ g(y_t) − t·Dg(f(x))(f(x+h) − f(x))` on `[0,1]`, whose derivative is
  `[Dg(y_t) − Dg(f(x))](f(x+h) − f(x))`; this bounds the difference
  `g(f(x+h)) − g(f(x)) − Dg(f(x))(f(x+h) − f(x))` and avoids the Bochner integral.  The remaining
  term `Dg(f(x))[f(x+h) − f(x) − Df(x)h]` is `o(|h|₁)` directly, since `Dg(f(x))` is bounded on
  `F₀`; the text's first integral is not needed.
* "For `|h|₁` small, `y_t ∈ V₁`": this uses that `V₁ = O₁ ∩ C₁` with `O₁` open and `C₁` convex
  (the only place where the structure of `V` enters), and the continuity of `f : U₁ → F₁`.
* The uniform convergence on the compact set is `IsCompact.eventually_forall_of_forall_eventually`
  applied to `(y, b, w) ↦ [Dg(y) − Dg(f(x))](w + b)` on `V₁ × F₀ × K`, `K` a compact set
  containing `Df(x)(ι(B̄₁))`; the text argues with sequences and subsequences.
* The equation `T(g ∘ f) = Tg ∘ Tf` is a statement about the chosen derivatives; it holds on `TU`
  because the derivative is unique on `U₁` (`IsSc1With.eq_of_uniqueDiffWithinAt`, which needs the
  quadrant structure of `U`).  The existence part needs no hypothesis on `U` at all.
* The text's `W ⊂ Q ⊂ G` plays no role.
-/

open Set Filter Topology Function Asymptotics

noncomputable section

namespace Polyfold

variable {E F G : ScBanach} {U : Set (E 0)} {V : Set (F 0)} {f : E 0 → F 0} {g : F 0 → G 0}
  {Df : E 1 → E 0 →L[ℝ] F 0} {Dg : F 1 → F 0 →L[ℝ] G 0}

namespace IsSc1With

/-- The mean value inequality along a segment in `V₁` (the text's second integral): if
`y₀ + t k ∈ V₁` for `t ∈ [0,1]` and `‖[Dg(y₀ + t k) − Dg(y₀)](ι k)‖ ≤ C` there, then
`‖g(ι(y₀ + k)) − g(ι y₀) − Dg(y₀)(ι k)‖ ≤ C`. -/
private lemma norm_sub_le_of_segment (hg : IsSc1With V g Dg) {y₀ k : F 1}
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, y₀ + t • k ∈ F.lvlSet V 1) {C : ℝ}
    (hC : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Dg (y₀ + t • k) (F.toBase 1 k) - Dg y₀ (F.toBase 1 k)‖ ≤ C) :
    ‖g (F.toBase 1 (y₀ + k)) - g (F.toBase 1 y₀) - Dg y₀ (F.toBase 1 k)‖ ≤ C := by
  set φ : ℝ → G 0 := fun t => g (F.toBase 1 (y₀ + t • k)) - t • Dg y₀ (F.toBase 1 k) with hφ
  have hγ : ∀ t : ℝ, HasDerivAt (fun t : ℝ => y₀ + t • k) k t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const k).const_add y₀
  have hder : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt φ
      (Dg (y₀ + t • k) (F.toBase 1 k) - Dg y₀ (F.toBase 1 k)) (Icc 0 1) t := by
    intro t ht
    have h1 : HasDerivWithinAt (fun t : ℝ => g (F.toBase 1 (y₀ + t • k)))
        (((Dg (y₀ + t • k)).comp (F.toBase 1)) k) (Icc 0 1) t :=
      HasFDerivWithinAt.comp_hasDerivWithinAt (l := g ∘ F.toBase 1) (f := fun t : ℝ => y₀ + t • k)
        t (hg.hasFDerivWithinAt _ (hseg t ht)) (hγ t).hasDerivWithinAt hseg
    have h2 : HasDerivWithinAt (fun t : ℝ => t • Dg y₀ (F.toBase 1 k)) (Dg y₀ (F.toBase 1 k))
        (Icc 0 1) t := by
      simpa using ((hasDerivAt_id t).smul_const (Dg y₀ (F.toBase 1 k))).hasDerivWithinAt
    exact h1.sub h2
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hC (convex_Icc 0 1)
    (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
  have h01 : φ 1 - φ 0 = g (F.toBase 1 (y₀ + k)) - g (F.toBase 1 y₀) - Dg y₀ (F.toBase 1 k) := by
    simp only [hφ, one_smul, zero_smul, add_zero, sub_zero]; abel
  rwa [h01, sub_zero, norm_one, mul_one] at this

/-- The uniform smallness of `[Dg(y) − Dg(y₀)](w + b)` for `y` near `y₀` in `V₁`, `w` in a compact
set `K` and `b` small (the compactness argument of the text). -/
private lemma exists_delta (hg : IsSc1With V g Dg) {y₀ : F 1} (hy₀ : y₀ ∈ F.lvlSet V 1)
    {K : Set (F 0)} (hK : IsCompact K) {c : ℝ} (hc : 0 < c) :
    ∃ δ > 0, ∀ y ∈ F.lvlSet V 1, ‖y - y₀‖ < δ → ∀ w ∈ K, ∀ b : F 0, ‖b‖ < δ →
      ‖Dg y (w + b) - Dg y₀ (w + b)‖ ≤ c := by
  -- the continuous map `(y, b, w) ↦ [Dg(y) − Dg(y₀)](w + b)` on the subtype `V₁`
  let Θ : (F.lvlSet V 1 × F 0) × F 0 → G 0 :=
    fun q => Dg q.1.1.1 (q.2 + q.1.2) - Dg y₀ (q.2 + q.1.2)
  have hΘ : Continuous Θ := by
    have h1 : Continuous fun q : (F.lvlSet V 1 × F 0) × F 0 => Dg q.1.1.1 (q.2 + q.1.2) := by
      refine hg.continuousOn_deriv.comp_continuous
        (f := fun q : (F.lvlSet V 1 × F 0) × F 0 => ((q.1.1.1 : F 1), q.2 + q.1.2)) ?_ ?_
      · fun_prop
      · intro q; exact q.1.1.2
    exact h1.sub ((Dg y₀).continuous.comp (by fun_prop))
  have key : ∀ᶠ q in 𝓝 ((⟨y₀, hy₀⟩, (0 : F 0)) : F.lvlSet V 1 × F 0), ∀ w ∈ K,
      ‖Θ (q, w)‖ ≤ c := by
    refine hK.eventually_forall_of_forall_eventually (P := fun q w => ‖Θ (q, w)‖ ≤ c) fun w _ => ?_
    have h0 : Θ ((⟨y₀, hy₀⟩, 0), w) = 0 := by simp [Θ]
    have := hΘ.continuousAt.eventually_mem (x := ((⟨y₀, hy₀⟩, 0), w))
      (s := Metric.closedBall 0 c) (by rw [h0]; exact Metric.closedBall_mem_nhds 0 hc)
    exact this.mono fun q hq => by simpa using hq
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 key
  refine ⟨δ, hδ, fun y hy hyδ w hw b hb => ?_⟩
  have := hδ' (y := (⟨y, hy⟩, b)) ?_ w hw
  · simpa [Θ] using this
  · rw [Prod.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_zero_right]
    exact max_lt hyδ hb

/-- The derivative part of the chain rule: `g ∘ f : U₁ → G₀` is differentiable at `x ∈ U₁` within
`U₁` with derivative `Dg(f(x)) ∘ Df(x)`.  Needs `V₁` open-in-convex. -/
theorem hasFDerivWithinAt_comp
    (hV : ∃ O C : Set (F 1), IsOpen O ∧ Convex ℝ C ∧ F.lvlSet V 1 = O ∩ C)
    (hg : IsSc1With V g Dg) (hf : IsSc1With U f Df) (hfV : MapsTo f U V) {x : E 1}
    (hx : x ∈ E.lvlSet U 1) :
    HasFDerivWithinAt (g ∘ f ∘ E.toBase 1)
      (((Dg (levelMap f 1 x)).comp (Df x)).comp (E.toBase 1)) (E.lvlSet U 1) x := by
  obtain ⟨O, C, hO, hC, hVOC⟩ := hV
  -- notation
  set ι := E.toBase 1 with hι
  set ιF := F.toBase 1 with hιF
  set f₁ := levelMap f 1 with hf₁
  set y₀ := f₁ x with hy₀
  have hy₀V : y₀ ∈ F.lvlSet V 1 := hf.isSc0.levelMap_mapsTo hfV 1 hx
  have hιF_f₁ : ∀ z ∈ E.lvlSet U 1, ιF (f₁ z) = f (ι z) := fun z hz => hf.isSc0.toBase_levelMap hz
  -- the compact set `K ⊇ Df(x)(ι(B̄₁))`
  obtain ⟨K₀, hK₀, hK₀sub⟩ :=
    (E.incl_isCompactOperator 0).image_closedBall_subset_compact (f := (E.incl 0 : E 1 →ₗ[ℝ] E 0)) 1
  set K := Df x '' K₀ with hK
  have hKc : IsCompact K := hK₀.image (Df x).continuous
  -- the radius of a ball around `y₀` inside `O`
  have hy₀O : y₀ ∈ O := (hVOC ▸ hy₀V).1
  obtain ⟨ρ, hρ, hρO⟩ := Metric.isOpen_iff.1 hO y₀ hy₀O
  -- the little-o statement
  rw [hasFDerivWithinAt_iff_isLittleO, isLittleO_iff]
  intro c hc
  -- the two tolerances
  have hc2 : 0 < c / 2 := by positivity
  obtain ⟨δ, hδ, hδ'⟩ := hg.exists_delta hy₀V hKc hc2
  set ε := min (δ / 2) (c / 2 / (‖Dg y₀‖ + 1)) with hε
  have hε0 : 0 < ε := lt_min (by positivity) (by positivity)
  have hεδ : ε ≤ δ / 2 := min_le_left _ _
  have hεc : ‖Dg y₀‖ * ε ≤ c / 2 := by
    calc ‖Dg y₀‖ * ε ≤ (‖Dg y₀‖ + 1) * (c / 2 / (‖Dg y₀‖ + 1)) :=
          mul_le_mul (by linarith) (min_le_right _ _) hε0.le (by positivity)
      _ = c / 2 := by field_simp
  -- the eventual facts
  have ev1 : ∀ᶠ z in 𝓝[E.lvlSet U 1] x, z ∈ E.lvlSet U 1 := self_mem_nhdsWithin
  have ev2 : ∀ᶠ z in 𝓝[E.lvlSet U 1] x, dist (f₁ z) (f₁ x) < min ρ δ :=
    Metric.tendsto_nhds.1 (hf.isSc0.continuousOn 1 x hx) _ (lt_min hρ hδ)
  have ev3 : ∀ᶠ z in 𝓝[E.lvlSet U 1] x,
      ‖(f ∘ ι) z - (f ∘ ι) x - ((Df x).comp ι) (z - x)‖ ≤ ε * ‖z - x‖ :=
    isLittleO_iff.1 (hasFDerivWithinAt_iff_isLittleO.1 (hf.hasFDerivWithinAt x hx)) hε0
  filter_upwards [ev1, ev2, ev3] with z hz hz2 hz3
  -- the remainder of `f`
  set r := f (ι z) - f (ι x) - Df x (ι (z - x)) with hr
  have hr' : ‖r‖ ≤ ε * ‖z - x‖ := hz3
  have hsplit : f (ι z) - f (ι x) = Df x (ι (z - x)) + r := by rw [hr]; abel
  -- the increment `k = f₁ z − y₀ ∈ F₁`
  set k := f₁ z - y₀ with hk
  have hιk : ιF k = f (ι z) - f (ι x) := by
    rw [hk, map_sub, hιF_f₁ z hz, hy₀, hιF_f₁ x hx]
  have hknorm : ‖k‖ < min ρ δ := by rwa [hk, ← dist_eq_norm]
  -- the segment lies in `V₁`
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, y₀ + t • k ∈ F.lvlSet V 1 := by
    intro t ht
    rw [hVOC]
    refine ⟨hρO ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg ht.1]
      calc t * ‖k‖ ≤ 1 * ‖k‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
        _ < ρ := by rw [one_mul]; exact lt_of_lt_of_le hknorm (min_le_left _ _)
    · have h1 : y₀ ∈ C := (hVOC ▸ hy₀V).2
      have h2 : f₁ z ∈ C := (hVOC ▸ hf.isSc0.levelMap_mapsTo hfV 1 hz).2
      have := hC.add_smul_sub_mem h1 h2 ht
      rwa [hk]
  -- the main estimate: `‖g(f z) − g(f x) − Dg(y₀)(ι k)‖ ≤ (c/2) ‖z − x‖`
  have hmain : ‖g (f (ι z)) - g (f (ι x)) - Dg y₀ (ιF k)‖ ≤ c / 2 * ‖z - x‖ := by
    by_cases hzx : z = x
    · subst hzx
      simp [hk, hy₀]
    have hs : 0 < ‖z - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hzx)
    set s := ‖z - x‖ with hs_def
    set u : E 1 := s⁻¹ • (z - x) with hu
    have hu1 : u ∈ Metric.closedBall (0 : E 1) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right, hu, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ hs.ne']
    set w₁ := Df x (ι u) with hw₁
    have hw₁K : w₁ ∈ K := ⟨ι u, hK₀sub ⟨u, hu1, rfl⟩, rfl⟩
    set b := s⁻¹ • r with hb
    have hbδ : ‖b‖ < δ := by
      rw [hb, norm_smul, norm_inv, norm_norm]
      calc s⁻¹ * ‖r‖ ≤ s⁻¹ * (ε * s) := by gcongr
        _ = ε := by field_simp
        _ ≤ δ / 2 := hεδ
        _ < δ := by linarith
    have hιk' : ιF k = s • (w₁ + b) := by
      rw [hιk, hsplit, hw₁, hb, smul_add, ← map_smul, ← map_smul, hu, smul_inv_smul₀ hs.ne',
        smul_inv_smul₀ hs.ne']
    have hbound : ∀ t ∈ Icc (0 : ℝ) 1,
        ‖Dg (y₀ + t • k) (ιF k) - Dg y₀ (ιF k)‖ ≤ c / 2 * s := by
      intro t ht
      have hyδ : ‖y₀ + t • k - y₀‖ < δ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        calc t * ‖k‖ ≤ 1 * ‖k‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
          _ < δ := by rw [one_mul]; exact lt_of_lt_of_le hknorm (min_le_right _ _)
      have := hδ' _ (hseg t ht) hyδ w₁ hw₁K b hbδ
      rw [hιk', map_smul, map_smul, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hs,
        mul_comm]
      exact mul_le_mul_of_nonneg_right this hs.le
    have := hg.norm_sub_le_of_segment hseg hbound
    rwa [hk, add_sub_cancel, hιF_f₁ z hz, hy₀, hιF_f₁ x hx] at this
  -- assemble
  have hsecond : ‖Dg y₀ r‖ ≤ c / 2 * ‖z - x‖ :=
    calc ‖Dg y₀ r‖ ≤ ‖Dg y₀‖ * ‖r‖ := (Dg y₀).le_opNorm r
      _ ≤ ‖Dg y₀‖ * (ε * ‖z - x‖) := by gcongr
      _ = ‖Dg y₀‖ * ε * ‖z - x‖ := by ring
      _ ≤ c / 2 * ‖z - x‖ := by gcongr
  have hid : (g ∘ f ∘ ι) z - (g ∘ f ∘ ι) x - (((Dg y₀).comp (Df x)).comp ι) (z - x)
      = (g (f (ι z)) - g (f (ι x)) - Dg y₀ (ιF k)) + Dg y₀ r := by
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply]
    rw [hιk, hsplit, map_add]
    abel
  rw [hid]
  calc ‖(g (f (ι z)) - g (f (ι x)) - Dg y₀ (ιF k)) + Dg y₀ r‖
      ≤ ‖g (f (ι z)) - g (f (ι x)) - Dg y₀ (ιF k)‖ + ‖Dg y₀ r‖ := norm_add_le _ _
    _ ≤ c / 2 * ‖z - x‖ + c / 2 * ‖z - x‖ := add_le_add hmain hsecond
    _ = c * ‖z - x‖ := by ring

/-- The tangent map of a composition, with the composed derivatives, agrees with the composition
of the tangent maps on `TU`. -/
lemma tangentMapWith_comp (hg : IsSc0 F G V g) (hf : IsSc0 E F U f) (hfV : MapsTo f U V) :
    EqOn (tangentMapWith (g ∘ f) fun x => (Dg (levelMap f 1 x)).comp (Df x))
      (tangentMapWith g Dg ∘ tangentMapWith f Df) (E.tangentSet U) := by
  intro p hp
  change (levelMap (g ∘ f) 1 p.1, Dg (levelMap f 1 p.1) (Df p.1 p.2)) =
    (levelMap g 1 (levelMap f 1 p.1), Dg (levelMap f 1 p.1) (Df p.1 p.2))
  rw [hg.levelMap_comp hf hfV hp]

/-- **The chain rule for sc¹ maps with given derivatives** (Theorem 1.3.1 (preprint 1.21), existence part): if `g`
is sc¹ on `V` with derivatives `Dg`, `f` is sc¹ on `U` with derivatives `Df`, `f(U) ⊆ V`, and `V₁`
is open-in-convex, then `g ∘ f` is sc¹ on `U` with derivatives `Dg(f(x)) ∘ Df(x)`. -/
theorem comp (hV : ∃ O C : Set (F 1), IsOpen O ∧ Convex ℝ C ∧ F.lvlSet V 1 = O ∩ C)
    (hg : IsSc1With V g Dg) (hf : IsSc1With U f Df) (hfV : MapsTo f U V) :
    IsSc1With U (g ∘ f) fun x => (Dg (levelMap f 1 x)).comp (Df x) where
  isSc0 := hg.isSc0.comp hf.isSc0 hfV
  hasFDerivWithinAt _ hx := hg.hasFDerivWithinAt_comp hV hf hfV hx
  tangent_isSc0 :=
    (hg.tangent_isSc0.comp hf.tangent_isSc0 (hf.tangentMapWith_mapsTo hfV)).congr
      (tangentMapWith_comp hg.isSc0 hf.isSc0 hfV).symm

end IsSc1With

/-- **Theorem 1.3.1 (preprint 1.21) (Chain Rule)**, for domains with the level-wise regularity `IsScDomain`: if
`f : U → V` and `g : V → G` are sc¹, then `g ∘ f` is sc¹ and `T(g ∘ f) = Tg ∘ Tf` on `TU`. -/
theorem theorem_1_3_1' (hU : IsScDomain E U) (hV : IsScDomain F V) (hf : IsSc1 U f) (hg : IsSc1 V g)
    (hfV : MapsTo f U V) :
    IsSc1 U (g ∘ f) ∧ EqOn (tangentMap U (g ∘ f)) (tangentMap V g ∘ tangentMap U f)
      (E.tangentSet U) := by
  have hcomp := hg.isSc1With_scDeriv.comp (hV.relOpenConvex 1) hf.isSc1With_scDeriv hfV
  refine ⟨hcomp.isSc1, ?_⟩
  exact (IsSc1.tangentMap_eqOn hcomp (hU.uniqueDiffWithinAt 1)).trans
    (IsSc1With.tangentMapWith_comp hg.isSc0 hf.isSc0 hfV)

/-- **Theorem 1.3.1 (preprint 1.21) (Chain Rule)**: let `U ⊂ C ⊂ E` and `V ⊂ D ⊂ F` be relatively open subsets of
partial quadrants in sc-Banach spaces, and `f : U → V`, `g : V → G` sc¹.  Then `g ∘ f : U → G` is
sc¹ and `T(g ∘ f) = Tg ∘ Tf` on `TU`. -/
theorem theorem_1_3_1 {C : Set (E 0)} {D : Set (F 0)} (hU : IsRelOpenInQuadrant E C U)
    (hV : IsRelOpenInQuadrant F D V) (hf : IsSc1 U f) (hg : IsSc1 V g) (hfV : MapsTo f U V) :
    IsSc1 U (g ∘ f) ∧ EqOn (tangentMap U (g ∘ f)) (tangentMap V g ∘ tangentMap U f)
      (E.tangentSet U) :=
  theorem_1_3_1' hU.isScDomain hV.isScDomain hf hg hfV

/-- The tangent maps of two sc¹ maps agreeing on `U` agree on `TU` (on a domain with unique
differentiability). -/
lemma IsSc1.tangentMap_congr (hU : IsScDomain E U) (hf : IsSc1 U f) {f' : E 0 → F 0}
    (hff' : EqOn f f' U) : EqOn (tangentMap U f) (tangentMap U f') (E.tangentSet U) := by
  have h1 : IsSc1With U f' (scDeriv U f) := hf.isSc1With_scDeriv.congr hff'
  refine EqOn.trans ?_ (IsSc1.tangentMap_eqOn h1 (hU.uniqueDiffWithinAt 1)).symm
  intro p hp
  change (levelMap f 1 p.1, scDeriv U f p.1 p.2) = (levelMap f' 1 p.1, scDeriv U f p.1 p.2)
  rw [IsSc0.levelMap_congr hff' hp]

/-- sc^k depends only on the values on `U` (on a domain with unique differentiability). -/
theorem IsSck.congr : ∀ {k : ℕ} {E F : ScBanach} {U : Set (E 0)} {f f' : E 0 → F 0},
    IsScDomain E U → EqOn f f' U → IsSck k E F U f → IsSck k E F U f'
  | 0, _, _, _, _, _, _, hff', h => IsSc0.congr h hff'
  | k + 1, _, _, _, _, _, hU, hff', h =>
    ⟨h.1.congr hff', IsSck.congr (k := k) hU.tangentSet (h.1.tangentMap_congr hU hff') h.2⟩

/-- **The chain rule for sc^k maps** (Theorem 1.3.1 (preprint 1.21) iterated): the composition of sc^k maps between
relatively open subsets of partial quadrants (or `IsScDomain`s) is sc^k. -/
theorem IsSck.comp : ∀ {k : ℕ} {E F G : ScBanach} {U : Set (E 0)} {V : Set (F 0)} {f : E 0 → F 0}
    {g : F 0 → G 0}, IsScDomain E U → IsScDomain F V → IsSck k F G V g → IsSck k E F U f →
    MapsTo f U V → IsSck k E G U (g ∘ f)
  | 0, _, _, _, _, _, _, _, _, _, hg, hf, hfV => IsSc0.comp hg hf hfV
  | k + 1, _, _, _, _, _, _, _, hU, hV, hg, hf, hfV => by
    obtain ⟨h1, h2⟩ := theorem_1_3_1' hU hV hf.1 hg.1 hfV
    refine ⟨h1, ?_⟩
    have := IsSck.comp (k := k) hU.tangentSet hV.tangentSet hg.2 hf.2 (hf.1.tangentMap_mapsTo hfV)
    exact IsSck.congr hU.tangentSet h2.symm this

/-- **The chain rule for sc-smooth maps**: the composition of sc-smooth maps is sc-smooth. -/
theorem IsScSmooth.comp (hU : IsScDomain E U) (hV : IsScDomain F V) (hg : IsScSmooth V g)
    (hf : IsScSmooth U f) (hfV : MapsTo f U V) : IsScSmooth U (g ∘ f) :=
  fun k => IsSck.comp hU hV (hg k) (hf k) hfV

/-- The chain rule for sc^k maps between relatively open subsets of partial quadrants, in the
text's hypotheses. -/
theorem IsSck.comp_of_isRelOpenInQuadrant {k : ℕ} {C : Set (E 0)} {D : Set (F 0)}
    (hU : IsRelOpenInQuadrant E C U) (hV : IsRelOpenInQuadrant F D V) (hg : IsSck k F G V g)
    (hf : IsSck k E F U f) (hfV : MapsTo f U V) : IsSck k E G U (g ∘ f) :=
  IsSck.comp hU.isScDomain hV.isScDomain hg hf hfV

end Polyfold
