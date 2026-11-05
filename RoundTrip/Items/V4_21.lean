import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_21

/-!
Round trip for V4_21 (Lemma 4.11, uniqueness: small zeros `a + y` of
`f(x) = (1 − p)(x − t(x))` lie on the graph of `δ`).  `A` is the conjunction of the types of
`GraphData.qL_lvlDeriv_zero`, `GraphData.lvlDeriv_zero_of_mem_N`,
`GraphData.exists_contraction_radius` and `GraphData.eq_of_p_eq` (no universe parameters).

A ⇒ B (proved).  B's setting yields the project's `GraphData` (`graphData`, as in V4_19: B's
sc-complement `Y` is a closed good complement, `p` corestricts to `T₀O`, `Dt(0)E` is the project's
`tangentSpace`).  Then, with `θ` small and `r` from A's `exists_contraction_radius` (level `1`):
* `mem_retract_of_zero`: a zero `x ∈ U` of `f` with `|x|₀` small lies on `O` and has
  `‖x‖₁ < r`.  Indeed `f(x) = 0` says `n = x − t(x) ∈ T₀O`; `u = t(x)` is small in `E₁` (the lift
  `t¹ : U → E₁` is continuous at `0`), so `x₁ = u₁ + n₁` and `u₁` lie in `C₁ ∩ B(0, r)`, and A's mean
  value estimate with `t₁(x₁) = t₁(u₁) = u₁` and A's `Dt(0)n₁ = n₁` give `‖n₁‖₁ ≤ θ‖n₁‖₁`, so
  `n = 0` (the text's argument "`a₁ = a`" of Lemma 4.12).
* For `x = a + y` (small): `x ∈ O`, A's contraction estimate gives `‖(1 − p)x‖₁ ≤ ‖1 − p‖θ‖x‖₁`,
  hence `a = p(x) ∈ C` (`GraphData.p_mem_C`, the good complement property); so `δ(a)` is defined
  by B's hypotheses on `δ`, `a + δ(a)` is a small zero (continuity of `δ` at `0`), hence on `O`;
  `p(a + y) = p(a + δ(a)) = a` and A's `eq_of_p_eq` (with the contraction estimate on `O₁`) give
  `a + y = a + δ(a)`.

B ⇒ A is not proved (genuine generality, see the JSON).
-/

namespace RoundTrip.V4_21
open Polyfold Set Metric

def A : Prop :=
  type_of% @Polyfold.GraphData.qL_lvlDeriv_zero ∧
  type_of% @Polyfold.GraphData.lvlDeriv_zero_of_mem_N ∧
  type_of% @Polyfold.GraphData.exists_contraction_radius ∧
  type_of% @Polyfold.GraphData.eq_of_p_eq

theorem A_holds : A :=
  ⟨@Polyfold.GraphData.qL_lvlDeriv_zero, @Polyfold.GraphData.lvlDeriv_zero_of_mem_N,
    @Polyfold.GraphData.exists_contraction_radius, @Polyfold.GraphData.eq_of_p_eq⟩

section Glue

variable {E : ScBanach} {C : Set (E.lvl 0)}

/-- The project's `ScRetraction.IsScPlus` is B's Definition 4.4 (cf. V4_9). -/
theorem isScPlus_iff (R : ScRetraction E C) : R.IsScPlus ↔ IsScPlusRetractionB R := by
  constructor
  · intro hR
    refine ⟨fun m x hx => ?_, E.liftOne ∘ R, fun x hx => IsScPlus.toBase_lift hR hx,
      hR.isScSmooth_lift⟩
    obtain ⟨y, -, hy⟩ := hR.mem_lvlSet_succ m hx
    exact ⟨y, hy⟩
  · rintro ⟨-, g, hg, hgs⟩
    exact (IsScPlus.iff_exists R.isScDomain).2 ⟨g, hgs, hg⟩

variable {t : ScRetraction E C} {Y : Submodule ℝ (E.lvl 0)} {p : E.lvl 0 →L[ℝ] E.lvl 0}

lemma isCompl_of (h : IsSetting49B t Y p) : IsCompl (tangentAtZero t) Y := by
  have := h.2.2.2.1.2.2 0
  rwa [ScBanach.levelSub_zero, ScBanach.levelSub_zero] at this

lemma goodComplement_of (h : IsSetting49B t Y p) : IsGoodComplement E C (tangentAtZero t) Y :=
  ⟨isCompl_of h, h.2.2.2.2.1⟩

lemma mem_of (h : IsSetting49B t Y p) (x : E.lvl 0) : p x ∈ tangentAtZero t := by
  have hsup : x ∈ tangentAtZero t ⊔ Y := by rw [(isCompl_of h).sup_eq_top]; exact Submodule.mem_top
  obtain ⟨n, hn, y, hy, rfl⟩ := Submodule.mem_sup.1 hsup
  rw [map_add, h.2.2.2.2.2.1 n hn, h.2.2.2.2.2.2 y hy, add_zero]
  exact hn

lemma zero_mem_lvlSet (h : IsSetting49B t Y p) : (0 : E.lvl 1) ∈ E.lvlSet t.retract 1 := by
  rw [ScBanach.mem_lvlSet, map_zero]; exact h.2.1

/-- **B's setting is the project's `GraphData`** (with `p` corestricted to `T₀O`). -/
noncomputable def graphData (h : IsSetting49B t Y p) : GraphData E C where
  T := t
  isScPlus := (isScPlus_iff t).2 h.1
  zero_mem := h.2.1
  N := tangentAtZero t
  N_eq := (tangentSpace_eq_coe_submodule t (zero_mem_lvlSet h)).symm
  goodPosition := ⟨h.2.2.1, Y, goodComplement_of h⟩
  Y := Y
  goodComplement := goodComplement_of h
  isClosed_Y := h.2.2.2.1.2.1.isClosed
  p := p.codRestrict _ (mem_of h)
  p_apply_N := fun n => Subtype.ext (h.2.2.2.2.2.1 n n.2)
  p_apply_Y := fun y hy => Subtype.ext (by
    change p y = 0
    exact h.2.2.2.2.2.2 y hy)

end Glue

section Zeros

variable {E : ScBanach} {C : Set (E.lvl 0)} (d : GraphData E C)

lemma mem_C_of_mem_U {z : E.lvl 0} (hz : z ∈ d.T.U) : z ∈ C := by
  obtain ⟨O', -, hU⟩ := d.T.relOpen.relOpen
  rw [hU] at hz; exact hz.2

/-- The text's "`a₁ = a`" step: a zero `x ∈ U` of `f` whose level-`1` data lie in `B(0, r)` is
fixed by `t`.  Uses A's mean value estimate (`hmvt`) and `Dt(0) = 1` on `N` (`hD`). -/
theorem apply_eq_of_zero {θ r : ℝ} (hθ1 : θ < 1)
    (hD : ∀ v : E.lvl 1, E.toBase 1 v ∈ d.N → d.T.lvlDeriv 0 0 v = v)
    (hmvt : ∀ z ∈ E.lvlSet C 1, ∀ z' ∈ E.lvlSet C 1, ‖z‖ < r → ‖z'‖ < r →
        ‖(d.T.lvlMap 0 z' - d.T.lvlMap 0 z) - d.T.lvlDeriv 0 0 (z' - z)‖ ≤ θ * ‖z' - z‖)
    {x : E.lvl 0} (hx : x ∈ d.T.U) (hf : (d.p (x - d.T x) : E.lvl 0) = x - d.T x)
    (hu : ‖E.liftOne (d.T x)‖ < r)
    (hxr : ‖E.liftOne (d.T x) + d.liftN 1 (d.p (x - d.T x))‖ < r) :
    d.T x = x := by
  set u₁ := E.liftOne (d.T x) with hu₁
  set n₁ := d.liftN 1 (d.p (x - d.T x)) with hn₁
  have htx : d.T x ∈ d.T.retract := d.T.apply_mem_retract hx
  have hu1 : E.toBase 1 u₁ = d.T x := IsScPlus.toBase_lift d.isScPlus hx
  have hn1 : E.toBase 1 n₁ = x - d.T x := by rw [hn₁, d.toBase_liftN, hf]
  have hx1 : E.toBase 1 (u₁ + n₁) = x := by rw [map_add, hu1, hn1]; abel
  have hx1U : u₁ + n₁ ∈ E.lvlSet d.T.U 1 := by rw [ScBanach.mem_lvlSet, hx1]; exact hx
  have hx1C : u₁ + n₁ ∈ E.lvlSet C 1 := by rw [ScBanach.mem_lvlSet, hx1]; exact mem_C_of_mem_U d hx
  have hu1C : u₁ ∈ E.lvlSet C 1 := by
    rw [ScBanach.mem_lvlSet, hu1]; exact mem_C_of_mem_U d (d.T.retract_subset htx)
  have hTx : d.T.lvlMap 0 (u₁ + n₁) = u₁ := by
    apply E.toBase_injective 1
    have h := d.isScPlus.toBase_lvlMap 0 hx1U
    refine h.trans ?_
    change d.T (E.toBase 1 (u₁ + n₁)) = E.toBase 1 u₁
    rw [hx1, hu1]
  have hTu : d.T.lvlMap 0 u₁ = u₁ := d.isScPlus.lvlMap_eq_self 0 (by
    change E.toBase 1 u₁ ∈ d.T.retract
    rw [hu1]; exact htx)
  have hDn : d.T.lvlDeriv 0 0 n₁ = n₁ := hD n₁ (by rw [hn1, ← hf]; exact (d.p _).2)
  have h := hmvt u₁ hu1C (u₁ + n₁) hx1C hu hxr
  rw [hTx, hTu, add_sub_cancel_left, hDn, sub_self, zero_sub, norm_neg] at h
  have hn0 : n₁ = 0 := by
    by_contra hne
    have : 0 < ‖n₁‖ := norm_pos_iff.2 hne
    nlinarith
  have : x - d.T x = 0 := by rw [← hn1, hn0, map_zero]
  exact (sub_eq_zero.1 this).symm

/-- **Small zeros of `f` lie on `O`** (with level-`1` norm `< r`). -/
theorem exists_rho {θ r : ℝ} (hθ1 : θ < 1) (hr : 0 < r)
    (hD : ∀ v : E.lvl 1, E.toBase 1 v ∈ d.N → d.T.lvlDeriv 0 0 v = v)
    (hmvt : ∀ z ∈ E.lvlSet C 1, ∀ z' ∈ E.lvlSet C 1, ‖z‖ < r → ‖z'‖ < r →
        ‖(d.T.lvlMap 0 z' - d.T.lvlMap 0 z) - d.T.lvlDeriv 0 0 (z' - z)‖ ≤ θ * ‖z' - z‖) :
    ∃ ρ > 0, ∀ x ∈ d.T.U, ‖x‖ < ρ → (d.p (x - d.T x) : E.lvl 0) = x - d.T x →
      d.T x = x ∧ ‖E.liftOne x‖ < r := by
  set cN := ‖d.liftN 1‖ with hcN
  set c₁ := ‖E.toBase 1‖ with hc₁
  have hcN0 : 0 ≤ cN := norm_nonneg (d.liftN 1)
  have hc₁0 : 0 ≤ c₁ := norm_nonneg (E.toBase 1)
  set r₁ := r / (2 * (1 + cN * c₁)) with hr₁
  have hr₁pos : 0 < r₁ := by positivity
  have hr₁r : r₁ < r := by
    rw [hr₁, div_lt_iff₀ (by positivity)]
    nlinarith [mul_nonneg hcN0 hc₁0]
  have hg0 : d.T.liftOne 0 = 0 := by
    change E.liftOne (d.T 0) = 0
    rw [d.T.apply_eq_self_of_mem_retract d.zero_mem]
    exact (E.liftOne_eq_iff ⟨0, map_zero _⟩).2 (map_zero _)
  obtain ⟨δ₀, hδ₀, hδ₀'⟩ := Metric.continuousWithinAt_iff.1
    ((d.isScPlus.isScSmooth_liftOne.isSc1.isSc0.continuousOn_base) 0 (d.zero_mem_lvlSet_U 0))
    r₁ hr₁pos
  refine ⟨min δ₀ (r / (2 * (cN + 1))), lt_min hδ₀ (by positivity), fun x hx hxρ hf => ?_⟩
  have hu : ‖E.liftOne (d.T x)‖ < r₁ := by
    have := hδ₀' hx (by rw [dist_zero_right]; exact hxρ.trans_le (min_le_left _ _))
    rwa [hg0, dist_zero_right] at this
  have hTx0 : ‖d.T x‖ ≤ c₁ * ‖E.liftOne (d.T x)‖ := by
    have := (E.toBase 1).le_opNorm (E.liftOne (d.T x))
    rwa [IsScPlus.toBase_lift d.isScPlus hx] at this
  have hn : ‖d.liftN 1 (d.p (x - d.T x))‖ ≤ cN * (‖x‖ + c₁ * ‖E.liftOne (d.T x)‖) := by
    calc ‖d.liftN 1 (d.p (x - d.T x))‖ ≤ cN * ‖d.p (x - d.T x)‖ := (d.liftN 1).le_opNorm _
      _ = cN * ‖x - d.T x‖ := by rw [← d.norm_coe, hf]
      _ ≤ cN * (‖x‖ + c₁ * ‖E.liftOne (d.T x)‖) := by
          gcongr
          exact (norm_sub_le _ _).trans (by gcongr)
  have hx2 : (cN + 1) * ‖x‖ < r / 2 := by
    have h1 : ‖x‖ < r / (2 * (cN + 1)) := hxρ.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h1
    linarith
  have hu2 : (1 + cN * c₁) * ‖E.liftOne (d.T x)‖ < r / 2 := by
    have h1 := hu
    rw [hr₁, lt_div_iff₀ (by positivity)] at h1
    linarith
  have hxr : ‖E.liftOne (d.T x) + d.liftN 1 (d.p (x - d.T x))‖ < r := by
    calc ‖E.liftOne (d.T x) + d.liftN 1 (d.p (x - d.T x))‖
        ≤ ‖E.liftOne (d.T x)‖ + ‖d.liftN 1 (d.p (x - d.T x))‖ := norm_add_le _ _
      _ ≤ ‖E.liftOne (d.T x)‖ + cN * (‖x‖ + c₁ * ‖E.liftOne (d.T x)‖) := by gcongr
      _ = (1 + cN * c₁) * ‖E.liftOne (d.T x)‖ + cN * ‖x‖ := by ring
      _ < r := by nlinarith [norm_nonneg x]
  have hTx := apply_eq_of_zero d hθ1 hD hmvt hx hf (hu.trans hr₁r) hxr
  refine ⟨hTx, ?_⟩
  have : E.liftOne x = E.liftOne (d.T x) := by rw [hTx]
  rw [this]; exact hu.trans hr₁r

end Zeros

theorem A_to_B : A → B := by
  rintro ⟨-, hA2, hA3, hA4⟩ E C t Y p δ hS hδ
  let d := graphData hS
  set cq := ‖d.qL 1‖ with hcq
  set c₁ := ‖E.toBase 1‖ with hc₁
  set cN := ‖d.liftN 1‖ with hcN
  have hcq0 : 0 ≤ cq := norm_nonneg (d.qL 1)
  have hc₁0 : 0 ≤ c₁ := norm_nonneg (E.toBase 1)
  have hcN0 : 0 ≤ cN := norm_nonneg (d.liftN 1)
  have hε := d.eps_pos
  -- the constant `θ`
  set m := min d.eps 1 with hm
  have hmpos : 0 < m := lt_min hε one_pos
  set K := (cq + 1) * (2 * c₁ * cN + 1) with hK
  have hKpos : 0 < K := by positivity
  set θ := min (1 / 2) (m / (2 * K)) with hθ
  have hθpos : 0 < θ := lt_min (by norm_num) (by positivity)
  have hθ1 : θ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hKθ : K * θ ≤ m / 2 := by
    calc K * θ ≤ K * (m / (2 * K)) := by gcongr; exact min_le_right _ _
      _ = m / 2 := by field_simp
  have hm1 : m ≤ 1 := min_le_right _ _
  have hmε : m ≤ d.eps := min_le_left _ _
  have hcqK : cq * θ ≤ K * θ := by
    apply mul_le_mul_of_nonneg_right _ hθpos.le
    nlinarith [mul_nonneg hc₁0 hcN0]
  have hcqθ : cq * θ ≤ 1 / 2 := by linarith
  have hcqθ1 : cq * θ < 1 := by linarith
  have hstep : 2 * c₁ * (cq * θ) * cN ≤ d.eps := by
    have : 2 * c₁ * (cq * θ) * cN ≤ K * θ := by
      have h1 : 2 * c₁ * (cq * θ) * cN = (2 * c₁ * cN * cq) * θ := by ring
      rw [h1]
      apply mul_le_mul_of_nonneg_right _ hθpos.le
      nlinarith [mul_nonneg hc₁0 hcN0, mul_nonneg (mul_nonneg hc₁0 hcN0) hcq0]
    linarith
  -- A's contraction radius on level `1`
  obtain ⟨r, hr, -, -, hmvt, hqL⟩ := hA3 d 0 hθpos
  have hD : ∀ v : E.lvl 1, E.toBase 1 v ∈ d.N → d.T.lvlDeriv 0 0 v = v :=
    fun v hv => hA2 d 0 hv
  have hqL' : ∀ u ∈ E.lvlSet d.T.retract 1, ∀ u' ∈ E.lvlSet d.T.retract 1, ‖u‖ < r → ‖u'‖ < r →
      ‖d.qL 1 (u' - u)‖ ≤ cq * θ * ‖u' - u‖ := hqL
  obtain ⟨ρ, hρ, hzero⟩ := exists_rho d hθ1 hr hD hmvt
  obtain ⟨-, hδt, ε₀, hε₀, hδε⟩ := hδ
  obtain ⟨η, hη, hηδ⟩ := Metric.tendsto_nhdsWithin_nhds.1 hδt (ρ / 2) (by positivity)
  refine ⟨min (min (ρ / 2) η) ε₀, lt_min (lt_min (by positivity) hη) hε₀,
    fun a ha y hy haε hyε hU hf => ?_⟩
  have haρ : ‖a‖ < ρ / 2 := haε.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have haη : ‖a‖ < η := haε.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have haε₀ : ‖a‖ < ε₀ := haε.trans_le (min_le_right _ _)
  have hyρ : ‖y‖ < ρ / 2 := hyε.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  -- `p(a + z) = a` for `z ∈ Y`
  have hpa : ∀ z ∈ Y, (d.p (a + z) : E.lvl 0) = a := fun z hz => by
    change p (a + z) = a
    rw [map_add, hS.2.2.2.2.2.1 a ha, hS.2.2.2.2.2.2 z hz, add_zero]
  have hfB : ∀ x, fB t p x = 0 → (d.p (x - d.T x) : E.lvl 0) = x - d.T x :=
    fun x h => (sub_eq_zero.1 h).symm
  -- a small zero `x` lies on `O`, and its lift is in `O₁ ∩ B(0, r)`
  have hlift : ∀ x ∈ d.T.U, d.T x = x → E.toBase 1 (E.liftOne x) = x ∧
      E.liftOne x ∈ E.lvlSet d.T.retract 1 := fun x hx hTx => by
    have h1 : E.toBase 1 (E.liftOne x) = x := by
      have := d.isScPlus.mem_range x hx
      rw [hTx] at this
      exact E.toBase_liftOne this
    refine ⟨h1, ?_⟩
    rw [ScBanach.mem_lvlSet, h1, ← hTx]
    exact d.T.apply_mem_retract hx
  -- the zero `a + y`
  have hxρ : ‖a + y‖ < ρ := (norm_add_le _ _).trans_lt (by linarith)
  obtain ⟨hTx, hx1r⟩ := hzero (a + y) hU hxρ (hfB _ hf)
  obtain ⟨hx1, hx1O⟩ := hlift (a + y) hU hTx
  -- `a ∈ C`
  have h0O : (0 : E.lvl 1) ∈ E.lvlSet d.T.retract 1 := d.zero_mem_lvlSet_retract 1
  have hq0 := hqL' 0 h0O _ hx1O (by rw [norm_zero]; exact hr) hx1r
  simp only [sub_zero] at hq0
  have haC : a ∈ C := by
    have := d.p_mem_C hx1O (mul_nonneg hcq0 hθpos.le) hcqθ hstep hq0
    rwa [hx1, hpa y hy] at this
  -- the graph point `a + δ(a)`
  obtain ⟨hδY, hδU, hδf⟩ := hδε a ha haC haε₀
  have hδρ : ‖δ a‖ < ρ / 2 := by
    have := hηδ ⟨ha, haC⟩ (by rwa [dist_zero_right])
    rwa [dist_zero_right] at this
  have hx'ρ : ‖a + δ a‖ < ρ := (norm_add_le _ _).trans_lt (by linarith)
  obtain ⟨hTx', hx1r'⟩ := hzero (a + δ a) hδU hx'ρ (hfB _ hδf)
  obtain ⟨hx1', hx1O'⟩ := hlift (a + δ a) hδU hTx'
  -- uniqueness: `p(a + y) = p(a + δ(a)) = a` and the contraction estimate on `O₁`
  have hq := hqL' _ hx1O _ hx1O' hx1r hx1r'
  have hp : d.p (E.toBase 1 (E.liftOne (a + y))) = d.p (E.toBase 1 (E.liftOne (a + δ a))) := by
    apply Subtype.ext
    rw [hx1, hx1', hpa y hy, hpa (δ a) hδY]
  have heq := hA4 d hcqθ1 hq hp
  have : a + δ a = a + y := by rw [← hx1, ← hx1', heq]
  exact (add_left_cancel this).symm

#rt_check RoundTrip.V4_21.A_to_B [Polyfold.GraphData.qL_lvlDeriv_zero, Polyfold.GraphData.lvlDeriv_zero_of_mem_N, Polyfold.GraphData.exists_contraction_radius, Polyfold.GraphData.eq_of_p_eq]

end RoundTrip.V4_21
