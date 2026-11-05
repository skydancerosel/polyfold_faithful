import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_19

/-!
Round trip for V4_19 (the mean value estimate for an sc⁺-retraction in the proofs of Lemmas 4.11,
4.12, the text's (76)–(77)).  The decls list two definitions (`ScRetraction.lvlMap`,
`ScRetraction.lvlDeriv`: vocabulary) and four theorems, so `A` is the conjunction of the types of
`ScRetraction.IsScPlus.hasFDerivWithinAt_lvlMap`, `ScRetraction.IsScPlus.continuousOn_lvlDeriv`,
`ScRetraction.IsScPlus.exists_mvt` and `exists_norm_sub_sub_le_of_hasFDerivWithinAt` (the last
one has a universe parameter, instantiated at `0`).

A ⇒ B (proved, using A's first two conjuncts): B's setting yields the project's `GraphData`
(`graphData`: B's sc-complement `Y` is a closed good complement, `p` corestricts to `T₀O`, and
`Dt(0)E` is the project's `tangentSpace`).  Take `g = t_1 = lvlMap 0` and `h = (1 − p)_1 ∘ t_1`
(`GraphData.qL 1`, the level-1 projection, continuous since `T₀O ⊆ E_∞` is finite-dimensional).
A gives `Dt_1(x) = lvlDeriv 0 x` as derivative on `U₁` and its continuity in the operator norm,
hence `C¹` (`contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn`, `U₁` has unique
derivatives); `fderivWithin h U₁ u = (1 − p)_1 Dt_1(u) = (1 − p)_1 (Dt_1(u) − Dt_1(0))` (since
`(1 − p)Dt(0) = 0`) has norm `≤ 1/2` near `0` by continuity of `Dt_1` at `0`; and the integral
formula is the fundamental theorem of calculus along the segment (`E₁` is complete).

B ⇒ A is not proved (genuine generality, see the JSON).  What B does give back is recorded in
`B_to_A_level_one`: in B's setting, `t_1 = lvlMap 0` is `C¹` on `U₁`.
-/

namespace RoundTrip.V4_19
open Polyfold Set Metric

def A : Prop :=
  type_of% @Polyfold.ScRetraction.IsScPlus.hasFDerivWithinAt_lvlMap ∧
  type_of% @Polyfold.ScRetraction.IsScPlus.continuousOn_lvlDeriv ∧
  type_of% @Polyfold.ScRetraction.IsScPlus.exists_mvt ∧
  type_of% @Polyfold.exists_norm_sub_sub_le_of_hasFDerivWithinAt.{0}

theorem A_holds : A :=
  ⟨@Polyfold.ScRetraction.IsScPlus.hasFDerivWithinAt_lvlMap,
    @Polyfold.ScRetraction.IsScPlus.continuousOn_lvlDeriv,
    @Polyfold.ScRetraction.IsScPlus.exists_mvt,
    @Polyfold.exists_norm_sub_sub_le_of_hasFDerivWithinAt.{0}⟩

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

theorem A_to_B : A → B := by
  rintro ⟨hA1, hA2, -, -⟩ E C t Y p hS
  let d := graphData hS
  have ht : t.IsScPlus := d.isScPlus
  have hUD : UniqueDiffOn ℝ (E.lvlSet t.U 1) := t.isScDomain.uniqueDiffWithinAt 1
  have hder : ∀ x ∈ E.lvlSet t.U 1,
      HasFDerivWithinAt (t.lvlMap 0) (t.lvlDeriv 0 x) (E.lvlSet t.U 1) x :=
    fun x hx => hA1 ht 0 hx
  have hcont : ContinuousOn (t.lvlDeriv 0) (E.lvlSet t.U 1) := hA2 ht 0
  have hg : ContDiffOn ℝ 1 (t.lvlMap 0) (E.lvlSet t.U 1) := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl,
      contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hUD]
    exact ⟨fun h0 => absurd h0 (by simp), t.lvlDeriv 0,
      by rw [contDiffOn_zero]; exact hcont, hder⟩
  have hq0 : ∀ v : E.lvl 1, d.qL 1 (t.lvlDeriv 0 0 v) = 0 := fun v => d.qL_lvlDeriv_zero 0 v
  refine ⟨t.lvlMap 0, d.qL 1 ∘ t.lvlMap 0, fun u hu => ht.toBase_lvlMap 0 hu, fun u hu => ?_,
    hg, (d.qL 1).contDiff.comp_contDiffOn hg, ?_, ?_⟩
  · rw [Function.comp_apply, d.toBase_qL, ht.toBase_lvlMap 0 hu]
    rfl
  · -- `‖(1 − p)Dt(u)‖ ≤ 1/2` near `0`
    set c := ‖d.qL 1‖ with hc
    have hc0 : 0 ≤ c := norm_nonneg _
    have hpos : (0 : ℝ) < 1 / (2 * (c + 1)) := by positivity
    have h0U : (0 : E.lvl 1) ∈ E.lvlSet t.U 1 := d.zero_mem_lvlSet_U 1
    obtain ⟨ε₁, hε₁, hball⟩ := Metric.continuousWithinAt_iff.1 (hcont 0 h0U) _ hpos
    refine ⟨ε₁, hε₁, fun u hu hun => ?_⟩
    have hfd : fderivWithin ℝ (d.qL 1 ∘ t.lvlMap 0) (E.lvlSet t.U 1) u =
        (d.qL 1).comp (t.lvlDeriv 0 u) :=
      ((d.qL 1).hasFDerivAt.comp_hasFDerivWithinAt u (hder u hu)).fderivWithin (hUD u hu)
    have hz : (d.qL 1).comp (t.lvlDeriv 0 u) =
        (d.qL 1).comp (t.lvlDeriv 0 u - t.lvlDeriv 0 0) := by
      ext v
      change d.qL 1 (t.lvlDeriv 0 u v) = d.qL 1 (t.lvlDeriv 0 u v - t.lvlDeriv 0 0 v)
      rw [map_sub, hq0, sub_zero]
    rw [hfd, hz]
    have h1 : ‖t.lvlDeriv 0 u - t.lvlDeriv 0 0‖ ≤ 1 / (2 * (c + 1)) := by
      have := hball hu (by rwa [dist_zero_right])
      rw [dist_eq_norm] at this
      exact this.le
    calc ‖(d.qL 1).comp (t.lvlDeriv 0 u - t.lvlDeriv 0 0)‖
        ≤ c * ‖t.lvlDeriv 0 u - t.lvlDeriv 0 0‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ c * (1 / (2 * (c + 1))) := by gcongr
      _ ≤ 1 / 2 := by
          rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  · -- the integral formula
    intro u v hseg
    have hz : ∀ s ∈ Icc (0 : ℝ) 1, u + s • (v - u) ∈ E.lvlSet t.U 1 := fun s hs =>
      hseg (by rw [segment_eq_image']; exact ⟨s, hs, rfl⟩)
    have hpath : ∀ s : ℝ, HasDerivAt (fun s : ℝ => u + s • (v - u)) (v - u) s := fun s => by
      simpa using ((hasDerivAt_id s).smul_const (v - u)).const_add u
    have hφ : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun s : ℝ => t.lvlMap 0 (u + s • (v - u)))
        (t.lvlDeriv 0 (u + s • (v - u)) (v - u)) (Icc 0 1) s := fun s hs =>
      HasFDerivWithinAt.comp_hasDerivWithinAt (l := t.lvlMap 0)
        (f := fun s : ℝ => u + s • (v - u)) s (hder _ (hz s hs)) (hpath s).hasDerivWithinAt
        (fun s' hs' => hz s' hs')
    have hcont' : ContinuousOn (fun s : ℝ => t.lvlDeriv 0 (u + s • (v - u)) (v - u)) (Icc 0 1) :=
      (hcont.comp (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
        (fun s hs => hz s hs)).clm_apply continuousOn_const
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le zero_le_one
      (fun s hs => (hφ s hs).continuousWithinAt)
      (fun s hs => ((hφ s (Ioo_subset_Icc_self hs)).hasDerivAt
        (Icc_mem_nhds hs.1 hs.2)).hasDerivWithinAt)
      (hcont'.intervalIntegrable_of_Icc zero_le_one)
    have hcongr : ∫ s in (0 : ℝ)..1,
        fderivWithin ℝ (t.lvlMap 0) (E.lvlSet t.U 1) (u + s • (v - u)) (v - u) =
        ∫ s in (0 : ℝ)..1, t.lvlDeriv 0 (u + s • (v - u)) (v - u) := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le zero_le_one] at hs
      rw [(hder _ (hz s hs)).fderivWithin (hUD _ (hz s hs))]
    rw [hcongr, hFTC]
    simp

/-- What B gives back (B ⇒ the level-1 part of A's first two conjuncts, up to identifying the
derivative): in B's setting, `t_1 = lvlMap 0` is `C¹` on `U₁`. -/
theorem B_to_A_level_one (hB : B) {E : ScBanach} {C : Set (E.lvl 0)} (t : ScRetraction E C)
    (Y : Submodule ℝ (E.lvl 0)) (p : E.lvl 0 →L[ℝ] E.lvl 0) (hS : IsSetting49B t Y p) :
    ContDiffOn ℝ 1 (t.lvlMap 0) (E.lvlSet t.U 1) := by
  have ht : t.IsScPlus := (isScPlus_iff t).2 hS.1
  obtain ⟨g, -, hg, -, hgC, -, -, -⟩ := hB E C t Y p hS
  refine hgC.congr fun u hu => E.toBase_injective 1 ?_
  rw [hg u hu]
  exact ht.toBase_lvlMap 0 hu

#rt_check RoundTrip.V4_19.A_to_B [Polyfold.ScRetraction.IsScPlus.hasFDerivWithinAt_lvlMap, Polyfold.ScRetraction.IsScPlus.continuousOn_lvlDeriv, Polyfold.ScRetraction.IsScPlus.exists_mvt, Polyfold.exists_norm_sub_sub_le_of_hasFDerivWithinAt]
#rt_check RoundTrip.V4_19.B_to_A_level_one [Polyfold.ScRetraction.IsScPlus.hasFDerivWithinAt_lvlMap, Polyfold.ScRetraction.IsScPlus.continuousOn_lvlDeriv, Polyfold.ScRetraction.IsScPlus.exists_mvt, Polyfold.exists_norm_sub_sub_le_of_hasFDerivWithinAt]
#rt_overlap RoundTrip.V4_19.B_to_A_level_one [Polyfold.ScRetraction.IsScPlus.hasFDerivWithinAt_lvlMap, Polyfold.ScRetraction.IsScPlus.continuousOn_lvlDeriv, Polyfold.ScRetraction.IsScPlus.exists_mvt, Polyfold.exists_norm_sub_sub_le_of_hasFDerivWithinAt]

end RoundTrip.V4_19
