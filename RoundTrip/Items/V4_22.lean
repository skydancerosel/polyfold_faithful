import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_22

/-!
Round trip for V4_22 (Lemma 4.12, existence).  The decls list a definition (`GraphData.eps'`,
vocabulary) and one theorem, so `A` is the type of `Polyfold.GraphData.exists_graph_point` (no
universe parameters).

The two statements are different:
* A (the project's Lemma 4.12, proved by a level-`1` contraction): for every `a ∈ N ∩ C` with
  `‖a‖₁ < ρ` there EXISTS `u ∈ O₁` with `p(u) = a`, `u − a ∈ Y` and quantitative bounds.
* B (the text's Lemma 4.12): for a GIVEN solution germ `δ` of `f(a + δ(a)) = 0`
  (`f = (1 − p)(id − t)`), the zeros `a + δ(a)` with `|a|₀ < ε` lie in `O`.

`B` is proved outright (`B_holds`), so `A_to_B` does not use A: from A one would still need the
uniqueness of Lemma 4.11 to identify `a + δ(a)` with A's point, and that argument's ingredients
(the level-`1` mean value estimate at `0` and level-`1` control of `a + δ(a)`) prove B directly.
The proof: `n = v − t(v) ∈ N` for `v = a + δ(a)` (`f(v) = 0`), so `v = t(v) + n ∈ E₁`; its
level-`1` norm is small because `t : U → E₁` is continuous at `0` (sc⁺) and `N ⊆ E_∞` is
finite-dimensional; the mean value estimate on `C₁ ∩ B₁(0, r)` with `Dt(0) = 1` on `N` gives
`‖t(v) − v‖₁ ≤ ½‖t(v) − v‖₁`, so `t(v) = v ∈ O` (the text's argument `a₁ = a`).

Glue: B's setting (`IsSetting49B`: sc⁺-retraction with "some sc-smooth lift", `T₀O = range Dt(0)`,
sc-splitting `T₀O ⊕ Y` with the `ε`-cone condition, `p : E → E` the projection) yields the
project's `GraphData` (`toGraphData`: `Y` closed from the sc-splitting, `p` co-restricted to `N`).

`B → A` is not proved: B presupposes a solution germ `δ`; deriving A's existence statement from B
needs the existence of `δ` (the contraction / implicit function theorem), i.e. re-proving A.
-/

namespace RoundTrip.V4_22
open Polyfold Set Metric Filter Topology

def A : Prop := type_of% @Polyfold.GraphData.exists_graph_point

theorem A_holds : A := @Polyfold.GraphData.exists_graph_point

section Glue

variable {E : ScBanach} {C : Set (E.lvl 0)}

theorem fromB {R : ScRetraction E C} (hR : IsScPlusRetractionB R) : R.IsScPlus := by
  obtain ⟨-, g, hg, hgs⟩ := hR
  exact (IsScPlus.iff_exists R.isScDomain).2 ⟨g, hgs, hg⟩

theorem isCompl_of_setting {t : ScRetraction E C} {Y : Submodule ℝ (E.lvl 0)}
    {p : E.lvl 0 →L[ℝ] E.lvl 0} (h : IsSetting49B t Y p) : IsCompl (tangentAtZero t) Y := by
  have := h.2.2.2.1.2.2 0
  simpa only [ScBanach.levelSub_zero] using this

theorem p_mem_of_setting {t : ScRetraction E C} {Y : Submodule ℝ (E.lvl 0)}
    {p : E.lvl 0 →L[ℝ] E.lvl 0} (h : IsSetting49B t Y p) (x : E.lvl 0) :
    p x ∈ tangentAtZero t := by
  have hx : x ∈ tangentAtZero t ⊔ Y := by
    rw [(isCompl_of_setting h).sup_eq_top]; exact Submodule.mem_top
  obtain ⟨n, hn, y, hy, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add, h.2.2.2.2.2.1 n hn, h.2.2.2.2.2.2 y hy, add_zero]
  exact hn

/-- B's setting of Proposition 4.9 gives the project's data `GraphData`. -/
noncomputable def toGraphData (t : ScRetraction E C) (Y : Submodule ℝ (E.lvl 0))
    (p : E.lvl 0 →L[ℝ] E.lvl 0) (h : IsSetting49B t Y p) : GraphData E C where
  T := t
  isScPlus := fromB h.1
  zero_mem := h.2.1
  N := tangentAtZero t
  N_eq := (tangentSpace_eq_coe_submodule t (by rw [ScBanach.mem_lvlSet, map_zero]; exact h.2.1)).symm
  goodPosition := ⟨h.2.2.1, Y, ⟨isCompl_of_setting h, h.2.2.2.2.1⟩⟩
  Y := Y
  goodComplement := ⟨isCompl_of_setting h, h.2.2.2.2.1⟩
  isClosed_Y := h.2.2.2.1.2.1.1
  p := p.codRestrict _ (p_mem_of_setting h)
  p_apply_N := fun n => Subtype.ext (h.2.2.2.2.2.1 n n.2)
  p_apply_Y := fun y hy => Subtype.ext (by
    change p y = 0
    exact h.2.2.2.2.2.2 y hy)

end Glue

/-- **The text's Lemma 4.12 (B) holds.** -/
theorem B_holds : B := by
  intro E C t Y p δ hset hsol
  let d := toGraphData t Y p hset
  have hθ : (0 : ℝ) < 1 / 2 := by norm_num
  obtain ⟨r, hr, -, -, hmvt, -⟩ := d.exists_contraction_radius 0 hθ
  -- continuity of the lift `t¹ : U → E₁` at `0`
  have hg0 : d.T.liftOne 0 = 0 := by
    change E.liftOne (d.T 0) = 0
    rw [d.T.apply_eq_self_of_mem_retract d.zero_mem]
    exact (E.liftOne_eq_iff ⟨0, map_zero _⟩).2 (map_zero _)
  set K : ℝ := ‖d.liftN 1‖ + 1 with hK
  set c : ℝ := ‖E.toBase 1‖ + 1 with hc
  have hK1 : 1 ≤ K := by have := norm_nonneg (d.liftN 1); linarith
  have hc1 : 1 ≤ c := by have := norm_nonneg (E.toBase 1); linarith
  set η : ℝ := r / (4 * K * c) with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨ρ₁, hρ₁, hρ₁'⟩ := Metric.continuousWithinAt_iff.1
    ((d.isScPlus.isScSmooth_liftOne.isSc1.isSc0.continuousOn_base) 0 (d.zero_mem_lvlSet_U 0)) η
    hηpos
  set ρ : ℝ := min ρ₁ (r / (4 * K)) with hρ
  have hρpos : 0 < ρ := lt_min hρ₁ (by positivity)
  obtain ⟨-, hδt, -⟩ := hsol
  obtain ⟨ε₁, hε₁, hε₁'⟩ := Metric.tendsto_nhdsWithin_nhds.1 hδt (ρ / 2) (by positivity)
  refine ⟨min ε₁ (ρ / 2), lt_min hε₁ (by positivity), fun a haN haC ha hvU hf => ?_⟩
  set v := a + δ a with hvdef
  -- `|v|₀ < ρ`
  have hδa : ‖δ a‖ < ρ / 2 := by
    have := hε₁' (x := a) ⟨haN, haC⟩ (by rw [dist_zero_right]; exact ha.trans_le (min_le_left _ _))
    rwa [dist_zero_right] at this
  have hv : ‖v‖ < ρ := by
    calc ‖v‖ ≤ ‖a‖ + ‖δ a‖ := norm_add_le _ _
      _ < ρ / 2 + ρ / 2 := add_lt_add (ha.trans_le (min_le_right _ _)) hδa
      _ = ρ := by ring
  -- `n = v − t(v) ∈ N`, from `f(v) = 0`
  have hn : v - t.toFun v ∈ tangentAtZero t := by
    unfold fB at hf
    rw [sub_eq_zero] at hf
    rw [hf]
    exact p_mem_of_setting hset _
  -- the level-`1` lifts `wh` of `t(v)` and `vh = wh + nh` of `v`
  set wh : E 1 := d.T.liftOne v with hwhdef
  have hwh : E.toBase 1 wh = t.toFun v := d.isScPlus.toBase_lift hvU
  set nh : E 1 := d.liftN 1 ⟨v - t.toFun v, hn⟩ with hnhdef
  have hnh : E.toBase 1 nh = v - t.toFun v := d.toBase_liftN 1 _
  set vh : E 1 := wh + nh with hvhdef
  have hvh : E.toBase 1 vh = v := by rw [hvhdef, map_add, hwh, hnh]; abel
  -- norms
  have hwhn : ‖wh‖ < η := by
    have := hρ₁' (x := v) hvU (by rw [dist_zero_right]; exact hv.trans_le (min_le_left _ _))
    rwa [hg0, dist_zero_right] at this
  have htv : ‖t.toFun v‖ ≤ c * η := by
    rw [← hwh]
    calc ‖E.toBase 1 wh‖ ≤ ‖E.toBase 1‖ * ‖wh‖ := (E.toBase 1).le_opNorm wh
      _ ≤ c * η := by
        apply mul_le_mul (by linarith) hwhn.le (norm_nonneg _) (by linarith)
  have hnn : ‖nh‖ ≤ K * ρ + K * c * η := by
    have h1 : ‖nh‖ ≤ ‖d.liftN 1‖ * ‖v - t.toFun v‖ := (d.liftN 1).le_opNorm _
    have h2 : ‖v - t.toFun v‖ ≤ ρ + c * η := by
      calc ‖v - t.toFun v‖ ≤ ‖v‖ + ‖t.toFun v‖ := norm_sub_le _ _
        _ ≤ ρ + c * η := add_le_add hv.le htv
    have h3 : ‖d.liftN 1‖ ≤ K := by linarith
    calc ‖nh‖ ≤ ‖d.liftN 1‖ * ‖v - t.toFun v‖ := h1
      _ ≤ K * (ρ + c * η) :=
          mul_le_mul h3 h2 (norm_nonneg _) (by linarith)
      _ = K * ρ + K * c * η := by ring
  have hKcη : K * c * η = r / 4 := by
    rw [hη]; field_simp
  have hη4 : η ≤ r / 4 := by
    rw [hη]
    apply div_le_div_of_nonneg_left hr.le (by norm_num)
    nlinarith
  have hKρ : K * ρ ≤ r / 4 := by
    calc K * ρ ≤ K * (r / (4 * K)) := mul_le_mul_of_nonneg_left (min_le_right _ _) (by linarith)
      _ = r / 4 := by field_simp
  have hvhn : ‖vh‖ < r := by
    calc ‖vh‖ ≤ ‖wh‖ + ‖nh‖ := norm_add_le _ _
      _ < r := by linarith
  have hwhr : ‖wh‖ < r := by linarith
  -- the mean value estimate at `0` on level `1`
  have hvhU : vh ∈ E.lvlSet d.T.U 1 := by rw [ScBanach.mem_lvlSet, hvh]; exact hvU
  have hvhC : vh ∈ E.lvlSet C 1 := d.T.lvlSet_U_subset_lvlSet_C 1 hvhU
  have hwhO : E.toBase 1 wh ∈ d.T.retract := hwh ▸ d.T.apply_mem_retract hvU
  have hwhC : wh ∈ E.lvlSet C 1 :=
    d.T.lvlSet_U_subset_lvlSet_C 1 (d.T.lvlSet_retract_subset 1 hwhO)
  have h := hmvt vh hvhC wh hwhC hvhn hwhr
  have h1 : d.T.lvlMap 0 wh = wh := d.isScPlus.lvlMap_eq_self 0 hwhO
  have h2 : d.T.lvlMap 0 vh = wh := by
    apply E.toBase_injective 1
    rw [d.isScPlus.toBase_lvlMap 0 hvhU, hvh, hwh]
    rfl
  have hwvN : E.toBase 1 (wh - vh) ∈ d.N := by
    rw [map_sub, hwh, hvh]
    have := (tangentAtZero t).neg_mem hn
    rwa [neg_sub] at this
  have h3 : d.T.lvlDeriv 0 0 (wh - vh) = wh - vh := d.lvlDeriv_zero_of_mem_N 0 hwvN
  rw [h1, h2, h3, sub_self, zero_sub, norm_neg] at h
  have hwv : wh = vh := by
    have : ‖wh - vh‖ ≤ 0 := by linarith [norm_nonneg (wh - vh)]
    exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
  rw [t.mem_retract_iff]
  refine ⟨hvU, ?_⟩
  rw [← hwh, hwv, hvh]

/-- `A → B` holds because B is proved outright (A is not used; see the module docstring). -/
theorem A_to_B : A → B := fun _ => B_holds

#rt_check RoundTrip.V4_22.A_to_B [Polyfold.GraphData.exists_graph_point]

end RoundTrip.V4_22
