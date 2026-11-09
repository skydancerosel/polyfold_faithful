import Polyfold.Chapter4.Submanifolds
import Polyfold.Chapter2.TameBoundaryExample

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §2.5 "Tame
M-polyfolds": **Definition 2.5.19** (p. 63, tame sub-M-polyfolds) and the paragraph after it
(p. 63), both new in the 2021 edition.  The definitions themselves are in
`Polyfold/Chapter2/TameBoundary.lean`: `MPolyfold.HasTameInducedStructure` (2021 Definition
2.5.18), `MPolyfold.TameSubData` and `MPolyfold.IsTameSubMPolyfold` (2021 Definition 2.5.19),
with the witnesses `hasTameInducedStructure_univ`, `isTameSubMPolyfold_univ`.

# Tame sub-M-polyfolds

## The text, paraphrased

(Definition 2.5.19) A sub-M-polyfold `Y` of a tame `X` is a *tame sub-M-polyfold* if every
`y ∈ Y` has an open `V` and an sc-smooth retraction `r : V → V` with (1) `r(V) = Y ∩ V`,
(2) `d_X ∘ r = d_X` on `V`, (3) at every smooth `y ∈ Y ∩ V`, `T_yX = T_yY ⊕ A` for an
sc-subspace `A` of the reduced tangent space `T_y^R X`.  (After it) A tame sub-M-polyfold of a
tame `X` is tame (it has a tame atlas).  In `X = [0,∞)² × ℝ` the set `A = {(x, y, 0)}` is a tame
sub-M-polyfold; `B = {(x, x, 0)}` is not, but the structure induced on `B` is tame, `B` being
diffeomorphic to `[0,∞)`.

## What is formalized

* **Chart independence of (3)**: `MPolyfold.TameSubData.hasReducedComplementAt_of_isChart`.
  `TameSubData` asks for (3) in *one* chart `φ₀ ∋ y` with *one* presentation `T₀` of its partial
  quadrant; then (3) holds in *every* chart `φ ∋ y`, for every presentation `T` of `φ.model.C`,
  and for the chart image `φ(W' ∩ Y)` of *any* retraction `r'` onto `Y` near `y` (a `SubData`),
  by Chapter 4's chart change `MPolyfold.isGeneralPositionRetractAt_chart_change`;
  `MPolyfold.TameSubData.complement_forall_charts` is the case `r' = r`.
* **A tame sub-M-polyfold is tame**: `MPolyfold.IsTameSubMPolyfold.hasTameInducedStructure`.
  The key step is `MPolyfold.TameSubData.isTameRetract_image`: in a chart `φ` with a tame model
  `(O, C, E)` (tame retraction `t`), `φ(W ∩ Y)` is a tame retract, by the retraction
  `(φ r φ⁻¹) ∘ t`: (1) comes from (2) of the definition and `d_X = d_C ∘ φ`
  (`degIndex_eq_chartDegIndex_of_isTameWith`), and the sc-complement of `T_x(φ(W ∩ Y))` in `E`
  inside `E_x` is `A ⊕ B`, with `A` from (3) in the chart `φ` (chart independence) and `B` the
  complement of `T_xO` from the tameness of `t`
  (`ScBanach.isScSplitting_sup_of_complementIn`).
* **The examples**, in `[0,∞)² ⊕ W` for an arbitrary sc-Banach space `W` (`W = ℝ` is the text's
  `[0,∞)² × ℝ`, `TameSubExample.examples_A_B`):
  `TameSubExample.isTameSubMPolyfold_setA`, `TameSubExample.hasTameInducedStructure_setA`;
  `TameSubExample.isSubMPolyfold_setB`, `TameSubExample.not_isTameSubMPolyfold_setB`
  (from `TameSubExample.not_mem_tameSubData_setB`),
  `TameSubExample.hasTameInducedStructure_setB` and
  `TameSubExample.halfLineToB_isScDiffeoOn` (`t ↦ (t, t, 0)` is an sc-diffeomorphism from the
  half-line onto `B` with its induced structure).  `A` is the case `L(a, w) = (a, 0)` of
  `TameSubExample.isTameSubMPolyfold_fixSet`: the fixed set of an idempotent sc-operator `L`
  which keeps the `ℝⁿ`-component is a tame sub-M-polyfold of `[0,∞)ⁿ ⊕ W`.

## What the text leaves implicit, and the choices made

* As `T_yX` carries no linear structure in this formalization (gap G.7), (3) is stated in charts
  (`HasReducedComplementAt`, see `TameSubData`); the chart independence above shows that the
  choice of chart, presentation and retraction does not matter.
* "Not difficult to see" is read as: the sub-charts of `Y` built on tame charts of `X`
  (`subChart`) have tame models.
* The obstruction for `B` sits at the corner `0`: (1) and (2) of 2021 Definition 2.5.19 already
  fail for every `r` defined near `0`, since `d_X(t, 0, 0) = 1` for `t > 0` while `d_X` takes only
  the values `0` and `2` on `B`.
* The half-line `[0,∞)` is `[0,∞) ⊕ ℝ⁰` (`quadrant 1 zeroSpace 0`).
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

namespace ScBanach

variable {E : ScBanach}

/-! ### Adding sc-complements -/

/-- For `A ≤ M` and an sc-splitting `E = M ⊕ B`, `(A ⊔ B)_m = A_m ⊔ B_m` on every level. -/
theorem levelSub_sup_of_le_of_isScSplitting {M A B : Submodule ℝ (E 0)}
    (hMB : E.IsScSplitting M B) (hAM : A ≤ M) (m : ℕ) :
    E.levelSub (A ⊔ B) m = E.levelSub A m ⊔ E.levelSub B m := by
  refine le_antisymm (fun v hv => ?_) (sup_le (Submodule.comap_mono le_sup_left)
    (Submodule.comap_mono le_sup_right))
  rw [mem_levelSub, Submodule.mem_sup] at hv
  obtain ⟨a, ha, b, hb, hab⟩ := hv
  have hv' : v ∈ E.levelSub M m ⊔ E.levelSub B m := by
    rw [(hMB.2.2 m).sup_eq_top]; exact Submodule.mem_top
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 hv'
  have h0 := hMB.2.2 0
  rw [levelSub_zero, levelSub_zero] at h0
  have hpa : E.toBase m p = a := by
    have hsum : E.toBase m p + E.toBase m q = a + b := by
      rw [← map_add, hpq, hab]
    have hdiff : E.toBase m p - a ∈ M ⊓ B := by
      refine ⟨M.sub_mem hp (hAM ha), ?_⟩
      have : E.toBase m p - a = b - E.toBase m q := by
        rw [sub_eq_sub_iff_add_eq_add, hsum, add_comm]
      rw [this]; exact B.sub_mem hb hq
    rw [h0.inf_eq_bot, Submodule.mem_bot, sub_eq_zero] at hdiff
    exact hdiff
  rw [← hpq]
  refine Submodule.add_mem_sup ?_ hq
  change E.toBase m p ∈ A
  rw [hpa]; exact ha

/-- **Adding complements**: if `E = M ⊕ B` is an sc-splitting and `N, A ⊆ M` are sc-subspaces with
`M_m = N_m ⊕ A_m` on every level, then `E = N ⊕ (A ⊕ B)` is an sc-splitting. -/
theorem isScSplitting_sup_of_complementIn {M N A B : Submodule ℝ (E 0)}
    (hMB : E.IsScSplitting M B) (hN : E.IsScSubspace N) (hA : E.IsScSubspace A) (hAM : A ≤ M)
    (hsplit : ∀ m, Disjoint (E.levelSub N m) (E.levelSub A m) ∧
      E.levelSub N m ⊔ E.levelSub A m = E.levelSub M m) :
    E.IsScSplitting N (A ⊔ B) := by
  have hlev := levelSub_sup_of_le_of_isScSplitting hMB hAM
  -- `A ⊔ B` is the preimage of `A` under the projection onto `M` along `B`
  set P := hMB.scProj 0 with hPdef
  have hPM : ∀ u ∈ M, P u = u := fun u hu => by
    have : u ∈ LinearMap.range (hMB.scProj 0 : E 0 →ₗ[ℝ] E 0) := by
      rw [hMB.range_scProj 0, levelSub_zero]; exact hu
    obtain ⟨w, rfl⟩ := this
    exact hMB.scProj_idem 0 w
  have hPB : ∀ u ∈ B, P u = 0 := fun u hu => by
    have : u ∈ LinearMap.ker (hMB.scProj 0 : E 0 →ₗ[ℝ] E 0) := by
      rw [hMB.ker_scProj 0, levelSub_zero]; exact hu
    exact this
  have hsubB : ∀ u, u - P u ∈ B := fun u => by
    have : u - P u ∈ LinearMap.ker (hMB.scProj 0 : E 0 →ₗ[ℝ] E 0) := by
      change P (u - P u) = 0
      rw [map_sub, hMB.scProj_idem 0 u, sub_self]
    rw [hMB.ker_scProj 0, levelSub_zero] at this
    exact this
  have hpre : ((A ⊔ B : Submodule ℝ (E 0)) : Set (E 0)) = P ⁻¹' (A : Set (E 0)) := by
    ext v
    constructor
    · intro hv
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
      change P (a + b) ∈ A
      rw [map_add, hPM a (hAM ha), hPB b hb, add_zero]; exact ha
    · intro hv
      have : v = P v + (v - P v) := by abel
      rw [SetLike.mem_coe, this]
      exact Submodule.add_mem_sup hv (hsubB v)
  have hAB : E.IsScSubspace (A ⊔ B) := by
    refine ⟨?_, fun m v hv => ?_⟩
    · rw [hpre]; exact hA.isClosed.preimage P.continuous
    · rw [SetLike.mem_coe, hlev m] at hv
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
      refine map_mem_closure₂ continuous_add (hA.2 m ha) (hMB.2.1.2 m hb) fun x hx y hy => ?_
      refine ⟨?_, ?_⟩
      · rw [SetLike.mem_coe, hlev m]; exact Submodule.add_mem_sup hx.1 hy.1
      · change E.toBase m (x + y) ∈ E.smooth
        rw [map_add]; exact E.smooth.add_mem hx.2 hy.2
  refine ⟨hN, hAB, fun m => ?_⟩
  rw [hlev m]
  have hNM : E.levelSub N m ≤ E.levelSub M m := (hsplit m).2 ▸ le_sup_left
  have hAM' : E.levelSub A m ≤ E.levelSub M m := Submodule.comap_mono hAM
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hxN hxAB
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hxAB
    have hbM : b ∈ E.levelSub M m := by
      have : b = x - a := by rw [← hab]; abel
      rw [this]; exact Submodule.sub_mem _ (hNM hxN) (hAM' ha)
    have hb0 : b = 0 := by
      have := (hMB.2.2 m).inf_eq_bot
      have hmem : b ∈ E.levelSub M m ⊓ E.levelSub B m := ⟨hbM, hb⟩
      rw [this, Submodule.mem_bot] at hmem; exact hmem
    rw [hb0, add_zero] at hab
    subst hab
    have := (hsplit m).1
    rw [Submodule.disjoint_def] at this
    exact this a hxN ha
  · rw [codisjoint_iff, ← sup_assoc, (hsplit m).2, (hMB.2.2 m).sup_eq_top]

end ScBanach

namespace MPolyfold

open TameBoundary

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- A point of an M-polyfold is smooth iff its image in one chart is a smooth point of the
model. -/
theorem mem_smoothSet_iff_of_isChart {φ : MChart X} (hφ : P.IsChart φ) {y : X}
    (hy : y ∈ φ.source) : y ∈ P.smoothSet ↔ φ y ∈ φ.model.E.smooth := by
  rw [smoothSet, mem_iInter]
  constructor
  · intro h
    exact (ScScale.mem_smooth_iff _).2 fun m => (P.mem_levelSet_iff hφ hy).1 (h m)
  · intro h m
    exact (P.mem_levelSet_iff hφ hy).2 ((ScScale.mem_smooth_iff _).1 h m)

namespace TameSubData

variable {Y : Set X}

/-- **Chart independence of 2021 Definition 2.5.19 (3)**, p. 63: if `Y` has the data `(V, r)`
of a tame sub-M-polyfold near `y` (with (3) in one chart), then at a smooth `y ∈ Y ∩ V` the
condition (3) holds in every chart `φ ∋ y`, for every presentation `T` of its partial quadrant,
and for the chart image `φ(W' ∩ Y)` of any retraction `r'` onto `Y` near `y` (`d'`). -/
theorem hasReducedComplementAt_of_isChart (d : P.TameSubData Y) (d' : P.SubData Y) {y : X}
    (hyY : y ∈ Y) (hyV : y ∈ d.V) (hyV' : y ∈ d'.V) (hys : y ∈ P.smoothSet)
    {φ : MChart X} (hφ : P.IsChart φ) (hyφ : y ∈ φ.source) {n : ℕ} {W : ScBanach}
    (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W))
    (hT : φ.model.C = T 0 ⁻¹' quadrant n W 0) (z : φ.model.E 1)
    (hz : φ.model.E.toBase 1 z = φ y) :
    HasReducedComplementAt φ.model.C φ.model.O (φ '' (d'.shrink φ ∩ Y)) T z := by
  obtain ⟨φ₀, n₀, W₀, T₀, z₀, hφ₀, hyφ₀, hT₀, hz₀, h₀⟩ := d.complement y ⟨hyY, hyV⟩ hys
  have hz₀s : z₀ ∈ φ₀.model.E.smoothLvl 1 := by
    change φ₀.model.E.toBase 1 z₀ ∈ φ₀.model.E.smooth
    rw [hz₀]; exact (mem_smoothSet_iff_of_isChart hφ₀ hyφ₀).1 hys
  exact isGeneralPositionRetractAt_chart_change hφ₀ hφ (A := Y)
    (d.toSubData.isOpen_shrink φ₀) (d'.isOpen_shrink φ) (d.toSubData.shrink_subset_source φ₀)
    (d'.shrink_subset_source φ) (d.toSubData.isScRetract_image φ₀ hφ₀)
    (d'.isScRetract_image φ hφ) hyY (d.toSubData.mem_shrink φ₀ hyY hyV hyφ₀)
    (d'.mem_shrink φ hyY hyV' hyφ) hz₀ hz hz₀s T₀ hT₀ T hT h₀

/-- **2021 Definition 2.5.19 (3) in every chart**: the condition `complement` of `TameSubData`,
asked in one chart at each smooth point, holds in every chart and for every presentation. -/
theorem complement_forall_charts (d : P.TameSubData Y) {y : X} (hy : y ∈ Y ∩ d.V)
    (hys : y ∈ P.smoothSet) {φ : MChart X} (hφ : P.IsChart φ) (hyφ : y ∈ φ.source) {n : ℕ}
    {W : ScBanach} (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W))
    (hT : φ.model.C = T 0 ⁻¹' quadrant n W 0) (z : φ.model.E 1)
    (hz : φ.model.E.toBase 1 z = φ y) :
    HasReducedComplementAt φ.model.C φ.model.O
      (φ '' ((d.V ∩ φ.source) ∩ d.r ⁻¹' (d.V ∩ φ.source) ∩ Y)) T z :=
  d.hasReducedComplementAt_of_isChart d.toSubData hy.1 hy.2 hy.2 hys hφ hyφ T hT z hz

/-- In every chart `φ` with a tame model, the chart image `φ(W ∩ Y)` of `Y` is a tame retract
(the step behind "a tame sub-M-polyfold is tame", 2021 p. 63): it is the retract of
`(φ r φ⁻¹) ∘ t` for the tame retraction `t` of the model. -/
theorem isTameRetract_image (d : P.TameSubData Y) {φ : MChart X} (hφ : P.IsChart φ)
    (htame : IsTameRetract φ.model.E φ.model.C φ.model.O) :
    IsTameRetract φ.model.E φ.model.C (φ '' (d.toSubData.shrink φ ∩ Y)) := by
  obtain ⟨R, hRO, hRt⟩ := htame
  set G := d.toSubData.shrink φ with hG
  have hGφ : G ⊆ φ.source := d.toSubData.shrink_subset_source φ
  obtain ⟨K, hK, hKeq⟩ := φ.exists_isOpen_image_eq hGφ (d.toSubData.isOpen_shrink φ)
  set R₁ := R.restrict hK with hR₁
  have hR₁ret : R₁.retract = φ '' G := by rw [hR₁, R.restrict_retract, hRO, hKeq]
  set s := φ ∘ d.r ∘ φ.symm with hs
  have hss : IsScSmoothRetractMap φ.model.E φ.model.C R₁.retract φ.model.E φ.model.C
      R₁.retract s := by
    rw [hR₁ret]; exact d.toSubData.rho_isScSmooth φ hφ
  have hidem : ∀ x ∈ R₁.retract, s (s x) = s x := by
    rw [hR₁ret]; exact fun x hx => d.toSubData.rho_idem φ hx
  set RY := R₁.compRetraction hss hidem with hRY
  have hRYret : RY.retract = φ '' (G ∩ Y) := by
    rw [hRY, R₁.compRetraction_retract, hR₁ret]; exact d.toSubData.rho_image φ
  refine ⟨RY, hRYret, fun n W T hT => ?_⟩
  have hR := hRt n W T hT
  have hdeg : ∀ y ∈ φ.source, P.degIndex y = Polyfold.degIndex φ.model.E φ.model.C (φ y) :=
      fun y hy => by
    rw [P.degIndex_eq_chartDegIndex_of_isTameWith hφ R hRO hT hR hy]; rfl
  refine ⟨fun u hu => ?_, fun x hx hxs => ?_⟩
  · -- (1): `d_C ∘ t = d_C`
    change Polyfold.degIndex φ.model.E φ.model.C (s (R u)) =
      Polyfold.degIndex φ.model.E φ.model.C u
    have hRu : R u ∈ φ '' G := by rw [← hR₁ret]; exact R₁.apply_mem_retract hu
    obtain ⟨g, hg, hgu⟩ := hRu
    have h1 : s (R u) = φ (d.r g) := by
      rw [← hgu, hs]
      simp only [Function.comp_apply, φ.symm_apply_apply (hGφ hg)]
    rw [h1, ← hdeg _ (d.toSubData.mapsTo_shrink φ hg).1.2,
      d.degIndex_apply g (d.toSubData.shrink_subset_V φ hg), hdeg g (hGφ hg), hgu]
    exact hR.degIndex_apply u hu.1
  · -- (2): the sc-complement `A ⊕ B ⊆ E_x` of `T_xY` in `E`
    have hxY : φ.model.E.toBase 1 x ∈ φ '' (G ∩ Y) := by rw [← hRYret]; exact hx
    obtain ⟨y, ⟨hyG, hyY⟩, hyx⟩ := hxY
    have hyφ := hGφ hyG
    have hys : y ∈ P.smoothSet :=
      (mem_smoothSet_iff_of_isChart hφ hyφ).2 (by rw [hyx]; exact hxs)
    have hgp := d.hasReducedComplementAt_of_isChart d.toSubData hyY
      (d.toSubData.shrink_subset_V φ hyG) (d.toSubData.shrink_subset_V φ hyG) hys hφ hyφ T hT
      x hyx.symm
    obtain ⟨N, M, A, hN, hM, hAM, hAsc, hsplit⟩ := hgp
    have hxR : x ∈ φ.model.E.lvlSet R.retract 1 := by
      rw [ScBanach.mem_lvlSet, ← hyx, hRO]; exact φ.mapsTo_model y hyφ
    obtain ⟨B, hMB, hBE⟩ := hR.exists_complement x hxR hxs
    have hMeq : M = LinearMap.range (scDeriv R.U R x : φ.model.E 0 →ₗ[ℝ] φ.model.E 0) :=
      SetLike.coe_injective (hM.trans (by rw [← hRO]; exact tangentSpace_eq_coe_submodule R hxR))
    have hNeq : N = LinearMap.range (scDeriv RY.U RY x : φ.model.E 0 →ₗ[ℝ] φ.model.E 0) :=
      SetLike.coe_injective (hN.trans (by
        rw [← hRYret]; exact tangentSpace_eq_coe_submodule RY hx))
    have hNsc : φ.model.E.IsScSubspace N := by
      rw [hNeq]; exact (RY.isScSplitting_range_scDeriv hx hxs).1
    subst hMeq
    refine ⟨A ⊔ B, ?_, sup_le (fun v hv => (hAM hv).2) hBE⟩
    rw [← hNeq]
    exact ScBanach.isScSplitting_sup_of_complementIn hMB hNsc hAsc (fun v hv => (hAM hv).1) hsplit

end TameSubData

/-- **2021, text after Definition 2.5.19, p. 63** (new in the 2021 edition): a tame
sub-M-polyfold `Y` of a tame M-polyfold `X` is tame, i.e. the structure induced on `Y` admits an
equivalent tame atlas (2021 Definition 2.5.18): the sub-charts built on tame charts of `X`. -/
theorem IsTameSubMPolyfold.hasTameInducedStructure {Y : Set X} (h : P.IsTameSubMPolyfold Y) :
    P.HasTameInducedStructure Y := by
  refine ⟨h.isSubMPolyfold, ?_⟩
  let _ := P.paracompactSpace_subtype Y
  refine isTame_of_forall_exists_chart _ fun a => ?_
  obtain ⟨d, had⟩ := h.2 a a.2
  obtain ⟨φ, hφ, haφ, ht⟩ := IsTame.exists_chart P h.1 a.1
  exact ⟨subChart d.toSubData hφ a, subPolyfold_isChart _ d.toSubData hφ a,
    d.toSubData.mem_shrink φ a.2 had haφ, d.isTameRetract_image hφ ht⟩

end MPolyfold

/-! ### The examples `A` and `B` in `[0,∞)² ⊕ W` -/

section Helpers

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : MPolyfold X} {Q : MPolyfold Y}

open MPolyfold

/-- Sc-smoothness is local (as the private `isScSmoothOn_of_locally` of
`Polyfold/Chapter7/SubGroupoid.lean`). -/
private theorem isScSmoothOn_of_locally_ts {f : X → Y} {U : Set X} (hU : IsOpen U)
    (h : ∀ x ∈ U, ∃ U' : Set X, IsOpen U' ∧ x ∈ U' ∧ U' ⊆ U ∧ P.IsScSmoothOn Q f U') :
    P.IsScSmoothOn Q f U := by
  have hcont : ContinuousOn f U := fun x hx => by
    obtain ⟨U', hU', hxU', -, hf⟩ := h x hx
    exact (hf.continuousOn.continuousAt (hU'.mem_nhds hxU')).continuousWithinAt
  refine IsScSmoothOn.of_exists_charts hU hcont fun x hx => ?_
  obtain ⟨U', hU', hxU', hU'U, hf⟩ := h x hx
  obtain ⟨φ, hφ, hxφ⟩ := P.exists_isChart_mem_source x
  obtain ⟨ψ, hψ, hfx⟩ := Q.exists_isChart_mem_source (f x)
  set V := (U' ∩ φ.source) ∩ f ⁻¹' ψ.source with hV
  have hVo : IsOpen V := (hf.continuousOn.mono inter_subset_left).isOpen_inter_preimage
    (hU'.inter φ.isOpen_source) ψ.isOpen_source
  exact ⟨φ, ψ, V, hφ, hψ, hVo, ⟨⟨hxU', hxφ⟩, hfx⟩, fun y hy => ⟨hU'U hy.1.1, hy.1.2⟩,
    fun y hy => hy.2, hf.smooth φ ψ hφ hψ V hVo (fun y hy => hy.1) fun y hy => hy.2⟩

/-- A map into a sub-M-polyfold `A ⊆ Y` is sc-smooth into `A` as soon as it is sc-smooth into
`Y` (as the private `isScSmoothOn_subPolyfold_of_val` of `Polyfold/Chapter7/SubGroupoid.lean`). -/
private theorem isScSmoothOn_subPolyfold_of_val_ts {A : Set Y} (hA : Q.IsSubMPolyfold A)
    [ParacompactSpace A] {f : X → A} {U : Set X}
    (hf : P.IsScSmoothOn Q (fun x => (f x : Y)) U) :
    P.IsScSmoothOn (subPolyfold hA) f U := by
  refine isScSmoothOn_of_locally_ts hf.isOpen fun x hx => ?_
  set d := hA.data (f x).2
  have hU' : IsOpen (U ∩ (fun x => (f x : Y)) ⁻¹' d.V) :=
    hf.continuousOn.isOpen_inter_preimage hf.isOpen d.isOpen
  refine ⟨_, hU', ⟨hx, hA.mem_data_V (f x).2⟩, inter_subset_left, ?_⟩
  refine (IsScSmoothOn.comp (subPolyfold_retraction_isScSmooth hA d (f x))
    (hf.mono hU' inter_subset_left) fun y hy => hy.2).congr fun y hy => Subtype.ext ?_
  simp only [Function.comp_apply]
  rw [d.retractInto_val (f x) hy.2]
  exact d.apply_eq_self ⟨(f y).2, hy.2⟩

end Helpers

namespace TameSubExample

open TameBoundary TameBoundaryExample MPolyfold

variable {n : ℕ} {W : ScBanach}

/-- The sc-operator `const V → const V'` of a linear map of finite-dimensional spaces (the same
as `ScOperator.ofConst` of `Polyfold/Chapter2/TangentLift.lean`, which this file does not
import). -/
def constOp {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup V'] [NormedSpace ℝ V'] [FiniteDimensional ℝ V']
    (L : V →L[ℝ] V') : ScOperator (ScBanach.const V) (ScBanach.const V') where
  lvl _ := L
  incl_comm _ _ := rfl

/-- An sc-operator `ℝⁿ ⊕ W → ℝ^{n'} ⊕ W'` mapping `[0,∞)ⁿ ⊕ W` into `[0,∞)^{n'} ⊕ W'` is an
sc-smooth map between the quadrant M-polyfolds. -/
theorem quadrantMap_isScSmoothMap {n' : ℕ} {W' : ScBanach}
    (L : ScOperator ((ScBanach.const (Fin n → ℝ)).prod W)
      ((ScBanach.const (Fin n' → ℝ)).prod W'))
    (hL : ∀ p ∈ quadrant n W 0, L 0 p ∈ quadrant n' W' 0) :
    (quadrantPolyfold n W).IsScSmoothMap (quadrantPolyfold n' W')
      (fun p => (⟨L 0 p.1, hL p.1 p.2⟩ : quadrant n' W' 0)) := by
  have hφ : (quadrantPolyfold n W).IsChart
      ((LocalModel.ofRelOpen (isRelOpenInQuadrant_quadrant n W)).selfChart
        (quadrant_nonempty n W)) :=
    (isRelOpenInQuadrant_quadrant n W).selfChart_isChart (quadrant_nonempty n W)
  have hψ : (quadrantPolyfold n' W').IsChart
      ((LocalModel.ofRelOpen (isRelOpenInQuadrant_quadrant n' W')).selfChart
        (quadrant_nonempty n' W')) :=
    (isRelOpenInQuadrant_quadrant n' W').selfChart_isChart (quadrant_nonempty n' W')
  set φ := (LocalModel.ofRelOpen (isRelOpenInQuadrant_quadrant n W)).selfChart
    (quadrant_nonempty n W) with hφdef
  set ψ := (LocalModel.ofRelOpen (isRelOpenInQuadrant_quadrant n' W')).selfChart
    (quadrant_nonempty n' W') with hψdef
  refine IsScSmoothOn.of_exists_charts isOpen_univ ?_ fun x _ =>
    ⟨φ, ψ, univ, hφ, hψ, isOpen_univ, mem_univ x, fun z _ => ⟨mem_univ z, mem_univ z⟩,
      mapsTo_univ _ _, ?_⟩
  · exact (((L 0).continuous.comp continuous_subtype_val).subtype_mk _).continuousOn
  · have hO : IsScRetract φ.model.E φ.model.C (φ '' univ) := by
      rw [show φ '' univ = φ.model.O from φ.image_source]; exact φ.model.isScRetract
    refine (L.isScSmoothRetractMap (O₁ := quadrant n' W' 0) hO ?_).congr ?_
    · rintro _ ⟨z, -, rfl⟩
      exact hL z.1 z.2
    · rintro _ ⟨z, -, rfl⟩
      have h : (φ.symm (φ z) : quadrant n W 0) = z := φ.symm_apply_apply (mem_univ z)
      exact (congrArg (fun y : quadrant n W 0 =>
        (L 0 y.1 : ((ScBanach.const (Fin n' → ℝ)).prod W') 0)) h).symm

variable (L : ScOperator ((ScBanach.const (Fin n → ℝ)).prod W)
  ((ScBanach.const (Fin n → ℝ)).prod W))

/-- The retraction `L` of `C = [0,∞)ⁿ ⊕ W`, for an idempotent sc-operator `L` mapping `C` into
itself. -/
def opRetraction (hL : ∀ p ∈ quadrant n W 0, L 0 p ∈ quadrant n W 0)
    (hidem : ∀ p, L 0 (L 0 p) = L 0 p) :
    ScRetraction ((ScBanach.const (Fin n → ℝ)).prod W) (quadrant n W 0) where
  U := quadrant n W 0
  toFun := L 0
  relOpen := isRelOpenInQuadrant_quadrant n W
  mapsTo := hL
  isScSmooth := L.isScSmooth (isRelOpenInQuadrant_quadrant n W).isScDomain
  idem p _ := hidem p

/-- The fixed points `{p | L p = p}` of `L` in `[0,∞)ⁿ ⊕ W`. -/
def fixSet : Set (quadrant n W 0) := {p | L 0 p.1 = p.1}

/-- The data `(V, r) = (X, L)` of the sub-M-polyfold `fixSet L`. -/
def opSubData (hL : ∀ p ∈ quadrant n W 0, L 0 p ∈ quadrant n W 0)
    (hidem : ∀ p, L 0 (L 0 p) = L 0 p) : (quadrantPolyfold n W).SubData (fixSet L) where
  V := univ
  r p := ⟨L 0 p.1, hL p.1 p.2⟩
  isOpen := isOpen_univ
  mapsTo := mapsTo_univ _ _
  isScSmoothOn := quadrantMap_isScSmoothMap L hL
  idem p _ := Subtype.ext (hidem p.1)
  image := by
    ext p
    constructor
    · rintro ⟨q, -, rfl⟩
      exact ⟨hidem q.1, mem_univ _⟩
    · rintro ⟨hp, -⟩
      exact ⟨p, mem_univ _, Subtype.ext hp⟩

/-- `fixSet L` is a sub-M-polyfold of `[0,∞)ⁿ ⊕ W`. -/
theorem isSubMPolyfold_fixSet (hL : ∀ p ∈ quadrant n W 0, L 0 p ∈ quadrant n W 0)
    (hidem : ∀ p, L 0 (L 0 p) = L 0 p) : (quadrantPolyfold n W).IsSubMPolyfold (fixSet L) :=
  fun _ _ => ⟨_, (opSubData L hL hidem).isOpen, mem_univ _, _, (opSubData L hL hidem).mapsTo,
    (opSubData L hL hidem).isScSmoothOn, (opSubData L hL hidem).idem,
    (opSubData L hL hidem).image⟩

/-- In the identity chart, `T_z(fixSet L) = L(E)` has the sc-complement `ker L` in `T_zC = E`;
it lies in `E_z` when `L` does not change the `ℝⁿ`-component. -/
theorem hasReducedComplementAt_fixSet (hL : ∀ p ∈ quadrant n W 0, L 0 p ∈ quadrant n W 0)
    (hidem : ∀ p, L 0 (L 0 p) = L 0 p) (hfst : ∀ p, (L 0 p).1 = p.1)
    {O Q : Set (((ScBanach.const (Fin n → ℝ)).prod W) 0)} (hO : O = quadrant n W 0)
    (hQ : Q = (opRetraction L hL hidem).retract) (z : ((ScBanach.const (Fin n → ℝ)).prod W) 1)
    (hz : z ∈ ((ScBanach.const (Fin n → ℝ)).prod W).lvlSet Q 1) :
    HasReducedComplementAt (quadrant n W 0) O Q (ScIso.refl _) z := by
  subst hO hQ
  have hU := isRelOpenInQuadrant_quadrant n W
  set R := opRetraction L hL hidem with hR
  have hzU : z ∈ ((ScBanach.const (Fin n → ℝ)).prod W).lvlSet (quadrant n W 0) 1 := by
    rw [ScBanach.mem_lvlSet] at hz ⊢; exact R.retract_subset hz
  have hS := ScBanach.isScSplitting_of_idem L hidem
  refine ⟨LinearMap.range (L 0 : ((ScBanach.const (Fin n → ℝ)).prod W) 0 →ₗ[ℝ]
      ((ScBanach.const (Fin n → ℝ)).prod W) 0), ⊤,
    LinearMap.ker (L 0 : ((ScBanach.const (Fin n → ℝ)).prod W) 0 →ₗ[ℝ]
      ((ScBanach.const (Fin n → ℝ)).prod W) 0), ?_, ?_, ?_, ?_, fun m => ?_⟩
  · rw [tangentSpace_eq_coe_submodule R hz]
    have : scDeriv R.U R z = L 0 := L.scDeriv_eq hU.isScDomain hzU
    rw [this]
  · have hret : (ScRetraction.id hU).retract = quadrant n W 0 := image_id _
    have hz0 : z ∈ ((ScBanach.const (Fin n → ℝ)).prod W).lvlSet (ScRetraction.id hU).retract 1 := by
      rw [hret]; exact hzU
    have h := tangentSpace_eq_coe_submodule (ScRetraction.id hU) hz0
    rw [hret] at h
    have hD : scDeriv (ScRetraction.id hU).U (ScRetraction.id hU) z =
        ContinuousLinearMap.id ℝ (((ScBanach.const (Fin n → ℝ)).prod W) 0) :=
      IsSc1.scDeriv_eqOn (isSc1With_id _) (hU.isScDomain.uniqueDiffWithinAt 1) hzU
    have hrange : LinearMap.range (scDeriv (ScRetraction.id hU).U (ScRetraction.id hU) z :
        ((ScBanach.const (Fin n → ℝ)).prod W) 0 →ₗ[ℝ]
          ((ScBanach.const (Fin n → ℝ)).prod W) 0) = ⊤ := by
      rw [hD]; exact LinearMap.range_id
    rw [h, hrange]
  · intro v hv
    have hv' : L 0 v = 0 := hv
    refine ⟨Submodule.mem_top, (mem_minimalSubspaceWith _).2 fun i _ => ?_⟩
    change v.1 i = 0
    rw [← hfst v, hv']
    rfl
  · exact hS.2.1
  · have hc := hS.2.2 m
    refine ⟨hc.disjoint, ?_⟩
    rw [hc.sup_eq_top]
    exact (Submodule.comap_top _).symm

/-- **The fixed set of a corner-preserving idempotent sc-operator is a tame sub-M-polyfold**:
if `L² = L` and `L` does not change the `ℝⁿ`-component, then `{L p = p}` is a tame
sub-M-polyfold of `[0,∞)ⁿ ⊕ W` (2021 Definition 2.5.19 with `V = X`, `r = L`). -/
theorem isTameSubMPolyfold_fixSet (hidem : ∀ p, L 0 (L 0 p) = L 0 p)
    (hfst : ∀ p, (L 0 p).1 = p.1) : (quadrantPolyfold n W).IsTameSubMPolyfold (fixSet L) := by
  have hL : ∀ p ∈ quadrant n W 0, L 0 p ∈ quadrant n W 0 := fun p hp i => by
    change 0 ≤ (L 0 p).1 i
    rw [hfst p]
    exact hp i
  have hU := isRelOpenInQuadrant_quadrant n W
  have hne : (LocalModel.ofRelOpen hU).O.Nonempty := quadrant_nonempty n W
  refine ⟨quadrantPolyfold_isTame n W, fun y _ =>
    ⟨⟨opSubData L hL hidem, fun x _ => ?_, fun y hy hys => ?_⟩, mem_univ y⟩⟩
  · change dq n W ⟨L 0 x.1, hL x.1 x.2⟩ = dq n W x
    rw [dq_eq, dq_eq]
    congr 1
    exact Finset.filter_congr fun i _ => by
      change (L 0 x.1).1 i = 0 ↔ x.1.1 i = 0
      rw [hfst]
  · have hφ : (quadrantPolyfold n W).IsChart ((LocalModel.ofRelOpen hU).selfChart hne) :=
      hU.selfChart_isChart hne
    obtain ⟨z, hz, -⟩ := exists_smoothLvl_one_of_mem_smooth
      ((mem_smoothSet_iff_of_isChart hφ (mem_univ y)).1 hys)
    refine ⟨_, n, W, ScIso.refl _, z, hφ, mem_univ y, by ext; rfl, hz, ?_⟩
    refine hasReducedComplementAt_fixSet L hL hidem hfst rfl ?_ z ?_
    · ext p
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact (opRetraction L hL hidem).mem_retract_iff.2 ⟨q.2, hq.2⟩
      · intro hp
        obtain ⟨hp, hLp⟩ := (opRetraction L hL hidem).mem_retract_iff.1 hp
        exact ⟨⟨p, hp⟩, ⟨⟨⟨mem_univ _, mem_univ _⟩, mem_univ _, mem_univ _⟩, hLp⟩, rfl⟩
    · exact (ScBanach.mem_lvlSet _).2
        ⟨y, ⟨⟨⟨mem_univ _, mem_univ _⟩, mem_univ _, mem_univ _⟩, hy.1⟩, hz.symm⟩

/-! #### `A = {(x, y, 0)}` -/

variable (W) in
/-- `(a, w) ↦ (a, 0)` on `ℝ² ⊕ W`. -/
def projA : ScOperator ((ScBanach.const (Fin 2 → ℝ)).prod W)
    ((ScBanach.const (Fin 2 → ℝ)).prod W) :=
  ((ScBanach.const (Fin 2 → ℝ)).prodInlOp W).comp ((ScBanach.const (Fin 2 → ℝ)).prodFstOp W)

variable (W) in
/-- `A = {(x, y, 0) | x, y ≥ 0}` in `X = [0,∞)² ⊕ W` (2021, p. 63, with `W = ℝ`). -/
def setA : Set (quadrant 2 W 0) := {p | (p : ((ScBanach.const (Fin 2 → ℝ)).prod W) 0).2 = 0}

lemma setA_eq_fixSet : setA W = fixSet (projA W) := by
  ext p
  change p.1.2 = 0 ↔ ((p.1.1, 0) : ((ScBanach.const (Fin 2 → ℝ)).prod W) 0) = p.1
  constructor
  · intro h
    exact Prod.ext rfl h.symm
  · intro h
    exact (congrArg Prod.snd h).symm

variable (W) in
/-- **2021, text after Definition 2.5.19, p. 63**: `A = {(x, y, 0)}` is a tame sub-M-polyfold of
`[0,∞)² ⊕ W` (the text's `[0,∞)² × ℝ` is `W = ℝ`, `examples_A_B`). -/
theorem isTameSubMPolyfold_setA : (quadrantPolyfold 2 W).IsTameSubMPolyfold (setA W) := by
  rw [setA_eq_fixSet]
  exact isTameSubMPolyfold_fixSet (projA W) (fun _ => rfl) fun _ => rfl

variable (W) in
/-- **2021, text after Definition 2.5.19, p. 63**: the structure induced on `A` is tame (as `A`
is a tame sub-M-polyfold, `IsTameSubMPolyfold.hasTameInducedStructure`). -/
theorem hasTameInducedStructure_setA :
    (quadrantPolyfold 2 W).HasTameInducedStructure (setA W) :=
  (isTameSubMPolyfold_setA W).hasTameInducedStructure

/-! #### `B = {(x, x, 0)}` -/

/-- The averaging `a ↦ ((a₀ + a₁)/2, (a₀ + a₁)/2)` on `ℝ²`. -/
def average2 : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun a _ => (a 0 + a 1) / 2
      map_add' := fun a b => by ext; simp only [Pi.add_apply]; ring
      map_smul' := fun c a => by
        ext; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }

lemma average2_apply (a : Fin 2 → ℝ) (i : Fin 2) : average2 a i = (a 0 + a 1) / 2 := rfl

variable (W) in
/-- `(a, w) ↦ (average2 a, 0)` on `ℝ² ⊕ W`, an sc-smooth retraction of `[0,∞)² ⊕ W` onto `B`. -/
def projB : ScOperator ((ScBanach.const (Fin 2 → ℝ)).prod W)
    ((ScBanach.const (Fin 2 → ℝ)).prod W) :=
  ((ScBanach.const (Fin 2 → ℝ)).prodInlOp W).comp
    ((constOp average2).comp ((ScBanach.const (Fin 2 → ℝ)).prodFstOp W))

lemma projB_mapsTo : ∀ p ∈ quadrant 2 W 0, projB W 0 p ∈ quadrant 2 W 0 := fun p hp i => by
  change 0 ≤ (p.1 0 + p.1 1) / 2
  have := hp 0; have := hp 1
  positivity

lemma projB_idem (p : ((ScBanach.const (Fin 2 → ℝ)).prod W) 0) :
    projB W 0 (projB W 0 p) = projB W 0 p := by
  refine Prod.ext (funext fun i => ?_) rfl
  change ((p.1 0 + p.1 1) / 2 + (p.1 0 + p.1 1) / 2) / 2 = (p.1 0 + p.1 1) / 2
  ring

variable (W) in
/-- `B = {(x, x, 0) | x ≥ 0}` in `X = [0,∞)² ⊕ W` (2021, p. 63, with `W = ℝ`). -/
def setB : Set (quadrant 2 W 0) :=
  {p | (p : ((ScBanach.const (Fin 2 → ℝ)).prod W) 0).1 0 =
    (p : ((ScBanach.const (Fin 2 → ℝ)).prod W) 0).1 1 ∧
      (p : ((ScBanach.const (Fin 2 → ℝ)).prod W) 0).2 = 0}

lemma setB_eq_fixSet : setB W = fixSet (projB W) := by
  ext p
  change p.1.1 0 = p.1.1 1 ∧ p.1.2 = 0 ↔
    ((average2 p.1.1, 0) : ((ScBanach.const (Fin 2 → ℝ)).prod W) 0) = p.1
  constructor
  · rintro ⟨h01, h2⟩
    refine Prod.ext (funext fun i => ?_) h2.symm
    change (p.1.1 0 + p.1.1 1) / 2 = p.1.1 i
    fin_cases i
    · change (p.1.1 0 + p.1.1 1) / 2 = p.1.1 0
      rw [h01]; ring
    · change (p.1.1 0 + p.1.1 1) / 2 = p.1.1 1
      rw [h01]; ring
  · intro h
    have h1 := congrArg Prod.fst h
    have e0 := congrFun h1 0
    have e1 := congrFun h1 1
    change (p.1.1 0 + p.1.1 1) / 2 = p.1.1 0 at e0
    change (p.1.1 0 + p.1.1 1) / 2 = p.1.1 1 at e1
    exact ⟨e0.symm.trans e1, (congrArg Prod.snd h).symm⟩

variable (W) in
/-- `B` is a sub-M-polyfold of `[0,∞)² ⊕ W` (`V = X`, `r = projB`). -/
theorem isSubMPolyfold_setB : (quadrantPolyfold 2 W).IsSubMPolyfold (setB W) := by
  rw [setB_eq_fixSet]
  exact isSubMPolyfold_fixSet (projB W) projB_mapsTo projB_idem

lemma zero_mem_setB : (⟨0, zero_mem_quadrant 2 W⟩ : quadrant 2 W 0) ∈ setB W := ⟨rfl, rfl⟩

/-- **2021, text after Definition 2.5.19, p. 63, at the corner**: no retraction `r` onto `B`
satisfying 2021 Definition 2.5.19 (1)–(2) is defined near the corner `0`.  For small `t > 0`
the point `(t, 0, 0) ∈ V` has `d_X = 1`, while `d_X = 0` or `2` on `B`; (3) is not needed. -/
theorem not_mem_tameSubData_setB (d : (quadrantPolyfold 2 W).TameSubData (setB W)) :
    (⟨0, zero_mem_quadrant 2 W⟩ : quadrant 2 W 0) ∉ d.V := by
  intro h0
  let γ : ℝ → quadrant 2 W 0 := fun t =>
    ⟨((fun i => if i = 0 then |t| else 0), 0), fun i => by
      change 0 ≤ (if i = 0 then |t| else 0)
      split_ifs
      · exact abs_nonneg t
      · exact le_rfl⟩
  have hγ : Continuous γ := by
    refine Continuous.subtype_mk ?_ _
    refine Continuous.prodMk (continuous_pi fun i => ?_) continuous_const
    split_ifs
    · exact continuous_abs
    · exact continuous_const
  have hγ0 : γ 0 = ⟨0, zero_mem_quadrant 2 W⟩ := by
    refine Subtype.ext (Prod.ext (funext fun i => ?_) rfl)
    change (if i = 0 then |(0 : ℝ)| else 0) = 0
    simp
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (d.isOpen.preimage hγ) 0
    (by rw [mem_preimage, hγ0]; exact h0)
  have hε2 : 0 < ε / 2 := half_pos hε
  have hx : γ (ε / 2) ∈ d.V := hball (by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hε2]
    exact half_lt_self hε)
  have hdx : dq 2 W (γ (ε / 2)) = 1 := by
    rw [dq_eq, Finset.card_filter, Fin.sum_univ_two]
    have h1 : coord 0 (γ (ε / 2)) = ε / 2 := by
      change (if (0 : Fin 2) = 0 then |ε / 2| else 0) = ε / 2
      rw [if_pos rfl, abs_of_pos hε2]
    have h2 : coord 1 (γ (ε / 2)) = 0 := by
      change (if (1 : Fin 2) = 0 then |ε / 2| else 0) = 0
      rw [if_neg (by decide)]
    rw [h1, h2, if_neg hε2.ne', if_pos rfl]
  have hrx : d.r (γ (ε / 2)) ∈ setB W := d.toSubData.apply_mem hx
  have hdr : dq 2 W (d.r (γ (ε / 2))) ≠ 1 := by
    rw [dq_eq, Finset.card_filter, Fin.sum_univ_two]
    have : coord 0 (d.r (γ (ε / 2))) = coord 1 (d.r (γ (ε / 2))) := hrx.1
    rw [this]
    split_ifs <;> simp
  exact hdr ((d.degIndex_apply _ hx).trans hdx)

variable (W) in
/-- **2021, text after Definition 2.5.19, p. 63**: `B = {(x, x, 0)}` is not a tame
sub-M-polyfold of `[0,∞)² ⊕ W`. -/
theorem not_isTameSubMPolyfold_setB :
    ¬ (quadrantPolyfold 2 W).IsTameSubMPolyfold (setB W) := fun h => by
  obtain ⟨d, hd⟩ := h.2 _ zero_mem_setB
  exact not_mem_tameSubData_setB d hd

/-! #### `B ≅ [0,∞)` and the tame induced structure on `B` -/

/-- The zero sc-Banach space `ℝ⁰`; `[0,∞) ⊕ ℝ⁰` is the half-line `[0,∞)`. -/
abbrev zeroSpace : ScBanach := ScBanach.const (Fin 0 → ℝ)

/-- `t ↦ (t, t)`, `ℝ → ℝ²`. -/
def dup2 : (Fin 1 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun t _ => t 0
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- `a ↦ a₀`, `ℝ² → ℝ`. -/
def first2 : (Fin 2 → ℝ) →L[ℝ] (Fin 1 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun a _ => a 0
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

variable (W) in
/-- `(t, 0) ↦ (t, t, 0)`, `ℝ ⊕ ℝ⁰ → ℝ² ⊕ W`. -/
def embOp : ScOperator ((ScBanach.const (Fin 1 → ℝ)).prod zeroSpace)
    ((ScBanach.const (Fin 2 → ℝ)).prod W) :=
  ((ScBanach.const (Fin 2 → ℝ)).prodInlOp W).comp
    ((constOp dup2).comp ((ScBanach.const (Fin 1 → ℝ)).prodFstOp zeroSpace))

variable (W) in
/-- `(a, w) ↦ (a₀, 0)`, `ℝ² ⊕ W → ℝ ⊕ ℝ⁰`. -/
def firstOp : ScOperator ((ScBanach.const (Fin 2 → ℝ)).prod W)
    ((ScBanach.const (Fin 1 → ℝ)).prod zeroSpace) :=
  ((ScBanach.const (Fin 1 → ℝ)).prodInlOp zeroSpace).comp
    ((constOp first2).comp ((ScBanach.const (Fin 2 → ℝ)).prodFstOp W))

lemma embOp_mapsTo : ∀ p ∈ quadrant 1 zeroSpace 0, embOp W 0 p ∈ quadrant 2 W 0 :=
  fun _ hp _ => hp 0

lemma firstOp_mapsTo : ∀ p ∈ quadrant 2 W 0, firstOp W 0 p ∈ quadrant 1 zeroSpace 0 :=
  fun _ hp _ => hp 0

variable (W) in
/-- The map `[0,∞) → B`, `t ↦ (t, t, 0)`. -/
def halfLineToB (s : quadrant 1 zeroSpace 0) : setB W :=
  ⟨⟨embOp W 0 s.1, embOp_mapsTo s.1 s.2⟩, ⟨rfl, rfl⟩⟩

variable (W) in
/-- The map `B → [0,∞)`, `(x, x, 0) ↦ x`. -/
def bToHalfLine (b : setB W) : quadrant 1 zeroSpace 0 :=
  ⟨firstOp W 0 b.1.1, firstOp_mapsTo b.1.1 b.1.2⟩

variable (W) in
/-- **2021, text after Definition 2.5.19, p. 63**: with the structure induced from
`[0,∞)² ⊕ W`, `B` is sc-diffeomorphic to the half-line `[0,∞)` (`= [0,∞) ⊕ ℝ⁰`). -/
theorem halfLineToB_isScDiffeoOn :
    letI := (quadrantPolyfold 2 W).paracompactSpace_subtype (setB W)
    (quadrantPolyfold 1 zeroSpace).IsScDiffeoOn (subPolyfold (isSubMPolyfold_setB W))
      (halfLineToB W) (bToHalfLine W) univ univ := by
  let _ := (quadrantPolyfold 2 W).paracompactSpace_subtype (setB W)
  refine ⟨?_, ?_, mapsTo_univ _ _, mapsTo_univ _ _, fun s _ => ?_, fun b _ => ?_⟩
  · exact isScSmoothOn_subPolyfold_of_val_ts (isSubMPolyfold_setB W)
      (quadrantMap_isScSmoothMap (embOp W) embOp_mapsTo)
  · exact (quadrantMap_isScSmoothMap (firstOp W) firstOp_mapsTo).comp
      (subPolyfold_inclusion_isScSmooth (isSubMPolyfold_setB W))
  · refine Subtype.ext (Prod.ext (funext fun i => ?_) (funext fun i => i.elim0))
    rw [Fin.fin_one_eq_zero i]
    rfl
  · refine Subtype.ext (Subtype.ext (Prod.ext (funext fun i => ?_) b.2.2.symm))
    fin_cases i
    · rfl
    · exact b.2.1

variable (W) in
/-- **2021, text after Definition 2.5.19, p. 63**: the M-polyfold structure induced on `B` is
tame (2021 Definition 2.5.18): the chart `B → [0,∞)`, `(x, x, 0) ↦ x`, has the tame model
`[0,∞)` (the identity retraction), although `B` is not a tame sub-M-polyfold. -/
theorem hasTameInducedStructure_setB :
    (quadrantPolyfold 2 W).HasTameInducedStructure (setB W) := by
  refine ⟨isSubMPolyfold_setB W, ?_⟩
  let _ := (quadrantPolyfold 2 W).paracompactSpace_subtype (setB W)
  have h := (halfLineToB_isScDiffeoOn W).symm
  have hU := isRelOpenInQuadrant_quadrant 1 zeroSpace
  have hne : (LocalModel.ofRelOpen hU).O.Nonempty := quadrant_nonempty 1 zeroSpace
  have hψ : (quadrantPolyfold 1 zeroSpace).IsChart ((LocalModel.ofRelOpen hU).selfChart hne) :=
    hU.selfChart_isChart hne
  refine isTame_of_forall_exists_chart _ fun b =>
    ⟨transportChart h _, transportChart_isChart h hψ, ⟨mem_univ b, mem_univ _⟩, ?_⟩
  change IsTameRetract _ (quadrant 1 zeroSpace 0)
    ((LocalModel.ofRelOpen hU).selfChart hne '' (univ ∩ univ))
  refine ⟨ScRetraction.id hU, ?_, ScRetraction.id_isTame hU⟩
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨⟨q, hq⟩, ⟨mem_univ _, mem_univ _⟩, rfl⟩
  · rintro ⟨q, -, rfl⟩
    exact ⟨q.1, q.2, rfl⟩

/-! #### The text's case `X = [0,∞)² × ℝ` -/

/-- **2021, text after Definition 2.5.19, p. 63** (new in the 2021 edition): in
`X = [0,∞)² × ℝ` (`W = ℝ`), `A = {(x, y, 0)}` is a tame sub-M-polyfold, `B = {(x, x, 0)}` is a
sub-M-polyfold which is not a tame sub-M-polyfold, the induced structure on `B` is tame, and `B`
is sc-diffeomorphic to `[0,∞)`. -/
theorem examples_A_B :
    (quadrantPolyfold 2 (ScBanach.const ℝ)).IsTameSubMPolyfold (setA (ScBanach.const ℝ)) ∧
      (quadrantPolyfold 2 (ScBanach.const ℝ)).IsSubMPolyfold (setB (ScBanach.const ℝ)) ∧
      ¬ (quadrantPolyfold 2 (ScBanach.const ℝ)).IsTameSubMPolyfold (setB (ScBanach.const ℝ)) ∧
      (quadrantPolyfold 2 (ScBanach.const ℝ)).HasTameInducedStructure
        (setB (ScBanach.const ℝ)) ∧
      (letI := (quadrantPolyfold 2 (ScBanach.const ℝ)).paracompactSpace_subtype
          (setB (ScBanach.const ℝ));
        (quadrantPolyfold 1 zeroSpace).IsScDiffeoOn
          (subPolyfold (isSubMPolyfold_setB (ScBanach.const ℝ)))
          (halfLineToB (ScBanach.const ℝ)) (bToHalfLine (ScBanach.const ℝ)) univ univ) :=
  ⟨isTameSubMPolyfold_setA _, isSubMPolyfold_setB _, not_isTameSubMPolyfold_setB _,
    hasTameInducedStructure_setB _, halfLineToB_isScDiffeoOn _⟩

end TameSubExample

end Polyfold
