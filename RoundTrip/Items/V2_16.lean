import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_16

/-! Round trip for V2_16 (the level `X^1` / `X_m` of an M-polyfold: the charts
`(V_m, φ, (O_m, C_m, E_m))` form an atlas).

`A` is the conjunction of the types of the listed theorems `Polyfold.ScRetraction.shift_retract`,
`Polyfold.IsScRetract.shift`, `Polyfold.IsScSmoothRetractMap.shift` (no universe parameter),
`Polyfold.MPolyfold.levelChart_compatible`, `Polyfold.MPolyfold.shift_isChart` and (refresh
2026-11-02, added to the row) `Polyfold.MPolyfold.mem_shift_levelSet_iff` (universe `0`; B lives in
`Type`).  `ScRetraction.shift`, `LocalModel.shift`, `levelChart`, `levelAtlas`, `MPolyfold.shift`
are definitions (vocabulary).

* `A → B` is NOT proved.  B is stated for every level `m`; A (and the project) only builds the
  charts and the M-polyfold for `m = 1` (`X¹`).  The new conjunct `mem_shift_levelSet_iff` says
  `(X¹)_m = X_{m+1}` as SETS only; it does not identify the topology of `(X¹)_{m-1}` (or of an
  iterate `X¹¹…`) with B's `levelTopology m` on `X_m`, nor the iterated level charts (models
  `E¹¹…`) with B's level-`m` charts (models `E^m = E.shiftAdd m`, retraction and transitions
  sc-smooth in that structure).  Getting B at level `m ≥ 2` would need Proposition 1.17 iterated
  and transported along `E¹…¹ ≅ E^m` for retractions and retract maps, and the homeomorphism
  `V_m ≃ O_m` for `levelTopology m`, i.e. the rest of the project's gap G.6: new construction,
  not glue.  Even at `m = 1` B uses `E^1 = E.shiftAdd 1` (levels `E_{1+k}`) where the project uses
  `E¹ = E.shift` (levels `E_{k+1}`); bridging `IsChartB`'s "`(O_1, C_1, E^1)` is a retract" needs a
  retraction in the `E.shiftAdd 1` structure (transport of `ScRetraction`, partial quadrant
  included, along `E¹ ≅ E^1`): glue, but not done.
* `B → A` is proved.  `levelChart_compatible` and `shift_isChart` come from B at `m = 1`: B's
  `CompatibleB` for the level charts gives a retraction in the `E^1` structure, and the chain rule
  with the sc-isomorphisms `E¹ ≅ E^1` (identity on level `0`, `shiftIso`) turns it into the
  project's Definition 2.7 in the `E¹` structure (`retractMap_of_B`).  The three general facts
  about retracts (`shift_retract`, `IsScRetract.shift`, `IsScSmoothRetractMap.shift`: Proposition
  1.17 for arbitrary retracts and maps between them) are NOT consequences of B as stated (B only
  speaks of chart transitions); they are re-proved here directly (`shift_retract'`,
  `isScRetract_shift'`, `isScSmoothRetractMap_shift'`), without B.  The new conjunct
  `mem_shift_levelSet_iff` follows from the level charts being charts of `X¹` (`shift_isChart`,
  derived from B above) and set-level glue (`mem_levelSet_iff` of `X¹` and of `X`,
  `ScBanach.mem_range_shift_toBase_iff`, `toBase_levelLift`). -/

namespace RoundTrip.V2_16
open Polyfold Set MPolyfold

/-- The project's statement (universe `0` where there is a universe). -/
def A : Prop :=
  (type_of% @Polyfold.ScRetraction.shift_retract) ∧
    (type_of% @Polyfold.IsScRetract.shift) ∧
    (type_of% @Polyfold.IsScSmoothRetractMap.shift) ∧
    (type_of% @Polyfold.MPolyfold.levelChart_compatible.{0}) ∧
    (type_of% @Polyfold.MPolyfold.shift_isChart.{0}) ∧
    (type_of% @Polyfold.MPolyfold.mem_shift_levelSet_iff.{0})

theorem A_holds : A :=
  ⟨@Polyfold.ScRetraction.shift_retract, @Polyfold.IsScRetract.shift,
    @Polyfold.IsScSmoothRetractMap.shift, @Polyfold.MPolyfold.levelChart_compatible.{0},
    @Polyfold.MPolyfold.shift_isChart.{0}, @Polyfold.MPolyfold.mem_shift_levelSet_iff.{0}⟩

section Glue

/-! #### Proposition 1.17 for retracts, re-proved (not from B) -/

theorem shift_retract' {E : ScBanach} {C : Set (E 0)} (R : ScRetraction E C) :
    R.shift.retract = E.lvlSet R.retract 1 := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    change E.toBase 1 (levelMap R 1 y) ∈ R.retract
    rw [R.isSc1.isSc0.toBase_levelMap hy]
    exact R.apply_mem_retract hy
  · intro hz
    exact ⟨z, R.lvlSet_retract_subset 1 hz, R.levelMap_one_eq_self hz⟩

theorem isScRetract_shift' {E : ScBanach} {C O : Set (E 0)} (hO : IsScRetract E C O) :
    IsScRetract E.shift (E.lvlSet C 1) (E.lvlSet O 1) := by
  obtain ⟨R, rfl⟩ := hO
  exact ⟨R.shift, shift_retract' R⟩

theorem isScSmoothRetractMap_shift' {E E' : ScBanach} {C O : Set (E 0)} {C' O' : Set (E' 0)}
    {f : E 0 → E' 0} (hf : IsScSmoothRetractMap E C O E' C' O' f) (hO : IsScRetract E C O) :
    IsScSmoothRetractMap E.shift (E.lvlSet C 1) (E.lvlSet O 1) E'.shift (E'.lvlSet C' 1)
      (E'.lvlSet O' 1) (levelMap f 1) := by
  rw [isScSmoothRetractMap_iff_exists (isScRetract_shift' hO)]
  refine ⟨hf.mapsTo_levelMap hO 1, ?_⟩
  have hf0 := hf.isSc0 hO
  obtain ⟨R, rfl⟩ := hO
  refine ⟨R.shift, shift_retract' R, ?_⟩
  have h1 := (hf.comp_isScSmooth R rfl).shift R.isScDomain
  refine h1.congr R.shift.isScDomain fun x hx => ?_
  exact hf0.levelMap_comp R.isSc1.isSc0 R.mapsTo_retract hx

/-! #### `E¹ ≅ E^1` -/

/-- `E¹ ≅ E^1`, the identity on level `0`. -/
noncomputable def shiftIso (E : ScBanach) : ScIso E.shift (E.shiftAdd 1) :=
  (E.shiftAddZeroIso.shift).trans (E.shiftAddShiftIso 0)

theorem shiftIso_zero (E : ScBanach) (x : E.shift 0) : (shiftIso E 0 x : E 1) = x := rfl

theorem shiftIso_symm_zero (E : ScBanach) (y : (E.shiftAdd 1) 0) :
    ((shiftIso E).symm 0 y : E 1) = y :=
  (shiftIso_zero E _).symm.trans ((shiftIso E 0).apply_symm_apply y)

/-- B's Definition 2.7 in the `E^1` structures gives the project's in the `E¹` structures (same
sets, same map: the chain rule with `E¹ ≅ E^1`). -/
theorem retractMap_of_B {E E' : ScBanach} {C O : Set (E 1)} {C' O' : Set (E' 1)}
    {f : E 1 → E' 1} (h : IsScSmoothRetractMapB (E.shiftAdd 1) C O (E'.shiftAdd 1) O' f) :
    IsScSmoothRetractMap E.shift C O E'.shift C' O' f := by
  obtain ⟨hmaps, R, hR, hsm⟩ := h
  refine ⟨hmaps, fun S hS => ?_⟩
  have h1 := IsScSmooth.comp S.isScDomain (isScDomain_univ _)
    ((shiftIso E).toScOperator.isScSmooth (isScDomain_univ _)) S.isScSmooth (mapsTo_univ _ _)
  have hmS : MapsTo ((shiftIso E).toScOperator 0 ∘ S.toFun) S.U R.U := fun y hy => by
    have : S y ∈ O := hS ▸ S.apply_mem_retract hy
    rw [← hR] at this
    exact R.retract_subset this
  have h2 := IsScSmooth.comp S.isScDomain R.isScDomain hsm h1 hmS
  have h3 := IsScSmooth.comp S.isScDomain (isScDomain_univ _)
    ((shiftIso E').symm.toScOperator.isScSmooth (isScDomain_univ _)) h2 (mapsTo_univ _ _)
  refine h3.congr S.isScDomain fun y hy => ?_
  have hSy : S y ∈ R.retract := by rw [hR]; exact hS ▸ S.apply_mem_retract hy
  change (shiftIso E').symm 0 (f (R (shiftIso E 0 (S y)))) = f (S y)
  rw [shiftIso_symm_zero]
  change f (R (S y)) = f (S y)
  rw [R.apply_eq_self_of_mem_retract hSy]

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- B's transition map `transB` is the transition map of the level charts on their overlap. -/
theorem transB_level {φ ψ : MChart X} (hφ : P.IsChart φ) (hψ : P.IsChart ψ) (x₀ y₀ : P.Level 1)
    {x : P.Level 1} (hx : x ∈ (levelChart hφ x₀).source) :
    transB (VmB P φ 1) (φmB P φ 1) (φmB P ψ 1) (levelChart hφ x₀ x) = levelChart hψ y₀ x := by
  unfold transB
  rw [dif_pos ⟨x, hx, rfl⟩]
  generalize_proofs h
  obtain ⟨hy, hyeq⟩ := h.choose_spec
  have : h.choose = x := (levelChart hφ x₀).toPartialEquiv.injOn hy hx hyeq
  rw [this]
  rfl

end Glue

/-- The level charts are compatible, from B at `m = 1`. -/
theorem levelChart_compatible_of_B (hB : B) {X : Type} [TopologicalSpace X] [T2Space X]
    [ParacompactSpace X] {P : MPolyfold X} {φ ψ : MChart X} (hφ : P.IsChart φ) (x₀ : P.Level 1)
    (hψ : P.IsChart ψ) (y₀ : P.Level 1) :
    (levelChart hφ x₀).Compatible (levelChart hψ y₀) := by
  have hkey : ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
      {P : MPolyfold X} {φ ψ : MChart X} (hφ : P.IsChart φ) (x₀ : P.Level 1)
      (hψ : P.IsChart ψ) (y₀ : P.Level 1),
      IsScSmoothRetractMap (levelChart hφ x₀).model.E (levelChart hφ x₀).model.C
        ((levelChart hφ x₀).overlap (levelChart hψ y₀)) (levelChart hψ y₀).model.E
        (levelChart hψ y₀).model.C ((levelChart hψ y₀).overlap (levelChart hφ x₀))
        ((levelChart hφ x₀).transition (levelChart hψ y₀)) := by
    intro X _ _ _ P φ ψ hφ x₀ hψ y₀
    have h := ((hB X P 1).2.1 φ ψ hφ hψ).1
    have hov : (levelChart hψ y₀).overlap (levelChart hφ x₀) =
        (levelChart hψ y₀) '' ((levelChart hφ x₀).source ∩ (levelChart hψ y₀).source) := by
      rw [MChart.overlap, inter_comm]
    rw [hov]
    refine (retractMap_of_B h).congr ?_
    rintro _ ⟨x, hx, rfl⟩
    have h1 := transB_level hφ hψ x₀ y₀ (x := x) hx.1
    have h2 : (levelChart hφ x₀).transition (levelChart hψ y₀) (levelChart hφ x₀ x) =
        levelChart hψ y₀ x := by
      change levelChart hψ y₀ ((levelChart hφ x₀).symm (levelChart hφ x₀ x)) = _
      rw [(levelChart hφ x₀).symm_apply_apply hx.1]
    exact h1.trans h2.symm
  exact ⟨hkey hφ x₀ hψ y₀, hkey hψ y₀ hφ x₀⟩

theorem shift_isChart_of_B (hB : B) : type_of% @Polyfold.MPolyfold.shift_isChart.{0} := by
  intro X _ _ _ P _ φ hφ x₀ χ hχ
  obtain ⟨ψ, hψ, y₀, rfl⟩ := hχ
  exact levelChart_compatible_of_B hB hφ x₀ hψ y₀

/-- `(X¹)_m = X_{m+1}`: the level charts are charts of `X¹` (from B), then set-level glue. -/
theorem mem_shift_levelSet_iff_of_B (hB : B) :
    type_of% @Polyfold.MPolyfold.mem_shift_levelSet_iff.{0} := by
  intro X _ _ _ PX m x
  obtain ⟨φ, hφ, hx⟩ := PX.exists_isChart_mem_source (PX.levelVal 1 x)
  rw [PX.shift.mem_levelSet_iff (shift_isChart_of_B hB hφ x)
      (show x ∈ (levelChart hφ x).source from hx),
    PX.mem_levelSet_iff hφ hx, levelChart_apply]
  change levelLift φ 1 (PX.levelVal 1 x) ∈ Set.range (φ.model.E.shift.toBase m) ↔ _
  rw [ScBanach.mem_range_shift_toBase_iff, PX.toBase_levelLift hφ hx (levelVal_mem x)]

theorem B_to_A : B → A := fun hB =>
  ⟨fun R => shift_retract' R, fun hO => isScRetract_shift' hO,
    fun hf hO => isScSmoothRetractMap_shift' hf hO,
    fun hφ x₀ hψ y₀ => levelChart_compatible_of_B hB hφ x₀ hψ y₀, shift_isChart_of_B hB,
    mem_shift_levelSet_iff_of_B hB⟩

#rt_check_soft RoundTrip.V2_16.B_to_A [Polyfold.ScRetraction.shift_retract,
  Polyfold.IsScRetract.shift, Polyfold.IsScSmoothRetractMap.shift,
  Polyfold.MPolyfold.levelChart_compatible, Polyfold.MPolyfold.shift_isChart,
  Polyfold.MPolyfold.mem_shift_levelSet_iff]
#rt_overlap RoundTrip.V2_16.B_to_A [Polyfold.ScRetraction.shift_retract,
  Polyfold.IsScRetract.shift, Polyfold.IsScSmoothRetractMap.shift,
  Polyfold.MPolyfold.levelChart_compatible, Polyfold.MPolyfold.shift_isChart,
  Polyfold.MPolyfold.mem_shift_levelSet_iff]

end RoundTrip.V2_16
