import Polyfold.Chapter2.TameFaces
import Polyfold.Chapter2.TameRetracts
import Polyfold.Chapter7.EpGroupoid

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, Definitions 2.4.1,
2.5.2, 2.5.7: **an M-polyfold with `d_X ≡ 0` is tame** (gap TX-7, used for Corollary 15.3.10,
whose hypothesis is `d_X ≡ 0` while Theorems 15.3.7 and 15.3.9 ask for a tame `X`).

# `d_X ≡ 0` implies tame

## The argument

At `x` take a chart `φ` with `d_C(φ(x)) = d_X(x) = 0` (the minimum of Definition 2.4.1 is
attained).  The points `y` of its domain with `d_C(φ(y)) = 0` form an open set `s`
(Lemma 2.4.3 for the chart).  The restriction of `φ` to `s` has the model `O ∩ W` (`W` open), and
the retraction `r` restricted to `U ∩ r⁻¹(W) ∩ {d_C = 0}` (an open part of the interior of `C`)
is tame: (1) `d_C ≡ 0` on its domain, (2) at a smooth point `E_x = E` (no vanishing coordinate),
and `(1 − Dr(x))E` is an sc-complement of `T_xO` (`ScRetraction.isScSplitting_range_scDeriv`).

## What is formalized

* `degIndexWith_eq_zero_iff_ty`, `isOpen_setOf_pos_coord_ty`;
* `isTameRetract_inter_of_degIndex_eq_zero_ty`: for an sc-smooth retraction `R` and an open `W`
  with `d_C = 0` on `r(U) ∩ W`, the retract `r(U) ∩ W` is tame;
* **`MPolyfold.isTame_of_degIndex_eq_zero`** and **`EpGroupoid.isTame_of_degIndex_eq_zero`**.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

variable {E : ScBanach} {C : Set (E 0)}

theorem degIndexWith_eq_zero_iff_ty {n : ℕ} {W : ScBanach}
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (x : E 0) :
    degIndexWith T x = 0 ↔ ∀ i, (T 0 x).1 i ≠ 0 := by
  simp [degIndexWith, quadrantDeg, Finset.card_eq_zero, Finset.filter_eq_empty_iff]

/-- The points with all half-line coordinates positive form an open set. -/
theorem isOpen_setOf_pos_coord_ty {n : ℕ} {W : ScBanach}
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) :
    IsOpen {z : E 0 | ∀ i, 0 < (T 0 z).1 i} := by
  have : {z : E 0 | ∀ i, 0 < (T 0 z).1 i} = ⋂ i, {z : E 0 | 0 < (T 0 z).1 i} := by
    ext z; simp
  rw [this]
  refine isOpen_iInter_of_finite fun i => isOpen_lt continuous_const ?_
  exact (continuous_apply i).comp (continuous_fst.comp (T 0).continuous)

/-- For `z ∈ C`: `d_C(z) = 0` iff all half-line coordinates of `z` are positive. -/
theorem degIndex_eq_zero_iff_pos_ty {n : ℕ} {W : ScBanach}
    {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)} (hT : C = T 0 ⁻¹' quadrant n W 0)
    {z : E 0} (hz : z ∈ C) : degIndex E C z = 0 ↔ ∀ i, 0 < (T 0 z).1 i := by
  rw [degIndex_eq T hT hz, degIndexWith_eq_zero_iff_ty]
  have hq : ∀ i, 0 ≤ (T 0 z).1 i := by
    have : z ∈ T 0 ⁻¹' quadrant n W 0 := hT ▸ hz
    exact this
  exact forall_congr' fun i => ⟨fun h => lt_of_le_of_ne (hq i) (Ne.symm h), fun h => h.ne'⟩

/-- **A retract without degenerate points is tame**: for an sc-smooth retraction `R` of `C` and an
open `W` with `d_C = 0` on `r(U) ∩ W`, the retract `r(U) ∩ W` is a tame retract (restrict `r` to
`U ∩ r⁻¹(W) ∩ {d_C = 0}`). -/
theorem isTameRetract_inter_of_degIndex_eq_zero_ty (R : ScRetraction E C) {W : Set (E 0)}
    (hW : IsOpen W) (h0 : ∀ y ∈ R.retract ∩ W, degIndex E C y = 0) :
    IsTameRetract E C (R.retract ∩ W) := by
  obtain ⟨n, V, T, hT⟩ := R.relOpen.isPartialQuadrant
  set D : Set (E 0) := {z | ∀ i, 0 < (T 0 z).1 i} with hD
  have hDo : IsOpen D := isOpen_setOf_pos_coord_ty T
  set R₁ := R.restrict hW with hR₁
  have hR₁U : R₁.U = R.U ∩ R ⁻¹' W := rfl
  have hRD : ∀ y ∈ R.retract ∩ W, y ∈ D := fun y hy =>
    (degIndex_eq_zero_iff_pos_ty hT (R.U_subset_C (R.retract_subset hy.1))).1 (h0 y hy)
  let R₂ : ScRetraction E C :=
    { U := R₁.U ∩ D
      toFun := R
      relOpen := R₁.relOpen.inter_isOpen hDo
      mapsTo := fun y hy => ⟨R₁.mapsTo hy.1, hRD _ ⟨R.apply_mem_retract hy.1.1, hy.1.2⟩⟩
      isScSmooth := R₁.isScSmooth.of_subset (R₁.relOpen.inter_isOpen hDo).isScDomain
        inter_subset_left
      idem := fun y hy => R.idem y hy.1.1 }
  have hR₂U : R₂.U = R.U ∩ R ⁻¹' W ∩ D := rfl
  have hret : R₂.retract = R.retract ∩ W := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨R.apply_mem_retract hy.1.1, hy.1.2⟩
    · rintro ⟨hzO, hzW⟩
      have hRz : R z = z := R.apply_eq_self_of_mem_retract hzO
      refine ⟨z, ⟨⟨R.retract_subset hzO, ?_⟩, hRD z ⟨hzO, hzW⟩⟩, hRz⟩
      change R z ∈ W
      rw [hRz]; exact hzW
  have hdeg0 : ∀ z ∈ R₂.U, degIndex E C z = 0 := fun z hz =>
    (degIndex_eq_zero_iff_pos_ty hT (R.U_subset_C hz.1.1)).2 hz.2
  refine ⟨R₂, hret, fun m W' T' hT' => ⟨fun x hx => ?_, fun x hx hs => ?_⟩⟩
  · rw [hdeg0 x hx, hdeg0 _ (R₂.mapsTo hx)]
  · refine ⟨_, R₂.isScSplitting_range_scDeriv hx hs, fun v _ => ?_⟩
    have hxU : E.toBase 1 x ∈ R₂.U := R₂.retract_subset hx
    have hxC : E.toBase 1 x ∈ C := R.U_subset_C hxU.1.1
    have h0' : degIndexWith T' (E.toBase 1 x) = 0 := by
      rw [← degIndex_eq T' hT' hxC]; exact hdeg0 _ hxU
    rw [mem_minimalSubspaceWith]
    intro i hi
    exact absurd hi ((degIndexWith_eq_zero_iff_ty T' _).1 h0' i)

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

/-- **An M-polyfold with `d_X ≡ 0` is tame** (Definitions 2.4.1, 2.5.7): every point lies in a
chart of the structure modelled on a tame retract. -/
theorem isTame_of_degIndex_eq_zero (h : ∀ x, P.degIndex x = 0) : P.IsTame := by
  refine P.isTame_of_forall_exists_chart fun x => ?_
  obtain ⟨φ, hφ, hx, hd⟩ := P.exists_isChart_degIndex_eq x
  set s : Set X := {y | y ∈ φ.source ∧ chartDegIndex φ y = 0} with hsdef
  have hss : s ⊆ φ.source := fun y hy => hy.1
  have hs : IsOpen s := isOpen_iff_mem_nhds.2 fun y hy => by
    filter_upwards [φ.isOpen_source.mem_nhds hy.1, eventually_chartDegIndex_le φ hy.1]
      with z hz hle
    exact ⟨hz, by have := hy.2; omega⟩
  refine ⟨φ.restrict hss hs, IsChart.restrict P hφ hss hs, ⟨hx, by rw [← hd, h x]⟩, ?_⟩
  obtain ⟨W, hW, hWs⟩ := φ.exists_isOpen_image_eq hss hs
  obtain ⟨R, hR⟩ := φ.model.isScRetract
  change IsTameRetract φ.model.E φ.model.C (φ '' s)
  rw [hWs, ← hR]
  refine isTameRetract_inter_of_degIndex_eq_zero_ty R hW fun y hy => ?_
  have hy' : y ∈ φ '' s := by rw [hWs, ← hR]; exact hy
  obtain ⟨z, hz, rfl⟩ := hy'
  exact hz.2

end MPolyfold

namespace EpGroupoid

universe u

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- **An ep-groupoid with `d_X ≡ 0` is tame** (its object M-polyfold is). -/
theorem isTame_of_degIndex_eq_zero (h : ∀ x, X.PObj.degIndex x = 0) : X.IsTame :=
  X.PObj.isTame_of_degIndex_eq_zero h

end EpGroupoid

end Polyfold
