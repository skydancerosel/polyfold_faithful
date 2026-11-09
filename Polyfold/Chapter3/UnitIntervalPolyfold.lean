import Polyfold.Chapter3.ParamPerturbation
import Polyfold.Chapter1.ExpositionLemmas
import Polyfold.Chapter2.LevelPolyfold
import Polyfold.Chapter2.TameFaces

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.2, Proposition 6.2.2
(p. 240) and §6.6 (pp. 263–276) (preprint: Proposition 6.2, §6.5): **the interval `[0, 1]` as an
M-polyfold with boundary** (Definition 2.3.4, preprint 2.13), the domain of the text's sc-smooth
paths.  Gap G.65 (the M-polyfold `[0, 1]` and its paths); row V3.98 (with
`IndexAlongPathsInterval.lean`).

# `[0, 1]` as an M-polyfold

## The text, paraphrased

The text's paths, homotopies and families are sc-smooth maps on `[0, 1]` (Proposition 6.2.2:
"an sc-smooth path `φ : [0, 1] → X`"; §6.6: the orientation propagated along such paths), and
`[0, 1]` is treated as an M-polyfold with boundary without comment.

## What is formalized

* `isScSmoothRetractMap_const_of_contDiff_of_mapsTo` (general): in finite dimensions a `C^∞` map
  sending a retract `O` into `O'` is sc-smooth between the retracts.
* `UnitInterval.halfC` (the half-line `[0, ∞)` in `ℝ¹`, a partial quadrant,
  `UnitInterval.isPartialQuadrant_halfC`) and `UnitInterval.modelO = [0, 1)`, relatively open in
  it (`UnitInterval.isRelOpen_modelO`); `UnitInterval.model`, the local model `([0, 1), [0, ∞), ℝ)`
  with the identity retraction.
* `UnitInterval.leftChart` (`t` on `[0, 1)`) and `UnitInterval.rightChart` (`1 − t` on `(0, 1]`),
  both onto `[0, 1)`; their transition maps are `v ↦ 1 − v`, which is `C^∞` and hence sc-smooth
  (`UnitInterval.leftChart_compatible_rightChart`).
* **`Polyfold.unitIntervalPolyfold`**: `unitInterval = [0, 1]` with the atlas of these two charts;
  `unitIntervalPolyfold_isTame` (its charts have the identity retraction, which is tame);
  `unitIntervalPolyfold_degIndex` (`d(t) = 1` at `t = 0, 1` and `0` inside: the boundary is
  `{0, 1}`).
* `isScSmoothMap_toUnitInterval`: a `C^∞` map `g : ℝⁿ → ℝ` with values in `[0, 1]` is an
  sc-smooth map `ℝⁿ → [0, 1]`; `isScSmoothMap_unitInterval_val`: the inclusion `[0, 1] → ℝ` is
  sc-smooth.
* `isScSmoothMap_sinSqInterval`, `sinSqInterval_surjective`: `s ↦ sin² s` is an sc-smooth map of
  `ℝ` **onto** `[0, 1]`; `MPolyfold.IsScSmoothMap.exists_rn_reparam`: **every sc-smooth path
  `φ : [0, 1] → X` is `ψ ∘ h` for an sc-smooth path `ψ = φ ∘ h : ℝ → X` and a surjection `h`**,
  so results about sc-smooth paths on `ℝ` with conclusions about the values `φ(t)` transfer to
  `[0, 1]`.
* `MPolyfold.IsScSmoothMap.restrictUnitInterval`: the restriction of an sc-smooth `φ : ℝ → X` to
  `[0, 1]` is an sc-smooth path `[0, 1] → X`; this is the reading of decision D2 (Findings,
  Chapter 6), so every path of that reading is a path in the present sense.

## What the text leaves implicit, and the choices made

* `ℝ` is modelled as `ℝ¹ = Fin 1 → ℝ` with the constant sc-structure (`rnSc 1`), as in
  `rnPolyfold 1`, so that the representatives of maps `ℝ → [0, 1]` are maps `ℝ¹ → ℝ¹` and the
  finite-dimensional criterion "sc-smooth = `C^∞`" (`isScSmooth_iff_contDiffOn_const`) applies
  directly.
* The two charts share one local model `([0, 1), [0, ∞), ℝ¹)`; at `0` and at `1` a chart point
  lies on the boundary `{0}` of the partial quadrant.
* The reduction of `[0, 1]`-paths to `ℝ`-paths uses one surjection `sin² : ℝ → [0, 1]` rather than
  local reparametrizations onto neighbourhoods of each `t₀` (such as `t₀ + ε tanh s`, or
  `ε s²/(1 + s²)` at `t₀ = 0`); the connectedness argument is then the one already in the
  `ℝ`-path results.
-/

open Set Function Filter Topology
open scoped ContDiff

noncomputable section

namespace Polyfold

/-! ### General: `C^∞` maps between retracts in finite dimensions -/

section FiniteDim

variable {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V'] [FiniteDimensional ℝ V']

/-- **A `C^∞` map is sc-smooth between retracts in finite dimensions**: if `g : V → V'` is `C^∞`
and maps the retract `O` into `O'`, it is sc-smooth from `(O, C, V)` to `(O', C', V')` (constant
sc-structures).  For a retraction `r` onto `O`, `g ∘ r` is `C^∞` on the domain of `r`
(`isScSmooth_iff_contDiffOn_const`). -/
theorem isScSmoothRetractMap_const_of_contDiff_of_mapsTo {C O : Set V} {C' O' : Set V'}
    (_hO : IsScRetract (ScBanach.const V) C O) {g : V → V'} (hg : ContDiff ℝ ∞ g)
    (hmaps : MapsTo g O O') :
    IsScSmoothRetractMap (ScBanach.const V) C O (ScBanach.const V') C' O' g := by
  refine ⟨hmaps, fun R _ => ?_⟩
  have hR : ContDiffOn ℝ ∞ (R : V → V) R.U :=
    (isScSmooth_iff_contDiffOn_const (W := V) R.isScDomain _).1 R.isScSmooth
  exact (isScSmooth_iff_contDiffOn_const (W := V') R.isScDomain _).2 (hg.comp_contDiffOn hR)

end FiniteDim

namespace UnitInterval

/-! ### The local model `([0, 1), [0, ∞), ℝ¹)` -/

/-- The half-line `[0, ∞)` in `ℝ¹`. -/
def halfC : Set (Fin 1 → ℝ) := {v | ∀ i, 0 ≤ v i}

/-- `[0, 1)` in `ℝ¹`. -/
def modelO : Set (Fin 1 → ℝ) := {v | v 0 < 1} ∩ halfC

lemma mem_modelO {v : Fin 1 → ℝ} : v ∈ modelO ↔ 0 ≤ v 0 ∧ v 0 < 1 :=
  ⟨fun h => ⟨h.2 0, h.1⟩, fun h => ⟨h.2, fun i => by rw [Fin.fin_one_eq_zero i]; exact h.1⟩⟩

/-- `ℝ¹ ≅ ℝ¹ ⊕ ℝ⁰` with the constant structures. -/
def quadIso : ScIso (rnSc 1) ((ScBanach.const (Fin 1 → ℝ)).prod (ScBanach.const (Fin 0 → ℝ))) where
  lvl _ := (ContinuousLinearEquiv.prodUnique ℝ (Fin 1 → ℝ) (Fin 0 → ℝ)).symm
  incl_comm _ _ := Prod.ext rfl (funext fun i => i.elim0)

/-- `[0, ∞)` is a partial quadrant of `ℝ¹` (2021 Definition 1.1.12, preprint 1.11). -/
theorem isPartialQuadrant_halfC : IsPartialQuadrant (rnSc 1) halfC :=
  ⟨1, ScBanach.const (Fin 0 → ℝ), quadIso, by ext v; rfl⟩

/-- `[0, 1)` is relatively open in `[0, ∞)`. -/
theorem isRelOpen_modelO : IsRelOpenInQuadrant (rnSc 1) halfC modelO :=
  ⟨isPartialQuadrant_halfC, {v | v 0 < 1}, isOpen_lt (continuous_apply 0) continuous_const, rfl⟩

/-- The local model `([0, 1), [0, ∞), ℝ¹)` (identity retraction). -/
def model : LocalModel := LocalModel.ofRelOpen isRelOpen_modelO

@[simp] lemma model_E : model.E = rnSc 1 := rfl
@[simp] lemma model_C : model.C = halfC := rfl
@[simp] lemma model_O : model.O = modelO := rfl

/-! ### The two charts -/

/-- The point `projIcc (v 0)` of `[0, 1]` is `v 0` when `v ∈ [0, 1)`. -/
lemma projIcc_val_of_mem {v : Fin 1 → ℝ} (hv : v ∈ modelO) :
    ((projIcc (0 : ℝ) 1 zero_le_one (v 0) : unitInterval) : ℝ) = v 0 := by
  rw [mem_modelO] at hv
  rw [projIcc_of_mem _ ⟨hv.1, hv.2.le⟩]

lemma projIcc_one_sub_val_of_mem {v : Fin 1 → ℝ} (hv : v ∈ modelO) :
    ((projIcc (0 : ℝ) 1 zero_le_one (1 - v 0) : unitInterval) : ℝ) = 1 - v 0 := by
  rw [mem_modelO] at hv
  rw [projIcc_of_mem _ ⟨by linarith, by linarith⟩]

lemma eq_const_zero (v : Fin 1 → ℝ) : (fun _ : Fin 1 => v 0) = v :=
  funext fun i => by rw [Fin.fin_one_eq_zero i]

/-- **The chart `t` on `[0, 1)`.** -/
def leftChart : MChart unitInterval where
  model := model
  toPartialEquiv :=
    { toFun := fun t _ => (t : ℝ)
      invFun := fun v => projIcc (0 : ℝ) 1 zero_le_one (v 0)
      source := {t | (t : ℝ) < 1}
      target := modelO
      map_source' := fun t ht => mem_modelO.2 ⟨t.2.1, ht⟩
      map_target' := fun v hv => by
        change ((projIcc (0 : ℝ) 1 zero_le_one (v 0) : unitInterval) : ℝ) < 1
        rw [projIcc_val_of_mem hv]; exact (mem_modelO.1 hv).2
      left_inv' := fun t _ => projIcc_val zero_le_one t
      right_inv' := fun v hv => by
        change (fun _ : Fin 1 => ((projIcc (0 : ℝ) 1 zero_le_one (v 0) : unitInterval) : ℝ)) = v
        rw [projIcc_val_of_mem hv]; exact eq_const_zero v }
  isOpen_source := isOpen_lt continuous_subtype_val continuous_const
  target_eq := rfl
  continuousOn_toFun := (continuous_pi fun _ => continuous_subtype_val).continuousOn
  continuousOn_invFun :=
    ((continuous_projIcc (a := (0 : ℝ)) (b := 1) (h := zero_le_one)).comp
      (continuous_apply (0 : Fin 1))).continuousOn

/-- **The chart `1 − t` on `(0, 1]`.** -/
def rightChart : MChart unitInterval where
  model := model
  toPartialEquiv :=
    { toFun := fun t _ => 1 - (t : ℝ)
      invFun := fun v => projIcc (0 : ℝ) 1 zero_le_one (1 - v 0)
      source := {t | 0 < (t : ℝ)}
      target := modelO
      map_source' := fun t ht => mem_modelO.2 ⟨by linarith [t.2.2], by linarith [ht.out]⟩
      map_target' := fun v hv => by
        change 0 < ((projIcc (0 : ℝ) 1 zero_le_one (1 - v 0) : unitInterval) : ℝ)
        rw [projIcc_one_sub_val_of_mem hv]; linarith [(mem_modelO.1 hv).2]
      left_inv' := fun t _ => by
        change projIcc (0 : ℝ) 1 zero_le_one (1 - (1 - (t : ℝ))) = t
        rw [sub_sub_cancel, projIcc_val]
      right_inv' := fun v hv => by
        change (fun _ : Fin 1 =>
          1 - ((projIcc (0 : ℝ) 1 zero_le_one (1 - v 0) : unitInterval) : ℝ)) = v
        rw [projIcc_one_sub_val_of_mem hv, sub_sub_cancel]; exact eq_const_zero v }
  isOpen_source := isOpen_lt continuous_const continuous_subtype_val
  target_eq := rfl
  continuousOn_toFun :=
    (continuous_pi fun _ => continuous_const.sub continuous_subtype_val).continuousOn
  continuousOn_invFun :=
    ((continuous_projIcc (a := (0 : ℝ)) (b := 1) (h := zero_le_one)).comp
      (continuous_const.sub (continuous_apply (0 : Fin 1)))).continuousOn

lemma leftChart_apply (t : unitInterval) :
    @Eq (Fin 1 → ℝ) (leftChart t) (fun _ => (t : ℝ)) := rfl
lemma rightChart_apply (t : unitInterval) :
    @Eq (Fin 1 → ℝ) (rightChart t) (fun _ => 1 - (t : ℝ)) := rfl
lemma leftChart_source : leftChart.source = {t : unitInterval | (t : ℝ) < 1} := rfl
lemma rightChart_source : rightChart.source = {t : unitInterval | 0 < (t : ℝ)} := rfl

/-- The flip `v ↦ 1 − v` of `ℝ¹`. -/
def flip (v : Fin 1 → ℝ) : Fin 1 → ℝ := fun _ => 1 - v 0

lemma contDiff_flip : ContDiff ℝ ∞ flip :=
  contDiff_pi.2 fun _ => contDiff_const.sub (contDiff_apply ℝ ℝ (0 : Fin 1))

/-- Both transition maps are the flip on the overlap. -/
lemma leftChart_transition_eqOn : EqOn (leftChart.transition rightChart) flip modelO := by
  intro v hv
  change (fun _ : Fin 1 => 1 - ((projIcc (0 : ℝ) 1 zero_le_one (v 0) : unitInterval) : ℝ)) = flip v
  rw [projIcc_val_of_mem hv]; rfl

lemma rightChart_transition_eqOn : EqOn (rightChart.transition leftChart) flip modelO := by
  intro v hv
  change (fun _ : Fin 1 => ((projIcc (0 : ℝ) 1 zero_le_one (1 - v 0) : unitInterval) : ℝ)) = flip v
  rw [projIcc_one_sub_val_of_mem hv]; rfl

/-- **The two charts are sc-smoothly compatible**: the transition maps are the flip `v ↦ 1 − v`,
which is `C^∞`. -/
theorem leftChart_compatible_rightChart : leftChart.Compatible rightChart := by
  refine ⟨?_, ?_⟩
  · have hsub : leftChart.overlap rightChart ⊆ modelO := leftChart.overlap_subset rightChart
    refine (isScSmoothRetractMap_const_of_contDiff_of_mapsTo (V := Fin 1 → ℝ) (V' := Fin 1 → ℝ)
      (leftChart.isScRetract_overlap rightChart) contDiff_flip ?_).congr ?_
    · intro v hv
      rw [← leftChart_transition_eqOn (hsub hv)]
      exact leftChart.transition_mapsTo rightChart hv
    · exact fun v hv => (leftChart_transition_eqOn (hsub hv)).symm
  · have hsub : rightChart.overlap leftChart ⊆ modelO := rightChart.overlap_subset leftChart
    refine (isScSmoothRetractMap_const_of_contDiff_of_mapsTo (V := Fin 1 → ℝ) (V' := Fin 1 → ℝ)
      (rightChart.isScRetract_overlap leftChart) contDiff_flip ?_).congr ?_
    · intro v hv
      rw [← rightChart_transition_eqOn (hsub hv)]
      exact rightChart.transition_mapsTo leftChart hv
    · exact fun v hv => (rightChart_transition_eqOn (hsub hv)).symm

end UnitInterval

open UnitInterval

/-! ### The M-polyfold `[0, 1]` -/

/-- **`[0, 1]` as an M-polyfold with boundary** (2021 Definition 2.3.4, preprint 2.13; the domain
of the paths of 2021 Proposition 6.2.2 and §6.6): the atlas of the chart `t` on `[0, 1)` and the
chart `1 − t` on `(0, 1]`, both onto `[0, 1) ⊆ [0, ∞)` with the identity retraction. -/
def unitIntervalPolyfold : MPolyfold unitInterval where
  atlas :=
    { charts := {leftChart, rightChart}
      compatible := by
        rintro φ (rfl | rfl) ψ (rfl | rfl)
        · exact MChart.compatible_self _
        · exact leftChart_compatible_rightChart
        · exact leftChart_compatible_rightChart.symm
        · exact MChart.compatible_self _
      cover := fun t => by
        by_cases ht : (t : ℝ) < 1
        · exact ⟨leftChart, Or.inl rfl, ht⟩
        · exact ⟨rightChart, Or.inr rfl, show (0 : ℝ) < t by linarith⟩ }

namespace UnitInterval

lemma isChart_leftChart : unitIntervalPolyfold.IsChart leftChart :=
  unitIntervalPolyfold.isChart_of_mem (Or.inl rfl)

lemma isChart_rightChart : unitIntervalPolyfold.IsChart rightChart :=
  unitIntervalPolyfold.isChart_of_mem (Or.inr rfl)

/-- Every point of `[0, 1]` lies in one of the two charts. -/
lemma mem_leftChart_or_rightChart (t : unitInterval) :
    t ∈ leftChart.source ∨ t ∈ rightChart.source := by
  by_cases ht : (t : ℝ) < 1
  · exact Or.inl ht
  · exact Or.inr (show (0 : ℝ) < t by linarith)

/-- The model `([0, 1), [0, ∞), ℝ¹)` is a tame retract (the identity retraction is tame). -/
lemma isTameRetract_model : IsTameRetract (rnSc 1) halfC modelO :=
  ⟨ScRetraction.id isRelOpen_modelO, image_id _, ScRetraction.id_isTame isRelOpen_modelO⟩

/-- The degeneracy index in either chart: `1` at a chart point `0`, `0` elsewhere. -/
lemma degIndex_model {v : Fin 1 → ℝ} (hv : v ∈ halfC) :
    Polyfold.degIndex (rnSc 1) halfC v = if v 0 = 0 then 1 else 0 := by
  rw [Polyfold.degIndex_eq quadIso (by ext; rfl) hv]
  change (Finset.univ.filter fun i : Fin 1 => v i = 0).card = _
  split_ifs with h
  · rw [Finset.card_eq_one]
    exact ⟨0, Finset.ext fun i => by simp [Fin.fin_one_eq_zero i, h]⟩
  · rw [Finset.card_eq_zero]
    exact Finset.ext fun i => by simp [Fin.fin_one_eq_zero i, h]

end UnitInterval

/-- `[0, 1]` is a **tame** M-polyfold (2021 Definition 2.5.7, preprint 2.37). -/
theorem unitIntervalPolyfold_isTame : unitIntervalPolyfold.IsTame := by
  refine MPolyfold.isTame_of_forall_exists_chart _ fun t => ?_
  rcases mem_leftChart_or_rightChart t with ht | ht
  · exact ⟨leftChart, isChart_leftChart, ht, isTameRetract_model⟩
  · exact ⟨rightChart, isChart_rightChart, ht, isTameRetract_model⟩

/-- **The boundary of `[0, 1]` is `{0, 1}`**: the degeneracy index (2021 Definition 2.4.1, preprint
2.22) is `1` at the end points and `0` in the interior. -/
theorem unitIntervalPolyfold_degIndex (t : unitInterval) :
    unitIntervalPolyfold.degIndex t = if (t : ℝ) = 0 ∨ (t : ℝ) = 1 then 1 else 0 := by
  rcases mem_leftChart_or_rightChart t with ht | ht
  · rw [unitIntervalPolyfold.degIndex_eq_chartDegIndex_of_isTameRetract isChart_leftChart
      isTameRetract_model ht]
    change Polyfold.degIndex (rnSc 1) halfC (fun _ => (t : ℝ)) = _
    rw [degIndex_model (fun _ => t.2.1)]
    have h1 : (t : ℝ) ≠ 1 := ne_of_lt ht
    simp only [h1, or_false]
  · rw [unitIntervalPolyfold.degIndex_eq_chartDegIndex_of_isTameRetract isChart_rightChart
      isTameRetract_model ht]
    change Polyfold.degIndex (rnSc 1) halfC (fun _ => 1 - (t : ℝ)) = _
    rw [degIndex_model (fun _ => by linarith [t.2.2])]
    have h0 : (t : ℝ) ≠ 0 := ne_of_gt ht
    have h : (1 - (t : ℝ) = 0) ↔ ((t : ℝ) = 1) := sub_eq_zero.trans eq_comm
    simp only [h0, false_or, h]

/-! ### Sc-smooth maps into and out of `[0, 1]` -/

/-- **A `C^∞` map `g : ℝⁿ → ℝ` with values in `[0, 1]` is an sc-smooth map `ℝⁿ → [0, 1]`**: in the
charts `rnChart n 0` and `t` (where `g < 1`) or `1 − t` (where `g > 0`) its representatives are
`g` and `1 − g`. -/
theorem isScSmoothMap_toUnitInterval {n : ℕ} {g : (Fin n → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g)
    (h01 : ∀ r, g r ∈ Icc (0 : ℝ) 1) :
    (rnPolyfold n).IsScSmoothMap unitIntervalPolyfold fun r => (⟨g r, h01 r⟩ : unitInterval) := by
  have hfc : Continuous fun r => (⟨g r, h01 r⟩ : unitInterval) := hg.continuous.subtype_mk h01
  have hg' : ContDiff ℝ ∞ fun r : Fin n → ℝ => g (r + 0) := hg.comp (contDiff_id.add contDiff_const)
  refine MPolyfold.IsScSmoothOn.of_exists_charts isOpen_univ hfc.continuousOn fun x _ => ?_
  by_cases hx : g x < 1
  · have hV : IsOpen {r | g r < 1} := isOpen_lt hg.continuous continuous_const
    refine ⟨rnChart n 0, leftChart, {r | g r < 1}, isChart_rnChart 0, isChart_leftChart, hV, hx,
      fun _ _ => ⟨mem_univ _, mem_univ _⟩, fun _ hr => hr, ?_⟩
    refine isScSmoothRetractMap_const_of_contDiff_of_mapsTo (V := Fin n → ℝ) (V' := Fin 1 → ℝ)
      (g := fun r _ => g (r + 0)) ((rnChart n 0).isScRetract_image (subset_univ _) hV)
      (contDiff_pi.2 fun _ => hg') ?_
    rintro _ ⟨r, hr, rfl⟩
    change (fun _ : Fin 1 => g (r - 0 + 0)) ∈ modelO
    rw [sub_add_cancel]
    exact mem_modelO.2 ⟨(h01 r).1, hr⟩
  · have hV : IsOpen {r | 0 < g r} := isOpen_lt continuous_const hg.continuous
    refine ⟨rnChart n 0, rightChart, {r | 0 < g r}, isChart_rnChart 0, isChart_rightChart, hV,
      show 0 < g x by linarith, fun _ _ => ⟨mem_univ _, mem_univ _⟩, fun _ hr => hr, ?_⟩
    refine isScSmoothRetractMap_const_of_contDiff_of_mapsTo (V := Fin n → ℝ) (V' := Fin 1 → ℝ)
      (g := fun r _ => 1 - g (r + 0)) ((rnChart n 0).isScRetract_image (subset_univ _) hV)
      (contDiff_pi.2 fun _ => contDiff_const.sub hg') ?_
    rintro _ ⟨r, hr, rfl⟩
    change (fun _ : Fin 1 => 1 - g (r - 0 + 0)) ∈ modelO
    rw [sub_add_cancel]
    exact mem_modelO.2 ⟨by linarith [(h01 r).2], by linarith [hr.out]⟩

/-- **The inclusion `[0, 1] → ℝ` is sc-smooth**: its representatives in the charts `t` and `1 − t`
are `v ↦ v` and `v ↦ 1 − v` on `[0, 1)`. -/
theorem isScSmoothMap_unitInterval_val :
    unitIntervalPolyfold.IsScSmoothMap (rnPolyfold 1) fun t _ => (t : ℝ) := by
  refine MPolyfold.IsScSmoothOn.of_exists_charts isOpen_univ
    (continuous_pi fun _ => continuous_subtype_val).continuousOn fun t _ => ?_
  rcases mem_leftChart_or_rightChart t with ht | ht
  · refine ⟨leftChart, rnChart 1 0, leftChart.source, isChart_leftChart, isChart_rnChart 0,
      leftChart.isOpen_source, ht, fun _ hs => ⟨mem_univ _, hs⟩, fun _ _ => mem_univ _, ?_⟩
    rw [leftChart.image_source]
    refine (isScSmoothRetractMap_const_of_contDiff_of_mapsTo (V := Fin 1 → ℝ) (V' := Fin 1 → ℝ)
      leftChart.model.isScRetract contDiff_id (mapsTo_univ _ _)).congr ?_
    intro (v : Fin 1 → ℝ) hv
    change v = (fun _ : Fin 1 => ((projIcc (0 : ℝ) 1 zero_le_one (v 0) : unitInterval) : ℝ)) - 0
    rw [projIcc_val_of_mem hv, sub_zero]
    exact (eq_const_zero v).symm
  · refine ⟨rightChart, rnChart 1 0, rightChart.source, isChart_rightChart, isChart_rnChart 0,
      rightChart.isOpen_source, ht, fun _ hs => ⟨mem_univ _, hs⟩, fun _ _ => mem_univ _, ?_⟩
    rw [rightChart.image_source]
    refine (isScSmoothRetractMap_const_of_contDiff_of_mapsTo (V := Fin 1 → ℝ) (V' := Fin 1 → ℝ)
      rightChart.model.isScRetract contDiff_flip (mapsTo_univ _ _)).congr ?_
    intro (v : Fin 1 → ℝ) hv
    change flip v =
      (fun _ : Fin 1 => ((projIcc (0 : ℝ) 1 zero_le_one (1 - v 0) : unitInterval) : ℝ)) - 0
    rw [projIcc_one_sub_val_of_mem hv, sub_zero]
    rfl

/-- `s ↦ sin² s`, a `C^∞` map of `ℝ` **onto** `[0, 1]`. -/
def sinSqInterval (r : Fin 1 → ℝ) : unitInterval :=
  ⟨Real.sin (r 0) ^ 2, sq_nonneg _, Real.sin_sq_le_one _⟩

theorem isScSmoothMap_sinSqInterval :
    (rnPolyfold 1).IsScSmoothMap unitIntervalPolyfold sinSqInterval :=
  isScSmoothMap_toUnitInterval ((Real.contDiff_sin.comp (contDiff_apply ℝ ℝ (0 : Fin 1))).pow 2) _

theorem sinSqInterval_surjective : Surjective sinSqInterval := by
  intro t
  have h0 : 0 ≤ Real.sqrt (t : ℝ) := Real.sqrt_nonneg _
  have h1 : Real.sqrt (t : ℝ) ≤ 1 := Real.sqrt_le_one.mpr t.2.2
  refine ⟨fun _ => Real.arcsin (Real.sqrt t), Subtype.ext ?_⟩
  change Real.sin (Real.arcsin (Real.sqrt t)) ^ 2 = t
  rw [Real.sin_arcsin (by linarith) h1, Real.sq_sqrt t.2.1]

section Paths

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

/-- **Every sc-smooth path on `[0, 1]` is a reparametrized sc-smooth path on `ℝ`**: for an
sc-smooth `φ : [0, 1] → X` there is a surjection `h : ℝ → [0, 1]` (namely `sin²`) with
`φ ∘ h : ℝ → X` sc-smooth (2021 Definition 2.3.8, preprint 2.14, and the chain rule,
`IsScSmoothMap.comp`). -/
theorem MPolyfold.IsScSmoothMap.exists_rn_reparam {φ : unitInterval → X}
    (hφ : unitIntervalPolyfold.IsScSmoothMap PX φ) :
    ∃ h : (Fin 1 → ℝ) → unitInterval, Surjective h ∧ (rnPolyfold 1).IsScSmoothMap PX (φ ∘ h) :=
  ⟨sinSqInterval, sinSqInterval_surjective, hφ.comp isScSmoothMap_sinSqInterval⟩

/-- **The paths of decision D2 are paths on `[0, 1]`**: the restriction of an sc-smooth
`φ : ℝ → X` to `[0, 1]` is sc-smooth on the M-polyfold `[0, 1]`. -/
theorem MPolyfold.IsScSmoothMap.restrictUnitInterval {φ : (Fin 1 → ℝ) → X}
    (hφ : (rnPolyfold 1).IsScSmoothMap PX φ) :
    unitIntervalPolyfold.IsScSmoothMap PX fun t => φ fun _ => (t : ℝ) :=
  hφ.comp isScSmoothMap_unitInterval_val

end Paths

end Polyfold
