import Polyfold.Chapter6.GapP1_CubeSections

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, Lemmas 6.6.4–6.6.5
(pp. 264–265; preprint Lemmas 6.29–6.30) for families on `[0, 1]ⁿ`: **the charts of `[0, 1]ⁿ`
centred at every point**, the first input of the pull-back of an sc-Fredholm section to
`[0, 1]ⁿ × X` (gap G.65 (a), step 1).

# Centred charts of `[0, 1]ⁿ`

## What is formalized

* `UnitCube.cChart q`: the corner chart `chart (corner q)` re-centred at `q` (`MChart.recentre`),
  `v = (fl (bᵢ) (q'ᵢ) − fl (bᵢ) (qᵢ))ᵢ` near `q`.  It is a chart of `cubePolyfold n`
  (`isChart_cChart`), contains `q` (`mem_cChart`) and sends it to `0` (`cChart_self`).  Its partial
  quadrant is the mixed quadrant `C_{e}` of the coordinates with `qᵢ ∈ {0, 1}` (Definition 2.5.1,
  `partialQuadrantAtWith`), and its model is **relatively open** in it (`cChart_relOpen`), so the
  identity is a (tame) retraction of the model (`cRetr`, `cRetr_retract`, `cRetr_isTame`).
* The levels of `[0, 1]ⁿ × X`: `prod_cube_mem_levelSet_iff`, `prod_cube_mem_smoothSet_iff`
  (`[0, 1]ⁿ` has the constant sc-structure, so `(q, x)` is on level `m` iff `x` is).
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u

namespace UnitCube

variable {n : ℕ}

/-- The presentation `[0, ∞)ⁿ = T⁻¹([0, ∞)ⁿ ⊕ ℝ⁰)` of the corner charts' quadrant. -/
lemma chart_model_C_eq (b : Fin n → Bool) :
    (chart b).model.C = (quadIso n) 0 ⁻¹' quadrant n (ScBanach.const (Fin 0 → ℝ)) 0 := by
  ext v; rfl

/-- Every point of `ℝⁿ` (constant structure) is smooth. -/
lemma mem_smooth_rnSc (e : Fin n → ℝ) : e ∈ (rnSc n).smooth :=
  (ScScale.mem_smooth_iff _).2 fun m => ⟨e, ScBanach.const_toBase _ m e⟩

/-- **The chart of `[0, 1]ⁿ` centred at `q`**: the corner chart of `q` re-centred at its value
`fl (b) (q)` (`MChart.recentre`); on its domain `v = (fl (bᵢ) (q'ᵢ) − fl (bᵢ) (qᵢ))ᵢ`. -/
def cChart (q : Fin n → unitInterval) : MChart (Fin n → unitInterval) :=
  (chart (corner q)).recentre (quadIso n) (chart_model_C_eq (corner q)) (chart (corner q) q)
    (mem_smooth_rnSc _)

theorem isChart_cChart (q : Fin n → unitInterval) : (cubePolyfold n).IsChart (cChart q) :=
  MChart.recentre_isChart _ _ _ _ _ (isChart_chart _)

theorem mem_cChart (q : Fin n → unitInterval) : q ∈ (cChart q).source :=
  MChart.mem_recentre_source _ _ _ _ _ (mem_chart_corner q) rfl

theorem cChart_self (q : Fin n → unitInterval) : cChart q q = 0 :=
  MChart.recentre_apply_self _ _ _ _ _ rfl

/-- The model of the centred chart is relatively open in its partial quadrant `C_e`. -/
theorem cChart_relOpen (q : Fin n → unitInterval) :
    IsRelOpenInQuadrant (rnSc n) (cChart q).model.C (cChart q).model.O := by
  set e : Fin n → ℝ := chart (corner q) q
  have hO : (cChart q).model.O =
      (fun v => v - e) '' (modelO n ∩ recentreNbhd (quadIso n) e) :=
    MChart.recentre_model_O _ _ _ _ _
  have himg : (fun v : Fin n → ℝ => v - e) '' (modelO n ∩ recentreNbhd (quadIso n) e) =
      (fun u => u + e) ⁻¹' (modelO n ∩ recentreNbhd (quadIso n) e) := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      change w - e + e ∈ modelO n ∩ recentreNbhd (quadIso n) e
      rw [sub_add_cancel]; exact hw
    · intro hv
      exact ⟨v + e, hv, add_sub_cancel_right v e⟩
  rw [hO, himg]
  exact relOpen_translate (chart_model_C_eq (corner q))
    ((isRelOpen_modelO n).inter_isOpen (isOpen_recentreNbhd (quadIso n) e)) inter_subset_right

/-- The identity retraction of the model of the centred chart. -/
def cRetr (q : Fin n → unitInterval) : ScRetraction (cChart q).model.E (cChart q).model.C :=
  ScRetraction.id (cChart_relOpen q)

lemma cRetr_retract (q : Fin n → unitInterval) : (cRetr q).retract = (cChart q).model.O := by
  change _root_.id '' (cChart q).model.O = _
  rw [image_id]

lemma cRetr_isTame (q : Fin n → unitInterval) : (cRetr q).IsTame :=
  ScRetraction.id_isTame (cChart_relOpen q)

lemma zero_mem_cChart_O (q : Fin n → unitInterval) :
    (0 : (cChart q).model.E 0) ∈ (cChart q).model.O := by
  have h := (cChart q).mapsTo_model q (mem_cChart q)
  rwa [cChart_self q] at h

end UnitCube

/-! ### The levels of `[0, 1]ⁿ × X` -/

section Levels

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {PX : MPolyfold X}

open UnitCube in
/-- A point `(q, x)` of `[0, 1]ⁿ × X` is on level `m` if and only if `x` is (`[0, 1]ⁿ` has the
constant sc-structure). -/
lemma prod_cube_mem_levelSet_iff {m : ℕ} {z : (Fin n → unitInterval) × X} :
    z ∈ ((cubePolyfold n).prod PX).levelSet m ↔ z.2 ∈ PX.levelSet m := by
  obtain ⟨φ, hφ, hx⟩ := PX.exists_isChart_mem_source z.2
  have hχ : ((cubePolyfold n).prod PX).IsChart ((chart (corner z.1)).prod φ) :=
    MPolyfold.IsChart.prod (isChart_chart _) hφ
  rw [((cubePolyfold n).prod PX).mem_levelSet_iff hχ
    (show z ∈ ((chart (corner z.1)).prod φ).source from ⟨mem_chart_corner z.1, hx⟩),
    PX.mem_levelSet_iff hφ hx]
  have hb : ∀ y : ((chart (corner z.1)).prod φ).model.E m,
      ((chart (corner z.1)).prod φ).model.E.toBase m y =
        ((ScBanach.const (Fin n → ℝ)).toBase m y.1, φ.model.E.toBase m y.2) := fun y =>
    ScBanach.prod_toBase (ScBanach.const (Fin n → ℝ)) φ.model.E m y
  constructor
  · rintro ⟨y, hy⟩
    rw [hb] at hy
    exact ⟨y.2, congrArg Prod.snd hy⟩
  · rintro ⟨y, hy⟩
    refine ⟨((chart (corner z.1) z.1 : Fin n → ℝ), y), ?_⟩
    exact (hb _).trans (Prod.ext (ScBanach.const_toBase _ m _) hy)

/-- The smooth points of `[0, 1]ⁿ × X` are the `(q, x)` with `x` smooth. -/
lemma prod_cube_mem_smoothSet_iff {z : (Fin n → unitInterval) × X} :
    z ∈ ((cubePolyfold n).prod PX).smoothSet ↔ z.2 ∈ PX.smoothSet := by
  simp only [MPolyfold.smoothSet, mem_iInter, prod_cube_mem_levelSet_iff]

end Levels

end Polyfold
