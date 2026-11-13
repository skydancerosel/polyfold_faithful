import Polyfold.Chapter3.QuadrantInverseSmooth

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §3.8.5: **Definition
3.8.14** (preprint 3.71), p. 164: maps of class `C^k` on relatively open subsets of partial
quadrants.

# Class `C^k` on partial quadrants, and its agreement with `ContDiffOn` and sc-smoothness

## The text, paraphrased

`f : U → ℝᵐ` on a relatively open `U ⊆ C` (`C ⊆ ℝⁿ` a partial quadrant) is of class `C¹` if at
every `x ∈ U` there is a bounded linear `Df(x)` with
`|f(x + h) − f(x) − Df(x)h| / |h| → 0` as `h → 0` with `x + h ∈ U`, and `x ↦ Df(x)` is continuous.
With the tangent map `Tf(x, h) = (f(x), Df(x)h)` on `TU = U ⊕ ℝⁿ`, relatively open in the partial
quadrant `C ⊕ ℝⁿ`, `f` is `C²` if `f` and `Tf` are `C¹`, and inductively `C^k` if `f` and `Tf` are
`C^{k−1}`; smooth if `C^k` for all `k`.

## What is formalized

* `Polyfold.IsClassC1On` (the text's `C¹`: a continuous family of one-sided derivatives),
  `Polyfold.bookTangentMap` (`Tf`), `Polyfold.IsClassCOn k` (the text's `C^k`, by its induction
  through `Tf`; `C⁰` is continuity), `Polyfold.IsClassSmoothOn`.
* `Polyfold.isClassC1On_iff_tendsto`: the derivative condition is the text's limit.
* **Agreement**: on every set with unique differentiability in a finite-dimensional space (in
  particular every relatively open subset of a partial quadrant), `IsClassCOn k U f ↔ ContDiffOn ℝ k
  f U` (`Polyfold.isClassCOn_iff_contDiffOn`) and smooth ↔ `C^∞`
  (`Polyfold.isClassSmoothOn_iff_contDiffOn`); for relatively open subsets of partial quadrants:
  `Polyfold.isClassCOn_iff_contDiffOn_of_isRelOpenInQuadrant`, and the text's `C¹` / smooth are
  sc¹ / sc-smooth (`Polyfold.isSc1_iff_isClassC1On`, `Polyfold.isScSmooth_iff_isClassSmoothOn`).
  So the project's use of `ContDiffOn` in §§3.8.5–3.8.6 is the text's notion.

`Tf` is built from `fderivWithin`; on a set with unique differentiability every derivative family
of the definition agrees with it on `U` (`Polyfold.IsClassC1On.eqOn_fderivWithin`), so this is the
text's `Tf`.
-/

open Set Filter Topology Function
open scoped ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace Polyfold

section Definition3814

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **Definition 3.8.14 (preprint 3.71), class `C¹`** (2021 p. 164): at every `x ∈ U` there is a
bounded linear `Df(x)` with `f(x + h) − f(x) − Df(x)h = o(|h|)` for `x + h ∈ U`, `h → 0`, and
`x ↦ Df(x)` is continuous on `U`. -/
def IsClassC1On (U : Set E) (f : E → F) : Prop :=
  ∃ Df : E → E →L[ℝ] F, (∀ x ∈ U, HasFDerivWithinAt f (Df x) U x) ∧ ContinuousOn Df U

/-- The derivative condition of Definition 3.8.14 is the text's limit
`|f(x + h) − f(x) − Df(x)h| / |h| → 0` as `x + h → x` within `U`. -/
theorem isClassC1On_iff_tendsto (U : Set E) (f : E → F) :
    IsClassC1On U f ↔ ∃ Df : E → E →L[ℝ] F,
      (∀ x ∈ U, Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - Df x (x' - x)‖) (𝓝[U] x) (𝓝 0)) ∧
        ContinuousOn Df U := by
  simp only [IsClassC1On, hasFDerivWithinAt_iff_tendsto]

/-- With unique differentiability the derivative family of Definition 3.8.14 is `fderivWithin`. -/
theorem IsClassC1On.eqOn_fderivWithin {U : Set E} {f : E → F} (hU : UniqueDiffOn ℝ U)
    {Df : E → E →L[ℝ] F} (hDf : ∀ x ∈ U, HasFDerivWithinAt f (Df x) U x) :
    EqOn Df (fderivWithin ℝ f U) U := fun x hx => ((hDf x hx).fderivWithin (hU x hx)).symm

/-- The tangent map `Tf(x, h) = (f(x), Df(x)h)` of Definition 3.8.14, on `TU = U × E`. -/
def bookTangentMap (U : Set E) (f : E → F) : E × E → F × F :=
  fun p => (f p.1, fderivWithin ℝ f U p.1 p.2)

/-- **Definition 3.8.14 (preprint 3.71), class `C^k`**: `C⁰` is continuity, `C¹` is
`IsClassC1On`, and `f` is `C^{k+2}` if `f` and `Tf` (on `TU = U × E`) are `C^{k+1}`. -/
def IsClassCOn : ℕ → {E F : Type} → [NormedAddCommGroup E] → [NormedSpace ℝ E] →
    [NormedAddCommGroup F] → [NormedSpace ℝ F] → Set E → (E → F) → Prop
  | 0, _, _, _, _, _, _, U, f => ContinuousOn f U
  | 1, _, _, _, _, _, _, U, f => IsClassC1On U f
  | k + 2, _, _, _, _, _, _, U, f =>
      IsClassCOn (k + 1) U f ∧ IsClassCOn (k + 1) (U ×ˢ (univ : Set _)) (bookTangentMap U f)

/-- **Definition 3.8.14, smooth**: of class `C^k` for every `k`. -/
def IsClassSmoothOn (U : Set E) (f : E → F) : Prop := ∀ k : ℕ, IsClassCOn k U f

theorem isClassCOn_zero {U : Set E} {f : E → F} : IsClassCOn 0 U f ↔ ContinuousOn f U := Iff.rfl

theorem isClassCOn_one {U : Set E} {f : E → F} : IsClassCOn 1 U f ↔ IsClassC1On U f := Iff.rfl

theorem isClassCOn_add_two {U : Set E} {f : E → F} {k : ℕ} :
    IsClassCOn (k + 2) U f ↔
      IsClassCOn (k + 1) U f ∧ IsClassCOn (k + 1) (U ×ˢ (univ : Set E)) (bookTangentMap U f) :=
  Iff.rfl

/-- `C¹` in the sense of Definition 3.8.14 is `ContDiffOn ℝ 1` on a set with unique
differentiability. -/
theorem isClassC1On_iff_contDiffOn {U : Set E} {f : E → F} (hU : UniqueDiffOn ℝ U) :
    IsClassC1On U f ↔ ContDiffOn ℝ 1 f U := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from (zero_add 1).symm, contDiffOn_succ_iff_fderivWithin hU]
  constructor
  · rintro ⟨Df, hDf, hc⟩
    refine ⟨fun x hx => (hDf x hx).differentiableWithinAt, fun h => absurd h (by simp), ?_⟩
    exact contDiffOn_zero.2 (hc.congr (IsClassC1On.eqOn_fderivWithin hU hDf).symm)
  · rintro ⟨hd, -, hc⟩
    exact ⟨fderivWithin ℝ f U, fun x hx => (hd x hx).hasFDerivWithinAt, contDiffOn_zero.1 hc⟩

/-- The tangent set `TU = U × E` has unique differentiability with `U`. -/
theorem uniqueDiffOn_tangentSet {U : Set E} (hU : UniqueDiffOn ℝ U) :
    UniqueDiffOn ℝ (U ×ˢ (univ : Set E)) := hU.prod uniqueDiffOn_univ

/-- The step of the induction: in finite dimensions, with unique differentiability,
`f` is `C^{k+2}` iff `f` and `Tf` are `C^{k+1}` (Mathlib's `ContDiffOn`). -/
theorem contDiffOn_add_two_iff_tangentMap [FiniteDimensional ℝ E] {U : Set E} {f : E → F}
    (hU : UniqueDiffOn ℝ U) (k : ℕ) :
    ContDiffOn ℝ (k + 2 : ℕ) f U ↔
      ContDiffOn ℝ (k + 1 : ℕ) f U ∧
        ContDiffOn ℝ (k + 1 : ℕ) (bookTangentMap U f) (U ×ˢ (univ : Set E)) := by
  constructor
  · intro hf
    have hf1 : ContDiffOn ℝ (k + 1 : ℕ) f U :=
      hf.of_le (by exact_mod_cast (by omega : k + 1 ≤ k + 2))
    have hD : ContDiffOn ℝ (k + 1 : ℕ) (fderivWithin ℝ f U) U :=
      hf.fderivWithin hU (by push_cast; exact le_rfl)
    refine ⟨hf1, ?_⟩
    have hfst : MapsTo Prod.fst (U ×ˢ (univ : Set E)) U := fun p hp => hp.1
    refine ContDiffOn.prodMk (hf1.comp contDiffOn_fst hfst) ?_
    exact (hD.comp contDiffOn_fst hfst).clm_apply contDiffOn_snd
  · rintro ⟨hf1, hT⟩
    rw [show ((k + 2 : ℕ) : WithTop ℕ∞) = ((k + 1 : ℕ) : WithTop ℕ∞) + 1 by push_cast; ring,
      contDiffOn_succ_iff_fderivWithin hU]
    refine ⟨hf1.differentiableOn (by exact_mod_cast (show k + 1 ≠ 0 by omega)),
      fun h => absurd h (by simp), ?_⟩
    rw [contDiffOn_clm_apply]
    intro v
    have hmap : MapsTo (fun x : E => (x, v)) U (U ×ˢ (univ : Set E)) :=
      fun x hx => ⟨hx, mem_univ _⟩
    have := (contDiff_snd.comp_contDiffOn (hT.comp (contDiffOn_id.prodMk contDiffOn_const) hmap))
    exact this

/-- **Agreement of Definition 3.8.14 with `ContDiffOn`**: on a set `U` with unique
differentiability in a finite-dimensional space (e.g. a relatively open subset of a partial
quadrant), `f` is of class `C^k` in the sense of the text iff `ContDiffOn ℝ k f U`. -/
theorem isClassCOn_iff_contDiffOn : ∀ (k : ℕ) {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} {f : E → F}, UniqueDiffOn ℝ U → (IsClassCOn k U f ↔ ContDiffOn ℝ k f U)
  | 0, _, _, _, _, _, _, _, _, _, _ => by
      rw [isClassCOn_zero]; exact_mod_cast contDiffOn_zero.symm
  | 1, _, _, _, _, _, _, _, _, _, hU => by
      rw [isClassCOn_one]; exact_mod_cast isClassC1On_iff_contDiffOn hU
  | k + 2, _, _, _, _, _, _, _, _, _, hU => by
      rw [isClassCOn_add_two, contDiffOn_add_two_iff_tangentMap hU,
        isClassCOn_iff_contDiffOn (k + 1) hU,
        isClassCOn_iff_contDiffOn (k + 1) (uniqueDiffOn_tangentSet hU)]

/-- Smooth in the sense of Definition 3.8.14 is `C^∞` (`ContDiffOn ℝ ∞`). -/
theorem isClassSmoothOn_iff_contDiffOn [FiniteDimensional ℝ E] {U : Set E} {f : E → F}
    (hU : UniqueDiffOn ℝ U) : IsClassSmoothOn U f ↔ ContDiffOn ℝ ∞ f U := by
  rw [contDiffOn_infty]
  exact forall_congr' fun k => isClassCOn_iff_contDiffOn k hU

end Definition3814

section Quadrants

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- **Definition 3.8.14 agrees with the project's `C^k`** on relatively open subsets of partial
quadrants (the setting of the text). -/
theorem isClassCOn_iff_contDiffOn_of_isRelOpenInQuadrant {C U : Set V}
    (hU : IsRelOpenInQuadrant (ScBanach.const V) C U) (k : ℕ) (f : V → W) :
    IsClassCOn k U f ↔ ContDiffOn ℝ k f U :=
  isClassCOn_iff_contDiffOn k hU.uniqueDiffOn_const

/-- The text's `C¹` (Definition 3.8.14) is sc¹ for the constant sc-structures. -/
theorem isSc1_iff_isClassC1On {C U : Set V} (hU : IsRelOpenInQuadrant (ScBanach.const V) C U)
    (f : (ScBanach.const V) 0 → (ScBanach.const W) 0) : IsSc1 U f ↔ IsClassC1On U f := by
  rw [isSc1_iff_contDiffOn_of_isRelOpenInQuadrant hU, isClassC1On_iff_contDiffOn
    hU.uniqueDiffOn_const]

/-- The text's smooth (Definition 3.8.14) is sc-smooth for the constant sc-structures. -/
theorem isScSmooth_iff_isClassSmoothOn {C U : Set V}
    (hU : IsRelOpenInQuadrant (ScBanach.const V) C U)
    (f : (ScBanach.const V) 0 → (ScBanach.const W) 0) : IsScSmooth U f ↔ IsClassSmoothOn U f := by
  rw [isScSmooth_iff_contDiffOn_of_isRelOpenInQuadrant hU, isClassSmoothOn_iff_contDiffOn
    hU.uniqueDiffOn_const]

end Quadrants

end Polyfold
