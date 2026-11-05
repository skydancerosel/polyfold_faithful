import Polyfold.Chapter3.TameGerms
import Polyfold.Chapter2.FibredProduct

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, Definition 2.34
and Definition 2.50: **a retract carries non-tame retractions** — the local core of the remark
(Findings, Chapter 3 item 190) that "the base retraction of every compatible strong bundle chart is
tame" is false for every strong bundle over a nonempty base.

# Non-tame retractions onto a product with a point

## The text, paraphrased

(Definition 2.34) An sc-smooth retraction `r : U → U` of a relatively open subset `U` of a partial
quadrant `C` is tame if (1) `d_C(r(x)) = d_C(x)` for `x ∈ U` and (2) at the smooth points of
`O = r(U)` the tangent space has an sc-complement in `E_x`.  (Definition 2.50) Two strong bundle
charts are compatible if their transition maps are sc-smooth; nothing is required of the
retractions whose images the local models are.

## What is formalized

* `Polyfold.halfLineSc W`, `Polyfold.ScRetraction.halfLineConst W`: the constant retraction
  `(a, w) ↦ (1, 0)` of the partial quadrant `[0, ∞) ⊕ W` of `ℝ ⊕ W` onto the point `(1, 0)`
  (sc-smooth: the value is a smooth point), with retract `{(1, 0)}`
  (`ScRetraction.halfLineConst_retract`).
* `Polyfold.ScRetraction.halfLineConst_prod_not_isTame`: **for every sc-smooth retraction `r` of a
  nonempty `U`, the product `c × r` with the constant retraction is not tame**: its retract is
  `{(1, 0)} × r(U)` (`ScRetraction.prod_retract`), and at `((0, 0), u)`, `u ∈ r(U)`,
  `d(c × r((0, 0), u)) = d((1, 0), u) = d_C(u)` while `d((0, 0), u) = 1 + d_C(u)` (the degeneracy
  index is additive, `degIndex_prod`).

## What the text leaves implicit, and the choices made (the findings)

* This is the retraction-level half of the construction of Findings item 190.  The other half —
  that the strong bundle chart `(1, φ)` with base retraction `c × r` and `Φ' = (1, Φ)` is a strong
  bundle chart compatible with every chart `(φ, U, R, Φ)` is compatible with (its transitions are
  those of `(φ, U, R, Φ)` composed with affine maps) — is **not formalized** in general (it is
  sc-calculus for affine maps of the size of `Chapter4/Recentre.lean`); for the trivial bundle
  `ℝⁿ × ℝᵏ → ℝⁿ` it is `TameVacuityChart.lean` (`TrivialBundle.not_forall_isTame_of_isChart`).  The factor is `ℝ ⊕ W` with an arbitrary
  sc-Banach space `W` only so that the partial quadrant `[0, ∞) ⊕ W` is in the presented form
  `quadrant 1 W 0` of Definition 1.21; `W = ℝ⁰` would do.
-/

open Set Function

noncomputable section

namespace Polyfold

variable {E : ScBanach} {C : Set (E 0)}

/-- The sc-Banach space `ℝ ⊕ W` with the partial quadrant `[0, ∞) ⊕ W` (`quadrant 1 W 0`). -/
abbrev halfLineSc (W : ScBanach) : ScBanach := (ScBanach.const (Fin 1 → ℝ)).prod W

/-- `[0, ∞) ⊕ W` is relatively open in itself, a partial quadrant of `ℝ ⊕ W`. -/
lemma isRelOpenInQuadrant_quadrant_one (W : ScBanach) :
    IsRelOpenInQuadrant (halfLineSc W) (quadrant 1 W 0) (quadrant 1 W 0) :=
  ⟨⟨1, W, ScIso.refl _, by ext; rfl⟩, univ, isOpen_univ, (univ_inter _).symm⟩

/-- The point `(1, 0)` of `ℝ ⊕ W`. -/
def halfLineOne (W : ScBanach) : (halfLineSc W) 0 := ((fun _ => 1), 0)

lemma halfLineOne_mem_smooth (W : ScBanach) : halfLineOne W ∈ (halfLineSc W).smooth := by
  refine (halfLineSc W).mem_smooth_iff.2 fun m => ⟨((fun _ => 1), 0), ?_⟩
  rw [ScBanach.prod_toBase, ScBanach.const_toBase, map_zero]
  rfl

/-- **The constant retraction** `(a, w) ↦ (1, 0)` of `[0, ∞) ⊕ W` onto the point `(1, 0)`; it is
sc-smooth because `(1, 0)` is a smooth point. -/
def ScRetraction.halfLineConst (W : ScBanach) :
    ScRetraction (halfLineSc W) (quadrant 1 W 0) where
  U := quadrant 1 W 0
  toFun := fun _ => halfLineOne W
  relOpen := isRelOpenInQuadrant_quadrant_one W
  mapsTo := fun _ _ _ => zero_le_one
  isScSmooth := by
    have hk := halfLineOne_mem_smooth W
    refine IsScSmooth.of_contDiffOn_levels (isRelOpenInQuadrant_quadrant_one W).isScDomain
      (fun m _ _ => (halfLineSc W).mem_smooth_iff.1 hk m) fun m => ?_
    obtain ⟨y, hy⟩ := (halfLineSc W).mem_smooth_iff.1 hk m
    have : ∀ x ∈ (halfLineSc W).lvlSet (quadrant 1 W 0) m,
        levelMap (E := halfLineSc W) (F := halfLineSc W) (fun _ => halfLineOne W) m x = y :=
      fun x _ => levelMap_eq_of_toBase_eq hy
    exact contDiffOn_const.congr this
  idem := fun _ _ => rfl

/-- The retract of the constant retraction is the point `(1, 0)`. -/
lemma ScRetraction.halfLineConst_retract (W : ScBanach) :
    (ScRetraction.halfLineConst W).retract = {halfLineOne W} := by
  ext p
  constructor
  · rintro ⟨q, -, rfl⟩; rfl
  · rintro rfl
    exact ⟨0, fun _ => le_rfl, rfl⟩

/-- **A retract carries a non-tame retraction** (the local core of Findings, Chapter 3 item 190):
for every sc-smooth retraction `r` of a nonempty `U ⊆ C`, the product `c × r` of the constant
retraction `c` of `[0, ∞) ⊕ W` onto `(1, 0)` with `r` — a retraction of `([0, ∞) ⊕ W) × U` onto
`{(1, 0)} × r(U)` (`halfLineConst_retract`, `ScRetraction.prod_retract`) — is not tame (Definition
2.34 (1) fails): at `((0, 0), u)` with `u ∈ r(U)` the degeneracy index is `1 + d_C(u)`, at its
image `((1, 0), u)` it is `d_C(u)` (`degIndex_prod`, `degIndex_quadrant`). -/
theorem ScRetraction.halfLineConst_prod_not_isTame (W : ScBanach) (R : ScRetraction E C)
    (hne : R.U.Nonempty) : ¬ ((ScRetraction.halfLineConst W).prod R).IsTame := by
  intro h
  obtain ⟨u₀, hu₀⟩ := hne
  have hu : R u₀ ∈ R.U := R.mapsTo hu₀
  have hRu : R (R u₀) = R u₀ := R.idem u₀ hu₀
  have hC₁ := (isRelOpenInQuadrant_quadrant_one W).isPartialQuadrant
  have hC := R.relOpen.isPartialQuadrant
  obtain ⟨n, W', T, hT⟩ := hC₁.prod hC
  have hp : ((0 : (halfLineSc W) 0), R u₀) ∈ ((ScRetraction.halfLineConst W).prod R).U :=
    ⟨fun _ => le_rfl, hu⟩
  have hdeg := (h n W' T hT).degIndex_apply _ hp
  rw [ScRetraction.prod_apply] at hdeg
  change degIndex ((halfLineSc W).prod E) (quadrant 1 W 0 ×ˢ C)
      ((halfLineOne W, R (R u₀)) : ((halfLineSc W).prod E) 0) =
    degIndex ((halfLineSc W).prod E) (quadrant 1 W 0 ×ˢ C)
      (((0 : (halfLineSc W) 0), R u₀) : ((halfLineSc W).prod E) 0) at hdeg
  have huC : R u₀ ∈ C := R.U_subset_C hu
  have h1 : halfLineOne W ∈ quadrant 1 W 0 := fun _ => zero_le_one
  have h0 : (0 : (halfLineSc W) 0) ∈ quadrant 1 W 0 := fun _ => le_rfl
  rw [hRu, degIndex_prod hC₁ hC h1 huC, degIndex_prod hC₁ hC h0 huC, degIndex_quadrant h1,
    degIndex_quadrant h0, quadrantDeg_zero] at hdeg
  have hq : quadrantDeg (halfLineOne W) = 0 := by
    simp [quadrantDeg, halfLineOne]
  omega

end Polyfold
