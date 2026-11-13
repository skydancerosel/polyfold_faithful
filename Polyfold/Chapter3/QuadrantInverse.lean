import Polyfold.Chapter3.QuadrantIFT

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, Appendix 3.8.4:
Theorem 3.8.15 (preprint 3.72) (the quadrant inverse function theorem) with Proposition 3.8.17 (preprint 3.73) and Lemmas 3.8.18–3.8.21 (preprint 3.74–3.77);
and the characterisation `d_C(x) = 0 ↔ x ∈ int C` of interior points (Definition 1.3.3 (preprint 1.23)).

# The inverse function theorem in partial quadrants

## The text, paraphrased

(Definition 3.8.14 (preprint 3.71)) `f : U → ℝᵐ` on a relatively open `U ⊆ C` is `C^1` if it has one-sided
derivatives `Df(x)` depending continuously on `x`; `C^k` if `f` and `Tf` are `C^{k−1}`.  (Theorem
3.72) Let `C ⊆ ℝⁿ` be a partial quadrant, `U ⊆ C` a relatively open neighbourhood of `0` and
`f : U → ℝⁿ` smooth with `f(U) ⊆ C`, (1) `f(0) = 0`, `Df(0)C = C`, (2) `d_C(x) = d_C(f(x))` on `U`.
Then `f` is a diffeomorphism between relatively open neighbourhoods `U'` and `V'` of `0` in `C`.
*Proof.*  `Df(0)` is an isomorphism (`ℝⁿ = C − C`), and `g = Df(0)⁻¹ ∘ f` satisfies (1), (2) with
`Dg(0) = 1`; Theorem 3.8.15 (preprint 3.72) follows from (Proposition 3.8.17 (preprint 3.73)): for `U` relatively open and convex,
`f : U → C` smooth with `|Df(x) − 1| ≤ 1/2` and (2), `V = f(U)` is relatively open in `C` and
`f : U → V` a diffeomorphism.  (Lemma 3.8.18 (preprint 3.74)) `|x − x'|/2 ≤ |f(x) − f(x')| ≤ 3|x − x'|/2`, so `f` is
injective; `V` is relatively open: for `y' = f(x')` and `B(x', 3r) ∩ C ⊆ U`, first the points with
`d_C = 0` of `B(y', r) ∩ C` lie in `V` (a segment from `y₀ = f(x₀)`, `d_C(x₀) = 0`, to such a point
stays in `V`: the supremum of the parameters in `V` is attained by a Cauchy argument, and the
classical inverse function theorem at the interior point `x*` with `f(x*) = y_{τ*}` pushes it
further), then the others by density.  (Lemma 3.8.21 (preprint 3.77)) `g = f⁻¹` is `C^1` with `Dg(y) = Df(g(y))⁻¹`
(the bi-Lipschitz estimate makes `|h| → 0 ⟺ |δ| → 0`).  (Lemma 3.8.20 (preprint 3.76), Proposition 3.8.17 (preprint 3.73)) The
iterated tangent maps `T^k f` are homeomorphisms and satisfy the hypotheses of Lemma 3.8.21 (preprint 3.77) again, so
`g` is `C^∞`.

## What is formalized

* `Polyfold.interior_quadrant`, `Polyfold.degIndex_eq_zero_iff` (`d_C(x) = 0 ↔ x ∈ int C`, the
  "interior points" of Definition 1.3.3 (preprint 1.23)), `Polyfold.degIndex_map_eq` (invariance of `d_C` under a
  linear isomorphism preserving `C`; Lemma 1.3.4 (preprint 1.24) for the presentation `T ∘ S`).
* `Polyfold.InvData` (the hypotheses of Proposition 3.8.17 (preprint 3.73), with `d_C(x) = d_C(f(x))` replaced by
  `x ∈ int C ↔ f(x) ∈ int C`, which is all the proof uses), `InvData.half_norm_le`,
  `InvData.norm_sub_le`, `InvData.injOn` (**Lemma 3.8.18 (preprint 3.74)**, (70)), `InvData.map_nhds_eq` (the
  classical inverse function theorem at interior points), `InvData.ball_inter_subset_image`,
  `InvData.image_relOpen` (**Lemma 3.8.18 (preprint 3.74)**, `f(U)` relatively open), `InvData.hasFDerivWithinAt_inv`
  (**Lemma 3.8.21 (preprint 3.77)**), `InvData.contDiffOn_inv` (the inverse is `C^j`), `Polyfold.proposition_3_8_17`
  (**Proposition 3.8.17 (preprint 3.73)**, for `C^j`, `j ≥ 1`), `Polyfold.corollary_3_8_19` (**Corollary 3.8.19 (preprint 3.75)**),
  `Polyfold.theorem_3_8_15` (**Theorem 3.8.15 (preprint 3.72)**, for `C^j` maps on a finite-dimensional `V`; `C^∞` is
  the case of all `j`).

## What the text leaves implicit, and the choices made (the findings)

* **Hypothesis (2) is used only through "`x` interior ⟺ `f(x)` interior"** (`d_C = 0` on both
  sides): the full equality of degeneracy indices is not needed for the inverse function theorem
  (`Polyfold.InvData.interior_iff`).  Some such hypothesis is needed: `f(x, y) = (x, y + x²)` on
  `C = [0,∞)²` is smooth with `f(C) ⊆ C`, `f(0) = 0`, `Df(0) = 1`, but `f(C) = {b ≥ a²}` is not a
  neighbourhood of `0` in `C` (it misses `(a, a²/2)`); here (2) fails at `(x, 0)`, `x > 0`, a
  boundary point mapped to the interior point `(x, x²)`.
* **`C^k` is Mathlib's `ContDiffOn` on `U`**, not Definition 3.71 (iterated tangent maps); on a
  relatively open subset of a partial quadrant the two agree (sc¹ = `C¹`, Chapter 1, and
  `Polyfold.isSc1_iff_contDiffOn_of_isRelOpenInQuadrant`).  Accordingly the regularity of the
  inverse (Lemma 3.8.20 (preprint 3.76) and the proof of Proposition 3.8.17 (preprint 3.73) via `T^k f`) is proved by bootstrapping
  `Dg = [Df]⁻¹ ∘ g` (`InvData.contDiffOn_inv`), as in `QuadrantIFT.lean`.
* **Lemma 3.8.18 (preprint 3.74), the openness**: the text's Cauchy-sequence step is replaced by the compactness of
  `A = f(B̄(x', 2r) ∩ C)` (`B̄(x', 2r) ∩ C ⊆ U` is compact in finite dimensions), which also gives
  the density step.  The interior starting point `x₀` must be chosen with `f(x₀) ∈ B(y', r)` (the
  text takes any `x₀ ∈ B(x', 3r) ∩ C` with `d_C(x₀) = 0`), and `τ'` in "`τ_n → τ'`" is `τ*`.
* **Lemma 3.8.21 (preprint 3.77)** is stated with the extra hypotheses "`V = f(U)` relatively open, `f : U → V` a
  homeomorphism, `Df(x)` invertible"; all three are consequences of Proposition 3.8.17 (preprint 3.73)'s hypotheses
  (`‖Df − 1‖ ≤ 1/2` makes `Df(x)` a unit), so only `InvData` is assumed here.  The general form, for any
  `C¹` homeomorphism with invertible derivative, is `lemma_3_8_21` (`GapP1_Lemma3821.lean`, 2026-11-12); Lemma
  3.8.20 (preprint 3.76) through it is `lemma_3_8_20` (`GapP1_Lemma3820.lean`).
* **`Df(0)` is an isomorphism** from `Df(0)C = C` because `C` has an interior point
  (`Polyfold.surjective_of_image_eq`; the text: `ℝⁿ = C − C`); `0 ∈ U` and `f(0) = 0` are not
  used in Proposition 3.8.17 (preprint 3.73) (`InvData` has neither).
* The partial quadrant structure of `C` enters Proposition 3.8.17 (preprint 3.73) only through: `C` convex and closed
  with nonempty interior, and `d_C = 0 ↔ interior`.
-/

open Set Filter Topology Function Module Asymptotics

set_option linter.unusedSectionVars false

noncomputable section

namespace Polyfold

/-! ### Interior points of a partial quadrant: `d_C(x) = 0` -/

section Degeneracy

variable {E : ScBanach}

/-- The interior of the model quadrant `[0,∞)ⁿ ⊕ W`: all half-line coordinates positive. -/
lemma interior_quadrant (n : ℕ) (W : ScBanach) :
    interior (quadrant n W 0) = {p | ∀ i, 0 < p.1 i} := by
  apply Subset.antisymm
  · intro p hp i
    by_contra hle
    push Not at hle
    have h0 : p.1 i = 0 := le_antisymm hle (interior_subset hp i)
    rw [mem_interior_iff_mem_nhds] at hp
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hp
    have hmem : ((p.1 - (δ / 2) • Pi.single i (1 : ℝ), p.2) : (Fin n → ℝ) × W 0) ∈
        Metric.ball p δ := by
      rw [Metric.mem_ball, dist_eq_norm]
      have : ((p.1 - (δ / 2) • Pi.single i (1 : ℝ), p.2) : (Fin n → ℝ) × W 0) - p =
          (-((δ / 2) • Pi.single i (1 : ℝ)), 0) := by
        ext <;> simp
      rw [this, Prod.norm_def, norm_neg, norm_zero, norm_smul, Pi.norm_single, norm_one, mul_one,
        Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ δ / 2)]
      exact max_lt (by linarith) hδ
    have := hball hmem i
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, h0,
      zero_sub] at this
    linarith
  · intro p hp
    rw [mem_interior_iff_mem_nhds]
    have hopen : IsOpen {p : (Fin n → ℝ) × W 0 | ∀ i, 0 < p.1 i} := by
      have : {p : (Fin n → ℝ) × W 0 | ∀ i, 0 < p.1 i} = ⋂ i, {p | 0 < p.1 i} := by
        ext q; simp
      rw [this]
      exact isOpen_iInter_of_finite fun i =>
        isOpen_lt continuous_const ((continuous_apply i).comp continuous_fst)
    exact Filter.mem_of_superset (hopen.mem_nhds hp) fun q hq i => (hq i).le

/-- `d_C(x) = 0` exactly at the interior points of `C` (Definition 1.3.3 (preprint 1.23): "`x` is an interior
point if `d_C(x) = 0`"). -/
theorem degIndex_eq_zero_iff {C : Set (E 0)} (hC : IsPartialQuadrant E C) {x : E 0}
    (hx : x ∈ C) : degIndex E C x = 0 ↔ x ∈ interior C := by
  classical
  obtain ⟨n, W, T, rfl⟩ := hC
  rw [degIndex_eq T rfl hx]
  have h1 : (T 0).toHomeomorph ⁻¹' interior (quadrant n W 0) =
      interior ((T 0) ⁻¹' quadrant n W 0) := (T 0).toHomeomorph.preimage_interior _
  have h2 : x ∈ interior ((T 0) ⁻¹' quadrant n W 0) ↔ T 0 x ∈ interior (quadrant n W 0) := by
    rw [← h1]; rfl
  rw [h2, interior_quadrant]
  change (Finset.univ.filter fun i => (T 0 x).1 i = 0).card = 0 ↔ ∀ i, 0 < (T 0 x).1 i
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h i
    exact lt_of_le_of_ne (hx i) (Ne.symm (h (Finset.mem_univ i)))
  · intro h i _
    exact (h i).ne'

end Degeneracy

/-! ### The degeneracy index under a linear isomorphism preserving `C` -/

section DegMap

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- A continuous linear automorphism of a finite-dimensional space as an sc-isomorphism of the
constant structure. -/
def ScIso.ofCLE (S : V ≃L[ℝ] V) : ScIso (ScBanach.const V) (ScBanach.const V) where
  lvl _ := S
  incl_comm _ _ := rfl

/-- The degeneracy index is invariant under a linear isomorphism `S` with `S(C) = C`
(Lemma 1.3.4 (preprint 1.24): the presentation `T ∘ S` of `C`). -/
theorem degIndex_map_eq {C : Set V} (hC : IsPartialQuadrant (ScBanach.const V) C) (S : V ≃L[ℝ] V)
    (hS : ∀ x, x ∈ C ↔ S x ∈ C) {x : V} (hx : x ∈ C) :
    degIndex (ScBanach.const V) C (S x) = degIndex (ScBanach.const V) C x := by
  obtain ⟨n, W, T, rfl⟩ := hC
  have hT' : (S ⁻¹' (T 0 ⁻¹' quadrant n W 0) : Set V) =
      ((ScIso.ofCLE S).trans T) 0 ⁻¹' quadrant n W 0 := rfl
  have hC' : (T 0 ⁻¹' quadrant n W 0 : Set V) = ((ScIso.ofCLE S).trans T) 0 ⁻¹' quadrant n W 0 := by
    rw [← hT']; ext y; exact hS y
  rw [degIndex_eq T rfl ((hS x).1 hx), degIndex_eq ((ScIso.ofCLE S).trans T) hC' hx]
  rfl

end DegMap

/-! ### Proposition 3.8.17 (preprint 3.73): the data -/

section Prop373

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The hypotheses of Proposition 3.8.17 (preprint 3.73): `U` a relatively open convex subset of the partial
quadrant `C ⊆ V`, `f : U → C` of class `C^j` (`j ≥ 1`) with `‖Df(x) − 1‖ ≤ 1/2` on `U`, and `f`
preserving interior points (`d_C(f(x)) = d_C(x)` is used only through `d_C = 0 ↔ interior`). -/
structure InvData (C U : Set V) (f : V → V) (j : ℕ) : Prop where
  isPartialQuadrant : IsPartialQuadrant (ScBanach.const V) C
  relOpen : ∃ O : Set V, IsOpen O ∧ U = O ∩ C
  convex : Convex ℝ U
  mapsTo : MapsTo f U C
  one_le : 1 ≤ j
  contDiffOn : ContDiffOn ℝ j f U
  deriv_bound : ∀ x ∈ U, ‖fderivWithin ℝ f U x - 1‖ ≤ 1 / 2
  interior_iff : ∀ x ∈ U, x ∈ interior C ↔ f x ∈ interior C

namespace InvData

variable {C U : Set V} {f : V → V} {j : ℕ} (h : InvData C U f j)
include h

lemma convex_C : Convex ℝ C := h.isPartialQuadrant.convex

lemma isClosed_C : IsClosed C := h.isPartialQuadrant.isClosed

lemma interior_C_nonempty : (interior C).Nonempty := by
  have := h.isPartialQuadrant.interior_lvlSet_nonempty 0
  rwa [ScBanach.lvlSet_const] at this

lemma U_subset : U ⊆ C := by
  obtain ⟨O, -, hU⟩ := h.relOpen; rw [hU]; exact inter_subset_right

lemma uniqueDiffOn_U : UniqueDiffOn ℝ U := by
  obtain ⟨O, hO, hU⟩ := h.relOpen
  rw [hU, inter_comm]
  exact (uniqueDiffOn_convex h.convex_C h.interior_C_nonempty).inter hO

lemma j_ne_zero : (j : WithTop ℕ∞) ≠ 0 := by
  have := h.one_le; exact_mod_cast (show j ≠ 0 by omega)

lemma hasFDerivWithinAt {x : V} (hx : x ∈ U) : HasFDerivWithinAt f (fderivWithin ℝ f U x) U x :=
  ((h.contDiffOn.differentiableOn h.j_ne_zero) x hx).hasFDerivWithinAt

lemma continuousOn : ContinuousOn f U := h.contDiffOn.continuousOn

/-- Lemma 3.8.18 (preprint 3.74), (70), first step: `f − id` is a `1/2`-contraction on `U`. -/
lemma norm_sub_sub_le {x x' : V} (hx : x ∈ U) (hx' : x' ∈ U) :
    ‖(f x' - x') - (f x - x)‖ ≤ 1 / 2 * ‖x' - x‖ :=
  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := fun z => f z - z)
    (f' := fun z => fderivWithin ℝ f U z - 1)
    (fun z hz => (h.hasFDerivWithinAt hz).sub (hasFDerivWithinAt_id z U))
    (fun z hz => h.deriv_bound z hz) h.convex hx hx'

/-- Lemma 3.8.18 (preprint 3.74), (70): `|x − x'|/2 ≤ |f(x) − f(x')|`. -/
lemma half_norm_le {x x' : V} (hx : x ∈ U) (hx' : x' ∈ U) :
    1 / 2 * ‖x' - x‖ ≤ ‖f x' - f x‖ := by
  have h1 := h.norm_sub_sub_le hx hx'
  have h2 : ‖x' - x‖ ≤ ‖f x' - f x‖ + ‖(f x' - x') - (f x - x)‖ := by
    calc ‖x' - x‖ = ‖(f x' - f x) - ((f x' - x') - (f x - x))‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  linarith

/-- Lemma 3.8.18 (preprint 3.74), (70): `|f(x) − f(x')| ≤ 3|x − x'|/2`. -/
lemma norm_sub_le {x x' : V} (hx : x ∈ U) (hx' : x' ∈ U) :
    ‖f x' - f x‖ ≤ 3 / 2 * ‖x' - x‖ := by
  have h1 := h.norm_sub_sub_le hx hx'
  have h2 : ‖f x' - f x‖ ≤ ‖x' - x‖ + ‖(f x' - x') - (f x - x)‖ := by
    calc ‖f x' - f x‖ = ‖(x' - x) + ((f x' - x') - (f x - x))‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  linarith

lemma injOn : InjOn f U := by
  intro x hx x' hx' hxx'
  have := h.half_norm_le hx hx'
  rw [hxx', sub_self, norm_zero] at this
  have h2 : ‖x' - x‖ ≤ 0 := by linarith
  exact (sub_eq_zero.1 (norm_le_zero_iff.1 h2)).symm

/-- `Df(x) = 1 − (1 − Df(x))` is a unit (`‖1 − Df(x)‖ ≤ 1/2`). -/
def derivUnit {x : V} (hx : x ∈ U) : (V →L[ℝ] V)ˣ :=
  Units.oneSub (1 - fderivWithin ℝ f U x)
    (by rw [norm_sub_rev]; exact (h.deriv_bound x hx).trans_lt (by norm_num))

lemma derivUnit_val {x : V} (hx : x ∈ U) : (h.derivUnit hx : V →L[ℝ] V) = fderivWithin ℝ f U x :=
  sub_sub_cancel _ _

lemma isUnit_deriv {x : V} (hx : x ∈ U) : IsUnit (fderivWithin ℝ f U x) := by
  have := (h.derivUnit hx).isUnit
  rwa [h.derivUnit_val hx] at this

/-- `U` is a neighbourhood of its interior points of `C`. -/
lemma U_mem_nhds {x : V} (hx : x ∈ U) (hxi : x ∈ interior C) : U ∈ 𝓝 x := by
  obtain ⟨O, hO, hU⟩ := h.relOpen
  have hxO : x ∈ O := by rw [hU] at hx; exact hx.1
  rw [hU]
  exact Filter.inter_mem (hO.mem_nhds hxO) (mem_interior_iff_mem_nhds.1 hxi)

/-- At an interior point of `C` the classical inverse function theorem applies: `f` maps
neighbourhoods of `x` onto neighbourhoods of `f(x)`. -/
lemma map_nhds_eq {x : V} (hx : x ∈ U) (hxi : x ∈ interior C) : map f (𝓝 x) = 𝓝 (f x) := by
  have hUn := h.U_mem_nhds hx hxi
  have hcd : ContDiffAt ℝ j f x := h.contDiffOn.contDiffAt hUn
  have hs : HasStrictFDerivAt f (fderiv ℝ f x) x := hcd.hasStrictFDerivAt h.j_ne_zero
  have heq : fderiv ℝ f x = (ContinuousLinearEquiv.ofUnit (h.derivUnit hx) : V →L[ℝ] V) := by
    rw [← fderivWithin_of_mem_nhds hUn, ← h.derivUnit_val hx]; rfl
  rw [heq] at hs
  exact hs.map_nhds_eq_of_equiv

/-- **Lemma 3.8.18 (preprint 3.74)**, the openness: if `B(x', 3r) ∩ C ⊆ U` then `B(f(x'), r) ∩ C ⊆ f(U)`. -/
theorem ball_inter_subset_image {x' : V} (hx' : x' ∈ U) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball x' (3 * r) ∩ C ⊆ U) : Metric.ball (f x') r ∩ C ⊆ f '' U := by
  obtain ⟨O, hO, hU⟩ := h.relOpen
  -- the compact set `A = f(B̄(x', 2r) ∩ C) ⊆ f(U)`
  set A := f '' (Metric.closedBall x' (2 * r) ∩ C) with hA
  have hsub : Metric.closedBall x' (2 * r) ∩ C ⊆ U := fun z hz =>
    hball ⟨Metric.closedBall_subset_ball (by linarith) hz.1, hz.2⟩
  have hAcpt : IsCompact A :=
    ((isCompact_closedBall x' (2 * r)).inter_right h.isClosed_C).image_of_continuousOn
      (h.continuousOn.mono hsub)
  have hAU : A ⊆ f '' U := Set.image_mono hsub
  have hkey : ∀ y ∈ Metric.ball (f x') r, y ∈ f '' U → y ∈ A := by
    rintro y hy ⟨x, hxU, rfl⟩
    refine ⟨x, ⟨?_, h.U_subset hxU⟩, rfl⟩
    have := h.half_norm_le hx' hxU
    rw [Metric.mem_closedBall, dist_eq_norm]
    rw [Metric.mem_ball, dist_eq_norm] at hy
    linarith
  -- an interior point `x₀ ∈ U` with `f(x₀) ∈ B(f(x'), r)`
  obtain ⟨x₀, hx₀U, hx₀i, hfx₀⟩ : ∃ x₀ ∈ U, x₀ ∈ interior C ∧ f x₀ ∈ Metric.ball (f x') r := by
    have hnhds : f ⁻¹' Metric.ball (f x') r ∈ 𝓝[U] x' :=
      (h.continuousOn x' hx').preimage_mem_nhdsWithin (Metric.ball_mem_nhds _ hr)
    obtain ⟨O₁, hO₁, hx'O₁, hO₁W⟩ := mem_nhdsWithin.1 hnhds
    have hx'O : x' ∈ O := by rw [hU] at hx'; exact hx'.1
    obtain ⟨z, hz⟩ := h.interior_C_nonempty
    have hev : ∀ᶠ t : ℝ in 𝓝 0, x' + t • (z - x') ∈ O₁ ∩ O := by
      have hc : Continuous fun t : ℝ => x' + t • (z - x') := by fun_prop
      exact (hc.continuousAt (x := 0)).preimage_mem_nhds
        (by simpa using (hO₁.inter hO).mem_nhds ⟨hx'O₁, hx'O⟩)
    obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 hev
    have ht0 : 0 < min (δ / 2) 1 := lt_min (by positivity) one_pos
    have htδ : dist (min (δ / 2) 1) 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht0]
      exact (min_le_left _ _).trans_lt (by linarith)
    have hmemO := hδ' htδ
    have hint : x' + min (δ / 2) 1 • (z - x') ∈ interior C :=
      h.convex_C.add_smul_sub_mem_interior (h.U_subset hx') hz ⟨ht0, min_le_right _ _⟩
    have hmemU : x' + min (δ / 2) 1 • (z - x') ∈ U := by
      rw [hU]; exact ⟨hmemO.2, interior_subset hint⟩
    exact ⟨_, hmemU, hint, hO₁W ⟨hmemO.1, hmemU⟩⟩
  have hy₀i : f x₀ ∈ interior C := (h.interior_iff x₀ hx₀U).1 hx₀i
  have hy₀A : f x₀ ∈ A := hkey _ hfx₀ ⟨x₀, hx₀U, rfl⟩
  -- Step 1: interior points of `C` in the ball lie in `A` (the segment argument)
  have hstep1 : ∀ y₁ ∈ Metric.ball (f x') r, y₁ ∈ interior C → y₁ ∈ A := by
    intro y₁ hy₁ hy₁i
    set γ : ℝ → V := fun t => f x₀ + t • (y₁ - f x₀) with hγ
    have hγc : Continuous γ := by fun_prop
    have hγball : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ Metric.ball (f x') r := fun t ht =>
      (convex_ball (f x') r).add_smul_sub_mem hfx₀ hy₁ ht
    have hγint : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ interior C := fun t ht =>
      h.convex_C.interior.add_smul_sub_mem hy₀i hy₁i ht
    set Sg : Set ℝ := Icc 0 1 ∩ γ ⁻¹' A with hSg
    have hSgc : IsClosed Sg := isClosed_Icc.inter (hAcpt.isClosed.preimage hγc)
    have h0Sg : (0 : ℝ) ∈ Sg := ⟨⟨le_rfl, zero_le_one⟩, by simpa [hγ] using hy₀A⟩
    have hSgbdd : BddAbove Sg := ⟨1, fun t ht => ht.1.2⟩
    have hsSg : sSup Sg ∈ Sg := hSgc.csSup_mem ⟨0, h0Sg⟩ hSgbdd
    have hs1 : sSup Sg = 1 := by
      by_contra hne
      have hlt : sSup Sg < 1 := lt_of_le_of_ne hsSg.1.2 hne
      obtain ⟨x₁, hx₁U, hx₁⟩ := hAU hsSg.2
      have hx₁i : x₁ ∈ interior C := (h.interior_iff x₁ hx₁U).2 (hx₁ ▸ hγint _ hsSg.1)
      have himg : f '' U ∈ 𝓝 (γ (sSup Sg)) := by
        rw [← hx₁, ← h.map_nhds_eq hx₁U hx₁i]
        exact image_mem_map (h.U_mem_nhds hx₁U hx₁i)
      have hev : ∀ᶠ t in 𝓝 (sSup Sg), γ t ∈ f '' U := hγc.continuousAt.preimage_mem_nhds himg
      obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 hev
      set t₂ := min 1 (sSup Sg + δ / 2) with ht₂
      have ht₂gt : sSup Sg < t₂ := lt_min hlt (by linarith)
      have ht₂Sg : t₂ ∈ Sg := by
        refine ⟨⟨hsSg.1.1.trans ht₂gt.le, min_le_left _ _⟩, ?_⟩
        have hdist : dist t₂ (sSup Sg) < δ := by
          rw [Real.dist_eq, abs_of_pos (by linarith)]
          linarith [min_le_right 1 (sSup Sg + δ / 2)]
        exact hkey _ (hγball t₂ ⟨hsSg.1.1.trans ht₂gt.le, min_le_left _ _⟩) (hδ' hdist)
      exact absurd (le_csSup hSgbdd ht₂Sg) (not_le.2 ht₂gt)
    have := hsSg.2
    rw [hs1] at this
    simpa [hγ] using this
  -- Step 2: every point of `B(f(x'), r) ∩ C` is a limit of such interior points
  intro y hy
  refine hAU ?_
  have htend : Tendsto (fun t : ℝ => y + t • (f x₀ - y)) (𝓝[>] 0) (𝓝 y) := by
    have hc : Continuous fun t : ℝ => y + t • (f x₀ - y) := by fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  refine hAcpt.isClosed.mem_of_tendsto htend ?_
  have h1 : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  have h2 : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 := nhdsWithin_le_nhds (eventually_lt_nhds one_pos)
  filter_upwards [h1, h2] with t ht0 ht1
  refine hstep1 _ ((convex_ball (f x') r).add_smul_sub_mem hy.1 hfx₀ ⟨ht0.le, ht1.le⟩) ?_
  exact h.convex_C.add_smul_sub_mem_interior hy.2 hy₀i ⟨ht0, ht1.le⟩

/-- **Lemma 3.8.18 (preprint 3.74)**: `f(U)` is a relatively open subset of `C`. -/
theorem image_relOpen : ∃ O' : Set V, IsOpen O' ∧ f '' U = O' ∩ C := by
  classical
  obtain ⟨O, hO, hU⟩ := h.relOpen
  have hrad : ∀ y ∈ f '' U, ∃ r > 0, Metric.ball y r ∩ C ⊆ f '' U := by
    rintro y ⟨x', hx', rfl⟩
    have hx'O : x' ∈ O := by rw [hU] at hx'; exact hx'.1
    obtain ⟨ρ, hρ, hρO⟩ := Metric.isOpen_iff.1 hO x' hx'O
    refine ⟨ρ / 3, by positivity, h.ball_inter_subset_image hx' (by positivity) fun z hz => ?_⟩
    rw [hU]
    refine ⟨hρO ?_, hz.2⟩
    have := hz.1
    rwa [show 3 * (ρ / 3) = ρ by ring] at this
  choose! r hr hrsub using hrad
  refine ⟨⋃ y ∈ f '' U, Metric.ball y (r y), isOpen_biUnion fun y _ => Metric.isOpen_ball, ?_⟩
  apply Subset.antisymm
  · intro y hy
    exact ⟨mem_biUnion hy (Metric.mem_ball_self (hr y hy)), h.mapsTo.image_subset hy⟩
  · rintro y ⟨hy, hyC⟩
    obtain ⟨y', hy', hyy'⟩ := mem_iUnion₂.1 hy
    exact hrsub y' hy' ⟨hyy', hyC⟩

/-! ### The inverse (Lemma 3.8.21 (preprint 3.77)) and its regularity (Proposition 3.8.17 (preprint 3.73)) -/

omit h in
/-- The inverse `g = f⁻¹ : f(U) → U`. -/
def inv (U : Set V) (f : V → V) : V → V := Function.invFunOn f U

lemma inv_mem {y : V} (hy : y ∈ f '' U) : inv U f y ∈ U := Function.invFunOn_mem hy

lemma apply_inv {y : V} (hy : y ∈ f '' U) : f (inv U f y) = y := Function.invFunOn_eq hy

lemma inv_apply {x : V} (hx : x ∈ U) : inv U f (f x) = x := h.injOn.leftInvOn_invFunOn hx

lemma norm_inv_sub_le {y y' : V} (hy : y ∈ f '' U) (hy' : y' ∈ f '' U) :
    ‖inv U f y' - inv U f y‖ ≤ 2 * ‖y' - y‖ := by
  have := h.half_norm_le (h.inv_mem hy) (h.inv_mem hy')
  rw [h.apply_inv hy, h.apply_inv hy'] at this
  linarith

lemma continuousOn_inv : ContinuousOn (inv U f) (f '' U) :=
  (LipschitzOnWith.of_dist_le_mul (K := 2) fun y hy y' hy' => by
    rw [dist_eq_norm, dist_eq_norm]
    exact h.norm_inv_sub_le hy' hy).continuousOn

lemma uniqueDiffOn_image : UniqueDiffOn ℝ (f '' U) := by
  obtain ⟨O', hO', hV⟩ := h.image_relOpen
  rw [hV, inter_comm]
  exact (uniqueDiffOn_convex h.convex_C h.interior_C_nonempty).inter hO'

/-- **Lemma 3.8.21 (preprint 3.77)**: the inverse is differentiable within `f(U)` with `Dg(y) = [Df(g(y))]⁻¹`. -/
theorem hasFDerivWithinAt_inv {y : V} (hy : y ∈ f '' U) :
    HasFDerivWithinAt (inv U f) (Ring.inverse (fderivWithin ℝ f U (inv U f y))) (f '' U) y := by
  have hxU : inv U f y ∈ U := h.inv_mem hy
  have hf := h.hasFDerivWithinAt hxU
  rw [hasFDerivWithinAt_iff_isLittleO] at hf ⊢
  have htend : Tendsto (inv U f) (𝓝[f '' U] y) (𝓝[U] (inv U f y)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨h.continuousOn_inv y hy, eventually_nhdsWithin_of_forall fun y' hy' => h.inv_mem hy'⟩
  have h1 := hf.comp_tendsto htend
  have h2 : (fun y' => inv U f y' - inv U f y) =O[𝓝[f '' U] y] (fun y' => y' - y) :=
    IsBigO.of_bound 2 (eventually_nhdsWithin_of_forall fun y' hy' => h.norm_inv_sub_le hy hy')
  have h3 := h1.trans_isBigO h2
  have hM : Ring.inverse (fderivWithin ℝ f U (inv U f y)) * fderivWithin ℝ f U (inv U f y) = 1 :=
    Ring.inverse_mul_cancel _ (h.isUnit_deriv hxU)
  have h4 := ((Ring.inverse (fderivWithin ℝ f U (inv U f y))).isBigO_comp _
    (𝓝[f '' U] y)).trans_isLittleO h3
  refine (isLittleO_neg_left.2 h4).congr' (eventually_nhdsWithin_of_forall fun y' hy' => ?_)
    EventuallyEq.rfl
  simp only [Function.comp_apply]
  rw [h.apply_inv hy', h.apply_inv hy, map_sub, map_sub, ← mul_apply_eq_comp, hM,
    one_apply_eq_self]
  abel

/-- `x ↦ [Df(x)]⁻¹` is of class `C^{j−1}` on `U`. -/
theorem contDiffOn_inverse_deriv :
    ContDiffOn ℝ (j - 1 : ℕ) (fun x => Ring.inverse (fderivWithin ℝ f U x)) U := by
  have hD : ContDiffOn ℝ (j - 1 : ℕ) (fderivWithin ℝ f U) U :=
    h.contDiffOn.fderivWithin h.uniqueDiffOn_U
      (by have := h.one_le; exact_mod_cast (show (j - 1 : ℕ) + 1 ≤ j by omega))
  intro x hx
  have h2 : ContDiffAt ℝ (j - 1 : ℕ) (Ring.inverse : (V →L[ℝ] V) → (V →L[ℝ] V))
      ((h.derivUnit hx : (V →L[ℝ] V)ˣ) : V →L[ℝ] V) := contDiffAt_ringInverse ℝ _
  rw [h.derivUnit_val hx] at h2
  exact h2.contDiffWithinAt.comp x (hD x hx) (mapsTo_univ _ _)

/-- **Proposition 3.8.17 (preprint 3.73), the regularity of the inverse**: `g = f⁻¹` is of class `C^j` on `f(U)`
(the text: via the iterated tangent maps `T^k f`, Lemma 3.8.20 (preprint 3.76); here by bootstrapping
`Dg = [Df]⁻¹ ∘ g`). -/
theorem contDiffOn_inv : ContDiffOn ℝ j (inv U f) (f '' U) := by
  have key : ∀ i : ℕ, i ≤ j → ContDiffOn ℝ i (inv U f) (f '' U) := by
    intro i
    induction i with
    | zero => intro _; exact contDiffOn_zero.2 h.continuousOn_inv
    | succ i ih =>
      intro hi
      rw [show ((i + 1 : ℕ) : WithTop ℕ∞) = (i : WithTop ℕ∞) + 1 by push_cast; rfl]
      refine (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn h.uniqueDiffOn_image).2
        ⟨fun hω => absurd hω (by simp), fun y => Ring.inverse (fderivWithin ℝ f U (inv U f y)), ?_,
          fun y hy => h.hasFDerivWithinAt_inv hy⟩
      have hΨ : ContDiffOn ℝ i (fun x => Ring.inverse (fderivWithin ℝ f U x)) U :=
        h.contDiffOn_inverse_deriv.of_le (by exact_mod_cast (show i ≤ j - 1 by omega))
      exact hΨ.comp (ih (by omega)) fun y hy => h.inv_mem hy
  exact key j le_rfl

end InvData

/-- **Proposition 3.8.17 (preprint 3.73)** (with Lemmas 3.74–3.77): under `InvData` — `U` relatively open and
convex in the partial quadrant `C`, `f : U → C` of class `C^j` with `‖Df − 1‖ ≤ 1/2` and preserving
interior points — the image `V = f(U)` is relatively open in `C` and `f : U → V` is a
`C^j`-diffeomorphism: injective, with inverse `g` of class `C^j` on `V`. -/
theorem proposition_3_8_17 {C U : Set V} {f : V → V} {j : ℕ} (h : InvData C U f j) :
    (∃ O' : Set V, IsOpen O' ∧ f '' U = O' ∩ C) ∧ InjOn f U ∧
      ∃ g : V → V, ContDiffOn ℝ j g (f '' U) ∧ (∀ x ∈ U, g (f x) = x) ∧
        ∀ y ∈ f '' U, f (g y) = y ∧ g y ∈ U :=
  ⟨h.image_relOpen, h.injOn, InvData.inv U f, h.contDiffOn_inv, fun _ hx => h.inv_apply hx,
    fun _ hy => ⟨h.apply_inv hy, h.inv_mem hy⟩⟩

/-- **Corollary 3.8.19 (preprint 3.75)**: under the assumptions of Proposition 3.8.17 (preprint 3.73), `f : U → V = f(U)` is a
homeomorphism between relatively open subsets of `C` (`V` relatively open by Lemma 3.8.18 (preprint 3.74)). -/
theorem corollary_3_8_19 {C U : Set V} {f : V → V} {j : ℕ} (h : InvData C U f j) :
    ContinuousOn f U ∧ ContinuousOn (InvData.inv U f) (f '' U) ∧
      (∀ x ∈ U, InvData.inv U f (f x) = x) ∧ ∀ y ∈ f '' U, f (InvData.inv U f y) = y :=
  ⟨h.continuousOn, h.continuousOn_inv, fun _ hx => h.inv_apply hx, fun _ hy => h.apply_inv hy⟩

end Prop373

/-! ### Theorem 3.8.15 (preprint 3.72) -/

section Theorem372

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- A linear map carrying a set with nonempty interior onto itself is onto. -/
lemma surjective_of_image_eq {C : Set V} (hCi : (interior C).Nonempty)
    (L : V →L[ℝ] V) (hL : L '' C = C) : Function.Surjective L := by
  obtain ⟨x₀, hx₀⟩ := hCi
  intro v
  have hev : ∀ᶠ t : ℝ in 𝓝 0, x₀ + t • v ∈ C := by
    have hc : Continuous fun t : ℝ => x₀ + t • v := by fun_prop
    exact (hc.continuousAt (x := 0)).preimage_mem_nhds
      (by simpa using mem_interior_iff_mem_nhds.1 hx₀)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 hev
  have h1 : x₀ + (δ / 2) • v ∈ C := hδ' (y := δ / 2)
    (by rw [dist_zero_right, Real.norm_of_nonneg (by positivity)]; linarith)
  have h0 : x₀ ∈ C := interior_subset hx₀
  rw [← hL] at h1 h0
  obtain ⟨c₁, -, hc₁⟩ := h1
  obtain ⟨c₂, -, hc₂⟩ := h0
  refine ⟨(δ / 2)⁻¹ • (c₁ - c₂), ?_⟩
  rw [map_smul, map_sub, hc₁, hc₂, add_sub_cancel_left, smul_smul,
    inv_mul_cancel₀ (by positivity), one_smul]

/-- **Theorem 3.8.15 (preprint 3.72) (quadrant inverse function theorem)**: `U` a relatively open neighbourhood of
`0` in the partial quadrant `C` of the finite-dimensional `V`, `f : U → V` of class `C^j`
(`j ≥ 1`; the text: smooth) with `f(U) ⊆ C`, (1) `f(0) = 0` and `Df(0)C = C`, (2)
`d_C(x) = d_C(f(x))` for `x ∈ U`.  Then there are relatively open neighbourhoods `U' ⊆ U` and `V'`
of `0` in `C` such that `f : U' → V'` is a `C^j`-diffeomorphism. -/
theorem theorem_3_8_15 {C U : Set V} (hU : IsRelOpenInQuadrant (ScBanach.const V) C U)
    (h0 : (0 : V) ∈ U) {f : V → V} {j : ℕ} (hj : 1 ≤ j) (hf : ContDiffOn ℝ j f U)
    (hfC : MapsTo f U C) (hf0 : f 0 = 0) (hDf : fderivWithin ℝ f U 0 '' C = C)
    (hdeg : ∀ x ∈ U, degIndex (ScBanach.const V) C x = degIndex (ScBanach.const V) C (f x)) :
    ∃ U' V' : Set V, (∃ O : Set V, IsOpen O ∧ U' = O ∩ C) ∧ (∃ O : Set V, IsOpen O ∧ V' = O ∩ C) ∧
      (0 : V) ∈ U' ∧ (0 : V) ∈ V' ∧ U' ⊆ U ∧ f '' U' = V' ∧ InjOn f U' ∧
      ∃ g : V → V, ContDiffOn ℝ j g V' ∧ (∀ x ∈ U', g (f x) = x) ∧
        ∀ y ∈ V', f (g y) = y ∧ g y ∈ U' := by
  classical
  obtain ⟨O, hO, hUO⟩ := hU.relOpen
  have hC := hU.isPartialQuadrant
  have hCconv : Convex ℝ C := hC.convex
  have hCint : (interior C).Nonempty := by
    have := hC.interior_lvlSet_nonempty 0
    rwa [ScBanach.lvlSet_const] at this
  have hUC : U ⊆ C := by rw [hUO]; exact inter_subset_right
  have h0O : (0 : V) ∈ O := by rw [hUO] at h0; exact h0.1
  have h0C : (0 : V) ∈ C := hUC h0
  have hUD : UniqueDiffOn ℝ U := by
    rw [hUO, inter_comm]; exact (uniqueDiffOn_convex hCconv hCint).inter hO
  have hjne : (j : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  -- `L = Df(0)` is an isomorphism preserving `C`
  set L : V →L[ℝ] V := fderivWithin ℝ f U 0 with hL
  have hLsurj : Function.Surjective L := surjective_of_image_eq hCint L hDf
  have hLinj : Function.Injective L :=
    (LinearMap.injective_iff_surjective (f := (L : V →ₗ[ℝ] V))).2 hLsurj
  let Le : V ≃L[ℝ] V :=
    (LinearEquiv.ofBijective (L : V →ₗ[ℝ] V) ⟨hLinj, hLsurj⟩).toContinuousLinearEquiv
  have hLe : ∀ x, Le x = L x := fun x => rfl
  have hLeC : ∀ x, x ∈ C ↔ Le x ∈ C := fun x => by
    rw [hLe]
    constructor
    · intro hx; rw [← hDf]; exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← hDf] at hx
      obtain ⟨c, hc, hcx⟩ := hx
      exact (hLinj hcx) ▸ hc
  have hLeC' : ∀ y, y ∈ C ↔ Le.symm y ∈ C := fun y => by
    rw [hLeC (Le.symm y), Le.apply_symm_apply]
  -- the normalized map `g₀ = L⁻¹ ∘ f`, `Dg₀(0) = 1`
  set g₀ : V → V := fun x => Le.symm (f x) with hg₀
  have hg₀cd : ContDiffOn ℝ j g₀ U := hf.continuousLinearMap_comp (Le.symm : V →L[ℝ] V)
  have hg₀D : ∀ x ∈ U, fderivWithin ℝ g₀ U x = (Le.symm : V →L[ℝ] V).comp (fderivWithin ℝ f U x) :=
    fun x hx => ((Le.symm : V →L[ℝ] V).hasFDerivAt.comp_hasFDerivWithinAt x
      ((hf.differentiableOn hjne) x hx).hasFDerivWithinAt).fderivWithin (hUD x hx)
  have hg₀D0 : fderivWithin ℝ g₀ U 0 = 1 := by
    rw [hg₀D 0 h0]
    refine ContinuousLinearMap.ext fun v => ?_
    change Le.symm (L v) = v
    rw [← hLe]; exact Le.symm_apply_apply v
  -- continuity of `Dg₀` at `0` within `U`: a radius `ρ` with `‖Dg₀ − 1‖ ≤ 1/2` on `U ∩ B(0, ρ)`
  have hcont : ContinuousWithinAt (fderivWithin ℝ g₀ U) U 0 :=
    (hg₀cd.fderivWithin hUD (by exact_mod_cast hj : (0 : WithTop ℕ∞) + 1 ≤ j)).continuousOn 0 h0
  rw [ContinuousWithinAt, hg₀D0, Metric.tendsto_nhdsWithin_nhds] at hcont
  obtain ⟨ρ₁, hρ₁, hρ₁'⟩ := hcont (1 / 2) (by norm_num)
  obtain ⟨ρ₂, hρ₂, hρ₂O⟩ := Metric.isOpen_iff.1 hO 0 h0O
  set ρ := min ρ₁ ρ₂ with hρ
  have hρpos : 0 < ρ := lt_min hρ₁ hρ₂
  set U' : Set V := Metric.ball 0 ρ ∩ C with hU'
  have hU'U : U' ⊆ U := fun x hx => by
    rw [hUO]; exact ⟨hρ₂O (Metric.ball_subset_ball (min_le_right _ _) hx.1), hx.2⟩
  have hU'eq : U' = U ∩ Metric.ball 0 ρ := by
    ext x
    constructor
    · intro hx; exact ⟨hU'U hx, hx.1⟩
    · intro hx; exact ⟨hx.2, hUC hx.1⟩
  have hD' : ∀ x ∈ U', fderivWithin ℝ g₀ U' x = fderivWithin ℝ g₀ U x := fun x hx => by
    rw [hU'eq, fderivWithin_inter (Metric.isOpen_ball.mem_nhds hx.1)]
  have hdata : InvData C U' g₀ j :=
    { isPartialQuadrant := hC
      relOpen := ⟨Metric.ball 0 ρ, Metric.isOpen_ball, rfl⟩
      convex := (convex_ball 0 ρ).inter hCconv
      mapsTo := fun x hx => (hLeC' _).1 (hfC (hU'U hx))
      one_le := hj
      contDiffOn := hg₀cd.mono hU'U
      deriv_bound := fun x hx => by
        rw [hD' x hx]
        have hdist : dist x 0 < ρ₁ := by
          have := hx.1; rw [Metric.mem_ball] at this
          exact this.trans_le (min_le_left _ _)
        have := (hρ₁' (hU'U hx) hdist).le
        rwa [dist_eq_norm] at this
      interior_iff := fun x hx => by
        have hxC : x ∈ C := hx.2
        have hgC : g₀ x ∈ C := (hLeC' _).1 (hfC (hU'U hx))
        rw [← degIndex_eq_zero_iff hC hxC, ← degIndex_eq_zero_iff hC hgC]
        have h1 : degIndex (ScBanach.const V) C (g₀ x) = degIndex (ScBanach.const V) C (f x) := by
          have := degIndex_map_eq hC Le hLeC (x := Le.symm (f x)) hgC
          rw [Le.apply_symm_apply] at this
          exact this.symm
        rw [h1, hdeg x (hU'U hx)] }
  obtain ⟨⟨O'', hO'', hV''⟩, hinj, g₁, hg₁cd, hg₁f, hg₁⟩ := proposition_3_8_17 hdata
  -- back to `f = Le ∘ g₀`
  have hfeq : ∀ x, f x = Le (g₀ x) := fun x => (Le.apply_symm_apply (f x)).symm
  have himg : f '' U' = Le '' (g₀ '' U') := by
    rw [← image_comp]; exact image_congr fun x _ => hfeq x
  have hLeCimg : Le '' C = C := by
    ext y
    constructor
    · rintro ⟨c, hc, rfl⟩; exact (hLeC c).1 hc
    · intro hy; exact ⟨Le.symm y, (hLeC' y).1 hy, Le.apply_symm_apply y⟩
  have hLeO : Le '' (O'' ∩ C) = Le '' O'' ∩ C := by
    rw [image_inter Le.injective, hLeCimg]
  refine ⟨U', f '' U', ⟨Metric.ball 0 ρ, Metric.isOpen_ball, rfl⟩,
    ⟨Le '' O'', Le.toHomeomorph.isOpenMap O'' hO'', by rw [himg, hV'', hLeO]⟩,
    ⟨Metric.mem_ball_self hρpos, h0C⟩, ⟨0, ⟨Metric.mem_ball_self hρpos, h0C⟩, hf0⟩, hU'U, rfl,
    ?_, fun y => g₁ (Le.symm y), ?_, fun x hx => ?_, fun y hy => ?_⟩
  · intro x hx x' hx' hxx'
    exact hinj hx hx' (Le.injective (by rw [← hfeq, ← hfeq]; exact hxx'))
  · refine hg₁cd.comp (Le.symm.contDiff.contDiffOn) ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · change g₁ (Le.symm (f x)) = x
    exact hg₁f x hx
  · obtain ⟨x, hx, rfl⟩ := hy
    have hmem : g₀ x ∈ g₀ '' U' := ⟨x, hx, rfl⟩
    refine ⟨?_, (hg₁ _ hmem).2⟩
    change f (g₁ (Le.symm (f x))) = f x
    rw [hfeq (g₁ (Le.symm (f x)))]
    change Le (g₀ (g₁ (g₀ x))) = f x
    rw [(hg₁ _ hmem).1]
    exact (hfeq x).symm

end Theorem372

end Polyfold
