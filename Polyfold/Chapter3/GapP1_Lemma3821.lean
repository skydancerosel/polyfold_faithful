import Polyfold.Chapter3.QuadrantInverse

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §3.8.5: **Lemma 3.8.21**
(preprint 3.77), p. 168, in the general form its use in the proof of Proposition 3.8.17
(preprint 3.73) needs.

# Lemma 3.8.21 for every homeomorphism with invertible derivative

## The text, paraphrased

Let `U` be relatively open in a partial quadrant `C ⊆ ℝⁿ` and `f : U → C` smooth (the text adds
"satisfying the assumptions of Proposition 3.8.17"), with `V = f(U)` relatively open in `C`,
`f : U → V` a homeomorphism and `Df(x)` invertible on `U`.  Then `g = f⁻¹` is `C¹` with
`Dg(y) = [Df(g(y))]⁻¹`.  The proof of Proposition 3.8.17 applies the lemma to the iterated tangent
maps `T^k f`, which do not satisfy `‖D(T^k f) − 1‖ ≤ 1/2`; so the form used is the general one
(any homeomorphism with invertible derivative).

## What is formalized

* `Polyfold.lemma_3_8_21`: the general form, for `f` of class `C¹` on `U` (the text: smooth), with
  no hypothesis of Proposition 3.8.17: `g` is differentiable within `V` with
  `Dg(y) = [Df(g(y))]⁻¹` and of class `C¹` on `V`.
* `Polyfold.lemma_3_8_21_contDiffOn`: if `f` is `C^j` (`j ≥ 1`) then so is `g`; and
  `Polyfold.lemma_3_8_21_smooth`: if `f` is `C^∞`, so is `g` — the conclusion the text draws in
  the proof of Proposition 3.8.17 from the lemma applied to the `T^k f`, here by bootstrapping
  `Dg = [Df]⁻¹ ∘ g`.
* `Polyfold.lemma_3_8_21_printed`: the printed form (the hypotheses of Proposition 3.8.17,
  `InvData`, together with the lemma's own) is a special case.

The proof is Mathlib's `HasFDerivWithinAt.of_local_left_inverse`: the text's bi-Lipschitz estimate
(3.65) is replaced by the invertibility of `Df(g(y))` alone.
-/

open Set Filter Topology Function
open scoped ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace Polyfold

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- A relatively open subset of a partial quadrant of a finite-dimensional space has unique
differentiability. -/
theorem IsRelOpenInQuadrant.uniqueDiffOn_const {C U : Set V}
    (hU : IsRelOpenInQuadrant (ScBanach.const V) C U) : UniqueDiffOn ℝ U := by
  obtain ⟨O, hO, rfl⟩ := hU.relOpen
  have hi : (interior C).Nonempty := by
    have := hU.isPartialQuadrant.interior_lvlSet_nonempty 0
    rwa [ScBanach.lvlSet_const] at this
  rw [inter_comm]
  exact (uniqueDiffOn_convex hU.isPartialQuadrant.convex hi).inter hO

section Lemma3821

variable {C U : Set V} {f g : V → V}

/-- The pointwise step of Lemma 3.8.21: a continuous inverse of a map with invertible derivative
within `U` at `g(y)` is differentiable within `f(U)` at `y`, with `Dg(y) = [Df(g(y))]⁻¹`. -/
theorem hasFDerivWithinAt_inverse_of_isUnit {y : V} (hy : y ∈ f '' U)
    (hg : ContinuousOn g (f '' U)) (hgf : ∀ x ∈ U, g (f x) = x)
    (hfd : HasFDerivWithinAt f (fderivWithin ℝ f U (g y)) U (g y))
    (hu : IsUnit (fderivWithin ℝ f U (g y))) :
    HasFDerivWithinAt g (Ring.inverse (fderivWithin ℝ f U (g y))) (f '' U) y := by
  have hgU : ∀ y' ∈ f '' U, g y' ∈ U := by
    rintro _ ⟨x, hx, rfl⟩; rw [hgf x hx]; exact hx
  have hfg : ∀ y' ∈ f '' U, f (g y') = y' := by
    rintro _ ⟨x, hx, rfl⟩; rw [hgf x hx]
  set u := hu.unit
  let f' : V ≃L[ℝ] V := ContinuousLinearEquiv.unitsEquiv ℝ V u
  have hf' : ((f' : V →L[ℝ] V)) = fderivWithin ℝ f U (g y) := by
    ext v; rfl
  have htend : Tendsto g (𝓝[f '' U] y) (𝓝[U] (g y)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hg y hy, eventually_nhdsWithin_of_forall hgU⟩
  have h := HasFDerivWithinAt.of_local_left_inverse (f' := f') htend (hf' ▸ hfd) hy
    (eventually_nhdsWithin_of_forall hfg)
  have hinv : ((f'.symm : V ≃L[ℝ] V) : V →L[ℝ] V) = Ring.inverse (fderivWithin ℝ f U (g y)) := by
    rw [← IsUnit.unit_spec hu, Ring.inverse_unit]
    ext v; rfl
  rwa [hinv] at h

/-- The derivative family `y ↦ [Df(g(y))]⁻¹` of the inverse is `C^i` on `f(U)` once `g` is
`C^i` there and `f` is `C^{i+1}` on `U`. -/
theorem contDiffOn_inverse_deriv_comp (hU : UniqueDiffOn ℝ U) {i : ℕ}
    (hf : ContDiffOn ℝ (i + 1 : ℕ) f U) (hgi : ContDiffOn ℝ i g (f '' U))
    (hgf : ∀ x ∈ U, g (f x) = x) (hDf : ∀ x ∈ U, IsUnit (fderivWithin ℝ f U x)) :
    ContDiffOn ℝ i (fun y => Ring.inverse (fderivWithin ℝ f U (g y))) (f '' U) := by
  have hgU : MapsTo g (f '' U) U := by
    rintro _ ⟨x, hx, rfl⟩; rw [hgf x hx]; exact hx
  have hD : ContDiffOn ℝ i (fderivWithin ℝ f U) U :=
    hf.fderivWithin hU (by push_cast; exact le_rfl)
  have hΨ : ContDiffOn ℝ i (fun x => Ring.inverse (fderivWithin ℝ f U x)) U := by
    intro x hx
    have h2 : ContDiffAt ℝ i (Ring.inverse : (V →L[ℝ] V) → (V →L[ℝ] V))
        (((hDf x hx).unit : (V →L[ℝ] V)ˣ) : V →L[ℝ] V) := contDiffAt_ringInverse ℝ _
    rw [IsUnit.unit_spec] at h2
    exact h2.contDiffWithinAt.comp x (hD x hx) (mapsTo_univ _ _)
  exact hΨ.comp hgi hgU

/-- **Lemma 3.8.21 (preprint 3.77), with the regularity of Proposition 3.8.17 (preprint 3.73)**, in
general form: let `U` be relatively open in a partial quadrant `C` of a finite-dimensional `V`,
`f` of class `C^j` (`j ≥ 1`) on `U` with `f(U)` relatively open in `C`, `g` a continuous inverse of
`f : U → f(U)` (so `f : U → f(U)` is a homeomorphism), and `Df(x)` invertible on `U`.  Then `g`
is of class `C^j` on `f(U)`.  (The text derives this for smooth `f` by applying the lemma to the
`T^k f`; here by bootstrapping `Dg = [Df]⁻¹ ∘ g`.) -/
theorem lemma_3_8_21_contDiffOn (hU : IsRelOpenInQuadrant (ScBanach.const V) C U)
    (hV : IsRelOpenInQuadrant (ScBanach.const V) C (f '' U)) {j : ℕ} (hj : 1 ≤ j)
    (hf : ContDiffOn ℝ j f U) (hg : ContinuousOn g (f '' U)) (hgf : ∀ x ∈ U, g (f x) = x)
    (hDf : ∀ x ∈ U, IsUnit (fderivWithin ℝ f U x)) : ContDiffOn ℝ j g (f '' U) := by
  have hUu := hU.uniqueDiffOn_const
  have hVu := hV.uniqueDiffOn_const
  have hgU : ∀ y ∈ f '' U, g y ∈ U := by
    rintro _ ⟨x, hx, rfl⟩; rw [hgf x hx]; exact hx
  have hfd : ∀ x ∈ U, HasFDerivWithinAt f (fderivWithin ℝ f U x) U x := fun x hx =>
    ((hf.differentiableOn (by exact_mod_cast (show j ≠ 0 by omega))) x hx).hasFDerivWithinAt
  have key : ∀ i : ℕ, i ≤ j → ContDiffOn ℝ i g (f '' U) := by
    intro i
    induction i with
    | zero => intro _; exact contDiffOn_zero.2 hg
    | succ i ih =>
      intro hi
      rw [show ((i + 1 : ℕ) : WithTop ℕ∞) = (i : WithTop ℕ∞) + 1 by push_cast; rfl]
      refine (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hVu).2
        ⟨fun hω => absurd hω (by simp), fun y => Ring.inverse (fderivWithin ℝ f U (g y)), ?_,
          fun y hy => hasFDerivWithinAt_inverse_of_isUnit hy hg hgf (hfd _ (hgU y hy))
            (hDf _ (hgU y hy))⟩
      exact contDiffOn_inverse_deriv_comp hUu
        (hf.of_le (by exact_mod_cast (show i + 1 ≤ j by omega))) (ih (by omega)) hgf hDf
  exact key j le_rfl

/-- **Lemma 3.8.21 (preprint 3.77)**, 2021 p. 168, in the general form the proof of Proposition
3.8.17 uses (none of that proposition's hypotheses): `U` relatively open in a partial quadrant `C`
of a finite-dimensional `V`, `f` of class `C¹` on `U` (the text: smooth) with `V' = f(U)`
relatively open in `C`, `f : U → V'` a homeomorphism with inverse `g`, and `Df(x)` invertible
for all `x ∈ U`.  Then `g` is of class `C¹` on `V'` and `Dg(y) = [Df(g(y))]⁻¹` for `y ∈ V'`. -/
theorem lemma_3_8_21 (hU : IsRelOpenInQuadrant (ScBanach.const V) C U)
    (hV : IsRelOpenInQuadrant (ScBanach.const V) C (f '' U))
    (hf : ContDiffOn ℝ 1 f U) (hg : ContinuousOn g (f '' U)) (hgf : ∀ x ∈ U, g (f x) = x)
    (hDf : ∀ x ∈ U, IsUnit (fderivWithin ℝ f U x)) :
    ContDiffOn ℝ 1 g (f '' U) ∧
      ∀ y ∈ f '' U, HasFDerivWithinAt g (Ring.inverse (fderivWithin ℝ f U (g y))) (f '' U) y := by
  have hgU : ∀ y ∈ f '' U, g y ∈ U := by
    rintro _ ⟨x, hx, rfl⟩; rw [hgf x hx]; exact hx
  refine ⟨by exact_mod_cast lemma_3_8_21_contDiffOn hU hV le_rfl (by exact_mod_cast hf) hg hgf hDf,
    fun y hy => hasFDerivWithinAt_inverse_of_isUnit hy hg hgf ?_ (hDf _ (hgU y hy))⟩
  exact ((hf.differentiableOn one_ne_zero) _ (hgU y hy)).hasFDerivWithinAt

/-- **Lemma 3.8.21 with Proposition 3.8.17's conclusion, smooth case**: under the hypotheses of
`lemma_3_8_21` with `f` of class `C^∞` on `U`, the inverse `g` is `C^∞` on `f(U)`, so
`f : U → f(U)` is a diffeomorphism in the sense of Definition 3.8.14. -/
theorem lemma_3_8_21_smooth (hU : IsRelOpenInQuadrant (ScBanach.const V) C U)
    (hV : IsRelOpenInQuadrant (ScBanach.const V) C (f '' U))
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContinuousOn g (f '' U)) (hgf : ∀ x ∈ U, g (f x) = x)
    (hDf : ∀ x ∈ U, IsUnit (fderivWithin ℝ f U x)) : ContDiffOn ℝ ∞ g (f '' U) := by
  rw [contDiffOn_infty] at hf ⊢
  intro k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact contDiffOn_zero.2 hg
  · exact lemma_3_8_21_contDiffOn hU hV hk (hf k) hg hgf hDf

/-- **Lemma 3.8.21 as printed** (2021 p. 168): with the hypotheses of Proposition 3.8.17
(`InvData`, of class `C^j`) added to the lemma's own, the inverse is `C¹` with
`Dg(y) = [Df(g(y))]⁻¹`.  A special case of `lemma_3_8_21`. -/
theorem lemma_3_8_21_printed {j : ℕ} (hd : InvData C U f j)
    (hV : IsRelOpenInQuadrant (ScBanach.const V) C (f '' U))
    (hg : ContinuousOn g (f '' U)) (hgf : ∀ x ∈ U, g (f x) = x)
    (hDf : ∀ x ∈ U, IsUnit (fderivWithin ℝ f U x)) :
    ContDiffOn ℝ 1 g (f '' U) ∧
      ∀ y ∈ f '' U, HasFDerivWithinAt g (Ring.inverse (fderivWithin ℝ f U (g y))) (f '' U) y :=
  lemma_3_8_21 ⟨hd.isPartialQuadrant, hd.relOpen⟩ hV
    (hd.contDiffOn.of_le (by exact_mod_cast hd.one_le)) hg hgf hDf

end Lemma3821

end Polyfold
