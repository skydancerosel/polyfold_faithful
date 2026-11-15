import Polyfold.Chapter15.CanonicalOrientationOrientedSection
import Polyfold.Chapter16.ModelPerturbations
import Polyfold.Chapter16.CanonicalOrientationWitness

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, §15.4,
pp. 701–703: **Definition 15.4.2** and **Corollary 15.4.4** (the integrals over a perturbation
with the canonical orientation), and the half-disc instance of **Theorem 15.4.1** for an
orientation in the sense of **Definition 12.5.4** with the index given at one point.

# The integral over a canonically oriented perturbation depends on `Λ` only

## The text, paraphrased

(Definition 15.4.2) The orientation of `Θ = Λ ∘ f` is the one determined by `(f, o)` and `Λ`.
(Corollary 15.4.4) The integrals `∫_{(Λ ∘ f, T̂)} ω` are those of this orientation; so they
depend on the perturbation `Λ` alone, not on further choices.

## What is formalized

* **`SBLocalization.IsCanonicalPerturbation.integral_eq`**,
  `IsCanonicalPerturbation.integralEff_eq`: two oriented regular perturbations of `f` with the
  canonical orientation of `(f, o)` and the same `Λ` (the auxiliary norms and neighbourhoods may
  differ) have the same integral and the same effective integral of every form
  (`IsCanonicalFor.unique`, `tameBranchedIntegral_congr_orientation`).
* `SBLocalization.integral_canonical_eq`: every such perturbation has the integral of
  `OrientedRegularPerturbation.canonical`.
* Witnesses on the half-disc example (`halfSEP 1 1`, `∂X ≠ ∅`, fibre `ℝ`; namespace
  `Polyfold.HalfSpaceBundle`):
  - `exists_scPath_halfSpace`: any two points of `H = [0, ∞) × ℝᵐ` are joined by an sc-smooth
    path.
  - **`theorem_15_4_1_of_definition_12_5_4_halfSEP`**: Theorem 15.4.1 with the one hypothesis
    Definition 12.5.4 for `halfOrientation`.
  - **`theorem_15_4_1_of_index_on_paths_halfSEP`**: Theorem 15.4.1 from the index `1` at the single
    boundary point `(0, 1)`, carried along sc-smooth paths to the whole half circle.
  - **`integral_eq_of_isCanonicalPerturbation_halfSEP`**: a canonically oriented perturbation
    with boundary in its support, and every canonically oriented perturbation with the same `Λ`
    has its integral.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter Module
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A : SEP.{u}} {f : A.Obj → A.W} {hf : A.B.IsScFredholmSection f}
  {hsec : A.B.HasScPlusSectionsThrough} {o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf y hy}
  {m : ℕ}

/-- **The integral over a canonically oriented perturbation depends on `Λ` only**
(Definition 15.4.2, Corollary 15.4.4): two oriented regular perturbations with the canonical
orientation of `(f, o)` and the same `Λ` give the same `∫_{(Λ ∘ f, T̂)} τ`. -/
theorem IsCanonicalPerturbation.integral_eq {P P' : OrientedRegularPerturbation A f m}
    (h : IsCanonicalPerturbation hf hsec o P) (h' : IsCanonicalPerturbation hf hsec o P')
    (hΛ : P.Λ = P'.Λ) (τ : A.baseEP.epFormsInfty (m + 1)) : P.integral τ = P'.integral τ := by
  obtain ⟨N, U, Λ, hreg, T, hb, hc, hT, hloc⟩ := P
  obtain ⟨N', U', Λ', hreg', T', hb', hc', hT', hloc'⟩ := P'
  change Λ = Λ' at hΛ
  subst hΛ
  exact A.baseEP.tameBranchedIntegral_congr_orientation (Nat.succ_pos m) hb hc hT hT'
    (fun y hy => IsCanonicalFor.unique h h' hy) hloc hloc' τ

/-- **The effective integral over a canonically oriented perturbation depends on `Λ` only**:
as `IsCanonicalPerturbation.integral_eq`, for `∮_{(Λ ∘ f, T̂)} τ`. -/
theorem IsCanonicalPerturbation.integralEff_eq (hLUC : A.X.IsLUC)
    {P P' : OrientedRegularPerturbation A f m}
    (h : IsCanonicalPerturbation hf hsec o P) (h' : IsCanonicalPerturbation hf hsec o P')
    (hΛ : P.Λ = P'.Λ) (τ : A.baseEP.epFormsInfty (m + 1)) :
    P.integralEff hLUC τ = P'.integralEff hLUC τ := by
  obtain ⟨N, U, Λ, hreg, T, hb, hc, hT, hloc⟩ := P
  obtain ⟨N', U', Λ', hreg', T', hb', hc', hT', hloc'⟩ := P'
  change Λ = Λ' at hΛ
  subst hΛ
  exact A.baseEP.tameBranchedIntegralEff_congr_orientation (Nat.succ_pos m) hb hc hT hT'
    (fun y hy => IsCanonicalFor.unique h h' hy) _ _ τ

/-- **Every canonically oriented perturbation has the integral of
`OrientedRegularPerturbation.canonical`** for its `Λ`. -/
theorem integral_canonical_eq {Λ : A.W → ℚ≥0} (hX : A.X.PObj.IsTame)
    (hbump : A.X.PObj.AdmitsBumpFunctions) (hF : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hF.2 y hy) (hinv : A.E.IsOrInvariant hF hsec o)
    (ho : haveI := paracompactSpace_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_pullback A.B
      IsSectionOrientation f hF.2 o)
    {N : A.B.One → ℝ} {U : Set A.Obj} (hreg : IsRegularPerturbation A f N U Λ)
    (hgood : ∀ x ∈ A.X.PObj.boundary, 0 < Λ (f x) → IsGoodPositionAt f Λ x)
    (hidx : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)), A.B.IsIndexAt f x (m + 1 : ℕ))
    {P : OrientedRegularPerturbation A f m} (hP : IsCanonicalPerturbation hF.2 hsec o P)
    (hΛ : P.Λ = Λ) (τ : A.baseEP.epFormsInfty (m + 1)) :
    P.integral τ =
      (OrientedRegularPerturbation.canonical hX hbump hF hft hsec o hinv ho hreg hgood
        hidx).integral τ :=
  hP.integral_eq (isCanonicalPerturbation_canonical hX hbump hF hft hsec o hinv ho hreg hgood
    hidx) hΛ τ

end SBLocalization

namespace HalfSpaceBundle

open SBLocalization StrongBundle StrongRetr MPolyfold EpGroupoid Linearization15

/-- **Any two points of `H = [0, ∞) × ℝᵐ` are joined by an sc-smooth path**:
`t ↦ (1 − χ(t)) x + χ(t) y` with a `C^∞` cut-off `χ` with values in `[0, 1]`, `χ(0) = 0`,
`χ(1) = 1`, stays in the convex set `H`. -/
theorem exists_scPath_halfSpace {m : ℕ} (x y : H m) :
    ∃ φ : (Fin 1 → ℝ) → H m, (rnPolyfold 1).IsScSmoothMap (basePoly m) φ ∧ φ 0 = x ∧ φ 1 = y := by
  have hq : ContDiff ℝ ∞ fun r : Fin 1 → ℝ => Real.smoothTransition (r 0) :=
    Real.smoothTransition.contDiff.comp (contDiff_apply ℝ ℝ (0 : Fin 1))
  set G : (Fin 1 → ℝ) → Pm m := fun r =>
    (1 - Real.smoothTransition (r 0)) • ((x : (halfSpaceSc m) 0) : Pm m) +
      Real.smoothTransition (r 0) • ((y : (halfSpaceSc m) 0) : Pm m) with hGdef
  have hG : ContDiff ℝ ∞ G :=
    ((contDiff_const.sub hq).smul contDiff_const).add (hq.smul contDiff_const)
  have hH : ∀ r, G r ∈ H m := fun r => by
    refine mem_quadrant_one_iff.2 ?_
    have a₀ : 0 ≤ ((x : (halfSpaceSc m) 0) : Pm m).1 0 := mem_quadrant_one_iff.1 x.2
    have a₁ : 0 ≤ ((y : (halfSpaceSc m) 0) : Pm m).1 0 := mem_quadrant_one_iff.1 y.2
    have b₀ : 0 ≤ 1 - Real.smoothTransition (r 0) :=
      sub_nonneg.2 (Real.smoothTransition.le_one _)
    have b₁ : 0 ≤ Real.smoothTransition (r 0) := Real.smoothTransition.nonneg _
    change 0 ≤ (1 - Real.smoothTransition (r 0)) * ((x : (halfSpaceSc m) 0) : Pm m).1 0 +
      Real.smoothTransition (r 0) * ((y : (halfSpaceSc m) 0) : Pm m).1 0
    exact add_nonneg (mul_nonneg b₀ a₀) (mul_nonneg b₁ a₁)
  have z0 : Real.smoothTransition 0 = 0 := Real.smoothTransition.zero_of_nonpos le_rfl
  have z1 : Real.smoothTransition 1 = 1 := Real.smoothTransition.one_of_one_le le_rfl
  refine ⟨fun r => ⟨G r, hH r⟩, isScSmoothMap_rn_halfSpace_of_contDiff hG hH, ?_, ?_⟩
  · refine Subtype.ext ?_
    change G 0 = _
    simp only [hGdef, Pi.zero_apply, z0, sub_zero, one_smul, zero_smul, add_zero]
  · refine Subtype.ext ?_
    change G 1 = _
    simp only [hGdef, Pi.one_apply, z1, sub_self, one_smul, zero_smul, zero_add]

/-- **Theorem 15.4.1 on the half-disc example with the one hypothesis of Definition 12.5.4**:
`halfOrientation` is an orientation of `f` in the sense of Definition 12.5.4
(`definition_12_5_4_halfOrientation`), and `theorem_15_4_1_of_definition_12_5_4` gives the
canonical orientation of the half circle. -/
theorem theorem_15_4_1_of_definition_12_5_4_halfSEP :
    IsCanonicalFor (zeroMultisection (halfSEP 1 1))
      (isScFredholmSectionFunctor_graphSection_halfSEP (k := 1) contDiff_halfDiscMap).2
      (hasScPlusSectionsThrough_halfSEP 1 1) (halfOrientation contDiff_halfDiscMap) 1
      (canonicalOrientation (zeroMultisection (halfSEP 1 1))
        (isScFredholmSectionFunctor_graphSection_halfSEP (k := 1) contDiff_halfDiscMap).2
        (hasScPlusSectionsThrough_halfSEP 1 1) (halfOrientation contDiff_halfDiscMap)) :=
  theorem_15_4_1_of_definition_12_5_4 (isTame_halfSEP 1 1) (admitsBumpFunctions_halfSEP 1 1)
    (isScFredholmSectionFunctor_graphSection_halfSEP contDiff_halfDiscMap)
    (isScFredholmSectionTame_graphSection_halfSEP contDiff_halfDiscMap)
    (isScPlusMultisection_zeroMultisection _) (hasScPlusSectionsThrough_halfSEP 1 1) _
    (definition_12_5_4_halfOrientation contDiff_halfDiscMap) isGoodPositionAt_halfDisc
    fun x _ => isIndexAt_halfDisc x

/-- **Theorem 15.4.1 on the half-disc example from the index at one point**: the index `1` of
`f` is used only at the boundary point `(0, 1)` of the support; sc-smooth paths in `H`
(`exists_scPath_halfSpace`) carry it to every point of the half circle
(`theorem_15_4_1_of_index_on_paths`). -/
theorem theorem_15_4_1_of_index_on_paths_halfSEP :
    IsCanonicalFor (zeroMultisection (halfSEP 1 1))
      (isScFredholmSectionFunctor_graphSection_halfSEP (k := 1) contDiff_halfDiscMap).2
      (hasScPlusSectionsThrough_halfSEP 1 1) (halfOrientation contDiff_halfDiscMap) 1
      (canonicalOrientation (zeroMultisection (halfSEP 1 1))
        (isScFredholmSectionFunctor_graphSection_halfSEP (k := 1) contDiff_halfDiscMap).2
        (hasScPlusSectionsThrough_halfSEP 1 1) (halfOrientation contDiff_halfDiscMap)) :=
  theorem_15_4_1_of_index_on_paths (isTame_halfSEP 1 1) (admitsBumpFunctions_halfSEP 1 1)
    (isScFredholmSectionFunctor_graphSection_halfSEP contDiff_halfDiscMap)
    (isScFredholmSectionTame_graphSection_halfSEP contDiff_halfDiscMap)
    (isScPlusMultisection_zeroMultisection _) (hasScPlusSectionsThrough_halfSEP 1 1) _
    (definition_12_5_4_halfOrientation contDiff_halfDiscMap) isGoodPositionAt_halfDisc
    fun x _ => by
      obtain ⟨φ, hφ, h0, h1⟩ := exists_scPath_halfSpace topPoint x
      exact ⟨φ, hφ, h1, by rw [h0]; exact isIndexAt_halfDisc topPoint⟩

/-- **The integral over a canonically oriented perturbation depends on `Λ` only, on the half-disc
example**: there is a canonically oriented regular perturbation `P` with `Λ` the zero
multisection and a boundary point in its support, and every canonically oriented regular
perturbation with the same `Λ` (for any auxiliary norm and neighbourhood) has the integral of
`P` for every form. -/
theorem integral_eq_of_isCanonicalPerturbation_halfSEP :
    ∃ P : OrientedRegularPerturbation (halfSEP 1 1) halfDiscSection 0,
      P.Λ = zeroMultisection (halfSEP 1 1) ∧
      IsCanonicalPerturbation
        (isScFredholmSectionFunctor_graphSection_halfSEP (k := 1) contDiff_halfDiscMap).2
        (hasScPlusSectionsThrough_halfSEP 1 1) (halfOrientation contDiff_halfDiscMap) P ∧
      (∃ x ∈ (halfSEP 1 1).X.PObj.boundary,
        x ∈ EpGroupoid.supp (fun z => (P.Λ (halfDiscSection z) : ℚ))) ∧
      ∀ P' : OrientedRegularPerturbation (halfSEP 1 1) halfDiscSection 0,
        IsCanonicalPerturbation
          (isScFredholmSectionFunctor_graphSection_halfSEP (k := 1) contDiff_halfDiscMap).2
          (hasScPlusSectionsThrough_halfSEP 1 1) (halfOrientation contDiff_halfDiscMap) P' →
        P'.Λ = zeroMultisection (halfSEP 1 1) → ∀ τ, P'.integral τ = P.integral τ := by
  obtain ⟨P, hΛ, hP, hb⟩ := exists_isCanonicalPerturbation_halfSEP
  exact ⟨P, hΛ, hP, hb, fun P' hP' hΛ' τ => hP'.integral_eq hP (hΛ'.trans hΛ.symm) τ⟩

end HalfSpaceBundle

end Polyfold
