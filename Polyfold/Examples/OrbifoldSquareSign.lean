import Polyfold.Examples.OrbifoldSquareCount
import Polyfold.Examples.SignDimZeroFrames
import Polyfold.Chapter6.ProperHomotopy

/-!
# The orbifold `ℂ/ℤ₅` and the section `z ↦ z²`: the signs of the perturbed zeros

A worked example for Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021),
Theorem 16.6.6, 2021 p. 739, for Fredholm index `0`, with Theorem 15.4.1 (pp. 701–702).

## What is formalized (namespace `Polyfold.Examples.OrbifoldSquare`)

* `sectionAdd_graphSection`, `famSection`, `isScPlusSection_famSection`,
  `pullbackSlice_famSection`: sections of the trivial bundle and the sc⁺-section
  `(t, x) ↦ (x, g(t))` of its pull-back to `ℝᵐ × ℝⁿ`.
* `negConst b`: the constant section `z ↦ (z, −b)`; `bijective_stabT_sqSection`: for `z ≠ 0`,
  `(f − f(z))'(z) = 2z` is an isomorphism, in every chart point.
* `IsPosAt o y`: the orientation `o` is positive at `(f − f(y))'(y)`, `y ≠ 0`;
  **`isPosAt_iff`**: for a continuous orientation, positivity at `y₀ ≠ 0` and at `y₁ ≠ 0` are
  equivalent (`isPosOr_iff_of_path` along `t ↦ y₀ · exp(t w)`).
* `sqOrientationPos`: the continuous orientation which is positive at `(f − f(y))'(y) = 2y` for
  every `y ≠ 0`; `sqOrientationRepPos` (Definition 16.6.5),
  `canonicalGermInput_sqOrientationRepPos`.
* **`positiveZeros_sqOrientationRepPos`**: the perturbed zero `r` of the five-branch
  multisection `Λ5 (r²)` has signed weight `+1/5` for the canonical orientation.
* `exists_canonical_t5_pos`, `count_eq_of_isAdmissible_pos`, `count_t5_pos`: the statements of
  `OrbifoldSquare.lean` and `OrbifoldSquareCount.lean` for `sqOrientationRepPos`.
* **`count_eq_two_fifths`**, `count_eq_two_fifths_all`: every admissible perturbation with the
  canonical orientation has count `2/5` on the constant form `1`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

open scoped ContDiff

noncomputable section

namespace Polyfold.Examples.OrbifoldSquare

open TrivialBundle EpGroupoid EpGroupoid.Examples StrongBundle MPolyfold StrongPolyfoldBundle
  StrongPolyfoldBundleStructure StrongBundleEquivalenceExamples
  StrongBundleLocalizationExamples SBLocalization StrongRetr Linearization15 PolyfoldClass

/-! ### Sections of the trivial bundle -/

section Trivial

variable {n k m : ℕ}

/-- The sum of two graph sections is the graph section of the sum. -/
theorem sectionAdd_graphSection (φ ψ : (Fin n → ℝ) → (Fin k → ℝ)) :
    sectionAdd (proj n k) (graphSection φ) (graphSection ψ) = graphSection (φ + ψ) := by
  funext x
  rw [sectionAdd_apply isSection_graphSection isSection_graphSection]
  exact Prod.ext (fst_fiber _) (snd_add _ _)

/-- The constant section through the `i`-th basis vector of the fibre. -/
def basisSection (n k : ℕ) (i : Fin k) : (Fin n → ℝ) → (Fin n → ℝ) × (Fin k → ℝ) :=
  graphSection fun _ => fun j => if i = j then (1 : ℝ) else 0

/-- **The section `(t, x) ↦ (x, g(t))`** of the pull-back of the trivial bundle `ℝⁿ × ℝᵏ → ℝⁿ`
to `ℝᵐ × ℝⁿ`. -/
def famSection (n : ℕ) (g : (Fin m → ℝ) → (Fin k → ℝ)) :
    (Fin m → ℝ) × (Fin n → ℝ) → pullbackSpace (proj n k) (Prod.snd : (Fin m → ℝ) × _ → _) :=
  reparamSection g (paramComb (basisSection n k) fun _ => isSection_graphSection)
    (isSection_pullbackLift _)

/-- The slices of `famSection g` are the constant sections `x ↦ (x, g(t))`. -/
theorem pullbackSlice_famSection (g : (Fin m → ℝ) → (Fin k → ℝ)) (q : Fin m → ℝ) :
    pullbackSlice (famSection n g) q = graphSection fun _ => g q := by
  funext x
  change ((fiberComb (basisSection n k) (fun _ => isSection_graphSection) (g q, x) :
    proj n k ⁻¹' {x}) : (Fin n → ℝ) × (Fin k → ℝ)) = (x, g q)
  refine Prod.ext (fst_fiber _) ?_
  unfold fiberComb
  have h := map_sum ((fibEquiv x).linearEquiv ℝ)
    (fun i => g q i • (⟨basisSection n k i x, isSection_graphSection x⟩ : proj n k ⁻¹' {x}))
    Finset.univ
  refine h.trans ?_
  simp only [map_smul]
  exact (pi_eq_sum_univ (g q)).symm

/-- **`famSection g` is an sc⁺-section** for a `C^∞` map `g`. -/
theorem isScPlusSection_famSection {g : (Fin m → ℝ) → (Fin k → ℝ)} (hg : ContDiff ℝ ∞ g) :
    haveI := paracompactSpace_rn_prod (rnPolyfold n)
    haveI := paracompactSpace_rn_pullback (bundle n k)
    ((bundle n k).pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m)
      (rnPolyfold n))).IsScPlusSection (famSection n g) := by
  have := paracompactSpace_rn_prod (rnPolyfold n)
  have := paracompactSpace_rn_pullback (bundle n k)
  exact (StrongBundle.isScPlusSection_paramComb (B := bundle n k)
    (fun i : Fin k => isScPlusSection_graphSection contDiff_const)).reparamSmooth hg

end Trivial

/-! ### The isomorphisms `(f − b)'(z) = 2z` -/

/-- The constant section `z ↦ (z, −b)`. -/
def negConst (b : Fin 2 → ℝ) : A5.Obj → A5.W := graphSection fun _ => -b

theorem isScPlusSection_negConst (b : Fin 2 → ℝ) : A5.B.IsScPlusSection (negConst b) :=
  isScPlusSection_graphSection contDiff_const

theorem sectionAdd_negConst (b : Fin 2 → ℝ) :
    sectionAdd A5.P sqSection (negConst b) = graphSection (sq + fun _ => -b) :=
  sectionAdd_graphSection _ _

/-- `(f − b)(z) = 0` iff `z² = b`. -/
theorem isZeroAt_negConst_iff {b x : Fin 2 → ℝ} :
    IsZeroAt A5.P (sectionAdd A5.P sqSection (negConst b)) x ↔ sq x = b := by
  rw [sectionAdd_negConst]
  refine (isZeroAt_graphSection_iff (n := 2) (k := 2)).trans ?_
  change sq x + -b = 0 ↔ _
  rw [add_neg_eq_zero]

theorem isZeroAt_negConst (x : Fin 2 → ℝ) :
    IsZeroAt A5.P (sectionAdd A5.P sqSection (negConst (sq x))) x :=
  isZeroAt_negConst_iff.2 rfl

theorem injective_rot {c : ℂ} (hc : c ≠ 0) : Injective (rot c) := fun a b hab => by
  have h := congrArg (rot c⁻¹) hab
  rwa [← rot_mul, ← rot_mul, inv_mul_cancel₀ hc, rot_one, rot_one] at h

/-- **`(f − b)'(z) = 2z` is an isomorphism for `z ≠ 0`**, in every chart point at `z`. -/
theorem bijective_stabT_sqSection {x : Fin 2 → ℝ} (hx : x ≠ 0) {S : A5.Obj → A5.W}
    (hS : A5.B.IsScPlusSection S) {b : Fin 2 → ℝ} (hSe : S = negConst b)
    (h0 : IsZeroAt A5.P (sectionAdd A5.P sqSection S) x) (p : ChartPoint A5.B x) :
    Bijective (p.stabT isScFredholmSectionFunctor_sqSection.2 hS h0) := by
  subst hSe
  have hf := isScFredholmSectionFunctor_sqSection.2
  let ch : StrongBundleChart A5.X.PObj A5.P := chart (k := 2) x
  have hch : A5.B.IsChart ch := isChart_chart x
  have hz : ch.φ.model.E.toBase 1 (0 : ch.φ.model.E 1) = ch.φ x := by
    rw [map_zero]
    exact (sub_self (show Fin 2 → ℝ from x)).symm
  let p₀ : ChartPoint A5.B x := chartPt ch hch (mem_univ _) 0 hz
  refine ChartPoint.bijective_stabT_of_bijective (p := p₀) p hf hS h0 ?_
  have hc : (2 * cE x) ≠ 0 := mul_ne_zero two_ne_zero fun h => hx (cE.map_eq_zero_iff.1 h)
  have hv : ∀ v : ↥p₀.T, ((p₀.stabT hf hS h0 v : ch.F 0) : Fin 2 → ℝ) =
      rot (2 * cE x) ((v : ch.φ.model.E 0) : Fin 2 → ℝ) := by
    intro v
    have he : (ch.principal (sectionAdd A5.P sqSection (negConst b)) ∘ r ch.R) =
        loc (sq + fun _ => -b) x := by
      rw [sectionAdd_negConst]
      funext u
      rfl
    have hd : HasFDerivAt (sq + fun _ => -b) (rot (2 * cE x)) x :=
      (hasFDerivAt_sq x).add_const (-b)
    change scDeriv ch.U (ch.principal (sectionAdd A5.P sqSection (negConst b)) ∘ r ch.R) 0
      (v : ch.φ.model.E 0) = _
    rw [he]
    exact (congrArg (fun T : (rnSc 2) 0 →L[ℝ] (rnSc 2) 0 => T (v : ch.φ.model.E 0))
      (scDeriv_loc (contDiff_sq.add contDiff_const) x)).trans (DFunLike.congr_fun hd.fderiv _)
  constructor
  · intro v w hvw
    have h := congrArg Subtype.val hvw
    rw [hv, hv] at h
    exact Subtype.ext (injective_rot hc h)
  · intro w
    obtain ⟨v, hv'⟩ := surjective_rot hc ((w : ch.F 0) : Fin 2 → ℝ)
    refine ⟨⟨v, ⟨v, ?_⟩⟩, Subtype.ext ?_⟩
    · exact congrArg (fun T : (rnSc 2) 0 →L[ℝ] (rnSc 2) 0 => T v) (scDeriv_r (k := 2) x)
    · rw [hv]
      exact hv'

/-! ### Positivity at the points `y ≠ 0` -/

/-- **The orientation `o` is positive at `(f − f(y))'(y) = 2y`.** -/
def IsPosAt (o : ∀ a (hs : a ∈ A5.X.PObj.smoothSet),
    Orx (B := A5.B) sqSection isScFredholmSectionFunctor_sqSection.2 a hs) (y : Fin 2 → ℝ) :
    Prop :=
  IsPosOr isScFredholmSectionFunctor_sqSection.2 (mem_smoothSet_A5 y) (o y (mem_smoothSet_A5 y))
    (negConst (sq y)) (isScPlusSection_negConst _) (isZeroAt_negConst y)

/-- **A continuous orientation which is positive at one point `y₀ ≠ 0` is positive at every
point `y₁ ≠ 0`**: `ℂ ∖ {0}` is connected by the paths `t ↦ y₀ · exp(t w)`, along which
`(f − f(γ_t))'(γ_t) = 2γ_t` is an isomorphism (`isPosOr_iff_of_path`). -/
theorem isPosAt_iff
    [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × A5.Obj)]
    [∀ n : ℕ, ParacompactSpace (pullbackSpace A5.P (Prod.snd : (Fin n → ℝ) × A5.Obj → A5.Obj))]
    [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × A5.Obj))]
    [∀ k n : ℕ, ParacompactSpace (pullbackSpace
      (pullbackProj A5.P (Prod.snd : (Fin n → ℝ) × A5.Obj → A5.Obj))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × A5.Obj) → (Fin n → ℝ) × A5.Obj))]
    {o : ∀ a (hs : a ∈ A5.X.PObj.smoothSet),
      Orx (B := A5.B) sqSection isScFredholmSectionFunctor_sqSection.2 a hs}
    (ho : IsContOrOn (orLocalTransport isTame_A5 admitsBumpFunctions_A5
      isScFredholmSectionTame_sqSection hasScPlusSectionsThrough_A5) univ o)
    {y₀ y₁ : Fin 2 → ℝ} (h₀ : y₀ ≠ 0) (h₁ : y₁ ≠ 0) : IsPosAt o y₀ ↔ IsPosAt o y₁ := by
  have hf := isScFredholmSectionFunctor_sqSection.2
  have hc₀ : cE y₀ ≠ 0 := fun h => h₀ (cE.map_eq_zero_iff.1 h)
  have hc₁ : cE y₁ ≠ 0 := fun h => h₁ (cE.map_eq_zero_iff.1 h)
  set w : ℂ := Complex.log (cE y₁ / cE y₀) with hwdef
  have hw : Complex.exp w = cE y₁ / cE y₀ := Complex.exp_log (div_ne_zero hc₁ hc₀)
  let γ : (Fin 1 → ℝ) → (Fin 2 → ℝ) := fun q => cE.symm (cE y₀ * Complex.exp ((q 0 : ℂ) * w))
  have hγd : ContDiff ℝ ∞ γ := by
    refine cE.symm.contDiff.comp (contDiff_const.mul ?_)
    refine (Complex.contDiff_exp (𝕜 := ℝ)).comp ?_
    exact (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ (0 : Fin 1))).mul contDiff_const
  have hγs : (rnPolyfold 1).IsScSmoothMap (rnPolyfold 2) γ := isScSmoothMap_rn_rn_of_contDiff hγd
  have hγ0 : ∀ q, γ q ≠ 0 := fun q h => by
    have h' : cE (γ q) = 0 := by rw [h, map_zero]
    rw [ContinuousLinearEquiv.apply_symm_apply] at h'
    exact mul_ne_zero hc₀ (Complex.exp_ne_zero _) h'
  have hg : ContDiff ℝ ∞ fun q : Fin 1 → ℝ => -sq (γ q) := (contDiff_sq.comp hγd).neg
  have hS := isScPlusSection_famSection (n := 2) hg
  have hslice : ∀ q, pullbackSlice (famSection 2 fun q : Fin 1 → ℝ => -sq (γ q)) q =
      negConst (sq (γ q)) := fun q => pullbackSlice_famSection _ q
  have hzq : ∀ q, IsZeroAt A5.P (sectionAdd A5.P sqSection
      (pullbackSlice (famSection 2 fun q : Fin 1 → ℝ => -sq (γ q)) q)) (γ q) := fun q => by
    exact (congrArg (fun T : A5.Obj → A5.W => IsZeroAt A5.P (sectionAdd A5.P sqSection T) (γ q))
      (hslice q)).mpr (isZeroAt_negConst _)
  have hz : ∀ q : Fin 1 → ℝ, IsZeroAt (pullbackProj A5.P Prod.snd)
      (sectionAdd (pullbackProj A5.P Prod.snd) (paramLift sqSection hf.isScSmooth.1)
        (famSection 2 fun q : Fin 1 → ℝ => -sq (γ q))) (q, γ q) := fun q => by
    refine (isZeroAt_pullback_iff_pullbackSlice (P := A5.P)
      ((isSection_pullbackLift _).sectionAdd hS.1) q (γ q)).2 ?_
    have e := pullbackSlice_sectionAdd_paramLift (P := A5.P) hf.isScSmooth.1 hS.1 q
    exact (congrArg (fun T : A5.Obj → A5.W => IsZeroAt A5.P T (γ q)) e).mpr (hzq q)
  have key := isPosOr_iff_of_path isTame_A5 admitsBumpFunctions_A5
    isScFredholmSectionTame_sqSection hasScPlusSectionsThrough_A5 ho hγs
    (fun _ _ => mem_univ _) hS (Eventually.of_forall hz)
    (fun q _ p h0 => bijective_stabT_sqSection (hγ0 q) _ (hslice q) h0 p)
    (mem_smoothSet_A5 _) (mem_smoothSet_A5 _) (hzq _) (hzq _)
  have e0 : γ (pt1 0) = y₀ := by
    change cE.symm (cE y₀ * Complex.exp (((0 : ℝ) : ℂ) * w)) = y₀
    rw [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one,
      ContinuousLinearEquiv.symm_apply_apply]
  have e1 : γ (pt1 1) = y₁ := by
    change cE.symm (cE y₀ * Complex.exp (((1 : ℝ) : ℂ) * w)) = y₁
    rw [Complex.ofReal_one, one_mul, hw, mul_div_cancel₀ _ hc₀,
      ContinuousLinearEquiv.symm_apply_apply]
  have c0 := isPosOr_congr_pt hf o e0 (mem_smoothSet_A5 _) (mem_smoothSet_A5 _)
    ((hslice (pt1 0)).trans (by rw [e0])) (hS.pullbackSlice _) (isScPlusSection_negConst _)
    (hzq _) (isZeroAt_negConst y₀)
  have c1 := isPosOr_congr_pt hf o e1 (mem_smoothSet_A5 _) (mem_smoothSet_A5 _)
    ((hslice (pt1 1)).trans (by rw [e1])) (hS.pullbackSlice _) (isScPlusSection_negConst _)
    (hzq _) (isZeroAt_negConst y₁)
  exact c0.symm.trans (key.trans c1)

/-! ### The orientation which is positive at the points `y ≠ 0` -/

/-- **`f` has a continuous orientation over `ℂ` which is positive at `(f − 1)'(1) = 2`**: of
the two continuous orientations, exactly one is. -/
theorem exists_isContOrOn_isPosAt :
    haveI := paracompactSpace_rn_prod A5.X.PObj
    haveI := paracompactSpace_rn_pullback A5.B
    haveI := paracompactSpace_rn_rn_prod A5.X.PObj
    haveI := paracompactSpace_rn_rn_pullback A5.B
    ∃ o : ∀ a (hs : a ∈ A5.X.PObj.smoothSet),
        Orx (B := A5.B) sqSection isScFredholmSectionFunctor_sqSection.2 a hs,
      IsContOrOn (orLocalTransport isTame_A5 admitsBumpFunctions_A5
        isScFredholmSectionTame_sqSection hasScPlusSectionsThrough_A5) univ o ∧
      IsPosAt o (cE.symm 1) := by
  have := paracompactSpace_rn_prod A5.X.PObj
  have := paracompactSpace_rn_pullback A5.B
  have := paracompactSpace_rn_rn_prod A5.X.PObj
  have := paracompactSpace_rn_rn_pullback A5.B
  obtain ⟨o, -, -, ho⟩ := exists_isContOrOn_sqSection
  have hf := isScFredholmSectionFunctor_sqSection.2
  have h2 : IsTwoPointed sqSection hf := fun x hs =>
    exists_two_orx hf hs hasScPlusSectionsThrough_A5
  by_cases hp : IsPosAt o (cE.symm 1)
  · exact ⟨o, ho, hp⟩
  · refine ⟨fun y hy => orOther (o y hy), ho.other _ h2, ?_⟩
    have hne : (cE.symm (1 : ℂ) : Fin 2 → ℝ) ≠ 0 := fun h =>
      one_ne_zero (cE.symm.map_eq_zero_iff.1 h)
    have hs := mem_smoothSet_A5 (cE.symm (1 : ℂ))
    have hall : ∀ a : Orx (B := A5.B) sqSection hf (cE.symm (1 : ℂ)) hs,
        a = o _ hs ∨ a = orOther (o _ hs) := fun a => by
      by_cases h : a = o _ hs
      · exact Or.inl h
      · exact Or.inr ((eq_orOther_iff h2 _ _).2 h)
    have hb := bijective_stabT_sqSection hne (isScPlusSection_negConst _) rfl
      (isZeroAt_negConst _)
      (chartPtOf (orChart A5.B (cE.symm (1 : ℂ))) (isChart_orChart _) (mem_orChart _) hs)
    rcases ChartPoint.isPos_or_isPos (ChartPoint.stabT_mem_linSet _ hf
      (isScPlusSection_negConst _) (isZeroAt_negConst _) hs) hb hall with h | h
    · exact absurd h hp
    · exact h

/-- **The orientation of `f` which is positive at the points `y ≠ 0`**: the continuous
orientation for which the isomorphisms `(f − f(y))'(y) = 2y` (complex linear) are positive. -/
def sqOrientationPos : ∀ a (hs : a ∈ A5.X.PObj.smoothSet),
    Orx (B := A5.B) sqSection isScFredholmSectionFunctor_sqSection.2 a hs :=
  exists_isContOrOn_isPosAt.choose

theorem isContOrOn_sqOrientationPos :
    haveI := paracompactSpace_rn_prod A5.X.PObj
    haveI := paracompactSpace_rn_pullback A5.B
    haveI := paracompactSpace_rn_rn_prod A5.X.PObj
    haveI := paracompactSpace_rn_rn_pullback A5.B
    IsContOrOn (orLocalTransport isTame_A5 admitsBumpFunctions_A5
      isScFredholmSectionTame_sqSection hasScPlusSectionsThrough_A5) univ sqOrientationPos :=
  exists_isContOrOn_isPosAt.choose_spec.1

/-- **`sqOrientationPos` is positive at every `y ≠ 0`.** -/
theorem isPosAt_sqOrientationPos {y : Fin 2 → ℝ} (hy : y ≠ 0) : IsPosAt sqOrientationPos y := by
  have := paracompactSpace_rn_prod A5.X.PObj
  have := paracompactSpace_rn_pullback A5.B
  have := paracompactSpace_rn_rn_prod A5.X.PObj
  have := paracompactSpace_rn_rn_pullback A5.B
  have hne : (cE.symm (1 : ℂ) : Fin 2 → ℝ) ≠ 0 := fun h =>
    one_ne_zero (cE.symm.map_eq_zero_iff.1 h)
  exact (isPosAt_iff isContOrOn_sqOrientationPos hne hy).1
    exists_isContOrOn_isPosAt.choose_spec.2

/-- **`sqOrientationPos` is an orientation in the sense of Definition 12.5.4.** -/
theorem definition_12_5_4_sqOrientationPos :
    haveI := paracompactSpace_rn_prod A5.X.PObj
    haveI := paracompactSpace_rn_pullback A5.B
    haveI := paracompactSpace_rn_rn_prod A5.X.PObj
    haveI := paracompactSpace_rn_rn_pullback A5.B
    A5.E.definition_12_5_4 isScFredholmSectionFunctor_sqSection hasScPlusSectionsThrough_A5
      (orTopology (orLocalTransport isTame_A5 admitsBumpFunctions_A5
        isScFredholmSectionTame_sqSection hasScPlusSectionsThrough_A5)) sqOrientationPos := by
  have := paracompactSpace_rn_prod A5.X.PObj
  have := paracompactSpace_rn_pullback A5.B
  have := paracompactSpace_rn_rn_prod A5.X.PObj
  have := paracompactSpace_rn_rn_pullback A5.B
  refine ⟨?_, isOrInvariant_of_isContOrOn isContOrOn_sqOrientationPos⟩
  let := orTopology (orLocalTransport isTame_A5 admitsBumpFunctions_A5
    isScFredholmSectionTame_sqSection hasScPlusSectionsThrough_A5)
  have h := continuousOn_orSec isContOrOn_sqOrientationPos
  rw [preimage_univ] at h
  exact continuousOn_univ.1 h

/-- **The orientation `sqOrientationPos` of the sc-Fredholm section `|z| ↦ |(z, z²)|` over
`ℂ/ℤ₅`** (Definition 16.6.5). -/
def sqOrientationRepPos : OrientationRep sqFredholmSection where
  a := sqRep
  ha := rfl
  hF := isScFredholmSectionFunctor_sqSection
  hsec := hasScPlusSectionsThrough_A5
  t := haveI := paracompactSpace_rn_prod A5.X.PObj
    haveI := paracompactSpace_rn_pullback A5.B
    haveI := paracompactSpace_rn_rn_prod A5.X.PObj
    haveI := paracompactSpace_rn_rn_pullback A5.B
    orTopology (orLocalTransport isTame_A5 admitsBumpFunctions_A5
      isScFredholmSectionTame_sqSection hasScPlusSectionsThrough_A5)
  isOrientationTopology := isOrientationTopology_sqSection
  o := sqOrientationPos
  isOrientation := definition_12_5_4_sqOrientationPos

/-- **The standing hypotheses of Theorem 16.6.6 (2021 p. 739) for index `0` hold in the model
of `sqOrientationRepPos`.** -/
theorem canonicalGermInput_sqOrientationRepPos : CanonicalGermInput sqOrientationRepPos 0 :=
  ⟨isScFredholmSectionTame_sqSection, fun x _ => by exact_mod_cast isIndexAt_sqSection x⟩

/-! ### The signs of the perturbed zeros -/

/-- `f − s_j = f + (−s_j)` for the constant section through `b`. -/
theorem subSec_graphSection_const (b : Fin 2 → ℝ) :
    subSec (A := A5) sqSection (graphSection fun _ => b) univ =
      sectionAdd A5.P sqSection (negConst b) := by
  have hsec : IsSection A5.P (graphSection (n := 2) (k := 2) fun _ => b) := isSection_graphSection
  have he : extendZero (A := A5) univ (graphSection fun _ => b) = graphSection fun _ => b :=
    funext fun y => (extendZero_eqOn (A := A5) (fun y _ => hsec y) (mem_univ y)).symm
  unfold subSec
  rw [he]
  congr 1
  funext x
  rw [sectionSmul_apply hsec]
  refine Prod.ext (fst_fiber _) ?_
  refine (snd_smul _ _).trans ?_
  change (-1 : ℝ) • b = -b
  rw [neg_one_smul]

/-- `z ↦ z²` and the branch `j = 0`: `r² = ζ⁰ r²`. -/
theorem sq_symm_eq_branchVal_zero (r : ℂ) : sq (cE.symm r) = branchVal (r ^ 2) 0 := by
  apply cE.injective
  rw [cE_sq, cE_branchVal, ContinuousLinearEquiv.apply_symm_apply]
  have h1 : (Multiplicative.ofAdd (0 : ZMod 5)) = 1 := rfl
  rw [h1, χ_one, one_pow, one_mul]

/-- **The perturbed zero `r` of `z² − ζ^{2j} r²` has signed weight `+1/5`** for the canonical
orientation of `(f, sqOrientationPos)`: `sqOrientationPos` is positive at `(f − r²)'(r) = 2r`
(`IsCanonicalFor.signedWeight_eq`), and exactly one of the five branches passes through `r`. -/
theorem signedWeight_canonical_eq {r : ℂ} (hr : r ≠ 0)
    {T : A5.Obj → A5.X.PObj.OrTangent →₀ ℚ}
    (h : IsCanonicalFor (Λ5 (r ^ 2)) sqOrientationRepPos.hF.2 sqOrientationRepPos.hsec
      sqOrientationRepPos.o 0 T) :
    signedWeight (X := X5) (T (cE.symm r)) = 1 / 5 := by
  have hf := isScFredholmSectionFunctor_sqSection.2
  have hc : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have hy0 : (cE.symm r : Fin 2 → ℝ) ≠ 0 := fun h0 => hr (cE.symm.map_eq_zero_iff.1 h0)
  have hsq := sq_symm_eq_branchVal_zero r
  have hpos : 0 < Λ5 (r ^ 2) (sqSection (cE.symm r)) :=
    (Λ5_sqSection_pos_iff (r ^ 2) (cE.symm r)).2 ⟨0, hsq⟩
  have hy : (cE.symm r : A5.Obj) ∈
      EpGroupoid.supp (fun z : A5.Obj => ((Λ5 (r ^ 2) (sqSection z) : ℚ≥0) : ℚ)) := by
    change (0 : ℚ) < _
    exact_mod_cast hpos
  have hys := mem_smoothSet_A5 (cE.symm r)
  have key := IsCanonicalFor.signedWeight_eq h hy hys isOpen_univ (mem_univ _)
    (isLocalRepOn_Λ5 (r ^ 2)) (fun j : Fin 5 => negConst (branchVal (r ^ 2) j))
    (fun j => isScPlusSection_negConst _)
    (fun j x' _ => congrFun (subSec_graphSection_const (branchVal (r ^ 2) j)).symm x')
    (fun j hj => by
      have e : sq (cE.symm r) = branchVal (r ^ 2) j :=
        (sqSection_eq_branch_iff (r ^ 2) j (cE.symm r)).1 hj.symm
      refine ⟨isZeroAt_negConst_iff.2 e, ?_⟩
      exact (isPosOr_congr hf hys _ (congrArg negConst e) (isScPlusSection_negConst _)
        (isScPlusSection_negConst _) (isZeroAt_negConst _) (isZeroAt_negConst_iff.2 e)).1
        (isPosAt_sqOrientationPos hy0))
  have e : Λ5 (r ^ 2) (sqSection (cE.symm r)) = 1 / 5 := by
    rw [Λ5_sqSection_eq hc, if_pos ⟨0, hsq⟩]
  refine key.trans ?_
  change (((Λ5 (r ^ 2) (sqSection (cE.symm r)) : ℚ≥0) : ℚ) : ℝ) = 1 / 5
  rw [e]
  norm_num

/-- **The perturbed zeros are positive for `sqOrientationRepPos`**: the statement
`PositiveZeros` of `OrbifoldSquareCount.lean`, for the orientation `sqOrientationPos`. -/
theorem positiveZeros_sqOrientationRepPos (P : PointSolution A5 sqSection) (r : ℂ) (hr : r ≠ 0)
    (hΛ : P.Λ = Λ5 (r ^ 2))
    (hcan : IsCanonicalFor P.Λ sqOrientationRepPos.hF.2 sqOrientationRepPos.hsec
      sqOrientationRepPos.o 0 P.T) :
    signedWeight (X := X5) (P.T (cE.symm r)) = 1 / 5 := by
  rw [hΛ] at hcan
  exact signedWeight_canonical_eq hr hcan

/-! ### The count `2/5` -/

/-- **The multisection `λ_c` with five branches is admissible and has a canonically oriented
perturbed solution set for `sqOrientationRepPos`**, for `0 < |c| ≤ 1`. -/
theorem exists_canonical_t5_pos {c : ℂ} (hc0 : c ≠ 0) (hc1 : ‖c‖ ≤ 1) :
    ∃ Q : PointOrientedPerturbation sqFredholmSection.1, Q.t = t5 c ∧
      Q.IsAdmissible n5 (univ : Set A5.X.OrbitSpace) ∧
      IsCanonicalPointSolutionSet sqOrientationRepPos Q :=
  theorem_16_6_6_index_zero_solutionSet_noBumps sqBundle_boundary_eq_empty isAuxNorm_n5
    isOpen_univ controlsCompactness_n5 canonicalGermInput_sqOrientationRepPos (t5 c)
    (isControlledBy_t5 hc1) (isInGeneralPositionWith_t5 hc0)

/-- **The count does not depend on the admissible perturbation** (Theorem 16.6.6, 2021 p. 739,
index `0`), for the orientation `sqOrientationRepPos`. -/
theorem count_eq_of_isAdmissible_pos {Q₀ Q₁ : PointOrientedPerturbation sqFredholmSection.1}
    (a₀ : Q₀.IsAdmissible n5 (univ : Set A5.X.OrbitSpace))
    (c₀ : IsCanonicalPointSolutionSet sqOrientationRepPos Q₀)
    (a₁ : Q₁.IsAdmissible n5 (univ : Set A5.X.OrbitSpace))
    (c₁ : IsCanonicalPointSolutionSet sqOrientationRepPos Q₁)
    (τ : ScForm sqBundle.polyfold 0) (hτ : ScForm.d τ = 0) :
    Q₀.count τ = Q₁.count τ ∧ Q₀.countEff τ = Q₁.countEff τ :=
  theorem_16_6_6_index_zero_count_eq_unconditional sqBundle_boundary_eq_empty isAuxNorm_n5
    isOpen_univ controlsCompactness_n5 canonicalGermInput_sqOrientationRepPos a₀ c₀ a₁ c₁ τ hτ

set_option maxHeartbeats 1600000 in
-- the model of the orientation is unfolded to `A5`
/-- **The count of the five-branch multisection as a sum over its two orbits** (Definition
9.5.6 (1) for `n = 0`): for `r ≠ 0`, a perturbed solution set `Q` of `λ_{r²}` with the canonical
orientation of `(f, o)`, `o = sqOrientationPos`, is the class of a point solution set `(Λ, T̂)`
of the model with `Λ = Λ5 (r²)` and `T̂` canonical, and its count of a `0`-form `τ` is
`signedWeight (T̂ r) · τ(r) + signedWeight (T̂ (−r)) · τ(−r)`. -/
theorem count_t5_pos {r : ℂ} (hr : r ≠ 0) {Q : PointOrientedPerturbation sqFredholmSection.1}
    (ht : Q.t = t5 (r ^ 2)) (hcan : IsCanonicalPointSolutionSet sqOrientationRepPos Q)
    (τ : ScForm sqBundle.polyfold 0) :
    ∃ P : PointSolution A5 sqSection, P.Λ = Λ5 (r ^ 2) ∧
      IsCanonicalFor P.Λ sqOrientationRepPos.hF.2 sqOrientationRepPos.hsec
        sqOrientationRepPos.o 0 P.T ∧
      Q.count τ = signedWeight (X := X5) (P.T (cE.symm r)) * sqEval τ (cE.symm r) +
        signedWeight (X := X5) (P.T (cE.symm (-r))) * sqEval τ (cE.symm (-r)) := by
  classical
  obtain ⟨P, hP, rfl⟩ := hcan
  have hΛ : P.Λ = Λ5 (r ^ 2) := by
    have h1 := congrArg ScPlusMultisection.toFun ht
    funext w
    have ca := (ofFunctor sqStructure rfl P.Λ P.isScPlusMultisection).comm w
    have cb := (ofFunctor sqStructure rfl (Λ5 (r ^ 2)) (isScPlusMultisection_Λ5 _)).comm w
    exact ca.symm.trans ((congrFun h1 _).trans cb)
  refine ⟨P, hΛ, hP, ?_⟩
  have hc2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have hne : cE.symm r ≠ cE.symm (-r) := fun h => π_ne_π_neg hr (congrArg X5.π h)
  have hpos : ∀ x ∈ ({(cE.symm r : A5.Obj), (cE.symm (-r) : A5.Obj)} : Finset A5.Obj),
      0 < P.Λ (sqSection x) := by
    intro x hx
    rw [hΛ]
    rcases Finset.mem_insert.1 hx with h | h
    · exact (Λ5_sqSection_pos_iff_orbit r x).2 (Or.inl ⟨1, by rw [h, one_smul]⟩)
    · replace h := Finset.mem_singleton.1 h
      exact (Λ5_sqSection_pos_iff_orbit r x).2 (Or.inr ⟨1, by rw [h, one_smul]⟩)
  have hinj : Set.InjOn A5.X.π
      (↑({(cE.symm r : A5.Obj), (cE.symm (-r) : A5.Obj)} : Finset A5.Obj) : Set A5.Obj) := by
    intro x hx y hy hxy
    rcases Finset.mem_insert.1 (Finset.mem_coe.1 hx) with h | h <;>
      rcases Finset.mem_insert.1 (Finset.mem_coe.1 hy) with h' | h'
    · exact h.trans h'.symm
    · replace h' := Finset.mem_singleton.1 h'
      rw [h, h'] at hxy
      exact absurd hxy (π_ne_π_neg hr)
    · replace h := Finset.mem_singleton.1 h
      rw [h, h'] at hxy
      exact absurd hxy.symm (π_ne_π_neg hr)
    · replace h := Finset.mem_singleton.1 h
      replace h' := Finset.mem_singleton.1 h'
      exact h.trans h'.symm
  have hcov : ∀ y, 0 < P.Λ (sqSection y) →
      ∃ x ∈ ({(cE.symm r : A5.Obj), (cE.symm (-r) : A5.Obj)} : Finset A5.Obj),
        A5.X.π x = A5.X.π y := by
    intro y hy
    rw [hΛ] at hy
    rcases (Λ5_sqSection_pos_iff_orbit r y).1 hy with ⟨g, hg⟩ | ⟨g, hg⟩
    · exact ⟨_, Finset.mem_insert_self _ _,
        (action_π_eq_π_iff isScSmoothMap_smul).2 ⟨g, hg.symm⟩⟩
    · exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
        (action_π_eq_π_iff isScSmoothMap_smul).2 ⟨g, hg.symm⟩⟩
  have hreg : ∀ x ∈ ({(cE.symm r : A5.Obj), (cE.symm (-r) : A5.Obj)} : Finset A5.Obj),
      Nat.card (X5.Isotropy x) = 1 := fun x hx =>
    card_isotropy_of_isRegular (isRegular_of_Λ5_pos hc2 (by rw [← hΛ]; exact hpos x hx))
  refine (count_solutionPointSuborbifold (c := sqBundle) sqOrientationRepPos.a P
    τ).trans ?_
  refine (P.count_eq_sum _ _ hpos hinj hcov).trans ?_
  have key : ∀ x : A5.Obj, Nat.card (X5.Isotropy x) = 1 →
      ((Nat.card (sqOrientationRepPos.a.S.A.X.Isotropy x) : ℕ) : ℝ)⁻¹ *
        (signedWeight (P.T x) * sqOrientationRepPos.a.S.A.baseEP.zeroFormEval
          (ScForm.toStructure sqOrientationRepPos.a.S.toPolyfoldStructure
            (toPolyfoldStructure_mem sqOrientationRepPos.a.hS) τ) x) =
      signedWeight (X := X5) (P.T x) * sqEval τ x := fun x h => by
    have h' : Nat.card (sqOrientationRepPos.a.S.A.X.Isotropy x) = 1 := h
    rw [h', Nat.cast_one, inv_one, one_mul]
    rfl
  let F : A5.Obj → ℝ := fun x =>
    ((Nat.card (sqOrientationRepPos.a.S.A.X.Isotropy x) : ℕ) : ℝ)⁻¹ *
      (signedWeight (P.T x) * sqOrientationRepPos.a.S.A.baseEP.zeroFormEval
        (ScForm.toStructure sqOrientationRepPos.a.S.toPolyfoldStructure
          (toPolyfoldStructure_mem sqOrientationRepPos.a.hS) τ) x)
  have k1 : F (cE.symm r) = signedWeight (X := X5) (P.T (cE.symm r)) * sqEval τ (cE.symm r) :=
    key _ (hreg _ (Finset.mem_insert_self _ _))
  have k2 : F (cE.symm (-r)) =
      signedWeight (X := X5) (P.T (cE.symm (-r))) * sqEval τ (cE.symm (-r)) :=
    key _ (hreg _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
  have hsum : ∑ x ∈ ({(cE.symm r : A5.Obj), (cE.symm (-r) : A5.Obj)} : Finset A5.Obj), F x =
      F (cE.symm r) + F (cE.symm (-r)) := Finset.sum_pair hne
  rw [k1, k2] at hsum
  exact hsum

/-- **The count `2/5`** (Theorem 16.6.6, 2021 p. 739, index `0`): every admissible perturbation
of `|z| ↦ |(z, z²)|` over `ℂ/ℤ₅` with the canonical orientation of `(f, sqOrientationPos)` has
count `2/5` on the constant form `1`: for `λ_1`, two orbits (`1` and `−1`) of weight `1/5`,
trivial isotropy and sign `+1`. -/
theorem count_eq_two_fifths {Q : PointOrientedPerturbation sqFredholmSection.1}
    (a : Q.IsAdmissible n5 (univ : Set A5.X.OrbitSpace))
    (hcan : IsCanonicalPointSolutionSet sqOrientationRepPos Q) : Q.count sqOne = 2 / 5 := by
  obtain ⟨Q₁, ht₁, a₁, c₁⟩ := exists_canonical_t5_pos (c := 1) one_ne_zero (by rw [norm_one])
  have ht : Q₁.t = t5 ((1 : ℂ) ^ 2) := by rw [one_pow]; exact ht₁
  obtain ⟨P, hΛ, hP, hcount⟩ := count_t5_pos one_ne_zero ht c₁ sqOne
  have hΛ' : P.Λ = Λ5 ((-1 : ℂ) ^ 2) := by rw [hΛ]; norm_num
  have w1 := positiveZeros_sqOrientationRepPos P 1 one_ne_zero hΛ hP
  have w2 := positiveZeros_sqOrientationRepPos P (-1) (neg_ne_zero.2 one_ne_zero) hΛ' hP
  rw [(count_eq_of_isAdmissible_pos a hcan a₁ c₁ sqOne d_sqOne).1, hcount, w1, w2, sqEval_sqOne,
    sqEval_sqOne]
  norm_num

/-- **The invariant of `|z| ↦ |(z, z²)|` over `ℂ/ℤ₅` is `2/5`**: admissible perturbations with
the canonical orientation of `(f, sqOrientationPos)` exist (the five-branch multisections `λ_c`,
`0 < |c| ≤ 1`), and every one of them has count `2/5` on the constant form `1`. -/
theorem count_eq_two_fifths_all :
    (∀ c : ℂ, c ≠ 0 → ‖c‖ ≤ 1 → ∃ Q : PointOrientedPerturbation sqFredholmSection.1,
      Q.t = t5 c ∧ Q.IsAdmissible n5 (univ : Set A5.X.OrbitSpace) ∧
      IsCanonicalPointSolutionSet sqOrientationRepPos Q) ∧
    ∀ Q : PointOrientedPerturbation sqFredholmSection.1,
      Q.IsAdmissible n5 (univ : Set A5.X.OrbitSpace) →
      IsCanonicalPointSolutionSet sqOrientationRepPos Q → Q.count sqOne = 2 / 5 :=
  ⟨fun _ hc0 hc1 => exists_canonical_t5_pos hc0 hc1, fun _ a hcan => count_eq_two_fifths a hcan⟩

end Polyfold.Examples.OrbifoldSquare
