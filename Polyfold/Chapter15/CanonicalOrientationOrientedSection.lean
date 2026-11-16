import Polyfold.Chapter15.CanonicalOrientationStokes
import Polyfold.Chapter5.IndexAlongPathsLocalBump
import Polyfold.Chapter6.OrientationBundle

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, §15.4,
pp. 701–703: **Theorem 15.4.1** and **Theorem 15.4.3** (2017: Theorems 15.6, 15.7) for an
oriented sc-Fredholm section functor in the sense of **Definition 12.5.4** (p. 594), and with
the index of `f` given at one point of each sc-smooth path component of the support.

# The canonical orientation for an orientation in the sense of Definition 12.5.4

## The text, paraphrased

(Theorem 15.4.1) For an oriented sc-Fredholm section functor `(f, o)` and an sc⁺-multisection
`Λ` in good position, `Θ = Λ ∘ f` has the canonical orientation.  "Oriented" is Definition
12.5.4: `o` is a section of `O_f → X_∞`, continuous for the topology of Theorem 6.6.17, and
invariant under the morphisms.  The dimension of `Θ` is the Fredholm index of `f`, which the
text treats as one number.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `definition_12_5_4_iff_isOrInvariant_isSectionOrientation`: for a tame `X` with sc-smooth bump
  functions and tame germ data, Definition 12.5.4 for the topology of Theorem 6.6.17 is the pair
  "invariant under the morphisms" (`IsOrInvariant`) and "orientation of `f`" (Definition 6.6.16,
  `IsSectionOrientation`), the two hypotheses of `theorem_15_4_1`.
* **`theorem_15_4_1_of_definition_12_5_4`**, **`theorem_15_4_3_of_definition_12_5_4`**,
  `theorem_15_4_3_eff_of_definition_12_5_4`: Theorems 15.4.1 and 15.4.3 with the single
  hypothesis "`o` is an orientation of `f`" (Definition 12.5.4).
* `isIndexAt_of_scPath`: Proposition 6.2.2 for Definition 6.2.1 with bump functions: the index
  is carried along sc-smooth paths.
* **`theorem_15_4_1_of_index_on_paths`**, **`theorem_15_4_3_of_index_on_paths`**: the same
  theorems when the index `n` is known at one point of each sc-smooth path component meeting the
  support (`hidx₀`: every point of the support is the end `φ(1)` of an sc-smooth path
  `φ : ℝ → X` with `ind(f, φ(0)) = n`), in place of the index at every point of the support.

## Reading

The index hypothesis `hidx₀` speaks of sc-smooth paths in `X`, not of topological components of
`supp(Λ ∘ f)`; Proposition 6.2.2 transports the index along such paths only.  On an sc-smoothly
path-connected `X` (for example a convex subset of a model) one point suffices.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter Module

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid

variable {A : SEP.{u}} {f : A.Obj → A.W} {Λ : A.W → ℚ≥0}

/-! ### Definition 12.5.4 as the hypothesis on `o` -/

/-- **Definition 12.5.4 for the topology of Theorem 6.6.17 is the pair of hypotheses of
Theorem 15.4.1**: `o` is invariant under the morphisms and is an orientation of `f`
(Definition 6.6.16). -/
theorem definition_12_5_4_iff_isOrInvariant_isSectionOrientation (hX : A.X.PObj.IsTame)
    (hbump : A.X.PObj.AdmitsBumpFunctions) (hF : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hF.2 y hy) :
    haveI := paracompactSpace_rn_prod A.X.PObj
    haveI := paracompactSpace_rn_pullback A.B
    haveI := paracompactSpace_rn_rn_prod A.X.PObj
    haveI := paracompactSpace_rn_rn_pullback A.B
    A.E.definition_12_5_4 hF hsec (orTopology (orLocalTransport hX hbump hft hsec)) o ↔
      A.E.IsOrInvariant hF hsec o ∧ IsSectionOrientation f hF.2 o := by
  have := paracompactSpace_rn_prod A.X.PObj
  have := paracompactSpace_rn_pullback A.B
  have := paracompactSpace_rn_rn_prod A.X.PObj
  have := paracompactSpace_rn_rn_pullback A.B
  rw [EpStrongBundle.definition_12_5_4_iff, isSectionOrientation_iff_continuous hX hbump hft hsec o]
  exact And.comm

/-- **Theorem 15.4.1 (2021 p. 702) for an orientation in the sense of Definition 12.5.4**: as
`theorem_15_4_1`, with the one hypothesis that `o` is an orientation of `f` (continuous for the
topology of Theorem 6.6.17 and invariant under the morphisms). -/
theorem theorem_15_4_1_of_definition_12_5_4 (hX : A.X.PObj.IsTame)
    (hbump : A.X.PObj.AdmitsBumpFunctions) (hF : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) (hΛ : IsScPlusMultisection A Λ)
    (hsec : A.B.HasScPlusSectionsThrough) (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hF.2 y hy)
    (hD : haveI := paracompactSpace_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_pullback A.B
      haveI := paracompactSpace_rn_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_rn_pullback A.B
      A.E.definition_12_5_4 hF hsec (orTopology (orLocalTransport hX hbump hft hsec)) o) {n : ℕ}
    (hgp : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)), IsGoodPositionAt f Λ x)
    (hidx : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)), A.B.IsIndexAt f x n) :
    IsCanonicalFor Λ hF.2 hsec o n (canonicalOrientation Λ hF.2 hsec o) := by
  obtain ⟨hinv, ho⟩ :=
    (definition_12_5_4_iff_isOrInvariant_isSectionOrientation hX hbump hF hft hsec o).1 hD
  exact theorem_15_4_1 hX hbump hF hft hΛ hsec o hinv ho hgp hidx

/-- **Theorem 15.4.3 (2021 p. 702) for an orientation in the sense of Definition 12.5.4**: as
`theorem_15_4_3`, with `hD` in place of `hinv`, `ho`. -/
theorem theorem_15_4_3_of_definition_12_5_4 {m : ℕ} (hm : 0 < m) (hX : A.X.PObj.IsTame)
    (hbump : A.X.PObj.AdmitsBumpFunctions) (hPU : A.X.HasScPartitionsOfUnity)
    (hF : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {N : A.B.One → ℝ} {U : Set A.Obj} (hcc : ControlsCompactness A f N U)
    (hΛ : IsScPlusMultisection A Λ) (hdom : domSupp Λ ⊆ U)
    (hN1 : ∀ x, pointwiseNorm N Λ x ≤ 1) (htr : IsTransversal f Λ)
    (hgood : ∀ x ∈ A.X.PObj.boundary, 0 < Λ (f x) → IsGoodPositionAt f Λ x)
    (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hF.2 y hy)
    (hD : haveI := paracompactSpace_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_pullback A.B
      haveI := paracompactSpace_rn_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_rn_pullback A.B
      A.E.definition_12_5_4 hF hsec (orTopology (orLocalTransport hX hbump hft hsec)) o)
    (hidx : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)), A.B.IsIndexAt f x (m + 1 : ℕ)) :
    ∃ hcan : IsCanonicalFor Λ hF.2 hsec o (m + 1) (canonicalOrientation Λ hF.2 hsec o),
      A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)) ∧
      A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ)) ∧
      ∀ (hΘ : A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)))
        (hcpt : A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ))) (ω : A.baseEP.epFormsInfty m),
        (A.baseEP.epFormsInftyEval (m + 1)).tameBranchedIntegral (Nat.succ_pos m) hΘ hcpt
            hcan.1 hcan.loc (A.baseEP.epFormsInftyD m ω) =
          A.baseEP.boundaryMeasure hm hΘ hcpt hcan.1 hcan.loc ω univ := by
  obtain ⟨hinv, ho⟩ :=
    (definition_12_5_4_iff_isOrInvariant_isSectionOrientation hX hbump hF hft hsec o).1 hD
  exact theorem_15_4_3 hm hX hbump hPU hF hft hcc hΛ hdom hN1 htr hgood hsec o hinv ho hidx

/-- **Theorem 15.4.3, effective version (p. 703), for an orientation in the sense of Definition
12.5.4**: as `theorem_15_4_3_eff`, with `hD` in place of `hinv`, `ho`. -/
theorem theorem_15_4_3_eff_of_definition_12_5_4 {m : ℕ} (hm : 0 < m) (hX : A.X.PObj.IsTame)
    (hbump : A.X.PObj.AdmitsBumpFunctions) (hPU : A.X.HasScPartitionsOfUnity)
    (hLUC : A.X.IsLUC) (hF : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) {N : A.B.One → ℝ} {U : Set A.Obj}
    (hcc : ControlsCompactness A f N U) (hΛ : IsScPlusMultisection A Λ) (hdom : domSupp Λ ⊆ U)
    (hN1 : ∀ x, pointwiseNorm N Λ x ≤ 1) (htr : IsTransversal f Λ)
    (hgood : ∀ x ∈ A.X.PObj.boundary, 0 < Λ (f x) → IsGoodPositionAt f Λ x)
    (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hF.2 y hy)
    (hD : haveI := paracompactSpace_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_pullback A.B
      haveI := paracompactSpace_rn_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_rn_pullback A.B
      A.E.definition_12_5_4 hF hsec (orTopology (orLocalTransport hX hbump hft hsec)) o)
    (hidx : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)), A.B.IsIndexAt f x (m + 1 : ℕ)) :
    ∃ hcan : IsCanonicalFor Λ hF.2 hsec o (m + 1) (canonicalOrientation Λ hF.2 hsec o),
      ∀ (hΘ : A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)))
        (hcpt : A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ))) (ω : A.baseEP.epFormsInfty m),
        (A.baseEP.epFormsInftyEval (m + 1)).tameBranchedIntegralEff (Nat.succ_pos m) hΘ hcpt
            hcan.1 (A.baseEP.hloc_hasLUC hLUC hcan.loc) (A.baseEP.epFormsInftyD m ω) =
          A.baseEP.boundaryMeasureEff hm hLUC hΘ hcpt hcan.1 hcan.loc ω univ := by
  obtain ⟨hinv, ho⟩ :=
    (definition_12_5_4_iff_isOrInvariant_isSectionOrientation hX hbump hF hft hsec o).1 hD
  exact theorem_15_4_3_eff hm hX hbump hPU hLUC hF hft hcc hΛ hdom hN1 htr hgood hsec o hinv ho
    hidx

/-! ### The index at one point of each sc-smooth path component -/

/-- **Proposition 6.2.2 for Definition 6.2.1 with bump functions**: if `f` has tame germ data,
`X` has sc-smooth bump functions and `φ : ℝ → X` is sc-smooth, `ind(f, φ(0)) = i` gives
`ind(f, φ(1)) = i` (`proposition_6_2_2_local`, `isIndexAtLocal_iff_isIndexAt`). -/
theorem isIndexAt_of_scPath (hbump : A.X.PObj.AdmitsBumpFunctions)
    (hft : A.B.IsScFredholmSectionTame f) {φ : (Fin 1 → ℝ) → A.Obj}
    (hφ : (rnPolyfold 1).IsScSmoothMap A.X.PObj φ) {i : ℤ} (h0 : A.B.IsIndexAt f (φ 0) i) :
    A.B.IsIndexAt f (φ 1) i := by
  have := paracompactSpace_rn_prod A.X.PObj
  have := paracompactSpace_rn_pullback A.B
  obtain ⟨j, hj⟩ := proposition_6_2_2_local hft hφ
  have hf := hft.toIsScFredholmSection
  have hj0 := (isIndexAtLocal_iff_isIndexAt hbump hf).1 (hj 0)
  have hji : j = i := hj0.unique hf h0
  rw [← hji]
  exact (isIndexAtLocal_iff_isIndexAt hbump hf).1 (hj 1)

/-- **The index on the support from one point of each sc-smooth path component**: if every
point of `supp(Λ ∘ f)` is the end `φ(1)` of an sc-smooth path with `ind(f, φ(0)) = n`, then
`f` has index `n` at every point of the support. -/
theorem isIndexAt_supp_of_paths (hbump : A.X.PObj.AdmitsBumpFunctions)
    (hft : A.B.IsScFredholmSectionTame f) {n : ℕ}
    (hidx₀ : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)), ∃ φ : (Fin 1 → ℝ) → A.Obj,
      (rnPolyfold 1).IsScSmoothMap A.X.PObj φ ∧ φ 1 = x ∧ A.B.IsIndexAt f (φ 0) n) :
    ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)), A.B.IsIndexAt f x n := fun x hx => by
  obtain ⟨φ, hφ, h1, h0⟩ := hidx₀ x hx
  rw [← h1]
  exact isIndexAt_of_scPath hbump hft hφ h0

/-- **Theorem 15.4.1 with the index given on sc-smooth path components**: as
`theorem_15_4_1_of_definition_12_5_4`, with `hidx₀` (index `n` at the start of an sc-smooth path
ending at each point of the support) in place of the index at every point of the support. -/
theorem theorem_15_4_1_of_index_on_paths (hX : A.X.PObj.IsTame)
    (hbump : A.X.PObj.AdmitsBumpFunctions) (hF : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) (hΛ : IsScPlusMultisection A Λ)
    (hsec : A.B.HasScPlusSectionsThrough) (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hF.2 y hy)
    (hD : haveI := paracompactSpace_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_pullback A.B
      haveI := paracompactSpace_rn_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_rn_pullback A.B
      A.E.definition_12_5_4 hF hsec (orTopology (orLocalTransport hX hbump hft hsec)) o) {n : ℕ}
    (hgp : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)), IsGoodPositionAt f Λ x)
    (hidx₀ : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)), ∃ φ : (Fin 1 → ℝ) → A.Obj,
      (rnPolyfold 1).IsScSmoothMap A.X.PObj φ ∧ φ 1 = x ∧ A.B.IsIndexAt f (φ 0) n) :
    IsCanonicalFor Λ hF.2 hsec o n (canonicalOrientation Λ hF.2 hsec o) :=
  theorem_15_4_1_of_definition_12_5_4 hX hbump hF hft hΛ hsec o hD hgp
    (isIndexAt_supp_of_paths hbump hft hidx₀)

/-- **Theorem 15.4.3 with the index given on sc-smooth path components**: as
`theorem_15_4_3_of_definition_12_5_4`, with `hidx₀` in place of `hidx`. -/
theorem theorem_15_4_3_of_index_on_paths {m : ℕ} (hm : 0 < m) (hX : A.X.PObj.IsTame)
    (hbump : A.X.PObj.AdmitsBumpFunctions) (hPU : A.X.HasScPartitionsOfUnity)
    (hF : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {N : A.B.One → ℝ} {U : Set A.Obj} (hcc : ControlsCompactness A f N U)
    (hΛ : IsScPlusMultisection A Λ) (hdom : domSupp Λ ⊆ U)
    (hN1 : ∀ x, pointwiseNorm N Λ x ≤ 1) (htr : IsTransversal f Λ)
    (hgood : ∀ x ∈ A.X.PObj.boundary, 0 < Λ (f x) → IsGoodPositionAt f Λ x)
    (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hF.2 y hy)
    (hD : haveI := paracompactSpace_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_pullback A.B
      haveI := paracompactSpace_rn_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_rn_pullback A.B
      A.E.definition_12_5_4 hF hsec (orTopology (orLocalTransport hX hbump hft hsec)) o)
    (hidx₀ : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)), ∃ φ : (Fin 1 → ℝ) → A.Obj,
      (rnPolyfold 1).IsScSmoothMap A.X.PObj φ ∧ φ 1 = x ∧ A.B.IsIndexAt f (φ 0) (m + 1 : ℕ)) :
    ∃ hcan : IsCanonicalFor Λ hF.2 hsec o (m + 1) (canonicalOrientation Λ hF.2 hsec o),
      A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)) ∧
      A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ)) ∧
      ∀ (hΘ : A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)))
        (hcpt : A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ))) (ω : A.baseEP.epFormsInfty m),
        (A.baseEP.epFormsInftyEval (m + 1)).tameBranchedIntegral (Nat.succ_pos m) hΘ hcpt
            hcan.1 hcan.loc (A.baseEP.epFormsInftyD m ω) =
          A.baseEP.boundaryMeasure hm hΘ hcpt hcan.1 hcan.loc ω univ :=
  theorem_15_4_3_of_definition_12_5_4 hm hX hbump hPU hF hft hcc hΛ hdom hN1 htr hgood hsec o
    hD (isIndexAt_supp_of_paths hbump hft hidx₀)

end SBLocalization

end Polyfold
