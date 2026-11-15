import Polyfold.Chapter15.CanonicalLiftContinuity
import Polyfold.Chapter9.GeneralCorollaries

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, §15.4,
pp. 701–703: **Theorem 15.4.1**, **Definition 15.4.2**, **Theorem 15.4.3** and
**Corollary 15.4.4** (2017: Theorem 15.6, Definition 15.7, Theorem 15.7, Corollary 15.2) with the
canonical orientation.

# The canonical orientation in Stokes' theorem and in the invariants

## The text, paraphrased

(Theorem 15.4.1, Definition 15.4.2) For an oriented sc-Fredholm section functor `(f, o)` and an
sc⁺-multisection `Λ` in good position, `Θ = Λ ∘ f` has the canonical orientation
`T̂_((f, o), Λ)`.  (Theorem 15.4.3) Under (1)–(3), `Θ` with this orientation is a compact, tame,
oriented branched ep⁺-subgroupoid and Stokes' theorem holds.  (Corollary 15.4.4) The integrals
over `(Λ ∘ f, T̂)` for regular perturbations define a map on cohomology.

## What is formalized (namespace `Polyfold.SBLocalization`)

* **`theorem_15_4_1`**: Theorem 15.4.1 in `Ĝr(X)`: for `X` tame with sc-smooth bump functions,
  `f` an sc-Fredholm section functor with tame germ data of index `n` on `supp(Λ ∘ f)`, `o` an
  orientation of `f` (continuous, Definition 6.6.16, and invariant under morphisms,
  Definition 12.5.4) and `(f, Λ)` in good position, `canonicalOrientation` is the canonical
  orientation of `Θ` (`IsCanonicalFor`).  The independence of Theorem 9.2.1 is Chapter 9's
  `hasIndependentTangentSums`.
* `isGoodPositionAt_of_transversal`: (2) and (3) of Theorem 15.4.3 give good position at every
  point of the support.
* **`theorem_15_4_3`**, `theorem_15_4_3_eff`: Theorem 15.4.3 with the canonical orientation: the
  inputs `hT`, `hloc` of `theorem_15_4_3_hyp` are those of `theorem_15_4_1`.
* `OrientedRegularPerturbation.canonical`, `isCanonicalPerturbation_canonical`: a regular
  perturbation with its canonical orientation, an inhabitant of the predicate
  `IsCanonicalPerturbation` (`Can`) of Corollary 15.4.4.
* **`corollary_15_4_4_canonical`**: Corollary 15.4.4 for the canonical orientation, from the
  oriented compact cobordisms between canonically oriented regular perturbations.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter Module

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid

variable {A : SEP.{u}} {f : A.Obj → A.W} {Λ : A.W → ℚ≥0}

/-- **Theorem 15.4.1 (2021 p. 702; 2017: Theorem 15.6) in `Ĝr(X)`**: let `X` be tame with
sc-smooth bump functions, `f` an sc-Fredholm section functor with tame germ data, `o` an
orientation of `f` (Definition 6.6.16, invariant under the morphisms, Definition 12.5.4), and
`Λ` an sc⁺-multisection such that `(f, Λ)` is in good position (Definition 15.2.4) and `f` has
index `n` at every point of `supp(Λ ∘ f)`.  Then `canonicalOrientation` is an orientation of
`Θ = Λ ∘ f` (Definition 9.3.2), represented near every point of the support by the oriented tame
branching structure of the solution sets `Mᵢ = {f = sᵢ}` with `T_yMᵢ = ker (f − sᵢ)'(y)` oriented
by `o` (`IsCanonicalFor`). -/
theorem theorem_15_4_1 (hX : A.X.PObj.IsTame) (hbump : A.X.PObj.AdmitsBumpFunctions)
    (hF : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hΛ : IsScPlusMultisection A Λ) (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hF.2 y hy)
    (hinv : A.E.IsOrInvariant hF hsec o)
    (ho : haveI := paracompactSpace_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_pullback A.B
      IsSectionOrientation f hF.2 o) {n : ℕ}
    (hgp : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)), IsGoodPositionAt f Λ x)
    (hidx : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)), A.B.IsIndexAt f x n) :
    IsCanonicalFor Λ hF.2 hsec o n (canonicalOrientation Λ hF.2 hsec o) :=
  theorem_15_4_1_of_isSectionOrientation hX hbump hF hft hΛ hsec o hinv ho hgp hidx
    (A.X.hasIndependentTangentSums _)

/-- **Good position on the whole support** from (2) and (3) of Theorem 15.4.3: transversality
gives good position at interior points (Remark 15.2.3), and (3) is good position at the boundary
points. -/
theorem isGoodPositionAt_of_transversal (hF : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) (hΛ : IsScPlusMultisection A Λ)
    (htr : IsTransversal f Λ)
    (hgood : ∀ x ∈ A.X.PObj.boundary, 0 < Λ (f x) → IsGoodPositionAt f Λ x) :
    ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)), IsGoodPositionAt f Λ x := fun x hx => by
  have hpos : 0 < Λ (f x) := by exact_mod_cast hx
  by_cases hb : x ∈ A.X.PObj.boundary
  · exact hgood x hb hpos
  · exact isGoodPositionAt_of_interior hF hft hΛ (Nat.lt_one_iff.1 (not_le.1 hb)) (htr x hpos)

/-- **Theorem 15.4.3 (2021 p. 702; 2017: Theorem 15.7) with the canonical orientation**: let `X`
be tame with sc-smooth bump functions and partitions of unity, `f` an sc-Fredholm section
functor with tame germ data of index `m + 1` on `supp(Λ ∘ f)`, `o` an orientation of `f`, and
`Λ` an sc⁺-multisection with (1) `N(Λ) ≤ 1`, dom-supp in `U`, `(N, U)` controlling compactness,
(2) `(f, Λ)` transversal, (3) good position at the points of `∂X ∩ supp(Λ ∘ f)`.  Then
`Θ = Λ ∘ f` is a compact branched ep⁺-subgroupoid, `T̂ = canonicalOrientation` is its canonical
orientation, and `∫_Θ̂ dω = μ^{∂Θ̂}_ω(∂S)` for every `ω ∈ Ωᵐ_{ep,∞}(X)`, `m ≥ 1`. -/
theorem theorem_15_4_3 {m : ℕ} (hm : 0 < m) (hX : A.X.PObj.IsTame)
    (hbump : A.X.PObj.AdmitsBumpFunctions) (hPU : A.X.HasScPartitionsOfUnity)
    (hF : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {N : A.B.One → ℝ} {U : Set A.Obj} (hcc : ControlsCompactness A f N U)
    (hΛ : IsScPlusMultisection A Λ) (hdom : domSupp Λ ⊆ U)
    (hN1 : ∀ x, pointwiseNorm N Λ x ≤ 1) (htr : IsTransversal f Λ)
    (hgood : ∀ x ∈ A.X.PObj.boundary, 0 < Λ (f x) → IsGoodPositionAt f Λ x)
    (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hF.2 y hy)
    (hinv : A.E.IsOrInvariant hF hsec o)
    (ho : haveI := paracompactSpace_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_pullback A.B
      IsSectionOrientation f hF.2 o)
    (hidx : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)), A.B.IsIndexAt f x (m + 1 : ℕ)) :
    ∃ hcan : IsCanonicalFor Λ hF.2 hsec o (m + 1) (canonicalOrientation Λ hF.2 hsec o),
      A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)) ∧
      A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ)) ∧
      ∀ (hΘ : A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)))
        (hcpt : A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ))) (ω : A.baseEP.epFormsInfty m),
        (A.baseEP.epFormsInftyEval (m + 1)).tameBranchedIntegral (Nat.succ_pos m) hΘ hcpt
            hcan.1 hcan.loc (A.baseEP.epFormsInftyD m ω) =
          A.baseEP.boundaryMeasure hm hΘ hcpt hcan.1 hcan.loc ω univ := by
  have hcan := theorem_15_4_1 hX hbump hF hft hΛ hsec o hinv ho
    (isGoodPositionAt_of_transversal hF hft hΛ htr hgood) hidx
  exact ⟨hcan, theorem_15_4_3_hyp hm hPU hF hft hcc hΛ hdom hN1 htr hgood hcan.1 hcan.loc⟩

/-- **Theorem 15.4.3, effective version (p. 703), with the canonical orientation**: with the
local unique continuation property, `∮_Θ̂ dω = ∮_{∂Θ̂} ω`; hypotheses as in `theorem_15_4_3`. -/
theorem theorem_15_4_3_eff {m : ℕ} (hm : 0 < m) (hX : A.X.PObj.IsTame)
    (hbump : A.X.PObj.AdmitsBumpFunctions) (hPU : A.X.HasScPartitionsOfUnity)
    (hLUC : A.X.IsLUC) (hF : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) {N : A.B.One → ℝ} {U : Set A.Obj}
    (hcc : ControlsCompactness A f N U) (hΛ : IsScPlusMultisection A Λ) (hdom : domSupp Λ ⊆ U)
    (hN1 : ∀ x, pointwiseNorm N Λ x ≤ 1) (htr : IsTransversal f Λ)
    (hgood : ∀ x ∈ A.X.PObj.boundary, 0 < Λ (f x) → IsGoodPositionAt f Λ x)
    (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hF.2 y hy)
    (hinv : A.E.IsOrInvariant hF hsec o)
    (ho : haveI := paracompactSpace_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_pullback A.B
      IsSectionOrientation f hF.2 o)
    (hidx : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)), A.B.IsIndexAt f x (m + 1 : ℕ)) :
    ∃ hcan : IsCanonicalFor Λ hF.2 hsec o (m + 1) (canonicalOrientation Λ hF.2 hsec o),
      ∀ (hΘ : A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)))
        (hcpt : A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ))) (ω : A.baseEP.epFormsInfty m),
        (A.baseEP.epFormsInftyEval (m + 1)).tameBranchedIntegralEff (Nat.succ_pos m) hΘ hcpt
            hcan.1 (A.baseEP.hloc_hasLUC hLUC hcan.loc) (A.baseEP.epFormsInftyD m ω) =
          A.baseEP.boundaryMeasureEff hm hLUC hΘ hcpt hcan.1 hcan.loc ω univ := by
  have hcan := theorem_15_4_1 hX hbump hF hft hΛ hsec o hinv ho
    (isGoodPositionAt_of_transversal hF hft hΛ htr hgood) hidx
  exact ⟨hcan, (theorem_15_4_3_eff_hyp hm hPU hLUC hF hft hcc hΛ hdom hN1 htr hgood hcan.1
    hcan.loc).2.2⟩

/-! ### Corollary 15.4.4 with the canonical orientation -/

section Canonical

variable {m : ℕ} (hX : A.X.PObj.IsTame) (hbump : A.X.PObj.AdmitsBumpFunctions)
  (hF : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
  (hsec : A.B.HasScPlusSectionsThrough)
  (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hF.2 y hy) (hinv : A.E.IsOrInvariant hF hsec o)
  (ho : haveI := paracompactSpace_rn_prod A.X.PObj
    haveI := paracompactSpace_rn_pullback A.B
    IsSectionOrientation f hF.2 o)

/-- **A regular perturbation with its canonical orientation** (Definition 15.4.2): for a
structurable regular perturbation `(N, U, Λ)` of an oriented sc-Fredholm section functor
`(f, o)` of index `m + 1` on `supp(Λ ∘ f)`, in good position at the boundary points of the
support, the oriented regular perturbation `(Λ ∘ f, T̂_((f, o), Λ))`. -/
def OrientedRegularPerturbation.canonical {N : A.B.One → ℝ} {U : Set A.Obj}
    (hreg : IsRegularPerturbation A f N U Λ)
    (hgood : ∀ x ∈ A.X.PObj.boundary, 0 < Λ (f x) → IsGoodPositionAt f Λ x)
    (hidx : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)), A.B.IsIndexAt f x (m + 1 : ℕ)) :
    OrientedRegularPerturbation A f m :=
  have hcan := theorem_15_4_1 hX hbump hF hft hreg.2.1.1 hsec o hinv ho
    (isGoodPositionAt_of_transversal hF hft hreg.2.1.1 hreg.2.2.2.2 hgood) hidx
  have hb := theorem_15_4_3_isBranched_hyp hF hft hreg.1 hreg.2.1.1 hreg.2.2.1
    (fun x => (hreg.2.2.2.1 x).le) hreg.2.2.2.2 hgood
  { N := N
    U := U
    Λ := Λ
    isRegular := hreg
    T := canonicalOrientation Λ hF.2 hsec o
    isBranched := hb.1
    isCompact := hb.2
    isOrientation := hcan.1
    loc := hcan.loc }

/-- **The canonically oriented perturbation satisfies the predicate `Can` of Corollary 15.4.4.** -/
theorem isCanonicalPerturbation_canonical {N : A.B.One → ℝ} {U : Set A.Obj}
    (hreg : IsRegularPerturbation A f N U Λ)
    (hgood : ∀ x ∈ A.X.PObj.boundary, 0 < Λ (f x) → IsGoodPositionAt f Λ x)
    (hidx : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)), A.B.IsIndexAt f x (m + 1 : ℕ)) :
    IsCanonicalPerturbation hF.2 hsec o
      (OrientedRegularPerturbation.canonical hX hbump hF hft hsec o hinv ho hreg hgood hidx) :=
  theorem_15_4_1 hX hbump hF hft hreg.2.1.1 hsec o hinv ho
    (isGoodPositionAt_of_transversal hF hft hreg.2.1.1 hreg.2.2.2.2 hgood) hidx

omit hX hbump hft hinv ho in
/-- **Corollary 15.4.4 (2021 p. 703; 2017: Corollary 15.2) for the canonical orientation**: for
`d_X ≡ 0` and `X` with sc-smooth partitions of unity, in every dimension `m + 1 ≥ 1`: exact forms
integrate to `0` over every regular perturbation with the canonical orientation of `(f, o)`, and
a closed form has the same integral over any two of them, provided any two are joined by an
oriented compact cobordism (in the text: `Θ̃ = Λ̃ ∘ f̃` over `[0, 1] × X` from
Corollary 15.3.10 (3) with its canonical orientation). -/
theorem corollary_15_4_4_canonical (hPU : A.X.HasScPartitionsOfUnity)
    (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (hcob : ∀ P₀ P₁ : OrientedRegularPerturbation A f m, IsCanonicalPerturbation hF.2 hsec o P₀ →
      IsCanonicalPerturbation hF.2 hsec o P₁ → P₀.HasOrientedCobordism P₁) :
    corollary_15_4_4_statement A f m (IsCanonicalPerturbation hF.2 hsec o) :=
  corollary_15_4_4_hyp hPU hd _ hcob

end Canonical

end SBLocalization

end Polyfold
