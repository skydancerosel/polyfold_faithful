import Polyfold.Chapter15.CanonicalOrientationStokes
import Polyfold.Chapter15.CollarCobordismCorollary
import Polyfold.Chapter12.LocalOrientationComparisonEp

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, §15.4,
pp. 701–703: **Theorem 15.4.1**, **Definition 15.4.2**, **Theorem 15.4.3** and
**Corollary 15.4.4** for an orientation made with local sc⁺-sections.

# The canonical orientation for an orientation of `f` in the local orientation sets

## The text, paraphrased

`Lin(f, x)` consists of the linearizations `(f − s)'(x)` for sc⁺-sections `s` defined near `x`
with `s(x) = f(x)` (p. 239), and an orientation of `f` (Definition 12.5.4) is a continuous
section of `O_f → X_∞` invariant under the morphisms.  Theorem 15.4.1 attaches to an oriented
`(f, o)` and an sc⁺-multisection `Λ` in good position the canonical orientation of `Λ ∘ f`.

## What is formalized (namespace `Polyfold.SBLocalization`)

The statements of §15.4 take an orientation `o` in the orientation sets `Orx` made with
sc⁺-sections over the whole object space.  Here the input is an orientation `oL` in the local
orientation sets `OrxLoc` (Definition 12.5.4 with local sc⁺-sections,
`EpStrongBundle.definition_12_5_4_loc`, which needs a tame `X` and tame germ data only).  With
sc-smooth bump functions the two kinds of orientation correspond (`orxLocEquiv`,
`definition_12_5_4_iff_loc`), and the statements are proved by passing to the image of `oL`.

* `orOfLoc`: the orientation `x ↦ orxLocEquiv⁻¹ (oL x)` in `Orx`; `orxLocEquiv_orOfLoc`,
  `orOfLoc_orxLocEquiv` (the passage is a bijection).
* **`definition_12_5_4_orOfLoc`**, `isOrInvariant_orOfLoc`, **`isSectionOrientation_orOfLoc`**:
  an orientation in the local sense gives the two hypotheses `hinv`, `ho` of Theorem 15.4.1;
  `definition_12_5_4_loc_of_orientation` is the converse.
* `canonicalOrientationLoc`: Definition 15.4.2 for `oL`.
* **`theorem_15_4_1_loc`**, **`theorem_15_4_3_loc`**, `theorem_15_4_3_eff_loc`: Theorems 15.4.1
  and 15.4.3 with `oL` as input.
* `isCanonicalPerturbation_canonical_loc`: the predicate `Can` of Corollary 15.4.4 is inhabited.
* **`corollary_15_4_4_loc`**, `corollary_15_4_4_eff_loc`: Corollary 15.4.4 for `oL`
  (`d_X ≡ 0`; partitions of unity on the object M-polyfold for Stokes; they also give the bump
  functions used for the passage).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle MPolyfold EpGroupoid

variable {A : SEP.{u}} {f : A.Obj → A.W} {Λ : A.W → ℚ≥0}

section Passage

variable (hX : A.X.PObj.IsTame) (hbump : A.X.PObj.AdmitsBumpFunctions)
  (hF : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
  (hsec : A.B.HasScPlusSectionsThrough)
  (oL : ∀ y (hy : y ∈ A.X.PObj.smoothSet), OrxLoc hft y hy)

/-- **The orientation in `Orx` of an orientation in the local orientation sets**:
`x ↦ orxLocEquiv⁻¹ (oL x)`. -/
def orOfLoc : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hF.2 y hy :=
  fun y hy => (orxLocEquiv hft hsec y hy).symm (oL y hy)

theorem orxLocEquiv_orOfLoc (y : A.Obj) (hy : y ∈ A.X.PObj.smoothSet) :
    orxLocEquiv hft hsec y hy (orOfLoc hF hft hsec oL y hy) = oL y hy :=
  Equiv.apply_symm_apply _ _

/-- The passage is a bijection: `orOfLoc` of the image of `o` is `o`. -/
theorem orOfLoc_orxLocEquiv (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hF.2 y hy) :
    orOfLoc hF hft hsec (fun y hy => orxLocEquiv hft hsec y hy (o y hy)) = o := by
  funext y hy
  exact Equiv.symm_apply_apply _ _

/-- **An orientation in the local sense is an orientation (Definition 12.5.4)** for the
topology of Theorem 6.6.17 made with sc-smooth bump functions. -/
theorem definition_12_5_4_orOfLoc (h : A.E.definition_12_5_4_loc hX hF hft oL) :
    haveI := paracompactSpace_rn_prod A.X.PObj
    haveI := paracompactSpace_rn_pullback A.B
    haveI := paracompactSpace_rn_rn_prod A.X.PObj
    haveI := paracompactSpace_rn_rn_pullback A.B
    A.E.definition_12_5_4 hF hsec (orTopology (orLocalTransport hX hbump hft hsec))
      (orOfLoc hF hft hsec oL) := by
  have := paracompactSpace_rn_prod A.X.PObj
  have := paracompactSpace_rn_pullback A.B
  have := paracompactSpace_rn_rn_prod A.X.PObj
  have := paracompactSpace_rn_rn_pullback A.B
  refine (A.E.definition_12_5_4_iff_loc hF hft hsec hX hbump _).2 ?_
  have e : (fun x hs => orxLocEquiv hft hsec x hs (orOfLoc hF hft hsec oL x hs)) = oL := by
    funext x hs
    exact orxLocEquiv_orOfLoc hF hft hsec oL x hs
  rw [e]
  exact h

include hbump in
/-- The invariance clause of Definition 12.5.4 for `orOfLoc`. -/
theorem isOrInvariant_orOfLoc (h : A.E.definition_12_5_4_loc hX hF hft oL) :
    A.E.IsOrInvariant hF hsec (orOfLoc hF hft hsec oL) :=
  (definition_12_5_4_orOfLoc hX hbump hF hft hsec oL h).2

include hbump in
/-- **An orientation in the local sense gives an orientation of Definition 6.6.16.** -/
theorem isSectionOrientation_orOfLoc (h : A.E.definition_12_5_4_loc hX hF hft oL) :
    haveI := paracompactSpace_rn_prod A.X.PObj
    haveI := paracompactSpace_rn_pullback A.B
    IsSectionOrientation f hF.2 (orOfLoc hF hft hsec oL) := by
  have := paracompactSpace_rn_prod A.X.PObj
  have := paracompactSpace_rn_pullback A.B
  have := paracompactSpace_rn_rn_prod A.X.PObj
  have := paracompactSpace_rn_rn_pullback A.B
  exact (isSectionOrientation_iff_continuous hX hbump hft hsec _).2
    (definition_12_5_4_orOfLoc hX hbump hF hft hsec oL h).1

include hbump in
/-- **The converse**: the image of an orientation `o` of `f` (Definition 6.6.16, invariant under
the morphisms) is an orientation in the local orientation sets. -/
theorem definition_12_5_4_loc_of_orientation
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hF.2 y hy)
    (hinv : A.E.IsOrInvariant hF hsec o)
    (ho : haveI := paracompactSpace_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_pullback A.B
      IsSectionOrientation f hF.2 o) :
    A.E.definition_12_5_4_loc hX hF hft fun y hy => orxLocEquiv hft hsec y hy (o y hy) := by
  have := paracompactSpace_rn_prod A.X.PObj
  have := paracompactSpace_rn_pullback A.B
  have := paracompactSpace_rn_rn_prod A.X.PObj
  have := paracompactSpace_rn_rn_pullback A.B
  exact (A.E.definition_12_5_4_iff_loc hF hft hsec hX hbump o).1
    ⟨(isSectionOrientation_iff_continuous hX hbump hft hsec o).1 ho, hinv⟩

/-- **Definition 15.4.2 for an orientation in the local orientation sets**: the canonical
orientation of `Θ = Λ ∘ f` for `oL`, the one of its image `orOfLoc`. -/
def canonicalOrientationLoc (Λ : A.W → ℚ≥0) := canonicalOrientation Λ hF.2 hsec
  (orOfLoc hF hft hsec oL)

end Passage

/-- **Theorem 15.4.1 (2021 p. 702) for an orientation made with local sc⁺-sections**: `X` tame
with sc-smooth bump functions, `f` an sc-Fredholm section functor with tame germ data of index
`n` on `supp(Λ ∘ f)`, `oL` an orientation of `f` in the sense of Definition 12.5.4 with local
sc⁺-sections, `Λ` an sc⁺-multisection with `(f, Λ)` in good position on the support.  Then
`canonicalOrientationLoc` is the canonical orientation of `Θ = Λ ∘ f`. -/
theorem theorem_15_4_1_loc (hX : A.X.PObj.IsTame) (hbump : A.X.PObj.AdmitsBumpFunctions)
    (hF : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hΛ : IsScPlusMultisection A Λ) (hsec : A.B.HasScPlusSectionsThrough)
    (oL : ∀ y (hy : y ∈ A.X.PObj.smoothSet), OrxLoc hft y hy)
    (hoL : A.E.definition_12_5_4_loc hX hF hft oL) {n : ℕ}
    (hgp : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)), IsGoodPositionAt f Λ x)
    (hidx : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)), A.B.IsIndexAt f x n) :
    IsCanonicalFor Λ hF.2 hsec (orOfLoc hF hft hsec oL) n
      (canonicalOrientationLoc hF hft hsec oL Λ) :=
  theorem_15_4_1 hX hbump hF hft hΛ hsec _ (isOrInvariant_orOfLoc hX hbump hF hft hsec oL hoL)
    (isSectionOrientation_orOfLoc hX hbump hF hft hsec oL hoL) hgp hidx

/-- **Theorem 15.4.3 (2021 p. 702) for an orientation made with local sc⁺-sections**: the
hypotheses of `theorem_15_4_3` with `oL` in place of `(o, hinv, ho)`. -/
theorem theorem_15_4_3_loc {m : ℕ} (hm : 0 < m) (hX : A.X.PObj.IsTame)
    (hbump : A.X.PObj.AdmitsBumpFunctions) (hPU : A.X.HasScPartitionsOfUnity)
    (hF : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {N : A.B.One → ℝ} {U : Set A.Obj} (hcc : ControlsCompactness A f N U)
    (hΛ : IsScPlusMultisection A Λ) (hdom : domSupp Λ ⊆ U)
    (hN1 : ∀ x, pointwiseNorm N Λ x ≤ 1) (htr : IsTransversal f Λ)
    (hgood : ∀ x ∈ A.X.PObj.boundary, 0 < Λ (f x) → IsGoodPositionAt f Λ x)
    (hsec : A.B.HasScPlusSectionsThrough)
    (oL : ∀ y (hy : y ∈ A.X.PObj.smoothSet), OrxLoc hft y hy)
    (hoL : A.E.definition_12_5_4_loc hX hF hft oL)
    (hidx : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)), A.B.IsIndexAt f x (m + 1 : ℕ)) :
    ∃ hcan : IsCanonicalFor Λ hF.2 hsec (orOfLoc hF hft hsec oL) (m + 1)
        (canonicalOrientationLoc hF hft hsec oL Λ),
      A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)) ∧
      A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ)) ∧
      ∀ (hΘ : A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)))
        (hcpt : A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ))) (ω : A.baseEP.epFormsInfty m),
        (A.baseEP.epFormsInftyEval (m + 1)).tameBranchedIntegral (Nat.succ_pos m) hΘ hcpt
            hcan.1 hcan.loc (A.baseEP.epFormsInftyD m ω) =
          A.baseEP.boundaryMeasure hm hΘ hcpt hcan.1 hcan.loc ω univ :=
  theorem_15_4_3 hm hX hbump hPU hF hft hcc hΛ hdom hN1 htr hgood hsec _
    (isOrInvariant_orOfLoc hX hbump hF hft hsec oL hoL)
    (isSectionOrientation_orOfLoc hX hbump hF hft hsec oL hoL) hidx

/-- **Theorem 15.4.3, effective version (p. 703), for an orientation made with local
sc⁺-sections.** -/
theorem theorem_15_4_3_eff_loc {m : ℕ} (hm : 0 < m) (hX : A.X.PObj.IsTame)
    (hbump : A.X.PObj.AdmitsBumpFunctions) (hPU : A.X.HasScPartitionsOfUnity)
    (hLUC : A.X.IsLUC) (hF : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) {N : A.B.One → ℝ} {U : Set A.Obj}
    (hcc : ControlsCompactness A f N U) (hΛ : IsScPlusMultisection A Λ) (hdom : domSupp Λ ⊆ U)
    (hN1 : ∀ x, pointwiseNorm N Λ x ≤ 1) (htr : IsTransversal f Λ)
    (hgood : ∀ x ∈ A.X.PObj.boundary, 0 < Λ (f x) → IsGoodPositionAt f Λ x)
    (hsec : A.B.HasScPlusSectionsThrough)
    (oL : ∀ y (hy : y ∈ A.X.PObj.smoothSet), OrxLoc hft y hy)
    (hoL : A.E.definition_12_5_4_loc hX hF hft oL)
    (hidx : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)), A.B.IsIndexAt f x (m + 1 : ℕ)) :
    ∃ hcan : IsCanonicalFor Λ hF.2 hsec (orOfLoc hF hft hsec oL) (m + 1)
        (canonicalOrientationLoc hF hft hsec oL Λ),
      ∀ (hΘ : A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)))
        (hcpt : A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ))) (ω : A.baseEP.epFormsInfty m),
        (A.baseEP.epFormsInftyEval (m + 1)).tameBranchedIntegralEff (Nat.succ_pos m) hΘ hcpt
            hcan.1 (A.baseEP.hloc_hasLUC hLUC hcan.loc) (A.baseEP.epFormsInftyD m ω) =
          A.baseEP.boundaryMeasureEff hm hLUC hΘ hcpt hcan.1 hcan.loc ω univ :=
  theorem_15_4_3_eff hm hX hbump hPU hLUC hF hft hcc hΛ hdom hN1 htr hgood hsec _
    (isOrInvariant_orOfLoc hX hbump hF hft hsec oL hoL)
    (isSectionOrientation_orOfLoc hX hbump hF hft hsec oL hoL) hidx

/-- **The predicate `Can` of Corollary 15.4.4 is inhabited for an orientation made with local
sc⁺-sections**: a structurable regular perturbation of index `m + 1` in good position at the
boundary points of its support, with the canonical orientation for `oL`. -/
theorem isCanonicalPerturbation_canonical_loc {m : ℕ} (hX : A.X.PObj.IsTame)
    (hbump : A.X.PObj.AdmitsBumpFunctions) (hF : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) (hsec : A.B.HasScPlusSectionsThrough)
    (oL : ∀ y (hy : y ∈ A.X.PObj.smoothSet), OrxLoc hft y hy)
    (hoL : A.E.definition_12_5_4_loc hX hF hft oL) {N : A.B.One → ℝ} {U : Set A.Obj}
    (hreg : IsRegularPerturbation A f N U Λ)
    (hgood : ∀ x ∈ A.X.PObj.boundary, 0 < Λ (f x) → IsGoodPositionAt f Λ x)
    (hidx : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)), A.B.IsIndexAt f x (m + 1 : ℕ)) :
    ∃ P : OrientedRegularPerturbation A f m,
      P.Λ = Λ ∧ IsCanonicalPerturbation hF.2 hsec (orOfLoc hF hft hsec oL) P :=
  ⟨OrientedRegularPerturbation.canonical hX hbump hF hft hsec _
      (isOrInvariant_orOfLoc hX hbump hF hft hsec oL hoL)
      (isSectionOrientation_orOfLoc hX hbump hF hft hsec oL hoL) hreg hgood hidx, rfl,
    isCanonicalPerturbation_canonical hX hbump hF hft hsec _ _ _ hreg hgood hidx⟩

/-- **Corollary 15.4.4 (2021 p. 703) for an orientation made with local sc⁺-sections**: for
`d_X ≡ 0`, `|X|` paracompact and sc-smooth partitions of unity on the object M-polyfold (used
for Stokes on `X` and on `[0, 1] × X`, and giving the bump functions), exact forms integrate to
`0` over every canonically oriented regular perturbation of `(f, oL)`, and a closed form has
the same integral over any two of them. -/
theorem corollary_15_4_4_loc (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (hF : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hsec : A.B.HasScPlusSectionsThrough) (hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough)
    (hpara : A.X.HasParacompactOrbitSpace) (hPU : A.X.PObj.AdmitsScPartitionsOfUnity)
    (oL : ∀ y (hy : y ∈ A.X.PObj.smoothSet), OrxLoc hft y hy)
    (hoL : A.E.definition_12_5_4_loc (MPolyfold.isTame_of_degIndex_eq_zero _ hd) hF hft oL)
    {m : ℕ} (hidx : ∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x ((m + 1 : ℕ) : ℤ)) :
    corollary_15_4_4_statement A f m
      (IsCanonicalPerturbation hF.2 hsec (orOfLoc hF hft hsec oL)) :=
  corollary_15_4_4_oriented_collar hd hF hft hsec hsec' _
    (isSectionOrientation_orOfLoc _ hPU.admitsBumpFunctions hF hft hsec oL hoL)
    (isOrInvariant_orOfLoc _ hPU.admitsBumpFunctions hF hft hsec oL hoL) hidx hpara hPU

/-- **Corollary 15.4.4, effective version (p. 703), for an orientation made with local
sc⁺-sections.** -/
theorem corollary_15_4_4_eff_loc (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (hF : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hsec : A.B.HasScPlusSectionsThrough) (hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough)
    (hpara : A.X.HasParacompactOrbitSpace) (hPU : A.X.PObj.AdmitsScPartitionsOfUnity)
    (hLUC : A.X.IsLUC) (hLUCC : (A.cubeSEP 1).X.IsLUC)
    (oL : ∀ y (hy : y ∈ A.X.PObj.smoothSet), OrxLoc hft y hy)
    (hoL : A.E.definition_12_5_4_loc (MPolyfold.isTame_of_degIndex_eq_zero _ hd) hF hft oL)
    {m : ℕ} (hidx : ∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x ((m + 1 : ℕ) : ℤ)) :
    corollary_15_4_4_eff_statement A f m hLUC
      (IsCanonicalPerturbation hF.2 hsec (orOfLoc hF hft hsec oL)) :=
  corollary_15_4_4_eff_oriented_collar hd hF hft hsec hsec' _
    (isSectionOrientation_orOfLoc _ hPU.admitsBumpFunctions hF hft hsec oL hoL)
    (isOrInvariant_orOfLoc _ hPU.admitsBumpFunctions hF hft hsec oL hoL) hidx hpara hPU hLUC
    hLUCC

end SBLocalization

end Polyfold
