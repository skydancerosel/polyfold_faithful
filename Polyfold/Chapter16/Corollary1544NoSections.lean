import Polyfold.Chapter15.CollarCobordismUnconditional
import Polyfold.Chapter15.CanonicalOrientationUnconditional
import Polyfold.Chapter15.AdmissibleCobordism
import Polyfold.Chapter16.IndexZeroUnconditional

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, Corollary 15.4.4,
p. 703 (2017: Corollary 15.2).  Numbers and pages are the 2021 text's.

# Corollary 15.4.4 with no hypothesis on sc⁺-sections of the cylinder

The forms of Corollary 15.4.4 with sc-smooth bump functions on `X`
(`Chapter15/CollarCobordismUnconditional`, `CanonicalOrientationUnconditional`,
`AdmissibleCobordism`) take, besides `hbump : A.X.AdmitsBumpFunctionsPointwise`, the hypothesis
`hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough` (sc⁺-sections of the pull-back bundle over
`[0, 1] × X` through every smooth fibre point).  It follows from `hbump`: bump functions on `X`
give bump functions on the object M-polyfold of `X` (Theorem 12.3.2 (1), 2021 p. 579), hence on
`[0, 1] × X` (`admitsBumpFunctions_prod_cube`), hence the sections (Proposition 6.6.3 (4), 2021
p. 263, `MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough`).  The same argument gives
`A.B.HasScPlusSectionsThrough` on `X`.

* `hasScPlusSectionsThrough_cubeSEP_of_bump`, `hasScPlusSectionsThrough_of_bump`.
* **`corollary_15_4_4_oriented_bump`**, **`corollary_15_4_4_eff_oriented_bump`**,
  **`corollary_15_4_4_wellDefined_bump`**: `corollary_15_4_4_oriented_collar_all`,
  `corollary_15_4_4_eff_oriented_collar_all`, `corollary_15_4_4_wellDefined_all` without `hsec'`
  (and, for the effective form, without `hLUCC`, which `isLUC_cubeSEP` gives from `hLUC`).
* `corollary_15_4_4_loc_bump`, `corollary_15_4_4_eff_loc_bump`: the forms for local orientations.
* `integral_eq_of_isTransversalPerturbation_bump`,
  `integralEff_eq_of_isTransversalPerturbation_bump`: the forms over all transversal
  perturbations, with the invariance `hinv` on `X` in place of the invariance on `[0, 1] × X`.

The hypothesis `hsec` (on `X`) stays in the statements because the canonical orientation
(`IsCanonicalPerturbation hf.2 hsec o`) is stated with it; by `hasScPlusSectionsThrough_of_bump`
it is not an additional assumption.

## Hypotheses of the text

Corollary 15.4.4 itself names: `d_X ≡ 0`, `|X|` paracompact, `f` sc-Fredholm with `|S_f|`
compact, `o` an orientation.  It is stated "in view of Corollary 15.3.10", and §15.3 assumes
throughout that `X` admits sc-smooth bump functions (2021 p. 692, "We also assume that X admits
sc-smooth bump functions so that we can construct sc⁺-multisections").  No partitions of unity
are named in Corollary 15.4.4 or Corollary 15.3.10 (Theorem 15.3.9, p. 698, assumes them).  The
forms here assume bump functions and no partitions of unity.

Witnesses: the hypotheses here are a subset of those of `corollary_15_4_4_oriented_collar_all`,
so its witnesses apply (`TrivialIsotropy.corollary_15_4_4_hypotheses_planeZ3`, isotropy `ℤ/3`,
index `1`; applied in `corollary_15_4_4_deRham_planeZ3`).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle MPolyfold EpGroupoid SEP

variable {A : SEP.{u}}

/-- **Sc⁺-sections of the cylinder bundle from bump functions on `X`** (Theorem 12.3.2 (1), 2021
p. 579; Proposition 6.6.3 (4), 2021 p. 263): if `X` admits sc-smooth bump functions, the strong
bundle over `[0, 1] × X` has sc⁺-sections through every smooth point of a fibre over a smooth
point. -/
theorem hasScPlusSectionsThrough_cubeSEP_of_bump (hbump : A.X.AdmitsBumpFunctionsPointwise) :
    (A.cubeSEP 1).B.HasScPlusSectionsThrough := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PMor
  exact MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough
    (admitsBumpFunctions_prod_cube (A.X.theorem_12_3_2_1.1 hbump))

/-- **Sc⁺-sections of `W → X` from bump functions on `X`** (Theorem 12.3.2 (1), 2021 p. 579;
Lemma 5.3.3, 2021 p. 217). -/
theorem hasScPlusSectionsThrough_of_bump (hbump : A.X.AdmitsBumpFunctionsPointwise) :
    A.B.HasScPlusSectionsThrough :=
  MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough (A.X.theorem_12_3_2_1.1 hbump)

variable {f : A.Obj → A.W}

/-- **Corollary 15.4.4 (2021 p. 703; 2017: Corollary 15.2) for an oriented sc-Fredholm section
functor, with sc-smooth bump functions on `X`.**  Let `d_X ≡ 0`, `|X|` paracompact, `X` with
sc-smooth bump functions, and `(f, o)` an oriented sc-Fredholm section functor
(`φ_* o_{s(φ)} = o_{t(φ)}`) with tame germ data and index `m + 1`.  Then exact forms integrate to
`0` over every regular perturbation with the canonical orientation of `(f, o)`, and a closed form
has the same integral over any two of them.  This is `corollary_15_4_4_oriented_collar_all` with
the hypothesis on sc⁺-sections of `[0, 1] × X` derived from `hbump`. -/
theorem corollary_15_4_4_oriented_bump (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy)
    (ho : haveI := paracompactSpace_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_pullback A.B
      IsSectionOrientation f hf.2 o)
    (hinv : A.E.IsOrInvariant hf hsec o)
    {m : ℕ} (hidx : ∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x ((m + 1 : ℕ) : ℤ))
    (hpara : A.X.HasParacompactOrbitSpace) (hbump : A.X.AdmitsBumpFunctionsPointwise) :
    corollary_15_4_4_statement A f m (IsCanonicalPerturbation hf.2 hsec o) :=
  corollary_15_4_4_oriented_collar_all hd hf hft hsec
    (hasScPlusSectionsThrough_cubeSEP_of_bump hbump) o ho hinv hidx hpara hbump

/-- **Corollary 15.4.4, effective version (2021 p. 703), for an oriented sc-Fredholm section
functor, with sc-smooth bump functions on `X`**: `corollary_15_4_4_eff_oriented_collar_all` with
the sc⁺-sections of `[0, 1] × X` derived from `hbump` and (LUC) on `[0, 1] × X` from (LUC) on `X`
(`isLUC_cubeSEP`). -/
theorem corollary_15_4_4_eff_oriented_bump (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy)
    (ho : haveI := paracompactSpace_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_pullback A.B
      IsSectionOrientation f hf.2 o)
    (hinv : A.E.IsOrInvariant hf hsec o)
    {m : ℕ} (hidx : ∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x ((m + 1 : ℕ) : ℤ))
    (hpara : A.X.HasParacompactOrbitSpace) (hbump : A.X.AdmitsBumpFunctionsPointwise)
    (hLUC : A.X.IsLUC) :
    corollary_15_4_4_eff_statement A f m hLUC (IsCanonicalPerturbation hf.2 hsec o) :=
  corollary_15_4_4_eff_oriented_collar_all hd hf hft hsec
    (hasScPlusSectionsThrough_cubeSEP_of_bump hbump) o ho hinv hidx hpara hbump hLUC
    (isLUC_cubeSEP hLUC)

/-- **Corollary 15.4.4, 2021 p. 703, existence and independence, with sc-smooth bump functions on
`X`**: for `d_X ≡ 0`, an oriented sc-Fredholm section functor `f` of index `m + 1` with tame germ
data and compact `|S_f|`, and paracompact `|X|`, canonically oriented regular perturbations in
general position exist, `∫_{Θ} dη = 0` for each of them, and `∫_{Θ} ω` is the same for any two of
them for every closed `ω`.  This is `corollary_15_4_4_wellDefined_all` with the sc⁺-sections of
`[0, 1] × X` derived from `hbump`. -/
theorem corollary_15_4_4_wellDefined_bump (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy)
    (ho : haveI := paracompactSpace_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_pullback A.B
      IsSectionOrientation f hf.2 o)
    (hinv : A.E.IsOrInvariant hf hsec o)
    {m : ℕ} (hidx : ∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x ((m + 1 : ℕ) : ℤ))
    (hpara : A.X.HasParacompactOrbitSpace) (hbump : A.X.AdmitsBumpFunctionsPointwise)
    (hS : A.E.HasCompactSolutionSetEp f) :
    (∃ P : OrientedRegularPerturbation A f m,
      IsCanonicalPerturbation hf.2 hsec o P ∧ IsInGeneralPosition A f P.Λ) ∧
      corollary_15_4_4_statement A f m (IsCanonicalPerturbation hf.2 hsec o) :=
  corollary_15_4_4_wellDefined_all hd hf hft hsec (hasScPlusSectionsThrough_cubeSEP_of_bump hbump)
    o ho hinv hidx hpara hbump hS

/-- **Corollary 15.4.4 (2021 p. 703) for an orientation given by local orientations (Definition
12.5.4 read locally), with sc-smooth bump functions on `X`**: `corollary_15_4_4_loc_all` with the
sc⁺-sections of `[0, 1] × X` derived from `hbump`. -/
theorem corollary_15_4_4_loc_bump (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (hF : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hsec : A.B.HasScPlusSectionsThrough)
    (hpara : A.X.HasParacompactOrbitSpace) (hbump : A.X.AdmitsBumpFunctionsPointwise)
    (oL : ∀ y (hy : y ∈ A.X.PObj.smoothSet), OrxLoc hft y hy)
    (hoL : A.E.definition_12_5_4_loc (MPolyfold.isTame_of_degIndex_eq_zero _ hd) hF hft oL)
    {m : ℕ} (hidx : ∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x ((m + 1 : ℕ) : ℤ)) :
    corollary_15_4_4_statement A f m
      (IsCanonicalPerturbation hF.2 hsec (orOfLoc hF hft hsec oL)) :=
  corollary_15_4_4_loc_all hd hF hft hsec (hasScPlusSectionsThrough_cubeSEP_of_bump hbump) hpara
    hbump oL hoL hidx

/-- **Corollary 15.4.4, effective version (2021 p. 703), for local orientations, with sc-smooth
bump functions on `X`**: `corollary_15_4_4_eff_loc_all` with the sc⁺-sections and (LUC) of
`[0, 1] × X` derived. -/
theorem corollary_15_4_4_eff_loc_bump (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (hF : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hsec : A.B.HasScPlusSectionsThrough)
    (hpara : A.X.HasParacompactOrbitSpace) (hbump : A.X.AdmitsBumpFunctionsPointwise)
    (hLUC : A.X.IsLUC)
    (oL : ∀ y (hy : y ∈ A.X.PObj.smoothSet), OrxLoc hft y hy)
    (hoL : A.E.definition_12_5_4_loc (MPolyfold.isTame_of_degIndex_eq_zero _ hd) hF hft oL)
    {m : ℕ} (hidx : ∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x ((m + 1 : ℕ) : ℤ)) :
    corollary_15_4_4_eff_statement A f m hLUC
      (IsCanonicalPerturbation hF.2 hsec (orOfLoc hF hft hsec oL)) :=
  corollary_15_4_4_eff_loc_all hd hF hft hsec (hasScPlusSectionsThrough_cubeSEP_of_bump hbump)
    hpara hbump hLUC (isLUC_cubeSEP hLUC) oL hoL hidx

/-- **Corollary 15.4.4 over all transversal perturbations, with sc-smooth bump functions on `X`**
(2021 p. 703, with the perturbations of Theorem 15.4.3, p. 702): a closed form has the same
integral over the canonically oriented solution sets of any two transversal perturbations.
`integral_eq_of_isTransversalPerturbation` with the sc⁺-sections of `[0, 1] × X` derived from
`hbump` and the invariance of `e ∧ o` on `[0, 1] × X` from `hinv`
(`isOrInvariant_cubeOrientation`). -/
theorem integral_eq_of_isTransversalPerturbation_bump {m : ℕ}
    (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy)
    (ho : haveI := paracompactSpace_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_pullback A.B
      IsSectionOrientation f hf.2 o)
    (hinv : A.E.IsOrInvariant hf hsec o)
    (hidx : ∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x ((m + 1 : ℕ) : ℤ))
    (hpara : A.X.HasParacompactOrbitSpace)
    (hbump : A.X.AdmitsBumpFunctionsPointwise) {S₀ S₁ : OrientedSolution A f m}
    {N₀ N₁ : A.B.One → ℝ} {U₀ U₁ : Set A.Obj}
    (hr₀ : IsTransversalPerturbation A f N₀ U₀ S₀.Λ)
    (hr₁ : IsTransversalPerturbation A f N₁ U₁ S₁.Λ)
    (h₀ : IsCanonicalFor S₀.Λ hf.2 hsec o (m + 1) S₀.T)
    (h₁ : IsCanonicalFor S₁.Λ hf.2 hsec o (m + 1) S₁.T)
    (ω : A.baseEP.epFormsInfty (m + 1)) (hω : A.baseEP.epFormsInftyD (m + 1) ω = 0) :
    S₀.integral ω = S₁.integral ω :=
  integral_eq_of_isTransversalPerturbation hd hf hft hsec
    (hasScPlusSectionsThrough_cubeSEP_of_bump hbump) o ho
    (isOrInvariant_cubeOrientation hf hft hsec (hasScPlusSectionsThrough_cubeSEP_of_bump hbump) o
      hinv) hidx hpara hbump hr₀ hr₁ h₀ h₁ ω hω

/-- **The effective form over all transversal perturbations, with sc-smooth bump functions on
`X`**: `integralEff_eq_of_isTransversalPerturbation` with the sc⁺-sections, the invariance and
(LUC) of `[0, 1] × X` derived. -/
theorem integralEff_eq_of_isTransversalPerturbation_bump {m : ℕ}
    (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy)
    (ho : haveI := paracompactSpace_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_pullback A.B
      IsSectionOrientation f hf.2 o)
    (hinv : A.E.IsOrInvariant hf hsec o)
    (hidx : ∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x ((m + 1 : ℕ) : ℤ))
    (hpara : A.X.HasParacompactOrbitSpace)
    (hbump : A.X.AdmitsBumpFunctionsPointwise) (hLUC : A.X.IsLUC)
    {S₀ S₁ : OrientedSolution A f m} {N₀ N₁ : A.B.One → ℝ} {U₀ U₁ : Set A.Obj}
    (hr₀ : IsTransversalPerturbation A f N₀ U₀ S₀.Λ)
    (hr₁ : IsTransversalPerturbation A f N₁ U₁ S₁.Λ)
    (h₀ : IsCanonicalFor S₀.Λ hf.2 hsec o (m + 1) S₀.T)
    (h₁ : IsCanonicalFor S₁.Λ hf.2 hsec o (m + 1) S₁.T)
    (ω : A.baseEP.epFormsInfty (m + 1)) (hω : A.baseEP.epFormsInftyD (m + 1) ω = 0) :
    S₀.integralEff hLUC ω = S₁.integralEff hLUC ω :=
  integralEff_eq_of_isTransversalPerturbation hd hf hft hsec
    (hasScPlusSectionsThrough_cubeSEP_of_bump hbump) o ho
    (isOrInvariant_cubeOrientation hf hft hsec (hasScPlusSectionsThrough_cubeSEP_of_bump hbump) o
      hinv) hidx hpara hbump hLUC (isLUC_cubeSEP hLUC) hr₀ hr₁ h₀ h₁ ω hω

end SBLocalization

end Polyfold
