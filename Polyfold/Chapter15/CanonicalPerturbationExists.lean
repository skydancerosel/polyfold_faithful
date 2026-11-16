import Polyfold.Chapter15.CollarCobordismCorollary
import Polyfold.Chapter15.RelativeLocalFamilies
import Polyfold.Chapter15.CanonicalOrientationStokes

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, p. 703:
**Corollary 15.4.4** (2017: Corollary 15.2) together with the existence of the perturbations it
is about.

# Corollary 15.4.4: canonically oriented regular perturbations exist

## The text, paraphrased

(p. 703) For an oriented sc-Fredholm section functor `f` of index `m + 1`, the integrals
`∫_{Θ} ω` over `Θ = Λ ∘ f`, `Λ` a regular perturbation in general position with `Θ` carrying the
canonical orientation, do not depend on `Λ` for closed `ω`, and `∫_{Θ} dη = 0`.  The perturbations
come from Corollary 15.3.10 (1).

## What is formalized (namespace `Polyfold.SBLocalization`)

* `isGoodPositionAt_of_isInGeneralPosition`: general position of `(f, Λ)` gives good position at
  every `x` with `Λ(f(x)) > 0`.
* `exists_isRegularPerturbation_isInGeneralPosition`: a regular perturbation `(N, U, Λ)` in
  general position exists (Theorem 12.2.2 for `N`, `exists_controlsCompactness` for `U`,
  Corollary 15.3.10 (1) for `Λ`).
* **`corollary_15_4_4_exists`**: an oriented regular perturbation with the canonical orientation
  of Definition 15.4.2 (`IsCanonicalPerturbation`), in general position, exists.
* **`corollary_15_4_4_wellDefined`**: existence together with the statement of Corollary 15.4.4
  (`corollary_15_4_4_oriented_collar`), with sc-smooth partitions of unity on `X`.

## Reading

The hypotheses are those of `corollary_15_4_4_oriented_collar` together with the compactness of
`|S_f|`, the hypothesis of Corollary 15.3.10 (1) under which regular perturbations exist.  For
`corollary_15_4_4_exists` sc-smooth bump functions (Definition 12.3.1) replace the partitions of
unity; Theorem 7.5.7 gives them from partitions of unity.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP

variable {A : SEP.{u}} {f : A.Obj → A.W}

/-- **General position gives good position** (Definitions 15.3.5, 15.2.4): if `(f, Λ)` is in
general position, `f` is in good position to `Λ` at every `x` with `Λ(f(x)) > 0`. -/
theorem isGoodPositionAt_of_isInGeneralPosition (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ)
    (hgp : IsInGeneralPosition A f Λ) {x : A.Obj} (hpos : 0 < Λ (f x)) :
    IsGoodPositionAt f Λ x :=
  isGoodPositionAt_of_isInGeneralPositionAt hf hft hΛ hpos
    ((isInGeneralPosition_iff_forall_at hf hΛ).1 hgp x hpos)

/-- **Regular perturbations in general position exist** (Theorem 12.2.2, Corollary 15.3.10 (1),
p. 699): for `d_X ≡ 0`, paracompact `|X|`, sc-smooth bump functions and compact `|S_f|` there are
an auxiliary norm `N`, an open `U` with `(N, U)` controlling compactness, and a regular
perturbation `Λ` of `f` for `(N, U)` in general position. -/
theorem exists_isRegularPerturbation_isInGeneralPosition (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (hpara : A.X.HasParacompactOrbitSpace) (hbump : A.X.AdmitsBumpFunctionsPointwise)
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hS : A.E.HasCompactSolutionSetEp f) :
    ∃ (N : A.B.One → ℝ) (U : Set A.Obj) (Λ : A.W → ℚ≥0),
      IsRegularPerturbation A f N U Λ ∧ IsInGeneralPosition A f Λ := by
  obtain ⟨N, hN⟩ := A.theorem_12_2_2 hpara
  obtain ⟨U, hcc⟩ := exists_controlsCompactness hf hS hN
  obtain ⟨Λ, hreg, hgp, -⟩ := corollary_15_3_10_1 hd hpara hbump hf hft hS hcc
  exact ⟨N, U, Λ, hreg, hgp⟩

/-- **Corollary 15.4.4, p. 703, the perturbations exist**: for `d_X ≡ 0`, an oriented
sc-Fredholm section functor `f` (Definitions 6.6.16, 12.5.4) of index `m + 1` at the smooth points
with compact `|S_f|`, paracompact `|X|` and sc-smooth bump functions, there is an oriented regular
perturbation of `f` carrying the canonical orientation of Definition 15.4.2 and in general
position. -/
theorem corollary_15_4_4_exists (hd : ∀ x, A.X.PObj.degIndex x = 0)
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
    ∃ P : OrientedRegularPerturbation A f m,
      IsCanonicalPerturbation hf.2 hsec o P ∧ IsInGeneralPosition A f P.Λ := by
  obtain ⟨N, U, Λ, hreg, hgp⟩ :=
    exists_isRegularPerturbation_isInGeneralPosition hd hpara hbump hf hft hS
  have hX : A.X.IsTame := A.X.isTame_of_degIndex_eq_zero hd
  have hbump' : A.X.PObj.AdmitsBumpFunctions := A.X.theorem_12_3_2_1.1 hbump
  have hgood : ∀ x ∈ A.X.PObj.boundary, 0 < Λ (f x) → IsGoodPositionAt f Λ x :=
    fun x _ hpos => isGoodPositionAt_of_isInGeneralPosition hf hft hreg.2.1.1 hgp hpos
  have hidx' : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)), A.B.IsIndexAt f x (m + 1 : ℕ) :=
    fun x hx => hidx x (mem_smoothSet_of_pos hft hreg.2.1.1 (by exact_mod_cast hx))
  exact ⟨OrientedRegularPerturbation.canonical hX hbump' hf hft hsec o hinv ho hreg hgood hidx',
    isCanonicalPerturbation_canonical hX hbump' hf hft hsec o hinv ho hreg hgood hidx', hgp⟩

/-- **Corollary 15.4.4, p. 703, existence and independence**: under the hypotheses of
`corollary_15_4_4_oriented_collar` and compact `|S_f|`, canonically oriented regular
perturbations in general position exist, `∫_{Θ} dη = 0` for each of them, and `∫_{Θ} ω` is the
same for any two of them for every closed `ω`. -/
theorem corollary_15_4_4_wellDefined (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hsec : A.B.HasScPlusSectionsThrough) (hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy)
    (ho : haveI := paracompactSpace_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_pullback A.B
      IsSectionOrientation f hf.2 o)
    (hinv : A.E.IsOrInvariant hf hsec o)
    {m : ℕ} (hidx : ∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x ((m + 1 : ℕ) : ℤ))
    (hpara : A.X.HasParacompactOrbitSpace) (hPU : A.X.PObj.AdmitsScPartitionsOfUnity)
    (hS : A.E.HasCompactSolutionSetEp f) :
    (∃ P : OrientedRegularPerturbation A f m,
      IsCanonicalPerturbation hf.2 hsec o P ∧ IsInGeneralPosition A f P.Λ) ∧
      corollary_15_4_4_statement A f m (IsCanonicalPerturbation hf.2 hsec o) :=
  ⟨corollary_15_4_4_exists hd hf hft hsec o ho hinv hidx hpara
      (EpGroupoid.admitsBumpFunctionsPointwise_of_hasScPartitionsOfUnity
        (A.X.theorem_7_5_7 hpara hPU)) hS,
    corollary_15_4_4_oriented_collar hd hf hft hsec hsec' o ho hinv hidx hpara hPU⟩

end SBLocalization

end Polyfold
