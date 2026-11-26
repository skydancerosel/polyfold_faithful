import Polyfold.Chapter16.Corollary1544NoSections
import Polyfold.Chapter16.IsotropyCircleCobordism

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, Corollary 15.4.4,
p. 703 (2017: Corollary 15.2).  Numbers and pages are the 2021 text's.

# Corollary 15.4.4 as a map on de Rham cohomology

The text states Corollary 15.4.4 as the existence of a well-defined map
`Φ_{(f,o)} : H*_dR(X) → ℝ` with `Φ_{(f,o)}([ω]) = ∫_{(Λ ∘ f, o)} ω` for a regular perturbation,
and, under (LUC), `Φ^eff_{(f,o)}([ω]) = ∮_{(Λ ∘ f, o)} ω`.  Here, degree-wise in the degree `k`
of the Fredholm index (`k = m + 1 ≥ 1`, and `k = 0` with weighted signed counts), with
`H^k_dR(X)` the project's `EP.epDeRham` (`ker d / im d` on `Ω^k_{ep,∞}(X)`):

* `OrientedRegularPerturbation.integral_sub`, `integralEff_sub`: `∫` and `∮` are additive in `ω`.
* `exists_deRham_map`: a family of functionals constant on closed forms differing by an exact
  form, and agreeing on closed forms, descends to one map on `H^k_dR(X)`.
* **`corollary_15_4_4_deRham`** (index `m + 1`) and **`corollary_15_4_4_index_zero_deRham`**
  (index `0`), with the effective halves `corollary_15_4_4_eff_deRham`,
  `corollary_15_4_4_index_zero_eff_deRham`: a canonically oriented regular perturbation
  exists, and there are maps `Φ`, `Φ^eff` (the latter under (LUC)) on `H^k_dR(X)` with
  `Φ([ω]) = ∫_P ω`, `Φ^eff([ω]) = ∮_P ω` for every closed `ω` and every canonically oriented
  regular perturbation `P`.

Hypotheses: those of the text (`d_X ≡ 0`, `|X|` paracompact, `|S_f|` compact, `(f, o)` oriented:
`ho` and the invariance `hinv`, Definitions 6.6.16 and 12.5.4), the Fredholm index (`hidx`),
sc-smooth bump functions on `X` (the standing assumption of §15.3, 2021 p. 692), and tame germ
data (`hft`).  The hypothesis `hsec` is part of the vocabulary of the canonical orientation and
follows from `hbump` (`hasScPlusSectionsThrough_of_bump`).  Witness:
`corollary_15_4_4_deRham_planeZ3`, the hypotheses of `corollary_15_4_4_deRham` for the circle
section over `ℤ/3 × ℝ² ⇉ ℝ²` (isotropy `ℤ/3` acting trivially on the base, index `1`;
`TrivialIsotropy.corollary_15_4_4_hypotheses_planeZ3`, with bump functions from partitions of
unity), where a canonically oriented regular perturbation exists and `Φ_{(f,o)}` is defined.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open MeasureTheory EpGroupoid

variable {A : SEP.{u}} {f : A.Obj → A.W}

namespace OrientedRegularPerturbation

variable {m : ℕ}

/-- `∫_P (ω − ω') = ∫_P ω − ∫_P ω'` (the measure `μ_ω` of Theorem 9.5.4 is linear in `ω`). -/
theorem integral_sub (P : OrientedRegularPerturbation A f m)
    (ω ω' : A.baseEP.epFormsInfty (m + 1)) :
    P.integral (ω - ω') = P.integral ω - P.integral ω' := by
  simp only [integral, FormEval.tameBranchedIntegral, FormEval.concreteBranchedIntegral,
    branchedIntegral]
  rw [LinearMap.map_sub]
  rfl

/-- `∮_P (ω − ω') = ∮_P ω − ∮_P ω'` (Theorem 9.5.5). -/
theorem integralEff_sub (hLUC : A.X.IsLUC) (P : OrientedRegularPerturbation A f m)
    (ω ω' : A.baseEP.epFormsInfty (m + 1)) :
    P.integralEff hLUC (ω - ω') = P.integralEff hLUC ω - P.integralEff hLUC ω' := by
  simp only [integralEff, FormEval.tameBranchedIntegralEff, FormEval.concreteBranchedIntegralEff,
    branchedIntegralEff]
  rw [LinearMap.map_sub]
  rfl

end OrientedRegularPerturbation

/-- **A well-defined map on `H^k_dR(X)`**: if each functional `I P` (for `P` with `Can P`) takes
the same value on two closed forms differing by an exact form, and any two of them agree on
closed forms, there is `Φ : H^k_dR(X) → ℝ` with `Φ([ω]) = I P ω` for every closed `ω` and every
`P` with `Can P`. -/
theorem exists_deRham_map {B : EP.{u}} {k : ℕ} {ι : Type*} (Can : ι → Prop)
    (I : ι → B.epFormsInfty k → ℝ)
    (hcls : ∀ P, Can P → ∀ ω ω' : B.epFormsInfty k, ω - ω' ∈ B.epFormsInftyDRange k →
      I P ω = I P ω')
    (hind : ∀ P₀ P₁, Can P₀ → Can P₁ → ∀ ω : B.epFormsInfty k, B.epFormsInftyD k ω = 0 →
      I P₀ ω = I P₁ ω) :
    ∃ Φ : B.epDeRham k → ℝ, ∀ P, Can P → ∀ (ω : B.epFormsInfty k)
      (hω : ω ∈ LinearMap.ker (B.epFormsInftyD k)), Φ (Submodule.Quotient.mk ⟨ω, hω⟩) = I P ω := by
  by_cases h : ∃ P, Can P
  · obtain ⟨P₀, h₀⟩ := h
    refine ⟨fun c => I P₀ (Function.surjInv (Submodule.Quotient.mk_surjective _) c).1,
      fun P hP ω hω => ?_⟩
    set r := Function.surjInv (Submodule.Quotient.mk_surjective
      ((B.epFormsInftyDRange k).comap (LinearMap.ker (B.epFormsInftyD k)).subtype))
      (Submodule.Quotient.mk ⟨ω, hω⟩) with hr
    have hmk : Submodule.Quotient.mk r = Submodule.Quotient.mk (p :=
        (B.epFormsInftyDRange k).comap (LinearMap.ker (B.epFormsInftyD k)).subtype) ⟨ω, hω⟩ :=
      Function.surjInv_eq _ _
    have hmem := (Submodule.Quotient.eq _).1 hmk
    simp only [Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_sub] at hmem
    exact (hcls P₀ h₀ _ _ hmem).trans (hind P₀ P h₀ hP ω (LinearMap.mem_ker.1 hω))
  · exact ⟨0, fun P hP => absurd ⟨P, hP⟩ h⟩

/-- **Corollary 15.4.4 (2021 p. 703; 2017: Corollary 15.2), in degree `m + 1`, as maps on de Rham
cohomology.**  Let `d_X ≡ 0`, `|X|` paracompact, `X` with sc-smooth bump functions, and `(f, o)`
an oriented sc-Fredholm section functor with tame germ data, compact `|S_f|` and Fredholm index
`m + 1`.  Then a regular perturbation with the canonical orientation of `(f, o)` (Definition
15.4.2) exists, and there is `Φ_{(f,o)} : H^{m+1}_dR(X) → ℝ` with
`Φ_{(f,o)}([ω]) = ∫_{(Λ ∘ f, o)} ω` for every closed `ω` and every such perturbation; if `X` has
the local unique continuation property, there is likewise `Φ^eff_{(f,o)}` with
`Φ^eff_{(f,o)}([ω]) = ∮_{(Λ ∘ f, o)} ω`.  (A perturbation in general position exists as well:
`corollary_15_4_4_wellDefined_bump`.) -/
theorem corollary_15_4_4_deRham (hd : ∀ x, A.X.PObj.degIndex x = 0)
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
    (∃ P : OrientedRegularPerturbation A f m, IsCanonicalPerturbation hf.2 hsec o P) ∧
    (∃ Φ : A.baseEP.epDeRham (m + 1) → ℝ, ∀ P : OrientedRegularPerturbation A f m,
      IsCanonicalPerturbation hf.2 hsec o P → ∀ (ω : A.baseEP.epFormsInfty (m + 1))
        (hω : ω ∈ LinearMap.ker (A.baseEP.epFormsInftyD (m + 1))),
        Φ (Submodule.Quotient.mk ⟨ω, hω⟩) = P.integral ω) ∧
    ∀ hLUC : A.X.IsLUC,
      ∃ Φ : A.baseEP.epDeRham (m + 1) → ℝ, ∀ P : OrientedRegularPerturbation A f m,
        IsCanonicalPerturbation hf.2 hsec o P → ∀ (ω : A.baseEP.epFormsInfty (m + 1))
          (hω : ω ∈ LinearMap.ker (A.baseEP.epFormsInftyD (m + 1))),
          Φ (Submodule.Quotient.mk ⟨ω, hω⟩) = P.integralEff hLUC ω := by
  obtain ⟨hex, h0, h1⟩ := corollary_15_4_4_wellDefined_bump hd hf hft hsec o ho hinv hidx hpara
    hbump hS
  refine ⟨hex.imp fun _ h => h.1,
    exists_deRham_map _ (fun P : OrientedRegularPerturbation A f m => P.integral)
      (fun P hP ω ω' hmem => ?_) h1, fun hLUC => ?_⟩
  · obtain ⟨η, hη⟩ := hmem
    have := h0 P hP η
    rw [hη, P.integral_sub] at this
    linarith
  · obtain ⟨e0, e1⟩ := corollary_15_4_4_eff_oriented_bump hd hf hft hsec o ho hinv hidx hpara
      hbump hLUC
    refine exists_deRham_map _ (fun P : OrientedRegularPerturbation A f m => P.integralEff hLUC)
      (fun P hP ω ω' hmem => ?_) e1
    obtain ⟨η, hη⟩ := hmem
    have := e0 P hP η
    rw [hη, P.integralEff_sub] at this
    linarith

/-- **Corollary 15.4.4, effective version (2021 p. 703), in degree `m + 1`, as a map on de Rham
cohomology**: under the hypotheses of `corollary_15_4_4_deRham` and the local unique continuation
property, a canonically oriented regular perturbation exists and there is
`Φ^eff_{(f,o)} : H^{m+1}_dR(X) → ℝ` with `Φ^eff_{(f,o)}([ω]) = ∮_{(Λ ∘ f, o)} ω` for every closed
`ω` and every such perturbation. -/
theorem corollary_15_4_4_eff_deRham (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy)
    (ho : haveI := paracompactSpace_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_pullback A.B
      IsSectionOrientation f hf.2 o)
    (hinv : A.E.IsOrInvariant hf hsec o)
    {m : ℕ} (hidx : ∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x ((m + 1 : ℕ) : ℤ))
    (hpara : A.X.HasParacompactOrbitSpace) (hbump : A.X.AdmitsBumpFunctionsPointwise)
    (hS : A.E.HasCompactSolutionSetEp f) (hLUC : A.X.IsLUC) :
    (∃ P : OrientedRegularPerturbation A f m, IsCanonicalPerturbation hf.2 hsec o P) ∧
    ∃ Φ : A.baseEP.epDeRham (m + 1) → ℝ, ∀ P : OrientedRegularPerturbation A f m,
      IsCanonicalPerturbation hf.2 hsec o P → ∀ (ω : A.baseEP.epFormsInfty (m + 1))
        (hω : ω ∈ LinearMap.ker (A.baseEP.epFormsInftyD (m + 1))),
        Φ (Submodule.Quotient.mk ⟨ω, hω⟩) = P.integralEff hLUC ω :=
  let h := corollary_15_4_4_deRham hd hf hft hsec o ho hinv hidx hpara hbump hS
  ⟨h.1, h.2.2 hLUC⟩

/-- **Corollary 15.4.4 (2021 p. 703) in Fredholm index `0`, as maps on `H^0_dR(X)`.**  Under the
hypotheses of `corollary_15_4_4_deRham` with index `0`: a regular perturbation of dimension `0`
with the canonical orientation of `(f, o)` exists, and there is `Φ_{(f,o)} : H^0_dR(X) → ℝ` with
`Φ_{(f,o)}([ω])` the weighted signed count `∫_{(Λ ∘ f, o)} ω` for every closed `ω` and every such
perturbation; under (LUC) likewise `Φ^eff_{(f,o)}` with the effective count `∮`. -/
theorem corollary_15_4_4_index_zero_deRham (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy)
    (ho : haveI := paracompactSpace_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_pullback A.B
      IsSectionOrientation f hf.2 o)
    (hinv : A.E.IsOrInvariant hf hsec o)
    (hidx : ∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x 0)
    (hpara : A.X.HasParacompactOrbitSpace) (hbump : A.X.AdmitsBumpFunctionsPointwise)
    (hS : A.E.HasCompactSolutionSetEp f) :
    (∃ P : PointPerturbation A f, P.IsCanonical hf.2 hsec o) ∧
    (∃ Φ : A.baseEP.epDeRham 0 → ℝ, ∀ P : PointPerturbation A f, P.IsCanonical hf.2 hsec o →
      ∀ (ω : A.baseEP.epFormsInfty 0) (hω : ω ∈ LinearMap.ker (A.baseEP.epFormsInftyD 0)),
        Φ (Submodule.Quotient.mk ⟨ω, hω⟩) = P.count ω) ∧
    ∀ hLUC : A.X.IsLUC,
      ∃ Φ : A.baseEP.epDeRham 0 → ℝ, ∀ P : PointPerturbation A f, P.IsCanonical hf.2 hsec o →
        ∀ (ω : A.baseEP.epFormsInfty 0) (hω : ω ∈ LinearMap.ker (A.baseEP.epFormsInftyD 0)),
          Φ (Submodule.Quotient.mk ⟨ω, hω⟩) = P.countEff hLUC ω := by
  obtain ⟨hex, hind⟩ := corollary_15_4_4_index_zero_wellDefined_all hd hf hft hsec o ho hidx hinv
    hpara hbump hS
  have hbot : ∀ ω ω' : A.baseEP.epFormsInfty 0, ω - ω' ∈ A.baseEP.epFormsInftyDRange 0 →
      ω = ω' := fun ω ω' h => sub_eq_zero.1 ((Submodule.mem_bot ℝ).1 h)
  refine ⟨hex.imp fun _ h => h.1,
    exists_deRham_map _ (fun P : PointPerturbation A f => P.count)
      (fun P _ ω ω' h => by rw [hbot ω ω' h])
      (fun P₀ P₁ h₀ h₁ ω hω => (hind P₀ P₁ h₀ h₁ ω hω).1), fun hLUC => ?_⟩
  exact exists_deRham_map _ (fun P : PointPerturbation A f => P.countEff hLUC)
    (fun P _ ω ω' h => by rw [hbot ω ω' h])
    (fun P₀ P₁ h₀ h₁ ω hω => (hind P₀ P₁ h₀ h₁ ω hω).2 hLUC)

/-- **Corollary 15.4.4, effective version (2021 p. 703), in Fredholm index `0`**: under the
hypotheses of `corollary_15_4_4_index_zero_deRham` and (LUC), a canonically oriented regular
perturbation of dimension `0` exists and there is `Φ^eff_{(f,o)} : H^0_dR(X) → ℝ` with
`Φ^eff_{(f,o)}([ω])` the effective count `∮_{(Λ ∘ f, o)} ω`. -/
theorem corollary_15_4_4_index_zero_eff_deRham (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy)
    (ho : haveI := paracompactSpace_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_pullback A.B
      IsSectionOrientation f hf.2 o)
    (hinv : A.E.IsOrInvariant hf hsec o)
    (hidx : ∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x 0)
    (hpara : A.X.HasParacompactOrbitSpace) (hbump : A.X.AdmitsBumpFunctionsPointwise)
    (hS : A.E.HasCompactSolutionSetEp f) (hLUC : A.X.IsLUC) :
    (∃ P : PointPerturbation A f, P.IsCanonical hf.2 hsec o) ∧
    ∃ Φ : A.baseEP.epDeRham 0 → ℝ, ∀ P : PointPerturbation A f, P.IsCanonical hf.2 hsec o →
      ∀ (ω : A.baseEP.epFormsInfty 0) (hω : ω ∈ LinearMap.ker (A.baseEP.epFormsInftyD 0)),
        Φ (Submodule.Quotient.mk ⟨ω, hω⟩) = P.countEff hLUC ω :=
  let h := corollary_15_4_4_index_zero_deRham hd hf hft hsec o ho hinv hidx hpara hbump hS
  ⟨h.1, h.2.2 hLUC⟩

open TrivialIsotropy TrivialBundle StrongBundleEquivalenceExamples
  StrongBundleLocalizationExamples in
/-- **Witness for `corollary_15_4_4_deRham`**: over `ℤ/3 × ℝ² ⇉ ℝ²` (isotropy `ℤ/3`, the circle
section `f(x) = (x, |x|² − 1)` of index `1`) the hypotheses hold
(`corollary_15_4_4_hypotheses_planeZ3`; bump functions from partitions of unity), so a
canonically oriented regular perturbation exists and `Φ_{(f,o)} : H^1_dR(X) → ℝ` is defined.
Weak: the group acts trivially on the base and `∂X = ∅`. -/
theorem corollary_15_4_4_deRham_planeZ3 :
    (∃ P : OrientedRegularPerturbation planeZ3SEP circleSection 0,
      IsCanonicalPerturbation isScFredholmSectionFunctor_circle_planeZ3.2
        (hasScPlusSectionsThrough_epSEP 2 1) circleSectionOrientation P) ∧
    ∃ Φ : planeZ3SEP.baseEP.epDeRham (0 + 1) → ℝ, ∀ P : OrientedRegularPerturbation planeZ3SEP
      circleSection 0, IsCanonicalPerturbation isScFredholmSectionFunctor_circle_planeZ3.2
        (hasScPlusSectionsThrough_epSEP 2 1) circleSectionOrientation P →
      ∀ (ω : planeZ3SEP.baseEP.epFormsInfty (0 + 1))
        (hω : ω ∈ LinearMap.ker (planeZ3SEP.baseEP.epFormsInftyD (0 + 1))),
        Φ (Submodule.Quotient.mk ⟨ω, hω⟩) = P.integral ω := by
  obtain ⟨-, -, -, -, hd, hpara, hPU, -, hF, hft, hS, ho, hinv, hidx⟩ :=
    corollary_15_4_4_hypotheses_planeZ3
  have h := corollary_15_4_4_deRham hd hF hft (hasScPlusSectionsThrough_epSEP 2 1)
    circleSectionOrientation ho hinv hidx hpara
    (EpGroupoid.admitsBumpFunctionsPointwise_of_hasScPartitionsOfUnity hPU) hS
  exact ⟨h.1, h.2.1⟩

end SBLocalization

end Polyfold
