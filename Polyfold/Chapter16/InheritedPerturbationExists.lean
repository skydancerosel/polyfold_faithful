import Polyfold.Chapter15.CanonicalPerturbationExists
import Polyfold.Chapter16.CanonicalIntegralInvariance
import Polyfold.Chapter16.GeneralPositionModels
import Polyfold.Chapter16.IndexZeroCylinder
import Polyfold.Chapter16.PerturbedSuborbifold

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §16.6, p. 739:
**Theorem 16.6.6** (2017: Theorem 16.8) together with the existence of the perturbed solution
sets it is about, and Corollary 15.4.4 (p. 703) in index `0`.

# Theorem 16.6.6: admissible perturbed solution sets exist

## The text, paraphrased

(p. 739) For `∂Z = ∅`, an oriented sc-Fredholm section `f` with compact solution set and `(n, U)`
controlling compactness, the perturbed solution sets `θ̂ = λ ∘ f`, `λ` controlled by `(n, U)` with
`(f, λ)` in general position, are compact tame branched suborbifolds with an orientation
inherited from `(f, o)`, and `∫_θ̂ τ` for closed `τ` does not depend on `λ`.

## What is formalized

Namespace `Polyfold.SBLocalization`:
* `corollary_15_4_4_index_zero_exists`, `corollary_15_4_4_index_zero_wellDefined`: Corollary
  15.4.4 in index `0` with the existence of the perturbations.

Namespace `Polyfold.StrongPolyfoldBundle`:
* `isControlledBy_of_isRegularPerturbation`, `OrientationRep.exists_isRegularPerturbation`: a
  regular perturbation in general position exists in the model of an orientation, and its class
  is controlled by `(n, U)`.
* **`theorem_16_6_6_canonical_exists`**, **`theorem_16_6_6_canonical_wellDefined`**: an admissible
  `θ̂` with the orientation inherited from `(f, o)` exists; with `theorem_16_6_6_canonical`, the
  integrals of closed forms agree over any two of them.
* `theorem_16_6_6_index_zero_exists`, `theorem_16_6_6_index_zero_wellDefined`: the same in
  index `0` (weighted signed counts).
* `ModelSolutionSet`, `IsCanonicalSolutionSet`: compact oriented solution sets in a model, and
  `θ̂` carrying the canonical orientation of `(f, o)` without regularity of `Λ`.
* **`theorem_16_6_6_canonical_solutionSet`**: every admissible `λ` gives a compact tame `θ̂` of
  dimension `m + 1` with the canonical orientation of `(f, o)`.
* `theorem_16_6_6_canonical_solutionSet_of_isStructurable`: for an admissible `λ` with a
  structurable model functor and `N(λ) < 1` that orientation is the inherited one.

## Reading

The hypotheses of the existence statements are those of `theorem_16_6_6_canonical` and
`theorem_16_6_6_index_zero_polyfold_canonical_input` with one standing input `H`.  The
independence of the integrals is proved for perturbations with the inherited orientation, which
comes from an oriented regular perturbation of the model (structurable, `N(Λ) < 1`).  For an
admissible `λ` without these properties the canonical orientation of `θ̂` is available
(`theorem_16_6_6_canonical_solutionSet`); a cobordism between two such `θ̂` is not formalized.
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

/-- **Corollary 15.4.4 in index `0`, the perturbations exist**: for `d_X ≡ 0`, an oriented
sc-Fredholm section functor `f` of index `0` at the smooth points with compact `|S_f|`, paracompact
`|X|` and sc-smooth bump functions, there is a regular perturbation in general position whose
points carry the canonical signs (`PointPerturbation.IsCanonical`). -/
theorem corollary_15_4_4_index_zero_exists (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy)
    (ho : haveI := paracompactSpace_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_pullback A.B
      IsSectionOrientation f hf.2 o)
    (hidx : ∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x 0)
    (hinv : A.E.IsOrInvariant hf hsec o) (hpara : A.X.HasParacompactOrbitSpace)
    (hbump : A.X.AdmitsBumpFunctionsPointwise) (hS : A.E.HasCompactSolutionSetEp f) :
    ∃ P : PointPerturbation A f, P.IsCanonical hf.2 hsec o ∧ IsInGeneralPosition A f P.Λ := by
  obtain ⟨N, U, Λ, hreg, hgp⟩ :=
    exists_isRegularPerturbation_isInGeneralPosition hd hpara hbump hf hft hS
  have hX : A.X.IsTame := A.X.isTame_of_degIndex_eq_zero hd
  have hbump' : A.X.PObj.AdmitsBumpFunctions := A.X.theorem_12_3_2_1.1 hbump
  have hgood : ∀ x ∈ A.X.PObj.boundary, 0 < Λ (f x) → IsGoodPositionAt f Λ x :=
    fun x _ hpos => isGoodPositionAt_of_isInGeneralPosition hf hft hreg.2.1.1 hgp hpos
  have hidx' : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)), A.B.IsIndexAt f x (0 : ℕ) :=
    fun x hx => by
      exact_mod_cast hidx x (mem_smoothSet_of_pos hft hreg.2.1.1 (by exact_mod_cast hx))
  exact ⟨PointPerturbation.canonical hX hbump' hf hft hsec o hinv ho hreg hgood hidx',
    PointPerturbation.isCanonical_canonical hX hbump' hf hft hsec o hinv ho hreg hgood hidx', hgp⟩

/-- **Corollary 15.4.4 in index `0`, existence and independence**: under the hypotheses of
`corollary_15_4_4_index_zero_oriented`, canonically signed regular perturbations in general
position exist, and the weighted signed counts and their effective versions agree for any two of
them for every closed `0`-form `ω`. -/
theorem corollary_15_4_4_index_zero_wellDefined (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy)
    (ho : haveI := paracompactSpace_rn_prod A.X.PObj
      haveI := paracompactSpace_rn_pullback A.B
      IsSectionOrientation f hf.2 o)
    (hidx : ∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x 0)
    (hinv : A.E.IsOrInvariant hf hsec o) (hpara : A.X.HasParacompactOrbitSpace)
    (hPU : A.X.HasScPartitionsOfUnity) (hPUC : (A.cubeSEP 1).X.PObj.AdmitsScPartitionsOfUnity)
    (hS : A.E.HasCompactSolutionSetEp f) :
    (∃ P : PointPerturbation A f, P.IsCanonical hf.2 hsec o ∧ IsInGeneralPosition A f P.Λ) ∧
      ∀ P₀ P₁ : PointPerturbation A f, P₀.IsCanonical hf.2 hsec o → P₁.IsCanonical hf.2 hsec o →
        ∀ ω : A.baseEP.epFormsInfty 0, A.baseEP.epFormsInftyD 0 ω = 0 →
          P₀.count ω = P₁.count ω ∧
            ∀ hLUC : A.X.IsLUC, P₀.countEff hLUC ω = P₁.countEff hLUC ω :=
  ⟨corollary_15_4_4_index_zero_exists hd hf hft hsec o ho hidx hinv hpara
      (EpGroupoid.admitsBumpFunctionsPointwise_of_hasScPartitionsOfUnity hPU) hS,
    fun P₀ P₁ h₀ h₁ ω hω => corollary_15_4_4_index_zero_oriented hd hf hft hsec o ho hidx hinv
      hpara hPU hPUC hS P₀ P₁ h₀ h₁ ω hω⟩

end SBLocalization

namespace StrongPolyfoldBundle

open StrongPolyfoldBundleStructure PolyfoldClass SBLocalization SEP

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p}

/-- **A perturbation in a model gives a controlled sc⁺-multisection** (Definition 16.5.4): if
`N(Λ) ≤ 1` for the norm `n` read in the model and `dom-supp(Λ) ⊆ g⁻¹(U)`, the class of `Λ` is
controlled by `(n, U)`. -/
theorem isControlledBy_of_isRegularPerturbation (a : SectionRep c) {n : Y → ℝ} {U : Set Z}
    {Λ : a.S.A.W → ℚ≥0} (hΛ : IsScPlusMultisection a.S.A Λ)
    (hN : ∀ x, pointwiseNorm (a.S.normOf n) Λ x ≤ 1) (hdom : domSupp Λ ⊆ a.g ⁻¹' U) :
    ScPlusMultisection.IsControlledBy (c := c) ⟦ofFunctor a.S a.hS Λ hΛ⟧ n U := by
  set b := ofFunctor a.S a.hS Λ hΛ
  refine ⟨fun z => ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := a.S.surjective_γπ z
    change c.normLam n b.lam _ ≤ 1
    rw [normLam_eq a.hS n Λ _ x fun w _ => b.comm w]
    exact hN x
  · rw [← remark_16_5_3 b]
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact hdom hx

/-- **Regular perturbations in general position exist in the model of an orientation**
(Corollary 15.3.10 (1)): for `Z` with sc-smooth partitions of unity, `∂Z = ∅`, compact solution
set, `(n, U)` controlling compactness and tame germ data of the representative `F` of `o`, there
is a regular perturbation of `F` for the norm `n` and `g⁻¹(U)`, in general position. -/
theorem OrientationRep.exists_isRegularPerturbation (hPU : c.polyfold.AdmitsScPartitionsOfUnity)
    (hbd : c.polyfold.boundary = ∅) {s : FredholmSection c} (hcs : s.1.HasCompactSolutionSet)
    {n : Y → ℝ} (hn : c.IsAuxNorm n) {U : Set Z} (hU : IsOpen U)
    (hcc : s.1.ControlsCompactness n U) (o : OrientationRep s)
    (hft : o.a.S.A.B.IsScFredholmSectionTame o.a.F) :
    ∃ Λ : o.a.S.A.W → ℚ≥0, IsRegularPerturbation o.a.S.A o.a.F (o.a.S.normOf n) (o.a.g ⁻¹' U) Λ ∧
      IsInGeneralPosition o.a.S.A o.a.F Λ := by
  have hd : ∀ x, o.a.S.A.X.PObj.degIndex x = 0 :=
    degIndex_eq_zero_of_boundary_eq_empty hbd o.a.hS
  have hPUq := (c.polyfold.definition_16_1_5_two).1 hPU o.a.S.toPolyfoldStructure
    (toPolyfoldStructure_mem o.a.hS)
  have hSa : o.a.S.A.E.HasCompactSolutionSetEp o.a.F := by
    rw [← o.a.hasCompactSolutionSet_iff, o.ha]; exact hcs
  have hcca := (o.a.controlsCompactness_iff hn hU).1 (by rw [o.ha]; exact hcc)
  obtain ⟨Λ, hreg, hgp, -⟩ := corollary_15_3_10_1 hd o.a.S.paracompact
    (EpGroupoid.admitsBumpFunctionsPointwise_of_hasScPartitionsOfUnity hPUq) o.hF hft hSa hcca
  exact ⟨Λ, hreg, hgp⟩

/-- **2021 Theorem 16.6.6, p. 739, the admissible perturbations exist**: under the hypotheses of
`theorem_16_6_6_canonical` and the standing hypotheses `H` of index `m + 1` in the model of `o`,
there is an admissible perturbed solution set `θ̂ = λ ∘ f` (controlled by `(n, U)`, in general
position) with the orientation inherited from `(f, o)`. -/
theorem theorem_16_6_6_canonical_exists (hPU : c.polyfold.AdmitsScPartitionsOfUnity)
    (hbd : c.polyfold.boundary = ∅) {s : FredholmSection c} (hcs : s.1.HasCompactSolutionSet)
    {n : Y → ℝ} (hn : c.IsAuxNorm n) {U : Set Z} (hU : IsOpen U)
    (hcc : s.1.ControlsCompactness n U) {m : ℕ} {o : OrientationRep s}
    (H : CanonicalInput o (m + 1)) :
    ∃ Q : OrientedPerturbation s.1 m, Q.IsAdmissible n U ∧
      IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o Q := by
  obtain ⟨Λ, hreg, hgp⟩ := o.exists_isRegularPerturbation hPU hbd hcs hn hU hcc H.tame
  have hd : ∀ x, o.a.S.A.X.PObj.degIndex x = 0 :=
    degIndex_eq_zero_of_boundary_eq_empty hbd o.a.hS
  have hPUq := (c.polyfold.definition_16_1_5_two).1 hPU o.a.S.toPolyfoldStructure
    (toPolyfoldStructure_mem o.a.hS)
  have hX : o.a.S.A.X.IsTame := o.a.S.A.X.isTame_of_degIndex_eq_zero hd
  have hbump : o.a.S.A.X.PObj.AdmitsBumpFunctions := o.a.S.A.X.theorem_12_3_2_1.1
    (EpGroupoid.admitsBumpFunctionsPointwise_of_hasScPartitionsOfUnity hPUq)
  have ho := o.isSectionOrientation_of_boundary_eq_empty hPU hbd H.tame
  have hgood : ∀ x ∈ o.a.S.A.X.PObj.boundary, 0 < Λ (o.a.F x) →
      SBLocalization.IsGoodPositionAt o.a.F Λ x :=
    fun x _ hpos => isGoodPositionAt_of_isInGeneralPosition o.hF H.tame hreg.2.1.1 hgp hpos
  have hidx : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (o.a.F z) : ℚ)),
      o.a.S.A.B.IsIndexAt o.a.F x (m + 1 : ℕ) := fun x hx =>
    H.index x (mem_smoothSet_of_pos H.tame hreg.2.1.1 (by exact_mod_cast hx))
  set P := OrientedRegularPerturbation.canonical hX hbump o.hF H.tame o.hsec o.o
    o.isOrientation.2 ho hreg hgood hidx
  refine ⟨(ModelPerturbation.ofRegular P).toOrientedPerturbation o.ha,
    ⟨isControlledBy_of_isRegularPerturbation o.a hreg.2.1.1 (fun x => (hreg.2.2.2.1 x).le)
      hreg.2.2.1, o.a, Λ, hreg.2.1.1, o.ha, rfl, hgp⟩, P, ?_, rfl⟩
  exact isCanonicalPerturbation_canonical hX hbump o.hF H.tame o.hsec o.o o.isOrientation.2 ho
    hreg hgood hidx

/-- **2021 Theorem 16.6.6, p. 739, existence and independence**: admissible perturbed solution
sets with the orientation inherited from `(f, o)` exist, and a closed `τ` has the same `∫_θ̂ τ`
and `∮_θ̂ τ` for any two of them. -/
theorem theorem_16_6_6_canonical_wellDefined (hPU : c.polyfold.AdmitsScPartitionsOfUnity)
    (hbd : c.polyfold.boundary = ∅) {s : FredholmSection c} (hcs : s.1.HasCompactSolutionSet)
    {n : Y → ℝ} (hn : c.IsAuxNorm n) {U : Set Z} (hU : IsOpen U)
    (hcc : s.1.ControlsCompactness n U) {m : ℕ} {o : OrientationRep s}
    (H : CanonicalInput o (m + 1)) :
    (∃ Q : OrientedPerturbation s.1 m, Q.IsAdmissible n U ∧
      IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o Q) ∧
    ∀ Q₀ Q₁ : OrientedPerturbation s.1 m, Q₀.IsAdmissible n U →
      IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o Q₀ →
      Q₁.IsAdmissible n U →
      IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o Q₁ →
      ∀ τ : ScForm c.polyfold (m + 1), ScForm.d τ = 0 →
        Q₀.integral τ = Q₁.integral τ ∧ Q₀.integralEff τ = Q₁.integralEff τ :=
  ⟨theorem_16_6_6_canonical_exists hPU hbd hcs hn hU hcc H,
    fun Q₀ Q₁ h₀ i₀ h₁ i₁ => (theorem_16_6_6_canonical hPU s n U m hbd hcs hn hU hcc o).2
      Q₀ Q₁ h₀ ⟨H, i₀⟩ h₁ ⟨H, i₁⟩⟩

/-- **2021 Theorem 16.6.6, p. 739, in index `0`, the admissible perturbations exist**: under the
hypotheses of `theorem_16_6_6_index_zero_polyfold_canonical_input` and the standing hypotheses `H`
of index `0`, there is an admissible finite perturbed solution set with the canonical signs
inherited from `(f, o)`. -/
theorem theorem_16_6_6_index_zero_exists (hPU : c.polyfold.AdmitsScPartitionsOfUnity)
    (hbd : c.polyfold.boundary = ∅) {s : FredholmSection c} (hcs : s.1.HasCompactSolutionSet)
    {n : Y → ℝ} (hn : c.IsAuxNorm n) {U : Set Z} (hU : IsOpen U)
    (hcc : s.1.ControlsCompactness n U) {o : OrientationRep s} (H : CanonicalInput o 0) :
    ∃ Q : PointOrientedPerturbation s.1, Q.IsAdmissible n U ∧
      IsInheritedFromPoint (fun o P => P.IsCanonical o.hF.2 o.hsec o.o) o Q := by
  obtain ⟨Λ, hreg, hgp⟩ := o.exists_isRegularPerturbation hPU hbd hcs hn hU hcc H.tame
  have hd : ∀ x, o.a.S.A.X.PObj.degIndex x = 0 :=
    degIndex_eq_zero_of_boundary_eq_empty hbd o.a.hS
  have hPUq := (c.polyfold.definition_16_1_5_two).1 hPU o.a.S.toPolyfoldStructure
    (toPolyfoldStructure_mem o.a.hS)
  have hX : o.a.S.A.X.IsTame := o.a.S.A.X.isTame_of_degIndex_eq_zero hd
  have hbump : o.a.S.A.X.PObj.AdmitsBumpFunctions := o.a.S.A.X.theorem_12_3_2_1.1
    (EpGroupoid.admitsBumpFunctionsPointwise_of_hasScPartitionsOfUnity hPUq)
  have ho := o.isSectionOrientation_of_boundary_eq_empty hPU hbd H.tame
  have hgood : ∀ x ∈ o.a.S.A.X.PObj.boundary, 0 < Λ (o.a.F x) →
      SBLocalization.IsGoodPositionAt o.a.F Λ x :=
    fun x _ hpos => isGoodPositionAt_of_isInGeneralPosition o.hF H.tame hreg.2.1.1 hgp hpos
  have hidx : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (o.a.F z) : ℚ)),
      o.a.S.A.B.IsIndexAt o.a.F x (0 : ℕ) := fun x hx => by
    exact_mod_cast H.index x (mem_smoothSet_of_pos H.tame hreg.2.1.1 (by exact_mod_cast hx))
  set P := PointPerturbation.canonical hX hbump o.hF H.tame o.hsec o.o o.isOrientation.2 ho hreg
    hgood hidx
  refine ⟨toPointOrientedPerturbation o.a P o.ha,
    ⟨isControlledBy_of_isRegularPerturbation o.a hreg.2.1.1 (fun x => (hreg.2.2.2.1 x).le)
      hreg.2.2.1, o.a, Λ, hreg.2.1.1, o.ha, rfl, hgp⟩, P, ?_, rfl⟩
  exact PointPerturbation.isCanonical_canonical hX hbump o.hF H.tame o.hsec o.o o.isOrientation.2
    ho hreg hgood hidx

/-- **2021 Theorem 16.6.6, p. 739, in index `0`, existence and independence**: admissible
perturbed solution sets with the signs inherited from `(f, o)` exist, and a closed `0`-form `τ` has
the same weighted signed counts (and effective counts) for any two of them. -/
theorem theorem_16_6_6_index_zero_wellDefined (hPU : c.polyfold.AdmitsScPartitionsOfUnity)
    (hbd : c.polyfold.boundary = ∅) {s : FredholmSection c} (hcs : s.1.HasCompactSolutionSet)
    {n : Y → ℝ} (hn : c.IsAuxNorm n) {U : Set Z} (hU : IsOpen U)
    (hcc : s.1.ControlsCompactness n U) {o : OrientationRep s} (H : CanonicalInput o 0) :
    (∃ Q : PointOrientedPerturbation s.1, Q.IsAdmissible n U ∧
      IsInheritedFromPoint (fun o P => P.IsCanonical o.hF.2 o.hsec o.o) o Q) ∧
    ∀ Q₀ Q₁ : PointOrientedPerturbation s.1, Q₀.IsAdmissible n U →
      IsInheritedFromPoint (fun o P => P.IsCanonical o.hF.2 o.hsec o.o) o Q₀ →
      Q₁.IsAdmissible n U →
      IsInheritedFromPoint (fun o P => P.IsCanonical o.hF.2 o.hsec o.o) o Q₁ →
      ∀ τ : ScForm c.polyfold 0, ScForm.d τ = 0 →
        Q₀.count τ = Q₁.count τ ∧ Q₀.countEff τ = Q₁.countEff τ := by
  refine ⟨theorem_16_6_6_index_zero_exists hPU hbd hcs hn hU hcc H,
    fun Q₀ Q₁ h₀ i₀ h₁ i₁ => ?_⟩
  obtain ⟨P₀, c₀, e₀⟩ := i₀
  obtain ⟨P₁, c₁, e₁⟩ := i₁
  exact theorem_16_6_6_index_zero_polyfold_canonical_input hPU s n U hbd hcs hn hU hcc o Q₀ Q₁
    h₀ ⟨P₀, ⟨H, c₀⟩, e₀⟩ h₁ ⟨P₁, ⟨H, c₁⟩, e₁⟩

/-! ### Every admissible perturbation: the canonical orientation of `θ̂` -/

section SolutionSet

open EpGroupoid

/-- **A compact oriented solution set in the model of a section representative**: an
sc⁺-multisection functor `Λ` with `Θ = Λ ∘ F` a compact branched ep⁺-subgroupoid, an orientation
`T̂` of `Θ`, and oriented tame local structures of dimension `m + 1` representing `T̂` at every
point of `supp(Θ)`.  No regularity of `Λ` (structurability, `N(Λ) < 1`) is part of the data. -/
structure ModelSolutionSet (a : SectionRep c) (m : ℕ) where
  /-- The sc⁺-multisection functor. -/
  Λ : a.S.A.W → ℚ≥0
  isScPlusMultisection : IsScPlusMultisection a.S.A Λ
  /-- The orientation `T̂` of `Θ = Λ ∘ F`. -/
  T : a.S.A.Obj → a.S.A.X.PObj.OrTangent →₀ ℚ
  isBranched : a.S.A.X.IsBranchedEpSubgroupoid (fun z => (Λ (a.F z) : ℚ))
  isCompact : a.S.A.X.IsCompactBranched (fun z => (Λ (a.F z) : ℚ))
  isOrientation : a.S.A.X.IsOrientation (fun z => (Λ (a.F z) : ℚ)) T
  loc : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (a.F z) : ℚ)),
    ∃ C : a.S.A.X.OrientedTameStructure (m + 1) (fun z => (Λ (a.F z) : ℚ)) x, C.Represents T

namespace ModelSolutionSet

variable {a : SectionRep c} {m : ℕ} (M : ModelSolutionSet a m)

/-- The oriented branched suborbifold representative `(Θ, T̂)` in the polyfold structure of the
representative. -/
def orientedRep : OrientedRep c.polyfold where
  p := a.S.toPolyfoldStructure
  mem := toPolyfoldStructure_mem a.hS
  A := ⟨fun z => (M.Λ (a.F z) : ℚ), a.S.A.X.smoothPart M.T, M.isBranched,
    EpGroupoid.hasIndependentTangentSums _, M.isOrientation.smoothPart⟩
  smooth := fun _ hx => smoothPart_of_notMem hx

/-- The class of `(Θ, T̂)`: a compact tame oriented branched suborbifold of `Z` of dimension
`m + 1`. -/
def toCompact : CompactOrientedSuborbifold c.polyfold m where
  θ := ⟦M.orientedRep⟧
  isCompact := ⟨M.orientedRep.toBranchedRep, rfl, M.isCompact⟩
  isTame := ⟨M.orientedRep, rfl, fun x hx => (M.loc x hx).imp fun C hC =>
    C.represents_congr (fun _ hy => (smoothPart_of_mem hy).symm) hC⟩

/-- The oriented perturbed solution set `θ̂ = λ ∘ f` (2021 p. 739) with `λ` the class of `Λ`. -/
def toOrientedPerturbation {s : ScSection c} (ha : ⟦a⟧ = s) : OrientedPerturbation s m where
  toCompactOrientedSuborbifold := M.toCompact
  t := ⟦ofFunctor a.S a.hS M.Λ M.isScPlusMultisection⟧
  isPerturbed :=
    (perturbedRep_toFun_ofFunctor a M.Λ M.isScPlusMultisection M.isBranched).trans
      (by rw [ha])

/-- The solution set of an oriented regular perturbation. -/
def ofRegular (P : OrientedRegularPerturbation a.S.A a.F m) : ModelSolutionSet a m where
  Λ := P.Λ
  isScPlusMultisection := P.isRegular.2.1.1
  T := P.T
  isBranched := P.isBranched
  isCompact := P.isCompact
  isOrientation := P.isOrientation
  loc := P.loc

/-- The perturbed solution set of `ofRegular P` is that of `P` (`ModelPerturbation.ofRegular`). -/
theorem toOrientedPerturbation_ofRegular (P : OrientedRegularPerturbation a.S.A a.F m)
    {s : ScSection c} (ha : ⟦a⟧ = s) :
    (ofRegular P).toOrientedPerturbation ha =
      (ModelPerturbation.ofRegular P).toOrientedPerturbation ha :=
  rfl

end ModelSolutionSet

/-- **`θ̂` carries the canonical orientation of `(f, o)`** (Definition 15.4.2 read in the model of
`o`): `Q` is the class of a compact oriented solution set `(Λ, T̂)` of the representative `F` that
carries `o`, with `T̂` the canonical orientation.  Unlike `IsInheritedFrom`, `Λ` need not be a
regular perturbation. -/
def IsCanonicalSolutionSet {s : FredholmSection c} {m : ℕ} (o : OrientationRep s)
    (Q : OrientedPerturbation s.1 m) : Prop :=
  ∃ M : ModelSolutionSet o.a m, IsCanonicalFor M.Λ o.hF.2 o.hsec o.o (m + 1) M.T ∧
    M.toOrientedPerturbation o.ha = Q

/-- The orientation inherited from `(f, o)` is a canonical orientation of the solution set. -/
theorem IsInheritedFrom.isCanonicalSolutionSet {s : FredholmSection c} {m : ℕ}
    {o : OrientationRep s} {Q : OrientedPerturbation s.1 m}
    (h : IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o Q) :
    IsCanonicalSolutionSet o Q := by
  obtain ⟨P, hP, rfl⟩ := h
  exact ⟨ModelSolutionSet.ofRegular P, hP, rfl⟩

/-- A canonically oriented solution set whose `Λ` is a regular perturbation has the orientation
inherited from `(f, o)`. -/
theorem isInheritedFrom_of_isRegularPerturbation {s : FredholmSection c} {m : ℕ}
    {o : OrientationRep s} (M : ModelSolutionSet o.a m)
    (hT : IsCanonicalFor M.Λ o.hF.2 o.hsec o.o (m + 1) M.T) {N : o.a.S.A.B.One → ℝ}
    {U : Set o.a.S.A.Obj} (hreg : IsRegularPerturbation o.a.S.A o.a.F N U M.Λ) :
    IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o
      (M.toOrientedPerturbation o.ha) :=
  ⟨⟨N, U, M.Λ, hreg, M.T, M.isBranched, M.isCompact, M.isOrientation, M.loc⟩, hT, rfl⟩

/-- **Every admissible `Λ` in the model gives a canonically oriented solution set**: for `Λ`
whose class is controlled by `(n, U)` and `(F, Λ)` in general position, `Θ = Λ ∘ F` is a compact
branched ep⁺-subgroupoid (Theorem 15.4.3) with the canonical orientation of dimension `m + 1`
(Theorem 15.4.1), and `N(Λ) ≤ 1`, `dom-supp(Λ) ⊆ g⁻¹(U)`, `(F, Λ)` transversal. -/
theorem exists_modelSolutionSet_canonical (hPU : c.polyfold.AdmitsScPartitionsOfUnity)
    (hbd : c.polyfold.boundary = ∅) {s : FredholmSection c} {n : Y → ℝ} (hn : c.IsAuxNorm n)
    {U : Set Z} (hU : IsOpen U) (hcc : s.1.ControlsCompactness n U) {m : ℕ}
    {o : OrientationRep s} (H : CanonicalInput o (m + 1)) {Λ : o.a.S.A.W → ℚ≥0}
    (hΛ : IsScPlusMultisection o.a.S.A Λ)
    (ht : ScPlusMultisection.IsControlledBy (c := c) ⟦ofFunctor o.a.S o.a.hS Λ hΛ⟧ n U)
    (hgp : IsInGeneralPosition o.a.S.A o.a.F Λ) :
    ∃ M : ModelSolutionSet o.a m, M.Λ = Λ ∧ IsCanonicalFor M.Λ o.hF.2 o.hsec o.o (m + 1) M.T ∧
      (∀ x, pointwiseNorm (o.a.S.normOf n) Λ x ≤ 1) ∧ domSupp Λ ⊆ o.a.g ⁻¹' U ∧
      IsTransversal o.a.F Λ := by
  have hd : ∀ x, o.a.S.A.X.PObj.degIndex x = 0 :=
    degIndex_eq_zero_of_boundary_eq_empty hbd o.a.hS
  have hPUq := (c.polyfold.definition_16_1_5_two).1 hPU o.a.S.toPolyfoldStructure
    (toPolyfoldStructure_mem o.a.hS)
  have hX : o.a.S.A.X.IsTame := o.a.S.A.X.isTame_of_degIndex_eq_zero hd
  have hbump : o.a.S.A.X.PObj.AdmitsBumpFunctions := o.a.S.A.X.theorem_12_3_2_1.1
    (EpGroupoid.admitsBumpFunctionsPointwise_of_hasScPartitionsOfUnity hPUq)
  have ho := o.isSectionOrientation_of_boundary_eq_empty hPU hbd H.tame
  have hcca := (o.a.controlsCompactness_iff hn hU).1 (by rw [o.ha]; exact hcc)
  set b := ofFunctor o.a.S o.a.hS Λ hΛ
  have hN1 : ∀ x, pointwiseNorm (o.a.S.normOf n) Λ x ≤ 1 := by
    intro x
    rw [← normLam_eq o.a.hS n Λ b.lam x fun w _ => b.comm w]
    exact ht.1 _
  have hdom : domSupp Λ ⊆ o.a.g ⁻¹' U := by
    intro x hx
    apply ht.2
    rw [← remark_16_5_3 b]
    exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  have htr := IsInGeneralPosition.isTransversal o.hF hΛ hgp
  have hgood : ∀ x, 0 < Λ (o.a.F x) → SBLocalization.IsGoodPositionAt o.a.F Λ x :=
    fun x hpos => isGoodPositionAt_of_isInGeneralPosition o.hF H.tame hΛ hgp hpos
  obtain ⟨hbr, hcpt⟩ := theorem_15_4_3_isBranched_hyp o.hF H.tame hcca hΛ hdom hN1 htr
    fun x _ => hgood x
  have hidx : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (o.a.F z) : ℚ)),
      o.a.S.A.B.IsIndexAt o.a.F x (m + 1 : ℕ) := fun x hx =>
    H.index x (mem_smoothSet_of_pos H.tame hΛ (by exact_mod_cast hx))
  have hcan := theorem_15_4_1 hX hbump o.hF H.tame hΛ o.hsec o.o o.isOrientation.2 ho
    (fun x hx => hgood x (by exact_mod_cast hx)) hidx
  exact ⟨⟨Λ, hΛ, canonicalOrientation Λ o.hF.2 o.hsec o.o, hbr, hcpt, hcan.1, hcan.loc⟩, rfl, hcan,
    hN1, hdom, htr⟩

/-- **2021 Theorem 16.6.6, p. 739: every admissible `λ` gives a canonically oriented `θ̂`**: for
every sc⁺-multisection `t` controlled by `(n, U)` with `(f, t)` in general position, the perturbed
solution set `θ̂ = t ∘ f` is a compact tame oriented branched suborbifold of dimension `m + 1`
carrying the canonical orientation of `(f, o)`.  Compactness of the solution set is not needed
for this. -/
theorem theorem_16_6_6_canonical_solutionSet (hPU : c.polyfold.AdmitsScPartitionsOfUnity)
    (hbd : c.polyfold.boundary = ∅) {s : FredholmSection c} {n : Y → ℝ} (hn : c.IsAuxNorm n)
    {U : Set Z} (hU : IsOpen U) (hcc : s.1.ControlsCompactness n U) {m : ℕ}
    {o : OrientationRep s} (H : CanonicalInput o (m + 1)) (t : ScPlusMultisection c)
    (ht : t.IsControlledBy n U) (hgp : s.1.IsInGeneralPositionWith t) :
    ∃ Q : OrientedPerturbation s.1 m, Q.t = t ∧ Q.IsAdmissible n U ∧
      IsCanonicalSolutionSet o Q := by
  obtain ⟨Λ, hΛ, hl⟩ := exists_functor_rep t o.a.hS
  have ht' : (⟦ofFunctor o.a.S o.a.hS Λ hΛ⟧ : ScPlusMultisection c) = t :=
    mk_ofFunctor_eq t o.a.hS hΛ hl
  have hgpΛ := (ScSection.isInGeneralPositionWith_iff_of_rep s.1 s.2 t o.a o.ha hΛ hl).1 hgp
  rw [← ht'] at ht
  obtain ⟨M, rfl, hcan, -⟩ := exists_modelSolutionSet_canonical hPU hbd hn hU hcc H hΛ ht hgpΛ
  exact ⟨M.toOrientedPerturbation o.ha, ht', ⟨ht, o.a, M.Λ, hΛ, o.ha, rfl, hgpΛ⟩, M, hcan, rfl⟩

/-- **Admissible structurable perturbations have the inherited orientation**: if the model
functor `Λ` of an admissible `λ` is structurable and `N(λ) < 1`, the canonically oriented `θ̂`
has the orientation inherited from `(f, o)`, so that `theorem_16_6_6_canonical_wellDefined`
applies to it. -/
theorem theorem_16_6_6_canonical_solutionSet_of_isStructurable
    (hPU : c.polyfold.AdmitsScPartitionsOfUnity)
    (hbd : c.polyfold.boundary = ∅) {s : FredholmSection c} {n : Y → ℝ} (hn : c.IsAuxNorm n)
    {U : Set Z} (hU : IsOpen U) (hcc : s.1.ControlsCompactness n U) {m : ℕ}
    {o : OrientationRep s} (H : CanonicalInput o (m + 1)) {Λ : o.a.S.A.W → ℚ≥0}
    (hstr : IsStructurable o.a.S.A Λ)
    (ht : ScPlusMultisection.IsControlledBy (c := c) ⟦ofFunctor o.a.S o.a.hS Λ hstr.1⟧ n U)
    (hlt : ∀ z, c.normLam n (ofFunctor o.a.S o.a.hS Λ hstr.1).lam z < 1)
    (hgp : s.1.IsInGeneralPositionWith ⟦ofFunctor o.a.S o.a.hS Λ hstr.1⟧) :
    ∃ Q : OrientedPerturbation s.1 m, Q.t = ⟦ofFunctor o.a.S o.a.hS Λ hstr.1⟧ ∧
      Q.IsAdmissible n U ∧ IsCanonicalSolutionSet o Q ∧
      IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o Q := by
  have hgpΛ := (ScSection.isInGeneralPositionWith_iff_of_rep s.1 s.2 _ o.a o.ha hstr.1
    (toFun_of_mk_ofFunctor_eq rfl)).1 hgp
  have hcca := (o.a.controlsCompactness_iff hn hU).1 (by rw [o.ha]; exact hcc)
  obtain ⟨M, rfl, hcan, -, hdom, htr⟩ :=
    exists_modelSolutionSet_canonical hPU hbd hn hU hcc H hstr.1 ht hgpΛ
  have hlt' : ∀ x, pointwiseNorm (o.a.S.normOf n) M.Λ x < 1 := fun x => by
    rw [← normLam_eq o.a.hS n M.Λ (ofFunctor o.a.S o.a.hS M.Λ hstr.1).lam x
      fun w _ => (ofFunctor o.a.S o.a.hS M.Λ hstr.1).comm w]
    exact hlt _
  exact ⟨M.toOrientedPerturbation o.ha, rfl, ⟨ht, hgp⟩, ⟨M, hcan, rfl⟩,
    isInheritedFrom_of_isRegularPerturbation M hcan ⟨hcca, hstr, hdom, hlt', htr⟩⟩

end SolutionSet

end StrongPolyfoldBundle

end Polyfold
