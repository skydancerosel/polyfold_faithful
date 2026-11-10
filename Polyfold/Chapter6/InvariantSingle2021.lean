import Polyfold.Chapter9.SolutionFaceForms2021
import Polyfold.Chapter6.SolutionSetOpen2021
import Polyfold.Chapter5.CylinderPerturbation2021
import Polyfold.Chapter6.PerturbedOrientation

/-!
# The invariant `Ψ` for one admissible section (2021 Theorem 6.7.1 (1), formula (6.35))

Theorem 6.7.1 (2021 p. 277–279) associates with a proper oriented sc-Fredholm section `(f, o)` of a
strong bundle `P : Y → X` over a tame M-polyfold with sc-smooth bump functions a linear map
`Ψ_{(f,o)} : H*_dR(X, ∂X) → ℝ`, `Ψ([ω, τ]) = ∫_{S_{f+s}} ω − ∫_{∂S_{f+s}} τ` (6.35), computed
with any section `s` admissible for `(N, U)` (the §6.7 preamble, p. 276). This file builds the
right-hand side of (6.35) for **one** admissible `s`, as a linear map on the relative de Rham
group of each degree `k`. The independence of `s`, `N` and `U` is not in this file.

## Main declarations

* `StrongBundle.IsAdmissible f N U s`: `s ∈ allowableSections N U` and `f + s` is in general
  position at all its zeros (p. 276). Satisfiable: `exists_isAdmissible`, and with the
  neighbourhood `U` of the preamble, `exists_isAdmissible_nbhd`.
* `StrongBundle.solPart f s k`, the part `S_k` of `S_{f+s}` where `f` has index `k` (reading R-c):
  it is clopen in `S_{f+s}`, compact when `S_{f+s}` is (`isCompact_solPart`), and
  `S_{f+s} = ⋃_k S_k` (`solutionSet_eq_iUnion_solPart`). With constant index `n`, `S_n = S_{f+s}`
  and `S_k = ∅` for `k ≠ n` (`solPart_eq_solutionSet`, `solPart_eq_empty_of_ne`).
* `solPartChartedSpace`, `isManifold_solPart`, `solPartOr`, `SolPartIsOrientedManifold`,
  `solPartIsOrientedManifold`: `S_k` is a Mathlib manifold with corners of dimension `k`, oriented
  by `o.sectionAdd` (Theorem 6.6.18 on the open set `V_k = solIndexNbhd`), with the instances and
  the orientation formula needed downstream.
* `solIntegral k`, `solBoundaryIntegral k : RelForms hX k →ₗ[ℝ] ℝ`: `(ω, τ) ↦ ∫_{S_k} ω|_S` and
  `(ω, τ) ↦ ∫_{∂S_k} τ|_{∂S}` (face forms of `SolutionFaceForms2021`); `0` if `S_k` is not
  compact, and `solBoundaryIntegral 0 = 0`. In degree `0`, `∫_{S_0} ω = ∑_{x ∈ S_0} ε(x) ω(x)`
  (`solIntegral_zero_eq_sum`, from `ManifoldForm.integral_eq_sum_of_dim_zero`).
* `psiForms k = solIntegral k − solBoundaryIntegral k`, which vanishes on `relD`-exact forms by
  Stokes' theorem (`psiForms_relD`).
* `psiAt k : relDeRham hX k →ₗ[ℝ] ℝ`, the map `Ψ` of (6.35) for this `s`, with
  `psiAt_mk : psiAt k [c] = solIntegral k c − solBoundaryIntegral k c` and the explicit forms
  `psiAt_mk_zero`, `psiAt_mk_succ`, `psiAt_mk_zero_eq_sum` for compact `S_{f+s}`, and
  `psiAt_of_eq_empty` (`Ψ = 0` in a degree with `S_k = ∅`). `psiAt` depends on `s` only, not
  on the pair `(N, U)` (`psiAt_congr_admissible`). For `∂X = ∅` (p. 279),
  `Ψ([ω, τ]) = ∫_{S_k} ω|_S` (`psiAt_mk_of_isWithoutBoundary`).

## Readings

* R-c: the text integrates a `k`-form over `S_{f+s}` and sets the integral `0` "if the dimensions
  of the forms and manifolds do not agree". Where the index of `f` is not constant, we read this
  as integrating over the part `S_k` of dimension `k`.
* The integrals are those of Mathlib manifolds (`ManifoldForm.integral`, `faceIntegral`). The
  linear maps are defined without a compactness hypothesis: they are `0` when `S_k` is not
  compact, and the `_apply` lemmas give the integrals when it is.
-/

open Set Filter Topology Manifold Module MeasureTheory

noncomputable section

namespace Polyfold

universe u v

local notation "𝓠" => modelWithCornersEuclideanQuadrant

local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-! ### Homogeneity of `∫_M`, and the integral in dimension `0` -/

namespace ManifoldForm

section Smul

variable {n k : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant n) M]

theorem chartForm_smul_eq (e : OpenPartialHomeomorph M (EuclideanQuadrant n)) (a : ℝ)
    (ω : ManifoldForm (𝓠 n) M k) : chartForm (𝓠 n) e (a • ω) = a • chartForm (𝓠 n) e ω := by
  funext y; ext v; rfl

theorem chartIntegral_smul_eq (e : OpenPartialHomeomorph M (EuclideanQuadrant n)) (a : ℝ)
    (ω : ManifoldForm (𝓠 n) M n) : chartIntegral e (a • ω) = a * chartIntegral e ω := by
  rw [chartIntegral, chartIntegral, chartForm_smul_eq, topFormIntegral, topFormIntegral,
    ← integral_const_mul]
  rfl

theorem _root_.Polyfold.IntegrationData.integral_smul_eq [IsManifold (𝓠 n) ∞ M]
    {o : TangentOrientation (𝓠 n) M n} {s : Set M} {ι : Type*} [Fintype ι]
    (D : IntegrationData M o s ι) (a : ℝ) (ω : ManifoldForm (𝓠 n) M n) :
    D.integral (a • ω) = a * D.integral ω := by
  simp only [IntegrationData.integral, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : smulFun (D.ρ j) (a • ω) = a • smulFun (D.ρ j) ω := by
    funext x
    change D.ρ j x • (a • ω x) = a • (D.ρ j x • ω x)
    exact smul_comm _ _ _
  rw [this, chartIntegral_smul_eq, mul_left_comm]

theorem tsupport_smul_subset (a : ℝ) (ω : ManifoldForm (𝓠 n) M k) :
    tsupport (a • ω) ⊆ tsupport ω :=
  closure_mono fun x hx h => hx (by
    change a • ω x = 0
    rw [show ω x = 0 from h, smul_zero])

theorem contMDiffForm_smul {r : WithTop ℕ∞} (a : ℝ) {ω : ManifoldForm (𝓠 n) M k}
    (hω : ContMDiffForm (𝓠 n) r ω) : ContMDiffForm (𝓠 n) r (a • ω) := fun x => by
  rw [chartForm_smul_eq]; exact (hω x).const_smul a

variable [IsManifold (𝓠 n) ∞ M] [T2Space M] [SigmaCompactSpace M]
  {o : TangentOrientation (𝓠 n) M n}

/-- **`∫_M` is homogeneous** on continuous compactly supported forms. -/
theorem integral_smul_eq (ho : o.IsContinuous (𝓠 n) ∞) {ω : ManifoldForm (𝓠 n) M n}
    (hω : ContMDiffForm (𝓠 n) 0 ω) (hc : IsCompact (tsupport ω)) (a : ℝ) :
    integral o (a • ω) = a * integral o ω := by
  obtain ⟨T, ⟨D⟩⟩ := exists_integrationData ho hc
  rw [integral_eq_integrationData ho (contMDiffForm_smul a hω)
      (hc.of_isClosed_subset isClosed_closure (tsupport_smul_subset a ω)) D
      (tsupport_smul_subset a ω), integral_eq_integrationData ho hω hc D subset_rfl,
    D.integral_smul_eq]

variable [CompactSpace M] (ho : o.IsContinuous (𝓠 n) ∞)

/-- **For compact `M`, `∫_M` is a linear map** on the `C^∞` `n`-forms. -/
def integralₗ {V : Type*} [AddCommGroup V] [Module ℝ V] (F : V →ₗ[ℝ] ManifoldForm (𝓠 n) M n)
    (hF : ∀ v, ContMDiffForm (𝓠 n) 0 (F v)) : V →ₗ[ℝ] ℝ where
  toFun v := integral o (F v)
  map_add' v w := by
    rw [map_add]
    exact integral_add ho (hF v) (hF w) isClosed_closure.isCompact isClosed_closure.isCompact
  map_smul' a v := by
    rw [map_smul]
    exact integral_smul_eq ho (hF v) isClosed_closure.isCompact a

theorem integralₗ_apply {V : Type*} [AddCommGroup V] [Module ℝ V]
    (F : V →ₗ[ℝ] ManifoldForm (𝓠 n) M n) (hF : ∀ v, ContMDiffForm (𝓠 n) 0 (F v)) (v : V) :
    integralₗ ho F hF v = integral o (F v) :=
  rfl

end Smul

/-! #### Dimension `0`: the integral is a signed sum over the points -/

section DimZero

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant 0) M]

theorem subsingleton_euclideanQuadrant_zero : Subsingleton (EuclideanQuadrant 0) :=
  ⟨fun _ _ => Subtype.ext (Subsingleton.elim _ _)⟩

/-- In dimension `0` the chart at `x` is defined on `{x}` only. -/
theorem chartAt_source_eq_singleton_of_dim_zero (x : M) :
    (chartAt (EuclideanQuadrant 0) x).source = {x} := by
  have := subsingleton_euclideanQuadrant_zero
  refine Subset.antisymm (fun y hy => ?_) (singleton_subset_iff.2 (mem_chart_source _ x))
  exact (chartAt (EuclideanQuadrant 0) x).injOn hy (mem_chart_source _ x) (Subsingleton.elim _ _)

/-- **A `0`-dimensional manifold is discrete.** -/
theorem discreteTopology_of_dim_zero : DiscreteTopology M :=
  discreteTopology_iff_isOpen_singleton.2 fun x => by
    rw [← chartAt_source_eq_singleton_of_dim_zero x]
    exact (chartAt (EuclideanQuadrant 0) x).open_source

/-- **A compact `0`-dimensional manifold is finite.** -/
theorem finite_of_dim_zero [CompactSpace M] : Finite M :=
  haveI := discreteTopology_of_dim_zero (M := M)
  finite_of_compact_of_discrete

/-- In dimension `0` every form is `C^r` (the charts are defined on a point). -/
theorem contMDiffForm_of_dim_zero {k : ℕ} (r : WithTop ℕ∞) (ω : ManifoldForm (𝓠 0) M k) :
    ContMDiffForm (𝓠 0) r ω := fun x =>
  (contDiffOn_const (c := chartForm (𝓠 0) (chartAt (EuclideanQuadrant 0) x) ω 0)).congr
    fun y _ => by rw [Subsingleton.elim y 0]

/-- **The chart integral in dimension `0`** is the value at the point: `ℝ⁰` has volume `1`
(`topFormIntegral_univ_fin_zero`). -/
theorem chartIntegral_of_dim_zero (x : M) (ω : ManifoldForm (𝓠 0) M 0) :
    chartIntegral (chartAt (EuclideanQuadrant 0) x) ω = ω x 0 := by
  have ht : ((chartAt (EuclideanQuadrant 0) x).extend (𝓠 0)).target = univ :=
    Set.Nonempty.eq_univ ⟨_, ((chartAt (EuclideanQuadrant 0) x).extend (𝓠 0)).map_source
      (by rw [OpenPartialHomeomorph.extend_source]; exact mem_chart_source _ x)⟩
  rw [chartIntegral, ht, topFormIntegral_univ_fin_zero,
    Subsingleton.elim (0 : EuclideanSpace ℝ (Fin 0)) (extChartAt (𝓠 0) x x)]
  refine (congrArg (fun φ => φ (stdFrame 0)) (chartForm_extChartAt_self ω x)).trans ?_
  exact congrArg _ (Subsingleton.elim _ _)

open Classical in
/-- **The integral over a finite `0`-dimensional manifold** (the case `k = 0` of Theorem 6.7.1,
2021 p. 277): `∫_M ω = ∑_x ε(x) ω(x)`, with `ε(x) = ±1` the sign of the orientation `o x` of
`T_xM = ℝ⁰` (`+1` for the standard orientation) and `ω(x) = ω x 0` the value of the `0`-form. -/
theorem integral_eq_sum_of_dim_zero [IsManifold (𝓠 0) ∞ M] [T2Space M] [Fintype M]
    {o : TangentOrientation (𝓠 0) M 0} (ho : o.IsContinuous (𝓠 0) ∞) (ω : ManifoldForm (𝓠 0) M 0) :
    integral o ω =
      ∑ x, orSign (decide (tangentOrToModel (o x) = stdOrientation 0)) * ω x 0 := by
  classical
  set ωx : M → ManifoldForm (𝓠 0) M 0 := fun x y => if y = x then ω y else 0 with hωx
  have hsum : ω = ∑ x, ωx x := by
    funext y
    rw [Finset.sum_apply]
    simp only [hωx, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  calc integral o ω = integral o (∑ x, ωx x) := by rw [← hsum]
    _ = ∑ x, integral o (ωx x) := integral_finsetSum ho Finset.univ
        (fun x _ => contMDiffForm_of_dim_zero _ _) fun x _ => isClosed_closure.isCompact
    _ = _ := Finset.sum_congr rfl fun x _ => ?_
  rw [integral_eq_chartIntegral ho (contMDiffForm_of_dim_zero _ (ωx x)) (V := {x})
    (singleton_subset_iff.2 (mem_chart_source _ x))
    (b := decide (tangentOrToModel (o x) = stdOrientation 0)) ?_ isCompact_singleton subset_rfl
    (fun y hy => by simp only [hωx]; exact if_neg hy), chartIntegral_of_dim_zero]
  · simp only [hωx, if_true]
  · rintro y rfl
    rw [orientationIn_chartAt]
    by_cases h : tangentOrToModel (o y) = stdOrientation 0
    · simp [h]
    · simp only [h, decide_false, signedOr_false]
      exact ((tangentOrToModel (o y)).eq_or_eq_neg (stdOrientation 0) (by simp)).resolve_left h

end DimZero

/-! #### The empty manifold -/

section Empty

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [IsEmpty M]

theorem integral_of_isEmpty [ChartedSpace (EuclideanQuadrant n) M] [IsManifold (𝓠 n) ∞ M]
    (o : TangentOrientation (𝓠 n) M n) (ω : ManifoldForm (𝓠 n) M n) : integral o ω = 0 := by
  rw [integral]
  split_ifs
  · exact Finset.sum_eq_zero fun j _ => isEmptyElim j.1
  · rfl

theorem boundaryIntegral_of_isEmpty [ChartedSpace (EuclideanQuadrant (n + 1)) M]
    [IsManifold (𝓠 (n + 1)) ∞ M] (o : TangentOrientation (𝓠 (n + 1)) M (n + 1))
    (ω : ManifoldForm (𝓠 (n + 1)) M n) : boundaryIntegral o ω = 0 := by
  rw [boundaryIntegral]
  split_ifs
  · exact Finset.sum_eq_zero fun j _ => isEmptyElim j.1
  · rfl

end Empty

end ManifoldForm

theorem faceIntegral_of_isEmpty {n : ℕ} {M : Type*} [TopologicalSpace M] [IsEmpty M]
    [ChartedSpace (EuclideanQuadrant (n + 1)) M] [IsManifold (𝓠 (n + 1)) ∞ M]
    (o : TangentOrientation (𝓠 (n + 1)) M (n + 1)) (σ : FaceFormData M n n) :
    faceIntegral o σ = 0 := by
  rw [faceIntegral]
  split_ifs
  · exact ManifoldForm.boundaryIntegral_of_isEmpty o _
  · rfl

/-! ### Admissible sections -/

section Admissible

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

namespace StrongBundle

variable (B) in
/-- **Admissible sections** (2021 §6.7, p. 276; preprint §6.7, before Theorem 6.43): an
sc⁺-section `s` supported in `U` with `N(s(x)) ≤ 1` (`allowableSections N U`) such that
`(f + s, x)` is in general position at every zero `x` of `f + s`. -/
structure IsAdmissible (f : X → Y) (N : B.One → ℝ) (U : Set X) (s : X → Y) : Prop where
  mem : s ∈ B.allowableSections N U
  gp : ∀ x, IsZeroAt P (sectionAdd P f s) x → B.IsGeneralPositionGerm (sectionAdd P f s) x

variable {f s : X → Y} {N : B.One → ℝ} {U : Set X}

theorem IsAdmissible.isScPlusSection (hs : B.IsAdmissible f N U s) : B.IsScPlusSection s :=
  hs.mem.1

/-- **Admissible sections exist** for every auxiliary norm `N` and every open `U ⊇ S_f`
(2021 §6.7, p. 276, from Theorem 5.3.10; `exists_admissible`): the hypothesis `IsAdmissible` is
satisfiable. -/
theorem exists_isAdmissible (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) (hS : IsCompact (solutionSet P f)) (hN : B.IsAuxNorm N)
    (hU : IsOpen U) (hSU : solutionSet P f ⊆ U) : ∃ s, B.IsAdmissible f N U s := by
  obtain ⟨s, hs, hgp⟩ := exists_admissible hX hbump hf hS hN hU hSU
  exact ⟨s, hs, hgp⟩

/-- **The neighbourhood `U` of the §6.7 preamble** (2021, p. 276): for a tame `f` with compact
solution set and an auxiliary norm `N` there is an open `U ⊇ S_f` (with the margin of reading R-b:
`cl{x ∈ U | N(f(x)) ≤ C}` compact for `C > 0`) such that `S_{f+s}` is compact for every
allowable `s`, and admissible sections for `(N, U)` exist (`exists_adapted_margin`,
`exists_isAdmissible`). -/
theorem exists_isAdmissible_nbhd (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) (hS : IsCompact (solutionSet P f)) (hN : B.IsAuxNorm N) :
    ∃ U : Set X, IsOpen U ∧ solutionSet P f ⊆ U ∧
      (∀ C : ℝ, 0 < C → IsCompact (closure {x ∈ U | B.AuxLe N (f x) C})) ∧
      (∀ s ∈ B.allowableSections N U, IsCompact (solutionSet P (sectionAdd P f s))) ∧
      ∃ s, B.IsAdmissible f N U s := by
  obtain ⟨U, hUo, hSU, -, hmar, hcpt⟩ :=
    exists_adapted_margin hf.toIsScFredholmSection hS hN isOpen_univ (subset_univ _)
  exact ⟨U, hUo, hSU, hmar, hcpt, exists_isAdmissible hX hbump hf hS hN hUo hSU⟩

end StrongBundle

end Admissible

/-! ### The index parts `S_k` of `S_{f+s}` (reading R-c) -/

section IndexParts

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f s : X → Y}

namespace StrongBundle

variable (B) in
/-- The open set cutting out the index part: the complement of the zeros of `f + s` at which the
germ `(f, x)` does not have index `k`. -/
def solIndexNbhd (f s : X → Y) (k : ℕ) : Set X :=
  (solutionSet P (sectionAdd P f s) \ {x | B.IsIndexAt f x k})ᶜ

variable (B) in
/-- **The index-`k` part `S_k` of `S_{f+s}`** (reading R-c of Theorem 6.7.1, 2021 p. 277): the
zeros `x` of `f + s` at which `f` has index `k` (Definition 6.2.1, p. 239), written as
`S_{f+s} ∩ V_k` with `V_k = solIndexNbhd`, which is open for admissible `s`
(`isOpen_solIndexNbhd`). -/
def solPart (f s : X → Y) (k : ℕ) : Set X :=
  solutionSet P (sectionAdd P f s) ∩ B.solIndexNbhd f s k

theorem solPart_eq (k : ℕ) :
    B.solPart f s k = {x ∈ solutionSet P (sectionAdd P f s) | B.IsIndexAt f x k} := by
  ext x
  simp only [solPart, solIndexNbhd, mem_inter_iff, mem_compl_iff, Set.mem_sdiff, mem_ofPred_eq]
  tauto

theorem mem_solPart_iff {k : ℕ} {x : X} :
    x ∈ B.solPart f s k ↔ IsZeroAt P (sectionAdd P f s) x ∧ B.IsIndexAt f x k := by
  rw [solPart_eq]; exact Iff.rfl

theorem solPart_subset (k : ℕ) : B.solPart f s k ⊆ solutionSet P (sectionAdd P f s) :=
  inter_subset_left

/-- At a zero of `f + s` (`s` sc⁺), the index of the germ `(f, x)` is that of `(f + s)'(x)`
(Definition 6.2.1 is well defined, `isLinOfIndex_sectionAdd_of_isZeroAt`). -/
theorem isLinOfIndex_sectionAdd_of_isIndexAt (hf : B.IsScFredholmSection f)
    (hs : B.IsScPlusSection s) {x : X} (hx : IsZeroAt P (sectionAdd P f s) x) {i : ℤ}
    (h : B.IsIndexAt f x i) : B.IsLinOfIndex (sectionAdd P f s) x i := by
  obtain ⟨s', hs', hs'x, hL⟩ := h
  have hfs : IsSection P f := hf.isScSmooth.1
  have hd : B.IsScPlusSection (sectionDiff P s s') :=
    hs.add (hs'.smul_left (isScSmoothMap_real_const (-1)))
  have hdx : IsZeroAt P (sectionDiff P s s') x :=
    isZeroAt_sectionDiff_of_isZeroAt_sectionAdd hfs hs'.1 hs.1 hs'x hx
  have h := isLinOfIndex_sectionAdd_of_isZeroAt (theorem_3_1_18_preprint hf hs') hd hs'x hdx hL
  rwa [sectionAdd_sectionAdd_sectionDiff hfs hs'.1 hs.1] at h

theorem isIndexAt_iff_isLinOfIndex (hf : B.IsScFredholmSection f) (hs : B.IsScPlusSection s)
    {x : X} (hx : IsZeroAt P (sectionAdd P f s) x) {i : ℤ} :
    B.IsIndexAt f x i ↔ B.IsLinOfIndex (sectionAdd P f s) x i :=
  ⟨isLinOfIndex_sectionAdd_of_isIndexAt hf hs hx, fun h => ⟨s, hs, hx, h⟩⟩

/-- `S_{f+s} \ S_k` as the image of a subset of `S_{f+s}`. -/
theorem solutionSet_diff_eq_image (hf : B.IsScFredholmSection f) (hs : B.IsScPlusSection s)
    (k : ℕ) : solutionSet P (sectionAdd P f s) \ {x | B.IsIndexAt f x k} =
      Subtype.val '' {x : solutionSet P (sectionAdd P f s) |
        B.IsLinOfIndex (sectionAdd P f s) x.1 k}ᶜ := by
  ext x
  simp only [Set.mem_sdiff, mem_ofPred_eq, mem_image, mem_compl_iff, Subtype.exists,
    exists_and_right, exists_eq_right]
  exact ⟨fun ⟨hx, hk⟩ => ⟨hx, fun h => hk ((isIndexAt_iff_isLinOfIndex hf hs hx).2 h)⟩,
    fun ⟨hx, hk⟩ => ⟨hx, fun h => hk ((isIndexAt_iff_isLinOfIndex hf hs hx).1 h)⟩⟩

/-- `S_k` as the image of a subset of `S_{f+s}`. -/
theorem solPart_eq_image (hf : B.IsScFredholmSection f) (hs : B.IsScPlusSection s) (k : ℕ) :
    B.solPart f s k = Subtype.val '' {x : solutionSet P (sectionAdd P f s) |
      B.IsLinOfIndex (sectionAdd P f s) x.1 k} := by
  rw [solPart_eq]
  ext x
  simp only [mem_ofPred_eq, mem_image, Subtype.exists, exists_and_right, exists_eq_right]
  exact ⟨fun ⟨hx, hk⟩ => ⟨hx, (isIndexAt_iff_isLinOfIndex hf hs hx).1 hk⟩,
    fun ⟨hx, hk⟩ => ⟨hx, (isIndexAt_iff_isLinOfIndex hf hs hx).2 hk⟩⟩

/-- **`V_k` is open** for `f + s` in general position at every zero: `S_{f+s}` is closed and the
part of index `≠ k` is closed in it (`isClopen_index_part`, the index is locally constant). -/
theorem isOpen_solIndexNbhd (hf : B.IsScFredholmSectionTame f) (hs : B.IsScPlusSection s)
    (hgp : ∀ x, IsZeroAt P (sectionAdd P f s) x → B.IsGeneralPositionGerm (sectionAdd P f s) x)
    (k : ℕ) : IsOpen (B.solIndexNbhd f s k) := by
  have hft := theorem_3_1_18_tame hf hs
  have hSc : IsClosed (solutionSet P (sectionAdd P f s)) := isClosed_solutionSet hft.isScSmooth
  rw [solIndexNbhd, isOpen_compl_iff, solutionSet_diff_eq_image hf.toIsScFredholmSection hs]
  exact hSc.isClosedMap_subtype_val _ (isClopen_index_part hft hgp k).compl.isClosed

/-- **`S_k` is closed** (and so compact when `S_{f+s}` is). -/
theorem isClosed_solPart (hf : B.IsScFredholmSectionTame f) (hs : B.IsScPlusSection s)
    (hgp : ∀ x, IsZeroAt P (sectionAdd P f s) x → B.IsGeneralPositionGerm (sectionAdd P f s) x)
    (k : ℕ) : IsClosed (B.solPart f s k) := by
  have hft := theorem_3_1_18_tame hf hs
  have hSc : IsClosed (solutionSet P (sectionAdd P f s)) := isClosed_solutionSet hft.isScSmooth
  rw [solPart_eq_image hf.toIsScFredholmSection hs]
  exact hSc.isClosedMap_subtype_val _ (isClopen_index_part hft hgp k).isClosed

theorem isCompact_solPart (hf : B.IsScFredholmSectionTame f) (hs : B.IsScPlusSection s)
    (hgp : ∀ x, IsZeroAt P (sectionAdd P f s) x → B.IsGeneralPositionGerm (sectionAdd P f s) x)
    (hS : IsCompact (solutionSet P (sectionAdd P f s))) (k : ℕ) :
    IsCompact (B.solPart f s k) :=
  hS.of_isClosed_subset (isClosed_solPart hf hs hgp k) (solPart_subset k)

/-- `S_{f+s}` is the union of its index parts. -/
theorem solutionSet_eq_iUnion_solPart (hf : B.IsScFredholmSectionTame f)
    (hs : B.IsScPlusSection s)
    (hgp : ∀ x, IsZeroAt P (sectionAdd P f s) x → B.IsGeneralPositionGerm (sectionAdd P f s) x) :
    solutionSet P (sectionAdd P f s) = ⋃ k : ℕ, B.solPart f s k := by
  ext x
  simp only [mem_iUnion, mem_solPart_iff]
  refine ⟨fun hx => ?_, fun ⟨_, hx, _⟩ => hx⟩
  have hft := theorem_3_1_18_tame hf hs
  obtain ⟨V, d, -, hxV, hind⟩ := theorem_3_6_8_index_locally_constant hft
    ((hgp x hx).isGoodPositionGermTame hft hx) hx
  exact ⟨d, hx, (isIndexAt_iff_isLinOfIndex hf.toIsScFredholmSection hs hx).2
    (hind x hxV hx).isLinOfIndex⟩

/-- **Constant index `n`** (2021 p. 279, the remark after the proof of Theorem 6.7.1, where
`Ψ` is `∫_{S_{f+s}} ω` in the degree `n` of the index of `f`, and zero otherwise): if `f` has
index `n` at every smooth point, then `S_k = ∅` for `k ≠ n`, so `Ψ = 0` in degree `k`
(`psiAt_of_eq_empty`). -/
theorem solPart_eq_empty_of_ne (hf : B.IsScFredholmSection f) (hs : B.IsScPlusSection s) {n k : ℕ}
    (hn : ∀ x ∈ PX.smoothSet, B.IsIndexAt f x n) (hk : k ≠ n) : B.solPart f s k = ∅ := by
  refine eq_empty_of_forall_notMem fun x hx => hk ?_
  have hx' := mem_solPart_iff.1 hx
  have hsm := (theorem_3_1_18_preprint hf hs).mem_smoothSet_of_isZeroAt hx'.1
  exact_mod_cast hx'.2.unique hf (hn x hsm)

/-- **Constant index `n`** (2021 p. 279): `S_n = S_{f+s}`. -/
theorem solPart_eq_solutionSet (hf : B.IsScFredholmSection f) (hs : B.IsScPlusSection s) {n : ℕ}
    (hn : ∀ x ∈ PX.smoothSet, B.IsIndexAt f x n) :
    B.solPart f s n = solutionSet P (sectionAdd P f s) := by
  refine Subset.antisymm (solPart_subset n) fun x hx => mem_solPart_iff.2 ⟨hx, hn x ?_⟩
  exact (theorem_3_1_18_preprint hf hs).mem_smoothSet_of_isZeroAt hx

end StrongBundle

end IndexParts

/-! ### `S_k` as a compact oriented Mathlib manifold of dimension `k` -/

section Structure

open MPolyfold StrongBundle

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f s : X → Y} {N : B.One → ℝ} {U : Set X}

/-- `S_k` is paracompact (`X` is metrizable). -/
instance paracompactSpace_solPart (k : ℕ) : ParacompactSpace ↥(B.solPart f s k) :=
  PX.paracompactSpace_subtype _

/-- `f + s` is a tame sc-Fredholm section (Theorem 3.1.18, 2021 p. 98). -/
theorem StrongBundle.IsAdmissible.sectionAdd_tame (hf : B.IsScFredholmSectionTame f)
    (hs : B.IsAdmissible f N U s) : B.IsScFredholmSectionTame (sectionAdd P f s) :=
  theorem_3_1_18_tame hf hs.isScPlusSection

theorem StrongBundle.IsAdmissible.mem_smoothSet (hf : B.IsScFredholmSectionTame f)
    (hs : B.IsAdmissible f N U s) {k : ℕ} {x : X} (hx : x ∈ B.solPart f s k) :
    x ∈ PX.smoothSet :=
  (hs.sectionAdd_tame hf).toIsScFredholmSection.mem_smoothSet_of_isZeroAt hx.1

variable (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions) (hf : B.IsScFredholmSectionTame f)
  (hs : B.IsAdmissible f N U s) (o : SectionOrientation f hf.toIsScFredholmSection) (k : ℕ)

include hf hs in
/-- Every zero in `V_k` has index `k`. -/
theorem isLinOfIndex_of_mem_solIndexNbhd :
    ∀ y ∈ B.solIndexNbhd f s k, IsZeroAt P (sectionAdd P f s) y →
      B.IsLinOfIndex (sectionAdd P f s) y k := fun _ hyV hy =>
  isLinOfIndex_sectionAdd_of_isIndexAt hf.toIsScFredholmSection hs.isScPlusSection hy
    (mem_solPart_iff.1 ⟨hy, hyV⟩).2

include hf hs in
theorem isOpen_solIndexNbhd_of_isAdmissible : IsOpen (B.solIndexNbhd f s k) :=
  isOpen_solIndexNbhd hf hs.isScPlusSection hs.gp k

include hf hs in
/-- **`S_k` is a `k`-dimensional submanifold** (Theorem 3.6.8, 2021 p. 136). -/
theorem isSubmanifoldOfDim_solPart : PX.IsSubmanifoldOfDim (B.solPart f s k) k :=
  isSubmanifoldOfDim_inter_open (theorem_3_1_18_tame hf hs.isScPlusSection)
    (isOpen_solIndexNbhd_of_isAdmissible hf hs k) (fun x _ hx => hs.gp x hx)
    (isLinOfIndex_of_mem_solIndexNbhd hf hs k)

include hf hs in
theorem isSubMPolyfold_solPart : PX.IsSubMPolyfold (B.solPart f s k) :=
  (isSubmanifoldOfDim_solPart hf hs k).1.isSubMPolyfold

include hX hf hs in
/-- **`S_k` is in general position at each of its points** (Definition 4.2.10, 2021 p. 190;
`exists_isOpen_isGeneralPositionGerm`). -/
theorem isGeneralPositionAt_solPart :
    ∀ y ∈ B.solPart f s k, PX.IsGeneralPositionAt (B.solPart f s k) y := by
  have hft := theorem_3_1_18_tame hf hs.isScPlusSection
  have hV := isOpen_solIndexNbhd_of_isAdmissible hf hs k
  intro y hy
  obtain ⟨W, hWo, hyW, hWA, hW⟩ := exists_isOpen_isGeneralPositionGerm hX hft hy.1 (hs.gp y hy.1)
  refine MPolyfold.IsGeneralPositionAt.congr_nhds hWA (isSubmanifoldOfDim_solPart hf hs k).1
    (hWo.inter hV) ⟨hyW, hy.2⟩ ?_ (hW y hyW hy.1).2.2
  ext w
  simp only [solPart, mem_inter_iff]
  tauto

include hX hf hs in
/-- **`d_{S_k} = d_X`** (Theorem 4.2.11 (2), 2021 p. 190). -/
theorem degIndex_solPart (a : ↥(B.solPart f s k)) :
    (subPolyfold (isSubMPolyfold_solPart hf hs k)).degIndex a = PX.degIndex a := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, W, -, haW, -, -, -, h2, -⟩ :=
    MPolyfold.theorem_4_2_11_preprint hX (isSubmanifoldOfDim_solPart hf hs k).1
      (isGeneralPositionAt_solPart hX hf hs k a a.2)
  exact h2 a haW

include hX hf hs in
/-- **The corner structure of dimension `k` of `S_k`** (Theorem 4.2.7, 2021 p. 188). -/
theorem hasCornerStructureOfDim_solPart :
    (subPolyfold (isSubMPolyfold_solPart hf hs k)).HasCornerStructureOfDim k :=
  (isSubmanifoldOfDim_solPart hf hs k).hasCornerStructureOfDim_of_tame hX
    (isGoodPositionAt_inter_open hX (theorem_3_1_18_tame hf hs.isScPlusSection)
      (isOpen_solIndexNbhd_of_isAdmissible hf hs k) (fun x _ hx => hs.gp x hx))

/-- **The charted space of `S_k`**: the corner charts of its corner structure of dimension `k`
(`cornerChartedSpace`; it is `solChartedSpaceOpen` for `V = V_k`). -/
abbrev solPartChartedSpace : ChartedSpace (EuclideanQuadrant k) ↥(B.solPart f s k) :=
  (subPolyfold (isSubMPolyfold_solPart hf hs k)).cornerChartedSpace
    (hasCornerStructureOfDim_solPart hX hf hs k)

theorem isManifold_solPart :
    letI := solPartChartedSpace hX hf hs k
    IsManifold (𝓠 k) ∞ ↥(B.solPart f s k) :=
  letI := solPartChartedSpace hX hf hs k
  isManifold_of_eq (hasCornerStructureOfDim_solPart hX hf hs k) rfl

/-- **The orientation of `S_k`** (2021 Theorem 6.6.18, p. 275, and §6.7, p. 277): at `x`, the
orientation of `T_xS_k = ker (f + s)'(x)` given by `o_x` (`solOrOpen` for the orientation
`o.sectionAdd` of `f + s`). -/
def solPartOr :
    letI := solPartChartedSpace hX hf hs k
    TangentOrientation (𝓠 k) ↥(B.solPart f s k) k :=
  letI := solPartChartedSpace hX hf hs k
  haveI : Fact (IsOpen (B.solIndexNbhd f s k)) := ⟨isOpen_solIndexNbhd_of_isAdmissible hf hs k⟩
  haveI : ParacompactSpace ↥(solutionSet P (sectionAdd P f s) ∩ B.solIndexNbhd f s k) :=
    PX.paracompactSpace_subtype _
  fun x => modelOrToTangent x (solOrOpen (Ω := B.solIndexNbhd f s k)
    (theorem_3_1_18_tame hf hs.isScPlusSection) (SectionOrientation.sectionAdd o hs.isScPlusSection)
    (fun x hx => hs.gp x hx.1) (fun y hy => isLinOfIndex_of_mem_solIndexNbhd hf hs k y hy.2 hy.1)
    (hasCornerStructureOfDim_solPart hX hf hs k) x)

include hbump in
/-- **The orientation of `S_k` is continuous** (`isContinuous_solOr_open`). -/
theorem isContinuous_solPartOr :
    letI := solPartChartedSpace hX hf hs k
    (solPartOr hX hf hs o k).IsContinuous (𝓠 k) ∞ :=
  letI := solPartChartedSpace hX hf hs k
  haveI : Fact (IsOpen (B.solIndexNbhd f s k)) := ⟨isOpen_solIndexNbhd_of_isAdmissible hf hs k⟩
  haveI : ParacompactSpace ↥(solutionSet P (sectionAdd P f s) ∩ B.solIndexNbhd f s k) :=
    PX.paracompactSpace_subtype _
  isContinuous_solOr_open (Ω := B.solIndexNbhd f s k) (inst := solPartChartedSpace hX hf hs k)
    (theorem_3_1_18_tame hf hs.isScPlusSection) (SectionOrientation.sectionAdd o hs.isScPlusSection)
    (fun x hx => hs.gp x hx.1) (fun y hy => isLinOfIndex_of_mem_solIndexNbhd hf hs k y hy.2 hy.1)
    (hasCornerStructureOfDim_solPart hX hf hs k) hX hbump rfl

/-- **`S_k` is a compact oriented manifold with boundary and corners of dimension `k`**
(2021 Theorem 6.7.1 (1), p. 277, for the part of index `k`): with the corner charts
(`solPartChartedSpace`) it is a Hausdorff Mathlib manifold `IsManifold (𝓠 k) ∞`, compact when
`S_{f+s}` is; its orientation `solPartOr` is continuous and is `o_x` on `T_xS_k = ker (f + s)'(x)`
(the natural orientation of Theorem 6.6.18 for the orientation `o.sectionAdd` of `f + s`). -/
structure SolPartIsOrientedManifold : Prop where
  isManifold :
    letI := solPartChartedSpace hX hf hs k
    IsManifold (𝓠 k) ∞ ↥(B.solPart f s k)
  t2Space : T2Space ↥(B.solPart f s k)
  compactSpace : IsCompact (solutionSet P (sectionAdd P f s)) → CompactSpace ↥(B.solPart f s k)
  isContinuous :
    letI := solPartChartedSpace hX hf hs k
    (solPartOr hX hf hs o k).IsContinuous (𝓠 k) ∞
  natural : IsNaturalSolutionOrientation (sectionAdd P f s)
    (theorem_3_1_18_tame hf hs.isScPlusSection) hs.gp
    (SectionOrientation.sectionAdd o hs.isScPlusSection)
  spec :
    letI := solPartChartedSpace hX hf hs k
    ∀ (x : ↥(B.solPart f s k)) (c : StrongBundleChart PX P) (hc : B.IsChart c)
      (hxc : x.1 ∈ c.φ.source),
      ∃ ι : EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ]
          c.linKer (sectionAdd P f s) (chartPtOf c hc hxc (hs.mem_smoothSet hf x.2)).z,
        (∀ v, (ι v : c.φ.model.E 0) = derivIn (𝓠 k) (chartAt (EuclideanQuadrant k) x)
          (fun y : ↥(B.solPart f s k) => c.φ y.1) x v) ∧
        ∀ b : Basis (Fin k) ℝ (EuclideanSpace ℝ (Fin k)),
          b.orientation = tangentOrToModel (solPartOr hX hf hs o k x) ↔
            (chartPtOf c hc hxc (hs.mem_smoothSet hf x.2)).tangentOr
                (hs.sectionAdd_tame hf).toIsScFredholmSection x.2.1 (hs.gp x.1 x.2.1).isLinSurjAt
                (toChartOr (hs.sectionAdd_tame hf).toIsScFredholmSection
                  (hs.mem_smoothSet hf x.2) c hc hxc
                  ((SectionOrientation.sectionAdd o hs.isScPlusSection).1 x.1
                    (hs.mem_smoothSet hf x.2))) =
              rayOfNeZero ℝ _ (wedge_equiv_ne_zero finrank_euclideanSpace_fin ι b)

include hbump in
/-- **`S_k` is a compact oriented manifold** (`SolPartIsOrientedManifold`), from
`theorem_6_6_18_oriented_open` for `V = V_k` and `isNaturalSolutionOrientation`. -/
theorem solPartIsOrientedManifold :
    SolPartIsOrientedManifold hX hf hs o k := by
  let := solPartChartedSpace hX hf hs k
  have : Fact (IsOpen (B.solIndexNbhd f s k)) := ⟨isOpen_solIndexNbhd_of_isAdmissible hf hs k⟩
  have : ParacompactSpace ↥(solutionSet P (sectionAdd P f s) ∩ B.solIndexNbhd f s k) :=
    PX.paracompactSpace_subtype _
  refine ⟨isManifold_solPart hX hf hs k, inferInstance, fun hS => ?_,
    isContinuous_solPartOr hX hbump hf hs o k,
    isNaturalSolutionOrientation _ hs.gp _, fun x c hc hxc => ?_⟩
  · exact isCompact_iff_compactSpace.1
      (isCompact_solPart hf hs.isScPlusSection hs.gp hS k)
  · exact solOr_spec_open (Ω := B.solIndexNbhd f s k) (inst := solPartChartedSpace hX hf hs k)
      (theorem_3_1_18_tame hf hs.isScPlusSection)
      (SectionOrientation.sectionAdd o hs.isScPlusSection)
      (fun x hx => hs.gp x hx.1)
      (fun y hy => isLinOfIndex_of_mem_solIndexNbhd hf hs k y hy.2 hy.1)
      (hasCornerStructureOfDim_solPart hX hf hs k) rfl x hc hxc

end Structure

/-! ### The integrals `∫_{S_k} ω|_S` and `∫_{∂S_k} τ|_{∂S}` -/

section Integrals

open MPolyfold StrongBundle

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f s : X → Y} {N : B.One → ℝ} {U : Set X}
  (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions) (hf : B.IsScFredholmSectionTame f)
  (hs : B.IsAdmissible f N U s) (o : SectionOrientation f hf.toIsScFredholmSection)

open Classical in
/-- **`ω ↦ ∫_{S_k} ω|_S`** on `Ωᵏ_∞(X)` (2021 Theorem 6.7.1, p. 277, formula (6.35)): the
integral over the `k`-dimensional part `S_k` of `S_{f+s}`, oriented by `solPartOr`, of the
restriction `ω|_S` (`formsInftyRestrict`); `0` if `S_k` is not compact. -/
def solFormsIntegral (k : ℕ) : (BundledMPolyfold.of PX).formsInfty k →ₗ[ℝ] ℝ :=
  letI := solPartChartedSpace hX hf hs k
  haveI := isManifold_solPart hX hf hs k
  if h : IsCompact (B.solPart f s k) then
    haveI := isCompact_iff_compactSpace.1 h
    ManifoldForm.integralₗ (isContinuous_solPartOr hX hbump hf hs o k)
      (formsInftyRestrict k (hasCornerStructureOfDim_solPart hX hf hs k))
      fun ω => (contMDiffForm_formsInftyRestrict rfl ω).of_le zero_le
  else 0

theorem solFormsIntegral_apply {k : ℕ} (h : IsCompact (B.solPart f s k))
    (ω : (BundledMPolyfold.of PX).formsInfty k) :
    letI := solPartChartedSpace hX hf hs k
    haveI := isManifold_solPart hX hf hs k
    solFormsIntegral hX hbump hf hs o k ω = ManifoldForm.integral (solPartOr hX hf hs o k)
      (formsInftyRestrict k (hasCornerStructureOfDim_solPart hX hf hs k) ω) := by
  simp only [solFormsIntegral, dif_pos h]
  rfl

theorem solFormsIntegral_of_not_isCompact {k : ℕ} (h : ¬ IsCompact (B.solPart f s k)) :
    solFormsIntegral hX hbump hf hs o k = 0 := by
  simp only [solFormsIntegral, dif_neg h]

open Classical in
/-- **`τ ↦ ∫_{∂S_{m+1}} τ|_{∂S}`** on `Ωᵐ_∞(∂X)` (2021 Theorem 6.7.1, p. 277, formula (6.35)):
the integral over the boundary of the `(m+1)`-dimensional part `S_{m+1}` of the restriction of
`τ` to its faces (`solFaceForm`, `ChartFaceForm.integral`); `0` if `S_{m+1}` is not compact. -/
def solBFormsIntegral (m : ℕ) : bFormsInfty hX m →ₗ[ℝ] ℝ :=
  letI := solPartChartedSpace hX hf hs (m + 1)
  haveI := isManifold_solPart hX hf hs (m + 1)
  if h : IsCompact (B.solPart f s (m + 1)) then
    haveI := isCompact_iff_compactSpace.1 h
    (ChartFaceForm.integralₗ (isContinuous_solPartOr hX hbump hf hs o (m + 1))).comp
      (solFaceForm (hasCornerStructureOfDim_solPart hX hf hs (m + 1)) hX
        (degIndex_solPart hX hf hs (m + 1)) rfl)
  else 0

theorem solBFormsIntegral_apply {m : ℕ} (h : IsCompact (B.solPart f s (m + 1)))
    (τ : bFormsInfty hX m) :
    letI := solPartChartedSpace hX hf hs (m + 1)
    haveI := isManifold_solPart hX hf hs (m + 1)
    solBFormsIntegral hX hbump hf hs o m τ =
      (solFaceForm (hasCornerStructureOfDim_solPart hX hf hs (m + 1)) hX
        (degIndex_solPart hX hf hs (m + 1)) rfl τ).integral (solPartOr hX hf hs o (m + 1)) := by
  simp only [solBFormsIntegral, dif_pos h]
  rfl

theorem solBFormsIntegral_of_not_isCompact {m : ℕ} (h : ¬ IsCompact (B.solPart f s (m + 1))) :
    solBFormsIntegral hX hbump hf hs o m = 0 := by
  simp only [solBFormsIntegral, dif_neg h]

/-- The component `ω ∈ Ωᵏ_∞(X)` of a relative form `(ω, τ)` (`ω` itself in degree `0`). -/
def relFormsFst : ∀ k, RelForms hX k →ₗ[ℝ] (BundledMPolyfold.of PX).formsInfty k
  | 0 => LinearMap.id
  | _ + 1 => LinearMap.fst ℝ _ _

/-- **`(ω, τ) ↦ ∫_{S_k} ω|_S`** on the relative forms of degree `k` (2021 Theorem 6.7.1 (1),
p. 277): the form of degree `k` is integrated over the part `S_k` of dimension `k`, so the
integrals of the forms of the other degrees, "defined to be zero", do not appear (reading R-c). -/
def solIntegral (k : ℕ) : RelForms hX k →ₗ[ℝ] ℝ :=
  (solFormsIntegral hX hbump hf hs o k).comp (relFormsFst hX k)

/-- **`(ω, τ) ↦ ∫_{∂S_k} τ|_{∂S}`** on the relative forms of degree `k` (2021 Theorem 6.7.1 (1),
p. 277): `0` in degree `0` (there is no `τ`); in degree `m + 1`, `τ ∈ Ωᵐ_∞(∂X)` is integrated
over the boundary of the `(m+1)`-dimensional part `S_{m+1}`. -/
def solBoundaryIntegral : ∀ k, RelForms hX k →ₗ[ℝ] ℝ
  | 0 => 0
  | m + 1 => (solBFormsIntegral hX hbump hf hs o m).comp (LinearMap.snd ℝ _ _)

theorem solIntegral_zero_apply (ω : RelForms hX 0) :
    solIntegral hX hbump hf hs o 0 ω = solFormsIntegral hX hbump hf hs o 0 ω :=
  rfl

theorem solIntegral_succ_apply (m : ℕ) (η : RelForms hX (m + 1)) :
    solIntegral hX hbump hf hs o (m + 1) η = solFormsIntegral hX hbump hf hs o (m + 1) η.1 :=
  rfl

theorem solBoundaryIntegral_zero : solBoundaryIntegral hX hbump hf hs o 0 = 0 :=
  rfl

theorem solBoundaryIntegral_succ_apply (m : ℕ) (η : RelForms hX (m + 1)) :
    solBoundaryIntegral hX hbump hf hs o (m + 1) η = solBFormsIntegral hX hbump hf hs o m η.2 :=
  rfl

/-- **`∂X = ∅`** (2021 p. 279): then `Ωᵐ_∞(∂X) = 0` (`subsingleton_bFormsInfty`), so the
boundary term `∫_{∂S_k} τ|_{∂S}` of (6.35) vanishes. -/
theorem solBoundaryIntegral_of_isWithoutBoundary (h : PX.IsWithoutBoundary) (k : ℕ) :
    solBoundaryIntegral hX hbump hf hs o k = 0 := by
  cases k with
  | zero => exact solBoundaryIntegral_zero hX hbump hf hs o
  | succ m =>
    refine LinearMap.ext fun η => ?_
    have := subsingleton_bFormsInfty (hP := hX) m h
    rw [solBoundaryIntegral_succ_apply, Subsingleton.elim η.2 0, map_zero, LinearMap.zero_apply]

/-- **The integrand of `Ψ`** (2021 (6.35), p. 277): `(ω, τ) ↦ ∫_{S} ω − ∫_{∂S} τ`, degree by
degree. -/
def psiForms (k : ℕ) : RelForms hX k →ₗ[ℝ] ℝ :=
  solIntegral hX hbump hf hs o k - solBoundaryIntegral hX hbump hf hs o k

theorem psiForms_apply (k : ℕ) (η : RelForms hX k) :
    psiForms hX hbump hf hs o k η =
      solIntegral hX hbump hf hs o k η - solBoundaryIntegral hX hbump hf hs o k η :=
  rfl

theorem solFormsIntegral_of_eq_empty {k : ℕ} (h : B.solPart f s k = ∅) :
    solFormsIntegral hX hbump hf hs o k = 0 := by
  have hc : IsCompact (B.solPart f s k) := by rw [h]; exact isCompact_empty
  let := solPartChartedSpace hX hf hs k
  have := isManifold_solPart hX hf hs k
  have : IsEmpty ↥(B.solPart f s k) := isEmpty_coe_sort.2 h
  refine LinearMap.ext fun ω => ?_
  rw [solFormsIntegral_apply hX hbump hf hs o hc, LinearMap.zero_apply]
  exact ManifoldForm.integral_of_isEmpty _ _

theorem solBFormsIntegral_of_eq_empty {m : ℕ} (h : B.solPart f s (m + 1) = ∅) :
    solBFormsIntegral hX hbump hf hs o m = 0 := by
  have hc : IsCompact (B.solPart f s (m + 1)) := by rw [h]; exact isCompact_empty
  let := solPartChartedSpace hX hf hs (m + 1)
  have := isManifold_solPart hX hf hs (m + 1)
  have : IsEmpty ↥(B.solPart f s (m + 1)) := isEmpty_coe_sort.2 h
  refine LinearMap.ext fun τ => ?_
  rw [solBFormsIntegral_apply hX hbump hf hs o hc, LinearMap.zero_apply]
  exact faceIntegral_of_isEmpty _ _

/-- **The integrals vanish when `S_k = ∅`** ("defined to be zero if the dimensions of the forms
and manifolds do not agree", 2021 Theorem 6.7.1 (1)): `ψ = 0` in degree `k`. -/
theorem psiForms_of_eq_empty {k : ℕ} (h : B.solPart f s k = ∅) :
    psiForms hX hbump hf hs o k = 0 := by
  rw [psiForms, solIntegral, solFormsIntegral_of_eq_empty hX hbump hf hs o h, LinearMap.zero_comp]
  cases k with
  | zero => rw [solBoundaryIntegral_zero, sub_zero]
  | succ m =>
    refine LinearMap.ext fun η => ?_
    rw [LinearMap.sub_apply, solBoundaryIntegral_succ_apply,
      solBFormsIntegral_of_eq_empty hX hbump hf hs o h]
    simp

/-- **`Ψ` vanishes on exact forms, degree `1`**: `∫_{S_1} dα − ∫_{∂S_1} j^*α = 0` (Stokes,
`stokes_formsInftyRestrict`, and `solFaceForm_jStar_integral`). -/
theorem psiForms_relD_zero (η : (BundledMPolyfold.of PX).formsInfty 0) :
    psiForms hX hbump hf hs o 1 (relD hX 0 η) = 0 := by
  rw [psiForms_apply, solIntegral_succ_apply, solBoundaryIntegral_succ_apply, relD_zero]
  change solFormsIntegral hX hbump hf hs o (0 + 1) ((BundledMPolyfold.of PX).formsInftyD 0 η) -
    solBFormsIntegral hX hbump hf hs o 0 (jStar hX 0 η) = 0
  by_cases h : IsCompact (B.solPart f s (0 + 1))
  · let := solPartChartedSpace hX hf hs (0 + 1)
    have := isManifold_solPart hX hf hs (0 + 1)
    have := isCompact_iff_compactSpace.1 h
    rw [solFormsIntegral_apply hX hbump hf hs o h, solBFormsIntegral_apply hX hbump hf hs o h,
      stokes_formsInftyRestrict rfl (isContinuous_solPartOr hX hbump hf hs o (0 + 1)),
      solFaceForm_jStar_integral _ hX _ rfl (isContinuous_solPartOr hX hbump hf hs o (0 + 1)),
      sub_self]
  · rw [solFormsIntegral_of_not_isCompact hX hbump hf hs o h,
      solBFormsIntegral_of_not_isCompact hX hbump hf hs o h, LinearMap.zero_apply,
      LinearMap.zero_apply, sub_self]

/-- **`Ψ` vanishes on exact forms, degree `m + 2`**: for `(dα, j^*α − dβ)`,
`∫_S dα − ∫_{∂S} j^*α + ∫_{∂S} dβ = 0` (Stokes `stokes_formsInftyRestrict`,
`solFaceForm_jStar_integral`, and `∫_{∂S} dβ = 0`: `solFaceForm_d`,
`ChartFaceForm.integral_d_eq_zero_of_compactSpace`). -/
theorem psiForms_relD_succ (m : ℕ)
    (η : (BundledMPolyfold.of PX).formsInfty (m + 1) × bFormsInfty hX m) :
    psiForms hX hbump hf hs o (m + 1 + 1) (relD hX (m + 1) η) = 0 := by
  rw [psiForms_apply, solIntegral_succ_apply, solBoundaryIntegral_succ_apply, relD_succ]
  change solFormsIntegral hX hbump hf hs o (m + 1 + 1)
      ((BundledMPolyfold.of PX).formsInftyD (m + 1) η.1) -
    solBFormsIntegral hX hbump hf hs o (m + 1)
      (jStar hX (m + 1) η.1 - bFormsInftyD hX m η.2) = 0
  rw [map_sub]
  by_cases h : IsCompact (B.solPart f s (m + 1 + 1))
  · let := solPartChartedSpace hX hf hs (m + 1 + 1)
    have := isManifold_solPart hX hf hs (m + 1 + 1)
    have := isCompact_iff_compactSpace.1 h
    have ho := isContinuous_solPartOr hX hbump hf hs o (m + 1 + 1)
    rw [solFormsIntegral_apply hX hbump hf hs o h, solBFormsIntegral_apply hX hbump hf hs o h,
      solBFormsIntegral_apply hX hbump hf hs o h, stokes_formsInftyRestrict rfl ho,
      solFaceForm_jStar_integral _ hX _ rfl ho, solFaceForm_d _ hX _ rfl,
      ChartFaceForm.integral_d_eq_zero_of_compactSpace ho, sub_zero, sub_self]
  · rw [solFormsIntegral_of_not_isCompact hX hbump hf hs o h,
      solBFormsIntegral_of_not_isCompact hX hbump hf hs o h, LinearMap.zero_apply,
      LinearMap.zero_apply, LinearMap.zero_apply, sub_zero, sub_self]

/-- **`Ψ` vanishes on `d`-exact relative forms** (2021, proof of Theorem 6.7.1, p. 277: the
definition (6.35) depends only on the class `[ω, τ]`): `Ψ(d(ω, τ)) = 0` in every degree. -/
theorem psiForms_relD : ∀ (k : ℕ) (η : RelForms hX k),
    psiForms hX hbump hf hs o (k + 1) (relD hX k η) = 0
  | 0, η => psiForms_relD_zero hX hbump hf hs o η
  | m + 1, η => psiForms_relD_succ hX hbump hf hs o m η

theorem relDRange_le_ker_psiForms (k : ℕ) :
    relDRange hX k ≤ LinearMap.ker (psiForms hX hbump hf hs o k) := by
  cases k with
  | zero =>
    intro η hη
    rw [show η = 0 from (Submodule.mem_bot ℝ).1 hη]
    exact Submodule.zero_mem _
  | succ m =>
    rintro _ ⟨θ, rfl⟩
    exact psiForms_relD hX hbump hf hs o m θ

/-- **2021 Theorem 6.7.1 (1), the map `Ψ_{(f,o)}` for one admissible section**: the linear map
`Hᵏ_dR(X, ∂X) → ℝ`, `[ω, τ] ↦ ∫_{S_k} ω − ∫_{∂S_k} τ` (formula (6.35), p. 277), well defined by
`psiForms_relD` (`Submodule.liftQ`).  It is defined for one admissible `s`; the independence of
`s` (and of `N`, `U`) is the rest of the proof of the theorem. -/
def psiAt (k : ℕ) : relDeRham hX k →ₗ[ℝ] ℝ :=
  Submodule.liftQ _ ((psiForms hX hbump hf hs o k).comp (LinearMap.ker (relD hX k)).subtype)
    fun η hη => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply]
      exact relDRange_le_ker_psiForms hX hbump hf hs o k hη

/-- **The value of `Ψ` on a class** (formula (6.35)): `Ψ([ω, τ]) = ∫_{S_k} ω|_S − ∫_{∂S_k} τ|_{∂S}`
for every closed relative form `(ω, τ)` of degree `k`. -/
theorem psiAt_mk (k : ℕ) (c : LinearMap.ker (relD hX k)) :
    psiAt hX hbump hf hs o k (relDeRhamMk hX k c) =
      solIntegral hX hbump hf hs o k c - solBoundaryIntegral hX hbump hf hs o k c :=
  Submodule.liftQ_apply _ _ c

/-- `Ψ ∘ [·] = ψ` on the closed forms. -/
theorem psiAt_comp_mk (k : ℕ) :
    (psiAt hX hbump hf hs o k).comp (relDeRhamMk hX k) =
      (psiForms hX hbump hf hs o k).comp (LinearMap.ker (relD hX k)).subtype :=
  LinearMap.ext fun c => psiAt_mk hX hbump hf hs o k c

/-- **`Ψ_s` depends on `s`, not on the pair `(N, U)`** for which `s` is admissible: the pair
enters only through proofs. With it, comparing two norms `N₀, N₁` (implicit in the proof of
2021 Theorem 6.7.1 (1), p. 277, where `Ψ` is defined from one `N`) reduces to comparing two
sections. -/
theorem psiAt_congr_admissible {N' : B.One → ℝ} {U' : Set X} (hs' : B.IsAdmissible f N' U' s) :
    psiAt hX hbump hf hs o = psiAt hX hbump hf hs' o :=
  rfl

/-- **`Ψ = 0` in a degree `k` with `S_k = ∅`** (in particular for `k ≠ n` when the index is
constantly `n`, `solPart_eq_empty_of_ne`; the case of 2021 p. 279). -/
theorem psiAt_of_eq_empty {k : ℕ} (h : B.solPart f s k = ∅) : psiAt hX hbump hf hs o k = 0 := by
  refine Submodule.linearMap_qext _ ?_
  rw [psiAt_comp_mk, psiForms_of_eq_empty hX hbump hf hs o h, LinearMap.zero_comp,
    LinearMap.zero_comp]

/-- **`Ψ` for `∂X = ∅`** (2021 p. 279): `Ψ([ω, τ]) = ∫_{S_k} ω|_S`. -/
theorem psiAt_mk_of_isWithoutBoundary (h : PX.IsWithoutBoundary) (k : ℕ)
    (c : LinearMap.ker (relD hX k)) :
    psiAt hX hbump hf hs o k (relDeRhamMk hX k c) = solIntegral hX hbump hf hs o k c := by
  rw [psiAt_mk, solBoundaryIntegral_of_isWithoutBoundary hX hbump hf hs o h, LinearMap.zero_apply,
    sub_zero]

/-- **`Ψ` on a class, for compact `S_{f+s}`, in degree `0`**: `Ψ([ω]) = ∫_{S_0} ω|_S`. -/
theorem psiAt_mk_zero (hS : IsCompact (solutionSet P (sectionAdd P f s)))
    (c : LinearMap.ker (relD hX 0)) :
    letI := solPartChartedSpace hX hf hs 0
    haveI := isManifold_solPart hX hf hs 0
    psiAt hX hbump hf hs o 0 (relDeRhamMk hX 0 c) = ManifoldForm.integral (solPartOr hX hf hs o 0)
      (formsInftyRestrict 0 (hasCornerStructureOfDim_solPart hX hf hs 0) (c : RelForms hX 0)) := by
  rw [psiAt_mk, solBoundaryIntegral_zero, LinearMap.zero_apply, sub_zero, solIntegral_zero_apply]
  exact solFormsIntegral_apply hX hbump hf hs o
    (isCompact_solPart hf hs.isScPlusSection hs.gp hS 0) _

/-- **`Ψ` on a class, for compact `S_{f+s}`, in degree `m + 1`** (formula (6.35)):
`Ψ([ω, τ]) = ∫_{S_{m+1}} ω|_S − ∫_{∂S_{m+1}} τ|_{∂S}`, as integrals over the Mathlib manifold
`S_{m+1}` and its faces. -/
theorem psiAt_mk_succ (hS : IsCompact (solutionSet P (sectionAdd P f s))) (m : ℕ)
    (c : LinearMap.ker (relD hX (m + 1))) :
    letI := solPartChartedSpace hX hf hs (m + 1)
    haveI := isManifold_solPart hX hf hs (m + 1)
    psiAt hX hbump hf hs o (m + 1) (relDeRhamMk hX (m + 1) c) =
      ManifoldForm.integral (solPartOr hX hf hs o (m + 1))
          (formsInftyRestrict (m + 1) (hasCornerStructureOfDim_solPart hX hf hs (m + 1))
            (c : RelForms hX (m + 1)).1) -
        (solFaceForm (hasCornerStructureOfDim_solPart hX hf hs (m + 1)) hX
          (degIndex_solPart hX hf hs (m + 1)) rfl (c : RelForms hX (m + 1)).2).integral
          (solPartOr hX hf hs o (m + 1)) := by
  have h := isCompact_solPart hf hs.isScPlusSection hs.gp hS (m + 1)
  rw [psiAt_mk, solIntegral_succ_apply, solBoundaryIntegral_succ_apply,
    solFormsIntegral_apply hX hbump hf hs o h, solBFormsIntegral_apply hX hbump hf hs o h]

include hX hf hs in
/-- **`S_0` is finite** when `S_{f+s}` is compact (a compact `0`-dimensional manifold). -/
theorem finite_solPart_zero (hS : IsCompact (solutionSet P (sectionAdd P f s))) :
    Finite ↥(B.solPart f s 0) :=
  letI := solPartChartedSpace hX hf hs 0
  haveI := isCompact_iff_compactSpace.1 (isCompact_solPart hf hs.isScPlusSection hs.gp hS 0)
  ManifoldForm.finite_of_dim_zero

open Classical in
/-- **Degree `0`: `∫_{S_0} ω` is a signed sum over the finitely many points of `S_0`**
(`integral_eq_sum_of_dim_zero`): `Ψ([ω]) = ∑_{x ∈ S_0} ε(x) ω(x)`, `ε(x) = +1` if the
orientation of `T_xS_0 = ℝ⁰` induced by `o_x` is the standard one and `−1` otherwise. -/
theorem solIntegral_zero_eq_sum [Fintype ↥(B.solPart f s 0)] (ω : RelForms hX 0) :
    letI := solPartChartedSpace hX hf hs 0
    solIntegral hX hbump hf hs o 0 ω =
      ∑ x, orSign (decide (tangentOrToModel (solPartOr hX hf hs o 0 x) = stdOrientation 0)) *
        formsInftyRestrict 0 (hasCornerStructureOfDim_solPart hX hf hs 0) ω x 0 := by
  let := solPartChartedSpace hX hf hs 0
  have := isManifold_solPart hX hf hs 0
  rw [solIntegral_zero_apply]
  exact (solFormsIntegral_apply hX hbump hf hs o (Set.toFinite _).isCompact ω).trans
    (ManifoldForm.integral_eq_sum_of_dim_zero (isContinuous_solPartOr hX hbump hf hs o 0) _)

open Classical in
/-- **`Ψ` in degree `0` as a signed count** (2021 Theorem 6.7.1 (1) for `k = 0`):
`Ψ([ω]) = ∑_{x ∈ S_0} ε(x) ω(x)`. -/
theorem psiAt_mk_zero_eq_sum [Fintype ↥(B.solPart f s 0)] (c : LinearMap.ker (relD hX 0)) :
    letI := solPartChartedSpace hX hf hs 0
    psiAt hX hbump hf hs o 0 (relDeRhamMk hX 0 c) =
      ∑ x, orSign (decide (tangentOrToModel (solPartOr hX hf hs o 0 x) = stdOrientation 0)) *
        formsInftyRestrict 0 (hasCornerStructureOfDim_solPart hX hf hs 0)
          (c : RelForms hX 0) x 0 := by
  rw [psiAt_mk, solBoundaryIntegral_zero, LinearMap.zero_apply, sub_zero]
  exact solIntegral_zero_eq_sum hX hbump hf hs o _

end Integrals

end Polyfold
