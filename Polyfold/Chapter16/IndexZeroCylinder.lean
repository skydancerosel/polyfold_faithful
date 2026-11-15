import Polyfold.Chapter15.CylinderPointEnds
import Polyfold.Chapter15.CylinderOrientationInvariance
import Polyfold.Chapter15.CylinderCobordismReduced
import Polyfold.Chapter16.IndexZeroPolyfoldTheorem

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, p. 703:
**Corollary 15.4.4** (2017: Corollary 15.2), and §16.6, p. 739: **Theorem 16.6.6** (2017:
Theorem 16.8), **for Fredholm index `0`**; with Theorem 15.4.1, Definition 15.4.2 (pp. 701–702)
and Corollary 15.3.10 (3) (p. 699).

# The oriented cobordism between two regular perturbations of dimension `0`

## The text, paraphrased

(p. 703) For an oriented sc-Fredholm section functor `(f, o)` and regular perturbations `Λ₀`,
`Λ₁`, the perturbation `Λ̃` of `f̃` on `[0, 1] × X` restricting to `Λᵢ` on the ends gives
`Θ̃ = Λ̃ ∘ f̃`, canonically oriented by `(f̃, õ)`, with `∂Θ̃ = Θ₁ ⊔ −Θ₀`; Stokes on `Θ̃` gives the
invariance of the integrals.  For Fredholm index `0` the `Θᵢ` are finite sets of weighted signed
points, `Θ̃` has dimension `1`, and the invariant is the weighted signed count (Theorem 16.6.6
for `k = 0`).

## What is formalized

Namespace `Polyfold.SBLocalization`:
* `PointPerturbation.IsCanonical`: the orientation of a regular perturbation of dimension `0`
  is the canonical one for `(f, o)` (Definition 15.4.2 with `n = 0`).
* **`theorem_15_4_1_cylinder_index_zero`**: Theorem 15.4.1 for `(f̃, õ)`, `õ = e ∧ o`, when `f`
  has index `0`: the canonical orientation of `Θ̃`, of dimension `1`.
* **`hasOrientedCobordism_of_isCanonical`**: two canonically oriented regular perturbations of
  dimension `0` are joined by an oriented compact cobordism of dimension `1`, and by an
  effective one (`PointPerturbation.HasOrientedCobordism`, `HasOrientedCobordismEff`).
* **`corollary_15_4_4_index_zero_oriented`**: Corollary 15.4.4 for index `0`: the weighted
  signed counts `∫`, `∮` of a closed `0`-form over two canonically oriented regular
  perturbations agree.
* `PointPerturbation.canonical`, `PointPerturbation.isCanonical_canonical`: every regular
  perturbation of an oriented `(f, o)` of index `0` carries the canonical orientation, so the
  perturbations of the corollary exist whenever regular perturbations do.

Namespace `Polyfold.StrongPolyfoldBundle`:
* `IndexZeroInput`: the standing hypotheses in the model of an orientation.
* **`theorem_16_6_6_index_zero_canonical`**, **`theorem_16_6_6_index_zero_polyfold_canonical`**:
  Theorem 16.6.6 for index `0`, in the model of the orientation and on the polyfold, for the
  canonical orientations, without a cobordism hypothesis.

## Reading

The hypotheses beyond the text's are the standing ones of Corollary 15.4.4 in positive
dimension: sc-smooth partitions of unity on `X` and on `[0, 1] × X` (Stokes, Theorem 9.5.17),
tame germ data of `f`, and "`(f, o)` is oriented" read as Definition 6.6.16 together with the
invariance under morphisms of Definition 12.5.4.  The index of `f` is `0` at every smooth point.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP UnitCube

variable {A : SEP.{u}} {f : A.Obj → A.W}

/-- **The predicate `Can` of Corollary 15.4.4 for index `0`**: the orientation of the regular
perturbation `P` of dimension `0` is the canonical one for `(f, o)` (Definition 15.4.2): near
every point of `supp(Λ ∘ f)` it is `∑ σᵢ · ({y}, o_{i,y})` in a local structure described by
kernels, the sign of the point `y` of `Mᵢ = {f = sᵢ}` being that of `o_y` on
`ker (f − sᵢ)'(y) = 0`. -/
def PointPerturbation.IsCanonical (hf : A.B.IsScFredholmSection f)
    (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf y hy) (P : PointPerturbation A f) : Prop :=
  IsCanonicalFor P.Λ hf hsec o 0 P.T

section Cylinder

variable (hd : ∀ x, A.X.PObj.degIndex x = 0)
  (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
  (hsec : A.B.HasScPlusSectionsThrough)
  (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy)
  (ho : haveI := paracompactSpace_rn_prod A.X.PObj
    haveI := paracompactSpace_rn_pullback A.B
    IsSectionOrientation f hf.2 o)
  (hidx : ∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x 0)

include hd ho hidx in
/-- **Theorem 15.4.1 (2021 p. 702; 2017: Theorem 15.6) for the cobordism, Fredholm index `0`**
(2021 p. 703): let `d_X ≡ 0`, `X` with sc-smooth bump functions, `(f, o)` an oriented
sc-Fredholm section functor with tame germ data of index `0`, and `õ = e ∧ o` invariant under
the morphisms of the cylinder.  For a transversal sc⁺-multisection `Λ̃` on `[0, 1] × X` with
`Λ̃ = Λᵢ` over `t = i` and the face condition of Theorem 15.3.9 for the glued data, the formula
of Theorem 15.4.1 for `(f̃, õ)` defines the canonical orientation of `Θ̃ = Λ̃ ∘ f̃`, of dimension
`1`. -/
theorem theorem_15_4_1_cylinder_index_zero (hbump : A.X.PObj.AdmitsBumpFunctions)
    (hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough)
    (hinvC : (A.cubeSEP 1).E.IsOrInvariant (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft)
      hsec' (cubeOrientation hf hft hsec o))
    {Λ' : (A.cubeSEP 1).W → ℚ≥0} {Λ₀ Λ₁ : A.W → ℚ≥0}
    (hΛ' : IsScPlusMultisection (A.cubeSEP 1) Λ')
    (htr : IsTransversal (cubeLiftEp (n := 1) f hf.1.1.1) Λ')
    (h0 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (cubeVal w).2)
    (h1 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (cubeVal w).2)
    (honto : IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue Λ₀ Λ₁)) :
    IsCanonicalFor Λ' (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 hsec'
      (cubeOrientation hf hft hsec o) (0 + 1)
      (canonicalOrientation Λ' (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 hsec'
        (cubeOrientation hf hft hsec o)) := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PMor
  have hX : A.X.IsTame := A.X.isTame_of_degIndex_eq_zero hd
  have hXC : (A.cubeSEP 1).X.IsTame := A.X.isTame_cubeProd 1 hX
  have hbumpC : (A.cubeSEP 1).X.PObj.AdmitsBumpFunctions := admitsBumpFunctions_prod_cube hbump
  have hfC := isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft
  have hftC := isScFredholmSectionTame_cubeLiftEp (n := 1) hft
  have hbd : ∀ w : (A.cubeSEP 1).W, (A.cubeSEP 1).P w ∈ (A.cubeSEP 1).X.PObj.boundary →
      Λ' w = cubeGlue Λ₀ Λ₁ w := fun w hw => by
    rcases (mem_boundary_cubeSEP_iff hX hd _).1 hw with h | h
    · exact (h0 w h).trans (cubeGlue_of_zero h).symm
    · exact (h1 w h).trans (cubeGlue_of_one h).symm
  have hgood : ∀ z ∈ (A.cubeSEP 1).X.PObj.boundary,
      0 < Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) →
        IsGoodPositionAt (cubeLiftEp (n := 1) f hf.1.1.1) Λ' z := fun z hz hpos =>
    isGoodPositionAt_of_isInGeneralPositionAt hfC hftC hΛ' hpos
      (isInGeneralPositionAt_of_isBoundaryFaceOnto hfC hftC hΛ' hbd honto hz hpos)
  have hidxC : ∀ z ∈ EpGroupoid.supp
      (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)),
      (A.cubeSEP 1).B.IsIndexAt (cubeLiftEp (n := 1) f hf.1.1.1) z ((0 + 1 : ℕ) : ℤ) :=
    fun z hz => by
    have hpos : 0 < Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) := by exact_mod_cast hz
    have hzs : z ∈ (A.cubeSEP 1).X.PObj.smoothSet := mem_smoothSet_of_pos hftC hΛ' hpos
    have hxs : z.2 ∈ A.X.PObj.smoothSet := prod_cube_mem_smoothSet_iff.1 hzs
    have hi0 : A.B.IsIndexAt f z.2 ((0 : ℕ) : ℤ) := by exact_mod_cast hidx z.2 hxs
    exact isIndexAt_cubeLiftEp hf hft hsec hxs hi0 z.1
  exact theorem_15_4_1 hXC hbumpC hfC hftC hΛ' hsec' (cubeOrientation hf hft hsec o) hinvC
    (isSectionOrientation_cubeOrientation hX hbump hf hft ho)
    (isGoodPositionAt_of_transversal hfC hftC hΛ' htr hgood) hidxC

include hd hft ho hidx in
/-- **The oriented cobordism between two regular perturbations of dimension `0`** (Corollary
15.4.4 for Fredholm index `0`, 2021 p. 703, with Corollary 15.3.10 (3) and Theorem 15.4.1).  Let
`d_X ≡ 0`, `|X|` paracompact, `X` with sc-smooth partitions of unity (also on `[0, 1] × X`), and
let `(f, o)` be an oriented sc-Fredholm section functor with compact solution set, tame germ
data and index `0`.  Any two regular perturbations of dimension `0` with the canonical
orientation of `(f, o)` are joined by an oriented compact cobordism of dimension `1`:
`Θ̃ = Λ̃ ∘ f̃` on `[0, 1] × X` (Corollary 15.3.10 (3)) with the canonical orientation of
`(f̃, e ∧ o)` (`theorem_15_4_1_cylinder_index_zero`), whose boundary measure of `pr^*ω` is
`∫_{P₁} ω − ∫_{P₀} ω` (`boundaryBranchedMeasureDim1_cylEnd_of_pointMatched`).  With the local
unique continuation property the same holds for the effective counts. -/
theorem hasOrientedCobordism_of_isCanonical (hinv : A.E.IsOrInvariant hf hsec o)
    (hpara : A.X.HasParacompactOrbitSpace) (hPU : A.X.HasScPartitionsOfUnity)
    (hPUC : (A.cubeSEP 1).X.PObj.AdmitsScPartitionsOfUnity)
    (hS : A.E.HasCompactSolutionSetEp f) (P₀ P₁ : PointPerturbation A f)
    (h₀ : P₀.IsCanonical hf.2 hsec o) (h₁ : P₁.IsCanonical hf.2 hsec o) :
    P₀.HasOrientedCobordism P₁ ∧ ∀ hLUC : A.X.IsLUC, P₀.HasOrientedCobordismEff hLUC P₁ := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PMor
  have hX : A.X.IsTame := A.X.isTame_of_degIndex_eq_zero hd
  have hXC : (A.cubeSEP 1).X.IsTame := A.X.isTame_cubeProd 1 hX
  have hbump : A.X.PObj.AdmitsBumpFunctions :=
    A.X.theorem_12_3_2_1.1 (EpGroupoid.admitsBumpFunctionsPointwise_of_hasScPartitionsOfUnity hPU)
  have hbumpC : (A.cubeSEP 1).X.PObj.AdmitsBumpFunctions := admitsBumpFunctions_prod_cube hbump
  have hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough :=
    MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough hbumpC
  have hftC := isScFredholmSectionTame_cubeLiftEp (n := 1) hft
  have hbs := isBoundaryStructurable_cubeGlue hd hpara P₀.isRegular.2.1 P₁.isRegular.2.1
  have honto := isBoundaryFaceOnto_cubeGlue hd hf hft P₀.isRegular.2.2.2.2 P₁.isRegular.2.2.2.2
  obtain ⟨Λ', hreg, e0, e1, hΘ', hcpt'⟩ := corollary_15_3_10_3_charged
    (theorem_15_3_9_charged_hyp theorem_15_3_7_relative) ((A.cubeSEP 1).exists_isTameChart hXC)
    hd hpara hPUC hf hft hS P₀.isRegular P₁.isRegular hbs honto
  have hΛ' : IsScPlusMultisection (A.cubeSEP 1) Λ' := hreg.2.1.1
  have hcan' := theorem_15_4_1_cylinder_index_zero hd hf hft hsec o ho hidx hbump hsec'
    (isOrInvariant_cubeOrientation hf hft hsec hsec' o hinv) hΛ' hreg.2.2.2.2 e0 e1 honto
  have hT' := hcan'.1
  have hloc' := hcan'.loc
  have hK' := hcan'.isKernelCanonical (canonContinuous Λ' hXC hbumpC hftC hsec'
    (cubeOrientation hf hft hsec o) (isSectionOrientation_cubeOrientation hX hbump hf hft ho))
  have hK₀ : IsKernelCanonical P₀.Λ hf.2 hsec o P₀.T :=
    IsCanonicalFor.isKernelCanonical h₀ (canonContinuous P₀.Λ hX hbump hft hsec o ho)
  have hK₁ : IsKernelCanonical P₁.Λ hf.2 hsec o P₁.T :=
    IsCanonicalFor.isKernelCanonical h₁ (canonContinuous P₁.Λ hX hbump hft hsec o ho)
  have z0 : ((0 : unitInterval) : ℝ) = 0 := rfl
  have z1 : ((1 : unitInterval) : ℝ) = 1 := rfl
  have m0 := exists_arePointMatchedAt_of_kernelCanonical hd hbump hf hft
    (fun x hx => (P₀.loc x hx).imp fun _ h => h.2) hΛ' e0 e1 honto (i := 0) (ε := -1)
    (Or.inl ⟨z0, rfl⟩) e0 hΘ' hK₀ hK'
  have m1 := exists_arePointMatchedAt_of_kernelCanonical hd hbump hf hft
    (fun x hx => (P₁.loc x hx).imp fun _ h => h.2) hΛ' e0 e1 honto (i := 1) (ε := 1)
    (Or.inr ⟨z1, rfl⟩) e1 hΘ' hK₁ hK'
  have hov0 := fun p => cylEndMap_mem_orbitSupp_zero hd hf.1.1.1 e0 e1 p
  have hov1 := fun p => cylEndMap_mem_orbitSupp_one hd hf.1.1.1 e0 e1 p
  refine ⟨⟨(A.cubeSEP 1).baseEP, A.X.cubeProj 1, hasScPartitionsOfUnity_cyl hpara hPUC, _, _,
    hΘ', hcpt', hT', hloc', fun ω => ?_⟩, fun hLUC => ⟨(A.cubeSEP 1).baseEP, A.X.cubeProj 1,
    hasScPartitionsOfUnity_cyl hpara hPUC, isLUC_cubeSEP hLUC, _, _, hΘ', hcpt', hT', hloc',
    fun ω => ?_⟩⟩
  · have E0 := boundaryBranchedMeasureDim1_cylEnd_of_pointMatched P₀.isBranched P₀.isCompact
      P₀.isOrientation P₀.loc hΘ' hcpt' hT' hloc' (i := 0) (q := fun _ => 0) z0 hov0 m0 ω
    have E1 := boundaryBranchedMeasureDim1_cylEnd_of_pointMatched P₁.isBranched P₁.isCompact
      P₁.isOrientation P₁.loc hΘ' hcpt' hT' hloc' (i := 1) (q := fun _ => 1) z1 hov1 m1 ω
    refine (A.X.signedMeasure_univ_eq_cylEnds (boundary_cyl_time hd)
      ((A.X.cubeProd 1).borel_le_lebesgueSigmaBoundaryH (0 + 1) _)
      ((A.cubeSEP 1).baseEP.boundaryBranchedMeasureDim1 hΘ' hcpt' hT' hloc'
        (EP.epFormsInftyPullback (A := (A.cubeSEP 1).baseEP) (B := A.baseEP) (A.X.cubeProj 1)
          0 ω))).trans ((congrArg₂ (· + ·) E0 E1).trans ?_)
    change -1 * P₀.count ω + 1 * P₁.count ω = _
    ring
  · have E0 := boundaryBranchedMeasureEffDim1_cylEnd_of_pointMatched hLUC (isLUC_cubeSEP hLUC)
      P₀.isBranched P₀.isCompact P₀.isOrientation (P₀.loc.hasLUC hLUC) hΘ' hcpt' hT'
      ((A.cubeSEP 1).baseEP.hloc_hasLUC_dim1 (isLUC_cubeSEP hLUC) hloc') (i := 0)
      (q := fun _ => 0) z0 hov0 m0 ω
    have E1 := boundaryBranchedMeasureEffDim1_cylEnd_of_pointMatched hLUC (isLUC_cubeSEP hLUC)
      P₁.isBranched P₁.isCompact P₁.isOrientation (P₁.loc.hasLUC hLUC) hΘ' hcpt' hT'
      ((A.cubeSEP 1).baseEP.hloc_hasLUC_dim1 (isLUC_cubeSEP hLUC) hloc') (i := 1)
      (q := fun _ => 1) z1 hov1 m1 ω
    refine (A.X.signedMeasure_univ_eq_cylEnds (boundary_cyl_time hd)
      ((A.X.cubeProd 1).borel_le_lebesgueSigmaBoundaryH (0 + 1) _)
      ((A.cubeSEP 1).baseEP.boundaryBranchedMeasureEffDim1 hΘ' hcpt' hT'
        ((A.cubeSEP 1).baseEP.hloc_hasLUC_dim1 (isLUC_cubeSEP hLUC) hloc')
        (EP.epFormsInftyPullback (A := (A.cubeSEP 1).baseEP) (B := A.baseEP) (A.X.cubeProj 1)
          0 ω))).trans ((congrArg₂ (· + ·) E0 E1).trans ?_)
    change -1 * P₀.countEff hLUC ω + 1 * P₁.countEff hLUC ω = _
    ring

include hd hft ho hidx in
/-- **Corollary 15.4.4 (2021 p. 703; 2017: Corollary 15.2) for Fredholm index `0`.**  Let
`d_X ≡ 0`, `|X|` paracompact, `X` with sc-smooth partitions of unity (also on `[0, 1] × X`; they
are used for Stokes), and let `(f, o)` be an oriented sc-Fredholm section functor with compact
solution set, tame germ data and index `0`.  Then a closed `0`-form has the same weighted signed
count `∫_{(Λ ∘ f, o)} ω` over any two regular perturbations with the canonical orientation of
`(f, o)` (Definition 15.4.2), and the same effective count `∮` when `X` has the local unique
continuation property.  No hypothesis on the cobordism. -/
theorem corollary_15_4_4_index_zero_oriented (hinv : A.E.IsOrInvariant hf hsec o)
    (hpara : A.X.HasParacompactOrbitSpace) (hPU : A.X.HasScPartitionsOfUnity)
    (hPUC : (A.cubeSEP 1).X.PObj.AdmitsScPartitionsOfUnity)
    (hS : A.E.HasCompactSolutionSetEp f) (P₀ P₁ : PointPerturbation A f)
    (h₀ : P₀.IsCanonical hf.2 hsec o) (h₁ : P₁.IsCanonical hf.2 hsec o)
    (ω : A.baseEP.epFormsInfty 0) (hω : A.baseEP.epFormsInftyD 0 ω = 0) :
    P₀.count ω = P₁.count ω ∧ ∀ hLUC : A.X.IsLUC, P₀.countEff hLUC ω = P₁.countEff hLUC ω := by
  obtain ⟨h, he⟩ := hasOrientedCobordism_of_isCanonical hd hf hft hsec o ho hidx hinv hpara hPU
    hPUC hS P₀ P₁ h₀ h₁
  have key := corollary_15_4_4_index_zero P₀ P₁ ω hω
  exact ⟨key.1 h, fun hLUC => key.2 hLUC (he hLUC)⟩

end Cylinder

/-! ### The canonically oriented perturbation -/

section Canonical

variable {Λ : A.W → ℚ≥0} (hX : A.X.PObj.IsTame) (hbump : A.X.PObj.AdmitsBumpFunctions)
  (hF : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
  (hsec : A.B.HasScPlusSectionsThrough)
  (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hF.2 y hy) (hinv : A.E.IsOrInvariant hF hsec o)
  (ho : haveI := paracompactSpace_rn_prod A.X.PObj
    haveI := paracompactSpace_rn_pullback A.B
    IsSectionOrientation f hF.2 o)

/-- **A regular perturbation of dimension `0` with its canonical orientation** (Definition
15.4.2 for Fredholm index `0`): for a structurable regular perturbation `(N, U, Λ)` of an
oriented sc-Fredholm section functor `(f, o)` of index `0` on `supp(Λ ∘ f)`, in good position at
the boundary points of the support, the regular perturbation `(Λ ∘ f, T̂_((f, o), Λ))` of
dimension `0`: the points of `supp(Λ ∘ f)` with the signs given by `o` (Theorem 15.4.1). -/
def PointPerturbation.canonical {N : A.B.One → ℝ} {U : Set A.Obj}
    (hreg : IsRegularPerturbation A f N U Λ)
    (hgood : ∀ x ∈ A.X.PObj.boundary, 0 < Λ (f x) → IsGoodPositionAt f Λ x)
    (hidx : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)), A.B.IsIndexAt f x (0 : ℕ)) :
    PointPerturbation A f :=
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
    loc := EpGroupoid.isPointTame_iff.2 hcan.loc }

/-- **The canonically oriented perturbation of dimension `0` satisfies the predicate `Can`.** -/
theorem PointPerturbation.isCanonical_canonical {N : A.B.One → ℝ} {U : Set A.Obj}
    (hreg : IsRegularPerturbation A f N U Λ)
    (hgood : ∀ x ∈ A.X.PObj.boundary, 0 < Λ (f x) → IsGoodPositionAt f Λ x)
    (hidx : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)), A.B.IsIndexAt f x (0 : ℕ)) :
    (PointPerturbation.canonical hX hbump hF hft hsec o hinv ho hreg hgood hidx).IsCanonical
      hF.2 hsec o :=
  theorem_15_4_1 hX hbump hF hft hreg.2.1.1 hsec o hinv ho
    (isGoodPositionAt_of_transversal hF hft hreg.2.1.1 hreg.2.2.2.2 hgood) hidx

end Canonical

end SBLocalization

namespace StrongPolyfoldBundle

open StrongPolyfoldBundleStructure PolyfoldClass SBLocalization

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p}

/-- **The standing hypotheses of Theorem 16.6.6 for index `0` in the model of an orientation
`o`**: sc-smooth partitions of unity on the object M-polyfold of `[0, 1] × X` (Stokes on the
cobordism), tame germ data of the representative `F`, `o` is an orientation of `F` in the sense
of Definition 6.6.16, and `F` has Fredholm index `0` at every smooth point. -/
structure IndexZeroInput {s : FredholmSection c} (o : OrientationRep s) : Prop where
  pu : (o.a.S.A.cubeSEP 1).X.PObj.AdmitsScPartitionsOfUnity
  tame : o.a.S.A.B.IsScFredholmSectionTame o.a.F
  orient : haveI := paracompactSpace_rn_prod o.a.S.A.X.PObj
    haveI := paracompactSpace_rn_pullback o.a.S.A.B
    IsSectionOrientation o.a.F o.hF.2 o.o
  index : ∀ x ∈ o.a.S.A.X.PObj.smoothSet, o.a.S.A.B.IsIndexAt o.a.F x 0

/-- **The cobordisms of Theorem 16.6.6 for index `0` in the model of `o`**: for `∂Z = ∅`, `Z`
with sc-smooth partitions of unity and `f` with compact solution set, any two regular
perturbations of dimension `0` with the canonical orientation of `(F, o)` are joined by an
oriented compact cobordism of dimension `1` and by an effective one. -/
theorem hasOrientedCobordism_of_indexZeroInput (hPU : c.polyfold.AdmitsScPartitionsOfUnity)
    (hbd : c.polyfold.boundary = ∅) {s : FredholmSection c} (hcs : s.1.HasCompactSolutionSet)
    {o : OrientationRep s} (H : IndexZeroInput o) (P₀ P₁ : PointPerturbation o.a.S.A o.a.F)
    (h₀ : P₀.IsCanonical o.hF.2 o.hsec o.o) (h₁ : P₁.IsCanonical o.hF.2 o.hsec o.o) :
    P₀.HasOrientedCobordism P₁ ∧
      P₀.HasOrientedCobordismEff (o.a.S.A.X.proposition_7_4_10_of_isZhou o.a.S.isZhou) P₁ := by
  have hd : ∀ x, o.a.S.A.X.PObj.degIndex x = 0 :=
    degIndex_eq_zero_of_boundary_eq_empty hbd o.a.hS
  have hS : o.a.S.A.E.HasCompactSolutionSetEp o.a.F := by
    rw [← o.a.hasCompactSolutionSet_iff, o.ha]; exact hcs
  have hPUq := (c.polyfold.definition_16_1_5_two).1 hPU o.a.S.toPolyfoldStructure
    (toPolyfoldStructure_mem o.a.hS)
  obtain ⟨h, he⟩ := hasOrientedCobordism_of_isCanonical hd o.hF H.tame o.hsec o.o H.orient
    H.index o.isOrientation.2 o.a.S.paracompact hPUq H.pu hS P₀ P₁ h₀ h₁
  exact ⟨h, he _⟩

/-- **2021 Theorem 16.6.6 for Fredholm index `0`, in the model of the orientation** (p. 739;
2017: Theorem 16.8): if `Z` admits sc-smooth partitions of unity and the standing hypotheses
hold in the model of every orientation, then for `∂Z = ∅` and `f` oriented with compact solution
set the counts `∫`, `∮` of a closed sc-differential `0`-form over two regular perturbations of
dimension `0` with the canonical orientation (Definition 15.4.2) agree.  The cobordisms are
those of `hasOrientedCobordism_of_indexZeroInput`. -/
theorem theorem_16_6_6_index_zero_canonical (hPU : c.polyfold.AdmitsScPartitionsOfUnity)
    (s : FredholmSection c) (n : Y → ℝ) (U : Set Z)
    (H : ∀ o : OrientationRep s, IndexZeroInput o) :
    theorem_16_6_6_index_zero_statement s n U
      (fun o P => P.IsCanonical o.hF.2 o.hsec o.o) :=
  theorem_16_6_6_index_zero_of_model s n U _ fun hbd hcs o P₀ P₁ h₀ h₁ =>
    hasOrientedCobordism_of_indexZeroInput hPU hbd hcs (H o) P₀ P₁ h₀ h₁

/-- **2021 Theorem 16.6.6 for Fredholm index `0`, on the polyfold** (p. 739; 2017: Theorem
16.8): under the hypotheses of `theorem_16_6_6_index_zero_canonical`, a closed `0`-form `τ` on
`Z` has the same count `∫_θ̂ τ` and the same effective count `∮_θ̂ τ` over any two admissible
perturbed solution sets of dimension `0` with the orientation inherited from `(f, o)` (the
canonical orientation of Definition 15.4.2, read in the model of `o`). -/
theorem theorem_16_6_6_index_zero_polyfold_canonical
    (hPU : c.polyfold.AdmitsScPartitionsOfUnity) (s : FredholmSection c) (n : Y → ℝ)
    (U : Set Z) (H : ∀ o : OrientationRep s, IndexZeroInput o) :
    theorem_16_6_6_index_zero_polyfold_statement s n U
      (IsInheritedFromPoint fun o P => P.IsCanonical o.hF.2 o.hsec o.o) :=
  theorem_16_6_6_index_zero_polyfold_of_model s n U _ fun hbd hcs o P₀ P₁ h₀ h₁ =>
    hasOrientedCobordism_of_indexZeroInput hPU hbd hcs (H o) P₀ P₁ h₀ h₁

end StrongPolyfoldBundle

end Polyfold
