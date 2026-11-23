import Polyfold.Chapter16.IndexZeroAllAdmissible
import Polyfold.Chapter15.AdmissibleCobordismLocal
import Polyfold.Chapter15.IndexZeroNoBumpsEnds

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, pp. 702–703:
**Theorem 15.4.1** on the cylinder and **Corollary 15.4.4** for Fredholm index `0`, with the
orientation of `f` read in the local orientation sets and no sc-smooth bump functions.

# Corollary 15.4.4 for index `0` from local families on the cylinder, without bump functions

## The text, paraphrased

(Corollary 15.4.4) The weighted signed count of a closed `0`-form over `Λ ∘ f` does not depend on
the perturbation; the proof joins two perturbations by the cobordism of Corollary 15.3.10 (3),
of dimension `1`, and uses Theorem 15.4.1 on `[0, 1] × X` and Stokes.

## What is formalized (namespace `Polyfold.SBLocalization`)

The statements of `theorem_15_4_1_cylinder_index_zero` and
`pointCount_eq_of_isTransversalPerturbation` with two changes: the orientation hypothesis is the
continuity of `o` in the local orientation sets (`IsSectionOrientationLoc`), and the perturbation
of the cylinder is obtained from local families at the interior points of the solution set of
the explicit extension (the hypothesis of `corollary_15_3_10_3_transversal_of_families`).

* `theorem_15_4_1_cylinder_index_zero_loc`,
* **`pointCount_eq_of_isTransversalPerturbation_loc`**.

## Reading

The continuity of the canonical orientations is `canonContinuous_loc`,
`canonContinuous_cubeOrientation_loc`; the matched structures on the ends are
`exists_arePointMatchedAt_of_kernelCanonical_loc`; Stokes is `EP.theorem_9_5_17_dim1_all`,
`EP.theorem_9_5_18_dim1_all`.
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

/-- **Theorem 15.4.1 (2021 p. 702; 2017: Theorem 15.6) for the cobordism, Fredholm index `0`**
(2021 p. 703), for an orientation made with local sc⁺-sections: let `d_X ≡ 0`, `(f, o)` an
sc-Fredholm section functor with tame germ data of index `0`, `o` an orientation of `f` in the
sense of Definition 6.6.16 for the local orientation sets, and `õ = e ∧ o` invariant under the
morphisms of the cylinder.  For a transversal sc⁺-multisection `Λ̃` on `[0, 1] × X` with
`Λ̃ = Λᵢ` over `t = i` and the face condition of Theorem 15.3.9 for the glued data, the formula
of Theorem 15.4.1 for `(f̃, õ)` defines the canonical orientation of `Θ̃ = Λ̃ ∘ f̃`, of dimension
`1`. -/
theorem theorem_15_4_1_cylinder_index_zero_loc (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hsec : A.B.HasScPlusSectionsThrough) (hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy)
    (hoL : IsSectionOrientationLoc (A.X.isTame_of_degIndex_eq_zero hd) hft
      fun y hy => orxLocEquiv hft hsec y hy (o y hy))
    (hinvC : (A.cubeSEP 1).E.IsOrInvariant
      (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft) hsec'
      (cubeOrientation hf hft hsec o))
    (hidx : ∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x 0)
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
  exact theorem_15_4_1_of_isSectionOrientationLoc (isTame_cubeSEP hX) hfC hftC hΛ' hsec'
    (cubeOrientation hf hft hsec o) hinvC
    (isSectionOrientationLoc_cubeOrientation hX hf hft hsec hsec' o hoL)
    (isGoodPositionAt_of_transversal hfC hftC hΛ' htr hgood) hidxC
    ((A.cubeSEP 1).X.hasIndependentTangentSums _)

section Cylinder

variable (hd : ∀ x, A.X.PObj.degIndex x = 0)
  (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
  (hsec : A.B.HasScPlusSectionsThrough) (hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough)
  (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy)
  (hoL : IsSectionOrientationLoc (A.X.isTame_of_degIndex_eq_zero hd) hft
    fun y hy => orxLocEquiv hft hsec y hy (o y hy))
  (hinvC : (A.cubeSEP 1).E.IsOrInvariant (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft)
    hsec' (cubeOrientation hf hft hsec o))
  (hidx : ∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x 0)

set_option maxHeartbeats 1600000 in
-- the cylinder's ep-groupoid is unfolded in several places
include hd hft hoL hinvC hidx in
/-- **2021 Corollary 15.4.4, p. 703, for Fredholm index `0`, over all transversal perturbations
with `N(Λ) ≤ 1`, from local families on the cylinder.**  Let `d_X ≡ 0`, `|X|` be paracompact,
the cylinder carry the local families `H`, and `(f, o)` be an sc-Fredholm section functor with
tame germ data and index `0`, with `o` continuous in the local orientation sets and `õ = e ∧ o`
invariant under the morphisms of the cylinder.  Let `P₀`, `P₁` be the point solution sets of
transversal perturbations `(Nⁱ, Uⁱ, Λⁱ)` (sc⁺, dom-supp in `Uⁱ`, `Nⁱ(Λⁱ) ≤ 1`, transversal; not
assumed structurable) with the canonical orientation of `(f, o)`.  Then a closed `0`-form has
the same weighted signed count over `P₀` and `P₁`, and the same effective count when `X` has the
local unique continuation property.  Neither sc-smooth bump functions nor partitions of unity
are assumed. -/
theorem pointCount_eq_of_isTransversalPerturbation_loc
    (hpara : A.X.HasParacompactOrbitSpace)
    {P₀ P₁ : PointSolution A f} {N₀ N₁ : A.B.One → ℝ} {U₀ U₁ : Set A.Obj}
    (hr₀ : IsTransversalPerturbation A f N₀ U₀ P₀.Λ)
    (hr₁ : IsTransversalPerturbation A f N₁ U₁ P₁.Λ)
    (h₀ : IsCanonicalFor P₀.Λ hf.2 hsec o 0 P₀.T) (h₁ : IsCanonicalFor P₁.Λ hf.2 hsec o 0 P₁.T)
    (H : ∀ x ∉ (A.cubeSEP 1).X.PObj.boundary,
      0 < cylExtension P₀.Λ P₁.Λ (cubeLiftEp (n := 1) f hf.1.1.1 x) →
      ∃ Q : Set (A.cubeSEP 1).Obj, IsOpen Q ∧ (A.cubeSEP 1).X.IsSaturated Q ∧ x ∈ Q ∧
        Nonempty (RelGPFamily (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf.1.1.1)
          (cylExtension P₀.Λ P₁.Λ) (collarAuxNorm A N₀ N₁)
          (interpSet A U₀ U₁ ∩ (A.cubeSEP 1).X.PObj.boundaryᶜ)
          (fun z => (1 + (collarCut₀ (cubeT z) + collarCut₁ (cubeT z))) / 2 -
            pointwiseNorm (collarAuxNorm A N₀ N₁) (cylExtension P₀.Λ P₁.Λ) z) Q))
    (ω : A.baseEP.epFormsInfty 0) (hω : A.baseEP.epFormsInftyD 0 ω = 0) :
    P₀.count ω = P₁.count ω ∧ ∀ hLUC : A.X.IsLUC, P₀.countEff hLUC ω = P₁.countEff hLUC ω := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PMor
  have hX : A.X.IsTame := A.X.isTame_of_degIndex_eq_zero hd
  have hXC : (A.cubeSEP 1).X.IsTame := A.X.isTame_cubeProd 1 hX
  have hftC := isScFredholmSectionTame_cubeLiftEp (n := 1) hft
  have honto := isBoundaryFaceOnto_cubeGlue hd hf hft hr₀.2.2.2.2 hr₁.2.2.2.2
  obtain ⟨Λ', hreg, e0, e1, -, hΘ', hcpt'⟩ :=
    corollary_15_3_10_3_transversal_of_families hd hpara hf hft hr₀ hr₁ H
  have hΛ' : IsScPlusMultisection (A.cubeSEP 1) Λ' := hreg.2.1
  have hcan' := theorem_15_4_1_cylinder_index_zero_loc hd hf hft hsec hsec' o hoL hinvC hidx
    hΛ' hreg.2.2.2.2 e0 e1 honto
  have hT' := hcan'.1
  have hloc' := hcan'.loc
  have hK' := hcan'.isKernelCanonical
    (canonContinuous_cubeOrientation_loc Λ' hX hf hft hsec hsec' o hoL)
  have hK₀ : IsKernelCanonical P₀.Λ hf.2 hsec o P₀.T :=
    IsCanonicalFor.isKernelCanonical h₀ (canonContinuous_loc P₀.Λ hX hft hsec o hoL)
  have hK₁ : IsKernelCanonical P₁.Λ hf.2 hsec o P₁.T :=
    IsCanonicalFor.isKernelCanonical h₁ (canonContinuous_loc P₁.Λ hX hft hsec o hoL)
  have z0 : ((0 : unitInterval) : ℝ) = 0 := rfl
  have z1 : ((1 : unitInterval) : ℝ) = 1 := rfl
  have m0 := exists_arePointMatchedAt_of_kernelCanonical_loc hd hf hft
    (fun x hx => (P₀.loc x hx).imp fun _ h => h.2) hΛ' e0 e1 honto (i := 0) (ε := -1)
    (Or.inl ⟨z0, rfl⟩) e0 hΘ' hK₀ hK'
  have m1 := exists_arePointMatchedAt_of_kernelCanonical_loc hd hf hft
    (fun x hx => (P₁.loc x hx).imp fun _ h => h.2) hΛ' e0 e1 honto (i := 1) (ε := 1)
    (Or.inr ⟨z1, rfl⟩) e1 hΘ' hK₁ hK'
  have hov0 := fun p => cylEndMap_mem_orbitSupp_zero hd hf.1.1.1 e0 e1 p
  have hov1 := fun p => cylEndMap_mem_orbitSupp_one hd hf.1.1.1 e0 e1 p
  have hdω : (A.cubeSEP 1).baseEP.epFormsInftyD 0
      (EP.epFormsInftyPullback (A := (A.cubeSEP 1).baseEP) (B := A.baseEP) (A.X.cubeProj 1)
        0 ω) = 0 := by
    have := LinearMap.congr_fun
      (EP.epFormsInftyD_comp_epFormsInftyPullback (A := (A.cubeSEP 1).baseEP) (B := A.baseEP)
        (A.X.cubeProj 1) 0) ω
    simp only [LinearMap.comp_apply] at this
    rw [this, hω, map_zero]
  refine ⟨?_, fun hLUC => ?_⟩
  · have E0 := boundaryBranchedMeasureDim1_cylEnd_of_pointMatched P₀.isBranched P₀.isCompact
      P₀.isOrientation P₀.loc hΘ' hcpt' hT' hloc' (i := 0) (q := fun _ => 0) z0 hov0 m0 ω
    have E1 := boundaryBranchedMeasureDim1_cylEnd_of_pointMatched P₁.isBranched P₁.isCompact
      P₁.isOrientation P₁.loc hΘ' hcpt' hT' hloc' (i := 1) (q := fun _ => 1) z1 hov1 m1 ω
    have hsum : (A.cubeSEP 1).baseEP.boundaryBranchedMeasureDim1 hΘ' hcpt' hT' hloc'
        (EP.epFormsInftyPullback (A := (A.cubeSEP 1).baseEP) (B := A.baseEP) (A.X.cubeProj 1)
          0 ω) univ = -1 * P₀.count ω + 1 * P₁.count ω :=
      (A.X.signedMeasure_univ_eq_cylEnds (boundary_cyl_time hd)
        ((A.X.cubeProd 1).borel_le_lebesgueSigmaBoundaryH (0 + 1) _)
        ((A.cubeSEP 1).baseEP.boundaryBranchedMeasureDim1 hΘ' hcpt' hT' hloc'
          (EP.epFormsInftyPullback (A := (A.cubeSEP 1).baseEP) (B := A.baseEP) (A.X.cubeProj 1)
            0 ω))).trans (congrArg₂ (· + ·) E0 E1)
    have hS := (A.cubeSEP 1).baseEP.theorem_9_5_17_dim1_all hΘ' hcpt' hT' hloc'
      (EP.epFormsInftyPullback (A := (A.cubeSEP 1).baseEP) (B := A.baseEP) (A.X.cubeProj 1) 0 ω)
    rw [hdω, tameBranchedIntegral_zero, hsum] at hS
    linarith
  · have hLUCC : (A.cubeSEP 1).X.IsLUC := isLUC_cubeSEP hLUC
    have E0 := boundaryBranchedMeasureEffDim1_cylEnd_of_pointMatched hLUC hLUCC
      P₀.isBranched P₀.isCompact P₀.isOrientation (P₀.loc.hasLUC hLUC) hΘ' hcpt' hT'
      ((A.cubeSEP 1).baseEP.hloc_hasLUC_dim1 hLUCC hloc') (i := 0)
      (q := fun _ => 0) z0 hov0 m0 ω
    have E1 := boundaryBranchedMeasureEffDim1_cylEnd_of_pointMatched hLUC hLUCC
      P₁.isBranched P₁.isCompact P₁.isOrientation (P₁.loc.hasLUC hLUC) hΘ' hcpt' hT'
      ((A.cubeSEP 1).baseEP.hloc_hasLUC_dim1 hLUCC hloc') (i := 1)
      (q := fun _ => 1) z1 hov1 m1 ω
    have hsum : (A.cubeSEP 1).baseEP.boundaryBranchedMeasureEffDim1 hΘ' hcpt' hT'
        ((A.cubeSEP 1).baseEP.hloc_hasLUC_dim1 hLUCC hloc')
        (EP.epFormsInftyPullback (A := (A.cubeSEP 1).baseEP) (B := A.baseEP) (A.X.cubeProj 1)
          0 ω) univ = -1 * P₀.countEff hLUC ω + 1 * P₁.countEff hLUC ω :=
      (A.X.signedMeasure_univ_eq_cylEnds (boundary_cyl_time hd)
        ((A.X.cubeProd 1).borel_le_lebesgueSigmaBoundaryH (0 + 1) _)
        ((A.cubeSEP 1).baseEP.boundaryBranchedMeasureEffDim1 hΘ' hcpt' hT'
          ((A.cubeSEP 1).baseEP.hloc_hasLUC_dim1 hLUCC hloc')
          (EP.epFormsInftyPullback (A := (A.cubeSEP 1).baseEP) (B := A.baseEP) (A.X.cubeProj 1)
            0 ω))).trans (congrArg₂ (· + ·) E0 E1)
    have hS := (A.cubeSEP 1).baseEP.theorem_9_5_18_dim1_all hΘ' hcpt' hT'
      ((A.cubeSEP 1).baseEP.hloc_hasLUC_dim1 hLUCC hloc')
      (EP.epFormsInftyPullback (A := (A.cubeSEP 1).baseEP) (B := A.baseEP) (A.X.cubeProj 1) 0 ω)
    have h0 : ((A.cubeSEP 1).baseEP.epFormsInftyEval (0 + 1)).tameBranchedIntegralEff
        (Nat.succ_pos 0) hΘ' hcpt' hT' ((A.cubeSEP 1).baseEP.hloc_hasLUC_dim1 hLUCC hloc') 0 =
        0 := by
      simp only [FormEval.tameBranchedIntegralEff, FormEval.concreteBranchedIntegralEff,
        branchedIntegralEff, map_zero]
      rfl
    rw [hdω, h0, hsum] at hS
    linarith

end Cylinder

end SBLocalization

end Polyfold
