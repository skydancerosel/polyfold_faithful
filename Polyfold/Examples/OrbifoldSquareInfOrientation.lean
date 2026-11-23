import Polyfold.Examples.OrbifoldSquareInfPositive
import Polyfold.Examples.OrbifoldSquareInfPerturbation
import Polyfold.Examples.OrInvariantSmooth

/-!
# The orbifold `(ℂ × H)/ℤ₅` and the section `(z, e) ↦ (z², e)`: the orientation and Theorem 16.6.6

The infinite-dimensional version of the worked example `ℂ/ℤ₅`, `z ↦ z²`, for Hofer–Wysocki–Zehnder,
*Polyfold and Fredholm Theory* (Springer 2021), **Theorem 16.6.6**, 2021 p. 739, for Fredholm
index `0`, with Definitions 12.5.4 (p. 594) and 16.6.5 (p. 739).

## What is formalized (namespace `Polyfold.Examples.OrbifoldSquareInf`)

* `orMor_zero_inf`: every isotropy morphism `((g, 0), e)` acts as the identity on `Or^f_{(0,e)}`
  (it has order dividing `5`, and `Or^f_{(0,e)}` has two elements).
* `isOrInvariant_of_isContOrOn_inf`: a continuous orientation of `f` over `ℂ × H` is invariant
  under the morphisms: at a morphism `((g, z), e)` with `e` smooth, the invariance is constant
  along `t ↦ ((g, t z), e)` and holds at `t = 0`; at the other morphisms there is nothing to show.
* **`infOrientationRepPos`**: the orientation of the sc-Fredholm section (Definition 16.6.5) which
  is positive at the isomorphisms `(2z, id)`, `z ≠ 0`.
* **`theorem_16_6_6_hypotheses_inf`**: the hypotheses of Theorem 16.6.6 for index `0`:
  `∂Z = ∅`, compact solution set, auxiliary norm, `(n, Z)` controls compactness, tame germ data
  and Fredholm index `0`.
* `theorem_16_6_6_inf`, `exists_canonical_tinf`, `count_eq_of_isAdmissible_inf`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

open scoped ContDiff

noncomputable section

namespace Polyfold.Examples.OrbifoldSquareInf

open TrivialBundle EpGroupoid EpGroupoid.Examples StrongBundle MPolyfold StrongPolyfoldBundle
  StrongPolyfoldBundleStructure StrongBundleEquivalenceExamples
  StrongBundleLocalizationExamples SBLocalization StrongRetr WeightedEllTwo OrbifoldSquare
  PolyfoldClass

/-- The morphism `((g, z), e)` of `(ℤ/5 ⋉ ℂ) × H`. -/
def mor (g : G5) (z : Fin 2 → ℝ) (e : HObj) : Ainf.Mor :=
  (((g, z), e) : (G5 × (Fin 2 → ℝ)) × HObj)

theorem src_mor (g : G5) (z : Fin 2 → ℝ) (e : HObj) : Ainf.X.src (mor g z e) = (z, e) := rfl

theorem tgt_mor (g : G5) (z : Fin 2 → ℝ) (e : HObj) : Ainf.X.tgt (mor g z e) = (g • z, e) := rfl

theorem tgt_mor_zero (g : G5) (e : HObj) :
    Ainf.X.tgt (mor g 0 e) = (((0 : Fin 2 → ℝ), e) : Ainf.Obj) :=
  Prod.ext (smul_zero5 g) rfl

/-! ### The isotropy of `(0, e)` acts trivially on `Or^f_{(0,e)}` -/

/-- **Every isotropy morphism `((g, 0), e)` acts as the identity on `Or^f_{(0, e)}`**: `g⁵ = 1`
and `Or^f_{(0, e)}` has two elements. -/
theorem orMor_zero_inf (g : G5) (e : HObj)
    (hs : (((0 : Fin 2 → ℝ), e) : Ainf.Obj) ∈ Ainf.X.PObj.smoothSet)
    (o : Orx (B := Ainf.B) sqInf isScFredholmSectionFunctor_sqInf.2
      (((0 : Fin 2 → ℝ), e) : Ainf.Obj) hs) :
    Ainf.E.orMor isScFredholmSectionFunctor_sqInf hasScPlusSectionsThrough_Ainf
      (mor g 0 e) rfl (tgt_mor_zero g e) hs hs o = o := by
  have hF := isScFredholmSectionFunctor_sqInf
  have hsec := hasScPlusSectionsThrough_Ainf
  let E : G5 → (Orx (B := Ainf.B) sqInf hF.2 (((0 : Fin 2 → ℝ), e) : Ainf.Obj) hs ≃
      Orx (B := Ainf.B) sqInf hF.2 (((0 : Fin 2 → ℝ), e) : Ainf.Obj) hs) :=
    fun a => Ainf.E.orMor hF hsec (mor a 0 e) rfl (tgt_mor_zero a e) hs hs
  have key : ∀ a b : G5, (E b).trans (E a) = E (a * b) := fun a b =>
    Ainf.E.orMor_comp hF hsec (φ := mor b 0 e) (ψ := mor a 0 e) rfl
      (tgt_mor_zero b e) rfl (tgt_mor_zero a e) hs hs hs
  have hone : E 1 = Equiv.refl _ :=
    Ainf.E.orMor_unit hF hsec (σ := mor 1 0 e) (x := (((0 : Fin 2 → ℝ), e) : Ainf.Obj)) rfl rfl
      (tgt_mor_zero 1 e) hs
  have hg : ∀ a : G5, a * (a * (a * (a * a))) = 1 := by decide
  have two := exists_two_orx hF.2 hs hsec
  have h5 : E g (E g (E g (E g (E g o)))) = o := by
    have k1 := DFunLike.congr_fun (key g g) o
    have k2 := DFunLike.congr_fun (key g (g * g)) o
    have k3 := DFunLike.congr_fun (key g (g * (g * g))) o
    have k4 := DFunLike.congr_fun (key g (g * (g * (g * g)))) o
    rw [Equiv.trans_apply] at k1 k2 k3 k4
    rw [k1, k2, k3, k4, hg g, hone]
    rfl
  have h2 : ∀ p, E g (E g p) = p := equiv_apply_apply_of_two two (E g)
  rw [h2, h2] at h5
  exact h5

/-! ### The invariance of a continuous orientation -/

/-- **Every continuous orientation of `f` over all of `ℂ × H` is invariant under the morphisms**
(Definition 12.5.4). -/
theorem isOrInvariant_of_isContOrOn_inf
    [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × Ainf.Obj)]
    [∀ n : ℕ, ParacompactSpace (pullbackSpace Ainf.P
      (Prod.snd : (Fin n → ℝ) × Ainf.Obj → Ainf.Obj))]
    [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × Ainf.Obj))]
    [∀ k n : ℕ, ParacompactSpace (pullbackSpace
      (pullbackProj Ainf.P (Prod.snd : (Fin n → ℝ) × Ainf.Obj → Ainf.Obj))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × Ainf.Obj) → (Fin n → ℝ) × Ainf.Obj))]
    {o : ∀ a (hs : a ∈ Ainf.X.PObj.smoothSet),
      Orx (B := Ainf.B) sqInf isScFredholmSectionFunctor_sqInf.2 a hs}
    (ho : IsContOrOn (orLocalTransport isTame_Ainf admitsBumpFunctions_Ainf
      isScFredholmSectionTame_sqInf hasScPlusSectionsThrough_Ainf) univ o) :
    Ainf.E.IsOrInvariant isScFredholmSectionFunctor_sqInf hasScPlusSectionsThrough_Ainf o := by
  have hF := isScFredholmSectionFunctor_sqInf
  have hsec := hasScPlusSectionsThrough_Ainf
  refine (Ainf.E.isOrInvariant_iff_forall_isOrInvariantAt hF hsec).2 fun m => ?_
  obtain ⟨⟨g, z⟩, e⟩ : (G5 × (Fin 2 → ℝ)) × HObj := m
  change Ainf.E.IsOrInvariantAt hF hsec o (mor g z e)
  by_cases he : ((e : HObj) : H 0) ∈ H.smooth
  · have hsm : ∀ y : Fin 2 → ℝ, ((y, e) : Ainf.Obj) ∈ Ainf.X.PObj.smoothSet := fun y =>
      (mem_smoothSet_Ainf_iff (x := ((y, e) : (Fin 2 → ℝ) × HObj))).2 he
    have hc : Continuous fun t : ℝ => mor g (t • z) e :=
      (continuous_const.prodMk (continuous_id.smul continuous_const)).prodMk continuous_const
    have h := Ainf.E.isOrInvariantAt_iff_of_continuous hF hsec isTame_Ainf
      admitsBumpFunctions_Ainf isScFredholmSectionTame_sqInf ho hc (fun t => hsm _)
      (fun t => hsm _) 1 0
    have e1 : mor g ((1 : ℝ) • z) e = mor g z e := by rw [one_smul]
    have e0 : mor g ((0 : ℝ) • z) e = mor g 0 e := by rw [zero_smul]
    rw [e1, e0] at h
    refine h.2 ?_
    refine (Ainf.E.isOrInvariantAt_iff' hF hsec).2 fun {x x'} hx hx' hs₁ hs₂ => ?_
    obtain rfl : (((0 : Fin 2 → ℝ), e) : Ainf.Obj) = x := hx
    obtain rfl : (((0 : Fin 2 → ℝ), e) : Ainf.Obj) = x' := (tgt_mor_zero g e).symm.trans hx'
    exact orMor_zero_inf g e hs₁ _
  · intro hs _
    exact absurd ((mem_smoothSet_Ainf_iff (x := ((z, e) : (Fin 2 → ℝ) × HObj))).1 hs) he

/-! ### The orientation -/

/-- **`infOrientationPos` is an orientation in the sense of Definition 12.5.4.** -/
theorem definition_12_5_4_infOrientationPos :
    haveI := paracompactSpace_rn_prod Ainf.X.PObj
    haveI := paracompactSpace_rn_pullback Ainf.B
    haveI := paracompactSpace_rn_rn_prod Ainf.X.PObj
    haveI := paracompactSpace_rn_rn_pullback Ainf.B
    Ainf.E.definition_12_5_4 isScFredholmSectionFunctor_sqInf hasScPlusSectionsThrough_Ainf
      (orTopology (orLocalTransport isTame_Ainf admitsBumpFunctions_Ainf
        isScFredholmSectionTame_sqInf hasScPlusSectionsThrough_Ainf)) infOrientationPos := by
  have := paracompactSpace_rn_prod Ainf.X.PObj
  have := paracompactSpace_rn_pullback Ainf.B
  have := paracompactSpace_rn_rn_prod Ainf.X.PObj
  have := paracompactSpace_rn_rn_pullback Ainf.B
  exact ⟨continuous_orSec_infOrientationPos,
    isOrInvariant_of_isContOrOn_inf isContOrOn_infOrientationPos⟩

/-- Part I's topology on `O_f` is a topology with the properties of Theorem 12.5.3. -/
theorem isOrientationTopology_sqInf :
    haveI := paracompactSpace_rn_prod Ainf.X.PObj
    haveI := paracompactSpace_rn_pullback Ainf.B
    haveI := paracompactSpace_rn_rn_prod Ainf.X.PObj
    haveI := paracompactSpace_rn_rn_pullback Ainf.B
    IsOrientationTopology (B := Ainf.B) sqInf isScFredholmSectionFunctor_sqInf.2
      (orTopology (orLocalTransport isTame_Ainf admitsBumpFunctions_Ainf
        isScFredholmSectionTame_sqInf hasScPlusSectionsThrough_Ainf)) := by
  have := paracompactSpace_rn_prod Ainf.X.PObj
  have := paracompactSpace_rn_pullback Ainf.B
  have := paracompactSpace_rn_rn_prod Ainf.X.PObj
  have := paracompactSpace_rn_rn_pullback Ainf.B
  obtain ⟨t₀, ht₀⟩ := (theorem_6_6_17 isTame_Ainf admitsBumpFunctions_Ainf
    isScFredholmSectionTame_sqInf).exists
  exact eq_orTopology_of isTame_Ainf admitsBumpFunctions_Ainf isScFredholmSectionTame_sqInf
    hasScPlusSectionsThrough_Ainf ht₀.isLocalHomeomorph ht₀.propagation ▸ ht₀

/-- **The orientation of the sc-Fredholm section `|(z, e)| ↦ |((z, z²), (e, e))|`**
(Definition 16.6.5) which is positive at the isomorphisms `(f − f(z, 0))'(z, 0) = (2z, id)`,
`z ≠ 0`. -/
def infOrientationRepPos : OrientationRep infFredholmSection where
  a := infRep
  ha := rfl
  hF := isScFredholmSectionFunctor_sqInf
  hsec := hasScPlusSectionsThrough_Ainf
  t := haveI := paracompactSpace_rn_prod Ainf.X.PObj
    haveI := paracompactSpace_rn_pullback Ainf.B
    haveI := paracompactSpace_rn_rn_prod Ainf.X.PObj
    haveI := paracompactSpace_rn_rn_pullback Ainf.B
    orTopology (orLocalTransport isTame_Ainf admitsBumpFunctions_Ainf
      isScFredholmSectionTame_sqInf hasScPlusSectionsThrough_Ainf)
  isOrientationTopology := isOrientationTopology_sqInf
  o := infOrientationPos
  isOrientation := definition_12_5_4_infOrientationPos

/-- **Tame germ data and Fredholm index `0`** in the model of `infOrientationRepPos`. -/
theorem canonicalGermInput_infOrientationRepPos : CanonicalGermInput infOrientationRepPos 0 :=
  ⟨isScFredholmSectionTame_sqInf, fun x hx => by exact_mod_cast isIndexAt_sqInf x hx⟩

/-! ### Theorem 16.6.6 for index `0` -/

/-- **The hypotheses of Theorem 16.6.6 (2021 p. 739) for index `0` hold for
`|(z, e)| ↦ |((z, z²), (e, e))|` over `(ℂ × H)/ℤ₅`**: `∂Z = ∅`, the solution set is compact, `n`
is an auxiliary norm, `Z` is open, `(n, Z)` controls compactness, and the model of the
orientation `infOrientationRepPos` has tame germ data and Fredholm index `0`. -/
theorem theorem_16_6_6_hypotheses_inf :
    infBundle.polyfold.boundary = ∅ ∧ infFredholmSection.1.HasCompactSolutionSet ∧
      infBundle.IsAuxNorm ninf ∧ IsOpen (univ : Set Ainf.X.OrbitSpace) ∧
      infFredholmSection.1.ControlsCompactness ninf (univ : Set Ainf.X.OrbitSpace) ∧
      CanonicalGermInput infOrientationRepPos 0 :=
  ⟨infBundle_boundary_eq_empty, hasCompactSolutionSet_infFredholmSection, isAuxNorm_ninf,
    isOpen_univ, controlsCompactness_ninf, canonicalGermInput_infOrientationRepPos⟩

/-- **Theorem 16.6.6 (2021 p. 739) for index `0`, for the section over `(ℂ × H)/ℤ₅`**, in the
form of `theorem_16_6_6_index_zero_polyfold_statement`. -/
theorem theorem_16_6_6_inf :
    theorem_16_6_6_index_zero_polyfold_statement infFredholmSection ninf
      (univ : Set Ainf.X.OrbitSpace)
      (fun o Q => CanonicalGermInput o 0 ∧ IsCanonicalPointSolutionSet o Q) :=
  theorem_16_6_6_index_zero_all_admissible_unconditional _ _ _

/-- **The multisection `λ_c` with five branches is admissible and has a canonically oriented
perturbed solution set**, for `0 < |c| ≤ 1`. -/
theorem exists_canonical_tinf {c : ℂ} (hc0 : c ≠ 0) (hc1 : ‖c‖ ≤ 1) :
    ∃ Q : PointOrientedPerturbation infFredholmSection.1, Q.t = tinf c ∧
      Q.IsAdmissible ninf (univ : Set Ainf.X.OrbitSpace) ∧
      IsCanonicalPointSolutionSet infOrientationRepPos Q :=
  theorem_16_6_6_index_zero_solutionSet_noBumps infBundle_boundary_eq_empty isAuxNorm_ninf
    isOpen_univ controlsCompactness_ninf canonicalGermInput_infOrientationRepPos (tinf c)
    (isControlledBy_tinf hc1) (isInGeneralPositionWith_tinf hc0)

/-- **The count does not depend on the admissible perturbation** (Theorem 16.6.6, 2021 p. 739,
index `0`). -/
theorem count_eq_of_isAdmissible_inf {Q₀ Q₁ : PointOrientedPerturbation infFredholmSection.1}
    (a₀ : Q₀.IsAdmissible ninf (univ : Set Ainf.X.OrbitSpace))
    (c₀ : IsCanonicalPointSolutionSet infOrientationRepPos Q₀)
    (a₁ : Q₁.IsAdmissible ninf (univ : Set Ainf.X.OrbitSpace))
    (c₁ : IsCanonicalPointSolutionSet infOrientationRepPos Q₁)
    (τ : ScForm infBundle.polyfold 0) (hτ : ScForm.d τ = 0) :
    Q₀.count τ = Q₁.count τ ∧ Q₀.countEff τ = Q₁.countEff τ :=
  theorem_16_6_6_index_zero_count_eq_unconditional infBundle_boundary_eq_empty isAuxNorm_ninf
    isOpen_univ controlsCompactness_ninf canonicalGermInput_infOrientationRepPos a₀ c₀ a₁ c₁ τ hτ

end Polyfold.Examples.OrbifoldSquareInf
