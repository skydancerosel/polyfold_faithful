import Polyfold.Chapter15.CylinderEndMatching

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, p. 703:
**Corollary 15.4.4** (2017: Corollary 15.2), the step "`∂Θ̃ = Θ₁ ⊔ −Θ₀`" of its proof,
assembled from the structures on the ends of the cylinder.

# Corollary 15.4.4 from the orientations of the matched structures

## The text, paraphrased

The cobordism `Θ̃ = Λ̃ ∘ f̃` over `[0, 1] × X` restricts to `Θᵢ` over `{i} × X`; with the canonical
orientations (Theorem 15.4.1) and the boundary orientation, `∂Θ̃ = Θ₁ ⊔ −Θ₀`, and Stokes' theorem
gives the equality of the integrals.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `CylinderMatchedOrientationsStatement`: every regular perturbation `Λ̃` of `f̃` that step (b)
  of the proof can produce carries an orientation `T̃`, described by oriented tame structures of
  dimension `m + 2`, such that at both ends every pair of a local branching structure of `Θ̃` at
  `(i, x)` described by kernels and its slice structure of `Θᵢ` at `x` has orientations
  describing `T̃` and the orientation of `Pᵢ`, with a positive frame of the sheet of `Θ̃` that
  starts with a vector of positive `t`-component and continues with a positive frame of the
  slice (`HasMatchedOrientations`).
* **`cylinderLocalEndsStatement_of_matchedOrientations`**: this gives the local end identities
  (`CylinderLocalEndsStatement`): the weights, the slices, the isotropy groups, the sheet
  integrals and the signs `−1` at `t = 0`, `+1` at `t = 1` are proved.
* **`corollary_15_4_4_of_matchedOrientations`**: Corollary 15.4.4 with step (c) of its proof in
  this form.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP

variable {A : SEP.{u}}

/-- **The orientations of the cobordism and of its ends, on matched structures** (step (c) of
the proof of Corollary 15.4.4 as a statement about orientations only): every regular
perturbation `Λ̃` of `f̃` on `[0, 1] × X` with `Λ̃ = Λᵢ` over `t = i` carries an orientation `T̃`
of `Θ̃`, described by oriented tame structures of dimension `m + 2`, such that for `i = 0, 1`
every pair of a local branching structure `K̃` of `Θ̃` at `(i, x)` described by kernels and a
slice structure `B` of `Θᵢ` at `x` has `HasMatchedOrientations` for `T̃` and the orientation of
`Pᵢ`. -/
def CylinderMatchedOrientationsStatement {f : A.Obj → A.W} (hf : IsSection A.P f) {m : ℕ}
    (P₀ P₁ : OrientedRegularPerturbation A f m) : Prop :=
  ∀ Λ' : (A.cubeSEP 1).W → ℚ≥0,
    IsRegularPerturbation (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf)
      (interpAuxNorm A P₀.N P₁.N) (interpSet A P₀.U P₁.U) Λ' →
    (∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = P₀.Λ (cubeVal w).2) →
    (∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = P₁.Λ (cubeVal w).2) →
    (A.cubeSEP 1).X.IsBranchedEpSubgroupoid
        (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ)) →
    (A.cubeSEP 1).X.IsCompactBranched (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ)) →
    ∃ T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ,
      (A.cubeSEP 1).X.IsOrientation (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ)) T' ∧
      (∀ x ∈ EpGroupoid.supp (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ)),
        ∃ C : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1)
          (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ)) x, C.Represents T') ∧
      (∀ x, 0 < P₀.Λ (f x) → ∀ (K' : KernelBranching (A.cubeSEP 1)
          (cubeLiftEp (n := 1) f hf) Λ' ((fun _ => 0), x))
        (B : A.X.TameBranchingStructure (fun z => (P₀.Λ (f z) : ℚ)) x) (e : K'.ι ≃ B.ι),
        (∀ j, K'.σ j = B.σ (e j)) →
        (∀ y, y ∈ B.U ↔ (((fun _ => 0), y) : (A.cubeSEP 1).Obj) ∈ K'.U) →
        (∀ p ∈ K'.U, p ∈ (A.cubeSEP 1).X.PObj.boundary → p.1 = fun _ => 0) →
        (∀ j, B.M (e j) = {y | (((fun _ => 0), y) : (A.cubeSEP 1).Obj) ∈ K'.M j}) →
        (∀ j, (A.cubeSEP 1).X.PObj.boundaryStratum (K'.M j) =
          (cubeFaceIncl A (fun _ => 0)).obj '' B.M (e j)) →
        (∀ j, A.X.PObj.IsSubmanifoldOfDim (B.M (e j)) (K'.dim j - 1)) →
        HasMatchedOrientations m hf P₀.T T' (fun _ => 0) K' B e) ∧
      (∀ x, 0 < P₁.Λ (f x) → ∀ (K' : KernelBranching (A.cubeSEP 1)
          (cubeLiftEp (n := 1) f hf) Λ' ((fun _ => 1), x))
        (B : A.X.TameBranchingStructure (fun z => (P₁.Λ (f z) : ℚ)) x) (e : K'.ι ≃ B.ι),
        (∀ j, K'.σ j = B.σ (e j)) →
        (∀ y, y ∈ B.U ↔ (((fun _ => 1), y) : (A.cubeSEP 1).Obj) ∈ K'.U) →
        (∀ p ∈ K'.U, p ∈ (A.cubeSEP 1).X.PObj.boundary → p.1 = fun _ => 1) →
        (∀ j, B.M (e j) = {y | (((fun _ => 1), y) : (A.cubeSEP 1).Obj) ∈ K'.M j}) →
        (∀ j, (A.cubeSEP 1).X.PObj.boundaryStratum (K'.M j) =
          (cubeFaceIncl A (fun _ => 1)).obj '' B.M (e j)) →
        (∀ j, A.X.PObj.IsSubmanifoldOfDim (B.M (e j)) (K'.dim j - 1)) →
        HasMatchedOrientations m hf P₁.T T' (fun _ => 1) K' B e)

set_option maxHeartbeats 1600000 in
-- the cylinder's ep-groupoid is unfolded in several places
/-- **The local end identities from the orientations of the matched structures** (proof of
Corollary 15.4.4, p. 703): for `d_X ≡ 0`, `f` sc-Fredholm with tame germ data and the face
condition of Theorem 15.3.9 for the glued data, `CylinderMatchedOrientationsStatement` gives
`CylinderLocalEndsStatement`. -/
theorem cylinderLocalEndsStatement_of_matchedOrientations (hd : ∀ x, A.X.PObj.degIndex x = 0)
    {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) {m : ℕ} {P₀ P₁ : OrientedRegularPerturbation A f m}
    (honto : IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue P₀.Λ P₁.Λ))
    (h : CylinderMatchedOrientationsStatement hf.1.1.1 P₀ P₁) :
    CylinderLocalEndsStatement hf.1.1.1 P₀ P₁ := by
  intro Λ' hreg e0 e1 hΘ' hcpt'
  obtain ⟨T', hT', hloc', hor₀, hor₁⟩ := h Λ' hreg e0 e1 hΘ' hcpt'
  have hΛ' : IsScPlusMultisection (A.cubeSEP 1) Λ' := hreg.2.1.1
  have z0 : ((0 : unitInterval) : ℝ) = 0 := rfl
  have z1 : ((1 : unitInterval) : ℝ) = 1 := rfl
  refine ⟨T', hT', hloc', fun p => cylEndMap_mem_orbitSupp_zero hd hf.1.1.1 e0 e1 p,
    fun p => cylEndMap_mem_orbitSupp_one hd hf.1.1.1 e0 e1 p, ?_, ?_⟩
  · exact isLocalEndIdentity_of_matched P₀ hΘ' hcpt' hT' hloc' (i := 0) _
      (exists_areMatchedAt_of_orientations hd hf hft P₀ hΛ' e0 e1 honto (i := 0)
        (Or.inl ⟨z0, rfl⟩) e0 hΘ' hor₀)
  · exact isLocalEndIdentity_of_matched P₁ hΘ' hcpt' hT' hloc' (i := 1) _
      (exists_areMatchedAt_of_orientations hd hf hft P₁ hΛ' e0 e1 honto (i := 1)
        (Or.inr ⟨z1, rfl⟩) e1 hΘ' hor₁)

/-- **Corollary 15.4.4 (2017: Corollary 15.2), p. 703, from the orientations of the matched
structures**: `corollary_15_4_4_of_local_ends` with step (c) reduced to
`CylinderMatchedOrientationsStatement`. -/
theorem corollary_15_4_4_of_matchedOrientations
    (hrelC : theorem_15_3_7_relative_statement (A.cubeSEP 1))
    (hd : ∀ x, A.X.PObj.degIndex x = 0) (hpara : A.X.HasParacompactOrbitSpace)
    (hPU : A.X.HasScPartitionsOfUnity) (hPUC : (A.cubeSEP 1).X.PObj.AdmitsScPartitionsOfUnity)
    {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) (hS : A.E.HasCompactSolutionSetEp f) {m : ℕ}
    (Can : OrientedRegularPerturbation A f m → Prop)
    (hglue : ∀ P₀ P₁, Can P₀ → Can P₁ →
      IsBoundaryStructurable (A.cubeSEP 1) (cubeGlue P₀.Λ P₁.Λ) ∧
        IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue P₀.Λ P₁.Λ))
    (hor : ∀ P₀ P₁, Can P₀ → Can P₁ →
      CylinderMatchedOrientationsStatement hf.1.1.1 P₀ P₁) :
    corollary_15_4_4_statement A f m Can :=
  corollary_15_4_4_of_local_ends hrelC hd hpara hPU hPUC hf hft hS Can hglue fun P₀ P₁ h₀ h₁ =>
    cylinderLocalEndsStatement_of_matchedOrientations hd hf hft (hglue P₀ P₁ h₀ h₁).2
      (hor P₀ P₁ h₀ h₁)

end SBLocalization

end Polyfold
