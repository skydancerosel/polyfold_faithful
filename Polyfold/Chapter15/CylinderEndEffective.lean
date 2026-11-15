import Polyfold.Chapter15.CylinderEndLocalization

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, p. 703:
**Corollary 15.4.4** (2017: Corollary 15.2), effective version: the step "`∂Θ̃ = Θ₁ ⊔ −Θ₀`"
for the effective measures of Theorems 9.5.5 and 9.5.16, from local structures.

# The effective local end identity from local structures

## The text, paraphrased

The effective boundary measure of `Θ̃` (Theorem 9.5.16) and the effective measure of `Θᵢ`
(Theorem 9.5.5) are given near the points of the supports by the local formulas with
`1/♯G^eff`.  If these agree up to the sign `ε` for one pair of structures near each point of
`|supp Θᵢ|`, the effective end identities follow.

## What is formalized

* `EP.boundaryMeasureEff_spec`: the local formula of Theorem 9.5.16 for `EP.boundaryMeasureEff`.
* **`isLocalEndIdentityEff_of_structures`**: the effective local end identity from an oriented
  tame structure `C` of `Θᵢ` at `x` and one `C̃` of `Θ̃` at a point over `x` whose effective
  local formulas agree up to `ε` over a neighbourhood of `|x|`.
* `CylinderLocalEndsEffStatement`, `cylinderOrientationEffStatement_of_local_ends`,
  **`corollary_15_4_4_eff_of_local_ends`**: the effective Corollary 15.4.4 with step (c) of its
  proof in the local form, with Theorem 15.3.9 on the cylinder reduced to the relative step.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace EP

open EpGroupoid

variable {A : EP.{u}} {m : ℕ} {Θ : A.Obj → ℚ} {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ}

/-- `boundaryMeasureEff` is the measure of Theorem 9.5.16 (it has the local formula with
`1/♯G_x^eff`). -/
theorem boundaryMeasureEff_spec (hm : 0 < m) (hLUC : A.X.IsLUC)
    (hΘ : A.X.IsBranchedEpSubgroupoid Θ) (hcpt : A.X.IsCompactBranched Θ)
    (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T)
    (ω : A.epFormsInfty m) (x : A.Obj) (C : A.X.OrientedTameStructure (m + 1) Θ x)
    (hCT : C.Represents T) (hx : x ∈ supp (A.X.boundaryTheta Θ))
    (hS : ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ (A.epFormsInftyEval m).msheets)
    (K : Set (A.X.orbitSupp (A.X.boundaryTheta Θ)))
    (hK : MeasurableSet[A.X.lebesgueSigmaBoundaryH (m + 1) Θ] K)
    (hKU : Subtype.val '' K ⊆ A.X.π '' C.U) :
    A.boundaryMeasureEff hm hLUC hΘ hcpt hT hloc ω K = (Nat.card (A.X.EffIsotropy x) : ℝ)⁻¹ *
      (C.boundaryFamily hΘ hCT).nonemptyPart.sheetSum
        ((A.epFormsInftyEval m).msheetIntegration hm) ω (A.X.π ⁻¹' (Subtype.val '' K)) :=
  (theorem_9_5_16_msheets (A.epFormsInftyEval m) hm hΘ hcpt
    (FormEval.isNDimensional_of_loc (A.hcovS_of_loc_isLUC hm hLUC hΘ hcpt hloc)) hT
    (fun x hx => ((A.hcovS_of_loc_isLUC hm hLUC hΘ hcpt hloc) x
      (A.X.supp_boundaryTheta_subset Θ hx).2).imp
      fun _ h => ⟨h.1, h.2.2.1, h.2.2.2⟩)).exists.choose_spec
    ω x C hCT hx hS (A.X.isLUC_iff_forall_naturalRep.1 hLUC x C.rep) K hK hKU

end EP

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP

variable {A : SEP.{u}}

set_option maxHeartbeats 1600000 in
-- the statement unfolds the cylinder's ep-groupoid in several places
/-- **The effective local end identity from local structures**: as
`isLocalEndIdentity_of_structures`, for the effective measures.  For every `x ∈ supp Θ` an
oriented tame structure `C` of `Θ` at `x` describing the orientation of `P` (sheets in the
class of the integration), one `C̃` of `Θ̃` at a point `z ∈ supp ∂Θ̃` describing `T̃` (nonempty
boundary sheets in the class of the integration) and an open neighbourhood `N` of `|x|` inside
`|U(x)|` over which the end `i` lies in `|Ũ(z)|`, such that for Borel `K` over `N` the local
formula of Theorem 9.5.16 for `C̃` and `pr^*ω` is `ε` times the one of Theorem 9.5.5 for `C`
and `ω`. -/
theorem isLocalEndIdentityEff_of_structures {f : A.Obj → A.W} {m : ℕ} (hLUC : A.X.IsLUC)
    (hLUCC : (A.cubeSEP 1).X.IsLUC) (P : OrientedRegularPerturbation A f m)
    {Θ' : (A.cubeSEP 1).Obj → ℚ} {T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ}
    (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid Θ')
    (hcpt' : (A.cubeSEP 1).X.IsCompactBranched Θ') (hT' : (A.cubeSEP 1).X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1) Θ' x, C.Represents T')
    {i ε : ℝ}
    (hover : ∀ p : cylEnd (X := A.X) Θ' i,
      cylEndMap p ∈ A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ)))
    (h : ∀ x ∈ EpGroupoid.supp (fun z => (P.Λ (f z) : ℚ)),
      ∃ (C : A.X.OrientedTameStructure (m + 1) (fun z => (P.Λ (f z) : ℚ)) x)
        (z : (A.cubeSEP 1).Obj) (C' : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1) Θ' z)
        (hCT' : C'.Represents T') (N : Set A.X.OrbitSpace),
        (∀ j, C.M j ∈ (A.baseEP.epFormsInftyEval (m + 1)).sheets) ∧ C.Represents P.T ∧
        z ∈ EpGroupoid.supp ((A.cubeSEP 1).X.boundaryTheta Θ') ∧
        (∀ j, (C'.boundarySheet j).Nonempty →
          C'.boundarySheet j ∈ ((A.cubeSEP 1).baseEP.epFormsInftyEval (m + 1)).msheets) ∧
        IsOpen N ∧ A.X.π x ∈ N ∧ N ⊆ A.X.π '' C.U ∧
        (∀ p : cylEnd (X := A.X) Θ' i, cylEndMap p ∈ N →
          p.1.1 ∈ (A.cubeSEP 1).X.π '' C'.U) ∧
        ∀ (ω : A.baseEP.epFormsInfty (m + 1))
          (K : Set (A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ)))),
          MeasurableSet[borel _] K → Subtype.val '' K ⊆ N →
          (Nat.card ((A.cubeSEP 1).X.EffIsotropy z) : ℝ)⁻¹ *
              (C'.boundaryFamily hΘ' hCT').nonemptyPart.sheetSum
                (((A.cubeSEP 1).baseEP.epFormsInftyEval (m + 1)).msheetIntegration
                  (Nat.succ_pos m))
                (EP.epFormsInftyPullback (A.X.cubeProj 1) (m + 1) ω)
                ((A.cubeSEP 1).X.π ⁻¹'
                  (Subtype.val '' (Subtype.val '' (cylEndProj hover ⁻¹' K)))) =
            ε * C.localMeasureEff
              ((A.baseEP.epFormsInftyEval (m + 1)).sheetIntegration (Nat.succ_pos m)) ω
              (Subtype.val '' K)) :
    IsLocalEndIdentityEff hLUC hLUCC P hΘ' hcpt' hT' hloc' i ε hover := by
  intro ω s
  obtain ⟨x, hx, hxs⟩ := s.2
  obtain ⟨C, z, C', hCT', N, hCS, hCT, hz, hS', hNo, hxN, hNU, hNU', hid⟩ := h x hx
  refine ⟨Subtype.val ⁻¹' N, hNo.preimage continuous_subtype_val, by
    change s.1 ∈ N
    rw [← hxs]
    exact hxN, fun K hK hKN => ?_⟩
  have hKN' : Subtype.val '' K ⊆ N := image_subset_iff.2 hKN
  have hm' := measurableSet_image_preimage_borel (A.X.isClosed_cylEnd Θ' i)
    (continuous_cylEndProj hover) hK
  have hKU' : Subtype.val '' (Subtype.val '' (cylEndProj hover ⁻¹' K)) ⊆
      (A.cubeSEP 1).X.π '' C'.U := by
    rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact hNU' p (hKN' ⟨_, hp, rfl⟩)
  have e1 := (A.cubeSEP 1).baseEP.boundaryMeasureEff_spec (Nat.succ_pos m) hLUCC hΘ' hcpt' hT'
    hloc' (EP.epFormsInftyPullback (A.X.cubeProj 1) (m + 1) ω) z C' hCT' hz hS'
    (Subtype.val '' (cylEndProj hover ⁻¹' K))
    ((A.X.cubeProd 1).borel_le_lebesgueSigmaBoundaryH (m + 1 + 1) Θ' _ hm') hKU'
  have e2 : P.measureEff hLUC ω K = C.localMeasureEff
      ((A.baseEP.epFormsInftyEval (m + 1)).sheetIntegration (Nat.succ_pos m)) ω
      (Subtype.val '' K) :=
    EpGroupoid.branchedMeasureEff_apply _ P.isBranched P.isCompact P.isOrientation _ ω C hCS hCT
      (A.X.isLUC_iff_forall_naturalRep.1 hLUC x C.rep) (borel_le_borelNullSigma _ _ hK)
      (hKN'.trans hNU)
  rw [e2, ← hid ω K hK hKN']
  exact e1

/-! ### The effective Corollary 15.4.4 from the local end identities -/

/-- **Step (c) of the proof of Corollary 15.4.4 in local form, effective version**: every
structurable regular perturbation `Λ̃` of `f̃` on `[0, 1] × X` that step (b) can produce carries
an orientation `T̃`, described by oriented tame structures of dimension `m + 2`, with the
effective local end identities (sign `−1` over `Θ₀`, sign `+1` over `Θ₁`). -/
def CylinderLocalEndsEffStatement {f : A.Obj → A.W} (hf : IsSection A.P f) {m : ℕ}
    (hLUC : A.X.IsLUC) (hLUCC : (A.cubeSEP 1).X.IsLUC)
    (P₀ P₁ : OrientedRegularPerturbation A f m) : Prop :=
  ∀ Λ' : (A.cubeSEP 1).W → ℚ≥0,
    IsRegularPerturbation (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf)
      (interpAuxNorm A P₀.N P₁.N) (interpSet A P₀.U P₁.U) Λ' →
    (∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = P₀.Λ (cubeVal w).2) →
    (∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = P₁.Λ (cubeVal w).2) →
    ∀ (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid
        (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ)))
      (hcpt' : (A.cubeSEP 1).X.IsCompactBranched
        (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ))),
    ∃ (T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ)
      (hT' : (A.cubeSEP 1).X.IsOrientation (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ)) T')
      (hloc' : ∀ x ∈ EpGroupoid.supp (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ)),
        ∃ C : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1)
          (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ)) x, C.Represents T')
      (hover₀ : ∀ p : cylEnd (X := A.X) (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ)) 0,
        cylEndMap p ∈ A.X.orbitSupp (fun z => (P₀.Λ (f z) : ℚ)))
      (hover₁ : ∀ p : cylEnd (X := A.X) (fun z => (Λ' (cubeLiftEp (n := 1) f hf z) : ℚ)) 1,
        cylEndMap p ∈ A.X.orbitSupp (fun z => (P₁.Λ (f z) : ℚ))),
      IsLocalEndIdentityEff hLUC hLUCC P₀ hΘ' hcpt' hT' hloc' 0 (-1) hover₀ ∧
        IsLocalEndIdentityEff hLUC hLUCC P₁ hΘ' hcpt' hT' hloc' 1 1 hover₁

/-- The effective local form of step (c) gives `CylinderOrientationEffStatement`. -/
theorem cylinderOrientationEffStatement_of_local_ends {f : A.Obj → A.W} (hf : IsSection A.P f)
    {m : ℕ} {hLUC : A.X.IsLUC} {hLUCC : (A.cubeSEP 1).X.IsLUC}
    {P₀ P₁ : OrientedRegularPerturbation A f m}
    (h : CylinderLocalEndsEffStatement hf hLUC hLUCC P₀ P₁) :
    CylinderOrientationEffStatement hf hLUC hLUCC P₀ P₁ := by
  intro Λ' hreg e0 e1 hΘ' hcpt'
  obtain ⟨T', hT', hloc', hover₀, hover₁, h₀, h₁⟩ := h Λ' hreg e0 e1 hΘ' hcpt'
  exact ⟨T', hT', hloc', isCylinderBoundaryEffOf_of_local hLUC hLUCC P₀ P₁ hΘ' hcpt' hT' hloc'
    hover₀ hover₁ h₀ h₁⟩

/-- **Corollary 15.4.4, effective version (p. 703), from the local end identities**: Theorem
15.3.9 on the cylinder reduced to the relative general position step (`hrelC`), the tame
strong bundle charts of `[0, 1] × X` proved, and step (c) in its effective local form. -/
theorem corollary_15_4_4_eff_of_local_ends
    (hrelC : theorem_15_3_7_relative_statement (A.cubeSEP 1))
    (hd : ∀ x, A.X.PObj.degIndex x = 0) (hpara : A.X.HasParacompactOrbitSpace)
    (hPU : A.X.HasScPartitionsOfUnity) (hLUC : A.X.IsLUC)
    (hPUC : (A.cubeSEP 1).X.PObj.AdmitsScPartitionsOfUnity) (hLUCC : (A.cubeSEP 1).X.IsLUC)
    {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) (hS : A.E.HasCompactSolutionSetEp f) {m : ℕ}
    (Can : OrientedRegularPerturbation A f m → Prop)
    (hglue : ∀ P₀ P₁, Can P₀ → Can P₁ →
      IsBoundaryStructurable (A.cubeSEP 1) (cubeGlue P₀.Λ P₁.Λ) ∧
        IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue P₀.Λ P₁.Λ))
    (hor : ∀ P₀ P₁, Can P₀ → Can P₁ →
      CylinderLocalEndsEffStatement hf.1.1.1 hLUC hLUCC P₀ P₁) :
    corollary_15_4_4_eff_statement A f m hLUC Can := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PMor
  have hXC : (A.cubeSEP 1).X.IsTame :=
    A.X.isTame_cubeProd 1 (A.X.isTame_of_degIndex_eq_zero hd)
  exact corollary_15_4_4_eff_cylinder_hyp (theorem_15_3_9_charged_hyp hrelC)
    ((A.cubeSEP 1).exists_isTameChart hXC) hd hpara hPU hLUC hPUC hLUCC hf hft hS Can hglue
    fun P₀ P₁ h₀ h₁ => cylinderOrientationEffStatement_of_local_ends hf.1.1.1 (hor P₀ P₁ h₀ h₁)

end SBLocalization

end Polyfold
