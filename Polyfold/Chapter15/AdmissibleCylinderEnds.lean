import Polyfold.Chapter15.CollarCobordismCorollary
import Polyfold.Chapter15.AdmissibleCylinderExtension

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, p. 703: the proof
of **Corollary 15.4.4** (2017: Corollary 15.2), step (c), `∂Θ̃ = Θ₁ ⊔ −Θ₀`, for solution sets
`Θ = Λ ∘ f` of sc⁺-multisections that are not assumed structurable.

# The end identities of the cylinder for oriented solution sets

## The text, paraphrased

(p. 703) `Θ̃ = Λ̃ ∘ f̃` on `[0, 1] × X` is canonically oriented by `(f̃, õ)`, and its oriented
boundary is `Θ₁ ⊔ −Θ₀` (outward normal `+∂_t` at `t = 1`, `−∂_t` at `t = 0`, Definition 9.3.10).

## What is formalized (namespace `Polyfold.SBLocalization`)

* `OrientedSolution A f m`: an sc⁺-multisection `Λ` with `Θ = Λ ∘ f` compact and branched, an
  orientation `T̂` of `Θ`, and oriented tame structures of dimension `m + 1` describing it (the
  data of `OrientedRegularPerturbation` without `(N, U)` and without the regularity of `Λ`);
  `OrientedSolution.ofRegular`, `integral`, `integralEff`, `measure`, `measureEff`.
* Namespace `Adm`: the local end identities for an `OrientedSolution` in place of an oriented
  regular perturbation: `IsLocalEndIdentity`, `boundaryMeasure_cylEnd_of_local`,
  `isLocalEndIdentity_of_structures`, `isLocalEndIdentity_of_matched`, their effective forms, and
  `exists_areMatchedAt_of_kernelCanonical`.  The proofs are those of the files
  `CylinderEndLocalization`, `CylinderEndEffective`, `CylinderEndStructures`,
  `CylinderEndEffectiveMatching`, `CylinderEndCanonical`, which do not use the regularity of `Λ`.

## Reading

The statements for oriented regular perturbations are the special case `OrientedSolution.ofRegular`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology MeasureTheory Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP

variable {A : SEP.{u}}

variable (A) in
/-- **An oriented solution set of dimension `m + 1`**: an sc⁺-multisection `Λ` with
`Θ = Λ ∘ f` compact and branched, and an orientation `T̂` of `Θ` described by oriented tame
structures of dimension `m + 1` (Theorem 15.4.3, 2021 p. 702).  Neither structurability of `Λ`
nor a bound on `N(Λ)` is part of the data. -/
structure OrientedSolution (f : A.Obj → A.W) (m : ℕ) where
  /-- The perturbation. -/
  Λ : A.W → ℚ≥0
  isScPlusMultisection : IsScPlusMultisection A Λ
  /-- The orientation `T̂` of `Θ = Λ ∘ f`. -/
  T : A.Obj → A.X.PObj.OrTangent →₀ ℚ
  isBranched : A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ))
  isCompact : A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ))
  isOrientation : A.X.IsOrientation (fun z => (Λ (f z) : ℚ)) T
  loc : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)),
    ∃ C : A.X.OrientedTameStructure (m + 1) (fun z => (Λ (f z) : ℚ)) x, C.Represents T

namespace OrientedSolution

variable {f : A.Obj → A.W} {m : ℕ}

/-- The oriented solution set of an oriented regular perturbation. -/
def ofRegular (P : OrientedRegularPerturbation A f m) : OrientedSolution A f m where
  Λ := P.Λ
  isScPlusMultisection := P.isRegular.2.1.1
  T := P.T
  isBranched := P.isBranched
  isCompact := P.isCompact
  isOrientation := P.isOrientation
  loc := P.loc

/-- `∫_{(Λ ∘ f, T̂)} ω` for `ω ∈ Ω^{m+1}_{ep,∞}(X)` (Definition 9.5.6 (1)). -/
def integral (P : OrientedSolution A f m) (ω : A.baseEP.epFormsInfty (m + 1)) : ℝ :=
  (A.baseEP.epFormsInftyEval (m + 1)).tameBranchedIntegral (Nat.succ_pos m) P.isBranched
    P.isCompact P.isOrientation P.loc ω

/-- `∮_{(Λ ∘ f, T̂)} ω`, for `X` with the local unique continuation property (Definition 9.5.6
(2)). -/
def integralEff (hLUC : A.X.IsLUC) (P : OrientedSolution A f m)
    (ω : A.baseEP.epFormsInfty (m + 1)) : ℝ :=
  (A.baseEP.epFormsInftyEval (m + 1)).tameBranchedIntegralEff (Nat.succ_pos m) P.isBranched
    P.isCompact P.isOrientation (A.baseEP.hloc_hasLUC hLUC P.loc) ω

theorem integral_ofRegular (P : OrientedRegularPerturbation A f m)
    (ω : A.baseEP.epFormsInfty (m + 1)) : (ofRegular P).integral ω = P.integral ω := rfl

theorem integralEff_ofRegular (hLUC : A.X.IsLUC) (P : OrientedRegularPerturbation A f m)
    (ω : A.baseEP.epFormsInfty (m + 1)) :
    (ofRegular P).integralEff hLUC ω = P.integralEff hLUC ω := rfl

/-- **The measure `ω ↦ μ_ω` of Theorem 9.5.4** on `(|supp Θ|, L(S))`, `Θ = Λ ∘ f`. -/
def measure (P : OrientedSolution A f m) :
    A.baseEP.epFormsInfty (m + 1) →ₗ[ℝ]
      @SignedMeasure (A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ)))
        (A.X.lebesgueSigma (A.baseEP.epFormsInftyEval (m + 1)).sheetNull
          (fun z => (P.Λ (f z) : ℚ))) :=
  EpGroupoid.branchedMeasure
    ((A.baseEP.epFormsInftyEval (m + 1)).sheetIntegration (Nat.succ_pos m)) P.isBranched
    P.isCompact P.isOrientation
    (EpGroupoid.FormEval.hcov_of_tameOpen (EpGroupoid.FormEval.tameOpen A.X) P.loc)

/-- `∫_{(Λ ∘ f, T̂)} ω = μ_ω(|supp Θ|)` (Definition 9.5.6 (1)). -/
theorem integral_eq_measure_univ (P : OrientedSolution A f m)
    (ω : A.baseEP.epFormsInfty (m + 1)) : P.integral ω = P.measure ω univ :=
  rfl

/-- **The effective measure `ω ↦ μ^eff_ω` of Theorem 9.5.5**, for `X` with the local unique
continuation property. -/
def measureEff (hLUC : A.X.IsLUC) (P : OrientedSolution A f m) :
    A.baseEP.epFormsInfty (m + 1) →ₗ[ℝ]
      @SignedMeasure (A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ)))
        (A.X.lebesgueSigma (A.baseEP.epFormsInftyEval (m + 1)).sheetNull
          (fun z => (P.Λ (f z) : ℚ))) :=
  EpGroupoid.branchedMeasureEff
    ((A.baseEP.epFormsInftyEval (m + 1)).sheetIntegration (Nat.succ_pos m)) P.isBranched
    P.isCompact P.isOrientation
    (EpGroupoid.FormEval.hcovEff_of_tameOpen (EpGroupoid.FormEval.tameOpen A.X)
      (A.baseEP.hloc_hasLUC hLUC P.loc))

/-- `∮_{(Λ ∘ f, T̂)} ω = μ^eff_ω(|supp Θ|)` (Definition 9.5.6 (2)). -/
theorem integralEff_eq_measureEff_univ (hLUC : A.X.IsLUC)
    (P : OrientedSolution A f m) (ω : A.baseEP.epFormsInfty (m + 1)) :
    P.integralEff hLUC ω = P.measureEff hLUC ω univ :=
  rfl

end OrientedSolution

namespace Adm

/-- **The local end identity** on the end `i` with sign `ε`: every point of `|supp Θ|` has an
open neighbourhood `N` such that, for every Borel `K ⊆ N`, the boundary measure of `pr^*ω` on
the part of the end `i` over `K` is `ε · μ^Θ_ω(K)`. -/
def IsLocalEndIdentity {f : A.Obj → A.W} {m : ℕ} (P : OrientedSolution A f m)
    {Θ' : (A.cubeSEP 1).Obj → ℚ} {T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ}
    (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid Θ')
    (hcpt' : (A.cubeSEP 1).X.IsCompactBranched Θ') (hT' : (A.cubeSEP 1).X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1) Θ' x, C.Represents T')
    (i ε : ℝ)
    (hover : ∀ p : cylEnd (X := A.X) Θ' i,
      cylEndMap p ∈ A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ))) : Prop :=
  ∀ (ω : A.baseEP.epFormsInfty (m + 1)) (s : A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ))),
    ∃ N : Set (A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ))), IsOpen N ∧ s ∈ N ∧
      ∀ K : Set (A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ))), MeasurableSet[borel _] K → K ⊆ N →
        (A.cubeSEP 1).baseEP.boundaryMeasure (Nat.succ_pos m) hΘ' hcpt' hT' hloc'
            (EP.epFormsInftyPullback (A.X.cubeProj 1) (m + 1) ω)
            (Subtype.val '' (cylEndProj hover ⁻¹' K)) = ε * P.measure ω K


/-- **The end identity from the local end identity**: the boundary measure of `pr^*ω` on the
whole end `i` is `ε · ∫_{Θ} ω`. -/
theorem boundaryMeasure_cylEnd_of_local {f : A.Obj → A.W} {m : ℕ}
    (P : OrientedSolution A f m)
    {Θ' : (A.cubeSEP 1).Obj → ℚ} {T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ}
    (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid Θ')
    (hcpt' : (A.cubeSEP 1).X.IsCompactBranched Θ') (hT' : (A.cubeSEP 1).X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1) Θ' x, C.Represents T')
    {i ε : ℝ}
    (hover : ∀ p : cylEnd (X := A.X) Θ' i,
      cylEndMap p ∈ A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ)))
    (h : IsLocalEndIdentity P hΘ' hcpt' hT' hloc' i ε hover)
    (ω : A.baseEP.epFormsInfty (m + 1)) :
    (A.cubeSEP 1).baseEP.boundaryMeasure (Nat.succ_pos m) hΘ' hcpt' hT' hloc'
        (EP.epFormsInftyPullback (A.X.cubeProj 1) (m + 1) ω) (cylEnd (X := A.X) Θ' i) =
      ε * P.integral ω := by
  have : CompactSpace (A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ))) :=
    isCompact_iff_compactSpace.1 P.isCompact
  rw [P.integral_eq_measure_univ]
  exact signedMeasure_closed_eq_of_local (borel_le_borelNullSigma _)
    ((A.X.cubeProd 1).borel_le_lebesgueSigmaBoundaryH (m + 1 + 1) Θ') _ _
    (A.X.isClosed_cylEnd Θ' i) (cylEndProj hover) (continuous_cylEndProj hover) ε (h ω)


set_option maxHeartbeats 1600000 in
-- the statement unfolds the cylinder's ep-groupoid in several places
/-- **The local end identity from local structures**: let every `x ∈ supp Θ` have an oriented
tame structure `C` of `Θ` at `x` describing the orientation of `P` (sheets in the class of the
integration), an oriented tame structure `C̃` of `Θ̃` at a point `z ∈ supp ∂Θ̃` describing `T̃`
(nonempty boundary sheets in the class of the integration), and an open neighbourhood `N` of
`|x|` in `|X|` inside `|U(x)|` over which the end `i` lies in `|Ũ(z)|`, such that for all Borel
`K` over `N` the local formula of Theorem 9.5.15 for `C̃`, `pr^*ω` and the part of the end over
`K` is `ε` times the local formula (9.21) of Theorem 9.5.4 for `C`, `ω` and `K`.  Then the local
end identity holds. -/
theorem isLocalEndIdentity_of_structures {f : A.Obj → A.W} {m : ℕ}
    (P : OrientedSolution A f m)
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
          (Nat.card ((A.cubeSEP 1).X.Isotropy z) : ℝ)⁻¹ *
              (C'.boundaryFamily hΘ' hCT').nonemptyPart.sheetSum
                (((A.cubeSEP 1).baseEP.epFormsInftyEval (m + 1)).msheetIntegration
                  (Nat.succ_pos m))
                (EP.epFormsInftyPullback (A.X.cubeProj 1) (m + 1) ω)
                ((A.cubeSEP 1).X.π ⁻¹'
                  (Subtype.val '' (Subtype.val '' (cylEndProj hover ⁻¹' K)))) =
            ε * C.localMeasure
              ((A.baseEP.epFormsInftyEval (m + 1)).sheetIntegration (Nat.succ_pos m)) ω
              (Subtype.val '' K)) :
    IsLocalEndIdentity P hΘ' hcpt' hT' hloc' i ε hover := by
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
  have e1 := (A.cubeSEP 1).baseEP.boundaryMeasure_spec (Nat.succ_pos m) hΘ' hcpt' hT' hloc'
    (EP.epFormsInftyPullback (A.X.cubeProj 1) (m + 1) ω) z C' hCT' hz hS'
    (Subtype.val '' (cylEndProj hover ⁻¹' K))
    ((A.X.cubeProd 1).borel_le_lebesgueSigmaBoundaryH (m + 1 + 1) Θ' _ hm') hKU'
  have e2 : P.measure ω K = C.localMeasure
      ((A.baseEP.epFormsInftyEval (m + 1)).sheetIntegration (Nat.succ_pos m)) ω
      (Subtype.val '' K) :=
    EpGroupoid.branchedMeasure_apply _ P.isBranched P.isCompact P.isOrientation _ ω C hCS hCT
      (borel_le_borelNullSigma _ _ hK) (hKN'.trans hNU)
  rw [e2, ← hid ω K hK hKN']
  exact e1


/-- **The local end identity, effective form**: as `IsLocalEndIdentity`, for the effective
boundary measure (Theorem 9.5.16) and the effective measure of `Θ` (Theorem 9.5.5). -/
def IsLocalEndIdentityEff {f : A.Obj → A.W} {m : ℕ} (hLUC : A.X.IsLUC)
    (hLUCC : (A.cubeSEP 1).X.IsLUC) (P : OrientedSolution A f m)
    {Θ' : (A.cubeSEP 1).Obj → ℚ} {T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ}
    (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid Θ')
    (hcpt' : (A.cubeSEP 1).X.IsCompactBranched Θ') (hT' : (A.cubeSEP 1).X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1) Θ' x, C.Represents T')
    (i ε : ℝ)
    (hover : ∀ p : cylEnd (X := A.X) Θ' i,
      cylEndMap p ∈ A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ))) : Prop :=
  ∀ (ω : A.baseEP.epFormsInfty (m + 1)) (s : A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ))),
    ∃ N : Set (A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ))), IsOpen N ∧ s ∈ N ∧
      ∀ K : Set (A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ))), MeasurableSet[borel _] K → K ⊆ N →
        (A.cubeSEP 1).baseEP.boundaryMeasureEff (Nat.succ_pos m) hLUCC hΘ' hcpt' hT' hloc'
            (EP.epFormsInftyPullback (A.X.cubeProj 1) (m + 1) ω)
            (Subtype.val '' (cylEndProj hover ⁻¹' K)) = ε * P.measureEff hLUC ω K


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
    (hLUCC : (A.cubeSEP 1).X.IsLUC) (P : OrientedSolution A f m)
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


set_option maxHeartbeats 1600000 in
-- the statement unfolds the cylinder's ep-groupoid in several places
/-- **The local end identity from matched structures** (proof of Corollary 15.4.4, p. 703):
let every `x ∈ supp Θ` have an oriented tame structure `C` of `Θ` at `x` (sheets in the class of
the integration, describing the orientation of `P`) and one `C̃` of `Θ̃` at `(i, x)` describing
`T̃` that match with sign `ε`.  Then the boundary measure of `pr^*ω` on the end `i` is locally
`ε` times the measure of `ω` on `|supp Θ|`. -/
theorem isLocalEndIdentity_of_matched {f : A.Obj → A.W} {m : ℕ}
    (P : OrientedSolution A f m)
    {Θ' : (A.cubeSEP 1).Obj → ℚ} {T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ}
    (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid Θ')
    (hcpt' : (A.cubeSEP 1).X.IsCompactBranched Θ') (hT' : (A.cubeSEP 1).X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1) Θ' x, C.Represents T')
    {i : unitInterval} {ε : ℝ}
    (hover : ∀ p : cylEnd (X := A.X) Θ' (i : ℝ),
      cylEndMap p ∈ A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ)))
    (h : ∀ x ∈ EpGroupoid.supp (fun z => (P.Λ (f z) : ℚ)),
      ∃ (C : A.X.OrientedTameStructure (m + 1) (fun z => (P.Λ (f z) : ℚ)) x)
        (C' : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1) Θ' ((fun _ => i), x))
        (hCT' : C'.Represents T') (hS : ∀ j, C.M j ∈ (A.baseEP.epFormsInftyEval (m + 1)).sheets),
        C.Represents P.T ∧ AreMatchedAt (fun _ => i) C C' hΘ' hCT' hS ε) :
    IsLocalEndIdentity P hΘ' hcpt' hT' hloc' (i : ℝ) ε hover := by
  classical
  set q : Fin 1 → unitInterval := fun _ => i with hq
  refine isLocalEndIdentity_of_structures P hΘ' hcpt' hT' hloc' hover fun x hx => ?_
  obtain ⟨C, C', hCT', hS, hCT, e, he, hrange, hσ, hM, hU, hε⟩ := h x hx
  -- the point `(i, x)` lies in `supp ∂Θ̃`
  have hsupp : ∀ j : (C'.boundaryFamily hΘ' hCT').nonemptyPart.ι, ∀ y ∈ C.M (e j),
      ((q, y) : (A.cubeSEP 1).Obj) ∈ EpGroupoid.supp ((A.cubeSEP 1).X.boundaryTheta Θ') :=
    fun j y hy => C'.boundarySheet_subset_supp_boundaryTheta j.1 (by
      rw [hM j]
      exact ⟨y, hy, rfl⟩)
  have hrg : ∀ j₀ : C.ι, ∀ y ∈ C.M j₀, ∃ j, e j = j₀ := fun j₀ y hy => by
    by_contra hne
    have := hrange j₀ (fun ⟨j, hj⟩ => hne ⟨j, hj⟩)
    rw [this] at hy
    exact hy
  have hz : ((q, x) : (A.cubeSEP 1).Obj) ∈
      EpGroupoid.supp ((A.cubeSEP 1).X.boundaryTheta Θ') := by
    obtain ⟨j₀, hj₀⟩ := (C.toLocalBranchingStructure.mem_supp_iff C.mem_U).1 hx
    obtain ⟨j, rfl⟩ := hrg j₀ x hj₀
    exact hsupp j x hj₀
  have hS' : ∀ j, (C'.boundarySheet j).Nonempty →
      C'.boundarySheet j ∈ ((A.cubeSEP 1).baseEP.epFormsInftyEval (m + 1)).msheets :=
    fun j hj => by
      have := hM ⟨j, hj⟩
      rw [this]
      exact cubeFace_mem_msheets q (hS _)
  have hNo : IsOpen (A.X.π '' C.U) := A.X.proposition_7_1_8 _ C.isOpen_U
  refine ⟨C, (q, x), C', hCT', A.X.π '' C.U, hS, hCT, hz, hS', hNo, ⟨x, C.mem_U, rfl⟩,
    Subset.rfl, ?_, ?_⟩
  · -- the end over `|U(x)|` lies in `|Ũ(i, x)|`
    intro p hp
    obtain ⟨z, -, hzp⟩ := p.1.2
    obtain ⟨y, hyU, hy⟩ := hp
    rw [A.X.cylEndMap_π p z hzp] at hy
    have ht : (z.1 0 : ℝ) = i := by
      have h2 : A.X.cylOrbitTime p.1.1 = i := p.2
      rwa [← hzp, cylOrbitTime_π] at h2
    have hz1 : z.1 = q := funext fun a => by
      have : a = 0 := Subsingleton.elim _ _
      subst this
      exact Subtype.ext ht
    refine ⟨(q, y), hU y hyU, ?_⟩
    rw [← hzp]
    exact ((A.X.cubeProd_π_eq_π_iff 1 (q, y) z).2 ⟨hz1.symm, hy⟩)
  · intro ω K hK hKN
    have hcl : IsClosed (A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ))) := P.isCompact.isClosed
    have hKb : MeasurableSet[borel A.X.OrbitSpace] (Subtype.val '' K) := by
      let _ : MeasurableSpace A.X.OrbitSpace := borel _
      have : BorelSpace A.X.OrbitSpace := ⟨rfl⟩
      have : BorelSpace (A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ))) := Subtype.borelSpace _
      exact hcl.measurableSet.subtype_image (by
        rw [BorelSpace.measurable_eq (α := A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ)))]
        exact hK)
    have hA₀ : MeasurableSet[borel A.Obj] (A.X.π ⁻¹' (Subtype.val '' K)) := by
      let _ : MeasurableSpace A.X.OrbitSpace := borel _
      have : BorelSpace A.X.OrbitSpace := ⟨rfl⟩
      let _ : MeasurableSpace A.Obj := borel _
      have : BorelSpace A.Obj := ⟨rfl⟩
      exact A.X.continuous_π.measurable hKb
    have hA : ∀ j₀, (A.cubeSEP 1).X.π ⁻¹'
          (Subtype.val '' (Subtype.val '' (cylEndProj hover ⁻¹' K))) ∩
          (cubeFaceIncl A q).obj '' C.M j₀ =
        (cubeFaceIncl A q).obj '' (A.X.π ⁻¹' (Subtype.val '' K) ∩ C.M j₀) := by
      intro j₀
      ext w
      constructor
      · rintro ⟨hw, y, hy, rfl⟩
        refine ⟨y, ⟨?_, hy⟩, rfl⟩
        obtain ⟨_, ⟨p, hpK, rfl⟩, hpw⟩ := hw
        have := A.X.cylEndMap_π p (q, y) hpw.symm
        exact ⟨cylEndProj hover p, hpK, this⟩
      · rintro ⟨y, ⟨⟨s, hsK, hsy⟩, hy⟩, rfl⟩
        refine ⟨?_, y, hy, rfl⟩
        obtain ⟨j, rfl⟩ := hrg j₀ y hy
        let p : cylEnd (X := A.X) Θ' (i : ℝ) :=
          ⟨⟨(A.X.cubeProd 1).π (q, y), (q, y), hsupp j y hy, rfl⟩, by
            change A.X.cylOrbitTime ((A.X.cubeProd 1).π (q, y)) = i
            rw [cylOrbitTime_π]⟩
        have hp : cylEndProj hover p = s := Subtype.ext (by
          change cylEndMap p = s.1
          rw [A.X.cylEndMap_π p (q, y) rfl]
          exact hsy.symm)
        exact ⟨_, ⟨p, by change cylEndProj hover p ∈ K; rw [hp]; exact hsK, rfl⟩, rfl⟩
    have hAm : ∀ j₀, (A.baseEP.epFormsInftyEval (m + 1)).sheetNull.IsMeasIn (C.M j₀)
        (A.X.π ⁻¹' (Subtype.val '' K) ∩ C.M j₀) := fun j₀ =>
      SheetNullSets.isMeasIn_inter_iff.2 (SheetNullSets.isMeasIn_of_borel hA₀)
    have hε' : (ε = 1 ∧ ∀ j, ∀ y ∈ A.X.π ⁻¹' (Subtype.val '' K) ∩ C.M (e j),
          (C'.boundaryOrient j.1).tangent ((cubeFaceIncl A q).obj y) =
            (faceOrient q (C.orient (e j)) (hS (e j)).1.1).tangent
              ((cubeFaceIncl A q).obj y)) ∨
        (ε = -1 ∧ ∀ j, ∀ y ∈ A.X.π ⁻¹' (Subtype.val '' K) ∩ C.M (e j),
          (C'.boundaryOrient j.1).tangent ((cubeFaceIncl A q).obj y) ≠
            (faceOrient q (C.orient (e j)) (hS (e j)).1.1).tangent
              ((cubeFaceIncl A q).obj y)) :=
      hε.imp (fun h => ⟨h.1, fun j y hy => h.2 j y hy.2⟩)
        (fun h => ⟨h.1, fun j y hy => h.2 j y hy.2⟩)
    have key := sheetSum_boundaryFamily_cubeFace q C C' hΘ' hCT' hS e he hrange hσ hM hA hAm
      hε' ω
    have hcard : Nat.card ((A.cubeSEP 1).X.Isotropy ((q, x) : (A.cubeSEP 1).Obj)) =
        Nat.card (A.X.Isotropy x) := A.X.card_isotropy_cubeProd 1 (q, x)
    rw [key, hcard]
    change _ = ε * ((Nat.card (A.X.Isotropy x) : ℝ)⁻¹ * _)
    ring


set_option maxHeartbeats 1600000 in
-- the statement unfolds the cylinder's ep-groupoid in several places
/-- **The effective local end identity from matched structures** (proof of Corollary 15.4.4,
p. 703, for the measures of Theorems 9.5.5 and 9.5.16): let every `x ∈ supp Θ` have an oriented
tame structure `C` of `Θ` at `x` (sheets in the class of the integration, describing the
orientation of `P`) and one `C̃` of `Θ̃` at `(i, x)` describing `T̃` that match with sign `ε`.
Then the effective boundary measure of `pr^*ω` on the end `i` is locally `ε` times the effective
measure of `ω` on `|supp Θ|`: the sheet sums agree up to `ε`, and
`♯G^eff_{(i, x)} = ♯G^eff_x`. -/
theorem isLocalEndIdentityEff_of_matched {f : A.Obj → A.W} {m : ℕ} (hLUC : A.X.IsLUC)
    (hLUCC : (A.cubeSEP 1).X.IsLUC) (P : OrientedSolution A f m)
    {Θ' : (A.cubeSEP 1).Obj → ℚ} {T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ}
    (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid Θ')
    (hcpt' : (A.cubeSEP 1).X.IsCompactBranched Θ') (hT' : (A.cubeSEP 1).X.IsOrientation Θ' T')
    (hloc' : ∀ x ∈ EpGroupoid.supp Θ',
      ∃ C : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1) Θ' x, C.Represents T')
    {i : unitInterval} {ε : ℝ}
    (hover : ∀ p : cylEnd (X := A.X) Θ' (i : ℝ),
      cylEndMap p ∈ A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ)))
    (h : ∀ x ∈ EpGroupoid.supp (fun z => (P.Λ (f z) : ℚ)),
      ∃ (C : A.X.OrientedTameStructure (m + 1) (fun z => (P.Λ (f z) : ℚ)) x)
        (C' : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1) Θ' ((fun _ => i), x))
        (hCT' : C'.Represents T') (hS : ∀ j, C.M j ∈ (A.baseEP.epFormsInftyEval (m + 1)).sheets),
        C.Represents P.T ∧ AreMatchedAt (fun _ => i) C C' hΘ' hCT' hS ε) :
    IsLocalEndIdentityEff hLUC hLUCC P hΘ' hcpt' hT' hloc' (i : ℝ) ε hover := by
  classical
  set q : Fin 1 → unitInterval := fun _ => i with hq
  refine isLocalEndIdentityEff_of_structures hLUC hLUCC P hΘ' hcpt' hT' hloc' hover
    fun x hx => ?_
  obtain ⟨C, C', hCT', hS, hCT, e, he, hrange, hσ, hM, hU, hε⟩ := h x hx
  -- the point `(i, x)` lies in `supp ∂Θ̃`
  have hsupp : ∀ j : (C'.boundaryFamily hΘ' hCT').nonemptyPart.ι, ∀ y ∈ C.M (e j),
      ((q, y) : (A.cubeSEP 1).Obj) ∈ EpGroupoid.supp ((A.cubeSEP 1).X.boundaryTheta Θ') :=
    fun j y hy => C'.boundarySheet_subset_supp_boundaryTheta j.1 (by
      rw [hM j]
      exact ⟨y, hy, rfl⟩)
  have hrg : ∀ j₀ : C.ι, ∀ y ∈ C.M j₀, ∃ j, e j = j₀ := fun j₀ y hy => by
    by_contra hne
    have := hrange j₀ (fun ⟨j, hj⟩ => hne ⟨j, hj⟩)
    rw [this] at hy
    exact hy
  have hz : ((q, x) : (A.cubeSEP 1).Obj) ∈
      EpGroupoid.supp ((A.cubeSEP 1).X.boundaryTheta Θ') := by
    obtain ⟨j₀, hj₀⟩ := (C.toLocalBranchingStructure.mem_supp_iff C.mem_U).1 hx
    obtain ⟨j, rfl⟩ := hrg j₀ x hj₀
    exact hsupp j x hj₀
  have hS' : ∀ j, (C'.boundarySheet j).Nonempty →
      C'.boundarySheet j ∈ ((A.cubeSEP 1).baseEP.epFormsInftyEval (m + 1)).msheets :=
    fun j hj => by
      have := hM ⟨j, hj⟩
      rw [this]
      exact cubeFace_mem_msheets q (hS _)
  have hNo : IsOpen (A.X.π '' C.U) := A.X.proposition_7_1_8 _ C.isOpen_U
  refine ⟨C, (q, x), C', hCT', A.X.π '' C.U, hS, hCT, hz, hS', hNo, ⟨x, C.mem_U, rfl⟩,
    Subset.rfl, ?_, ?_⟩
  · -- the end over `|U(x)|` lies in `|Ũ(i, x)|`
    intro p hp
    obtain ⟨z, -, hzp⟩ := p.1.2
    obtain ⟨y, hyU, hy⟩ := hp
    rw [A.X.cylEndMap_π p z hzp] at hy
    have ht : (z.1 0 : ℝ) = i := by
      have h2 : A.X.cylOrbitTime p.1.1 = i := p.2
      rwa [← hzp, cylOrbitTime_π] at h2
    have hz1 : z.1 = q := funext fun a => by
      have : a = 0 := Subsingleton.elim _ _
      subst this
      exact Subtype.ext ht
    refine ⟨(q, y), hU y hyU, ?_⟩
    rw [← hzp]
    exact ((A.X.cubeProd_π_eq_π_iff 1 (q, y) z).2 ⟨hz1.symm, hy⟩)
  · intro ω K hK hKN
    have hcl : IsClosed (A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ))) := P.isCompact.isClosed
    have hKb : MeasurableSet[borel A.X.OrbitSpace] (Subtype.val '' K) := by
      let _ : MeasurableSpace A.X.OrbitSpace := borel _
      have : BorelSpace A.X.OrbitSpace := ⟨rfl⟩
      have : BorelSpace (A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ))) := Subtype.borelSpace _
      exact hcl.measurableSet.subtype_image (by
        rw [BorelSpace.measurable_eq (α := A.X.orbitSupp (fun z => (P.Λ (f z) : ℚ)))]
        exact hK)
    have hA₀ : MeasurableSet[borel A.Obj] (A.X.π ⁻¹' (Subtype.val '' K)) := by
      let _ : MeasurableSpace A.X.OrbitSpace := borel _
      have : BorelSpace A.X.OrbitSpace := ⟨rfl⟩
      let _ : MeasurableSpace A.Obj := borel _
      have : BorelSpace A.Obj := ⟨rfl⟩
      exact A.X.continuous_π.measurable hKb
    have hA : ∀ j₀, (A.cubeSEP 1).X.π ⁻¹'
          (Subtype.val '' (Subtype.val '' (cylEndProj hover ⁻¹' K))) ∩
          (cubeFaceIncl A q).obj '' C.M j₀ =
        (cubeFaceIncl A q).obj '' (A.X.π ⁻¹' (Subtype.val '' K) ∩ C.M j₀) := by
      intro j₀
      ext w
      constructor
      · rintro ⟨hw, y, hy, rfl⟩
        refine ⟨y, ⟨?_, hy⟩, rfl⟩
        obtain ⟨_, ⟨p, hpK, rfl⟩, hpw⟩ := hw
        have := A.X.cylEndMap_π p (q, y) hpw.symm
        exact ⟨cylEndProj hover p, hpK, this⟩
      · rintro ⟨y, ⟨⟨s, hsK, hsy⟩, hy⟩, rfl⟩
        refine ⟨?_, y, hy, rfl⟩
        obtain ⟨j, rfl⟩ := hrg j₀ y hy
        let p : cylEnd (X := A.X) Θ' (i : ℝ) :=
          ⟨⟨(A.X.cubeProd 1).π (q, y), (q, y), hsupp j y hy, rfl⟩, by
            change A.X.cylOrbitTime ((A.X.cubeProd 1).π (q, y)) = i
            rw [cylOrbitTime_π]⟩
        have hp : cylEndProj hover p = s := Subtype.ext (by
          change cylEndMap p = s.1
          rw [A.X.cylEndMap_π p (q, y) rfl]
          exact hsy.symm)
        exact ⟨_, ⟨p, by change cylEndProj hover p ∈ K; rw [hp]; exact hsK, rfl⟩, rfl⟩
    have hAm : ∀ j₀, (A.baseEP.epFormsInftyEval (m + 1)).sheetNull.IsMeasIn (C.M j₀)
        (A.X.π ⁻¹' (Subtype.val '' K) ∩ C.M j₀) := fun j₀ =>
      SheetNullSets.isMeasIn_inter_iff.2 (SheetNullSets.isMeasIn_of_borel hA₀)
    have hε' : (ε = 1 ∧ ∀ j, ∀ y ∈ A.X.π ⁻¹' (Subtype.val '' K) ∩ C.M (e j),
          (C'.boundaryOrient j.1).tangent ((cubeFaceIncl A q).obj y) =
            (faceOrient q (C.orient (e j)) (hS (e j)).1.1).tangent
              ((cubeFaceIncl A q).obj y)) ∨
        (ε = -1 ∧ ∀ j, ∀ y ∈ A.X.π ⁻¹' (Subtype.val '' K) ∩ C.M (e j),
          (C'.boundaryOrient j.1).tangent ((cubeFaceIncl A q).obj y) ≠
            (faceOrient q (C.orient (e j)) (hS (e j)).1.1).tangent
              ((cubeFaceIncl A q).obj y)) :=
      hε.imp (fun h => ⟨h.1, fun j y hy => h.2 j y hy.2⟩)
        (fun h => ⟨h.1, fun j y hy => h.2 j y hy.2⟩)
    have key := sheetSum_boundaryFamily_cubeFace q C C' hΘ' hCT' hS e he hrange hσ hM hA hAm
      hε' ω
    have hcard : Nat.card ((A.cubeSEP 1).X.EffIsotropy ((q, x) : (A.cubeSEP 1).Obj)) =
        Nat.card (A.X.EffIsotropy x) := A.X.card_effIsotropy_cubeProd 1 (q, x)
    rw [key, hcard]
    change _ = ε * ((Nat.card (A.X.EffIsotropy x) : ℝ)⁻¹ * _)
    ring


set_option maxHeartbeats 1600000 in
-- the cylinder's ep-groupoid is unfolded in several places
/-- **Matched oriented structures at the points of `supp Θᵢ`, for the canonical orientations**
(proof of Corollary 15.4.4, p. 703).  Let `d_X ≡ 0`, `f` sc-Fredholm with tame germ data, `P`
an oriented solution set of `f`, `Λ̃` an sc⁺-multisection on `[0, 1] × X` with
`Λ̃ = Λⁱ` over `t = i`, `Λ̃ = Λ_P` over the end `i ∈ {0, 1}`, the face condition of Theorem
15.3.9 for the glued data, and `ε = (−1)^{i+1}`.  Let the orientation of `P` be given by the
formula of Theorem 15.4.1 for `(f, o)`, and `T̃` by that formula for `(f̃, õ)`, in every local
structure described by kernels, and let the frame convention of the canonical orientations hold
on the end `i`.  Then every `x ∈ supp Θ` has oriented tame structures `C` of `Θ` at `x`, with
sheets in the class of the integration and describing `T_P`, and `C̃` of `Θ̃` at `(i, x)`
describing `T̃`, matched with sign `ε`. -/
theorem exists_areMatchedAt_of_kernelCanonical (hd : ∀ x, A.X.PObj.degIndex x = 0)
    {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) {m : ℕ} (P : OrientedSolution A f m)
    {Λ' : (A.cubeSEP 1).W → ℚ≥0} {Λ₀ Λ₁ : A.W → ℚ≥0}
    (hΛ' : IsScPlusMultisection (A.cubeSEP 1) Λ')
    (h0 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (cubeVal w).2)
    (h1 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (cubeVal w).2)
    (honto : IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue Λ₀ Λ₁))
    {i : unitInterval} {ε : ℝ} (hi : ((i : ℝ) = 0 ∧ ε = -1) ∨ ((i : ℝ) = 1 ∧ ε = 1))
    (hΛi : ∀ w, ((cubeVal w).1.1 0 : ℝ) = i → Λ' w = P.Λ (cubeVal w).2)
    {T' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).X.PObj.OrTangent →₀ ℚ}
    (hΘ' : (A.cubeSEP 1).X.IsBranchedEpSubgroupoid
      (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)))
    {hsec : A.B.HasScPlusSectionsThrough}
    {o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy}
    {hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough}
    {o' : ∀ z (hz : z ∈ (A.cubeSEP 1).X.PObj.smoothSet),
      Orx (cubeLiftEp (n := 1) f hf.1.1.1)
        (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 z hz}
    (hP : IsKernelCanonical P.Λ hf.2 hsec o P.T)
    (hT' : IsKernelCanonical Λ' (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2
      hsec' o' T')
    (hconv : CylinderKernelFrameConvention hf.2 hsec o
      (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 hsec' o' (fun _ => i)) :
    ∀ x ∈ EpGroupoid.supp (fun z => (P.Λ (f z) : ℚ)),
      ∃ (C : A.X.OrientedTameStructure (m + 1) (fun z => (P.Λ (f z) : ℚ)) x)
        (C' : (A.cubeSEP 1).X.OrientedTameStructure (m + 1 + 1)
          (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) ((fun _ => i), x))
        (hCT' : C'.Represents T') (hS : ∀ j, C.M j ∈ (A.baseEP.epFormsInftyEval (m + 1)).sheets),
        C.Represents P.T ∧ AreMatchedAt (fun _ => i) C C' hΘ' hCT' hS ε := by
  classical
  intro x hx
  have hpos : 0 < P.Λ (f x) := by
    have h : (0 : ℚ) < (P.Λ (f x) : ℚ) := hx
    exact_mod_cast h
  have hi' : (i : ℝ) = 0 ∨ (i : ℝ) = 1 := hi.imp (fun h => h.1) (fun h => h.1)
  -- the class of sheets: in dimension `m + 1`, the class of the integration
  let S : ℕ → Set (Set A.Obj) := fun d =>
    {N | d = m + 1 → N ∈ (A.baseEP.epFormsInftyEval (m + 1)).sheets}
  have hS₁ : ∀ d N, A.X.PObj.IsSubmanifoldOfDim N d → x ∈ N →
      ∃ V : Set A.Obj, IsOpen V ∧ x ∈ V ∧ N ∩ V ∈ S d := fun d N hN hxN => by
    by_cases hdm : d = m + 1
    · subst hdm
      obtain ⟨V, hV, hxV, hNV⟩ :=
        EpGroupoid.FormEval.exists_mem_sheets (F := A.baseEP.epFormsInftyEval (m + 1)) hN hxN
      exact ⟨V, hV, hxV, fun _ => hNV⟩
    · exact ⟨univ, isOpen_univ, mem_univ _, fun h => absurd h hdm⟩
  have hS₂ : ∀ d N V, N ∈ S d → IsOpen V → N ∩ V ∈ S d := fun d N V hN hV hdm =>
    EpGroupoid.FormEval.inter_mem_sheets (hN hdm) hV
  obtain ⟨K', K, e, hσ, hU, -, hM, hstr, hKd, hKs, hcls⟩ :=
    exists_matched_kernel_branching_of_class hd hf hft hΛ' h0 h1 honto hi' hΛi hpos S hS₁ hS₂
  obtain ⟨C₀, hC₀⟩ := P.loc x hx
  have hn : ∀ j, K.dim j = m + 1 := fun j => by
    have hxs : x ∈ A.X.PObj.smoothSet := K.smooth j x (K.mem_M j)
    exact K.dim_eq_of_represents hf.2 hsec o (hP.2 x K x K.mem_U hxs) C₀ hC₀ hxs j
  have hn' : ∀ j, K'.dim j = m + 1 + 1 := fun j => by rw [hKd j, hn]
  have hc := hP.1 x K
  have hc' := hT'.1 _ K'
  have hCT' : (K'.toOrientedTame hc' hn').Represents T' :=
    K'.represents_toOrientedTame hc' hn' (hT'.2 _ K')
  have hCT : (K.toOrientedTame hc hn).Represents P.T :=
    K.represents_toOrientedTame hc hn (hP.2 x K)
  have hSh : ∀ j, (K.toOrientedTame hc hn).M j ∈
      (A.baseEP.epFormsInftyEval (m + 1)).sheets := fun j => by
    obtain ⟨j', rfl⟩ := e.surjective j
    exact hcls j' (hn (e j'))
  refine ⟨K.toOrientedTame hc hn, K'.toOrientedTame hc' hn', hCT', hSh, hCT, ?_⟩
  exact areMatchedAt_of_equiv_timeFirst _ _ hΘ' hCT' hSh
    (hi.imp (fun h => ⟨h.1, h.2⟩) (fun h => ⟨h.1, h.2⟩)) e hσ hstr
    (fun y hy => (hU y).1 hy)
    (K.hasTimeFirstFrames_of_convention hconv K' hc hc' hn hn' (fun j => j) e hKs
      fun j y hy => by
        have h := hy
        rw [hM j] at h
        exact h)


end Adm

end SBLocalization

end Polyfold
