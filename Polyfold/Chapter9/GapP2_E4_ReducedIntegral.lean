import Polyfold.Chapter9.GapP2_E4_ReducedRep

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, Chapter 9, §9.5,
**Proposition 9.5.13 (2)**, p. 446 (new in the 2021 edition), at the level of the integrals.

# The effective branched integral on `X` is the branched integral on `X_R`

## The text, paraphrased

(Proposition 9.5.13 (2)) If `X` has the local unique continuation property, then
`∮_Θ̂ ω = ∫_Θ̂' ω'`, where `(Θ̂', ω')` is the data on the reduced ep-groupoid `X_R` induced from
`(Θ̂, ω)`.  (Proof, pp. 447–448) `X` and `X_R` have the same object M-polyfold and `Θ' = Θ`; the
same local branching structures serve for `Θ̂'`, and `♯G_x^eff = ♯G'_x`; hence
`μ^eff_{Θ̂, ω}(K) = μ_{Θ̂', ω'}(K)` for measurable `K`, and the identity follows with `K = S`.

## What is formalized (namespace `Polyfold.EpGroupoid`)

For a `SheetIntegration` `𝓘` on `X` (the integrals of the forms over the oriented sheets of a
class `S`, `GapP2_E1_SheetIntegration.lean`) and its copy `𝓘.toReduced` on `X_R`:

* `orbitHomeomorphReduced` (`|X| ≅ |X_R|`, `|x| ↦ |x|`), `orbitSuppHomeomorphReduced`
  (`|supp Θ|` in `|X|` and in `|X_R|`), `preimage_π_image_val_reduced` (the preimages in `X` agree);
* the induced data: `IsBranchedEpSubgroupoid.toReduced`, `IsCompactBranched.toReduced`,
  `IsOrientation.toReduced` (`GapP2_E4_ReducedRep.lean`), `hcov_reduced` (the oriented tame
  structures with the property of Definition 7.2.18 serve on `X_R`);
* `measurableSet_image_orbitSuppHomeomorphReduced`: `L(S)` on `|X|` goes to `L(S)` on `|X_R|`;
* **`proposition_9_5_13_2_measure`**: `μ^eff_{Θ̂, ω}(K) = μ_{Θ̂', ω'}(K)` for `K ∈ L(S)`;
* **`proposition_9_5_13_2`**: `∮_Θ̂ ω = ∫_Θ̂' ω'` (under LUC, which makes `T_R` Hausdorff,
  `t2Space_reducedMor_of_isLUC`, so that `X_R` is defined).

## Reading

* "The data on `X_R` induced from `(Θ̂, ω)`" is read as: `Θ' = Θ`, the same oriented lift
  `T̂Θ' = T̂Θ` (an orientation on `X_R` by `IsOrientation.toReduced`), and the same integrals of `ω`
  over the oriented sheets (`SheetIntegration.toReduced`); a form `ω` of `X` is one of `X_R`
  because the tangent maps of the morphisms `[φ]` of `X_R` are those of `φ` (`tangentMor_reducedπ`).
* The measures live on `|supp Θ|` in `|X|` and in `|X_R|`; these are different quotients of the
  same object space, identified by `orbitSuppHomeomorphReduced`, and the measure identity is read
  through it.
* LUC enters as in the text: through `T_x = ker Φ` for the natural representations
  (`NaturalRep.toReduced`), and it makes `X_R` an ep-groupoid.  No hypothesis is added: the
  hypotheses of `proposition_9_5_13_2` are those of Theorem 9.5.5 (`theorem_9_5_5`) and LUC.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

section Orbit

variable [T2Space X.ReducedMor]

/-- `|X| → |X_R|`, `|x| ↦ |x|`. -/
def orbitReduced : X.OrbitSpace → X.reducedEpGroupoid.OrbitSpace :=
  Quotient.lift X.reducedEpGroupoid.π fun _ _ h => by
    obtain ⟨φ, hs, ht⟩ := h
    exact X.reducedEpGroupoid.π_eq_π_iff.2 ⟨X.reducedπ φ, hs, ht⟩

/-- `|X_R| → |X|`, `|x| ↦ |x|`. -/
def orbitUnreduced : X.reducedEpGroupoid.OrbitSpace → X.OrbitSpace :=
  Quotient.lift X.π fun _ _ h => by
    obtain ⟨q, hs, ht⟩ := h
    obtain ⟨φ, rfl⟩ := X.surjective_reducedπ q
    exact X.π_eq_π_iff.2 ⟨φ, hs, ht⟩

theorem orbitReduced_π (y : Obj) : orbitReduced (X.π y) = X.reducedEpGroupoid.π y := rfl

theorem orbitUnreduced_π (y : Obj) : orbitUnreduced (X.reducedEpGroupoid.π y) = X.π y := rfl

theorem orbitUnreduced_orbitReduced (q : X.OrbitSpace) : orbitUnreduced (orbitReduced q) = q := by
  obtain ⟨y, rfl⟩ := X.surjective_π q
  rfl

theorem orbitReduced_orbitUnreduced (q : X.reducedEpGroupoid.OrbitSpace) :
    orbitReduced (orbitUnreduced q) = q := by
  obtain ⟨y, rfl⟩ := X.reducedEpGroupoid.surjective_π q
  rfl

variable (X) in
/-- **`|X| ≅ |X_R|`**: `X` and `X_R` have the same objects, and `x, y` are isomorphic in `X_R` iff
they are in `X`. -/
def orbitHomeomorphReduced : X.OrbitSpace ≃ₜ X.reducedEpGroupoid.OrbitSpace where
  toFun := orbitReduced
  invFun := orbitUnreduced
  left_inv := orbitUnreduced_orbitReduced
  right_inv := orbitReduced_orbitUnreduced
  continuous_toFun := X.reducedEpGroupoid.continuous_π.quotient_lift _
  continuous_invFun := X.continuous_π.quotient_lift _

variable {Θ : Obj → ℚ}

theorem orbitSupp_eq_preimage_reduced (Θ : Obj → ℚ) :
    X.orbitSupp Θ = X.orbitHomeomorphReduced ⁻¹' X.reducedEpGroupoid.orbitSupp Θ := by
  ext q
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, hq⟩
    refine ⟨y, hy, ?_⟩
    have h := congrArg orbitUnreduced hq
    rw [orbitUnreduced_π] at h
    rw [h]
    exact orbitUnreduced_orbitReduced q

variable (X) in
/-- `|supp Θ|` in `|X|` and in `|X_R|`. -/
def orbitSuppHomeomorphReduced (Θ : Obj → ℚ) :
    X.orbitSupp Θ ≃ₜ X.reducedEpGroupoid.orbitSupp Θ :=
  X.orbitHomeomorphReduced.sets (orbitSupp_eq_preimage_reduced Θ)

theorem coe_orbitSuppHomeomorphReduced (p : X.orbitSupp Θ) :
    ((X.orbitSuppHomeomorphReduced Θ p : X.reducedEpGroupoid.orbitSupp Θ) :
      X.reducedEpGroupoid.OrbitSpace) = orbitReduced (p : X.OrbitSpace) := rfl

theorem orbitSupp_reduced_eq_image (Θ : Obj → ℚ) :
    X.reducedEpGroupoid.orbitSupp Θ = X.orbitHomeomorphReduced '' X.orbitSupp Θ := by
  rw [orbitSupp_eq_preimage_reduced (X := X) Θ, Homeomorph.image_preimage]

/-- **The preimages in the objects agree**: `π_R⁻¹(|K|) = π⁻¹(|K|)` for `K ⊆ |supp Θ|`. -/
theorem preimage_π_image_val_reduced (K : Set (X.orbitSupp Θ)) :
    X.reducedEpGroupoid.π ⁻¹' (Subtype.val '' (X.orbitSuppHomeomorphReduced Θ '' K)) =
      X.π ⁻¹' (Subtype.val '' K) := by
  ext y
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, hq⟩
    refine ⟨p, hp, ?_⟩
    have h := congrArg orbitUnreduced hq
    rwa [coe_orbitSuppHomeomorphReduced, orbitUnreduced_orbitReduced, orbitUnreduced_π] at h
  · rintro ⟨p, hp, hq⟩
    refine ⟨_, ⟨p, hp, rfl⟩, ?_⟩
    rw [coe_orbitSuppHomeomorphReduced, hq]
    rfl

/-- **`Θ` is a branched ep⁺-subgroupoid of `X_R`** (2021 p. 447). -/
theorem IsBranchedEpSubgroupoid.toReduced (h : X.IsBranchedEpSubgroupoid Θ) :
    X.reducedEpGroupoid.IsBranchedEpSubgroupoid Θ :=
  h.toReduced_of_paracompact
    ((X.orbitSuppHomeomorphReduced Θ).paracompactSpace_iff.1 h.paracompactSpace_orbitSupp)

/-- `|supp Θ| ⊆ |X_R|` is compact if `|supp Θ| ⊆ |X|` is. -/
theorem IsCompactBranched.toReduced (h : X.IsCompactBranched Θ) :
    X.reducedEpGroupoid.IsCompactBranched Θ := by
  change IsCompact (X.reducedEpGroupoid.orbitSupp Θ)
  rw [orbitSupp_reduced_eq_image Θ]
  exact h.image X.orbitHomeomorphReduced.continuous

end Orbit

/-! ### The σ-algebras and the measures -/

section Measures

variable [T2Space X.ReducedMor] {S : Set (Set Obj)} {G : SheetNullSets S} {Ω : Type*}
  [AddCommGroup Ω] [Module ℝ Ω] {n : ℕ} {Θ : Obj → ℚ}

/-- **`L(S)` on `|X|` goes to `L(S)` on `|X_R|`** (Definition 9.5.3): Borel sets go to Borel sets
under the homeomorphism, and a set of measure zero (Definition 9.5.1) goes to one, since the tame
local branching structures of `X` serve on `X_R` (under LUC every natural representation has the
property of Definition 7.2.18, `isLUC_iff_forall_naturalRep`) and the preimages in the objects
agree. -/
theorem measurableSet_image_orbitSuppHomeomorphReduced (hL : X.IsLUC) {K : Set (X.orbitSupp Θ)}
    (hK : MeasurableSet[X.lebesgueSigma G Θ] K) :
    MeasurableSet[X.reducedEpGroupoid.lebesgueSigma G Θ] (X.orbitSuppHomeomorphReduced Θ '' K) := by
  have hm : @Measurable _ _ (X.reducedEpGroupoid.lebesgueSigma G Θ) (X.lebesgueSigma G Θ)
      (X.orbitSuppHomeomorphReduced Θ).symm := by
    refine @measurable_generateFrom _ _ (X.reducedEpGroupoid.lebesgueSigma G Θ) _ _
      fun t ht => ?_
    rcases ht with ht | ht
    · exact borel_le_borelNullSigma _ _
        ((X.orbitSuppHomeomorphReduced Θ).symm.continuous.borel_measurable ht)
    · refine measurableSet_borelNullSigma_of_mem ?_
      change X.reducedEpGroupoid.IsMeasureZeroSupp G Θ
        (Subtype.val '' ((X.orbitSuppHomeomorphReduced Θ).symm ⁻¹' t))
      rw [Homeomorph.preimage_symm]
      intro y hy
      obtain ⟨B, hBS, hBn⟩ := ht y hy
      refine ⟨B.toReduced (X.isLUC_iff_forall_naturalRep.1 hL y B.rep), hBS, fun i => ?_⟩
      change G.IsNull (B.M i)
        (B.M i ∩ X.reducedEpGroupoid.π ⁻¹' (Subtype.val '' (X.orbitSuppHomeomorphReduced Θ '' t)))
      rw [preimage_π_image_val_reduced]
      exact hBn i
  have h := hm hK
  rwa [Homeomorph.preimage_symm] at h

/-- **The oriented tame structures of Theorem 9.5.5 on `X` serve on `X_R`** (2021 p. 447, "we can
take the same local branching structure for `Θ̂'`"): the hypothesis of Theorem 9.5.4 on `X_R`. -/
theorem hcov_reduced {T : Obj → X.PObj.OrTangent →₀ ℚ}
    (hcovL : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ S) ∧ C.Represents T ∧ C.rep.HasLUC) :
    ∀ x ∈ supp Θ, ∃ C : X.reducedEpGroupoid.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ S) ∧ C.Represents T := fun x hx => by
  obtain ⟨C, hS, hT, hL⟩ := hcovL x hx
  exact ⟨C.toReduced hL, hS, hT⟩

variable (𝓘 : X.SheetIntegration G Ω)

/-- **Proposition 9.5.13 (2), the measures (2021 pp. 446–448, new in the 2021 edition)**: under
LUC, the effective measure of Theorem 9.5.5 on `X` is the measure of Theorem 9.5.4 on `X_R` for
the induced data: `μ^eff_{Θ̂, ω}(K) = μ_{Θ̂', ω'}(K)` for every `K ∈ L(S)` (read on `|X_R|` through
`orbitSuppHomeomorphReduced`).  Proof as in the text: the pushed measure satisfies the local
formula of Theorem 9.5.5 (same structures, same integrals, `♯G'_x = ♯G_x^eff`), and the measure of
Theorem 9.5.5 is unique. -/
theorem proposition_9_5_13_2_measure (hL : X.IsLUC) (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) {T : Obj → X.PObj.OrTangent →₀ ℚ} (hT : X.IsOrientation Θ T)
    (hcovL : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ S) ∧ C.Represents T ∧ C.rep.HasLUC)
    (ω : Ω) {K : Set (X.orbitSupp Θ)} (hK : MeasurableSet[X.lebesgueSigma G Θ] K) :
    branchedMeasureEff 𝓘 hΘ hcpt hT hcovL ω K =
      branchedMeasure 𝓘.toReduced hΘ.toReduced hcpt.toReduced hT.toReduced (hcov_reduced hcovL)
        ω (X.orbitSuppHomeomorphReduced Θ '' K) := by
  let _ : MeasurableSpace (X.orbitSupp Θ) := X.lebesgueSigma G Θ
  let _ : MeasurableSpace (X.reducedEpGroupoid.orbitSupp Θ) :=
    X.reducedEpGroupoid.lebesgueSigma G Θ
  set e := X.orbitSuppHomeomorphReduced Θ with he
  set μR := branchedMeasure 𝓘.toReduced hΘ.toReduced hcpt.toReduced hT.toReduced
    (hcov_reduced hcovL) with hμR
  have hm : Measurable e.symm := fun t ht => by
    rw [Homeomorph.preimage_symm]
    exact measurableSet_image_orbitSuppHomeomorphReduced hL ht
  let Ψ : Ω →ₗ[ℝ] SignedMeasure (X.orbitSupp Θ) := (VectorMeasure.mapₗ e.symm).comp μR
  have hΨ : ∀ ω' K', MeasurableSet K' → Ψ ω' K' = μR ω' (e '' K') := fun ω' K' hK' => by
    change (μR ω').map e.symm K' = _
    rw [VectorMeasure.map_apply _ hm hK', Homeomorph.preimage_symm]
  have heq : branchedMeasureEff 𝓘 hΘ hcpt hT hcovL = Ψ := by
    refine (theorem_9_5_5 𝓘 hΘ hcpt hT hcovL).unique
      (fun ω' x C hC K' hK' hKU => branchedMeasureEff_apply 𝓘 hΘ hcpt hT hcovL ω' C hC.1 hC.2.1
        hC.2.2 hK' hKU) (fun ω' x C hC K' hK' hKU => ?_)
    have hK'R : MeasurableSet (e '' K') := measurableSet_image_orbitSuppHomeomorphReduced hL hK'
    have hKUR : Subtype.val '' (e '' K') ⊆ X.reducedEpGroupoid.π '' (C.toReduced hC.2.2).U := by
      rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      obtain ⟨y, hyU, hy⟩ := hKU ⟨p, hp, rfl⟩
      refine ⟨y, hyU, ?_⟩
      rw [coe_orbitSuppHomeomorphReduced, ← hy]
      rfl
    rw [hΨ ω' K' hK', hμR, branchedMeasure_apply 𝓘.toReduced hΘ.toReduced hcpt.toReduced
      hT.toReduced (hcov_reduced hcovL) ω' (C.toReduced hC.2.2) hC.1 hC.2.1 hK'R hKUR,
      OrientedTameStructure.localMeasure, OrientedTameStructure.localMeasureEff,
      card_isotropy_reduced_eq_card_effIsotropy, preimage_π_image_val_reduced]
    rfl
  rw [heq, hΨ ω K hK]

/-- **Proposition 9.5.13 (2) for the integrals, under `T_R` Hausdorff** (equivalent to LUC,
`theorem_7_2_22`): `∮_Θ̂ ω = ∫_Θ̂' ω'`. -/
theorem proposition_9_5_13_2_of_t2Space (hL : X.IsLUC) (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) {T : Obj → X.PObj.OrTangent →₀ ℚ} (hT : X.IsOrientation Θ T)
    (hcovL : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ S) ∧ C.Represents T ∧ C.rep.HasLUC) (ω : Ω) :
    branchedIntegralEff 𝓘 hΘ hcpt hT hcovL ω =
      branchedIntegral 𝓘.toReduced hΘ.toReduced hcpt.toReduced hT.toReduced
        (hcov_reduced hcovL) ω := by
  change branchedMeasureEff 𝓘 hΘ hcpt hT hcovL ω univ =
    branchedMeasure 𝓘.toReduced hΘ.toReduced hcpt.toReduced hT.toReduced (hcov_reduced hcovL) ω
      univ
  rw [proposition_9_5_13_2_measure 𝓘 hL hΘ hcpt hT hcovL ω MeasurableSet.univ, image_univ,
    (X.orbitSuppHomeomorphReduced Θ).range_coe]

end Measures

variable {S : Set (Set Obj)} {G : SheetNullSets S} {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω]
  {n : ℕ} {Θ : Obj → ℚ}

/-- **Proposition 9.5.13 (2), 2021 p. 446 (new in the 2021 edition)**: if `X` has the local unique
continuation property (so that `T_R` is Hausdorff and the reduced ep-groupoid `X_R` is defined,
`t2Space_reducedMor_of_isLUC`), then for an oriented, tame, compact branched ep⁺-subgroupoid
`Θ̂ = (Θ, T̂Θ)` of dimension `n` as in Theorem 9.5.5 and every form `ω`,
`∮_Θ̂ ω = ∫_Θ̂' ω'`, where `(Θ̂', ω')` is the data on `X_R` induced from `(Θ̂, ω)`: `Θ' = Θ`,
the same orientation, and the same integrals over the oriented sheets
(`SheetIntegration.toReduced`).  Proved for every `SheetIntegration` (the integrals of forms
over the sheets, gap G.107). -/
theorem proposition_9_5_13_2 (𝓘 : X.SheetIntegration G Ω) (hL : X.IsLUC)
    (hΘ : X.IsBranchedEpSubgroupoid Θ) (hcpt : X.IsCompactBranched Θ)
    {T : Obj → X.PObj.OrTangent →₀ ℚ} (hT : X.IsOrientation Θ T)
    (hcovL : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ S) ∧ C.Represents T ∧ C.rep.HasLUC) (ω : Ω) :
    letI := X.t2Space_reducedMor_of_isLUC hL
    branchedIntegralEff 𝓘 hΘ hcpt hT hcovL ω =
      branchedIntegral 𝓘.toReduced hΘ.toReduced hcpt.toReduced hT.toReduced
        (hcov_reduced hcovL) ω :=
  letI := X.t2Space_reducedMor_of_isLUC hL
  proposition_9_5_13_2_of_t2Space 𝓘 hL hΘ hcpt hT hcovL ω

end EpGroupoid

end Polyfold
