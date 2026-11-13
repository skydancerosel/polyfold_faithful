import Polyfold.Chapter9.StokesDimOne

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, **Theorems 9.5.16 and 9.5.18 for `n = 1`** (pp. 449–450; 2017:
Theorems 9.5, 9.7), gaps G.109, G.110.  Numbers and pages are the 2021 text's.

# The effective theorems for `n = 1` with the text's hypothesis "X has LUC"

`theorem_9_5_16_dim1` and `theorem_9_5_18_dim1` ask for structures whose `U(x)` has the local
unique continuation property.  The text assumes instead that `X` has it (Definition 7.2.18);
then every structure has it (`isLUC_iff_forall_naturalRep`), so the local formula holds for every
structure whose nonempty boundary sheets are points, without a premise on the structure.

* **`EP.theorem_9_5_16_dim1_isLUC`**, **`EP.theorem_9_5_18_dim1_isLUC`**.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace EP

open EpGroupoid

variable (A : EP.{u}) {Θ : A.Obj → ℚ} {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ}

/-- `hloc` together with the local unique continuation property of `U(x)`, when `X` has it. -/
theorem hloc_hasLUC_dim1 (hLUC : A.X.IsLUC)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (0 + 1) Θ x, C.Represents T) :
    ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (0 + 1) Θ x, C.Represents T ∧ C.rep.HasLUC :=
  fun x hx => (hloc x hx).imp fun C h => ⟨h, A.X.isLUC_iff_forall_naturalRep.1 hLUC x C.rep⟩

/-- **Theorem 9.5.16, 2021 p. 449 (2017: Theorem 9.5), for `n = 1`**, with the text's hypothesis
that `X` has the local unique continuation property: `Θ̂` oriented, tame, compact and
`1`-dimensional.  There is exactly one linear map `ω ↦ μ_ω^{∂,eff}` from `Ω⁰_{ep,∞}(X)` to the
signed measures on `(∂S, L(∂S))` with `μ_ω^{∂,eff}(K) = (1/♯G_x^eff) ∑ σᵢ ∫_{Kᵢ} ω|(∂₁Mᵢ, o_{∂Mᵢ})`
for every oriented tame structure at `x ∈ supp(∂Θ)` describing `T̂Θ` whose nonempty boundary
sheets are points, and every measurable `K ⊆ ∂S` in `|U(x)|`. -/
theorem theorem_9_5_16_dim1_isLUC (hLUC : A.X.IsLUC) (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (0 + 1) Θ x, C.Represents T) :
    ∃! Φ : A.epFormsInfty 0 →ₗ[ℝ] @SignedMeasure (A.X.orbitSupp (A.X.boundaryTheta Θ))
        (A.X.lebesgueSigmaBoundaryH (0 + 1) Θ),
      ∀ (ω : A.epFormsInfty 0) (x : A.Obj) (C : A.X.OrientedTameStructure (0 + 1) Θ x)
        (hCT : C.Represents T), x ∈ supp (A.X.boundaryTheta Θ) →
        (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ pointSheets A.X) →
        ∀ K : Set (A.X.orbitSupp (A.X.boundaryTheta Θ)),
          MeasurableSet[A.X.lebesgueSigmaBoundaryH (0 + 1) Θ] K →
          Subtype.val '' K ⊆ A.X.π '' C.U →
          Φ ω K = (Nat.card (A.X.EffIsotropy x) : ℝ)⁻¹ *
            (C.boundaryFamily hΘ hCT).nonemptyPart.sheetSum A.zeroFormIntegration ω
              (A.X.π ⁻¹' (Subtype.val '' K)) := by
  obtain ⟨Φ, hΦ, huniq⟩ :=
    A.theorem_9_5_16_dim1 hΘ hcpt hT (A.hloc_hasLUC_dim1 hLUC hloc)
  refine ⟨Φ, fun ω x C hCT hx hS K hK hKU =>
    hΦ ω x C hCT hx hS (A.X.isLUC_iff_forall_naturalRep.1 hLUC x C.rep) K hK hKU, ?_⟩
  exact fun Ψ hΨ => huniq Ψ fun ω x C hCT hx hS _ K hK hKU => hΨ ω x C hCT hx hS K hK hKU

/-- **Theorem 9.5.18 (effective Stokes), 2021 p. 450 (2017: Theorem 9.7), for `n = 1`**, with the
text's hypotheses: `X` with sc-smooth partitions of unity and the local unique continuation
property, `Θ̂` oriented, tame, compact and `1`-dimensional, `ω ∈ Ω⁰_{ep,∞}(X)`.  Then
`∮_Θ̂ dω = μ^{∂Θ̂,eff}_ω(∂S)` with the effective boundary measure of Theorem 9.5.16. -/
theorem theorem_9_5_18_dim1_isLUC (hPU : A.X.HasScPartitionsOfUnity) (hLUC : A.X.IsLUC)
    (hΘ : A.X.IsBranchedEpSubgroupoid Θ) (hcpt : A.X.IsCompactBranched Θ)
    (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (0 + 1) Θ x, C.Represents T)
    (ω : A.epFormsInfty 0) :
    (A.epFormsInftyEval (0 + 1)).tameBranchedIntegralEff (Nat.succ_pos 0) hΘ hcpt hT
        (A.hloc_hasLUC_dim1 hLUC hloc) (A.epFormsInftyD 0 ω) =
      A.boundaryBranchedMeasureEffDim1 hΘ hcpt hT (A.hloc_hasLUC_dim1 hLUC hloc) ω univ :=
  A.theorem_9_5_18_dim1 hPU hΘ hcpt hT (A.hloc_hasLUC_dim1 hLUC hloc) ω

end EP

end Polyfold
