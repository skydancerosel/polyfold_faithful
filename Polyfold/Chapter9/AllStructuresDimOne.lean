import Polyfold.Chapter9.FinitePointIntegration
import Polyfold.Chapter9.EffectiveDimOneLUC
import Polyfold.Chapter9.AllStructures

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, §9.5, **Theorems 9.5.15 and 9.5.16 for `n = 1`** (p. 449; 2017: Theorems 9.4, 9.5), gap
G.109, row V9.67.  Numbers and pages are the 2021 text's.

# The local formula for `n = 1` for every oriented tame structure

`theorem_9_5_15_dim1` gives the local formula for the structures whose nonempty boundary sheets
are single points.  Here it is proved for **every** oriented tame structure describing `T̂Θ`, as
the text states it.  The boundary sheet `∂₁Mᵢ` of an arbitrary structure is a finite set of
points, and `∫_{Kᵢ} ω|(∂₁Mᵢ, o)` is the signed sum over the points of `Kᵢ`
(`EP.finZeroFormIntegration`).

Finiteness (K1's covering argument of `AllStructures`, for `n = 1`): `∂₁Mᵢ` lies in a
compact subset `K` of `supp Θ`.  Cover `K` by finitely many structures whose boundary sheets have
at most one point (`exists_boundarySheet_subsingleton`).  At `z ∈ ∂₁Mᵢ` some sheet `M'_k ∋ z` of
such a structure has `T_zM'_k = T_zMᵢ` (`MPolyfold.k1_exists_tangent_eq`), so
`z ∈ ∂₁M'_k` (`MPolyfold.k1_mem_boundaryStratum_of_tangent_eq`).  So `∂₁Mᵢ` lies in finitely many
sets with at most one point.

* **`EP.boundarySheet_finite_of_loc`**, `EP.boundarySheet_mem_finPointSheets_of_loc`;
* **`EP.theorem_9_5_15_dim1_all`**, **`EP.theorem_9_5_16_dim1_all`**: Theorems 9.5.15 and 9.5.16
  for `n = 1` with the local formula for every oriented tame structure;
* **`EP.boundaryBranchedMeasureDim1_apply_all`**, `EP.boundaryBranchedMeasureEffDim1_apply_all`:
  the measures of `theorem_9_5_17_dim1` and `theorem_9_5_18_dim1` are these measures.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace EP

open EpGroupoid

variable (A : EP.{u}) {Θ : A.Obj → ℚ} {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ}

/-- **Every boundary sheet of every `1`-dimensional oriented tame structure is finite**, for `Θ`
compact, branched and tame (`hloc`). -/
theorem boundarySheet_finite_of_loc (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (0 + 1) Θ x, C.Represents T)
    {x : A.Obj} (C : A.X.OrientedTameStructure (0 + 1) Θ x) (i : C.ι) :
    (C.boundarySheet i).Finite := by
  classical
  have hnd := FormEval.isNDimensional_of_loc hloc
  obtain ⟨K, hK, hUK, hKs⟩ :=
    exists_isCompact_supp_inter hΘ.isFunctorial hcpt hnd C.hasPropernessProperty.2
  have hG : ∀ p : K, ∃ G : A.X.OrientedTameStructure (0 + 1) Θ p.1,
      G.Represents T ∧ ∀ k, (G.boundarySheet k).Subsingleton := fun p => by
    obtain ⟨C₀, hC₀⟩ := hloc p.1 (hKs p.2)
    obtain ⟨G, hGT, hs, -⟩ := C₀.exists_boundarySheet_subsingleton hC₀
    exact ⟨G, hGT, hs⟩
  choose G hGT hGs using hG
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun p : K => (G p).U) (fun p => (G p).isOpen_U)
    fun y hy => mem_iUnion.2 ⟨⟨y, hy⟩, (G _).mem_U⟩
  refine (t.finite_toSet.biUnion fun p _ => finite_iUnion fun k => (hGs p k).finite).subset ?_
  intro z hz
  have hzM : z ∈ C.M i := C.boundarySheet_subset i hz
  have hzK : z ∈ K := hUK ⟨C.toTameBranchingStructure.toLocalBranchingStructure.M_subset_supp i
    hzM, C.subset_U i hzM⟩
  obtain ⟨p, hpt, hzp⟩ := mem_iUnion₂.1 (ht hzK)
  obtain ⟨k, hzk, hT⟩ := MPolyfold.k1_exists_tangent_eq (C.isSubmanifoldOfDim i)
    (G p).isSubmanifoldOfDim (G p).isOpen_U
    (fun q hq => mem_iUnion.2
      (((G p).toTameBranchingStructure.toLocalBranchingStructure.mem_supp_iff hq.2).1
        (C.toTameBranchingStructure.toLocalBranchingStructure.M_subset_supp i hq.1)))
    (fun k w hw hwk =>
      (G p).toTameBranchingStructure.toLocalBranchingStructure.k1_exists_isOpen_disjoint k hw hwk)
    hzM hzp
  have hzb : z ∈ (G p).boundarySheet k :=
    MPolyfold.k1_mem_boundaryStratum_of_tangent_eq hz hzk hT
  exact mem_iUnion₂.2 ⟨p, Finset.mem_coe.2 hpt, mem_iUnion.2 ⟨k, hzb⟩⟩

/-- **Every boundary sheet of every `1`-dimensional oriented tame structure is a finite set of
smooth points** (the class of `EP.finZeroFormIntegration`). -/
theorem boundarySheet_mem_finPointSheets_of_loc (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (0 + 1) Θ x, C.Represents T)
    {x : A.Obj} (C : A.X.OrientedTameStructure (0 + 1) Θ x) (i : C.ι) :
    C.boundarySheet i ∈ finPointSheets A.X :=
  ⟨A.boundarySheet_finite_of_loc hΘ hcpt hloc C i, fun _ hp => hΘ.support_subset
    (C.toTameBranchingStructure.toLocalBranchingStructure.M_subset_supp i
      (C.boundarySheet_subset i hp))⟩

/-- **Theorem 9.5.15, 2021 p. 449 (2017: Theorem 9.4), for `n = 1`, as stated in the text**: `Θ̂`
oriented, tame, compact and `1`-dimensional.  There is exactly one linear map `ω ↦ μ_ω^∂` from
`Ω⁰_{ep,∞}(X)` to the signed measures on `(∂S, L(∂S))` with
`μ_ω^∂(K) = (1/♯G_x) ∑ σᵢ ∫_{Kᵢ} ω|(∂₁Mᵢ, o_{∂Mᵢ})` for **every** oriented tame structure at
`x ∈ supp(∂Θ)` describing `T̂Θ` and every measurable `K ⊆ ∂S` in `|U(x)|`; here `∂₁Mᵢ` is a finite
set of points and `∫_{Kᵢ} ω|(∂₁Mᵢ, o) = ∑_{p ∈ Kᵢ} ±ω(p)` (`finZeroFormIntegration`). -/
theorem theorem_9_5_15_dim1_all (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (0 + 1) Θ x, C.Represents T) :
    ∃! Φ : A.epFormsInfty 0 →ₗ[ℝ] @SignedMeasure (A.X.orbitSupp (A.X.boundaryTheta Θ))
        (A.X.lebesgueSigmaBoundaryH (0 + 1) Θ),
      ∀ (ω : A.epFormsInfty 0) (x : A.Obj) (C : A.X.OrientedTameStructure (0 + 1) Θ x)
        (hCT : C.Represents T), x ∈ supp (A.X.boundaryTheta Θ) →
        ∀ K : Set (A.X.orbitSupp (A.X.boundaryTheta Θ)),
          MeasurableSet[A.X.lebesgueSigmaBoundaryH (0 + 1) Θ] K →
          Subtype.val '' K ⊆ A.X.π '' C.U →
          Φ ω K = (Nat.card (A.X.Isotropy x) : ℝ)⁻¹ *
            (C.boundaryFamily hΘ hCT).nonemptyPart.sheetSum A.finZeroFormIntegration ω
              (A.X.π ⁻¹' (Subtype.val '' K)) := by
  have hmem := fun {x : A.Obj} (C : A.X.OrientedTameStructure (0 + 1) Θ x) (i : C.ι) =>
    A.boundarySheet_mem_finPointSheets_of_loc hΘ hcpt hloc C i
  obtain ⟨Φ, hΦ, huniq⟩ := theorem_9_5_15_hyp A.finZeroFormIntegration hΘ hcpt
    (FormEval.isNDimensional_of_loc hloc) hT (fun N B => finPoint_isNull_iff_isHNull_zero N B)
    (fun x hx => (hloc x (A.X.supp_boundaryTheta_subset Θ hx).2).imp fun C hC =>
      ⟨hC, fun i _ => hmem C i⟩)
  exact ⟨Φ, fun ω x C hCT hx => hΦ ω x C hCT hx fun i _ => hmem C i,
    fun Ψ hΨ => huniq Ψ fun ω x C hCT hx _ => hΨ ω x C hCT hx⟩

/-- **Theorem 9.5.16, 2021 p. 449 (2017: Theorem 9.5), for `n = 1`, as stated in the text**: `X`
with the local unique continuation property, `Θ̂` as in Theorem 9.5.15; the local formula with
`1/♯G_x^eff` for every oriented tame structure. -/
theorem theorem_9_5_16_dim1_all (hLUC : A.X.IsLUC) (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (0 + 1) Θ x, C.Represents T) :
    ∃! Φ : A.epFormsInfty 0 →ₗ[ℝ] @SignedMeasure (A.X.orbitSupp (A.X.boundaryTheta Θ))
        (A.X.lebesgueSigmaBoundaryH (0 + 1) Θ),
      ∀ (ω : A.epFormsInfty 0) (x : A.Obj) (C : A.X.OrientedTameStructure (0 + 1) Θ x)
        (hCT : C.Represents T), x ∈ supp (A.X.boundaryTheta Θ) →
        ∀ K : Set (A.X.orbitSupp (A.X.boundaryTheta Θ)),
          MeasurableSet[A.X.lebesgueSigmaBoundaryH (0 + 1) Θ] K →
          Subtype.val '' K ⊆ A.X.π '' C.U →
          Φ ω K = (Nat.card (A.X.EffIsotropy x) : ℝ)⁻¹ *
            (C.boundaryFamily hΘ hCT).nonemptyPart.sheetSum A.finZeroFormIntegration ω
              (A.X.π ⁻¹' (Subtype.val '' K)) := by
  have hmem := fun {x : A.Obj} (C : A.X.OrientedTameStructure (0 + 1) Θ x) (i : C.ι) =>
    A.boundarySheet_mem_finPointSheets_of_loc hΘ hcpt hloc C i
  have hL := fun {x : A.Obj} (C : A.X.OrientedTameStructure (0 + 1) Θ x) =>
    A.X.isLUC_iff_forall_naturalRep.1 hLUC x C.rep
  obtain ⟨Φ, hΦ, huniq⟩ := theorem_9_5_16_hyp A.finZeroFormIntegration hΘ hcpt
    (FormEval.isNDimensional_of_loc hloc) hT (fun N B => finPoint_isNull_iff_isHNull_zero N B)
    (fun x hx => (hloc x (A.X.supp_boundaryTheta_subset Θ hx).2).imp fun C hC =>
      ⟨hC, fun i _ => hmem C i, hL C⟩)
  exact ⟨Φ, fun ω x C hCT hx => hΦ ω x C hCT hx (fun i _ => hmem C i) (hL C),
    fun Ψ hΨ => huniq Ψ fun ω x C hCT hx _ _ => hΨ ω x C hCT hx⟩

/-- On a family of sheets with at most one point, the two integrations of `0`-forms give the
same sums. -/
theorem sheetSum_finZeroFormIntegration_eq {D : Set A.Obj} {m : ℕ} {x : A.Obj}
    (F : A.X.OrientedSheetFamily D m x) (hF : ∀ i, (F.N i).Subsingleton)
    (ω : A.epFormsInfty 0) (B : Set A.Obj) :
    F.sheetSum A.finZeroFormIntegration ω B = F.sheetSum A.zeroFormIntegration ω B :=
  Finset.sum_congr rfl fun i _ => by
    rw [A.finZeroFormIntegration_integ_eq ω (hF i)]

/-- **The boundary measure of `theorem_9_5_17_dim1` has the local formula for every oriented tame
structure** (with `∫_{Kᵢ} ω|(∂₁Mᵢ, o) = ∑_{p ∈ Kᵢ} ±ω(p)`). -/
theorem boundaryBranchedMeasureDim1_apply_all (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (0 + 1) Θ x, C.Represents T)
    (ω : A.epFormsInfty 0) (x : A.Obj) (C : A.X.OrientedTameStructure (0 + 1) Θ x)
    (hCT : C.Represents T) (hx : x ∈ supp (A.X.boundaryTheta Θ))
    (K : Set (A.X.orbitSupp (A.X.boundaryTheta Θ)))
    (hK : MeasurableSet[A.X.lebesgueSigmaBoundaryH (0 + 1) Θ] K)
    (hKU : Subtype.val '' K ⊆ A.X.π '' C.U) :
    A.boundaryBranchedMeasureDim1 hΘ hcpt hT hloc ω K = (Nat.card (A.X.Isotropy x) : ℝ)⁻¹ *
      (C.boundaryFamily hΘ hCT).nonemptyPart.sheetSum A.finZeroFormIntegration ω
        (A.X.π ⁻¹' (Subtype.val '' K)) := by
  obtain ⟨Φ, hΦ, -⟩ := A.theorem_9_5_15_dim1_all hΘ hcpt hT hloc
  have hEq : Φ = A.boundaryBranchedMeasureDim1 hΘ hcpt hT hloc :=
    (A.theorem_9_5_15_dim1 hΘ hcpt hT hloc).unique
      (fun ω x C hCT hx hS K hK hKU => by
        rw [hΦ ω x C hCT hx K hK hKU,
          A.sheetSum_finZeroFormIntegration_eq (C.boundaryFamily hΘ hCT).nonemptyPart
            (fun i => subsingleton_of_mem_pointSheets (hS i.1 i.2))])
      (A.theorem_9_5_15_dim1 hΘ hcpt hT hloc).exists.choose_spec
  rw [← hEq]
  exact hΦ ω x C hCT hx K hK hKU

/-- **The effective boundary measure of `theorem_9_5_18_dim1` has the local formula for every
oriented tame structure**, when `X` has the local unique continuation property. -/
theorem boundaryBranchedMeasureEffDim1_apply_all (hLUC : A.X.IsLUC)
    (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (0 + 1) Θ x, C.Represents T)
    (ω : A.epFormsInfty 0) (x : A.Obj) (C : A.X.OrientedTameStructure (0 + 1) Θ x)
    (hCT : C.Represents T) (hx : x ∈ supp (A.X.boundaryTheta Θ))
    (K : Set (A.X.orbitSupp (A.X.boundaryTheta Θ)))
    (hK : MeasurableSet[A.X.lebesgueSigmaBoundaryH (0 + 1) Θ] K)
    (hKU : Subtype.val '' K ⊆ A.X.π '' C.U) :
    A.boundaryBranchedMeasureEffDim1 hΘ hcpt hT (A.hloc_hasLUC_dim1 hLUC hloc) ω K =
      (Nat.card (A.X.EffIsotropy x) : ℝ)⁻¹ *
        (C.boundaryFamily hΘ hCT).nonemptyPart.sheetSum A.finZeroFormIntegration ω
          (A.X.π ⁻¹' (Subtype.val '' K)) := by
  obtain ⟨Φ, hΦ, -⟩ := A.theorem_9_5_16_dim1_all hLUC hΘ hcpt hT hloc
  have hEq : Φ = A.boundaryBranchedMeasureEffDim1 hΘ hcpt hT (A.hloc_hasLUC_dim1 hLUC hloc) :=
    (A.theorem_9_5_16_dim1 hΘ hcpt hT (A.hloc_hasLUC_dim1 hLUC hloc)).unique
      (fun ω x C hCT hx hS _ K hK hKU => by
        rw [hΦ ω x C hCT hx K hK hKU,
          A.sheetSum_finZeroFormIntegration_eq (C.boundaryFamily hΘ hCT).nonemptyPart
            (fun i => subsingleton_of_mem_pointSheets (hS i.1 i.2))])
      (A.theorem_9_5_16_dim1 hΘ hcpt hT (A.hloc_hasLUC_dim1 hLUC hloc)).exists.choose_spec
  rw [← hEq]
  exact hΦ ω x C hCT hx K hK hKU

end EP

end Polyfold
