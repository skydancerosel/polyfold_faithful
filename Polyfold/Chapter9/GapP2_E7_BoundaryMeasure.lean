import Polyfold.Chapter9.GapP2_E7_BoundaryFamily
import Polyfold.Chapter9.GapP2_E6_StratumRetraction
import Polyfold.Chapter9.GapP2_E5_BoundaryNullSigma
import Polyfold.Chapter9.GapP2_E2MeasureGlue
import Polyfold.Chapter9.GapP2_E4_MultiChartCompact
import Polyfold.Chapter9.GeneralCorollaries

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, **Theorems 9.5.15 and 9.5.16** (p. 449; 2017: Theorems 9.4, 9.5),
gap G.109.  Numbers and pages are the 2021 text's.

# The canonical boundary measures `μ_ω^∂` on `(∂S, L(∂S))`

For an oriented tame `Θ̂` of dimension `m + 1` and `∂S = |supp(∂Θ)|` with the σ-algebra
`L(∂S)` of Definition 9.5.14 (`lebesgueSigmaBoundaryH`), the forms `ω` give signed measures
characterized by `μ_ω^∂(K) = (1/♯G_x) ∑ σᵢ ∫_{Kᵢ} ω|(∂₁Mᵢ, o_{∂Mᵢ})`, `Kᵢ = ∂₁Mᵢ ∩ π⁻¹(K)`.

* `OrientedSheetFamily.nonemptyPart`: drop the empty sheets of a family (the same `orientedSum`).
* `OrientedTameStructure.boundarySheet_subset_submanifoldBoundary`,
  `boundarySheet_subset_supp_boundaryTheta`: `∂₁Mᵢ ⊆ ∂Mᵢ` and `∂₁Mᵢ ⊆ supp(∂Θ)`.
* **`OrientedTameStructure.isMeasIn_boundarySheet`**: for `K ∈ L(∂S)` the trace of `π⁻¹(K)` on
  `∂₁Mᵢ` is Borel modulo an `m`-dimensional null set (induction over the generators of
  `L(∂S)`; the null generators through `isHNull_boundary_of_isMeasureZeroBoundary`).
* **`theorem_9_5_15_hyp`, `theorem_9_5_16_hyp`**: for any sheet integration whose null sets are
  the `m`-dimensional null sets, with `hcov`: at every point of `supp(∂Θ)` an oriented tame
  structure describing `T̂Θ` whose nonempty boundary sheets lie in the class `S` of the
  integration.
* `theorem_9_5_15_msheets`, `theorem_9_5_16_msheets`: the instance `S = F.msheets` (E4's
  integration over countably many graph charts).
* `hcov_msheets_of_isCompact` (compact boundary sheets satisfy the class condition) and
  `hcov_zero` (the hypothesis for `Θ = 0`).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

open MPolyfold

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ} {T : Obj → X.PObj.OrTangent →₀ ℚ}

/-! ### Dropping the empty sheets of a family -/

namespace OrientedSheetFamily

open scoped Classical

variable {D : Set Obj} {m : ℕ} {x : Obj} (F : X.OrientedSheetFamily D m x)

/-- **The nonempty sheets of a family**: the same representation, the sheets `Nᵢ ≠ ∅`. -/
def nonemptyPart : X.OrientedSheetFamily D m x where
  rep := F.rep
  ι := {i : F.ι // (F.N i).Nonempty}
  N i := F.N i.1
  σ i := F.σ i.1
  orient i := F.orient i.1
  isSmoothSubmanifold i := F.isSmoothSubmanifold i.1
  iUnion_eq := by
    rw [← F.iUnion_eq]
    ext y
    simp only [mem_iUnion]
    exact ⟨fun ⟨i, hi⟩ => ⟨i.1, hi⟩, fun ⟨i, hi⟩ => ⟨⟨i, y, hi⟩, hi⟩⟩

theorem nonemptyPart_N (i : F.nonemptyPart.ι) : F.nonemptyPart.N i = F.N i.1 := rfl

theorem nonemptyPart_rep : F.nonemptyPart.rep = F.rep := rfl

theorem orientedSum_nonemptyPart (y : Obj) : F.nonemptyPart.orientedSum y = F.orientedSum y := by
  unfold orientedSum
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i => (F.N i).Nonempty)
    (fun i => if y ∈ F.N i then Finsupp.single ((F.orient i).tangent y) (F.σ i) else 0)]
  have h0 : ∑ i : {i // ¬ (F.N i).Nonempty},
      (if y ∈ F.N i.1 then Finsupp.single ((F.orient i.1).tangent y) (F.σ i.1) else 0) = 0 :=
    Finset.sum_eq_zero fun i _ => if_neg fun hy => i.2 ⟨y, hy⟩
  rw [h0, add_zero]
  rfl

theorem represents_nonemptyPart {T' : Obj → X.PObj.OrTangent →₀ ℚ} (h : F.Represents T') :
    F.nonemptyPart.Represents T' := fun y hy => by
  rw [orientedSum_nonemptyPart]; exact h y hy

end OrientedSheetFamily

/-! ### The boundary sheets lie in `∂Mᵢ` and in `supp(∂Θ)` -/

namespace OrientedTameStructure

variable {m : ℕ} {x : Obj} (C : X.OrientedTameStructure (m + 1) Θ x)

/-- `∂₁Mᵢ ⊆ ∂Mᵢ`. -/
theorem boundarySheet_subset_submanifoldBoundary (i : C.ι) :
    C.boundarySheet i ⊆ X.PObj.submanifoldBoundary (C.M i) := by
  intro y hy
  have h : y ∈ X.PObj.stratumOne (C.M i) := by
    rw [stratumOne_eq_boundaryStratum (C.isSubmanifoldOfDim i).1 (C.hasTameInducedStructure i)]
    exact hy
  exact stratumOne_subset_submanifoldBoundary _ h

/-- `∂₁Mᵢ ⊆ supp(∂Θ)`: `∂Θ(y) = ∑_{y ∈ ∂Mⱼ} σⱼ > 0`. -/
theorem boundarySheet_subset_supp_boundaryTheta (i : C.ι) :
    C.boundarySheet i ⊆ supp (X.boundaryTheta Θ) := by
  classical
  intro y hy
  have hyb := C.boundarySheet_subset_submanifoldBoundary i hy
  have hyM : y ∈ C.M i := C.boundarySheet_subset i hy
  change 0 < X.boundaryTheta Θ y
  rw [X.boundaryTheta_eq (hasIndependentTangentSums Θ) C.toLocalBranchingStructure
    (C.subset_U i hyM)]
  exact Finset.sum_pos' (fun j _ => (C.σ_pos j).le) ⟨i, by simp [hyb], C.σ_pos i⟩

theorem π_mem_orbitSupp_boundaryTheta {i : C.ι} {y : Obj} (hy : y ∈ C.boundarySheet i) :
    X.π y ∈ X.orbitSupp (X.boundaryTheta Θ) :=
  ⟨y, C.boundarySheet_subset_supp_boundaryTheta i hy, rfl⟩

/-! ### Measurability of the traces of `K ∈ L(∂S)` -/

/-- **The preimage of `K ∈ L(∂S)` is measurable in the boundary sheets** (Definition 9.5.14):
for a null-set system `G` whose null sets are those of `m`-dimensional measure zero, the trace of
`π⁻¹(K)` on `∂₁Mᵢ` is a Borel set modified by a null set.  By induction over the generators of
`L(∂S)`: a Borel `K = B₀ ∩ ∂S` has the Borel trace `π⁻¹(B₀) ∩ ∂₁Mᵢ`; for `K` of measure zero,
`∂Mᵢ ∩ π⁻¹(K)` is `m`-null for every tame structure at a point of `supp(∂Θ)`
(`isHNull_boundary_of_isMeasureZeroBoundary`), and `∂₁Mᵢ ⊆ ∂Mᵢ`. -/
theorem isMeasIn_boundarySheet {S : Set (Set Obj)} {G : SheetNullSets S}
    (hG : ∀ N A, G.IsNull N A ↔ X.PObj.IsHNull m (A ∩ N)) (hnd : X.IsNDimensional Θ (m + 1))
    (hx : x ∈ supp (X.boundaryTheta Θ)) (i : C.ι) {K : Set (X.orbitSupp (X.boundaryTheta Θ))}
    (hK : MeasurableSet[X.lebesgueSigmaBoundaryH (m + 1) Θ] K) :
    G.IsMeasIn (C.boundarySheet i) (X.π ⁻¹' (Subtype.val '' K)) := by
  set N := C.boundarySheet i with hN
  have hsupp : ∀ y ∈ N, X.π y ∈ X.orbitSupp (X.boundaryTheta Θ) :=
    fun y hy => C.π_mem_orbitSupp_boundaryTheta hy
  let M' : MeasurableSpace (X.orbitSupp (X.boundaryTheta Θ)) :=
    { MeasurableSet' := fun K => G.IsMeasIn N (X.π ⁻¹' (Subtype.val '' K))
      measurableSet_empty := by
        rw [image_empty, preimage_empty]
        exact @MeasurableSet.empty _ (G.sheetSigma N)
      measurableSet_compl := fun K hK => by
        rw [← SheetNullSets.isMeasIn_inter_iff]
        have e : X.π ⁻¹' (Subtype.val '' Kᶜ) ∩ N = (X.π ⁻¹' (Subtype.val '' K))ᶜ ∩ N := by
          ext y
          constructor
          · rintro ⟨⟨k, hk, hky⟩, hyN⟩
            refine ⟨fun ⟨k', hk', hk'y⟩ => hk ?_, hyN⟩
            have : k' = k := Subtype.ext (hk'y.trans hky.symm)
            exact this ▸ hk'
          · rintro ⟨hn, hyN⟩
            exact ⟨⟨⟨X.π y, hsupp y hyN⟩, fun hk => hn ⟨_, hk, rfl⟩, rfl⟩, hyN⟩
        rw [e, SheetNullSets.isMeasIn_inter_iff]
        exact @MeasurableSet.compl _ _ (G.sheetSigma N) hK
      measurableSet_iUnion := fun f hf => by
        rw [image_iUnion, preimage_iUnion]
        exact @MeasurableSet.iUnion _ _ (G.sheetSigma N) _ _ hf }
  have hle : X.lebesgueSigmaBoundaryH (m + 1) Θ ≤ M' := by
    refine MeasurableSpace.generateFrom_le ?_
    rintro K (hK | hK)
    · obtain ⟨B₀, hB₀, rfl⟩ : ∃ B₀, MeasurableSet[borel X.OrbitSpace] B₀ ∧
          Subtype.val ⁻¹' B₀ = K := by
        have h := hK
        rw [show borel (X.orbitSupp (X.boundaryTheta Θ)) =
          (borel X.OrbitSpace).comap Subtype.val from borel_comap] at h
        exact h
      change G.IsMeasIn N _
      rw [← SheetNullSets.isMeasIn_inter_iff]
      have e : X.π ⁻¹' (Subtype.val '' (Subtype.val ⁻¹' B₀ :
          Set (X.orbitSupp (X.boundaryTheta Θ)))) ∩ N = X.π ⁻¹' B₀ ∩ N := by
        ext y
        constructor
        · rintro ⟨⟨k, hkB, hky⟩, hyN⟩
          refine ⟨?_, hyN⟩
          change X.π y ∈ B₀
          rw [← hky]; exact hkB
        · rintro ⟨hyB, hyN⟩
          exact ⟨⟨⟨X.π y, hsupp y hyN⟩, hyB, rfl⟩, hyN⟩
      rw [e, SheetNullSets.isMeasIn_inter_iff]
      exact SheetNullSets.isMeasIn_of_borel (X.continuous_π.borel_measurable hB₀)
    · change G.IsMeasIn N _
      have h := isHNull_boundary_of_isMeasureZeroBoundary (hasIndependentTangentSums Θ) hnd hK hx
        C.toTameBranchingStructure i
      rw [Nat.add_sub_cancel] at h
      refine SheetNullSets.isMeasIn_of_isNull ((hG _ _).2 (h.mono ?_))
      rintro y ⟨⟨hyK, hyN⟩, -⟩
      exact ⟨C.boundarySheet_subset_submanifoldBoundary i hyN, hyK⟩
  exact hle K hK

end OrientedTameStructure

/-! ### Theorems 9.5.15 and 9.5.16 -/

section Measures

variable {S : Set (Set Obj)} {G : SheetNullSets S} {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω]
  (𝓘 : X.SheetIntegration G Ω) {m : ℕ}

/-- The class of boundary families: those of the oriented tame structures `C` at points of
`supp(∂Θ)` describing `T̂Θ` whose nonempty boundary sheets lie in `S`, with a condition `P` on
`C` (`P = True`, or the local unique continuation property). -/
def BoundaryGood (hΘ : X.IsBranchedEpSubgroupoid Θ) (S : Set (Set Obj))
    (P : ∀ x, X.OrientedTameStructure (m + 1) Θ x → Prop) (x : Obj)
    (F : X.OrientedSheetFamily (X.boundaryStratumSet Θ T) m x) : Prop :=
  ∃ (C : X.OrientedTameStructure (m + 1) Θ x) (hCT : C.Represents T),
    x ∈ supp (X.boundaryTheta Θ) ∧ (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ S) ∧
      P x C ∧ F = (C.boundaryFamily hΘ hCT).nonemptyPart

/-- The common core of Theorems 9.5.15 and 9.5.16: the normalization `c` and the condition `P`
on the structures are parameters. -/
theorem existsUnique_boundaryMeasure (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) (hnd : X.IsNDimensional Θ (m + 1)) (hT : X.IsOrientation Θ T)
    (hG : ∀ N A, G.IsNull N A ↔ X.PObj.IsHNull m (A ∩ N))
    (c : Obj → ℝ) (hc : ∀ φ : Mor, c (X.src φ) = c (X.tgt φ))
    (P : ∀ x, X.OrientedTameStructure (m + 1) Θ x → Prop)
    (hPc : ∀ x C, P x C → ∀ a : C.rep.U, c x *
      (Nat.card (X.Isotropy x ⧸ MulAction.stabilizer (X.Isotropy x) a) : ℝ) = c a)
    (hcov : ∀ x ∈ supp (X.boundaryTheta Θ), ∃ C : X.OrientedTameStructure (m + 1) Θ x,
      C.Represents T ∧ (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ S) ∧ P x C) :
    ∃! Φ : Ω →ₗ[ℝ] @SignedMeasure (X.orbitSupp (X.boundaryTheta Θ))
        (X.lebesgueSigmaBoundaryH (m + 1) Θ),
      ∀ (ω : Ω) (x : Obj) (C : X.OrientedTameStructure (m + 1) Θ x) (hCT : C.Represents T),
        x ∈ supp (X.boundaryTheta Θ) →
        (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ S) → P x C →
        ∀ K : Set (X.orbitSupp (X.boundaryTheta Θ)),
          MeasurableSet[X.lebesgueSigmaBoundaryH (m + 1) Θ] K →
          Subtype.val '' K ⊆ X.π '' C.U →
          Φ ω K = c x * (C.boundaryFamily hΘ hCT).nonemptyPart.sheetSum 𝓘 ω
            (X.π ⁻¹' (Subtype.val '' K)) := by
  have hind := hasIndependentTangentSums (X := X) Θ
  obtain ⟨Φ, hΦ, huniq⟩ := existsUnique_familyMeasure 𝓘
    (isMorSaturated_boundaryStratumSet hΘ hT) (isNaturalOn_boundaryStratumSet hΘ hT)
    (isCompact_orbitSupp_boundaryTheta hΘ hind hcpt) (X.lebesgueSigmaBoundaryH (m + 1) Θ)
    (borel_le_lebesgueSigmaBoundaryH (m + 1) Θ) c hc (BoundaryGood hΘ S P)
    (fun x F hF i => by
      obtain ⟨C, hCT, -, hS, -, rfl⟩ := hF
      exact hS i.1 i.2)
    (fun x F hF => by
      obtain ⟨C, hCT, -, -, -, rfl⟩ := hF
      exact OrientedSheetFamily.represents_nonemptyPart _ (C.represents_boundaryFamily hΘ hCT))
    (fun x F hF a => by
      obtain ⟨C, hCT, -, -, hP, rfl⟩ := hF
      exact hPc x C hP a)
    (fun x F hF K hK i => by
      obtain ⟨C, hCT, hx, -, -, rfl⟩ := hF
      exact C.isMeasIn_boundarySheet hG hnd hx i.1 hK)
    (fun x hx => by
      obtain ⟨C, hCT, hS, hP⟩ := hcov x hx
      exact ⟨_, C, hCT, hx, hS, hP, rfl⟩)
  refine ⟨Φ, fun ω x C hCT hx hS hP K hK hKU => hΦ ω x _ ⟨C, hCT, hx, hS, hP, rfl⟩ K hK
    (by rw [OrientedSheetFamily.nonemptyPart_rep]; change _ ⊆ X.π '' C.rep.U
        rw [← C.U_eq]; exact hKU), fun Ψ hΨ => huniq Ψ ?_⟩
  rintro ω x F ⟨C, hCT, hx, hS, hP, rfl⟩ K hK hKU
  refine hΨ ω x C hCT hx hS hP K hK ?_
  rw [C.U_eq]; exact hKU

/-- **Theorem 9.5.15, 2021 p. 449 (2017: Theorem 9.4)**, for a sheet integration `𝓘` whose null
sets are those of `m`-dimensional measure zero: let `Θ̂` be oriented, tame, compact, of dimension
`m + 1`.  There is a linear map `ω ↦ μ_ω^∂` from the forms to the finite signed measures on
`(∂S, L(∂S))` characterized uniquely by: for every oriented tame structure `(Mᵢ, oᵢ)`, `(σᵢ)` on
`U(x)`, `x ∈ supp(∂Θ)`, describing `T̂Θ` (nonempty boundary sheets in `S`), and every measurable
`K ⊆ ∂S` contained in `|U(x)|`, `μ_ω^∂(K) = (1/♯G_x) ∑ σᵢ ∫_{Kᵢ} ω|(∂₁Mᵢ, o_{∂Mᵢ})` (the sum
over the nonempty `∂₁Mᵢ`).  Added hypothesis `hcov`: such structures exist at every point of
`supp(∂Θ)` (the analogue of E1's `theorem_9_5_4` hypothesis). -/
theorem theorem_9_5_15_hyp (hΘ : X.IsBranchedEpSubgroupoid Θ) (hcpt : X.IsCompactBranched Θ)
    (hnd : X.IsNDimensional Θ (m + 1)) (hT : X.IsOrientation Θ T)
    (hG : ∀ N A, G.IsNull N A ↔ X.PObj.IsHNull m (A ∩ N))
    (hcov : ∀ x ∈ supp (X.boundaryTheta Θ), ∃ C : X.OrientedTameStructure (m + 1) Θ x,
      C.Represents T ∧ ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ S) :
    ∃! Φ : Ω →ₗ[ℝ] @SignedMeasure (X.orbitSupp (X.boundaryTheta Θ))
        (X.lebesgueSigmaBoundaryH (m + 1) Θ),
      ∀ (ω : Ω) (x : Obj) (C : X.OrientedTameStructure (m + 1) Θ x) (hCT : C.Represents T),
        x ∈ supp (X.boundaryTheta Θ) →
        (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ S) →
        ∀ K : Set (X.orbitSupp (X.boundaryTheta Θ)),
          MeasurableSet[X.lebesgueSigmaBoundaryH (m + 1) Θ] K →
          Subtype.val '' K ⊆ X.π '' C.U →
          Φ ω K = (Nat.card (X.Isotropy x) : ℝ)⁻¹ *
            (C.boundaryFamily hΘ hCT).nonemptyPart.sheetSum 𝓘 ω (X.π ⁻¹' (Subtype.val '' K)) := by
  obtain ⟨Φ, hΦ, huniq⟩ := existsUnique_boundaryMeasure 𝓘 hΘ hcpt hnd hT hG
    (fun x => (Nat.card (X.Isotropy x) : ℝ)⁻¹) (fun φ => by rw [card_isotropy_eq_of_mor φ rfl rfl])
    (fun _ _ => True) (fun x C _ a => card_isotropy_normalizing C.rep a)
    (fun x hx => by obtain ⟨C, h1, h2⟩ := hcov x hx; exact ⟨C, h1, h2, True.intro⟩)
  exact ⟨Φ, fun ω x C hCT hx hS => hΦ ω x C hCT hx hS True.intro,
    fun Ψ hΨ => huniq Ψ fun ω x C hCT hx hS _ => hΨ ω x C hCT hx hS⟩

/-- **Theorem 9.5.16, 2021 p. 449 (2017: Theorem 9.5)**: as Theorem 9.5.15 for structures whose
`U(x)` has the local unique continuation property, with `1/♯G_x^eff`. -/
theorem theorem_9_5_16_hyp (hΘ : X.IsBranchedEpSubgroupoid Θ) (hcpt : X.IsCompactBranched Θ)
    (hnd : X.IsNDimensional Θ (m + 1)) (hT : X.IsOrientation Θ T)
    (hG : ∀ N A, G.IsNull N A ↔ X.PObj.IsHNull m (A ∩ N))
    (hcov : ∀ x ∈ supp (X.boundaryTheta Θ), ∃ C : X.OrientedTameStructure (m + 1) Θ x,
      C.Represents T ∧ (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ S) ∧
        C.rep.HasLUC) :
    ∃! Φ : Ω →ₗ[ℝ] @SignedMeasure (X.orbitSupp (X.boundaryTheta Θ))
        (X.lebesgueSigmaBoundaryH (m + 1) Θ),
      ∀ (ω : Ω) (x : Obj) (C : X.OrientedTameStructure (m + 1) Θ x) (hCT : C.Represents T),
        x ∈ supp (X.boundaryTheta Θ) →
        (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ S) → C.rep.HasLUC →
        ∀ K : Set (X.orbitSupp (X.boundaryTheta Θ)),
          MeasurableSet[X.lebesgueSigmaBoundaryH (m + 1) Θ] K →
          Subtype.val '' K ⊆ X.π '' C.U →
          Φ ω K = (Nat.card (X.EffIsotropy x) : ℝ)⁻¹ *
            (C.boundaryFamily hΘ hCT).nonemptyPart.sheetSum 𝓘 ω (X.π ⁻¹' (Subtype.val '' K)) :=
  existsUnique_boundaryMeasure 𝓘 hΘ hcpt hnd hT hG
    (fun x => (Nat.card (X.EffIsotropy x) : ℝ)⁻¹)
    (fun φ => by rw [card_effIsotropy_eq_of_mor φ rfl rfl])
    (fun _ C => C.rep.HasLUC) (fun x C hL a => card_effIsotropy_normalizing C.rep hL a) hcov

end Measures

/-! ### The instance `S = F.msheets` -/

section MSheets

variable {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω] {m : ℕ} (F : X.FormEval m Ω)

/-- **Theorem 9.5.15** for E4's integration over countably many graph charts (`F.msheets`). -/
theorem theorem_9_5_15_msheets (hm : 0 < m) (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) (hnd : X.IsNDimensional Θ (m + 1)) (hT : X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp (X.boundaryTheta Θ), ∃ C : X.OrientedTameStructure (m + 1) Θ x,
      C.Represents T ∧ ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ F.msheets) :
    ∃! Φ : Ω →ₗ[ℝ] @SignedMeasure (X.orbitSupp (X.boundaryTheta Θ))
        (X.lebesgueSigmaBoundaryH (m + 1) Θ),
      ∀ (ω : Ω) (x : Obj) (C : X.OrientedTameStructure (m + 1) Θ x) (hCT : C.Represents T),
        x ∈ supp (X.boundaryTheta Θ) →
        (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ F.msheets) →
        ∀ K : Set (X.orbitSupp (X.boundaryTheta Θ)),
          MeasurableSet[X.lebesgueSigmaBoundaryH (m + 1) Θ] K →
          Subtype.val '' K ⊆ X.π '' C.U →
          Φ ω K = (Nat.card (X.Isotropy x) : ℝ)⁻¹ *
            (C.boundaryFamily hΘ hCT).nonemptyPart.sheetSum (F.msheetIntegration hm) ω
              (X.π ⁻¹' (Subtype.val '' K)) :=
  theorem_9_5_15_hyp (F.msheetIntegration hm) hΘ hcpt hnd hT (fun _ _ => Iff.rfl) hcov

/-- **Theorem 9.5.16** for E4's integration over countably many graph charts (`F.msheets`). -/
theorem theorem_9_5_16_msheets (hm : 0 < m) (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) (hnd : X.IsNDimensional Θ (m + 1)) (hT : X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp (X.boundaryTheta Θ), ∃ C : X.OrientedTameStructure (m + 1) Θ x,
      C.Represents T ∧ (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ F.msheets) ∧
        C.rep.HasLUC) :
    ∃! Φ : Ω →ₗ[ℝ] @SignedMeasure (X.orbitSupp (X.boundaryTheta Θ))
        (X.lebesgueSigmaBoundaryH (m + 1) Θ),
      ∀ (ω : Ω) (x : Obj) (C : X.OrientedTameStructure (m + 1) Θ x) (hCT : C.Represents T),
        x ∈ supp (X.boundaryTheta Θ) →
        (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ F.msheets) → C.rep.HasLUC →
        ∀ K : Set (X.orbitSupp (X.boundaryTheta Θ)),
          MeasurableSet[X.lebesgueSigmaBoundaryH (m + 1) Θ] K →
          Subtype.val '' K ⊆ X.π '' C.U →
          Φ ω K = (Nat.card (X.EffIsotropy x) : ℝ)⁻¹ *
            (C.boundaryFamily hΘ hCT).nonemptyPart.sheetSum (F.msheetIntegration hm) ω
              (X.π ⁻¹' (Subtype.val '' K)) :=
  theorem_9_5_16_hyp (F.msheetIntegration hm) hΘ hcpt hnd hT (fun _ _ => Iff.rfl) hcov

/-! ### The hypothesis `hcov` -/

/-- **Compact boundary sheets satisfy the class condition**: a nonempty compact `∂₁Mᵢ` lies in
`F.msheets` (E4's `msheets_of_isCompact`; `∂₁Mᵢ` is an `m`-dimensional submanifold, E6). -/
theorem OrientedTameStructure.boundarySheet_mem_msheets_of_isCompact {x : Obj}
    (C : X.OrientedTameStructure (m + 1) Θ x) (i : C.ι) (hc : IsCompact (C.boundarySheet i))
    (hne : (C.boundarySheet i).Nonempty) : C.boundarySheet i ∈ F.msheets :=
  FormEval.msheets_of_isCompact (C.isSubmanifoldOfDim_boundarySheet i) hc hne

/-- `hcov` holds for every `Θ` whose structures (at the points of `supp(∂Θ)`) have compact
boundary sheets. -/
theorem hcov_msheets_of_isCompact
    (h : ∀ x ∈ supp (X.boundaryTheta Θ), ∃ C : X.OrientedTameStructure (m + 1) Θ x,
      C.Represents T ∧ ∀ i, IsCompact (C.boundarySheet i)) :
    ∀ x ∈ supp (X.boundaryTheta Θ), ∃ C : X.OrientedTameStructure (m + 1) Θ x,
      C.Represents T ∧ ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ F.msheets :=
  fun x hx => by
    obtain ⟨C, hCT, hc⟩ := h x hx
    exact ⟨C, hCT, fun i hne => C.boundarySheet_mem_msheets_of_isCompact F i (hc i) hne⟩

end MSheets

/-- `hcov` holds for `Θ = 0` (`supp(∂0) = ∅`). -/
theorem hcov_zero {m : ℕ} {S : Set (Set Obj)} (T : Obj → X.PObj.OrTangent →₀ ℚ) :
    ∀ x ∈ supp (X.boundaryTheta (0 : Obj → ℚ)), ∃ C : X.OrientedTameStructure (m + 1) 0 x,
      C.Represents T ∧ ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ S := by
  intro x hx
  exfalso
  have h0 : X.boundaryTheta (0 : Obj → ℚ) x = 0 :=
    X.boundaryTheta_eq_zero_of_not_mem_supp (Θ := 0) (lt_irrefl (0 : ℚ))
  change 0 < X.boundaryTheta (0 : Obj → ℚ) x at hx
  rw [h0] at hx
  exact lt_irrefl _ hx

end EpGroupoid

end Polyfold
