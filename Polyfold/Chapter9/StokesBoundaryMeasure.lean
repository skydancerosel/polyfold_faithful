import Polyfold.Chapter9.BoundaryLocal
import Polyfold.Chapter9.BoundaryIntegralStratum
import Polyfold.Chapter9.StokesPartitionAllDegrees
import Polyfold.Chapter9.FiniteTheorem

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5: **Theorems 9.5.17 and 9.5.18 (Stokes), pp. 449–451** (2017: Theorems
9.6, 9.7), gap G.110.  Numbers and pages are the 2021 text's.

# Stokes' theorem with the boundary measures of Theorems 9.5.15, 9.5.16

`∫_Θ̂ dω = ∫_{∂S} ω dμ^{∂Θ̂}` (`= μ^{∂Θ̂}_ω(∂S)`), and `∮_Θ̂ dω = ∮_{∂S} ω dμ^{∂Θ̂}` for the
effective integrals, for `ω ∈ Ωᵐ_{ep,∞}(X)`, `m ≥ 1`, with E7's boundary measures for E4's integral
over countably many graph charts (`theorem_9_5_15_msheets`, `theorem_9_5_16_msheets`).

The proof is the one on pp. 450–451: E5/E6's `stokes_of_boundary_functional_all` with
`Φ^∂(ω) = μ^∂_ω(∂S)`; the two properties it needs are
(a) `μ^∂_{βω}(∂S) = c(x) ∑ᵢ σᵢ ∫_{∂(Mᵢ,oᵢ)} βω` for `supp β ⊆ U(x)^*`: the locality of `μ^∂`
(`boundaryMeasure_univ_eq`) and Part I's boundary integral of a sheet equal to the integral over
its boundary stratum `∂₁Mᵢ` with `o_{∂Mᵢ}` (E8F's `boundaryIntegral_eq_msInteg`); for structures
at points off `supp(∂Θ)` the structure is first restricted so that `U(x)^*` avoids `supp(∂Θ)`
(`exists_restrict_subset`), and both sides vanish;
(b) `μ^∂_{βω} = 0` when `supp β ∩ supp Θ = ∅` (`boundaryMeasure_eq_zero_of_integ_eq_zero`).

* **`EP.stokes_of_boundaryMeasure`**: the generic statement (weights `c`, condition `P`).
* **`EP.theorem_9_5_17_hyp`, `EP.theorem_9_5_18_hyp`**: for every `Φ^∂` with the local formula of
  Theorem 9.5.15 (9.5.16).
* **`EP.boundaryBranchedMeasure`**, **`EP.theorem_9_5_17_msheets`**, and the effective
  `EP.boundaryBranchedMeasureEff`, **`EP.theorem_9_5_18_msheets`**: with the measures of
  Theorems 9.5.15, 9.5.16 themselves, `∫_Θ̂ dω = μ^∂_ω(∂S)`.

Added hypothesis `hcovS` (E7's class condition, together with the one-chart condition of the
interior integral): at every point of `supp Θ` an oriented tame structure describing `T̂Θ` whose
sheets lie in one graph chart (`sheets`) and whose nonempty boundary sheets lie in `msheets`.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory Module Manifold

noncomputable section

namespace Polyfold

universe u

open MPolyfold EpGroupoid

namespace EP

variable (A : EP.{u}) {m : ℕ} {Θ : A.Obj → ℚ} {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ}

/-- `∫_B βω = 0` over a sheet of `msheets` when `β` vanishes on `B ∩ N`. -/
theorem msInteg_smul_eq_zero {β : A.Obj → ℝ} (hβ : A.X.PObj.IsScSmoothMap realPolyfold β)
    (hinv : ∀ φ : A.Mor, β (A.X.src φ) = β (A.X.tgt φ)) (ω : A.epFormsInfty m) (N : Set A.Obj)
    (g : A.Obj → A.X.PObj.OrTangent) {B : Set A.Obj} (h : ∀ y ∈ B ∩ N, β y = 0) :
    (A.epFormsInftyEval m).msInteg (A.epFormsInftySmul β m hβ hinv ω) N g B = 0 :=
  (A.epFormsInftyEval m).msInteg_eq_zero_of_ev_eq_zero _ N g fun y hy _ hN' hyN' _ hα => by
    rw [A.epFormsInftyEval_epFormsInftySmul hβ hinv ω hN' hyN' hα, h y hy, zero_mul]

/-- **The boundary integrals of `βω` over the sheets of one structure** (last equality of the
display on p. 451): for `supp β ⊆ U(x)^*`, `Θ` compact,
`∑ᵢ σᵢ ∫_{∂(Mᵢ,oᵢ)} βω = ∑ᵢ σᵢ ∫_{∂₁Mᵢ} βω|(∂₁Mᵢ, o_{∂Mᵢ})`. -/
theorem sum_boundaryIntegral_smul_eq (hm : 0 < m) (hcpt : A.X.IsCompactBranched Θ) {x : A.Obj}
    (C : A.X.OrientedTameStructure (m + 1) Θ x)
    (hS : ∀ i, C.M i ∈ (A.epFormsInftyEval (m + 1)).sheets)
    (hb : ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ (A.epFormsInftyEval m).msheets)
    {β : A.Obj → ℝ} (hβ : A.X.PObj.IsScSmoothMap realPolyfold β)
    (hinv : ∀ φ : A.Mor, β (A.X.src φ) = β (A.X.tgt φ))
    (hsupp : tsupport β ⊆ A.X.π ⁻¹' (A.X.π '' C.U)) (ω : A.epFormsInfty m) :
    ∑ i, (C.σ i : ℝ) * (C.orientedSheet (A.epFormsInftyEval (m + 1)) hS i).boundaryIntegral
        (A.epFormsInftyToObj m (A.epFormsInftySmul β m hβ hinv ω)) =
      ∑ i, (C.σ i : ℝ) * (A.epFormsInftyEval m).msInteg (A.epFormsInftySmul β m hβ hinv ω)
        (C.boundarySheet i) (C.boundaryOrient i).tangent (C.boundarySheet i) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have hK : IsCompact (C.M i ∩ tsupport β) :=
    C.toTameBranchingStructure.isCompact_inter hcpt (isClosed_tsupport β)
      (EpGroupoid.isSaturated_tsupport hinv) hsupp i
  let _ := A.X.PObj.paracompactSpace_subtype (C.M i)
  let hcs := C.toTameBranchingStructure.hasCornerStructureOfDim C.isSubmanifoldOfDim i
  let _ := (subPolyfold (C.isSubmanifoldOfDim i).1.isSubMPolyfold).cornerChartedSpace hcs
  have h0 : (C.orientedSheet (A.epFormsInftyEval (m + 1)) hS i).VanishesOff (tsupport β)
      (A.epFormsInftyToObj m (A.epFormsInftySmul β m hβ hinv ω)) := fun y hy =>
    A.formsInftyRestrict_smul_eq_zero (hcs := hcs) hm (C.isSubmanifoldOfDim i).1 hβ hinv ω y hy
  exact A.boundaryIntegral_eq_msInteg hm C hS i (hb i) _ (isClosed_tsupport β) hK h0

/-! ### The generic statement -/

variable (Φ : A.epFormsInfty (m + 1) →ₗ[ℝ] @SignedMeasure (A.X.orbitSupp Θ)
    (A.X.lebesgueSigma (A.epFormsInftyEval (m + 1)).sheetNull Θ))
  (Φb : A.epFormsInfty m →ₗ[ℝ] @SignedMeasure (A.X.orbitSupp (A.X.boundaryTheta Θ))
    (A.X.lebesgueSigmaBoundaryH (m + 1) Θ))
  (c : A.Obj → ℝ) (P : ∀ x, A.X.OrientedTameStructure (m + 1) Θ x → Prop)

/-- **Stokes' theorem with the boundary measure, generic form**: let `Φ` have the local formula of
Theorem 9.5.4 or 9.5.5 and `Φb` the one of Theorem 9.5.15 or 9.5.16 (weights `c`, a condition `P`
on the structures, inherited by restrictions with the same action), and let every point of
`supp Θ` have a structure describing `T̂Θ` with sheets in one graph chart, nonempty boundary
sheets in `msheets`, and `P`.  Then `Φ(dω)(S) = Φb(ω)(∂S)`. -/
theorem stokes_of_boundaryMeasure (hm : 0 < m) (hPU : A.X.HasScPartitionsOfUnity)
    (hΘ : A.X.IsBranchedEpSubgroupoid Θ) (hcpt : A.X.IsCompactBranched Θ)
    (hPres : ∀ x (C₀ C : A.X.OrientedTameStructure (m + 1) Θ x), P x C₀ →
      C.rep.U ⊆ C₀.rep.U → C.rep.Φ = C₀.rep.Φ → P x C)
    (hcovS : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T ∧
      (∀ i, C.M i ∈ (A.epFormsInftyEval (m + 1)).sheets) ∧
      (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ (A.epFormsInftyEval m).msheets) ∧
        P x C)
    (hΦ : ∀ (η : A.epFormsInfty (m + 1)) (x : A.Obj)
      (C : A.X.OrientedTameStructure (m + 1) Θ x),
      (∀ i, C.M i ∈ (A.epFormsInftyEval (m + 1)).sheets) → C.Represents T → P x C →
      ∀ K : Set (A.X.orbitSupp Θ),
        MeasurableSet[A.X.lebesgueSigma (A.epFormsInftyEval (m + 1)).sheetNull Θ] K →
        Subtype.val '' K ⊆ A.X.π '' C.U →
        Φ η K = c x * C.sheetSum ((A.epFormsInftyEval (m + 1)).sheetIntegration (Nat.succ_pos m))
          η (A.X.π ⁻¹' (Subtype.val '' K)))
    (hΦb : IsBoundaryLocal (A.epFormsInftyEval m) hm hΘ Φb c P (T := T))
    (ω : A.epFormsInfty m) :
    Φ (A.epFormsInftyD m ω) univ = Φb ω univ := by
  have hnd : A.X.IsNDimensional Θ (m + 1) := FormEval.isNDimensional_of_loc hcovS
  have hcovB : ∀ x ∈ supp (A.X.boundaryTheta Θ), ∃ C : A.X.OrientedTameStructure (m + 1) Θ x,
      C.Represents T ∧
        (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ (A.epFormsInftyEval m).msheets) ∧
        P x C := fun x hx => by
    obtain ⟨C, hCT, -, hb, hP⟩ := hcovS x (A.X.supp_boundaryTheta_subset Θ hx).2
    exact ⟨C, hCT, hb, hP⟩
  let Good : ∀ x, A.X.OrientedTameStructure (m + 1) Θ x → Prop := fun x C =>
    ((∀ i, C.M i ∈ (A.epFormsInftyEval (m + 1)).sheets) ∧ C.Represents T ∧ P x C) ∧
      (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ (A.epFormsInftyEval m).msheets) ∧
      (x ∈ supp (A.X.boundaryTheta Θ) ∨
        Disjoint (A.X.π ⁻¹' (A.X.π '' C.U)) (supp (A.X.boundaryTheta Θ)))
  have hcov : ∀ x ∈ supp Θ, ∃ C, Good x C := fun x hx => by
    obtain ⟨C₀, hCT, hS, hb, hP⟩ := hcovS x hx
    by_cases hxb : x ∈ supp (A.X.boundaryTheta Θ)
    · exact ⟨C₀, ⟨hS, hCT, hP⟩, hb, Or.inl hxb⟩
    · obtain ⟨C, hS', hCT', hUW, hU, hΦeq⟩ :=
        C₀.exists_restrict_subset (A.epFormsInftyEval (m + 1)) hCT hS
        (isOpen_compl_preimage_orbitSupp_boundaryTheta hΘ hcpt)
        (mem_compl_preimage_orbitSupp_boundaryTheta hΘ hxb)
      have hd := disjoint_preimage_image_supp_boundaryTheta hUW
      exact ⟨C, ⟨hS', hCT', hPres x C₀ C hP hU hΦeq⟩,
        fun i hne => (hne.ne_empty (C.boundarySheet_eq_empty hd i)).elim, Or.inr hd⟩
  let Φb' : A.epFormsInfty m →ₗ[ℝ] ℝ :=
    { toFun := fun ω => Φb ω univ
      map_add' := fun a b => by rw [map_add]; rfl
      map_smul' := fun r a => by rw [map_smul]; rfl }
  have huniv : MeasurableSet[A.X.lebesgueSigmaBoundaryH (m + 1) Θ]
      (univ : Set (A.X.orbitSupp (A.X.boundaryTheta Θ))) :=
    @MeasurableSet.univ _ (A.X.lebesgueSigmaBoundaryH (m + 1) Θ)
  refine A.stokes_of_boundary_functional_all Φ c Good hPU hcpt (fun _ _ h => h.1.1) hcov
    (fun η x C hC K hK hKU => hΦ η x C hC.1.1 hC.1.2.1 hC.1.2.2 K hK hKU) Φb'
    (fun x C hC β hβ hinv hs ω => ?_) (fun β hβ hinv hd ω => ?_) ω
  · change Φb (A.epFormsInftySmul β m hβ hinv ω) univ = _
    rw [A.sum_boundaryIntegral_smul_eq hm hcpt C hC.1.1 hC.2.1 hβ hinv hs ω]
    rcases hC.2.2 with hx | hd
    · exact boundaryMeasure_univ_eq (A.epFormsInftyEval m) hm hΘ Φb c P hcpt hnd hΦb hcovB _ C
        hC.1.2.1 hx hC.2.1
        hC.1.2.2 (isClosed_tsupport β) (EpGroupoid.isSaturated_tsupport hinv) hs
        fun x' C' _ i B _ hBZ => A.msInteg_smul_eq_zero hβ hinv ω _ _ fun y hy =>
          image_eq_zero_of_notMem_tsupport (Set.disjoint_left.1 hBZ hy.1)
    · have h1 : Φb (A.epFormsInftySmul β m hβ hinv ω) univ = 0 :=
        boundaryMeasure_eq_zero_of_integ_eq_zero (A.epFormsInftyEval m) hm hΘ Φb c P hcpt hΦb hcovB
          _ huniv
          fun x' C' _ i B hB => A.msInteg_smul_eq_zero hβ hinv ω _ _ fun y hy =>
            image_eq_zero_of_notMem_tsupport fun hyt => Set.disjoint_left.1 hd (hs hyt)
              (C'.boundarySheet_subset_supp_boundaryTheta i (hB hy.1).1)
      rw [h1, Finset.sum_eq_zero fun i _ => ?_, mul_zero]
      rw [(A.epFormsInftyEval m).msInteg_of_inter_eq_empty _ _
        (by rw [C.boundarySheet_eq_empty hd i, inter_empty]),
        mul_zero]
  · change Φb (A.epFormsInftySmul β m hβ hinv ω) univ = 0
    exact boundaryMeasure_eq_zero_of_integ_eq_zero (A.epFormsInftyEval m) hm hΘ Φb c P hcpt hΦb
      hcovB _ huniv
      fun x' C' _ i B hB => A.msInteg_smul_eq_zero hβ hinv ω _ _ fun y hy =>
        image_eq_zero_of_notMem_tsupport fun hyt => Set.disjoint_left.1 hd hyt
          (C'.toTameBranchingStructure.toLocalBranchingStructure.M_subset_supp i
            (C'.boundarySheet_subset i (hB hy.1).1))

/-! ### Theorems 9.5.17 and 9.5.18 -/

/-- **Theorem 9.5.17 (Stokes), 2021 p. 449 (2017: Theorem 9.6)**: `X` with sc-smooth partitions
of unity, `Θ` compact, oriented by `T̂Θ = T`, `ω ∈ Ωᵐ_{ep,∞}(X)`, `m ≥ 1`.  For every linear
`ω ↦ μ^∂_ω` with the characterizing local formula of Theorem 9.5.15 (weights `1/♯G_x`),
`∫_Θ̂ dω = μ^∂_ω(∂S) = ∫_{∂S} ω dμ^{∂Θ̂}`.  Hypothesis `hcovS`: at every point of `supp Θ` an
oriented tame structure describing `T̂Θ` with sheets in one graph chart and nonempty boundary
sheets in `msheets` (E7's class condition). -/
theorem theorem_9_5_17_hyp (hm : 0 < m) (hPU : A.X.HasScPartitionsOfUnity)
    (hΘ : A.X.IsBranchedEpSubgroupoid Θ) (hcpt : A.X.IsCompactBranched Θ)
    (hT : A.X.IsOrientation Θ T)
    (hcovS : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T ∧
      (∀ i, C.M i ∈ (A.epFormsInftyEval (m + 1)).sheets) ∧
      ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ (A.epFormsInftyEval m).msheets)
    (hΦb : IsBoundaryLocal (A.epFormsInftyEval m) hm hΘ Φb
      (fun x => (Nat.card (A.X.Isotropy x) : ℝ)⁻¹) (fun _ _ => True) (T := T))
    (ω : A.epFormsInfty m) :
    (A.epFormsInftyEval (m + 1)).tameBranchedIntegral (Nat.succ_pos m) hΘ hcpt hT
        (fun x hx => (hcovS x hx).imp fun _ h => h.1) (A.epFormsInftyD m ω) =
      Φb ω univ := by
  set F := A.epFormsInftyEval (m + 1) with hF
  have hcov := F.hcov_of_loc (fun x hx => (hcovS x hx).imp fun _ h => h.1)
  exact A.stokes_of_boundaryMeasure
    (branchedMeasure (F.sheetIntegration (Nat.succ_pos m)) hΘ hcpt hT hcov) Φb
    (fun x => (Nat.card (A.X.Isotropy x) : ℝ)⁻¹) (fun _ _ => True) hm hPU hΘ hcpt
    (fun _ _ _ _ _ _ => True.intro)
    (fun x hx => (hcovS x hx).imp fun _ h => ⟨h.1, h.2.1, h.2.2, True.intro⟩)
    (fun η x C hS hCT _ K hK hKU => branchedMeasure_apply (F.sheetIntegration (Nat.succ_pos m))
      hΘ hcpt hT hcov η C hS hCT hK hKU) hΦb ω

/-- **Theorem 9.5.18 (effective Stokes), 2021 p. 450 (2017: Theorem 9.7)**: the same for the
effective integrals, `∮_Θ̂ dω = μ^∂_ω(∂S)` for every `μ^∂` with the local formula of Theorem
9.5.16 (weights `1/♯G_x^eff`, structures with the property of Definition 7.2.18 on `U(x)`). -/
theorem theorem_9_5_18_hyp (hm : 0 < m) (hPU : A.X.HasScPartitionsOfUnity)
    (hΘ : A.X.IsBranchedEpSubgroupoid Θ) (hcpt : A.X.IsCompactBranched Θ)
    (hT : A.X.IsOrientation Θ T)
    (hcovS : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T ∧
      (∀ i, C.M i ∈ (A.epFormsInftyEval (m + 1)).sheets) ∧
      (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ (A.epFormsInftyEval m).msheets) ∧
        C.rep.HasLUC)
    (hΦb : IsBoundaryLocal (A.epFormsInftyEval m) hm hΘ Φb
      (fun x => (Nat.card (A.X.EffIsotropy x) : ℝ)⁻¹) (fun _ C => C.rep.HasLUC) (T := T))
    (ω : A.epFormsInfty m) :
    (A.epFormsInftyEval (m + 1)).tameBranchedIntegralEff (Nat.succ_pos m) hΘ hcpt hT
        (fun x hx => (hcovS x hx).imp fun _ h => ⟨h.1, h.2.2.2⟩) (A.epFormsInftyD m ω) =
      Φb ω univ := by
  set F := A.epFormsInftyEval (m + 1) with hF
  have hcov := F.hcovEff_of_loc (fun x hx => (hcovS x hx).imp fun _ h => ⟨h.1, h.2.2.2⟩)
  exact A.stokes_of_boundaryMeasure
    (branchedMeasureEff (F.sheetIntegration (Nat.succ_pos m)) hΘ hcpt hT hcov) Φb
    (fun x => (Nat.card (A.X.EffIsotropy x) : ℝ)⁻¹) (fun _ C => C.rep.HasLUC) hm hPU hΘ hcpt
    (fun _ C₀ C hL hU hΦ g V hV hne hVU hid y hy => by
      rw [hΦ] at hid ⊢
      exact hL g V hV hne (hVU.trans hU) hid y (hU hy))
    hcovS
    (fun η x C hS hCT hL K hK hKU => branchedMeasureEff_apply
      (F.sheetIntegration (Nat.succ_pos m)) hΘ hcpt hT hcov η C hS hCT hL hK hKU) hΦb ω

/-! ### With the measures of Theorems 9.5.15, 9.5.16 -/

/-- The hypothesis of Theorem 9.5.15 at the points of `supp(∂Θ)`, from `hcovS`. -/
theorem hcovB_of_hcovS
    (hcovS : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T ∧
      (∀ i, C.M i ∈ (A.epFormsInftyEval (m + 1)).sheets) ∧
      ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ (A.epFormsInftyEval m).msheets) :
    ∀ x ∈ supp (A.X.boundaryTheta Θ), ∃ C : A.X.OrientedTameStructure (m + 1) Θ x,
      C.Represents T ∧
        ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ (A.epFormsInftyEval m).msheets :=
  fun x hx => (hcovS x (A.X.supp_boundaryTheta_subset Θ hx).2).imp fun _ h => ⟨h.1, h.2.2⟩

/-- **The boundary measure `ω ↦ μ^{∂Θ̂}_ω` of Theorem 9.5.15** (E7's `theorem_9_5_15_msheets`,
for E4's integral over countably many graph charts). -/
def boundaryBranchedMeasure (hm : 0 < m) (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T)
    (hcovS : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T ∧
      (∀ i, C.M i ∈ (A.epFormsInftyEval (m + 1)).sheets) ∧
      ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ (A.epFormsInftyEval m).msheets) :
    A.epFormsInfty m →ₗ[ℝ] @SignedMeasure (A.X.orbitSupp (A.X.boundaryTheta Θ))
      (A.X.lebesgueSigmaBoundaryH (m + 1) Θ) :=
  (theorem_9_5_15_msheets (A.epFormsInftyEval m) hm hΘ hcpt
    (FormEval.isNDimensional_of_loc hcovS) hT (A.hcovB_of_hcovS hcovS)).exists.choose

/-- **Theorem 9.5.17 (Stokes), 2021 p. 449, as printed**: `∫_Θ̂ dω = ∫_{∂S} ω dμ^{∂Θ̂}`
(`= μ^{∂Θ̂}_ω(∂S)`), with the boundary measure of Theorem 9.5.15. -/
theorem theorem_9_5_17_msheets (hm : 0 < m) (hPU : A.X.HasScPartitionsOfUnity)
    (hΘ : A.X.IsBranchedEpSubgroupoid Θ) (hcpt : A.X.IsCompactBranched Θ)
    (hT : A.X.IsOrientation Θ T)
    (hcovS : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T ∧
      (∀ i, C.M i ∈ (A.epFormsInftyEval (m + 1)).sheets) ∧
      ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ (A.epFormsInftyEval m).msheets)
    (ω : A.epFormsInfty m) :
    (A.epFormsInftyEval (m + 1)).tameBranchedIntegral (Nat.succ_pos m) hΘ hcpt hT
        (fun x hx => (hcovS x hx).imp fun _ h => h.1) (A.epFormsInftyD m ω) =
      A.boundaryBranchedMeasure hm hΘ hcpt hT hcovS ω univ :=
  A.theorem_9_5_17_hyp _ hm hPU hΘ hcpt hT hcovS
    (fun ω x C hCT hx hS _ K hK hKU =>
      (theorem_9_5_15_msheets (A.epFormsInftyEval m) hm hΘ hcpt
        (FormEval.isNDimensional_of_loc hcovS) hT (A.hcovB_of_hcovS hcovS)).exists.choose_spec
        ω x C hCT hx hS K hK hKU) ω

/-- **The effective boundary measure of Theorem 9.5.16** (E7's `theorem_9_5_16_msheets`). -/
def boundaryBranchedMeasureEff (hm : 0 < m) (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T)
    (hcovS : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T ∧
      (∀ i, C.M i ∈ (A.epFormsInftyEval (m + 1)).sheets) ∧
      (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ (A.epFormsInftyEval m).msheets) ∧
        C.rep.HasLUC) :
    A.epFormsInfty m →ₗ[ℝ] @SignedMeasure (A.X.orbitSupp (A.X.boundaryTheta Θ))
      (A.X.lebesgueSigmaBoundaryH (m + 1) Θ) :=
  (theorem_9_5_16_msheets (A.epFormsInftyEval m) hm hΘ hcpt
    (FormEval.isNDimensional_of_loc hcovS) hT
    (fun x hx => (hcovS x (A.X.supp_boundaryTheta_subset Θ hx).2).imp
      fun _ h => ⟨h.1, h.2.2.1, h.2.2.2⟩)).exists.choose

/-- **Theorem 9.5.18 (effective Stokes), 2021 p. 450, as printed**:
`∮_Θ̂ dω = ∮_{∂S} ω dμ^{∂Θ̂}`, with the effective boundary measure of Theorem 9.5.16. -/
theorem theorem_9_5_18_msheets (hm : 0 < m) (hPU : A.X.HasScPartitionsOfUnity)
    (hΘ : A.X.IsBranchedEpSubgroupoid Θ) (hcpt : A.X.IsCompactBranched Θ)
    (hT : A.X.IsOrientation Θ T)
    (hcovS : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T ∧
      (∀ i, C.M i ∈ (A.epFormsInftyEval (m + 1)).sheets) ∧
      (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ (A.epFormsInftyEval m).msheets) ∧
        C.rep.HasLUC)
    (ω : A.epFormsInfty m) :
    (A.epFormsInftyEval (m + 1)).tameBranchedIntegralEff (Nat.succ_pos m) hΘ hcpt hT
        (fun x hx => (hcovS x hx).imp fun _ h => ⟨h.1, h.2.2.2⟩) (A.epFormsInftyD m ω) =
      A.boundaryBranchedMeasureEff hm hΘ hcpt hT hcovS ω univ :=
  A.theorem_9_5_18_hyp _ hm hPU hΘ hcpt hT hcovS
    (theorem_9_5_16_msheets (A.epFormsInftyEval m) hm hΘ hcpt
      (FormEval.isNDimensional_of_loc hcovS) hT
      (fun x hx => (hcovS x (A.X.supp_boundaryTheta_subset Θ hx).2).imp
        fun _ h => ⟨h.1, h.2.2.1, h.2.2.2⟩)).exists.choose_spec ω

end EP

end Polyfold
