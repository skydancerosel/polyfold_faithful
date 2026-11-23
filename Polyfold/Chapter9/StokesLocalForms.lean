import Polyfold.Chapter9.StokesLocalFormsCompare
import Polyfold.Chapter9.StokesLocalFormsStructures
import Polyfold.Chapter9.StokesTextHypotheses

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5, **Theorems 9.5.17 and 9.5.18 (Stokes), pp. 449–451, with Remark 9.5.19,
p. 451** (2017: Theorems 9.6, 9.7, Remark 9.8), point G.153.  Numbers and pages are the 2021
text's.

# Stokes' theorem from the pieces `β_k ω` near `supp Θ`

The proof of Theorem 9.5.18 on pp. 450–451 cuts `ω` into the pieces `ω_k = β_k ω`,
`supp β_k ⊆ U_k^*`.  With a partition of unity near `supp Θ` (Remark 9.5.19) the pieces are forms
near `supp Θ` (`EP.LocalFormSystem`).  Here the display on p. 451 is carried out for such pieces,
`m ≥ 1`:

`∫_Θ̂ dω = μ'_{dω}(S) = ∑ₖ μ'_{dω_k}(S) = ∑ₖ c(x_k) ∑ᵢ σᵢ ∫_{(Mᵢ,oᵢ)} dω_k
  = ∑ₖ c(x_k) ∑ᵢ σᵢ ∫_{∂₁Mᵢ} ω_k = ∑ₖ μ'^∂_{ω_k}(∂S) = μ'^∂_ω(∂S) = μ^∂_ω(∂S)`,

with `μ'`, `μ'^∂` the measures of Theorems 9.5.4/9.5.5 and 9.5.15/9.5.16 for the forms near
`supp Θ`; the first and the last equality compare the measures of the two spaces of forms
(`StokesLocalFormsCompare.lean`).  The structures `U(x)` are chosen before the pieces, with sheets
in the class of every space of forms (`StokesLocalFormsStructures.lean`).

* `EP.stokes_of_localFormSystem`: the generic statement for one system of pieces (weights `c`,
  condition `P`).
* **`EP.stokes_of_localFormSystems`**: Theorem 9.5.17 for `ω`, from systems of pieces subordinate
  to every family of neighbourhoods.
* **`EP.stokesEff_of_localFormSystems`**: Theorem 9.5.18 for `ω`.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u

open MPolyfold EpGroupoid

namespace EP

variable (A : EP.{u}) {m : ℕ} {Θ : A.Obj → ℚ} {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ}

/-- A nonempty boundary sheet inside a compact part of a tame sheet is in the class `msheets` of
`Ωᵐ_{ep,∞}(X)`. -/
theorem mem_msheets_of_isBoundedBoundary (hm : 0 < m) {B : Set A.Obj}
    (h : IsBoundedBoundary A.X Θ m B) (hne : B.Nonempty) :
    B ∈ (A.epFormsInftyEval m).msheets := by
  obtain ⟨M, V, K, hM, ht, -, hV, hK, hKM, hsub, rfl⟩ := h
  exact A.boundaryStratum_inter_mem_msheets hm hM ht hV hK hKM hsub hne

variable {A}

/-- A nonempty boundary sheet inside a compact part of a tame sheet in `supp Θ` is in the class
`msheets` of the forms of degree `m` near `supp Θ`. -/
theorem LocalFormSystem.mem_msheets_of_isBoundedBoundary {N : A.Obj → Set A.Obj}
    {ω : A.epFormsInfty m} (S : A.LocalFormSystem m Θ N ω) {B : Set A.Obj}
    (h : IsBoundedBoundary A.X Θ m B) (hne : B.Nonempty) : B ∈ S.G0.msheets := by
  obtain ⟨M, V, K, hM, ht, hMs, hV, hK, hKM, hsub, rfl⟩ := h
  exact S.boundaryStratum_mem hM ht hMs hV hK hKM hsub hne

variable (A)

/-- **Stokes' theorem from one system of pieces, generic form** (the display on p. 451): let
`C_x`, `x ∈ supp Θ`, be structures describing `T̂Θ` with sheets in the class of every space of
forms, boundary sheets inside compact parts of tame sheets, the condition `P`, and `x ∈ supp(∂Θ)`
or `U(x)^*` disjoint from `supp(∂Θ)`; let `S` be a system of pieces with `Z_k ⊆ U(x_k)^*`; let
`Φ`, `Φb` be the measures of `Ω_{ep,∞}(X)` and `Φ'`, `Φb'` those of the forms near `supp Θ`, all
with the local formulas for the weights `c` and the condition `P`.  Then `Φ(dω)(S) = Φb(ω)(∂S)`. -/
theorem stokes_of_localFormSystem (hm : 0 < m) (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (c : A.Obj → ℝ)
    (P : ∀ x, A.X.OrientedTameStructure (m + 1) Θ x → Prop)
    (Cx : ∀ x, x ∈ supp Θ → A.X.OrientedTameStructure (m + 1) Θ x)
    (hCT : ∀ x hx, (Cx x hx).Represents T)
    (hCS : ∀ x hx i, IsChartBounded A.X (m + 1) ((Cx x hx).M i))
    (hCB : ∀ x hx i, IsBoundedBoundary A.X Θ m ((Cx x hx).boundarySheet i))
    (hCd : ∀ x hx, x ∈ supp (A.X.boundaryTheta Θ) ∨
      Disjoint (A.X.π ⁻¹' (A.X.π '' (Cx x hx).U)) (supp (A.X.boundaryTheta Θ)))
    (hCP : ∀ x hx, P x (Cx x hx))
    {N : A.Obj → Set A.Obj} {ω : A.epFormsInfty m} (S : A.LocalFormSystem m Θ N ω)
    (hZ : ∀ k, S.Z k ⊆ A.X.π ⁻¹' (A.X.π '' (Cx (S.pt k) (S.pt_mem k)).U))
    (Φ : A.epFormsInfty (m + 1) →ₗ[ℝ] @SignedMeasure (A.X.orbitSupp Θ)
      (A.X.lebesgueSigma (A.epFormsInftyEval (m + 1)).sheetNull Θ))
    (hΦ : ∀ (η : A.epFormsInfty (m + 1)) (x : A.Obj)
      (C : A.X.OrientedTameStructure (m + 1) Θ x),
      (∀ i, C.M i ∈ (A.epFormsInftyEval (m + 1)).sheets) → C.Represents T → P x C →
      ∀ K : Set (A.X.orbitSupp Θ),
        MeasurableSet[A.X.lebesgueSigma (A.epFormsInftyEval (m + 1)).sheetNull Θ] K →
        Subtype.val '' K ⊆ A.X.π '' C.U →
        Φ η K = c x * C.sheetSum ((A.epFormsInftyEval (m + 1)).sheetIntegration (Nat.succ_pos m))
          η (A.X.π ⁻¹' (Subtype.val '' K)))
    (Φb : A.epFormsInfty m →ₗ[ℝ] @SignedMeasure (A.X.orbitSupp (A.X.boundaryTheta Θ))
      (A.X.lebesgueSigmaBoundaryH (m + 1) Θ))
    (hΦb : IsBoundaryLocal (A.epFormsInftyEval m) hm hΘ Φb c P (T := T))
    (Φ' : S.Ω1 →ₗ[ℝ] @SignedMeasure (A.X.orbitSupp Θ) (A.X.lebesgueSigma S.F1.sheetNull Θ))
    (hΦ' : ∀ (η : S.Ω1) (x : A.Obj) (C : A.X.OrientedTameStructure (m + 1) Θ x),
      (∀ i, C.M i ∈ S.F1.sheets) → C.Represents T → P x C →
      ∀ K : Set (A.X.orbitSupp Θ), MeasurableSet[A.X.lebesgueSigma S.F1.sheetNull Θ] K →
        Subtype.val '' K ⊆ A.X.π '' C.U →
        Φ' η K = c x * C.sheetSum (S.F1.sheetIntegration (Nat.succ_pos m))
          η (A.X.π ⁻¹' (Subtype.val '' K)))
    (Φb' : S.Ω0 →ₗ[ℝ] @SignedMeasure (A.X.orbitSupp (A.X.boundaryTheta Θ))
      (A.X.lebesgueSigmaBoundaryH (m + 1) Θ))
    (hΦb' : IsBoundaryLocal S.G0 hm hΘ Φb' c P (T := T)) :
    Φ (A.epFormsInftyD m ω) univ = Φb ω univ := by
  have hnd : A.X.IsNDimensional Θ (m + 1) :=
    FormEval.isNDimensional_of_loc (P := fun _ _ => True) fun x hx => ⟨Cx x hx, trivial⟩
  have hF : ∀ x hx i, (Cx x hx).M i ∈ (A.epFormsInftyEval (m + 1)).sheets := fun x hx i => (hCS x hx i).mem_sheets _
  have hF1 : ∀ x hx i, (Cx x hx).M i ∈ S.F1.sheets := fun x hx i =>
    (hCS x hx i).mem_sheets S.F1
  have hG : ∀ x hx i, ((Cx x hx).boundarySheet i).Nonempty →
      (Cx x hx).boundarySheet i ∈ (A.epFormsInftyEval m).msheets := fun x hx i hne =>
    A.mem_msheets_of_isBoundedBoundary hm (hCB x hx i) hne
  have hG0 : ∀ x hx i, ((Cx x hx).boundarySheet i).Nonempty →
      (Cx x hx).boundarySheet i ∈ S.G0.msheets := fun x hx i hne =>
    S.mem_msheets_of_isBoundedBoundary (hCB x hx i) hne
  let Good : ∀ x, A.X.OrientedTameStructure (m + 1) Θ x → Prop := fun x C =>
    (∀ i, C.M i ∈ (A.epFormsInftyEval (m + 1)).sheets) ∧ (∀ i, C.M i ∈ S.F1.sheets) ∧ C.Represents T ∧ P x C
  have hcov : ∀ x ∈ supp Θ, ∃ C, Good x C := fun x hx =>
    ⟨Cx x hx, hF x hx, hF1 x hx, hCT x hx, hCP x hx⟩
  have hsub : ∀ {x}, x ∈ supp (A.X.boundaryTheta Θ) → x ∈ supp Θ := fun hx =>
    (A.X.supp_boundaryTheta_subset Θ hx).2
  have hcovB : ∀ x ∈ supp (A.X.boundaryTheta Θ), ∃ C : A.X.OrientedTameStructure (m + 1) Θ x,
      C.Represents T ∧ (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ (A.epFormsInftyEval m).msheets) ∧
        (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ S.G0.msheets) ∧ P x C :=
    fun x hx => ⟨Cx x (hsub hx), hCT x _, hG x _, hG0 x _, hCP x _⟩
  have hcovB' : ∀ x ∈ supp (A.X.boundaryTheta Θ),
      ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T ∧
        (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ S.G0.msheets) ∧ P x C :=
    fun x hx => ⟨Cx x (hsub hx), hCT x _, hG0 x _, hCP x _⟩
  have hΦg : ∀ (η : S.Ω1) (x : A.Obj) (C : A.X.OrientedTameStructure (m + 1) Θ x), Good x C →
      ∀ K : Set (A.X.orbitSupp Θ), MeasurableSet[A.X.lebesgueSigma S.F1.sheetNull Θ] K →
        Subtype.val '' K ⊆ A.X.π '' C.U →
        Φ' η K = c x * C.sheetSum (S.F1.sheetIntegration (Nat.succ_pos m))
          η (A.X.π ⁻¹' (Subtype.val '' K)) :=
    fun η x C h => hΦ' η x C h.2.1 h.2.2.1 h.2.2.2
  -- the first and the last equality: the two spaces of forms
  have step1 : Φ' (S.j1 (A.epFormsInftyD m ω)) univ = Φ (A.epFormsInftyD m ω) univ :=
    measure_univ_eq_cross (A.epFormsInftyEval (m + 1)) S.F1 (Nat.succ_pos m) Φ Φ' c Good hcpt hcov (fun _ _ h => h.1)
      (fun _ _ h => h.2.1) (fun η x C h => hΦ η x C h.1 h.2.2.1 h.2.2.2) hΦg
      fun y hy M hM hyM β hβ => S.j1_ev _ hM hyM hy β hβ
  have step3 : Φb' (S.j0 ω) univ = Φb ω univ :=
    boundaryMeasure_univ_eq_cross (A.epFormsInftyEval m) S.G0 hm hΘ Φb Φb' c P hcpt hnd hΦb
      hΦb' hcovB fun y hy M hM hyM β hβ => S.j0_ev _ hM hyM hy β hβ
  -- the pieces
  have huniv : MeasurableSet[A.X.lebesgueSigmaBoundaryH (m + 1) Θ]
      (univ : Set (A.X.orbitSupp (A.X.boundaryTheta Θ))) :=
    @MeasurableSet.univ _ (A.X.lebesgueSigmaBoundaryH (m + 1) Θ)
  have step2 : ∀ k, Φ' (S.v k) univ = Φb' (S.u k) univ := fun k => by
    set C := Cx (S.pt k) (S.pt_mem k) with hC
    have hCg : Good (S.pt k) C := ⟨hF _ _, hF1 _ _, hCT _ _, hCP _ _⟩
    have h1 := measure_univ_eq_of_integ_eq_zero (S.F1.sheetIntegration (Nat.succ_pos m)) Φ' c
      Good hcpt (fun _ _ h => h.2.1) hcov hΦg (S.v k) C hCg (S.isClosed_Z k)
      (S.isSaturated_Z k) (hZ k) fun x' C' hC' i B hB hBZ => by
        rw [FormEval.sheetIntegration_integ]
        exact S.integ_v_eq_zero k C' i (hC'.2.1 i) B hB hBZ
    simp only [FormEval.sheetIntegration_integ] at h1
    have h2 : ∀ i, S.F1.integ (S.v k) (C.M i) (C.orient i).tangent (C.M i) =
        S.G0.msInteg (S.u k) (C.boundarySheet i) (C.boundaryOrient i).tangent
          (C.boundarySheet i) := fun i =>
      S.stokes_sheet k C i (hF1 _ _ i) (hG0 _ _ i)
        (C.toTameBranchingStructure.isCompact_inter hcpt (S.isClosed_Z k) (S.isSaturated_Z k)
          (hZ k) i)
    rw [h1, Finset.sum_congr rfl fun i _ => by rw [h2 i]]
    rcases hCd (S.pt k) (S.pt_mem k) with hx | hd
    · exact (boundaryMeasure_univ_eq S.G0 hm hΘ Φb' c P hcpt hnd hΦb' hcovB' (S.u k) C
        (hCT _ _) hx (hG0 _ _) (hCP _ _) (S.isClosed_Z k) (S.isSaturated_Z k) (hZ k)
        fun x' C' _ i B hB hBZ => S.msInteg_u_eq_zero k C' i B hB hBZ).symm
    · have h0 : Φb' (S.u k) univ = 0 :=
        boundaryMeasure_eq_zero_of_integ_eq_zero S.G0 hm hΘ Φb' c P hcpt hΦb' hcovB' (S.u k)
          huniv fun x' C' _ i B hB => S.msInteg_u_eq_zero k C' i B (fun y hy => (hB hy).1)
            (Set.disjoint_left.2 fun y hyB hyZ => Set.disjoint_left.1 hd (hZ k hyZ)
              (C'.boundarySheet_subset_supp_boundaryTheta i (hB hyB).1))
      rw [h0, Finset.sum_eq_zero fun i _ => ?_, mul_zero]
      rw [S.G0.msInteg_of_inter_eq_empty _ _
        (by rw [C.boundarySheet_eq_empty hd i, inter_empty]), mul_zero]
  -- linearity
  let L1 : S.Ω1 →ₗ[ℝ] ℝ :=
    { toFun := fun η => Φ' η univ
      map_add' := fun a b => by rw [map_add]; rfl
      map_smul' := fun r a => by rw [map_smul]; rfl }
  let L0 : S.Ω0 →ₗ[ℝ] ℝ :=
    { toFun := fun η => Φb' η univ
      map_add' := fun a b => by rw [map_add]; rfl
      map_smul' := fun r a => by rw [map_smul]; rfl }
  have e1 : L1 (S.j1 (A.epFormsInftyD m ω)) = ∑ k, L1 (S.v k) := by
    rw [← S.sum_v, map_sum]
  have e0 : L0 (S.j0 ω) = ∑ k, L0 (S.u k) := by
    rw [← S.sum_u, map_sum]
  rw [← step1, ← step3]
  change L1 (S.j1 (A.epFormsInftyD m ω)) = L0 (S.j0 ω)
  rw [e1, e0]
  exact Finset.sum_congr rfl fun k _ => step2 k

/-! ### Theorems 9.5.17 and 9.5.18 -/

open scoped Classical in
/-- **Theorem 9.5.17 (Stokes), 2021 p. 449, with Remark 9.5.19, p. 451**: `Θ` a compact branched
ep⁺-subgroupoid, oriented by `T̂Θ = T`, tame (`hloc`), of dimension `m + 1`, `m ≥ 1`, and
`ω ∈ Ωᵐ_{ep,∞}(X)` with systems of pieces `β_k ω` near `supp Θ` subordinate to every family of
open neighbourhoods `N(x)` of the points of `supp Θ`:
`∫_Θ̂ dω = ∫_{∂S} ω dμ^{∂Θ̂} = μ^{∂Θ̂}_ω(∂S)`. -/
theorem stokes_of_localFormSystems (hm : 0 < m) (hΘ : A.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : A.X.IsCompactBranched Θ) (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T)
    (ω : A.epFormsInfty m)
    (hsys : ∀ N : A.Obj → Set A.Obj, (∀ x ∈ supp Θ, IsOpen (N x) ∧ x ∈ N x) →
      Nonempty (A.LocalFormSystem m Θ N ω)) :
    (A.epFormsInftyEval (m + 1)).tameBranchedIntegral (Nat.succ_pos m) hΘ hcpt hT hloc
        (A.epFormsInftyD m ω) =
      A.boundaryMeasure hm hΘ hcpt hT hloc ω univ := by
  have hnd : A.X.IsNDimensional Θ (m + 1) := FormEval.isNDimensional_of_loc hloc
  have hex : ∀ x (_ : x ∈ supp Θ), ∃ C : A.X.OrientedTameStructure (m + 1) Θ x,
      C.Represents T ∧ (∀ i, IsChartBounded A.X (m + 1) (C.M i)) ∧
      (∀ i, IsBoundedBoundary A.X Θ m (C.boundarySheet i)) ∧
      (x ∈ supp (A.X.boundaryTheta Θ) ∨
        Disjoint (A.X.π ⁻¹' (A.X.π '' C.U)) (supp (A.X.boundaryTheta Θ))) := fun x hx => by
    obtain ⟨C₀, hC₀⟩ := hloc x hx
    obtain ⟨C, h1, h2, h3, h4, -, -⟩ := C₀.exists_restrict_all hΘ hcpt hnd hC₀
    exact ⟨C, h1, h2, h3, h4⟩
  choose Cx hCT hCS hCB hCd using hex
  let N : A.Obj → Set A.Obj := fun x => if h : x ∈ supp Θ then (Cx x h).U else univ
  obtain ⟨S⟩ := hsys N fun x hx => by
    simp only [N, dif_pos hx]
    exact ⟨(Cx x hx).isOpen_U, (Cx x hx).mem_U⟩
  have hZ : ∀ k, S.Z k ⊆ A.X.π ⁻¹' (A.X.π '' (Cx (S.pt k) (S.pt_mem k)).U) := fun k => by
    have h := S.Z_subset k
    simp only [N, dif_pos (S.pt_mem k)] at h
    exact h
  set F := A.epFormsInftyEval (m + 1) with hFdef
  have hcov := F.hcov_of_loc hloc
  have hcov1 : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x,
      (∀ i, C.M i ∈ S.F1.sheets) ∧ C.Represents T := fun x hx =>
    ⟨Cx x hx, fun i => (hCS x hx i).mem_sheets S.F1, hCT x hx⟩
  have hcovB1 : ∀ x ∈ supp (A.X.boundaryTheta Θ),
      ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T ∧
        ∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ S.G0.msheets := fun x hx =>
    ⟨Cx x (A.X.supp_boundaryTheta_subset Θ hx).2, hCT x _, fun i hne =>
      S.mem_msheets_of_isBoundedBoundary (hCB x _ i) hne⟩
  obtain ⟨Φb', hΦb', -⟩ := theorem_9_5_15_msheets S.G0 hm hΘ hcpt hnd hT hcovB1
  exact A.stokes_of_localFormSystem hm hΘ hcpt (fun x => (Nat.card (A.X.Isotropy x) : ℝ)⁻¹)
    (fun _ _ => True) Cx hCT hCS hCB hCd (fun _ _ => trivial) S hZ
    (branchedMeasure (F.sheetIntegration (Nat.succ_pos m)) hΘ hcpt hT hcov)
    (fun η x C hS hC _ K hK hKU => branchedMeasure_apply (F.sheetIntegration (Nat.succ_pos m))
      hΘ hcpt hT hcov η C hS hC hK hKU)
    (A.boundaryMeasure hm hΘ hcpt hT hloc)
    (fun ω x C hC hx hS _ K hK hKU =>
      A.boundaryMeasure_spec hm hΘ hcpt hT hloc ω x C hC hx hS K hK hKU)
    (branchedMeasure (S.F1.sheetIntegration (Nat.succ_pos m)) hΘ hcpt hT hcov1)
    (fun η x C hS hC _ K hK hKU => branchedMeasure_apply
      (S.F1.sheetIntegration (Nat.succ_pos m)) hΘ hcpt hT hcov1 η C hS hC hK hKU)
    Φb' (fun ω x C hC hx hS _ K hK hKU => hΦb' ω x C hC hx hS K hK hKU)

open scoped Classical in
/-- **Theorem 9.5.18 (effective Stokes), 2021 p. 450, with Remark 9.5.19, p. 451**: as
`stokes_of_localFormSystems` for `X` with the local unique continuation property,
`∮_Θ̂ dω = ∮_{∂S} ω dμ^{∂Θ̂} = μ^{∂Θ̂,eff}_ω(∂S)`. -/
theorem stokesEff_of_localFormSystems (hm : 0 < m) (hLUC : A.X.IsLUC)
    (hΘ : A.X.IsBranchedEpSubgroupoid Θ) (hcpt : A.X.IsCompactBranched Θ)
    (hT : A.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T)
    (ω : A.epFormsInfty m)
    (hsys : ∀ N : A.Obj → Set A.Obj, (∀ x ∈ supp Θ, IsOpen (N x) ∧ x ∈ N x) →
      Nonempty (A.LocalFormSystem m Θ N ω)) :
    (A.epFormsInftyEval (m + 1)).tameBranchedIntegralEff (Nat.succ_pos m) hΘ hcpt hT
        (A.hloc_hasLUC hLUC hloc) (A.epFormsInftyD m ω) =
      A.boundaryMeasureEff hm hLUC hΘ hcpt hT hloc ω univ := by
  have hnd : A.X.IsNDimensional Θ (m + 1) := FormEval.isNDimensional_of_loc hloc
  have hL : ∀ x (C : A.X.OrientedTameStructure (m + 1) Θ x), C.rep.HasLUC := fun x C =>
    A.X.isLUC_iff_forall_naturalRep.1 hLUC x C.rep
  have hex : ∀ x (_ : x ∈ supp Θ), ∃ C : A.X.OrientedTameStructure (m + 1) Θ x,
      C.Represents T ∧ (∀ i, IsChartBounded A.X (m + 1) (C.M i)) ∧
      (∀ i, IsBoundedBoundary A.X Θ m (C.boundarySheet i)) ∧
      (x ∈ supp (A.X.boundaryTheta Θ) ∨
        Disjoint (A.X.π ⁻¹' (A.X.π '' C.U)) (supp (A.X.boundaryTheta Θ))) := fun x hx => by
    obtain ⟨C₀, hC₀⟩ := hloc x hx
    obtain ⟨C, h1, h2, h3, h4, -, -⟩ := C₀.exists_restrict_all hΘ hcpt hnd hC₀
    exact ⟨C, h1, h2, h3, h4⟩
  choose Cx hCT hCS hCB hCd using hex
  let N : A.Obj → Set A.Obj := fun x => if h : x ∈ supp Θ then (Cx x h).U else univ
  obtain ⟨S⟩ := hsys N fun x hx => by
    simp only [N, dif_pos hx]
    exact ⟨(Cx x hx).isOpen_U, (Cx x hx).mem_U⟩
  have hZ : ∀ k, S.Z k ⊆ A.X.π ⁻¹' (A.X.π '' (Cx (S.pt k) (S.pt_mem k)).U) := fun k => by
    have h := S.Z_subset k
    simp only [N, dif_pos (S.pt_mem k)] at h
    exact h
  set F := A.epFormsInftyEval (m + 1) with hFdef
  have hcov := F.hcovEff_of_loc (A.hloc_hasLUC hLUC hloc)
  have hcov1 : ∀ x ∈ supp Θ, ∃ C : A.X.OrientedTameStructure (m + 1) Θ x,
      (∀ i, C.M i ∈ S.F1.sheets) ∧ C.Represents T ∧ C.rep.HasLUC := fun x hx =>
    ⟨Cx x hx, fun i => (hCS x hx i).mem_sheets S.F1, hCT x hx, hL x _⟩
  have hcovB1 : ∀ x ∈ supp (A.X.boundaryTheta Θ),
      ∃ C : A.X.OrientedTameStructure (m + 1) Θ x, C.Represents T ∧
        (∀ i, (C.boundarySheet i).Nonempty → C.boundarySheet i ∈ S.G0.msheets) ∧
        C.rep.HasLUC := fun x hx =>
    ⟨Cx x (A.X.supp_boundaryTheta_subset Θ hx).2, hCT x _, fun i hne =>
      S.mem_msheets_of_isBoundedBoundary (hCB x _ i) hne, hL x _⟩
  obtain ⟨Φb', hΦb', -⟩ := theorem_9_5_16_msheets S.G0 hm hΘ hcpt hnd hT hcovB1
  exact A.stokes_of_localFormSystem hm hΘ hcpt
    (fun x => (Nat.card (A.X.EffIsotropy x) : ℝ)⁻¹) (fun _ C => C.rep.HasLUC) Cx hCT hCS hCB
    hCd (fun x _ => hL x _) S hZ
    (branchedMeasureEff (F.sheetIntegration (Nat.succ_pos m)) hΘ hcpt hT hcov)
    (fun η x C hS hC hP K hK hKU => branchedMeasureEff_apply
      (F.sheetIntegration (Nat.succ_pos m)) hΘ hcpt hT hcov η C hS hC hP hK hKU)
    (A.boundaryMeasureEff hm hLUC hΘ hcpt hT hloc)
    (theorem_9_5_16_msheets (A.epFormsInftyEval m) hm hΘ hcpt
      (FormEval.isNDimensional_of_loc (A.hcovS_of_loc_isLUC hm hLUC hΘ hcpt hloc)) hT
      (fun x hx => ((A.hcovS_of_loc_isLUC hm hLUC hΘ hcpt hloc) x
        (A.X.supp_boundaryTheta_subset Θ hx).2).imp
        fun _ h => ⟨h.1, h.2.2.1, h.2.2.2⟩)).exists.choose_spec
    (branchedMeasureEff (S.F1.sheetIntegration (Nat.succ_pos m)) hΘ hcpt hT hcov1)
    (fun η x C hS hC hP K hK hKU => branchedMeasureEff_apply
      (S.F1.sheetIntegration (Nat.succ_pos m)) hΘ hcpt hT hcov1 η C hS hC hP hK hKU)
    Φb' hΦb'

end EP

end Polyfold
