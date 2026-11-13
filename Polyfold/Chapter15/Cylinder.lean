import Polyfold.Chapter15.RegularPerturbations
import Polyfold.Chapter5.DegeneracyZeroTame

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, p. 699:
**Corollary 15.3.10 (1), (3)** with fewer added hypotheses (gaps TX-5, TX-7): the cylinder
`[0, 1] × X` has a paracompact orbit space, `d_X ≡ 0` makes `X` tame, and the boundary data of
TX's `corollary_15_3_10_3_hyp` are satisfiable.

# The cylinder `[0, 1] × X`

## What is formalized

* `EpGroupoid.cubeOrbitHomeomorph`: `[0, 1]ⁿ × |X| ≃ₜ |[0, 1]ⁿ × X|` (P's `cubeOrbitMap` is a
  continuous open bijection), and **`EpGroupoid.hasParacompactOrbitSpace_cubeProd`**:
  `|[0, 1]ⁿ × X|` is paracompact if `|X|` is (compact × paracompact).
* `SBLocalization.isReducedOntoAtPt_of_injective`, `isBoundaryFaceOnto_of_injective`: when
  `P : W → X` is injective (fibres `0`), every operator of `T(f, Λ)(x)` is onto.
  `injective_cubeSEP_P`, `injective_epSEP_zero_P`.
* **`corollary_15_3_10_1_ty`**: Corollary 15.3.10 (1) from Theorem 15.3.7 without the
  hypothesis "`X` tame" (it follows from `d_X ≡ 0`, `EpGroupoid.isTame_of_degIndex_eq_zero`).
* **`corollary_15_3_10_3_ty`**: TX's Corollary 15.3.10 (3) without "`X` tame" and with the
  paracompactness of `|[0, 1] × X|` derived from that of `|X|` (a hypothesis of the corollary).
* **`corollary_15_3_10_3_boundary_witness`**: on `ℝⁿ × ℝ⁰ → ℝⁿ` (`epSEP n 0`), for every section
  `f` and all auxiliary norms `N⁰, N¹` and open `U⁰, U¹`, the boundary data `Λ_∂ = Λ⁰ = Λ¹ = 0`
  satisfy all hypotheses of `corollary_15_3_10_3_hyp` on `Λ_∂` (and `X` is tame, `d_X ≡ 0`,
  `|[0, 1] × X|` paracompact): these hypotheses are satisfiable together;
  `admitsScPartitionsOfUnity_cube_rn`: `[0, 1] × ℝⁿ` admits sc-smooth partitions of unity
  (the hypothesis `hPUC` there).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

/-! ### The orbit space of `[0, 1]ⁿ × X` -/

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
  (n : ℕ) [ParacompactSpace ((Fin n → unitInterval) × Obj)]
  [ParacompactSpace ((Fin n → unitInterval) × Mor)]

theorem injective_cubeOrbitMap : Injective (X.cubeOrbitMap n) := by
  rintro ⟨q, a⟩ ⟨q', a'⟩ h
  obtain ⟨x, rfl⟩ := X.surjective_π a
  obtain ⟨x', rfl⟩ := X.surjective_π a'
  have h' : (X.cubeProd n).π (q, x) = (X.cubeProd n).π (q', x') := h
  rw [cubeProd_π_eq_π_iff] at h'
  exact Prod.ext h'.1 h'.2

theorem surjective_cubeOrbitMap : Surjective (X.cubeOrbitMap n) := by
  intro o
  obtain ⟨⟨q, x⟩, rfl⟩ := (X.cubeProd n).surjective_π o
  exact ⟨(q, X.π x), rfl⟩

theorem isOpenMap_cubeOrbitMap : IsOpenMap (X.cubeOrbitMap n) := by
  intro O hO
  have e : X.cubeOrbitMap n '' O =
      (X.cubeProd n).π '' (Prod.map id X.π ⁻¹' O) := by
    ext o
    constructor
    · rintro ⟨⟨q, a⟩, hp, rfl⟩
      obtain ⟨x, rfl⟩ := X.surjective_π a
      exact ⟨(q, x), hp, rfl⟩
    · rintro ⟨⟨q, x⟩, hp, rfl⟩
      exact ⟨(q, X.π x), hp, rfl⟩
  rw [e]
  exact (X.cubeProd n).proposition_7_1_8 _
    (hO.preimage (continuous_id.prodMap X.continuous_π))

/-- **`[0, 1]ⁿ × |X| ≃ₜ |[0, 1]ⁿ × X|`**, `(q, |x|) ↦ |(q, x)|`. -/
def cubeOrbitHomeomorph : (Fin n → unitInterval) × X.OrbitSpace ≃ₜ (X.cubeProd n).OrbitSpace :=
  Equiv.toHomeomorphOfContinuousOpen
    (Equiv.ofBijective _ ⟨X.injective_cubeOrbitMap n, X.surjective_cubeOrbitMap n⟩)
    (X.continuous_cubeOrbitMap n) (X.isOpenMap_cubeOrbitMap n)

/-- **`|[0, 1]ⁿ × X|` is paracompact if `|X|` is** (`[0, 1]ⁿ` is compact). -/
theorem hasParacompactOrbitSpace_cubeProd (h : X.HasParacompactOrbitSpace) :
    (X.cubeProd n).HasParacompactOrbitSpace := by
  have : ParacompactSpace X.OrbitSpace := h
  exact (X.cubeOrbitHomeomorph n).paracompactSpace_iff.1 inferInstance

end EpGroupoid

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP

variable {A : SEP.{u}}

/-! ### Bundles with fibres `0` -/

/-- If `P : W → X` is injective (all fibres are `0`), every operator onto a fibre is onto. -/
theorem isReducedOntoAtPt_of_injective (hP : Injective A.P) (f : A.Obj → A.W)
    (Λ : A.W → ℚ≥0) (x : A.X.PObj.Level 1) : IsReducedOntoAtPt f Λ x := by
  intro L _ φ hφ hx k V T _ w
  refine ⟨0, Subtype.ext (hP ?_)⟩
  have h1 := ((L.domRestrict (reducedTangentFiber hφ hx T)) 0).2
  have h2 := w.2
  exact h1.trans h2.symm

theorem isBoundaryFaceOnto_of_injective (hP : Injective A.P) (f : A.Obj → A.W)
    (Λ : A.W → ℚ≥0) : IsBoundaryFaceOnto f Λ :=
  fun Λ' _ _ x _ _ _ => isReducedOntoAtPt_of_injective hP f Λ' x

theorem zeroMultisection_eq_one_of_injective (hP : Injective A.P) (w : A.W) :
    zeroMultisection A w = 1 := by
  unfold zeroMultisection
  rw [if_pos (hP (proj_fiberZero A.P (A.P w)).symm)]

theorem injective_cubeSEP_P {n : ℕ} (hP : Injective A.P) : Injective (A.cubeSEP n).P := by
  intro w w' h
  have h1 : (cubeVal w).1 = (cubeVal w').1 := h
  have hw : A.P (cubeVal w).2 = (cubeVal w).1.2 :=
    (show pullbackSpace A.P (Prod.snd : (Fin n → unitInterval) × A.Obj → A.Obj) from w).2
  have hw' : A.P (cubeVal w').2 = (cubeVal w').1.2 :=
    (show pullbackSpace A.P (Prod.snd : (Fin n → unitInterval) × A.Obj → A.Obj) from w').2
  have h2 : (cubeVal w).2 = (cubeVal w').2 := hP (by rw [hw, hw', h1])
  exact Subtype.ext (Prod.ext h1 h2)

theorem injective_epSEP_zero_P (n : ℕ) :
    Injective (StrongBundleEquivalenceExamples.epSEP n 0).P := by
  intro w w' h
  exact Prod.ext h (funext fun i => i.elim0)

/-! ### Corollary 15.3.10 (1) and (3) without "`X` tame" -/

/-- **Corollary 15.3.10 (1), p. 699, from Theorem 15.3.7**, with the hypotheses of the corollary
(`d_X ≡ 0`, paracompact `|X|`, `f` sc-Fredholm with compact `|S_f|`, `(N, U)` controlling
compactness) and those Theorem 15.3.7 adds (sc-smooth bump functions, tame germ data of `f`);
TX's hypothesis "`X` tame" is dropped: it follows from `d_X ≡ 0`. -/
theorem corollary_15_3_10_1_ty (h157 : theorem_15_3_7_statement A)
    (hd : ∀ x, A.X.PObj.degIndex x = 0) (hpara : A.X.HasParacompactOrbitSpace)
    (hbump : A.X.AdmitsBumpFunctionsPointwise) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hS : A.E.HasCompactSolutionSetEp f) {N : A.B.One → ℝ} {U : Set A.Obj}
    (hcc : ControlsCompactness A f N U) :
    ∃ Λ : A.W → ℚ≥0, IsRegularPerturbation A f N U Λ ∧ IsInGeneralPosition A f Λ ∧
      A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)) ∧
      A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ)) :=
  corollary_15_3_10_1_hyp h157 hd hpara (A.X.isTame_of_degIndex_eq_zero hd) hbump hf hft hS hcc

/-- **Corollary 15.3.10 (3), p. 699, from Theorem 15.3.9 on `[0, 1] × X`**: TX's
`corollary_15_3_10_3_hyp` with "`X` tame" derived from `d_X ≡ 0` and the paracompactness of
`|[0, 1] × X|` derived from that of `|X|`.  The boundary data `Λ_∂` remain hypotheses (TX-4);
they are satisfiable, `corollary_15_3_10_3_boundary_witness`. -/
theorem corollary_15_3_10_3_ty (h159 : theorem_15_3_9_statement (A.cubeSEP 1))
    (hd : ∀ x, A.X.PObj.degIndex x = 0) (hpara : A.X.HasParacompactOrbitSpace)
    (hPUC : (A.cubeSEP 1).X.PObj.AdmitsScPartitionsOfUnity) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hS : A.E.HasCompactSolutionSetEp f) {N₀ N₁ : A.B.One → ℝ} {U₀ U₁ : Set A.Obj}
    (h₀ : ControlsCompactness A f N₀ U₀) (h₁ : ControlsCompactness A f N₁ U₁)
    {Λ₀ Λ₁ : A.W → ℚ≥0} (Λb : (A.cubeSEP 1).W → ℚ≥0)
    (hb₀ : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λb w = Λ₀ (cubeVal w).2)
    (hb₁ : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λb w = Λ₁ (cubeVal w).2)
    (hbs : IsBoundaryStructurable (A.cubeSEP 1) Λb)
    (hbdom : boundaryDomSupp Λb ⊆ interpSet A U₀ U₁)
    (hbN : ∀ z ∈ (A.cubeSEP 1).X.PObj.boundary, pointwiseNorm (interpAuxNorm A N₀ N₁) Λb z < 1)
    (hbonto : IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) Λb) :
    ∃ Λ' : (A.cubeSEP 1).W → ℚ≥0,
      IsRegularPerturbation (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf.1.1.1)
        (interpAuxNorm A N₀ N₁) (interpSet A U₀ U₁) Λ' ∧
      (∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (cubeVal w).2) ∧
      (∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (cubeVal w).2) ∧
      (A.cubeSEP 1).X.IsBranchedEpSubgroupoid
        (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) ∧
      (A.cubeSEP 1).X.IsCompactBranched
        (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PMor
  exact corollary_15_3_10_3_hyp h159 (A.X.isTame_of_degIndex_eq_zero hd) hd
    (A.X.hasParacompactOrbitSpace_cubeProd 1 hpara) hPUC hf hft hS h₀ h₁ Λb hb₀ hb₁ hbs hbdom
    hbN hbonto

/-! ### The boundary data are satisfiable -/

/-- **Witness for the boundary hypotheses of Corollary 15.3.10 (3)** (TX-5): on `ℝⁿ × ℝ⁰ → ℝⁿ`
(`epSEP n 0`, tame, `d_X ≡ 0`, `|[0, 1] × X|` paracompact), for every section `f`, all
auxiliary norms `N⁰, N¹` and all `U⁰, U¹`, the multisections `Λ_∂ = Λ⁰ = Λ¹ = 0` satisfy every
hypothesis that `corollary_15_3_10_3_hyp` puts on `Λ_∂`. -/
theorem corollary_15_3_10_3_boundary_witness (n : ℕ)
    (f : (StrongBundleEquivalenceExamples.epSEP n 0).Obj →
      (StrongBundleEquivalenceExamples.epSEP n 0).W)
    (hf : IsSection (StrongBundleEquivalenceExamples.epSEP n 0).P f)
    {N₀ N₁ : (StrongBundleEquivalenceExamples.epSEP n 0).B.One → ℝ}
    (hN₀ : (StrongBundleEquivalenceExamples.epSEP n 0).E.IsAuxNorm N₀)
    (hN₁ : (StrongBundleEquivalenceExamples.epSEP n 0).E.IsAuxNorm N₁)
    (U₀ U₁ : Set (StrongBundleEquivalenceExamples.epSEP n 0).Obj) :
    let A := StrongBundleEquivalenceExamples.epSEP n 0
    let Λb := zeroMultisection (A.cubeSEP 1)
    A.X.IsTame ∧ (∀ x, A.X.PObj.degIndex x = 0) ∧ (A.cubeSEP 1).X.HasParacompactOrbitSpace ∧
    (∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λb w = zeroMultisection A (cubeVal w).2) ∧
    (∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λb w = zeroMultisection A (cubeVal w).2) ∧
    IsBoundaryStructurable (A.cubeSEP 1) Λb ∧ boundaryDomSupp Λb ⊆ interpSet A U₀ U₁ ∧
    (∀ z ∈ (A.cubeSEP 1).X.PObj.boundary, pointwiseNorm (interpAuxNorm A N₀ N₁) Λb z < 1) ∧
    IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf) Λb := by
  intro A Λb
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PMor
  have hX : A.X.IsTame := EpGroupoid.isTame_trivial_rn n
  have hd : ∀ x, A.X.PObj.degIndex x = 0 := EpGroupoid.degIndex_rnPolyfold_trivial n
  have hparaC : (A.cubeSEP 1).X.HasParacompactOrbitSpace :=
    A.X.hasParacompactOrbitSpace_cubeProd 1
      (EpGroupoid.hasParacompactOrbitSpace_trivial (rnPolyfold n))
  have hP : Injective A.P := injective_epSEP_zero_P n
  have hPC : Injective (A.cubeSEP 1).P := injective_cubeSEP_P hP
  have hN := isAuxNorm_interpAuxNorm hN₀ hN₁
  refine ⟨hX, hd, hparaC, fun w _ => ?_, fun w _ => ?_,
    isBoundaryStructurable_zero (A.X.isTame_cubeProd 1 hX) hparaC, ?_, fun z _ => ?_,
    isBoundaryFaceOnto_of_injective hPC _ _⟩
  · change zeroMultisection (A.cubeSEP 1) w = _
    rw [zeroMultisection_eq_one_of_injective hPC, zeroMultisection_eq_one_of_injective hP]
  · change zeroMultisection (A.cubeSEP 1) w = _
    rw [zeroMultisection_eq_one_of_injective hPC, zeroMultisection_eq_one_of_injective hP]
  · change boundaryDomSupp (zeroMultisection (A.cubeSEP 1)) ⊆ _
    rw [boundaryDomSupp_zero]; exact empty_subset _
  · change pointwiseNorm _ (zeroMultisection (A.cubeSEP 1)) z < 1
    rw [pointwiseNorm_zeroMultisection hN.isAuxNorm]; norm_num

/-- **`[0, 1] × ℝⁿ` admits sc-smooth partitions of unity** (Theorem 5.5.10 with the product
charts `chart b × id`, whose finite-dimensional models have the approximation property,
Proposition 5.5.11): the hypothesis `hPUC` of `corollary_15_3_10_3_ty` holds on `epSEP n 0`. -/
theorem admitsScPartitionsOfUnity_cube_rn (n : ℕ) :
    ((StrongBundleEquivalenceExamples.epSEP n 0).cubeSEP 1).X.PObj.AdmitsScPartitionsOfUnity := by
  change ((cubePolyfold 1).prod (rnPolyfold n)).AdmitsScPartitionsOfUnity
  refine theorem_5_5_10.2 ⟨{χ | ∃ b, χ = (UnitCube.chart b).prod (rnChart n 0)}, ?_, fun p =>
    ⟨_, ⟨UnitCube.corner p.1, rfl⟩, UnitCube.mem_chart_corner p.1, mem_univ p.2⟩, ?_⟩
  · rintro _ ⟨b, rfl⟩
    exact (UnitCube.isChart_chart b).prod (isChart_rnChart 0)
  · rintro _ ⟨b, rfl⟩
    have : FiniteDimensional ℝ (((UnitCube.chart b).prod (rnChart n 0)).model.E 0) := by
      change FiniteDimensional ℝ ((Fin 1 → ℝ) × (Fin n → ℝ))
      infer_instance
    exact proposition_5_5_11 _ (admitsContDiffPartitionsOfUnity_of_finiteDimensional _)

end SBLocalization

end Polyfold
