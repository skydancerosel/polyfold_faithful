import Polyfold.Chapter15.RelativeSeeds
import Polyfold.Chapter15.ChargedExtensionFibres
import Polyfold.Chapter15.GlueStructurable
import Polyfold.Chapter15.CylinderCobordism

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, **Theorem 15.3.9
(Transversal Extension Theorem)**, p. 694 (2017: Theorem 15.5), and its proof, steps (c)–(d),
pp. 698–699; **Corollary 15.3.10 (1), (3)**, p. 699.

# The relative local families and Theorem 15.3.9

## The text, paraphrased

Step (c): by the hypothesis on the boundary data, `(f, Λ₀)` is in general position at the points
of `supp(Λ₀ ∘ f) ∩ ∂X`, hence near them.  Step (d): away from `∂X` one argues as in Theorem
15.3.7, with parameter families whose domain support avoids `∂X`, and takes
`Λ̃ = Λ_t ⊕ Λ₀` for a small regular `t`.

## What is formalized (namespace `Polyfold.SBLocalization`)

* **`exists_isOpen_isReducedOntoAtPt`** (step (c)): general position of `(f, Λ₀)` at a point is
  open along `supp(Λ₀ ∘ f)`, on a saturated open neighbourhood.  *Proof*: the local Sard step
  relative to `Λ₀` (`exists_local_paramGP_rel`) for the family without parameters; a null set in
  `ℝ⁰` is empty.
* **`relative_local_families_holds`**: `relative_local_families_statement A` for every `A`: at
  boundary points of the support the empty family on that neighbourhood, at the other points the
  atomic families of the seeds (`exists_relGPFamily_of_seeds`, `hasLocalParamSeedsRel`).
* **`theorem_15_3_7_relative`**: steps (c)–(d), `theorem_15_3_7_relative_statement A`.
* **`theorem_15_3_9`**: Theorem 15.3.9, `theorem_15_3_9_statement A`, with no added hypothesis.
* **`corollary_15_3_10_1`**: Corollary 15.3.10 (1) (Theorem 15.3.7 for paracompact `|X|`).
* `corollary_15_3_10_3_of_face_onto`, `corollary_15_4_4_of_glue_or`: Corollary 15.3.10 (3) and
  Corollary 15.4.4 with Theorem 15.3.9 on `[0, 1] × X` proved.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP OrientedRegularPerturbation

variable {A : SEP.{u}}

/-! ### Step (c): general position is open along the support -/

/-- A Lebesgue null set in `ℝ⁰` is empty. -/
theorem notMem_of_volume_eq_zero_fin_zero {CV : Set (Fin 0 → ℝ)} (h : volume CV = 0)
    (t : Fin 0 → ℝ) : t ∉ CV := by
  intro ht
  have e : CV = univ := eq_univ_of_forall fun t' => by rwa [Subsingleton.elim t' t]
  rw [e, volume_pi, Measure.pi_of_empty, measure_univ] at h
  exact one_ne_zero h

/-- **Step (c) of the proof of Theorem 15.3.9: general position of `(f, Λ₀)` is open along
`supp(Λ₀ ∘ f)`**: for tame `X`, an sc-Fredholm section functor `f` with tame germ data and an
sc⁺-multisection `Λ₀`, if every operator of `T(f, Λ₀)(x)` is onto on `T^R_xX`, the same holds at
every point of `supp(Λ₀ ∘ f)` in a saturated open neighbourhood of `x`. -/
theorem exists_isOpen_isReducedOntoAtPt (hX : A.X.IsTame) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {Λ₀ : A.W → ℚ≥0} (hΛ₀ : IsScPlusMultisection A Λ₀) {x : A.Obj}
    (hx1 : x ∈ A.X.PObj.levelSet 1)
    (hred : IsReducedOntoAtPt f Λ₀ (A.X.PObj.levelMk 1 x hx1)) :
    ∃ Q : Set A.Obj, IsOpen Q ∧ A.X.IsSaturated Q ∧ x ∈ Q ∧ ∀ y : A.X.PObj.Level 1,
      A.X.PObj.levelVal 1 y ∈ Q → 0 < Λ₀ (f (A.X.PObj.levelVal 1 y)) →
        IsReducedOntoAtPt f Λ₀ y := by
  have hon : IsParamOntoAtRel f Λ₀ (fun _ : Fin 0 → ℝ => zeroMultisection A)
      (A.X.PObj.levelMk 1 x hx1) := IsParamOntoAtRel.of_reducedOnto hred isLinearFamily_zero
  obtain ⟨V, hVo, hxV, δ, hδ, CV, hCV, hgp⟩ := exists_local_paramGP_rel hX hf hft hΛ₀
    (fun _ => isScPlusMultisection_zeroMultisection A) hon
  rw [A.X.PObj.levelVal_levelMk] at hxV
  have e : multisectionAdd Λ₀ (zeroMultisection A) = Λ₀ := multisectionAdd_zeroMultisection hΛ₀
  have hV : ∀ y ∈ V, 0 < Λ₀ (f y) → IsInGeneralPositionAt f Λ₀ y := by
    intro y hy hpos
    have h := hgp 0 (by rw [norm_zero]; exact hδ) (notMem_of_volume_eq_zero_fin_zero hCV 0) y hy
    rw [e] at h
    exact h hpos
  refine ⟨A.X.saturation V, EpGroupoid.isOpen_saturation_of_isOpen A.X hVo,
    EpGroupoid.isSaturated_saturation A.X V, A.X.subset_saturation V hxV, fun y hy hpos => ?_⟩
  obtain ⟨a, haV, ha⟩ := hy
  obtain ⟨φ, hφs, hφt⟩ := A.X.π_eq_π_iff.1 ha
  have hpa : 0 < Λ₀ (f (A.X.src φ)) := by
    rw [← comp_tgt_eq_src hf hΛ₀ φ, hφt]; exact hpos
  obtain ⟨hy1, hr⟩ := isInGeneralPositionAt_of_mor hf hΛ₀ φ (hV _ (hφs ▸ haV) hpa)
  have ey : A.X.PObj.levelMk 1 (A.X.tgt φ) hy1 = y :=
    A.X.PObj.levelVal_injective 1 (by rw [A.X.PObj.levelVal_levelMk, hφt])
  rw [ey] at hr
  exact hr

/-! ### Steps (c)–(d) and Theorem 15.3.9 -/

/-- **The relative local families of the proof of Theorem 15.3.9 (steps (c)–(d), pp. 698–699)
exist**: `relative_local_families_statement A` holds for every `A`.  At the points of
`supp(Λ₀ ∘ f) ∩ ∂X` the family without parameters, on a neighbourhood where `(f, Λ₀)` is in
general position (`exists_isOpen_isReducedOntoAtPt`); at the other points the atomic family of
seeds supported away from `∂X` (`exists_relGPFamily_of_seeds`, `hasLocalParamSeedsRel`). -/
theorem relative_local_families_holds : relative_local_families_statement A := by
  intro hX _ hPU f hf hft _ N U hcc h hc hfun hh Λ₀ hΛ₀ hdom hN hbd
  obtain ⟨D, -⟩ := hΛ₀.2
  have h𝒰 : Nonempty A.X.GoodSystem := ⟨D.𝒰⟩
  have hNB : A.B.IsAuxNorm N := hcc.1.isAuxNorm
  refine hasLocalGPFamiliesRel_of_boundary h𝒰 hNB (fun x hxb hpos => ?_)
    (exists_relGPFamily_of_seeds h𝒰 hf hcc hΛ₀.1 hdom hc hfun (fun x => (hh x).2) hN
      (hasLocalParamSeedsRel hX hPU.admitsBumpFunctions hf hft hΛ₀.1 hNB))
  have hx1 := mem_levelSet_one_of_pos hf hΛ₀.1 hpos
  exact exists_isOpen_isReducedOntoAtPt hX hf hft hΛ₀.1 hx1
    (hbd _ (by rw [A.X.PObj.levelVal_levelMk]; exact hxb)
      (by rw [A.X.PObj.levelVal_levelMk]; exact hpos))

/-- **Steps (c)–(d) of the proof of Theorem 15.3.9 (pp. 698–699)**: the relative form of the
general position theorem, `theorem_15_3_7_relative_statement A`, for every `A`. -/
theorem theorem_15_3_7_relative : theorem_15_3_7_relative_statement A :=
  theorem_15_3_7_relative_of_local relative_local_families_holds

/-- **2021 Theorem 15.3.9 (Transversal Extension Theorem), p. 694 (2017: Theorem 15.5)**:
`theorem_15_3_9_statement A` for every `A`.  Let `X` be tame with paracompact `|X|` and sc-smooth
partitions of unity, `f` an sc-Fredholm section functor (with tame germ data) with compact
`|S_f|`, `(N, U)` controlling compactness, `Λ : W|∂X → ℚ⁺` structurable with domain support in
`U` and `N(Λ) < h` on `∂X` for a continuous functor `h : X → (0, 1]`, and `T(f|∂X, Λ)` onto with
respect to the intersections of local faces at the smooth points of `∂X`.  Then there is a
structurable `Λ̃` with `Λ̃ = Λ` over `∂X`, `dom-supp(Λ̃) ⊆ U`, `N(Λ̃) < h`, `(f, Λ̃)` transversal,
and `Λ̃ ∘ f` a compact branched ep⁺-subgroupoid. -/
theorem theorem_15_3_9 : theorem_15_3_9_statement A :=
  theorem_15_3_9_of_rel theorem_15_3_7_relative

/-! ### Corollary 15.3.10 -/

/-- **2021 Corollary 15.3.10 (1), p. 699 (2017: Corollary 15.1 (1))**: for `d_X ≡ 0`, paracompact
`|X|`, sc-smooth bump functions, `f` sc-Fredholm (with tame germ data) with compact `|S_f|` and
`(N, U)` controlling compactness, there is a structurable regular perturbation `(N, U, Λ)`; it
is in general position and `Λ ∘ f` is a compact branched ep⁺-subgroupoid. -/
theorem corollary_15_3_10_1 (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (hpara : A.X.HasParacompactOrbitSpace) (hbump : A.X.AdmitsBumpFunctionsPointwise)
    {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) (hS : A.E.HasCompactSolutionSetEp f)
    {N : A.B.One → ℝ} {U : Set A.Obj} (hcc : ControlsCompactness A f N U) :
    ∃ Λ : A.W → ℚ≥0, IsRegularPerturbation A f N U Λ ∧ IsInGeneralPosition A f Λ ∧
      A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)) ∧
      A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ)) :=
  corollary_15_3_10_1_ty (theorem_15_3_7_of_paracompact hpara) hd hpara hbump hf hft hS hcc

/-- **Corollary 15.3.10 (3), p. 699, for two structurable regular perturbations**, with
Theorem 15.3.9 on `[0, 1] × X` proved (`theorem_15_3_7_relative`): the added hypotheses are
`CubeLiftFace A` (`hF`), the face condition of the glued data (`hbonto`) and sc-smooth partitions
of unity on `X` (`hPU`). -/
theorem corollary_15_3_10_3_of_face_onto
    (hF : CubeLiftFace A) (hd : ∀ x, A.X.PObj.degIndex x = 0) (hpara : A.X.HasParacompactOrbitSpace)
    (hPU : A.X.PObj.AdmitsScPartitionsOfUnity) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hS : A.E.HasCompactSolutionSetEp f) {N₀ N₁ : A.B.One → ℝ} {U₀ U₁ : Set A.Obj}
    {Λ₀ Λ₁ : A.W → ℚ≥0} (hr₀ : IsRegularPerturbation A f N₀ U₀ Λ₀)
    (hr₁ : IsRegularPerturbation A f N₁ U₁ Λ₁)
    (hbonto : IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue Λ₀ Λ₁)) :
    ∃ Λ' : (A.cubeSEP 1).W → ℚ≥0,
      IsRegularPerturbation (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf.1.1.1)
        (interpAuxNorm A N₀ N₁) (interpSet A U₀ U₁) Λ' ∧
      (∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (cubeVal w).2) ∧
      (∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (cubeVal w).2) ∧
      (A.cubeSEP 1).X.IsBranchedEpSubgroupoid
        (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) ∧
      (A.cubeSEP 1).X.IsCompactBranched
        (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) :=
  corollary_15_3_10_3_of_rel theorem_15_3_7_relative hF hd hpara hPU hf hft hS hr₀ hr₁ hbonto

/-- **Corollary 15.4.4, p. 703, along the text's argument, with Theorem 15.3.9 on `[0, 1] × X`
proved** (`corollary_15_4_4_of_rel` with `theorem_15_3_7_relative`): what is left are partitions
of unity on the cylinder (`hPUC`), the two conditions on the glued data (`hglue`) and step (c)
(`hor`). -/
theorem corollary_15_4_4_of_glue_or
    (hd : ∀ x, A.X.PObj.degIndex x = 0) (hpara : A.X.HasParacompactOrbitSpace)
    (hPU : A.X.HasScPartitionsOfUnity) (hPUC : (A.cubeSEP 1).X.PObj.AdmitsScPartitionsOfUnity)
    {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) (hS : A.E.HasCompactSolutionSetEp f) {m : ℕ}
    (Can : OrientedRegularPerturbation A f m → Prop)
    (hglue : ∀ P₀ P₁, Can P₀ → Can P₁ →
      IsBoundaryStructurable (A.cubeSEP 1) (cubeGlue P₀.Λ P₁.Λ) ∧
        IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue P₀.Λ P₁.Λ))
    (hor : ∀ P₀ P₁, Can P₀ → Can P₁ → CylinderOrientationStatement hf.1.1.1 P₀ P₁) :
    corollary_15_4_4_statement A f m Can :=
  corollary_15_4_4_of_rel theorem_15_3_7_relative hd hpara hPU hPUC hf hft hS Can hglue hor

end SBLocalization

end Polyfold
