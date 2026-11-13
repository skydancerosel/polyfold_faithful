import Polyfold.Chapter15.LocalFamilies

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, proof of
**Theorem 15.3.7** (General Position; 2017: Theorem 15.4), pp. 694–696: the seeds of the local
constructions from a pointwise choice and the openness of (15.1).

# The seeds `s¹_j` of the local constructions

## The text, paraphrased

At `x ∈ S_f` the proof takes finitely many smooth `w_j ∈ W_x` with
`f'(x)(T^R_xX) + span{w_j} = W_x` (possible since `f'(x)` is sc-Fredholm and `T^R_xX` has finite
codimension), sc⁺-sections `s¹_j` with `s¹_j(x) = w_j`, supported near `x` and small (Part I's
Lemma 5.3.3), and then uses that the parametrized surjectivity (15.1) persists at the points of
`S_f` near `x`.

## What is formalized (namespace `Polyfold.SBLocalization`)

* **`HasPointwiseParamOnto A f N`**: at every `x ∈ S_f` and for every `ε > 0` there are finitely
  many smooth `w_j ∈ W_x` with `N(w_j) < ε` and (15.1) at `x` with the vectors `w_j` (the
  Fredholm linear algebra at one point).
* **`HasParamOntoOpen A f`**: for sc⁺-sections `s_j` with (15.1) at `x ∈ S_f` with the vectors
  `s_j(x)`, (15.1) with `s_j(y)` holds at every `y ∈ S_f` near `x` (the openness of the
  parametrized reduced surjectivity along the solution set).
* **`hasLocalParamSeeds_of`**: the two give `HasLocalParamSeeds` (bump functions, Part I's
  Lemma 5.3.3, smooth solutions).
* **`theorem_15_3_7_of_pointwise`**: Theorem 15.3.7 (`theorem_15_3_7_statement`) from a good
  system, `HasPointwiseParamOnto`, `HasParamOntoOpen` and GP's
  `HasParametricGeneralPosition`, under the hypotheses of the theorem (tame germ data gives
  `S_f ⊆ X_∞`, L's `mem_smoothSet_of_eq`).
* Witnesses on `ℝⁿ × ℝ⁰ → ℝⁿ`: `isParamOntoVec_epSEP_zero`,
  `hasPointwiseParamOnto_epSEP_zero`, `hasParamOntoOpen_epSEP_zero`,
  `theorem_15_3_7_statement_epSEP_zero_of_pointwise`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle MPolyfold

variable {A : SEP.{u}}

variable (A) in
/-- **The pointwise choice of the proof of Theorem 15.3.7** (p. 694): at every `x ∈ S_f` and for
every `ε > 0`, finitely many smooth vectors `w_j ∈ W_x` with `N(w_j) < ε` and
`f'(x)(T^R_xX) + span{w_j} = W_x` ((15.1) at `x`, `IsParamOntoVec`). -/
def HasPointwiseParamOnto (f : A.Obj → A.W) (N : A.B.One → ℝ) : Prop :=
  ∀ x : A.X.PObj.Level 1, A.X.PObj.levelVal 1 x ∈ solutionSet A.P f → ∀ ε > 0,
    ∃ (ℓ : ℕ) (w : Fin ℓ → A.P ⁻¹' {A.X.PObj.levelVal 1 x}),
      (∀ j, (w j : A.W) ∈ A.B.toMPolyfold0.smoothSet) ∧ (∀ j, normW N (w j) < ε) ∧
      IsParamOntoVec f x w

variable (A) in
/-- **The openness of (15.1) along `S_f`** (used in the proof of Theorem 15.3.7, p. 695): for
sc⁺-sections `s_j` with (15.1) at `x ∈ S_f` with the vectors `s_j(x)`, (15.1) with `s_j(y)` holds
at every `y ∈ S_f` in a neighbourhood of `x`. -/
def HasParamOntoOpen (f : A.Obj → A.W) : Prop :=
  ∀ (ℓ : ℕ) (s : Fin ℓ → A.Obj → A.W) (hs : ∀ j, A.B.IsScPlusSection (s j))
    (x : A.X.PObj.Level 1), A.X.PObj.levelVal 1 x ∈ solutionSet A.P f →
    IsParamOntoVec f x (fun j => ⟨s j (A.X.PObj.levelVal 1 x), (hs j).1 _⟩) →
    ∃ W : Set A.Obj, IsOpen W ∧ A.X.PObj.levelVal 1 x ∈ W ∧ ∀ y : A.X.PObj.Level 1,
      A.X.PObj.levelVal 1 y ∈ W → A.X.PObj.levelVal 1 y ∈ solutionSet A.P f →
        IsParamOntoVec f y (fun j => ⟨s j (A.X.PObj.levelVal 1 y), (hs j).1 _⟩)

variable {f : A.Obj → A.W} {N : A.B.One → ℝ}

/-- **The seeds from the pointwise choice and the openness of (15.1)**: with sc-smooth bump
functions and smooth solutions, Part I's Lemma 5.3.3 extends the vectors `w_j` to sc⁺-sections
`s_j` supported in `O` with `N(s_j) < ε`. -/
theorem hasLocalParamSeeds_of (hbump : A.X.AdmitsBumpFunctionsPointwise) (hN : A.B.IsAuxNorm N)
    (hsm : solutionSet A.P f ⊆ A.X.PObj.smoothSet) (h1 : HasPointwiseParamOnto A f N)
    (h2 : HasParamOntoOpen A f) : HasLocalParamSeeds A f N := by
  intro x hx O hO hxO ε hε
  have hxs := hsm hx
  have hx1 : x ∈ A.X.PObj.levelSet 1 := mem_iInter.1 hxs 1
  set x₁ := A.X.PObj.levelMk 1 x hx1
  obtain ⟨ℓ, w, hwsm, hwN, hon⟩ :=
    h1 x₁ (by rwa [A.X.PObj.levelVal_levelMk]) (ε / 2) (half_pos hε)
  have hloc : ∀ j, ∃ s : A.Obj → A.W, A.B.IsScPlusSection s ∧ s x = w j ∧
      sectionSupport A.P s ⊆ O ∧ ∀ y, normW N (s y) ≤ ε := by
    intro j
    obtain ⟨he1, s, hs, hsx, hsO, hsN⟩ := lemma_5_3_3 (EpGroupoid.theorem_12_3_2_1.1 hbump) hN
      hxs (hwsm j) (w j).2 (half_pos hε) hO hxO
    refine ⟨s, hs, hsx, hsO, fun y => ?_⟩
    rw [normW_of_mem N (hs.mem_oneSet y)]
    have h3 := hsN y (hs.mem_oneSet y)
    have hw := hwN j
    rw [normW_of_mem N he1] at hw
    linarith
  choose s hs hsx hsO hsN using hloc
  have hon' : IsParamOntoVec f x₁ (fun j => ⟨s j (A.X.PObj.levelVal 1 x₁), (hs j).1 _⟩) := by
    have e : (fun j => (⟨s j (A.X.PObj.levelVal 1 x₁), (hs j).1 _⟩ :
        A.P ⁻¹' {A.X.PObj.levelVal 1 x₁})) = w := funext fun j => Subtype.ext (hsx j)
    rw [e]
    exact hon
  obtain ⟨W, hWo, hxW, hW⟩ := h2 ℓ s hs x₁ (by rwa [A.X.PObj.levelVal_levelMk]) hon'
  exact ⟨ℓ, s, hs, hsO, hsN, W, hWo, hxW, hW⟩

/-- **Theorem 15.3.7 as stated (`theorem_15_3_7_statement`)** from a good system and, under the
hypotheses of the theorem, the pointwise choice (`HasPointwiseParamOnto`), the openness of (15.1)
(`HasParamOntoOpen`) and GP's parametric transversality step (`HasParametricGeneralPosition`). -/
theorem theorem_15_3_7_of_pointwise (h𝒰 : Nonempty A.X.GoodSystem)
    (H : A.X.IsTame → A.X.AdmitsBumpFunctionsPointwise →
      ∀ f : A.Obj → A.W, A.E.IsScFredholmSectionFunctor f → A.B.IsScFredholmSectionTame f →
        A.E.HasCompactSolutionSetEp f →
        ∀ (N : A.B.One → ℝ) (U : Set A.Obj), ControlsCompactness A f N U →
          HasPointwiseParamOnto A f N ∧ HasParamOntoOpen A f ∧
            HasParametricGeneralPosition A f N U) :
    theorem_15_3_7_statement A :=
  theorem_15_3_7_of_seeds h𝒰 fun htame hbump f hf hft hS N U hcc =>
    ⟨hasLocalParamSeeds_of hbump hcc.1.isAuxNorm (fun y hy => mem_smoothSet_of_eq hft
      isOpen_univ (isScPlusSectionOn_fiberZero isOpen_univ) (mem_univ y) hy)
      (H htame hbump f hf hft hS N U hcc).1 (H htame hbump f hf hft hS N U hcc).2.1,
      (H htame hbump f hf hft hS N U hcc).2.2⟩

/-! ### Satisfiability on `ℝⁿ × ℝ⁰ → ℝⁿ` -/

/-- On `ℝⁿ × ℝ⁰ → ℝⁿ` (fibres `0`), (15.1) holds at every point for every family of vectors. -/
theorem isParamOntoVec_epSEP_zero (n : ℕ)
    (f : (StrongBundleEquivalenceExamples.epSEP n 0).Obj →
      (StrongBundleEquivalenceExamples.epSEP n 0).W)
    (y : (StrongBundleEquivalenceExamples.epSEP n 0).X.PObj.Level 1) {ℓ : ℕ}
    (v : Fin ℓ → (StrongBundleEquivalenceExamples.epSEP n 0).P ⁻¹'
      {(StrongBundleEquivalenceExamples.epSEP n 0).X.PObj.levelVal 1 y}) :
    IsParamOntoVec f y v :=
  fun _ _ _ _ _ _ _ _ _ _ => ⟨0, zero_mem _, 0, fiber_eq_epSEP_zero n _ _⟩

/-- **`HasPointwiseParamOnto` is satisfiable** (`ℓ = 0`). -/
theorem hasPointwiseParamOnto_epSEP_zero (n : ℕ)
    (f : (StrongBundleEquivalenceExamples.epSEP n 0).Obj →
      (StrongBundleEquivalenceExamples.epSEP n 0).W)
    (N : (StrongBundleEquivalenceExamples.epSEP n 0).B.One → ℝ) :
    HasPointwiseParamOnto (StrongBundleEquivalenceExamples.epSEP n 0) f N :=
  fun x _ _ _ => ⟨0, fun j => j.elim0, fun j => j.elim0, fun j => j.elim0,
    isParamOntoVec_epSEP_zero n f x _⟩

/-- **`HasParamOntoOpen` is satisfiable** (`W = ℝⁿ`). -/
theorem hasParamOntoOpen_epSEP_zero (n : ℕ)
    (f : (StrongBundleEquivalenceExamples.epSEP n 0).Obj →
      (StrongBundleEquivalenceExamples.epSEP n 0).W) :
    HasParamOntoOpen (StrongBundleEquivalenceExamples.epSEP n 0) f :=
  fun _ _ _ _ _ _ => ⟨univ, isOpen_univ, mem_univ _, fun y _ _ =>
    isParamOntoVec_epSEP_zero n f y _⟩

/-- **The hypotheses of `theorem_15_3_7_of_pointwise` hold together** on `ℝⁿ × ℝ⁰ → ℝⁿ`. -/
theorem theorem_15_3_7_statement_epSEP_zero_of_pointwise (n : ℕ) :
    theorem_15_3_7_statement (StrongBundleEquivalenceExamples.epSEP n 0) :=
  theorem_15_3_7_of_pointwise (nonempty_goodSystem_epSEP_zero n)
    fun _ _ f _ _ _ N U _ => ⟨hasPointwiseParamOnto_epSEP_zero n f N,
      hasParamOntoOpen_epSEP_zero n f, hasParametricGeneralPosition_epSEP_zero n f N U⟩

end SBLocalization

end Polyfold
