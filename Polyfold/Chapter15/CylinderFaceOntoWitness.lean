import Polyfold.Chapter15.FaceOntoCorollaries
import Polyfold.Chapter15.TransversalExtensionWitness
import Polyfold.Chapter15.ParamOntoBridge
import Polyfold.Chapter14.OpenExtension

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Corollary 15.3.10 (3)
(p. 699): **an instance with non-zero fibres of the face condition on the cylinder** and of
Corollary 15.3.10 (3).

# The face condition on `[0, 1] × ℝ`

## The example

On `ℝ × ℝ → ℝ` over the trivial ep-groupoid of `ℝ` (`epSEP 1 1`, `d_X ≡ 0`), the section
`f(x) = (x, x)` (`TrivialBundle.diagSection`) and the multisection `Λ₀` of the zero section:
`supp(Λ₀ ∘ f) = {0}` and `Df(0) = id` is onto the fibre `ℝ`, so `(f, Λ₀)` is transversal.  On the
cylinder `[0, 1] × ℝ`, whose boundary `{0, 1} × ℝ` is non-empty, the glued data `Λ̃ = Λ₀` on both
ends have weight `1` at the boundary points `(0, 0)` and `(1, 0)` of `supp(Λ̃ ∘ f̃)`, so the face
condition `IsBoundaryFaceOnto f̃ Λ̃` is not vacuous there; it holds by
`SBLocalization.isBoundaryFaceOnto_cubeGlue`.

## What is formalized (namespace `Polyfold.TrivialBundle`)

* `isTransversal_diagSection`: `(f, Λ₀)` is transversal (Definition 15.2.1);
* **`isBoundaryFaceOnto_cubeGlue_diagSection`**: non-zero fibres, the boundary points `(q, 0)`,
  `q ∈ {0, 1}`, of `[0, 1] × ℝ` with `Λ̃(f̃(q, 0)) = 1`, and the face condition of the glued data;
* **`corollary_15_3_10_3_regular_epSEP`**: Corollary 15.3.10 (3) for two structurable regular
  perturbations of `f` (from `corollary_15_3_10_1_epSEP`), through
  `SBLocalization.corollary_15_3_10_3_regular`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter
open scoped ContDiff

noncomputable section

namespace Polyfold

namespace TrivialBundle

open SBLocalization StrongBundle StrongRetr MPolyfold EpGroupoid SEP StrongBundleEquivalenceExamples

/-- `f(x) = (x, x)` is an sc-Fredholm section functor of `ℝ × ℝ → ℝ`. -/
theorem isScFredholmSectionFunctor_diagSection :
    (epSEP 1 1).E.IsScFredholmSectionFunctor diagSection :=
  graphSection_mem_fredholmSectionFunctors_epBundle contDiff_id

/-- `Λ₀(f(x)) > 0` only at `x = 0`. -/
theorem eq_zero_of_zeroMultisection_diagSection_pos {x₀ : (epSEP 1 1).Obj}
    (h : 0 < zeroMultisection (epSEP 1 1) (diagSection x₀)) : x₀ = (show (epSEP 1 1).Obj from (0 : Fin 1 → ℝ)) := by
  classical
  have aux : ∀ w : (epSEP 1 1).W, w = diagSection x₀ →
      0 < zeroMultisection (epSEP 1 1) w → x₀ = (show (epSEP 1 1).Obj from (0 : Fin 1 → ℝ)) := by
    intro w hw hpos
    by_contra hne
    unfold zeroMultisection at hpos
    rw [if_neg] at hpos
    · exact lt_irrefl _ hpos
    · intro e
      apply hne
      subst hw
      exact (isZeroAt_graphSection_iff (n := 1) (k := 1) (φ := id) (x := x₀)).1 e
  exact aux _ rfl h

/-- `Λ₀(f(0)) = 1`. -/
theorem zeroMultisection_diagSection_zero :
    zeroMultisection (epSEP 1 1) (diagSection (show (epSEP 1 1).Obj from (0 : Fin 1 → ℝ))) = 1 := by
  classical
  have aux : ∀ w : (epSEP 1 1).W, w = diagSection (show (epSEP 1 1).Obj from (0 : Fin 1 → ℝ)) →
      zeroMultisection (epSEP 1 1) w = 1 := by
    intro w hw
    have key : w = fiberZero (epSEP 1 1).P ((epSEP 1 1).P w) := by
      subst hw
      exact (isZeroAt_graphSection_iff (n := 1) (k := 1) (φ := id)
        (x := (0 : Fin 1 → ℝ))).2 rfl
    unfold zeroMultisection
    rw [if_pos key]
  exact aux _ rfl

/-- **`(f, Λ₀)` is transversal** (Definition 15.2.1): at the only point `0` of `supp(Λ₀ ∘ f)`,
in the translation chart, `(f − 0)'(0) = id` is onto `ℝ`. -/
theorem isTransversal_diagSection :
    IsTransversal diagSection (zeroMultisection (epSEP 1 1)) := by
  classical
  have hf := isScFredholmSectionFunctor_diagSection
  intro x₀ hpos
  have h0 := eq_zero_of_zeroMultisection_diagSection_pos hpos
  have hx1 : x₀ ∈ (epSEP 1 1).X.PObj.levelSet 1 := by
    have h : (x₀ : Fin 1 → ℝ) ∈ (rnPolyfold 1).levelSet 1 := by
      rw [rnPolyfold_levelSet]; exact mem_univ _
    exact h
  refine ⟨hpos, hx1, ?_⟩
  set x := (epSEP 1 1).X.PObj.levelMk 1 x₀ hx1 with hxdef
  intro L hL
  have hxv : (epSEP 1 1).X.PObj.levelVal 1 x = x₀ := (epSEP 1 1).X.PObj.levelVal_levelMk _ _ _
  let c : StrongBundleChart (epSEP 1 1).X.PObj (epSEP 1 1).P := chart (k := 1) (0 : Fin 1 → ℝ)
  have hc : (epSEP 1 1).B.IsChart c := isChart_chart 0
  have hx : (epSEP 1 1).X.PObj.levelVal 1 x ∈ c.φ.source := mem_univ _
  have hx0 : diagSection ((epSEP 1 1).X.PObj.levelVal 1 x) =
      fiberZero (epSEP 1 1).P ((epSEP 1 1).X.PObj.levelVal 1 x) := by
    rw [hxv]; exact (isZeroAt_graphSection_iff (n := 1) (k := 1) (φ := id) (x := x₀)).2 h0
  rw [← (mem_support_linearization_zero_iff hf hc hx hx0 L).1 hL]
  refine (surjective_toIntr_subDeriv_iff hf.1.1 (isScPlusSectionOn_fiberZero isOpen_univ) hc
    (subset_univ _) hx hx0).2 ?_
  set z := levelLift c.φ 1 ((epSEP 1 1).X.PObj.levelVal 1 x)
  have hD0 : ∀ w : Fin 1 → ℝ, scDeriv (E := rnSc 1) (F := rnSc 1) univ (fun u : Fin 1 → ℝ => u) w =
      ContinuousLinearMap.id ℝ _ := fun w => by
    have := scDeriv_univ_const (V := Fin 1 → ℝ) (V' := Fin 1 → ℝ) contDiff_id w
    rw [fderiv_id] at this
    exact this
  have hD : scDeriv (E := rnSc 1) (F := rnSc 1) univ (fun u : Fin 1 → ℝ => u) z =
      ContinuousLinearMap.id ℝ _ := hD0 z
  have he : ((fun y => c.principal diagSection y - c.principal (fiberZero (epSEP 1 1).P) y) ∘
      r c.R) = fun u : Fin 1 → ℝ => u := by
    funext u
    have h2 : c.principal (fiberZero (epSEP 1 1).P) u = 0 :=
      c.snd_fiberZero (x := c.φ.symm u) (mem_univ _)
    change c.principal diagSection u - c.principal (fiberZero (epSEP 1 1).P) u = u
    rw [h2, sub_zero]
    exact add_zero u
  intro k _
  refine ⟨k, ⟨k, ?_⟩, ?_⟩
  · exact congrArg (fun T : (rnSc 1) 0 →L[ℝ] (rnSc 1) 0 => T k) hD
  · change scDeriv c.U ((fun y => c.principal diagSection y -
      c.principal (fiberZero (epSEP 1 1).P) y) ∘ r c.R) z k = k
    rw [he]
    exact congrArg (fun T : (rnSc 1) 0 →L[ℝ] (rnSc 1) 0 => T k) hD

/-- **The face condition on the cylinder `[0, 1] × ℝ`, with non-zero fibres and non-vacuous**:
the fibres of `ℝ × ℝ → ℝ` are non-zero; for `q ∈ {0, 1}` the point `(q, 0)` lies on the boundary
of `[0, 1] × ℝ` and the glued data `Λ̃ = Λ₀ ∪ Λ₀` of the two ends have weight `1` at `f̃(q, 0)`;
and `IsBoundaryFaceOnto f̃ Λ̃` holds (`isBoundaryFaceOnto_cubeGlue`). -/
theorem isBoundaryFaceOnto_cubeGlue_diagSection :
    (∀ y : (epSEP 1 1).Obj, Nontrivial ((epSEP 1 1).P ⁻¹' {y})) ∧
    (∀ q : Fin 1 → unitInterval, ((q 0 : ℝ) = 0 ∨ (q 0 : ℝ) = 1) →
      (show ((epSEP 1 1).cubeSEP 1).Obj from (q, (0 : Fin 1 → ℝ))) ∈
          ((epSEP 1 1).cubeSEP 1).X.PObj.boundary ∧
        cubeGlue (zeroMultisection (epSEP 1 1)) (zeroMultisection (epSEP 1 1))
          (cubeLiftEp (n := 1) diagSection isScFredholmSectionFunctor_diagSection.1.1.1
            (q, (0 : Fin 1 → ℝ))) = 1) ∧
    IsBoundaryFaceOnto (cubeLiftEp (n := 1) diagSection isScFredholmSectionFunctor_diagSection.1.1.1)
      (cubeGlue (zeroMultisection (epSEP 1 1)) (zeroMultisection (epSEP 1 1))) := by
  obtain ⟨hfib, -, hd, -, -, hf, hft, -⟩ := corollary_15_3_10_1_hypotheses_epSEP
  have hX : (epSEP 1 1).X.IsTame := (epSEP 1 1).X.isTame_of_degIndex_eq_zero hd
  refine ⟨hfib, fun q hq => ⟨(mem_boundary_cubeSEP_iff hX hd _).2 hq, ?_⟩,
    isBoundaryFaceOnto_cubeGlue hd hf hft isTransversal_diagSection isTransversal_diagSection⟩
  unfold cubeGlue
  split_ifs <;> exact zeroMultisection_diagSection_zero

/-- **Corollary 15.3.10 (3) on `ℝ × ℝ → ℝ`, with non-zero fibres**
(`corollary_15_3_10_3_regular`): for two structurable regular perturbations `Λ₀`, `Λ₁` of
`f(x) = (x, x)` (they exist by `corollary_15_3_10_1_epSEP`), there is a structurable regular
perturbation `Λ'` of `f̃` on `[0, 1] × ℝ` restricting to `Λᵢ` on `{i} × ℝ`, with `Λ' ∘ f̃` a compact
branched ep⁺-subgroupoid. -/
theorem corollary_15_3_10_3_regular_epSEP {N₀ N₁ : (epSEP 1 1).B.One → ℝ}
    {U₀ U₁ : Set (epSEP 1 1).Obj} {Λ₀ Λ₁ : (epSEP 1 1).W → ℚ≥0}
    (hr₀ : IsRegularPerturbation (epSEP 1 1) diagSection N₀ U₀ Λ₀)
    (hr₁ : IsRegularPerturbation (epSEP 1 1) diagSection N₁ U₁ Λ₁) :
    ∃ Λ' : ((epSEP 1 1).cubeSEP 1).W → ℚ≥0,
      IsRegularPerturbation ((epSEP 1 1).cubeSEP 1)
        (cubeLiftEp (n := 1) diagSection isScFredholmSectionFunctor_diagSection.1.1.1)
        (interpAuxNorm (epSEP 1 1) N₀ N₁) (interpSet (epSEP 1 1) U₀ U₁) Λ' ∧
      (∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (cubeVal w).2) ∧
      (∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (cubeVal w).2) ∧
      ((epSEP 1 1).cubeSEP 1).X.IsBranchedEpSubgroupoid
        (fun z => (Λ' (cubeLiftEp (n := 1) diagSection
          isScFredholmSectionFunctor_diagSection.1.1.1 z) : ℚ)) ∧
      ((epSEP 1 1).cubeSEP 1).X.IsCompactBranched
        (fun z => (Λ' (cubeLiftEp (n := 1) diagSection
          isScFredholmSectionFunctor_diagSection.1.1.1 z) : ℚ)) := by
  obtain ⟨-, -, hd, hpara, -, hf, hft, hS, -⟩ := corollary_15_3_10_1_hypotheses_epSEP
  exact corollary_15_3_10_3_regular hd hpara (proposition_14_1_4_hypotheses_rn 1 1).2 hf hft hS
    hr₀ hr₁

/-- **The hypotheses of `corollary_15_3_10_3_regular_epSEP` are satisfiable**: there is a
structurable regular perturbation of `f(x) = (x, x)` (Corollary 15.3.10 (1)), so Corollary
15.3.10 (3) applies to the pair `(Λ, Λ)`. -/
theorem corollary_15_3_10_3_regular_epSEP_nonempty :
    ∃ (N : (epSEP 1 1).B.One → ℝ) (U : Set (epSEP 1 1).Obj) (Λ : (epSEP 1 1).W → ℚ≥0),
      IsRegularPerturbation (epSEP 1 1) diagSection N U Λ ∧
      ∃ Λ' : ((epSEP 1 1).cubeSEP 1).W → ℚ≥0,
        IsRegularPerturbation ((epSEP 1 1).cubeSEP 1)
          (cubeLiftEp (n := 1) diagSection isScFredholmSectionFunctor_diagSection.1.1.1)
          (interpAuxNorm (epSEP 1 1) N N) (interpSet (epSEP 1 1) U U) Λ' ∧
        (∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ (cubeVal w).2) ∧
        (∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ (cubeVal w).2) := by
  obtain ⟨N, U, Λ, hr, -⟩ := corollary_15_3_10_1_epSEP
  obtain ⟨Λ', h1, h2, h3, -⟩ := corollary_15_3_10_3_regular_epSEP hr hr
  exact ⟨N, U, Λ, hr, Λ', h1, h2, h3⟩

end TrivialBundle

end Polyfold
