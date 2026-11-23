import Polyfold.Chapter9.BumpsNearCompact
import Polyfold.Chapter15.RelativeStepSeeds

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, **Definition
15.3.1** (p. 691, `(N, U)` controls compactness) and the bump functions used in the proofs of
Theorems 15.3.7 and 15.3.9 (pp. 696–699).

# Bump functions near the set cut out by a controlling pair

## The text, paraphrased

If `(N, U)` controls the compactness of `f`, the orbit space of `{x ∈ U | N(f(x)) ≤ 1}` has
compact closure.  The solution set of every perturbation `Λ` with dom-supp in `U` and `N(Λ) ≤ 1`
lies in this set, and the constructions of §15.3 use sc-smooth bump functions at its points.

## What is formalized (namespace `Polyfold.SBLocalization`)

* **`exists_bumps_of_controlsCompactness`**: for `(N, U)` controlling the compactness of `f`,
  finitely many objects `p_i` and open `N_i ∋ p_i`, there is a saturated open
  `W ⊇ {x ∈ U | N(f(x)) ≤ 1}` such that the restricted ep-groupoid `X|W` carries sc-smooth
  functors `F_i ≥ 0` with `F_i(p_i) = 1` and `supp F_i ⊆ π⁻¹π(N_i)`.  No bump functions on `X`
  are assumed.
* `exists_bumps_of_controlsCompactness_cylinder`: the same on `[0, 1] × X` for the collar pair of
  two controlling pairs (Corollary 15.3.10 (2), p. 699).

## Reading

`W` depends on the finite family (`EP.exists_bumps_near_compact`).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle MPolyfold EpGroupoid SEP

variable {A : SEP.{u}}

/-- **Finitely many bump functions near `{x ∈ U | N(f(x)) ≤ 1}`** (Definition 15.3.1, 2021
p. 691; Definition 12.3.1, p. 579, on a restricted ep-groupoid).  Let `(N, U)` control the
compactness of `f`, `p_i` be finitely many objects and `N_i ∋ p_i` open.  Then there is a
saturated open `W ⊇ {x ∈ U | N(f(x)) ≤ 1}` such that on `X|W` there are sc-smooth functions
`F_i ≥ 0`, constant on the orbits, with `F_i(p_i) = 1` and support in `π⁻¹π(N_i)`. -/
theorem exists_bumps_of_controlsCompactness {f : A.Obj → A.W} {N : A.B.One → ℝ}
    {U : Set A.Obj} (hcc : ControlsCompactness A f N U) {ι : Type*} [Finite ι]
    (p : ι → A.Obj) (N' : ι → Set A.Obj) (hN : ∀ i, IsOpen (N' i)) (hpN : ∀ i, p i ∈ N' i) :
    ∃ (W : Set A.Obj) (hW : A.X.IsEpSubgroupoid W), IsOpen W ∧
      {x ∈ U | A.B.AuxLe N (f x) 1} ⊆ W ∧
      ∃ F : ι → A.Obj → ℝ, ∀ i,
        (A.baseEP.sub hW).X.PObj.IsScSmoothMap realPolyfold (A.baseEP.subFun hW (F i)) ∧
        (∀ φ : (A.baseEP.sub hW).Mor, A.baseEP.subFun hW (F i) ((A.baseEP.sub hW).X.src φ) =
          A.baseEP.subFun hW (F i) ((A.baseEP.sub hW).X.tgt φ)) ∧
        (∀ y, 0 ≤ F i y) ∧ F i (p i) = 1 ∧
        tsupport (A.baseEP.subFun hW (F i)) ⊆
          (A.baseEP.subFunctor hW).obj ⁻¹' (A.X.π ⁻¹' (A.X.π '' N' i)) := by
  obtain ⟨W, hW, hWo, hTW, F, hF⟩ :=
    A.baseEP.exists_bumps_near_compact hcc.2.2.2.2 p N' hN hpN
  exact ⟨W, hW, hWo, fun x hx => hTW (subset_closure ⟨x, hx, rfl⟩), F, hF⟩

/-- **Finitely many bump functions on `[0, 1] × X` near the set cut out by the collar pair**
(Corollary 15.3.10 (2), 2021 p. 699): for controlling pairs `(Nⁱ, Uⁱ)` of `f`, the statement of
`exists_bumps_of_controlsCompactness` for `f̃` and `(Ñ, Ũ)`. -/
theorem exists_bumps_of_controlsCompactness_cylinder {f : A.Obj → A.W}
    (hf : IsSection A.P f) {N₀ N₁ : A.B.One → ℝ} {U₀ U₁ : Set A.Obj}
    (h₀ : ControlsCompactness A f N₀ U₀) (h₁ : ControlsCompactness A f N₁ U₁)
    {ι : Type*} [Finite ι] (p : ι → (A.cubeSEP 1).Obj) (N' : ι → Set (A.cubeSEP 1).Obj)
    (hN : ∀ i, IsOpen (N' i)) (hpN : ∀ i, p i ∈ N' i) :
    ∃ (W : Set (A.cubeSEP 1).Obj) (hW : (A.cubeSEP 1).X.IsEpSubgroupoid W), IsOpen W ∧
      {x ∈ interpSet A U₀ U₁ | (A.cubeSEP 1).B.AuxLe (collarAuxNorm A N₀ N₁)
        (cubeLiftEp (n := 1) f hf x) 1} ⊆ W ∧
      ∃ F : ι → (A.cubeSEP 1).Obj → ℝ, ∀ i,
        ((A.cubeSEP 1).baseEP.sub hW).X.PObj.IsScSmoothMap realPolyfold
          ((A.cubeSEP 1).baseEP.subFun hW (F i)) ∧
        (∀ φ : ((A.cubeSEP 1).baseEP.sub hW).Mor,
          (A.cubeSEP 1).baseEP.subFun hW (F i) (((A.cubeSEP 1).baseEP.sub hW).X.src φ) =
            (A.cubeSEP 1).baseEP.subFun hW (F i) (((A.cubeSEP 1).baseEP.sub hW).X.tgt φ)) ∧
        (∀ y, 0 ≤ F i y) ∧ F i (p i) = 1 ∧
        tsupport ((A.cubeSEP 1).baseEP.subFun hW (F i)) ⊆
          ((A.cubeSEP 1).baseEP.subFunctor hW).obj ⁻¹'
            ((A.cubeSEP 1).X.π ⁻¹' ((A.cubeSEP 1).X.π '' N' i)) :=
  exists_bumps_of_controlsCompactness (controlsCompactness_collar hf h₀ h₁) p N' hN hpN

end SBLocalization

end Polyfold
