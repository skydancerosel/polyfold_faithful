import Polyfold.Chapter15.CylinderSliceKernels
import Polyfold.Chapter15.CylinderFaceOntoWitness

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, p. 703 (proof of
**Corollary 15.4.4**; 2017: Corollary 15.2): **an instance with non-empty sheets of the matched
local branching structures on an end of the cylinder**.

# Matched structures on `[0, 1] × ℝ`

## The example

On `ℝ × ℝ → ℝ` over the trivial ep-groupoid of `ℝ` (`epSEP 1 1`, `d_X ≡ 0`, non-zero fibres), the
section `f(x) = (x, x)` and the multisection `Λ₀` of the zero section: `supp(Λ₀ ∘ f) = {0}`.  On
the cylinder `[0, 1] × ℝ` take `Λ̃ = ` the multisection of the zero section of `W̃`; it is `Λ₀`
over both ends, `supp(Λ̃ ∘ f̃) = [0, 1] × {0}`, and the face condition of Theorem 15.3.9 holds
(`isBoundaryFaceOnto_cubeGlue_diagSection`).  At the boundary point `(i, 0)`, `i ∈ {0, 1}`, the
matched structures of `exists_matched_kernel_branching` exist, their index set is non-empty,
every sheet `Mⱼ` contains `0`, and every boundary sheet `∂₁M̃ⱼ = {i} × Mⱼ` contains `(i, 0)`.

## What is formalized

* `SBLocalization.zeroMultisection_cubeSEP`: the multisection of the zero section of `W̃` is
  `w ↦ Λ₀(w₂)`.
* **`TrivialBundle.exists_matched_kernel_branching_diagSection`**: the instance.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open SEP

/-- **The multisection of the zero section of `W̃ → [0, 1]ⁿ × X`** is `w ↦ Λ₀(w₂)`, `Λ₀` the
multisection of the zero section of `W → X`. -/
theorem zeroMultisection_cubeSEP {A : SEP.{u}} {n : ℕ} (w : (A.cubeSEP n).W) :
    zeroMultisection (A.cubeSEP n) w = zeroMultisection A (cubeVal w).2 := by
  classical
  unfold zeroMultisection
  by_cases h : w = fiberZero (A.cubeSEP n).P ((A.cubeSEP n).P w)
  · have h2 : (cubeVal w).2 = fiberZero A.P (A.P (cubeVal w).2) := by
      have e := congrArg (fun v => (cubeVal v).2) h
      rw [P_cubeVal_snd]
      exact e
    rw [if_pos h, if_pos h2]
  · rw [if_neg h, if_neg (cubeVal_snd_ne_fiberZero h)]

end SBLocalization

namespace TrivialBundle

open SBLocalization StrongBundle StrongRetr MPolyfold EpGroupoid SEP StrongBundleEquivalenceExamples

/-- **Matched local branching structures on an end of `[0, 1] × ℝ`, with non-empty sheets**
(`exists_matched_kernel_branching` for `f(x) = (x, x)` on `ℝ × ℝ → ℝ`, `Λ̃` and `Λ` the
multisections of the zero sections, at the point `(i, 0)`, `i ∈ {0, 1}`).  The fibres are
non-zero, `(i, 0)` is a boundary point of the cylinder, and there are local branching structures
`K̃` of `Λ̃ ∘ f̃` at `(i, 0)` and `K` of `Λ ∘ f` at `0`, both described by kernels, with a
bijection `e` of the index sets, such that: the index set is non-empty; the weights agree;
`Mⱼ = {y | (i, y) ∈ M̃ⱼ}`; `∂₁M̃ⱼ = {i} × Mⱼ`; `0 ∈ Mⱼ` and `(i, 0) ∈ ∂₁M̃ⱼ` for every `j`;
`dim M̃ⱼ = dim Mⱼ + 1`; and the sections of `K` are the restrictions of those of `K̃`. -/
theorem exists_matched_kernel_branching_diagSection {i : unitInterval}
    (hi : (i : ℝ) = 0 ∨ (i : ℝ) = 1) :
    (∀ y : (epSEP 1 1).Obj, Nontrivial ((epSEP 1 1).P ⁻¹' {y})) ∧
    (show ((epSEP 1 1).cubeSEP 1).Obj from ((fun _ => i), (0 : Fin 1 → ℝ))) ∈
      ((epSEP 1 1).cubeSEP 1).X.PObj.boundary ∧
    ∃ (K' : KernelBranching ((epSEP 1 1).cubeSEP 1)
        (cubeLiftEp (n := 1) diagSection isScFredholmSectionFunctor_diagSection.1.1.1)
        (zeroMultisection ((epSEP 1 1).cubeSEP 1))
        ((fun _ => i), (show (epSEP 1 1).Obj from (0 : Fin 1 → ℝ))))
      (K : KernelBranching (epSEP 1 1) diagSection (zeroMultisection (epSEP 1 1))
        (show (epSEP 1 1).Obj from (0 : Fin 1 → ℝ))) (e : K'.ι ≃ K.ι),
      Nonempty K'.ι ∧ (∀ j, K'.σ j = K.σ (e j)) ∧
      (∀ j, K.M (e j) = {y | (((fun _ => i), y) : ((epSEP 1 1).cubeSEP 1).Obj) ∈ K'.M j}) ∧
      (∀ j, ((epSEP 1 1).cubeSEP 1).X.PObj.boundaryStratum (K'.M j) =
        (cubeFaceIncl (epSEP 1 1) (fun _ => i)).obj '' K.M (e j)) ∧
      (∀ j, (show (epSEP 1 1).Obj from (0 : Fin 1 → ℝ)) ∈ K.M (e j)) ∧
      (∀ j, (show ((epSEP 1 1).cubeSEP 1).Obj from ((fun _ => i), (0 : Fin 1 → ℝ))) ∈
        ((epSEP 1 1).cubeSEP 1).X.PObj.boundaryStratum (K'.M j)) ∧
      (∀ j, K'.dim j = K.dim (e j) + 1) ∧
      ∀ j, ∀ y ∈ K.O, (((fun _ => i), y) : ((epSEP 1 1).cubeSEP 1).Obj) ∈ K'.O →
        cubeVal (K'.s j ((fun _ => i), y)) = (((fun _ => i), y), K.s (e j) y) := by
  obtain ⟨hfib, -, hd, -, -, hf, hft, -⟩ := corollary_15_3_10_1_hypotheses_epSEP
  have hX : (epSEP 1 1).X.IsTame := (epSEP 1 1).X.isTame_of_degIndex_eq_zero hd
  have hb : (show ((epSEP 1 1).cubeSEP 1).Obj from ((fun _ => i), (0 : Fin 1 → ℝ))) ∈
      ((epSEP 1 1).cubeSEP 1).X.PObj.boundary := (mem_boundary_cubeSEP_iff hX hd _).2 hi
  have honto := isBoundaryFaceOnto_cubeGlue hd hf hft isTransversal_diagSection
    isTransversal_diagSection
  have hpos : 0 < zeroMultisection (epSEP 1 1)
      (diagSection (show (epSEP 1 1).Obj from (0 : Fin 1 → ℝ))) := by
    rw [zeroMultisection_diagSection_zero]; exact one_pos
  obtain ⟨K', K, e, hσ, -, -, hM, hstr, hdim, hs⟩ := exists_matched_kernel_branching hd hf hft
    (isScPlusMultisection_zeroMultisection ((epSEP 1 1).cubeSEP 1))
    (fun w _ => zeroMultisection_cubeSEP w) (fun w _ => zeroMultisection_cubeSEP w) honto hi
    (fun w _ => zeroMultisection_cubeSEP w) hpos
  have hmem : ∀ j, (show ((epSEP 1 1).cubeSEP 1).Obj from ((fun _ => i), (0 : Fin 1 → ℝ))) ∈
      ((epSEP 1 1).cubeSEP 1).X.PObj.boundaryStratum (K'.M j) := fun j => by
    rw [hstr j]
    exact ⟨_, K.mem_M (e j), rfl⟩
  refine ⟨hfib, hb, K', K, e, ?_, hσ, hM, hstr, fun j => K.mem_M (e j), hmem, hdim, hs⟩
  have hsupp : (show ((epSEP 1 1).cubeSEP 1).Obj from ((fun _ => i), (0 : Fin 1 → ℝ))) ∈
      EpGroupoid.supp (fun z => (zeroMultisection ((epSEP 1 1).cubeSEP 1)
        (cubeLiftEp (n := 1) diagSection isScFredholmSectionFunctor_diagSection.1.1.1 z) : ℚ)) := by
    change (0 : ℚ) < (zeroMultisection ((epSEP 1 1).cubeSEP 1)
      (cubeLiftEp (n := 1) diagSection isScFredholmSectionFunctor_diagSection.1.1.1
        ((fun _ => i), (0 : Fin 1 → ℝ))) : ℚ)
    rw [zeroMultisection_cubeSEP]
    exact_mod_cast hpos
  obtain ⟨j, -⟩ := (K'.toLocalBranchingStructure.mem_supp_iff K'.mem_U).1 hsupp
  exact ⟨j⟩

end TrivialBundle

end Polyfold
