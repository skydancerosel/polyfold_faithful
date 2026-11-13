import Polyfold.Chapter5.Theorem5315_LocalData

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §5.3,
**Theorem 5.3.15** (p. 223; 2017: Theorem 5.8; preprint: Theorem 5.22).  Gap G.48.

# Theorem 5.3.15: the Morse-type structure

## The text, paraphrased

(Theorem 5.3.15) Let `P : Y → X` be a strong bundle over a tame M-polyfold admitting sc-smooth
bump functions, `(f, t)` a generalized compact homotopy (Definition 5.3.13) whose ends
`Xᵢ = t⁻¹(i)` have no boundary and carry problems `(fᵢ, Pᵢ)` in general position, with
`∂X = X₀ ⊔ X₁`, and `N` an auxiliary norm.  Then there is an open neighbourhood `U` of the
solution set `S_f` such that `S_{f+s}` is compact for every `s ∈ Γ^{+,1}_U(P)`, and for every
`ε > 0` there is an `s₀ ∈ Γ^{+,1}_U(P)` with `N(s₀(x)) ≤ ε`, vanishing near `∂X`, such that
(1) `(f + s₀, x)` is in general position at every zero and (2) `t : S_{f+s₀} → [0, 1]` has only
Morse-type critical points.

## What is formalized

* **`theorem_5_3_15`**: the statement, with both conclusions and no added hypothesis.  It is
  `theorem_5_3_15_hyp` (`Theorem5315_Morse.lean`) with its hypothesis `hloc` (the local data
  (A1)–(A3) of the perturbed sections) discharged by `StrongBundle.hasMorseLocalData`
  (`Theorem5315_LocalData.lean`).
* The hypotheses are satisfiable: `isSubmersiveGenCompactHomotopy_witness` (`Book2021.lean`)
  with `theorem_5_3_15_generalPosition_witness` (`Theorem5315_Ends.lean`).

## What the text leaves implicit, and the choices made

* "Morse-type critical points" is read through smooth parametrizations of the solution set
  (`MPolyfold.HasOnlyMorseCriticalPoints`, `Theorem5315_MorseParam.lean`).
* The zeros on `∂X` are regular points of `t|S`, whatever the degeneracy index of the point:
  `t` has an extremum there, so `dt(x)` vanishes on the reduced tangent space, while
  `dt(x) ≠ 0` (Definition 5.3.13 (3)) and `T_xX = ker f'(x) + T^R_xX`.  Of `∂X = X₀ ⊔ X₁` this
  uses `t(∂X) ⊆ {0, 1}` only.
-/

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- **2021 Theorem 5.3.15, p. 223** (2017: Theorem 5.8; preprint: Theorem 5.22), the Morse-type
structure.  Let `X` admit sc-smooth bump functions, `(f, t)` be a generalized compact homotopy
(2021 Definition 5.3.13) whose ends `Xᵢ = t⁻¹(i)` have no boundary and whose end problems are in
general position, `∂X = X₀ ∪ X₁`, and `N` an auxiliary norm.  Then there is an open `U ⊇ S_f`
such that `S_{f+s}` is compact for every `s ∈ Γ^{+,1}_U(P)`, and for every `ε > 0` an
`s₀ ∈ Γ^{+,1}_U(P)` with `N(s₀(x)) ≤ ε`, vanishing near `∂X`, such that (1) `(f + s₀, x)` is in
general position at every `x ∈ S_{f+s₀}` and (2) `t : S_{f+s₀} → [0, 1]` has only Morse-type
critical points (`MPolyfold.HasOnlyMorseCriticalPoints`).  The statement is the book's; the
proof is `theorem_5_3_15_hyp` with the local data from `StrongBundle.hasMorseLocalData`. -/
theorem theorem_5_3_15 (hbump : PX.AdmitsBumpFunctions) {t : X → ℝ}
    (h : B.IsSubmersiveGenCompactHomotopy f t)
    (hends : B.IsGeneralPositionAtEnds f h.isScFredholm.isScSmooth.1 t)
    (hbd : PX.boundary = t ⁻¹' {0} ∪ t ⁻¹' {1}) {N : B.One → ℝ} (hN : B.IsAuxNorm N) :
    ∃ U : Set X, IsOpen U ∧ solutionSet P f ⊆ U ∧
      (∀ s ∈ B.allowableSections N U, IsCompact (solutionSet P (sectionAdd P f s))) ∧
      ∀ ε > 0, ∃ s₀ ∈ B.allowableSections N U,
        (∀ x (hx : s₀ x ∈ B.oneSet), N (B.oneMk (s₀ x) hx) ≤ ε) ∧
        (∀ᶠ x in 𝓝ˢ PX.boundary, IsZeroAt P s₀ x) ∧
        (∀ x ∈ solutionSet P (sectionAdd P f s₀),
          B.IsGeneralPositionGerm (sectionAdd P f s₀) x) ∧
        PX.HasOnlyMorseCriticalPoints (solutionSet P (sectionAdd P f s₀)) t :=
  theorem_5_3_15_hyp hbump h hends hbd hN fun _ hs _ _ hgp =>
    StrongBundle.hasMorseLocalData hbump hN h.isScSmooth_t h.surjDeriv h.mem_Icc hbd.le
      (theorem_3_1_18_tame h.isScFredholm hs) hgp

end Polyfold
