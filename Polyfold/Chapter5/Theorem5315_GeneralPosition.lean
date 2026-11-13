import Polyfold.Chapter5.CylinderPerturbation2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §5.3,
**Theorem 5.3.15** (p. 223; 2017: Theorem 5.8; preprint: Theorem 5.22), the compactness
statement and conclusion (1).  Gap G.48.

# Theorem 5.3.15: the perturbation in general position that vanishes near the boundary

## The text, paraphrased

(Theorem 5.3.15) For a generalized compact homotopy `f` between two compact problems
`(fᵢ, Pᵢ)` over M-polyfolds without boundary, both in general position, with `∂X = X₀ ⊔ X₁`, and an
auxiliary norm `N`: there is an open `U ⊇ S_f` with `S_{f+s}` compact for all `s ∈ Γ^{+,1}_U(P)`,
and an arbitrarily small `s₀ ∈ Γ^{+,1}_U(P)` vanishing near `∂X` such that (1) `(f + s₀, x)` is in
general position at every zero and (2) `t` on `S_{f+s₀}` has only Morse-type critical points.

## What is formalized

* `theorem_5_3_15_generalPosition_hyp`: the open set `U`, the compactness of `S_{f+s}` and an
  arbitrarily small `s₀ ∈ Γ^{+,1}_U(P)` vanishing near `∂X` with (1).  The hypotheses on the ends
  enter in the form the proof uses them (p. 223, bottom, "in view of the assumption that
  `(fᵢ, Xᵢ)` are already in general position"): **`(f, x)` is in general position at every zero
  `x ∈ ∂X`**.  The function `t` plays no role in this part.
* `theorem_5_3_15_generalPosition_hyp_of_boundary_empty`: the hypothesis holds when `∂X = ∅`
  (satisfiability; this is then Theorem 5.3.10 with one small section).

## Done elsewhere (2026-11-12)

* The step from the printed hypotheses (`∂X = X₀ ⊔ X₁`, `(fᵢ, x)` in general position on the
  boundaryless `Xᵢ`) to the general position of `(f, x)` in `X` at the zeros on `∂X` is
  `StrongBundle.IsSubmersiveGenCompactHomotopy.isGeneralPositionGerm_of_mem_boundary`
  (`Theorem5315_Ends.lean`), and (1) under the printed hypotheses is
  `theorem_5_3_15_generalPosition` there.
* Conclusion (2) is `theorem_5_3_15` (`Theorem5315_Final.lean`); the finite-dimensional step of
  its proof is in `Chapter5/Theorem5315_ParametricMorse.lean`.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u v

section Theorem5315

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- General position at the zeros on a set `A` holds at the zeros in an open neighbourhood of
`S_f ∩ A` (`exists_isOpen_isGeneralPositionGerm`; 2021 Theorem 4.2.11 (3), p. 168). -/
lemma exists_isOpen_isGeneralPositionGerm_of_forall (hX : PX.IsTame)
    (hf : B.IsScFredholmSectionTame f) {A : Set X}
    (hA : ∀ x ∈ A, IsZeroAt P f x → B.IsGeneralPositionGerm f x) :
    ∃ W : Set X, IsOpen W ∧ solutionSet P f ∩ A ⊆ W ∧
      ∀ y ∈ W, IsZeroAt P f y → B.IsGeneralPositionGerm f y := by
  choose Wx hWo hxW _ hW using fun x : ↥(solutionSet P f ∩ A) =>
    exists_isOpen_isGeneralPositionGerm hX hf x.2.1 (hA x.1 x.2.2 x.2.1)
  refine ⟨⋃ x, Wx x, isOpen_iUnion hWo, fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hxW _⟩, ?_⟩
  intro y hy hy0
  obtain ⟨x, hyx⟩ := mem_iUnion.1 hy
  exact (hW x y hyx hy0).2.1

/-- **2021 Theorem 5.3.15, p. 223** (2017: Theorem 5.8; preprint: Theorem 5.22), the compactness
statement and conclusion (1), with the hypotheses on the ends in the form the proof uses.  Let
`P : Y → X` be a strong bundle over a tame M-polyfold with sc-smooth bump functions, `f` an
sc-Fredholm section (tame germ data) with compact solution set, `N` an auxiliary norm, and let
`(f, x)` be in general position at every zero `x ∈ ∂X` (`hbd`; in the text this follows from the
general position of the end problems `(fᵢ, Pᵢ)` and `∂X = X₀ ⊔ X₁`, a step formalized as
`StrongBundle.IsSubmersiveGenCompactHomotopy.isGeneralPositionGerm_of_mem_boundary` in
`Theorem5315_Ends.lean`).  Then there is an open `U ⊇ S_f` such that `S_{f+s}` is compact for every
`s ∈ Γ^{+,1}_U(P)`, and for every `ε > 0` an `s₀ ∈ Γ^{+,1}_U(P)` with `N(s₀(x)) ≤ ε` for all `x`,
vanishing near `∂X`, such that `(f + s₀, x)` is in general position at every `x ∈ S_{f+s₀}`.
*Proof*: `theorem_5_3_10_relative_hyp` for the compact part `K = S_f ∖ W_b` of the zero set,
`W_b` an open set around `S_f ∩ ∂X` on which the zeros are in general position, and the
perturbation supported in `U ∖ ∂X`.  Conclusion (2) (Morse-type critical points of `t`) is not
part of this statement; the full theorem is `theorem_5_3_15` (`Theorem5315_Final.lean`). -/
theorem theorem_5_3_15_generalPosition_hyp (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) (hS : IsCompact (solutionSet P f)) {N : B.One → ℝ}
    (hN : B.IsAuxNorm N)
    (hbd : ∀ x ∈ PX.boundary, IsZeroAt P f x → B.IsGeneralPositionGerm f x) :
    ∃ U : Set X, IsOpen U ∧ solutionSet P f ⊆ U ∧
      (∀ s ∈ B.allowableSections N U, IsCompact (solutionSet P (sectionAdd P f s))) ∧
      ∀ ε > 0, ∃ s₀ ∈ B.allowableSections N U,
        (∀ x (hx : s₀ x ∈ B.oneSet), N (B.oneMk (s₀ x) hx) ≤ ε) ∧
        (∀ᶠ x in 𝓝ˢ PX.boundary, IsZeroAt P s₀ x) ∧
        ∀ x ∈ solutionSet P (sectionAdd P f s₀), B.IsGeneralPositionGerm (sectionAdd P f s₀) x := by
  obtain ⟨U, hUo, hSU, -, hcpt, hcptS⟩ :=
    exists_adapted_margin hf.toIsScFredholmSection hS hN isOpen_univ (subset_univ _)
  refine ⟨U, hUo, hSU, hcptS, fun ε hε => ?_⟩
  obtain ⟨Wb, hWbo, hSWb, hgpWb⟩ := exists_isOpen_isGeneralPositionGerm_of_forall hX hf hbd
  have hbcl : IsClosed PX.boundary := PX.isClosed_boundary
  -- the compact part of the zero set off `W_b`, and the open set `U ∖ ∂X`
  have hK : IsCompact (solutionSet P f \ Wb) := hS.diff hWbo
  have hKW : solutionSet P f \ Wb ⊆ U ∩ PX.boundaryᶜ := fun x hx =>
    ⟨hSU hx.1, fun hxb => hx.2 (hSWb ⟨hx.1, hxb⟩)⟩
  have hcptW : IsCompact (closure {x ∈ U ∩ PX.boundaryᶜ | B.AuxLe N (f x) 1}) :=
    (hcpt 1 one_pos).of_isClosed_subset isClosed_closure
      (closure_mono fun x hx => ⟨hx.1.1, hx.2⟩)
  obtain ⟨p, hp, hpsupp, hpN, hgp⟩ := theorem_5_3_10_relative_hyp hX hbump hf hN
    (hUo.inter hbcl.isOpen_compl) hK hKW
    (fun x hx0 hxK => hgpWb x (by_contra fun h => hxK ⟨hx0, h⟩) hx0) hcptW
    (lt_min hε one_pos)
  refine ⟨p, ⟨hp, hpsupp.trans inter_subset_left, fun x hx => ?_⟩, fun x hx => ?_, ?_,
    fun x hx => hgp x hx⟩
  · obtain ⟨_, h⟩ := hpN x
    exact h.trans (min_le_right _ _)
  · obtain ⟨_, h⟩ := hpN x
    exact h.trans (min_le_left _ _)
  · -- `p = 0` on the open set `X ∖ supp p ⊇ ∂X`
    have hopen : IsOpen (sectionSupport P p)ᶜ := isClosed_closure.isOpen_compl
    have hsub : PX.boundary ⊆ (sectionSupport P p)ᶜ := fun x hxb hxs => (hpsupp hxs).2 hxb
    filter_upwards [hopen.mem_nhdsSet.2 hsub] with x hx
    exact not_not.1 fun hne => hx (subset_closure hne)

/-- **Satisfiability of the hypothesis of `theorem_5_3_15_generalPosition_hyp`**: over an
M-polyfold without boundary the hypothesis on the zeros on `∂X` is empty, and the statement is
2021 Theorem 5.3.10 (p. 220) with one arbitrarily small section. -/
theorem theorem_5_3_15_generalPosition_hyp_of_boundary_empty (hX : PX.IsTame)
    (hbump : PX.AdmitsBumpFunctions) (hf : B.IsScFredholmSectionTame f)
    (hS : IsCompact (solutionSet P f)) {N : B.One → ℝ} (hN : B.IsAuxNorm N)
    (hbdry : PX.boundary = ∅) :
    ∃ U : Set X, IsOpen U ∧ solutionSet P f ⊆ U ∧
      (∀ s ∈ B.allowableSections N U, IsCompact (solutionSet P (sectionAdd P f s))) ∧
      ∀ ε > 0, ∃ s₀ ∈ B.allowableSections N U,
        (∀ x (hx : s₀ x ∈ B.oneSet), N (B.oneMk (s₀ x) hx) ≤ ε) ∧
        (∀ᶠ x in 𝓝ˢ PX.boundary, IsZeroAt P s₀ x) ∧
        ∀ x ∈ solutionSet P (sectionAdd P f s₀), B.IsGeneralPositionGerm (sectionAdd P f s₀) x :=
  theorem_5_3_15_generalPosition_hyp hX hbump hf hS hN fun x hx => by
    rw [hbdry] at hx; exact absurd hx (notMem_empty x)

end Theorem5315

end Polyfold
