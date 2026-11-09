import Polyfold.Chapter5.MainTheoremsBookForm
import Polyfold.Chapter3.MainTheorems2021

/-!
# Theorems 5.3.10 and 5.3.12 in the book's form, with the 2021 definitions

2021 Theorem 5.3.10, p. 220 and 2021 Theorem 5.3.12, p. 222.  `MainTheoremsBookForm.lean` states
both theorems with the book's quantifiers for the project's sc-Fredholm notion
(`IsScFredholmSectionTame`, `IsGoodPositionGermTame`); `MainTheorems2021.lean` states them with the
2021 notions (`IsScFredholmSectionTame2021`, `IsGoodPositionGermTame2021`) but in the form the
proofs produce (a family `t₁, …, t_m`, `paramSlice`, a null set of parameters).  This file
combines the two: the book's quantifiers **and** the 2021 notions, so that a reviewer reads one
statement per theorem and checks only the 2021 definitions (rows V3.108, V3.110 and the reading
of "tame strong bundle", gap G.79).

* `theorem_5_3_10_book_2021def`: `theorem_5_3_10_2021` with `hf` in the 2021 sense.
* `theorem_5_3_12_book_2021def`: `theorem_5_3_12_2021` with `hf`, the boundary hypothesis and the
  good-position conclusion in the 2021 sense.

Both are corollaries through the dictionary `StrongBundle.isScFredholmSectionTame2021_iff`,
`StrongBundle.isGoodPositionGermTame2021_iff`.
-/

open Set Filter Topology Function Module MeasureTheory

noncomputable section

namespace Polyfold

universe u v

section BookForm2021

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

/-- **2021 Theorem 5.3.10, p. 220 (perturbation: general position)**, with the book's quantifiers
and the 2021 sc-Fredholm notion.  Let `P : Y → X` be a strong bundle over a tame M-polyfold
admitting sc-smooth bump functions, `f` an sc-Fredholm section (2021 Definition 3.6.4, germ data
in tame charts) with compact solution set and `N` an auxiliary norm.  There is an open `U ⊇ S_f`
such that `S_{f+s}` is compact for every `s ∈ Γ^{+,1}_U(P)`, and a subset `O ⊆ Γ^{+,1}_U(P)`,
dense for `ρ(s, s') = sup_x N(s(x) − s'(x))`, such that for every `s ∈ O`, `(f + s, x)` is in
general position at every `x ∈ S_{f+s}`; `S_{f+s}` is a compact sub-M-polyfold whose induced
structure is that of a manifold with boundary with corners, with `d_{S_{f+s}} = d_X`. -/
theorem theorem_5_3_10_book_2021def (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    {f : X → Y} (hf : B.IsScFredholmSectionTame2021 f) (hS : IsCompact (solutionSet P f))
    {N : B.One → ℝ} (hN : B.IsAuxNorm N) :
    ∃ U : Set X, IsOpen U ∧ solutionSet P f ⊆ U ∧
      (∀ s ∈ B.allowableSections N U, IsCompact (solutionSet P (sectionAdd P f s))) ∧
      ∃ O ⊆ B.allowableSections N U,
        (∀ (s' : X → Y) (hs' : B.IsScPlusSection s'), s' ∈ B.allowableSections N U → ∀ ε > 0,
          ∃ (s : X → Y) (hs : B.IsScPlusSection s), s ∈ O ∧ ∀ x, B.sectionDistAt N hs hs' x ≤ ε) ∧
        ∀ s ∈ O,
          (∀ x ∈ solutionSet P (sectionAdd P f s), B.IsGeneralPositionGerm (sectionAdd P f s) x) ∧
          IsCompact (solutionSet P (sectionAdd P f s)) ∧
          ∃ hsub : PX.IsSubMPolyfold (solutionSet P (sectionAdd P f s)),
            haveI := PX.paracompactSpace_subtype (solutionSet P (sectionAdd P f s))
            (MPolyfold.subPolyfold hsub).HasCornerStructure ∧
              ∀ a : solutionSet P (sectionAdd P f s),
                (MPolyfold.subPolyfold hsub).degIndex a = PX.degIndex a :=
  theorem_5_3_10_2021 hX hbump (StrongBundle.isScFredholmSectionTame2021_iff.1 hf) hS hN

/-- **2021 Theorem 5.3.12, p. 222 (perturbation and transversality: good position)**, with the
book's quantifiers and the 2021 notions.  Let `P : Y → X` be a strong bundle over an M-polyfold
admitting sc-smooth bump functions, `f` an sc-Fredholm section (2021 sense) with compact solution
set, `N` an auxiliary norm, and `(f, x)` in good position (2021 sense) at every zero `x ∈ ∂X`.
There is an open `U ⊇ S_f` such that `S_{f+s}` is compact for every `s ∈ Γ^{+,1}_U(P)`, and for
every `ε > 0` an `s ∈ Γ^{+,1}_U(P)` with `N(s(x)) ≤ ε`, `s = 0` near `∂X`, `f + s` transversal and
in good position at every zero, such that a nonempty `S_{f+s}` is a sub-M-polyfold whose induced
structure is that of a manifold with boundary with corners. -/
theorem theorem_5_3_12_book_2021def (hbump : PX.AdmitsBumpFunctions) {f : X → Y}
    (hf : B.IsScFredholmSectionTame2021 f) (hS : IsCompact (solutionSet P f)) {N : B.One → ℝ}
    (hN : B.IsAuxNorm N)
    (hbd : ∀ x ∈ PX.boundary, IsZeroAt P f x → B.IsGoodPositionGermTame2021 f x) :
    ∃ U : Set X, IsOpen U ∧ solutionSet P f ⊆ U ∧
      (∀ s ∈ B.allowableSections N U, IsCompact (solutionSet P (sectionAdd P f s))) ∧
      ∀ ε > 0, ∃ s ∈ B.allowableSections N U,
        (∀ x (hx : s x ∈ B.oneSet), N (B.oneMk (s x) hx) ≤ ε) ∧
        (∀ᶠ x in 𝓝ˢ PX.boundary, IsZeroAt P s x) ∧
        B.IsTransversal (sectionAdd P f s) ∧
        (∀ x ∈ solutionSet P (sectionAdd P f s),
          B.IsGoodPositionGermTame2021 (sectionAdd P f s) x) ∧
        ((solutionSet P (sectionAdd P f s)).Nonempty →
          ∃ hsub : PX.IsSubMPolyfold (solutionSet P (sectionAdd P f s)),
            haveI := PX.paracompactSpace_subtype (solutionSet P (sectionAdd P f s))
            (MPolyfold.subPolyfold hsub).IsManifoldWithCornersLoc) := by
  obtain ⟨U, hUo, hSU, hcpt, hε⟩ :=
    theorem_5_3_12_2021 hbump (StrongBundle.isScFredholmSectionTame2021_iff.1 hf) hS hN
      fun x hx hx0 => StrongBundle.isGoodPositionGermTame2021_iff.1 (hbd x hx hx0)
  refine ⟨U, hUo, hSU, hcpt, fun ε hε0 => ?_⟩
  obtain ⟨s, hs, hN', hbd', htr, hgood, hman⟩ := hε ε hε0
  exact ⟨s, hs, hN', hbd', htr,
    fun x hx => StrongBundle.isGoodPositionGermTame2021_iff.2 (hgood x hx), hman⟩

end BookForm2021

end Polyfold
