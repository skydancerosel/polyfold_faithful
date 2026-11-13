import Polyfold.Chapter6.CobordismOrientationEnds2021d

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.7, p. 277–279:
**Theorem 6.7.1** (preprint Theorem 6.43; 2017 Theorem 6.4) and its case `∂X = ∅` (p. 279).

# Theorem 6.7.1

`theorem_6_7_1` and `theorem_6_7_1_noBoundary` are the statements of `theorem_6_7_1_hyp` and
`theorem_6_7_1_noBoundary_hyp` (`Theorem671Assembly2021.lean`) without their two hypotheses on
the cobordism `S_F`:

* the relative form `p₁^*ω − dβ` on `S_F` is built in `cobordismRelativeFormsInner`
  (`CobordismRelativeForms2021b.lean`), which gives `theorem_6_7_1_of_orientation`;
* the orientation of `S_F`, of product form `e ∧ o_{S_i}` on the two ends (Remark 6.6.19), is
  `cobordismOrientationHyp` (`CobordismOrientationEnds2021d.lean`).

The standing hypotheses are those of the earlier forms: `X` tame (`hX`) with sc-smooth bump
functions (`hbump`); sc-Fredholm sections have tame germ data; part (2) is read as in R-d
(a proper homotopy `S` from `f₀`, `f₁ = f₀ + S(1, ·)`, `o₁` induced by `o₀`).
-/

open Set

noncomputable section

namespace Polyfold

universe u v

open MPolyfold StrongBundle

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

/-- **2021 Theorem 6.7.1** (p. 277; preprint Theorem 6.43; 2017 Theorem 6.4): for a strong
bundle over a tame M-polyfold `X` with sc-smooth bump functions there is `Ψ` assigning to every
proper oriented sc-Fredholm section `(f, o)` linear maps `Ψ_{(f,o)} : H^k_{dR}(X, ∂X) → ℝ` such
that (1) for every auxiliary norm `N` there is a neighbourhood `U` of `S_f` as in Theorem 5.3.6,
and for every such `U` and every admissible `s` (`N(s) ≤ 1`, support in `U`, `f + s` in general
position), `Ψ_{(f,o)}([ω, τ]) = ∫_{S_{f+s}} ω − ∫_{∂S_{f+s}} τ` over the index-`k` part of
`S_{f+s}`, a compact manifold with boundary with corners oriented by `o`; (2) `Ψ` is invariant
along proper oriented homotopies. The statement is that of `theorem_6_7_1_hyp`, without
hypotheses on the cobordism: `theorem_6_7_1_of_orientation` and `cobordismOrientationHyp`. -/
theorem theorem_6_7_1 (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions) :
    ∃ Ψ : ∀ (f : X → Y) (hf : B.IsScFredholmSectionTame f), B.IsProper f →
        SectionOrientation f hf.toIsScFredholmSection → ∀ k : ℕ, relDeRham hX k →ₗ[ℝ] ℝ,
      (∀ (f : X → Y) (hf : B.IsScFredholmSectionTame f) (hP : B.IsProper f)
          (o : SectionOrientation f hf.toIsScFredholmSection) (N : B.One → ℝ), B.IsAuxNorm N →
        (∃ U : Set X, IsOpen U ∧ solutionSet P f ⊆ U ∧
          ∀ C : ℝ, 0 < C → IsCompact (closure {x ∈ U | B.AuxLe N (f x) C})) ∧
        ∀ U : Set X, IsOpen U → solutionSet P f ⊆ U →
          (∀ C : ℝ, 0 < C → IsCompact (closure {x ∈ U | B.AuxLe N (f x) C})) →
          (∀ s ∈ B.allowableSections N U, IsCompact (solutionSet P (sectionAdd P f s))) ∧
          (∃ s, B.IsAdmissible f N U s) ∧
          ∀ (s : X → Y) (hs : B.IsAdmissible f N U s),
            IsCompact (solutionSet P (sectionAdd P f s)) ∧
            solutionSet P (sectionAdd P f s) = ⋃ k : ℕ, B.solPart f s k ∧
            ∀ k : ℕ, IsCompact (B.solPart f s k) ∧ SolPartIsOrientedManifold hX hf hs o k ∧
              ∀ c : LinearMap.ker (relD hX k),
                Ψ f hf hP o k (relDeRhamMk hX k c) =
                  solIntegral hX hbump hf hs o k c - solBoundaryIntegral hX hbump hf hs o k c) ∧
      ∀ (f₀ : X → Y) (hf₀ : B.IsScFredholmSectionTame f₀) (hP₀ : B.IsProper f₀)
        (o₀ : SectionOrientation f₀ hf₀.toIsScFredholmSection)
        (S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))
        (hf₁ : B.IsScFredholmSectionTame (sectionAdd P f₀ (pullbackSlice S 1)))
        (hP₁ : B.IsProper (sectionAdd P f₀ (pullbackSlice S 1)))
        (o₁ : SectionOrientation (sectionAdd P f₀ (pullbackSlice S 1)) hf₁.toIsScFredholmSection),
        IsProperOrientedHomotopyBetween hf₀ o₀ S o₁ →
          ∀ k : ℕ, Ψ f₀ hf₀ hP₀ o₀ k = Ψ _ hf₁ hP₁ o₁ k :=
  theorem_6_7_1_of_orientation hX hbump (cobordismOrientationHyp hX hbump)

/-- **2021 p. 279, the case `∂X = ∅` of Theorem 6.7.1** (2017: after Theorem 6.4; preprint
p. 233): for `X` without boundary there is `Φ` assigning to every proper oriented sc-Fredholm
section linear maps `Φ_{(f,o)} : H^k_{dR}(X) → ℝ` with `Φ([ω]) = ∫_{S_{f+s}} ω` in the degree
`n` of the (constant) index and `Φ = 0` in the other degrees, invariant along proper oriented
homotopies. The statement is that of `theorem_6_7_1_noBoundary_hyp`, without hypotheses on the
cobordism: `theorem_6_7_1_noBoundary_of_orientation` and `cobordismOrientationHyp`. -/
theorem theorem_6_7_1_noBoundary (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hbd : PX.IsWithoutBoundary) :
    ∃ Φ : ∀ (f : X → Y) (hf : B.IsScFredholmSectionTame f), B.IsProper f →
        SectionOrientation f hf.toIsScFredholmSection →
          ∀ k : ℕ, (BundledMPolyfold.of PX).scDeRham k →ₗ[ℝ] ℝ,
      (∀ (f : X → Y) (hf : B.IsScFredholmSectionTame f) (hP : B.IsProper f)
          (o : SectionOrientation f hf.toIsScFredholmSection) (N : B.One → ℝ), B.IsAuxNorm N →
        (∃ U : Set X, IsOpen U ∧ solutionSet P f ⊆ U ∧
          ∀ C : ℝ, 0 < C → IsCompact (closure {x ∈ U | B.AuxLe N (f x) C})) ∧
        ∀ U : Set X, IsOpen U → solutionSet P f ⊆ U →
          (∀ C : ℝ, 0 < C → IsCompact (closure {x ∈ U | B.AuxLe N (f x) C})) →
          (∃ s, B.IsAdmissible f N U s) ∧
          ∀ (s : X → Y) (hs : B.IsAdmissible f N U s) (n : ℕ),
            (∀ x ∈ PX.smoothSet, B.IsIndexAt f x n) →
            IsCompact (solutionSet P (sectionAdd P f s)) ∧
            B.solPart f s n = solutionSet P (sectionAdd P f s) ∧
            (∀ c : LinearMap.ker ((BundledMPolyfold.of PX).formsInftyD n),
              letI := solPartChartedSpace hX hf hs n
              haveI := isManifold_solPart hX hf hs n
              Φ f hf hP o n ((BundledMPolyfold.of PX).scDeRhamMk n c) =
                ManifoldForm.integral (solPartOr hX hf hs o n)
                  (formsInftyRestrict n (hasCornerStructureOfDim_solPart hX hf hs n)
                    (c : (BundledMPolyfold.of PX).formsInfty n))) ∧
            ∀ k : ℕ, k ≠ n → Φ f hf hP o k = 0) ∧
      ∀ (f₀ : X → Y) (hf₀ : B.IsScFredholmSectionTame f₀) (hP₀ : B.IsProper f₀)
        (o₀ : SectionOrientation f₀ hf₀.toIsScFredholmSection)
        (S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))
        (hf₁ : B.IsScFredholmSectionTame (sectionAdd P f₀ (pullbackSlice S 1)))
        (hP₁ : B.IsProper (sectionAdd P f₀ (pullbackSlice S 1)))
        (o₁ : SectionOrientation (sectionAdd P f₀ (pullbackSlice S 1)) hf₁.toIsScFredholmSection),
        IsProperOrientedHomotopyBetween hf₀ o₀ S o₁ →
          ∀ k : ℕ, Φ f₀ hf₀ hP₀ o₀ k = Φ _ hf₁ hP₁ o₁ k :=
  theorem_6_7_1_noBoundary_of_orientation hX hbump hbd (cobordismOrientationHyp hX hbump)

end Polyfold
