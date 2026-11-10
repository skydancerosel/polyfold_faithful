import Polyfold.Chapter6.InvariantSingle2021
import Polyfold.Chapter6.ProperHomotopy2021
import Polyfold.Chapter3.NonVacuity
import Polyfold.Chapter9.Boundary

/-!
# 2021 Theorem 6.7.1 (p. 277; preprint Theorem 6.43) and the case `∂X = ∅` (p. 279)

Theorem 6.7.1 associates with a proper oriented sc-Fredholm section `(f, o)` of a strong bundle
over a tame M-polyfold with sc-smooth bump functions a linear map
`Ψ_{(f,o)} : H*_dR(X, ∂X) → ℝ`, given by `∫_{S_{f+s}} ω − ∫_{∂S_{f+s}} τ` for every admissible `s`
(1), and invariant under proper oriented homotopies (2). This file assembles the theorem from the
two steps of its proof, stated as `Prop`s:

* (A) `PsiIndepAdmissible`: `Ψ_s` (`psiAt`, `InvariantSingle2021`) is the same for two sections
  admissible for one pair `(N, U)` (the cobordism argument, p. 277–279);
* (B) `PsiIndepHomotopy`: `Ψ_{s₀}(f₀, o₀) = Ψ_{s₁}(f₁, o₁)` along a proper oriented homotopy
  ("the same homotopy argument", p. 279).

Both use only the API of `InvariantSingle2021` and `ProperHomotopy2021`; they are proved elsewhere
(wave 4b, `InvariantCobordism2021`), and this file does not import that proof.

## Main declarations

* `psiInvariant`: `Ψ_{(f,o)}`, `psiAt` for one chosen admissible section (`AdmissibleData`).
* `psiInvariant_eq_psiAt`: by (A), `Ψ = Ψ_s` for every `N`, every `U` with the margin of reading
  R-b and every `s` admissible for `(N, U)`; two norms are compared through a section admissible
  for both (`exists_admissible_two`, `psiAt_congr_admissible`).
* `psiInvariant_spec`, `psiInvariant_homotopy`: (1) and (2) for `psiInvariant`.
* `theorem_6_7_1_of_indep`: Theorem 6.7.1, with the trace of each hypothesis to the text.
* `theorem_6_7_1_noBoundary_of_indep`: the case `∂X = ∅` (p. 279), `Φ = Ψ` on `Hᵏ_sc(X)`, with
  `Φ([ω]) = ∫_{S_{f+s}} ω` in the degree `n` of the (constant) index and `Φ = 0` otherwise.
* `theorem_6_7_1_witness`: on the point `ℝ⁰` with the zero bundle and `f = 0`, the hypotheses hold
  and `Ψ([1]) = ±1`.

## Readings (plan section 0)

* R-b: the `U` of (1) is a neighbourhood of `S_f` with `cl{x ∈ U | N(f x) ≤ C}` compact for
  `C > 0`; (1) is stated for every such `U` (and such `U` exist for every `N`).
* R-c: degree `k` is paired with the part `S_k` of `S_{f+s}` where `f` has index `k`; this is the
  text's "the integrals are defined to be zero if the dimensions do not agree".
* R-d: the proper oriented homotopy of (2), which the text does not define, is
  `IsProperOrientedHomotopyBetween` (`f₁ = f₀ + S(1, ·)`, `o₁ = o₀.sectionAdd`).
-/

open Set Filter Topology Manifold Module MeasureTheory

noncomputable section

namespace Polyfold

universe u v

open MPolyfold StrongBundle

section Interface

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

variable (B : StrongBundle PX P) (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)

/-- **(A) `Ψ_s` does not depend on the admissible section** (2021 Theorem 6.7.1, proof of (1),
p. 277–279, the cobordism `S_F` between `S_{f+s₀}` and `S_{f+s₁}`): for a proper oriented
sc-Fredholm section `(f, o)`, an auxiliary norm `N`, an open `U ⊇ S_f` with the margin of reading
R-b (`cl{x ∈ U | N(f x) ≤ C}` compact for `C > 0`, as `exists_isAdmissible_nbhd` provides), and
two sections `s₀`, `s₁` admissible for `(N, U)`, the maps `Ψ_{s₀}` and `Ψ_{s₁}` (`psiAt`) agree in
every degree. Stated as a `Prop` so that Theorem 6.7.1 can be assembled from it
(`theorem_6_7_1_of_indep`); wave 4b proves it. -/
def PsiIndepAdmissible : Prop :=
  ∀ (f : X → Y) (hf : B.IsScFredholmSectionTame f), B.IsProper f →
    ∀ (o : SectionOrientation f hf.toIsScFredholmSection) (N : B.One → ℝ), B.IsAuxNorm N →
      ∀ U : Set X, IsOpen U → solutionSet P f ⊆ U →
        (∀ C : ℝ, 0 < C → IsCompact (closure {x ∈ U | B.AuxLe N (f x) C})) →
        ∀ (s₀ s₁ : X → Y) (hs₀ : B.IsAdmissible f N U s₀) (hs₁ : B.IsAdmissible f N U s₁)
          (k : ℕ), psiAt hX hbump hf hs₀ o k = psiAt hX hbump hf hs₁ o k

/-- **(B) `Ψ` is invariant under a proper oriented homotopy** (2021 Theorem 6.7.1 (2), p. 277, and
its proof, p. 279: "the same homotopy argument as in (1)"): for a proper oriented homotopy `S` from
`(f₀, o₀)` to `(f₁, o₁)`, `f₁ = f₀ + S(1, ·)`, `o₁ = o₀.sectionAdd`
(`IsProperOrientedHomotopyBetween`, reading R-d), and sections `s₀`, `s₁` admissible for `f₀`, `f₁`
with respect to pairs `(N₀, U₀)`, `(N₁, U₁)` whose neighbourhoods have the margin of reading R-b,
`Ψ_{s₀}(f₀, o₀) = Ψ_{s₁}(f₁, o₁)` in every degree. Stated as a `Prop` (wave 4b proves it). -/
def PsiIndepHomotopy : Prop :=
  ∀ (f₀ : X → Y) (hf₀ : B.IsScFredholmSectionTame f₀)
    (o₀ : SectionOrientation f₀ hf₀.toIsScFredholmSection)
    (S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))
    (hf₁ : B.IsScFredholmSectionTame (sectionAdd P f₀ (pullbackSlice S 1)))
    (o₁ : SectionOrientation (sectionAdd P f₀ (pullbackSlice S 1)) hf₁.toIsScFredholmSection),
    IsProperOrientedHomotopyBetween hf₀ o₀ S o₁ →
    ∀ (N₀ : B.One → ℝ), B.IsAuxNorm N₀ → ∀ U₀ : Set X, IsOpen U₀ → solutionSet P f₀ ⊆ U₀ →
      (∀ C : ℝ, 0 < C → IsCompact (closure {x ∈ U₀ | B.AuxLe N₀ (f₀ x) C})) →
    ∀ (N₁ : B.One → ℝ), B.IsAuxNorm N₁ → ∀ U₁ : Set X, IsOpen U₁ →
      solutionSet P (sectionAdd P f₀ (pullbackSlice S 1)) ⊆ U₁ →
      (∀ C : ℝ, 0 < C → IsCompact (closure {x ∈ U₁ |
        B.AuxLe N₁ (sectionAdd P f₀ (pullbackSlice S 1) x) C})) →
    ∀ (s₀ s₁ : X → Y) (hs₀ : B.IsAdmissible f₀ N₀ U₀ s₀)
      (hs₁ : B.IsAdmissible (sectionAdd P f₀ (pullbackSlice S 1)) N₁ U₁ s₁) (k : ℕ),
      psiAt hX hbump hf₀ hs₀ o₀ k = psiAt hX hbump hf₁ hs₁ o₁ k

end Interface

/-! ### The choice of one admissible section, and `Ψ` -/

section Assembly

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

namespace StrongBundle

/-- **The neighbourhood `U` of the §6.7 preamble** (2021 p. 276): if `U ⊇ S_f` has the margin
`cl{x ∈ U | N(f x) ≤ 1}` compact, then `S_{f+s}` is compact for every allowable `s`
(Remark 5.3.4, `remark_5_3_4`). -/
theorem isCompact_solutionSet_sectionAdd_of_margin {f : X → Y} (hf : B.IsScFredholmSection f)
    {N : B.One → ℝ} (hN : B.IsAuxNorm N) {U : Set X} (hSU : solutionSet P f ⊆ U)
    (hmar : IsCompact (closure {x ∈ U | B.AuxLe N (f x) 1})) {s : X → Y}
    (hs : s ∈ B.allowableSections N U) : IsCompact (solutionSet P (sectionAdd P f s)) := by
  obtain ⟨hs, hssupp, hsN⟩ := hs
  have hsU : ∀ x ∉ U, IsZeroAt P s x := fun x hx =>
    not_not.1 fun hne => hx (hssupp (subset_closure hne))
  have hsN' : ∀ x, B.AuxLe N (s x) 1 := fun x => ⟨hs.mem_oneSet x, hsN x _⟩
  obtain ⟨-, hcl⟩ := remark_5_3_4 hN hf.isScSmooth.1 hSU hmar hs.1 hsU hsN'
  exact hcl.of_isClosed_subset
    (isClosed_solutionSet (theorem_3_1_18_preprint hf hs).isScSmooth) subset_closure

variable (B) in
/-- **The data that define `Ψ`** (2021 Theorem 6.7.1, proof of (1), p. 277): an auxiliary norm
`N`, an open `U ⊇ S_f` with the margin of reading R-b, and a section `s` admissible for `(N, U)`. -/
structure AdmissibleData (f : X → Y) where
  /-- The auxiliary norm. -/
  N : B.One → ℝ
  /-- The neighbourhood of `S_f`. -/
  U : Set X
  /-- The admissible section. -/
  s : X → Y
  isAuxNorm : B.IsAuxNorm N
  isOpen : IsOpen U
  subset : solutionSet P f ⊆ U
  margin : ∀ C : ℝ, 0 < C → IsCompact (closure {x ∈ U | B.AuxLe N (f x) C})
  isAdmissible : B.IsAdmissible f N U s

/-- **The data exist** for every tame `f` with compact solution set: an auxiliary norm
(Proposition 5.1.3, `proposition_5_1_3_exists`), the neighbourhood and an admissible section
(Theorem 5.3.10, `exists_isAdmissible_nbhd`). -/
theorem nonempty_admissibleData (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions) {f : X → Y}
    (hf : B.IsScFredholmSectionTame f) (hS : IsCompact (solutionSet P f)) :
    Nonempty (B.AdmissibleData f) := by
  obtain ⟨N, hN⟩ := proposition_5_1_3_exists (B := B)
  obtain ⟨U, hUo, hSU, hmar, -, s, hs⟩ := exists_isAdmissible_nbhd hX hbump hf hS hN
  exact ⟨⟨N, U, s, hN, hUo, hSU, hmar, hs⟩⟩

end StrongBundle

variable (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)

/-- **The map `Ψ_{(f,o)}` of 2021 Theorem 6.7.1** (p. 277, formula (6.35)): `psiAt` for one
chosen admissible section (`AdmissibleData`, chosen with `Classical.choice`). By (A)
(`PsiIndepAdmissible`) it does not depend on the choice (`psiInvariant_eq_psiAt`). -/
def psiInvariant {f : X → Y} (hf : B.IsScFredholmSectionTame f) (hP : B.IsProper f)
    (o : SectionOrientation f hf.toIsScFredholmSection) (k : ℕ) : relDeRham hX k →ₗ[ℝ] ℝ :=
  psiAt hX hbump hf (Classical.choice (nonempty_admissibleData hX hbump hf hP.1)).isAdmissible o k

/-- **`Ψ` is `Ψ_s` for every admissible `s`** (2021 Theorem 6.7.1 (1), p. 277): for every
auxiliary norm `N`, every open `U ⊇ S_f` with the margin of reading R-b and every `s` admissible
for `(N, U)`, `Ψ_{(f,o)} = Ψ_s`. The chosen section `s*` (for `(N*, U*)`) and `s` are compared
through a third section `s₂` admissible for both pairs (`exists_admissible_two`): (A) for
`(N*, U*)`, `psiAt_congr_admissible`, (A) for `(N, U)`. -/
theorem psiInvariant_eq_psiAt (hA : PsiIndepAdmissible B hX hbump) {f : X → Y}
    (hf : B.IsScFredholmSectionTame f) (hP : B.IsProper f)
    (o : SectionOrientation f hf.toIsScFredholmSection) {N : B.One → ℝ} (hN : B.IsAuxNorm N)
    {U : Set X} (hU : IsOpen U) (hSU : solutionSet P f ⊆ U)
    (hmar : ∀ C : ℝ, 0 < C → IsCompact (closure {x ∈ U | B.AuxLe N (f x) C}))
    {s : X → Y} (hs : B.IsAdmissible f N U s) (k : ℕ) :
    psiInvariant hX hbump hf hP o k = psiAt hX hbump hf hs o k := by
  set D := Classical.choice (nonempty_admissibleData hX hbump hf hP.1) with hD
  obtain ⟨s₂, h₂D, h₂, hgp⟩ := exists_admissible_two hX hbump hf hP.1 D.isAuxNorm hN D.isOpen hU
    D.subset hSU
  have hs₂D : B.IsAdmissible f D.N D.U s₂ := ⟨h₂D, hgp⟩
  have hs₂ : B.IsAdmissible f N U s₂ := ⟨h₂, hgp⟩
  calc psiInvariant hX hbump hf hP o k = psiAt hX hbump hf D.isAdmissible o k := rfl
    _ = psiAt hX hbump hf hs₂D o k :=
      hA f hf hP o D.N D.isAuxNorm D.U D.isOpen D.subset D.margin _ _ D.isAdmissible hs₂D k
    _ = psiAt hX hbump hf hs₂ o k := by rw [psiAt_congr_admissible hX hbump hf hs₂D o hs₂]
    _ = psiAt hX hbump hf hs o k := hA f hf hP o N hN U hU hSU hmar _ _ hs₂ hs k

/-- **2021 Theorem 6.7.1 (1)** (p. 277) for `Ψ = psiInvariant`, for every auxiliary norm `N`
and every open `U ⊇ S_f` with the margin of reading R-b: `S_{f+s}` is compact for every allowable
`s`, admissible sections exist, and for each admissible `s`, `S_{f+s}` is compact, is the union of
its index parts `S_k` (reading R-c), each `S_k` is a compact oriented manifold with boundary and
corners of dimension `k` (`SolPartIsOrientedManifold`), and
`Ψ([ω, τ]) = ∫_{S_k} ω − ∫_{∂S_k} τ` in degree `k`. -/
theorem psiInvariant_spec (hA : PsiIndepAdmissible B hX hbump) {f : X → Y}
    (hf : B.IsScFredholmSectionTame f) (hP : B.IsProper f)
    (o : SectionOrientation f hf.toIsScFredholmSection) {N : B.One → ℝ} (hN : B.IsAuxNorm N)
    {U : Set X} (hU : IsOpen U) (hSU : solutionSet P f ⊆ U)
    (hmar : ∀ C : ℝ, 0 < C → IsCompact (closure {x ∈ U | B.AuxLe N (f x) C})) :
    (∀ s ∈ B.allowableSections N U, IsCompact (solutionSet P (sectionAdd P f s))) ∧
    (∃ s, B.IsAdmissible f N U s) ∧
    ∀ (s : X → Y) (hs : B.IsAdmissible f N U s),
      IsCompact (solutionSet P (sectionAdd P f s)) ∧
      solutionSet P (sectionAdd P f s) = ⋃ k : ℕ, B.solPart f s k ∧
      ∀ k : ℕ, IsCompact (B.solPart f s k) ∧ SolPartIsOrientedManifold hX hf hs o k ∧
        ∀ c : LinearMap.ker (relD hX k),
          psiInvariant hX hbump hf hP o k (relDeRhamMk hX k c) =
            solIntegral hX hbump hf hs o k c - solBoundaryIntegral hX hbump hf hs o k c := by
  have hcpt : ∀ s ∈ B.allowableSections N U, IsCompact (solutionSet P (sectionAdd P f s)) :=
    fun s hs => isCompact_solutionSet_sectionAdd_of_margin hf.toIsScFredholmSection hN hSU
      (hmar 1 one_pos) hs
  refine ⟨hcpt, exists_isAdmissible hX hbump hf hP.1 hN hU hSU, fun s hs => ?_⟩
  have hS := hcpt s hs.mem
  refine ⟨hS, solutionSet_eq_iUnion_solPart hf hs.isScPlusSection hs.gp, fun k => ?_⟩
  refine ⟨isCompact_solPart hf hs.isScPlusSection hs.gp hS k,
    solPartIsOrientedManifold hX hbump hf hs o k, fun c => ?_⟩
  rw [psiInvariant_eq_psiAt hX hbump hA hf hP o hN hU hSU hmar hs k]
  exact psiAt_mk hX hbump hf hs o k c

/-- **2021 Theorem 6.7.1 (2)** (p. 277) for `Ψ = psiInvariant`: a proper oriented homotopy from
`(f₀, o₀)` to `(f₁, o₁)` (`IsProperOrientedHomotopyBetween`, reading R-d) gives
`Ψ_{(f₀,o₀)} = Ψ_{(f₁,o₁)}`, by (B) (`PsiIndepHomotopy`) applied to the two chosen sections. -/
theorem psiInvariant_homotopy (hB : PsiIndepHomotopy B hX hbump) {f₀ : X → Y}
    (hf₀ : B.IsScFredholmSectionTame f₀) (hP₀ : B.IsProper f₀)
    (o₀ : SectionOrientation f₀ hf₀.toIsScFredholmSection)
    {S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
    (hf₁ : B.IsScFredholmSectionTame (sectionAdd P f₀ (pullbackSlice S 1)))
    (hP₁ : B.IsProper (sectionAdd P f₀ (pullbackSlice S 1)))
    {o₁ : SectionOrientation (sectionAdd P f₀ (pullbackSlice S 1)) hf₁.toIsScFredholmSection}
    (hH : IsProperOrientedHomotopyBetween hf₀ o₀ S o₁) (k : ℕ) :
    psiInvariant hX hbump hf₀ hP₀ o₀ k = psiInvariant hX hbump hf₁ hP₁ o₁ k := by
  set D₀ := Classical.choice (nonempty_admissibleData hX hbump hf₀ hP₀.1)
  set D₁ := Classical.choice (nonempty_admissibleData hX hbump hf₁ hP₁.1)
  exact hB f₀ hf₀ o₀ S hf₁ o₁ hH D₀.N D₀.isAuxNorm D₀.U D₀.isOpen D₀.subset D₀.margin
    D₁.N D₁.isAuxNorm D₁.U D₁.isOpen D₁.subset D₁.margin _ _ D₀.isAdmissible D₁.isAdmissible k

end Assembly

/-! ### Theorem 6.7.1 -/

section Theorem

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

/-- **2021 Theorem 6.7.1** (p. 277; preprint Theorem 6.43), assembled from (A) and (B).

There is a map `Ψ` which associates with a proper oriented sc-Fredholm section `(f, o)` a linear
map `Ψ_{(f,o)} : Hᵏ_dR(X, ∂X) → ℝ` in every degree `k`, with:
* (1) for every auxiliary norm `N` there are open neighbourhoods `U ⊇ S_f` with the margin of
  reading R-b; for each such `U`, `S_{f+s}` is compact for every allowable `s`, admissible
  sections exist, and for each admissible `s`, `S_{f+s}` is compact, is the union of its index
  parts `S_k`, each `S_k` is a compact oriented manifold with boundary and corners of dimension `k`,
  and `Ψ([ω, τ]) = ∫_{S_k} ω − ∫_{∂S_k} τ`;
* (2) `Ψ_{(f₀,o₀)} = Ψ_{(f₁,o₁)}` for a proper oriented homotopy between `(f₀, o₀)` and `(f₁, o₁)`.

**Trace of the hypotheses to the text.**
* `hX` (tame), `hbump` (sc-smooth bump functions), the strong bundle `B`: the first two sentences
  of the theorem.
* `hA`, `hB` are not hypotheses of the text: they are (A) and (B), the two steps of its proof
  (independence of the admissible section, p. 277–279, and "the same homotopy argument", p. 279),
  stated as `PsiIndepAdmissible` and `PsiIndepHomotopy` and proved separately (wave 4b).
* In `Ψ`: `hf`, "sc-Fredholm section" (the library's tame form, Definition 3.6.4; the 2021
  definition via `isScFredholmSectionTame2021_iff`); `hP`, "proper", Definition 5.2.1 (3); `o`,
  "oriented", Definition 6.6.16.
* In (1): `N`, "auxiliary norm", Definition 5.1.1; the neighbourhood `U` of the §6.7 preamble
  (p. 276) from Theorem 5.3.10, read with the margin `cl{x ∈ U | N(f x) ≤ C}` compact (reading
  R-b; such `U` exist, the first clause); "admissible for `(N, U)`", the §6.7 preamble
  (`IsAdmissible`); the compact oriented manifold and the formula, (1) with (6.35); the rule
  "the integrals are zero if the dimensions do not agree" as the pairing of degree `k` with the
  part `S_k` of index `k` (reading R-c).
* In (2): the proper oriented homotopy, not defined in the text, read as in R-d
  (`IsProperOrientedHomotopyBetween`: `f₁ = f₀ + S(1, ·)`, `o₁ = o₀.sectionAdd`); `hP₀`, `hP₁`
  are implied by it (`IsProperOrientedHomotopy.isProper_zero`, `isProper_one`) and are there
  because `Ψ` takes them. -/
theorem theorem_6_7_1_of_indep (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hA : PsiIndepAdmissible B hX hbump) (hB : PsiIndepHomotopy B hX hbump) :
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
          ∀ k : ℕ, Ψ f₀ hf₀ hP₀ o₀ k = Ψ _ hf₁ hP₁ o₁ k := by
  refine ⟨fun f hf hP o k => psiInvariant hX hbump hf hP o k, fun f hf hP o N hN => ⟨?_, ?_⟩,
    fun f₀ hf₀ hP₀ o₀ S hf₁ hP₁ o₁ hH k =>
      psiInvariant_homotopy hX hbump hB hf₀ hP₀ o₀ hf₁ hP₁ hH k⟩
  · obtain ⟨U, hUo, hSU, hmar, -⟩ := exists_isAdmissible_nbhd hX hbump hf hP.1 hN
    exact ⟨U, hUo, hSU, hmar⟩
  · exact fun U hU hSU hmar => psiInvariant_spec hX hbump hA hf hP o hN hU hSU hmar

end Theorem

/-! ### The case `∂X = ∅` (2021 p. 279) -/

section NoBoundary

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)

/-- For `∂X = ∅`, the `ω`-component of a relative form is its image under `relFormsEquiv`. -/
theorem relFormsFst_eq_relFormsEquiv (h : PX.IsWithoutBoundary) :
    ∀ (k : ℕ) (η : RelForms hX k), relFormsFst hX k η = relFormsEquiv h k η
  | 0, _ => rfl
  | _ + 1, _ => rfl

/-- **`Ψ` on `Hᵏ_sc(X)` for `∂X = ∅`** (2021 p. 279): `Ψ_{(f,o)}` composed with
`Hᵏ_sc(X) ≃ Hᵏ_dR(X, ∂X)` (`relDeRhamEquivOfNoBoundary`). -/
def psiInvariantNoBoundary (h : PX.IsWithoutBoundary) {f : X → Y}
    (hf : B.IsScFredholmSectionTame f) (hP : B.IsProper f)
    (o : SectionOrientation f hf.toIsScFredholmSection) (k : ℕ) :
    (BundledMPolyfold.of PX).scDeRham k →ₗ[ℝ] ℝ :=
  (psiInvariant hX hbump hf hP o k).comp
    (relDeRhamEquivOfNoBoundary (hP := hX) k h).symm.toLinearMap

/-- `[ω] ∈ Hᵏ_sc(X)` corresponds to the class of `(ω, 0)` in `Hᵏ_dR(X, ∂X)`. -/
theorem relDeRhamEquivOfNoBoundary_symm_mk (h : PX.IsWithoutBoundary) (k : ℕ)
    (c : LinearMap.ker ((BundledMPolyfold.of PX).formsInftyD k)) :
    (relDeRhamEquivOfNoBoundary (hP := hX) k h).symm ((BundledMPolyfold.of PX).scDeRhamMk k c) =
      relDeRhamMk hX k ((kerRelDEquiv (hP := hX) k h).symm c) := by
  rw [LinearEquiv.symm_apply_eq, relDeRhamEquivOfNoBoundary_mk]
  exact congrArg _ ((kerRelDEquiv (hP := hX) k h).apply_symm_apply c).symm

/-- `Φ = Ψ ∘ (Hᵏ_sc(X) ≃ Hᵏ_dR(X, ∂X))` on elements. -/
theorem psiInvariantNoBoundary_apply (h : PX.IsWithoutBoundary) {f : X → Y}
    (hf : B.IsScFredholmSectionTame f) (hP : B.IsProper f)
    (o : SectionOrientation f hf.toIsScFredholmSection) (k : ℕ)
    (x : (BundledMPolyfold.of PX).scDeRham k) :
    psiInvariantNoBoundary hX hbump h hf hP o k x =
      psiInvariant hX hbump hf hP o k ((relDeRhamEquivOfNoBoundary (hP := hX) k h).symm x) :=
  rfl

/-- **2021 p. 279, degree `n`**: for `∂X = ∅` and `f` of constant index `n`,
`Ψ([ω]) = ∫_{S_{f+s}} ω` for every admissible `s` (here `S_{f+s} = S_n`,
`solPart_eq_solutionSet`). -/
theorem psiInvariantNoBoundary_mk (hA : PsiIndepAdmissible B hX hbump) (h : PX.IsWithoutBoundary)
    {f : X → Y} (hf : B.IsScFredholmSectionTame f) (hP : B.IsProper f)
    (o : SectionOrientation f hf.toIsScFredholmSection) {N : B.One → ℝ} (hN : B.IsAuxNorm N)
    {U : Set X} (hU : IsOpen U) (hSU : solutionSet P f ⊆ U)
    (hmar : ∀ C : ℝ, 0 < C → IsCompact (closure {x ∈ U | B.AuxLe N (f x) C}))
    {s : X → Y} (hs : B.IsAdmissible f N U s) (n : ℕ)
    (c : LinearMap.ker ((BundledMPolyfold.of PX).formsInftyD n)) :
    letI := solPartChartedSpace hX hf hs n
    haveI := isManifold_solPart hX hf hs n
    psiInvariantNoBoundary hX hbump h hf hP o n ((BundledMPolyfold.of PX).scDeRhamMk n c) =
      ManifoldForm.integral (solPartOr hX hf hs o n)
        (formsInftyRestrict n (hasCornerStructureOfDim_solPart hX hf hs n)
          (c : (BundledMPolyfold.of PX).formsInfty n)) := by
  have hS := isCompact_solutionSet_sectionAdd_of_margin hf.toIsScFredholmSection hN hSU
    (hmar 1 one_pos) hs.mem
  have hc : relFormsFst hX n ((kerRelDEquiv (hP := hX) n h).symm c : RelForms hX n) =
      (c : (BundledMPolyfold.of PX).formsInfty n) := by
    rw [relFormsFst_eq_relFormsEquiv hX h, ← coe_kerRelDEquiv, LinearEquiv.apply_symm_apply]
  rw [psiInvariantNoBoundary_apply, relDeRhamEquivOfNoBoundary_symm_mk,
    psiInvariant_eq_psiAt hX hbump hA hf hP o hN hU hSU hmar hs,
    psiAt_mk_of_isWithoutBoundary hX hbump hf hs o h]
  change solFormsIntegral hX hbump hf hs o n (relFormsFst hX n _) = _
  rw [hc]
  exact solFormsIntegral_apply hX hbump hf hs o
    (isCompact_solPart hf hs.isScPlusSection hs.gp hS n) _

/-- **2021 p. 279, the other degrees**, on elements: for `f` of constant index `n`, `Ψ = 0` in
degree `k ≠ n` (`S_k = ∅`, `solPart_eq_empty_of_ne`). -/
theorem psiInvariantNoBoundary_apply_of_ne (hA : PsiIndepAdmissible B hX hbump)
    (h : PX.IsWithoutBoundary) {f : X → Y} (hf : B.IsScFredholmSectionTame f) (hP : B.IsProper f)
    (o : SectionOrientation f hf.toIsScFredholmSection) {n : ℕ}
    (hn : ∀ x ∈ PX.smoothSet, B.IsIndexAt f x n) {k : ℕ} (hk : k ≠ n)
    (x : (BundledMPolyfold.of PX).scDeRham k) :
    psiInvariantNoBoundary hX hbump h hf hP o k x = 0 := by
  obtain ⟨N, hN⟩ := proposition_5_1_3_exists (B := B)
  obtain ⟨U, hUo, hSU, hmar, -, s, hs⟩ := exists_isAdmissible_nbhd hX hbump hf hP.1 hN
  have h1 : psiInvariant hX hbump hf hP o k = 0 :=
    (psiInvariant_eq_psiAt hX hbump hA hf hP o hN hUo hSU hmar hs k).trans
      (psiAt_of_eq_empty hX hbump hf hs o
        (solPart_eq_empty_of_ne hf.toIsScFredholmSection hs.isScPlusSection hn hk))
  rw [psiInvariantNoBoundary_apply]
  simp only [h1, LinearMap.zero_apply]

/-- **2021 p. 279, the other degrees**: for `f` of constant index `n`, `Ψ = 0` in degree `k ≠ n`. -/
theorem psiInvariantNoBoundary_of_ne (hA : PsiIndepAdmissible B hX hbump)
    (h : PX.IsWithoutBoundary) {f : X → Y} (hf : B.IsScFredholmSectionTame f) (hP : B.IsProper f)
    (o : SectionOrientation f hf.toIsScFredholmSection) {n : ℕ}
    (hn : ∀ x ∈ PX.smoothSet, B.IsIndexAt f x n) {k : ℕ} (hk : k ≠ n) :
    psiInvariantNoBoundary hX hbump h hf hP o k = 0 :=
  LinearMap.ext fun x => psiInvariantNoBoundary_apply_of_ne hX hbump hA h hf hP o hn hk x

/-- **Theorem 6.7.1 (2) for `∂X = ∅`**: `Φ` is invariant under proper oriented homotopies. -/
theorem psiInvariantNoBoundary_homotopy (hB : PsiIndepHomotopy B hX hbump)
    (h : PX.IsWithoutBoundary) {f₀ : X → Y}
    (hf₀ : B.IsScFredholmSectionTame f₀) (hP₀ : B.IsProper f₀)
    (o₀ : SectionOrientation f₀ hf₀.toIsScFredholmSection)
    {S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
    (hf₁ : B.IsScFredholmSectionTame (sectionAdd P f₀ (pullbackSlice S 1)))
    (hP₁ : B.IsProper (sectionAdd P f₀ (pullbackSlice S 1)))
    {o₁ : SectionOrientation (sectionAdd P f₀ (pullbackSlice S 1)) hf₁.toIsScFredholmSection}
    (hH : IsProperOrientedHomotopyBetween hf₀ o₀ S o₁) (k : ℕ) :
    psiInvariantNoBoundary hX hbump h hf₀ hP₀ o₀ k =
      psiInvariantNoBoundary hX hbump h hf₁ hP₁ o₁ k :=
  LinearMap.ext fun x => (psiInvariantNoBoundary_apply hX hbump h hf₀ hP₀ o₀ k x).trans
    ((LinearMap.congr_fun (psiInvariant_homotopy hX hbump hB hf₀ hP₀ o₀ hf₁ hP₁ hH k) _).trans
      (psiInvariantNoBoundary_apply hX hbump h hf₁ hP₁ o₁ k x).symm)

/-- **2021 p. 279, the case `∂X = ∅` of Theorem 6.7.1** (after its proof; 2017: after Theorem 6.4;
preprint p. 233), assembled from (A) and (B): there is a map `Φ` which associates with a proper
oriented sc-Fredholm section `(f, o)` a linear map `Φ_{(f,o)} : Hᵏ_sc(X) → ℝ` in each degree `k`
(`Φ = Ψ` under `Hᵏ_sc(X) ≃ Hᵏ_dR(X, ∂X)`, `relDeRhamEquivOfNoBoundary`) such that, for every
auxiliary norm `N`, every neighbourhood `U` as in Theorem 6.7.1 (1) and every `s` admissible for
`(N, U)`: if `f` has constant index `n`, then `S_{f+s}` is compact and equals its part `S_n`,
`Φ([ω]) = ∫_{S_{f+s}} ω` in degree `n` (the integral over the Mathlib manifold `S_n = S_{f+s}`),
and `Φ = 0` in the other degrees; and `Φ` is invariant under proper oriented homotopies.
The hypotheses trace to the text as in `theorem_6_7_1_of_indep`; `hbd` is "`∂X = ∅`", and `hn` is
"`n` is equal to the index of `f`" (at every smooth point). -/
theorem theorem_6_7_1_noBoundary_of_indep (hbd : PX.IsWithoutBoundary)
    (hA : PsiIndepAdmissible B hX hbump) (hB : PsiIndepHomotopy B hX hbump) :
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
          ∀ k : ℕ, Φ f₀ hf₀ hP₀ o₀ k = Φ _ hf₁ hP₁ o₁ k := by
  refine ⟨fun f hf hP o k => psiInvariantNoBoundary hX hbump hbd hf hP o k,
    fun f hf hP o N hN => ⟨?_, fun U hU hSU hmar => ⟨exists_isAdmissible hX hbump hf hP.1 hN hU hSU,
      fun s hs n hn => ⟨?_, ?_, ?_, ?_⟩⟩⟩, fun f₀ hf₀ hP₀ o₀ S hf₁ hP₁ o₁ hH k => ?_⟩
  · obtain ⟨U, hUo, hSU, hmar, -⟩ := exists_isAdmissible_nbhd hX hbump hf hP.1 hN
    exact ⟨U, hUo, hSU, hmar⟩
  · exact isCompact_solutionSet_sectionAdd_of_margin hf.toIsScFredholmSection hN hSU
      (hmar 1 one_pos) hs.mem
  · exact solPart_eq_solutionSet hf.toIsScFredholmSection hs.isScPlusSection hn
  · exact fun c => psiInvariantNoBoundary_mk hX hbump hA hbd hf hP o hN hU hSU hmar hs n c
  · exact fun k hk => psiInvariantNoBoundary_of_ne hX hbump hA hbd hf hP o hn hk
  · exact psiInvariantNoBoundary_homotopy hX hbump hB hbd hf₀ hP₀ o₀ hf₁ hP₁ hH k

end NoBoundary

/-! ### Non-vacuity: the point `ℝ⁰`, the zero bundle and `f = 0` -/

section Witness

open TrivialBundle CategoryTheory

/-- The point `ℝ⁰` admits sc-smooth bump functions (the constant `1`). -/
theorem rnPolyfold_zero_admitsBumpFunctions : (rnPolyfold 0).AdmitsBumpFunctions :=
  fun x _ _ hxU => ⟨fun _ => 1, isScSmoothMap_real_const 1, one_ne_zero,
    fun y _ => by rwa [Subsingleton.elim y x]⟩

/-- The section `f = 0` of the zero bundle `ℝ⁰ × ℝ⁰ → ℝ⁰` (the graph of `0 : ℝ⁰ → ℝ⁰`). -/
abbrev ptSection : (Fin 0 → ℝ) → (Fin 0 → ℝ) × (Fin 0 → ℝ) := graphSection fun _ => 0

/-- `f = 0` is a tame sc-Fredholm section (the graph section of a `C^∞` map, `NonVacuity`). -/
theorem isScFredholmSectionTame_ptSection : (bundle 0 0).IsScFredholmSectionTame ptSection :=
  (isScFredholmSectionTame_graphSection_wholeChart contDiff_const).isScFredholmSectionTame

/-- `f = 0` is proper (its solution set, the point, is compact; Theorem 5.2.2). -/
theorem isProper_ptSection : (bundle 0 0).IsProper ptSection :=
  theorem_5_2_2_preprint isScFredholmSectionTame_ptSection.toIsScFredholmSection
    (Set.toFinite _).isCompact

/-- There is one sc-smooth path between two points of `ℝ⁰`. -/
instance subsingleton_scPath_rnPolyfold_zero (x y : Fin 0 → ℝ) :
    Subsingleton (ScPath (rnPolyfold 0) x y) :=
  ⟨fun a b => by
    cases a; cases b
    congr
    exact Subsingleton.elim _ _⟩

/-- The path category of `ℝ⁰` has only identities. -/
instance subsingleton_hom_pathCat_rnPolyfold_zero (x y : PathCat (rnPolyfold 0)) :
    Subsingleton (x ⟶ y) :=
  ⟨fun a b => Quotient.inductionOn₂ (s₁ := ScPath.setoid _ _ _) (s₂ := ScPath.setoid _ _ _) a b
    fun p q => congrArg _ (Subsingleton.elim p q)⟩

/-- **Every choice `y ↦ o_y` is an orientation of `f = 0` on `ℝ⁰`** (Definition 6.6.16): by
`isSectionOrientation_iff` it suffices that `Γ_f([φ]) o_x = o_y` for the morphisms of the path
category, which are identities (`orFunctorMap_id`). -/
theorem isSectionOrientation_pt
    (o : ∀ y (hy : y ∈ (rnPolyfold 0).smoothSet),
      Orx ptSection isScFredholmSectionTame_ptSection.toIsScFredholmSection y hy) :
    haveI := paracompactSpace_rn_prod (rnPolyfold 0)
    haveI := paracompactSpace_rn_pullback (bundle 0 0)
    IsSectionOrientation ptSection isScFredholmSectionTame_ptSection.toIsScFredholmSection o := by
  have := paracompactSpace_rn_prod (rnPolyfold 0)
  have := paracompactSpace_rn_pullback (bundle 0 0)
  refine (isSectionOrientation_iff rnPolyfold_isTame rnPolyfold_zero_admitsBumpFunctions
    isScFredholmSectionTame_ptSection
    (MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough rnPolyfold_zero_admitsBumpFunctions)
    o).2 fun x y a => ?_
  obtain ⟨xp, xs⟩ := x
  obtain ⟨yp, ys⟩ := y
  obtain rfl : xp = yp := Subsingleton.elim _ _
  have ha : a = 𝟙 (⟨xp, xs⟩ : PathCat (rnPolyfold 0)) := Subsingleton.elim _ _
  rw [ha, orFunctorMap_id]
  rfl

/-- **The tangent spaces of an M-polyfold on a one-point set are `0`**: in a chart `φ` the retract
`O = φ(source)` is one point, whose tangent space is `{0}` (`tangentSpace_singleton_subset`). -/
theorem MPolyfold.subsingleton_tangentFiber {X : Type u} [TopologicalSpace X] [T2Space X]
    [ParacompactSpace X] [Subsingleton X] (P : MPolyfold X) (x : P.Level 1) :
    Subsingleton (P.tangentFiber x) := by
  obtain ⟨φ, hφ, hx⟩ := P.exists_isChart_mem_source (P.levelVal 1 x)
  obtain ⟨R, hR⟩ := φ.model.isScRetract
  have hO : φ.model.O = {φ (P.levelVal 1 x)} := by
    rw [← φ.image_source]
    refine Subset.antisymm ?_ (singleton_subset_iff.2 ⟨_, hx, rfl⟩)
    rintro _ ⟨y, -, rfl⟩
    rw [Subsingleton.elim y (P.levelVal 1 x)]
    rfl
  have hmodel : ∀ v ∈ tangentFiberModel hφ hx, v = 0 := fun v hv => by
    have hv' : v ∈ tangentSpace φ.model.E φ.model.C {φ (P.levelVal 1 x)}
        (levelLift φ 1 (P.levelVal 1 x)) := by
      rw [← hO]; exact (mem_tangentFiberModel hφ hx).1 hv
    exact tangentSpace_singleton_subset R (hR.trans hO)
      (P.toBase_levelLift hφ hx (P.levelVal_mem x)) hv'
  refine ⟨fun α β => (tangentFiberLinearEquiv hφ hx).injective ?_⟩
  exact Subtype.ext ((hmodel _ (Submodule.coe_mem _)).trans (hmodel _ (Submodule.coe_mem _)).symm)

/-- **Forms of positive degree on a one-point M-polyfold vanish.** -/
theorem MPolyfold.form_succ_eq_zero {X : Type u} [TopologicalSpace X] [T2Space X]
    [ParacompactSpace X] [Subsingleton X] (P : MPolyfold X) {k : ℕ}
    (ω : ∀ x : P.Level 1, P.tangentFiber x [⋀^Fin (k + 1)]→ₗ[ℝ] ℝ) : ω = 0 := by
  funext x
  have := P.subsingleton_tangentFiber x
  ext v
  rw [Subsingleton.elim v 0, AlternatingMap.map_zero]
  rfl

/-- The constant `0`-form `1` on `ℝ⁰`, as an element of `Ω⁰_∞`. -/
def ptOne : (BundledMPolyfold.of (rnPolyfold 0)).formsInfty 0 :=
  (BundledMPolyfold.of (rnPolyfold 0)).formsInftyOf 0 0
    ⟨(rnPolyfold 0).constForm 1, constForm_mem_scForms 1⟩

/-- `d1 = 0`: the `1`-forms on `ℝ⁰` vanish (`MPolyfold.form_succ_eq_zero`). -/
theorem formsInftyD_ptOne : (BundledMPolyfold.of (rnPolyfold 0)).formsInftyD 0 ptOne = 0 := by
  rw [ptOne, BundledMPolyfold.formsInftyD_of]
  have : (BundledMPolyfold.of (rnPolyfold 0)).formsD 0 0
      ⟨(rnPolyfold 0).constForm 1, constForm_mem_scForms 1⟩ = 0 :=
    haveI : Subsingleton ((BundledMPolyfold.of (rnPolyfold 0)).lift (0 + 1)).carrier :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim (α := Fin 0 → ℝ) _ _)⟩
    Subtype.ext (MPolyfold.form_succ_eq_zero _ _)
  rw [this, map_zero]

/-- `ℝⁿ` has no boundary. -/
theorem isWithoutBoundary_rnPolyfold (n : ℕ) : (rnPolyfold n).IsWithoutBoundary :=
  rnPolyfold_degIndex n

/-- **`[1]` is a class of `H⁰_dR(ℝ⁰, ∂ℝ⁰)`**: `d1 = 0` and `j^*1 = 0` (`∂ℝ⁰ = ∅`). -/
theorem relD_ptOne : relD (rnPolyfold_isTame (n := 0)) 0 ptOne = 0 := by
  have := subsingleton_bFormsInfty (hP := rnPolyfold_isTame (n := 0)) 0
    (isWithoutBoundary_rnPolyfold 0)
  change relDZero _ ptOne = 0
  rw [relDZero_apply, formsInftyD_ptOne, Subsingleton.elim (jStar _ 0 ptOne) 0]
  rfl

/-- A one-point manifold modelled on `EuclideanQuadrant k` has dimension `k = 0`. -/
theorem eq_zero_of_subsingleton_chartedSpace {k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanQuadrant k) M] [Subsingleton M] (x : M) : k = 0 := by
  by_contra hk
  set e := chartAt (EuclideanQuadrant k) x
  have hp : e x ∈ e.target := e.map_source (mem_chart_source _ x)
  have hsub : e.target ⊆ {e x} := fun q hq => by
    rw [mem_singleton_iff, ← e.right_inv hq, Subsingleton.elim (e.symm q) x]
  have hnhds : ({e x} : Set (EuclideanQuadrant k)) ∈ 𝓝 (e x) :=
    Filter.mem_of_superset (e.open_target.mem_nhds hp) hsub
  set i : Fin k := ⟨0, Nat.pos_of_ne_zero hk⟩
  let γ : ℝ → EuclideanQuadrant k := fun t =>
    ⟨(e x).1 + |t| • EuclideanSpace.single i 1, fun j => by
      have := (e x).2 j
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]
      split_ifs <;> positivity⟩
  have hγ : Continuous γ :=
    (continuous_const.add (continuous_abs.smul continuous_const)).subtype_mk _
  have hγ0 : γ 0 = e x := Subtype.ext (by simp [γ])
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ ({e x} : Set (EuclideanQuadrant k)) :=
    hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hnhds)
  obtain ⟨t, ht, htne⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : {t : ℝ | t ≠ 0} ∈ 𝓝[≠] (0 : ℝ))).exists
  have h := congrArg (fun q : EuclideanQuadrant k => q.1 i) (mem_singleton_iff.1 ht)
  simp only [γ, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, if_true, smul_eq_mul,
    mul_one, add_eq_left, abs_eq_zero] at h
  exact htne h

/-- **An orientation of `f = 0` on the point**: any choice `o_x ∈ Or_x^f` at the one point
(the path category of `ℝ⁰` has only identities, `isSectionOrientation_pt`). -/
def ptOrientation :
    SectionOrientation ptSection isScFredholmSectionTame_ptSection.toIsScFredholmSection :=
  ⟨fun _ hy => (exists_two_orx isScFredholmSectionTame_ptSection.toIsScFredholmSection hy
      (MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough
        rnPolyfold_zero_admitsBumpFunctions)).choose,
    isSectionOrientation_pt _⟩

/-- The sign `orSign b` is `±1`. -/
theorem orSign_eq_one_or (b : Bool) : orSign b = 1 ∨ orSign b = -1 := by
  cases b
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- **`Ψ_s([1]) = ±1` on the point**, for every admissible `s`: `S_{f+s}` is the one point, of
index `0`, and `Ψ([1])` is its sign (`psiAt_mk_zero_eq_sum`). -/
theorem psiAt_ptOne {N : (bundle 0 0).One → ℝ} {U : Set (Fin 0 → ℝ)}
    {s : (Fin 0 → ℝ) → (Fin 0 → ℝ) × (Fin 0 → ℝ)}
    (o : SectionOrientation ptSection isScFredholmSectionTame_ptSection.toIsScFredholmSection)
    (hs : (bundle 0 0).IsAdmissible ptSection N U s) :
    psiAt rnPolyfold_isTame rnPolyfold_zero_admitsBumpFunctions isScFredholmSectionTame_ptSection
        hs o 0 (relDeRhamMk rnPolyfold_isTame 0 ⟨ptOne, relD_ptOne⟩) = 1 ∨
      psiAt rnPolyfold_isTame rnPolyfold_zero_admitsBumpFunctions isScFredholmSectionTame_ptSection
        hs o 0 (relDeRhamMk rnPolyfold_isTame 0 ⟨ptOne, relD_ptOne⟩) = -1 := by
  have hf := isScFredholmSectionTame_ptSection
  have hmem : (0 : Fin 0 → ℝ) ∈ (bundle 0 0).solPart ptSection s 0 := by
    have hz : (0 : Fin 0 → ℝ) ∈ solutionSet (proj 0 0) (sectionAdd (proj 0 0) ptSection s) :=
      Subsingleton.elim (α := (Fin 0 → ℝ) × (Fin 0 → ℝ)) _ _
    rw [solutionSet_eq_iUnion_solPart hf hs.isScPlusSection hs.gp] at hz
    obtain ⟨k, hk⟩ := mem_iUnion.1 hz
    let := solPartChartedSpace rnPolyfold_isTame hf hs k
    obtain rfl : k = 0 := eq_zero_of_subsingleton_chartedSpace
      (⟨_, hk⟩ : ↥((bundle 0 0).solPart ptSection s k))
    exact hk
  have : Fintype ↥((bundle 0 0).solPart ptSection s 0) := Fintype.ofFinite _
  let := solPartChartedSpace rnPolyfold_isTame hf hs 0
  rw [psiAt_mk_zero_eq_sum, Fintype.sum_subsingleton _ ⟨0, hmem⟩]
  have hval : formsInftyRestrict 0 (hasCornerStructureOfDim_solPart rnPolyfold_isTame hf hs 0)
      ptOne ⟨0, hmem⟩ 0 = 1 := by
    unfold ptOne
    rw [formsInftyRestrict_of]
    rfl
  change orSign _ * formsInftyRestrict 0 _ ptOne _ 0 = 1 ∨
    orSign _ * formsInftyRestrict 0 _ ptOne _ 0 = -1
  rw [hval, mul_one]
  exact orSign_eq_one_or _


/-- **2021 Theorem 6.7.1 is not vacuous** (non-vacuity witness, not in the text): on the point
`X = ℝ⁰` with the zero bundle `ℝ⁰ × ℝ⁰ → ℝ⁰` and `f = 0`, the standing hypotheses hold (`X` is tame
and admits sc-smooth bump functions), `f` is a proper tame sc-Fredholm section with an orientation
`o`, and on the class `[1]` of the constant `0`-form `1` (closed: `relD_ptOne`), `Ψ_s([1]) = ±1`
for every admissible `s` (for any `(N, U)`), in particular for `Ψ = psiInvariant`. `S_{f+s}` is
the point, of index `0`, counted with its sign. Every `Ψ` with property (1) of
`theorem_6_7_1_of_indep` agrees with `Ψ_s` (`psiAt_mk`), so it is not `0` either. Proper oriented
homotopies exist for every proper oriented `f` (`witness_isProperOrientedHomotopyBetween`). -/
theorem theorem_6_7_1_witness :
    ∃ (hX : (rnPolyfold 0).IsTame) (hbump : (rnPolyfold 0).AdmitsBumpFunctions)
      (hf : (bundle 0 0).IsScFredholmSectionTame ptSection) (hP : (bundle 0 0).IsProper ptSection)
      (o : SectionOrientation ptSection hf.toIsScFredholmSection) (c : LinearMap.ker (relD hX 0)),
      (∀ (N : (bundle 0 0).One → ℝ) (U : Set (Fin 0 → ℝ))
          (s : (Fin 0 → ℝ) → (Fin 0 → ℝ) × (Fin 0 → ℝ))
          (hs : (bundle 0 0).IsAdmissible ptSection N U s),
        psiAt hX hbump hf hs o 0 (relDeRhamMk hX 0 c) = 1 ∨
          psiAt hX hbump hf hs o 0 (relDeRhamMk hX 0 c) = -1) ∧
      (psiInvariant hX hbump hf hP o 0 (relDeRhamMk hX 0 c) = 1 ∨
        psiInvariant hX hbump hf hP o 0 (relDeRhamMk hX 0 c) = -1) :=
  ⟨rnPolyfold_isTame, rnPolyfold_zero_admitsBumpFunctions, isScFredholmSectionTame_ptSection,
    isProper_ptSection, ptOrientation, ⟨ptOne, relD_ptOne⟩,
    fun _ _ _ hs => psiAt_ptOne ptOrientation hs, psiAt_ptOne ptOrientation _⟩

end Witness

end Polyfold
