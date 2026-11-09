import Polyfold.Chapter3.Book2021Germs
import Polyfold.Chapter3.GlobalIFTNearbyOntoG
import Polyfold.Chapter3.GlobalIFTTheoremsG
import Polyfold.Chapter3.IndexAlongPathsDevice
import Polyfold.Chapter5.Corollary58
import Polyfold.Chapter5.Book2021
import Polyfold.Chapter5.GeneralPosition

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941;
2014 preprint): **the main theorems of Chapters 3, 5 and 6 stated with the 2021 definitions of the
sc-Fredholm germ and the sc-Fredholm section** — Theorem 3.1.22 (p. 100), Theorem 3.1.26 (p. 103),
Corollary 3.1.27 (p. 104), Theorem 3.6.8 (p. 136), Theorems 3.6.10 and 3.6.11 (p. 140),
Corollary 5.2.5 (p. 212), Theorems 5.3.5 (p. 217), 5.3.10 (p. 220) and 5.3.12 (p. 222), and
Proposition 6.2.2 (p. 240) (preprint: Theorems 3.19, 3.23, Corollary 3.24, Theorems 3.54, 3.56,
3.57, Corollary 5.8, Theorems 5.13, 5.18, 5.19, Proposition 6.2).  Numbers and pages are the 2021
text's, the preprint ones in parentheses.

# The main theorems with the 2021 Fredholm notions

## The text, paraphrased

(Definition 3.6.3, p. 135 = Definition 3.1.11, p. 96) `(f, x)` is an sc-Fredholm germ if there is a
strong bundle chart around `x` in which the local section has a filling `g` (Definition 3.6.1 =
3.1.4, no tameness of the retraction) and a local sc⁺-section `s` with `s(0) = g(0)` such that
`g − s` is conjugated near `0` to a basic germ.  (Definition 3.6.4 = 3.1.16) An sc-Fredholm
section is sc-smooth, regularizing, and an sc-Fredholm germ at every smooth point.  (Definition
3.6.6, p. 136) An sc-Fredholm germ `(f, x)` **of a tame strong bundle** with `f(x) = 0` is in good
position if `f'(x)` is onto and, if `d_X(x) ≥ 1`, `ker f'(x)` is in good position to `C_xX`.
(Theorem 3.6.8) For an sc-Fredholm section of a tame strong bundle, a zero in good position has a
neighbourhood `V` on which (1) every zero is in good position and (2) the solution set is a
sub-M-polyfold with the structure of a manifold with boundary with corners.  Theorems 3.1.22,
3.1.26, Corollary 3.1.27, Theorems 3.6.10 and 3.6.11 are its interior, boundary and global forms;
Corollary 5.2.5 passes to `f¹`; Theorems 5.3.5, 5.3.10, 5.3.12 are the perturbation theorems and
Proposition 6.2.2 the stability of the index along sc-smooth paths.

## What is formalized

The project states these theorems with its own notions `StrongBundle.IsScFredholmSection`,
`IsScFredholmSectionTame`, `IsGoodPositionGermTame` (`GlobalIFTNearbyOntoG.lean`,
`GlobalIFTTheoremsG.lean`, `Chapter5/*`, `IndexAlongPathsDevice.lean`).  `Book2021Germs.lean`
proves that the 2021 definitions `IsScFredholmGerm2021` / `IsScFredholmSection2021` (the book's
Definitions 3.6.3 and 3.6.4, literally) coincide with the project's (`isScFredholmGerm2021_iff`,
`isScFredholmSection2021_iff`).  This file adds the remaining dictionary and restates each theorem
with the 2021 notions, so that a reviewer checks only the 2021 definitions (comparison rows
V3.108, V3.110) and not the project's (V3.13, V3.16):

* `StrongBundle.IsScFredholmGermTame2021`: the 2021 germ data (Definition 3.6.3 with the 2021
  filling) in a **tame** strong bundle chart — the project's reading of "sc-Fredholm germ of a tame
  strong bundle" (row V3.103); `isScFredholmGermTame2021_iff` (it is the project's
  `IsScFredholmGermTame`) and `isScFredholmGermTame2021_iff_2017` (it is the 2017 germ
  `IsScFredholmGerm2017`: a 2021 filling over a tame retraction is a 2017 filling).
* `StrongBundle.IsScFredholmSectionTame2021` (Definition 3.6.4 with tame germ data),
  `isScFredholmSectionTame2021_iff`; `StrongBundle.IsGoodPositionGermTame2021` (Definition 3.6.6
  in a tame chart with the 2021 filling), `isGoodPositionGermTame2021_iff`.
* The theorems, each a corollary of the project's by the dictionary:
  `theorem_3_6_8_2021def` (Theorem 3.6.8 (1), (2); from `theorem_3_6_8'`),
  `theorem_3_1_26_2021def` (Theorem 3.1.26; `theorem_3_1_26'`),
  `theorem_3_1_22_2021def` and `theorem_3_1_22_linearization_2021def` (Theorem 3.1.22;
  `theorem_3_1_22'`, `theorem_3_1_22_linearization`),
  `theorem_3_6_11_2021def` (Theorem 3.6.11; `theorem_3_6_11`),
  `corollary_3_1_27_2021def` (Corollary 3.1.27; `corollary_3_1_27`),
  `theorem_3_6_10_2021def` (Theorem 3.6.10; `theorem_3_6_10`),
  `corollary_5_2_5_2021def` (Corollary 5.2.5 for `i = 1`; `corollary_5_2_5`),
  `theorem_5_3_5_2021def` (Theorem 5.3.5; `theorem_5_3_5`),
  `theorem_5_3_10_2021def` (Theorem 5.3.10; `theorem_5_3_10_param`),
  `theorem_5_3_12_2021def` (Theorem 5.3.12; `theorem_5_3_12_param`),
  `proposition_6_2_2_2021def` (Proposition 6.2.2; `proposition_6_2_2'`).
  The versions used are the ones without the added hypothesis `IsGoodPositionGermFilled` (the
  primed theorems of `GlobalIFTNearbyOntoG.lean`), so no hypothesis is added here.

## What the text leaves implicit, and the choices made

* **"Tame strong bundle" is read as "germ data in a tame chart"** (`IsTameChart`), as in the
  project's `IsScFredholmSectionTame` (row V3.103); the passage from germ data in an arbitrary
  compatible chart to germ data in a tame one is open (gap G.79).  The 2021 filling itself asks no
  tameness; in a tame chart the two fillings agree, which is why the tame 2021 germ is also the
  2017 germ (`isScFredholmGermTame2021_iff_2017`).
* The conclusions are the project's; where they mention good position of nearby zeros, they are
  stated with `IsGoodPositionGermTame2021`.
-/

open Set Filter Topology Function Module MeasureTheory
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-! ### The dictionary: tame germ data with the 2021 filling -/

namespace StrongBundle

variable (B) in
/-- **2021 Definition 3.6.3, p. 135, in a tame strong bundle chart** (the reading of "sc-Fredholm
germ of a tame strong bundle" of Definition 3.6.6 and Theorem 3.6.8; row V3.103): the data of
`IsScFredholmGerm2021` (the 2021 filling, no tameness) in a chart `c` with `IsTameChart c`. -/
def IsScFredholmGermTame2021 (f : X → Y) (x₀ : X) : Prop :=
  x₀ ∈ PX.smoothSet ∧
  ∃ (c : StrongBundleChart PX P) (_ : B.IsTameChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
    (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0) (s : c.φ.model.E 0 → c.F 1),
    IsFilling2021 c.relOpen c.isRetraction h0 (c.principal f) g ∧
    IsScPlusGerm c.φ.model.C c.U s ∧ c.F.toBase 1 (s 0) = g 0 ∧
    IsConjugateToBasicGerm c.U (fun u => g u - c.F.toBase 1 (s u))

/-- **The tame 2021 germ is the project's `IsScFredholmGermTame`** (Definition 3.6.3 (preprint 3.50) of the
preprint, germ reading): `r(0) = 0` holds in a chart centred at `x₀`. -/
theorem isScFredholmGermTame2021_iff {x₀ : X} :
    B.IsScFredholmGermTame2021 f x₀ ↔ B.IsScFredholmGermTame f x₀ := by
  constructor
  · rintro ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj⟩
    exact ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill.isFillingGerm, hsm, hs0, hconj⟩
  · rintro ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj⟩
    exact ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill.isFilling2021 (zero_mem_O_of_chart hxV hφ0),
      hsm, hs0, hconj⟩

/-- **The tame 2021 germ is the 2017 germ**: in a tame chart the 2021 filling is a 2017 filling
(2017 Definition 3.4 asks the base retraction to be tame, which `IsTameChart` provides). -/
theorem isScFredholmGermTame2021_iff_2017 {x₀ : X} :
    B.IsScFredholmGermTame2021 f x₀ ↔ B.IsScFredholmGerm2017 f x₀ := by
  rw [isScFredholmGermTame2021_iff, isScFredholmGerm2017_iff]

/-- A tame 2021 germ is a 2021 germ (Definition 3.6.3 in an arbitrary compatible chart). -/
theorem IsScFredholmGermTame2021.isScFredholmGerm2021 {x₀ : X}
    (h : B.IsScFredholmGermTame2021 f x₀) : B.IsScFredholmGerm2021 f x₀ :=
  isScFredholmGerm2021_iff.2 (isScFredholmGermTame2021_iff.1 h).isScFredholmGerm

variable (B) in
/-- **2021 Definition 3.6.4, p. 135, with germ data in tame charts** (row V3.103): an sc-Fredholm
section in the 2021 sense (`IsScFredholmSection2021`) whose germ data at every smooth point can be
taken in a tame strong bundle chart. -/
structure IsScFredholmSectionTame2021 (f : X → Y) : Prop extends B.IsScFredholmSection2021 f where
  germTame : ∀ x ∈ PX.smoothSet, B.IsScFredholmGermTame2021 f x

/-- **The tame 2021 section is the project's `IsScFredholmSectionTame`.** -/
theorem isScFredholmSectionTame2021_iff :
    B.IsScFredholmSectionTame2021 f ↔ B.IsScFredholmSectionTame f :=
  ⟨fun h => ⟨isScFredholmSection2021_iff.1 h.toIsScFredholmSection2021,
      fun x hx => isScFredholmGermTame2021_iff.1 (h.germTame x hx)⟩,
    fun h => ⟨isScFredholmSection2021_iff.2 h.toIsScFredholmSection,
      fun x hx => isScFredholmGermTame2021_iff.2 (h.germTame x hx)⟩⟩

variable (B) in
/-- **2021 Definition 3.6.6, p. 136, in a tame chart with the 2021 filling**: the data of
`IsScFredholmGermTame2021` together with a derivative family `Dg` of the filling germ such that
`Dg(0)` is in good position in the chart (`IsGoodPositionAtGerm`: `Tf̃(0) = Dg(0)|_{T₀O}` is onto
and its kernel is in good position to the partial cone `T₀O ∩ C` in `T₀O`). -/
def IsGoodPositionGermTame2021 (f : X → Y) (x₀ : X) : Prop :=
  x₀ ∈ PX.smoothSet ∧
  ∃ (c : StrongBundleChart PX P) (_ : B.IsTameChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
    (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0) (s : c.φ.model.E 0 → c.F 1),
    IsFilling2021 c.relOpen c.isRetraction h0 (c.principal f) g ∧
    IsScPlusGerm c.φ.model.C c.U s ∧ c.F.toBase 1 (s 0) = g 0 ∧
    IsConjugateToBasicGerm c.U (fun u => g u - c.F.toBase 1 (s u)) ∧
    ∃ (G : ScNbhdGerm c.φ.model.E c.φ.model.C) (Dg : c.φ.model.E 1 → c.φ.model.E 0 →L[ℝ] c.F 0),
      G.U 0 ⊆ c.U ∧ IsSc1GermWith G g Dg ∧
      IsGoodPositionAtGerm c.relOpen c.isRetraction h0 (Dg 0)

/-- **Good position with the 2021 filling is the project's `IsGoodPositionGermTame`.** -/
theorem isGoodPositionGermTame2021_iff {x₀ : X} :
    B.IsGoodPositionGermTame2021 f x₀ ↔ B.IsGoodPositionGermTame f x₀ := by
  constructor
  · rintro ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj, hgp⟩
    exact ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill.isFillingGerm, hsm, hs0, hconj, hgp⟩
  · rintro ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill, hsm, hs0, hconj, hgp⟩
    exact ⟨hs, c, hc, hxV, hφ0, h0, g, s, hfill.isFilling2021 (zero_mem_O_of_chart hxV hφ0),
      hsm, hs0, hconj, hgp⟩

/-- A germ in good position (2021 filling) is a tame 2021 germ. -/
theorem IsGoodPositionGermTame2021.isScFredholmGermTame2021 {x₀ : X}
    (h : B.IsGoodPositionGermTame2021 f x₀) : B.IsScFredholmGermTame2021 f x₀ :=
  isScFredholmGermTame2021_iff.2 (isGoodPositionGermTame2021_iff.1 h).isScFredholmGermTame

/-- Satisfiability of the tame 2021 section: the graph section of a `C^∞` map `φ : ℝⁿ → ℝᵏ`. -/
theorem isScFredholmSectionTame2021_graphSection {n k : ℕ} {φ : (Fin n → ℝ) → (Fin k → ℝ)}
    (hφ : ContDiff ℝ ∞ φ) :
    (TrivialBundle.bundleEven n k).IsScFredholmSectionTame2021 (TrivialBundle.graphSection φ) :=
  isScFredholmSectionTame2021_iff.2
    (TrivialBundle.isScFredholmSectionTame_graphSection_even hφ)

end StrongBundle

open StrongBundle

/-! ### Chapter 3: the implicit function theorems -/

/-- **2021 Theorem 3.6.8, p. 136** (preprint: Theorem 3.54), for the 2021 definitions: for an
sc-Fredholm section `f` with germ data in tame charts (`IsScFredholmSectionTame2021`), a zero `x₀`
in good position (`IsGoodPositionGermTame2021`) has an open neighbourhood `Vx` such that (1) every
zero in `Vx` is in good position, and (2) the solution set has at `x₀` regular tangent germ data
of Definition 3.2.1 (2) of dimension `d` on a chart with source in `Vx`, with locally constant
dimension (the sub-M-polyfold and manifold structure follow by Theorem 3.2.3, `theorem_3_2_3_of_isRegular`;
see `theorem_3_1_26_2021def`).  From `theorem_3_6_8'`, which adds no hypothesis. -/
theorem theorem_3_6_8_2021def (hf : B.IsScFredholmSectionTame2021 f) {x₀ : X}
    (hg : B.IsGoodPositionGermTame2021 f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ Vx : Set X, IsOpen Vx ∧ x₀ ∈ Vx ∧
      (∀ y ∈ Vx, IsZeroAt P f y → B.IsGoodPositionGermTame2021 f y) ∧
      ∃ d : ℕ, ∃ D : PX.TangentGermChart (solutionSet P f) x₀ d, D.IsRegular ∧ D.φ.source ⊆ Vx ∧
        ∀ y ∈ solutionSet P f ∩ D.φ.source,
          ∀ (n' : ℕ) (_ : PX.TangentGermChart (solutionSet P f) y n'), n' = d := by
  obtain ⟨Vx, hVxo, hx₀Vx, hall, hD⟩ := theorem_3_6_8' (isScFredholmSectionTame2021_iff.1 hf)
    (isGoodPositionGermTame2021_iff.1 hg) hx₀
  exact ⟨Vx, hVxo, hx₀Vx, fun y hy hy0 => isGoodPositionGermTame2021_iff.2 (hall y hy hy0), hD⟩

/-- **2021 Theorem 3.1.26, p. 103 (implicit function theorem, boundary case)** (preprint: Theorem
3.23), for the 2021 definitions: an sc-Fredholm section with germ data in tame charts and a zero
`x` in good position; then there is an open `U ∋ x` such that every zero in `U` is in good
position, `S(f, U)` consists of smooth points, is a sub-M-polyfold of `X`, and its induced
structure is tame and that of a `d`-dimensional manifold with boundary with corners.  From
`theorem_3_1_26'`. -/
theorem theorem_3_1_26_2021def (hf : B.IsScFredholmSectionTame2021 f) {x : X}
    (hx : IsZeroAt P f x) (hg : B.IsGoodPositionGermTame2021 f x) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ (∀ y ∈ U, IsZeroAt P f y → B.IsGoodPositionGermTame2021 f y) ∧
      (∀ y ∈ U, IsZeroAt P f y → y ∈ PX.smoothSet) ∧
      ∃ d : ℕ, ∃ hsub : PX.IsSubMPolyfold {y ∈ U | IsZeroAt P f y},
        haveI := PX.paracompactSpace_subtype {y ∈ U | IsZeroAt P f y}
        (MPolyfold.subPolyfold hsub).IsTame ∧
          (MPolyfold.subPolyfold hsub).IsManifoldWithCorners d := by
  obtain ⟨U, hUo, hxU, hall, hsm, hrest⟩ := theorem_3_1_26' (isScFredholmSectionTame2021_iff.1 hf)
    hx (isGoodPositionGermTame2021_iff.1 hg)
  exact ⟨U, hUo, hxU, fun y hy hy0 => isGoodPositionGermTame2021_iff.2 (hall y hy hy0), hsm,
    hrest⟩

/-- **2021 Theorem 3.1.22, p. 100, the first clause** (preprint: Theorem 3.19): for an
sc-Fredholm section in the 2021 sense and a zero `x₀` in good position, the linearization
`Tf(x₀) = Dg(0)|_{T₀O}` in the chart of the germ data is Fredholm of index `n − N`, and so is
`Dg(0)` (Proposition 3.6.5 for germs, `proposition_3_6_5_preprint`).  From `theorem_3_1_22_linearization`. -/
theorem theorem_3_1_22_linearization_2021def (hf : B.IsScFredholmSection2021 f) {x₀ : X}
    (hx₀ : IsZeroAt P f x₀) (hg : B.IsGoodPositionGermTame2021 f x₀) :
    ∃ (c : StrongBundleChart PX P) (_ : B.IsChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
      (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0)
      (_ : IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g)
      (G : ScNbhdGerm c.φ.model.E c.φ.model.C) (_ : G.U 0 ⊆ c.U) (_ : IsScSmoothGerm G g)
      (Dg : c.φ.model.E 1 → c.φ.model.E 0 →L[ℝ] c.F 0) (_ : IsSc1GermWith G g Dg)
      (h1 : ∀ x, StrongRetr.ρCLM c.isRetraction h0 (Dg 0 (scDeriv c.U (StrongRetr.r c.R) 0 x)) =
        Dg 0 (scDeriv c.U (StrongRetr.r c.R) 0 x)) (n N : ℕ),
      ContinuousLinearMap.IsFredholm (Dg 0) ∧ fredholmIndex (Dg 0) = n - N ∧
      ContinuousLinearMap.IsFredholm (fillerRestrict (scDeriv c.U (StrongRetr.r c.R) 0)
        (StrongRetr.ρCLM c.isRetraction h0) (Dg 0) h1) ∧
      fredholmIndex (fillerRestrict (scDeriv c.U (StrongRetr.r c.R) 0)
        (StrongRetr.ρCLM c.isRetraction h0) (Dg 0) h1) = n - N :=
  theorem_3_1_22_linearization (isScFredholmSection2021_iff.1 hf) hx₀
    (isGoodPositionGermTame2021_iff.1 hg).isGoodPositionGerm

/-- **2021 Theorem 3.1.22, p. 100 (implicit function theorem, interior case)** (preprint: Theorem
3.19), for the 2021 definitions: for an M-polyfold with `d_X ≡ 0`, an sc-Fredholm section with
germ data in tame charts and a zero `x₀` in good position (here: `f'(x₀)` onto), there is an open
`U ∋ x₀` such that every zero in `U` is in good position, `S(f, U)` consists of smooth points and
is a sub-M-polyfold whose induced structure is that of a `d`-dimensional manifold without
boundary.  From `theorem_3_1_22'`; the first clause is `theorem_3_1_22_linearization_2021def`. -/
theorem theorem_3_1_22_2021def (hX : PX.IsWithoutBoundary) (hf : B.IsScFredholmSectionTame2021 f)
    {x₀ : X} (hx₀ : IsZeroAt P f x₀) (hg : B.IsGoodPositionGermTame2021 f x₀) :
    ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧
      (∀ y ∈ U, IsZeroAt P f y → B.IsGoodPositionGermTame2021 f y) ∧
      (∀ y ∈ U, IsZeroAt P f y → y ∈ PX.smoothSet) ∧
      ∃ d : ℕ, ∃ hsub : PX.IsSubMPolyfold {y ∈ U | IsZeroAt P f y},
        haveI := PX.paracompactSpace_subtype {y ∈ U | IsZeroAt P f y}
        (MPolyfold.subPolyfold hsub).IsManifoldWithCorners d ∧
          (MPolyfold.subPolyfold hsub).IsWithoutBoundary := by
  obtain ⟨U, hUo, hxU, hall, hsm, hrest⟩ := theorem_3_1_22' hX
    (isScFredholmSectionTame2021_iff.1 hf) hx₀ (isGoodPositionGermTame2021_iff.1 hg)
  exact ⟨U, hUo, hxU, fun y hy hy0 => isGoodPositionGermTame2021_iff.2 (hall y hy hy0), hsm,
    hrest⟩

/-- **2021 Theorem 3.6.11, p. 140 (global implicit function theorem II)** (preprint: Theorem
3.57), for the 2021 definitions: an sc-Fredholm section in the 2021 sense whose germ is in good
position (in a tame chart) at every zero; then the nonempty solution set `S` is a sub-M-polyfold
of `X` whose induced structure is tame and that of a manifold with boundary with corners of
locally constant dimension, with regular tangent germ data at every point.  From
`theorem_3_6_11`. -/
theorem theorem_3_6_11_2021def (hf : B.IsScFredholmSection2021 f)
    (hall : ∀ x, IsZeroAt P f x → B.IsGoodPositionGermTame2021 f x)
    (hne : (solutionSet P f).Nonempty) :
    ∃ hsub : PX.IsSubMPolyfold (solutionSet P f),
      haveI := PX.paracompactSpace_subtype (solutionSet P f)
      (MPolyfold.subPolyfold hsub).IsTame ∧
        (MPolyfold.subPolyfold hsub).IsManifoldWithCornersLoc ∧
        ∀ x ∈ solutionSet P f, ∃ d : ℕ, ∃ D : PX.TangentGermChart (solutionSet P f) x d,
          D.IsRegular ∧ ∀ y ∈ solutionSet P f ∩ D.φ.source,
            ∀ (n' : ℕ) (_ : PX.TangentGermChart (solutionSet P f) y n'), n' = d :=
  theorem_3_6_11 (isScFredholmSection2021_iff.1 hf)
    (fun x hx => isGoodPositionGermTame2021_iff.1 (hall x hx)) hne

/-- **2021 Corollary 3.1.27, p. 104** (preprint: Corollary 3.24), for the 2021 definitions: the
solution set of an sc-Fredholm section in good position at every zero is a sub-M-polyfold whose
induced structure is tame and that of a manifold with boundary with corners.  From
`corollary_3_1_27`. -/
theorem corollary_3_1_27_2021def (hf : B.IsScFredholmSection2021 f)
    (hall : ∀ x, IsZeroAt P f x → B.IsGoodPositionGermTame2021 f x)
    (hne : (solutionSet P f).Nonempty) :
    ∃ hsub : PX.IsSubMPolyfold (solutionSet P f),
      haveI := PX.paracompactSpace_subtype (solutionSet P f)
      (MPolyfold.subPolyfold hsub).IsTame ∧
        (MPolyfold.subPolyfold hsub).IsManifoldWithCornersLoc :=
  corollary_3_1_27 (isScFredholmSection2021_iff.1 hf)
    (fun x hx => isGoodPositionGermTame2021_iff.1 (hall x hx)) hne

/-- **2021 Theorem 3.6.10, p. 140 (global implicit function theorem I)** (preprint: Theorem
3.56), for the 2021 definitions: over an M-polyfold without boundary, the solution set of an
sc-Fredholm section in good position (`f'(x)` onto) at every zero is a sub-M-polyfold whose
induced structure is that of a manifold without boundary.  From `theorem_3_6_10`. -/
theorem theorem_3_6_10_2021def (hX : PX.IsWithoutBoundary) (hf : B.IsScFredholmSection2021 f)
    (hall : ∀ x, IsZeroAt P f x → B.IsGoodPositionGermTame2021 f x)
    (hne : (solutionSet P f).Nonempty) :
    ∃ hsub : PX.IsSubMPolyfold (solutionSet P f),
      haveI := PX.paracompactSpace_subtype (solutionSet P f)
      (MPolyfold.subPolyfold hsub).IsManifoldWithCornersLoc ∧
        (MPolyfold.subPolyfold hsub).IsWithoutBoundary :=
  theorem_3_6_10 hX (isScFredholmSection2021_iff.1 hf)
    (fun x hx => isGoodPositionGermTame2021_iff.1 (hall x hx)) hne

/-! ### Chapter 5: Corollary 5.2.5 and the perturbation theorems -/

/-- **2021 Corollary 5.2.5, p. 212, for `i = 1`** (preprint: Corollary 5.8), for the 2021
definitions: if `f` is an sc-Fredholm section of `P : Y → X` with compact solution set, then `f¹`
is an sc-Fredholm section (2021 sense) of `P¹ : Y¹ → X¹` with compact solution set.  From
`corollary_5_2_5`. -/
theorem corollary_5_2_5_2021def (hf : B.IsScFredholmSection2021 f)
    (hS : IsCompact (solutionSet P f)) :
    B.shift.IsScFredholmSection2021 (B.sectionShift f) ∧
      IsCompact (solutionSet B.shiftProj (B.sectionShift f)) :=
  ⟨isScFredholmSection2021_iff.2 (corollary_5_2_5 (isScFredholmSection2021_iff.1 hf) hS).1,
    (corollary_5_2_5 (isScFredholmSection2021_iff.1 hf) hS).2⟩

/-- **2021 Theorem 5.3.5, p. 217 (perturbation: interior case)** (preprint: Theorem 5.13), for
the 2021 definitions: `theorem_5_3_5` with the sc-Fredholm hypothesis in the 2021 sense
(germ data in tame charts). -/
theorem theorem_5_3_5_2021def (hX : PX.IsWithoutBoundary) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame2021 f) (hS : IsCompact (solutionSet P f))
    {N : B.One → ℝ} (hN : B.IsAuxNorm N) :
    ∃ U : Set X, IsOpen U ∧ solutionSet P f ⊆ U ∧
      (∀ s ∈ B.allowableSections N U, IsCompact (solutionSet P (sectionAdd P f s))) ∧
      ∀ (s' : X → Y) (hs' : B.IsScPlusSection s'), s' ∈ B.allowableSections N U → ∀ ε > 0,
        ∃ (s : X → Y) (hs : B.IsScPlusSection s), s ∈ B.allowableSections N U ∧
          (∀ x, B.sectionDistAt N hs hs' x ≤ ε) ∧
          B.IsTransversal (sectionAdd P f s) ∧
          (PX.IsSubMPolyfold (solutionSet P (sectionAdd P f s)) ∧
            IsCompact (solutionSet P (sectionAdd P f s))) ∧
          ((solutionSet P (sectionAdd P f s)).Nonempty →
            B.SolutionSetIsManifold (sectionAdd P f s)) :=
  theorem_5_3_5 hX hbump (isScFredholmSectionTame2021_iff.1 hf) hS hN

/-- **2021 Theorem 5.3.10, p. 220 (perturbation: general position)** (preprint: Theorem 5.18),
for the 2021 definitions: `theorem_5_3_10_param` with the sc-Fredholm hypothesis in the 2021 sense. -/
theorem theorem_5_3_10_2021def (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame2021 f) (hS : IsCompact (solutionSet P f)) {N : B.One → ℝ}
    (hN : B.IsAuxNorm N) :
    ∃ U : Set X, IsOpen U ∧ solutionSet P f ⊆ U ∧
      (∀ s ∈ B.allowableSections N U, IsCompact (solutionSet P (sectionAdd P f s))) ∧
      ∀ (s₀ : X → Y) (hs₀ : B.IsScPlusSection s₀), sectionSupport P s₀ ⊆ U → ∀ ε > 0,
        (∀ x (hx : s₀ x ∈ B.oneSet), N (B.oneMk (s₀ x) hx) ≤ 1 - ε) →
        ∃ (m : ℕ) (t : Fin m → X → Y) (ht : ∀ i, B.IsScPlusSection (t i)),
          (∀ i, sectionSupport P (t i) ⊆ U) ∧
          (∀ i x (hx : t i x ∈ B.oneSet), N (B.oneMk (t i x) hx) ≤ 1) ∧
          ∃ δ > 0, ∃ CV : Set (Fin m → ℝ), volume CV = 0 ∧
            ∀ lam : Fin m → ℝ, ‖lam‖ < δ → lam ∉ CV →
              paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam ∈ B.allowableSections N U ∧
              B.SolutionSetInGeneralPosition
                (sectionAdd P f (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam)) :=
  theorem_5_3_10_param hX hbump (isScFredholmSectionTame2021_iff.1 hf) hS hN

/-- **2021 Theorem 5.3.12, p. 222 (perturbation and transversality: good position)** (preprint:
Theorem 5.19), for the 2021 definitions: `theorem_5_3_12_param` with the sc-Fredholm hypothesis and the
good-position hypothesis and conclusion in the 2021 sense. -/
theorem theorem_5_3_12_2021def (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame2021 f) (hS : IsCompact (solutionSet P f)) {N : B.One → ℝ}
    (hN : B.IsAuxNorm N)
    (hbd : ∀ x ∈ PX.boundary, IsZeroAt P f x → B.IsGoodPositionGermTame2021 f x) :
    ∃ U : Set X, IsOpen U ∧ solutionSet P f ⊆ U ∧
      (∀ s ∈ B.allowableSections N U, IsCompact (solutionSet P (sectionAdd P f s))) ∧
      ∃ (m : ℕ) (t : Fin m → X → Y) (ht : ∀ i, B.IsScPlusSection (t i)),
        (∀ i, sectionSupport P (t i) ⊆ U) ∧ (∀ i, Disjoint (sectionSupport P (t i)) PX.boundary) ∧
        (∀ i x (hx : t i x ∈ B.oneSet), N (B.oneMk (t i x) hx) ≤ 1) ∧
        ∃ δ > 0, ∃ CV : Set (Fin m → ℝ), volume CV = 0 ∧
          ∀ lam : Fin m → ℝ, ‖lam‖ < δ → lam ∉ CV →
            paramSlice (fiberZero P) isSection_fiberZero t (fun i => (ht i).1) lam ∈
              B.allowableSections N U ∧
            Disjoint (sectionSupport P
              (paramSlice (fiberZero P) isSection_fiberZero t (fun i => (ht i).1) lam))
              PX.boundary ∧
            B.IsTransversal (sectionAdd P f
              (paramSlice (fiberZero P) isSection_fiberZero t (fun i => (ht i).1) lam)) ∧
            (∀ x, IsZeroAt P (sectionAdd P f
                (paramSlice (fiberZero P) isSection_fiberZero t (fun i => (ht i).1) lam)) x →
              B.IsGoodPositionGermTame2021 (sectionAdd P f
                (paramSlice (fiberZero P) isSection_fiberZero t (fun i => (ht i).1) lam)) x) ∧
            IsCompact (solutionSet P (sectionAdd P f
              (paramSlice (fiberZero P) isSection_fiberZero t (fun i => (ht i).1) lam))) ∧
            ((solutionSet P (sectionAdd P f
                (paramSlice (fiberZero P) isSection_fiberZero t (fun i => (ht i).1) lam))).Nonempty
              →
              ∃ hsub : PX.IsSubMPolyfold (solutionSet P (sectionAdd P f
                  (paramSlice (fiberZero P) isSection_fiberZero t (fun i => (ht i).1) lam))),
                haveI := PX.paracompactSpace_subtype (solutionSet P (sectionAdd P f
                  (paramSlice (fiberZero P) isSection_fiberZero t (fun i => (ht i).1) lam)))
                (MPolyfold.subPolyfold hsub).IsTame ∧
                  (MPolyfold.subPolyfold hsub).IsManifoldWithCornersLoc) := by
  obtain ⟨U, hUo, hSU, hcpt, m, t, ht, hsupp, hdisj, hN1, δ, hδ, CV, hCV, hlam⟩ :=
    theorem_5_3_12_param hbump (isScFredholmSectionTame2021_iff.1 hf) hS hN
      fun x hx hx0 => isGoodPositionGermTame2021_iff.1 (hbd x hx hx0)
  refine ⟨U, hUo, hSU, hcpt, m, t, ht, hsupp, hdisj, hN1, δ, hδ, CV, hCV, fun lam h1 h2 => ?_⟩
  obtain ⟨ha, hb, hc, hgood, he, hf'⟩ := hlam lam h1 h2
  exact ⟨ha, hb, hc, fun x hx => isGoodPositionGermTame2021_iff.2 (hgood x hx), he, hf'⟩

/-! ### Chapter 6: Proposition 6.2.2 -/

/-- **2021 Proposition 6.2.2, p. 240 (stability of `ind(f, x)` along sc-smooth paths)**
(preprint: Proposition 6.2), for the 2021 definitions: `X` admits sc-smooth bump functions, `f` is
an sc-Fredholm section with germ data in tame charts (2021 sense) and `φ : ℝ → X` an sc-smooth
path; then `ind(f, φ(t))` is one integer for all `t`.  From `proposition_6_2_2'`. -/
theorem proposition_6_2_2_2021def (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame2021 f) {φ : (Fin 1 → ℝ) → X}
    (hφ : (rnPolyfold 1).IsScSmoothMap PX φ) :
    ∃ i : ℤ, ∀ t, B.IsIndexAt f (φ t) i :=
  proposition_6_2_2' hbump (isScFredholmSectionTame2021_iff.1 hf) hφ

end Polyfold
