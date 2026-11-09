import Polyfold.Chapter3.IndexAlongPathsInterval
import Polyfold.Chapter3.MainTheorems2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.2, **Proposition 6.2.2**
(p. 240; preprint: Proposition 6.2) **for sc-smooth paths `φ : [0, 1] → X` and the 2021
definitions** of the sc-Fredholm section (Definitions 3.6.3 and 3.6.4, p. 135).  Row V3.98 and
the Proposition 6.2.2 part of gap G.65, in the vocabulary of `MainTheorems2021.lean`.

# Proposition 6.2.2 on `[0, 1]` with the 2021 definitions

## What is formalized

* `Polyfold.proposition_6_2_2_interval_2021def`: for an sc-Fredholm section in the 2021 sense with
  germ data in tame charts (`IsScFredholmSectionTame2021`) and an sc-smooth path
  `φ : [0, 1] → X` (`unitIntervalPolyfold`), `ind(f, φ(t))` (local sections, `IsIndexAtLocal`) is
  one integer for all `t`; no bump functions.  `proposition_6_2_2_interval_2021def'`: the text's
  `ind(f, φ(0)) = ind(f, φ(1))`.
* `Polyfold.proposition_6_2_2_interval_bump_2021def`: the form with global sc⁺-sections
  (`IsIndexAt`) when `X` admits sc-smooth bump functions (the `[0, 1]` form of
  `proposition_6_2_2_2021def`).

All three are `IndexAlongPathsInterval.lean` through the dictionary
`StrongBundle.isScFredholmSectionTame2021_iff`; no hypothesis is added.

## What the text leaves implicit, and the choices made

* "Tame strong bundle" is read, as in `MainTheorems2021.lean`, as germ data in tame charts
  (row V3.103); the version with the plain 2021 section `IsScFredholmSection2021` and germ data
  in arbitrary charts waits for gap G.79, as for paths on `ℝ`.
-/

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- **2021 Proposition 6.2.2, p. 240, for paths on `[0, 1]` and the 2021 definitions**: for an
sc-Fredholm section `f` in the 2021 sense with germ data in tame charts and an sc-smooth path
`φ : [0, 1] → X`, `ind(f, φ(t))` (local sections) is one integer for all `t`.  From
`proposition_6_2_2_interval`. -/
theorem proposition_6_2_2_interval_2021def (hf : B.IsScFredholmSectionTame2021 f)
    {φ : unitInterval → X} (hφ : unitIntervalPolyfold.IsScSmoothMap PX φ) :
    ∃ i : ℤ, ∀ t, B.IsIndexAtLocal f (φ t) i :=
  proposition_6_2_2_interval (StrongBundle.isScFredholmSectionTame2021_iff.1 hf) hφ

/-- **2021 Proposition 6.2.2, the text's form, with the 2021 definitions**:
`ind(f, φ(0)) = ind(f, φ(1))` for an sc-smooth path `φ : [0, 1] → X`. -/
theorem proposition_6_2_2_interval_2021def' (hf : B.IsScFredholmSectionTame2021 f)
    {φ : unitInterval → X} (hφ : unitIntervalPolyfold.IsScSmoothMap PX φ) {i j : ℤ}
    (hi : B.IsIndexAtLocal f (φ 0) i) (hj : B.IsIndexAtLocal f (φ 1) j) : i = j :=
  proposition_6_2_2_interval' (StrongBundle.isScFredholmSectionTame2021_iff.1 hf) hφ hi hj

/-- **2021 Proposition 6.2.2 on `[0, 1]` with the 2021 definitions and global sc⁺-sections**
(`IsIndexAt`), when `X` admits sc-smooth bump functions.  From
`proposition_6_2_2_interval_bump`. -/
theorem proposition_6_2_2_interval_bump_2021def (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame2021 f) {φ : unitInterval → X}
    (hφ : unitIntervalPolyfold.IsScSmoothMap PX φ) :
    ∃ i : ℤ, ∀ t, B.IsIndexAt f (φ t) i :=
  proposition_6_2_2_interval_bump hbump (StrongBundle.isScFredholmSectionTame2021_iff.1 hf) hφ

end Polyfold
