import Polyfold.Chapter3.UnitIntervalPolyfold
import Polyfold.Chapter3.IndexAlongPathsLocal
import Polyfold.Chapter3.IndexAlongPathsDevice

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.2, **Proposition 6.2.2**
(p. 240; preprint: Proposition 6.2, p. 201), **for sc-smooth paths `φ : [0, 1] → X`**, as
printed.  Closes the remaining narrowing of row V3.98 and the Proposition 6.2.2 part of gap G.65
(decision D2: paths read on `ℝ`).

# Proposition 6.2.2 on `[0, 1]`

## The text, paraphrased

(Proposition 6.2.2) Let `P : Y → X` be a strong bundle over a tame M-polyfold `X` and `f` an
sc-Fredholm section.  If the smooth points `x₀`, `x₁` are joined by an sc-smooth path
`φ : [0, 1] → X`, then `ind(f, x₀) = ind(f, x₁)`; the proof shows that `t ↦ ind(f, φ(t))` is
locally constant.

## What is formalized

* `Polyfold.exists_forall_of_unitInterval_path`: **a statement `∃ i, ∀ s, Q(ψ(s), i)` proved for
  all sc-smooth paths `ψ : ℝ → X` holds for all sc-smooth paths `φ : [0, 1] → X`**: `φ ∘ sin²` is
  an sc-smooth path on `ℝ` with the same values (`IsScSmoothMap.exists_rn_reparam`,
  `UnitIntervalPolyfold.lean`).
* **`Polyfold.proposition_6_2_2_interval`** (**Proposition 6.2.2 with the text's hypotheses**):
  for an sc-Fredholm section `f` with tame germ data of a strong bundle `P : Y → X` (no bump
  functions) and an sc-smooth path `φ : [0, 1] → X` (`unitIntervalPolyfold`, Definition 2.3.8),
  `ind(f, φ(t))` (Definition 6.2.1 with local sections, `IsIndexAtLocal`) is one integer for all
  `t ∈ [0, 1]`; `proposition_6_2_2_interval'` is the text's form `ind(f, φ(0)) = ind(f, φ(1))`.
  From `proposition_6_2_2_local`.
* `Polyfold.proposition_6_2_2_interval_bump`: the same with global sc⁺-sections (`IsIndexAt`)
  when `X` admits sc-smooth bump functions; from `proposition_6_2_2'`.
* `Polyfold.proposition_6_2_2_interval_of_rn`: the earlier reading (decision D2) is the special
  case of the restriction to `[0, 1]` of an sc-smooth path on `ℝ`
  (`IsScSmoothMap.restrictUnitInterval`); this is also the witness that the path hypothesis is
  satisfiable (e.g. the inclusion `[0, 1] → ℝ`, `isScSmoothMap_unitInterval_val`).

## What the text leaves implicit, and the choices made

* `[0, 1]` is the M-polyfold `unitIntervalPolyfold` of `UnitIntervalPolyfold.lean` (two charts
  `t` and `1 − t` onto `[0, 1) ⊆ [0, ∞)`), and "sc-smooth path" is Definition 2.3.8 (preprint
  2.14, `IsScSmoothMap`) for this M-polyfold.  No hypothesis is added beyond those of the
  `ℝ`-path results (`IsScFredholmSectionTame`: "strong bundle over a tame M-polyfold" is read as
  germ data in tame charts, row V3.103).
* The proof does not redo the text's local argument on `[0, 1]`: `φ ∘ sin²` is an sc-smooth path on
  `ℝ` taking every value of `φ`, and the `ℝ`-path results apply to it.
-/

open Set Function

noncomputable section

namespace Polyfold

universe u v

section Interval

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

/-- **From paths on `ℝ` to paths on `[0, 1]`**: if every sc-smooth path `ψ : ℝ → X` has an `i` with
`Q(ψ(s), i)` for all `s`, then so does every sc-smooth path `φ : [0, 1] → X` (apply the hypothesis
to `φ ∘ sin²`, which takes every value of `φ`). -/
theorem exists_forall_of_unitInterval_path {α : Type*} {Q : X → α → Prop}
    (h : ∀ ψ : (Fin 1 → ℝ) → X, (rnPolyfold 1).IsScSmoothMap PX ψ → ∃ i, ∀ s, Q (ψ s) i)
    {φ : unitInterval → X} (hφ : unitIntervalPolyfold.IsScSmoothMap PX φ) :
    ∃ i, ∀ t, Q (φ t) i := by
  obtain ⟨g, hg, hψ⟩ := hφ.exists_rn_reparam
  obtain ⟨i, hi⟩ := h _ hψ
  refine ⟨i, fun t => ?_⟩
  obtain ⟨s, rfl⟩ := hg t
  exact hi s

end Interval

section Prop622

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- **2021 Proposition 6.2.2, p. 240 (stability of the index along sc-smooth paths), for paths on
`[0, 1]`** (preprint: Proposition 6.2): let `f` be an sc-Fredholm section with tame germ data of a
strong bundle `P : Y → X` (no bump functions) and `φ : [0, 1] → X` an sc-smooth path.  Then
`ind(f, φ(t))` (Definition 6.2.1 with a locally defined sc⁺-section, `IsIndexAtLocal`) is one
integer for all `t ∈ [0, 1]`.  From `proposition_6_2_2_local` applied to `φ ∘ sin²`. -/
theorem proposition_6_2_2_interval (hf : B.IsScFredholmSectionTame f) {φ : unitInterval → X}
    (hφ : unitIntervalPolyfold.IsScSmoothMap PX φ) :
    ∃ i : ℤ, ∀ t, B.IsIndexAtLocal f (φ t) i :=
  exists_forall_of_unitInterval_path (fun _ hψ => proposition_6_2_2_local hf hψ) hφ

/-- **2021 Proposition 6.2.2, the text's form**: `ind(f, φ(0)) = ind(f, φ(1))` for an sc-smooth
path `φ : [0, 1] → X`, for any two values `i`, `j` of the local index at the ends of the path
(`IsIndexAtLocal.unique`). -/
theorem proposition_6_2_2_interval' (hf : B.IsScFredholmSectionTame f) {φ : unitInterval → X}
    (hφ : unitIntervalPolyfold.IsScSmoothMap PX φ) {i j : ℤ}
    (hi : B.IsIndexAtLocal f (φ 0) i) (hj : B.IsIndexAtLocal f (φ 1) j) : i = j := by
  obtain ⟨k, hk⟩ := proposition_6_2_2_interval hf hφ
  exact (hi.unique hf.toIsScFredholmSection (hk 0)).trans
    ((hk 1).unique hf.toIsScFredholmSection hj)

/-- **2021 Proposition 6.2.2 on `[0, 1]` with global sc⁺-sections** (Definition 6.2.1 with a
section of `P` on all of `X`, `IsIndexAt`), when `X` admits sc-smooth bump functions.  From
`proposition_6_2_2'` applied to `φ ∘ sin²`. -/
theorem proposition_6_2_2_interval_bump (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) {φ : unitInterval → X}
    (hφ : unitIntervalPolyfold.IsScSmoothMap PX φ) :
    ∃ i : ℤ, ∀ t, B.IsIndexAt f (φ t) i :=
  exists_forall_of_unitInterval_path (fun _ hψ => proposition_6_2_2' hbump hf hψ) hφ

/-- **The reading of decision D2 is a special case**: for an sc-smooth `φ : ℝ → X`, the
`[0, 1]`-statement applies to its restriction `t ↦ φ(t)`, `t ∈ [0, 1]`
(`IsScSmoothMap.restrictUnitInterval`). -/
theorem proposition_6_2_2_interval_of_rn (hf : B.IsScFredholmSectionTame f)
    {φ : (Fin 1 → ℝ) → X} (hφ : (rnPolyfold 1).IsScSmoothMap PX φ) :
    ∃ i : ℤ, ∀ t : unitInterval, B.IsIndexAtLocal f (φ fun _ => (t : ℝ)) i :=
  proposition_6_2_2_interval hf hφ.restrictUnitInterval

end Prop622

end Polyfold
