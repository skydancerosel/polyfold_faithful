import Polyfold.Chapter6.DetBundle
import Polyfold.Chapter6.LinSet

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.5, p. 219:
the determinant bundle `DET(f, x)` over `Lin(f, x)` and **Definition 6.6.2 (preprint 6.27)** (the set `Or_x^f` of
its two orientations) *(book 2017: Definition 6.9; see `BookConcordance.md`)*.

# Orientations of the linearizations at a point

## The text, paraphrased

`Lin(f, x)` is a convex subset of the Fredholm operators, so by Proposition 6.6.1 (preprint 6.26) the restriction
`DET(f, x)` of `DET(T_xX, Y_x)` to `Lin(f, x)` has exactly two orientations.  (Definition 6.6.2 (preprint 6.27))
`Or_x^f` is the two-element set of orientations of `DET(f, x)`, `Or_x^f = {o_x, −o_x}`; the
category `𝒪_f` has these sets as objects and the bijections as morphisms.

## What is formalized

* `ChartPoint.isFredholm_of_mem_linSet`; `ChartPoint.detLin p f hf` (`DET(f, x)`, the pull-back of
  `DET(T_zO, K_z)` to `Lin(f, x)`); `ChartPoint.Or p f hf` (**Definition 6.6.2 (preprint 6.27)**, the orientations).
* `ChartPoint.exists_two_or`: `Or_x^f` has exactly two elements (Proposition 6.6.1 (preprint 6.26)).
* `ChartPoint.orEquivRay`: for `L ∈ Lin(f, x)`, `o ↦ o(L)` is a bijection of `Or_x^f` with the two
  orientations of the line `det(L)`.

## Reading

`DET(f, x)` is made in a chart point (`LinSet.lean`).  The category `𝒪_f` is read through its
objects: a morphism `Or_x^f → Or_y^f` is a bijection of these types (`Equiv`).  `−o_x` is the other
element; the fibres of `DET` are tensor products, on which no negation is set up, so the two
elements are stated as "exactly two".
-/

open Module Bundle Topology Set

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

namespace ChartPoint

variable {x : X} (p : ChartPoint B x)

/-- The members of `Lin(f, x)` are Fredholm. -/
theorem isFredholm_of_mem_linSet (hf : B.IsScFredholmSection f) :
    ∀ L ∈ p.linSet f, L.IsFredholm := fun _ hL =>
  (p.isFredholm_isIndexAt_of_mem_linSet hf hL).1

variable (f) in
/-- **`DET(f, x)`**: the determinant bundle `DET(T_xX, Y_x)` restricted to `Lin(f, x)`. -/
abbrev detLin (hf : B.IsScFredholmSection f) : p.linSet f → Type _ :=
  DetOn (p.linSet f) (p.isFredholm_of_mem_linSet hf)

variable (f) in
/-- **Definition 6.6.2 (preprint 6.27)**: `Or_x^f`, the orientations of `DET(f, x)`. -/
abbrev Or (hf : B.IsScFredholmSection f) : Type _ := LineOrientation (p.detLin f hf)

/-- **`Or_x^f` has exactly two elements** at a smooth point (Proposition 6.6.1 (preprint 6.26): `Lin(f, x)` is
nonempty and convex). -/
theorem exists_two_or (hf : B.IsScFredholmSection f) (hx : x ∈ PX.smoothSet)
    (hsec : B.HasScPlusSectionsThrough) :
    ∃ o₁ o₂ : p.Or f hf, o₁ ≠ o₂ ∧ ∀ o, o = o₁ ∨ o = o₂ :=
  (proposition_6_6_1 (p.convex_linSet hf) (p.linSet_nonempty hf hx hsec)
    (p.isFredholm_of_mem_linSet hf)).2

/-- **An orientation of `DET(f, x)` is its value at one linearization**: for `L ∈ Lin(f, x)`,
`o ↦ o(L)` is a bijection of `Or_x^f` with the orientations of `det(L)`. -/
def orEquivRay (hf : B.IsScFredholmSection f) {L : ↥p.T →L[ℝ] ↥p.K} (hL : L ∈ p.linSet f) :
    p.Or f hf ≃ Module.Ray ℝ (fredholmDet L) :=
  haveI : ContractibleSpace (p.linSet f) := (p.convex_linSet hf).contractibleSpace ⟨L, hL⟩
  haveI : LocallyPathConnectedSpace (p.linSet f) := (p.convex_linSet hf).locallyPathConnectedSpace
  { toFun := fun o => o ⟨L, hL⟩
    invFun := fun r => (exists_lineOrientation_apply_eq (L := p.detLin f hf) ⟨L, hL⟩ r).choose
    left_inv := fun o => LineOrientation.eq_of_apply_eq ⟨L, hL⟩
      (exists_lineOrientation_apply_eq (L := p.detLin f hf) ⟨L, hL⟩ (o ⟨L, hL⟩)).choose_spec
    right_inv := fun r =>
      (exists_lineOrientation_apply_eq (L := p.detLin f hf) ⟨L, hL⟩ r).choose_spec }

/-- `orEquivRay` is the value of the orientation at `L`. -/
theorem orEquivRay_apply (hf : B.IsScFredholmSection f) {L : ↥p.T →L[ℝ] ↥p.K}
    (hL : L ∈ p.linSet f) (o : p.Or f hf) : p.orEquivRay hf hL o = o ⟨L, hL⟩ :=
  rfl

end ChartPoint

end Polyfold
