import Polyfold
/-! Blind formalization of V7_16 (the 2017 book, Part II, §7.1, the remark after
Proposition 7.4, p. 230: isomorphic objects have isomorphic isotropy groups, via conjugation).
Choices:
- Setting: `Obj Mor : Type` (universe 0, as in the other blind files) with their topologies
  (`T2`, paracompact) as instances and `X : EpGroupoid Obj Mor` (the project's Definition 7.3,
  fields read with `#print`), the setting of §7.1. The claim itself only uses the groupoid
  structure `s, t, m, ι` of `X` (`X.src`, `X.tgt`, `X.comp φ ψ = φ ∘ ψ`, `X.inv`).
- `G_x` is written out as the set `Gset X x = {g | s g = x ∧ t g = x}` with the product
  `g · h = g ∘ h = X.comp g h` (Definition 7.2); I do not use the project's `Isotropy` group
  instance (its definition is not in the vocabulary). A group isomorphism `G_x → G_y` is
  expressed as a map `e : Mor → Mor` that is a bijection `Gset X x → Gset X y` (`Set.BijOn`)
  and is multiplicative on `G_x`; a multiplicative bijection between groups is a group
  isomorphism (units and inverses are then preserved).
- "`x` and `y` are isomorphic": `∃ φ, s φ = x ∧ t φ = y` (Definition 7.1).
- `B` is the conjunction of
  (1) isomorphic objects have isomorphic isotropy groups;
  (2) for every `φ : x → y` the map `g ↦ φ ∘ g ∘ φ⁻¹` (`X.comp φ (X.comp g (X.inv φ))`) is a
      group isomorphism `G_x → G_y` (this is the identification described in the text).
- Not in `B`: "In general, there is no canonical identification of `G_x` with `G_y`; any
  identification depends on an initial choice of `φ`." I read this as a remark, not a claim
  about a given `X`. Its formal content, that the conjugation map can depend on `φ`, is recorded
  separately as `Remark` (an existence statement over ep-groupoids). "Any identification … is
  given by `g ↦ φ ∘ g ∘ φ⁻¹`" does not hold as a claim about every group isomorphism
  `G_x ≅ G_y` (for `x = y` with `G_x ≅ ℤ/3` acting trivially, inversion is not a conjugation), so
  I read it as describing the identification of (2).
-/
namespace RoundTrip.V7_16
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- The isotropy group `G_x` as a set of morphisms `x → x`. -/
def Gset (X : EpGroupoid Obj Mor) (x : Obj) : Set Mor := {g | X.src g = x ∧ X.tgt g = x}

/-- `e` is a group isomorphism `G_x → G_y` (a multiplicative bijection; product `g ∘ h`). -/
def IsGroupIsoOn (X : EpGroupoid Obj Mor) (x y : Obj) (e : Mor → Mor) : Prop :=
  Set.BijOn e (Gset X x) (Gset X y) ∧
    ∀ g ∈ Gset X x, ∀ h ∈ Gset X x, e (X.comp g h) = X.comp (e g) (e h)

/-- Conjugation by `φ`: `g ↦ φ ∘ g ∘ φ⁻¹`. -/
def conj (X : EpGroupoid Obj Mor) (φ : Mor) (g : Mor) : Mor := X.comp φ (X.comp g (X.inv φ))

end

/-- Isomorphic objects have isomorphic isotropy groups, and every `φ : x → y` gives the
isomorphism `G_x → G_y`, `g ↦ φ ∘ g ∘ φ⁻¹`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    (∀ x y : Obj, (∃ φ : Mor, X.src φ = x ∧ X.tgt φ = y) →
      ∃ e : Mor → Mor, IsGroupIsoOn X x y e) ∧
    (∀ (x y : Obj) (φ : Mor), X.src φ = x → X.tgt φ = y → IsGroupIsoOn X x y (conj X φ))

/-- (Not part of `B`.) The remark "there is no canonical identification; it depends on the choice
of `φ`": some ep-groupoid has two morphisms `φ, φ' : x → y` with different conjugation maps. -/
def Remark : Prop :=
  ∃ (Obj Mor : Type) (_ : TopologicalSpace Obj) (_ : T2Space Obj) (_ : ParacompactSpace Obj)
    (_ : TopologicalSpace Mor) (_ : T2Space Mor) (_ : ParacompactSpace Mor)
    (X : EpGroupoid Obj Mor) (φ φ' : Mor),
    X.src φ = X.src φ' ∧ X.tgt φ = X.tgt φ' ∧ ∃ g ∈ Gset X (X.src φ), conj X φ g ≠ conj X φ' g

end RoundTrip.V7_16
