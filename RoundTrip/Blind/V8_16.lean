import Polyfold
/-! Blind formalization of V8_16 (the text's Part II, §8.1, after Definition 8.1.13 = 2017
Definition 8.1, 2017 p. 267).

Text: the relation `F ≃ G` between sc-smooth functors `F, G : X → Y` of ep-groupoids is an
equivalence relation (stated without proof).

Choices:
- Setting as in my `RoundTrip/Blind/V8_15.lean`: ep-groupoids `X : EpGroupoid Obj Mor`,
  `Y : EpGroupoid Obj' Mor'`, all spaces in `Type` (universe 0), sc-smooth functors = the
  project's `EpFunctor` (`RoundTrip/Blind/V7_9.lean`).
- The relation `F ≃ G` is my reading of Definition 8.1.13 (copied from V8_15): there is an
  sc-smooth `τ : X → 𝐘` with `s(τ x) = F x`, `t(τ x) = G x` and `τ(x') ∘ F(h) = G(h) ∘ τ(x)` for
  `h : x → x'` (`NatEquivB`).  I do not use the project's `NaturallyEquivalent` here (V8_15 says it
  is the same relation).
- B: for all ep-groupoids `X`, `Y`, `NatEquivB` is reflexive, symmetric and transitive on
  `EpFunctor X Y` (Mathlib's `Equivalence`).
- Nothing looks false to me (reflexivity: `x ↦ 1_{F x}`; symmetry: `x ↦ τ(x)⁻¹`, sc-smooth as
  `ι ∘ τ`; transitivity: `x ↦ σ(x) ∘ τ(x)`, sc-smooth as `m ∘ (σ, τ)`).
-/
namespace RoundTrip.V8_16
open Polyfold

section
variable {Obj Mor Obj' Mor' : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']

/-- **Definition 8.1.13**: `τ` is a natural transformation `F → G`. -/
def IsNatTransB {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} (F G : EpFunctor X Y)
    (τ : Obj → Mor') : Prop :=
  X.PObj.IsScSmoothMap Y.PMor τ ∧
  (∀ x : Obj, Y.src (τ x) = F.obj x ∧ Y.tgt (τ x) = G.obj x) ∧
  (∀ (h : Mor) (x x' : Obj), X.src h = x → X.tgt h = x' →
    Y.comp (τ x') (F.mor h) = Y.comp (G.mor h) (τ x))

/-- **Definition 8.1.13**: `F ≃ G`, there is a natural transformation `F → G`. -/
def NatEquivB {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} (F G : EpFunctor X Y) : Prop :=
  ∃ τ : Obj → Mor', IsNatTransB F G τ

end

/-- Natural equivalence of sc-smooth functors between two ep-groupoids is an equivalence
relation. -/
def B : Prop :=
  ∀ (Obj Mor Obj' Mor' : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
    [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
    (X : EpGroupoid Obj Mor) (Y : EpGroupoid Obj' Mor'),
    Equivalence (NatEquivB (X := X) (Y := Y))

end RoundTrip.V8_16
