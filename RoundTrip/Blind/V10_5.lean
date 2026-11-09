import Polyfold
/-! Blind formalization of V10_5 (the text's Part II, §10.1, Proposition 10.1.5, p. 464 of the
Springer 2021 book; 2017: Proposition 10.2, p. 336).

Text: if `F ≃ G` and one of them is an equivalence, so is the other (quoted from the literature
without proof).

Choices:
- Setting: ep-groupoids `X : EpGroupoid Obj Mor`, `Y : EpGroupoid Obj' Mor'`, all four spaces in
  `Type` (universe 0), Hausdorff and paracompact (`RoundTrip/Blind/V7_3.lean`); `F, G` are
  sc-smooth functors `X → Y` (the project's `EpFunctor`, `RoundTrip/Blind/V7_9.lean`).
- "equivalence": my `IsEquivB` (Definition 10.1.1), copied from `RoundTrip/Blind/V10_1.lean`
  (full and faithful; `|F|` a homeomorphism of my quotient-topology orbit spaces; local
  sc-diffeomorphism on objects).
- `F ≃ G`: my `NatEqB` (Definition 10.1.4), copied from `RoundTrip/Blind/V10_4.lean`: there is an
  sc-smooth `τ : X → 𝐘` with `τ(x) : F(x) → G(x)` and `τ(x') ∘ F(φ) = G(φ) ∘ τ(x)`.
- "one of them is an equivalence, so is the other": both implications, for `F ≃ G`.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_5
open Polyfold

universe u v

section
variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']

/-- `x ≅ y` in the groupoid `G`: there is a morphism `x → y`. -/
def IsoRelB {O M : Type u} (G : GroupoidStr O M) (x y : O) : Prop :=
  ∃ φ : M, G.src φ = x ∧ G.tgt φ = y

/-- The orbit space `|G|`, the objects modulo `≅`, with the quotient topology. -/
abbrev OrbB {O M : Type u} (G : GroupoidStr O M) : Type u :=
  Quot (IsoRelB G)

/-- `F` is full and faithful: `φ ↦ F φ` is a bijection `mor(x, x') → mor(F x, F x')`. -/
def FullyFaithfulB {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} (F : EpFunctor X Y) :
    Prop :=
  (∀ φ φ' : Mor, X.src φ = X.src φ' → X.tgt φ = X.tgt φ' → F.mor φ = F.mor φ' → φ = φ') ∧
  (∀ (x x' : Obj) (ψ : Mor'), Y.src ψ = F.obj x → Y.tgt ψ = F.obj x' →
    ∃ φ : Mor, X.src φ = x ∧ X.tgt φ = x' ∧ F.mor φ = ψ)

/-- The induced map `|F| : |X| → |Y|`, `|x| ↦ |F x|`, is a homeomorphism. -/
def OrbitHomeoB {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} (F : EpFunctor X Y) :
    Prop :=
  ∃ e : OrbB X.toGroupoidStr ≃ₜ OrbB Y.toGroupoidStr,
    ∀ x : Obj, e (Quot.mk _ x) = Quot.mk _ (F.obj x)

/-- `F` is a local sc-diffeomorphism on objects. -/
def LocalScDiffeoObjB {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} (F : EpFunctor X Y) :
    Prop :=
  ∀ x : Obj, ∃ (U : Set Obj) (V : Set Obj') (g : Obj' → Obj),
    x ∈ U ∧ X.PObj.IsScDiffeoOn Y.PObj F.obj g U V

/-- **Definition 10.1.1**: `F` is an equivalence. -/
def IsEquivB {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} (F : EpFunctor X Y) : Prop :=
  FullyFaithfulB F ∧ OrbitHomeoB F ∧ LocalScDiffeoObjB F

/-- **Definition 10.1.4**: `τ` is a natural transformation `F → G`. -/
def IsNatTransB {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} (F G : EpFunctor X Y)
    (τ : Obj → Mor') : Prop :=
  X.PObj.IsScSmoothMap Y.PMor τ ∧
  (∀ x : Obj, Y.src (τ x) = F.obj x ∧ Y.tgt (τ x) = G.obj x) ∧
  (∀ (φ : Mor) (x x' : Obj), X.src φ = x → X.tgt φ = x' →
    Y.comp (τ x') (F.mor φ) = Y.comp (G.mor φ) (τ x))

/-- `F ≃ G`: there is a natural transformation `F → G`. -/
def NatEqB {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} (F G : EpFunctor X Y) : Prop :=
  ∃ τ : Obj → Mor', IsNatTransB F G τ

end

/-- Proposition 10.1.5: if `F ≃ G`, then `F` is an equivalence iff `G` is. -/
def B : Prop :=
  ∀ (Obj Mor Obj' Mor' : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
    [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
    (X : EpGroupoid Obj Mor) (Y : EpGroupoid Obj' Mor') (F G : EpFunctor X Y),
    NatEqB F G → ((IsEquivB F → IsEquivB G) ∧ (IsEquivB G → IsEquivB F))

end RoundTrip.V10_5
