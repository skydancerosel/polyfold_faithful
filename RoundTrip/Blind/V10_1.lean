import Polyfold
/-! Blind formalization of V10_1 (the text's Part II, §10.1, Definition 10.1.1, p. 461 of the
Springer 2021 book; 2017: Definition 10.1, p. 333).

Text: an equivalence `F : X → Y` of ep-groupoids is an sc-smooth functor which is faithful and
full, induces a homeomorphism `|F| : |X| → |Y|`, and is a local sc-diffeomorphism on objects; `E`
is the class of equivalences.

Choices:
- This item is a definition.  Setting: ep-groupoids `X : EpGroupoid Obj Mor`,
  `Y : EpGroupoid Obj' Mor'` (the project's Definition 7.3), all four spaces in `Type`
  (universe 0), Hausdorff and paracompact as the project's `EpGroupoid` requires
  (`RoundTrip/Blind/V7_3.lean`).  My notions are universe polymorphic (`Type u`, `Type v`), for
  reuse with tangent groupoids (V10_7).  "sc-smooth functor" is the project's `EpFunctor`
  (checked to be the text's notion in `RoundTrip/Blind/V7_9.lean`).
- "faithful and full" (`FullyFaithfulB`): for all `x, x'` the map `mor(x, x') → mor(F x, F x')`,
  `φ ↦ F φ`, is injective and surjective (stated without subtypes: injectivity on pairs with equal
  sources and targets; every `ψ : F x → F x'` is some `F φ` with `φ : x → x'`).
- `|X|` (`OrbB`): the quotient of the objects by "there is a morphism `x → y`" with Mathlib's
  quotient topology (`Quot`, coinduced topology), my own; the project's orbit space is not used.
  "`|F|` is a homeomorphism" (`OrbitHomeoB`): there is a homeomorphism `e : |X| ≃ₜ |Y|` with
  `e |x| = |F x|` (this pins `e` down as the induced map `|F|`).
- "local sc-diffeomorphism on objects" (`LocalScDiffeoObjB`): every object `x` has an open
  neighbourhood `U` on which `F` is an sc-diffeomorphism onto an open `V` (the project's
  `MPolyfold.IsScDiffeoOn`, read with `#print`: `F` and an inverse `g` sc-smooth on the open sets
  `U`, `V`, mapping them to each other, mutually inverse).
- B says: (a) the project's `EpFunctor.IsEquivalence` is my `IsEquivB` (in universe 0), and
  (b) the project's class `EP.equivalences` (a `MorphismProperty` of the category `EP`, whose
  morphisms are `EpFunctor`s) consists exactly of the `F` with `IsEquivB F`.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_1
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

end

/-- Definition 10.1.1: the project's equivalences, and its class `E = EP.equivalences`, are the
text's equivalences. -/
def B : Prop :=
  (∀ (Obj Mor Obj' Mor' : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
    [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
    (X : EpGroupoid Obj Mor) (Y : EpGroupoid Obj' Mor') (F : EpFunctor X Y),
      F.IsEquivalence ↔ IsEquivB F) ∧
  (∀ (A A' : EP.{0}) (F : A ⟶ A'),
      EP.equivalences F ↔ IsEquivB (show EpFunctor A.X A'.X from F))

end RoundTrip.V10_1
