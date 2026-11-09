import Polyfold
/-! Blind formalization of V10_2 (the text's Part II, §10.1, Lemma 10.1.2 and the remarks around
it, p. 462 of the Springer 2021 book; 2017: Lemma 10.1, p. 334).

Text: an sc-smooth functor which is a local sc-diffeomorphism on objects and an equivalence of
categories is an equivalence; equivalences need not be invertible as functors.

Choices:
- Setting: ep-groupoids `X : EpGroupoid Obj Mor`, `Y : EpGroupoid Obj' Mor'`, all four spaces in
  `Type` (universe 0), Hausdorff and paracompact (`RoundTrip/Blind/V7_3.lean`); "sc-smooth
  functor" is the project's `EpFunctor` (`RoundTrip/Blind/V7_9.lean`).
- "equivalence" (Definition 10.1.1) is my `IsEquivB`, copied from `RoundTrip/Blind/V10_1.lean`:
  full and faithful, `|F| : |X| → |Y|` a homeomorphism (my orbit space `OrbB`, a `Quot` with the
  quotient topology), and a local sc-diffeomorphism on objects (`LocalScDiffeoObjB`, via the
  project's `MPolyfold.IsScDiffeoOn`).
- "equivalence of categories": read as full, faithful and essentially surjective
  (`FullyFaithfulB ∧ EssSurjB`; every `y` is isomorphic to some `F x`), which is equivalent (with
  choice) to the existence of a quasi-inverse functor with natural isomorphisms.
- (a) the lemma, for all `X`, `Y`, `F`.
- (b) "equivalences need not be invertible as functors": there are ep-groupoids (bundled as the
  project's `EP` objects, to quantify over the spaces with their instances) and an equivalence
  `F` with no inverse functor.  I state "no inverse functor" as: there are no maps
  `g₀ : Obj' → Obj`, `g₁ : Mor' → Mor` inverse to `F.obj`, `F.mor` on both sides (an inverse
  functor would give such maps, and conversely inverse maps of a functor form a functor), so this
  is also "no inverse sc-smooth functor", the reading for the category `EP`.  I do not read it as
  "no inverse up to natural equivalence".
- Nothing looks false to me.
-/
namespace RoundTrip.V10_2
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

/-- `F` is essentially surjective: every object of `Y` is isomorphic to some `F x`. -/
def EssSurjB {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} (F : EpFunctor X Y) : Prop :=
  ∀ y : Obj', ∃ (x : Obj) (ψ : Mor'), Y.src ψ = F.obj x ∧ Y.tgt ψ = y

end

/-- Lemma 10.1.2: a local sc-diffeomorphism on objects which is an equivalence of categories is
an equivalence; and some equivalence has no inverse functor. -/
def B : Prop :=
  (∀ (Obj Mor Obj' Mor' : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
    [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
    (X : EpGroupoid Obj Mor) (Y : EpGroupoid Obj' Mor') (F : EpFunctor X Y),
      LocalScDiffeoObjB F → FullyFaithfulB F → EssSurjB F → IsEquivB F) ∧
  (∃ (A A' : EP.{0}) (F : EpFunctor A.X A'.X), IsEquivB F ∧
    ¬ ∃ (g₀ : A'.Obj → A.Obj) (g₁ : A'.Mor → A.Mor),
      (∀ x, g₀ (F.obj x) = x) ∧ (∀ y, F.obj (g₀ y) = y) ∧
      (∀ φ, g₁ (F.mor φ) = φ) ∧ (∀ ψ, F.mor (g₁ ψ) = ψ))

end RoundTrip.V10_2
