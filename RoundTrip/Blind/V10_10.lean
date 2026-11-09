import Polyfold
/-! Blind formalization of V10_10 (the text's Part II, §10.1, Proposition 10.1.13, p. 472 of the
Springer 2021 book; new in the 2021 edition).

Text: for an equivalence `F`, `F_R : 𝐗^R → 𝐘^R` is well defined, continuous and open, and `𝐗^R`
is Hausdorff iff `𝐘^R` is.

Choices:
- Setting: ep-groupoids `X : EpGroupoid Obj Mor`, `Y : EpGroupoid Obj' Mor'`, all four spaces in
  `Type` (universe 0), Hausdorff and paracompact (`RoundTrip/Blind/V7_3.lean`); `F : X → Y` an
  sc-smooth functor (the project's `EpFunctor`).
- "equivalence": my `IsEquivB` (Definition 10.1.1), copied from `RoundTrip/Blind/V10_1.lean`.
- `𝐗^R`: the project's `X.ReducedMor = Quot X.ReducedRel` with projection `X.reducedπ`
  (`φ ∼ φ'` iff `s φ = s φ'` and `φ = φ' ∘ g` for some `g ∈ T_{s φ}`; read with `#print`, the
  notion checked in `RoundTrip/Blind/V7_38.lean`), with the quotient topology (checked by `rfl`,
  not kept here, that the instance is `coinduced X.reducedπ`).  No M-polyfold structure on `𝐗^R`
  is involved (that needs `𝐗^R` Hausdorff, V10_11).
- `F_R([φ]) = [F(φ)]`.  "well defined": `φ ∼ φ'` implies `[F φ] = [F φ']`; then (equivalently)
  there is a map `f : 𝐗^R → 𝐘^R` with `f [φ] = [F φ]`, and it is continuous and open
  (`IsOpenMap`).  "Hausdorff": `T2Space`.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_10
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

/-- Proposition 10.1.13: for an equivalence `F`, `F_R : 𝐗^R → 𝐘^R`, `[φ] ↦ [F φ]`, is well
defined, continuous and open, and `𝐗^R` is Hausdorff iff `𝐘^R` is. -/
def B : Prop :=
  ∀ (Obj Mor Obj' Mor' : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
    [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
    (X : EpGroupoid Obj Mor) (Y : EpGroupoid Obj' Mor') (F : EpFunctor X Y),
    IsEquivB F →
      -- `F_R` is well defined
      (∀ φ φ' : Mor, X.ReducedRel φ φ' → Y.reducedπ (F.mor φ) = Y.reducedπ (F.mor φ')) ∧
      -- `F_R` is continuous and open
      (∃ f : X.ReducedMor → Y.ReducedMor,
        (∀ φ : Mor, f (X.reducedπ φ) = Y.reducedπ (F.mor φ)) ∧ Continuous f ∧ IsOpenMap f) ∧
      -- `𝐗^R` is Hausdorff iff `𝐘^R` is
      (T2Space X.ReducedMor ↔ T2Space Y.ReducedMor)

end RoundTrip.V10_10
