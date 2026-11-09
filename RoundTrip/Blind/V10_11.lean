import Polyfold
/-! Blind formalization of V10_11 (the text's Part II, §10.1, Proposition 10.1.14, p. 473 of the
Springer 2021 book; 2017: Proposition 10.5, p. 341).

Text: if `F` is an equivalence and `𝐗^R`, `𝐘^R` are Hausdorff, `F_R : X_R → Y_R` is a
well-defined sc-smooth functor and an equivalence.

Choices:
- Setting: ep-groupoids `X : EpGroupoid Obj Mor`, `Y : EpGroupoid Obj' Mor'`, all four spaces in
  `Type` (universe 0), Hausdorff and paracompact (`RoundTrip/Blind/V7_3.lean`); `F : X → Y` an
  sc-smooth functor (the project's `EpFunctor`).
- "equivalence": my `IsEquivB` (Definition 10.1.1), copied from `RoundTrip/Blind/V10_1.lean`,
  for `F` and for `F_R`.
- `𝐗^R`: the project's `X.ReducedMor` (`Quot X.ReducedRel`, quotient topology; see
  `RoundTrip/Blind/V7_38.lean`).  "Hausdorff": `T2Space`, taken as instance hypotheses.
- `X_R`: the project's reduced ep-groupoid `X.reducedEpGroupoid` (objects `X`, morphisms `𝐗^R`
  with the M-polyfold structure of Proposition 7.9 and the descended structure maps; checked in
  `RoundTrip/Blind/V7_40.lean`).  It takes `T2Space` and `ParacompactSpace` instances for `𝐗^R`;
  the paracompactness instance is found by Lean from the Hausdorff hypothesis, so B assumes only
  what the text assumes.
- "`F_R : X_R → Y_R` is a well-defined sc-smooth functor": there is an sc-smooth functor
  `F_R : X_R → Y_R` (an `EpFunctor`) with `F_R = F` on objects and `F_R [φ] = [F φ]` on
  morphisms.  "and an equivalence": `IsEquivB F_R`.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_11
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

/-- Proposition 10.1.14: for an equivalence `F` with `𝐗^R`, `𝐘^R` Hausdorff, `F_R = (F, [φ] ↦
[F φ])` is an sc-smooth functor `X_R → Y_R` and an equivalence. -/
def B : Prop :=
  ∀ (Obj Mor Obj' Mor' : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
    [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
    (X : EpGroupoid Obj Mor) (Y : EpGroupoid Obj' Mor') (F : EpFunctor X Y)
    [T2Space X.ReducedMor] [T2Space Y.ReducedMor],
    IsEquivB F →
      ∃ FR : EpFunctor X.reducedEpGroupoid Y.reducedEpGroupoid,
        (∀ x : Obj, FR.obj x = F.obj x) ∧
        (∀ φ : Mor, FR.mor (X.reducedπ φ) = Y.reducedπ (F.mor φ)) ∧
        IsEquivB FR

end RoundTrip.V10_11
