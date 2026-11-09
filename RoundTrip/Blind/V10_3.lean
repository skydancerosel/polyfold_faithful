import Polyfold
/-! Blind formalization of V10_3 (the text's Part II, §10.1, Proposition 10.1.3, p. 462 of the
Springer 2021 book; 2017: Proposition 10.1, p. 334).

Text: for an open covering `𝒰` of the object M-polyfold of `X`, the ep-groupoid `X_𝒰` of pairs
`(U, x)` and triples `(U, φ, V)`, with the structure induced from `X` and `𝐗`, and the functor
`(U, x) ↦ x`, `(U, φ, V) ↦ φ` is an equivalence.

Choices:
- Setting: an ep-groupoid `X : EpGroupoid Obj Mor`, `Obj Mor : Type` (universe 0), Hausdorff and
  paracompact (`RoundTrip/Blind/V7_3.lean`).
- The covering: the project's `X.OpenCover ι` (read with `#print`: a family `U_i`, `i : ι`, of
  open sets of objects covering `Obj`), with `ι : Type` carrying the discrete topology.  The
  text's covering, a set `𝒰` of open sets, is the case `ι = 𝒰`; an indexed family is the general
  case (repetitions allowed).
- `X_𝒰`: the project's construction `𝒰.epGroupoid` and functor `𝒰.functor` (I cannot build an
  ep-groupoid in B myself).  To pin them down as the text's, B states their structure: objects are
  the pairs `(i, x)` with `x ∈ U_i` (`𝒰.objSet`, read with `#print`), morphisms the triples
  `((i, j), φ)` with `s φ ∈ U_i`, `t φ ∈ U_j` (`𝒰.morSet`); `s(i, φ, j) = (i, s φ)`,
  `t(i, φ, j) = (j, t φ)`, `(j, ψ, k) ∘ (i, φ, j) = (i, ψ ∘ φ, k)` on composable pairs,
  `1_(i, x) = (i, 1_x, i)`, `(i, φ, j)⁻¹ = (j, φ⁻¹, i)`; the functor is `(i, x) ↦ x`,
  `(i, φ, j) ↦ φ`.  The M-polyfold structures "induced from `X` and `𝐗`" are B's equations
  `PObj = 𝒰.objPolyfold`, `PMor = 𝒰.morPolyfold` (docstrings: the open subsets of `ι × X` and of
  `(ι × ι) × 𝐗`, `ι` discrete; I did not unfold them further).  The equivalence claim itself
  (the functor is a local sc-diffeomorphism on objects) ties the object structure to that of `X`.
- The project's construction needs `[Nonempty Obj]`; B carries this hypothesis.  It excludes only
  the empty ep-groupoid, where the text's claim is trivial.
- "is an equivalence": my `IsEquivB` (Definition 10.1.1), copied from
  `RoundTrip/Blind/V10_1.lean`.  "is an ep-groupoid" is the existence of `𝒰.epGroupoid` (a
  definition), not restated.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_3
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

/-- Proposition 10.1.3: for an open covering `𝒰` of the objects, `X_𝒰` (pairs `(i, x)`, triples
`(i, φ, j)`, structure induced from `X`) and the functor `X_𝒰 → X`, `(i, x) ↦ x`,
`(i, φ, j) ↦ φ`, which is an equivalence. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] [Nonempty Obj]
    (X : EpGroupoid Obj Mor) (ι : Type) [TopologicalSpace ι] [DiscreteTopology ι]
    (𝒰 : X.OpenCover ι),
    -- objects and morphisms of `X_𝒰`
    (∀ p : ι × Obj, p ∈ 𝒰.objSet ↔ p.2 ∈ 𝒰.set p.1) ∧
    (∀ q : (ι × ι) × Mor, q ∈ 𝒰.morSet ↔ X.src q.2 ∈ 𝒰.set q.1.1 ∧ X.tgt q.2 ∈ 𝒰.set q.1.2) ∧
    -- the structure maps of `X_𝒰`
    (∀ q : 𝒰.morSet, ((𝒰.epGroupoid.src q : 𝒰.objSet) : ι × Obj) = (q.1.1.1, X.src q.1.2)) ∧
    (∀ q : 𝒰.morSet, ((𝒰.epGroupoid.tgt q : 𝒰.objSet) : ι × Obj) = (q.1.1.2, X.tgt q.1.2)) ∧
    (∀ q q' : 𝒰.morSet, 𝒰.epGroupoid.src q = 𝒰.epGroupoid.tgt q' →
      ((𝒰.epGroupoid.comp q q' : 𝒰.morSet) : (ι × ι) × Mor) =
        ((q'.1.1.1, q.1.1.2), X.comp q.1.2 q'.1.2)) ∧
    (∀ p : 𝒰.objSet,
      ((𝒰.epGroupoid.unit p : 𝒰.morSet) : (ι × ι) × Mor) = ((p.1.1, p.1.1), X.unit p.1.2)) ∧
    (∀ q : 𝒰.morSet,
      ((𝒰.epGroupoid.inv q : 𝒰.morSet) : (ι × ι) × Mor) = ((q.1.1.2, q.1.1.1), X.inv q.1.2)) ∧
    -- the M-polyfold structures induced from `X` and `𝐗`
    𝒰.epGroupoid.PObj = 𝒰.objPolyfold ∧ 𝒰.epGroupoid.PMor = 𝒰.morPolyfold ∧
    -- the functor `(i, x) ↦ x`, `(i, φ, j) ↦ φ`, and it is an equivalence
    (∀ p : 𝒰.objSet, 𝒰.functor.obj p = p.1.2) ∧
    (∀ q : 𝒰.morSet, 𝒰.functor.mor q = q.1.2) ∧
    IsEquivB 𝒰.functor

end RoundTrip.V10_3
