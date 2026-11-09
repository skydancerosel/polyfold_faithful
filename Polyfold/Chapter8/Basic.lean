import Polyfold.Chapter7.Lift
import Polyfold.Chapter7.LocalDiffeo
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.NatTrans

set_option maxSynthPendingDepth 3

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2017, arXiv 1707.08941), Part II,
Chapter 8, "Bundles and Covering Functors": the **definitions** that do not need strong bundles
(Definitions 8.1.13, 8.5.1, 8.5.5 (2017: 8.1, 8.8, 8.9), pp. 266, 275, 279) and the **structure maps of the tangent**
`T(X, 𝐗) = (TX, T𝐗)` of an ep-groupoid ((8.1)–(8.9), pp. 257–258).  Numbers and pages are the
2017 text's (there is no 2014 preprint of Part II).  The theorems about these objects are in the
other files of `Polyfold/Chapter8/`.

# Definitions of Chapter 8

## The text, paraphrased

(§8.1, pp. 257–258) The tangent of the ep-groupoid `(X, 𝐗)` is the pair `(TX, T𝐗)`.  A tangent
vector `(φ, h) ∈ T_φ𝐗` is viewed as a morphism `T s(φ)(h) → T t(φ)(h)`: `s_T = Ts`, `t_T = Tt`
(8.3).  For `T s(ψ)(k) = T t(φ)(h)` (8.4), `(ψ, k) ∘ (φ, h) = (ψ ∘ φ, T s(ψ ∘ φ)⁻¹(T s(φ)(h)))`
(8.5), in short `k ∘ h = T s(p(k) ∘ p(h))⁻¹ T s(p(h))(h)` (8.6), `p : T𝐗 → 𝐗¹` the projection; the
unit of `a ∈ T_xX` is `1_a = (1_x, T s(1_x)⁻¹(a))` (8.7), (8.8); the inverse is
`ι_T(φ, k) = (φ⁻¹, T ι(φ)(k))` (8.9).

(Definition 8.1.13 (2017: 8.1), p. 367 (2017 p. 266)) Two sc-smooth functors `F, G : X → Y` are naturally equivalent, `F ≃ G`,
if there is an sc-smooth map `τ : X → 𝐘` with `τ(x) : F(x) → G(x)` and `τ(x') ∘ F(h) = G(h) ∘ τ(x)`
for every `h : x → x'`; `τ` is a natural transformation `τ : F → G`.

(Definition 8.5.1 (2017: 8.8), p. 383 (2017 p. 275)) An sc-smooth functor `F : Y → X` is a proper covering functor if
(1) `F : Y → X` on objects is a surjective local sc-diffeomorphism; (2) every `F⁻¹(x)` is finite,
and there are an open `U(x)` and mutually disjoint open `U(y) ∋ y`, `y ∈ F⁻¹(x)`, with
`F : U(y) → U(x)` sc-diffeomorphisms and `F⁻¹(U(x)) = ⋃ U(y)`; (3) `𝐘 → 𝐗 ₛ×_F Y`,
`φ ↦ (F(φ), s(φ))`, is an sc-diffeomorphism.

(Definition 8.5.5 (2017: 8.9), p. 388 (2017 p. 279)) `D`, `C` categories with finitely many objects and morphisms, all
morphisms isomorphisms, `C` with a single object `x`.  A covering functor `f : D → C` is a functor
with `D → C ₛ×_f D`, `ψ ↦ (f(ψ), s(ψ))`, a bijection.  A geometric lift of `f` consists of functors
`L_D : D → Diff_sc`, `L_C : C → Diff_sc` and a natural transformation `τ : L_D → L_C ∘ f`;
`Diff_sc` is the category of M-polyfolds and sc-diffeomorphisms (p. 279).

## What is formalized

* The tangent data (`EpGroupoid.tSrc`, `tTgt`, `tUnit`, `tInv`, `tBase`, `tComp`): the tangent maps
  of `s, t, u, ι` (Part I's `MPolyfold.tangentMap`) and the composition (8.6) by choice, as
  Chapter 7's `tangentMor`.  That `tUnit = Tu` is (8.8) is Lemma 8.1.5 (2017: 8.4)'s first computation; that
  these maps form an ep-groupoid is Theorem 8.1.1 (2017: 8.1) (`TangentEp.lean`).
* `EpNatTrans F G` (**Definition 8.1.13 (2017: 8.1)**), `EpFunctor.NaturallyEquivalent`.
* `EpFunctor.IsProperCovering` (**Definition 8.5.1 (2017: 8.8)**), condition (3) on Part I's fibred-product
  sub-M-polyfold (`MPolyfold.subPolyfold (isSubMPolyfold_fibredProduct …)`, as Definition 7.1.3 (2017: 7.3) (4)).
* `MPolyfoldCat` and `ScDiffeo` (the category `Diff_sc`), `IsCoveringFunctor`, `GeometricLift`
  (**Definition 8.5.5 (2017: 8.9)**).

## What the text leaves implicit, and the choices made

* `T𝐗`'s composition is total in Lean (the junk value `h` off composable pairs, as Chapter 7's
  `GroupoidStr.comp`); on composable pairs it is the unique `v ∈ T_{p k ∘ p h}𝐗` with
  `Ts(v) = Ts(h)` (uniqueness: `Ts` is injective on the fibres, `s` being a local
  sc-diffeomorphism).  The text's (8.5) writes `T_{φ∘ψ}𝐗` for `T_{ψ∘φ}𝐗` (possible misprint).
* `TX` and `T𝐗` are Part I's `TangentSpace`, in `Type (max u 1)` for `X : Type u`.
* In Definition 8.5.1 (2017: 8.8) (2) the neighbourhood `U(x)` is open and the `U(y)` are indexed by the points
  of `F⁻¹(x)` with local inverses `σ y : U(x) → U(y)`.
* In Definition 8.5.5 (2017: 8.9) the category `C` with one object is `SingleObj G` for a finite group `G` (its
  automorphisms), `D` a finite Mathlib `Groupoid` (finitely many objects and morphisms);
  `C ₛ×_f D = G × D` since `C` has one object.  The finiteness of `D`, of its hom-sets and of `G`
  is not part of `IsCoveringFunctor` and `GeometricLift` (unused instance arguments are dropped):
  it is carried as the instance arguments `[Fintype D] [∀ a b, Fintype (a ⟶ b)] [Fintype G]` of the
  results that use it (Proposition 8.5.7 (2017: 8.3), Theorem 8.5.8 (2017: 8.6)).  `Diff_sc` (`MPolyfoldCat`) has bundled
  M-polyfolds of one universe as objects and sc-diffeomorphisms (`IsScDiffeoOn` on `univ`) as
  morphisms.
-/

open Set Function CategoryTheory

noncomputable section

namespace Polyfold

universe u v w

/-! ### The structure maps of the tangent `T(X, 𝐗)` ((8.1)–(8.9), pp. 257–258) -/

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- The source map `s_T = Ts : T𝐗 → TX` (8.3). -/
def tSrc : X.PMor.TangentSpace → X.PObj.TangentSpace := MPolyfold.tangentMap X.isScSmoothMap_src

/-- The target map `t_T = Tt : T𝐗 → TX` (8.3). -/
def tTgt : X.PMor.TangentSpace → X.PObj.TangentSpace := MPolyfold.tangentMap X.isScSmoothMap_tgt

/-- The unit map `u_T = Tu : TX → T𝐗`; (8.8) `u_T(a) = (1_x, T s(1_x)⁻¹(a))` is Lemma 8.1.5 (2017: 8.4). -/
def tUnit : X.PObj.TangentSpace → X.PMor.TangentSpace := MPolyfold.tangentMap X.isScSmoothMap_unit

/-- The inverse map `ι_T(φ, k) = (φ⁻¹, T ι(φ)(k))`, i.e. `ι_T = Tι` (8.9). -/
def tInv : X.PMor.TangentSpace → X.PMor.TangentSpace := MPolyfold.tangentMap X.isScSmoothMap_inv

/-- The base point `p(h) ∈ 𝐗¹ ⊆ 𝐗` of a tangent vector `h ∈ T_φ𝐗`. -/
def tBase (v : X.PMor.TangentSpace) : Mor := X.PMor.levelVal 1 (X.PMor.tangentProj v)

open scoped Classical in
/-- The composition (8.5)–(8.6): `k ∘ h = T s(p(k) ∘ p(h))⁻¹ (T s(p(h))(h))`, the vector `v` over
`p(k) ∘ p(h)` with `Ts(v) = Ts(h)` (unique: Lemma 8.1.7 (2017: 8.6), `s` a local sc-diffeomorphism); `h` when
there is none (never, for composable pairs). -/
def tComp (k h : X.PMor.TangentSpace) : X.PMor.TangentSpace :=
  if hv : ∃ v : X.PMor.TangentSpace, X.tBase v = X.comp (X.tBase k) (X.tBase h) ∧
      X.tSrc v = X.tSrc h then hv.choose
  else h

end EpGroupoid

/-! ### Definition 8.1.13 (2017: 8.1): natural transformations -/

section NatTrans

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}

/-- **Definition 8.1.13 (2017: 8.1) (natural transformation)**: an sc-smooth map `τ : X → 𝐘` with
`τ(x) : F(x) → G(x)` and `τ(x') ∘ F(h) = G(h) ∘ τ(x)` for every morphism `h : x → x'`. -/
structure EpNatTrans (F G : EpFunctor X Y) where
  /-- The morphism `τ(x) : F(x) → G(x)`. -/
  app : Obj → Mor'
  isScSmoothMap_app : X.PObj.IsScSmoothMap Y.PMor app
  src_app : ∀ x, Y.src (app x) = F.obj x
  tgt_app : ∀ x, Y.tgt (app x) = G.obj x
  naturality : ∀ h : Mor, Y.comp (app (X.tgt h)) (F.mor h) = Y.comp (G.mor h) (app (X.src h))

/-- **Definition 8.1.13 (2017: 8.1) (natural equivalence)**: `F ≃ G` if there is a natural transformation
`τ : F → G`. -/
def EpFunctor.NaturallyEquivalent (F G : EpFunctor X Y) : Prop := Nonempty (EpNatTrans F G)

end NatTrans

/-! ### Definition 8.5.1 (2017: 8.8): proper covering functors -/

section ProperCovering

variable {ObjY MorY : Type u} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  {ObjX MorX : Type v} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {Y : EpGroupoid ObjY MorY} {X : EpGroupoid ObjX MorX}

/-- The map `L_F : 𝐘 → 𝐗 ₛ×_F Y`, `φ ↦ (F(φ), s(φ))` of Definition 8.5.1 (2017: 8.8) (3). -/
def EpFunctor.fibredMap (F : EpFunctor Y X) (φ : MorY) :
    MPolyfold.fibredProduct X.src F.obj :=
  ⟨(F.mor φ, Y.src φ), F.src_mor φ⟩

/-- **Definition 8.5.1 (2017: 8.8) (proper covering functor)**: (1) `F` is a surjective local
sc-diffeomorphism on objects; (2) the fibres `F⁻¹(x)` are finite and evenly covered: an open
`U(x) ∋ x` and mutually disjoint `U(y) ∋ y`, `y ∈ F⁻¹(x)`, with `F : U(y) → U(x)`
sc-diffeomorphisms (inverses `σ y`) and `F⁻¹(U(x)) = ⋃_{y ∈ F⁻¹(x)} U(y)`; (3) `φ ↦ (F(φ), s(φ))`
is an sc-diffeomorphism `𝐘 → 𝐗 ₛ×_F Y` onto Part I's fibred-product sub-M-polyfold of
`𝐗 × Y`. -/
structure EpFunctor.IsProperCovering (F : EpFunctor Y X) : Prop where
  surjective : Surjective F.obj
  isLocalScDiffeo : Y.PObj.IsLocalScDiffeo X.PObj F.obj
  finite_fiber : ∀ x, (F.obj ⁻¹' {x}).Finite
  evenlyCovered : ∀ x, ∃ (U : Set ObjX) (V : ObjY → Set ObjY) (σ : ObjY → ObjX → ObjY),
    IsOpen U ∧ x ∈ U ∧ (F.obj ⁻¹' {x}).PairwiseDisjoint V ∧
    (∀ y ∈ F.obj ⁻¹' {x}, y ∈ V y ∧ Y.PObj.IsScDiffeoOn X.PObj F.obj (σ y) (V y) U) ∧
    F.obj ⁻¹' U = ⋃ y ∈ F.obj ⁻¹' {x}, V y
  isScDiffeo_fibredMap :
    letI := MPolyfold.paracompactSpace_prod X.PMor Y.PObj
    letI := (X.PMor.prod Y.PObj).paracompactSpace_subtype (MPolyfold.fibredProduct X.src F.obj)
    ∃ g : MPolyfold.fibredProduct X.src F.obj → MorY,
      Y.PMor.IsScDiffeoOn (MPolyfold.subPolyfold
        (MPolyfold.isSubMPolyfold_fibredProduct X.isLocalScDiffeo_src F.isScSmoothMap_obj))
        F.fibredMap g univ univ

end ProperCovering

/-! ### Definition 8.5.5 (2017: 8.9): covering functors of finite groupoids and geometric lifts -/

/-- An object of `Diff_sc` (p. 279): an M-polyfold, bundled. -/
structure MPolyfoldCat : Type (u + 1) where
  /-- The underlying space. -/
  carrier : Type u
  [instTop : TopologicalSpace carrier]
  [instT2 : T2Space carrier]
  [instPara : ParacompactSpace carrier]
  /-- The M-polyfold structure. -/
  P : MPolyfold carrier

attribute [instance] MPolyfoldCat.instTop MPolyfoldCat.instT2 MPolyfoldCat.instPara

/-- A morphism of `Diff_sc`: an sc-diffeomorphism `A → B`. -/
structure ScDiffeo (A B : MPolyfoldCat.{u}) where
  /-- The map. -/
  toFun : A.carrier → B.carrier
  /-- Its inverse. -/
  invFun : B.carrier → A.carrier
  isScDiffeoOn : A.P.IsScDiffeoOn B.P toFun invFun univ univ

namespace ScDiffeo

theorem ext {A B : MPolyfoldCat.{u}} {f g : ScDiffeo A B} (h : f.toFun = g.toFun) : f = g := by
  have hinv : f.invFun = g.invFun := funext fun b => by
    have h1 := f.isScDiffeoOn.right_inv b (mem_univ b)
    have h2 := g.isScDiffeoOn.left_inv (f.invFun b) (mem_univ _)
    rw [← h] at h2
    rw [h1] at h2
    exact h2.symm
  cases f; cases g
  cases h; cases hinv
  rfl

/-- The identity sc-diffeomorphism. -/
def id (A : MPolyfoldCat.{u}) : ScDiffeo A A :=
  ⟨_root_.id, _root_.id, MPolyfold.isScDiffeoOn_id isOpen_univ⟩

/-- The composition `g ∘ f`. -/
def comp {A B C : MPolyfoldCat.{u}} (f : ScDiffeo A B) (g : ScDiffeo B C) : ScDiffeo A C :=
  ⟨g.toFun ∘ f.toFun, f.invFun ∘ g.invFun, g.isScDiffeoOn.comp f.isScDiffeoOn⟩

end ScDiffeo

/-- **`Diff_sc`** (p. 279): M-polyfolds and sc-diffeomorphisms. -/
instance : Category MPolyfoldCat.{u} where
  Hom A B := ScDiffeo A B
  id A := ScDiffeo.id A
  comp f g := ScDiffeo.comp f g
  id_comp _ := ScDiffeo.ext rfl
  comp_id _ := ScDiffeo.ext rfl
  assoc _ _ _ := ScDiffeo.ext rfl

section CoveringFunctor

variable {D : Type u} [Groupoid.{u} D] [Fintype D] [∀ a b : D, Fintype (a ⟶ b)]
  {G : Type u} [Group G] [Fintype G]

/-- The map `D → C ₛ×_f D = G × D`, `ψ ↦ (f(ψ), s(ψ))`, on the morphisms `ψ : a → b` of `D`. -/
def coveringMap (f : D ⥤ SingleObj G) (ψ : Σ a b : D, a ⟶ b) : G × D :=
  ((f.map ψ.2.2 : G), ψ.1)

/-- **Definition 8.5.5 (2017: 8.9) (covering functor)**: `f : D → C` (here `C = SingleObj G`, one object with
automorphism group `G`) with `ψ ↦ (f(ψ), s(ψ))` a bijection from the morphisms of `D` onto
`C ₛ×_f D = G × D`. -/
def IsCoveringFunctor (f : D ⥤ SingleObj G) : Prop := Bijective (coveringMap f)

/-- **Definition 8.5.5 (2017: 8.9) (geometric lift)** of a covering functor `f : D → C`: functors
`L_D : D → Diff_sc`, `L_C : C → Diff_sc` and a natural transformation `τ : L_D → L_C ∘ f`. -/
structure GeometricLift (f : D ⥤ SingleObj G) where
  /-- `L_D`, with `U(y) = L_D(y)`. -/
  LD : D ⥤ MPolyfoldCat.{u}
  /-- `L_C`, with `U(x) = L_C(x)`. -/
  LC : SingleObj G ⥤ MPolyfoldCat.{u}
  /-- `τ(y) : U(y) → U(x)`. -/
  τ : LD ⟶ f ⋙ LC

end CoveringFunctor

end Polyfold
