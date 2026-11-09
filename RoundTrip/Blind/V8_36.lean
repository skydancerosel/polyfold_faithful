import Polyfold
/-! Blind formalization of V8_36 (the 2017 book, arXiv 1707.08941, Part II, §8.4, Theorem 8.6
(Proper Covering II) and its proof, pp. 283–284; 2021: Theorem 8.5.8).

Text: let `F : Y → X` be a proper covering functor, `x ∈ X`; `C` the full subcategory of `X` on
`x` (morphisms `G_x`), `D` the full subcategory on the finite set `F⁻¹(x)`.  Then `f = F|D : D → C`
is a covering functor.  Given a sufficiently small open neighborhood `U(x)` of `x` as in Theorem
8.5.3, there exist a geometric lift `A : K → L` of `f` and fully faithful open embedding functors
`Φ : L → X`, `Ψ : K → Y`, the image of `Φ` the full subcategory associated with `U(x)` and the image
of `Ψ` the full subcategory associated with `F⁻¹(U(x))`, such that `F ∘ Ψ = Φ ∘ A`.  (Proof:
`L_C(x) = U(x)`, `L_C(g) = Φ(g)`, `L_D(y) = U(y)`, `L_D(ψ) = t ∘ (s|𝐔(ψ₀))⁻¹` for `ψ : y → y'` in
`𝐔(ψ₀)`, `τ(y) = F|U(y)`; "one verifies" this is a geometric lift, and `A : K → L`,
`L = G_x ⋉ U(x)`, is its functor of Proposition 8.5.7.)

Choices:
- Setting: spaces in `Type`, Hausdorff paracompact; the project's `EpGroupoid`, `EpFunctor`,
  `EpFunctor.IsProperCovering` (= Definition 8.5.1, `#print`ed, see V8_29).
- `D`: the project's `F.FiberCat x` (`#print`ed: objects the points of `F⁻¹(x)`, `a ⟶ b` the
  morphisms `mor(a, b)` of `Y` (a subtype, checked by `rfl`), composition that of `Y`).  `C`:
  `SingleObj G_x` with the project's group `X.Isotropy x` (`g ∘ h = g * h`).  `f = F|D`: the
  project's `F.restrictFiber x` (`#print`ed / `rfl`: `ψ ↦ F(ψ) ∈ G_x`).  Covering functor: the
  project's `IsCoveringFunctor` (= the text's definition, see V8_32).
- "A sufficiently small `U(x)` as in Theorem 8.5.3": as in my V8_30, an open `V ∋ x` such that the
  conclusion holds for every connected `U(x) ⊆ V` with natural-action data `(Φr, Γr)`
  (`IsNatAction`, copied from V7_21/V8_30).
- "A geometric lift `A : K → L`": a project `GeometricLift` `L` of `f` together with its functor
  of Proposition 8.5.7, characterized exactly as in my `RoundTrip/Blind/V8_35.lean` (`IsModelB`,
  copied: `L = G_x ⋉ U(x)` on `L_C(x)` and `G_x × L_C(x)`, `K` on `⨆ L_D(y)` and
  `⨆ mor(y, y') × L_D(y)`, the text's structure maps, disjoint-union M-polyfold structures, `A`
  given by `τ` and `f`), with `G_x` discrete and the needed paracompactness asserted.
- Fully faithful open embedding functor (my `IsFFOEB`): bijective on every `mor(a, b)`, and on
  objects and on morphisms an sc-diffeomorphism onto its image (`IsScDiffeoOn` onto the range,
  which makes the range open).  "Image the full subcategory associated with `U(x)`": the ranges of
  `Φ` on objects and morphisms are `U(x)` and `{φ | s φ, t φ ∈ U(x)}`; likewise for `Ψ` and
  `F⁻¹(U(x))`.  `F ∘ Ψ = Φ ∘ A` on objects and on morphisms.
- The proof's description of the lift, read through the embeddings: `L_C(g) = Φr(g)`:
  `Φ(g ∗ z) = Φr(g)(Φ(z))`; `L_D(y) = U(y)`: `Ψ` maps the summand `L_D(y)` onto `U(y)`; and
  `L_D(ψ) = t ∘ (s|𝐔(ψ))⁻¹`: `Ψ` maps `(ψ, z)` into the sheet `𝐔(ψ)` (then `Ψ(ψ, z)` is the
  `s`-lift of `Ψ(z)` in `𝐔(ψ)`, and `L_D(ψ)` is `t ∘ (s|𝐔(ψ))⁻¹` by functoriality).  Here `U(y)`,
  `𝐔(ψ)` are those of Theorem 8.5.3, which (0), (2) there force to be the connected component of
  `F⁻¹(U(x))` containing `y` and the connected component of `{φ | s φ ∈ U(a), t φ ∈ U(b)}`
  containing `ψ` (see my V8_31); I write them so.  `τ(y) = F|U(y)` then follows from
  `F ∘ Ψ = Φ ∘ A` and `A|L_D(y) = τ(y)`.
- Nothing looks false to me.
-/
namespace RoundTrip.V8_36
open Polyfold CategoryTheory

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- The natural `G_x`-action on the open neighbourhood `U` of `x` (as in V7_21, V8_30). -/
structure IsNatAction (X : EpGroupoid Obj Mor) (x : Obj) (U : Set Obj)
    (Φ : X.Isotropy x → Obj → Obj) (Γ : X.Isotropy x → Obj → Mor) : Prop where
  isOpen : IsOpen U
  mem : x ∈ U
  diffeo : ∀ g, ∃ ψ : Obj → Obj, X.PObj.IsScDiffeoOn X.PObj (Φ g) ψ U U
  hom : ∀ g h, ∀ y ∈ U, Φ (g * h) y = Φ g (Φ h y)
  smooth : ∀ g, X.PObj.IsScSmoothOn X.PMor (Γ g) U
  Γ_x : ∀ g, Γ g x = g.val
  src_tgt : ∀ g, ∀ y ∈ U, X.src (Γ g y) = y ∧ X.tgt (Γ g y) = Φ g y
  unique : ∀ h : Mor, X.src h ∈ U → X.tgt h ∈ U → ∃! g, Γ g (X.src h) = h

end

/-- The morphisms between points of `S`. -/
def morOnB {Obj Mor : Type} (G : GroupoidStr Obj Mor) (S : Set Obj) : Set Mor :=
  {φ | G.src φ ∈ S ∧ G.tgt φ ∈ S}

/-- `mor(a, b)`. -/
def morB {Obj Mor : Type} (G : GroupoidStr Obj Mor) (a b : Obj) : Set Mor :=
  {φ | G.src φ = a ∧ G.tgt φ = b}

/-- A fully faithful open embedding functor `Φ : X' → X`. -/
def IsFFOEB {Obj Mor Obj' Mor' : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
    [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
    {X' : EpGroupoid Obj' Mor'} {X : EpGroupoid Obj Mor} (Φ : EpFunctor X' X) : Prop :=
  (∀ a b : Obj', Set.BijOn Φ.mor (morB X'.toGroupoidStr a b)
    (morB X.toGroupoidStr (Φ.obj a) (Φ.obj b))) ∧
  (∃ g : Obj → Obj', X'.PObj.IsScDiffeoOn X.PObj Φ.obj g Set.univ (Set.range Φ.obj)) ∧
  (∃ g : Mor → Mor', X'.PMor.IsScDiffeoOn X.PMor Φ.mor g Set.univ (Set.range Φ.mor))

section
variable {D : Type} [Groupoid D] {G : Type} [Group G] {f : D ⥤ SingleObj G}

/-- `U(x) = L_C(x)` (as in V8_35). -/
abbrev UxB (L : GeometricLift.{0} f) : Type := (L.LC.obj (SingleObj.star G)).carrier

/-- The objects `⨆_{y ∈ D} L_D(y)` (as in V8_35). -/
abbrev ObjYB (L : GeometricLift.{0} f) : Type := Σ y : D, (L.LD.obj y).carrier

/-- The morphisms `⨆_{(y, y')} mor(y, y') × L_D(y)` (as in V8_35). -/
abbrev MorYB (L : GeometricLift.{0} f) : Type :=
  Σ ψ : (Σ (a : D) (b : D), (a ⟶ b)), (L.LD.obj ψ.1).carrier

/-- The action `g ∗ z = L_C(g)(z)` (as in V8_35). -/
def actB (L : GeometricLift.{0} f) (g : G) (z : UxB L) : UxB L :=
  (L.LC.map (show SingleObj.star G ⟶ SingleObj.star G from g)).toFun z

/-- The construction of Proposition 8.5.7 (copied from V8_35). -/
def IsModelB (L : GeometricLift.{0} f) [TopologicalSpace G] [DiscreteTopology G]
    [ParacompactSpace (ObjYB L)]
    [ParacompactSpace (MorYB L)] [ParacompactSpace (G × UxB L)]
    (EY : EpGroupoid (ObjYB L) (MorYB L)) (EX : EpGroupoid (UxB L) (G × UxB L))
    (A : EpFunctor EY EX) : Prop :=
  (∀ p : G × UxB L, EX.src p = p.2) ∧
  (∀ p : G × UxB L, EX.tgt p = actB L p.1 p.2) ∧
  (∀ p q : G × UxB L, EX.src p = EX.tgt q → EX.comp p q = (p.1 * q.1, q.2)) ∧
  (∀ z : UxB L, EX.unit z = (1, z)) ∧
  (∀ p : G × UxB L, EX.inv p = (p.1⁻¹, actB L p.1 p.2)) ∧
  (∃ h : UxB L → UxB L,
    (L.LC.obj (SingleObj.star G)).P.IsScDiffeoOn EX.PObj id h Set.univ Set.univ) ∧
  (∀ g : G, ∃ h : G × UxB L → UxB L,
    (L.LC.obj (SingleObj.star G)).P.IsScDiffeoOn EX.PMor (fun z => (g, z)) h Set.univ
      {p | p.1 = g}) ∧
  (∀ (ψ : Σ (a : D) (b : D), (a ⟶ b)) (z : (L.LD.obj ψ.1).carrier),
    EY.src ⟨ψ, z⟩ = ⟨ψ.1, z⟩) ∧
  (∀ (a b : D) (ψ : a ⟶ b) (z : (L.LD.obj a).carrier),
    EY.tgt ⟨⟨a, b, ψ⟩, z⟩ = ⟨b, (L.LD.map ψ).toFun z⟩) ∧
  (∀ (a b c : D) (γ : a ⟶ b) (ψ : b ⟶ c) (z : (L.LD.obj a).carrier),
    EY.comp ⟨⟨b, c, ψ⟩, (L.LD.map γ).toFun z⟩ ⟨⟨a, b, γ⟩, z⟩ = ⟨⟨a, c, γ ≫ ψ⟩, z⟩) ∧
  (∀ (y : D) (z : (L.LD.obj y).carrier), EY.unit ⟨y, z⟩ = ⟨⟨y, y, 𝟙 y⟩, z⟩) ∧
  (∀ (a b : D) (ψ : a ⟶ b) (z : (L.LD.obj a).carrier),
    EY.inv ⟨⟨a, b, ψ⟩, z⟩ = ⟨⟨b, a, Groupoid.inv ψ⟩, (L.LD.map ψ).toFun z⟩) ∧
  (∀ y : D, ∃ h : ObjYB L → (L.LD.obj y).carrier,
    (L.LD.obj y).P.IsScDiffeoOn EY.PObj (fun z => (⟨y, z⟩ : ObjYB L)) h Set.univ
      (Set.range (fun z => (⟨y, z⟩ : ObjYB L)))) ∧
  (∀ ψ : Σ (a : D) (b : D), (a ⟶ b), ∃ h : MorYB L → (L.LD.obj ψ.1).carrier,
    (L.LD.obj ψ.1).P.IsScDiffeoOn EY.PMor (fun z => (⟨ψ, z⟩ : MorYB L)) h Set.univ
      (Set.range (fun z => (⟨ψ, z⟩ : MorYB L)))) ∧
  (∀ (y : D) (z : (L.LD.obj y).carrier), A.obj ⟨y, z⟩ = (L.τ.app y).toFun z) ∧
  (∀ (a b : D) (ψ : a ⟶ b) (z : (L.LD.obj a).carrier),
    A.mor ⟨⟨a, b, ψ⟩, z⟩ = ((f.map ψ : G), (L.τ.app a).toFun z))

end

/-- Theorem 8.5.8: `f = F|D` is a covering functor; for every sufficiently small connected
`U(x)` with the natural action there are a geometric lift of `f`, its functor `A : K → L` of
Proposition 8.5.7, and fully faithful open embeddings `Φ : L → X`, `Ψ : K → Y` onto the full
subcategories on `U(x)` and `F⁻¹(U(x))` with `F ∘ Ψ = Φ ∘ A`, the lift being the one of the
proof. -/
def B : Prop :=
  ∀ (ObjY MorY ObjX MorX : Type)
    [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
    [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
    [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
    [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
    (Y : EpGroupoid ObjY MorY) (X : EpGroupoid ObjX MorX) (F : EpFunctor Y X),
    F.IsProperCovering → ∀ x : ObjX,
      IsCoveringFunctor (F.restrictFiber x) ∧
      ∃ V : Set ObjX, IsOpen V ∧ x ∈ V ∧
        ∀ (U : Set ObjX) (Φr : X.Isotropy x → ObjX → ObjX) (Γr : X.Isotropy x → ObjX → MorX),
          IsNatAction X x U Φr Γr → IsConnected U → U ⊆ V →
          letI : TopologicalSpace (X.Isotropy x) := ⊥
          haveI : DiscreteTopology (X.Isotropy x) := ⟨rfl⟩
          ∃ (L : GeometricLift.{0} (F.restrictFiber x))
            (_ : ParacompactSpace (ObjYB L)) (_ : ParacompactSpace (MorYB L))
            (_ : ParacompactSpace (X.Isotropy x × UxB L))
            (K : EpGroupoid (ObjYB L) (MorYB L)) (Lg : EpGroupoid (UxB L) (X.Isotropy x × UxB L))
            (A : EpFunctor K Lg) (Φ : EpFunctor Lg X) (Ψ : EpFunctor K Y),
            IsModelB L K Lg A ∧ IsFFOEB Φ ∧ IsFFOEB Ψ ∧
            -- the images
            Set.range Φ.obj = U ∧ Set.range Φ.mor = morOnB X.toGroupoidStr U ∧
            Set.range Ψ.obj = F.obj ⁻¹' U ∧
            Set.range Ψ.mor = morOnB Y.toGroupoidStr (F.obj ⁻¹' U) ∧
            -- `F ∘ Ψ = Φ ∘ A`
            F.obj ∘ Ψ.obj = Φ.obj ∘ A.obj ∧ F.mor ∘ Ψ.mor = Φ.mor ∘ A.mor ∧
            -- the proof: `L_C(g) = Φr(g)`
            (∀ (g : X.Isotropy x) (z : UxB L), Φ.obj (actB L g z) = Φr g (Φ.obj z)) ∧
            -- the proof: `L_D(y) = U(y)`
            (∀ y : F.FiberCat x,
              Set.range (fun z : (L.LD.obj y).carrier => Ψ.obj ⟨y, z⟩) =
                connectedComponentIn (F.obj ⁻¹' U) y.val) ∧
            -- the proof: `L_D(ψ) = t ∘ (s|𝐔(ψ))⁻¹`
            (∀ (a b : F.FiberCat x) (ψ : a ⟶ b) (z : (L.LD.obj a).carrier),
              Ψ.mor ⟨⟨a, b, ψ⟩, z⟩ ∈ connectedComponentIn
                {φ : MorY | Y.src φ ∈ connectedComponentIn (F.obj ⁻¹' U) a.val ∧
                  Y.tgt φ ∈ connectedComponentIn (F.obj ⁻¹' U) b.val} ψ.1)

end RoundTrip.V8_36
