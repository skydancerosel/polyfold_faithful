import Polyfold
/-! Blind formalization of V8_30 (the 2017 book, arXiv 1707.08941, Part II, §8.4, Theorem 8.5
(Proper Covering I), p. 277; 2021: Theorem 8.5.3, p. 385).

Text: let `F : Y → X` be a proper covering functor and `x ∈ X`.  Then for a connected and
sufficiently small open neighborhood `U(x)` admitting the natural `G_x`-action (data `(Φ, Γ)`):
(0) `F⁻¹(U(x))` is a disjoint union of connected open neighborhoods `U(y)` of all `y ∈ F⁻¹(x)`,
every `F : U(y) → U(x)` an sc-diffeomorphism; (1) `Γ(G_x, U(x)) = {φ | s φ, t φ ∈ U(x)} =: 𝐔(x)`
is the union of connected components `𝐔(g)`, `g ∈ G_x`, and `s, t : 𝐔(g) → U(x)` are
sc-diffeomorphisms; (2) for `y, y' ∈ F⁻¹(x)`, `𝐔(y, y') = {ψ | s ψ ∈ U(y), t ψ ∈ U(y')}` is the
disjoint union of connected open neighborhoods `𝐔(ψ₀)` of the morphisms `ψ₀ : y → y'`, for which
(3) `s : 𝐔(ψ₀) → U(y)`, `t : 𝐔(ψ₀) → U(y')` are sc-diffeomorphisms; (4) `F : 𝐔(ψ₀) → 𝐔(F(ψ₀))` is
an sc-diffeomorphism; (5) the square with top `F : 𝐔(ψ₀) → 𝐔(F(ψ₀))`, left `s : 𝐔(ψ₀) → U(s(ψ₀))`,
right `t : 𝐔(F(ψ₀)) → U(t(F(ψ₀)))`, bottom `F : U(s(ψ₀)) → U(t(F(ψ₀)))` is a commutative diagram of
sc-diffeomorphisms.

Choices:
- Setting: spaces in `Type` (universe 0, as in the Chapter 7 blind files), Hausdorff paracompact;
  the project's `EpGroupoid`, `EpFunctor`, `EpFunctor.IsProperCovering` (`#print`ed; = Definition
  8.5.1, see `RoundTrip/Blind/V8_29.lean`); sc-diffeomorphisms between open subsets are the
  project's `MPolyfold.IsScDiffeoOn` (`#print`ed: sc-smooth both ways on open sets, mutually
  inverse, mapping the sets to each other) with an existentially quantified inverse.
- "`U(x)` admitting the natural `G_x`-action (given by `(Φ, Γ)`)": my `IsNatAction X x U Φ Γ`,
  copied from `RoundTrip/Blind/V7_21.lean` (the conclusions of Theorem 7.1.13: `U` open, `x ∈ U`,
  `Φ(g)` sc-diffeomorphisms of `U`, `Φ` multiplicative, `Γ(g, ·)` sc-smooth on `U`, `Γ(g, x) = g`,
  `s Γ(g, y) = y`, `t Γ(g, y) = Φ(g)(y)`, uniqueness of `g`); `G_x` is the project's
  `X.Isotropy x` (product `g ∘ h`, checked by `rfl`).  "Connected" is a separate hypothesis.
- "For a connected and sufficiently small `U(x)`": there is an open `V ∋ x` such that the
  conclusions hold for EVERY connected `U(x) ⊆ V` with natural-action data `(Φ, Γ)` (the usual
  meaning of "sufficiently small"; the stronger of the two possible readings, the other being
  "for some such `U(x)` inside every `V`").  The `U(y)` and `𝐔(ψ₀)` are existentially quantified
  per `U(x)` (`Uy : ObjY → Set ObjY`, `UY : MorY → Set MorY`; values off `F⁻¹(x)` resp. off the
  morphisms between points of `F⁻¹(x)` are junk).
- (0): `Uy y` open, connected, `y ∈ Uy y`, `F : Uy y → U` an sc-diffeomorphism, pairwise disjoint
  on `F⁻¹(x)`, `F⁻¹(U) = ⋃_{y ∈ F⁻¹(x)} Uy y`.
- (1): `𝐔(g)` is the connected component of `𝐔(x)` containing `g` (`connectedComponentIn`, the
  reading of "connected components `𝐔(g)`, `g ∈ G_x`", as in `RoundTrip/Blind/V7_19.lean`); the
  image of `Γ` on `G_x × U` is `𝐔(x)`, `𝐔(x) = ⋃_g 𝐔(g)`, the `𝐔(g)` for distinct `g` are disjoint
  (they are enumerated by `g`), and `s, t : 𝐔(g) → U` are sc-diffeomorphisms.
- (2): for `y, y' ∈ F⁻¹(x)`, `𝐔(y, y') = ⋃_{ψ₀ ∈ mor(y, y')} UY ψ₀`, pairwise disjoint over
  `mor(y, y')`, each `UY ψ₀` open, connected, containing `ψ₀` ("centred at").  (3)–(5) for every
  morphism `ψ₀` between points of `F⁻¹(x)`.  (4): `𝐔(F(ψ₀))` is the component of `𝐔(x)` containing
  `F(ψ₀) ∈ G_x` (Remark 8.5.4 (a)), i.e. the `𝐔(g)` of (1) for `g = F(ψ₀)`.
- (5): `U(s(ψ₀))` is `Uy (s ψ₀)` and `U(t(F(ψ₀)))` is `U(x)` (`t(F(ψ₀)) = F(t(ψ₀)) = x`).  The
  four arrows are sc-diffeomorphisms (top: (4), left: (3); right and bottom restated), and
  commutativity, literally `t ∘ F = F ∘ s` on `𝐔(ψ₀)`.
- FALSE AS WRITTEN (formalized literally anyway): the commutativity in (5).  `t(F(ψ)) = F(t(ψ))`
  and `F(s(ψ)) = s(F(ψ))`, so `t ∘ F = F ∘ s` on `𝐔(ψ₀)` would force `t = s` on `𝐔(F(ψ₀))`.
  Counterexample: `X = Y = ℤ/2 ⋉ ℝ` (reflection), `F` the identity (a proper covering functor),
  `x = 0`, `U = (-ε, ε)`, `ψ₀ = (-1, 0)`: by (2) `𝐔(ψ₀)` must be the component `{(-1, z)}`, and
  `t(F(-1, z)) = -z ≠ z = F(s(-1, z))` for `z ≠ 0`.  Presumably the right arrow should be
  `s : 𝐔(F(ψ₀)) → U(s(F(ψ₀)))` (then `s ∘ F = F ∘ s`, functoriality), or `t` on both sides.
  Hence B is false.
-/
namespace RoundTrip.V8_30
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- The natural `G_x`-action on the open neighbourhood `U` of `x` (the data `Φ`, `Γ` of
Theorem 7.1.13 with its properties), as in `RoundTrip/Blind/V7_21.lean`. -/
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

/-- The morphisms between points of `S` (`𝐔(x)` for `S = U(x)`). -/
def morOnB {Obj Mor : Type} (G : GroupoidStr Obj Mor) (S : Set Obj) : Set Mor :=
  {φ | G.src φ ∈ S ∧ G.tgt φ ∈ S}

/-- `mor(y, y')`. -/
def morB {Obj Mor : Type} (G : GroupoidStr Obj Mor) (y y' : Obj) : Set Mor :=
  {φ | G.src φ = y ∧ G.tgt φ = y'}

/-- `𝐔(φ)`: the connected component of `𝐔(x)` containing `φ` (for `φ = g ∈ G_x`, or `F(ψ₀)`). -/
def compB {Obj Mor : Type} [TopologicalSpace Mor] (G : GroupoidStr Obj Mor) (U : Set Obj)
    (φ : Mor) : Set Mor :=
  connectedComponentIn (morOnB G U) φ

section
variable {ObjY MorY ObjX MorX : Type}
  [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {Y : EpGroupoid ObjY MorY} {X : EpGroupoid ObjX MorX}

/-- (0): `F⁻¹(U)` is the disjoint union of the connected open `Uy y ∋ y`, `y ∈ F⁻¹(x)`, with
`F : Uy y → U` sc-diffeomorphisms. -/
def Cond0 (F : EpFunctor Y X) (x : ObjX) (U : Set ObjX) (Uy : ObjY → Set ObjY) : Prop :=
  (∀ y ∈ F.obj ⁻¹' {x}, IsOpen (Uy y) ∧ IsConnected (Uy y) ∧ y ∈ Uy y ∧
    ∃ σ : ObjX → ObjY, Y.PObj.IsScDiffeoOn X.PObj F.obj σ (Uy y) U) ∧
  (F.obj ⁻¹' {x}).PairwiseDisjoint Uy ∧
  F.obj ⁻¹' U = ⋃ y ∈ F.obj ⁻¹' {x}, Uy y

/-- (1): `Γ(G_x × U) = 𝐔(x) = ⨆_g 𝐔(g)`, `s, t : 𝐔(g) → U` sc-diffeomorphisms. -/
def Cond1 (X : EpGroupoid ObjX MorX) (x : ObjX) (U : Set ObjX)
    (Γ : X.Isotropy x → ObjX → MorX) : Prop :=
  (fun p : X.Isotropy x × ObjX => Γ p.1 p.2) '' (Set.univ ×ˢ U) = morOnB X.toGroupoidStr U ∧
  morOnB X.toGroupoidStr U = ⋃ g : X.Isotropy x, compB X.toGroupoidStr U g.val ∧
  Pairwise (fun g h : X.Isotropy x =>
    Disjoint (compB X.toGroupoidStr U g.val) (compB X.toGroupoidStr U h.val)) ∧
  ∀ g : X.Isotropy x,
    (∃ σ : ObjX → MorX, X.PMor.IsScDiffeoOn X.PObj X.src σ (compB X.toGroupoidStr U g.val) U) ∧
    (∃ τ : ObjX → MorX, X.PMor.IsScDiffeoOn X.PObj X.tgt τ (compB X.toGroupoidStr U g.val) U)

/-- (2): `𝐔(y, y') = ⨆_{ψ₀ : y → y'} 𝐔(ψ₀)`, the `𝐔(ψ₀) ∋ ψ₀` connected and open. -/
def Cond2 (F : EpFunctor Y X) (x : ObjX) (Uy : ObjY → Set ObjY) (UY : MorY → Set MorY) : Prop :=
  ∀ y ∈ F.obj ⁻¹' {x}, ∀ y' ∈ F.obj ⁻¹' {x},
    {ψ : MorY | Y.src ψ ∈ Uy y ∧ Y.tgt ψ ∈ Uy y'} = ⋃ ψ₀ ∈ morB Y.toGroupoidStr y y', UY ψ₀ ∧
    (morB Y.toGroupoidStr y y').PairwiseDisjoint UY ∧
    ∀ ψ₀ ∈ morB Y.toGroupoidStr y y', IsOpen (UY ψ₀) ∧ IsConnected (UY ψ₀) ∧ ψ₀ ∈ UY ψ₀

/-- (3)–(5) for the morphisms `ψ₀` between points of `F⁻¹(x)`. -/
def Cond345 (F : EpFunctor Y X) (x : ObjX) (U : Set ObjX) (Uy : ObjY → Set ObjY)
    (UY : MorY → Set MorY) : Prop :=
  ∀ ψ₀ ∈ morOnB Y.toGroupoidStr (F.obj ⁻¹' {x}),
    -- (3) `s : 𝐔(ψ₀) → U(y)`, `t : 𝐔(ψ₀) → U(y')`
    (∃ σ : ObjY → MorY, Y.PMor.IsScDiffeoOn Y.PObj Y.src σ (UY ψ₀) (Uy (Y.src ψ₀))) ∧
    (∃ τ : ObjY → MorY, Y.PMor.IsScDiffeoOn Y.PObj Y.tgt τ (UY ψ₀) (Uy (Y.tgt ψ₀))) ∧
    -- (4) `F : 𝐔(ψ₀) → 𝐔(F(ψ₀))`
    (∃ σ : MorX → MorY,
      Y.PMor.IsScDiffeoOn X.PMor F.mor σ (UY ψ₀) (compB X.toGroupoidStr U (F.mor ψ₀))) ∧
    -- (5) the right and bottom arrows are sc-diffeomorphisms
    (∃ τ : ObjX → MorX,
      X.PMor.IsScDiffeoOn X.PObj X.tgt τ (compB X.toGroupoidStr U (F.mor ψ₀)) U) ∧
    (∃ σ : ObjX → ObjY, Y.PObj.IsScDiffeoOn X.PObj F.obj σ (Uy (Y.src ψ₀)) U) ∧
    -- (5) the square commutes, literally `t ∘ F = F ∘ s` on `𝐔(ψ₀)`
    (∀ ψ ∈ UY ψ₀, X.tgt (F.mor ψ) = F.obj (Y.src ψ))

end

/-- Theorem 8.5.3: for a proper covering functor `F` and `x ∈ X` there is an open `V ∋ x` such
that for every connected `U(x) ⊆ V` with the natural `G_x`-action `(Φ, Γ)`, (1) holds and there
are `U(y)`, `𝐔(ψ₀)` with (0), (2)–(5). -/
def B : Prop :=
  ∀ (ObjY MorY ObjX MorX : Type)
    [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
    [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
    [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
    [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
    (Y : EpGroupoid ObjY MorY) (X : EpGroupoid ObjX MorX) (F : EpFunctor Y X),
    F.IsProperCovering → ∀ x : ObjX,
      ∃ V : Set ObjX, IsOpen V ∧ x ∈ V ∧
        ∀ (U : Set ObjX) (Φ : X.Isotropy x → ObjX → ObjX) (Γ : X.Isotropy x → ObjX → MorX),
          IsNatAction X x U Φ Γ → IsConnected U → U ⊆ V →
            Cond1 X x U Γ ∧
            ∃ (Uy : ObjY → Set ObjY) (UY : MorY → Set MorY),
              Cond0 F x U Uy ∧ Cond2 F x Uy UY ∧ Cond345 F x U Uy UY

end RoundTrip.V8_30
