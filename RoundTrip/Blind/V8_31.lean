import Polyfold
/-! Blind formalization of V8_31 (the 2017 book, arXiv 1707.08941, Part II, §8.4, Remark 8.2,
pp. 277–278; 2021: Remark 8.5.4, pp. 386–387).

Text: (a) as `F` is a functor, for a morphism `φ : y → y'` of `𝐘` between `y, y' ∈ F⁻¹(x)`,
`F(φ) : F(y) → F(y')` belongs to the isotropy group `G_x`.  (b) In Theorem 8.5.3 everything is
determined by the choice of a small connected open neighborhood `U(x)` of `x` admitting the
natural `G_x`-action; the construction of the data `(Φ, Γ)` of Theorem 7.1.13 is natural, and the
main point of the proof is the interplay between `F` restricted to suitable subsets and its
compatibility with the source and target maps.

Choices:
- Setting as in my `RoundTrip/Blind/V8_30.lean` (spaces in `Type`, Hausdorff paracompact, the
  project's `EpGroupoid`, `EpFunctor`, `EpFunctor.IsProperCovering`, `IsScDiffeoOn`), with the
  same `IsNatAction` (from `RoundTrip/Blind/V7_21.lean`) and the same conditions (0), (2) of
  Theorem 8.5.3 (`Cond0`, `Cond2`, copied from V8_30).  The context is that of Theorem 8.5.3: `F`
  a proper covering functor.
- (a): `F(φ) ∈ G_x` means `s(F φ) = x` and `t(F φ) = x`.
- (b), "everything is determined by the choice of `U(x)`", read as uniqueness: for a connected
  `U(x)` with natural-action data, (i) the data `(Φ, Γ)` on `U(x)` are unique (any two agree on
  `G_x × U(x)`), and (ii) any two families `U(y)`, `𝐔(ψ₀)` satisfying (0) and (2) of Theorem 8.5.3
  agree at every `y ∈ F⁻¹(x)` and every morphism `ψ₀` between points of `F⁻¹(x)` (the `𝐔(g)` of
  (1) are by definition the components of `𝐔(x)`, so they are determined already).  I state this
  for every such `U(x)`, without the smallness restriction (smallness is only needed for
  existence).
- Not formalized: "the construction of `(Φ, Γ)` is natural" beyond (i), and the comment on the
  main point of the proof.
- Nothing looks false to me.
-/
namespace RoundTrip.V8_31
open Polyfold

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

/-- `mor(y, y')`. -/
def morB {Obj Mor : Type} (G : GroupoidStr Obj Mor) (y y' : Obj) : Set Mor :=
  {φ | G.src φ = y ∧ G.tgt φ = y'}

section
variable {ObjY MorY ObjX MorX : Type}
  [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {Y : EpGroupoid ObjY MorY} {X : EpGroupoid ObjX MorX}

/-- Theorem 8.5.3 (0) (as in V8_30). -/
def Cond0 (F : EpFunctor Y X) (x : ObjX) (U : Set ObjX) (Uy : ObjY → Set ObjY) : Prop :=
  (∀ y ∈ F.obj ⁻¹' {x}, IsOpen (Uy y) ∧ IsConnected (Uy y) ∧ y ∈ Uy y ∧
    ∃ σ : ObjX → ObjY, Y.PObj.IsScDiffeoOn X.PObj F.obj σ (Uy y) U) ∧
  (F.obj ⁻¹' {x}).PairwiseDisjoint Uy ∧
  F.obj ⁻¹' U = ⋃ y ∈ F.obj ⁻¹' {x}, Uy y

/-- Theorem 8.5.3 (2) (as in V8_30). -/
def Cond2 (F : EpFunctor Y X) (x : ObjX) (Uy : ObjY → Set ObjY) (UY : MorY → Set MorY) : Prop :=
  ∀ y ∈ F.obj ⁻¹' {x}, ∀ y' ∈ F.obj ⁻¹' {x},
    {ψ : MorY | Y.src ψ ∈ Uy y ∧ Y.tgt ψ ∈ Uy y'} = ⋃ ψ₀ ∈ morB Y.toGroupoidStr y y', UY ψ₀ ∧
    (morB Y.toGroupoidStr y y').PairwiseDisjoint UY ∧
    ∀ ψ₀ ∈ morB Y.toGroupoidStr y y', IsOpen (UY ψ₀) ∧ IsConnected (UY ψ₀) ∧ ψ₀ ∈ UY ψ₀

end

/-- Remark 8.5.4: (a) `F` maps the morphisms between points of `F⁻¹(x)` into `G_x`; (b) for a
connected `U(x)` with the natural action, the data `(Φ, Γ)` and the `U(y)`, `𝐔(ψ₀)` of
Theorem 8.5.3 are uniquely determined by `U(x)`. -/
def B : Prop :=
  ∀ (ObjY MorY ObjX MorX : Type)
    [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
    [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
    [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
    [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
    (Y : EpGroupoid ObjY MorY) (X : EpGroupoid ObjX MorX) (F : EpFunctor Y X),
    F.IsProperCovering → ∀ x : ObjX,
      -- (a)
      (∀ φ : MorY, F.obj (Y.src φ) = x → F.obj (Y.tgt φ) = x →
        X.src (F.mor φ) = x ∧ X.tgt (F.mor φ) = x) ∧
      -- (b) (i): `(Φ, Γ)` is determined by `U(x)`
      (∀ (U : Set ObjX) (Φ Φ' : X.Isotropy x → ObjX → ObjX) (Γ Γ' : X.Isotropy x → ObjX → MorX),
        IsNatAction X x U Φ Γ → IsNatAction X x U Φ' Γ' → IsConnected U →
          ∀ g : X.Isotropy x, ∀ y ∈ U, Φ g y = Φ' g y ∧ Γ g y = Γ' g y) ∧
      -- (b) (ii): the `U(y)` and `𝐔(ψ₀)` are determined by `U(x)`
      (∀ (U : Set ObjX) (Φ : X.Isotropy x → ObjX → ObjX) (Γ : X.Isotropy x → ObjX → MorX),
        IsNatAction X x U Φ Γ → IsConnected U →
        ∀ (Uy Uy' : ObjY → Set ObjY) (UY UY' : MorY → Set MorY),
          Cond0 F x U Uy → Cond2 F x Uy UY → Cond0 F x U Uy' → Cond2 F x Uy' UY' →
          (∀ y ∈ F.obj ⁻¹' {x}, Uy y = Uy' y) ∧
          (∀ ψ₀ ∈ morOnB Y.toGroupoidStr (F.obj ⁻¹' {x}), UY ψ₀ = UY' ψ₀))

end RoundTrip.V8_31
