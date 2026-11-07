import Polyfold
/-! Blind formalization of V7_26 (the 2017 book, arXiv 1707.08941, Part II, §7.1,
Definition 7.8, p. 236: the natural representation of `𝐘`).

Text: for an ep-groupoid `X` and the full subcategory `𝐘` of a finite set of isomorphic objects,
a functor `f` as constructed in Proposition 7.5 with its stated properties is called the natural
representation of `𝐘` on neighbourhoods contained in `V` (or on a small neighbourhood of `𝐘`).

Choices:
- This item is a definition.  B says that the project's notion, `X.NaturalRepFinite Y V` (a
  structure carrying data `U`, `F`, `sheet`, `srcInv`; fields read with `#print`), is the text's:
  a pair `(U, F)` (neighbourhoods `U(y)`, maps `F ψ = f(ψ)`) has the properties of
  Proposition 7.5 (my `IsNatRepFinB`, copied from `RoundTrip/Blind/V7_25.lean`, where all
  readings are recorded) iff it is the `(U, F)` of some `N : X.NaturalRepFinite Y V`, agreeing on
  `Y` and on the relevant domains (`N.F ψ = F ψ` on `U(s ψ)` for `ψ ∈ 𝐘`; values elsewhere are
  junk on both sides).
- Setting as in V7_25: `Obj Mor : Type` (universe 0), the project's `X : EpGroupoid Obj Mor`,
  `Y : Finset Obj` mutually isomorphic, `V ∈ nhdsSet Y` (the context of Proposition 7.5; the
  definition itself does not use these hypotheses).  "On a small neighbourhood of `𝐘`" is only an
  alternative name and adds nothing.
- Inherited doubt (V7_25): in property (2) I read the target of `t : 𝐔(ψ) → ·` as `U(y')` for
  `ψ : y → y'` (the md's `U(y)` looks like a misprint).
-/
namespace RoundTrip.V7_26
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- The natural `G_x`-action on the open neighbourhood `U` of `x` (the data `Φ`, `Γ` of
Theorem 7.1 with its properties (1)–(3)), as in `RoundTrip/Blind/V7_21.lean`. -/
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

/-- `𝐔 = {φ ∈ 𝐗 | s φ, t φ ∈ ⋃_{y ∈ Y} U(y)}`. -/
def bigU (X : EpGroupoid Obj Mor) (Y : Finset Obj) (U : Obj → Set Obj) : Set Mor :=
  X.morOn (⋃ y ∈ Y, U y)

/-- `(U, F)` is a functor `f` with the properties stated in Proposition 7.5 (neighbourhoods in
`V`), as in `RoundTrip/Blind/V7_25.lean`. -/
def IsNatRepFinB (X : EpGroupoid Obj Mor) (Y : Finset Obj) (V : Set Obj) (U : Obj → Set Obj)
    (F : Mor → Obj → Obj) : Prop :=
  (∀ y ∈ Y, IsOpen (U y) ∧ IsConnected (U y) ∧ y ∈ U y ∧ U y ⊆ V) ∧
  (↑Y : Set Obj).PairwiseDisjoint U ∧
  (∀ ψ ∈ X.morOn ↑Y, ∃ G : Obj → Obj,
    X.PObj.IsScDiffeoOn X.PObj (F ψ) G (U (X.src ψ)) (U (X.tgt ψ))) ∧
  (∀ φ ∈ X.morOn ↑Y, ∀ ψ ∈ X.morOn ↑Y, X.src φ = X.tgt ψ →
    ∀ z ∈ U (X.src ψ), F (X.comp φ ψ) z = F φ (F ψ z)) ∧
  (∀ y ∈ Y, ∀ z ∈ U y, F (X.unit y) z = z) ∧
  bigU X Y U = (⋃ ψ ∈ X.morOn ↑Y, connectedComponentIn (bigU X Y U) ψ) ∧
  (X.morOn ↑Y).PairwiseDisjoint (fun ψ => connectedComponentIn (bigU X Y U) ψ) ∧
  (∀ y ∈ Y, ∃ Γ : X.Isotropy y → Obj → Mor, IsNatAction X y (U y) (fun g => F g.val) Γ) ∧
  (∀ ψ ∈ X.morOn ↑Y,
    (∃ σ : Obj → Mor, X.PMor.IsScDiffeoOn X.PObj X.src σ
      (connectedComponentIn (bigU X Y U) ψ) (U (X.src ψ))) ∧
    (∃ τ : Obj → Mor, X.PMor.IsScDiffeoOn X.PObj X.tgt τ
      (connectedComponentIn (bigU X Y U) ψ) (U (X.tgt ψ)))) ∧
  (∀ ψ ∈ X.morOn ↑Y, ∀ φ ∈ connectedComponentIn (bigU X Y U) ψ, F ψ (X.src φ) = X.tgt φ)

end

/-- Definition 7.8: the project's natural representations of `𝐘` on neighbourhoods in `V` are
exactly the functors with the properties of Proposition 7.5. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Y : Finset Obj),
    (∀ y ∈ Y, ∀ y' ∈ Y, ∃ φ : Mor, X.src φ = y ∧ X.tgt φ = y') →
    ∀ V : Set Obj, V ∈ nhdsSet (↑Y : Set Obj) →
    ∀ (U : Obj → Set Obj) (F : Mor → Obj → Obj),
      IsNatRepFinB X Y V U F ↔
        ∃ N : X.NaturalRepFinite Y V, (∀ y ∈ Y, N.U y = U y) ∧
          ∀ ψ ∈ X.morOn ↑Y, ∀ z ∈ U (X.src ψ), N.F ψ z = F ψ z

end RoundTrip.V7_26
