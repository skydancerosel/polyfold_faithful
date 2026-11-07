import Polyfold
/-! Blind formalization of V7_25 (the 2017 book, arXiv 1707.08941, Part II, §7.1,
Proposition 7.5, pp. 233–234: natural representations of finitely many isomorphic objects).

Text: for a finite set `Y` of distinct, mutually isomorphic objects, with full subcategory
`(Y, 𝐘)`, and a neighbourhood `V` of `Y`, there is a functor `f` giving mutually disjoint
connected open neighbourhoods `U(y) ⊆ V` and, for `ψ : y → y'` in `𝐘`, sc-diffeomorphisms
`f(ψ) : U(y) → U(y')`; `𝐔 = {φ | s φ, t φ ∈ ⋃ U(y)}` decomposes into the connected components
`𝐔(ψ)`, `ψ ∈ 𝐘`, and (1) `G_y` acts on `U(y)` via the natural action; (2) `s`, `t` on `𝐔(ψ)` are
sc-diffeomorphisms; (3) `f(ψ)(z) = t ∘ (s|𝐔(ψ))⁻¹(z)` for `ψ : y → y'`, `z ∈ U(y)`.

Choices:
- Setting as in my `RoundTrip/Blind/V7_21.lean`: `Obj Mor : Type` (universe 0), the project's
  `X : EpGroupoid Obj Mor`, `G_y = X.Isotropy y` (`g * h = g ∘ h`, checked by `rfl`).  "The
  natural action" of `G_y` on `U(y)`: my `IsNatAction` (Theorem 7.1's data; `U` open, not
  required connected — here `U(y)` is connected anyway).
- `Y`: a `Finset Obj` (distinct elements); "mutually isomorphic": a morphism `y → y'` for all
  `y, y' ∈ Y` (written out; = project's `Isomorphic`).  `𝐘 = {φ | s φ, t φ ∈ Y}` (project's
  `X.morOn`, `#print`ed).  "A neighbourhood `V` of `Y`": `V ∈ nhdsSet Y` (not necessarily open;
  equivalent to the open case since the `U(y)` are open).
- The functor `f`: data `U : Obj → Set Obj` (used on `Y`) and `F : Mor → Obj → Obj` (`F ψ = f(ψ)`,
  used on `U(s ψ)`).  "Functor": `f(φ ∘ ψ) = f(φ) ∘ f(ψ)` on `U(s ψ)` for composable
  `φ, ψ ∈ 𝐘`, and `f(1_y) = id` on `U(y)`.  "sc-diffeomorphism `U(y) → U(y')`": project's
  `IsScDiffeoOn` (`#print`ed) with some inverse.
- "Decomposes into the union of connected components `𝐔(ψ)`, `ψ ∈ 𝐘`": `𝐔(ψ)` is read as the
  connected component of `ψ` in `𝐔` (`connectedComponentIn 𝐔 ψ`); B asserts `𝐔 = ⋃_{ψ ∈ 𝐘} 𝐔(ψ)`
  and that distinct `ψ` give disjoint (= distinct) components, so the components of `𝐔` are
  indexed by `𝐘`.
- (1): for every `y ∈ Y`, `g ↦ f(g)|U(y)` (`g ∈ G_y ⊆ 𝐘`) is the `Φ` of a natural action of `G_y`
  on `U(y)` (with some `Γ`).
- (2): DOUBT.  The md says "`s : 𝐔(ψ) → U(y)` and `t : 𝐔(ψ) → U(y)`" with `y` unbound in (2).
  For `ψ : y → y'` (the convention of (3)) the literal `t : 𝐔(ψ) → U(y)` is false when `y ≠ y'`
  (`t ψ = y' ∈ U(y')`, disjoint from `U(y)`), and (3) puts `t ∘ (s|𝐔(ψ))⁻¹` into `U(y')`.  I read
  it as the misprint/slip it seems to be: `s : 𝐔(ψ) → U(s ψ)`, `t : 𝐔(ψ) → U(t ψ)`, each an
  sc-diffeomorphism (some inverse).
- (3): with (2), `(s|𝐔(ψ))⁻¹(z)` is the unique `φ ∈ 𝐔(ψ)` with `s φ = z`; I state (3) as
  `f(ψ)(s φ) = t φ` for all `φ ∈ 𝐔(ψ)` (equivalent given (2)).
-/
namespace RoundTrip.V7_25
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
`V`): the natural representation of `𝐘` (Definition 7.8). -/
def IsNatRepFinB (X : EpGroupoid Obj Mor) (Y : Finset Obj) (V : Set Obj) (U : Obj → Set Obj)
    (F : Mor → Obj → Obj) : Prop :=
  -- mutually disjoint connected open neighbourhoods `U(y) ⊆ V`
  (∀ y ∈ Y, IsOpen (U y) ∧ IsConnected (U y) ∧ y ∈ U y ∧ U y ⊆ V) ∧
  (↑Y : Set Obj).PairwiseDisjoint U ∧
  -- `f(ψ) : U(y) → U(y')` is an sc-diffeomorphism
  (∀ ψ ∈ X.morOn ↑Y, ∃ G : Obj → Obj,
    X.PObj.IsScDiffeoOn X.PObj (F ψ) G (U (X.src ψ)) (U (X.tgt ψ))) ∧
  -- `f` is a functor
  (∀ φ ∈ X.morOn ↑Y, ∀ ψ ∈ X.morOn ↑Y, X.src φ = X.tgt ψ →
    ∀ z ∈ U (X.src ψ), F (X.comp φ ψ) z = F φ (F ψ z)) ∧
  (∀ y ∈ Y, ∀ z ∈ U y, F (X.unit y) z = z) ∧
  -- `𝐔` is the union of its connected components `𝐔(ψ)`, `ψ ∈ 𝐘`, distinct for distinct `ψ`
  bigU X Y U = (⋃ ψ ∈ X.morOn ↑Y, connectedComponentIn (bigU X Y U) ψ) ∧
  (X.morOn ↑Y).PairwiseDisjoint (fun ψ => connectedComponentIn (bigU X Y U) ψ) ∧
  -- (1) `G_y` acts on `U(y)` via the natural action
  (∀ y ∈ Y, ∃ Γ : X.Isotropy y → Obj → Mor, IsNatAction X y (U y) (fun g => F g.val) Γ) ∧
  -- (2) `s : 𝐔(ψ) → U(y)`, `t : 𝐔(ψ) → U(y')` are sc-diffeomorphisms
  (∀ ψ ∈ X.morOn ↑Y,
    (∃ σ : Obj → Mor, X.PMor.IsScDiffeoOn X.PObj X.src σ
      (connectedComponentIn (bigU X Y U) ψ) (U (X.src ψ))) ∧
    (∃ τ : Obj → Mor, X.PMor.IsScDiffeoOn X.PObj X.tgt τ
      (connectedComponentIn (bigU X Y U) ψ) (U (X.tgt ψ)))) ∧
  -- (3) `f(ψ) = t ∘ (s|𝐔(ψ))⁻¹`
  (∀ ψ ∈ X.morOn ↑Y, ∀ φ ∈ connectedComponentIn (bigU X Y U) ψ, F ψ (X.src φ) = X.tgt φ)

end

/-- Proposition 7.5: a finite set of mutually isomorphic objects has, on neighbourhoods inside
any given neighbourhood `V`, a natural representation `f` with properties (1)–(3). -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Y : Finset Obj),
    (∀ y ∈ Y, ∀ y' ∈ Y, ∃ φ : Mor, X.src φ = y ∧ X.tgt φ = y') →
    ∀ V : Set Obj, V ∈ nhdsSet (↑Y : Set Obj) →
      ∃ (U : Obj → Set Obj) (F : Mor → Obj → Obj), IsNatRepFinB X Y V U F

end RoundTrip.V7_25
