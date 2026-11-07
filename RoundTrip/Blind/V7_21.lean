import Polyfold
/-! Blind formalization of V7_21 (the 2017 book, arXiv 1707.08941, Part II, §7.1, pp. 231–232:
the translation groupoid `G_x ⋉ U(x)` is an ep-groupoid).

Text: for `x` and `U = U(x)` with the natural `G = G_x`-action, `G ⋉ U = (U, G × U)` with
`s(g, y) = y`, `t(g, y) = Φ(g)(y)`, `(g, y) ∘ (h, z) = (g ∘ h, z)` (for `y = Φ(h)(z)`) is an
ep-groupoid.

Choices:
- Setting: `Obj Mor : Type` (universe 0, as in the other blind files; the project's
  `EpGroupoid` has `Obj`, `Mor` in one universe) with the Hausdorff/paracompact instances the
  project's `EpGroupoid` asks for; `X : EpGroupoid Obj Mor` is the project's ep-groupoid
  (Definition 7.3, fields read with `#print`).  `G_x` is the project's `X.Isotropy x` (morphisms
  `x → x`); I checked by `rfl` that its product is `(g * h).val = X.comp g.val h.val` (`g ∘ h`),
  `1 = 1_x`, `g⁻¹ = ι(g)`.
- "`U(x)` with the natural `G_x`-action" (the data of Theorem 7.1, which the md does not quote):
  my `IsNatAction X x U Φ Γ` — `U` open, `x ∈ U`, every `Φ(g)` an sc-diffeomorphism of `U`
  (project's `IsScDiffeoOn`, `#print`ed: sc-smooth on `U` with an sc-smooth inverse on `U`),
  `Φ(g ∘ h) = Φ(g) ∘ Φ(h)` on `U`, `Γ : G_x × U → 𝐗` sc-smooth (read as: every `Γ(g, ·)`
  sc-smooth on `U`, `G_x` being discrete), (1) `Γ(g, x) = g`, (2) `s Γ(g, y) = y`,
  `t Γ(g, y) = Φ(g)(y)`, (3) every `h : y → z` with `y, z ∈ U` is `Γ(g, y)` for a unique `g`.
  I did NOT use the project's `NaturalRep`: its docstring and fields also demand `U` connected,
  which none of the quoted Chapter 7 statements attach to "the natural action" (V7_23 adds
  "connected" explicitly as a further choice).  `Φ`, `Γ` are total maps; only values on `U`
  matter.
- "is an ep-groupoid": there are paracompactness instances on `U` and `G × U` (part of
  "M-polyfold", as in the project; asserted, not assumed) and an `EpGroupoid` structure `E` on
  the objects `↥U` and morphisms `G_x × ↥U` with exactly the text's `s`, `t` and composition (on
  composable pairs; `1` and `ι` are then forced by the groupoid laws), whose object M-polyfold
  has the charts of the open subset `U ⊆ X` (project's `restrictOpen`) and whose morphism
  M-polyfold has the charts of the product of the discrete `G_x` (project's `discretePolyfold`,
  topology `⊥`) with `U` (project's `MPolyfold.prod`) — the text's implicit structures ("`#G`
  copies of `U`").  Equality of M-polyfold structures is read as equality of the sets of
  (maximal-atlas) charts, `IsChart`.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V7_21
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- The natural `G_x`-action on the open neighbourhood `U` of `x` (the data `Φ`, `Γ` of
Theorem 7.1 with its properties (1)–(3)). -/
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

/-- The translation groupoid `G_x ⋉ U(x)` (objects `U`, morphisms `G_x × U`, `s(g, y) = y`,
`t(g, y) = Φ(g)(y)`, `(g, y) ∘ (h, z) = (gh, z)`), with `U` open in `X` and `G_x × U` the product
of the discrete `G_x` with `U`, is an ep-groupoid. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (x : Obj) (U : Set Obj) (Φ : X.Isotropy x → Obj → Obj)
    (Γ : X.Isotropy x → Obj → Mor) (h : IsNatAction X x U Φ Γ),
    letI : TopologicalSpace (X.Isotropy x) := ⊥
    haveI : DiscreteTopology (X.Isotropy x) := ⟨rfl⟩
    haveI : Nonempty U := ⟨⟨x, h.mem⟩⟩
    ∃ (_ : ParacompactSpace U) (_ : ParacompactSpace (X.Isotropy x × U))
      (E : EpGroupoid U (X.Isotropy x × U)),
      (∀ p : X.Isotropy x × U, E.src p = p.2) ∧
      (∀ p : X.Isotropy x × U, (E.tgt p : Obj) = Φ p.1 p.2) ∧
      (∀ p q : X.Isotropy x × U, E.src p = E.tgt q → E.comp p q = (p.1 * q.1, q.2)) ∧
      (∀ φ : MChart U, E.PObj.IsChart φ ↔ (X.PObj.restrictOpen h.isOpen).IsChart φ) ∧
      (∀ φ : MChart (X.Isotropy x × U), E.PMor.IsChart φ ↔
        ((discretePolyfold (X.Isotropy x)).prod (X.PObj.restrictOpen h.isOpen)).IsChart φ)

end RoundTrip.V7_21
