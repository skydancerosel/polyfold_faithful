import Polyfold
/-! Blind formalization of V7_66 (the 2017 book's Part II, §7.5.2, Lemma 7.10, p. 255).

Text: let `X` be an ep-groupoid with paracompact `|X|` whose object M-polyfold admits sc-smooth
partitions of unity; let `x ∈ X` and `U(x)`, `V(x)` open neighbourhoods of `x` with
`U(x) ⊆ cl_X(U(x)) ⊆ V(x)`, `V(x)` admitting the natural `G_x`-action and `U(x)` invariant.  If
`β : X → [0, 1]` is continuous with support in `U(x)` and invariant under the `G_x`-action on
`V(x)`, there is an sc-smooth `f : X → [0, ∞)` with support in `V(x)`, invariant under the
`G_x`-action on `V(x)`, with `β ≤ f` on `X`.

Choices:
- Setting: `Obj Mor : Type` (universe 0, as in the other blind files), with the instances of the
  project's `EpGroupoid`, `X : EpGroupoid Obj Mor` (the project's Definition 7.3, fields read
  with `#print`, as in `RoundTrip/Blind/V7_49.lean`); `G_x` is the project's `X.Isotropy x`.
- "`|X|` paracompact": Mathlib's `ParacompactSpace X.OrbitSpace` (quotient topology).
  "admits sc-smooth partitions of unity": the project's `X.PObj.AdmitsScPartitionsOfUnity`
  (Definition 5.28, `#print`; item V5_47).  Both are hypotheses of the text, kept although the
  proof I see needs only the second.
- "`V(x)` admits the natural `G_x`-action": the data `(Φ, Γ)` of Theorem 7.1 on `V(x)`
  (`IsNatActionB`, the clauses of `RoundTrip/Blind/V7_62.lean` / `NatRepB` of V7_35).  The
  action is taken as GIVEN data, universally quantified ("the `G_x`-action on `V(x)`" refers to
  it); I do not use the project's `NaturalRep` (it requires `V(x)` connected).
- "`U(x)` invariant": `Φ(g)(U(x)) ⊆ U(x)` for all `g` (equality follows, `Φ` being a group
  action on `V(x) ⊇ U(x)`).  "`β` / `f` invariant under the action on `V(x)`":
  `β(Φ(g)(y)) = β(y)` for `y ∈ V(x)`, all `g`.
- "support in `A`": `tsupport ⊆ A` (closure in `X` of `{≠ 0}`).  `β : X → [0, 1]` is a real
  function with values in `[0, 1]`, continuous; `f : X → [0, ∞)` a real function `≥ 0`,
  sc-smooth (`X.PObj.IsScSmoothMap realPolyfold`, as in V5_47).
- "open neighbourhoods of `x`": open with `x ∈`; `U(x) ⊆ cl U(x)` is trivial and kept.
- Nothing looks false to me.
-/
namespace RoundTrip.V7_66
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- **The natural `G_x`-action on `U`** (Theorem 7.1): `U` open, `x ∈ U`, `Φ : G_x → Diff_sc(U)`
a homomorphism, `Γ : G_x × U → 𝐗` sc-smooth with `Γ(g, x) = g`, `s Γ(g, y) = y`,
`t Γ(g, y) = Φ(g)(y)`, and `Γ(·, s h) ↦ h` unique for morphisms `h` between points of `U`. -/
def IsNatActionB (X : EpGroupoid Obj Mor) (x : Obj) (U : Set Obj)
    (Φ : X.Isotropy x → Obj → Obj) (Γ : X.Isotropy x → Obj → Mor) : Prop :=
  IsOpen U ∧ x ∈ U ∧
  (∀ g, ∃ ψ : Obj → Obj, X.PObj.IsScDiffeoOn X.PObj (Φ g) ψ U U) ∧
  (∀ g h, ∀ y ∈ U, Φ (g * h) y = Φ g (Φ h y)) ∧
  (∀ g, X.PObj.IsScSmoothOn X.PMor (Γ g) U) ∧
  (∀ g, Γ g x = g.val) ∧
  (∀ g, ∀ y ∈ U, X.src (Γ g y) = y ∧ X.tgt (Γ g y) = Φ g y) ∧
  (∀ h : Mor, X.src h ∈ U → X.tgt h ∈ U → ∃! g, Γ g (X.src h) = h)

end

/-- Lemma 7.10: an invariant continuous `β ≤ 1` supported in `U(x)` has an invariant sc-smooth
majorant supported in `V(x)`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    ParacompactSpace X.OrbitSpace → X.PObj.AdmitsScPartitionsOfUnity →
    ∀ (x : Obj) (U V : Set Obj), IsOpen U → x ∈ U → IsOpen V → x ∈ V →
      U ⊆ closure U → closure U ⊆ V →
      ∀ (Φ : X.Isotropy x → Obj → Obj) (Γ : X.Isotropy x → Obj → Mor),
        IsNatActionB X x V Φ Γ → (∀ g, Set.MapsTo (Φ g) U U) →
        ∀ β : Obj → ℝ, Continuous β → (∀ y, β y ∈ Set.Icc (0 : ℝ) 1) → tsupport β ⊆ U →
          (∀ g, ∀ y ∈ V, β (Φ g y) = β y) →
          ∃ f : Obj → ℝ, X.PObj.IsScSmoothMap realPolyfold f ∧ (∀ y, 0 ≤ f y) ∧
            tsupport f ⊆ V ∧ (∀ g, ∀ y ∈ V, f (Φ g y) = f y) ∧ ∀ y, β y ≤ f y

end RoundTrip.V7_66
