import Polyfold
/-! Blind formalization of V7_27 (the 2017 book, arXiv 1707.08941, Part II, §7.1,
Proposition 7.6, p. 236: `|U(x)|` and `G_x\U(x)`).

Text: for `x ∈ X` and an open neighbourhood `U(x)` with the natural `G_x`-action `Φ`
(`g ∗ y = Φ(g)(y)`), `τ : G_x\U(x) → |U(x)| = π(U(x))`, `G_x ∗ y ↦ |y|`, is a homeomorphism; in
other words the obvious functor `G_x ⋉ U(x) → X` (inclusion on objects, `(g, y) ↦ Γ(g, y)`) is
fully faithful and induces a homeomorphism `|U(x)|_{G_x ⋉ U(x)} = G_x\U(x) → |U(x)| = π(U(x))`.

Choices:
- Setting as in my `RoundTrip/Blind/V7_21.lean`: `Obj Mor : Type` (universe 0), the project's
  `X : EpGroupoid Obj Mor`, `G_x = X.Isotropy x` (`g * h = g ∘ h`, checked by `rfl`), and "an
  open neighbourhood `U(x)` with the natural `G_x`-action" my `IsNatAction X x U Φ Γ`
  (Theorem 7.1's data; `U` open, not required connected — the project's `NaturalRep` requires
  connected `U`, so I did not use it).  "`z ∈ |X|`, `x` with `z = |x|`" only names `x`: B is for
  every `x`.
- `|X|`: the project's `X.OrbitSpace` (quotient by "there is a morphism", `#print`ed) with the
  quotient topology (Mathlib's instance, `#synth`ed); `π = X.π`; `|U(x)| = π(U(x))` carries the
  subspace topology of `|X|`.
- `G_x\U(x)`: the quotient of the subspace `U` by `y ∼ g ∗ y` (`Quot` of `orbRel`, which needs no
  proof that it is an equivalence), with Mathlib's quotient topology.  The orbit space
  `|U(x)|_{G_x ⋉ U(x)}` of the translation groupoid (morphisms `(g, y) : y → g ∗ y`) is the
  quotient by the same relation, so it is the same space; the text's identification is then
  definitional and the two homeomorphism claims coincide.
- "`τ` is a homeomorphism": there is a homeomorphism `G_x\U(x) ≃ₜ π(U(x))` sending the class of
  `y` to `|y|` (i.e. `τ` is well defined and a homeomorphism).
- "The obvious functor is fully faithful": as in my V7_22 — `(g, y) ↦ Γ(g, y)` respects
  composition `(g, Φ(h)z) ∘ (h, z) = (gh, z)` and units, and is a bijection
  `{g | Φ(g)(y) = z} → mor_X(y, z)` for `y, z ∈ U`.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V7_27
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

/-- `y ∼ g ∗ y` on `U`: the `G_x`-orbits, and the isomorphism relation of `G_x ⋉ U`. -/
def orbRel (X : EpGroupoid Obj Mor) (x : Obj) (U : Set Obj) (Φ : X.Isotropy x → Obj → Obj) :
    U → U → Prop :=
  fun y y' => ∃ g : X.Isotropy x, Φ g y = y'

end

/-- Proposition 7.6: `τ : G_x\U(x) → π(U(x))`, `G_x ∗ y ↦ |y|`, is a homeomorphism, and the
functor `G_x ⋉ U(x) → X`, `y ↦ y`, `(g, y) ↦ Γ(g, y)`, is fully faithful (and induces `τ` on
orbit spaces). -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (x : Obj) (U : Set Obj) (Φ : X.Isotropy x → Obj → Obj)
    (Γ : X.Isotropy x → Obj → Mor), IsNatAction X x U Φ Γ →
    -- `τ` is a homeomorphism `G_x\U(x) = |U(x)|_{G_x ⋉ U(x)} → π(U(x))`
    (∃ τ : Quot (orbRel X x U Φ) ≃ₜ ↥(X.π '' U),
      ∀ y : U, (τ (Quot.mk _ y) : X.OrbitSpace) = X.π y) ∧
    -- the obvious functor: composition and units
    (∀ (g h : X.Isotropy x), ∀ z ∈ U, Γ (g * h) z = X.comp (Γ g (Φ h z)) (Γ h z)) ∧
    (∀ y ∈ U, Γ 1 y = X.unit y) ∧
    -- fully faithful
    (∀ y ∈ U, ∀ z ∈ U, Set.BijOn (fun g => Γ g y) {g | Φ g y = z} (X.mor y z))

end RoundTrip.V7_27
