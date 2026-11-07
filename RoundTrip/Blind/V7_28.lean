import Polyfold
/-! Blind formalization of V7_28 (the 2017 book, arXiv 1707.08941, Part II, §7.1,
Definition 7.9 and the two sentences after it, p. 237: local uniformizers).

Text: a local uniformizer around `x` is a fully faithful embedding `Ψ_x : G_x ⋉ U(x) → X`, `U(x)`
an open neighbourhood of `x` with the natural `G_x`-action, such that `Ψ_x` induces a
homeomorphism between `|U(x)|_{G_x ⋉ U(x)}` and the open neighbourhood `|U(x)| = π(U(x))` of
`π(x)` in `|X|`.  Every object has a local uniformizer (Proposition 7.6); a local uniformizer is
injective on objects and on morphisms.

Choices:
- Setting as in my `RoundTrip/Blind/V7_21.lean`: `Obj Mor : Type` (universe 0), the project's
  `X : EpGroupoid Obj Mor`, `G_x = X.Isotropy x` (`g * h = g ∘ h`, checked by `rfl`), "`U(x)`
  with the natural `G_x`-action" my `IsNatAction X x U Φ Γ` (Theorem 7.1's data; `U` open, NOT
  required connected).  `G_x ⋉ U(x)`: objects `U`, morphisms `(g, y) : y → Φ(g)(y)`,
  `(g, Φ(h)z) ∘ (h, z) = (gh, z)`, units `(1, y)` (p. 232 / V7_21).
- `Ψ_x`: maps `ΨO` on objects (used on `U`) and `ΨM` on morphisms (`ΨM g y = Ψ_x(g, y)`), a
  functor (`s`, `t`, composition, units).  No sc-smoothness is required (the md asks none).
  "Fully faithful": `g ↦ Ψ_x(g, y)` is a bijection `{g | Φ(g)y = z} → mor_X(Ψ y, Ψ z)` for
  `y, z ∈ U`.  "Embedding": read in the categorical sense, injective on objects (`InjOn ΨO U`);
  DOUBT: it might instead mean that `Ψ_x` is the inclusion `U ⊆ X` on objects — I do not
  assume that.
- "Induces a homeomorphism between `|U(x)|_{G⋉U}` and `π(U(x))`": `|U(x)|_{G⋉U}` is the quotient
  of the subspace `U` by `y ∼ Φ(g)(y)` (`Quot` of `orbRel`, quotient topology); there is a
  homeomorphism onto the subspace `π(U(x)) ⊆ |X|` (project's `X.OrbitSpace`, quotient topology)
  sending the class of `y` to `|Ψ_x(y)|`.
- B is the conjunction of: (D) the definition — my `IsLocalUniformizerB` holds for
  `(U, Φ, Γ, ΨO, ΨM)` iff these are the data of a project `X.LocalUniformizer x` (fields read with
  `#print`: a `NaturalRep` `rep` and a `GroupoidFunctor` `Ψ` on `rep.translationGroupoid`);
  (E) existence around every `x`; (I) injectivity on objects and on morphisms (on `G_x × U`);
  (O) the presupposition "`π(U(x))` is an open neighbourhood of `π(x)` in `|X|`", for every
  natural action.
- DOUBT for (D): from `#print` I know that the project's `NaturalRep` requires `U` connected and
  that `LocalUniformizer` requires `Ψ.obj y = y`; under my readings ("the natural action" without
  connectedness, "embedding" = injective on objects) the direction text ⇒ project of (D) then
  fails.  I keep (D) as the text's definition; the difference is exactly these two readings.
- Nothing in the statement itself looks false to me.
-/
namespace RoundTrip.V7_28
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

/-- `y ∼ g ∗ y` on `U`: the isomorphism relation of `G_x ⋉ U` (its orbit space is the quotient). -/
def orbRel (X : EpGroupoid Obj Mor) (x : Obj) (U : Set Obj) (Φ : X.Isotropy x → Obj → Obj) :
    U → U → Prop :=
  fun y y' => ∃ g : X.Isotropy x, Φ g y = y'

/-- `(ΨO, ΨM)` is a functor `G_x ⋉ U → X`. -/
def IsFunctorB (X : EpGroupoid Obj Mor) (x : Obj) (U : Set Obj) (Φ : X.Isotropy x → Obj → Obj)
    (ΨO : Obj → Obj) (ΨM : X.Isotropy x → Obj → Mor) : Prop :=
  (∀ g, ∀ y ∈ U, X.src (ΨM g y) = ΨO y ∧ X.tgt (ΨM g y) = ΨO (Φ g y)) ∧
  (∀ (g h : X.Isotropy x), ∀ z ∈ U, ΨM (g * h) z = X.comp (ΨM g (Φ h z)) (ΨM h z)) ∧
  (∀ y ∈ U, ΨM 1 y = X.unit (ΨO y))

/-- **Definition 7.9**: `(ΨO, ΨM)` is a local uniformizer around `x` on `U` with the natural
action `(Φ, Γ)`: a fully faithful embedding `G_x ⋉ U → X` inducing a homeomorphism
`|U|_{G_x ⋉ U} → π(U)`. -/
def IsLocalUniformizerB (X : EpGroupoid Obj Mor) (x : Obj) (U : Set Obj)
    (Φ : X.Isotropy x → Obj → Obj) (Γ : X.Isotropy x → Obj → Mor) (ΨO : Obj → Obj)
    (ΨM : X.Isotropy x → Obj → Mor) : Prop :=
  IsNatAction X x U Φ Γ ∧ IsFunctorB X x U Φ ΨO ΨM ∧
  -- fully faithful
  (∀ y ∈ U, ∀ z ∈ U, Set.BijOn (fun g => ΨM g y) {g | Φ g y = z} (X.mor (ΨO y) (ΨO z))) ∧
  -- an embedding: injective on objects
  Set.InjOn ΨO U ∧
  -- the induced map of orbit spaces is a homeomorphism onto `π(U)`
  ∃ τ : Quot (orbRel X x U Φ) ≃ₜ ↥(X.π '' U),
    ∀ y : U, (τ (Quot.mk _ y) : X.OrbitSpace) = X.π (ΨO y)

end

/-- Definition 7.9 (the project's `LocalUniformizer` is the text's notion), every object has a
local uniformizer, local uniformizers are injective on objects and morphisms, and `π(U(x))` is an
open neighbourhood of `π(x)`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    -- (D) the definition
    (∀ (x : Obj) (U : Set Obj) (Φ : X.Isotropy x → Obj → Obj) (Γ : X.Isotropy x → Obj → Mor)
        (ΨO : Obj → Obj) (ΨM : X.Isotropy x → Obj → Mor),
      IsLocalUniformizerB X x U Φ Γ ΨO ΨM ↔
        ∃ L : X.LocalUniformizer x, L.rep.U = U ∧
          (∀ g, ∀ y ∈ U, L.rep.Φ g y = Φ g y ∧ L.rep.Γ g y = Γ g y) ∧
          (∀ y : L.rep.U, L.Ψ.obj y = ΨO y) ∧
          (∀ (g : X.Isotropy x) (y : L.rep.U), L.Ψ.mor (g, y) = ΨM g y)) ∧
    -- (E) a local uniformizer around every object
    (∀ x : Obj, ∃ (U : Set Obj) (Φ : X.Isotropy x → Obj → Obj) (Γ : X.Isotropy x → Obj → Mor)
        (ΨO : Obj → Obj) (ΨM : X.Isotropy x → Obj → Mor), IsLocalUniformizerB X x U Φ Γ ΨO ΨM) ∧
    -- (I) injective on objects and on morphisms
    (∀ (x : Obj) (U : Set Obj) (Φ : X.Isotropy x → Obj → Obj) (Γ : X.Isotropy x → Obj → Mor)
        (ΨO : Obj → Obj) (ΨM : X.Isotropy x → Obj → Mor),
      IsLocalUniformizerB X x U Φ Γ ΨO ΨM →
        Set.InjOn ΨO U ∧
          Set.InjOn (fun p : X.Isotropy x × Obj => ΨM p.1 p.2) (Set.univ ×ˢ U)) ∧
    -- (O) `π(U(x))` is an open neighbourhood of `π(x)` in `|X|`
    (∀ (x : Obj) (U : Set Obj) (Φ : X.Isotropy x → Obj → Obj) (Γ : X.Isotropy x → Obj → Mor),
      IsNatAction X x U Φ Γ → IsOpen (X.π '' U) ∧ X.π x ∈ X.π '' U)

end RoundTrip.V7_28
