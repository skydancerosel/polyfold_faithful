import Polyfold
/-! Blind formalization of V7_22 (the 2017 book, arXiv 1707.08941, Part II, §7.1, p. 232: the
functor `Γ : G_x ⋉ U(x) → X` is fully faithful and identifies `G_x ⋉ U(x)` with the full
subcategory `(U(x), 𝐔(x))`).

Text: the natural functor `Γ`, `y ↦ y` on objects and `(g, y) ↦ Γ(g, y)` on morphisms, is full
and faithful (`mor_{G⋉U}(y, z) → mor_X(y, z)` is onto and injective); its image is the full
subcategory `(U(x), 𝐔(x))`; hence `Γ` identifies `G_x ⋉ U(x)` with `(U(x), 𝐔(x))`.

Choices:
- Setting as in my `RoundTrip/Blind/V7_21.lean`: `Obj Mor : Type` (universe 0), the project's
  `X : EpGroupoid Obj Mor`, `G_x = X.Isotropy x` (product `g * h = g ∘ h`, checked by `rfl`), and
  "the natural `G_x`-action on `U(x)`" my `IsNatAction X x U Φ Γ` (Theorem 7.1's data, `U` open,
  NOT required connected; the project's `NaturalRep` additionally requires connected `U`, so I
  did not use it).
- Morphisms of `G ⋉ U`: `(g, y) : y → Φ(g)(y)`, `y ∈ U`, composition `(g, y) ∘ (h, z) = (gh, z)`
  for `y = Φ(h)(z)`, unit `(1, y)` (p. 232 / V7_21).  "The natural functor": B asserts that
  `(g, y) ↦ Γ(g, y)` respects composition and units (respecting `s`, `t` is hypothesis (2) of the
  natural action and is not repeated).
- "Full and faithful": for `y, z ∈ U`, `g ↦ Γ(g, y)` is a bijection from
  `mor_{G⋉U}(y, z) ≅ {g | Φ(g)(y) = z}` onto `mor_X(y, z)` (project's `X.mor y z`, `#print`ed:
  `{φ | s φ = y ∧ t φ = z}`).
- "The image is the full subcategory `(U(x), 𝐔(x))`": on objects the image is `U` (trivially,
  the functor being the inclusion), on morphisms `{Γ(g, y) | g ∈ G_x, y ∈ U} = 𝐔(x)` with
  `𝐔(x) = {φ | s φ, t φ ∈ U}` (project's `X.morOn U`, `#print`ed).  "Identifies" (as categories):
  in addition `(g, y) ↦ Γ(g, y)` is injective on `G_x × U`, i.e. `Γ` is an isomorphism of
  categories onto `(U(x), 𝐔(x))`.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V7_22
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

end

/-- `Γ : G_x ⋉ U(x) → X` is a functor, fully faithful, with image the full subcategory
`(U(x), 𝐔(x))`, and it identifies `G_x ⋉ U(x)` with that full subcategory. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (x : Obj) (U : Set Obj) (Φ : X.Isotropy x → Obj → Obj)
    (Γ : X.Isotropy x → Obj → Mor), IsNatAction X x U Φ Γ →
    -- `Γ` is a functor: `Γ((g, Φ(h)z) ∘ (h, z)) = Γ(g, Φ(h)z) ∘ Γ(h, z)` and `Γ(1, y) = 1_y`
    (∀ (g h : X.Isotropy x), ∀ z ∈ U, Γ (g * h) z = X.comp (Γ g (Φ h z)) (Γ h z)) ∧
    (∀ y ∈ U, Γ 1 y = X.unit y) ∧
    -- full and faithful: `mor_{G⋉U}(y, z) → mor_X(y, z)` is a bijection
    (∀ y ∈ U, ∀ z ∈ U, Set.BijOn (fun g => Γ g y) {g | Φ g y = z} (X.mor y z)) ∧
    -- the image on morphisms is `𝐔(x)`
    ((fun p : X.Isotropy x × Obj => Γ p.1 p.2) '' (Set.univ ×ˢ U) = X.morOn U) ∧
    -- `Γ` identifies `G_x ⋉ U(x)` with `(U(x), 𝐔(x))`: injective on all morphisms
    Set.InjOn (fun p : X.Isotropy x × Obj => Γ p.1 p.2) (Set.univ ×ˢ U)

end RoundTrip.V7_22
