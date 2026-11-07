import Polyfold
/-! Blind formalization of V7_62 (the 2017 book's Part II, §7.5.1, Theorem 7.5 = Theorem 7.1,
pp. 253–254: the natural representation).

Text: given an ep-groupoid `X`, `x₀ ∈ X` and an open `V ∋ x₀`, there are an open `U ∋ x₀`,
`U ⊆ V`, a homomorphism `Φ : G_{x₀} → Diff_sc(U)`, `Φ(g) = t_g ∘ s_g⁻¹`, and an sc-smooth
`Γ : G_{x₀} × U → 𝐗` with `Γ(g, x₀) = g`, `s Γ(g, y) = y`, `t Γ(g, y) = Φ(g)(y)`, and every
morphism `h : y → z` between points of `U` is `Γ(g, y)` for a unique `g`.  In the proof
`N_g = N^t_g ∩ N^s_g` are pairwise disjoint open neighbourhoods of the `g` on which `s, t` are
sc-diffeomorphisms, `s_g = s|N_g`, `t_g = t|N_g`, `Γ(g, y) = s_g⁻¹(y)`.

Choices:
- Setting: `Obj Mor : Type` (universe 0, as in the other blind files), with the instances of the
  project's `EpGroupoid`, `X : EpGroupoid Obj Mor` (the project's Definition 7.3, fields read
  with `#print`, as in `RoundTrip/Blind/V7_49.lean`).  `G_{x₀}` is the project's
  `X.Isotropy x₀` with its group structure; I checked by `rfl` that `(g * h).val = g ∘ h`.
- The natural action (`IsNatActionB X x₀ U Φ Γ`, the same clauses as `NatRepB` of
  `RoundTrip/Blind/V7_35.lean`): `U` open, `x₀ ∈ U`; every `Φ(g)` an sc-diffeomorphism of `U` onto
  `U` (the project's `IsScDiffeoOn`, `#print`: both maps sc-smooth on the open sets, `MapsTo` both
  ways, mutually inverse there); `Φ(gh) = Φ(g) ∘ Φ(h)` on `U` (a homomorphism into the group
  `Diff_sc(U)`; `Φ(1) = id` follows); `Γ` sc-smooth on the M-polyfold `G_{x₀} × U` (a finite
  disjoint union of copies of `U`), read as: every `Γ(g, ·)` sc-smooth on `U`
  (`IsScSmoothOn`); the three listed properties, for all `y ∈ U`, all `g`, and every morphism `h`
  with `s h, t h ∈ U`.  `Φ`, `Γ` are total functions; only their values on `U` matter.  I did not
  use the project's `NaturalRep`: it also requires `U` connected (`#print`), which the statement
  does not ask.
- "`Φ(g) = t_g ∘ s_g⁻¹`": I read this formula as part of the claim and formalize it with the
  proof's sheets: there are pairwise disjoint sets `N_g ∋ g` of morphisms on which `s` and `t`
  are sc-diffeomorphisms onto open subsets of `X`, with `Γ(g, y) ∈ N_g` for `y ∈ U`; since
  `s Γ(g, y) = y` this says `Γ(g, ·) = s_g⁻¹` on `U` and then `Φ(g) = t Γ(g, ·) = t_g ∘ s_g⁻¹`.
  (The contractibility of `N^s_g, N^t_g` and the common target `U₀` are choices in the proof, not
  claims about the result; left out.)
- "In particular, every morphism between points in `U` is in the image of `Γ`" follows from the
  uniqueness clause; not repeated.
- Nothing looks false to me.
-/
namespace RoundTrip.V7_62
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

/-- Theorem 7.5 (= 7.1): every neighbourhood of `x₀` contains one with the natural
representation `Φ(g) = t_g ∘ s_g⁻¹`, `Γ(g, ·) = s_g⁻¹`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (x₀ : Obj) (V : Set Obj), IsOpen V → x₀ ∈ V →
    ∃ (U : Set Obj) (Φ : X.Isotropy x₀ → Obj → Obj) (Γ : X.Isotropy x₀ → Obj → Mor),
      U ⊆ V ∧ IsNatActionB X x₀ U Φ Γ ∧
      ∃ N : X.Isotropy x₀ → Set Mor,
        Pairwise (Function.onFun Disjoint N) ∧
        (∀ g, g.val ∈ N g) ∧
        (∀ g, ∃ (σ : Obj → Mor) (S : Set Obj), X.PMor.IsScDiffeoOn X.PObj X.src σ (N g) S) ∧
        (∀ g, ∃ (τ : Obj → Mor) (T : Set Obj), X.PMor.IsScDiffeoOn X.PObj X.tgt τ (N g) T) ∧
        ∀ g, ∀ y ∈ U, Γ g y ∈ N g

end RoundTrip.V7_62
