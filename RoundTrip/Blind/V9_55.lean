import Polyfold
/-! Blind formalization of V9_55 (the Springer 2021 book, Part II, §9.5, Lemma 9.5.10, p. 444,
and (9.23), p. 445; new in the 2021 edition): the effective orders.

Text: the same (as Lemma 9.5.9) for the effective measures under (LUC); the proof uses
`T_x = {g | ĝ = id on an open W}`, `T_x ⊆ H`, `T_y` identified with `T_x`, and (9.23)
`♯R = ♯G^eff_x / ♯H^eff_y`.

Choices:
- The item is "the effective orders and (9.23)": the effective measures themselves (integrals of
  sc-differential forms) are not in the vocabulary and not formalized; B is the conjunction of the
  four group-theoretic facts of the proof.
- Setting as in my `RoundTrip/Blind/V9_54.lean` (prelude copied): the project's ep-groupoid `X`
  with (LUC) (project's `IsLUC`, 2021 Definition 7.2.18, compared in `RoundTrip/Blind/V8_45.lean`),
  `x`, a connected `U = U(x)` with the natural `G_x`-action `Φ`, `Γ` (my `IsNatAction`, `ĝ = Φ(g)`),
  `y ∈ U`, `H = {g | Φ(g)(y) = y}` (`stabB`), `R` a set of left coset representatives of `H`
  (`IsLeftCosetRepsB`).  `Θ` and the local branching structure of Lemma 9.5.9 do not enter these
  facts and are omitted.
- `T_x`: the project's `X.trivialSubgroup x` (the `g` with `Φ(g) = id` on some natural
  representation; compared in `RoundTrip/Blind/V7_37.lean`).  "`T_x = {g | ĝ = id on an open W}`":
  `T_x` is the set of `g` with `Φ(g) = id` on some nonempty open `W ⊆ U` (the `U` at hand).
- "`T_y` identified with `T_x`": under the isomorphism `e : H ≅ G_y`, `h ↦ Γ(h, y)` of
  Lemma 9.5.9, `h ∈ T_x ↔ e(h) ∈ T_y` (for `h ∈ H`, using `T_x ⊆ H`).
- (9.23): `♯R = ♯G^eff_x / ♯H^eff_y`, with `G^eff_x = G_x/T_x` the project's `X.EffIsotropy x`
  (compared in `RoundTrip/Blind/V7_41.lean`) and `H^eff_y` read as `H/T_x ≅ G_y/T_y = G^eff_y`
  (by the identification above), so `♯H^eff_y = ♯X.EffIsotropy y`; `Nat.card`, `ℕ`-division.
- Nothing looks false to me.
-/
namespace RoundTrip.V9_55
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- The natural `G_x`-action on the open neighbourhood `U` of `x` (the data `Φ`, `Γ` of
Theorem 7.1), as in `RoundTrip/Blind/V7_21.lean` and `RoundTrip/Blind/V9_34.lean`. -/
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

/-- `H = {g ∈ G_x | g ∗ y = y}`, the elements of `G_x` fixing `y`. -/
def stabB {X : EpGroupoid Obj Mor} {x : Obj} (Φ : X.Isotropy x → Obj → Obj) (y : Obj) :
    Set (X.Isotropy x) :=
  {g | Φ g y = y}

end

/-- `R` is a set of representatives of the left cosets of `H` in `G`, `G = ⨆_{r ∈ R} rH`:
every `g` is `r h` (`h ∈ H`) for exactly one `r ∈ R`. -/
def IsLeftCosetRepsB {G : Type} [Group G] (H R : Set G) : Prop :=
  ∀ g : G, ∃! r : G, r ∈ R ∧ ∃ h ∈ H, g = r * h

/-- **Lemma 9.5.10, the effective orders**: under (LUC), `T_x` consists of the `g` with
`ĝ = id` on a nonempty open subset of `U(x)`, `T_x ⊆ H`, the isomorphism `H ≅ G_y` identifies
`T_x` with `T_y`, and (9.23) `♯R = ♯G^eff_x / ♯G^eff_y`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor), X.IsLUC →
    ∀ (x : Obj) (U : Set Obj) (Φ : X.Isotropy x → Obj → Obj) (Γ : X.Isotropy x → Obj → Mor),
      IsNatAction X x U Φ Γ → IsConnected U →
      ∀ y ∈ U,
        -- `T_x = {g | ĝ = id on an open W}`
        ((X.trivialSubgroup x : Set (X.Isotropy x)) =
          {g | ∃ W : Set Obj, IsOpen W ∧ W.Nonempty ∧ W ⊆ U ∧ ∀ w ∈ W, Φ g w = w}) ∧
        -- `T_x ⊆ H`
        ((X.trivialSubgroup x : Set (X.Isotropy x)) ⊆ stabB Φ y) ∧
        -- `T_y` identified with `T_x` under `H ≅ G_y`
        (∃ (Hs : Subgroup (X.Isotropy x)) (e : Hs ≃* X.Isotropy y),
          (Hs : Set (X.Isotropy x)) = stabB Φ y ∧ (∀ h : Hs, (e h).val = Γ h.1 y) ∧
          ∀ h : Hs, h.1 ∈ X.trivialSubgroup x ↔ e h ∈ X.trivialSubgroup y) ∧
        -- (9.23)
        (∀ R : Set (X.Isotropy x), IsLeftCosetRepsB (stabB Φ y) R →
          Nat.card R = Nat.card (X.EffIsotropy x) / Nat.card (X.EffIsotropy y))

end RoundTrip.V9_55
