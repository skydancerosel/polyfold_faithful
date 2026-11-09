import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_48

/-!
Round trip for V8_48 (2021 Definition 8.4.2, the local regularity property of a strong bundle,
and Proposition 8.4.3, p. 382).

The item lists the definitions `EpStrongBundle.natLift`, `EpStrongBundle.IsLR` (vocabulary) and
one theorem, the witness `EpStrongBundle.isLR_trivial` (every strong bundle over the trivial
ep-groupoid of an M-polyfold has the local regularity property).  `A` is its type, universe at
`0`.  The project does **not** formalize Proposition 8.4.3 (its file says so).

`B` is (i) `E.IsLR ↔ IsLRB E` for every strong bundle `E` (the blind author's own reading of
Definition 8.4.2, quantifying over *local* strong bundle isomorphisms of `W|U(x)`) and (ii)
Proposition 8.4.3 (`X` effective with (LR) ⇒ `IsLRB E`).

* `B ⇒ A` (`B_to_A`): the trivial ep-groupoid is effective (`EpGroupoid.isEffective_trivial`) and
  has (LR) (`isLR_trivialGroupoid`, proved here: `|β y| = |y|` forces `β y = y`), so (ii) gives
  `IsLRB E` for the trivial strong bundle and (i) turns it into `E.IsLR`.
* `A ⇒ B` fails: `A` is a single witness and says nothing about (i) or (ii) for other bundles.
  Of (i) only `IsLRB E → E.IsLR` is proved (`isLR_of_isLRB`, the project's quantifier ranges over
  fewer maps: strong bundle maps `Φ : W → W` defined globally that restrict to isomorphisms of
  `W|U(x)`); the converse would need every local strong bundle isomorphism of `W|U(x)` to be the
  restriction of a global strong bundle map.  (ii) is Proposition 8.4.3 itself.
-/

namespace RoundTrip.V8_48
open Polyfold

/-- The project's statement (universe `0`). -/
def A : Prop := type_of% @Polyfold.EpStrongBundle.isLR_trivial.{0}

theorem A_holds : A := @Polyfold.EpStrongBundle.isLR_trivial.{0}

/-- The trivial ep-groupoid of an M-polyfold has (LR) (2021 Definition 7.4.19). -/
theorem isLR_trivialGroupoid {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
    (PZ : MPolyfold Z) : (EpGroupoid.trivial PZ).IsLR := by
  intro x O hO hxO
  obtain ⟨R, hRO⟩ := (EpGroupoid.trivial PZ).theorem_7_1 x hO hxO
  refine ⟨R, hRO, fun β β' _ hπ => ⟨1, fun y hy => ?_⟩⟩
  obtain ⟨φ, h1, h2⟩ := (GroupoidStr.π_eq_π_iff _).1 (hπ y hy)
  have hs := R.src_Γ 1 y hy
  have ht := R.tgt_Γ 1 y hy
  change φ = β y at h1
  change φ = y at h2
  change R.Γ 1 y = y at hs
  change R.Γ 1 y = R.Φ 1 y at ht
  rw [← h1, h2, ← ht, hs]

/-- Half of B (i): the blind reading `IsLRB` implies the project's `IsLR` (every global strong
bundle map restricting to an isomorphism of `W|U(x)` is a local strong bundle isomorphism, and
`π(Φ w) = π w` gives the morphism `φ` with `μ(φ, w) = Φ w`). -/
theorem isLR_of_isLRB {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
    {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {SB : StrongBundle X.PObj P}
    (E : EpStrongBundle X SB) (h : IsLRB E) : E.IsLR := by
  intro x O hO hxO
  obtain ⟨R, hRO, hR⟩ := h x O hO hxO
  refine ⟨R, hRO, fun β Φ hΦ hiso hπ => ?_⟩
  have hone : ∀ w : SB.One, P (SB.oneVal w) ∈ R.U → Φ (SB.oneVal w) ∈ SB.oneSet :=
    fun w _ => hΦ.mapsTo_oneSet (SB.oneVal_mem w)
  have hsb : IsSBIsoOnB SB R.U β Φ := by
    refine ⟨hiso.isScDiffeoOn_base, fun w _ => hΦ.covers w, fun x' _ => hΦ.fiber_linear x',
      hiso.isScDiffeoOn_zero, hone, ?_⟩
    obtain ⟨Ψ₁, hΨ₁⟩ := hiso.isScDiffeoOn_one
    refine ⟨Ψ₁, hΨ₁.congr fun w hw => ?_⟩
    have hw' : P (SB.oneVal w) ∈ R.U := hw
    simp only [oneMapB, dif_pos hw']
    rfl
  have hiw : ∀ w, P w ∈ R.U → IsoW E w (Φ w) := by
    intro w hw
    obtain ⟨⟨⟨φ, w'⟩, hq⟩, h1, h2⟩ := (GroupoidStr.π_eq_π_iff _).1 (hπ w hw).symm
    change w' = w at h1
    subst h1
    exact ⟨φ, hq, h2⟩
  obtain ⟨g, hg⟩ := hR β Φ hsb hiw
  exact ⟨g, fun w hw => hg w hw⟩

/-- `B ⇒ A`: Proposition 8.4.3 (B (ii)) for the trivial ep-groupoid, which is effective and has
(LR), then B (i). -/
theorem B_to_A : B → A := by
  intro hB Z _ _ _ PZ W _ _ _ P _ _ SB
  exact (hB.1 Z Z (EpGroupoid.trivial PZ) W P SB (EpStrongBundle.trivial SB)).2
    (hB.2 Z Z (EpGroupoid.trivial PZ) W P SB (EpStrongBundle.trivial SB)
      (EpGroupoid.isEffective_trivial PZ) (isLR_trivialGroupoid PZ))

#rt_check RoundTrip.V8_48.B_to_A [Polyfold.EpStrongBundle.isLR_trivial]
#rt_check RoundTrip.V8_48.isLR_of_isLRB [Polyfold.EpStrongBundle.isLR_trivial]
#rt_overlap RoundTrip.V8_48.B_to_A [Polyfold.EpStrongBundle.isLR_trivial]

end RoundTrip.V8_48
