import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_20

/-! Round trip for V4_20 (Proposition 4.9: an sc⁺-retract near `0` is sc-diffeomorphic, through
"the sc-projection `p`", to a relatively open subset of the partial quadrant `T₀O ∩ C` of `T₀O`).

`A` is the conjunction of the types of `Polyfold.proposition_4_9` and
`Polyfold.finiteDimensional_tangentSpace_zero` (no universe parameters; `GraphData` is a
definition, the bundled hypotheses of `proposition_4_9`).

Neither direction is proved.  The two statements are about **different maps**:

* `A`'s `p` is the continuous projection onto `N = T₀O` along an **arbitrary closed good
  complement `Y`** (hypotheses: the project's `IsInGoodPosition`, with an algebraic complement;
  `Y` closed; `p = 1` on `N`, `p = 0` on `Y`), and `A` also gives the graph form `Γ(a) − a ∈ Y`.
* `B`'s `p` is **`Dt(0)`** (the item says `p = Dt(0)`), with B's good position asking an
  sc-complement `Y`, which then plays no further role.

`Dt(0)` is a projection onto `N` along `ker Dt(0)`, so B is the instance `Y = ker Dt(0)` of A —
**provided `ker Dt(0)` is a good complement of `N`**, which `A` does not say.  It is true (sketch):
`Dt(0)` maps `C` into `C` (the project has `mapsTo_partialQuadrant` for derivatives); writing
`C = T⁻¹([0,∞)ⁿ ⊕ W)`, every coordinate `λ_i` that vanishes at some `n₀ ≠ 0` of `N ∩ C` vanishes on
every good complement (test `n₀ ± y`), so these coordinates map `N` onto their range; `λ_i ∘ Dt(0)`
is a nonnegative combination of the `λ_j`, which forces `λ_i ∘ Dt(0) = λ_i` for them, hence
`λ_i(ker Dt(0)) = 0`; the other coordinates are `≥ c|n|` on `N ∩ C` by compactness.  So `ker Dt(0)`
is a closed good complement and A gives B, after also transporting the conclusion from the
constant sc-structure on `N` (A) to the induced one `E.ofSubspace hN` (B), and producing
`IsScRetract E C (O ∩ W)` and `hN : IsScSubspace T₀O` (`N ⊆ E_∞` finite-dimensional).  This is a new
lemma about the retraction plus sc-structure transport, not glue: `A → B` is left unproved.

`B → A` fails for genuine generality: `A` holds for every closed good complement `Y` (projection
along `Y`), under the weaker algebraic good-position hypothesis; from B (about `Dt(0)` only) one would
need that `p_Y ∘ q` (`q` the inverse of `Dt(0)|_O`) is a local diffeomorphism of `N ∩ C` near `0`, a
one-sided inverse-function argument on a partial quadrant, and the graph form; `B` does not give
`dim T₀O < ∞` either (`finiteDimensional_tangentSpace_zero`).

What `A` does give in B's setting is proved below (`A_in_B_setting`): B's hypotheses imply A's (B's
sc-complement `Y` is a closed good complement; `Dt(0)E` is the project's `tangentSpace`), and A then
yields the sc-diffeomorphism `O ∩ W ≅ V` through the projection along **B's `Y`**, not `Dt(0)`. -/

namespace RoundTrip.V4_20
open Polyfold Set

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.proposition_4_9) ∧ (type_of% @Polyfold.finiteDimensional_tangentSpace_zero)

theorem A_holds : A := ⟨@Polyfold.proposition_4_9, @Polyfold.finiteDimensional_tangentSpace_zero⟩

/-- Under B's hypotheses, `A` (its second conjunct, Lemma 4.7 (ii)) gives `dim Dt(0)E < ∞`. -/
theorem finiteDimensional_of_A (hA : A) {E : ScBanach} {C : Set (E.lvl 0)} (t : ScRetraction E C)
    (ht : t.IsScPlus) (h0 : (0 : E.lvl 0) ∈ t.retract) :
    FiniteDimensional ℝ (tangentAtZero t) := by
  have h0' : (0 : E.lvl 1) ∈ E.lvlSet t.retract 1 := by
    rw [ScBanach.mem_lvlSet, map_zero]; exact h0
  exact hA.2 t ht h0 (tangentSpace_eq_coe_submodule t h0').symm

/-- **What `A` gives in B's setting**: under B's hypotheses (`T₀O = Dt(0)E` finite-dimensional by
`finiteDimensional_of_A`), `O` is near `0` sc-diffeomorphic to a relatively open `V ∋ 0` in
`T₀O ∩ C` (constant sc-structure on `T₀O`) through the projection `p` along B's good
sc-complement `Y` — not through `Dt(0)`. -/
theorem A_in_B_setting (hA : A) (E : ScBanach) (C : Set (E.lvl 0)) (t : ScRetraction E C)
    (ht : t.IsScPlus) (h0 : (0 : E.lvl 0) ∈ t.retract) (hg : IsGoodPositionB E C (tangentAtZero t))
    [FiniteDimensional ℝ (tangentAtZero t)] :
    ∃ (Y : Submodule ℝ (E.lvl 0)) (p : E.lvl 0 →L[ℝ] tangentAtZero t),
      E.IsScSplitting (tangentAtZero t) Y ∧ (∀ n : tangentAtZero t, p n = n) ∧
      (∀ y ∈ Y, p y = 0) ∧
      ∃ (W : Set (E.lvl 0)) (V : Set (tangentAtZero t)) (Γ : tangentAtZero t → E.lvl 0),
        IsOpen W ∧ (0 : E.lvl 0) ∈ W ∧
        IsRelOpenInQuadrant (ScBanach.const (tangentAtZero t)) (Subtype.val ⁻¹' C) V ∧
        (0 : tangentAtZero t) ∈ V ∧
        IsScSmoothRetractMap E C (t.retract ∩ W) (ScBanach.const (tangentAtZero t))
          (Subtype.val ⁻¹' C) V p ∧
        IsScSmoothRetractMap (ScBanach.const (tangentAtZero t)) (Subtype.val ⁻¹' C) V E C
          (t.retract ∩ W) Γ ∧
        (∀ u ∈ t.retract ∩ W, Γ (p u) = u) ∧ (∀ a ∈ V, p (Γ a) = a) := by
  have h0' : (0 : E.lvl 1) ∈ E.lvlSet t.retract 1 := by
    rw [ScBanach.mem_lvlSet, map_zero]; exact h0
  have hN : ((tangentAtZero t : Submodule ℝ (E.lvl 0)) : Set (E.lvl 0)) =
      tangentSpace E C t.retract 0 := (tangentSpace_eq_coe_submodule t h0').symm
  obtain ⟨hint, Y, hY, ε, hε, hgood⟩ := hg
  have hcompl : IsCompl (tangentAtZero t) Y := by
    have := hY.2.2 0
    rwa [ScBanach.levelSub_zero, ScBanach.levelSub_zero] at this
  have hYc : IsClosed (Y : Set (E.lvl 0)) := hY.2.1.isClosed
  have hgc : IsGoodComplement E C (tangentAtZero t) Y := ⟨hcompl, ε, hε, hgood⟩
  obtain ⟨p, hpN, hpY, -⟩ := exists_proj_of_isCompl hYc hcompl
  obtain ⟨W, V, Γ, hW, h0W, hV, h0V, -, hpΓ, -, -, hΓp, -, hpmap, hΓmap⟩ :=
    hA.1 t ht h0 hN ⟨hint, Y, hgc⟩ hgc hYc p hpN hpY
  exact ⟨Y, p, hY, hpN, hpY, W, V, Γ, hW, h0W, hV, h0V, hpmap, hΓmap, hΓp, hpΓ⟩

#rt_check RoundTrip.V4_20.finiteDimensional_of_A [Polyfold.proposition_4_9,
  Polyfold.finiteDimensional_tangentSpace_zero]
#rt_check RoundTrip.V4_20.A_in_B_setting [Polyfold.proposition_4_9,
  Polyfold.finiteDimensional_tangentSpace_zero]

end RoundTrip.V4_20
