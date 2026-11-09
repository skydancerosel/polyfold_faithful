import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_46

/-! Round trip for V4_46 (proof of Theorem 4.22: linear algebra at the corner of a centred chart).

`A` is the conjunction of the types of `Polyfold.mem_minimalSubspaceWith_zero`,
`Polyfold.minimalSubspaceWith_zero_le`, `Polyfold.add_mem_iff_of_mem_zero`,
`Polyfold.degIndexWith_add_of_mem_zero`, `Polyfold.coordsOn_surjective`,
`Polyfold.exists_isClosed_isCompl_le` (universe `0` for its normed space `V`),
`Polyfold.exists_goodComplement_le_zero` and `Polyfold.degIndex_slice`.

Neither direction is proved.

`A → B` fails because `A` contains no sc-level (levelwise) statement: B's conclusions (1) and (2)
are sc-splittings (`E.IsScSplitting`: sc-subspaces, complementary on every level `E_m`) and (3) is a
partial quadrant for the *induced* sc-structure `E.ofSubspace hTA`, while `A`'s lemmas work on
level `0` only: a *closed algebraic* complement `Y ⊆ E_0` of a finite-dimensional `N` with
`N + E_0 = E` (`exists_isClosed_isCompl_le`, `exists_goodComplement_le_zero`), coordinates, and the
presentation of `N ∩ C` with the *constant* structure (inside `degIndex_slice`).  What `A` does give
is the level-`0` shadow of B, proved below as `A_to_B_level0`: `T₀A + E_0 = E`, a closed complement
`Y ⊆ E_0` of `T₀A` with `C = (T₀A ∩ C) ⊕ Y`, `E₀ = N ⊕ E_0` algebraically for every `N` with
`T₀A = N ⊕ (T₀A ∩ E_0)`, and `T₀A ∩ C` a partial quadrant of `T₀A` with the constant structure.
Upgrading this to B needs the sc-complement `Y = Ã ⊕ Z` (closedness through the projection along
`Z`, levelwise splitting and density of smooth points), `E_0 = T⁻¹({0} ⊕ W)` as an sc-subspace with
`E_m = N ⊕ (E_0)_m`, and the sc-isomorphism `E.ofSubspace hTA ≅ ℝᵏ ⊕ (T₀A ∩ E_0)`: genuine
sc-level arguments that `A` does not contain (the project replaced the text's sc-splittings by the
coordinate presentation, see the docstring of `LocalStructure.lean`).  B itself looks true.

`B → A` fails: `A`'s conjuncts are general coordinate lemmas (for any presented partial quadrant,
any `x`, `k`, any finite-dimensional `N` with `N + E_0 = E`, any normed space `V`), while B is one
implication under the specific hypotheses `E = T₀O ⊕ Z = T₀A ⊕ Ã ⊕ Z`; B does not yield them (they
are provable outright, which would be vacuous for the audit). -/

namespace RoundTrip.V4_46
open Polyfold Set

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.mem_minimalSubspaceWith_zero) ∧
    (type_of% @Polyfold.minimalSubspaceWith_zero_le) ∧
    (type_of% @Polyfold.add_mem_iff_of_mem_zero) ∧
    (type_of% @Polyfold.degIndexWith_add_of_mem_zero) ∧
    (type_of% @Polyfold.coordsOn_surjective) ∧
    (type_of% @Polyfold.exists_isClosed_isCompl_le.{0}) ∧
    (type_of% @Polyfold.exists_goodComplement_le_zero) ∧
    (type_of% @Polyfold.degIndex_slice)

theorem A_holds : A :=
  ⟨@Polyfold.mem_minimalSubspaceWith_zero, @Polyfold.minimalSubspaceWith_zero_le,
    @Polyfold.add_mem_iff_of_mem_zero, @Polyfold.degIndexWith_add_of_mem_zero,
    @Polyfold.coordsOn_surjective, @Polyfold.exists_isClosed_isCompl_le.{0},
    @Polyfold.exists_goodComplement_le_zero, @Polyfold.degIndex_slice⟩

/-- **What `A` gives**: the level-`0` shadow of B (sc-splittings replaced by closed or algebraic
complements, the induced sc-structure on `T₀A` by the constant one). -/
theorem A_to_B_level0 (hA : A) :
    ∀ (E : ScBanach) (n : ℕ) (W' : ScBanach) (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W'))
      (C : Set (E.lvl 0)), C = T.lvl 0 ⁻¹' quadrant n W' 0 →
      ∀ (TO Z TA At : Submodule ℝ (E.lvl 0)),
        E.IsScSplitting TO Z → Z ≤ minimalSubspaceWith T 0 →
        E.IsScSubspace TA → E.IsScSubspace At →
        (∀ m : ℕ, E.levelSub TA m ⊓ E.levelSub At m = ⊥ ∧
          E.levelSub TA m ⊔ E.levelSub At m = E.levelSub TO m) →
        At ≤ minimalSubspaceWith T 0 → ∀ [FiniteDimensional ℝ TA],
          TA ⊔ minimalSubspaceWith T 0 = ⊤ ∧
          (∃ Y : Submodule ℝ (E.lvl 0), IsClosed (Y : Set (E.lvl 0)) ∧ IsCompl TA Y ∧
            Y ≤ minimalSubspaceWith T 0 ∧ C = {c | ∃ a ∈ TA, a ∈ C ∧ ∃ y ∈ Y, c = a + y}) ∧
          (∀ N : Submodule ℝ (E.lvl 0), N ⊓ (TA ⊓ minimalSubspaceWith T 0) = ⊥ →
            N ⊔ (TA ⊓ minimalSubspaceWith T 0) = TA → IsCompl N (minimalSubspaceWith T 0)) ∧
          IsPartialQuadrant (ScBanach.const TA) (Subtype.val ⁻¹' C) := by
  obtain ⟨-, -, hadd, -, -, hcompl, hgood, -⟩ := hA
  intro E n W' T C hC TO Z TA At hOZ hZ _ _ hlev hAt _
  set W₀ := minimalSubspaceWith T 0 with hW₀
  -- `T₀A + E_0 = E`
  have hTO : TA ⊔ At = TO := by
    have := (hlev 0).2
    rwa [ScBanach.levelSub_zero, ScBanach.levelSub_zero, ScBanach.levelSub_zero] at this
  have hOZ0 : IsCompl TO Z := by
    have := hOZ.2.2 0
    rwa [ScBanach.levelSub_zero, ScBanach.levelSub_zero] at this
  have htop : TA ⊔ W₀ = ⊤ := by
    rw [eq_top_iff, ← hOZ0.sup_eq_top, ← hTO]
    exact sup_le (sup_le le_sup_left (hAt.trans le_sup_right)) (hZ.trans le_sup_right)
  refine ⟨htop, ?_, ?_, ?_⟩
  · -- a closed complement `Y ⊆ E_0`, and `C = (T₀A ∩ C) ⊕ Y`
    obtain ⟨Y, hYW, hYc, hTAY⟩ := hcompl (isClosed_minimalSubspaceWith T 0) htop
    refine ⟨Y, hYc, hTAY, hYW, ?_⟩
    ext c
    constructor
    · intro hc
      have hcm : c ∈ TA ⊔ Y := by rw [hTAY.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨a, ha, y, hy, rfl⟩ := Submodule.mem_sup.1 hcm
      exact ⟨a, ha, (hadd T hC (hYW hy)).1 hc, y, hy, rfl⟩
    · rintro ⟨a, -, haC, y, hy, rfl⟩
      exact (hadd T hC (hYW hy)).2 haC
  · -- `E₀ = N ⊕ E_0` (algebraically)
    intro N hN1 hN2
    have hNTA : N ≤ TA := hN2 ▸ le_sup_left
    refine IsCompl.of_eq ?_ ?_
    · rw [eq_bot_iff, ← hN1]
      intro v hv
      exact ⟨hv.1, hNTA hv.1, hv.2⟩
    · rw [eq_top_iff, ← htop, ← hN2]
      exact sup_le (sup_le le_sup_left (inf_le_right.trans le_sup_right)) le_sup_right
  · -- `T₀A ∩ C` is a partial quadrant of `T₀A` (constant structure)
    exact proposition_3_1_25 ⟨n, W', T, hC⟩ (hgood T hC htop).1

#rt_check RoundTrip.V4_46.A_to_B_level0 [Polyfold.mem_minimalSubspaceWith_zero,
  Polyfold.minimalSubspaceWith_zero_le, Polyfold.add_mem_iff_of_mem_zero,
  Polyfold.degIndexWith_add_of_mem_zero, Polyfold.coordsOn_surjective,
  Polyfold.exists_isClosed_isCompl_le, Polyfold.exists_goodComplement_le_zero,
  Polyfold.degIndex_slice]

end RoundTrip.V4_46
