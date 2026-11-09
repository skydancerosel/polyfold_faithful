import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V1_19

/-! Round trip for V1_19 (Corollary 1.20: maps into `ℝᴺ`).

`A` is the conjunction of the types of the theorems in the item's declaration list:
`corollary_1_2_5_text`, `IsScSmooth.of_contDiffOn_levels_finiteDimensional_text`,
`IsScSmooth.of_contDiffOn_finiteDimensional`, `corollary_1_2_5_zero`, `corollary_1_2_5`,
`corollary_1_2_5_base`.  None has universe parameters (`V : Type` is explicit in each).

Same notions: `ℝᴺ` with the constant sc-structure; `B`'s `f ∘ E.toBase l` on `U_l` and `IsSck`.

* `A → B`: `corollary_1_2_5_text` with `V = Fin N → ℝ`, on the sc-domain `U`.
* `B → A` fails for a genuine reason: every conjunct of `A` is stated for an arbitrary
  `IsScDomain U` (e.g. a closed disc), `B` only for relatively open subsets of partial quadrants.
  The other difference — `A` allows any finite-dimensional normed `V`, `B` only `Fin N → ℝ` with
  the sup norm — is only effort: on relatively open subsets of partial quadrants all six conjuncts
  follow from `B` (`B_general` transports along a linear isomorphism `ℝᴺ ≅ V`, composing with the
  sc-operator it induces between the constant sc-structures). -/

namespace RoundTrip.V1_19
open Polyfold Set
open scoped ContDiff

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.corollary_1_2_5_text) ∧
    (type_of% @Polyfold.IsScSmooth.of_contDiffOn_levels_finiteDimensional_text) ∧
    (type_of% @Polyfold.IsScSmooth.of_contDiffOn_finiteDimensional) ∧
    (type_of% @Polyfold.corollary_1_2_5_zero) ∧ (type_of% @Polyfold.corollary_1_2_5) ∧
    (type_of% @Polyfold.corollary_1_2_5_base)

theorem A_holds : A :=
  ⟨@Polyfold.corollary_1_2_5_text, @Polyfold.IsScSmooth.of_contDiffOn_levels_finiteDimensional_text,
    @Polyfold.IsScSmooth.of_contDiffOn_finiteDimensional, @Polyfold.corollary_1_2_5_zero,
    @Polyfold.corollary_1_2_5, @Polyfold.corollary_1_2_5_base⟩

theorem A_to_B : A → B := by
  intro hA E C U N f k hU h
  exact hA.1 (V := Fin N → ℝ) hU.isScDomain h

/-- `B → A` on relatively open subsets of partial quadrants, for an arbitrary finite-dimensional
target `V` (the content of `corollary_1_2_5_text` there): transport along `ℝᴺ ≅ V`. -/
theorem B_general (hB : B) {E : ScBanach} {C U : Set (E 0)} (hUC : IsRelOpenInQuadrant E C U)
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {f : E 0 → (ScBanach.const V) 0} {k : ℕ}
    (h : ∀ l, l ≤ k → ContDiffOn ℝ (l + 1) (f ∘ E.toBase l) (E.lvlSet U l)) :
    IsSck (k + 1) E (ScBanach.const V) U f := by
  let e : (Fin (Module.finrank ℝ V) → ℝ) ≃L[ℝ] V :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  have hg : IsSck (k + 1) E (ScBanach.const (Fin (Module.finrank ℝ V) → ℝ)) U
      (fun x => e.symm (f x)) :=
    hB E C U _ (fun x => e.symm (f x)) k hUC fun l hl =>
      e.symm.contDiff.comp_contDiffOn (h l hl)
  let T : ScOperator (ScBanach.const (Fin (Module.finrank ℝ V) → ℝ)) (ScBanach.const V) :=
    { lvl := fun _ => (e : (Fin (Module.finrank ℝ V) → ℝ) →L[ℝ] V)
      incl_comm := fun _ _ => rfl }
  have hc := IsSck.comp hUC.isScDomain (isScDomain_univ _)
    ((T.isScSmooth (isScDomain_univ _)) (k + 1)) hg (mapsTo_univ _ _)
  refine IsSck.congr hUC.isScDomain (fun x _ => ?_) hc
  change e (e.symm (f x)) = f x
  exact e.apply_symm_apply (f x)

/-- `B → A` on relatively open subsets of partial quadrants: all six conjuncts of `A`. -/
theorem B_to_A_quadrant (hB : B) {E : ScBanach} {C U : Set (E 0)}
    (hUC : IsRelOpenInQuadrant E C U) {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {f : E 0 → (ScBanach.const V) 0} :
    -- `corollary_1_2_5_text`
    (∀ {k : ℕ}, (∀ l, l ≤ k → ContDiffOn ℝ (l + 1) (f ∘ E.toBase l) (E.lvlSet U l)) →
      IsSck (k + 1) E (ScBanach.const V) U f) ∧
    -- `IsScSmooth.of_contDiffOn_levels_finiteDimensional_text`
    ((∀ l : ℕ, ContDiffOn ℝ (l + 1) (f ∘ E.toBase l) (E.lvlSet U l)) → IsScSmooth U f) ∧
    -- `IsScSmooth.of_contDiffOn_finiteDimensional`
    (ContDiffOn ℝ ∞ f U → IsScSmooth U f) ∧
    -- `corollary_1_2_5_zero`
    ((∀ m, ContDiffOn ℝ 1 (f ∘ E.toBase m) (E.lvlSet U m)) → IsSc1 U f) ∧
    -- `corollary_1_2_5`
    (∀ {k : ℕ}, (∀ m, ContDiffOn ℝ (k + 1) (f ∘ E.toBase m) (E.lvlSet U m)) →
      IsSck (k + 1) E (ScBanach.const V) U f) ∧
    -- `corollary_1_2_5_base`
    (∀ {k : ℕ}, ContDiffOn ℝ (k + 1) f U → IsSck (k + 1) E (ScBanach.const V) U f) := by
  have htext := fun {k : ℕ} h => B_general hB hUC (f := f) (k := k) h
  have hstrong : ∀ {k : ℕ}, (∀ m, ContDiffOn ℝ (k + 1) (f ∘ E.toBase m) (E.lvlSet U m)) →
      IsSck (k + 1) E (ScBanach.const V) U f := fun {k} h =>
    htext fun l hl => (h l).of_le (by exact_mod_cast Nat.add_le_add_right hl 1)
  have hbase : ∀ {k : ℕ}, ContDiffOn ℝ (k + 1) f U → IsSck (k + 1) E (ScBanach.const V) U f :=
    fun {k} h => hstrong fun m => h.comp (E.toBase m).contDiff.contDiffOn
      (E.mapsTo_toBase_lvlSet U m)
  refine ⟨htext, fun h k => ?_, fun h k => ?_, fun h => ?_, hstrong, hbase⟩
  · cases k with
    | zero => exact (htext (k := 0) fun l _ => h l).isSc0
    | succ k => exact htext fun l _ => h l
  · cases k with
    | zero => exact (hbase (k := 0) (h.of_le (by exact_mod_cast le_top))).isSc0
    | succ k => exact hbase (h.of_le (by exact_mod_cast le_top))
  · exact (hstrong (k := 0) fun m => by simpa using h m).isSc1

#rt_check RoundTrip.V1_19.A_to_B [Polyfold.corollary_1_2_5_text,
  Polyfold.IsScSmooth.of_contDiffOn_levels_finiteDimensional_text,
  Polyfold.IsScSmooth.of_contDiffOn_finiteDimensional, Polyfold.corollary_1_2_5_zero,
  Polyfold.corollary_1_2_5, Polyfold.corollary_1_2_5_base]
#rt_check RoundTrip.V1_19.B_to_A_quadrant [Polyfold.corollary_1_2_5_text,
  Polyfold.IsScSmooth.of_contDiffOn_levels_finiteDimensional_text,
  Polyfold.IsScSmooth.of_contDiffOn_finiteDimensional, Polyfold.corollary_1_2_5_zero,
  Polyfold.corollary_1_2_5, Polyfold.corollary_1_2_5_base]

end RoundTrip.V1_19
