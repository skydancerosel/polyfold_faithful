import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V16_18

set_option maxSynthPendingDepth 3

/-! Round trip for V16_18 (2021 Definition 16.2.3, p. 719; 2017: Definition 16.14: the tangent
polyfold `(T(Z, c), Tc)`).

The item lists the definitions `PolyfoldClass.tangentStructure` (`(TX, Tα)`) and
`PolyfoldClass.tangent` (`Tc`, the class of `(TX₀, Tα₀)`), vocabulary, and the theorems
`tangentStructure_equiv` (all `(TX, Tα)` are equivalent), `definition_16_2_3` (each `(TX, Tα)` lies
in `Tc`), `PolyfoldStructure.tangent_paracompact` (`|TX|` paracompact),
`PolyfoldStructure.tangent_isZhou` (`TX` satisfies (ZHOU)); `A` is the conjunction of their types
at universe `0` (`Z : Type`, `T(Z, c) : Type 1`).
`B` builds `(TX, Tα)` itself (`TStr`) from the three conditions of Definition 16.1.1 and states:
(1) the conditions hold; (2) all `TStr` are equivalent; (3) each lies in `c.tangent`.
`TStr c q hq h1 h2 h3` is `tangentStructure q hq` by definitional unfolding (all three
conditions are propositions, and `IsHomeomorph.homeomorph` depends only on the function).
* `A_to_B`: (1) from `tangent_paracompact`, `tangent_isZhou`, and
  `PolyfoldClass.isHomeomorph_tangentMap` (a non-item project lemma; `A` lists no statement that
  `Tα` is a homeomorphism, it sits inside the definition `tangentStructure`); (2) from
  `tangentStructure_equiv`; (3) from `definition_16_2_3`.
* `B_to_A`: `tangent_paracompact`, `tangent_isZhou` for `p` from `B` (1) with `c := ⟦p⟧`;
  `tangentStructure_equiv` from `B` (2); `definition_16_2_3` from `B` (3) (with the conditions
  from `B` (1)). -/

namespace RoundTrip.V16_18
open Polyfold

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.PolyfoldClass.tangentStructure_equiv.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.definition_16_2_3.{0}) ∧
  (type_of% @Polyfold.PolyfoldStructure.tangent_paracompact.{0}) ∧
  (type_of% @Polyfold.PolyfoldStructure.tangent_isZhou.{0})

theorem A_holds : A :=
  ⟨@Polyfold.PolyfoldClass.tangentStructure_equiv.{0},
    @Polyfold.PolyfoldClass.definition_16_2_3.{0},
    @Polyfold.PolyfoldStructure.tangent_paracompact.{0},
    @Polyfold.PolyfoldStructure.tangent_isZhou.{0}⟩

/-- `B`'s structure is the project's `tangentStructure`. -/
theorem TStr_eq {Z : Type} [TopologicalSpace Z] (c : PolyfoldClass Z) (q : PolyfoldStructure Z)
    (hq : ⟦q⟧ = c) h1 h2 h3 : TStr c q hq h1 h2 h3 = PolyfoldClass.tangentStructure q hq := rfl

theorem A_to_B : A → B := by
  rintro ⟨hequiv, hdef, hpara, hzhou⟩ Z _ c
  refine ⟨fun q hq => ⟨hpara q, hzhou q, PolyfoldClass.isHomeomorph_tangentMap q hq⟩,
    fun q hq h1 h2 h3 q' hq' h1' h2' h3' => ?_, fun q hq h1 h2 h3 => ?_⟩
  · rw [TStr_eq, TStr_eq]
    exact hequiv hq hq'
  · rw [TStr_eq]
    exact hdef q hq

theorem B_to_A : B → A := by
  intro hB
  refine ⟨@fun Z _ c p q hp hq => ?_, @fun Z _ c q hq => ?_, @fun Z _ p => ?_,
    @fun Z _ p => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := (hB Z c).1 p hp
    obtain ⟨h1', h2', h3'⟩ := (hB Z c).1 q hq
    exact (hB Z c).2.1 p hp h1 h2 h3 q hq h1' h2' h3'
  · obtain ⟨h1, h2, h3⟩ := (hB Z c).1 q hq
    exact (hB Z c).2.2 q hq h1 h2 h3
  · exact ((hB Z ⟦p⟧).1 p rfl).1
  · exact ((hB Z ⟦p⟧).1 p rfl).2.1

/-! ### The same proofs against a copy of the statement's definitions

`A`'s statement mentions the definitions `tangentStructure` and `tangent`, whose fields
`paracompact := q.tangent_paracompact` and `isZhou := q.tangent_isZhou` are the item's own
theorems, written as plain constants (Lean does not abstract them into `_proof_N`).  `B`'s
statement also mentions `c.tangent`.  So every term mentioning `A` or `B` reaches them: plain
`#rt_check` and `#rt_check_soft` both report them (recorded below with `#guard_msgs`).  To show that this is the only route, `A'` is `A` with these two
definitions replaced by copies whose proof fields come from the non-item lemmas
`theorem_8_1_15` and `proposition_8_1_16_2021`, and `B'` is `B` with `c.tangent` replaced by
the copy; `A' = A` and `B' = B` hold by `rfl`, and the same proofs, `A' → B'` and `B' → A'`,
pass plain `#rt_check`. -/

/-- Copy of `tangentStructure` with the proof fields from non-item lemmas. -/
noncomputable def tStr' {Z : Type} [TopologicalSpace Z] {c : PolyfoldClass Z}
    (q : PolyfoldStructure Z) (hq : ⟦q⟧ = c) : PolyfoldStructure c.TangentSpace where
  X := q.X.tangentAny
  paracompact := q.X.X.theorem_8_1_15 q.paracompact
  isZhou := q.X.X.proposition_8_1_16_2021 q.isZhou
  β := PolyfoldClass.tangentHomeomorph q hq

/-- `A` with `tangentStructure`, `tangent` replaced by the copies. -/
def A' : Prop :=
  (∀ {Z : Type} [TopologicalSpace Z] {c : PolyfoldClass Z} {p q : PolyfoldStructure Z}
      (hp : ⟦p⟧ = c) (hq : ⟦q⟧ = c), PolyfoldStructure.Equiv (tStr' p hp) (tStr' q hq)) ∧
  (∀ {Z : Type} [TopologicalSpace Z] {c : PolyfoldClass Z} (q : PolyfoldStructure Z)
      (hq : ⟦q⟧ = c),
      (⟦tStr' q hq⟧ : PolyfoldClass c.TangentSpace) = ⟦tStr' c.out (Quotient.out_eq c)⟧) ∧
  (∀ {Z : Type} [TopologicalSpace Z] (p : PolyfoldStructure Z),
      p.X.tangentAny.X.HasParacompactOrbitSpace) ∧
  (∀ {Z : Type} [TopologicalSpace Z] (p : PolyfoldStructure Z), p.X.tangentAny.X.IsZhou)

set_option maxHeartbeats 100000 in
/-- `A'` is `A` (definitional unfolding and proof irrelevance). -/
theorem A'_eq : A' = A := rfl

set_option maxHeartbeats 100000 in
/-- `B` with `c.tangent` replaced by the copy (`B`'s statement also mentions `tangent`). -/
def B' : Prop :=
  ∀ (Z : Type) [TopologicalSpace Z] (c : PolyfoldClass Z),
    (∀ (q : PolyfoldStructure Z) (hq : ⟦q⟧ = c),
      q.X.tangentAny.X.HasParacompactOrbitSpace ∧ q.X.tangentAny.X.IsZhou ∧
        IsHomeomorph (PolyfoldClass.tangentMap q hq)) ∧
    (∀ (q : PolyfoldStructure Z) (hq : ⟦q⟧ = c) h1 h2 h3
        (q' : PolyfoldStructure Z) (hq' : ⟦q'⟧ = c) h1' h2' h3',
      (TStr c q hq h1 h2 h3).Equiv (TStr c q' hq' h1' h2' h3')) ∧
    (∀ (q : PolyfoldStructure Z) (hq : ⟦q⟧ = c) h1 h2 h3,
      (⟦TStr c q hq h1 h2 h3⟧ : PolyfoldClass c.TangentSpace) =
        ⟦tStr' c.out (Quotient.out_eq c)⟧)

set_option maxHeartbeats 100000 in
/-- `B'` is `B`. -/
theorem B'_eq : B' = B := rfl

set_option maxHeartbeats 100000 in
theorem A'_to_B' : A' → B' := by
  rintro ⟨hequiv, hdef, hpara, hzhou⟩ Z _ c
  exact ⟨fun q hq => ⟨hpara q, hzhou q, PolyfoldClass.isHomeomorph_tangentMap q hq⟩,
    fun q hq _ _ _ q' hq' _ _ _ => hequiv hq hq', fun q hq _ _ _ => hdef q hq⟩

set_option maxHeartbeats 100000 in
theorem B'_to_A' : B' → A' := by
  intro hB
  refine ⟨@fun Z _ c p q hp hq => ?_, @fun Z _ c q hq => ?_, @fun Z _ p => ?_,
    @fun Z _ p => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := (hB Z c).1 p hp
    obtain ⟨h1', h2', h3'⟩ := (hB Z c).1 q hq
    exact (hB Z c).2.1 p hp h1 h2 h3 q hq h1' h2' h3'
  · obtain ⟨h1, h2, h3⟩ := (hB Z c).1 q hq
    exact (hB Z c).2.2 q hq h1 h2 h3
  · exact ((hB Z ⟦p⟧).1 p rfl).1
  · exact ((hB Z ⟦p⟧).1 p rfl).2.1

/--
error: rt_check FAIL: RoundTrip.V16_18.A_to_B uses [Polyfold.PolyfoldStructure.tangent_paracompact,
 Polyfold.PolyfoldStructure.tangent_isZhou]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V16_18.A_to_B [Polyfold.PolyfoldClass.tangentStructure_equiv,
  Polyfold.PolyfoldClass.definition_16_2_3, Polyfold.PolyfoldStructure.tangent_paracompact,
  Polyfold.PolyfoldStructure.tangent_isZhou]
/--
error: rt_check FAIL: RoundTrip.V16_18.B_to_A uses [Polyfold.PolyfoldStructure.tangent_paracompact,
 Polyfold.PolyfoldStructure.tangent_isZhou]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V16_18.B_to_A [Polyfold.PolyfoldClass.tangentStructure_equiv,
  Polyfold.PolyfoldClass.definition_16_2_3, Polyfold.PolyfoldStructure.tangent_paracompact,
  Polyfold.PolyfoldStructure.tangent_isZhou]
/--
error: rt_check_soft FAIL: RoundTrip.V16_18.A_to_B uses [Polyfold.PolyfoldStructure.tangent_paracompact,
 Polyfold.PolyfoldStructure.tangent_isZhou]
-/
#guard_msgs (whitespace := lax) in
#rt_check_soft RoundTrip.V16_18.A_to_B [Polyfold.PolyfoldClass.tangentStructure_equiv,
  Polyfold.PolyfoldClass.definition_16_2_3, Polyfold.PolyfoldStructure.tangent_paracompact,
  Polyfold.PolyfoldStructure.tangent_isZhou]
/--
error: rt_check_soft FAIL: RoundTrip.V16_18.B_to_A uses [Polyfold.PolyfoldStructure.tangent_paracompact,
 Polyfold.PolyfoldStructure.tangent_isZhou]
-/
#guard_msgs (whitespace := lax) in
#rt_check_soft RoundTrip.V16_18.B_to_A [Polyfold.PolyfoldClass.tangentStructure_equiv,
  Polyfold.PolyfoldClass.definition_16_2_3, Polyfold.PolyfoldStructure.tangent_paracompact,
  Polyfold.PolyfoldStructure.tangent_isZhou]
#rt_check RoundTrip.V16_18.A'_to_B' [Polyfold.PolyfoldClass.tangentStructure_equiv,
  Polyfold.PolyfoldClass.definition_16_2_3, Polyfold.PolyfoldStructure.tangent_paracompact,
  Polyfold.PolyfoldStructure.tangent_isZhou]
#rt_check RoundTrip.V16_18.B'_to_A' [Polyfold.PolyfoldClass.tangentStructure_equiv,
  Polyfold.PolyfoldClass.definition_16_2_3, Polyfold.PolyfoldStructure.tangent_paracompact,
  Polyfold.PolyfoldStructure.tangent_isZhou]
#rt_overlap RoundTrip.V16_18.B_to_A [Polyfold.PolyfoldClass.tangentStructure_equiv,
  Polyfold.PolyfoldClass.definition_16_2_3, Polyfold.PolyfoldStructure.tangent_paracompact,
  Polyfold.PolyfoldStructure.tangent_isZhou]
#rt_overlap RoundTrip.V16_18.B'_to_A' [Polyfold.PolyfoldClass.tangentStructure_equiv,
  Polyfold.PolyfoldClass.definition_16_2_3, Polyfold.PolyfoldStructure.tangent_paracompact,
  Polyfold.PolyfoldStructure.tangent_isZhou]

end RoundTrip.V16_18
