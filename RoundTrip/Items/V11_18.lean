import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V11_18

/-!
Round trip for V11_18 (2021 Theorem 11.3.3, p. 537: branched ep⁺-subgroupoids under generalized
isomorphisms).

The item lists ten theorems; `A` is the conjunction of their types, universes at `0`
(`X Y : EP.{0}`): `theorem_11_3_3_one` … `_six` for `EPLoc.pushTheta f`, `EPLoc.pullTheta f`
(computed on the chosen representative `rep f`), `isNDimensional_pushTheta`,
`isNDimensional_pullTheta`, `orbitSupp_pushTheta` and the counterexample
`not_proposition_9_1_11_rn` (no universe parameter).  (3)–(5) and the `n`-dimensionality are
stated for merely functorial `Θ`, `Θ'`; (6) for any dimensional decomposition (no separate
branched hypothesis on `Θ`).

`B`: for every generalized isomorphism `f` and **every** representative `d` of `f`, `Thm1133B` for
`d.pushTheta`, `d.pullTheta` (for branched `Θ`, `Θ'`).

* `A ⇒ B` (`A_to_B`): `d.Φ` is an equivalence (non-item `theorem_10_3_10`), so the non-item
  `pushTheta_homMk`, `pullTheta_homMk` (V11_16) identify `d.pushTheta Θ`, `d.pullTheta Θ'` with
  `EPLoc.pushTheta f Θ`, `EPLoc.pullTheta f Θ'` for functorial `Θ`, `Θ'`; then each conjunct of
  `B` is a conjunct of `A`.
* `B ⇒ A` fails for a genuine reason (`A` is more general): `theorem_11_3_3_three/four/five` and
  `isNDimensional_push/pullTheta` hold for every **functorial** `Θ` (resp. `Θ'`), not only for
  branched ones, and `B` says nothing about non-branched functors; `orbitSupp_pushTheta`
  (`|supp f_*Θ| = |f|(|supp Θ|)`) and the counterexample to the uniqueness in Proposition 9.1.11
  are not in `B`.  `B` does give (1), (2) and, for branched `Θ`, (3)–(6) (`B_to_A_core`).
-/

namespace RoundTrip.V11_18
open Polyfold Polyfold.EPLocalization CategoryTheory

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  type_of% @Polyfold.EPLocalization.EPLoc.theorem_11_3_3_one.{0} ∧
  type_of% @Polyfold.EPLocalization.EPLoc.theorem_11_3_3_two.{0} ∧
  type_of% @Polyfold.EPLocalization.EPLoc.theorem_11_3_3_three.{0} ∧
  type_of% @Polyfold.EPLocalization.EPLoc.theorem_11_3_3_four.{0} ∧
  type_of% @Polyfold.EPLocalization.EPLoc.theorem_11_3_3_five.{0} ∧
  type_of% @Polyfold.EPLocalization.EPLoc.theorem_11_3_3_six.{0} ∧
  type_of% @Polyfold.EPLocalization.EPLoc.isNDimensional_pushTheta.{0} ∧
  type_of% @Polyfold.EPLocalization.EPLoc.isNDimensional_pullTheta.{0} ∧
  type_of% @Polyfold.EPLocalization.EPLoc.orbitSupp_pushTheta.{0} ∧
  type_of% @Polyfold.EpGroupoid.not_proposition_9_1_11_rn

theorem A_holds : A :=
  ⟨@EPLoc.theorem_11_3_3_one, @EPLoc.theorem_11_3_3_two, @EPLoc.theorem_11_3_3_three,
    @EPLoc.theorem_11_3_3_four, @EPLoc.theorem_11_3_3_five, @EPLoc.theorem_11_3_3_six,
    @EPLoc.isNDimensional_pushTheta, @EPLoc.isNDimensional_pullTheta, @EPLoc.orbitSupp_pushTheta,
    EpGroupoid.not_proposition_9_1_11_rn⟩

theorem A_to_B : A → B := by
  rintro ⟨h1, h2, h3, h4, h5, h6, -, -, -, -⟩
  intro X Y f hf d hd
  have hΦ : d.Φ.IsEquivalence := (EPLoc.theorem_10_3_10 d).1.1 (hd ▸ hf)
  have epush : ∀ Θ : X.Obj → ℚ, X.X.IsFunctorial Θ → d.pushTheta Θ = EPLoc.pushTheta f Θ :=
    fun Θ hΘ => by rw [← hd, EPLoc.pushTheta_homMk d hΦ hΘ]
  have epull : ∀ Θ' : Y.Obj → ℚ, Y.X.IsFunctorial Θ' → d.pullTheta Θ' = EPLoc.pullTheta f Θ' :=
    fun Θ' hΘ' => by rw [← hd, EPLoc.pullTheta_homMk d hΘ']
  refine ⟨fun Θ hΘ => ?_, fun Θ' hΘ' => ?_, fun Θ hΘ hc => ?_, fun Θ' hΘ' hc => ?_,
    fun Θ hΘ hc => ?_, fun Θ' hΘ' hc => ?_, fun Θ hΘ hc => ?_, fun Θ' hΘ' hc => ?_,
    fun Θ hΘ hc => ?_, fun Θ' hΘ' hc => ?_, fun Θ Θk hΘ hc => ?_, fun Θ' Θk hΘ' hc => ?_⟩
  · rw [epush Θ hΘ.isFunctorial]; exact h1 hf hΘ
  · rw [epull Θ' hΘ'.isFunctorial]; exact h2 hf hΘ'
  · rw [epush Θ hΘ.isFunctorial]
    exact (h3 hf (Θ' := fun _ => 0) hΘ.isFunctorial (fun _ => rfl)).1 hc
  · rw [epull Θ' hΘ'.isFunctorial]
    exact (h3 hf (Θ := fun _ => 0) (fun _ => rfl) hΘ'.isFunctorial).2 hc
  · rw [epush Θ hΘ.isFunctorial]
    exact (h4 hf (Θ' := fun _ => 0) hΘ.isFunctorial (fun _ => rfl)).1 hc
  · rw [epull Θ' hΘ'.isFunctorial]
    exact (h4 hf (Θ := fun _ => 0) (fun _ => rfl) hΘ'.isFunctorial).2 hc
  · rw [epush Θ hΘ.isFunctorial]
    exact (h5 hf (Θ' := fun _ => 0) hΘ.isFunctorial (fun _ => rfl)).1 hc
  · rw [epull Θ' hΘ'.isFunctorial]
    exact (h5 hf (Θ := fun _ => 0) (fun _ => rfl) hΘ'.isFunctorial).2.1 hc
  · rw [epush Θ hΘ.isFunctorial]
    exact (h5 hf (Θ' := fun _ => 0) hΘ.isFunctorial (fun _ => rfl)).2.2.1 hc
  · rw [epull Θ' hΘ'.isFunctorial]
    exact (h5 hf (Θ := fun _ => 0) (fun _ => rfl) hΘ'.isFunctorial).2.2.2 hc
  · have hk : (fun k => d.pushTheta (Θk k)) = fun k => EPLoc.pushTheta f (Θk k) :=
      funext fun k => epush _ (hc.isBranched k).isFunctorial
    rw [epush Θ hΘ.isFunctorial, hk]
    exact (h6 hf).1 hc
  · have hk : (fun k => d.pullTheta (Θk k)) = fun k => EPLoc.pullTheta f (Θk k) :=
      funext fun k => epull _ (hc.isBranched k).isFunctorial
    rw [epull Θ' hΘ'.isFunctorial, hk]
    exact (h6 hf).2 hc

/-- What `B` gives: (1) and (2) of `A` (on the representative `rep f`). -/
theorem B_to_A_core (hB : B) :
    type_of% @Polyfold.EPLocalization.EPLoc.theorem_11_3_3_one.{0} ∧
    type_of% @Polyfold.EPLocalization.EPLoc.theorem_11_3_3_two.{0} :=
  ⟨fun {X Y f} hf {Θ} hΘ => (hB X Y f hf (EPLoc.rep f) (EPLoc.homMk_rep f)).1 Θ hΘ,
    fun {X Y f} hf {Θ'} hΘ' => (hB X Y f hf (EPLoc.rep f) (EPLoc.homMk_rep f)).2.1 Θ' hΘ'⟩

#rt_check RoundTrip.V11_18.A_to_B [Polyfold.EPLocalization.EPLoc.theorem_11_3_3_one,
  Polyfold.EPLocalization.EPLoc.theorem_11_3_3_two,
  Polyfold.EPLocalization.EPLoc.theorem_11_3_3_three,
  Polyfold.EPLocalization.EPLoc.theorem_11_3_3_four,
  Polyfold.EPLocalization.EPLoc.theorem_11_3_3_five,
  Polyfold.EPLocalization.EPLoc.theorem_11_3_3_six,
  Polyfold.EPLocalization.EPLoc.isNDimensional_pushTheta,
  Polyfold.EPLocalization.EPLoc.isNDimensional_pullTheta,
  Polyfold.EPLocalization.EPLoc.orbitSupp_pushTheta,
  Polyfold.EpGroupoid.not_proposition_9_1_11_rn]
#rt_check RoundTrip.V11_18.B_to_A_core [Polyfold.EPLocalization.EPLoc.theorem_11_3_3_one,
  Polyfold.EPLocalization.EPLoc.theorem_11_3_3_two,
  Polyfold.EPLocalization.EPLoc.theorem_11_3_3_three,
  Polyfold.EPLocalization.EPLoc.theorem_11_3_3_four,
  Polyfold.EPLocalization.EPLoc.theorem_11_3_3_five,
  Polyfold.EPLocalization.EPLoc.theorem_11_3_3_six,
  Polyfold.EPLocalization.EPLoc.isNDimensional_pushTheta,
  Polyfold.EPLocalization.EPLoc.isNDimensional_pullTheta,
  Polyfold.EPLocalization.EPLoc.orbitSupp_pushTheta,
  Polyfold.EpGroupoid.not_proposition_9_1_11_rn]
#rt_overlap RoundTrip.V11_18.A_to_B [Polyfold.EPLocalization.EPLoc.theorem_11_3_3_one,
  Polyfold.EPLocalization.EPLoc.theorem_11_3_3_two,
  Polyfold.EPLocalization.EPLoc.theorem_11_3_3_three,
  Polyfold.EPLocalization.EPLoc.theorem_11_3_3_four,
  Polyfold.EPLocalization.EPLoc.theorem_11_3_3_five,
  Polyfold.EPLocalization.EPLoc.theorem_11_3_3_six,
  Polyfold.EPLocalization.EPLoc.isNDimensional_pushTheta,
  Polyfold.EPLocalization.EPLoc.isNDimensional_pullTheta,
  Polyfold.EPLocalization.EPLoc.orbitSupp_pushTheta,
  Polyfold.EpGroupoid.not_proposition_9_1_11_rn]

end RoundTrip.V11_18
