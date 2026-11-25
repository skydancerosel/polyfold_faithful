import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V16_8

set_option maxSynthPendingDepth 3

/-! Round trip for V16_8 (2021 Lemma 16.1.13, p. 712; 2017: Lemma 16.1: the degeneracy index of a
polyfold structure does not depend on the structure).

The item lists the definition `PolyfoldStructure.degIndex` (`d_{(X,β)} = d_{|X|} ∘ β⁻¹`,
vocabulary) and the theorems `degIndex_eq` (`d_{(X,β)}(z) = d_X(x)` whenever `β(|x|) = z`) and
`lemma_16_1_13` (`p ∼ q ⇒ d_p = d_q`); `A` is the conjunction of their types at universe `0`.
`B` states the lemma through the defining formula: `p ∼ q`, `β_p(|x|) = β_q(|x'|)` ⇒
`d_X(x) = d_{X'}(x')`.
* `A_to_B`: `degIndex_eq` on both sides and `lemma_16_1_13`.
* `B_to_A`: `degIndex_eq` from `B` with `p ∼ p` (`Equiv.refl`): `d_{(X,β)}(z) = d_X(x₀)` for a
  representative `x₀` of `β⁻¹ z` (by the definition, `degIndexOrbit_π` is `rfl`), and `B` compares
  `x₀` with `x`.  `lemma_16_1_13` from `B` with representatives of `β_p⁻¹ z` and `β_q⁻¹ z`. -/

namespace RoundTrip.V16_8
open Polyfold

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.PolyfoldStructure.degIndex_eq.{0}) ∧
  (type_of% @Polyfold.PolyfoldStructure.lemma_16_1_13.{0})

theorem A_holds : A :=
  ⟨@Polyfold.PolyfoldStructure.degIndex_eq.{0}, @Polyfold.PolyfoldStructure.lemma_16_1_13.{0}⟩

theorem A_to_B : A → B := by
  rintro ⟨hdeg, hlem⟩ Z _ s t h x x' hxx'
  rw [← hdeg s (rfl : s.β (s.X.X.π x) = _), ← hdeg t (rfl : t.β (t.X.X.π x') = _),
    hlem h]
  exact congrArg t.degIndex hxx'

/-- From `B`: `d_{(X,β)}(z) = d_X(x)` for `β(|x|) = z`. -/
theorem degIndex_eq_of_B (hB : B) {Z : Type} [TopologicalSpace Z] (p : PolyfoldStructure Z)
    {x : p.X.Obj} {z : Z} (h : p.β (p.X.X.π x) = z) : p.degIndex z = p.X.X.PObj.degIndex x := by
  obtain ⟨x₀, hx₀⟩ := Quotient.exists_rep (p.β.symm z)
  have e : p.degIndex z = p.X.X.PObj.degIndex x₀ := by
    change p.X.X.degIndexOrbit (p.β.symm z) = _
    rw [← hx₀]
    rfl
  rw [e]
  refine hB Z p p (PolyfoldStructure.Equiv.refl p) x₀ x ?_
  change p.β ⟦x₀⟧ = p.β (p.X.X.π x)
  rw [hx₀, h, Homeomorph.apply_symm_apply]

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun p x z h => degIndex_eq_of_B hB p h, @fun Z _ p q h => ?_⟩
  funext z
  obtain ⟨x, hx⟩ := Quotient.exists_rep (p.β.symm z)
  obtain ⟨x', hx'⟩ := Quotient.exists_rep (q.β.symm z)
  have h1 : p.β (p.X.X.π x) = z := by
    change p.β ⟦x⟧ = z
    rw [hx, Homeomorph.apply_symm_apply]
  have h2 : q.β (q.X.X.π x') = z := by
    change q.β ⟦x'⟧ = z
    rw [hx', Homeomorph.apply_symm_apply]
  rw [degIndex_eq_of_B hB p h1, degIndex_eq_of_B hB q h2]
  exact hB _ p q h x x' (h1.trans h2.symm)

/-! ### The main conjunct alone (`lemma_16_1_13`) -/

/-- The main conjunct. -/
def Amain : Prop := type_of% @Polyfold.PolyfoldStructure.lemma_16_1_13.{0}

/-- `d_{(X,β)}(β(|x|)) = d_X(x)`, by the definition (`degIndexOrbit_π` is `rfl`). -/
theorem degIndex_apply {Z : Type} [TopologicalSpace Z] (p : PolyfoldStructure Z) (x : p.X.Obj) :
    p.degIndex (p.β (p.X.X.π x)) = p.X.X.PObj.degIndex x := by
  change p.X.X.degIndexOrbit (p.β.symm (p.β (p.X.X.π x))) = _
  rw [Homeomorph.symm_apply_apply]
  rfl

theorem Amain_to_B : Amain → B := by
  intro hA Z _ s t h x x' hxx'
  rw [← degIndex_apply s x, ← degIndex_apply t x', hA h]
  exact congrArg t.degIndex hxx'

theorem B_to_Amain : B → Amain := fun hB => (B_to_A hB).2

#rt_check RoundTrip.V16_8.A_to_B [Polyfold.PolyfoldStructure.degIndex_eq,
  Polyfold.PolyfoldStructure.lemma_16_1_13]
#rt_check RoundTrip.V16_8.B_to_A [Polyfold.PolyfoldStructure.degIndex_eq,
  Polyfold.PolyfoldStructure.lemma_16_1_13]
#rt_check RoundTrip.V16_8.Amain_to_B [Polyfold.PolyfoldStructure.degIndex_eq,
  Polyfold.PolyfoldStructure.lemma_16_1_13]
#rt_check RoundTrip.V16_8.B_to_Amain [Polyfold.PolyfoldStructure.degIndex_eq,
  Polyfold.PolyfoldStructure.lemma_16_1_13]
#rt_overlap RoundTrip.V16_8.B_to_A [Polyfold.PolyfoldStructure.degIndex_eq,
  Polyfold.PolyfoldStructure.lemma_16_1_13]

end RoundTrip.V16_8
