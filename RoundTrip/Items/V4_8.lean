import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_8

/-!
Round trip for V4_8 (proof of Lemma 4.7 (ii): `Dr(o)` is an sc⁺-operator, compact on every level,
and a projection with finite-dimensional image).  `A` is the conjunction of the types of
`Polyfold.IsScPlus.exists_scPlus_deriv`, `Polyfold.IsScPlus.isCompactOperator_deriv` and
`Polyfold.finiteDimensional_range_of_isCompactOperator_of_idem` (the last one has a universe
parameter, instantiated at `0`).

A ⇒ B: at `o₁` with `ι₁ o₁ ∈ O`, `o₁` is smooth (Lemma 4.7 (i), `lemma_4_7_i`) and lies in `U₁`;
A's sc⁺-operator `S : E → E¹` gives B's level maps `E_m → E_{m+1}` and `E_m → E_m`
(`ScOperator.toBase_comm`), A gives compactness, and A's Riesz lemma applied to the idempotent
`Dr(o)` (`ScRetraction.scDeriv_comp_self`) gives the finite-dimensional range.

B ⇒ A is not proved: A is stated for arbitrary sc⁺-maps `f : U → F` on an sc-domain and every
smooth `x ∈ U₁`, and its third conjunct is the Riesz lemma for any normed space; B only speaks of
sc⁺-retractions at points of their image.  `B_to_A_retraction` shows that B does give A's first
two conjuncts for `f = r` an sc⁺-retraction at `o ∈ O` (rebuilding an `ScPlus` operator from B's
level maps).
-/

namespace RoundTrip.V4_8
open Polyfold

def A : Prop :=
  type_of% @Polyfold.IsScPlus.exists_scPlus_deriv ∧
  type_of% @Polyfold.IsScPlus.isCompactOperator_deriv ∧
  type_of% @Polyfold.finiteDimensional_range_of_isCompactOperator_of_idem.{0}

theorem A_holds : A :=
  ⟨@Polyfold.IsScPlus.exists_scPlus_deriv, @Polyfold.IsScPlus.isCompactOperator_deriv,
    @Polyfold.finiteDimensional_range_of_isCompactOperator_of_idem.{0}⟩

theorem A_to_B : A → B := by
  rintro ⟨-, hA2, hA3⟩ E C r hr o₁ ho
  have hr' : IsScPlus r.U r := hr
  have hs : o₁ ∈ E.smoothLvl 1 := lemma_4_7_i hr ho
  have hoU : o₁ ∈ E.lvlSet r.U 1 := r.retract_subset ho
  obtain ⟨hc, S, hS, hSc⟩ := hA2 r.isScDomain hr' hoU hs
  refine ⟨fun m => ⟨S m, fun x => ?_⟩, fun m => ⟨S.toScOperator m, fun x => ?_, hSc m⟩, ?_⟩
  · rw [ScScale.toBase_succ, ← hS, ← ScOperator.toBase_comm]
    rfl
  · rw [ScOperator.toBase_comm, hS]
  · exact hA3 _ hc fun v =>
      congrArg (fun L : E 0 →L[ℝ] E 0 => L v) (r.scDeriv_comp_self ho)

/-- What B does give: A's first two conjuncts for `f = r` an sc⁺-retraction, at points of the
retract (B ⇒ restricted A). -/
theorem B_to_A_retraction (hB : B) {E : ScBanach} {C : Set (E 0)} (r : ScRetraction E C)
    (hr : r.IsScPlus) (o₁ : E 1) (ho : E.toBase 1 o₁ ∈ r.retract) :
    (∃ S : ScPlus E E, ∀ v, S.toScOperator 0 v = scDeriv r.U r o₁ v) ∧
    (IsCompactOperator (scDeriv r.U r o₁) ∧
      ∃ S : ScPlus E E, (∀ v, S.toScOperator 0 v = scDeriv r.U r o₁ v) ∧
        ∀ m, IsCompactOperator (S.toScOperator m)) := by
  obtain ⟨hP, hK, -⟩ := hB E C r hr o₁ ho
  set T := scDeriv r.U r.toFun o₁ with hT
  choose S' hS' using hP
  let S : ScPlus E E :=
    { lvl := fun m => S' m
      incl_comm := fun m x => by
        apply E.toBase_injective (m + 1)
        change E.toBase (m + 1) (E.incl (m + 1) (S' (m + 1) x)) = E.toBase (m + 1) (S' m (E.incl m x))
        rw [← ScScale.toBase_succ, hS', hS', ScScale.toBase_succ] }
  have hS0 : ∀ v, S.toScOperator 0 v = T v := fun v => by
    have := hS' 0 v
    rw [ScScale.toBase_succ] at this
    exact this
  refine ⟨⟨S, hS0⟩, ?_, S, hS0, fun m => S.isCompactOperator m⟩
  obtain ⟨K, hK1, hK2⟩ := hK 0
  have : (K : E 0 → E 0) = T := funext fun x => hK1 x
  change IsCompactOperator (T : E 0 → E 0)
  rw [← this]
  exact hK2

#rt_check RoundTrip.V4_8.A_to_B [Polyfold.IsScPlus.exists_scPlus_deriv, Polyfold.IsScPlus.isCompactOperator_deriv, Polyfold.finiteDimensional_range_of_isCompactOperator_of_idem]
#rt_check RoundTrip.V4_8.B_to_A_retraction [Polyfold.IsScPlus.exists_scPlus_deriv, Polyfold.IsScPlus.isCompactOperator_deriv, Polyfold.finiteDimensional_range_of_isCompactOperator_of_idem]
#rt_overlap RoundTrip.V4_8.B_to_A_retraction [Polyfold.IsScPlus.exists_scPlus_deriv, Polyfold.IsScPlus.isCompactOperator_deriv, Polyfold.finiteDimensional_range_of_isCompactOperator_of_idem]

end RoundTrip.V4_8
