import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V1_3

/-! Round trip for V1_3 (Definition 1.4: sc⁺-operators, and their sc-compactness).

`A` is the conjunction of the types of the theorems `ScPlus.isCompactOperator` and
`ScPlus.toScOperator_mem_range_toBase_succ` (no universe parameters); `ScPlus`,
`ScBanach.shiftIncl`, `ScPlus.toScOperator` are vocabulary.  `B` says (1) the project's `ScPlus`
is the text's sc⁺-operator and (2) every sc⁺-operator is sc-compact.

* `A → B` (proved): (1) both directions are glue (the text's level maps `S_m : E_m → F_{m+1}` are
  automatically linear and commute with the inclusions, since `F_{m+1} → F₀` is injective);
  (2) is `A`'s `isCompactOperator` applied to the `ScPlus` given by (1).
* `B → A` (proved): `isCompactOperator` from `B`'s (1) ⇒ and (2); the level-raising property from
  `B`'s (1) ⇒. -/

namespace RoundTrip.V1_3
open Polyfold

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.ScPlus.isCompactOperator) ∧
    (type_of% @Polyfold.ScPlus.toScOperator_mem_range_toBase_succ)

theorem A_holds : A :=
  ⟨@Polyfold.ScPlus.isCompactOperator, @Polyfold.ScPlus.toScOperator_mem_range_toBase_succ⟩

section Glue

variable {E F : ScBanach}

/-- The level map `E_m → F_{m+1}` of a text sc⁺-operator, as a continuous linear map. -/
noncomputable def plusLin (S : E.lvl 0 →ₗ[ℝ] F.lvl 0) {m : ℕ} (Sm : E.lvl m → F.lvl (m + 1))
    (h : ∀ x, F.toBase (m + 1) (Sm x) = S (E.toBase m x)) (hc : Continuous Sm) :
    E.lvl m →L[ℝ] F.lvl (m + 1) where
  toFun := Sm
  map_add' x y := F.toBase_injective (m + 1) (by simp only [map_add, h])
  map_smul' c x := F.toBase_injective (m + 1) (by simp only [map_smul, h, RingHom.id_apply])
  cont := hc

/-- The project's `ScPlus` of a text sc⁺-operator. -/
noncomputable def ofText {S : E.lvl 0 →ₗ[ℝ] F.lvl 0} (h : IsScPlusText S) : ScPlus E F where
  lvl m := plusLin S (h.2 m).choose (h.2 m).choose_spec.1 (h.2 m).choose_spec.2
  incl_comm m x := by
    apply F.toBase_injective (m + 1)
    change F.toBase (m + 1 + 1) ((h.2 (m + 1)).choose x) = F.toBase (m + 1) ((h.2 m).choose _)
    rw [(h.2 (m + 1)).choose_spec.1, (h.2 m).choose_spec.1]
    rfl

theorem ofText_toScOperator {S : E.lvl 0 →ₗ[ℝ] F.lvl 0} (h : IsScPlusText S) (x : E.lvl 0) :
    (ofText h).toScOperator.lvl 0 x = S x :=
  (h.2 0).choose_spec.1 x

theorem text_of_scPlus {S : E.lvl 0 →ₗ[ℝ] F.lvl 0} (S' : ScPlus E F)
    (hS' : ∀ x, S'.toScOperator.lvl 0 x = S x) : IsScPlusText S := by
  refine ⟨fun m => ⟨S'.toScOperator.lvl m, fun x => ?_, (S'.toScOperator.lvl m).continuous⟩,
    fun m => ⟨S'.lvl m, fun x => ?_, (S'.lvl m).continuous⟩⟩
  · rw [ScOperator.toBase_comm, hS']
  · rw [ScScale.toBase_succ]
    change F.toBase m (S'.toScOperator.lvl m x) = _
    rw [ScOperator.toBase_comm, hS']

end Glue

theorem A_to_B : A → B := by
  intro hA
  refine ⟨fun E F S => ⟨fun ⟨S', hS'⟩ => text_of_scPlus S' hS', fun h =>
    ⟨ofText h, ofText_toScOperator h⟩⟩, fun E F S h => fun m => ?_⟩
  refine ⟨(ofText h).toScOperator.lvl m, fun x => ?_, hA.1 (ofText h) m⟩
  rw [ScOperator.toBase_comm, ofText_toScOperator]

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun {E F} S m => ?_, fun {E F} S m x hx => ?_⟩
  · obtain ⟨Sm, h1, h2⟩ := (hB.2 E F _ ((hB.1 E F (S.toScOperator.lvl 0 :
      E.lvl 0 →ₗ[ℝ] F.lvl 0)).1 ⟨S, fun _ => rfl⟩)) m
    have : Sm = S.toScOperator.lvl m := funext fun x => F.toBase_injective m (by
      rw [h1, ScOperator.toBase_comm]; rfl)
    rwa [this] at h2
  · obtain ⟨y, rfl⟩ := hx
    obtain ⟨-, h2⟩ := (hB.1 E F (S.toScOperator.lvl 0 : E.lvl 0 →ₗ[ℝ] F.lvl 0)).1
      ⟨S, fun _ => rfl⟩
    obtain ⟨Sm, h, -⟩ := h2 m
    exact ⟨Sm y, h y⟩

#rt_check RoundTrip.V1_3.A_to_B [Polyfold.ScPlus.isCompactOperator,
  Polyfold.ScPlus.toScOperator_mem_range_toBase_succ]
#rt_check RoundTrip.V1_3.B_to_A [Polyfold.ScPlus.isCompactOperator,
  Polyfold.ScPlus.toScOperator_mem_range_toBase_succ]
#rt_overlap RoundTrip.V1_3.B_to_A [Polyfold.ScPlus.isCompactOperator,
  Polyfold.ScPlus.toScOperator_mem_range_toBase_succ]

end RoundTrip.V1_3
