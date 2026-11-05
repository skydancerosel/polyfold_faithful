import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_35

/-!
Round trip for V3_35 (Theorem 3.40).  `A` is the conjunction of the types of
`Polyfold.theorem_3_40_compactness`, `Polyfold.theorem_3_40_regularity`,
`Polyfold.IsSc0ContractionGerm.exists_lift`, `Polyfold.IsSc0ContractionGerm.isCompact_lift_image`
and `Polyfold.theorem_3_12_local` (no universe parameters).

`A → B`: `theorem_3_12_local` (in `A`) for B's basic germ `h` and the sc⁺-germ `s` (only its sc⁰
part is needed; a partial quadrant is closed) gives nested open `O(i) ∋ 0` in `E₀` with
`cl(S ∩ O(i)) = ι_i(K_i)`.  B's relatively open `O(m)` are `O(m) ∩ U₀` (`U₀ = G.U 0`, relatively
open in `C`): `S ∩ O(m) ∩ U₀ ⊆ S ∩ O(m)`, so its closure lies in the range of `ι_m`.
-/

namespace RoundTrip.V3_35
open Polyfold

/-- The project's statement: Theorem 3.40, its lifts, and the local Theorem 3.12. -/
def A : Prop :=
  type_of% @Polyfold.theorem_3_40_compactness ∧ type_of% @Polyfold.theorem_3_40_regularity ∧
    type_of% @Polyfold.IsSc0ContractionGerm.exists_lift ∧
    type_of% @Polyfold.IsSc0ContractionGerm.isCompact_lift_image ∧
    type_of% @Polyfold.theorem_3_12_local

theorem A_holds : A :=
  ⟨@Polyfold.theorem_3_40_compactness, @Polyfold.theorem_3_40_regularity,
    @Polyfold.IsSc0ContractionGerm.exists_lift, @Polyfold.IsSc0ContractionGerm.isCompact_lift_image,
    @Polyfold.theorem_3_12_local⟩

theorem A_to_B : A → B := by
  intro hA n N W Ct G h Bh s hPQ hh hs hs0 f S
  obtain ⟨O, hO, h0, hnest, hK⟩ := hA.2.2.2.2 hh hPQ.isClosed (hs 0) hs0
  obtain ⟨OG, hOG, hGU⟩ := G.relOpen 0
  rw [ScBanach.paramProd_lvlSet] at hGU
  refine ⟨fun m => O m ∩ G.U 0,
    fun m => ⟨⟨O m ∩ OG, (hO m).inter hOG, ?_⟩, ⟨h0 m, G.zero_mem 0⟩,
      fun x hx => ⟨hnest m hx.1, hx.2⟩⟩, fun x hx => hx.2, fun m x hx => ?_⟩
  · rw [hGU]
    ext x
    simp only [Set.mem_inter_iff]
    tauto
  · obtain ⟨K, -, hKeq⟩ := hK m
    have hsub : S ∩ (O m ∩ G.U 0) ⊆
        {x ∈ G.U 0 | h x + (ScBanach.paramProd (Fin N → ℝ) W).toBase 1 (s x) = 0} ∩ O m :=
      fun x hx => ⟨hx.1, hx.2.1⟩
    have hx' := closure_mono hsub hx.1
    rw [hKeq] at hx'
    obtain ⟨y, -, rfl⟩ := hx'
    exact ⟨hx.2, y, rfl⟩

#rt_check RoundTrip.V3_35.A_to_B [Polyfold.theorem_3_40_compactness,
  Polyfold.theorem_3_40_regularity, Polyfold.IsSc0ContractionGerm.exists_lift,
  Polyfold.IsSc0ContractionGerm.isCompact_lift_image, Polyfold.theorem_3_12_local]

end RoundTrip.V3_35
