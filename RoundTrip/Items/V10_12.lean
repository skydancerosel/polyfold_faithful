import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_12

/-! Round trip for V10_12 (2021 Example 10.1.15, p. 474; 2017: Example 10.1, p. 341: for
`X = ℤ/4 ⋉ ℝ`, `Y = ℤ/4 ⋉ ℝ²` and `Φ` the functor to the origin, `Φ` does not induce a map
`𝐗^R → 𝐘^R`).

The item lists the definitions `example1015X`, `example1015Y`, `example1015Functor` (vocabulary)
and five theorems (no universes); `A` is the conjunction of their types:
* `example1015X_two_mem_nonEffectivePart`: `(2, x) ∈ 𝐗^T` for every `x`;
* `example1015Y_two_not_mem_nonEffectivePart`: `(2, 0) ∉ 𝐘^T`;
* `example1015X_reducedπ_one_eq_three`: `[(1, x)] = [(3, x)]` in `𝐗^R`;
* `example1015Y_reducedπ_one_ne_three`: `[(1, 0)] ≠ [(3, 0)]` in `𝐘^R`;
* `example_10_1_15`: no `f : 𝐗^R → 𝐘^R` with `f [φ] = [Φ φ]` (B's claim, verbatim).

`B` pins down the example (structure maps with the actions `(-1)^i` on `ℝ` and rotation by
`i · 90°` on `ℝ²`, units, object M-polyfolds `rnPolyfold 1`, `rnPolyfold 2`, `Φ(x) = 0`,
`Φ(i, x) = (i, 0)`) and states the non-existence of `f`.

* `A_to_B`: the pinning equations hold by `rfl`, except the target map of `X`, which is
  `z4Sign i • x` (`z4Sign i = ±1 ∈ ℤˣ`) and is matched with B's `if … then x else -x` by
  unfolding `z4Sign`; the claim is `example_10_1_15`.
* `B_to_A`: `example_10_1_15` is `B`'s claim.  The four auxiliary facts are computations in the
  example that `B` does not state (`B` only says no `f` exists); they are re-proved outright
  below (the project's proofs, copied, from the non-item lemmas `mem_nonEffectivePart_iff`,
  `reducedπ_eq_iff_comp_inv`, `not_eventually_eq_neg`, `z4_inv_three_mul_one`, …).
-/

namespace RoundTrip.V10_12
open Polyfold Polyfold.EpGroupoid.Examples Set Filter Topology

/-- The project's statement, one definition per theorem. -/
def A1 : Prop := type_of% @Polyfold.EpGroupoid.Examples.example1015X_two_mem_nonEffectivePart
def A2 : Prop := type_of% @Polyfold.EpGroupoid.Examples.example1015Y_two_not_mem_nonEffectivePart
def A3 : Prop := type_of% @Polyfold.EpGroupoid.Examples.example1015X_reducedπ_one_eq_three
def A4 : Prop := type_of% @Polyfold.EpGroupoid.Examples.example1015Y_reducedπ_one_ne_three
def A5 : Prop := type_of% @Polyfold.EpGroupoid.Examples.example_10_1_15

/-- The project's statement. -/
def A : Prop := A1 ∧ A2 ∧ A3 ∧ A4 ∧ A5

theorem A_holds : A :=
  ⟨Polyfold.EpGroupoid.Examples.example1015X_two_mem_nonEffectivePart,
    Polyfold.EpGroupoid.Examples.example1015Y_two_not_mem_nonEffectivePart,
    Polyfold.EpGroupoid.Examples.example1015X_reducedπ_one_eq_three,
    Polyfold.EpGroupoid.Examples.example1015Y_reducedπ_one_ne_three,
    Polyfold.EpGroupoid.Examples.example_10_1_15⟩

theorem A_to_B : A → B := by
  rintro ⟨-, -, -, -, h5⟩
  refine ⟨fun i x => ⟨rfl, ?_⟩, fun _ => rfl, rfl, fun _ _ => ⟨rfl, rfl⟩, fun _ => rfl, rfl,
    fun _ => rfl, fun _ _ => rfl, h5⟩
  change z4Sign i • x = _
  unfold z4Sign
  split_ifs <;> simp

/-! ### The four auxiliary facts, re-proved outright (the project's proofs) -/

section Outright

attribute [local instance] z4LineAction z4PlaneAction

theorem example1015X_two_mem_nonEffectivePart' : A1 := by
  intro x
  rw [example1015X.mem_nonEffectivePart_iff]
  have hO : IsOpen ({(Multiplicative.ofAdd 2 : Multiplicative (ZMod 4))} ×ˢ univ :
      Set (Multiplicative (ZMod 4) × (Fin 1 → ℝ))) :=
    (isOpen_discrete _).prod isOpen_univ
  filter_upwards [hO.mem_nhds ⟨rfl, mem_univ _⟩] with ψ hψ
  change ψ.2 = ψ.1 • ψ.2
  rw [mem_singleton_iff.1 hψ.1, z4_smul_line, show z4Sign (Multiplicative.ofAdd 2) = 1 by decide,
    one_smul]

theorem example1015Y_two_not_mem_nonEffectivePart' : A2 := by
  intro h
  have h' := ((continuous_const.prodMk continuous_id).tendsto (0 : Fin 2 → ℝ)).eventually
    (example1015Y.mem_nonEffectivePart_iff.1 h)
  refine not_eventually_eq_neg (n := 2) ?_
  filter_upwards [h'] with y hy
  change y = (Multiplicative.ofAdd 2 : Multiplicative (ZMod 4)) • y at hy
  rwa [z4_smul_plane, show (Multiplicative.toAdd
      (Multiplicative.ofAdd 2 : Multiplicative (ZMod 4))).val = 2 from rfl,
    Function.iterate_succ_apply, Function.iterate_one, quarterTurn_quarterTurn] at hy

theorem example1015X_reducedπ_one_eq_three' : A3 := by
  intro x
  refine example1015X.reducedπ_eq_iff_comp_inv.2 ⟨?_, ?_⟩
  · change (Multiplicative.ofAdd 1 : Multiplicative (ZMod 4)) • x =
      (Multiplicative.ofAdd 3 : Multiplicative (ZMod 4)) • x
    rw [z4_smul_line, z4_smul_line, show z4Sign (Multiplicative.ofAdd 1) = -1 by decide,
      show z4Sign (Multiplicative.ofAdd 3) = -1 by decide]
  · change ((Multiplicative.ofAdd 3 : Multiplicative (ZMod 4))⁻¹ * Multiplicative.ofAdd 1, x) ∈ _
    rw [z4_inv_three_mul_one]
    exact example1015X_two_mem_nonEffectivePart' x

theorem example1015Y_reducedπ_one_ne_three' : A4 := by
  intro h
  have h' := (example1015Y.reducedπ_eq_iff_comp_inv.1 h).2
  change ((Multiplicative.ofAdd 3 : Multiplicative (ZMod 4))⁻¹ * Multiplicative.ofAdd 1,
    (0 : Fin 2 → ℝ)) ∈ _ at h'
  rw [z4_inv_three_mul_one] at h'
  exact example1015Y_two_not_mem_nonEffectivePart' h'

end Outright

theorem B_to_A : B → A :=
  fun hB => ⟨example1015X_two_mem_nonEffectivePart', example1015Y_two_not_mem_nonEffectivePart',
    example1015X_reducedπ_one_eq_three', example1015Y_reducedπ_one_ne_three',
    hB.2.2.2.2.2.2.2.2⟩

#rt_check RoundTrip.V10_12.A_to_B [
  Polyfold.EpGroupoid.Examples.example1015X_two_mem_nonEffectivePart,
  Polyfold.EpGroupoid.Examples.example1015Y_two_not_mem_nonEffectivePart,
  Polyfold.EpGroupoid.Examples.example1015X_reducedπ_one_eq_three,
  Polyfold.EpGroupoid.Examples.example1015Y_reducedπ_one_ne_three,
  Polyfold.EpGroupoid.Examples.example_10_1_15]
#rt_check RoundTrip.V10_12.B_to_A [
  Polyfold.EpGroupoid.Examples.example1015X_two_mem_nonEffectivePart,
  Polyfold.EpGroupoid.Examples.example1015Y_two_not_mem_nonEffectivePart,
  Polyfold.EpGroupoid.Examples.example1015X_reducedπ_one_eq_three,
  Polyfold.EpGroupoid.Examples.example1015Y_reducedπ_one_ne_three,
  Polyfold.EpGroupoid.Examples.example_10_1_15]
#rt_overlap RoundTrip.V10_12.B_to_A [
  Polyfold.EpGroupoid.Examples.example1015X_two_mem_nonEffectivePart,
  Polyfold.EpGroupoid.Examples.example1015Y_two_not_mem_nonEffectivePart,
  Polyfold.EpGroupoid.Examples.example1015X_reducedπ_one_eq_three,
  Polyfold.EpGroupoid.Examples.example1015Y_reducedπ_one_ne_three,
  Polyfold.EpGroupoid.Examples.example_10_1_15]

end RoundTrip.V10_12
