import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_55

open Set Filter Topology Function

noncomputable section

namespace RoundTrip.V3_55
open Polyfold

/-- The project's statement: `lemma_3_8_8` and `sigmaCoord_surjective` (both for an arbitrary
normed space `V` with arbitrary linear functionals `ℓ_i`; universe instantiated at `0`).  `vanIdx`
is vocabulary. -/
def A : Prop :=
  type_of% @Polyfold.lemma_3_8_8.{0} ∧ type_of% @Polyfold.sigmaCoord_surjective.{0}

theorem A_holds : A := ⟨@Polyfold.lemma_3_8_8.{0}, @Polyfold.sigmaCoord_surjective.{0}⟩

/-- The coordinate functionals `x ↦ x_i` of `ℝⁿ ⊕ W`, as linear maps. -/
def coordLin (n : ℕ) (W : ScBanach) (i : Fin n) : (Emod n W).lvl 0 →ₗ[ℝ] ℝ :=
  (LinearMap.proj i).comp (LinearMap.fst ℝ (Fin n → ℝ) (W.lvl 0))

@[simp] lemma coordLin_apply (n : ℕ) (W : ScBanach) (i : Fin n) (x : (Emod n W).lvl 0) :
    coordLin n W i x = x.1 i := rfl

/-- A ⇒ B: the conjunct `lemma_3_8_8` with `ℓ_i` the coordinates, `P = N^⊥`; the blind `Σ` is the
project's `vanIdx` for these functionals.  (Only the `ε`-property of the good complement is used.) -/
theorem A_to_B : A → B := by
  rintro ⟨h65, -⟩
  intro n W N _ _ _ Nperp hgc p hp i hi
  obtain ⟨-, ε, hε, hgood⟩ := hgc
  have hvan : i ∈ vanIdx (coordLin n W) N := by
    obtain ⟨a, haN, haC, ha0, hai⟩ := hi
    rw [mem_vanIdx]
    exact ⟨⟨a, haN⟩, fun j => haC j, fun h => ha0 (congrArg Subtype.val h), hai⟩
  exact h65 (coordLin n W) N Nperp hε (fun x hx q hq hle => hgood x hx q hq hle) hp hvan

#rt_check RoundTrip.V3_55.A_to_B [Polyfold.lemma_3_8_8, Polyfold.sigmaCoord_surjective]

end RoundTrip.V3_55
