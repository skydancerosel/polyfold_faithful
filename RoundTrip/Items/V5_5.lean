import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_5

namespace RoundTrip.V5_5
open Polyfold

/-- The project's statement (Proposition 5.3, existence part, with the properties of the glued norm
`N(w) = Σᵢ ρᵢ(P(w))·|Φᵢ[1](w)|₁` of its proof), universes instantiated at `0` (the index type of
the chart family in `continuous_gluedNorm` etc. also at `0`). -/
def A : Prop :=
  type_of% @Polyfold.proposition_5_1_3_exists.{0, 0} ∧
  type_of% @Polyfold.StrongBundle.continuous_gluedNorm.{0, 0, 0} ∧
  type_of% @Polyfold.StrongBundle.isCompleteFiberNorm_gluedNorm.{0, 0, 0} ∧
  type_of% @Polyfold.StrongBundle.gluedNorm_bounds.{0, 0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.proposition_5_1_3_exists.{0, 0}, @Polyfold.StrongBundle.continuous_gluedNorm.{0, 0, 0},
    @Polyfold.StrongBundle.isCompleteFiberNorm_gluedNorm.{0, 0, 0},
    @Polyfold.StrongBundle.gluedNorm_bounds.{0, 0, 0}⟩

/-- `A ⇒ B`: the first conjunct of A is B. -/
theorem A_to_B : A → B := by
  intro hA X _ _ _ PX Y _ _ _ P _ _ Bd
  exact hA.1 (B := Bd)

/-! `B ⇒ A` is not proved: B is only the existence of an auxiliary norm; the other three conjuncts
of A are properties of the specific glued norm `gluedNorm B c ρ` (continuity, complete norm on every
fibre, local two-sided comparison with the `|·|₁` of any chart), about which B says nothing.  They
are the mathematical content of the proof of Proposition 5.3 and would have to be re-proved. -/

#rt_check RoundTrip.V5_5.A_to_B [Polyfold.proposition_5_1_3_exists,
  Polyfold.StrongBundle.continuous_gluedNorm, Polyfold.StrongBundle.isCompleteFiberNorm_gluedNorm,
  Polyfold.StrongBundle.gluedNorm_bounds]

end RoundTrip.V5_5
