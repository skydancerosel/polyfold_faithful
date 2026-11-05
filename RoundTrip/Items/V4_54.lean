import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_54

/-!
Round trip for V4_54 (Theorem 4.23, families and Sard's theorem).  `A` is the type of
`Polyfold.theorem_4_23`, universe instantiated at `0`.

Glue for `A → B`:
* `|λ| ≤ ε` / `|λ| < ε`: B's `eucNorm λ = √(Σ λᵢ²)` vs A's `Σ λᵢ² ≤ ε²` / `< ε²` (`ε > 0`).
* B's hypotheses `∃ paracompact, IsTameSubmanifold A` give A's `IsSmoothSubmanifold A`,
  `[ParacompactSpace A]` and `IsTameSubmanifold A`; (1), (2), compact closure are the same.
* A's stratified regular values (`IsStratRegularValue`: `Tp` maps `T_zA ∩ E_z` onto `ℝᵐ`) give
  B's plain regular values (`IsRegularPointB`: `Tp` maps `T_zA` onto `ℝᵐ`) by forgetting the
  constraint `v.2 ∈ E_z`.
* The fibre conclusions coincide (A also gives tameness of `A_λ`, which B does not ask); the
  paracompactness of `A_λ` is `paracompactSpace_subtype`.

`B → A` is not proved: B's plain regular values do not give A's stratified ones.
-/

namespace RoundTrip.V4_54
open Polyfold MeasureTheory

/-- The project's statement, universe `0`. -/
def A : Prop := type_of% @Polyfold.theorem_4_23.{0}

theorem A_holds : A := @Polyfold.theorem_4_23.{0}

theorem eucNorm_lt_iff {m : ℕ} {ε : ℝ} (hε : 0 < ε) (l : Fin m → ℝ) :
    eucNorm l < ε ↔ ∑ i, l i ^ 2 < ε ^ 2 :=
  Real.sqrt_lt' hε

theorem eucNorm_le_iff {m : ℕ} {ε : ℝ} (hε : 0 < ε) (l : Fin m → ℝ) :
    eucNorm l ≤ ε ↔ ∑ i, l i ^ 2 ≤ ε ^ 2 := by
  unfold eucNorm
  rw [Real.sqrt_le_left hε.le]

theorem A_to_B : A → B := by
  intro hA X _ _ _ PX m _ S ε hX ⟨hpar, hSt⟩ hcl hε h1 h2
  have hS : ((rnPolyfold m).prod PX).IsSmoothSubmanifold S := hSt.1
  have hball : {l : Fin m → ℝ | eucNorm l < ε} = {l | ∑ i, l i ^ 2 < ε ^ 2} :=
    Set.ext fun l => eucNorm_lt_iff hε l
  obtain ⟨Sig, hSig, hnull, hprop⟩ := hA hX hS hSt hcl hε
    (fun l hl => h1 l ((eucNorm_le_iff hε l).2 hl)) h2
  refine ⟨Sig, hball ▸ hSig, hball ▸ hnull, fun l hl => ?_⟩
  obtain ⟨hreg, hcpt, hF, hgp, hcs, -⟩ := hprop l hl
  refine ⟨fun z hz hzl => ?_, hF, hcpt, ⟨hF.isSubMPolyfold, PX.paracompactSpace_subtype _, hcs⟩, hgp⟩
  obtain ⟨hzS, d, a, φ, n, Wq, T, y, hzV, hφ, hz2, -, hy, hμ⟩ := hreg z hz hzl
  refine ⟨hzS, d, a, φ, y, hzV, hφ, hz2, hy, fun μ => ?_⟩
  obtain ⟨v, hv, -, hv1⟩ := hμ μ
  exact ⟨v, hv, hv1⟩

#rt_check RoundTrip.V4_54.A_to_B [Polyfold.theorem_4_23]

end RoundTrip.V4_54
