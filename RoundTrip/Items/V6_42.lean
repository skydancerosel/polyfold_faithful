import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_42

/-! Round trip for V6_42 (Lemma 6.30 for the push-forward: the stabilized kernels form the bundle
`L` over `[0, 1]`).

A (universes at `0`): `exists_continuousOn_lift_chart` (a continuous level-`1` lift of an
sc-smooth `Φ : ℝⁿ → X` read in a chart) and `exists_isStabKernels` (for `Φ : ℝⁿ → X` with
`Φ([0, 1]ⁿ)` in a chart, `S` with `f̃ + S = 0` along `Φ` NEAR `[0, 1]ⁿ`, and `s₁, …, s_k` with
the parametrized (P) — general position of `f̃ + S + Σ λᵢ sᵢ` on `ℝᵏ × ℝⁿ × X` at `(0, (q, Φ q))`
for `q` NEAR `[0, 1]ⁿ` — the stabilized kernels form a CONTINUOUS family `IsStabKernels`).

B: for a path (`n = 1`), choices with the text's pointwise (P) (general position of
`F_t = f − s(·, t) + Σ λᵢ sᵢ(·, t)` on `ℝᵏ × X` at `(0, φ(t))` for each `t ∈ [0, 1]`, and
`s(φ(t), t) = f(φ(t))` only on `[0, 1]`), the kernels `L_t` form a SMOOTH family: local frames
`C^∞` in `t` (on level `0`).

No direction is proved.
* `A ⇒ B` fails for two genuine reasons: (i) A gives only continuity of the family, B asks for
  `C^∞` frames (the text's "smooth vector bundle"); nothing in A or in the project's other lemmas
  gives smoothness in `t`; (ii) A's hypotheses are not B's: A's (P) is general position of the
  parametrized section (one more variable `t`) on a neighbourhood of `[0, 1]`, with zeros along the
  path on a neighbourhood of `[0, 1]`, and A asks `IsScFredholmSectionTame` (germ data in tame
  charts); B gives general position of each `F_t` separately at `t ∈ [0, 1]` only, zeros only on
  `[0, 1]`, and `IsScFredholmSection` with `PX.IsTame`.  Bridging (ii) (fixed-`t` general position
  ⇒ parametrized general position, openness, extension past the end points) is Lemma 6.30 work,
  not glue.
* `B ⇒ A` fails: A is for families over cubes `[0, 1]ⁿ` of every dimension `n` (used for the
  homotopies of Theorem 6.35), B only for paths; A's `IsStabKernels` also records the surjectivity
  of `T_q ⊕ φ_q` and the identification of `Λ_q` for every lift, which B does not state; and B's
  pointwise (P) is not implied by A's parametrized (P) (the extra `t`-direction can be needed for
  surjectivity off the zero curve), so B cannot even be instantiated from A's hypotheses.
-/

namespace RoundTrip.V6_42
open Polyfold

/-- The project's statement, universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Polyfold.exists_continuousOn_lift_chart.{0} ∧
  type_of% @Polyfold.exists_isStabKernels.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.exists_continuousOn_lift_chart.{0}, @Polyfold.exists_isStabKernels.{0, 0}⟩

end RoundTrip.V6_42
