import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_23

/-! Round trip for V6_23 (Lemma 6.21: `γ^Q_{PS}` is an isomorphism of local determinant bundles).

`A` is the conjunction of the types of `LocalDetChart.gammaProj_frame_eq` and `lemma_6_21`
(universes at `0`).  `LocalDetChart`, `frame`, `gammaProj`, `linDetEquivOfEq`, `zSol`, `cokerLift`,
`rangeInfKer` are definitions (vocabulary).

**Neither direction is proved.**

What A says.  For two charts `c` (projection `P`, centre `T`, radius `ε`) and `c'` (projection
`Q ≤ P`, centre `T'`, radius `ε'`) and Fredholm `S` in both balls:
* `gammaProj_frame_eq` (under two dimension hypotheses): the EXPLICIT formula
  `γ^Q_{PS}(ω_c(S)) = (det(kerProj(k(S), z(S))) · det([d], [f])⁻¹) · ω_{c'}(S)` (formula (91));
* `lemma_6_21`: `γ^Q_{PS}(ω_c(S)) = g(S) ω_{c'}(S)` with `g` continuous and nowhere zero on
  `{S Fredholm, in both balls}`.
These are statements about the two chart frames `ω_c`, `ω_{c'}` only; the project never puts a
topology on `⋃ {S} × det(PS)`.

What B says.  For admissible `(T, P, ε)`, `(T, Q, ε)` (same centre and radius) and `Q ≤ P`, the side
conditions of `γ^Q_{PS}` hold and `(S, h) ↦ (S, γ^Q_{PS} h)` is a homeomorphism for B's natural
topologies `natTopD` — the final topologies of the frame maps of ALL pairs of continuous local
kernel / cokernel frames.

`A → B` fails for effort (believed true).  B's statement is about `natTopD`, so one needs
Lemma 6.19 for these final topologies: (a) for every continuous frame pair `(σ, f)` over `U`, the
coefficient of `σ ∧ … ⊗ ([f] ∧ …)*` against the chart frame `ω_c` is continuous (`det` of
`kerProj ∘ σ` and of `[f]` in `F/R(P)`), so that a set is `natTopD`-open iff its preimage under the
chart frame map `(S, t) ↦ (S, t ω_c(S))` is open, and (b) the same for `Q`.  Given (a), (b),
`gammaQP` reads `(S, t) ↦ (S, t g(S))` in chart coordinates, and `lemma_6_21` (applied to the two
charts with centre `T` and radius `ε` built from B's hypotheses, with `S` Fredholm on the ball)
gives the homeomorphism.  The project does
not formalize Lemma 6.19 (the same gap blocks V6_22 `A → B`), and building it for `⨆`-coinduced
topologies, plus a `LocalDetChart` from `IsDetChart` and Fredholmness of `S` on the ball, is
substantial new work, not attempted within the budget.

`B → A` fails.  (i) `gammaProj_frame_eq` is an explicit linear-algebra formula; B is purely
topological and carries no information about it (reproving it means redoing §6.7's
projection-sequence computation).  (ii) `lemma_6_21` needs, from B's homeomorphism, the continuity
of the coordinate `g` of `γ(ω_c)` against `ω_{c'}`, i.e. continuity of coordinate extraction out of
`natTopD` — again Lemma 6.19 (B gives a homeomorphism, not a trivialization) — and A allows charts
with different centres and radii while B has one `T` and one `ε` (localizing needs Lemma 6.17 at
every point of the intersection).

Checked below: B is well-posed — its existential side conditions (`P S` Fredholm, `Q ∈ Π_{PS}`,
`QPS = QS` on the ball) follow from its hypotheses (`side_conditions`), so B is not vacuous for
that reason. -/

namespace RoundTrip.V6_23
open Polyfold

/-- The project's statement (formula (91) on the frames, and Lemma 6.21), universes at `0`. -/
def A : Prop :=
  (type_of% @Polyfold.LocalDetChart.gammaProj_frame_eq.{0, 0}) ∧
    (type_of% @Polyfold.lemma_6_21.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.LocalDetChart.gammaProj_frame_eq.{0, 0}, @Polyfold.lemma_6_21.{0, 0}⟩

section SideConditions

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- On the ball of an admissible `(T, P, ε)`, `P S` is Fredholm: `ker(PS) ∩ Y = 0` (the
isomorphism `y ↦ PSy` on `Y`), so `ker(PS)` injects into `ker(PT)` (projection along `Y`), and
`R(PS) = R(P)` is closed of finite codimension. -/
theorem isFredholm_comp_of_isDetChart {T : E →L[ℝ] F} {P : F →L[ℝ] F} {ε : ℝ}
    (hP : IsDetChart T P ε) (S : E →L[ℝ] F) (hS : ‖S - T‖ < ε) : (P.comp S).IsFredholm := by
  obtain ⟨hT, hPg, -, hgood, Y, hY, hiso⟩ := hP
  have gS := hgood S hS
  obtain ⟨e, he⟩ := hiso S hS
  set K := LinearMap.ker ((P.comp T : E →L[ℝ] F) : E →ₗ[ℝ] F) with hK
  have : FiniteDimensional ℝ K := (hPg.isFredholm_comp hT).finite_ker
  set f : LinearMap.ker ((P.comp S : E →L[ℝ] F) : E →ₗ[ℝ] F) →ₗ[ℝ] K :=
    LinearMap.codRestrict K ((K.projection Y hY.isCompl) ∘ₗ
      (LinearMap.ker ((P.comp S : E →L[ℝ] F) : E →ₗ[ℝ] F)).subtype)
      (fun x => Submodule.projection_apply_mem _ _) with hf
  have hinj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun x hx => ?_
    have h0 : K.projection Y hY.isCompl (x : E) = 0 := congrArg Subtype.val hx
    have hxY : (x : E) ∈ Y := by
      have := Submodule.sub_projection_mem hY.isCompl (x : E)
      rwa [h0, sub_zero] at this
    have hPS : P (S x) = 0 := x.2
    have he0 : e ⟨x, hxY⟩ = 0 := Subtype.ext (by rw [he]; exact hPS)
    have := congrArg Subtype.val ((LinearEquiv.map_eq_zero_iff e.toLinearEquiv).1 he0)
    exact Subtype.ext this
  refine isFredholm_of_banach _ ?_ ?_ ?_
  · exact Module.Finite.of_injective f hinj
  · rw [gS.range_comp]
    exact gS.isClosed_range
  · change Module.Finite ℝ (F ⧸ LinearMap.range ((P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F))
    rw [gS.range_comp]
    exact gS.finite_coker

/-- B's existential side conditions follow from its hypotheses (B is well-posed). -/
theorem side_conditions (T : E →L[ℝ] F) (P Q : F →L[ℝ] F) (ε : ℝ)
    (hP : IsDetChart T P ε) (hQc : IsDetChart T Q ε) (hQP : ProjLE Q P) :
    (∀ S : Metric.ball T ε, (P.comp (S : E →L[ℝ] F)).IsFredholm) ∧
    (∀ S : Metric.ball T ε, IsGoodLeftProj (P.comp (S : E →L[ℝ] F)) Q) ∧
    (∀ S : Metric.ball T ε, Q.comp (P.comp (S : E →L[ℝ] F)) = Q.comp (S : E →L[ℝ] F)) :=
  ⟨fun S => isFredholm_comp_of_isDetChart hP S (mem_ball_iff_norm.1 S.2),
    fun S => (hQc.2.2.2.1 S (mem_ball_iff_norm.1 S.2)).of_projLE hQP,
    fun S => comp_comp_eq_of_projLE (T := (S : E →L[ℝ] F)) hQP⟩

end SideConditions

#rt_check RoundTrip.V6_23.side_conditions [Polyfold.LocalDetChart.gammaProj_frame_eq,
  Polyfold.lemma_6_21]

end RoundTrip.V6_23
