import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_77

/-!
Round trip for V3_77 (Theorems 3.43, 3.47 and Theorem 3.54 (3) with a closed good complement that
projects into the quadrant).  `A` is the conjunction of the types of `Polyfold.theorem_3_5_6_closed`,
`Polyfold.theorem_3_5_6_proj`, `Polyfold.theorem_3_5_11_proj`, `Polyfold.theorem_3_5_11_closed`,
`Polyfold.theorem_3_6_8_graph_proj` (universes `u, v` at `0`),
`Polyfold.IsGoodComplement.prod_top_graph`, `Polyfold.ProjectsInto.prod_top_graph` and
`Polyfold.ShiftedBasicData.exists_sol_of_goodComplement`.  Since the germ reading (refresh
2026-11-02) `theorem_3_6_8_graph_proj` assumes the text's germ reading (`IsGoodPositionGermTame`);
`B`'s whole-chart `IsGoodPosData` in (c) implies it (as a hypothesis), so nothing below changes.

Neither direction is proved.  Compared with the earlier items V3_38 (Theorem 3.43), V3_42
(Corollary 3.47) and V3_48 (Theorem 3.54 (3)), the new `A` records `IsClosed Y` (and `ProjectsInto`),
which removes **one** of the gaps found there: B's complement is an *sc*-complement, A's only an
algebraic one; with `Y` closed and the kernel smooth they agree.  This is proved below
(`isGoodComplementSc_of_closed`, and `le_smooth_of_isInGoodPositionSc`: B's own hypothesis that
the kernel is in sc-good position makes the kernel smooth), with `isScSplitting_of_isClosed` copied
from V3_20.  The remaining gaps:

* `A → B`, (a) Theorem 3.43: B is stated for **every** strong bundle isomorphism `Φ` with
  `(Φ_* f)¹` basic, concluding good position of `K' = ker D(Φ_* f)(0)` and the graph form.  A's
  `theorem_3_5_6_closed/proj` are germ-form statements about `ShiftedBasicData` and *assume* the
  good position of `K'` (`hpos`) and the level-`1` smallness of the zeros (`hreg`, Lemma 3.42);
  deriving these for an arbitrary `Φ` (the project does it only for its own coordinate change of
  Theorem 3.38) is new mathematics.
* `A → B`, (b) Corollary 3.47: the setting is reachable (V3_42: absorb the `ℝᴺ`-part of `s`, the
  data of Theorem 3.38 from Proposition 1.10, sc-good position ⇒ `IsInGoodPosition`) and now the
  complement too (below).  What is left is the regularity of `σ`: B's `IsGraphSolution` asks for
  `σ : K → E₁` of class `C¹` *into level `1`* on `V` and an sc-smooth **germ** (one germ of
  neighbourhoods `O(K ∩ C, 0)`) into `E¹`; A gives `σ` into level `0`, `C¹` there, values on level
  `1`, and `C^k`-lifts into level `k` on neighbourhoods `V_k` depending on `k`.  The `C¹`-into-`E₁`
  part can be had by shrinking `V` to `V₁` (and `U₀` accordingly); the sc-smooth germ needs a germ
  version of Proposition 1.19 on finite-dimensional domains (`C^k` lifts on shrinking
  neighbourhoods ⇒ sc^k-germ on the diagonal germ), which the project lacks (as in V3_22).
* `A → B`, (c) Theorem 3.54 (3): B is claimed for every good-position datum `(c, g, s, D)` at `x`,
  `theorem_3_6_8_graph_proj` only for a chart and coordinate change it chooses (existential); and
  `GraphFormCor` again needs the germ regularity of `σ`.
* `B → A`: A's hypotheses are weaker (algebraic good position `hpos`, arbitrary finite-dimensional
  `P`, any `ShiftedBasicData`/`StabilityData`, `IsSection` and `IsGoodPositionGermTame` for 3.54)
  and A concludes more (`ProjectsInto`, smoothness of the kernel, `C^k`-lifts, injectivity of
  `ψ ∘ φ`); the lemmas `prod_top_graph` and `exists_sol_of_goodComplement` are general facts
  outside B.
-/

namespace RoundTrip.V3_77
open Polyfold Set Module

/-- The project's statement: the listed theorems, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.theorem_3_5_6_closed ∧ type_of% @Polyfold.theorem_3_5_6_proj ∧
    type_of% @Polyfold.theorem_3_5_11_proj ∧ type_of% @Polyfold.theorem_3_5_11_closed ∧
    type_of% @Polyfold.theorem_3_6_8_graph_proj.{0, 0} ∧
    type_of% @Polyfold.IsGoodComplement.prod_top_graph ∧
    type_of% @Polyfold.ProjectsInto.prod_top_graph ∧
    type_of% @Polyfold.ShiftedBasicData.exists_sol_of_goodComplement

theorem A_holds : A :=
  ⟨@Polyfold.theorem_3_5_6_closed, @Polyfold.theorem_3_5_6_proj, @Polyfold.theorem_3_5_11_proj,
    @Polyfold.theorem_3_5_11_closed, @Polyfold.theorem_3_6_8_graph_proj.{0, 0},
    @Polyfold.IsGoodComplement.prod_top_graph, @Polyfold.ProjectsInto.prod_top_graph,
    @Polyfold.ShiftedBasicData.exists_sol_of_goodComplement⟩

/-! ### Diagnostic: A's closed complement is B's sc-complement (copied from V3_20) -/

section Split

variable {E : ScBanach} {N Y : Submodule ℝ (E 0)} [FiniteDimensional ℝ N]

/-- The level-`m` projection `x ↦ lift_m(π x)` onto `N_m` along `Y_m`. -/
noncomputable def projLvl (hN : N ≤ E.smooth) (h : Submodule.IsTopCompl N Y) (m : ℕ) :
    E m →L[ℝ] E m :=
  (LinearMap.toContinuousLinearMap (finSmoothLift hN m)).comp
    ((N.projectionOntoL Y h).comp (E.toBase m))

lemma toBase_projLvl (hN : N ≤ E.smooth) (h : Submodule.IsTopCompl N Y) (m : ℕ) (x : E m) :
    E.toBase m (projLvl hN h m x) = (N.projectionOntoL Y h (E.toBase m x) : E 0) :=
  toBase_finSmoothLift hN m _

noncomputable def projOp (hN : N ≤ E.smooth) (h : Submodule.IsTopCompl N Y) : ScOperator E E where
  lvl := projLvl hN h
  incl_comm m x := by
    apply E.toBase_injective m
    rw [← ScScale.toBase_succ, toBase_projLvl, toBase_projLvl, ScScale.toBase_succ]

lemma projOp_zero (hN : N ≤ E.smooth) (h : Submodule.IsTopCompl N Y) (x : E 0) :
    projOp hN h 0 x = (N.projectionOntoL Y h x : E 0) :=
  toBase_projLvl hN h 0 x

/-- A closed complement `Y` of a smooth finite-dimensional `N` is an sc-complement. -/
theorem isScSplitting_of_isClosed (hN : N ≤ E.smooth) (hNY : IsCompl N Y)
    (hY : IsClosed (Y : Set (E 0))) : E.IsScSplitting N Y := by
  have h : Submodule.IsTopCompl N Y :=
    (Submodule.IsCompl.isTopCompl_of_isClosed_of_finiteDimensional hNY.symm hY).symm
  have hidem : ∀ x, projOp hN h 0 (projOp hN h 0 x) = projOp hN h 0 x := fun x => by
    rw [projOp_zero hN h (projOp hN h 0 x), projOp_zero hN h x,
      Submodule.projectionOntoL_apply_left]
  have hS := ScBanach.isScSplitting_of_idem (projOp hN h) hidem
  have hr : LinearMap.range (projOp hN h 0 : E 0 →ₗ[ℝ] E 0) = N := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      change projOp hN h 0 y ∈ N
      rw [projOp_zero]
      exact (N.projectionOntoL Y h y).2
    · intro hx
      refine ⟨x, ?_⟩
      change projOp hN h 0 x = x
      rw [projOp_zero, Submodule.projectionOntoL_apply_left h ⟨x, hx⟩]
  have hk : LinearMap.ker (projOp hN h 0 : E 0 →ₗ[ℝ] E 0) = Y := by
    ext x
    rw [LinearMap.mem_ker]
    change projOp hN h 0 x = 0 ↔ x ∈ Y
    rw [projOp_zero, ← Submodule.projectionOntoL_apply_eq_zero_iff h]
    exact ⟨fun h0 => Subtype.ext h0, fun h0 => by rw [h0]; rfl⟩
  rwa [hr, hk] at hS

end Split

/-- **Diagnostic**: the project's closed (algebraic) good complement of a smooth
finite-dimensional `K` is the blind file's good complement (an sc-complement). -/
theorem isGoodComplementSc_of_closed {E : ScBanach} {C : Set (E 0)} {K Y : Submodule ℝ (E 0)}
    [FiniteDimensional ℝ K] (hK : K ≤ E.smooth) (hY : IsGoodComplement E C K Y)
    (hYc : IsClosed (Y : Set (E 0))) : IsGoodComplementSc E C K Y :=
  ⟨isScSplitting_of_isClosed hK hY.isCompl hYc, hY.exists_eps⟩

/-- **Diagnostic**: B's hypothesis (the finite-dimensional kernel is in sc-good position) makes it
smooth (Proposition 1.6), so `isGoodComplementSc_of_closed` applies to the kernel. -/
theorem le_smooth_of_isInGoodPositionSc {E : ScBanach} {C : Set (E 0)} {K : Submodule ℝ (E 0)}
    [FiniteDimensional ℝ K] (h : IsInGoodPositionSc E C K) : K ≤ E.smooth := by
  obtain ⟨-, Y, hsplit, -⟩ := h
  exact (E.proposition_1_1_7_iff K).1 hsplit.1

#rt_check RoundTrip.V3_77.isGoodComplementSc_of_closed [Polyfold.theorem_3_5_6_closed,
  Polyfold.theorem_3_5_6_proj, Polyfold.theorem_3_5_11_proj, Polyfold.theorem_3_5_11_closed,
  Polyfold.theorem_3_6_8_graph_proj, Polyfold.IsGoodComplement.prod_top_graph,
  Polyfold.ProjectsInto.prod_top_graph, Polyfold.ShiftedBasicData.exists_sol_of_goodComplement]

end RoundTrip.V3_77
