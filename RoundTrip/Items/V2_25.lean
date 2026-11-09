import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_25

/-! Round trip for V2_25 (Proposition 2.21 (3), (4): tangent spaces of a sub-M-polyfold).

`A` is the conjunction of the types of the listed theorems `Polyfold.ScRetraction.compRetraction_retract`,
`Polyfold.proposition_2_3_19_three`, `Polyfold.proposition_2_3_19_four` (no universe parameters: everything
lives in sc-Banach spaces).  `ScRetraction.compRetraction` (`t = s ∘ r`) is a definition.

**Neither direction is proved.**

What A says.  A is the text's *proof in coordinates*, for an arbitrary sc-retraction `R` with
retract `O = R(U)` and an arbitrary sc-smooth `s : O → O` with `s ∘ s = s` (so `s(O)` plays the
role of `A ∩ O`), at `a ∈ s(O)₁`:
* (3) (`a` smooth) `T_aO = Dr(a)E`, `T_a s(O) = Dt(a)E` (`t = s ∘ r`), `Dt(a)E ⊆ Dr(a)E`, and the
  explicit complement: `Dt(a)E` and `(Dr(a) − Dt(a))E` are sc-subspaces of `E` whose levelwise sum
  is direct and equals `Dr(a)E` on every level;
* (4) `s : O → s(O)` is sc-smooth (as a map of retracts) and `T(s)(a)(T_aO) = T_a s(O)`;
* `compRetraction_retract`: the retract of `t` is `s(O)`.

What B says.  B is the global statement on an M-polyfold `X`, for a sub-M-polyfold `A`, for EVERY
structure `Q` on `A` with Proposition 2.21 (1), (2): (3) at `a ∈ A_∞`, in every chart `φ` of `X`
around `a`, the chart images of `Ti(a)(T_aA)` and of `T_aX` (tangent bundle of Definition 2.18,
`tangentChartMap`, `tangentMap`) are submodules `L ⊆ M` of `E` and SOME sc-complement `B'` of `L`
in `M` exists; (4) for every sc-smooth retraction `s : W → W` onto `W ∩ A`, `W → A` is sc-smooth
and the chart image of `Ts(a)(T_aX)` (over representatives with chart domain in `W`) is the chart
image of `Ti(a)(T_aA)`.

`A → B` fails for lack of transport, not for a mathematical reason (believed true).  The project
does not transport Proposition 2.21 (3), (4) from the chart to `T_aX` / `T_aA` (its own header,
gap G.7).  Doing so is new work on the tangent-bundle API: given `a`, a chart `φ`, the data
`(V, r)` of `A` at `a` and an arbitrary `Q` with (1), (2), one must (i) identify the chart image of
`T_aX` with `T_{φ(a)}O` (done below, `tangentInChartB_eq`), (ii) apply A to the retraction `R'`
onto `φ(W)` (`W` the shrunken domain) and `s := φ ∘ r ∘ φ⁻¹` (an sc-smooth idempotent of `φ(W)`
with image `φ(W ∩ A)`), and use the locality of `T_{φ(a)}` (`retractTangent_inter_isOpen`),
(iii) show the chart image of `Ti(a)(T_aA)` is `T_{φ(a)}φ(W ∩ A)` for an ARBITRARY `Q` with
(1), (2) — the chain rule for `φ ∘ i ∘ κ⁻¹` and `κ ∘ (i⁻¹ ∘ r) ∘ φ⁻¹` (`κ` a chart of `Q`), whose
composites are `id` near `κ(a)` and `φ ∘ r ∘ φ⁻¹` — and (iv) for (4), the same for
`φ ∘ s ∘ φ_p⁻¹` in mixed charts.  Steps (iii), (iv) are several hundred lines of chart and
tangent-map glue; they were not attempted within the budget.

`B → A` fails for a genuine reason.  A's conjuncts are about arbitrary retractions of sc-Banach
spaces and give explicit formulas — `T_aO = Dr(a)E`, `T_a s(O) = Dt(a)E` and the specific
complement `(Dr(a) − Dt(a))E` — while B (3) only asserts that SOME sc-complement exists, in charts of
M-polyfolds; B says nothing about `Dr(a)`, `Dt(a)`, about the definition `compRetraction`, or about
retracts not presented as charts of a sub-M-polyfold.  Recovering A from B would require realising
`O` as an M-polyfold and `s(O)` as a sub-M-polyfold, and would still leave the explicit formulas
and the explicit complement to be proved directly.

What is checked below: the glue lemma (i), and that B's "`W → A` is sc-smooth" in (4) is already
B's hypothesis (2) on `Q`. -/

namespace RoundTrip.V2_25
open Polyfold Set MPolyfold

/-- The project's statement (no universe parameters). -/
def A : Prop :=
  (type_of% @Polyfold.ScRetraction.compRetraction_retract) ∧
    (type_of% @Polyfold.proposition_2_3_19_three) ∧ (type_of% @Polyfold.proposition_2_3_19_four)

theorem A_holds : A :=
  ⟨@Polyfold.ScRetraction.compRetraction_retract, @Polyfold.proposition_2_3_19_three,
    @Polyfold.proposition_2_3_19_four⟩

section Glue

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

/-- (i) The chart image of `T_aX` is the tangent space `T_{φ(a)}O` of the model retract. -/
theorem tangentInChartB_eq (P : MPolyfold X) {φ : MChart X} (hφ : P.IsChart φ) (a : X)
    (ha : a ∈ P.smoothSet) (haφ : a ∈ φ.source) :
    tangentInChartB P hφ a ha =
      tangentSpace φ.model.E φ.model.C φ.model.O (levelLift φ 1 a) := by
  ext h
  constructor
  · rintro ⟨α, hα, rfl⟩
    have hα' : P.tangentProj α = ⟨a, Set.mem_iInter.1 ha 1⟩ := hα
    have hproj : P.levelVal 1 (P.tangentProj α) = a := by rw [hα']; rfl
    have hαφ : α ∈ tangentChartSet (P := P) φ := by
      change P.levelVal 1 (P.tangentProj α) ∈ φ.source
      rw [hproj]; exact haφ
    have hmem := tangentChartMap_mem hφ hαφ
    have hfst := tangentChartMap_fst hφ hαφ
    rw [hproj] at hfst
    change ((levelLift φ 1 a, (tangentChartMap hφ α).2) : φ.model.E.tangent 0) ∈
      retractTangent φ.model.E φ.model.C φ.model.O
    rw [← hfst]
    exact hmem
  · intro hh
    let p : P.TangentPre := ⟨a, φ, h, hφ, haφ, Set.mem_iInter.1 ha 1, hh⟩
    refine ⟨TangentSpace.mk p, level_ext rfl, ?_⟩
    change (tangentChartMap p.isChart (TangentSpace.mk p)).2 = h
    rw [tangentChartMap_mk_self]
    rfl

/-- B's "the induced map `W → A` is sc-smooth" is hypothesis (2) of `IsNaturalSubStructureB`. -/
theorem induced_isScSmoothOn (P : MPolyfold X) (S : Set X) [ParacompactSpace S] (Q : MPolyfold S)
    (hQ : IsNaturalSubStructureB P S Q) (W : Set X) (s : X → X) (hW : IsOpen W)
    (hsW : MapsTo s W W) (hsm : P.IsScSmoothOn P s W) (hidem : ∀ x ∈ W, s (s x) = s x)
    (himg : s '' W = W ∩ S) (g : X → S) (hg : ∀ x ∈ W, (g x : X) = s x) :
    P.IsScSmoothOn Q g W :=
  hQ.2 W s hW hsW hsm hidem (by rw [himg, inter_comm]) g hg

end Glue

#rt_check RoundTrip.V2_25.tangentInChartB_eq [Polyfold.ScRetraction.compRetraction_retract,
  Polyfold.proposition_2_3_19_three, Polyfold.proposition_2_3_19_four]
#rt_check RoundTrip.V2_25.induced_isScSmoothOn [Polyfold.ScRetraction.compRetraction_retract,
  Polyfold.proposition_2_3_19_three, Polyfold.proposition_2_3_19_four]

end RoundTrip.V2_25
