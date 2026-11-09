import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V1_15

/-! Round trip for V1_15 (Proposition 1.16: sc¹ in terms of the levels, and `Df(x)` is an
sc-operator at smooth points).

`A` is the conjunction of the types of the theorems in the item's declaration list:
`IsSc1Levels.continuousOn_clm`, `IsSc1Levels.contDiffOn`, `IsSc1Levels.toBase_apply`,
`IsSc1Levels.isSc1With`, `IsSc1With.isSc1Levels`, `proposition_1_2_1`,
`IsSc1With.contDiffOn_base`, `IsSc1With.scOperator_deriv` (`IsSc1Levels` is a definition, the
vocabulary).  None has universe parameters (`ScBanach` lives in `Type`).

Same notions: `B`'s `levelTo f (m+1) m` is `levelMap f m ∘ E.incl m` by `rfl`; `sc⁰`, `sc¹`,
`IsSc1With`, `IsScOperator`, `E_∞` are the project's.  `B`'s conditions (1)–(2) (`C¹` with
`fderivWithin`, plus an extension family `Dl`) and the project's `IsSc1Levels U f Dl`
(derivative `Dl m x ∘ ι` of `f : U_{m+1} → F_m` within `U_{m+1}`, and joint continuity) agree on
domains with unique differentiability, the operator-norm continuity of `df` being the compact-open
lemma.

* `A → B`: `proposition_1_2_1`, `IsSc1Levels.contDiffOn`, `IsSc1Levels.continuousOn_clm` and
  `IsSc1With.scOperator_deriv`, on the sc-domain `U` (`IsRelOpenInQuadrant.isScDomain`).
* `B → A` fails for a genuine reason: every conjunct of `A` is stated for an arbitrary
  `IsScDomain U` (e.g. a closed disc; `continuousOn_clm`, `contDiffOn_base`, `scOperator_deriv` even
  for arbitrary `U`, and `continuousOn_clm`, `contDiffOn` without `f` sc⁰), and several are lemmas
  `B` does not state (`toBase_apply`: the extensions are restrictions of `Dl 0`;
  `isSc1With` / `isSc1Levels`: the specific derivative families `Dl 0` and `levelDeriv D`).  `B`
  covers only relatively open subsets of partial quadrants.  On those domains the two conjuncts that
  correspond to the text — `proposition_1_2_1` and `scOperator_deriv` — follow from `B`
  (`B_proposition_1_16_quadrant`, `B_scOperator_deriv_quadrant`). -/

namespace RoundTrip.V1_15
open Polyfold Set

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.IsSc1Levels.continuousOn_clm) ∧
    (type_of% @Polyfold.IsSc1Levels.contDiffOn) ∧
    (type_of% @Polyfold.IsSc1Levels.toBase_apply) ∧
    (type_of% @Polyfold.IsSc1Levels.isSc1With) ∧
    (type_of% @Polyfold.IsSc1With.isSc1Levels) ∧
    (type_of% @Polyfold.proposition_1_2_1) ∧
    (type_of% @Polyfold.IsSc1With.contDiffOn_base) ∧
    (type_of% @Polyfold.IsSc1With.scOperator_deriv)

theorem A_holds : A :=
  ⟨@Polyfold.IsSc1Levels.continuousOn_clm, @Polyfold.IsSc1Levels.contDiffOn,
    @Polyfold.IsSc1Levels.toBase_apply, @Polyfold.IsSc1Levels.isSc1With,
    @Polyfold.IsSc1With.isSc1Levels, @Polyfold.proposition_1_2_1,
    @Polyfold.IsSc1With.contDiffOn_base, @Polyfold.IsSc1With.scOperator_deriv⟩

/-- The blind `levelTo f (m+1) m` is the project's `levelMap f m ∘ ι_m`. -/
theorem levelTo_eq {E F : ScBanach} (f : E 0 → F 0) (m : ℕ) :
    levelTo f (m + 1) m = levelMap f m ∘ E.incl m := rfl

theorem A_to_B : A → B := by
  intro hA E F C U f hUC hf
  obtain ⟨hclm, hcd, -, -, -, hprop, -, hscop⟩ := hA
  have hU := hUC.isScDomain
  have hfd : ∀ Dl : ∀ m, E (m + 1) → E m →L[ℝ] F m, IsSc1Levels U f Dl → ∀ m,
      ∀ x ∈ E.lvlSet U (m + 1),
        fderivWithin ℝ (levelTo f (m + 1) m) (E.lvlSet U (m + 1)) x = (Dl m x).comp (E.incl m) :=
    fun Dl h m x hx => (h.hasFDerivWithinAt m x hx).fderivWithin (hU.uniqueDiffWithinAt (m + 1) x hx)
  refine ⟨⟨fun h1 => ?_, fun ⟨h1, Dl, h2⟩ => ?_⟩, fun D hD x₁ hx hs => hscop hD hx hs⟩
  · obtain ⟨Dl, hDl⟩ := (hprop hU hf).1 h1
    exact ⟨fun m => ⟨hcd hU hDl m, (hclm hDl m).congr fun x hx => hfd Dl hDl m x hx⟩,
      Dl, fun m => ⟨fun x hx => (hfd Dl hDl m x hx).symm, hDl.continuousOn m⟩⟩
  · refine (hprop hU hf).2 ⟨Dl, ⟨fun m x hx => ?_, fun m => (h2 m).2⟩⟩
    have hd := ((h1 m).1.differentiableOn one_ne_zero x hx).hasFDerivWithinAt
    rw [← (h2 m).1 x hx] at hd
    exact hd

/-- `B → A`, restricted to relatively open subsets of partial quadrants: `proposition_1_2_1`. -/
theorem B_proposition_1_16_quadrant (hB : B) {E F : ScBanach} {C U : Set (E 0)}
    (hUC : IsRelOpenInQuadrant E C U) {f : E 0 → F 0} (hf : IsSc0 E F U f) :
    IsSc1 U f ↔ ∃ Dl : ∀ m, E (m + 1) → E m →L[ℝ] F m, IsSc1Levels U f Dl := by
  have hU := hUC.isScDomain
  have hB' := (hB E F C U f hUC hf).1
  constructor
  · intro h1
    obtain ⟨hc, Dl, h2⟩ := hB'.1 h1
    refine ⟨Dl, ⟨fun m x hx => ?_, fun m => (h2 m).2⟩⟩
    have hd := ((hc m).1.differentiableOn one_ne_zero x hx).hasFDerivWithinAt
    rw [← (h2 m).1 x hx] at hd
    exact hd
  · rintro ⟨Dl, hDl⟩
    have hfd : ∀ m, ∀ x ∈ E.lvlSet U (m + 1),
        fderivWithin ℝ (levelTo f (m + 1) m) (E.lvlSet U (m + 1)) x = (Dl m x).comp (E.incl m) :=
      fun m x hx =>
        (hDl.hasFDerivWithinAt m x hx).fderivWithin (hU.uniqueDiffWithinAt (m + 1) x hx)
    have hclm : ∀ m, ContinuousOn (fun x => (Dl m x).comp (E.incl m)) (E.lvlSet U (m + 1)) :=
      fun m => continuousOn_clm_comp_of_isCompactOperator (A := Dl m) (hDl.continuousOn m)
        (E.incl_isCompactOperator m)
    refine hB'.2 ⟨fun m => ⟨?_, (hclm m).congr fun x hx => hfd m x hx⟩,
      Dl, fun m => ⟨fun x hx => (hfd m x hx).symm, hDl.continuousOn m⟩⟩
    rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl,
      contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (hU.uniqueDiffWithinAt (m + 1))]
    refine ⟨fun h0 => absurd h0 (by simp), fun x => (Dl m x).comp (E.incl m), ?_,
      hDl.hasFDerivWithinAt m⟩
    rw [contDiffOn_zero]; exact hclm m

/-- `B → A`, restricted to relatively open subsets of partial quadrants: `scOperator_deriv`. -/
theorem B_scOperator_deriv_quadrant (hB : B) {E F : ScBanach} {C U : Set (E 0)}
    (hUC : IsRelOpenInQuadrant E C U) {f : E 0 → F 0} {D : E 1 → E 0 →L[ℝ] F 0}
    (h : IsSc1With U f D) {x : E 1} (hx : x ∈ E.lvlSet U 1) (hs : x ∈ E.smoothLvl 1) :
    IsScOperator (D x) :=
  (hB E F C U f hUC h.isSc0).2 D h x hx hs

#rt_check RoundTrip.V1_15.A_to_B [Polyfold.IsSc1Levels.continuousOn_clm,
  Polyfold.IsSc1Levels.contDiffOn, Polyfold.IsSc1Levels.toBase_apply,
  Polyfold.IsSc1Levels.isSc1With, Polyfold.IsSc1With.isSc1Levels, Polyfold.proposition_1_2_1,
  Polyfold.IsSc1With.contDiffOn_base, Polyfold.IsSc1With.scOperator_deriv]
#rt_check RoundTrip.V1_15.B_proposition_1_16_quadrant [Polyfold.IsSc1Levels.continuousOn_clm,
  Polyfold.IsSc1Levels.contDiffOn, Polyfold.IsSc1Levels.toBase_apply,
  Polyfold.IsSc1Levels.isSc1With, Polyfold.IsSc1With.isSc1Levels, Polyfold.proposition_1_2_1,
  Polyfold.IsSc1With.contDiffOn_base, Polyfold.IsSc1With.scOperator_deriv]
#rt_check RoundTrip.V1_15.B_scOperator_deriv_quadrant [Polyfold.IsSc1Levels.continuousOn_clm,
  Polyfold.IsSc1Levels.contDiffOn, Polyfold.IsSc1Levels.toBase_apply,
  Polyfold.IsSc1Levels.isSc1With, Polyfold.IsSc1With.isSc1Levels, Polyfold.proposition_1_2_1,
  Polyfold.IsSc1With.contDiffOn_base, Polyfold.IsSc1With.scOperator_deriv]

end RoundTrip.V1_15
