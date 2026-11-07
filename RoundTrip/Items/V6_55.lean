import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_55

/-! Round trip for V6_55 (`Or_x^f` in a chosen chart; it has two elements).

A is the conjunction of `isChart_orChart`, `mem_orChart`, `toChartOr_orChart`, `toChartOr_trans` and
`exists_two_orx` (universes at `0`).  B: at every smooth point of a TAME `X`, for an sc-Fredholm `f`
and every chart point `p` at `x`, `Nat.card (Or^f_x read in p) = 2`.

* `A → B` is not proved: A's `exists_two_orx` assumes `Bd.HasScPlusSectionsThrough` (sc⁺-sections
  through every smooth fibre point, which make `Lin(f, x)` nonempty, Proposition 6.26); B's setting
  does not give it (B's author flagged this: without such sections `Lin(f, x)` may be empty and
  `Or^f_x` has one element).  With it added, `A → B` is proved (`A_to_B_hsec`: A's two elements of
  `Orx`, carried to any chart point by `ChartPoint.orTransfer`); tameness is not used.
* `B → A` is not proved: B speaks only of tame `X`, A's `exists_two_orx` of every `X`; under
  tameness B gives it (`B_to_existsTwo_tame`).  A's other four conjuncts (the chosen chart is a chart
  at `x`, `toChartOr` is the identity in it and composes with `orTransfer`) are facts about the
  project's definitions which B does not state.
-/

namespace RoundTrip.V6_55
open Polyfold

/-- The project's statement (the five theorems of the row), universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Polyfold.isChart_orChart.{0, 0} ∧
  type_of% @Polyfold.mem_orChart.{0, 0} ∧
  type_of% @Polyfold.toChartOr_orChart.{0, 0} ∧
  type_of% @Polyfold.toChartOr_trans.{0, 0} ∧
  type_of% @Polyfold.exists_two_orx.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.isChart_orChart.{0, 0}, @Polyfold.mem_orChart.{0, 0},
    @Polyfold.toChartOr_orChart.{0, 0}, @Polyfold.toChartOr_trans.{0, 0},
    @Polyfold.exists_two_orx.{0, 0}⟩

theorem natCard_eq_two {α : Type*} {o₁ o₂ : α} (h : o₁ ≠ o₂) (h' : ∀ o, o = o₁ ∨ o = o₂) :
    Nat.card α = 2 :=
  Nat.card_eq_two_iff.2 ⟨o₁, o₂, h, Set.eq_univ_of_forall fun o => by
    rcases h' o with rfl | rfl <;> simp⟩

theorem two_of_natCard {α : Type*} (h : Nat.card α = 2) :
    ∃ o₁ o₂ : α, o₁ ≠ o₂ ∧ ∀ o, o = o₁ ∨ o = o₂ := by
  obtain ⟨a, b, hab, hu⟩ := Nat.card_eq_two_iff.1 h
  refine ⟨a, b, hab, fun o => ?_⟩
  have : o ∈ ({a, b} : Set α) := hu ▸ Set.mem_univ o
  simpa using this

/-- B with the hypothesis `HasScPlusSectionsThrough` of A's `exists_two_orx` added. -/
def B_hsec : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (hf : Bd.IsScFredholmSection f),
    Bd.HasScPlusSectionsThrough → PX.IsTame → ∀ x ∈ PX.smoothSet, ∀ p : ChartPoint Bd x,
      Nat.card (ChartPoint.Or f p hf) = 2

/-- The part of A that `A → B` uses (`isChart_orChart`, `mem_orChart`, `exists_two_orx`); unlike A, its
statement does not contain the banned `isChart_orChart` as a proof term (A's `toChartOr_orChart`
does). -/
def A' : Prop :=
  type_of% @Polyfold.isChart_orChart.{0, 0} ∧
  type_of% @Polyfold.mem_orChart.{0, 0} ∧
  type_of% @Polyfold.exists_two_orx.{0, 0}

/-- `A → B` with `HasScPlusSectionsThrough` added (through `A'`): A's two elements of `Or^f_x` in the
chosen chart, carried to `p` by `orTransfer`. -/
theorem A'_to_B_hsec : A' → B_hsec := by
  intro hA
  obtain ⟨hch, hmem, h2⟩ := hA
  intro X _ _ _ PX Y _ _ _ P _ _ Bd f hf hsec _ x hx p
  obtain ⟨o₁, o₂, h12, hall⟩ := h2 hf hx hsec
  rw [← Nat.card_congr ((chartPtOf (orChart Bd x) (hch x) (hmem x) hx).orTransfer p hf hx)]
  exact natCard_eq_two h12 hall

theorem A_to_B_hsec : A → B_hsec := fun hA => A'_to_B_hsec ⟨hA.1, hA.2.1, hA.2.2.2.2⟩

/-- A's `exists_two_orx` restricted to tame `X`. -/
def ExistsTwoTame : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (hf : Bd.IsScFredholmSection f),
    PX.IsTame → ∀ {x : X} (hs : x ∈ PX.smoothSet), Bd.HasScPlusSectionsThrough →
      ∃ o₁ o₂ : Orx f hf x hs, o₁ ≠ o₂ ∧ ∀ o, o = o₁ ∨ o = o₂

/-- `B → A`'s main conjunct, for tame `X` (B applied to the chosen chart point). -/
theorem B_to_existsTwo_tame : B → ExistsTwoTame := by
  intro hB X _ _ _ PX Y _ _ _ P _ _ Bd f hf hX x hs _
  exact two_of_natCard (hB PX P Bd f hf hX x hs
    (chartPtOf (orChart Bd x) (Bd.isChart_of_mem (Bd.exists_chart_mem x).choose_spec.1)
      (Bd.exists_chart_mem x).choose_spec.2 hs))

open Lean Elab Command in
/-- `#rt_check_except_defs T [d₁, …] [n₁, …]` (as in items V1_32, V2_24, V3_64, V6_19): the harness
traversal `rtCollect` with the bodies of the definitions `dᵢ` not unfolded; fails if the proof of
`T` reaches some `nᵢ` elsewhere. -/
elab "#rt_check_except_defs " t:ident " [" ds:ident,* "]" " [" bs:ident,* "]" : command => do
  let env ← getEnv
  let some ci := env.find? t.getId | throwError "unknown {t.getId}"
  let roots := ((rtValue? ci).map (·.getUsedConstants)).getD #[]
  let seen := ds.getElems.foldl (fun s d => s.insert d.getId) NameSet.empty
  let used := rtCollect env roots.toList seen
  if used.contains ``sorryAx then throwError "FAIL: {t.getId} contains sorry"
  let bad := bs.getElems.toList.map (·.getId) |>.filter used.contains
  unless bad.isEmpty do throwError "FAIL: {t.getId} uses {bad} outside the bodies of the definitions"
  logInfo m!"OK: {t.getId} reaches the banned declarations only through the bodies of the definitions {ds.getElems.toList.map (·.getId)}"

-- `A_to_B_hsec` cannot pass any traversal: its statement `A` contains `toChartOr_orChart`, whose
-- statement contains the banned `isChart_orChart`, `mem_orChart` as proof terms
-- (`toChartOr hf hs (orChart B x) (isChart_orChart x) (mem_orChart x) = Equiv.refl _`).  It is
-- factored through `A'` (as in V3_64).  `A'_to_B_hsec` and `B_to_existsTwo_tame` mention `Orx`, whose
-- body passes `isChart_orChart`, `mem_orChart` directly to `chartPtOf` (not a `_proof_N`), so they
-- fail `#rt_check_soft` and pass the traversal with the body of `Orx` not unfolded.
/-- error: rt_check_soft FAIL: RoundTrip.V6_55.A'_to_B_hsec uses [Polyfold.isChart_orChart, Polyfold.mem_orChart] -/
#guard_msgs in
#rt_check_soft RoundTrip.V6_55.A'_to_B_hsec [Polyfold.isChart_orChart, Polyfold.mem_orChart,
  Polyfold.toChartOr_orChart, Polyfold.toChartOr_trans, Polyfold.exists_two_orx]
/-- error: rt_check_soft FAIL: RoundTrip.V6_55.B_to_existsTwo_tame uses [Polyfold.isChart_orChart, Polyfold.mem_orChart] -/
#guard_msgs in
#rt_check_soft RoundTrip.V6_55.B_to_existsTwo_tame [Polyfold.isChart_orChart, Polyfold.mem_orChart,
  Polyfold.toChartOr_orChart, Polyfold.toChartOr_trans, Polyfold.exists_two_orx]
#rt_check_except_defs RoundTrip.V6_55.A'_to_B_hsec [Polyfold.Orx] [Polyfold.isChart_orChart, Polyfold.mem_orChart,
  Polyfold.toChartOr_orChart, Polyfold.toChartOr_trans, Polyfold.exists_two_orx]
#rt_check_except_defs RoundTrip.V6_55.B_to_existsTwo_tame [Polyfold.Orx] [Polyfold.isChart_orChart, Polyfold.mem_orChart,
  Polyfold.toChartOr_orChart, Polyfold.toChartOr_trans, Polyfold.exists_two_orx]
#rt_overlap RoundTrip.V6_55.B_to_existsTwo_tame [Polyfold.isChart_orChart, Polyfold.mem_orChart,
  Polyfold.toChartOr_orChart, Polyfold.toChartOr_trans, Polyfold.exists_two_orx]

end RoundTrip.V6_55
