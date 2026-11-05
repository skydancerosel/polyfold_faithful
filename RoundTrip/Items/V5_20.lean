import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_20

namespace RoundTrip.V5_20
open Polyfold

/-- The project's statement (Lemma 5.11), universes instantiated at `0`. -/
def A : Prop := type_of% @Polyfold.lemma_5_11.{0, 0}

theorem A_holds : A := @Polyfold.lemma_5_11.{0, 0}

#check A

/-- Not the item (diagnostic): B's intended reading (`N(s(y)) < N(e) + ε` for all `y`) with the
project's pointwise bump hypothesis `AdmitsBumpFunctions` in place of B's
`AdmitsBumpFunctionsWeak`. -/
def BIntendedStrong : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (N : Bd.One → ℝ),
    IsTameStrongBundle Bd → PX.AdmitsBumpFunctions → Bd.IsAuxNorm N →
    ∀ x ∈ PX.smoothSet, ∀ e : Bd.One, P (Bd.oneVal e) = x →
      (∀ m : ℕ, Bd.oneVal e ∈ Bd.doubleLevel m m) →
      ∀ ε : ℝ, 0 < ε → ∀ U : Set X, IsOpen U → x ∈ U →
        ∃ s : X → Y, Bd.IsScPlusSection s ∧ s x = Bd.oneVal e ∧ sectionSupport P s ⊆ U ∧
          ∀ y : X, NLt Bd N (s y) (N e + ε)

/-- B's notion of a smooth vector (`e ∈ Y_{m,m}` for all `m`) gives the project's
(`e ∈ (Y[0])_∞`). -/
theorem mem_smoothSet_of_doubleLevel {X : Type} [TopologicalSpace X] [T2Space X]
    [ParacompactSpace X] {PX : MPolyfold X} {Y : Type} [TopologicalSpace Y] [T2Space Y]
    [ParacompactSpace Y] {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) {y : Y} (hy : ∀ m : ℕ, y ∈ Bd.doubleLevel m m) :
    y ∈ Bd.toMPolyfold0.smoothSet := by
  refine Set.mem_iInter.2 fun m => ?_
  obtain ⟨c, hc, hxc⟩ := StrongBundle.exists_chart_mem Bd (P y)
  have hes : y ∈ c.toPartialEquiv.source := c.mem_source_of_proj hxc
  rw [Bd.toMPolyfold0.mem_levelSet_iff (Bd.isChart_toMChart hc) hes]
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hy m c hc hes
  refine ⟨((a, b) : (c.φ.model.E.prod c.F) m), ?_⟩
  refine (ScBanach.prod_toBase c.φ.model.E c.F m (a, b)).trans ?_
  exact Prod.ext ha hb

/-- `A ⇒ BIntendedStrong` (hence `A ⇒ B` once the bump hypothesis is strengthened): the tameness
hypothesis is ignored, B's smooth `e` is A's smooth `e`, and A's bound at every `y` is B's. -/
theorem A_to_BIntendedStrong : A → BIntendedStrong := by
  intro hA X _ _ _ PX Y _ _ _ P _ _ Bd N _hT hbump hN x hx e hPe _hlev ε hε U hU hxU
  obtain ⟨he1, s, hs, hsx, hsupp, hbd⟩ :=
    hA hbump hN hx (mem_smoothSet_of_doubleLevel Bd _hlev) hPe hε hU hxU
  exact ⟨s, hs, hsx, hsupp, fun y => ⟨hs.mem_oneSet y, hbd y (hs.mem_oneSet y)⟩⟩

/-! `A ⇒ B` is not proved: B assumes only `AdmitsBumpFunctionsWeak` ("not identically zero"),
A needs `AdmitsBumpFunctions` (`f(x) ≠ 0`); no project lemma (and no evident argument) turns weak
bumps into bumps non-zero at a given point.  With that one hypothesis strengthened the
implication holds (`A_to_BIntendedStrong`, which also gives B's literal bound at `x`).

`B ⇒ A` is not proved: B speaks only of tame strong bundles over tame `X`
(`IsTameStrongBundle`), A of every strong bundle (the project's proof uses no tameness); and B's
literal norm bound is at the given `x` only, where it is vacuous (`s(x) = e`), while A bounds
`N(s(y))` at every `y`.  The second gap is glue (cut off B's section by a bump `β` with
`β(x) = 1` supported where `N(s) < N(e) + ε`, using A's strong bumps), the first is a genuine
generality difference. -/

#rt_check RoundTrip.V5_20.A_to_BIntendedStrong [Polyfold.lemma_5_11]

end RoundTrip.V5_20
