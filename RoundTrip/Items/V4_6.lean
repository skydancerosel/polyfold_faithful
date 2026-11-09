import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_6

/-!
Round trip for V4_6 (Remark 4.3).  Refreshed 2026-11-02 against HEAD (Remark 4.3's example entered
the comparison row).  The decls list two definitions (`ScBanach.liftOne`, `MPolyfold.toLevelOne`,
vocabulary) and eight theorems, so `A` is the conjunction of the types of
`MPolyfold.remark_4_1_3_levelVal`, `MPolyfold.remark_4_1_3_isScDiffeo`, `remark_4_1_3_const`,
`remark_4_1_3_example`, `remark_4_1_3_retract_example`, `IsLossFamily.isScSmooth`,
`exists_retract_smooth_not_scPlus_of_data` and `MPolyfold.mem_shift_levelSet_iff` (universes at `0`).

* A ⇒ B (proved, new): clauses 1, 2, 4 of B as before (`A_to_B_rest`); B's third clause ("possibly
  `X¹ ≠ X` although the underlying sets agree": an M-polyfold with `X₀ = X_∞` and a junk value `x₀`
  for which `1₀¹` is not an sc-diffeomorphism) now follows from A's `remark_4_1_3_retract_example`:
  the retract `O` is non-empty (`∅` is trivially an sc⁺-retract), and the one-chart M-polyfold of
  `O` (`retractPolyfold`, Proposition 4.8 in the chart, `retractPolyfold_smooth_not_toLevelOne`)
  has `X₀ = X_∞` and `1₀¹` not sc-smooth.  (`remark_4_1_3_example` alone does not suffice: its
  M-polyfold could be empty, while B's clause asks for a point of `X₁`.)
* B ⇒ A (not proved any more): B gives the first three conjuncts (`B_to_A_main`, the old `B_to_A`)
  and `remark_4_1_3_example` (`B_gives_example`; the junk value of `1₀¹` is irrelevant when
  `X₀ = X₁`).  It does not give the four auxiliary conjuncts: `IsLossFamily.isScSmooth` (an
  sc-smoothness criterion for families of operators with loss) and
  `exists_retract_smooth_not_scPlus_of_data` (the reduction of the example to its data) are lemmas
  about sc-Banach spaces that B does not mention; `remark_4_1_3_retract_example` asks for a retract
  in a whole sc-Banach space (`C = E`), whereas B's M-polyfold only yields a chart retract in a
  partial quadrant `C`; `mem_shift_levelSet_iff` (`(X¹)_m = X_{m+1}`) is not in B.
-/

namespace RoundTrip.V4_6
open Polyfold Set

def A : Prop :=
  type_of% @Polyfold.MPolyfold.remark_4_1_3_levelVal.{0} ∧
  type_of% @Polyfold.MPolyfold.remark_4_1_3_isScDiffeo.{0} ∧
  type_of% @Polyfold.remark_4_1_3_const ∧
  type_of% @Polyfold.remark_4_1_3_example ∧
  type_of% @Polyfold.remark_4_1_3_retract_example ∧
  type_of% @Polyfold.IsLossFamily.isScSmooth ∧
  type_of% @Polyfold.exists_retract_smooth_not_scPlus_of_data ∧
  type_of% @Polyfold.MPolyfold.mem_shift_levelSet_iff.{0}

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.remark_4_1_3_levelVal.{0}, @Polyfold.MPolyfold.remark_4_1_3_isScDiffeo.{0},
    @Polyfold.remark_4_1_3_const, @Polyfold.remark_4_1_3_example, @Polyfold.remark_4_1_3_retract_example,
    @Polyfold.IsLossFamily.isScSmooth, @Polyfold.exists_retract_smooth_not_scPlus_of_data,
    @Polyfold.MPolyfold.mem_shift_levelSet_iff.{0}⟩

/-- The first three conjuncts of `A` (the ones before the refresh). -/
def A_main : Prop :=
  type_of% @Polyfold.MPolyfold.remark_4_1_3_levelVal.{0} ∧
  type_of% @Polyfold.MPolyfold.remark_4_1_3_isScDiffeo.{0} ∧
  type_of% @Polyfold.remark_4_1_3_const

/-- The conjuncts of `A` that `A ⇒ B` uses (their statements do not mention `RemarkFourThreeData`,
see the harness note at the end). -/
def A' : Prop := A_main ∧ type_of% @Polyfold.remark_4_1_3_retract_example

theorem A_to_A' (hA : A) : A' := ⟨⟨hA.1, hA.2.1, hA.2.2.1⟩, hA.2.2.2.2.1⟩

section Glue

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem relOpen_univ : IsRelOpenInQuadrant (ScBanach.const V) univ univ :=
  ⟨isPartialQuadrant_univ _, ⟨univ, isOpen_univ, (inter_univ _).symm⟩⟩

/-- The single chart of the M-polyfold of `V`. -/
theorem isChart_self (hV : IsRelOpenInQuadrant (ScBanach.const V) univ univ) :
    (hV.toMPolyfold ⟨0, mem_univ _⟩).IsChart
      ((LocalModel.ofRelOpen hV).selfChart ⟨0, mem_univ _⟩) :=
  MPolyfold.isChart_of_mem _ (mem_singleton _)

/-- Every point of the M-polyfold of `V` lies on every level (definitional for `ScBanach.const`). -/
theorem mem_levelSet (hV : IsRelOpenInQuadrant (ScBanach.const V) univ univ) (m : ℕ)
    (x : (LocalModel.ofRelOpen hV).O) : x ∈ (hV.toMPolyfold ⟨0, mem_univ _⟩).levelSet m :=
  ⟨_, isChart_self hV, mem_univ x, ⟨x.1, ScBanach.const_toBase V m x.1⟩⟩

theorem smoothSet_eq (hV : IsRelOpenInQuadrant (ScBanach.const V) univ univ) :
    (hV.toMPolyfold ⟨0, mem_univ _⟩).smoothSet = univ :=
  eq_univ_of_forall fun x => mem_iInter.2 fun m => mem_levelSet hV m x

theorem liftOne_const (x : V) : (ScBanach.const V).liftOne x = x := by
  have := (ScBanach.const V).liftOne_toBase x
  rwa [ScBanach.const_toBase] at this

end Glue

/-- A gives clauses 1, 2 and 4 of B (from its first three conjuncts). -/
theorem A_to_B_rest (hA : A_main) :
    (∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X),
      P.shift.IsScSmoothMap P (P.levelVal 1)) ∧
    (∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X),
      P.smoothSet = Set.univ → ∀ x₀ : P.Level 1,
        (∀ x : X, P.levelVal 1 (P.toLevelOne x₀ x) = x) ∧
        (∀ y : P.Level 1, P.toLevelOne x₀ (P.levelVal 1 y) = y) ∧
        (P.IsScSmoothMap P.shift (P.toLevelOne x₀) →
          IsScDiffeoB P (P.toLevelOne x₀) (P.levelVal 1))) ∧
    (∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
      (hV : IsRelOpenInQuadrant (ScBanach.const V) Set.univ Set.univ),
      (hV.toMPolyfold ⟨0, Set.mem_univ _⟩).levelSet 1 = Set.univ ∧
      ∀ x₀ : (hV.toMPolyfold ⟨0, Set.mem_univ _⟩).Level 1,
        IsScDiffeoB (hV.toMPolyfold ⟨0, Set.mem_univ _⟩)
          ((hV.toMPolyfold ⟨0, Set.mem_univ _⟩).toLevelOne x₀)
          ((hV.toMPolyfold ⟨0, Set.mem_univ _⟩).levelVal 1)) := by
  obtain ⟨hA1, hA2, hA3⟩ := hA
  have diffeo : ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
      (P : MPolyfold X), (∀ x, x ∈ P.levelSet 1) → ∀ x₀ : P.Level 1,
      P.IsScSmoothMap P.shift (P.toLevelOne x₀) →
        IsScDiffeoB P (P.toLevelOne x₀) (P.levelVal 1) := by
    intro X _ _ _ P h1 x₀ hsm
    have d := hA2 h1 x₀ hsm
    exact ⟨d.isScSmoothOn, d.isScSmoothOn_inv, fun x => d.left_inv x (mem_univ x),
      fun y => d.right_inv y (mem_univ y)⟩
  refine ⟨fun X _ _ _ P => hA1 P, fun X _ _ _ P hsm x₀ => ?_, fun V _ _ _ hV => ?_⟩
  · have h1 : ∀ x, x ∈ P.levelSet 1 := fun x =>
      MPolyfold.smoothSet_subset_levelSet 1 (hsm ▸ mem_univ x)
    exact ⟨fun x => MPolyfold.levelVal_toLevelOne x₀ (h1 x),
      fun y => MPolyfold.toLevelOne_levelVal x₀ y, diffeo X _ h1 x₀⟩
  · have h1 : ∀ x, x ∈ (hV.toMPolyfold ⟨0, mem_univ _⟩).levelSet 1 := mem_levelSet hV 1
    refine ⟨eq_univ_of_forall h1, fun x₀ => diffeo _ _ h1 x₀ ?_⟩
    have hplus : IsScPlusRetract (ScBanach.const V) univ univ :=
      (hA3 V).2.2 univ univ hV.isScRetract
    exact ((MPolyfold.proposition_4_1_8_chart (isChart_self hV) x₀).1 hplus).2

/-- A gives B's third clause, from `remark_4_1_3_retract_example`: the one-chart M-polyfold of a
non-empty sc-retract `O = O_∞` that is not an sc⁺-retract. -/
theorem A_gives_B3 (hR : type_of% @Polyfold.remark_4_1_3_retract_example) :
    ∃ (X : Type) (_ : TopologicalSpace X) (_ : T2Space X) (_ : ParacompactSpace X)
      (P : MPolyfold X), P.smoothSet = Set.univ ∧
        ∃ x₀ : P.Level 1, ¬ IsScDiffeoB P (P.toLevelOne x₀) (P.levelVal 1) := by
  obtain ⟨E, O, hO, hsm, hnot⟩ := hR
  -- `O ≠ ∅`: the empty set is an sc⁺-retract (a retraction onto `∅` has `U = ∅`)
  have hne : O.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    obtain ⟨R, hR⟩ := hO
    have hU : R.U = ∅ := by
      refine eq_empty_of_forall_notMem fun x hx => ?_
      have h : R x ∈ R.retract := ⟨x, hx, rfl⟩
      rw [hR] at h; exact notMem_empty _ h
    refine hnot ⟨R, hR, ?_⟩
    show Polyfold.IsScPlus R.U R
    refine ⟨fun x hx => ?_, ?_⟩
    · rw [hU] at hx; exact absurd hx (notMem_empty x)
    · exact IsScSmooth.of_locally R.isScDomain fun x hx => by
        rw [hU] at hx; exact absurd hx (notMem_empty x)
  obtain ⟨o, ho⟩ := hne
  obtain ⟨hall, hnm⟩ := retractPolyfold_smooth_not_toLevelOne hO ⟨o, ho⟩ hsm hnot
  have h1 : (⟨o, ho⟩ : O) ∈ (retractPolyfold hO ⟨o, ho⟩).levelSet 1 :=
    MPolyfold.smoothSet_subset_levelSet 1 (hall _)
  exact ⟨O, inferInstance, inferInstance, inferInstance, retractPolyfold hO ⟨o, ho⟩,
    eq_univ_of_forall hall, (retractPolyfold hO ⟨o, ho⟩).levelMk 1 _ h1, fun hd => hnm _ hd.1⟩

/-- B from the conjuncts `A'` of `A`. -/
theorem A'_to_B : A' → B := fun h =>
  ⟨(A_to_B_rest h.1).1, (A_to_B_rest h.1).2.1, A_gives_B3 h.2, (A_to_B_rest h.1).2.2⟩

/-- **A ⇒ B.** -/
theorem A_to_B : A → B := fun h => A'_to_B (A_to_A' h)

/-- B gives the first three conjuncts of A (the `B_to_A` of the original audit). -/
theorem B_to_A_main : B → A_main := by
  rintro ⟨hB1, -, -, hB4⟩
  refine ⟨fun P => hB1 _ P, fun {X} _ _ _ {P} h1 x₀ hsm => ?_, fun V _ _ _ => ?_⟩
  · exact ⟨hsm, hB1 X P, mapsTo_univ _ _, mapsTo_univ _ _,
      fun x _ => MPolyfold.levelVal_toLevelOne x₀ (h1 x),
      fun y _ => MPolyfold.toLevelOne_levelVal x₀ y⟩
  refine ⟨rfl, liftOne_const, fun C O hO => ?_⟩
  -- `(V, V, V)` is an sc⁺-retract, from B's last clause and Proposition 4.8 in the chart
  have hV : IsRelOpenInQuadrant (ScBanach.const V) univ univ := relOpen_univ
  obtain ⟨hlev, hdiff⟩ := hB4 V hV
  have h0 : (⟨0, mem_univ _⟩ : (LocalModel.ofRelOpen hV).O) ∈
      (hV.toMPolyfold ⟨0, mem_univ _⟩).levelSet 1 := by rw [hlev]; exact mem_univ _
  let x₀ := (hV.toMPolyfold ⟨0, mem_univ _⟩).levelMk 1 _ h0
  have hsm := (hdiff x₀).1
  have hplus : IsScPlusRetract (ScBanach.const V) univ univ :=
    (MPolyfold.proposition_4_1_8_chart (isChart_self hV) x₀).2
      ⟨fun x _ => by rw [smoothSet_eq hV]; exact mem_univ x, hsm⟩
  -- every retraction `R` of `V` is sc⁺: `R = T ∘ R` with `T` the sc⁺-retraction onto `V`
  obtain ⟨T, hT, hTp⟩ := hplus
  obtain ⟨R, rfl⟩ := hO
  refine ⟨R, rfl, ?_⟩
  have hTr : ∀ y, y ∈ T.retract := fun y => by rw [hT]; exact mem_univ y
  have hTU : ∀ y, y ∈ T.U := fun y => T.retract_subset (hTr y)
  have h := IsScPlus.comp_isScSmooth R.isScDomain T.isScDomain hTp R.isScSmooth
    (fun x _ => hTU (R x))
  refine h.congr R.isScDomain fun x _ => ?_
  exact T.apply_eq_self_of_mem_retract (hTr _)

/-- B gives `remark_4_1_3_example`: B's third clause together with its second (if `1₀¹` were
sc-smooth it would be an sc-diffeomorphism); the junk value of `1₀¹` plays no role when every point
lies in `X₁`. -/
theorem B_gives_example (hB : B) : type_of% @Polyfold.remark_4_1_3_example := by
  obtain ⟨-, hB2, ⟨X, _, _, _, P, hsm, x₀, hnd⟩, -⟩ := hB
  refine ⟨X, inferInstance, inferInstance, inferInstance, P, fun x => hsm ▸ mem_univ x,
    fun x₀' hmap => hnd ?_⟩
  have h1 : ∀ x, x ∈ P.levelSet 1 := fun x =>
    MPolyfold.smoothSet_subset_levelSet 1 (hsm ▸ mem_univ x)
  have e : P.toLevelOne x₀' = P.toLevelOne x₀ := funext fun x => MPolyfold.level_ext (by
    rw [MPolyfold.levelVal_toLevelOne x₀' (h1 x), MPolyfold.levelVal_toLevelOne x₀ (h1 x)])
  rw [e] at hmap
  exact (hB2 X P hsm x₀).2.2 hmap

open Lean Elab Command in
/-- `#rt_check_except_defs T [d₁, …] [n₁, …]` (as in items V2_24, V2_53): the harness traversal
`rtCollect` with the bodies of the definitions `dᵢ` not unfolded; fails if the proof of `T` reaches
some `nᵢ` elsewhere. -/
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

#rt_check RoundTrip.V4_6.A'_to_B [Polyfold.MPolyfold.remark_4_1_3_levelVal,
  Polyfold.MPolyfold.remark_4_1_3_isScDiffeo, Polyfold.remark_4_1_3_const, Polyfold.remark_4_1_3_example,
  Polyfold.remark_4_1_3_retract_example, Polyfold.IsLossFamily.isScSmooth,
  Polyfold.exists_retract_smooth_not_scPlus_of_data, Polyfold.MPolyfold.mem_shift_levelSet_iff]
#rt_check RoundTrip.V4_6.A_to_B_rest [Polyfold.MPolyfold.remark_4_1_3_levelVal,
  Polyfold.MPolyfold.remark_4_1_3_isScDiffeo, Polyfold.remark_4_1_3_const, Polyfold.remark_4_1_3_example,
  Polyfold.remark_4_1_3_retract_example, Polyfold.IsLossFamily.isScSmooth,
  Polyfold.exists_retract_smooth_not_scPlus_of_data, Polyfold.MPolyfold.mem_shift_levelSet_iff]
-- Harness: `A_to_B` itself cannot pass `#rt_check`/`#rt_check_soft`: its binder type `A` contains
-- the type of `exists_retract_smooth_not_scPlus_of_data`, i.e. `RemarkFourThreeData`, whose body
-- uses the definition `IsLossFamily.retraction`, whose `isScSmooth` field is the (non-abstracted)
-- proof `h.isScSmooth_famRetr`, which uses the banned `IsLossFamily.isScSmooth`.  The traversal
-- with the body of `IsLossFamily.retraction` not unfolded passes:
#rt_check_except_defs RoundTrip.V4_6.A_to_B [Polyfold.IsLossFamily.retraction] [Polyfold.MPolyfold.remark_4_1_3_levelVal,
  Polyfold.MPolyfold.remark_4_1_3_isScDiffeo, Polyfold.remark_4_1_3_const, Polyfold.remark_4_1_3_example,
  Polyfold.remark_4_1_3_retract_example, Polyfold.IsLossFamily.isScSmooth,
  Polyfold.exists_retract_smooth_not_scPlus_of_data, Polyfold.MPolyfold.mem_shift_levelSet_iff]
/-- error: rt_check_soft FAIL: RoundTrip.V4_6.A_to_B uses [Polyfold.IsLossFamily.isScSmooth] -/
#guard_msgs in
#rt_check_soft RoundTrip.V4_6.A_to_B [Polyfold.MPolyfold.remark_4_1_3_levelVal,
  Polyfold.MPolyfold.remark_4_1_3_isScDiffeo, Polyfold.remark_4_1_3_const, Polyfold.remark_4_1_3_example,
  Polyfold.remark_4_1_3_retract_example, Polyfold.IsLossFamily.isScSmooth,
  Polyfold.exists_retract_smooth_not_scPlus_of_data, Polyfold.MPolyfold.mem_shift_levelSet_iff]
#rt_check RoundTrip.V4_6.B_to_A_main [Polyfold.MPolyfold.remark_4_1_3_levelVal,
  Polyfold.MPolyfold.remark_4_1_3_isScDiffeo, Polyfold.remark_4_1_3_const, Polyfold.remark_4_1_3_example,
  Polyfold.remark_4_1_3_retract_example, Polyfold.IsLossFamily.isScSmooth,
  Polyfold.exists_retract_smooth_not_scPlus_of_data, Polyfold.MPolyfold.mem_shift_levelSet_iff]
#rt_check RoundTrip.V4_6.B_gives_example [Polyfold.MPolyfold.remark_4_1_3_levelVal,
  Polyfold.MPolyfold.remark_4_1_3_isScDiffeo, Polyfold.remark_4_1_3_const, Polyfold.remark_4_1_3_example,
  Polyfold.remark_4_1_3_retract_example, Polyfold.IsLossFamily.isScSmooth,
  Polyfold.exists_retract_smooth_not_scPlus_of_data, Polyfold.MPolyfold.mem_shift_levelSet_iff]
#rt_overlap RoundTrip.V4_6.A'_to_B [Polyfold.MPolyfold.remark_4_1_3_levelVal,
  Polyfold.MPolyfold.remark_4_1_3_isScDiffeo, Polyfold.remark_4_1_3_const, Polyfold.remark_4_1_3_example,
  Polyfold.remark_4_1_3_retract_example, Polyfold.IsLossFamily.isScSmooth,
  Polyfold.exists_retract_smooth_not_scPlus_of_data, Polyfold.MPolyfold.mem_shift_levelSet_iff]
#rt_overlap RoundTrip.V4_6.B_to_A_main [Polyfold.MPolyfold.remark_4_1_3_levelVal,
  Polyfold.MPolyfold.remark_4_1_3_isScDiffeo, Polyfold.remark_4_1_3_const, Polyfold.remark_4_1_3_example,
  Polyfold.remark_4_1_3_retract_example, Polyfold.IsLossFamily.isScSmooth,
  Polyfold.exists_retract_smooth_not_scPlus_of_data, Polyfold.MPolyfold.mem_shift_levelSet_iff]

end RoundTrip.V4_6
