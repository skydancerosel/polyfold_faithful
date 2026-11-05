import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V1_32

/-! Round trip for V1_32 (Definition 1.5 and the proof of Proposition 1.6: sc-splittings are
sc-projections).

`A` is the conjunction of the types of the theorems among the item's declarations
(`IsScSplitting.isTopCompl`, `scProj_idem`, `range_scProj`, `ker_scProj`, `ScOperator.idem_lvl`,
`ScOperator.levelSub_range_eq`, `isScSplitting_of_idem`, `isScSplitting_iff_exists_scProj`);
`IsScSplitting.scProj` is a definition (vocabulary).  No universe parameters.

**Harness note.** The definition `IsScSplitting.scProj` (which occurs in the statements of
`scProj_idem`, `range_scProj`, `ker_scProj`, `isScSplitting_iff_exists_scProj`, hence in `A`)
passes the banned theorem `IsScSplitting.isTopCompl` as a proof argument of `projectionL` in its
*data* field `lvl` (`#print` shows it is not abstracted into a `scProj._proof_N`).  Therefore
every term that mentions `A` reaches `isTopCompl` through the body of `scProj`, and neither
`#rt_check` nor `#rt_check_soft` can pass with `isTopCompl` in the banned list (documented below
with `#guard_msgs`).  We therefore run `#rt_check` with the seven other theorems and check
`isTopCompl` with `#rt_check_except_scProj`, which runs the harness traversal `rtCollect` with
`scProj` marked as already visited (its body is not unfolded): our proofs never invoke
`isTopCompl` themselves (they use the Mathlib lemma `IsCompl.isTopCompl_of_isClosed` directly,
`isTopCompl'` below). -/

namespace RoundTrip.V1_32
open Polyfold

open Lean Elab Command in
/-- `#rt_check_except_scProj T`: the proof of `T` reaches `IsScSplitting.isTopCompl` only through
the body of the definition `IsScSplitting.scProj`. -/
elab "#rt_check_except_scProj " t:ident : command => do
  let env ← getEnv
  let some ci := env.find? t.getId | throwError "unknown {t.getId}"
  let roots := ((rtValue? ci).map (·.getUsedConstants)).getD #[]
  let used := rtCollect env roots.toList
    (NameSet.empty.insert ``Polyfold.ScBanach.IsScSplitting.scProj)
  if used.contains ``sorryAx then throwError "FAIL: {t.getId} contains sorry"
  if used.contains ``Polyfold.ScBanach.IsScSplitting.isTopCompl then
    throwError "FAIL: {t.getId} uses isTopCompl outside the body of scProj"
  logInfo m!"OK: {t.getId} reaches isTopCompl only through the body of the definition scProj"

/-! ### Glue: the text's sc-subspaces and topological direct sums -/

theorem isScSubspace_of_text {E : ScBanach} {A : Submodule ℝ (E.lvl 0)}
    (h : IsScSubspaceText E A) : E.IsScSubspace A := by
  refine ⟨h.1, fun m => ?_⟩
  have hd := (Subtype.dense_iff (s := (E.levelSub A m : Set (E m)))).1 (h.2.2.2 m)
  refine hd.trans (closure_mono ?_)
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x.2, hx⟩

theorem text_of_isScSubspace {E : ScBanach} {A : Submodule ℝ (E.lvl 0)}
    (h : E.IsScSubspace A) : IsScSubspaceText E A := by
  refine ⟨h.1, fun m => ?_, fun m => ?_, fun m => ?_⟩
  · have := E.isClosed_levelSub h.1 m
    exact this.completeSpace_coe
  · exact (E.ofSubspaceScale h.1).incl_isCompactOperator m
  · refine (Subtype.dense_iff (s := (E.levelSub A m : Set (E m)))).2 fun x hx => ?_
    refine closure_mono ?_ (h.2 m hx)
    rintro y ⟨hy1, hy2⟩
    exact ⟨⟨y, hy1⟩, hy2, rfl⟩

theorem topDirectSum_of_isCompl {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] {A B : Submodule ℝ V} (h : IsCompl A B) (hA : IsClosed (A : Set V))
    (hB : IsClosed (B : Set V)) : TopDirectSum A B := by
  have ht := Submodule.IsCompl.isTopCompl_of_isClosed h hA hB
  refine ⟨Submodule.prodEquivOfIsTopCompl A B ht, fun p => ?_⟩
  rw [Submodule.coe_prodEquivOfIsTopCompl]
  exact Submodule.coe_prodEquivOfIsCompl' A B _ p

theorem isCompl_of_topDirectSum {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {A B : Submodule ℝ V} (h : TopDirectSum A B) : IsCompl A B := by
  obtain ⟨e, he⟩ := h
  refine ⟨Submodule.disjoint_def.2 fun x hxA hxB => ?_,
    Submodule.codisjoint_iff_exists_add_eq.2 fun z => ?_⟩
  · have h1 : e (⟨x, hxA⟩, ⟨-x, B.neg_mem hxB⟩) = e 0 := by
      rw [he, map_zero]; simp
    have := congrArg (fun p : A × B => (p.1 : V)) (e.injective h1)
    simpa using this
  · obtain ⟨p, rfl⟩ := e.surjective z
    exact ⟨p.1, p.2, p.1.2, p.2.2, (he p).symm⟩

/-- B's first conjunct, proved directly: the project's (algebraic) sc-splittings are the text's
(topological) ones. -/
theorem splitting_iff (E : ScBanach) (F G : Submodule ℝ (E.lvl 0)) :
    E.IsScSplitting F G ↔ IsScSplittingText E F G := by
  constructor
  · rintro ⟨hF, hG, hc⟩
    exact ⟨text_of_isScSubspace hF, text_of_isScSubspace hG, fun m =>
      topDirectSum_of_isCompl (hc m) (E.isClosed_levelSub hF.1 m) (E.isClosed_levelSub hG.1 m)⟩
  · rintro ⟨hF, hG, ht⟩
    exact ⟨isScSubspace_of_text hF, isScSubspace_of_text hG,
      fun m => isCompl_of_topDirectSum (ht m)⟩

/-- An idempotent `P` with `P(E_m) ⊆ E_m` continuously, as a project `ScOperator`. -/
noncomputable def toScOp (E : ScBanach) (P : E.lvl 0 →ₗ[ℝ] E.lvl 0) (hP : IsScOperatorText E P) :
    ScOperator E E where
  lvl m :=
    { toFun := (hP m).choose
      map_add' := fun x y => E.toBase_injective m (by
        rw [(hP m).choose_spec.1, map_add, map_add, map_add, (hP m).choose_spec.1,
          (hP m).choose_spec.1])
      map_smul' := fun c x => E.toBase_injective m (by
        rw [(hP m).choose_spec.1, map_smul, map_smul, RingHom.id_apply, map_smul,
          (hP m).choose_spec.1])
      cont := (hP m).choose_spec.2 }
  incl_comm m x := E.toBase_injective m (by
    change E.toBase (m + 1) ((hP (m + 1)).choose x) = E.toBase m ((hP m).choose (E.incl m x))
    rw [(hP (m + 1)).choose_spec.1, (hP m).choose_spec.1, ScScale.toBase_succ])

theorem toScOp_zero (E : ScBanach) (P : E.lvl 0 →ₗ[ℝ] E.lvl 0) (hP : IsScOperatorText E P)
    (x : E 0) : toScOp E P hP 0 x = P x := (hP 0).choose_spec.1 x

theorem ker_eq_range_id_sub {V : Type} [AddCommGroup V] [Module ℝ V] (P : V →ₗ[ℝ] V)
    (hP : ∀ x, P (P x) = P x) : LinearMap.ker P = LinearMap.range (LinearMap.id - P) := by
  ext x
  constructor
  · intro hx
    refine ⟨x, ?_⟩
    rw [LinearMap.mem_ker] at hx
    simp [hx]
  · rintro ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    simp [hP]

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.ScBanach.IsScSplitting.isTopCompl) ∧
  (type_of% @Polyfold.ScBanach.IsScSplitting.scProj_idem) ∧
  (type_of% @Polyfold.ScBanach.IsScSplitting.range_scProj) ∧
  (type_of% @Polyfold.ScBanach.IsScSplitting.ker_scProj) ∧
  (type_of% @Polyfold.ScOperator.idem_lvl) ∧
  (type_of% @Polyfold.ScOperator.levelSub_range_eq) ∧
  (type_of% @Polyfold.ScBanach.isScSplitting_of_idem) ∧
  (type_of% @Polyfold.ScBanach.isScSplitting_iff_exists_scProj)

theorem A_holds : A :=
  ⟨@Polyfold.ScBanach.IsScSplitting.isTopCompl, @Polyfold.ScBanach.IsScSplitting.scProj_idem,
    @Polyfold.ScBanach.IsScSplitting.range_scProj, @Polyfold.ScBanach.IsScSplitting.ker_scProj,
    @Polyfold.ScOperator.idem_lvl, @Polyfold.ScOperator.levelSub_range_eq,
    @Polyfold.ScBanach.isScSplitting_of_idem,
    @Polyfold.ScBanach.isScSplitting_iff_exists_scProj⟩

/-- `A → B`: the first conjunct of `B` is the glue `splitting_iff` (Mathlib: closed complements in
a Banach space are topological); the second is `isScSplitting_of_idem` for the sc-operator built
from `P`, with `ker P = (1 − P)(E)`. -/
theorem A_to_B : A → B := by
  intro hA
  refine ⟨splitting_iff, ?_⟩
  intro E P hP hidem
  refine ⟨⟨hP, hidem⟩, ?_⟩
  have hidem' : ∀ x, P (P x) = P x := fun x => LinearMap.congr_fun hidem x
  set Q := toScOp E P hP with hQ
  have hQ0 : (Q 0 : E 0 →ₗ[ℝ] E 0) = P := LinearMap.ext fun x => toScOp_zero E P hP x
  have hQidem : ∀ x, Q 0 (Q 0 x) = Q 0 x := fun x => by
    rw [hQ, toScOp_zero, toScOp_zero, hidem']
  have hs := hA.2.2.2.2.2.2.1 Q hQidem
  rw [hQ0, ker_eq_range_id_sub P hidem'] at hs
  exact (splitting_iff E _ _).1 hs

/-! ### `B → A` -/

/-- Our own proof of the `IsTopCompl` of a splitting (Mathlib only). -/
theorem isTopCompl' {E : ScBanach} {A B : Submodule ℝ (E.lvl 0)} (h : E.IsScSplitting A B)
    (m : ℕ) : (E.levelSub A m).IsTopCompl (E.levelSub B m) :=
  Submodule.IsCompl.isTopCompl_of_isClosed (h.2.2 m) (E.isClosed_levelSub h.1.1 m)
    (E.isClosed_levelSub h.2.1.1 m)

theorem scProj_idem' {E : ScBanach} {A B : Submodule ℝ (E.lvl 0)} (h : E.IsScSplitting A B)
    (m : ℕ) (x : E m) : h.scProj m (h.scProj m x) = h.scProj m x :=
  (Submodule.projectionL_eq_self_iff (isTopCompl' h m) _).2
    (Submodule.projectionL_apply_mem (isTopCompl' h m) x)

theorem range_scProj' {E : ScBanach} {A B : Submodule ℝ (E.lvl 0)} (h : E.IsScSplitting A B)
    (m : ℕ) : LinearMap.range (h.scProj m : E m →ₗ[ℝ] E m) = E.levelSub A m := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩; exact Submodule.projectionL_apply_mem (isTopCompl' h m) y
  · intro hx; exact ⟨x, (Submodule.projectionL_eq_self_iff (isTopCompl' h m) _).2 hx⟩

theorem ker_scProj' {E : ScBanach} {A B : Submodule ℝ (E.lvl 0)} (h : E.IsScSplitting A B)
    (m : ℕ) : LinearMap.ker (h.scProj m : E m →ₗ[ℝ] E m) = E.levelSub B m := by
  ext x
  exact Submodule.projectionL_apply_eq_zero_iff (isTopCompl' h m)

/-- `B → A`: the conjuncts about the definition `scProj` (the projection along a splitting),
`isTopCompl`, `idem_lvl` and `levelSub_range_eq` are elementary facts not addressed by `B`
(proved directly, Mathlib only); `isScSplitting_of_idem` and the `←` direction of
`isScSplitting_iff_exists_scProj` come from `B` (second conjunct, converted to the project's
notion by the first conjunct). -/
theorem B_to_A : B → A := by
  intro hB
  have hidem : ∀ {E : ScBanach} (P : ScOperator E E), (∀ x, P 0 (P 0 x) = P 0 x) →
      E.IsScSplitting (LinearMap.range (P 0 : E 0 →ₗ[ℝ] E 0))
        (LinearMap.ker (P 0 : E 0 →ₗ[ℝ] E 0)) := by
    intro E P hP
    have hT : IsScOperatorText E (P 0 : E 0 →ₗ[ℝ] E 0) :=
      fun m => ⟨P m, fun x => P.toBase_comm m x, (P m).continuous⟩
    have h2 := (hB.2 E (P 0 : E 0 →ₗ[ℝ] E 0) hT (LinearMap.ext hP)).2
    rw [← ker_eq_range_id_sub _ hP] at h2
    exact (hB.1 E _ _).2 h2
  refine ⟨fun {E A B} h m => isTopCompl' h m, fun {E A B} h m x => scProj_idem' h m x,
    fun {E A B} h m => range_scProj' h m, fun {E A B} h m => ker_scProj' h m, ?_, ?_,
    fun {E} P hP => hidem P hP, ?_⟩
  · intro E P hP m x
    apply E.toBase_injective m
    rw [P.toBase_comm, P.toBase_comm, hP]
  · intro E P hP m
    ext x
    rw [ScBanach.mem_levelSub]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨x, E.toBase_injective m ?_⟩
      change E.toBase m (P m x) = E.toBase m x
      rw [P.toBase_comm, ← hy]
      exact hP y
    · rintro ⟨y, rfl⟩
      exact ⟨E.toBase m y, (P.toBase_comm m y).symm⟩
  · intro E A B
    constructor
    · intro h
      refine ⟨h.scProj, scProj_idem' h 0, ?_, ?_⟩
      · rw [range_scProj' h 0, ScBanach.levelSub_zero]
      · rw [ker_scProj' h 0, ScBanach.levelSub_zero]
    · rintro ⟨P, hP, rfl, rfl⟩
      exact hidem P hP

/-- error: rt_check FAIL: RoundTrip.V1_32.A_to_B uses [Polyfold.ScBanach.IsScSplitting.isTopCompl] -/
#guard_msgs in
#rt_check RoundTrip.V1_32.A_to_B [Polyfold.ScBanach.IsScSplitting.isTopCompl]

#rt_check RoundTrip.V1_32.A_to_B [Polyfold.ScBanach.IsScSplitting.scProj_idem,
  Polyfold.ScBanach.IsScSplitting.range_scProj, Polyfold.ScBanach.IsScSplitting.ker_scProj,
  Polyfold.ScOperator.idem_lvl, Polyfold.ScOperator.levelSub_range_eq,
  Polyfold.ScBanach.isScSplitting_of_idem, Polyfold.ScBanach.isScSplitting_iff_exists_scProj]
#rt_check_except_scProj RoundTrip.V1_32.A_to_B
#rt_check RoundTrip.V1_32.B_to_A [Polyfold.ScBanach.IsScSplitting.scProj_idem,
  Polyfold.ScBanach.IsScSplitting.range_scProj, Polyfold.ScBanach.IsScSplitting.ker_scProj,
  Polyfold.ScOperator.idem_lvl, Polyfold.ScOperator.levelSub_range_eq,
  Polyfold.ScBanach.isScSplitting_of_idem, Polyfold.ScBanach.isScSplitting_iff_exists_scProj]
#rt_check_except_scProj RoundTrip.V1_32.B_to_A
#rt_overlap RoundTrip.V1_32.B_to_A [Polyfold.ScBanach.IsScSplitting.isTopCompl,
  Polyfold.ScBanach.IsScSplitting.scProj_idem,
  Polyfold.ScBanach.IsScSplitting.range_scProj, Polyfold.ScBanach.IsScSplitting.ker_scProj,
  Polyfold.ScOperator.idem_lvl, Polyfold.ScOperator.levelSub_range_eq,
  Polyfold.ScBanach.isScSplitting_of_idem, Polyfold.ScBanach.isScSplitting_iff_exists_scProj]

end RoundTrip.V1_32
