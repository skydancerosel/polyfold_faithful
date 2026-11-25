import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V16_21

set_option maxSynthPendingDepth 3

/-! Round trip for V16_21 (2021 Theorem 16.2.6, p. 721; 2017: Theorem 16.2: the de Rham complex
of a polyfold and the pull-back by sc-smooth maps).

The item lists the definitions `ScForm.d`, `MapRep.pullback`, `ScMap.pullback` (vocabulary) and
ten theorems; `A` is the conjunction of their types, at universe `0` (`B` lives in `Type`).

* `A_to_B`: `B`'s four conjuncts are `d_mk`, `d_comp_d` (pointwise), `pullback_mk` (after
  rewriting `F`) and `d_comp_pullback` (pointwise).
* `B_to_A`: `d_mk`, `d_comp_d`, `pullback_mk`, `d_comp_pullback` from `B`; the third conjunct of
  `theorem_16_2_6_complex` is `rfl`; `MapRep.pullback_eq_of_equiv` from `B`'s representative
  formula (both representatives compute the pull-back of the one class); `pullback_id`,
  `pullback_mk_comp`, `pullback_comp` from `B`'s representative formula with the generalized-map
  lemmas `formsPullback_id`, `formsPullback_comp` and `ScMap.comp_mk`.

**Harness note.** `ScMap.pullback` is a `Quotient.lift` whose well-definedness field
(`ScMap.pullback._proof_1`) is the banned `MapRep.pullback_eq_of_equiv`; both `A` and `B` mention
`ScMap.pullback`, so plain `#rt_check` fails (recorded with `#guard_msgs`) and `#rt_check_soft`
is used. -/

namespace RoundTrip.V16_21
open Polyfold Polyfold.PolyfoldClass CategoryTheory
open Polyfold.EPLocalization Polyfold.EPLocalization.EPLoc

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.PolyfoldClass.theorem_16_2_6_complex.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.ScForm.d_mk.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.ScForm.d_comp_d.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.MapRep.pullback_eq_of_equiv.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.ScMap.pullback_mk.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.ScMap.d_comp_pullback.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.ScMap.pullback_id.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.ScMap.pullback_mk_comp.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.ScMap.pullback_comp.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.theorem_16_2_6_pullback.{0})

theorem A_holds : A :=
  ⟨@Polyfold.PolyfoldClass.theorem_16_2_6_complex.{0},
    @Polyfold.PolyfoldClass.ScForm.d_mk.{0},
    @Polyfold.PolyfoldClass.ScForm.d_comp_d.{0},
    @Polyfold.PolyfoldClass.MapRep.pullback_eq_of_equiv.{0},
    @Polyfold.PolyfoldClass.ScMap.pullback_mk.{0},
    @Polyfold.PolyfoldClass.ScMap.d_comp_pullback.{0},
    @Polyfold.PolyfoldClass.ScMap.pullback_id.{0},
    @Polyfold.PolyfoldClass.ScMap.pullback_mk_comp.{0},
    @Polyfold.PolyfoldClass.ScMap.pullback_comp.{0},
    @Polyfold.PolyfoldClass.theorem_16_2_6_pullback.{0}⟩

theorem A_to_B : A → B := by
  rintro ⟨-, hdmk, hdd, -, hpmk, hdp, -⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Z _ c k p hp ω
    exact hdmk p hp ω
  · intro Z _ c k ω
    exact LinearMap.congr_fun (hdd (c := c) (k := k)) ω
  · intro Z W _ _ c d F p hp q hq φ hF k τ
    subst hF
    exact hpmk p hp q hq φ τ
  · intro Z W _ _ c d F k τ
    exact LinearMap.congr_fun (hdp F k) τ

theorem B_to_A : B → A := by
  rintro ⟨hdmk, hdd, hpmk, hdp⟩
  -- the pieces, from `B`
  have dmk : ∀ {Z : Type} [TopologicalSpace Z] {c : PolyfoldClass Z} {k : ℕ}
      (q : PolyfoldStructure Z) (hq : (⟦q⟧ : PolyfoldClass Z) = c) (ω : q.X.epFormsInfty k),
      ScForm.d (ScForm.mk q hq ω) = ScForm.mk q hq (q.X.epFormsInftyD k ω) :=
    fun q hq ω => hdmk _ _ _ q hq ω
  have dd : ∀ {Z : Type} [TopologicalSpace Z] {c : PolyfoldClass Z} {k : ℕ},
      (ScForm.d (c := c) (k := k + 1)).comp ScForm.d = 0 :=
    fun {_ _ c k} => LinearMap.ext fun ω => hdd _ c k ω
  have pmk : ∀ {Z W : Type} [TopologicalSpace Z] [TopologicalSpace W]
      {c : PolyfoldClass Z} {d : PolyfoldClass W} {k : ℕ}
      (p : PolyfoldStructure Z) (hp : (⟦p⟧ : PolyfoldClass Z) = c)
      (q : PolyfoldStructure W) (hq : (⟦q⟧ : PolyfoldClass W) = d) (φ : PSHom p q)
      (ω : q.X.epFormsInfty k),
      ScMap.pullback (ScMap.mk p hp q hq φ) k (ScForm.mk q hq ω) =
        ScForm.mk p hp (formsPullback φ.gen k ω) :=
    fun p hp q hq φ ω => hpmk _ _ _ _ _ p hp q hq φ rfl _ ω
  have dp : ∀ {Z W : Type} [TopologicalSpace Z] [TopologicalSpace W]
      {c : PolyfoldClass Z} {d : PolyfoldClass W} (F : ScMap c d) (k : ℕ),
      ScForm.d.comp (F.pullback k) = (F.pullback (k + 1)).comp ScForm.d :=
    fun F k => LinearMap.ext fun τ => hdp _ _ _ _ F k τ
  -- `MapRep.pullback` computes the pull-back of its class
  have rep : ∀ {Z W : Type} [TopologicalSpace Z] [TopologicalSpace W]
      {c : PolyfoldClass Z} {d : PolyfoldClass W} (a : MapRep c d) (k : ℕ),
      a.pullback k = ScMap.pullback (ScMap.mk a.p a.hp a.q a.hq a.φ) k := by
    intro Z W _ _ c d a k
    refine LinearMap.ext fun ω => ?_
    rw [MapRep.pullback_apply, ← ScForm.mk_toStructure a.q a.hq ω, pmk,
      ScForm.toStructure_mk]
  have eqv : ∀ {Z W : Type} [TopologicalSpace Z] [TopologicalSpace W]
      {c : PolyfoldClass Z} {d : PolyfoldClass W} {a b : MapRep c d}, a ≈ b → ∀ k : ℕ,
      a.pullback k = b.pullback k := by
    intro Z W _ _ c d a b hab k
    rw [rep a, rep b]
    exact congrArg (fun F => ScMap.pullback F k) (Quotient.sound hab)
  have pid : ∀ {Z : Type} [TopologicalSpace Z] (c : PolyfoldClass Z) (k : ℕ),
      (ScMap.id c).pullback k = LinearMap.id := by
    intro Z _ c k
    refine LinearMap.ext fun ω => ?_
    rw [LinearMap.id_apply, ← ScForm.mk_toStructure c.out (Quotient.out_eq c) ω]
    change ScMap.pullback (ScMap.mk _ _ _ _ (PSHom.id _)) k _ = _
    rw [pmk]
    change ScForm.mk _ _ (formsPullback (𝟙 _) k _) = _
    rw [formsPullback_id]
    rfl
  have pmkc : ∀ {Z W V : Type} [TopologicalSpace Z] [TopologicalSpace W] [TopologicalSpace V]
      {c : PolyfoldClass Z} {d : PolyfoldClass W} {e : PolyfoldClass V}
      (p : PolyfoldStructure Z) (hp : (⟦p⟧ : PolyfoldClass Z) = c)
      (q : PolyfoldStructure W) (hq : (⟦q⟧ : PolyfoldClass W) = d) (r : PolyfoldStructure V)
      (hr : (⟦r⟧ : PolyfoldClass V) = e) (a : PSHom p q) (b : PSHom q r) (k : ℕ),
      ScMap.pullback (ScMap.mk p hp r hr (a.comp b)) k =
        (ScMap.pullback (ScMap.mk p hp q hq a) k).comp (ScMap.pullback (ScMap.mk q hq r hr b) k) := by
    intro Z W V _ _ _ c d e p hp q hq r hr a b k
    refine LinearMap.ext fun ω => ?_
    rw [← ScForm.mk_toStructure r hr ω, LinearMap.comp_apply, pmk, pmk, pmk, PSHom.comp_gen,
      formsPullback_comp, LinearMap.comp_apply]
  have pcomp : ∀ {Z W V : Type} [TopologicalSpace Z] [TopologicalSpace W] [TopologicalSpace V]
      {c : PolyfoldClass Z} {d : PolyfoldClass W} {e : PolyfoldClass V}
      (hd : d.IsEffective) (F : ScMap c d) (G : ScMap d e) (k : ℕ),
      ScMap.pullback (ScMap.comp hd F G) k = (ScMap.pullback F k).comp (ScMap.pullback G k) := by
    intro Z W V _ _ _ c d e hd F G k
    obtain ⟨p, hp⟩ := Quotient.exists_rep c
    obtain ⟨q, hq⟩ := Quotient.exists_rep d
    obtain ⟨r, hr⟩ := Quotient.exists_rep e
    obtain ⟨a, rfl⟩ := ScMap.exists_rep F p hp q hq
    obtain ⟨b, rfl⟩ := ScMap.exists_rep G q hq r hr
    rw [ScMap.comp_mk hd, pmkc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Z _ c k
    exact ⟨fun q hq ω => dmk q hq ω, dd, fun _ _ => rfl⟩
  · intros; apply dmk
  · intros; exact dd
  · intros; apply eqv; assumption
  · intros; apply pmk
  · intros; apply dp
  · intros; apply pid
  · intros; apply pmkc
  · intros; apply pcomp
  · intro Z W _ _ c d F k
    refine ⟨dp F k, ?_, pid _ k⟩
    intro p hp q hq φ h ω
    subst h
    exact pmk p hp q hq φ ω

/-- The text's claim is carried by two conjuncts together, `theorem_16_2_6_complex` and
`theorem_16_2_6_pullback`; `B` against their conjunction. -/
def Amain : Prop :=
  (type_of% @Polyfold.PolyfoldClass.theorem_16_2_6_complex.{0}) ∧
    (type_of% @Polyfold.PolyfoldClass.theorem_16_2_6_pullback.{0})

theorem main_A_to_B : Amain → B := by
  rintro ⟨hc, hpb⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Z _ c k p hp ω
    exact (hc c k).1 p hp ω
  · intro Z _ c k ω
    exact LinearMap.congr_fun (hc c k).2.1 ω
  · intro Z W _ _ c d F p hp q hq φ hF k τ
    exact (hpb F k).2.1 p hp q hq φ hF.symm τ
  · intro Z W _ _ c d F k τ
    exact LinearMap.congr_fun (hpb F k).1 τ

theorem main_B_to_A : B → Amain := fun h =>
  let hA := B_to_A h
  ⟨hA.1, hA.2.2.2.2.2.2.2.2.2⟩

/-! ### The no-peeking check

`ScMap.pullback F k := Quotient.lift (fun a => a.pullback k) (fun _ _ h =>
MapRep.pullback_eq_of_equiv h k) F`: the banned `pullback_eq_of_equiv` sits in the *body* of the
definition `ScMap.pullback`, which both `A` and `B` mention.  Lean did not abstract it into a
`ScMap.pullback._proof_N`, so `#rt_check` and `#rt_check_soft` both fail on every term mentioning
`ScMap.pullback` (recorded with `#guard_msgs`).  `#rt_check_opaque` (as in `V7_5`) is `#rt_check`
except that the value of `ScMap.pullback` is not followed (its type is); it confirms that no
proof below reaches a banned theorem other than through that definition. -/

open Lean Elab Command in
/-- `rtCollect`, except that the values of the constants in `opq` are not traversed. -/
partial def rtCollectOpaque (env : Environment) (opq : List Name) (todo : List Name)
    (seen : NameSet) : NameSet := Id.run do
  let mut todo := todo
  let mut seen := seen
  while true do
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      if seen.contains n then continue
      seen := seen.insert n
      let some ci := env.find? n | continue
      let inProject := match env.getModuleIdxFor? n with
        | none => true
        | some i =>
          let m := env.header.moduleNames[i.toNat]!
          (`Polyfold).isPrefixOf m || (`RoundTrip).isPrefixOf m
      unless inProject do continue
      let vals := if opq.contains n then #[] else ((rtValue? ci).map (·.getUsedConstants)).getD #[]
      todo := (ci.type.getUsedConstants ++ vals).toList ++ todo
  return seen

open Lean Elab Command in
elab "#rt_check_opaque " t:ident " [" bs:ident,* "]" " opaque " " [" os:ident,* "]" : command => do
  let env ← getEnv
  let some ci := env.find? t.getId | throwError "unknown {t.getId}"
  let opq := os.getElems.toList.map (·.getId)
  let roots := ((rtValue? ci).map (·.getUsedConstants)).getD #[]
  let used := rtCollectOpaque env opq roots.toList {}
  if used.contains ``sorryAx then throwError "rt_check_opaque FAIL: {t.getId} contains sorry"
  let bad := bs.getElems.toList.map (·.getId) |>.filter used.contains
  if bad.isEmpty then
    logInfo m!"rt_check_opaque OK: {t.getId} avoids the banned declarations (values of {opq} not followed)"
  else throwError "rt_check_opaque FAIL: {t.getId} uses {bad}"

/--
error: rt_check FAIL: RoundTrip.V16_21.A_to_B uses [Polyfold.PolyfoldClass.MapRep.pullback_eq_of_equiv]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V16_21.A_to_B [Polyfold.PolyfoldClass.theorem_16_2_6_complex,
  Polyfold.PolyfoldClass.ScForm.d_mk, Polyfold.PolyfoldClass.ScForm.d_comp_d,
  Polyfold.PolyfoldClass.MapRep.pullback_eq_of_equiv, Polyfold.PolyfoldClass.ScMap.pullback_mk,
  Polyfold.PolyfoldClass.ScMap.d_comp_pullback, Polyfold.PolyfoldClass.ScMap.pullback_id,
  Polyfold.PolyfoldClass.ScMap.pullback_mk_comp, Polyfold.PolyfoldClass.ScMap.pullback_comp,
  Polyfold.PolyfoldClass.theorem_16_2_6_pullback]
/--
error: rt_check FAIL: RoundTrip.V16_21.B_to_A uses [Polyfold.PolyfoldClass.MapRep.pullback_eq_of_equiv]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V16_21.B_to_A [Polyfold.PolyfoldClass.theorem_16_2_6_complex,
  Polyfold.PolyfoldClass.ScForm.d_mk, Polyfold.PolyfoldClass.ScForm.d_comp_d,
  Polyfold.PolyfoldClass.MapRep.pullback_eq_of_equiv, Polyfold.PolyfoldClass.ScMap.pullback_mk,
  Polyfold.PolyfoldClass.ScMap.d_comp_pullback, Polyfold.PolyfoldClass.ScMap.pullback_id,
  Polyfold.PolyfoldClass.ScMap.pullback_mk_comp, Polyfold.PolyfoldClass.ScMap.pullback_comp,
  Polyfold.PolyfoldClass.theorem_16_2_6_pullback]
#rt_check_opaque RoundTrip.V16_21.A_to_B [Polyfold.PolyfoldClass.theorem_16_2_6_complex,
  Polyfold.PolyfoldClass.ScForm.d_mk, Polyfold.PolyfoldClass.ScForm.d_comp_d,
  Polyfold.PolyfoldClass.MapRep.pullback_eq_of_equiv, Polyfold.PolyfoldClass.ScMap.pullback_mk,
  Polyfold.PolyfoldClass.ScMap.d_comp_pullback, Polyfold.PolyfoldClass.ScMap.pullback_id,
  Polyfold.PolyfoldClass.ScMap.pullback_mk_comp, Polyfold.PolyfoldClass.ScMap.pullback_comp,
  Polyfold.PolyfoldClass.theorem_16_2_6_pullback]
  opaque [Polyfold.PolyfoldClass.ScMap.pullback]
#rt_check_opaque RoundTrip.V16_21.B_to_A [Polyfold.PolyfoldClass.theorem_16_2_6_complex,
  Polyfold.PolyfoldClass.ScForm.d_mk, Polyfold.PolyfoldClass.ScForm.d_comp_d,
  Polyfold.PolyfoldClass.MapRep.pullback_eq_of_equiv, Polyfold.PolyfoldClass.ScMap.pullback_mk,
  Polyfold.PolyfoldClass.ScMap.d_comp_pullback, Polyfold.PolyfoldClass.ScMap.pullback_id,
  Polyfold.PolyfoldClass.ScMap.pullback_mk_comp, Polyfold.PolyfoldClass.ScMap.pullback_comp,
  Polyfold.PolyfoldClass.theorem_16_2_6_pullback]
  opaque [Polyfold.PolyfoldClass.ScMap.pullback]
#rt_check_opaque RoundTrip.V16_21.main_A_to_B [Polyfold.PolyfoldClass.theorem_16_2_6_complex,
  Polyfold.PolyfoldClass.ScForm.d_mk, Polyfold.PolyfoldClass.ScForm.d_comp_d,
  Polyfold.PolyfoldClass.MapRep.pullback_eq_of_equiv, Polyfold.PolyfoldClass.ScMap.pullback_mk,
  Polyfold.PolyfoldClass.ScMap.d_comp_pullback, Polyfold.PolyfoldClass.ScMap.pullback_id,
  Polyfold.PolyfoldClass.ScMap.pullback_mk_comp, Polyfold.PolyfoldClass.ScMap.pullback_comp,
  Polyfold.PolyfoldClass.theorem_16_2_6_pullback]
  opaque [Polyfold.PolyfoldClass.ScMap.pullback]
#rt_check_opaque RoundTrip.V16_21.main_B_to_A [Polyfold.PolyfoldClass.theorem_16_2_6_complex,
  Polyfold.PolyfoldClass.ScForm.d_mk, Polyfold.PolyfoldClass.ScForm.d_comp_d,
  Polyfold.PolyfoldClass.MapRep.pullback_eq_of_equiv, Polyfold.PolyfoldClass.ScMap.pullback_mk,
  Polyfold.PolyfoldClass.ScMap.d_comp_pullback, Polyfold.PolyfoldClass.ScMap.pullback_id,
  Polyfold.PolyfoldClass.ScMap.pullback_mk_comp, Polyfold.PolyfoldClass.ScMap.pullback_comp,
  Polyfold.PolyfoldClass.theorem_16_2_6_pullback]
  opaque [Polyfold.PolyfoldClass.ScMap.pullback]
#rt_overlap RoundTrip.V16_21.B_to_A [Polyfold.PolyfoldClass.theorem_16_2_6_complex,
  Polyfold.PolyfoldClass.ScForm.d_mk, Polyfold.PolyfoldClass.ScForm.d_comp_d,
  Polyfold.PolyfoldClass.MapRep.pullback_eq_of_equiv, Polyfold.PolyfoldClass.ScMap.pullback_mk,
  Polyfold.PolyfoldClass.ScMap.d_comp_pullback, Polyfold.PolyfoldClass.ScMap.pullback_id,
  Polyfold.PolyfoldClass.ScMap.pullback_mk_comp, Polyfold.PolyfoldClass.ScMap.pullback_comp,
  Polyfold.PolyfoldClass.theorem_16_2_6_pullback]

end RoundTrip.V16_21
