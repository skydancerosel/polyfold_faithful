import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_1

/-! Round trip for V8_1 ((8.1)–(8.9), 2017 pp. 257–258: the tangent data `T(X, 𝐗)` and its
structure maps).

The listed definitions `EpGroupoid.tSrc`, `tTgt`, `tUnit`, `tInv`, `tBase`, `tComp`,
`MPolyfold.tangentMap`, `MPolyfold.tangentProj` are vocabulary.  `A` is the conjunction of the types
of the eight listed theorems (`tangent_ext`, `exists_tSrc_eq`, `src_tBase_eq`, `tComp_spec`,
`tBase_tComp`, `tSrc_tComp`, `tComp_eq`, `tUnit_eq`), universes at `0` (`B` lives in `Type`; the
tangent spaces are then in `Type 1`).

* `A → B`.  The witnesses are the project's `isScSmoothMap_src/tgt/inv`.  B's fibrewise bijectivity
  of `Ts` is `tangent_ext` (injectivity on a fibre), `exists_tSrc_eq` (surjectivity) and
  `levelVal_tangentProj_tSrc` (maps-to); "(8.4) implies `s ψ = t φ`" is `src_tBase_eq`; (8.5) for
  `tComp`, for `tangentGroupoidStr` and for `tangentEpGroupoid` is `tComp_spec` (the structures'
  `comp` is `tComp` by definition); B's unit characterization of `tUnit = Tu` is the project lemma
  pair `tBase_tUnit`, `tSrc_tUnit`; B's `Tt(1_a) = a` for *every* `v` with B's unit
  characterization uses `tUnit_eq` (such a `v` is `tUnit a`) and then `tTgt_tUnit`.  The rest
  (`PObj`, `PMor`, `src`, `tgt`, `inv`, `tBase`) is `rfl`.
* `B → A`.  `tangent_ext` is B's injectivity on the fibre over `tBase v` (proof irrelevance
  identifies B's `tangentMap hs` with `tSrc`); `exists_tSrc_eq` is B's surjectivity plus
  `level_ext`; `src_tBase_eq` and `tComp_spec` (hence `tBase_tComp`, `tSrc_tComp`) are B's clauses;
  `tComp_eq` and `tUnit_eq` are uniqueness from the derived `tangent_ext` and B's (8.5)/(8.8)
  clauses for the project's `tComp`/`tUnit`. -/

namespace RoundTrip.V8_1
open Polyfold

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.tangent_ext.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.exists_tSrc_eq.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.src_tBase_eq.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.tComp_spec.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.tBase_tComp.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.tSrc_tComp.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.tComp_eq.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.tUnit_eq.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.tangent_ext.{0}, @Polyfold.EpGroupoid.exists_tSrc_eq.{0},
    @Polyfold.EpGroupoid.src_tBase_eq.{0}, @Polyfold.EpGroupoid.tComp_spec.{0},
    @Polyfold.EpGroupoid.tBase_tComp.{0}, @Polyfold.EpGroupoid.tSrc_tComp.{0},
    @Polyfold.EpGroupoid.tComp_eq.{0}, @Polyfold.EpGroupoid.tUnit_eq.{0}⟩

/-! ### `A → B` -/

theorem A_to_B : A → B := by
  rintro ⟨hext, hexists, hsrc, hspec, -, -, -, hunit⟩
  intro Obj Mor _ _ _ _ _ _ X
  refine ⟨X.isScSmoothMap_src, X.isScSmoothMap_tgt, X.isScSmoothMap_inv, ?_, ?_, ?_, rfl, rfl,
    ?_, ?_, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · -- `Ts : T_φ𝐗 → T_{s φ}X` is a bijection
    intro φ hφ
    refine ⟨fun v hv => ?_, fun v hv w hw hvw => hext X (hv.trans hw.symm) hvw, fun a ha => ?_⟩
    · change X.PObj.levelVal 1 (X.PObj.tangentProj (X.tSrc v)) = X.src φ
      rw [X.levelVal_tangentProj_tSrc]
      exact congrArg X.src hv
    · obtain ⟨v, hv, hva⟩ := hexists X (φ := X.PMor.levelMk 1 φ hφ) ha
      refine ⟨v, ?_, hva⟩
      change X.PMor.levelVal 1 (X.PMor.tangentProj v) = φ
      rw [hv, MPolyfold.levelVal_levelMk]
  · intro k h hkh
    exact hsrc X hkh
  · rintro a v ⟨hb, hs⟩
    rw [← hunit X hb hs]
    exact X.tTgt_tUnit a
  · exact ⟨rfl, rfl, fun k h hkh => hspec X hkh, fun a => ⟨X.tBase_tUnit a, X.tSrc_tUnit a⟩, rfl⟩
  · exact ⟨rfl, rfl, fun k h hkh => hspec X hkh, fun a => ⟨X.tBase_tUnit a, X.tSrc_tUnit a⟩, rfl⟩
  · intro k h hkh
    exact hspec X hkh
  · exact fun a => ⟨X.tBase_tUnit a, X.tSrc_tUnit a⟩

/-! ### `B → A` -/

section FromB

variable (hB : B) {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
include hB

theorem ext_of_B {v w : X.PMor.TangentSpace} (hb : X.tBase v = X.tBase w)
    (hs : X.tSrc v = X.tSrc w) : v = w := by
  obtain ⟨_, _, _, hbij, -⟩ := hB Obj Mor X
  exact (hbij (X.tBase v) (X.tBase_mem_levelSet v)).injOn rfl hb.symm hs

theorem exists_of_B {φ : X.PMor.Level 1} {a : X.PObj.TangentSpace}
    (ha : X.PObj.levelVal 1 (X.PObj.tangentProj a) = X.src (X.PMor.levelVal 1 φ)) :
    ∃ v, X.PMor.tangentProj v = φ ∧ X.tSrc v = a := by
  obtain ⟨_, _, _, hbij, -⟩ := hB Obj Mor X
  obtain ⟨v, hv, hva⟩ := (hbij (X.PMor.levelVal 1 φ) (MPolyfold.levelVal_mem _)).surjOn ha
  exact ⟨v, MPolyfold.level_ext hv, hva⟩

theorem src_of_B {k h : X.PMor.TangentSpace} (hkh : X.tSrc k = X.tTgt h) :
    X.src (X.tBase k) = X.tgt (X.tBase h) := by
  obtain ⟨_, _, _, -, hc, -⟩ := hB Obj Mor X
  exact hc k h hkh

theorem spec_of_B {k h : X.PMor.TangentSpace} (hkh : X.tSrc k = X.tTgt h) :
    X.tBase (X.tComp k h) = X.comp (X.tBase k) (X.tBase h) ∧
      X.tSrc (X.tComp k h) = X.tSrc h := by
  obtain ⟨_, _, _, -, -, -, -, -, -, -, -, -, -, hc, -⟩ := hB Obj Mor X
  exact hc k h hkh

theorem unit_of_B {a : X.PObj.TangentSpace} {v : X.PMor.TangentSpace}
    (hb : X.tBase v = X.unit (X.PObj.levelVal 1 (X.PObj.tangentProj a))) (hs : X.tSrc v = a) :
    X.tUnit a = v := by
  obtain ⟨_, _, _, -, -, -, -, -, -, -, -, -, -, -, hu, -⟩ := hB Obj Mor X
  exact ext_of_B hB X ((hu a).1.trans hb.symm) ((hu a).2.trans hs.symm)

end FromB

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Obj Mor _ _ _ _ _ _ X v w hb hs
    exact ext_of_B hB X hb hs
  · intro Obj Mor _ _ _ _ _ _ X φ a ha
    exact exists_of_B hB X ha
  · intro Obj Mor _ _ _ _ _ _ X k h hkh
    exact src_of_B hB X hkh
  · intro Obj Mor _ _ _ _ _ _ X k h hkh
    exact spec_of_B hB X hkh
  · intro Obj Mor _ _ _ _ _ _ X k h hkh
    exact (spec_of_B hB X hkh).1
  · intro Obj Mor _ _ _ _ _ _ X k h hkh
    exact (spec_of_B hB X hkh).2
  · intro Obj Mor _ _ _ _ _ _ X k h v hkh hb hs
    exact ext_of_B hB X ((spec_of_B hB X hkh).1.trans hb.symm)
      ((spec_of_B hB X hkh).2.trans hs.symm)
  · intro Obj Mor _ _ _ _ _ _ X a v hb hs
    exact unit_of_B hB X hb hs

/-! ### The no-peeking check

`B` names the project's `tangentGroupoidStr` and `tangentEpGroupoid`, whose proof fields are
proved with the banned theorems (`comp_assoc := X.lemma_8_1_4 h h'`, `exists_isProperMap :=
X.lemma_8_1_8`, `isScSmoothComp := X.isScSmoothComp_tangent`, …).  Lean abstracts only non-trivial
proof terms into `_proof_N`; these fields are applications of a constant to variables and stay
inline, so `#rt_check_soft` (which softens only `_proof_N`) fails already for `B → B := id`
(`B_self` below).  The check `#rt_check_defthm_V8_1` is `#rt_check_soft` with one change: a
*theorem* occurring in the value of a project *definition* is soft as well (it can only occur
there as a proof, abstracted or not).  Both directions pass it, and the banned theorems are reached
only through the proof fields of `tangentGroupoidStr` / `tangentEpGroupoid` (and of the
definitions they use). -/

open Lean Elab Command in
/-- `rtCollectSoft`, with every theorem in the value of a project definition soft. -/
partial def collectDefThm (env : Environment) (todo : List (Name × Bool)) (hard soft : NameSet) :
    NameSet × NameSet := Id.run do
  let mut todo := todo
  let mut hard := hard
  let mut soft := soft
  while true do
    match todo with
    | [] => break
    | (n, isHard) :: rest =>
      todo := rest
      if hard.contains n then continue
      if !isHard && soft.contains n then continue
      if isHard then hard := hard.insert n else soft := soft.insert n
      let some ci := env.find? n | continue
      let inProject := match env.getModuleIdxFor? n with
        | none => true
        | some i =>
          let m := env.header.moduleNames[i.toNat]!
          (`Polyfold).isPrefixOf m || (`RoundTrip).isPrefixOf m
      unless inProject do continue
      let isDef := match ci with | .defnInfo _ => true | _ => false
      let isThm (c : Name) : Bool := match env.find? c with | some (.thmInfo _) => true | _ => false
      let tys := ci.type.getUsedConstants.toList.map (·, isHard)
      let vals := (((rtValue? ci).map (·.getUsedConstants)).getD #[]).toList.map fun c =>
        (c, isHard && !(isDef && (rtIsDefProof c || isThm c)))
      todo := tys ++ vals ++ todo
  return (hard, soft)

open Lean Elab Command in
elab "#rt_check_defthm_V8_1 " t:ident " [" bs:ident,* "]" : command => do
  let env ← getEnv
  let some ci := env.find? t.getId | throwError "unknown {t.getId}"
  let roots := ((rtValue? ci).map (·.getUsedConstants)).getD #[]
  let (hard, soft) := collectDefThm env (roots.toList.map (·, true)) {} {}
  if hard.contains ``sorryAx || soft.contains ``sorryAx then
    throwError "rt_check_defthm FAIL: {t.getId} contains sorry (or failed to elaborate)"
  let banned := bs.getElems.toList.map (·.getId)
  let badHard := banned.filter hard.contains
  let badSoft := banned.filter fun b => soft.contains b && !hard.contains b
  unless badHard.isEmpty do throwError "rt_check_defthm FAIL: {t.getId} uses {badHard}"
  logInfo m!"rt_check_defthm OK: {t.getId} reaches {badSoft} only through proofs inside definitions"

/-- `B → B`: the official `#rt_check_soft` fails on it, so the failure is `B`'s vocabulary. -/
theorem B_self : B → B := id

/--
error: rt_check_soft FAIL: RoundTrip.V8_1.B_self uses [Polyfold.EpGroupoid.tangent_ext,
 Polyfold.EpGroupoid.exists_tSrc_eq,
 Polyfold.EpGroupoid.src_tBase_eq,
 Polyfold.EpGroupoid.tComp_spec,
 Polyfold.EpGroupoid.tBase_tComp,
 Polyfold.EpGroupoid.tSrc_tComp,
 Polyfold.EpGroupoid.tComp_eq]
-/
#guard_msgs in
#rt_check_soft RoundTrip.V8_1.B_self [Polyfold.EpGroupoid.tangent_ext,
  Polyfold.EpGroupoid.exists_tSrc_eq, Polyfold.EpGroupoid.src_tBase_eq,
  Polyfold.EpGroupoid.tComp_spec, Polyfold.EpGroupoid.tBase_tComp,
  Polyfold.EpGroupoid.tSrc_tComp, Polyfold.EpGroupoid.tComp_eq, Polyfold.EpGroupoid.tUnit_eq]

#rt_check_defthm_V8_1 RoundTrip.V8_1.A_to_B [Polyfold.EpGroupoid.tangent_ext,
  Polyfold.EpGroupoid.exists_tSrc_eq, Polyfold.EpGroupoid.src_tBase_eq,
  Polyfold.EpGroupoid.tComp_spec, Polyfold.EpGroupoid.tBase_tComp,
  Polyfold.EpGroupoid.tSrc_tComp, Polyfold.EpGroupoid.tComp_eq, Polyfold.EpGroupoid.tUnit_eq]
#rt_check_defthm_V8_1 RoundTrip.V8_1.B_to_A [Polyfold.EpGroupoid.tangent_ext,
  Polyfold.EpGroupoid.exists_tSrc_eq, Polyfold.EpGroupoid.src_tBase_eq,
  Polyfold.EpGroupoid.tComp_spec, Polyfold.EpGroupoid.tBase_tComp,
  Polyfold.EpGroupoid.tSrc_tComp, Polyfold.EpGroupoid.tComp_eq, Polyfold.EpGroupoid.tUnit_eq]
#rt_overlap RoundTrip.V8_1.B_to_A [Polyfold.EpGroupoid.tangent_ext,
  Polyfold.EpGroupoid.exists_tSrc_eq, Polyfold.EpGroupoid.src_tBase_eq,
  Polyfold.EpGroupoid.tComp_spec, Polyfold.EpGroupoid.tBase_tComp,
  Polyfold.EpGroupoid.tSrc_tComp, Polyfold.EpGroupoid.tComp_eq, Polyfold.EpGroupoid.tUnit_eq]

end RoundTrip.V8_1
