import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V19_87

set_option maxSynthPendingDepth 3

/-! Round trip for V19_87 (2021 Proposition 19.7.26, p. 926: the M-polyfold structure of
`M(Ψ̂, Ψ̂')`).

The item lists the definitions `basePolyfold`, `fibSet`, `fibPolyfold`, `hatPolyfold`
(vocabulary) and the theorems `isSubMPolyfold_fibSet`, `isScDiffeoOn_toFibSet`,
`isLocalScDiffeo_pB`, `isScDiffeoOn_id_of_isLocalScDiffeo_pB`, `isTame_basePolyfold`,
`isTame_hatPolyfold`, `proposition_19_7_26` (main conjunct); `A` is the conjunction of their types
at universe `0`.

* `A_to_B` (and `main_A_to_B`, from `proposition_19_7_26` alone): the structure is the project's
  `hatPolyfold` (transported from the fibred-product sub-M-polyfold `M(Ψ, Ψ') ₛ×_τ̂ E` along the
  homeomorphism (19.26)); Hausdorff and paracompact from the non-item `t2Space_MHat`,
  `paracompactSpace_MHat`; `p` a local sc-diffeomorphism from `A`.  `B`'s hypothesis
  `HasClassUniformizers` for `F` gives the project's one for `F̂`; `B`'s metrizability hypothesis
  is the project's (`natTop` of a proof-irrelevant argument).
* `B_to_A`: not proved.  `B` is existential: some M-polyfold structure `S` with `p` a local
  sc-diffeomorphism.  `A` is about the specific `hatPolyfold`: it adds the uniqueness of the
  structure ("characterized by", the identity `S → hatPolyfold` is an sc-diffeomorphism), that
  `⟨p, s⟩` is an sc-diffeomorphism onto the sub-M-polyfold `M(Ψ, Ψ') ₛ×_τ̂ E`, the
  sub-M-polyfold property itself, and tameness; none of these is a consequence of `B`'s
  content.

**Harness note.**  The statements of `A` mention `fibPolyfold`/`hatPolyfold`, whose bodies use the
banned `isSubMPolyfold_fibSet` directly (`fibPolyfold := subPolyfold (isSubMPolyfold_fibSet x y)`),
so every term mentioning them reaches that theorem: plain `#rt_check` fails, recorded with
`#guard_msgs`.  `#rt_check_except` below runs the same traversal without unfolding the
vocabulary definitions `fibPolyfold`, `hatPolyfold`: it passes, so the proof takes `p`'s local sc-diffeomorphism from `A`
and uses no item theorem otherwise. -/

namespace RoundTrip.V19_87
open Polyfold GroupoidalCategory

def A : Prop :=
  (type_of% @Polyfold.GroupoidalCategory.CoveringBasicConstruction.isSubMPolyfold_fibSet.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.CoveringBasicConstruction.isScDiffeoOn_toFibSet.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.CoveringBasicConstruction.isLocalScDiffeo_pB.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.CoveringBasicConstruction.isScDiffeoOn_id_of_isLocalScDiffeo_pB.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.CoveringBasicConstruction.isTame_basePolyfold.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.CoveringBasicConstruction.isTame_hatPolyfold.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_26.{0})

theorem A_holds : A :=
  ⟨@Polyfold.GroupoidalCategory.CoveringBasicConstruction.isSubMPolyfold_fibSet.{0},
    @Polyfold.GroupoidalCategory.CoveringBasicConstruction.isScDiffeoOn_toFibSet.{0},
    @Polyfold.GroupoidalCategory.CoveringBasicConstruction.isLocalScDiffeo_pB.{0},
    @Polyfold.GroupoidalCategory.CoveringBasicConstruction.isScDiffeoOn_id_of_isLocalScDiffeo_pB.{0},
    @Polyfold.GroupoidalCategory.CoveringBasicConstruction.isTame_basePolyfold.{0},
    @Polyfold.GroupoidalCategory.CoveringBasicConstruction.isTame_hatPolyfold.{0},
    @Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_26.{0}⟩

/-- `HasClassUniformizers` for `F` gives it for `F̂`. -/
theorem hasClassUniformizers_of_toBasic {A B : GroupoidalCategory.{0}}
    {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr} (Bh : CoveringBasicConstruction P)
    (hB : Bh.toBasic.U.HasClassUniformizers) : Bh.HasClassUniformizers := fun z => by
  obtain ⟨β, hβ, Ψ, Ψh, hΨh, -⟩ := hB z
  exact ⟨β, hβ, Ψh, hΨh⟩

theorem main_A_to_B :
    (type_of% @Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_26.{0}) →
      B := by
  intro h A B P hP Bh hB hm x y
  have hU := hasClassUniformizers_of_toBasic Bh hB
  exact ⟨Bh.t2Space_MHat hP x y, Bh.paracompactSpace_MHat hP x y, Bh.hatPolyfold hP x y,
    (h Bh hP hU hm x y).2.1.1⟩

theorem A_to_B : A → B := by
  intro h A B P hP Bh _hB _hm x y
  exact ⟨Bh.t2Space_MHat hP x y, Bh.paracompactSpace_MHat hP x y, Bh.hatPolyfold hP x y,
    h.2.2.1 Bh hP x y⟩

open Lean Elab Command in
/-- `#rt_check` without unfolding the listed vocabulary definitions. -/
elab "#rt_check_except " t:ident " [" bs:ident,* "]" " except " " [" ds:ident,* "]" :
    command => do
  let env ← Lean.getEnv
  let some ci := env.find? t.getId | throwError "unknown {t.getId}"
  let roots := ((rtValue? ci).map (·.getUsedConstants)).getD #[]
  let skip : Lean.NameSet := ds.getElems.foldl (fun s d => s.insert d.getId) {}
  let used := rtCollect env roots.toList skip
  if used.contains ``sorryAx then throwError "rt_check_except FAIL: sorry"
  let bad := bs.getElems.toList.map (·.getId) |>.filter used.contains
  if bad.isEmpty then Lean.logInfo m!"rt_check_except OK: {t.getId} avoids the banned declarations"
  else throwError "rt_check_except FAIL: {t.getId} uses {bad}"

/--
error: rt_check FAIL: RoundTrip.V19_87.A_to_B uses [Polyfold.GroupoidalCategory.CoveringBasicConstruction.isSubMPolyfold_fibSet]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V19_87.A_to_B [Polyfold.GroupoidalCategory.CoveringBasicConstruction.isSubMPolyfold_fibSet,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.isScDiffeoOn_toFibSet,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.isLocalScDiffeo_pB,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.isScDiffeoOn_id_of_isLocalScDiffeo_pB,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.isTame_basePolyfold,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.isTame_hatPolyfold,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_26]
/--
error: rt_check_soft FAIL: RoundTrip.V19_87.A_to_B uses [Polyfold.GroupoidalCategory.CoveringBasicConstruction.isSubMPolyfold_fibSet]
-/
#guard_msgs (whitespace := lax) in
#rt_check_soft RoundTrip.V19_87.A_to_B [Polyfold.GroupoidalCategory.CoveringBasicConstruction.isSubMPolyfold_fibSet,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.isScDiffeoOn_toFibSet,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.isLocalScDiffeo_pB,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.isScDiffeoOn_id_of_isLocalScDiffeo_pB,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.isTame_basePolyfold,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.isTame_hatPolyfold,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_26]
#rt_check_except RoundTrip.V19_87.A_to_B [Polyfold.GroupoidalCategory.CoveringBasicConstruction.isSubMPolyfold_fibSet,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.isScDiffeoOn_toFibSet,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.isLocalScDiffeo_pB,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.isScDiffeoOn_id_of_isLocalScDiffeo_pB,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.isTame_basePolyfold,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.isTame_hatPolyfold,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_26] except
  [Polyfold.GroupoidalCategory.CoveringBasicConstruction.fibPolyfold,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.hatPolyfold]
#rt_check_except RoundTrip.V19_87.main_A_to_B [Polyfold.GroupoidalCategory.CoveringBasicConstruction.isSubMPolyfold_fibSet,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.isScDiffeoOn_toFibSet,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.isLocalScDiffeo_pB,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.isScDiffeoOn_id_of_isLocalScDiffeo_pB,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.isTame_basePolyfold,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.isTame_hatPolyfold,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_26] except
  [Polyfold.GroupoidalCategory.CoveringBasicConstruction.fibPolyfold,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.hatPolyfold]

end RoundTrip.V19_87
