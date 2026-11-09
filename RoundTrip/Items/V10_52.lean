import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_52

/-! Round trip for V10_52 (2021 §10.5, p. 504: `[D]` covers `[d]`; the map `|[D]|`).

The item lists the definitions `SDiagram.base`, `SDiagram.total`, `GenSBMap.base`,
`GenSBMap.total`, `SDiagram.orbitMap`, `GenSBMap.orbitMap`, `SEP.baseEP`, `SEP.totalEP`
(vocabulary) and seven theorems; `A` is the conjunction of their types, universes at `0`:
`IsRefinement.base` (a refinement covers a refinement of the base diagrams), `Equiv.base`,
`Equiv.total`, `SDiagram.continuous_orbitMap`, `Equiv.orbitMap_eq` (`|D|` depends only on the
class), `GenSBMap.orbitMap_eq_total` (`|[D]|` is the orbit map of the generalized map of total
spaces), `GenSBMap.continuous_orbitMap`.

* `A_to_B`: (a) from `Equiv.base` and `homMk_eq_homMk_iff` (B's `baseDiagB D` is `D.base` up to
  the proof field); (b) by `rfl`; (c) from `|Φ|` being a homeomorphism (the field
  `isHomeomorph_orbitMap` of the equivalence of total ep-groupoids; not an item theorem); (d)
  from the project's `Diagram.orbitMap_orbitMap_F` for `D.total`; (e) from `Equiv.orbitMap_eq`
  and (d).
* `B_to_A`: `Equiv.base` from B (a); `Equiv.orbitMap_eq` from B (c) (surjectivity), (d), (e).
  The other five conjuncts are not consequences of `B` (B does not mention refinements of base
  diagrams, equivalence of the total diagrams, continuity, or `GenSBMap.total`) and are re-proved
  outright from non-item project lemmas: `IsRefinement.base` from `SEP.NatEquiv.base`,
  `Equiv.total` from `IsRefinement.total`, continuity from `Diagram.continuous_orbitMap`,
  `orbitMap_eq_total` by `Quot.inductionOn` and `rfl`.

**Harness note.**  The statements contain the definitions `GenSBMap.base`, `GenSBMap.total`
(in `A` and `B`) and `GenSBMap.orbitMap` (in `A` and `B`), `Quot.lift`s whose well-definedness
proofs are the banned `Equiv.base`, `Equiv.total` (abstracted into `GenSBMap.base._proof_1`,
`GenSBMap.total._proof_1`) and `Equiv.orbitMap_eq` (passed as a plain application in the body of
`GenSBMap.orbitMap`, not abstracted; it reaches `Equiv.total` in turn).  So every term mentioning
`A` or `B` reaches them: plain `#rt_check` fails on both directions, and so does `#rt_check_soft`
(because of `GenSBMap.orbitMap`); both recorded with `#guard_msgs`.  As in V7_40 and V8_25, the
local `#rt_check_except_defs` (the harness `rtCollect` with the bodies of these three statement
definitions not unfolded) passes on both directions: the proofs use the banned theorems only as
hypotheses taken from `A` (in `A_to_B`), never as constants. -/

namespace RoundTrip.V10_52
open Polyfold CategoryTheory SBLocalization

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.SBLocalization.SDiagram.IsRefinement.base.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.Equiv.base.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.Equiv.total.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.continuous_orbitMap.{0}) ∧
  (type_of% @Polyfold.SBLocalization.SDiagram.Equiv.orbitMap_eq.{0}) ∧
  (type_of% @Polyfold.SBLocalization.GenSBMap.orbitMap_eq_total.{0}) ∧
  (type_of% @Polyfold.SBLocalization.GenSBMap.continuous_orbitMap.{0})

theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.SDiagram.IsRefinement.base.{0},
    @Polyfold.SBLocalization.SDiagram.Equiv.base.{0},
    @Polyfold.SBLocalization.SDiagram.Equiv.total.{0},
    @Polyfold.SBLocalization.SDiagram.continuous_orbitMap.{0},
    @Polyfold.SBLocalization.SDiagram.Equiv.orbitMap_eq.{0},
    @Polyfold.SBLocalization.GenSBMap.orbitMap_eq_total.{0},
    @Polyfold.SBLocalization.GenSBMap.continuous_orbitMap.{0}⟩

/-! ### Glue (no item theorem) -/

/-- `|D|(|Φ(w'')|) = |Ψ(w'')|`, from `Diagram.orbitMap_orbitMap_F` for the total diagram. -/
theorem orbitMap_π_Φ {A A' : SEP.{0}} (D : SDiagram A A') (w'' : D.B.W) :
    D.orbitMap (A.E.toEpGroupoid.π (D.Φ.Φ.obj w'')) = A'.E.toEpGroupoid.π (D.Ψ.Φ.obj w'') := by
  have h := D.total.orbitMap_orbitMap_F (D.B.E.toEpGroupoid.π w'')
  change D.total.orbitMap ((SEP.Hom.Φ D.Φ).orbitMap (D.B.E.toEpGroupoid.π w'')) =
    (SEP.Hom.Φ D.Ψ).orbitMap (D.B.E.toEpGroupoid.π w'') at h
  rw [GroupoidFunctor.orbitMap_π, GroupoidFunctor.orbitMap_π] at h
  exact h

/-- `|Φ|` is onto, on representatives. -/
theorem orbit_surj {A A' : SEP.{0}} (D : SDiagram A A') (w : A.W) :
    ∃ w'' : D.B.W, A.E.toEpGroupoid.π (D.Φ.Φ.obj w'') = A.E.toEpGroupoid.π w := by
  obtain ⟨r, hr⟩ := D.hΦ.isEquivalence.isHomeomorph_orbitMap.surjective (A.E.toEpGroupoid.π w)
  obtain ⟨w'', rfl⟩ := GroupoidStr.surjective_π _ r
  refine ⟨w'', ?_⟩
  rw [← GroupoidFunctor.orbitMap_π]
  exact hr

/-- `|Φ|` is one-to-one, on representatives. -/
theorem orbit_inj {A A' : SEP.{0}} (D : SDiagram A A') (w₁ w₂ : D.B.W)
    (h : A.E.toEpGroupoid.π (D.Φ.Φ.obj w₁) = A.E.toEpGroupoid.π (D.Φ.Φ.obj w₂)) :
    D.B.E.toEpGroupoid.π w₁ = D.B.E.toEpGroupoid.π w₂ := by
  apply D.hΦ.isEquivalence.isHomeomorph_orbitMap.injective
  rw [GroupoidFunctor.orbitMap_π, GroupoidFunctor.orbitMap_π]
  exact h

theorem A_to_B : A → B := by
  rintro ⟨-, hbase, -, -, horb, -, -⟩ A A'
  refine ⟨fun D D' h => EPLocalization.EPLoc.homMk_eq_homMk_iff.2 (hbase h), fun D => rfl,
    fun D => ⟨orbit_surj D, orbit_inj D⟩, fun D w'' => orbitMap_π_Φ D w'', ?_⟩
  intro D D' h w₁ w₂ hw
  rw [← orbitMap_π_Φ D w₁, ← orbitMap_π_Φ D' w₂, hw, horb h]

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `IsRefinement.base`, re-proved outright
    intro A A' D' D h
    obtain ⟨H, hH, hΦ, hΨ⟩ := h
    exact ⟨SEP.Hom.ϕ H, hH.isEquivalence_base, hΦ.base, hΨ.base⟩
  · -- `Equiv.base`, from B (a)
    intro A A' D D' h
    exact EPLocalization.EPLoc.homMk_eq_homMk_iff.1 ((hB A A').1 D D' h)
  · -- `Equiv.total`, re-proved outright
    intro A A' D D' h
    obtain ⟨D'', h₁, h₂⟩ := h
    exact ⟨D''.total, h₁.total, h₂.total⟩
  · intro A A' D
    exact D.total.continuous_orbitMap
  · -- `Equiv.orbitMap_eq`, from B (c), (d), (e)
    intro A A' D D' h
    funext q
    obtain ⟨w, rfl⟩ := GroupoidStr.surjective_π _ q
    obtain ⟨w₁, hw₁⟩ := ((hB A A').2.2.1 D).1 w
    obtain ⟨w₂, hw₂⟩ := ((hB A A').2.2.1 D').1 w
    have e₁ := (hB A A').2.2.2.1 D w₁
    have e₂ := (hB A A').2.2.2.1 D' w₂
    have e := (hB A A').2.2.2.2 D D' h w₁ w₂ (hw₁.trans hw₂.symm)
    rw [hw₁] at e₁
    rw [hw₂] at e₂
    exact e₁.trans (e.trans e₂.symm)
  · intro A A' f
    exact Quot.inductionOn f fun _ => rfl
  · intro A A' f
    exact Quot.inductionOn (motive := fun f : GenSBMap A A' => Continuous f.orbitMap) f
      fun D => D.total.continuous_orbitMap

open Lean Elab Command in
/-- `#rt_check_except_defs T [nᵢ]`: the harness traversal `rtCollect` with the bodies of the
statement definitions `GenSBMap.orbitMap`, `GenSBMap.base`, `GenSBMap.total` not unfolded: the
proof of `T` reaches the banned `nᵢ` only through those bodies (their `Quot.lift`
well-definedness proofs). -/
elab "#rt_check_except_defs " t:ident " [" bs:ident,* "]" : command => do
  let env ← getEnv
  let some ci := env.find? t.getId | throwError "unknown {t.getId}"
  let roots := ((rtValue? ci).map (·.getUsedConstants)).getD #[]
  let used := rtCollect env roots.toList
    (((NameSet.empty.insert ``Polyfold.SBLocalization.GenSBMap.orbitMap).insert
      ``Polyfold.SBLocalization.GenSBMap.base).insert ``Polyfold.SBLocalization.GenSBMap.total)
  if used.contains ``sorryAx then throwError "FAIL: {t.getId} contains sorry"
  let bad := bs.getElems.toList.map (·.getId) |>.filter used.contains
  unless bad.isEmpty do
    throwError "FAIL: {t.getId} uses {bad} outside the bodies of GenSBMap.orbitMap/base/total"
  logInfo m!"OK: {t.getId} reaches the banned theorems only through the bodies of GenSBMap.orbitMap/base/total"

/--
error: rt_check FAIL: RoundTrip.V10_52.A_to_B uses [Polyfold.SBLocalization.SDiagram.IsRefinement.base,
 Polyfold.SBLocalization.SDiagram.Equiv.base,
 Polyfold.SBLocalization.SDiagram.Equiv.total,
 Polyfold.SBLocalization.SDiagram.Equiv.orbitMap_eq]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V10_52.A_to_B [Polyfold.SBLocalization.SDiagram.IsRefinement.base,
  Polyfold.SBLocalization.SDiagram.Equiv.base, Polyfold.SBLocalization.SDiagram.Equiv.total,
  Polyfold.SBLocalization.SDiagram.continuous_orbitMap,
  Polyfold.SBLocalization.SDiagram.Equiv.orbitMap_eq,
  Polyfold.SBLocalization.GenSBMap.orbitMap_eq_total,
  Polyfold.SBLocalization.GenSBMap.continuous_orbitMap]

/--
error: rt_check_soft FAIL: RoundTrip.V10_52.A_to_B uses [Polyfold.SBLocalization.SDiagram.Equiv.total,
 Polyfold.SBLocalization.SDiagram.Equiv.orbitMap_eq]
-/
#guard_msgs (whitespace := lax) in
#rt_check_soft RoundTrip.V10_52.A_to_B [Polyfold.SBLocalization.SDiagram.IsRefinement.base,
  Polyfold.SBLocalization.SDiagram.Equiv.base, Polyfold.SBLocalization.SDiagram.Equiv.total,
  Polyfold.SBLocalization.SDiagram.continuous_orbitMap,
  Polyfold.SBLocalization.SDiagram.Equiv.orbitMap_eq,
  Polyfold.SBLocalization.GenSBMap.orbitMap_eq_total,
  Polyfold.SBLocalization.GenSBMap.continuous_orbitMap]

/--
error: rt_check FAIL: RoundTrip.V10_52.B_to_A uses [Polyfold.SBLocalization.SDiagram.IsRefinement.base,
 Polyfold.SBLocalization.SDiagram.Equiv.base,
 Polyfold.SBLocalization.SDiagram.Equiv.total,
 Polyfold.SBLocalization.SDiagram.Equiv.orbitMap_eq]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V10_52.B_to_A [Polyfold.SBLocalization.SDiagram.IsRefinement.base,
  Polyfold.SBLocalization.SDiagram.Equiv.base, Polyfold.SBLocalization.SDiagram.Equiv.total,
  Polyfold.SBLocalization.SDiagram.continuous_orbitMap,
  Polyfold.SBLocalization.SDiagram.Equiv.orbitMap_eq,
  Polyfold.SBLocalization.GenSBMap.orbitMap_eq_total,
  Polyfold.SBLocalization.GenSBMap.continuous_orbitMap]

/--
error: rt_check_soft FAIL: RoundTrip.V10_52.B_to_A uses [Polyfold.SBLocalization.SDiagram.Equiv.total,
 Polyfold.SBLocalization.SDiagram.Equiv.orbitMap_eq]
-/
#guard_msgs (whitespace := lax) in
#rt_check_soft RoundTrip.V10_52.B_to_A [Polyfold.SBLocalization.SDiagram.IsRefinement.base,
  Polyfold.SBLocalization.SDiagram.Equiv.base, Polyfold.SBLocalization.SDiagram.Equiv.total,
  Polyfold.SBLocalization.SDiagram.continuous_orbitMap,
  Polyfold.SBLocalization.SDiagram.Equiv.orbitMap_eq,
  Polyfold.SBLocalization.GenSBMap.orbitMap_eq_total,
  Polyfold.SBLocalization.GenSBMap.continuous_orbitMap]

#rt_check_except_defs RoundTrip.V10_52.A_to_B [Polyfold.SBLocalization.SDiagram.IsRefinement.base,
  Polyfold.SBLocalization.SDiagram.Equiv.base, Polyfold.SBLocalization.SDiagram.Equiv.total,
  Polyfold.SBLocalization.SDiagram.continuous_orbitMap,
  Polyfold.SBLocalization.SDiagram.Equiv.orbitMap_eq,
  Polyfold.SBLocalization.GenSBMap.orbitMap_eq_total,
  Polyfold.SBLocalization.GenSBMap.continuous_orbitMap]
#rt_check_except_defs RoundTrip.V10_52.B_to_A [Polyfold.SBLocalization.SDiagram.IsRefinement.base,
  Polyfold.SBLocalization.SDiagram.Equiv.base, Polyfold.SBLocalization.SDiagram.Equiv.total,
  Polyfold.SBLocalization.SDiagram.continuous_orbitMap,
  Polyfold.SBLocalization.SDiagram.Equiv.orbitMap_eq,
  Polyfold.SBLocalization.GenSBMap.orbitMap_eq_total,
  Polyfold.SBLocalization.GenSBMap.continuous_orbitMap]
#rt_overlap RoundTrip.V10_52.B_to_A [Polyfold.SBLocalization.SDiagram.IsRefinement.base,
  Polyfold.SBLocalization.SDiagram.Equiv.base, Polyfold.SBLocalization.SDiagram.Equiv.total,
  Polyfold.SBLocalization.SDiagram.continuous_orbitMap,
  Polyfold.SBLocalization.SDiagram.Equiv.orbitMap_eq,
  Polyfold.SBLocalization.GenSBMap.orbitMap_eq_total,
  Polyfold.SBLocalization.GenSBMap.continuous_orbitMap]

end RoundTrip.V10_52
