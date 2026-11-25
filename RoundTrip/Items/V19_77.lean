import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V19_77

set_option maxSynthPendingDepth 3

/-! Round trip for V19_77 (2021 Proposition 19.7.15, p. 915: the structure maps of
`M(Ψ̂, Ψ̂')`).

The item lists `invHatHomeomorph` (a definition: vocabulary) and the theorems
`proposition_19_7_15_one`, `isLocalHomeomorph_srcHat`, `continuous_unitHat`,
`isLocalHomeomorph_tgtHat`, `isLocalHomeomorph_mulHat`, `proposition_19_7_15_hyp` (main
conjunct); `A` is the conjunction of their types at universe `0`.  The statements about `t̂`
(hence `ι̂`, `m̂` and the main conjunct) assume `IsCompatible` (every `t̂` is continuous); `B`
assumes nothing beyond the setting.

* `not_B`: `B` does not hold: for the project's `twistBasic` (a basic construction for the
  finite-to-one covering functor `absCovP`, two members of `F̂(0)` over the same `Ψ` twisted
  against each other), `t̂` is not a local homeomorphism
  (`proposition_19_7_15_two_without_compatible`, not an item theorem), contradicting `B` (2).
* `A_to_B` cannot hold (`A` holds, `B` does not): `not_A_to_B`.
* `B_to_A`: proved, using `B` for `ŝ`, `t̂` (with `IsCompatible` discarded), `ι̂`, `û`, `m̂`.
  `B` has no clause for `p` (the project's 19.7.15 (1) is "`p` is a surjective local
  homeomorphism and (19.26) a homeomorphism"; `B`'s (1) is the target description); these and
  the metrizability clauses come from the non-item `proposition_19_7_14`, `fibHomeomorph`,
  `metrizableSpace_MHat`, `BasicConstruction.metrizableSpace_M`. -/

namespace RoundTrip.V19_77
open Polyfold GroupoidalCategory

def A : Prop :=
  (type_of% @Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_15_one.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.CoveringBasicConstruction.isLocalHomeomorph_srcHat.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.CoveringBasicConstruction.continuous_unitHat.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.CoveringBasicConstruction.isLocalHomeomorph_tgtHat.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.CoveringBasicConstruction.isLocalHomeomorph_mulHat.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_15_hyp.{0})

theorem A_holds : A :=
  ⟨@Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_15_one.{0},
    @Polyfold.GroupoidalCategory.CoveringBasicConstruction.isLocalHomeomorph_srcHat.{0},
    @Polyfold.GroupoidalCategory.CoveringBasicConstruction.continuous_unitHat.{0},
    @Polyfold.GroupoidalCategory.CoveringBasicConstruction.isLocalHomeomorph_tgtHat.{0},
    @Polyfold.GroupoidalCategory.CoveringBasicConstruction.isLocalHomeomorph_mulHat.{0},
    @Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_15_hyp.{0}⟩

/-- `B` does not hold: `t̂` of `twistBasic` is not a local homeomorphism. -/
theorem not_B : ¬ B := by
  intro hB
  obtain ⟨hP, -, hn⟩ := proposition_19_7_15_two_without_compatible
  exact hn fun x y => ((hB _ _ absCovP hP twistBasic).2.1 x y).2

theorem not_A_to_B : ¬ (A → B) := fun h => not_B (h A_holds)

/-- From `B`: the clauses about `ŝ`, `t̂`, `ι̂`, `û`, `m̂` for the project's topology. -/
theorem B_clauses (hB : B) {A B : GroupoidalCategory.{0}}
    {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr} (Bh : CoveringBasicConstruction P)
    (hP : IsFiniteToOneCovering P) :
    (∀ x y : Bh.hatU.Unif, IsLocalHomeomorph (Bh.srcHat x y)) ∧
    (∀ x y : Bh.hatU.Unif, IsLocalHomeomorph (Bh.tgtHat x y)) ∧
    (∀ x y : Bh.hatU.Unif, ∃ e : Bh.MHat x y ≃ₜ Bh.MHat y x, ∀ a, e a = Bh.invHat x y a) ∧
    (∀ x : Bh.hatU.Unif, Continuous (Bh.unitHat x)) ∧
    (∀ x y z : Bh.hatU.Unif, IsLocalHomeomorph (Bh.mulHat x y z)) := by
  obtain ⟨-, h2, h3, h3', h4⟩ := hB A B P hP Bh
  exact ⟨fun x y => (h2 x y).1, fun x y => (h2 x y).2, h3, h3', h4⟩

/-- `û` is continuous, for any `P` (the project's proof of `continuous_unitHat`, copied). -/
theorem continuous_unitHat' {A B : GroupoidalCategory.{0}}
    {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr} (Bh : CoveringBasicConstruction P)
    (x : Bh.hatU.Unif) : Continuous (Bh.unitHat x) := by
  refine continuous_induced_rng.2 (Continuous.subtype_mk (Continuous.prodMk ?_ continuous_id) _)
  have h : (fun e => Bh.pB x x (Bh.unitHat x e)) =
      (fun o => Bh.toBasic.rep.toTr (GroupoidStr.TransitionSet.unit o : x.Ψh.Ψ.Trans x.Ψh.Ψ)) ∘
        x.Ψh.τ.obj :=
    funext fun e => x.Ψh.transMap_unit e
  change Continuous fun e => Bh.pB x x (Bh.unitHat x e)
  rw [h]
  exact (Bh.toBasic.rep.continuous_unit x.toUnif).comp (Bh.isLocalHomeomorph_τ x).continuous

theorem main_B_to_A : B →
    (type_of% @Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_15_hyp.{0}) := by
  intro hB A B P Bh hP _hC x y z
  obtain ⟨hs, ht, hi, hu, hm⟩ := B_clauses hB Bh hP
  exact ⟨⟨(Bh.proposition_19_7_14 hP x y).1, (Bh.proposition_19_7_14 hP x y).2,
      Bh.fibHomeomorph hP x y, fun _ => rfl⟩, ⟨hs x y, ht x y⟩, ⟨hi x y, hu x⟩, hm x y z,
    Bh.metrizableSpace_MHat hP x y, Bh.toBasic.metrizableSpace_M x.toUnif y.toUnif⟩

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun Bh hP x y => ⟨(Bh.proposition_19_7_14 hP x y).1, (Bh.proposition_19_7_14 hP x y).2,
      Bh.fibHomeomorph hP x y, fun _ => rfl⟩,
    fun Bh hP x y => (B_clauses hB Bh hP).1 x y, fun Bh x => ?_,
    fun Bh hP _ x y => (B_clauses hB Bh hP).2.1 x y,
    fun Bh hP _ x y z => (B_clauses hB Bh hP).2.2.2.2 x y z, main_B_to_A hB⟩
  -- `û` is continuous: `B` gives it only for a finite-to-one covering functor, which this
  -- conjunct does not assume; re-proved outright (the project's proof, copied).
  exact continuous_unitHat' Bh x


/-! ### `A ⇒ B` under `IsCompatible`

`B` restricted to compatible constructions (`IsCompatible`, every `t̂` continuous) follows from
`A`: (2)–(4) are `A`'s clauses, and the target description (1) is
`(ι × id) ∘ (19.26)_{Ψ̂', Ψ̂} ∘ ι̂`, a composition of homeomorphisms (`ι̂` by `A` under
`IsCompatible`). -/

/-- `B` for compatible basic constructions. -/
def BC : Prop :=
  ∀ (A B : GroupoidalCategory.{0}) (P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr),
    IsFiniteToOneCovering P →
    ∀ Bh : CoveringBasicConstruction P, Bh.IsCompatible →
      (∀ x y : Bh.hatU.Unif, ∃ e : MT Bh x y ≃ₜ TgtFib Bh x y,
        ∀ h : MT Bh x y, e h = toTgtFib Bh x y h) ∧
      (∀ x y : Bh.hatU.Unif,
        IsLocalHomeomorph (fun h : MT Bh x y => Bh.srcHat x y h) ∧
        IsLocalHomeomorph (fun h : MT Bh x y => Bh.tgtHat x y h)) ∧
      (∀ x y : Bh.hatU.Unif, ∃ e : MT Bh x y ≃ₜ MT Bh y x,
        ∀ h : MT Bh x y, e h = Bh.invHat x y h) ∧
      (∀ x : Bh.hatU.Unif, Continuous (fun e : x.Ψh.ObjE => (Bh.unitHat x e : MT Bh x x))) ∧
      (∀ x y z : Bh.hatU.Unif, IsLocalHomeomorph (mT Bh x y z))

/-- `M(Ψ', Ψ) ₛ×_τ̂' E' ≃ₜ M(Ψ, Ψ') ₜ×_τ̂' E'`, `(h, e') ↦ (ι h, e')`. -/
noncomputable def fibToTgt {A B : GroupoidalCategory.{0}}
    {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr} (Bh : CoveringBasicConstruction P)
    (x y : Bh.hatU.Unif) : Bh.Fib y x ≃ₜ TgtFib Bh x y :=
  ((Bh.toBasic.rep.invHomeomorph y.toUnif x.toUnif).prodCongr (Homeomorph.refl _)).subtype
    fun _ => Iff.rfl

theorem A_to_BC : A → BC := by
  intro hA A B P hP Bh hC
  obtain ⟨-, -, -, -, -, h⟩ := hA
  refine ⟨fun x y => ?_, fun x y => (h Bh hP hC x y x).2.1, fun x y => (h Bh hP hC x y x).2.2.1.1,
    fun x => (h Bh hP hC x x x).2.2.1.2, fun x y z => (h Bh hP hC x y z).2.2.2.1⟩
  obtain ⟨ei, hei⟩ := (h Bh hP hC x y x).2.2.1.1
  obtain ⟨ef, hef⟩ := (h Bh hP hC y x x).1.2.2
  refine ⟨(ei.trans ef).trans (fibToTgt Bh x y), fun a => ?_⟩
  change fibToTgt Bh x y (ef (ei a)) = toTgtFib Bh x y a
  have e1 : ef (ei (a : Bh.MHat x y)) = Bh.toFib y x (Bh.invHat x y a) :=
    (congrArg ef (hei a)).trans (hef _)
  rw [e1]
  refine Subtype.ext (Prod.ext ?_ rfl)
  change Bh.toBasic.rep.invHomeomorph y.toUnif x.toUnif (Bh.pB y x (Bh.invHat x y a)) = Bh.pB x y a
  have : Bh.pB y x (Bh.invHat x y a) = Bh.toBasic.rep.invHomeomorph x.toUnif y.toUnif
      (Bh.pB x y a) := x.Ψh.transMap_inv y.Ψh (a : x.Ψh.Trans y.Ψh)
  rw [this]
  exact (Bh.toBasic.rep.invHomeomorph x.toUnif y.toUnif).left_inv _

#rt_check RoundTrip.V19_77.not_B [Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_15_one,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.isLocalHomeomorph_srcHat,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.continuous_unitHat,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.isLocalHomeomorph_tgtHat,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.isLocalHomeomorph_mulHat,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_15_hyp]
#rt_check RoundTrip.V19_77.B_to_A [Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_15_one,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.isLocalHomeomorph_srcHat,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.continuous_unitHat,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.isLocalHomeomorph_tgtHat,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.isLocalHomeomorph_mulHat,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_15_hyp]
#rt_check RoundTrip.V19_77.main_B_to_A [Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_15_one,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.isLocalHomeomorph_srcHat,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.continuous_unitHat,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.isLocalHomeomorph_tgtHat,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.isLocalHomeomorph_mulHat,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_15_hyp]
#rt_check RoundTrip.V19_77.A_to_BC [Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_15_one,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.isLocalHomeomorph_srcHat,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.continuous_unitHat,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.isLocalHomeomorph_tgtHat,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.isLocalHomeomorph_mulHat,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_15_hyp]
#rt_overlap RoundTrip.V19_77.B_to_A [Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_15_one,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.isLocalHomeomorph_srcHat,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.continuous_unitHat,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.isLocalHomeomorph_tgtHat,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.isLocalHomeomorph_mulHat,
  Polyfold.GroupoidalCategory.CoveringBasicConstruction.proposition_19_7_15_hyp]

end RoundTrip.V19_77
