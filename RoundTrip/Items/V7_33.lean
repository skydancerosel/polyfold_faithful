import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_33

/-! Round trip for V7_33 (Definition 7.11: effective ep-groupoids, regular objects, `X_reg`;
the remark "if `s(φ)` is regular, so is `t(φ)`").

`A` is the conjunction of the types of the listed theorems, at universe `0` (B lives in `Type`):
`GroupoidStr.isRegular_tgt_iff` (for an arbitrary `GroupoidStr`, both directions),
`EpGroupoid.isRegular_tgt_of_isRegular_src`, `EpGroupoid.isSaturated_regularSet`.
`EpGroupoid.IsEffective`, `GroupoidStr.IsRegular`, `GroupoidStr.regularSet` are definitions.

`A → B` (proved).  The three definitional conjuncts of B hold outright: the project writes
`g ≠ 1` and `g = 1` in the group `G_x`, B writes `g.val ≠ 1_x`, `g.val = 1_x` on the underlying
morphisms; they agree by `Isotropy.ext` and `(1 : G_x).val = u(x)` (`rfl`).  B's last conjunct is
A's `isRegular_tgt_of_isRegular_src` (the hypothesis is used here).

`B → A` (proved).  `isRegular_tgt_of_isRegular_src` and `isSaturated_regularSet` come from B's
last conjunct and its regularity characterization (with `isSaturated_iff`).  A's
`GroupoidStr.isRegular_tgt_iff` is stated for EVERY groupoid structure (no topology, no
M-polyfolds), and B only speaks of ep-groupoids, so this conjunct is re-proved outright
(conjugation `g ↦ φ ∘ g ∘ φ⁻¹`, `isotropyConj`); it is also more than the text's one-way remark
(it is an `↔`). -/

namespace RoundTrip.V7_33
open Polyfold

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.GroupoidStr.isRegular_tgt_iff.{0}) ∧
    (type_of% @Polyfold.EpGroupoid.isRegular_tgt_of_isRegular_src.{0}) ∧
    (type_of% @Polyfold.EpGroupoid.isSaturated_regularSet.{0})

theorem A_holds : A :=
  ⟨@Polyfold.GroupoidStr.isRegular_tgt_iff.{0},
    @Polyfold.EpGroupoid.isRegular_tgt_of_isRegular_src.{0},
    @Polyfold.EpGroupoid.isSaturated_regularSet.{0}⟩

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- `g = 1` in `G_x` iff `g.val = u(x)`. -/
theorem isotropy_eq_one_iff (X : EpGroupoid Obj Mor) {x : Obj} (g : X.Isotropy x) :
    g = 1 ↔ g.val = X.unit x :=
  ⟨fun h => by rw [h]; rfl, fun h => GroupoidStr.Isotropy.ext h⟩

theorem isRegular_iff_B (X : EpGroupoid Obj Mor) (x : Obj) :
    X.IsRegular x ↔ IsRegularB X x :=
  forall_congr' fun g => isotropy_eq_one_iff X g

theorem isEffective_iff_B (X : EpGroupoid Obj Mor) : X.IsEffective ↔ IsEffectiveB X :=
  forall_congr' fun _ => forall_congr' fun g =>
    imp_congr_left (not_congr (isotropy_eq_one_iff X g))

theorem regularSet_eq_B (X : EpGroupoid Obj Mor) : X.regularSet = XregB X :=
  Set.ext fun x => isRegular_iff_B X x

end

theorem A_to_B : A → B := by
  rintro ⟨-, hst, -⟩ Obj Mor _ _ _ _ _ _ X
  refine ⟨isEffective_iff_B X, isRegular_iff_B X, regularSet_eq_B X, fun φ h => ?_⟩
  exact (isRegular_iff_B X _).1 (hst (X := X) ((isRegular_iff_B X _).2 h))

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_⟩
  · -- outright: B does not speak of bare groupoid structures
    intro Obj Mor G φ
    set e := G.isotropyConj φ rfl rfl
    constructor
    · intro h g
      exact e.injective ((h _).trans (map_one e).symm)
    · intro h g
      rw [← e.apply_symm_apply g, h (e.symm g), map_one]
  · intro Obj Mor _ _ _ _ _ _ X φ h
    obtain ⟨-, hreg, -, htgt⟩ := hB Obj Mor X
    exact (hreg _).2 (htgt φ ((hreg _).1 h))
  · intro Obj Mor _ _ _ _ _ _ X
    obtain ⟨-, hreg, -, htgt⟩ := hB Obj Mor X
    exact X.isSaturated_iff.2 fun φ h => (hreg _).2 (htgt φ ((hreg _).1 h))

#rt_check RoundTrip.V7_33.A_to_B [Polyfold.GroupoidStr.isRegular_tgt_iff,
  Polyfold.EpGroupoid.isRegular_tgt_of_isRegular_src, Polyfold.EpGroupoid.isSaturated_regularSet]
#rt_check RoundTrip.V7_33.B_to_A [Polyfold.GroupoidStr.isRegular_tgt_iff,
  Polyfold.EpGroupoid.isRegular_tgt_of_isRegular_src, Polyfold.EpGroupoid.isSaturated_regularSet]
#rt_overlap RoundTrip.V7_33.B_to_A [Polyfold.GroupoidStr.isRegular_tgt_iff,
  Polyfold.EpGroupoid.isRegular_tgt_of_isRegular_src, Polyfold.EpGroupoid.isSaturated_regularSet]
#rt_overlap RoundTrip.V7_33.A_to_B [Polyfold.GroupoidStr.isRegular_tgt_iff,
  Polyfold.EpGroupoid.isRegular_tgt_of_isRegular_src, Polyfold.EpGroupoid.isSaturated_regularSet]

end RoundTrip.V7_33
