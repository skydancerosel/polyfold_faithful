import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V14_33

set_option maxSynthPendingDepth 3

/-! Round trip for V14_33 (2021 Proposition 14.4.14, pp. 667–671, the local extensions `ŝᵃᵢ`;
2017: Proposition 14.7).

`A` is the conjunction of the types of the nine listed theorems at universe `0`
(`glueSection_congr_at` at `.{0,0}`, its index type in `Type`).  `B` is on `SEP.{0}`.

* `A_to_B`: from the conjunct `ZConcrete.proposition_14_4_14` alone.  Its tameness hypothesis is
  `hB` (a tame strong bundle chart about every object), which follows from `B`'s `A.X.IsTame` by
  `SEP.exists_isTameChart`; `B`'s paracompactness hypothesis is not needed.  The data match by
  definition (`C.toZData.V = C.Vh`, `C.toZSections.s a i = (T.dec.S (bdryRetr C.x₀ a)).s i`).
* `B_to_A` is not proved.  On the main conjunct, `ZConcrete.proposition_14_4_14` assumes only
  `hB` and partitions of unity, while `B` also assumes `|X|` paracompact and `X` tame; neither
  follows from `hB` (tameness of the object M-polyfold would need an equivalent atlas built from
  the base charts of the tame bundle charts, not available as a lemma; paracompactness of `|X|`
  is independent of `hB` and of the data `C`).  The other conjuncts are intermediate statements
  of the proof (the general `proposition_14_4_14` for any `CoherentNbhdSystem`, the `_of_hyp`
  and `_of_limit` forms, `coherentNbhdSystem_hyp`, `exists_local_piece`, `eqvGen_s0`,
  `glueSection_congr_at`, `ZConcrete.isFaceScPlus`); they do not follow from `B`.
-/

namespace RoundTrip.V14_33
open Polyfold Polyfold.SBLocalization

/-- The project's statement at universe `0`. -/
def A : Prop :=
  (type_of% @Polyfold.SBLocalization.glueSection_congr_at.{0,0}) ∧
  (type_of% @Polyfold.SBLocalization.CoherentNbhdSystem.eqvGen_s0.{0}) ∧
  (type_of% @Polyfold.SBLocalization.CoherentNbhdSystem.exists_local_piece.{0}) ∧
  (type_of% @Polyfold.SBLocalization.proposition_14_4_14.{0}) ∧
  (type_of% @Polyfold.SBLocalization.proposition_14_4_14_of_hyp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.coherentNbhdSystem_hyp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.proposition_14_4_14_of_limit.{0}) ∧
  (type_of% @Polyfold.SBLocalization.ZConcrete.isFaceScPlus.{0}) ∧
  (type_of% @Polyfold.SBLocalization.ZConcrete.proposition_14_4_14.{0})

theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.glueSection_congr_at.{0,0},
   @Polyfold.SBLocalization.CoherentNbhdSystem.eqvGen_s0.{0},
   @Polyfold.SBLocalization.CoherentNbhdSystem.exists_local_piece.{0},
   @Polyfold.SBLocalization.proposition_14_4_14.{0},
   @Polyfold.SBLocalization.proposition_14_4_14_of_hyp.{0},
   @Polyfold.SBLocalization.coherentNbhdSystem_hyp.{0},
   @Polyfold.SBLocalization.proposition_14_4_14_of_limit.{0},
   @Polyfold.SBLocalization.ZConcrete.isFaceScPlus.{0},
   @Polyfold.SBLocalization.ZConcrete.proposition_14_4_14.{0}⟩

/-- The main conjunct alone gives `B`. -/
theorem main_to_B
    (hA : type_of% @Polyfold.SBLocalization.ZConcrete.proposition_14_4_14.{0}) : B := by
  intro A hT _hpara hpu T P E Q C a ha
  exact hA C (SEP.exists_isTameChart A hT) hpu ha

theorem A_to_B (hA : A) : B := main_to_B hA.2.2.2.2.2.2.2.2

#rt_check RoundTrip.V14_33.main_to_B [Polyfold.SBLocalization.glueSection_congr_at,
  Polyfold.SBLocalization.CoherentNbhdSystem.eqvGen_s0,
  Polyfold.SBLocalization.CoherentNbhdSystem.exists_local_piece,
  Polyfold.SBLocalization.proposition_14_4_14,
  Polyfold.SBLocalization.proposition_14_4_14_of_hyp,
  Polyfold.SBLocalization.coherentNbhdSystem_hyp,
  Polyfold.SBLocalization.proposition_14_4_14_of_limit,
  Polyfold.SBLocalization.ZConcrete.isFaceScPlus,
  Polyfold.SBLocalization.ZConcrete.proposition_14_4_14]
#rt_check RoundTrip.V14_33.A_to_B [Polyfold.SBLocalization.glueSection_congr_at,
  Polyfold.SBLocalization.CoherentNbhdSystem.eqvGen_s0,
  Polyfold.SBLocalization.CoherentNbhdSystem.exists_local_piece,
  Polyfold.SBLocalization.proposition_14_4_14,
  Polyfold.SBLocalization.proposition_14_4_14_of_hyp,
  Polyfold.SBLocalization.coherentNbhdSystem_hyp,
  Polyfold.SBLocalization.proposition_14_4_14_of_limit,
  Polyfold.SBLocalization.ZConcrete.isFaceScPlus,
  Polyfold.SBLocalization.ZConcrete.proposition_14_4_14]
#rt_overlap RoundTrip.V14_33.A_to_B [Polyfold.SBLocalization.glueSection_congr_at,
  Polyfold.SBLocalization.CoherentNbhdSystem.eqvGen_s0,
  Polyfold.SBLocalization.CoherentNbhdSystem.exists_local_piece,
  Polyfold.SBLocalization.proposition_14_4_14,
  Polyfold.SBLocalization.proposition_14_4_14_of_hyp,
  Polyfold.SBLocalization.coherentNbhdSystem_hyp,
  Polyfold.SBLocalization.proposition_14_4_14_of_limit,
  Polyfold.SBLocalization.ZConcrete.isFaceScPlus,
  Polyfold.SBLocalization.ZConcrete.proposition_14_4_14]

end RoundTrip.V14_33
