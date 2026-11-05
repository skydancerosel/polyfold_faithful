import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_46

/-! **Refresh 2026-11-02** (HEAD after the germ reading of Definition 3.11 and the notions built
on it).
Both germ theorems of A (IsGeneralPositionGerm.isGoodPositionGerm and
.isGoodPositionGermTame) now conclude the
germ-reading good position, and B's IsGoodPositionGermTame means the same; A ⇒ B is still A's
third conjunct. Result unchanged.
-/

namespace RoundTrip.V5_46
open Polyfold

/-- The project's statement: the conjunction of the three theorems of the decls (universes of the
two germ theorems instantiated at `0`; the linear-algebra core has no universe parameters):
`isInGoodPositionIn_of_scComplement_le_reduced` (a subspace of `T_zO` with an sc-complement
inside `T^R_zO` is in good position, for a tame retraction), `IsGeneralPositionGerm.isGoodPositionGerm`
(general ⇒ good position, Definition 3.53, for an sc-Fredholm section, no tameness of the
section's germ data) and `IsGeneralPositionGerm.isGoodPositionGermTame` (the same in the tame
chart of the germ data, for a section with tame germ data). -/
def A : Prop :=
  (type_of% @Polyfold.isInGoodPositionIn_of_scComplement_le_reduced) ∧
  (type_of% @Polyfold.StrongBundle.IsGeneralPositionGerm.isGoodPositionGerm.{0, 0}) ∧
  (type_of% @Polyfold.StrongBundle.IsGeneralPositionGerm.isGoodPositionGermTame.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.isInGoodPositionIn_of_scComplement_le_reduced,
    @Polyfold.StrongBundle.IsGeneralPositionGerm.isGoodPositionGerm.{0, 0},
    @Polyfold.StrongBundle.IsGeneralPositionGerm.isGoodPositionGermTame.{0, 0}⟩

/-- `A ⇒ B`: B is the third conjunct of A at a zero, with the extra hypothesis
`IsTameStrongBundle Bd`, which is not used. -/
theorem A_to_B : A → B := by
  intro hA X _ _ _ PX Y _ _ _ P _ _ Bd f _ hf x hx0 hgp
  exact hA.2.2 hf hx0 hgp

/-! `B ⇒ A` is not proved.  B assumes a tame strong bundle (`IsTameStrongBundle Bd`: an equivalent
strong bundle atlas whose base retractions are all tame), which none of A's three conjuncts
assumes: the germ conjuncts only use the one tame chart supplied by Definition 5.17 (and, for the
`Tame` version, the tame germ data of `f`), and `isGoodPositionGerm` does not even assume tame germ
data (`IsScFredholmSection` only).  A's first conjunct is the linear algebra for an arbitrary tame
retraction `R` and arbitrary `N, B ⊆ T_zO`, which cannot be extracted from B without building a
strong bundle realising them.  So A is strictly more general; deriving it from B would be
re-proving Lemma 5.26. -/

#rt_check RoundTrip.V5_46.A_to_B [Polyfold.isInGoodPositionIn_of_scComplement_le_reduced,
  Polyfold.StrongBundle.IsGeneralPositionGerm.isGoodPositionGerm,
  Polyfold.StrongBundle.IsGeneralPositionGerm.isGoodPositionGermTame]

end RoundTrip.V5_46
