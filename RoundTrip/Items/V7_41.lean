import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_41

/-!
Round trip for V7_41 (the isotropy of `X_R` is `G_x/T_x`; Definition 7.13, `G_x^eff`).

The item lists five definitions (`reducedIsotropyHom`, `quotientTrivialSubgroupEquiv`,
`EffIsotropy`, `effIsotropyEquiv`, `effIsotropyEquivReduced`: vocabulary) and three theorems.
`A` is the conjunction of the types of the theorems, universes at `0` (`Obj Mor : Type`):
* `surjective_reducedIsotropyHom`: `g ↦ [g]`, `G_x → G̃_x` (isotropy of `x` in
  `reducedGroupoidStr`) is onto;
* `ker_reducedIsotropyHom`: its kernel is `T_x` (`trivialSubgroup x`);
* `normalClosure_trivialSet`: `normalClosure(T_x) = T_x`.

`B`: `T_x` is normal, `g ↦ [g]` is onto with kernel `T_x`, and there is `e : EffIsotropy x ≃*
G̃_x` with `e(g·normalClosure(T_x)) = [g]` (`EffIsotropy x = G_x ⧸ normalClosure(T_x)`).

`A ⇒ B`: normality of `T_x` from `T_x = ker`; `e` is `G_x/normalClosure(T_x) = G_x/ker ≅ G̃_x`
(Mathlib's first isomorphism theorem, using `normalClosure(T_x) = T_x = ker` from `A`; the
project's `quotientTrivialSubgroupEquiv` / `effIsotropyEquivReduced` are not used).
`B ⇒ A`: the normal closure of a normal subgroup is itself (`Subgroup.normalClosure_eq_self`,
applied with B's normality, not the project instance `trivialSubgroup_normal`).
-/

namespace RoundTrip.V7_41
open Polyfold

/-- The project's statements, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.EpGroupoid.surjective_reducedIsotropyHom.{0} ∧
  type_of% @Polyfold.EpGroupoid.ker_reducedIsotropyHom.{0} ∧
  type_of% @Polyfold.EpGroupoid.normalClosure_trivialSet.{0}

theorem A_holds : A :=
  ⟨@EpGroupoid.surjective_reducedIsotropyHom, @EpGroupoid.ker_reducedIsotropyHom,
    @EpGroupoid.normalClosure_trivialSet⟩

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X x
  have hsurj := hA.1 X x
  have hker := hA.2.1 X x
  have hnc := hA.2.2 X x
  refine ⟨hker ▸ MonoidHom.normal_ker _, hsurj, hker, ?_⟩
  refine ⟨(QuotientGroup.quotientMulEquivOfEq (hnc.trans hker.symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hsurj), fun g => ?_⟩
  rfl

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_⟩
  · intro Obj Mor _ _ _ _ _ _ X x
    exact (hB Obj Mor X x).2.1
  · intro Obj Mor _ _ _ _ _ _ X x
    exact (hB Obj Mor X x).2.2.1
  · intro Obj Mor _ _ _ _ _ _ X x
    exact @Subgroup.normalClosure_eq_self _ _ (X.trivialSubgroup x) (hB Obj Mor X x).1

#rt_check RoundTrip.V7_41.A_to_B [Polyfold.EpGroupoid.surjective_reducedIsotropyHom,
  Polyfold.EpGroupoid.ker_reducedIsotropyHom, Polyfold.EpGroupoid.normalClosure_trivialSet]
#rt_check RoundTrip.V7_41.B_to_A [Polyfold.EpGroupoid.surjective_reducedIsotropyHom,
  Polyfold.EpGroupoid.ker_reducedIsotropyHom, Polyfold.EpGroupoid.normalClosure_trivialSet]
#rt_overlap RoundTrip.V7_41.B_to_A [Polyfold.EpGroupoid.surjective_reducedIsotropyHom,
  Polyfold.EpGroupoid.ker_reducedIsotropyHom, Polyfold.EpGroupoid.normalClosure_trivialSet]

end RoundTrip.V7_41
