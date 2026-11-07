import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_48

/-! Round trip for V6_48 (§6.5, the homotopy argument, pp. 226–227, and Theorem 6.35, p. 227).

* `A`: the types of `theorem_6_35` and `push_eq_of_homotopy` (universes at `0`);
  `HasLocalPropagation` is vocabulary.
* `B`: (B1) every smooth `x` of a tame `X` has an open, sc-smoothly contractible `U ∋ x` in a
  chart with `HasLocalPropagation` (for an sc-Fredholm `f`); (B2) two sc-smooth paths with the
  same end points in an open sc-smoothly contractible `U` are sc-smoothly homotopic in `U` with
  end points fixed.
* `B ⇒ theorem_6_35` (`B_to_theorem_6_35`): (B1) has weaker hypotheses (no bump functions, no
  tame germs for `f`, no second family of paracompactness instances) and a stronger conclusion
  (contractibility).  `B ⇒ push_eq_of_homotopy` is not proved: that lemma is for an arbitrary
  homotopy in the domain of an arbitrary chart (with a section as in Proposition 6.28 (3)), while
  `B` only gives the propagation property on some neighbourhood of each point; deriving it would
  mean re-proving the analytic homotopy argument (Lemma 6.29 on the square, `push_square`) or a
  covering/chart-change argument.  So `B ⇒ A` fails.
* `A ⇒ B` fails: (B1) asks for contractibility of `U`, which `theorem_6_35` does not give (the
  project's `U` comes from Proposition 6.28 with property (1′) — homotopies in a larger `W` — and
  is not shown to be contractible); `A`'s hypotheses `PX.AdmitsBumpFunctions`,
  `IsScFredholmSectionTame f` and the families
  `ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))`, `ParacompactSpace (pullbackSpace …)`
  are not given by `B` (all satisfiable: e.g. `admitsBumpFunctions_of_hilbert`, metrizable `X`);
  and (B2) is a statement of path topology with no counterpart in `A`.
-/

namespace RoundTrip.V6_48
open Polyfold

/-- The project's statement: the item's theorems, universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Polyfold.theorem_6_35.{0, 0} ∧ type_of% @Polyfold.push_eq_of_homotopy.{0, 0}

theorem A_holds : A := ⟨@Polyfold.theorem_6_35.{0, 0}, @Polyfold.push_eq_of_homotopy.{0, 0}⟩

/-- **(B1) gives Theorem 6.35 as formalized**: forget contractibility; the extra hypotheses of the
project's theorem (bump functions, tame germs, the second family of instances) are not needed. -/
theorem B_to_theorem_6_35 (hB : B) : type_of% @Polyfold.theorem_6_35.{0, 0} := by
  intro X _ _ _ PX Y _ _ _ P _ _ Bd f _ _ _ _ hX _ hf x hx
  obtain ⟨c, hc, U, hUo, hxU, -, hLP⟩ := hB.1 PX P Bd f hf.toIsScFredholmSection hX x hx
  exact ⟨c, hc, U, hUo, hxU, hLP⟩

#rt_check RoundTrip.V6_48.B_to_theorem_6_35 [Polyfold.theorem_6_35, Polyfold.push_eq_of_homotopy]
#rt_overlap RoundTrip.V6_48.B_to_theorem_6_35 [Polyfold.theorem_6_35,
  Polyfold.push_eq_of_homotopy]

end RoundTrip.V6_48
