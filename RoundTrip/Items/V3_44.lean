import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_44

/-!
Round trip for V3_44 (Remark 3.49: shrinking `O`).

`A` is the type of `Polyfold.IsFillerOf.remark_3_6_2` (no universe parameters): for a filler `g` of
`f̂` (`IsFillerOf`: conditions (1), (2) near `0`, `k = [1 − ρ(r(·))]g` sc¹ on the whole `U`, the
linearization (3)) there is an open `W ∋ 0` with `f̂ = g` on `O ∩ W` and
`g(y) = ρ(r(y))g(y), y ∈ U ∩ W ⇒ y ∈ O`.

Neither direction is proved.
* `A → B` fails at the hypothesis: B starts from the text's germ filling (`IsFillingB`: `g` and `k`
  sc-smooth/sc¹ only on a germ of neighbourhoods whose levels may shrink), A from `IsFillerOf`,
  which asks `k` to be sc¹ on the whole `U` and the linearization to be `scDeriv U k 0`; a germ
  filling does not give this (cf. V3_43, `not_B`), although A's proof uses only (1) and (2).  At
  the conclusion, B also asks for a genuinely new tame strong local bundle: an `R`-invariant
  relatively open `U' ⊆ U` (so `R` is again a strong bundle retraction there), tame, with `(g, 0)`
  still a filling on `U'` and (1), (2) holding on all of `O' = r(U')`, `U'`; A only produces the
  open `W` (and `U ∩ W` is not `R`-invariant, `O ∩ W ≠ r(U ∩ W)` in general).  That part is glue
  (`U' = U ∩ W ∩ r⁻¹(W)`, restriction of germs and of the tame retraction, locality of
  derivatives), not new mathematics.
* `B → A` fails: B's hypotheses (`g` an sc-smooth germ, `f` an sc-smooth section germ, the tame
  base retraction, `r(0) = 0`) are not available in A, which holds for any filler.
* `A_direct`: A is proved outright from the filter definitions (no project theorem): its content
  is the step "a property holding eventually near `0` holds on an open neighbourhood".
-/

namespace RoundTrip.V3_44
open Polyfold Set Filter Topology StrongRetr

/-- The project's statement: Remark 3.49. -/
def A : Prop := type_of% @Polyfold.IsFillerOf.remark_3_6_2

theorem A_holds : A := @Polyfold.IsFillerOf.remark_3_6_2

/-- A, proved directly: only the conditions (1), (2) of the filler are used. -/
theorem A_direct : A := by
  intro E F C U R hU hR h0 fb g hfg
  obtain ⟨W, hWsub, hWopen, h0W⟩ := mem_nhds_iff.1 (hfg.eq_on.and hfg.mem_of_fixed)
  exact ⟨W, hWopen, h0W, fun x hx => (hWsub hx.2).1 hx.1, fun y hy => (hWsub hy.2).2 hy.1⟩

#rt_check RoundTrip.V3_44.A_direct [Polyfold.IsFillerOf.remark_3_6_2]

end RoundTrip.V3_44
