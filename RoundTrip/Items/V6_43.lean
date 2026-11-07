import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_43

/-! Round trip for V6_43 (push-forward data along paths: the choices of Proposition 6.28 and
Lemma 6.29, pp. 221, 224).

A (universes at `0`): `pt1_mem_Icc`, `exists_lift_of_smooth`, `isZeroAt_sectionAdd_reparamSection`,
`IsStabKernels.push_eq_of_eq`, `isPush_reparam`, `IsPush.split` and `exists_isPush` (for tame `X`
ADMITTING BUMP FUNCTIONS, `f` sc-Fredholm with tame germ data, a chart `c` and `W ⊆ dom c` with
property (3) of Proposition 6.28 for paths in `W` — an sc⁺-section `S` with `f̃ + S = 0` along the
path NEAR `[0, 1]` — every sc-smooth path in `W` carries a push-forward datum `IsPush` in `c`).

B: for `X = U` with (1)–(4) of Proposition 6.28 (`IsGoodNbhd`: contractible, compact zero set,
sections along paths with `s(φ(t), t) = f(φ(t))` on `[0, 1]`, sc⁺-sections through every smooth
point of `Y`), along every sc-smooth path there are ONE set of choices `s, s₁, …, s_k` with the
text's pointwise (P), and for them, in EVERY chart containing the path, the linearizations can be
read and the facts used by the construction hold (`Facts`: Fredholm, onto, a continuous kernel
family, `T_0, T_1 ∈ Lin`).

No direction is proved.
* `A ⇒ B` fails: B's hypotheses do not give A's — B has no `PX.AdmitsBumpFunctions` (needed by the
  project's `lemma_6_29`, which builds the `sᵢ` with bump functions; B instead offers (4) of
  Proposition 6.28), its sections along paths vanish only on `[0, 1]` (A needs a neighbourhood),
  and it has `IsScFredholmSection` + `PX.IsTame` rather than `IsScFredholmSectionTame`.  And A's
  conclusion is not B's: A's datum is per chart and carries the parametrized (P) of the project
  (general position on `ℝᵏ × ℝ × X` near `[0, 1]`), while B asks for chart-independent choices with
  the fixed-`t` (P) on `ℝᵏ × X` and for `Facts` in every chart (Lemma 6.30 under the text's (P),
  as in V6_39/V6_42).  These are mathematical gaps (Lemma 6.29 from (4) instead of bump functions;
  Lemma 6.30 under pointwise (P)), not glue.
* `B ⇒ A` fails: A's conjuncts are about the project's `IsPush`/`IsStabKernels.push` (restriction
  along affine maps, splitting at the midpoint, existence of an `IsPush` datum), none of which B
  mentions; and A's `exists_isPush` is for an arbitrary `W` in a chart (no `X = U`, no (1), (2),
  (4)), under hypotheses (bump functions, zeros near `[0, 1]`) from which B's pointwise (P) does
  not follow.
-/

namespace RoundTrip.V6_43
open Polyfold

/-- The project's statement, universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Polyfold.pt1_mem_Icc ∧
  type_of% @Polyfold.exists_lift_of_smooth.{0, 0} ∧
  type_of% @Polyfold.isZeroAt_sectionAdd_reparamSection.{0, 0} ∧
  type_of% @Polyfold.IsStabKernels.push_eq_of_eq.{0, 0, 0} ∧
  type_of% @Polyfold.isPush_reparam.{0, 0} ∧
  type_of% @Polyfold.IsPush.split.{0, 0} ∧
  type_of% @Polyfold.exists_isPush.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.pt1_mem_Icc, @Polyfold.exists_lift_of_smooth.{0, 0},
    @Polyfold.isZeroAt_sectionAdd_reparamSection.{0, 0}, @Polyfold.IsStabKernels.push_eq_of_eq.{0, 0, 0},
    @Polyfold.isPush_reparam.{0, 0}, @Polyfold.IsPush.split.{0, 0}, @Polyfold.exists_isPush.{0, 0}⟩

end RoundTrip.V6_43
