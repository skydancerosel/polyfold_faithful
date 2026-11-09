import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_33

/-! Round trip for V6_33 (the section `F` and Lemma 6.29).

A = `isZeroAt_paramSection_zero` ∧ `exists_sections_isGeneralPositionGerm_of_isCompact` ∧
`lemma_6_6_4` (universes at `0`).  `lemma_6_6_4`: for **`PX.IsTame`**, **`PX.AdmitsBumpFunctions`**,
**`f` with tame germ data** (`IsScFredholmSectionTame`), a **globally** sc-smooth `Φ : ℝⁿ → X`
and a **global** sc⁺-section `S` of `π*Y → ℝⁿ × X` with `(f̃ + S)(q, Φ q) = 0` for `q` **near**
`[0, 1]ⁿ`, there are finitely many global sc⁺-sections `s₁, …, s_k` of `π*Y` such that the
**family** `F(λ, (q, y)) = f(y) + S(q, y) + Σ λᵢ sᵢ(q, y)`, a section over `ℝᵏ × (ℝⁿ × X)`, is in
general position at `(0, (q, Φ q))` for `q` near `[0, 1]ⁿ`.
B = for a tame strong bundle (every point in a tame strong bundle chart), `f` sc-Fredholm, `U` as
in Proposition 6.28 (B's `IsNbhd628`), a path `φ` sc-smooth near `[0, 1]` in `U` and `s` sc⁺ near
`[0,1] × U` with `s(t, φ t) = f(φ t)` on `[0, 1]`: (a) there are `s₁, …, s_k` (sc⁺ near
`[0,1] × U`) with (P): every **slice** `F_t` (over `ℝᵏ × X`) is in general position at
`(0, φ t)`, `t ∈ [0, 1]`; (b) for **every** such family, (P) implies that the family
`F(t, λ, y)` over `ℝ¹ × (ℝᵏ × X)` is in general position at `(t, (0, φ t))`.

Neither direction is proved.

* `A ⇒ B` fails.  Hypotheses of A not given by B: `PX.AdmitsBumpFunctions` (satisfiable, not
  implied); `IsScFredholmSectionTame f` (germ data in tame charts; satisfiable, B has only
  `IsScFredholmSection` and tame charts — getting tame germ data from these is a chart-change
  argument); `PX.IsTame` (B's "every point in a tame strong bundle chart" should give it through
  `isTame_of_forall_exists_chart`: glue); a *global* sc⁺-section `S` vanishing with `f` *near*
  `[0,1]ⁿ` and a *globally* sc-smooth `Φ` (B's `s` is sc⁺ only near `[0,1] × U` and agrees with
  `f` only on `[0, 1]`; B's `φ` is sc-smooth only near `[0, 1]`).  The conclusions differ in
  substance: A gives general position of the *family* over `ℝᵏ × (ℝⁿ × X)`; B (a) asks for
  general position of every *slice* `F_t` over `ℝᵏ × X` — the project states it is not proved
  ("this chart computation is not carried out here": tangent vectors of the curve of zeros, the
  reduced tangent space of `ℝᵏ × X` versus `ℝᵏ × (ℝ × X)`); B (b), the implication (P) ⇒ family
  general position for arbitrary `s₁, …, s_k`, is not in A at all, and its family lives over
  `ℝ¹ × (ℝᵏ × X)`, A's over `ℝᵏ × (ℝ¹ × X)` (another factor order: invariance of general
  position under the swap diffeomorphism would also be needed).  Real mathematics.
* `B ⇒ A` fails.  A is for arbitrary `n`-parameter families `Φ` and global sections, and
  `exists_sections_isGeneralPositionGerm_of_isCompact` for any compact set of zeros of any
  tame sc-Fredholm section; B only for paths in a neighbourhood `U` with (1)–(4) of Proposition
  6.28 (whose existence, with B's contractibility (1), is itself not established; see V6_32) and
  sections near `[0,1] × U`.  `isZeroAt_paramSection_zero` would be proved outright.
-/

namespace RoundTrip.V6_33
open Polyfold

/-- The project's statement, universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Polyfold.isZeroAt_paramSection_zero.{0, 0} ∧
  type_of% @Polyfold.exists_sections_isGeneralPositionGerm_of_isCompact.{0, 0} ∧
  type_of% @Polyfold.lemma_6_6_4.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.isZeroAt_paramSection_zero.{0, 0},
    @Polyfold.exists_sections_isGeneralPositionGerm_of_isCompact.{0, 0},
    @Polyfold.lemma_6_6_4.{0, 0}⟩

/-! `A_to_B` and `B_to_A` are not proved (see the module docstring). -/

end RoundTrip.V6_33
