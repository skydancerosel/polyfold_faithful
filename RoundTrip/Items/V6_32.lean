import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_32

/-! Round trip for V6_32 (Proposition 6.28, the neighbourhoods `U(x)`).

A = the conjunction of the item's theorems (universes at `0`): the tools
`exists_contDiff_eq_id_near_Icc_mapsTo`, `exists_isScSmoothMap_eq_one_nhdsSet`,
`exists_nhds_isCompact_zeros`, `exists_isScPlusSection_pullback_of_mapsTo_of_bump`,
`exists_isScPlusSection_pullback_of_family`, `hasScPlusSectionsThrough_pullback_rn_of_bump`,
`MPolyfold.paracompactSpace_prod`, `paracompactSpace_pullbackSpace`, and `proposition_6_28`:
**with sc-smooth bump functions**, a smooth `x` has open `U ⊆ W ⊆ dom φ_c` (`c` in the atlas) with
(1′) two sc-smooth paths in `U` with the same end points are sc-smoothly homotopic **in `W`** with
end points fixed; (2) `{y ∈ cl U | f y = 0}` compact; (3) for every `n` and every globally
sc-smooth `Φ : ℝⁿ → X` with `Φ([0,1]ⁿ) ⊆ W` a **global** sc⁺-section `S` of `ℝⁿ × X → Y` with
`(f + S)(q, Φ q) = 0` near `[0,1]ⁿ` and `S(q, ·)` depending on `q ∈ [0,1]ⁿ` only through `Φ(q)`;
(4) `ℝⁿ × X → Y` has sc⁺-sections through all smooth fibre points.
B = without bump functions, a smooth `x` has an open `U ∋ x` with (1) `U` sc-smoothly contractible
**in itself** (`H([0,1] × U) ⊆ U`, `H(1, ·) = id`, `H(0, ·)` constant); (2); (3) for paths `φ`
sc-smooth near `[0, 1]` with `φ([0,1]) ⊆ U` an sc⁺-section near `[0,1] × U` with
`s(t, φ t) = f(φ t)` on `[0, 1]`; (4) sc⁺-sections near `[0,1] × U` through smooth fibre points
over `[0,1] × U_∞`.

Neither direction is proved.

* `A ⇒ B`: (a) A's `proposition_6_28` has the hypothesis `PX.AdmitsBumpFunctions`, which B does
  not give (satisfiable: e.g. M-polyfolds modelled on Hilbert spaces or `ℝⁿ`; not implied).
  (b) B's (1) is not given by A: A has only (1′), homotopies of paths that stay in the larger `W`;
  the straight-line contraction `r((1 − t) u₀ + t φ(y))` of A's `U = φ⁻¹(B_{δ'}(u₀))` lands in
  `W = φ⁻¹(B_δ(u₀))`, not in `U`, and a neighbourhood that the retraction maps into itself is not
  available in general (the project's reading: (1) is not established for `U` itself).  This is
  real mathematics, not glue.  (Glue that would also be needed: `s := −S`, restriction of the
  global sections to open `W ⊇ [0,1] × U`, and B's paths sc-smooth only near `[0, 1]` against A's
  globally sc-smooth `Φ`, via `exists_contDiff_eq_id_near_Icc_mapsTo`.)
* `B ⇒ A`: A states more than B: the chart domain `W` containing `U`, (1′) with a homotopy (B's
  contraction of `U` gives null-homotopies, not homotopies rel end points; building those
  sc-smoothly needs a smoothing/concatenation argument), (3) for all `n`-parameter families with
  the parameter-dependence clause and **global** sections, (4) **global** sections on `ℝⁿ × X`
  (impossible to get from B without bump functions), and the auxiliary lemmas
  (`exists_contDiff_eq_id_near_Icc_mapsTo`, `exists_isScSmoothMap_eq_one_nhdsSet` with bump
  functions, …), which B does not speak about.
-/

namespace RoundTrip.V6_32
open Polyfold

/-- The project's statement, universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Polyfold.exists_contDiff_eq_id_near_Icc_mapsTo ∧
  type_of% @Polyfold.exists_isScSmoothMap_eq_one_nhdsSet.{0} ∧
  type_of% @Polyfold.exists_nhds_isCompact_zeros.{0, 0} ∧
  type_of% @Polyfold.exists_isScPlusSection_pullback_of_mapsTo_of_bump.{0, 0} ∧
  type_of% @Polyfold.exists_isScPlusSection_pullback_of_family.{0, 0} ∧
  type_of% @Polyfold.hasScPlusSectionsThrough_pullback_rn_of_bump.{0, 0} ∧
  type_of% @Polyfold.proposition_6_28.{0, 0} ∧
  type_of% @Polyfold.MPolyfold.paracompactSpace_prod.{0, 0} ∧
  type_of% @Polyfold.paracompactSpace_pullbackSpace.{0, 0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.exists_contDiff_eq_id_near_Icc_mapsTo,
    @Polyfold.exists_isScSmoothMap_eq_one_nhdsSet.{0},
    @Polyfold.exists_nhds_isCompact_zeros.{0, 0},
    @Polyfold.exists_isScPlusSection_pullback_of_mapsTo_of_bump.{0, 0},
    @Polyfold.exists_isScPlusSection_pullback_of_family.{0, 0},
    @Polyfold.hasScPlusSectionsThrough_pullback_rn_of_bump.{0, 0},
    @Polyfold.proposition_6_28.{0, 0},
    @Polyfold.MPolyfold.paracompactSpace_prod.{0, 0},
    @Polyfold.paracompactSpace_pullbackSpace.{0, 0, 0}⟩

/-! `A_to_B` and `B_to_A` are not proved (see the module docstring). -/

end RoundTrip.V6_32
