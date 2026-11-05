import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_76

/-!
Round trip for V3_76 (Corollary 3.39).  `A` is the conjunction of the types of
`Polyfold.corollary_3_39`, `Polyfold.corollary_3_39_isConjugate`,
`Polyfold.ConjugationData.compIso_eq_strongShift`, `Polyfold.IsStrongBundleIso.shift`,
`Polyfold.IsStrongBundleIso.comp`, `Polyfold.IsStrongBundleIso.pushforward_comp`,
`Polyfold.StabilityData.linIso_isStrongBundleIso` and
`Polyfold.ScOperator.isStrongBundleIso_prodMap` (none has universe parameters).

Neither direction is proved.

* `A → B` fails at the hypotheses (a genuine difference of reading, closing it is new
  mathematics, not glue).  A's `corollary_3_39` / `corollary_3_39_isConjugate` assume that `g` and
  `s` are sc-smooth **on the relatively open set `U`** (`IsScSmooth U g`, `IsScSmooth U s`, set
  sense: one neighbourhood for all levels and orders).  B assumes only germ regularity: `s` is an
  sc-smooth germ on `G` (`IsScSmoothGerm G s`, Definition 3.2, neighbourhoods `G.U m` shrinking
  with the level) and `g` is anything whose push-forward `Φ_* g` is a basic germ on a germ `G'`
  (so `g = Φ'`-pull-back of a germ, again only an sc-smooth *germ*).  A germ does not give
  sc-smoothness on any single relatively open `U₀ ∋ 0` (no `U₀` with `U₀ ∩ E_m ⊆ G.U m` for all
  `m` need exist), so A's theorems cannot be applied to B's data, even after shrinking `U`.  The
  rest of B's setting is reachable: B's `Φ`, `U'`, `G'`, `pushforward Φ Φ' g` (basic on `G'`) form
  the project's `ConjugationData U g` (`conj` holds on all of `U` because
  `pushforward Φ Φ' g (φ u) = (Φ (u, g u)).2`), with `Pn = Fin n → ℝ`, `Q = Fin N → ℝ`.  Even
  under set-sense hypotheses, B's conclusion asks for parameter spaces of the form
  `Fin n' → ℝ`, `Fin N' → ℝ` and a level-`0` isomorphism `Ψ` whose index raise conjugates; A gives
  `Λ₀ = 𝒮.linIso₀` with target `paramProd (Pn × 𝒮.Cs) 𝒮.XB × paramProd (Q × 𝒮.Zs) 𝒮.XB`
  (`compIso_eq_strongShift`: `Λ₀ ∘ Φ` is a level-`0` iso whose raise is `Γ`), so a further
  transport of the basic germ along linear isomorphisms `Pn × Cs ≃ ℝ^{n'}` would be needed (glue,
  not attempted since the hypothesis gap already blocks the direction).
* `B → A` fails: A contains general facts about strong bundle isomorphisms
  (`IsStrongBundleIso.shift`, `.comp`, `.pushforward_comp`, `isStrongBundleIso_prodMap`,
  `linIso_isStrongBundleIso`) for arbitrary sc-Banach spaces and data, which B (a statement about
  conjugations to basic germs on `Fin n → ℝ` parameter spaces) does not imply; and A's corollary is
  stated for arbitrary finite-dimensional parameter types `Pn`, `Q` of `ConjugationData`.
-/

namespace RoundTrip.V3_76
open Polyfold

/-- The project's statement: the listed theorems (no universe parameters). -/
def A : Prop :=
  type_of% @Polyfold.corollary_3_39 ∧ type_of% @Polyfold.corollary_3_39_isConjugate ∧
    type_of% @Polyfold.ConjugationData.compIso_eq_strongShift ∧
    type_of% @Polyfold.IsStrongBundleIso.shift ∧ type_of% @Polyfold.IsStrongBundleIso.comp ∧
    type_of% @Polyfold.IsStrongBundleIso.pushforward_comp ∧
    type_of% @Polyfold.StabilityData.linIso_isStrongBundleIso ∧
    type_of% @Polyfold.ScOperator.isStrongBundleIso_prodMap

theorem A_holds : A :=
  ⟨@Polyfold.corollary_3_39, @Polyfold.corollary_3_39_isConjugate,
    @Polyfold.ConjugationData.compIso_eq_strongShift, @Polyfold.IsStrongBundleIso.shift,
    @Polyfold.IsStrongBundleIso.comp, @Polyfold.IsStrongBundleIso.pushforward_comp,
    @Polyfold.StabilityData.linIso_isStrongBundleIso, @Polyfold.ScOperator.isStrongBundleIso_prodMap⟩

end RoundTrip.V3_76
