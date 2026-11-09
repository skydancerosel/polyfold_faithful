import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_48

/-! Round trip for V10_48 (2021 Remark 10.3.18, pp. 492–493; 2017: Remark 10.3, p. 355):
equivalence of pairs `(X, β)`.

The item lists the definitions `OrbitChart` (pairs `(X, β)`, `β : |X| ≃ₜ Z`), `OrbitChart.Rel`
(`(X', β')` is related to `(X, β)` if a generalized isomorphism `f : X → X'` has `β' ∘ |f| = β`)
and `OrbitChart.setoid` (vocabulary), and four theorems; `A` is the conjunction of their types,
universes at `0` (`B` lives in `Type`; the witness has none): `Rel.refl`, `Rel.symm`,
`Rel.trans` (for every topological space `Z`: the project drops metrizability) and the witness
`rel_pairEP_pointEP` (`(ℤ-pair, |pairToPoint|) ~ (point, 1)`).

`B`: (1) for metrizable `Z`, `Rel c c'` iff some diagram `d : c.X → c'.X` with a two-sided
inverse up to common refinement has `β' ∘ |d| = β` (the definition, on representatives);
(2) "`f` is in general not unique": a metrizable `Z`, pairs `c`, `c'` and two such `d`, `d'`
without common refinement.

* `A_to_B` is proved **outright** (`B` is true; `A` gives neither part).  (1) is the definition
  of `Rel` unfolded (`EPLoc.homMk_surjective`, `homMk_eq_homMk_iff`; B's `EquivB` is
  definitionally `Diagram.Equiv`).  (2) is **not in `A`** (the project's docstring lists the
  non-uniqueness as not formalized), but it follows from the project's counterexample to
  Theorem 10.3.19 (`LocalizationLRCounterexample`, not an item theorem): on
  `X = ℤ/3 × ℝ ⇉ ℝ` (trivial action), `[X ←1 X →Inv X]` and `[1_X]` are generalized
  isomorphisms with the same orbit map that differ (`genInv_ne_genId`, through the isotropy
  relation of Remark 10.5.5).  We take `Z = |X|` (metrizable by Corollary 7.1: `|X|` is an open
  quotient of `ℝ`, hence second countable) and `c = c' = (X, 1)`.
* `B_to_A` is proved **outright**: `Rel.refl`, `Rel.symm`, `Rel.trans` hold for every
  topological `Z`, while `B` speaks of metrizable `Z` only and does not contain the transitivity
  argument (Proposition 10.3.11); the witness is a fact about `pairToPoint`.  The project's
  proofs are copied (from the non-item lemmas `EPLoc.proposition_10_3_11`, `EPLoc.orbitMap_id`,
  `Examples.isGeneralizedIso_pairToPoint`). -/

namespace RoundTrip.V10_48
open Polyfold Polyfold.EPLocalization CategoryTheory

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EPLocalization.OrbitChart.Rel.refl.{0}) ∧
  (type_of% @Polyfold.EPLocalization.OrbitChart.Rel.symm.{0}) ∧
  (type_of% @Polyfold.EPLocalization.OrbitChart.Rel.trans.{0}) ∧
  (type_of% @Polyfold.EPLocalization.OrbitChart.rel_pairEP_pointEP)

theorem A_holds : A :=
  ⟨@Polyfold.EPLocalization.OrbitChart.Rel.refl.{0},
    @Polyfold.EPLocalization.OrbitChart.Rel.symm.{0},
    @Polyfold.EPLocalization.OrbitChart.Rel.trans.{0},
    @Polyfold.EPLocalization.OrbitChart.rel_pairEP_pointEP⟩

/-! ### `B` holds (outright) -/

/-- A generalized isomorphism `[d]` gives B's two-sided inverse up to common refinement. -/
theorem isGenIsoB_of {X Y : EP.{0}} (d : Diagram X Y)
    (h : EPLoc.IsGeneralizedIso (EPLoc.homMk d)) : IsGenIsoB d := by
  obtain ⟨g, h₁, h₂⟩ := h
  obtain ⟨e, rfl⟩ := EPLoc.homMk_surjective g
  exact ⟨e, EPLoc.homMk_eq_homMk_iff.1 h₁, EPLoc.homMk_eq_homMk_iff.1 h₂⟩

/-- `B` (1): the definition of `Rel`, on representatives. -/
theorem B1 (Z : Type) [TopologicalSpace Z] (c c' : OrbitChart Z) :
    OrbitChart.Rel c c' ↔ ∃ d : Diagram c.X c'.X, IsGenIsoB d ∧ ⇑c'.β ∘ orbB d = ⇑c.β := by
  constructor
  · rintro ⟨f, hf, hβ⟩
    obtain ⟨d, rfl⟩ := EPLoc.homMk_surjective f
    exact ⟨d, isGenIsoB_of d hf, hβ⟩
  · rintro ⟨d, ⟨e, h₁, h₂⟩, hβ⟩
    exact ⟨EPLoc.homMk d,
      ⟨EPLoc.homMk e, EPLoc.homMk_eq_homMk_iff.2 h₁, EPLoc.homMk_eq_homMk_iff.2 h₂⟩, hβ⟩

open LocalizationLRCounterexample SBLocalization in
/-- `|X|` is metrizable for `X = ℤ/3 × ℝ ⇉ ℝ`: an open quotient of `ℝ` is second countable
(Proposition 7.1), and Corollary 7.1. -/
theorem metrizableSpace_z3 : TopologicalSpace.MetrizableSpace z3EP.X.OrbitSpace := by
  have : SecondCountableTopology z3EP.Obj := (inferInstance : SecondCountableTopology (Fin 1 → ℝ))
  have : SecondCountableTopology z3EP.X.OrbitSpace :=
    TopologicalSpace.Quotient.secondCountableTopology z3EP.X.proposition_7_1
  exact z3EP.X.corollary_7_1

open LocalizationLRCounterexample SBLocalization StrongBundleLocalizationExamples in
/-- `B` (2): `[X ←1 X →Inv X]` and `[1_X]` on `X = ℤ/3 × ℝ ⇉ ℝ`, both over `(X, 1)`. -/
theorem B2 : ∃ (Z : Type) (_ : TopologicalSpace Z), TopologicalSpace.MetrizableSpace Z ∧
    ∃ (c c' : OrbitChart Z) (d d' : Diagram c.X c'.X),
      IsGenIsoB d ∧ IsGenIsoB d' ∧ ⇑c'.β ∘ orbB d = ⇑c.β ∧ ⇑c'.β ∘ orbB d' = ⇑c.β ∧
      ¬ EquivB d d' := by
  -- `|[1_X]| = 1`
  have hid : orbB (SDiagram.id (z3SEP 0)).base = _root_.id := by
    funext q
    exact (IsHomeomorph.homeomorph _
      (SDiagram.id (z3SEP 0)).base.isEquivalence_F.isHomeomorph_orbitMap).apply_symm_apply q
  -- `|[Inv]| = |[1_X]|`
  have hinv : orbB (SDiagram.ofHom (z3InvHom 0)).base = orbB (SDiagram.id (z3SEP 0)).base :=
    orbitMap_genInv
  refine ⟨z3EP.X.OrbitSpace, inferInstance, metrizableSpace_z3, ⟨z3EP, Homeomorph.refl _⟩,
    ⟨z3EP, Homeomorph.refl _⟩, (SDiagram.ofHom (z3InvHom 0)).base,
    (SDiagram.id (z3SEP 0)).base, isGenIsoB_of _ isGeneralizedIso_genInv,
    isGenIsoB_of _ isGeneralizedIso_genId, ?_, ?_, fun h => ?_⟩
  · funext q
    exact congrFun (hinv.trans hid) q
  · funext q
    exact congrFun hid q
  · exact genInv_ne_genId (EPLoc.homMk_eq_homMk_iff.2 h)

theorem A_to_B : A → B.{0} := fun _ => ⟨fun Z _ _ c c' => B1 Z c c', B2⟩

/-! ### `A` holds (outright; the project's proofs) -/

theorem B_to_A : B.{0} → A := by
  intro _
  refine ⟨fun p => ?_, fun {Z} _ {p q} h => ?_, fun {Z} _ {p q r} h h' => ?_, ?_⟩
  · exact ⟨𝟙 _, ⟨𝟙 _, Category.id_comp _, Category.id_comp _⟩, by
      rw [EPLoc.orbitMap_id]; rfl⟩
  · obtain ⟨f, ⟨g, hfg, hgf⟩, hβ⟩ := h
    refine ⟨g, ⟨f, hgf, hfg⟩, ?_⟩
    rw [← hβ, Function.comp_assoc, ← EPLoc.proposition_10_3_11, hgf, EPLoc.orbitMap_id]
    rfl
  · obtain ⟨f, ⟨g, hfg, hgf⟩, hβ⟩ := h
    obtain ⟨f', ⟨g', hfg', hgf'⟩, hβ'⟩ := h'
    refine ⟨f ≫ f', ⟨g' ≫ g, ?_, ?_⟩, ?_⟩
    · rw [Category.assoc, ← Category.assoc f', hfg', Category.id_comp, hfg]
    · rw [Category.assoc, ← Category.assoc g, hgf, Category.id_comp, hgf']
    · rw [EPLoc.proposition_10_3_11, ← Function.comp_assoc, hβ', hβ]
  · refine ⟨EPLoc.localizationFunctor.map Examples.pairToPointEP,
      Examples.isGeneralizedIso_pairToPoint.1, ?_⟩
    funext q
    change Diagram.orbitMap (Diagram.ofFunctor Examples.pairToPointEP) q = _
    rw [Diagram.orbitMap_eq_of (r := q) (congrFun EpFunctor.orbitMap_id q)]
    rfl

#rt_check RoundTrip.V10_48.A_to_B [Polyfold.EPLocalization.OrbitChart.Rel.refl,
  Polyfold.EPLocalization.OrbitChart.Rel.symm, Polyfold.EPLocalization.OrbitChart.Rel.trans,
  Polyfold.EPLocalization.OrbitChart.rel_pairEP_pointEP]
#rt_check RoundTrip.V10_48.B_to_A [Polyfold.EPLocalization.OrbitChart.Rel.refl,
  Polyfold.EPLocalization.OrbitChart.Rel.symm, Polyfold.EPLocalization.OrbitChart.Rel.trans,
  Polyfold.EPLocalization.OrbitChart.rel_pairEP_pointEP]
#rt_overlap RoundTrip.V10_48.B_to_A [Polyfold.EPLocalization.OrbitChart.Rel.refl,
  Polyfold.EPLocalization.OrbitChart.Rel.symm, Polyfold.EPLocalization.OrbitChart.Rel.trans,
  Polyfold.EPLocalization.OrbitChart.rel_pairEP_pointEP]
#rt_overlap RoundTrip.V10_48.A_to_B [Polyfold.EPLocalization.OrbitChart.Rel.refl,
  Polyfold.EPLocalization.OrbitChart.Rel.symm, Polyfold.EPLocalization.OrbitChart.Rel.trans,
  Polyfold.EPLocalization.OrbitChart.rel_pairEP_pointEP]

end RoundTrip.V10_48
