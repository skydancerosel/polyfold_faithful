import Polyfold.Chapter16.PolyfoldStructure

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 16,
§16.1: the uniqueness claims after **Definition 16.1.2** (p. 707; 2017: Definition 16.2), on
pp. 709–710 (isomorphisms of `PS`), and in **Remark 16.1.7** (p. 711; 2017: Remark 16.1).
Numbers and pages are the 2021 text's.

# The uniqueness of the generalized isomorphism of equivalent polyfold structures

## The text, paraphrased

(After Definition 16.1.2) The generalized isomorphism `f : X → Y` with `α = β ∘ |f|` is unique,
"as a consequence of (ZHOU)" (in 2017, where Definition 16.1 asks for neither (ZHOU) nor
paracompactness, without that qualification), by Theorem 10.3.19.  (pp. 709–710) For an
isomorphism `(f, f)` of polyfold structures, the generalized isomorphism `f` is determined by
the homeomorphism `f`.  (Remark 16.1.7) For a homeomorphism `h : Z → W` and polyfold structures
`(X, α)`, `(Y, β)` there is at most one generalized isomorphism `f` with `h ∘ α = β ∘ |f|`.

## The check (wave-1 task Z)

`X = ℤ/3 × ℝ ⇉ ℝ`, the trivial action (`trivialZ3EpGroupoid`), is the ep-groupoid on which
Theorem 10.3.19 does not hold as we read it (`not_theorem_10_3_19`).  It satisfies (ZHOU)
(`Examples.isZhou_trivialZ3`, Chapter 7: every element acts trivially, so `T_x = G_x`), its
orbit map `π : ℝ → |X|` is a homeomorphism (`isHomeomorph_π_trivialZ3`), so `|X|` is
paracompact, and `(X, π⁻¹)` is a polyfold structure on `ℝ` (`z3PolyfoldStructure`).  The
generalized isomorphisms `[1_X]` and `[X ←1 X →Inv X]` of Chapter 10 both satisfy
`α = α ∘ |f|` and differ.  Hence:

* **The uniqueness after Definition 16.1.2 does not hold as we read it**:
  `not_uniqueness_16_1_2` (from `uniqueness_16_1_2_counterexample`).
* **Remark 16.1.7 does not hold as we read it**, with `h = id`: `not_remark_16_1_7`.  The
  same pair is a counterexample to the claim on pp. 709–710 (two isomorphisms `(genId, id)`,
  `(genInv, id)` of `PS` over the same homeomorphism).
* The polyfold structure is not effective (`not_isEffective_z3PolyfoldStructure`); for an
  effective target both claims hold (`PolyfoldStructure.uniqueness_16_1_2_of_isEffective`,
  `remark_16_1_7_of_isEffective`).

Definition 16.1.2 itself (an equivalence relation) and the notion of polyfold are unaffected;
what fails is only that the witness `f` is determined by `|f|`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

open EPLocalization

namespace EpGroupoid.Examples

/-- The orbit map of `ℤ/3 × ℝ ⇉ ℝ` (trivial action) is injective: every morphism has `s = t`. -/
theorem injective_π_trivialZ3 : Function.Injective trivialZ3EpGroupoid.π := fun x y h => by
  obtain ⟨φ, h1, h2⟩ := (GroupoidStr.π_eq_π_iff _).1 h
  exact h1.symm.trans h2

/-- The orbit map `π : ℝ → |ℤ/3 × ℝ ⇉ ℝ|` is a homeomorphism (continuous, open by Proposition
7.1.8, bijective). -/
theorem isHomeomorph_π_trivialZ3 : IsHomeomorph trivialZ3EpGroupoid.π :=
  ⟨trivialZ3EpGroupoid.continuous_π, trivialZ3EpGroupoid.proposition_7_1_8,
    ⟨injective_π_trivialZ3, trivialZ3EpGroupoid.surjective_π⟩⟩

/-- `|ℤ/3 × ℝ ⇉ ℝ| ≃ₜ ℝ`. -/
def trivialZ3OrbitHomeomorph : trivialZ3EpGroupoid.OrbitSpace ≃ₜ (Fin 1 → ℝ) :=
  (isHomeomorph_π_trivialZ3.homeomorph _).symm

/-- `|ℤ/3 × ℝ ⇉ ℝ|` is paracompact. -/
theorem hasParacompactOrbitSpace_trivialZ3 : trivialZ3EpGroupoid.HasParacompactOrbitSpace :=
  trivialZ3OrbitHomeomorph.paracompactSpace_iff.2 inferInstance

end EpGroupoid.Examples

namespace PolyfoldStructure

open EpGroupoid.Examples LocalizationLRCounterexample

/-- **A polyfold structure on `ℝ` with nontrivial isotropy** (Definition 16.1.1): `ℤ/3 × ℝ ⇉ ℝ`
(trivial action), paracompact orbit space, (ZHOU), `β = π⁻¹ : |X| → ℝ`.  Also the witness that
Definition 16.1.1 is satisfiable. -/
def z3PolyfoldStructure : PolyfoldStructure (Fin 1 → ℝ) :=
  ⟨z3EP, hasParacompactOrbitSpace_trivialZ3, EpGroupoid.Examples.isZhou_trivialZ3,
    trivialZ3OrbitHomeomorph⟩

/-- `ℝ` with the class of `z3PolyfoldStructure` is a polyfold (Definition 16.1.3, witness). -/
def z3Polyfold : PolyfoldClass (Fin 1 → ℝ) := ⟦z3PolyfoldStructure⟧

/-- The ep-groupoid of `z3PolyfoldStructure` is not effective. -/
theorem not_isEffective_z3PolyfoldStructure : ¬ z3PolyfoldStructure.X.X.IsEffective :=
  not_isEffective_trivialZ3

/-- The statement after **2021 Definition 16.1.2, p. 707 (2017: Definition 16.2)**, in universe
`u`: for polyfold structures `(X, α)`, `(Y, β)` on `Z`, at most one generalized isomorphism
`f : X → Y` has `α = β ∘ |f|`.  It does not hold as we read it: `not_uniqueness_16_1_2`. -/
def Uniqueness_16_1_2 : Prop :=
  ∀ (Z : Type u) [TopologicalSpace Z] (p q : PolyfoldStructure Z)
    (f f' : EPLoc.of p.X ⟶ EPLoc.of q.X), EPLoc.IsGeneralizedIso f →
    EPLoc.IsGeneralizedIso f' → ⇑p.β = ⇑q.β ∘ EPLoc.orbitMap f →
    ⇑p.β = ⇑q.β ∘ EPLoc.orbitMap f' → f = f'

/-- The statement of **2021 Remark 16.1.7, p. 711 (2017: Remark 16.1)**, in universe `u`: for a
homeomorphism `h : Z → W` and polyfold structures `(X, α)` on `Z`, `(Y, β)` on `W`, at most one
generalized isomorphism `f : X → Y` has `h ∘ α = β ∘ |f|`.  It does not hold as we read it:
`not_remark_16_1_7`. -/
def Remark_16_1_7 : Prop :=
  ∀ (Z W : Type u) [TopologicalSpace Z] [TopologicalSpace W] (h : Z ≃ₜ W)
    (p : PolyfoldStructure Z) (q : PolyfoldStructure W) (f f' : EPLoc.of p.X ⟶ EPLoc.of q.X),
    EPLoc.IsGeneralizedIso f → EPLoc.IsGeneralizedIso f' →
    ⇑h ∘ ⇑p.β = ⇑q.β ∘ EPLoc.orbitMap f → ⇑h ∘ ⇑p.β = ⇑q.β ∘ EPLoc.orbitMap f' → f = f'

/-- `[1_X]` and `[X ←1 X →Inv X]` both witness the equivalence of `z3PolyfoldStructure` with
itself (`α = α ∘ |f|`). -/
theorem β_eq_β_comp_orbitMap_genId :
    ⇑z3PolyfoldStructure.β = ⇑z3PolyfoldStructure.β ∘ EPLoc.orbitMap genId := by
  funext q
  change _ = z3PolyfoldStructure.β (EPLoc.orbitMap (𝟙 (EPLoc.of z3EP)) q)
  rw [EPLoc.orbitMap_id]
  rfl

theorem β_eq_β_comp_orbitMap_genInv :
    ⇑z3PolyfoldStructure.β = ⇑z3PolyfoldStructure.β ∘ EPLoc.orbitMap genInv := by
  rw [orbitMap_genInv]
  exact β_eq_β_comp_orbitMap_genId

/-- **The counterexample to the uniqueness after 2021 Definition 16.1.2** (and to Remark
16.1.7 with `h = id`): on the polyfold structure `z3PolyfoldStructure` of `ℝ` (with (ZHOU) and
paracompact orbit space), the generalized isomorphisms `[X ←1 X →Inv X]` and `[1_X]` both satisfy
`α = α ∘ |f|`, and they differ. -/
theorem uniqueness_16_1_2_counterexample :
    z3PolyfoldStructure.X.X.IsZhou ∧ z3PolyfoldStructure.X.X.HasParacompactOrbitSpace ∧
      EPLoc.IsGeneralizedIso genInv ∧ EPLoc.IsGeneralizedIso genId ∧
      ⇑z3PolyfoldStructure.β = ⇑z3PolyfoldStructure.β ∘ EPLoc.orbitMap genInv ∧
      ⇑z3PolyfoldStructure.β = ⇑z3PolyfoldStructure.β ∘ EPLoc.orbitMap genId ∧
      genInv ≠ genId :=
  ⟨z3PolyfoldStructure.isZhou, z3PolyfoldStructure.paracompact, isGeneralizedIso_genInv,
    isGeneralizedIso_genId, β_eq_β_comp_orbitMap_genInv, β_eq_β_comp_orbitMap_genId,
    genInv_ne_genId⟩

/-- **The uniqueness after 2021 Definition 16.1.2, p. 707, does not hold as we read it**:
`uniqueness_16_1_2_counterexample`. -/
theorem not_uniqueness_16_1_2 : ¬ Uniqueness_16_1_2.{0} := fun h =>
  genInv_ne_genId (h _ z3PolyfoldStructure z3PolyfoldStructure genInv genId
    isGeneralizedIso_genInv isGeneralizedIso_genId β_eq_β_comp_orbitMap_genInv
    β_eq_β_comp_orbitMap_genId)

/-- **2021 Remark 16.1.7, p. 711, does not hold as we read it** (nor the claim on pp. 709–710
that an isomorphism `(f, f)` of `PS` is determined by `f`): take `h = id` in
`uniqueness_16_1_2_counterexample`. -/
theorem not_remark_16_1_7 : ¬ Remark_16_1_7.{0} := fun h =>
  genInv_ne_genId (h _ _ (Homeomorph.refl _) z3PolyfoldStructure z3PolyfoldStructure genInv genId
    isGeneralizedIso_genInv isGeneralizedIso_genId β_eq_β_comp_orbitMap_genInv
    β_eq_β_comp_orbitMap_genId)

/-- The uniqueness after Definition 16.1.2 holds when every target is effective
(`uniqueness_16_1_2_of_isEffective`). -/
theorem uniqueness_16_1_2_of_forall_isEffective {Z : Type u} [TopologicalSpace Z]
    {p q : PolyfoldStructure Z} (hq : q.X.X.IsEffective) {f f' : EPLoc.of p.X ⟶ EPLoc.of q.X}
    (hf : EPLoc.IsGeneralizedIso f) (hf' : EPLoc.IsGeneralizedIso f')
    (h : ⇑p.β = ⇑q.β ∘ EPLoc.orbitMap f) (h' : ⇑p.β = ⇑q.β ∘ EPLoc.orbitMap f') : f = f' :=
  uniqueness_16_1_2_of_isEffective hq hf hf' h h'

end PolyfoldStructure

end Polyfold
