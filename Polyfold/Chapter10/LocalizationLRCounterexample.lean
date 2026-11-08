import Polyfold.Chapter10.LocalizationLR
import Polyfold.Chapter10.EquivalenceLREffective
import Polyfold.Chapter10.StrongBundleLocalizationExamples
import Polyfold.Chapter8.TangentZhou

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 10: **Theorem 10.3.19** (§10.3, p. 493; 2017: Theorem 10.7) and its strong
bundle version **Theorem 10.5.7** (§10.5, p. 508; 2017: Theorem 10.10).  Numbers and pages
are the 2021 text's.

# Generalized isomorphisms are not determined by their orbit maps under (LR)

## The text, paraphrased

(Theorem 10.3.19) If one of the ep-groupoids `X`, `Y` has the local regularity property (LR), two
generalized isomorphisms `f, f' : X → Y` with `|f| = |f'|` are equal.  *Proof* (text, pp.
493–494): represent `f`, `f'` by `X ←F A →H Y` and `X ←F A →H' Y` (after a weak fibred product),
so that `|H| = |H'|`; Proposition 10.1.10 (1) gives, near every `a ∈ A`, an sc-smooth family
`α_a(b) : H(b) → H'(b)`; on the ep-groupoid `A_𝒰` of the cover by these neighbourhoods the `α_a`
are said to give a natural transformation `H_𝒰 → H'_𝒰`, and the two diagrams through `A_𝒰` are
then equivalent.

(Theorem 10.5.7) For strong bundles with the local regularity property of Definition 8.4.2,
generalized strong bundle isomorphisms `[D], [D']` with `|[D]| = |[D']|` are equal.

## What is formalized

* `EPLoc.Theorem_10_3_19` (the statement, in universe `u`) and
  `SBLocalization.Theorem_10_5_7` (the strong bundle statement, universe `0`).
* `EpGroupoid.Examples.isLR_trivialZ3`: `X = ℤ/3 × ℝ ⇉ ℝ` with the trivial action
  (`trivialZ3EpGroupoid`, Chapter 7) has (LR) in the sense of Definition 7.4.19
  (`EpGroupoid.IsLR`, which asks the property inside every open `O ∋ x`): its orbits are points,
  so the only orbit-preserving `β` is the identity `= 1̂`.
* `LocalizationLRCounterexample.theorem_10_3_19_counterexample` and **`not_theorem_10_3_19`**:
  `[X ←1 X →Inv X]` and `[1_X]` (`Inv(g, x) = (g⁻¹, x)`, a functor as `ℤ/3` is abelian) are
  generalized isomorphisms of `X` with the same orbit map, and they differ.  The inequality is the
  base part of `StrongBundleLocalizationExamples.remark_10_5_5` (the relation
  `Diagram.IsotropyRel`, invariant under equivalence of diagrams, pairs the generator with itself
  for `[1_X]` and not for `[Inv]`).
* `LocalizationLRCounterexample.not_naturallyEquivalent_id_inv`: there is no natural
  transformation `1 → Inv`, although the family `α_z = 1_z : 1(z) → Inv(z)` of Proposition
  10.1.10 (1) exists.
* `LocalizationLRCounterexample.isLR_z3EpBundle` (Definition 8.4.2 for `ℝ × ℝᵏ → ℝ` with the
  trivial `μ`) and **`not_theorem_10_5_7`**, from the full statement of `remark_10_5_5`.
* **The strongest correct version we prove**, `EPLoc.theorem_10_3_19_of_isEffective`: Theorem
  10.3.19 holds when in addition `Y` is effective (`EpGroupoid.IsEffective`).  Proof: for
  `e = f⁻¹ ≫ f'`, represented by `Y ←F A →Φ Y` with `|Φ| = |F|`, the families of Proposition
  10.1.10 (1) glue to a natural transformation `F → Φ` (`EquivalenceLREffective.lean`), so
  `e = [Y ←F A →F Y] = 1_Y`.  This avoids the weak fibred product and the cover `A_𝒰` of the
  text.  Hypotheses satisfiable: `theorem_10_3_19_of_isEffective_hypotheses` (point).

## What does not hold as we read it

* **Theorem 10.3.19 does not hold as we read it**, nor does Theorem 10.5.7.  The step of the proof
  that we cannot follow is the passage from the local families `α_a` to a natural transformation
  `H_𝒰 → H'_𝒰`: Proposition 10.1.10 (1) gives sc-smooth families `α_z : H(z) → H'(z)` with no
  naturality, and in the example the naturality `α_z ∘ g = g⁻¹ ∘ α_z` in the abelian `G_z = ℤ/3`
  fails for every choice of `α_z` and every generator `g`, on any neighbourhood.
* (LR) holds for the example in the reading of Definition 7.4.19 and also in its alternative
  formulation (p. 337), since every orbit is a point; the example is not effective
  (`EpGroupoid.Examples.not_isEffective_trivialZ3`).  The text itself notes in Remark 10.5.5 that
  `|[D]| = |[D']|` does not force `[D] = [D']` for strong bundles in general.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

namespace EPLocalization.EPLoc

/-- The statement of **2021 Theorem 10.3.19, p. 493 (2017: Theorem 10.7)** for ep-groupoids in
universe `u`: if one of `X`, `Y` has (LR), generalized isomorphisms `f, f' : X → Y` with
`|f| = |f'|` are equal.  It does not hold as we read it: `not_theorem_10_3_19`. -/
def Theorem_10_3_19 : Prop :=
  ∀ X Y : EP.{u}, X.X.IsLR ∨ Y.X.IsLR → ∀ f f' : of X ⟶ of Y, IsGeneralizedIso f →
    IsGeneralizedIso f' → orbitMap f = orbitMap f' → f = f'

/-- **Theorem 10.3.19 for an effective target** (the strongest correct version we prove): if one
of `X`, `Y` has (LR) and `Y` is effective, generalized isomorphisms `f, f' : X → Y` with
`|f| = |f'|` are equal. -/
theorem theorem_10_3_19_of_isEffective {X Y : EP.{u}} (hY : Y.X.IsEffective)
    (hLR : X.X.IsLR ∨ Y.X.IsLR) {f f' : of X ⟶ of Y} (hf : IsGeneralizedIso f)
    (hf' : IsGeneralizedIso f') (h : orbitMap f = orbitMap f') : f = f' := by
  have hYLR : Y.X.IsLR := hLR.elim (proposition_10_3_16 hf).1 id
  obtain ⟨g, hfg, hgf⟩ := hf
  have he : IsGeneralizedIso (g ≫ f') := by
    rw [isGeneralizedIso_iff_isIso] at hf' ⊢
    have : IsIso g := ⟨⟨f, hgf, hfg⟩⟩
    infer_instance
  have heo : orbitMap (g ≫ f') = _root_.id := by
    rw [proposition_10_3_11, ← h, ← proposition_10_3_11, hgf, orbitMap_id]
  have he1 : g ≫ f' = 𝟙 (of Y) := by
    obtain ⟨d, hd, hΦ⟩ := exists_diagram_of_isGeneralizedIso he
    rw [← hd] at heo ⊢
    have hdo : d.orbitMap = _root_.id := heo
    have hFΦ : d.F.orbitMap = d.Φ.orbitMap := funext fun q => by
      rw [← d.orbitMap_orbitMap_F q, hdo]
      rfl
    have hnat := EpFunctor.naturallyEquivalent_of_isEffective d.isEquivalence_F hΦ hFΦ
      ((EpFunctor.proposition_10_1_9 d.isEquivalence_F).2 hYLR) hY
    exact homMk_eq_homMk_iff.2
      ((Diagram.isRefinement_of_naturallyEquivalent d d.F d.isEquivalence_F d.F (.refl _)
        hnat).equiv.symm.trans (Diagram.isRefinement_id d.A d.F d.isEquivalence_F).equiv)
  calc f = f ≫ 𝟙 _ := (Category.comp_id f).symm
    _ = f ≫ g ≫ f' := by rw [he1]
    _ = f' := by rw [← Category.assoc, hfg, Category.id_comp]

/-- **Witness** for `theorem_10_3_19_of_isEffective`: the point ep-groupoid is effective, has
(LR), and `𝟙` is a generalized isomorphism. -/
theorem theorem_10_3_19_of_isEffective_hypotheses :
    EpGroupoid.Examples.pointEP.X.IsEffective ∧ EpGroupoid.Examples.pointEP.X.IsLR ∧
      IsGeneralizedIso (𝟙 (of EpGroupoid.Examples.pointEP)) :=
  ⟨EquivalenceLREffectiveExamples.isEffective_pointEP, EpGroupoid.Examples.isSLR_pointEP 0,
    ⟨𝟙 _, Category.id_comp _, Category.id_comp _⟩⟩

end EPLocalization.EPLoc

namespace SBLocalization

/-- The statement of **2021 Theorem 10.5.7, p. 508 (2017: Theorem 10.10)** for strong
bundles in universe `0`: if both strong bundles have the local regularity property (Definition
8.4.2), generalized strong bundle isomorphisms `[D], [D']` with `|[D]| = |[D']|` are equal.  It
does not hold as we read it: `not_theorem_10_5_7`. -/
def Theorem_10_5_7 : Prop :=
  ∀ A A' : SEP.{0}, A.E.IsLR → A'.E.IsLR → ∀ f f' : GenSBMap A A', f.IsGeneralizedIso →
    f'.IsGeneralizedIso → f.orbitMap = f'.orbitMap → f = f'

end SBLocalization

/-- **`ℤ/3 × ℝ ⇉ ℝ` (trivial action) has the local regularity property** (Definition 7.4.19):
its orbits are points, so an orbit-preserving `β` is the identity, the action of `1`. -/
theorem EpGroupoid.Examples.isLR_trivialZ3 : trivialZ3EpGroupoid.IsLR := by
  intro x O hO hxO
  obtain ⟨R, hRO⟩ := trivialZ3EpGroupoid.theorem_7_1 x hO hxO
  refine ⟨R, hRO, fun β β' _ hπ => ⟨1, fun y hy => ?_⟩⟩
  obtain ⟨φ, h1, h2⟩ := (GroupoidStr.π_eq_π_iff _).1 (hπ y hy)
  rw [R.Φ_one y hy]
  exact h1.symm.trans h2

namespace LocalizationLRCounterexample

open EpGroupoid.Examples EPLocalization SBLocalization StrongBundleLocalizationExamples

/-- **The step of the proof of Theorem 10.3.19 that we cannot follow**: there is no natural
transformation `1 → Inv` on `ℤ/3 × ℝ ⇉ ℝ` (naturality at the generator `g ∈ G_0` would give
`g = g⁻¹`), although `z ↦ 1_z : z → Inv(z) = z` is an sc-smooth family as in Proposition
10.1.10 (1). -/
theorem not_naturallyEquivalent_id_inv :
    ¬ (EpFunctor.id trivialZ3EpGroupoid).NaturallyEquivalent z3Inv := by
  rintro ⟨τ⟩
  have h := congrArg Prod.fst (τ.naturality (Multiplicative.ofAdd (1 : ZMod 3), 0))
  change (τ.app 0).1 * Multiplicative.ofAdd (1 : ZMod 3) =
    (Multiplicative.ofAdd (1 : ZMod 3))⁻¹ * (τ.app 0).1 at h
  rw [mul_comm, mul_right_cancel_iff] at h
  exact absurd h (by decide)

/-- The base ep-groupoid `ℤ/3 × ℝ ⇉ ℝ` as an object of `EP`. -/
abbrev z3EP : EP.{0} := (z3SEP 0).baseEP

/-- `[X ←1 X →Inv X]` for `X = ℤ/3 × ℝ ⇉ ℝ`. -/
abbrev genInv : EPLoc.of z3EP ⟶ EPLoc.of z3EP := (SDiagram.ofHom (z3InvHom 0)).cls.base

/-- `[1_X]` for `X = ℤ/3 × ℝ ⇉ ℝ`. -/
abbrev genId : EPLoc.of z3EP ⟶ EPLoc.of z3EP := (SDiagram.id (z3SEP 0)).cls.base

theorem isGeneralizedIso_genInv : EPLoc.IsGeneralizedIso genInv :=
  (EPLoc.theorem_10_3_10 _).1.2 (z3InvHom_mem_equivalences 0).isEquivalence_base

theorem isGeneralizedIso_genId : EPLoc.IsGeneralizedIso genId :=
  (EPLoc.theorem_10_3_10 _).1.2 (SEP.equivalences.id_mem (z3SEP 0)).isEquivalence_base

theorem orbitMap_genInv : EPLoc.orbitMap genInv = EPLoc.orbitMap genId :=
  base_orbitMap_ofHom_z3InvHom 0

theorem genInv_ne_genId : genInv ≠ genId := (remark_10_5_5 0).2.2.2.1

/-- **2021 Theorem 10.3.19, p. 493 (2017: Theorem 10.7), does not hold as we read it**: on
`X = ℤ/3 × ℝ ⇉ ℝ` (trivial action), which has (LR), the generalized isomorphisms
`[X ←1 X →Inv X]` and `[1_X]` have the same orbit map but differ. -/
theorem theorem_10_3_19_counterexample :
    z3EP.X.IsLR ∧ EPLoc.IsGeneralizedIso genInv ∧ EPLoc.IsGeneralizedIso genId ∧
      EPLoc.orbitMap genInv = EPLoc.orbitMap genId ∧ genInv ≠ genId :=
  ⟨isLR_trivialZ3, isGeneralizedIso_genInv, isGeneralizedIso_genId, orbitMap_genInv,
    genInv_ne_genId⟩

/-- **Theorem 10.3.19, as stated, does not hold as we read it.** -/
theorem not_theorem_10_3_19 : ¬ EPLoc.Theorem_10_3_19.{0} := fun h =>
  genInv_ne_genId (h z3EP z3EP (Or.inl isLR_trivialZ3) _ _ isGeneralizedIso_genInv
    isGeneralizedIso_genId orbitMap_genInv)

/-- **The strong bundle `ℝ × ℝᵏ → ℝ` over `ℤ/3 × ℝ ⇉ ℝ` (trivial `μ`) has the local regularity
property** (Definition 8.4.2): its orbits are points. -/
theorem isLR_z3EpBundle (k : ℕ) : (z3EpBundle k).IsLR := by
  intro x O hO hxO
  obtain ⟨R, hRO⟩ := trivialZ3EpGroupoid.theorem_7_1 x hO hxO
  refine ⟨R, hRO, fun β Φ hΦ _ hπ => ⟨1, fun w hw => ?_⟩⟩
  obtain ⟨q, h1, h2⟩ := (GroupoidStr.π_eq_π_iff _).1 (hπ w hw)
  exact h1.symm.trans h2

/-- **2021 Theorem 10.5.7, p. 508 (2017: Theorem 10.10), does not hold as we read it**: the
generalized strong bundle isomorphisms `[W ←1 W →Inv W]` and `[1_W]` of Remark 10.5.5, for
`W = ℝ × ℝᵏ → ℝ` over `ℤ/3 × ℝ ⇉ ℝ` (local regularity property: `isLR_z3EpBundle`), have the same
orbit map and differ. -/
theorem not_theorem_10_5_7 : ¬ Theorem_10_5_7 := fun h =>
  (remark_10_5_5 0).2.2.2.2 (h _ _ (isLR_z3EpBundle 0) (isLR_z3EpBundle 0) _ _
    (remark_10_5_5 0).1 (remark_10_5_5 0).2.1 (remark_10_5_5 0).2.2.1)

end LocalizationLRCounterexample

end Polyfold
