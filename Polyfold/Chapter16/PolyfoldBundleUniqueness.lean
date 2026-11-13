import Polyfold.Chapter16.StrongPolyfoldBundle
import Polyfold.Chapter16.ZhouUniquenessCheck
import Polyfold.Chapter10.LocalizationLREffectiveBundle

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 16,
§16.3: the uniqueness claim after **Definition 16.3.3** (p. 723; 2017: after Definition 16.17).
Numbers and pages are the 2021 text's.

# The uniqueness of `f` and `F` for equivalent strong polyfold bundle structures

## The text, paraphrased

(After Definition 16.3.3) For equivalent strong polyfold bundle structures the generalized
isomorphism `f` and the generalized strong bundle isomorphism `F` are uniquely determined:
`|f| = γ'⁻¹ ∘ γ` is fixed, so `f` is unique by (ZHOU), Theorem 10.3.19 and Proposition 7.4.22;
similarly `F` by Proposition 10.4.7.

## The check

`W = ℝ × ℝᵏ → ℝ` over `X = ℤ/3 × ℝ ⇉ ℝ` with the trivial actions (`z3SEP k`, Chapter 10) has
(ZHOU) (`isZhou_trivialZ3`), paracompact `|X|` (`hasParacompactOrbitSpace_trivialZ3`) and the
local regularity property (`isLR_z3EpBundle`), so `((P, μ), id, id)` is a strong polyfold bundle
structure for `|P| : |W| → |X|` (`z3Structure`).  The generalized strong bundle isomorphisms
`[1_W]` and `[W ←1 W →Inv W]` of Remark 10.5.5 both satisfy the two conditions of Definition 16.3.3
for the pair `(z3Structure, z3Structure)`, and they differ, already on the bases.  Hence:

* **The uniqueness after Definition 16.3.3 does not hold as we read it**, neither for `f` nor for
  `F`: `not_uniqueness_16_3_3`, from `uniqueness_16_3_3_counterexample`.
* For an effective base of the target both are unique: `uniqueness_16_3_3_of_isEffective`
  (Theorem 10.3.19 and Theorem 10.5.7 for an effective base; (ZHOU) gives (LR)).

Definitions 16.3.3 and 16.3.4 are unaffected.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

open EPLocalization SBLocalization

namespace StrongPolyfoldBundleStructure

/-- The statement after **2021 Definition 16.3.3, p. 723**, in universe `u`: for equivalent
strong polyfold bundle structures, the generalized isomorphism `f` and the generalized strong
bundle isomorphism `F` of Definition 16.3.3 are unique.  It does not hold as we read it:
`not_uniqueness_16_3_3`. -/
def Uniqueness_16_3_3 : Prop :=
  ∀ (Y Z : Type u) [TopologicalSpace Y] [TopologicalSpace Z] (p : Y → Z)
    (S S' : StrongPolyfoldBundleStructure p) (F F' : GenSBMap S.A S'.A),
    F.IsGeneralizedIso → F'.IsGeneralizedIso →
    ⇑S'.γ ∘ EPLoc.orbitMap F.base = ⇑S.γ → ⇑S'.Γ ∘ F.orbitMap = ⇑S.Γ →
    ⇑S'.γ ∘ EPLoc.orbitMap F'.base = ⇑S.γ → ⇑S'.Γ ∘ F'.orbitMap = ⇑S.Γ →
    F.base = F'.base ∧ F = F'

/-- **The uniqueness after Definition 16.3.3 for an effective base of the target**: if `X'` is
effective, `F` (Theorem 10.5.7 for an effective base) and `f` (Theorem 10.3.19 for an effective
target) are unique. -/
theorem uniqueness_16_3_3_of_isEffective {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
    {p : Y → Z} {S S' : StrongPolyfoldBundleStructure p} (hS' : S'.A.X.IsEffective)
    {F F' : GenSBMap S.A S'.A} (hF : F.IsGeneralizedIso) (hF' : F'.IsGeneralizedIso)
    (hγ : ⇑S'.γ ∘ EPLoc.orbitMap F.base = ⇑S.γ) (hΓ : ⇑S'.Γ ∘ F.orbitMap = ⇑S.Γ)
    (hγ' : ⇑S'.γ ∘ EPLoc.orbitMap F'.base = ⇑S.γ) (hΓ' : ⇑S'.Γ ∘ F'.orbitMap = ⇑S.Γ) :
    F.base = F'.base ∧ F = F' := by
  have hLR : S.A.X.IsLR := S.A.X.proposition_7_4_22_of_isZhou S.isZhou
  have horb : F.orbitMap = F'.orbitMap := by
    have e : ⇑S'.Γ ∘ F.orbitMap = ⇑S'.Γ ∘ F'.orbitMap := hΓ.trans hΓ'.symm
    funext q
    exact S'.Γ.injective (congrFun e q)
  have hbase : EPLoc.orbitMap F.base = EPLoc.orbitMap F'.base := by
    have e : ⇑S'.γ ∘ EPLoc.orbitMap F.base = ⇑S'.γ ∘ EPLoc.orbitMap F'.base := hγ.trans hγ'.symm
    funext q
    exact S'.γ.injective (congrFun e q)
  have hFF : F = F' :=
    theorem_10_5_7_of_isEffective S.isLR S'.isLR (Or.inl hLR) hS' hF hF' horb
  exact ⟨congrArg GenSBMap.base hFF, hFF⟩

open EpGroupoid.Examples StrongBundleLocalizationExamples LocalizationLRCounterexample

variable (k : ℕ)

/-- **A strong polyfold bundle structure with nontrivial isotropy** (Definition 16.3.1, also its
satisfiability): `ℝ × ℝᵏ → ℝ` over `ℤ/3 × ℝ ⇉ ℝ` (trivial actions), `Γ = id`, `γ = id`, for
`p = |P| : |W| → |X|`. -/
def z3Structure :
    StrongPolyfoldBundleStructure (z3SEP k).E.projFunctor.orbitMap where
  A := z3SEP k
  isZhou := isZhou_trivialZ3
  paracompact := hasParacompactOrbitSpace_trivialZ3
  isLR := isLR_z3EpBundle k
  Γ := Homeomorph.refl _
  γ := Homeomorph.refl _
  comm := rfl

/-- The strong polyfold bundle of `z3Structure` (Definition 16.3.4, witness). -/
def z3Bundle : StrongPolyfoldBundle (z3SEP k).E.projFunctor.orbitMap := ⟦z3Structure k⟧

theorem z3_orbitMap_id : (SDiagram.id (z3SEP k)).cls.orbitMap = _root_.id :=
  SDiagram.orbitMap_id' (z3SEP k)

theorem z3_baseOrbitMap_id : EPLoc.orbitMap (SDiagram.id (z3SEP k)).cls.base = _root_.id :=
  SEPLoc.baseOrbitMap_id (z3SEP k)

/-- **The counterexample to the uniqueness after 2021 Definition 16.3.3**: for `z3Structure`
(with (ZHOU), paracompact `|X|`, the local regularity property), `[W ←1 W →Inv W]` and `[1_W]`
are generalized strong bundle isomorphisms satisfying both conditions of Definition 16.3.3, and
they differ, already on the bases. -/
theorem uniqueness_16_3_3_counterexample :
    (SDiagram.ofHom (z3InvHom k)).cls.IsGeneralizedIso ∧
      (SDiagram.id (z3SEP k)).cls.IsGeneralizedIso ∧
      ⇑(z3Structure k).γ ∘ EPLoc.orbitMap (SDiagram.ofHom (z3InvHom k)).cls.base =
        ⇑(z3Structure k).γ ∧
      ⇑(z3Structure k).Γ ∘ (SDiagram.ofHom (z3InvHom k)).cls.orbitMap = ⇑(z3Structure k).Γ ∧
      ⇑(z3Structure k).γ ∘ EPLoc.orbitMap (SDiagram.id (z3SEP k)).cls.base =
        ⇑(z3Structure k).γ ∧
      ⇑(z3Structure k).Γ ∘ (SDiagram.id (z3SEP k)).cls.orbitMap = ⇑(z3Structure k).Γ ∧
      (SDiagram.ofHom (z3InvHom k)).cls.base ≠ (SDiagram.id (z3SEP k)).cls.base ∧
      (SDiagram.ofHom (z3InvHom k)).cls ≠ (SDiagram.id (z3SEP k)).cls := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := remark_10_5_5 k
  have hb : EPLoc.orbitMap (SDiagram.ofHom (z3InvHom k)).cls.base = _root_.id := by
    rw [← z3_baseOrbitMap_id k]
    exact base_orbitMap_ofHom_z3InvHom k
  have ht : (SDiagram.ofHom (z3InvHom k)).cls.orbitMap = _root_.id := by
    rw [← z3_orbitMap_id k]
    exact h3
  refine ⟨h1, h2, ?_, ?_, ?_, ?_, h4, h5⟩
  · rw [hb]; rfl
  · rw [ht]; rfl
  · rw [z3_baseOrbitMap_id]; rfl
  · rw [z3_orbitMap_id]; rfl

/-- **The uniqueness after 2021 Definition 16.3.3, p. 723, does not hold as we read it**, for
`f` and for `F`: `uniqueness_16_3_3_counterexample`. -/
theorem not_uniqueness_16_3_3 : ¬ Uniqueness_16_3_3.{0} := fun h => by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -⟩ := uniqueness_16_3_3_counterexample 0
  exact h7 (h _ _ _ (z3Structure 0) (z3Structure 0) _ _ h1 h2 h3 h4 h5 h6).1

/-- The base ep-groupoid of `z3Structure` is not effective. -/
theorem not_isEffective_z3Structure : ¬ (z3Structure k).A.X.IsEffective :=
  not_isEffective_trivialZ3

end StrongPolyfoldBundleStructure

end Polyfold
