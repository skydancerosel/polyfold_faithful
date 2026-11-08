import Polyfold.Chapter10.LocalizationCategory
import Polyfold.Chapter10.EquivalenceZhou

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 10, §10.3 (pp. 492–495; 2017: pp. 355–356): **Proposition 10.3.17, Remark
10.3.18, Definition 10.3.20 and Theorem 10.3.21** (for (LUC), (SLUC), (ZHOU)), all new in the 2021
edition except Remark 10.3.18 (2017: Remark 10.3, p. 355).  Numbers and pages are the 2021
text's.  The category `EP(E⁻¹)` is in `LocalizationCategory.lean`.

# Properties invariant under generalized isomorphisms

## The text, paraphrased

(p. 492) A generalized isomorphism `f : X → Y` is represented by `X ←F A →G Y` with `F`, `G`
equivalences, so a property invariant under equivalences passes from `X` to `A` to `Y`:
(Proposition 10.3.16) the local regularity property, by Proposition 10.1.9; (Proposition
10.3.17) the local unique continuation property, by Proposition 10.1.16.  (Remark 10.3.18, pp.
492–493) For a metrizable `Z`, pairs `(X, β)` with `β : |X| → Z` a homeomorphism; `(X', β')` is
equivalent to `(X, β)` if a generalized isomorphism `f : X → X'` has `β' ∘ |f| = β`; such `f` is
in general not unique.  (Theorem 10.3.19, p. 493) If one of `X`, `Y` has (LR), generalized
isomorphisms `f, f' : X → Y` with `|f| = |f'|` are equal (via Proposition 10.1.10).  (Definition
10.3.20, p. 494) `EP_reg` and `EP_reg(E⁻¹)`, the full subcategories of `EP` and `EP(E⁻¹)` on the
ep-groupoids with (LR).  (Theorem 10.3.21, p. 495) If one of `X`, `Y` has one of (LR), (LUC),
(SLR), (SLUC), (ZHOU), so has the other (Propositions 10.1.9, 10.1.16–10.1.19).

## What is formalized (namespace `Polyfold.EPLocalization`)

* `EPLoc.exists_diagram_of_isGeneralizedIso` (a representative with both legs equivalences, from
  Theorem 10.3.10) and `EPLoc.iff_of_isGeneralizedIso` (invariance under equivalences implies
  invariance under generalized isomorphisms).
* **Proposition 10.3.17**: `EPLoc.proposition_10_3_17`.  **Theorem 10.3.21** for (LUC), (SLUC),
  (ZHOU): `EPLoc.theorem_10_3_21` (from `EpFunctor.proposition_10_1_16`,
  `EP.proposition_10_1_18`, `EpFunctor.proposition_10_1_17`).
* **Definition 10.3.20**: `EPreg`, `EPLocReg` (`ObjectProperty.FullSubcategory`, with Mathlib's
  category structure); witnesses `Examples.pointReg`, `Examples.pointLocReg` (the point
  ep-groupoid has (LR), `EpGroupoid.Examples.isSLR_pointEP`).
* **Remark 10.3.18**: `OrbitChart` (pairs `(X, β)`), `OrbitChart.Rel`, an equivalence relation
  (`Rel.refl`, `Rel.symm`, `Rel.trans`, `OrbitChart.setoid`, by Proposition 10.3.11); witness
  `rel_pairEP_pointEP` (`(ℤ-pair, |pairToPoint|)` and `(point, 1)` are equivalent).

## Not formalized

* **Proposition 10.3.16** and the (LR), (SLR) parts of **Theorem 10.3.21**: they rest on
  Proposition 10.1.9, which is not formalized in §10.1; `iff_of_isGeneralizedIso` reduces them to
  it exactly as the text does.
* **Theorem 10.3.19**: it rests on Proposition 10.1.10 (not formalized in §10.1).
* **Remark 10.3.18**, the non-uniqueness of `f`, and **Remark 10.3.13**: interpretive; no
  invariant separating generalized maps with the same orbit map is available.

## What the text leaves implicit, and the choices made

* "If one has the property, so has the other" is stated as an `↔`.
* In Remark 10.3.18 the metrizability of `Z` plays no role in the relation and is dropped; `Z`
  is a topological space in the universe of the orbit spaces.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

namespace EPLocalization

namespace EPLoc

variable {X Y : EP.{u}}

/-- A generalized isomorphism `f : X → Y` is represented by a diagram of equivalences
`X ←F A →Φ Y` (Theorem 10.3.10; the input of Propositions 10.3.16, 10.3.17 and Theorem
10.3.21). -/
theorem exists_diagram_of_isGeneralizedIso {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) :
    ∃ d : Diagram X Y, homMk d = f ∧ d.Φ.IsEquivalence := by
  obtain ⟨d, rfl⟩ := homMk_surjective f
  exact ⟨d, rfl, (theorem_10_3_10 d).1.1 hf⟩

/-- A property of ep-groupoids invariant under equivalences is invariant under generalized
isomorphisms (2021 p. 492: `X ←F A →G Y` with `F`, `G` equivalences). -/
theorem iff_of_isGeneralizedIso (P : EP.{u} → Prop)
    (hP : ∀ {A B : EP.{u}} (F : EpFunctor A.X B.X), F.IsEquivalence → (P A ↔ P B))
    {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) : P X ↔ P Y := by
  obtain ⟨d, -, hΦ⟩ := exists_diagram_of_isGeneralizedIso hf
  exact (hP d.F d.isEquivalence_F).symm.trans (hP d.Φ hΦ)

/-- **2021 Proposition 10.3.17, p. 492 (new in the 2021 edition)**: if `f : X → Y` is a
generalized isomorphism, `X` has the local unique continuation property iff `Y` has it
(Proposition 10.1.16). -/
theorem proposition_10_3_17 {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) :
    X.X.IsLUC ↔ Y.X.IsLUC :=
  iff_of_isGeneralizedIso (fun A => A.X.IsLUC) (fun _ hF => EpFunctor.proposition_10_1_16 hF) hf

/-- **2021 Theorem 10.3.21, p. 495 (new in the 2021 edition)**, for the properties (LUC),
(SLUC) and (ZHOU) (Propositions 10.1.16, 10.1.18, 10.1.17); the parts (LR) and (SLR) rest on
Proposition 10.1.9, which is not formalized. -/
theorem theorem_10_3_21 {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) :
    (X.X.IsLUC ↔ Y.X.IsLUC) ∧ (X.IsSLUC ↔ Y.IsSLUC) ∧ (X.X.IsZhou ↔ Y.X.IsZhou) :=
  ⟨proposition_10_3_17 hf,
    iff_of_isGeneralizedIso EP.IsSLUC (fun _ hF => EP.proposition_10_1_18 hF) hf,
    iff_of_isGeneralizedIso (fun A => A.X.IsZhou) (fun _ hF => EpFunctor.proposition_10_1_17 hF)
      hf⟩

end EPLoc

/-! ### Definition 10.3.20 -/

/-- **2021 Definition 10.3.20, p. 494 (new in the 2021 edition)**: `EP_reg`, the full
subcategory of `EP` of the ep-groupoids with the local regularity property (LR). -/
abbrev EPreg : Type (u + 1) := ObjectProperty.FullSubcategory fun X : EP.{u} => X.X.IsLR

/-- **2021 Definition 10.3.20**: `EP_reg(E⁻¹)`, the full subcategory of `EP(E⁻¹)` of the
ep-groupoids with (LR). -/
abbrev EPLocReg : Type (u + 1) :=
  ObjectProperty.FullSubcategory fun X : EPLoc.{u} => X.toEP.X.IsLR

/-- **Witness** for Definition 10.3.20: the point ep-groupoid has (LR), so it is an object of
`EP_reg` and of `EP_reg(E⁻¹)`. -/
def Examples.pointReg : EPreg.{0} :=
  ⟨EpGroupoid.Examples.pointEP, EpGroupoid.Examples.isSLR_pointEP 0⟩

/-- The point ep-groupoid as an object of `EP_reg(E⁻¹)`. -/
def Examples.pointLocReg : EPLocReg.{0} :=
  ⟨EPLoc.of EpGroupoid.Examples.pointEP, EpGroupoid.Examples.isSLR_pointEP 0⟩

/-! ### Remark 10.3.18: equivalence of pairs `(X, β)` -/

/-- A pair `(X, β)` of an ep-groupoid and a homeomorphism `β : |X| → Z` (2021 Remark 10.3.18,
p. 492 (2017: Remark 10.3, p. 355)). -/
structure OrbitChart (Z : Type u) [TopologicalSpace Z] : Type (u + 1) where
  /-- The ep-groupoid. -/
  X : EP.{u}
  /-- The homeomorphism `β : |X| → Z`. -/
  β : X.X.OrbitSpace ≃ₜ Z

namespace OrbitChart

variable {Z : Type u} [TopologicalSpace Z]

/-- **Remark 10.3.18**: `(X', β')` is equivalent to `(X, β)` if some generalized isomorphism
`f : X → X'` has `β' ∘ |f| = β`. -/
def Rel (p q : OrbitChart Z) : Prop :=
  ∃ f : EPLoc.of p.X ⟶ EPLoc.of q.X, EPLoc.IsGeneralizedIso f ∧ q.β ∘ EPLoc.orbitMap f = p.β

theorem Rel.refl (p : OrbitChart Z) : Rel p p :=
  ⟨𝟙 _, ⟨𝟙 _, Category.id_comp _, Category.id_comp _⟩, by rw [EPLoc.orbitMap_id]; rfl⟩

theorem Rel.symm {p q : OrbitChart Z} (h : Rel p q) : Rel q p := by
  obtain ⟨f, ⟨g, hfg, hgf⟩, hβ⟩ := h
  refine ⟨g, ⟨f, hgf, hfg⟩, ?_⟩
  rw [← hβ, Function.comp_assoc, ← EPLoc.proposition_10_3_11, hgf, EPLoc.orbitMap_id]
  rfl

theorem Rel.trans {p q r : OrbitChart Z} (h : Rel p q) (h' : Rel q r) : Rel p r := by
  obtain ⟨f, ⟨g, hfg, hgf⟩, hβ⟩ := h
  obtain ⟨f', ⟨g', hfg', hgf'⟩, hβ'⟩ := h'
  refine ⟨f ≫ f', ⟨g' ≫ g, ?_, ?_⟩, ?_⟩
  · rw [Category.assoc, ← Category.assoc f', hfg', Category.id_comp, hfg]
  · rw [Category.assoc, ← Category.assoc g, hgf, Category.id_comp, hgf']
  · rw [EPLoc.proposition_10_3_11, ← Function.comp_assoc, hβ', hβ]

/-- **Remark 10.3.18**: the equivalence of pairs `(X, β)` is an equivalence relation. -/
instance setoid : Setoid (OrbitChart Z) where
  r := Rel
  iseqv := ⟨Rel.refl, Rel.symm, Rel.trans⟩

/-- **Witness** for Remark 10.3.18: `(pairEP, |pairToPoint|)` and `(pointEP, 1)` are equivalent
pairs over `Z = |point|`. -/
theorem rel_pairEP_pointEP :
    Rel (Z := Examples.pointEP.X.OrbitSpace)
      ⟨Examples.pairEP, IsHomeomorph.homeomorph _
        Examples.isEquivalence_pairToPointEP.isHomeomorph_orbitMap⟩
      ⟨Examples.pointEP, Homeomorph.refl _⟩ := by
  refine ⟨EPLoc.localizationFunctor.map Examples.pairToPointEP,
    Examples.isGeneralizedIso_pairToPoint.1, ?_⟩
  funext q
  change Diagram.orbitMap (Diagram.ofFunctor Examples.pairToPointEP) q = _
  rw [Diagram.orbitMap_eq_of (r := q) (congrFun EpFunctor.orbitMap_id q)]
  rfl

end OrbitChart

end EPLocalization

end Polyfold
