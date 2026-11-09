import Polyfold.Chapter11.CoveringEquivalenceTheorem

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 11, §11.6 "Coverings and Equivalences" (pp. 561–566; 2017: pp. 410–413):
the category `PC` of proper coverings and its class `E_PC` of equivalences, **Definition 11.6.7**
(2017: Definition 11.8) and **Proposition 11.6.8** (2017: Proposition 11.8); a note on
**Remark 11.6.9** (2017: Remark 11.4).

# Diagrams of proper coverings and common refinements

## The text, paraphrased

(p. 561) Proper coverings of ep-groupoids and the functors of Definition 11.6.4 (1) form a
category `PC` with the class `E_PC` of equivalences.  A diagram `d : F → F'` is
`F ← A → F'`, `Γ : A → F` an equivalence of proper coverings and `ε : A → F'` a functor.

(Definition 11.6.7, p. 561) A common refinement of diagrams `d, d' : F → F'` consists of
equivalences `H : A'' → A`, `H' : A'' → A'` with `Γ ∘ H ≃ Γ' ∘ H'` and `ε ∘ H ≃ ε' ∘ H'`.

(Proposition 11.6.8, p. 562) If `d, d'` and `d', d''` have common refinements, so have `d, d''`.
*Proof*: take the weak fibred product `A'' ×_{A'} B''` of `H'` and `K`; by Theorem 11.6.6 its
projections are equivalences and `H' ∘ π_{A''} ≃ K ∘ π_{B''}`; then `H ∘ π_{A''}` and
`K' ∘ π_{B''}` refine `d, d''`.

(pp. 561–563) The localization `PC(E⁻¹)`, with the classes `[d]` as morphisms, is sketched; the
details are left to the reader.  (Remark 11.6.9, pp. 563–566) Strong bundles are incorporated:
Definition 8.5.9 is recalled, and a category `SBPC` of proper strong bundle coverings with a
localization is indicated, the details again left to the reader.

## What is formalized (namespace `Polyfold.PC`)

* `ProperCoveringHom.comp_assoc`; `PC` (a bundled proper covering functor), the `Category PC`
  instance, `PC.equivalences : MorphismProperty PC` (`E_PC`), multiplicative.
* `PC.fibred Γ hΓ Λ`, `fibredFst`, `fibredSnd`: Theorem 11.6.6 (1) as an object of `PC`.
* `PC.Diagram F F'`; **Definition 11.6.7**: `Diagram.CommonRefinement`, `HasCommonRefinement`.
* **Proposition 11.6.8**: `PC.proposition_11_6_8`; with reflexivity and symmetry,
  `Diagram.hasCommonRefinement_equivalence` (the text's "defines an equivalence relation").
* Witnesses (namespace `Polyfold.PC.Examples`): the objects `pair`, `point` (identity coverings
  of the pair groupoid of `ℤ` and of the point), `equivalences_pairToPoint` (a morphism of `E_PC`
  without inverse functor), the diagrams `diagram` (`pair ← pair → point`) and `diagram'`
  (through the weak fibred product `pair ×_point pair`), and `hasCommonRefinement_diagram`, a
  common refinement of them built from Theorem 11.6.6 (3).

## What the text leaves implicit, and the choices made

* In the proof of Proposition 11.6.8 the displayed chain for the `ε`'s ends at
  `ε' ∘ K ∘ π_{B''}`; the last step to `ε'' ∘ K' ∘ π_{B''}` uses the fourth assumption
  `ε' ∘ K ≃ ε'' ∘ K'`, as in the chain for the `Γ`'s.  The formal proof adds it.
* "Naturally equivalent" is Definition 11.6.5 (`ProperCoveringHom.NaturallyEquivalent`), which is
  compatible with composition on both sides; composition is associative on the nose.
* All proper coverings in `PC` live in one universe, so that weak fibred products stay in `PC`.
* Not formalized: the localization `PC(E⁻¹)` and the functor `I : PC → PC(E⁻¹)` (sketched, the
  well-definedness of the composition left to the reader), and the category `SBPC` of Remark
  11.6.9 with its localization (details left to the reader).  The rest of Remark 11.6.9 recalls
  2021 Definition 8.5.9, which is `EpStrongBundle.IsProperStrongBundleCovering2021`
  (`Chapter8/Book2021.lean`).
-/

set_option maxSynthPendingDepth 3

open Set Function CategoryTheory

noncomputable section

namespace Polyfold

/-! ### The category `PC`, Definition 11.6.7 and Proposition 11.6.8 -/

section PC

universe u

theorem ProperCoveringHom.comp_assoc {O₁ M₁ O₂ M₂ O₃ M₃ O₄ M₄ O₅ M₅ O₆ M₆ O₇ M₇ O₈ M₈ : Type u}
    [TopologicalSpace O₁] [T2Space O₁] [ParacompactSpace O₁] [TopologicalSpace M₁] [T2Space M₁]
    [ParacompactSpace M₁] [TopologicalSpace O₂] [T2Space O₂] [ParacompactSpace O₂]
    [TopologicalSpace M₂] [T2Space M₂] [ParacompactSpace M₂] [TopologicalSpace O₃] [T2Space O₃]
    [ParacompactSpace O₃] [TopologicalSpace M₃] [T2Space M₃] [ParacompactSpace M₃]
    [TopologicalSpace O₄] [T2Space O₄] [ParacompactSpace O₄] [TopologicalSpace M₄] [T2Space M₄]
    [ParacompactSpace M₄] [TopologicalSpace O₅] [T2Space O₅] [ParacompactSpace O₅]
    [TopologicalSpace M₅] [T2Space M₅] [ParacompactSpace M₅] [TopologicalSpace O₆] [T2Space O₆]
    [ParacompactSpace O₆] [TopologicalSpace M₆] [T2Space M₆] [ParacompactSpace M₆]
    [TopologicalSpace O₇] [T2Space O₇] [ParacompactSpace O₇] [TopologicalSpace M₇] [T2Space M₇]
    [ParacompactSpace M₇] [TopologicalSpace O₈] [T2Space O₈] [ParacompactSpace O₈]
    [TopologicalSpace M₈] [T2Space M₈] [ParacompactSpace M₈]
    {Y₁ : EpGroupoid O₁ M₁} {X₁ : EpGroupoid O₂ M₂} {Y₂ : EpGroupoid O₃ M₃}
    {X₂ : EpGroupoid O₄ M₄} {Y₃ : EpGroupoid O₅ M₅} {X₃ : EpGroupoid O₆ M₆}
    {Y₄ : EpGroupoid O₇ M₇} {X₄ : EpGroupoid O₈ M₈} {F₁ : EpFunctor Y₁ X₁} {F₂ : EpFunctor Y₂ X₂}
    {F₃ : EpFunctor Y₃ X₃} {F₄ : EpFunctor Y₄ X₄} (Γ₃ : ProperCoveringHom F₃ F₄)
    (Γ₂ : ProperCoveringHom F₂ F₃) (Γ₁ : ProperCoveringHom F₁ F₂) :
    (Γ₃.comp Γ₂).comp Γ₁ = Γ₃.comp (Γ₂.comp Γ₁) :=
  ProperCoveringHom.ext (EpFunctor.ext rfl rfl) (EpFunctor.ext rfl rfl)

/-- **A proper covering functor between ep-groupoids**, bundled: an object of the category `PC`
of proper coverings (2021 p. 561). -/
structure PC : Type (u + 1) where
  /-- The ep-groupoid `Y`. -/
  Y : EP.{u}
  /-- The ep-groupoid `X`. -/
  X : EP.{u}
  /-- The proper covering functor `F : Y → X`. -/
  F : EpFunctor Y.X X.X
  isProperCovering : F.IsProperCovering

/-- **The category `PC`** (2021 p. 561): proper covering functors and the sc-smooth functors
between them of Definition 11.6.4 (1). -/
instance : Category PC.{u} where
  Hom A B := ProperCoveringHom A.F B.F
  id A := ProperCoveringHom.id A.F
  comp f g := g.comp f
  id_comp _ := ProperCoveringHom.ext (EpFunctor.ext rfl rfl) (EpFunctor.ext rfl rfl)
  comp_id _ := ProperCoveringHom.ext (EpFunctor.ext rfl rfl) (EpFunctor.ext rfl rfl)
  assoc _ _ _ := ProperCoveringHom.ext (EpFunctor.ext rfl rfl) (EpFunctor.ext rfl rfl)

/-- **The class `E_PC` of equivalences** (Definition 11.6.4 (2)), a multiplicative class of
morphisms of `PC`. -/
def PC.equivalences : MorphismProperty PC.{u} := fun _ _ Γ => ProperCoveringHom.IsEquivalence Γ

instance : PC.equivalences.{u}.IsMultiplicative where
  id_mem A := ProperCoveringHom.IsEquivalence.id (F := A.F)
  comp_mem _ _ hf hg := ProperCoveringHom.IsEquivalence.comp hg hf

namespace PC

open WeakFibredProduct ProperCoveringHom

/-- **The weak fibred product of proper coverings** `A ×_C B` along an equivalence
`Γ : A → C` and a functor `Λ : B → C` (Theorem 11.6.6 (1)): `H : P → Q`. -/
def fibred {A B C : PC.{u}} (Γ : ProperCoveringHom A.F C.F) (hΓ : Γ.IsEquivalence)
    (Λ : ProperCoveringHom B.F C.F) : PC.{u} where
  Y := ⟨_, _, epGroupoid Γ.Ψ Λ.Ψ (.of_isEquivalence_left hΓ.isEquivalence_Ψ)⟩
  X := ⟨_, _, epGroupoid Γ.Φ Λ.Φ (.of_isEquivalence_left hΓ.isEquivalence_Φ)⟩
  F := hFunctor Γ Λ _ _
  isProperCovering := (theorem_11_6_6 Γ Λ A.isProperCovering C.isProperCovering
    B.isProperCovering hΓ).1

/-- `π_A : A ×_C B → A`. -/
def fibredFst {A B C : PC.{u}} (Γ : ProperCoveringHom A.F C.F) (hΓ : Γ.IsEquivalence)
    (Λ : ProperCoveringHom B.F C.F) : ProperCoveringHom (fibred Γ hΓ Λ).F A.F :=
  projLeftHom Γ Λ _ _

/-- `π_B : A ×_C B → B`. -/
def fibredSnd {A B C : PC.{u}} (Γ : ProperCoveringHom A.F C.F) (hΓ : Γ.IsEquivalence)
    (Λ : ProperCoveringHom B.F C.F) : ProperCoveringHom (fibred Γ hΓ Λ).F B.F :=
  projRightHom Γ Λ _ _

/-- A diagram `d : F ← A → F'` between proper coverings (2021 p. 561): `Γ : A → F` an
equivalence of proper coverings and `ε : A → F'` a functor between proper coverings. -/
structure Diagram (F F' : PC.{u}) where
  /-- The proper covering `A`. -/
  A : PC.{u}
  /-- The equivalence `Γ : A → F`. -/
  Γ : ProperCoveringHom A.F F.F
  isEquivalence_Γ : Γ.IsEquivalence
  /-- The functor `ε : A → F'`. -/
  ε : ProperCoveringHom A.F F'.F

/-- **2021 Definition 11.6.7, p. 561 (2017: Definition 11.8, p. 410)**: a common refinement of
diagrams `d, d' : F → F'` between proper coverings: equivalences `H : A'' → A`, `H' : A'' → A'`
of proper coverings with `Γ ∘ H ≃ Γ' ∘ H'` and `ε ∘ H ≃ ε' ∘ H'` (Definition 11.6.5). -/
structure Diagram.CommonRefinement {F F' : PC.{u}} (d d' : Diagram F F') where
  /-- The proper covering `A''`. -/
  A'' : PC.{u}
  /-- `H : A'' → A`. -/
  H : ProperCoveringHom A''.F d.A.F
  /-- `H' : A'' → A'`. -/
  H' : ProperCoveringHom A''.F d'.A.F
  isEquivalence_H : H.IsEquivalence
  isEquivalence_H' : H'.IsEquivalence
  natEquiv_Γ : (d.Γ.comp H).NaturallyEquivalent (d'.Γ.comp H')
  natEquiv_ε : (d.ε.comp H).NaturallyEquivalent (d'.ε.comp H')

/-- `d` and `d'` have a common refinement. -/
def Diagram.HasCommonRefinement {F F' : PC.{u}} (d d' : Diagram F F') : Prop :=
  Nonempty (d.CommonRefinement d')

/-- **2021 Proposition 11.6.8, p. 562 (2017: Proposition 11.8, p. 411)**: if `d, d'` and
`d', d''` have common refinements, so have `d, d''`: the weak fibred product `A'' ×_{A'} B''` of
`H'` and `K` with the equivalences `H ∘ π_{A''}` and `K' ∘ π_{B''}` (Theorem 11.6.6). -/
theorem proposition_11_6_8 {F F' : PC.{u}} {d d' d'' : Diagram F F'}
    (h : d.HasCommonRefinement d') (h' : d'.HasCommonRefinement d'') :
    d.HasCommonRefinement d'' := by
  obtain ⟨⟨A₁, H, H', hH, hH', hΓ₁, hε₁⟩⟩ := h
  obtain ⟨⟨B₁, K, K', hK, hK', hΓ₂, hε₂⟩⟩ := h'
  obtain ⟨-, hπr, hnat, -, hπl⟩ := theorem_11_6_6 H' K A₁.isProperCovering d'.A.isProperCovering
    B₁.isProperCovering hH'
  have hEq := naturallyEquivalent_equivalence (F := (fibred H' hH' K).F) (F' := F.F)
  have hEq' := naturallyEquivalent_equivalence (F := (fibred H' hH' K).F) (F' := F'.F)
  have hn := hnat.comp_right d'.Γ
  have hn' := hnat.comp_right d'.ε
  rw [← ProperCoveringHom.comp_assoc, ← ProperCoveringHom.comp_assoc] at hn hn'
  refine ⟨⟨fibred H' hH' K, H.comp (fibredFst H' hH' K), K'.comp (fibredSnd H' hH' K),
    hH.comp (hπl hK), hK'.comp hπr, ?_, ?_⟩⟩
  · rw [← ProperCoveringHom.comp_assoc, ← ProperCoveringHom.comp_assoc]
    exact hEq.trans (hΓ₁.comp_left _) (hEq.trans hn (hΓ₂.comp_left _))
  · rw [← ProperCoveringHom.comp_assoc, ← ProperCoveringHom.comp_assoc]
    exact hEq'.trans (hε₁.comp_left _) (hEq'.trans hn' (hε₂.comp_left _))

/-- Having a common refinement is an equivalence relation on diagrams `F → F'` (2021 p. 561,
"as the following proposition shows"; reflexivity and symmetry are immediate). -/
theorem Diagram.hasCommonRefinement_equivalence {F F' : PC.{u}} :
    Equivalence (Diagram.HasCommonRefinement (F := F) (F' := F')) where
  refl d := ⟨⟨d.A, ProperCoveringHom.id _, ProperCoveringHom.id _, IsEquivalence.id,
    IsEquivalence.id, naturallyEquivalent_equivalence.refl _,
    naturallyEquivalent_equivalence.refl _⟩⟩
  symm := fun ⟨c⟩ => ⟨⟨c.A'', c.H', c.H, c.isEquivalence_H', c.isEquivalence_H,
    naturallyEquivalent_equivalence.symm c.natEquiv_Γ,
    naturallyEquivalent_equivalence.symm c.natEquiv_ε⟩⟩
  trans := proposition_11_6_8

end PC

end PC


/-! ### Witnesses -/

namespace PC.Examples

open EpGroupoid.Examples CoveringEquivalence.Examples ProperCoveringHom

/-- The identity covering of the pair groupoid of `ℤ`, an object of `PC`. -/
abbrev pair : PC.{0} :=
  ⟨⟨ℤ, ℤ × ℤ, pairEpGroupoid⟩, ⟨ℤ, ℤ × ℤ, pairEpGroupoid⟩, EpFunctor.id _,
    EpFunctor.isProperCovering_id⟩

/-- The identity covering of the point, an object of `PC`. -/
abbrev point : PC.{0} :=
  ⟨⟨Unit, Unit, pointEpGroupoid⟩, ⟨Unit, Unit, pointEpGroupoid⟩, EpFunctor.id _,
    EpFunctor.isProperCovering_id⟩

/-- **Witness for `E_PC`**: `pairToPointCovering : pair ⟶ point` is in the class of
equivalences. -/
theorem equivalences_pairToPoint :
    PC.equivalences (show pair ⟶ point from pairToPointCovering) :=
  isEquivalence_pairToPointCovering

/-- **Witness for diagrams**: `pair ← pair → point` with `Γ = 1` and `ε = pairToPointCovering`. -/
def diagram : Diagram pair point :=
  ⟨pair, ProperCoveringHom.id _, IsEquivalence.id, pairToPointCovering⟩

/-- The weak fibred product `pair ×_point pair` of `pairToPointCovering` with itself. -/
abbrev fibredPair : PC.{0} :=
  fibred (A := pair) (B := pair) (C := point) pairToPointCovering
    isEquivalence_pairToPointCovering pairToPointCovering

/-- `π₁ : pair ×_point pair → pair` is an equivalence (Theorem 11.6.6, last claim). -/
theorem isEquivalence_fibredFst :
    (fibredFst (A := pair) (B := pair) (C := point) pairToPointCovering
      isEquivalence_pairToPointCovering pairToPointCovering).IsEquivalence :=
  (theorem_11_6_6 _ _ pair.isProperCovering point.isProperCovering pair.isProperCovering
    isEquivalence_pairToPointCovering).2.2.2.2 isEquivalence_pairToPointCovering

/-- **Witness for diagrams**: `pair ← pair ×_point pair → point` with `Γ = π₁` and
`ε = pairToPointCovering ∘ π₂`. -/
def diagram' : Diagram pair point where
  A := fibredPair
  Γ := fibredFst pairToPointCovering isEquivalence_pairToPointCovering pairToPointCovering
  isEquivalence_Γ := isEquivalence_fibredFst
  ε := pairToPointCovering.comp
    (fibredSnd pairToPointCovering isEquivalence_pairToPointCovering pairToPointCovering)

/-- **Witness for Definition 11.6.7 and Proposition 11.6.8**: `diagram` and `diagram'` have a
common refinement, `H = π₁`, `H' = 1`; the natural equivalence for the `ε`'s is Theorem
11.6.6 (3).  Proposition 11.6.8 then applies to `diagram, diagram', diagram`. -/
theorem hasCommonRefinement_diagram : diagram.HasCommonRefinement diagram' :=
  ⟨⟨fibredPair,
    fibredFst pairToPointCovering isEquivalence_pairToPointCovering pairToPointCovering,
    ProperCoveringHom.id _, isEquivalence_fibredFst, IsEquivalence.id,
    naturallyEquivalent_equivalence.refl _,
    (theorem_11_6_6 _ _ pair.isProperCovering point.isProperCovering pair.isProperCovering
      isEquivalence_pairToPointCovering).2.2.1⟩⟩

/-- **Witness for Proposition 11.6.8**: from `diagram ≈ diagram'` and its symmetric. -/
theorem hasCommonRefinement_diagram_diagram :
    diagram.HasCommonRefinement diagram :=
  proposition_11_6_8 hasCommonRefinement_diagram
    (Diagram.hasCommonRefinement_equivalence.symm hasCommonRefinement_diagram)

end PC.Examples

end Polyfold
