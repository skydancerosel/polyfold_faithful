import Polyfold.Chapter11.CoveringEquivalenceDiagram
import Polyfold.Chapter10.Localization

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 11, §11.6 "Coverings and Equivalences", pp. 561–563 (2017: pp. 410–413):
**the localization `PC(E⁻¹)`** of the category of proper coverings at its equivalences, and
**the functor `I : PC → PC(E⁻¹)`**.

## The text, paraphrased

(p. 561) The localization of `PC` at `E_PC` is carried out as in the ep-groupoid case; the text
sketches the basic points and leaves the details to the reader.  `PC(E⁻¹)` has the objects of
`PC`; a morphism `F → F'` is the class `[d]` of a diagram `d : F ←Γ A →ε F'` under common
refinement (Definition 11.6.7, Proposition 11.6.8).  (p. 563) For `d : F → F'` and
`d' : F' → F''` the composite `[d'] ∘ [d]` is the class of `F ← A ×_{F'} A' → F''`, through the
weak fibred product of `A →ε F' ←Γ' A'`; its class does not depend on the representatives.
The identities are `[F ←1 F →1 F]`, the inverse of `[F ←Γ A →Γ' F']` (`Γ'` an equivalence) is
`[F' ←Γ' A →Γ F]`, and `I` is the identity on objects with `I(ε) = [F ←1 F →ε F']`.

## What is formalized

* `WeakFibredProduct.pairFunctor L R α : P → X ×_Y Z`, `p ↦ (L(p), α(p), R(p))`, for functors
  `L : P → X`, `R : P → Z` and a natural transformation `α : F ∘ L → G ∘ R` (the universal
  property of the weak fibred product, Theorem 10.2.2, on the nose: `π_X ∘ ⟨L, R⟩ = L`,
  `π_Z ∘ ⟨L, R⟩ = R`); `PC.fibredLift` is its version for proper coverings, `(ψ, ϕ)` on the
  two levels, with the square (11.20) for `α`.
* `PC.IsEquivalence.of_comp_left` (two out of three for `E_PC`), `PC.isEquivalence_fibredLift`.
* `PC.Diagram.comp` (the composite through `PC.fibred`), `Diagram.id`, `Diagram.ofHom`,
  `Diagram.setoid`, the well-definedness `Diagram.hasCommonRefinement_comp`, associativity and the
  unit laws up to common refinement.
* `PCLoc` and its `Category` instance (**`PC(E⁻¹)`**), `PCLoc.homMk`, the functor
  **`PCLoc.I : PC ⥤ PCLoc`**, **`PCLoc.isIso_I_map`** (equivalences go to isomorphisms,
  inverse `[F' ←Γ F →1 F]`, `PCLoc.inv_I_map`), `PCLoc.homMk_eq` (`[d] = I(Γ)⁻¹ ≫ I(ε)`),
  **`PCLoc.isIso_homMk`** and **`PCLoc.inv_homMk`** (the inverse of `[F ←Γ A →Γ' F']` for an
  equivalence `Γ'` is `[F' ←Γ' A →Γ F]`), `PCLoc.isInvertedBy_I`.
* Witness: `PCLoc.Examples.not_isIso_pairToPoint_isIso_I_map` (`pair → point` is not an
  isomorphism of `PC`, its image under `I` is one of `PC(E⁻¹)`).

## Choices

* The text takes `A ×_{F'} A'` (`A` first); Theorem 11.6.6 is stated in the project with the
  equivalence on the left, so the middle of the composite is `A' ×_{F'} A` (`PC.fibred Γ' ε`),
  `Γ ∘ π_A` and `ε' ∘ π_{A'}` as in the text.  The two products are isomorphic; the class of the
  composite is what matters.
* Well-definedness is proved with explicit maps of weak fibred products (`fibredLift`) which are
  equivalences by two out of three (the projection to the side of the equivalence is one,
  Theorem 11.6.6 (2)); the common refinement of Definition 11.6.7 is then a single equivalence
  `M` with `Γ' ∘ M ≃ Γ`, `ε' ∘ M ≃ ε` (`Diagram.hasCommonRefinement_of_map`).
-/

set_option maxSynthPendingDepth 3

open Set Function CategoryTheory

noncomputable section

namespace Polyfold

/-! ### Maps into a weak fibred product -/

namespace WeakFibredProduct

section Pair

universe u₀ u v w

variable {ObjP MorP : Type u₀} [TopologicalSpace ObjP] [T2Space ObjP] [ParacompactSpace ObjP]
  [TopologicalSpace MorP] [T2Space MorP] [ParacompactSpace MorP]
  {ObjX MorX : Type u} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {ObjY MorY : Type v} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  {ObjZ MorZ : Type w} [TopologicalSpace ObjZ] [T2Space ObjZ] [ParacompactSpace ObjZ]
  [TopologicalSpace MorZ] [T2Space MorZ] [ParacompactSpace MorZ]
  {P : EpGroupoid ObjP MorP} {X : EpGroupoid ObjX MorX} {Y : EpGroupoid ObjY MorY}
  {Z : EpGroupoid ObjZ MorZ} {F : EpFunctor X Y} {G : EpFunctor Z Y}
  (L : EpFunctor P X) (R : EpFunctor P Z) (α : EpNatTrans (F.comp L) (G.comp R))

/-- `p ↦ (L(p), α(p), R(p))`. -/
def pairObj (p : ObjP) : Obj F G :=
  Obj.mk F G (L.obj p) (α.app p) (R.obj p) (α.src_app p) (α.tgt_app p)

/-- `m ↦ (L(m), α(s(m)), R(m))`. -/
def pairMor (m : MorP) : Mor F G :=
  Mor.mk F G (L.mor m) (α.app (P.src m)) (R.mor m)
    ((α.src_app _).trans (congrArg F.obj (L.src_mor m).symm))
    ((α.tgt_app _).trans (congrArg G.obj (R.src_mor m).symm))

variable {L R α}

theorem src_pairMor (m : MorP) : src (pairMor L R α m) = pairObj L R α (P.src m) :=
  Obj.ext (L.src_mor m) rfl (R.src_mor m)

theorem tgt_pairMor (m : MorP) : tgt (pairMor L R α m) = pairObj L R α (P.tgt m) := by
  refine Obj.ext (L.tgt_mor m) ?_ (R.tgt_mor m)
  change Y.comp (Y.comp (G.mor (R.mor m)) (α.app (P.src m))) (Y.inv (F.mor (L.mor m))) =
    α.app (P.tgt m)
  have hn : Y.comp (G.mor (R.mor m)) (α.app (P.src m)) =
      Y.comp (α.app (P.tgt m)) (F.mor (L.mor m)) := (α.naturality m).symm
  rw [hn, GroupoidStr.comp_inv_cancel_right]
  rw [α.src_app, F.tgt_mor, L.tgt_mor]
  rfl

variable (L R α)

/-- **The map `⟨L, R⟩_α : P → X ×_Y Z`** into the weak fibred product (Definition 10.2.1),
`p ↦ (L(p), α(p), R(p))` and `m ↦ (L(m), α(s(m)), R(m))`, for a natural transformation
`α : F ∘ L → G ∘ R`. -/
def pairFunctor (h : Admissible F G) : EpFunctor P (epGroupoid F G h) where
  obj := pairObj L R α
  mor := pairMor L R α
  src_mor := src_pairMor
  tgt_mor := tgt_pairMor
  mor_comp m m' hc := by
    have hc' : src (pairMor L R α m) = tgt (pairMor L R α m') := by
      rw [src_pairMor, tgt_pairMor, hc]
    change pairMor L R α (P.comp m m') = comp (pairMor L R α m) (pairMor L R α m')
    refine Mor.ext ?_ ?_ ?_
    · rw [h_comp hc']; exact L.mor_comp _ _ hc
    · rw [φ_comp hc']
      change α.app (P.src (P.comp m m')) = α.app (P.src m')
      rw [P.src_comp _ _ hc]
    · rw [k_comp hc']; exact R.mor_comp _ _ hc
  mor_unit p := by
    refine Mor.ext (L.mor_unit p) ?_ (R.mor_unit p)
    change α.app (P.src (P.unit p)) = α.app p
    rw [P.src_unit]
  isScSmoothMap_obj := isScSmoothOn_obj_of h L.isScSmoothMap_obj α.isScSmoothMap_app
    R.isScSmoothMap_obj
  isScSmoothMap_mor := isScSmoothOn_mor_of h L.isScSmoothMap_mor
    (α.isScSmoothMap_app.comp P.isScSmoothMap_src) R.isScSmoothMap_mor

theorem projLeft_comp_pairFunctor (h : Admissible F G) :
    (projLeft F G h).comp (pairFunctor L R α h) = L := EpFunctor.ext rfl rfl

theorem projRight_comp_pairFunctor (h : Admissible F G) :
    (projRight F G h).comp (pairFunctor L R α h) = R := EpFunctor.ext rfl rfl

end Pair

end WeakFibredProduct

/-! ### Maps into `PC.fibred` -/

universe u

namespace PC

open WeakFibredProduct ProperCoveringHom

/-- Equalities of functors between proper coverings that hold on objects and morphisms by
definition. -/
local macro "pc_ext" : tactic =>
  `(tactic| exact ProperCoveringHom.ext (EpFunctor.ext rfl rfl) (EpFunctor.ext rfl rfl))

theorem natEquiv_of_eq {A B : PC.{u}} {Γ₁ Γ₂ Γ₁' Γ₂' : ProperCoveringHom A.F B.F}
    (h : Γ₁'.NaturallyEquivalent Γ₂') (h₁ : Γ₁ = Γ₁') (h₂ : Γ₂ = Γ₂') :
    Γ₁.NaturallyEquivalent Γ₂ := h₁ ▸ h₂ ▸ h

/-- **Two out of three for `E_PC`**: if `G` and `G ∘ L` are equivalences of proper coverings,
so is `L` (the fibre condition is automatic, `ProperCoveringHom.isEquivalence_iff`). -/
theorem IsEquivalence.of_comp_left {A B C : PC.{u}} {G : ProperCoveringHom B.F C.F}
    {L : ProperCoveringHom A.F B.F} (hG : G.IsEquivalence) (hGL : (G.comp L).IsEquivalence) :
    L.IsEquivalence :=
  (isEquivalence_iff A.isProperCovering B.isProperCovering L).2
    ⟨EpFunctor.IsEquivalence.of_comp_left hG.isEquivalence_Ψ hGL.isEquivalence_Ψ,
      EpFunctor.IsEquivalence.of_comp_left hG.isEquivalence_Φ hGL.isEquivalence_Φ⟩

theorem comp_id {A B : PC.{u}} (Γ : ProperCoveringHom A.F B.F) :
    Γ.comp (ProperCoveringHom.id A.F) = Γ :=
  ProperCoveringHom.ext (EpFunctor.ext rfl rfl) (EpFunctor.ext rfl rfl)

theorem id_comp {A B : PC.{u}} (Γ : ProperCoveringHom A.F B.F) :
    (ProperCoveringHom.id B.F).comp Γ = Γ :=
  ProperCoveringHom.ext (EpFunctor.ext rfl rfl) (EpFunctor.ext rfl rfl)

/-- `π_B : A ×_C B → B` is an equivalence (Theorem 11.6.6 (2)). -/
theorem isEquivalence_fibredSnd {A B C : PC.{u}} (Γ : ProperCoveringHom A.F C.F)
    (hΓ : Γ.IsEquivalence) (Λ : ProperCoveringHom B.F C.F) :
    (fibredSnd Γ hΓ Λ).IsEquivalence :=
  (theorem_11_6_6 Γ Λ A.isProperCovering C.isProperCovering B.isProperCovering hΓ).2.1

/-- `τ_P(y, ψ', y'') = ψ'`, `τ_Q(x, φ', x'') = φ'`: `Γ ∘ π_A → Λ ∘ π_B` (Theorem 11.6.6 (3)). -/
def fibredNatTrans {A B C : PC.{u}} (Γ : ProperCoveringHom A.F C.F) (hΓ : Γ.IsEquivalence)
    (Λ : ProperCoveringHom B.F C.F) :
    NatTrans (Γ.comp (fibredFst Γ hΓ Λ)) (Λ.comp (fibredSnd Γ hΓ Λ)) :=
  natTransProj Γ Λ _ _

section Lift

variable {A B C P : PC.{u}} (Γ : ProperCoveringHom A.F C.F) (hΓ : Γ.IsEquivalence)
  (Λ : ProperCoveringHom B.F C.F) {L : ProperCoveringHom P.F A.F} {R : ProperCoveringHom P.F B.F}

/-- **The map `⟨L, R⟩_α : P → A ×_C B` of proper coverings**: `pairFunctor` on the level of `Y`
and on the level of `X`, for a natural transformation `α : Γ ∘ L → Λ ∘ R` (Definition 11.6.5);
the square with `H` (11.18), (11.19) is (11.20) for `α`. -/
def fibredLift (α : NatTrans (Γ.comp L) (Λ.comp R)) : ProperCoveringHom P.F (fibred Γ hΓ Λ).F where
  Ψ := pairFunctor L.Ψ R.Ψ α.τY _
  Φ := pairFunctor L.Φ R.Φ α.τX _
  comm_obj y := Obj.ext (L.comm_obj y) (α.comm y) (R.comm_obj y)
  comm_mor ψ := by
    refine Mor.ext (L.comm_mor ψ) ?_ (R.comm_mor ψ)
    change α.τX.app (P.X.X.src (P.F.mor ψ)) = C.F.mor (α.τY.app (P.Y.X.src ψ))
    rw [P.F.src_mor]
    exact α.comm _

variable {Γ hΓ Λ}

theorem fibredFst_comp_fibredLift (α : NatTrans (Γ.comp L) (Λ.comp R)) :
    (fibredFst Γ hΓ Λ).comp (fibredLift Γ hΓ Λ α) = L :=
  ProperCoveringHom.ext (EpFunctor.ext rfl rfl) (EpFunctor.ext rfl rfl)

theorem fibredSnd_comp_fibredLift (α : NatTrans (Γ.comp L) (Λ.comp R)) :
    (fibredSnd Γ hΓ Λ).comp (fibredLift Γ hΓ Λ α) = R :=
  ProperCoveringHom.ext (EpFunctor.ext rfl rfl) (EpFunctor.ext rfl rfl)

/-- `⟨L, R⟩_α` is an equivalence when `R` is one (two out of three with `π_B`). -/
theorem isEquivalence_fibredLift (α : NatTrans (Γ.comp L) (Λ.comp R)) (hR : R.IsEquivalence) :
    (fibredLift Γ hΓ Λ α).IsEquivalence :=
  IsEquivalence.of_comp_left (isEquivalence_fibredSnd Γ hΓ Λ)
    (by rw [fibredSnd_comp_fibredLift]; exact hR)

end Lift

/-! ### Composition of diagrams -/

namespace Diagram

variable {F F' F'' F''' : PC.{u}}

/-- The identity diagram `F ←1 F →1 F`. -/
def id (F : PC.{u}) : Diagram F F :=
  ⟨F, ProperCoveringHom.id _, IsEquivalence.id, ProperCoveringHom.id _⟩

/-- The diagram `F ←1 F →ε F'` of a functor `ε` (the value of `I`). -/
def ofHom (ε : ProperCoveringHom F.F F'.F) : Diagram F F' :=
  ⟨F, ProperCoveringHom.id _, IsEquivalence.id, ε⟩

/-- **The composite** of `d : F ←Γ A →ε F'` and `e : F' ←Γ' A' →ε' F''` (2021 p. 563):
`F ←(Γ ∘ π_A) A' ×_{F'} A →(ε' ∘ π_{A'}) F''`. -/
def comp (d : Diagram F F') (e : Diagram F' F'') : Diagram F F'' where
  A := fibred e.Γ e.isEquivalence_Γ d.ε
  Γ := d.Γ.comp (fibredSnd e.Γ e.isEquivalence_Γ d.ε)
  isEquivalence_Γ := d.isEquivalence_Γ.comp (isEquivalence_fibredSnd _ _ _)
  ε := e.ε.comp (fibredFst e.Γ e.isEquivalence_Γ d.ε)

/-- Common refinement as a relation on `Diagram F F'`. -/
instance setoid (F F' : PC.{u}) : Setoid (Diagram F F') :=
  ⟨HasCommonRefinement, hasCommonRefinement_equivalence⟩

/-- A common refinement from a single equivalence `M : A → A'` with `Γ' ∘ M ≃ Γ` and
`ε' ∘ M ≃ ε` (take `H = 1`, `H' = M` in Definition 11.6.7). -/
theorem hasCommonRefinement_of_map {d d' : Diagram F F'} (M : ProperCoveringHom d.A.F d'.A.F)
    (hM : M.IsEquivalence) (hΓ : (d'.Γ.comp M).NaturallyEquivalent d.Γ)
    (hε : (d'.ε.comp M).NaturallyEquivalent d.ε) : d.HasCommonRefinement d' :=
  ⟨⟨d.A, ProperCoveringHom.id _, M, IsEquivalence.id, hM,
    by rw [comp_id]; exact naturallyEquivalent_equivalence.symm hΓ,
    by rw [comp_id]; exact naturallyEquivalent_equivalence.symm hε⟩⟩

theorem hasCommonRefinement_of_map_eq {d d' : Diagram F F'} (M : ProperCoveringHom d.A.F d'.A.F)
    (hM : M.IsEquivalence) (hΓ : d'.Γ.comp M = d.Γ) (hε : d'.ε.comp M = d.ε) :
    d.HasCommonRefinement d' :=
  hasCommonRefinement_of_map M hM (by rw [hΓ]; exact naturallyEquivalent_equivalence.refl _)
    (by rw [hε]; exact naturallyEquivalent_equivalence.refl _)

/-- **Well-definedness in the first argument** (2021 p. 563, "independent of the
representatives"): for a common refinement `(A'', H, H')` of `d₁, d₂`, the weak fibred product
`P = A' ×_{F'} A''` maps to both composites by equivalences. -/
theorem hasCommonRefinement_comp_left {d₁ d₂ : Diagram F F'} (h : d₁.HasCommonRefinement d₂)
    (e : Diagram F' F'') : (d₁.comp e).HasCommonRefinement (d₂.comp e) := by
  obtain ⟨c⟩ := h
  obtain ⟨σ⟩ := c.natEquiv_ε
  let P := fibred e.Γ e.isEquivalence_Γ (d₁.ε.comp c.H)
  let ν := fibredNatTrans e.Γ e.isEquivalence_Γ (d₁.ε.comp c.H)
  let M₁ : ProperCoveringHom P.F (d₁.comp e).A.F :=
    fibredLift (L := fibredFst _ _ _) (R := c.H.comp (fibredSnd _ _ _)) e.Γ e.isEquivalence_Γ
      d₁.ε ν
  let M₂ : ProperCoveringHom P.F (d₂.comp e).A.F :=
    fibredLift (L := fibredFst _ _ _) (R := c.H'.comp (fibredSnd _ _ _)) e.Γ e.isEquivalence_Γ
      d₂.ε (ν.trans (σ.whiskerLeft _))
  have hM₁ : M₁.IsEquivalence :=
    isEquivalence_fibredLift _ (c.isEquivalence_H.comp (isEquivalence_fibredSnd _ _ _))
  have hM₂ : M₂.IsEquivalence :=
    isEquivalence_fibredLift _ (c.isEquivalence_H'.comp (isEquivalence_fibredSnd _ _ _))
  refine ⟨⟨P, M₁, M₂, hM₁, hM₂, ?_, ?_⟩⟩
  · exact natEquiv_of_eq (c.natEquiv_Γ.comp_left (fibredSnd _ _ _)) (by pc_ext) (by pc_ext)
  · exact natEquiv_of_eq (naturallyEquivalent_equivalence.refl (e.ε.comp (fibredFst _ _ _)))
      (by pc_ext) (by pc_ext)

/-- **Well-definedness in the second argument**: for a common refinement `(B'', K, K')` of
`e₁, e₂`, the weak fibred product `B'' ×_{F'} A` (along `Γ₁ ∘ K`) maps to both composites. -/
theorem hasCommonRefinement_comp_right (d : Diagram F F') {e₁ e₂ : Diagram F' F''}
    (h : e₁.HasCommonRefinement e₂) : (d.comp e₁).HasCommonRefinement (d.comp e₂) := by
  obtain ⟨c⟩ := h
  obtain ⟨τ⟩ := c.natEquiv_Γ
  have hE : (e₁.Γ.comp c.H).IsEquivalence := e₁.isEquivalence_Γ.comp c.isEquivalence_H
  let P := fibred (e₁.Γ.comp c.H) hE d.ε
  let ν := fibredNatTrans (e₁.Γ.comp c.H) hE d.ε
  let M₁ : ProperCoveringHom P.F (d.comp e₁).A.F :=
    fibredLift (L := c.H.comp (fibredFst _ _ _)) (R := fibredSnd _ _ _) e₁.Γ e₁.isEquivalence_Γ
      d.ε ν
  let M₂ : ProperCoveringHom P.F (d.comp e₂).A.F :=
    fibredLift (L := c.H'.comp (fibredFst _ _ _)) (R := fibredSnd _ _ _) e₂.Γ e₂.isEquivalence_Γ
      d.ε ((τ.whiskerLeft _).symm.trans ν)
  have hM₁ : M₁.IsEquivalence := isEquivalence_fibredLift _ (isEquivalence_fibredSnd _ _ _)
  have hM₂ : M₂.IsEquivalence := isEquivalence_fibredLift _ (isEquivalence_fibredSnd _ _ _)
  refine ⟨⟨P, M₁, M₂, hM₁, hM₂, ?_, ?_⟩⟩
  · exact natEquiv_of_eq (naturallyEquivalent_equivalence.refl (d.Γ.comp (fibredSnd _ _ _)))
      (by pc_ext) (by pc_ext)
  · exact natEquiv_of_eq (c.natEquiv_ε.comp_left (fibredFst _ _ _)) (by pc_ext) (by pc_ext)

/-- **The class of the composite does not depend on the representatives** (2021 p. 563). -/
theorem hasCommonRefinement_comp {d₁ d₂ : Diagram F F'} {e₁ e₂ : Diagram F' F''}
    (hd : d₁.HasCommonRefinement d₂) (he : e₁.HasCommonRefinement e₂) :
    (d₁.comp e₁).HasCommonRefinement (d₂.comp e₂) :=
  hasCommonRefinement_equivalence.trans (hasCommonRefinement_comp_left hd e₁)
    (hasCommonRefinement_comp_right d₂ he)

/-- Associativity up to common refinement: the reassociation
`(A ×_{F'} A') ×_{F''} A'' → A ×_{F'} (A' ×_{F''} A'')` (in the order of `comp`) is built from
two `fibredLift`s. -/
theorem hasCommonRefinement_assoc (d : Diagram F F') (e : Diagram F' F'') (f : Diagram F'' F''') :
    ((d.comp e).comp f).HasCommonRefinement (d.comp (e.comp f)) := by
  let P₁ := ((d.comp e).comp f).A
  let L₀ : ProperCoveringHom P₁.F (fibred f.Γ f.isEquivalence_Γ e.ε).F :=
    fibredLift (L := fibredFst _ _ _)
      (R := (fibredFst e.Γ e.isEquivalence_Γ d.ε).comp (fibredSnd _ _ _)) f.Γ f.isEquivalence_Γ
      e.ε (fibredNatTrans f.Γ f.isEquivalence_Γ (d.comp e).ε)
  let α₀ : NatTrans ((e.comp f).Γ.comp L₀)
      (d.ε.comp ((fibredSnd e.Γ e.isEquivalence_Γ d.ε).comp (fibredSnd _ _ _))) :=
    (fibredNatTrans e.Γ e.isEquivalence_Γ d.ε).whiskerLeft
      (fibredSnd f.Γ f.isEquivalence_Γ (d.comp e).ε)
  let M : ProperCoveringHom P₁.F (d.comp (e.comp f)).A.F :=
    fibredLift (L := L₀) (e.comp f).Γ (e.comp f).isEquivalence_Γ d.ε α₀
  refine hasCommonRefinement_of_map_eq M (isEquivalence_fibredLift _
    ((isEquivalence_fibredSnd _ _ _).comp (isEquivalence_fibredSnd _ _ _))) ?_ ?_
  · pc_ext
  · pc_ext

/-- `d ∘ [F' ←1 F' →ε' F''] ≈ [F ←Γ A →(ε' ∘ ε) F'']`, through `⟨ε, 1⟩ : A → F' ×_{F'} A`. -/
theorem hasCommonRefinement_comp_ofHom (d : Diagram F F') (ε' : ProperCoveringHom F'.F F''.F) :
    (d.comp (ofHom ε')).HasCommonRefinement ⟨d.A, d.Γ, d.isEquivalence_Γ, ε'.comp d.ε⟩ := by
  refine hasCommonRefinement_equivalence.symm ?_
  let M : ProperCoveringHom d.A.F (d.comp (ofHom ε')).A.F :=
    fibredLift (L := d.ε) (R := ProperCoveringHom.id _) (ProperCoveringHom.id _)
      IsEquivalence.id d.ε (NatTrans.refl d.ε)
  refine hasCommonRefinement_of_map_eq M (isEquivalence_fibredLift _ IsEquivalence.id) ?_ ?_
  · pc_ext
  · pc_ext

/-- `[F ←1 F →1 F] ∘ d ≈ d`, through `⟨1, Γ⟩ : A → A ×_F F`. -/
theorem hasCommonRefinement_id_comp (d : Diagram F F') :
    ((id F).comp d).HasCommonRefinement d := by
  refine hasCommonRefinement_equivalence.symm ?_
  let M : ProperCoveringHom d.A.F ((id F).comp d).A.F :=
    fibredLift (L := ProperCoveringHom.id _) (R := d.Γ) d.Γ d.isEquivalence_Γ
      (ProperCoveringHom.id _) (NatTrans.refl d.Γ)
  refine hasCommonRefinement_of_map_eq M (isEquivalence_fibredLift _ d.isEquivalence_Γ) ?_ ?_
  · pc_ext
  · pc_ext

theorem hasCommonRefinement_comp_id (d : Diagram F F') :
    (d.comp (id F')).HasCommonRefinement d := by
  have h := hasCommonRefinement_comp_ofHom d (ProperCoveringHom.id _)
  rwa [id_comp] at h

/-- `[F ←1 F →Γ F'] ∘ [F' ←Γ F →1 F] ≈ [F ←1 F →1 F]`, through the diagonal `F → F ×_{F'} F`. -/
theorem hasCommonRefinement_ofHom_comp_inv {Γ : ProperCoveringHom F.F F'.F}
    (hΓ : Γ.IsEquivalence) :
    ((ofHom Γ).comp ⟨F, Γ, hΓ, ProperCoveringHom.id _⟩).HasCommonRefinement (id F) := by
  refine hasCommonRefinement_equivalence.symm ?_
  let M : ProperCoveringHom F.F ((ofHom Γ).comp ⟨F, Γ, hΓ, ProperCoveringHom.id _⟩).A.F :=
    fibredLift (L := ProperCoveringHom.id _) (R := ProperCoveringHom.id _) Γ hΓ Γ (NatTrans.refl _)
  refine hasCommonRefinement_of_map_eq M (isEquivalence_fibredLift _ IsEquivalence.id) ?_ ?_
  · pc_ext
  · pc_ext

/-- `[F' ←Γ F →Γ F'] ≈ [F' ←1 F' →1 F']`, through `Γ`. -/
theorem hasCommonRefinement_self {Γ : ProperCoveringHom F.F F'.F} (hΓ : Γ.IsEquivalence) :
    (⟨F, Γ, hΓ, Γ⟩ : Diagram F' F').HasCommonRefinement (id F') :=
  hasCommonRefinement_of_map_eq Γ hΓ (id_comp Γ) (id_comp Γ)

end Diagram

end PC

/-! ### The category `PC(E⁻¹)` and the functor `I` -/

/-- **The localization `PC(E⁻¹)`** (2021 p. 561): the objects of `PC`. -/
structure PCLoc : Type (u + 1) where
  /-- The underlying proper covering. -/
  of ::
  toPC : PC.{u}

namespace PCLoc

open PC PC.Diagram

/-- **The category `PC(E⁻¹)`** (2021 pp. 561–563): morphisms are the classes `[d]` of diagrams
under common refinement, composed through weak fibred products; the identities are
`[F ←1 F →1 F]`. -/
instance : Category.{u + 1} PCLoc.{u} where
  Hom F F' := Quotient (Diagram.setoid F.toPC F'.toPC)
  id F := ⟦Diagram.id F.toPC⟧
  comp f g := Quotient.map₂ Diagram.comp (fun _ _ hd _ _ he => hasCommonRefinement_comp hd he) f g
  id_comp f := Quotient.inductionOn f fun d => Quotient.sound (hasCommonRefinement_id_comp d)
  comp_id f := Quotient.inductionOn f fun d => Quotient.sound (hasCommonRefinement_comp_id d)
  assoc f g h := Quotient.inductionOn₃ f g h fun d e f =>
    Quotient.sound (hasCommonRefinement_assoc d e f)

/-- The class `[d]` of a diagram. -/
def homMk {F F' : PC.{u}} (d : Diagram F F') : of F ⟶ of F' := ⟦d⟧

theorem homMk_comp {F F' F'' : PC.{u}} (d : Diagram F F') (e : Diagram F' F'') :
    homMk d ≫ homMk e = homMk (d.comp e) := rfl

theorem homMk_eq_homMk_iff {F F' : PC.{u}} {d d' : Diagram F F'} :
    homMk d = homMk d' ↔ d.HasCommonRefinement d' :=
  Quotient.eq (r := Diagram.setoid F F')

theorem homMk_surjective {F F' : PC.{u}} (f : of F ⟶ of F') : ∃ d : Diagram F F', homMk d = f :=
  Quotient.exists_rep f

theorem id_eq (F : PC.{u}) : 𝟙 (of F) = homMk (Diagram.id F) := rfl

/-- **The functor `I : PC → PC(E⁻¹)`** (2021 p. 563): the identity on objects,
`I(ε) = [F ←1 F →ε F']`. -/
def I : PC.{u} ⥤ PCLoc.{u} where
  obj := of
  map ε := homMk (Diagram.ofHom ε)
  map_id _ := rfl
  map_comp ε₁ ε₂ := by
    change homMk (Diagram.ofHom (ε₂.comp ε₁)) = homMk ((Diagram.ofHom ε₁).comp (Diagram.ofHom ε₂))
    exact (homMk_eq_homMk_iff.2 (hasCommonRefinement_comp_ofHom (Diagram.ofHom ε₁) ε₂)).symm

theorem I_map {F F' : PC.{u}} (ε : F ⟶ F') : I.map ε = homMk (Diagram.ofHom ε) := rfl

/-- `[F ←1 F →Γ F'] ≫ [F' ←Γ F →1 F] = 𝟙`. -/
theorem homMk_ofHom_comp_inv {F F' : PC.{u}} (Γ : ProperCoveringHom F.F F'.F)
    (hΓ : Γ.IsEquivalence) :
    homMk (Diagram.ofHom Γ) ≫ homMk (⟨F, Γ, hΓ, ProperCoveringHom.id _⟩ : Diagram F' F) =
      𝟙 (of F) :=
  homMk_eq_homMk_iff.2 (hasCommonRefinement_ofHom_comp_inv hΓ)

/-- `[F' ←Γ F →1 F] ≫ [F ←1 F →Γ F'] = 𝟙`. -/
theorem homMk_inv_comp_ofHom {F F' : PC.{u}} (Γ : ProperCoveringHom F.F F'.F)
    (hΓ : Γ.IsEquivalence) :
    homMk (⟨F, Γ, hΓ, ProperCoveringHom.id _⟩ : Diagram F' F) ≫ homMk (Diagram.ofHom Γ) =
      𝟙 (of F') :=
  homMk_eq_homMk_iff.2 (hasCommonRefinement_equivalence.trans
    (hasCommonRefinement_comp_ofHom _ Γ) (hasCommonRefinement_self (Γ := Γ) hΓ))

/-- **`I` maps equivalences to isomorphisms** (2021 p. 563): the inverse of `I(Γ)` is
`[F' ←Γ F →1 F]`. -/
theorem isIso_I_map {F F' : PC.{u}} (Γ : F ⟶ F') (hΓ : PC.equivalences Γ) : IsIso (I.map Γ) :=
  ⟨homMk ⟨F, Γ, hΓ, ProperCoveringHom.id _⟩, homMk_ofHom_comp_inv Γ hΓ,
    homMk_inv_comp_ofHom Γ hΓ⟩

theorem inv_I_map {F F' : PC.{u}} (Γ : F ⟶ F') (hΓ : PC.equivalences Γ) :
    haveI := isIso_I_map Γ hΓ
    inv (I.map Γ) = homMk ⟨F, Γ, hΓ, ProperCoveringHom.id _⟩ := by
  have := isIso_I_map Γ hΓ
  exact IsIso.inv_eq_of_hom_inv_id (homMk_ofHom_comp_inv Γ hΓ)

/-- `I` inverts `E_PC`. -/
theorem isInvertedBy_I : PC.equivalences.{u}.IsInvertedBy I := fun _ _ Γ hΓ => isIso_I_map Γ hΓ

theorem homMk_mk_eq {F F' A : PC.{u}} (Γ : ProperCoveringHom A.F F.F) (hΓ : Γ.IsEquivalence)
    (ε : ProperCoveringHom A.F F'.F) :
    homMk (⟨A, Γ, hΓ, ε⟩ : Diagram F F') =
      homMk (⟨A, Γ, hΓ, ProperCoveringHom.id _⟩ : Diagram F A) ≫ homMk (Diagram.ofHom ε) := by
  change homMk _ = homMk (Diagram.comp
    (⟨A, Γ, hΓ, ProperCoveringHom.id _⟩ : Diagram F A) (Diagram.ofHom ε))
  refine homMk_eq_homMk_iff.2 (hasCommonRefinement_equivalence.symm ?_)
  have h := hasCommonRefinement_comp_ofHom
    (⟨A, Γ, hΓ, ProperCoveringHom.id _⟩ : Diagram F A) ε
  rw [PC.comp_id] at h
  exact h

/-- **Every morphism is `I(Γ)⁻¹ ≫ I(ε)`**: `[F ←Γ A →ε F'] = [F ←Γ A →1 A] ≫ I(ε)`. -/
theorem homMk_eq {F F' : PC.{u}} (d : Diagram F F') :
    haveI := isIso_I_map (F := d.A) (F' := F) d.Γ d.isEquivalence_Γ
    homMk d = inv (I.map (X := d.A) (Y := F) d.Γ) ≫ I.map (X := d.A) (Y := F') d.ε :=
  have := isIso_I_map (F := d.A) (F' := F) d.Γ d.isEquivalence_Γ
  (homMk_mk_eq d.Γ d.isEquivalence_Γ d.ε).trans (by rw [inv_I_map]; rfl)

/-- **The inverse of `[F ←Γ A →Γ' F']`** for an equivalence `Γ'` is `[F' ←Γ' A →Γ F]`
(2021 p. 563). -/
theorem homMk_comp_homMk_symm {F F' : PC.{u}} (d : Diagram F F') (hε : d.ε.IsEquivalence) :
    homMk d ≫ homMk (⟨d.A, d.ε, hε, d.Γ⟩ : Diagram F' F) = 𝟙 (of F) := by
  obtain ⟨A, Γ, hΓ, ε⟩ := d
  rw [homMk_mk_eq Γ hΓ ε, homMk_mk_eq ε hε Γ, Category.assoc,
    ← Category.assoc (homMk (Diagram.ofHom ε)),
    homMk_ofHom_comp_inv ε hε, Category.id_comp, homMk_inv_comp_ofHom Γ hΓ]

theorem isIso_homMk {F F' : PC.{u}} (d : Diagram F F') (hε : d.ε.IsEquivalence) :
    IsIso (homMk d) :=
  ⟨homMk (⟨d.A, d.ε, hε, d.Γ⟩ : Diagram F' F), homMk_comp_homMk_symm d hε,
    homMk_comp_homMk_symm (⟨d.A, d.ε, hε, d.Γ⟩ : Diagram F' F) d.isEquivalence_Γ⟩

theorem inv_homMk {F F' : PC.{u}} (d : Diagram F F') (hε : d.ε.IsEquivalence) :
    haveI := isIso_homMk d hε
    inv (homMk d) = homMk (⟨d.A, d.ε, hε, d.Γ⟩ : Diagram F' F) := by
  have := isIso_homMk d hε
  exact IsIso.inv_eq_of_hom_inv_id (homMk_comp_homMk_symm d hε)

end PCLoc

/-! ### Witness -/

namespace PCLoc.Examples

open PC.Examples CoveringEquivalence.Examples EpGroupoid.Examples

/-- **Witness for `PC(E⁻¹)`**: `pairToPointCovering : pair → point` is not an isomorphism of `PC`
(it has no inverse functor), but `I` maps it to an isomorphism of `PC(E⁻¹)`. -/
theorem not_isIso_pairToPoint_isIso_I_map :
    ¬ IsIso (show pair ⟶ point from pairToPointCovering) ∧
      IsIso (I.map (show pair ⟶ point from pairToPointCovering)) := by
  refine ⟨fun h => not_exists_leftInverse_pairToPoint ⟨(inv (show pair ⟶ point from
    pairToPointCovering) : ProperCoveringHom _ _).Ψ, fun x => ?_⟩,
    isIso_I_map _ isEquivalence_pairToPointCovering⟩
  have e := congrArg (fun g : pair ⟶ pair => (g : ProperCoveringHom _ _).Ψ.obj x)
    (IsIso.hom_inv_id (show pair ⟶ point from pairToPointCovering))
  exact e

end PCLoc.Examples

end Polyfold
