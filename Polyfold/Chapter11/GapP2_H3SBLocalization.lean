import Polyfold.Chapter11.GapP2_H3SBFibred
import Polyfold.Chapter10.StrongBundleEquivalenceExamples

/-!
# `SBPC[E⁻¹_SBPC]` by diagrams (2021 Remark 11.6.9)

**2021 Remark 11.6.9, p. 566 (2017: Remark 11.27)**: "With the notion of equivalence one can carry
out the associated localization procedure resulting in `SBPC[E⁻¹_SBPC]`.  The details are left to
the reader."  The procedure is the one of `PC` (pp. 561–563): morphisms `F → F'` are classes of
diagrams `F ←Γ A →ε F'` (`Γ` an equivalence) under common refinement (Definition 11.6.7), composed
through weak fibred products (Theorem 11.6.6).  Here it is carried out for `SBPC`, with the strong
bundle Theorem 11.6.6 of `GapP2_H3SBFibred.lean`; the construction is that of
`GapP2_HPCLocalization.lean` for `PC`.

## Main declarations

* `SEP.wfpLift`, `SBPC.fibredLift`: maps into weak fibred products from natural transformations,
  with `fibredLift_fibredFst`, `fibredLift_fibredSnd` and `equivalences_fibredLift`.
* `SBPC.Diagram`, `Diagram.CommonRefinement`, `Diagram.HasCommonRefinement` (Definition 11.6.7 for
  `SBPC`), **`SBPC.proposition_11_6_8`** and `Diagram.hasCommonRefinement_equivalence`.
* `Diagram.comp`, `Diagram.hasCommonRefinement_comp` (the class of the composite does not depend on
  the representatives), associativity and unit laws.
* **`SBPCLoc`** with its `Category` instance (`SBPC[E⁻¹_SBPC]` by diagrams), `SBPCLoc.I`,
  **`SBPCLoc.isIso_I_map`**, `SBPCLoc.homMk_eq` (`[d] = I(Γ)⁻¹ ≫ I(ε)`), `SBPCLoc.isIso_homMk`,
  `SBPCLoc.inv_homMk`.
* `SBPCLoc.fromLoc`: the comparison functor from Mathlib's localization `SBPC.Loc` (H2), with
  `SBPC.Q ⋙ fromLoc = I`.
* Witness: `SBPC.Examples.theorem_11_6_6_ep` (Theorem 11.6.6 for the identity covering of the
  bundle `ℝⁿ × ℝᵏ → ℝⁿ`, all conclusions, with a nonempty weak fibred product).

## Choices

* As in `GapP2_HPCLocalization`, the middle of the composite of `d : F ← A → F'` and
  `e : F' ← A' → F''` is `A' ×_{F'} A` (Theorem 11.6.6 is stated with the equivalence on the left).
* Natural equivalence of morphisms of `SBPC` is `SBPC.NaturallyEquivalent` (strong bundle natural
  transformations on both levels with (11.20) for the bases).
-/

set_option maxSynthPendingDepth 3

open Set Function CategoryTheory

noncomputable section

namespace Polyfold

universe u

/-! ### Maps into the weak fibred product of strong bundles -/

namespace SEP

open EpStrongBundle SBWeakFibredProduct WeakFibredProduct

variable {A A' A'' C : SEP.{u}} {Φ : A ⟶ A'} (hΦ : SEP.equivalences Φ) (Ψ : A'' ⟶ A')
  {L : C ⟶ A} {R : C ⟶ A''}
  (θ : C.E.StrongBundleNatTrans A'.E (Hom.ϕ (L ≫ Φ)) (Hom.ϕ (R ≫ Ψ)) (Hom.Φ (L ≫ Φ))
    (Hom.Φ (R ≫ Ψ)))

/-- **The map `⟨L, R⟩_θ : C → W ×_{W'} W''`**, `c ↦ ((L(P c), τ(P c), R(P c)), R(c))`, covering
`pairFunctor`, for a natural transformation `θ : Φ ∘ L → Ψ ∘ R` of strong bundle functors. -/
def wfpLift : C ⟶ wfpSEP hΦ Ψ :=
  A''.pullbackLiftHom (SBWeakFibredProduct.baseEP hΦ Ψ)
    (projRight (Hom.ϕ Φ) (Hom.ϕ Ψ) (admissible hΦ Ψ))
    (pairFunctor (Hom.ϕ L) (Hom.ϕ R) θ.τ (admissible hΦ Ψ)) R
    (projRight_comp_pairFunctor _ _ _ _).symm

theorem wfpLift_ϕ :
    Hom.ϕ (wfpLift hΦ Ψ θ) = pairFunctor (Hom.ϕ L) (Hom.ϕ R) θ.τ (admissible hΦ Ψ) := rfl

theorem wfpLift_projZ : wfpLift hΦ Ψ θ ≫ SBWeakFibredProduct.projZ hΦ Ψ = R :=
  A''.pullbackLiftHom_comp _ _ _ R _

/-- `ΠX ∘ ⟨L, R⟩_θ = L`: `Φ(L(c)) = μ'(τ(P c)⁻¹, Ψ(R(c)))` by (10.23) for `θ`. -/
theorem wfpLift_projX : wfpLift hΦ Ψ θ ≫ SBWeakFibredProduct.projX hΦ Ψ = L := by
  refine Hom.ext_obj (EpFunctor.ext rfl rfl) (funext fun c => ?_)
  change (Hom.Φ (SBWeakFibredProduct.projX hΦ Ψ)).obj ((Hom.Φ (wfpLift hΦ Ψ θ)).obj c) =
    (Hom.Φ L).obj c
  have hL := Hom.isStrongBundleFunctor L
  have hR := Hom.isStrongBundleFunctor (R ≫ Ψ)
  have hv : A'.P ((Hom.Φ (R ≫ Ψ)).obj c) = A'.X.src (A'.X.inv (θ.τ.app (C.P c))) := by
    rw [A'.X.src_inv, θ.τ.tgt_app, hR.isStrongBundleMap_obj.covers]
  refine coneHom_obj_eq hΦ Ψ (Y := SBWeakFibredProduct.baseEP hΦ Ψ) _ _ _
    (hL.isStrongBundleMap_obj.covers c) ?_
  exact (μ_inv_eq_of_eq_μ (E := A'.E) hv (θ.mem c).out (θ.obj_eq c)).symm

end SEP

namespace SBPC

open WeakFibredProduct SBWeakFibredProduct

variable {S S' S'' P₀ : SBPC.{u}} (Γ : S ⟶ S') (hΓ : equivalences Γ) (Λ : S'' ⟶ S')
  {L : P₀ ⟶ S} {R : P₀ ⟶ S''}

/-- `NatTrans` transported along equalities of morphisms. -/
def NatTrans.ofEq {S₁ S₂ : SBPC.{u}} {f g f' g' : S₁ ⟶ S₂} (θ : NatTrans f' g') (h₁ : f = f')
    (h₂ : g = g') : NatTrans f g :=
  h₁ ▸ h₂ ▸ θ

/-- **The map `⟨L, R⟩_α : P₀ → (A, F) ×_{(A', F')} (A'', F'')` of `SBPC`**: `SEP.wfpLift` on both
levels, for a natural transformation `α : Γ ∘ L → Λ ∘ R`; the cube commutes by (11.20) for `α`
and the top faces of `L`, `R`. -/
def fibredLift (α : NatTrans (L ≫ Γ) (R ≫ Λ)) : P₀ ⟶ fibred Γ hΓ Λ :=
  (⟨SEP.wfpLift hΓ.1 (Hom.a Λ) α.θa, SEP.wfpLift hΓ.2.1 (Hom.b Λ) α.θb, by
    let β := PC.fibredLift (forget.map Γ) hΓ.2.2 (forget.map Λ) (L := forget.map L)
      (R := forget.map R) α.toPC
    refine SEP.Hom.ext_obj (EpFunctor.ext (funext β.comm_obj) (funext β.comm_mor))
      (funext fun c => Subtype.ext (Prod.ext ?_ ?_))
    · change pairObj _ _ _ (P₀.V.P ((SEP.Hom.Φ P₀.A).obj c)) =
        ProperCoveringHom.hObj (forget.map Γ) (forget.map Λ) (pairObj _ _ _ (P₀.W.P c))
      rw [(SEP.Hom.isStrongBundleFunctor P₀.A).isStrongBundleMap_obj.covers]
      exact β.comm_obj _
    · exact comm_total R c⟩ : Hom _ _)

variable {Γ hΓ Λ}

theorem fibredLift_fibredSnd (α : NatTrans (L ≫ Γ) (R ≫ Λ)) :
    fibredLift Γ hΓ Λ α ≫ fibredSnd Γ hΓ Λ = R :=
  hom_ext (SEP.wfpLift_projZ hΓ.1 (Hom.a Λ) α.θa) (SEP.wfpLift_projZ hΓ.2.1 (Hom.b Λ) α.θb)

theorem fibredLift_fibredFst (α : NatTrans (L ≫ Γ) (R ≫ Λ)) :
    fibredLift Γ hΓ Λ α ≫ fibredFst Γ hΓ Λ = L :=
  hom_ext (SEP.wfpLift_projX hΓ.1 (Hom.a Λ) α.θa) (SEP.wfpLift_projX hΓ.2.1 (Hom.b Λ) α.θb)

/-- `⟨L, R⟩_α` is an equivalence when `R` is one (two out of three with `π_{(A'', F'')}`). -/
theorem equivalences_fibredLift (α : NatTrans (L ≫ Γ) (R ≫ Λ)) (hR : equivalences R) :
    equivalences (fibredLift Γ hΓ Λ α) :=
  equivalences_of_comp_left (equivalences_fibredSnd Γ hΓ Λ)
    (by rw [fibredLift_fibredSnd]; exact hR)

/-! ### Diagrams and common refinements -/

/-- A diagram `F ←Γ A →ε F'` of `SBPC`: `Γ ∈ E_SBPC`. -/
structure Diagram (F F' : SBPC.{u}) where
  /-- The middle object. -/
  A : SBPC.{u}
  /-- The equivalence `Γ : A → F`. -/
  Γ : A ⟶ F
  isEquivalence_Γ : equivalences Γ
  /-- The morphism `ε : A → F'`. -/
  ε : A ⟶ F'

/-- **Definition 11.6.7 for `SBPC`** (2021 Remark 11.6.9): a common refinement of `d, d'`:
equivalences `H : A'' → A`, `H' : A'' → A'` with `Γ ∘ H ≃ Γ' ∘ H'` and `ε ∘ H ≃ ε' ∘ H'`. -/
structure Diagram.CommonRefinement {F F' : SBPC.{u}} (d d' : Diagram F F') where
  /-- The middle object. -/
  A'' : SBPC.{u}
  /-- `H : A'' → A`. -/
  H : A'' ⟶ d.A
  /-- `H' : A'' → A'`. -/
  H' : A'' ⟶ d'.A
  isEquivalence_H : equivalences H
  isEquivalence_H' : equivalences H'
  natEquiv_Γ : NaturallyEquivalent (H ≫ d.Γ) (H' ≫ d'.Γ)
  natEquiv_ε : NaturallyEquivalent (H ≫ d.ε) (H' ≫ d'.ε)

/-- `d` and `d'` have a common refinement. -/
def Diagram.HasCommonRefinement {F F' : SBPC.{u}} (d d' : Diagram F F') : Prop :=
  Nonempty (d.CommonRefinement d')

/-- **Proposition 11.6.8 for `SBPC`**: having a common refinement is transitive, through the
weak fibred product of `H'` and `K` (strong bundle Theorem 11.6.6). -/
theorem proposition_11_6_8 {F F' : SBPC.{u}} {d d' d'' : Diagram F F'}
    (h : d.HasCommonRefinement d') (h' : d'.HasCommonRefinement d'') :
    d.HasCommonRefinement d'' := by
  obtain ⟨⟨A₁, H, H', hH, hH', hΓ₁, hε₁⟩⟩ := h
  obtain ⟨⟨B₁, K, K', hK, hK', hΓ₂, hε₂⟩⟩ := h'
  obtain ⟨-, hπr, hnat, -, hπl⟩ := theorem_11_6_6 H' hH' K
  have hE := naturallyEquivalent_equivalence (S := fibred H' hH' K) (S' := F)
  have hE' := naturallyEquivalent_equivalence (S := fibred H' hH' K) (S' := F')
  refine ⟨⟨fibred H' hH' K, fibredFst H' hH' K ≫ H, fibredSnd H' hH' K ≫ K',
    MorphismProperty.comp_mem _ _ _ (hπl hK) hH,
    MorphismProperty.comp_mem _ _ _ hπr hK', ?_, ?_⟩⟩
  · have h₁ := hΓ₁.comp_left (fibredFst H' hH' K)
    have h₂ := hnat.comp_right d'.Γ
    have h₃ := hΓ₂.comp_left (fibredSnd H' hH' K)
    simp only [Category.assoc] at h₁ h₂ h₃ ⊢
    exact hE.trans h₁ (hE.trans h₂ h₃)
  · have h₁ := hε₁.comp_left (fibredFst H' hH' K)
    have h₂ := hnat.comp_right d'.ε
    have h₃ := hε₂.comp_left (fibredSnd H' hH' K)
    simp only [Category.assoc] at h₁ h₂ h₃ ⊢
    exact hE'.trans h₁ (hE'.trans h₂ h₃)

theorem Diagram.hasCommonRefinement_equivalence {F F' : SBPC.{u}} :
    Equivalence (Diagram.HasCommonRefinement (F := F) (F' := F')) where
  refl d := ⟨⟨d.A, 𝟙 _, 𝟙 _, MorphismProperty.id_mem _ _, MorphismProperty.id_mem _ _,
    naturallyEquivalent_equivalence.refl _, naturallyEquivalent_equivalence.refl _⟩⟩
  symm := fun ⟨c⟩ => ⟨⟨c.A'', c.H', c.H, c.isEquivalence_H', c.isEquivalence_H,
    naturallyEquivalent_equivalence.symm c.natEquiv_Γ,
    naturallyEquivalent_equivalence.symm c.natEquiv_ε⟩⟩
  trans := proposition_11_6_8

namespace Diagram

variable {F F' F'' F''' : SBPC.{u}}

/-- The identity diagram `F ←1 F →1 F`. -/
def id (F : SBPC.{u}) : Diagram F F := ⟨F, 𝟙 _, MorphismProperty.id_mem _ _, 𝟙 _⟩

/-- The diagram `F ←1 F →ε F'` of a morphism `ε`. -/
def ofHom (ε : F ⟶ F') : Diagram F F' := ⟨F, 𝟙 _, MorphismProperty.id_mem _ _, ε⟩

/-- **The composite** of `d : F ←Γ A →ε F'` and `e : F' ←Γ' A' →ε' F''`:
`F ← A' ×_{F'} A → F''` with the legs `Γ ∘ π_A` and `ε' ∘ π_{A'}`. -/
def comp (d : Diagram F F') (e : Diagram F' F'') : Diagram F F'' where
  A := fibred e.Γ e.isEquivalence_Γ d.ε
  Γ := fibredSnd e.Γ e.isEquivalence_Γ d.ε ≫ d.Γ
  isEquivalence_Γ := MorphismProperty.comp_mem _ _ _ (equivalences_fibredSnd _ _ _)
    d.isEquivalence_Γ
  ε := fibredFst e.Γ e.isEquivalence_Γ d.ε ≫ e.ε

/-- Common refinement as a relation on `Diagram F F'`. -/
instance setoid (F F' : SBPC.{u}) : Setoid (Diagram F F') :=
  ⟨HasCommonRefinement, hasCommonRefinement_equivalence⟩

/-- A common refinement from a single equivalence `M : A → A'` with `M ≫ Γ' ≃ Γ`,
`M ≫ ε' ≃ ε`. -/
theorem hasCommonRefinement_of_map {d d' : Diagram F F'} (M : d.A ⟶ d'.A) (hM : equivalences M)
    (hΓ : NaturallyEquivalent (M ≫ d'.Γ) d.Γ) (hε : NaturallyEquivalent (M ≫ d'.ε) d.ε) :
    d.HasCommonRefinement d' :=
  ⟨⟨d.A, 𝟙 _, M, MorphismProperty.id_mem _ _, hM,
    by rw [Category.id_comp]; exact naturallyEquivalent_equivalence.symm hΓ,
    by rw [Category.id_comp]; exact naturallyEquivalent_equivalence.symm hε⟩⟩

theorem hasCommonRefinement_of_map_eq {d d' : Diagram F F'} (M : d.A ⟶ d'.A)
    (hM : equivalences M) (hΓ : M ≫ d'.Γ = d.Γ) (hε : M ≫ d'.ε = d.ε) :
    d.HasCommonRefinement d' :=
  hasCommonRefinement_of_map M hM (by rw [hΓ]; exact naturallyEquivalent_equivalence.refl _)
    (by rw [hε]; exact naturallyEquivalent_equivalence.refl _)

/-- **Well-definedness in the first argument**: for a common refinement `(A'', H, H')` of
`d₁, d₂`, the weak fibred product `A' ×_{F'} A''` maps to both composites by equivalences. -/
theorem hasCommonRefinement_comp_left {d₁ d₂ : Diagram F F'} (h : d₁.HasCommonRefinement d₂)
    (e : Diagram F' F'') : (d₁.comp e).HasCommonRefinement (d₂.comp e) := by
  obtain ⟨c⟩ := h
  obtain ⟨σ⟩ := c.natEquiv_ε
  let ν := fibredNatTrans e.Γ e.isEquivalence_Γ (c.H ≫ d₁.ε)
  let M₁ : fibred e.Γ e.isEquivalence_Γ (c.H ≫ d₁.ε) ⟶ fibred e.Γ e.isEquivalence_Γ d₁.ε :=
    fibredLift (L := fibredFst _ _ _) (R := fibredSnd _ _ _ ≫ c.H) e.Γ e.isEquivalence_Γ d₁.ε
      (ν.ofEq rfl (Category.assoc _ _ _))
  let M₂ : fibred e.Γ e.isEquivalence_Γ (c.H ≫ d₁.ε) ⟶ fibred e.Γ e.isEquivalence_Γ d₂.ε :=
    fibredLift (L := fibredFst _ _ _) (R := fibredSnd _ _ _ ≫ c.H') e.Γ e.isEquivalence_Γ d₂.ε
      ((ν.trans (σ.whiskerLeft _)).ofEq rfl (Category.assoc _ _ _))
  have e₁ : M₁ ≫ fibredSnd e.Γ e.isEquivalence_Γ d₁.ε = fibredSnd _ _ _ ≫ c.H :=
    fibredLift_fibredSnd _
  have e₂ : M₂ ≫ fibredSnd e.Γ e.isEquivalence_Γ d₂.ε = fibredSnd _ _ _ ≫ c.H' :=
    fibredLift_fibredSnd _
  have f₁ : M₁ ≫ fibredFst e.Γ e.isEquivalence_Γ d₁.ε = fibredFst _ _ _ :=
    fibredLift_fibredFst _
  have f₂ : M₂ ≫ fibredFst e.Γ e.isEquivalence_Γ d₂.ε = fibredFst _ _ _ :=
    fibredLift_fibredFst _
  refine ⟨⟨_, M₁, M₂,
    equivalences_fibredLift _ (MorphismProperty.comp_mem _ _ _ (equivalences_fibredSnd _ _ _)
      c.isEquivalence_H),
    equivalences_fibredLift _ (MorphismProperty.comp_mem _ _ _ (equivalences_fibredSnd _ _ _)
      c.isEquivalence_H'), ?_, ?_⟩⟩
  · change NaturallyEquivalent (M₁ ≫ fibredSnd _ _ _ ≫ d₁.Γ) (M₂ ≫ fibredSnd _ _ _ ≫ d₂.Γ)
    rw [← Category.assoc, e₁, ← Category.assoc, e₂, Category.assoc, Category.assoc]
    exact c.natEquiv_Γ.comp_left _
  · change NaturallyEquivalent (M₁ ≫ fibredFst _ _ _ ≫ e.ε) (M₂ ≫ fibredFst _ _ _ ≫ e.ε)
    rw [← Category.assoc, f₁, ← Category.assoc, f₂]
    exact naturallyEquivalent_equivalence.refl _

/-- **Well-definedness in the second argument**: for a common refinement `(B'', K, K')` of
`e₁, e₂`, the weak fibred product along `Γ₁ ∘ K` maps to both composites. -/
theorem hasCommonRefinement_comp_right (d : Diagram F F') {e₁ e₂ : Diagram F' F''}
    (h : e₁.HasCommonRefinement e₂) : (d.comp e₁).HasCommonRefinement (d.comp e₂) := by
  obtain ⟨c⟩ := h
  obtain ⟨τ⟩ := c.natEquiv_Γ
  have hE : equivalences (c.H ≫ e₁.Γ) :=
    MorphismProperty.comp_mem _ _ _ c.isEquivalence_H e₁.isEquivalence_Γ
  let ν := fibredNatTrans (c.H ≫ e₁.Γ) hE d.ε
  let M₁ : fibred (c.H ≫ e₁.Γ) hE d.ε ⟶ fibred e₁.Γ e₁.isEquivalence_Γ d.ε :=
    fibredLift (L := fibredFst _ _ _ ≫ c.H) (R := fibredSnd _ _ _) e₁.Γ e₁.isEquivalence_Γ d.ε
      (ν.ofEq (Category.assoc _ _ _) rfl)
  let M₂ : fibred (c.H ≫ e₁.Γ) hE d.ε ⟶ fibred e₂.Γ e₂.isEquivalence_Γ d.ε :=
    fibredLift (L := fibredFst _ _ _ ≫ c.H') (R := fibredSnd _ _ _) e₂.Γ e₂.isEquivalence_Γ d.ε
      (((τ.whiskerLeft _).symm.trans ν).ofEq (Category.assoc _ _ _) rfl)
  have e₁' : M₁ ≫ fibredSnd e₁.Γ e₁.isEquivalence_Γ d.ε = fibredSnd _ _ _ :=
    fibredLift_fibredSnd _
  have e₂' : M₂ ≫ fibredSnd e₂.Γ e₂.isEquivalence_Γ d.ε = fibredSnd _ _ _ :=
    fibredLift_fibredSnd _
  have f₁ : M₁ ≫ fibredFst e₁.Γ e₁.isEquivalence_Γ d.ε = fibredFst _ _ _ ≫ c.H :=
    fibredLift_fibredFst _
  have f₂ : M₂ ≫ fibredFst e₂.Γ e₂.isEquivalence_Γ d.ε = fibredFst _ _ _ ≫ c.H' :=
    fibredLift_fibredFst _
  refine ⟨⟨_, M₁, M₂, equivalences_fibredLift _ (equivalences_fibredSnd _ _ _),
    equivalences_fibredLift _ (equivalences_fibredSnd _ _ _), ?_, ?_⟩⟩
  · change NaturallyEquivalent (M₁ ≫ fibredSnd _ _ _ ≫ d.Γ) (M₂ ≫ fibredSnd _ _ _ ≫ d.Γ)
    rw [← Category.assoc, e₁', ← Category.assoc, e₂']
    exact naturallyEquivalent_equivalence.refl _
  · change NaturallyEquivalent (M₁ ≫ fibredFst _ _ _ ≫ e₁.ε) (M₂ ≫ fibredFst _ _ _ ≫ e₂.ε)
    rw [← Category.assoc, f₁, ← Category.assoc, f₂, Category.assoc, Category.assoc]
    exact c.natEquiv_ε.comp_left _

/-- **The class of the composite does not depend on the representatives**. -/
theorem hasCommonRefinement_comp {d₁ d₂ : Diagram F F'} {e₁ e₂ : Diagram F' F''}
    (hd : d₁.HasCommonRefinement d₂) (he : e₁.HasCommonRefinement e₂) :
    (d₁.comp e₁).HasCommonRefinement (d₂.comp e₂) :=
  hasCommonRefinement_equivalence.trans (hasCommonRefinement_comp_left hd e₁)
    (hasCommonRefinement_comp_right d₂ he)

/-- Associativity up to common refinement, through two `fibredLift`s. -/
theorem hasCommonRefinement_assoc (d : Diagram F F') (e : Diagram F' F'') (f : Diagram F'' F''') :
    ((d.comp e).comp f).HasCommonRefinement (d.comp (e.comp f)) := by
  let L₀ : fibred f.Γ f.isEquivalence_Γ (d.comp e).ε ⟶ fibred f.Γ f.isEquivalence_Γ e.ε :=
    fibredLift (L := fibredFst _ _ _) (R := fibredSnd _ _ _ ≫ fibredFst e.Γ e.isEquivalence_Γ d.ε)
      f.Γ f.isEquivalence_Γ e.ε
      ((fibredNatTrans f.Γ f.isEquivalence_Γ (d.comp e).ε).ofEq rfl (Category.assoc _ _ _))
  have hL₀ : L₀ ≫ fibredSnd f.Γ f.isEquivalence_Γ e.ε =
      fibredSnd _ _ _ ≫ fibredFst e.Γ e.isEquivalence_Γ d.ε := fibredLift_fibredSnd _
  have hL₀' : L₀ ≫ fibredFst f.Γ f.isEquivalence_Γ e.ε = fibredFst _ _ _ :=
    fibredLift_fibredFst _
  let α₀ : NatTrans (L₀ ≫ (e.comp f).Γ)
      ((fibredSnd _ _ _ ≫ fibredSnd e.Γ e.isEquivalence_Γ d.ε) ≫ d.ε) :=
    ((fibredNatTrans e.Γ e.isEquivalence_Γ d.ε).whiskerLeft
      (fibredSnd f.Γ f.isEquivalence_Γ (d.comp e).ε)).ofEq
      (by
        change L₀ ≫ fibredSnd _ _ _ ≫ e.Γ = _
        rw [← Category.assoc, hL₀]; exact Category.assoc _ _ _)
      (Category.assoc _ _ _)
  let M : fibred f.Γ f.isEquivalence_Γ (d.comp e).ε ⟶
      fibred (e.comp f).Γ (e.comp f).isEquivalence_Γ d.ε :=
    fibredLift (L := L₀) (e.comp f).Γ (e.comp f).isEquivalence_Γ d.ε α₀
  have hM : M ≫ fibredSnd (e.comp f).Γ (e.comp f).isEquivalence_Γ d.ε =
      fibredSnd _ _ _ ≫ fibredSnd e.Γ e.isEquivalence_Γ d.ε := fibredLift_fibredSnd _
  have hM' : M ≫ fibredFst (e.comp f).Γ (e.comp f).isEquivalence_Γ d.ε = L₀ :=
    fibredLift_fibredFst _
  refine hasCommonRefinement_of_map_eq M (equivalences_fibredLift _
    (MorphismProperty.comp_mem _ _ _ (equivalences_fibredSnd _ _ _)
      (equivalences_fibredSnd _ _ _))) ?_ ?_
  · change M ≫ fibredSnd _ _ _ ≫ d.Γ = fibredSnd _ _ _ ≫ fibredSnd _ _ _ ≫ d.Γ
    rw [← Category.assoc, hM]; exact Category.assoc _ _ _
  · change M ≫ fibredFst _ _ _ ≫ fibredFst _ _ _ ≫ f.ε = fibredFst _ _ _ ≫ f.ε
    rw [← Category.assoc, hM']
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ f.ε) hL₀')

/-- `d ∘ [F' ←1 F' →ε' F''] ≈ [F ←Γ A →(ε' ∘ ε) F'']`, through `⟨ε, 1⟩ : A → F' ×_{F'} A`. -/
theorem hasCommonRefinement_comp_ofHom (d : Diagram F F') (ε' : F' ⟶ F'') :
    (d.comp (ofHom ε')).HasCommonRefinement ⟨d.A, d.Γ, d.isEquivalence_Γ, d.ε ≫ ε'⟩ := by
  refine hasCommonRefinement_equivalence.symm ?_
  let M : d.A ⟶ fibred (𝟙 F') (MorphismProperty.id_mem _ _) d.ε :=
    fibredLift (L := d.ε) (R := 𝟙 _) (𝟙 _) (MorphismProperty.id_mem _ _) d.ε
      ((NatTrans.refl d.ε).ofEq (Category.comp_id _) (Category.id_comp _))
  have h₁ : M ≫ fibredSnd (𝟙 _) (MorphismProperty.id_mem _ _) d.ε = 𝟙 _ :=
    fibredLift_fibredSnd _
  have h₂ : M ≫ fibredFst (𝟙 _) (MorphismProperty.id_mem _ _) d.ε = d.ε :=
    fibredLift_fibredFst _
  refine hasCommonRefinement_of_map_eq M (equivalences_fibredLift _
    (MorphismProperty.id_mem _ _)) ?_ ?_
  · change M ≫ fibredSnd _ _ _ ≫ d.Γ = d.Γ
    rw [← Category.assoc, h₁, Category.id_comp]
  · change M ≫ fibredFst _ _ _ ≫ ε' = d.ε ≫ ε'
    rw [← Category.assoc, h₂]

/-- `[F ←1 F →1 F] ∘ d ≈ d`, through `⟨1, Γ⟩ : A → A ×_F F`. -/
theorem hasCommonRefinement_id_comp (d : Diagram F F') :
    ((id F).comp d).HasCommonRefinement d := by
  refine hasCommonRefinement_equivalence.symm ?_
  let M : d.A ⟶ fibred d.Γ d.isEquivalence_Γ (𝟙 F) :=
    fibredLift (L := 𝟙 _) (R := d.Γ) d.Γ d.isEquivalence_Γ (𝟙 _)
      ((NatTrans.refl d.Γ).ofEq (Category.id_comp _) (Category.comp_id _))
  have h₁ : M ≫ fibredSnd d.Γ d.isEquivalence_Γ (𝟙 _) = d.Γ := fibredLift_fibredSnd _
  have h₂ : M ≫ fibredFst d.Γ d.isEquivalence_Γ (𝟙 _) = 𝟙 _ := fibredLift_fibredFst _
  refine hasCommonRefinement_of_map_eq M (equivalences_fibredLift _ d.isEquivalence_Γ) ?_ ?_
  · change M ≫ fibredSnd _ _ _ ≫ 𝟙 _ = d.Γ
    rw [Category.comp_id, h₁]
  · change M ≫ fibredFst _ _ _ ≫ d.ε = d.ε
    rw [← Category.assoc, h₂, Category.id_comp]

theorem hasCommonRefinement_comp_id (d : Diagram F F') :
    (d.comp (id F')).HasCommonRefinement d := by
  have h := hasCommonRefinement_comp_ofHom d (𝟙 _)
  rwa [Category.comp_id] at h

/-- `[F ←1 F →Γ F'] ∘ [F' ←Γ F →1 F] ≈ [F ←1 F →1 F]`, through the diagonal `F → F ×_{F'} F`. -/
theorem hasCommonRefinement_ofHom_comp_inv {Γ : F ⟶ F'} (hΓ : equivalences Γ) :
    ((ofHom Γ).comp ⟨F, Γ, hΓ, 𝟙 _⟩).HasCommonRefinement (id F) := by
  refine hasCommonRefinement_equivalence.symm ?_
  let M : F ⟶ fibred Γ hΓ Γ :=
    fibredLift (L := 𝟙 _) (R := 𝟙 _) Γ hΓ Γ (NatTrans.refl _)
  have h₁ : M ≫ fibredSnd Γ hΓ Γ = 𝟙 _ := fibredLift_fibredSnd _
  have h₂ : M ≫ fibredFst Γ hΓ Γ = 𝟙 _ := fibredLift_fibredFst _
  refine hasCommonRefinement_of_map_eq M (equivalences_fibredLift _
    (MorphismProperty.id_mem _ _)) ?_ ?_
  · change M ≫ fibredSnd _ _ _ ≫ 𝟙 _ = 𝟙 _
    rw [Category.comp_id, h₁]
  · change M ≫ fibredFst _ _ _ ≫ 𝟙 _ = 𝟙 _
    rw [Category.comp_id, h₂]

/-- `[F' ←Γ F →Γ F'] ≈ [F' ←1 F' →1 F']`, through `Γ`. -/
theorem hasCommonRefinement_self {Γ : F ⟶ F'} (hΓ : equivalences Γ) :
    (⟨F, Γ, hΓ, Γ⟩ : Diagram F' F').HasCommonRefinement (id F') :=
  hasCommonRefinement_of_map_eq Γ hΓ (Category.comp_id Γ) (Category.comp_id Γ)

end Diagram

end SBPC

/-! ### The category `SBPC[E⁻¹_SBPC]` by diagrams and the functor `I` -/

/-- **The localization `SBPC[E⁻¹_SBPC]` by diagrams** (2021 Remark 11.6.9): the objects of
`SBPC`. -/
structure SBPCLoc : Type (u + 1) where
  /-- The underlying proper strong bundle covering. -/
  of ::
  toSBPC : SBPC.{u}

namespace SBPCLoc

open SBPC SBPC.Diagram

/-- **The category `SBPC[E⁻¹_SBPC]`**: morphisms are the classes `[d]` of diagrams under common
refinement, composed through the weak fibred products of the strong bundle Theorem 11.6.6. -/
instance : Category.{u + 1} SBPCLoc.{u} where
  Hom F F' := Quotient (Diagram.setoid F.toSBPC F'.toSBPC)
  id F := ⟦Diagram.id F.toSBPC⟧
  comp f g := Quotient.map₂ Diagram.comp (fun _ _ hd _ _ he => hasCommonRefinement_comp hd he) f g
  id_comp f := Quotient.inductionOn f fun d => Quotient.sound (hasCommonRefinement_id_comp d)
  comp_id f := Quotient.inductionOn f fun d => Quotient.sound (hasCommonRefinement_comp_id d)
  assoc f g h := Quotient.inductionOn₃ f g h fun d e f =>
    Quotient.sound (hasCommonRefinement_assoc d e f)

/-- The class `[d]` of a diagram. -/
def homMk {F F' : SBPC.{u}} (d : Diagram F F') : of F ⟶ of F' := ⟦d⟧

theorem homMk_comp {F F' F'' : SBPC.{u}} (d : Diagram F F') (e : Diagram F' F'') :
    homMk d ≫ homMk e = homMk (d.comp e) := rfl

theorem homMk_eq_homMk_iff {F F' : SBPC.{u}} {d d' : Diagram F F'} :
    homMk d = homMk d' ↔ d.HasCommonRefinement d' :=
  Quotient.eq (r := Diagram.setoid F F')

theorem homMk_surjective {F F' : SBPC.{u}} (f : of F ⟶ of F') :
    ∃ d : Diagram F F', homMk d = f :=
  Quotient.exists_rep f

/-- **The functor `I : SBPC → SBPC[E⁻¹_SBPC]`**: the identity on objects,
`I(ε) = [F ←1 F →ε F']`. -/
def I : SBPC.{u} ⥤ SBPCLoc.{u} where
  obj := of
  map ε := homMk (Diagram.ofHom ε)
  map_id _ := rfl
  map_comp ε₁ ε₂ := by
    change homMk (Diagram.ofHom (ε₁ ≫ ε₂)) = homMk ((Diagram.ofHom ε₁).comp (Diagram.ofHom ε₂))
    exact (homMk_eq_homMk_iff.2 (hasCommonRefinement_comp_ofHom (Diagram.ofHom ε₁) ε₂)).symm

theorem I_map {F F' : SBPC.{u}} (ε : F ⟶ F') : I.map ε = homMk (Diagram.ofHom ε) := rfl

theorem homMk_ofHom_comp_inv {F F' : SBPC.{u}} (Γ : F ⟶ F') (hΓ : equivalences Γ) :
    homMk (Diagram.ofHom Γ) ≫ homMk (⟨F, Γ, hΓ, 𝟙 _⟩ : Diagram F' F) = 𝟙 (of F) :=
  homMk_eq_homMk_iff.2 (hasCommonRefinement_ofHom_comp_inv hΓ)

theorem homMk_inv_comp_ofHom {F F' : SBPC.{u}} (Γ : F ⟶ F') (hΓ : equivalences Γ) :
    homMk (⟨F, Γ, hΓ, 𝟙 _⟩ : Diagram F' F) ≫ homMk (Diagram.ofHom Γ) = 𝟙 (of F') := by
  refine homMk_eq_homMk_iff.2 (hasCommonRefinement_equivalence.trans
    (hasCommonRefinement_comp_ofHom _ Γ) ?_)
  have h := hasCommonRefinement_self (Γ := Γ) hΓ
  rwa [Category.id_comp]

/-- **`I` maps `E_SBPC` to isomorphisms**: the inverse of `I(Γ)` is `[F' ←Γ F →1 F]`. -/
theorem isIso_I_map {F F' : SBPC.{u}} (Γ : F ⟶ F') (hΓ : equivalences Γ) : IsIso (I.map Γ) :=
  ⟨homMk ⟨F, Γ, hΓ, 𝟙 _⟩, homMk_ofHom_comp_inv Γ hΓ, homMk_inv_comp_ofHom Γ hΓ⟩

theorem inv_I_map {F F' : SBPC.{u}} (Γ : F ⟶ F') (hΓ : equivalences Γ) :
    haveI := isIso_I_map Γ hΓ
    inv (I.map Γ) = homMk ⟨F, Γ, hΓ, 𝟙 _⟩ := by
  have := isIso_I_map Γ hΓ
  exact IsIso.inv_eq_of_hom_inv_id (homMk_ofHom_comp_inv Γ hΓ)

/-- `I` inverts `E_SBPC`. -/
theorem isInvertedBy_I : SBPC.equivalences.{u}.IsInvertedBy I := fun _ _ Γ hΓ => isIso_I_map Γ hΓ

theorem homMk_mk_eq {F F' A : SBPC.{u}} (Γ : A ⟶ F) (hΓ : equivalences Γ) (ε : A ⟶ F') :
    homMk (⟨A, Γ, hΓ, ε⟩ : Diagram F F') =
      homMk (⟨A, Γ, hΓ, 𝟙 _⟩ : Diagram F A) ≫ homMk (Diagram.ofHom ε) := by
  change homMk _ = homMk (Diagram.comp (⟨A, Γ, hΓ, 𝟙 _⟩ : Diagram F A) (Diagram.ofHom ε))
  refine homMk_eq_homMk_iff.2 (hasCommonRefinement_equivalence.symm ?_)
  have h := hasCommonRefinement_comp_ofHom (⟨A, Γ, hΓ, 𝟙 _⟩ : Diagram F A) ε
  rw [Category.id_comp] at h
  exact h

/-- **Every morphism is `I(Γ)⁻¹ ≫ I(ε)`**. -/
theorem homMk_eq {F F' : SBPC.{u}} (d : Diagram F F') :
    haveI := isIso_I_map (F := d.A) (F' := F) d.Γ d.isEquivalence_Γ
    homMk d = inv (I.map (X := d.A) (Y := F) d.Γ) ≫ I.map (X := d.A) (Y := F') d.ε :=
  have := isIso_I_map (F := d.A) (F' := F) d.Γ d.isEquivalence_Γ
  (homMk_mk_eq d.Γ d.isEquivalence_Γ d.ε).trans (by rw [inv_I_map]; rfl)

/-- **The inverse of `[F ←Γ A →Γ' F']`** for an equivalence `Γ'` is `[F' ←Γ' A →Γ F]`. -/
theorem homMk_comp_homMk_symm {F F' : SBPC.{u}} (d : Diagram F F') (hε : equivalences d.ε) :
    homMk d ≫ homMk (⟨d.A, d.ε, hε, d.Γ⟩ : Diagram F' F) = 𝟙 (of F) := by
  obtain ⟨A, Γ, hΓ, ε⟩ := d
  rw [homMk_mk_eq Γ hΓ ε, homMk_mk_eq ε hε Γ, Category.assoc,
    ← Category.assoc (homMk (Diagram.ofHom ε)),
    homMk_ofHom_comp_inv ε hε, Category.id_comp, homMk_inv_comp_ofHom Γ hΓ]

theorem isIso_homMk {F F' : SBPC.{u}} (d : Diagram F F') (hε : equivalences d.ε) :
    IsIso (homMk d) :=
  ⟨homMk (⟨d.A, d.ε, hε, d.Γ⟩ : Diagram F' F), homMk_comp_homMk_symm d hε,
    homMk_comp_homMk_symm (⟨d.A, d.ε, hε, d.Γ⟩ : Diagram F' F) d.isEquivalence_Γ⟩

theorem inv_homMk {F F' : SBPC.{u}} (d : Diagram F F') (hε : equivalences d.ε) :
    haveI := isIso_homMk d hε
    inv (homMk d) = homMk (⟨d.A, d.ε, hε, d.Γ⟩ : Diagram F' F) := by
  have := isIso_homMk d hε
  exact IsIso.inv_eq_of_hom_inv_id (homMk_comp_homMk_symm d hε)

/-- **The comparison with the universal localization**: H2's `SBPC.Loc` (Mathlib's construction)
maps to `SBPCLoc` by the universal property, compatibly with `Q` and `I`. -/
def fromLoc : SBPC.Loc.{u} ⥤ SBPCLoc.{u} := SBPC.lift I isInvertedBy_I

theorem fromLoc_fac : SBPC.Q ⋙ fromLoc.{u} = I := SBPC.fac I isInvertedBy_I

end SBPCLoc

/-! ### Witness -/

namespace SBPC.Examples

open StrongBundleEquivalenceExamples SBWeakFibredProduct

/-- **Witness for the strong bundle Theorem 11.6.6**: for the identity covering `(1, 1)` of the
bundle `ℝⁿ × ℝᵏ → ℝⁿ` and the identity cube (in `E_SBPC`), all conclusions hold, and the weak
fibred product `W ×_W W` is nonempty. -/
theorem theorem_11_6_6_ep (n k : ℕ) :
    Nonempty (fibred (𝟙 (ofSEP (epSEP n k))) (equivalences_id _) (𝟙 _)).W.W ∧
    (fibred (𝟙 (ofSEP (epSEP n k))) (equivalences_id _) (𝟙 _)).W.E.IsProperStrongBundleCovering2021
      (fibred (𝟙 (ofSEP (epSEP n k))) (equivalences_id _) (𝟙 _)).V.E
      (fibredH (𝟙 (ofSEP (epSEP n k))) (equivalences_id _) (𝟙 _))
      (SEP.Hom.Φ (fibred (𝟙 (ofSEP (epSEP n k))) (equivalences_id _) (𝟙 _)).A).obj ∧
    equivalences (fibredSnd (𝟙 (ofSEP (epSEP n k))) (equivalences_id _) (𝟙 _)) ∧
    equivalences (fibredFst (𝟙 (ofSEP (epSEP n k))) (equivalences_id _) (𝟙 _)) ∧
    NaturallyEquivalent
      (fibredFst (𝟙 (ofSEP (epSEP n k))) (equivalences_id _) (𝟙 _) ≫ 𝟙 _)
      (fibredSnd (𝟙 (ofSEP (epSEP n k))) (equivalences_id _) (𝟙 _) ≫ 𝟙 _) := by
  obtain ⟨w, -⟩ := (epSEP n k).B.surjective ((0 : Fin n → ℝ) : (epSEP n k).Obj)
  obtain ⟨h1, h2, h3, -, h5⟩ := theorem_11_6_6 (𝟙 (ofSEP (epSEP n k))) (equivalences_id _) (𝟙 _)
  exact ⟨nonempty_wfpSEP _ _ w, h1, h2, h5 (equivalences_id _), h3⟩

end SBPC.Examples

end Polyfold

end
