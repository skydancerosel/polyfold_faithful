import Polyfold.Chapter16.InheritedOrientationGeneralPosition
import Polyfold.Chapter16.IndexZeroCylinder

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §16.6, p. 739:
**Definition 16.6.5** and **Theorem 16.6.6** (2017: Definition 16.42, Theorem 16.8) **for
Fredholm index `0`**, with **Definition 16.4.4** (pp. 730–731), **Theorem 15.4.1**,
**Definition 15.4.2** (pp. 701–702) and **Definition 15.3.5** (p. 693).  Numbers and pages are
the 2021 text's.

# The inherited orientation of dimension `0` does not depend on the model

## The text, paraphrased

(Definition 16.6.5) An orientation of an sc-Fredholm section `f` is an orientation `o` of a
representative `(W, F)`; through Theorem 12.5.7 it gives the orientations of the other
representatives.  (p. 739) For `λ` with `(f, λ)` in general position, `θ = λ ∘ f` carries the
orientation inherited from `(f, o)` (Theorem 15.4.1, Definition 15.4.2).  For Fredholm index `0`,
`θ` is a finite set of weighted points and the orientation is a sign at each point; the counts
`∫_θ̂ τ`, `∮_θ̂ τ` of a closed `0`-form do not depend on `λ` (Theorem 16.6.6).

## What is formalized

Two orientations `o`, `o'` of `f` on two representatives related by a diagram
`W₁ ←Φ W'' →Ψ W₂` (`OrientationRep.Correspondence`), and regular perturbations of dimension `0`
(`SBLocalization.PointPerturbation`) with the canonical orientation
(`PointPerturbation.IsCanonical`, the signed reading of the frame convention for `0`-dimensional
sheets):

* `PointOrientedPerturbation.ext_suborbifold_t`: equality from the suborbifold and `λ`.
* **`pointOrientedRep_rel_of_diagram`**: the representatives `((Λᵢ ∘ Fᵢ, T̂ᵢ), (Xᵢ, γᵢ))` of two
  canonically oriented point perturbations with `Λ₁ ∘ Φ = Λ₂ ∘ Ψ` are related (Definition
  16.4.4) by the base generalized isomorphism of the diagram; the canonical orientation on the
  middle bundle is the pull-back `ϕ^* T̂₁` (`IsCanonicalFor.pullSection`), in dimension `0`.
  `pointSuborbifold_eq_of_diagram`: the suborbifolds of `Z` are equal.
* `IsPointCanonicalInGeneralPosition o P`: canonical and `(F, Λ)` in general position.
* **`isInheritedFromPoint_of_diagram`**: for one perturbation, with good position of `[D]_* Λ` at
  the boundary points of its support; **`isInheritedFromPoint_of_correspondence_generalPosition`**:
  the same without that hypothesis, for perturbations in general position.
* **`isInheritedFromPoint_generalPosition_iff_of_correspondence`**: `IsInheritedFromPoint o Q ↔
  IsInheritedFromPoint o' Q` for a tame strong polyfold bundle whose polyfold admits sc-smooth
  bump functions, any boundary, tame germ data in the model of `o`, index `0` in both models.
* **`isInheritedFromPoint_iff_of_correspondence`**: the same for `∂Z = ∅` and every canonically
  oriented perturbation (no general position asked).
* **`theorem_16_6_6_index_zero_correspondence`**,
  **`theorem_16_6_6_index_zero_correspondence_generalPosition`**: Theorem 16.6.6 for index `0`
  across two models: `∫_θ̂₀ τ = ∫_θ̂₁ τ` and `∮_θ̂₀ τ = ∮_θ̂₁ τ` for `θ̂₀` inherited from `o` and
  `θ̂₁` inherited from `o'`, with the standing hypotheses (`IndexZeroInput`) in the model of `o`
  and the index in the model of `o'` only.

## Reading

* As in dimension `≥ 1`, the inherited orientation is read in the model that carries `o`; for
  index `0` it is the sign at each point (`frameSign`), so the comparison of the two models is
  the equality of the pulled-back sections `ϕ₁^* T̂₁ = ϕ₂^* T̂₂` of `Ĝr`, here of sums of signed
  empty frames.
* The index `0` in the model of `o'` is kept as a hypothesis (as in dimension `≥ 1`).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

open EPLocalization EpGroupoid SBLocalization PolyfoldClass

namespace StrongPolyfoldBundle

open StrongPolyfoldBundleStructure SEP

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p}

/-- Two oriented perturbed solution sets of dimension `0` with the same suborbifold and the same
`λ` are equal. -/
theorem PointOrientedPerturbation.ext_suborbifold_t {s : ScSection c}
    {P P' : PointOrientedPerturbation s}
    (h₁ : P.toPointSuborbifold = P'.toPointSuborbifold) (h₂ : P.t = P'.t) : P = P' := by
  obtain ⟨a, t, hp⟩ := P
  obtain ⟨a', t', hp'⟩ := P'
  obtain rfl : a = a' := h₁
  obtain rfl : t = t' := h₂
  rfl

/-! ### Two models with corresponding canonical orientations of dimension `0` -/

section Diagram

variable {a₁ a₂ : SectionRep c}

/-- **The representatives of dimension `0` of two models with corresponding canonical orientations
are related** (Definition 16.4.4, §16.6 p. 739, for Fredholm index `0`).  Let
`D : W₁ ←Φ W'' →Ψ W₂` be a diagram of strong bundle equivalences with `Γ₂ ∘ |D| = Γ₁` and
`Φ^* F₁ = Ψ^* F₂`, let the orientations correspond over `W''` (`Φ^* o₁ = Ψ^* o₂`), and let
`P₁`, `P₂` be regular perturbations of dimension `0` with `Λ₁ ∘ Φ = Λ₂ ∘ Ψ`, each with the
canonical orientation of `(Fᵢ, oᵢ)`.  Then `((Λ₁ ∘ F₁, T̂₁), (X₁, γ₁))` and
`((Λ₂ ∘ F₂, T̂₂), (X₂, γ₂))` are related by the base generalized isomorphism `[d]` of `D`.  The
canonical orientation on `W''` is `ϕ₁^* T̂₁`. -/
theorem pointOrientedRep_rel_of_diagram (P₁ : PointPerturbation a₁.S.A a₁.F)
    (P₂ : PointPerturbation a₂.S.A a₂.F)
    (D : SBLocalization.SDiagram a₁.S.A a₂.S.A) (hΨ : SEP.equivalences D.Ψ)
    (hΓ : ⇑a₂.S.Γ ∘ D.orbitMap = ⇑a₁.S.Γ)
    (hF₁ : a₁.S.A.E.IsScFredholmSectionFunctor a₁.F)
    (hF₂ : a₂.S.A.E.IsScFredholmSectionFunctor a₂.F)
    (hF'' : D.B.E.IsScFredholmSectionFunctor (D.hΦ.pullback a₁.F))
    (hpb : D.hΦ.pullback a₁.F = (SBLocalization.sbe hΨ).pullback a₂.F)
    (hsec₁ : a₁.S.A.B.HasScPlusSectionsThrough) (hsec₂ : a₂.S.A.B.HasScPlusSectionsThrough)
    (hsec'' : D.B.B.HasScPlusSectionsThrough)
    (hΛ : ∀ w, P₁.Λ ((SEP.Hom.Φ D.Φ).obj w) = P₂.Λ ((SEP.Hom.Φ D.Ψ).obj w))
    {o₁ : ∀ x (hs : x ∈ a₁.S.A.X.PObj.smoothSet), Orx a₁.F hF₁.2 x hs}
    {o₂ : ∀ x (hs : x ∈ a₂.S.A.X.PObj.smoothSet), Orx a₂.F hF₂.2 x hs}
    (ho : D.hΦ.pullOr hF'' hF₁ rfl hsec'' hsec₁ o₁ =
      (SBLocalization.sbe hΨ).pullOr hF'' hF₂ hpb hsec'' hsec₂ o₂)
    (hC₁ : P₁.IsCanonical hF₁.2 hsec₁ o₁) (hC₂ : P₂.IsCanonical hF₂.2 hsec₂ o₂) :
    OrientedRep.Rel (pointOrientedRep a₁ P₁) (pointOrientedRep a₂ P₂) := by
  set h₁ := D.hΦ with hh₁
  set h₂ := SBLocalization.sbe hΨ with hh₂
  have hC₁' := IsCanonicalFor.smoothPart hC₁
  have hC₂' := IsCanonicalFor.smoothPart hC₂
  have hf : EPLoc.IsGeneralizedIso (EPLoc.homMk D.base) :=
    (SBLocalization.GenSBMap.remark_10_5_3 ⟨D, rfl, hΨ⟩).1
  refine ⟨EPLoc.homMk D.base, hf, (Γ_base (F := D.cls) hΓ).symm, ?_⟩
  refine OrientedBranched.ext' ?_ ?_
  · change EPLoc.pullTheta (EPLoc.homMk D.base) (fun z => ((P₂.Λ (a₂.F z) : ℚ≥0) : ℚ)) =
      fun z => ((P₁.Λ (a₁.F z) : ℚ≥0) : ℚ)
    rw [EPLoc.pullTheta_homMk D.base P₂.isBranched.isFunctorial]
    change (SEP.Hom.ϕ D.Φ).pushforwardTheta ((SEP.Hom.ϕ D.Ψ).pullbackTheta
      (fun z => ((P₂.Λ (a₂.F z) : ℚ≥0) : ℚ))) = _
    rw [← pullbackTheta_eq h₂ hF₂ hpb (Λ := fun w => P₂.Λ ((SEP.Hom.Φ D.Ψ).obj w)) rfl]
    have e1 : (fun z => ((P₂.Λ ((SEP.Hom.Φ D.Ψ).obj (h₁.pullback a₁.F z)) : ℚ≥0) : ℚ)) =
        fun z => ((P₁.Λ ((SEP.Hom.Φ D.Φ).obj (h₁.pullback a₁.F z)) : ℚ≥0) : ℚ) :=
      funext fun z => by rw [hΛ]
    rw [e1, pullbackTheta_eq h₁ hF₁ rfl (Λ := fun w => P₁.Λ ((SEP.Hom.Φ D.Φ).obj w))
      (Λ' := P₁.Λ) rfl]
    exact EpFunctor.pushforwardTheta_pullbackTheta h₁.isEquivalence_base.essSurj
      P₁.isBranched.isFunctorial
  · change EPLoc.pullSection (EPLoc.homMk D.base) (a₂.S.A.X.smoothPart P₂.T) =
      a₁.S.A.X.smoothPart P₁.T
    rw [EPLoc.pullSection_homMk D.base h₂.isEquivalence_base
      P₂.isOrientation.smoothPart.isGrHatSection]
    change (SEP.Hom.ϕ D.Φ).pushSection ((SEP.Hom.ϕ D.Ψ).pullSection
      (a₂.S.A.X.smoothPart P₂.T)) = a₁.S.A.X.smoothPart P₁.T
    have e : (SEP.Hom.ϕ D.Ψ).pullSection (a₂.S.A.X.smoothPart P₂.T) =
        (SEP.Hom.ϕ D.Φ).pullSection (a₁.S.A.X.smoothPart P₁.T) := by
      funext y
      by_cases hys : y ∈ D.B.X.PObj.smoothSet
      · exact (IsCanonicalFor.pullSection_eq_pullSection_of_canonical h₁ h₂ hF₁ hF₂ hF'' rfl
          hpb hsec₁ hsec₂ hsec'' hΛ ho hC₁' hC₂' hys).symm
      · rw [EpFunctor.pullSection_of_not_mem hys, EpFunctor.pullSection_of_not_mem hys]
    rw [e]
    exact EpFunctor.pushSection_pullSection h₁.isEquivalence_base
      ⟨P₁.isOrientation.smoothPart.isGrHatSection, fun _ hx => smoothPart_of_notMem hx⟩

/-- **The suborbifold of dimension `0` of `Z` does not depend on the model of the orientation**
(§16.6, p. 739), under the hypotheses of `pointOrientedRep_rel_of_diagram`. -/
theorem pointSuborbifold_eq_of_diagram (P₁ : PointPerturbation a₁.S.A a₁.F)
    (P₂ : PointPerturbation a₂.S.A a₂.F)
    (D : SBLocalization.SDiagram a₁.S.A a₂.S.A) (hΨ : SEP.equivalences D.Ψ)
    (hΓ : ⇑a₂.S.Γ ∘ D.orbitMap = ⇑a₁.S.Γ)
    (hF₁ : a₁.S.A.E.IsScFredholmSectionFunctor a₁.F)
    (hF₂ : a₂.S.A.E.IsScFredholmSectionFunctor a₂.F)
    (hF'' : D.B.E.IsScFredholmSectionFunctor (D.hΦ.pullback a₁.F))
    (hpb : D.hΦ.pullback a₁.F = (SBLocalization.sbe hΨ).pullback a₂.F)
    (hsec₁ : a₁.S.A.B.HasScPlusSectionsThrough) (hsec₂ : a₂.S.A.B.HasScPlusSectionsThrough)
    (hsec'' : D.B.B.HasScPlusSectionsThrough)
    (hΛ : ∀ w, P₁.Λ ((SEP.Hom.Φ D.Φ).obj w) = P₂.Λ ((SEP.Hom.Φ D.Ψ).obj w))
    {o₁ : ∀ x (hs : x ∈ a₁.S.A.X.PObj.smoothSet), Orx a₁.F hF₁.2 x hs}
    {o₂ : ∀ x (hs : x ∈ a₂.S.A.X.PObj.smoothSet), Orx a₂.F hF₂.2 x hs}
    (ho : D.hΦ.pullOr hF'' hF₁ rfl hsec'' hsec₁ o₁ =
      (SBLocalization.sbe hΨ).pullOr hF'' hF₂ hpb hsec'' hsec₂ o₂)
    (hC₁ : P₁.IsCanonical hF₁.2 hsec₁ o₁) (hC₂ : P₂.IsCanonical hF₂.2 hsec₂ o₂) :
    pointSuborbifold a₁ P₁ = pointSuborbifold a₂ P₂ := by
  have h := Quotient.sound (s := OrientedRep.setoid c.polyfold)
    (pointOrientedRep_rel_of_diagram P₁ P₂ D hΨ hΓ hF₁ hF₂ hF'' hpb hsec₁ hsec₂ hsec'' hΛ ho
      hC₁ hC₂)
  unfold pointSuborbifold
  congr 1

end Diagram

/-! ### The inherited orientation of dimension `0` in the other model -/

variable {s : FredholmSection c}

open OrientationRep

/-- **The perturbations of Theorem 16.6.6 for index `0`** (p. 739): `P` carries the canonical
orientation of `(F, o)` (Theorem 15.4.1, Definition 15.4.2, signed for `0`-dimensional sheets)
and `(F, Λ)` is in general position (Definition 15.3.5). -/
def IsPointCanonicalInGeneralPosition (o : OrientationRep s)
    (P : PointPerturbation o.a.S.A o.a.F) : Prop :=
  P.IsCanonical o.hF.2 o.hsec o.o ∧ IsInGeneralPosition o.a.S.A o.a.F P.Λ

/-- An orientation of dimension `0` inherited along a perturbation in general position is
inherited along a canonical perturbation. -/
theorem IsInheritedFromPoint.of_generalPosition {o : OrientationRep s}
    {Q : PointOrientedPerturbation s.1}
    (h : IsInheritedFromPoint IsPointCanonicalInGeneralPosition o Q) :
    IsInheritedFromPoint (fun o P => P.IsCanonical o.hF.2 o.hsec o.o) o Q := by
  obtain ⟨P, hP, hQ⟩ := h
  exact ⟨P, hP.1, hQ⟩

/-- **The canonically oriented perturbation `[D]_* Λ` of the other model, for one `P`** (§16.6,
p. 739, Fredholm index `0`).  Let `C` relate the models of `o` and `o'`, and let the model of
`o'` satisfy the standing hypotheses of Theorem 15.4.1 (tame, sc-smooth bump functions, tame germ
data, index `0` at smooth points).  For a regular perturbation `P` of dimension `0` of the model of
`o` with the canonical orientation of `(F₁, o)`, such that `[D]_* Λ` is in good position at the
boundary points of `supp([D]_* Λ ∘ F₂)`, the regular perturbation `[D]_* Λ` of the model of `o'`
(`isRegularPerturbation_pushMult`) with the canonical orientation of `(F₂, o')`
(`PointPerturbation.canonical`) is canonical and has the same oriented perturbed solution set
`λ ∘ f` on `Z` (`pointSuborbifold_eq_of_diagram`). -/
theorem isInheritedFromPoint_of_diagram {o o' : OrientationRep s} (C : Correspondence o o')
    (hX : o'.a.S.A.X.PObj.IsTame) (hbump : o'.a.S.A.X.PObj.AdmitsBumpFunctions)
    (hft : o'.a.S.A.B.IsScFredholmSectionTame o'.a.F)
    (hidx : ∀ x ∈ o'.a.S.A.X.PObj.smoothSet, o'.a.S.A.B.IsIndexAt o'.a.F x ((0 : ℕ) : ℤ))
    (P : PointPerturbation o.a.S.A o.a.F) (hP : P.IsCanonical o.hF.2 o.hsec o.o)
    (hgood : ∀ x ∈ o'.a.S.A.X.PObj.boundary, 0 < C.D.pushMult C.hΨ P.Λ (o'.a.F x) →
      SBLocalization.IsGoodPositionAt o'.a.F (C.D.pushMult C.hΨ P.Λ) x) :
    ∃ P' : PointPerturbation o'.a.S.A o'.a.F,
      P'.Λ = C.D.pushMult C.hΨ P.Λ ∧ P'.IsCanonical o'.hF.2 o'.hsec o'.o ∧
      toPointOrientedPerturbation o'.a P' o'.ha = toPointOrientedPerturbation o.a P o.ha := by
  obtain ⟨D, hΨ, hΓ, f'', hF'', hpb₁, hpb₂, hsec'', ho⟩ := C
  subst hpb₁
  have hs : (⟦o.a⟧ : ScSection c) = ⟦o'.a⟧ := o.ha.trans o'.ha.symm
  have hreg := isRegularPerturbation_pushMult hs D hΨ hΓ o.hF o'.hF hpb₂ P.isRegular
  have ho' := o'.isSectionOrientation hX hbump hft
  have hidx' : ∀ x ∈ EpGroupoid.supp
      (fun z => ((D.pushMult hΨ P.Λ (o'.a.F z) : ℚ≥0) : ℚ)),
      o'.a.S.A.B.IsIndexAt o'.a.F x (0 : ℕ) := fun x hx =>
    hidx x (mem_smoothSet_of_pos hft hreg.2.1.1 (by exact_mod_cast hx))
  set P' := PointPerturbation.canonical hX hbump o'.hF hft o'.hsec o'.o o'.isOrientation.2 ho'
    hreg hgood hidx' with hP'
  have hC₂ : P'.IsCanonical o'.hF.2 o'.hsec o'.o :=
    PointPerturbation.isCanonical_canonical hX hbump o'.hF hft o'.hsec o'.o
      o'.isOrientation.2 ho' hreg hgood hidx'
  refine ⟨P', rfl, hC₂, ?_⟩
  have hΛ : ∀ w, P.Λ ((SEP.Hom.Φ D.Φ).obj w) = P'.Λ ((SEP.Hom.Φ D.Ψ).obj w) := fun w =>
    (SBLocalization.pushMult_eq hΨ (P.isRegular.2.1.1.1.pullMult D.Φ) rfl).symm
  have heq := pointSuborbifold_eq_of_diagram P P' D hΨ hΓ o.hF o'.hF hF'' hpb₂ o.hsec o'.hsec
    hsec'' hΛ ho hP hC₂
  exact PointOrientedPerturbation.ext_suborbifold_t heq.symm
    (mk_ofFunctor_pushMult o.a.hS o'.a.hS D hΨ hΓ _ _)

/-- **The perturbed solution set of dimension `0` inherited from `o` along a perturbation in
general position is inherited from `o'`** (§16.6, p. 739, Fredholm index `0`), for one
perturbation, under the standing hypotheses of Theorem 15.4.1 in the model of `o'` and with no
hypothesis on the boundary: good position of `[D]_* Λ` at the boundary points of its support
follows from general position in the model of `o`
(`SDiagram.isGoodPositionAt_pushMult_of_isInGeneralPosition`). -/
theorem isInheritedFromPoint_of_correspondence_generalPosition {o o' : OrientationRep s}
    (C : Correspondence o o') (hX : o'.a.S.A.X.PObj.IsTame)
    (hbump : o'.a.S.A.X.PObj.AdmitsBumpFunctions)
    (hft : o'.a.S.A.B.IsScFredholmSectionTame o'.a.F)
    (hidx : ∀ x ∈ o'.a.S.A.X.PObj.smoothSet, o'.a.S.A.B.IsIndexAt o'.a.F x ((0 : ℕ) : ℤ))
    (P : PointPerturbation o.a.S.A o.a.F) (hP : IsPointCanonicalInGeneralPosition o P) :
    IsInheritedFromPoint IsPointCanonicalInGeneralPosition o'
      (toPointOrientedPerturbation o.a P o.ha) := by
  have hgp₂ := (C.isInGeneralPosition_pushMult_iff P.isRegular.2.1.1).1 hP.2
  have hgood : ∀ x ∈ o'.a.S.A.X.PObj.boundary, 0 < C.D.pushMult C.hΨ P.Λ (o'.a.F x) →
      SBLocalization.IsGoodPositionAt o'.a.F (C.D.pushMult C.hΨ P.Λ) x := fun _ _ hpos =>
    C.D.isGoodPositionAt_pushMult_of_isInGeneralPosition C.hΨ o.hF o'.hF hft
      (C.hpb₁.symm.trans C.hpb₂) P.isRegular.2.1.1 hP.2 hpos
  obtain ⟨P', hΛ', hC₂, heq⟩ := isInheritedFromPoint_of_diagram C hX hbump hft hidx P hP.1 hgood
  exact ⟨P', ⟨hC₂, hΛ' ▸ hgp₂⟩, heq⟩

/-- **2021 §16.6, p. 739, for Fredholm index `0`: the orientation inherited from `(f, o)` along a
perturbation in general position does not depend on the model of `o`.**  Let `c` be a tame
strong polyfold bundle whose polyfold admits sc-smooth bump functions (no hypothesis on `∂Z`),
and `o`, `o'` orientations of `f` on two representatives which correspond over a diagram, with
tame germ data in the model of `o` and index `0` in both models.  Then `θ̂` of dimension `0` has
the orientation inherited from `o` iff it has the one inherited from `o'`. -/
theorem isInheritedFromPoint_generalPosition_iff_of_correspondence (hc : c.IsTame)
    (hbump : c.polyfold.AdmitsBumpFunctions) {o o' : OrientationRep s}
    (C : Correspondence o o') (hft : o.a.S.A.B.IsScFredholmSectionTame o.a.F)
    (hidx : ∀ x ∈ o.a.S.A.X.PObj.smoothSet, o.a.S.A.B.IsIndexAt o.a.F x ((0 : ℕ) : ℤ))
    (hidx' : ∀ x ∈ o'.a.S.A.X.PObj.smoothSet, o'.a.S.A.B.IsIndexAt o'.a.F x ((0 : ℕ) : ℤ))
    (Q : PointOrientedPerturbation s.1) :
    IsInheritedFromPoint IsPointCanonicalInGeneralPosition o Q ↔
      IsInheritedFromPoint IsPointCanonicalInGeneralPosition o' Q := by
  obtain ⟨hX, hb⟩ := o.tame_bump_of_polyfold hc hbump
  obtain ⟨hX', hb'⟩ := o'.tame_bump_of_polyfold hc hbump
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact isInheritedFromPoint_of_correspondence_generalPosition C hX' hb'
      (C.isScFredholmSectionTame hft) hidx' P hP
  · rintro ⟨P, hP, rfl⟩
    exact isInheritedFromPoint_of_correspondence_generalPosition C.symm hX hb hft hidx P hP

/-- **`IsInheritedFromPoint o Q → IsInheritedFromPoint o' Q` for `∂Z = ∅`** (Theorem 16.6.6's
hypotheses, Fredholm index `0`): with sc-smooth partitions of unity on `Z`, tame germ data and
index `0` in the model of `o'`, for every canonically oriented perturbation (the boundary
hypothesis is empty). -/
theorem isInheritedFromPoint_of_correspondence_of_boundary_eq_empty
    (hPU : c.polyfold.AdmitsScPartitionsOfUnity) (hbd : c.polyfold.boundary = ∅)
    {o o' : OrientationRep s} (C : Correspondence o o')
    (hft : o'.a.S.A.B.IsScFredholmSectionTame o'.a.F)
    (hidx : ∀ x ∈ o'.a.S.A.X.PObj.smoothSet, o'.a.S.A.B.IsIndexAt o'.a.F x ((0 : ℕ) : ℤ))
    {Q : PointOrientedPerturbation s.1} :
    IsInheritedFromPoint (fun o P => P.IsCanonical o.hF.2 o.hsec o.o) o Q →
      IsInheritedFromPoint (fun o P => P.IsCanonical o.hF.2 o.hsec o.o) o' Q := by
  rintro ⟨P, hP, rfl⟩
  obtain ⟨hX, hbump, hbd'⟩ := o'.tame_bump_of_boundary_eq_empty hPU hbd
  obtain ⟨P', -, hC₂, heq⟩ := isInheritedFromPoint_of_diagram C hX hbump hft hidx P hP
    fun x hx => absurd hx (hbd' x)
  exact ⟨P', hC₂, heq⟩

/-- **2021 §16.6, p. 739, for Fredholm index `0` and `∂Z = ∅`: the orientation inherited from
`(f, o)` does not depend on the model of `o`.**  Let `Z` admit sc-smooth partitions of unity,
`∂Z = ∅`, and `o`, `o'` orientations of `f` which correspond over a diagram, with tame germ data
in the model of `o` and index `0` in both models.  Then `θ̂` of dimension `0` has the orientation
inherited from `o` iff it has the one inherited from `o'`, for every canonically oriented
perturbation. -/
theorem isInheritedFromPoint_iff_of_correspondence (hPU : c.polyfold.AdmitsScPartitionsOfUnity)
    (hbd : c.polyfold.boundary = ∅) {o o' : OrientationRep s} (C : Correspondence o o')
    (hft : o.a.S.A.B.IsScFredholmSectionTame o.a.F)
    (hidx : ∀ x ∈ o.a.S.A.X.PObj.smoothSet, o.a.S.A.B.IsIndexAt o.a.F x ((0 : ℕ) : ℤ))
    (hidx' : ∀ x ∈ o'.a.S.A.X.PObj.smoothSet, o'.a.S.A.B.IsIndexAt o'.a.F x ((0 : ℕ) : ℤ))
    (Q : PointOrientedPerturbation s.1) :
    IsInheritedFromPoint (fun o P => P.IsCanonical o.hF.2 o.hsec o.o) o Q ↔
      IsInheritedFromPoint (fun o P => P.IsCanonical o.hF.2 o.hsec o.o) o' Q :=
  ⟨isInheritedFromPoint_of_correspondence_of_boundary_eq_empty hPU hbd C
      (C.isScFredholmSectionTame hft) hidx',
    isInheritedFromPoint_of_correspondence_of_boundary_eq_empty hPU hbd C.symm hft hidx⟩

/-! ### Theorem 16.6.6 for index `0` across two models -/

/-- **2021 Theorem 16.6.6, p. 739, for Fredholm index `0`, across two models of the
orientation**: let `Z` admit sc-smooth partitions of unity, `∂Z = ∅`, `f` with compact solution
set, `(n, U)` controlling compactness, and `o`, `o'` orientations of `f` which correspond over a
diagram (`Correspondence`), with the standing hypotheses in the model of `o`
(`IndexZeroInput o`) and index `0` in the model of `o'`.  For admissible `θ̂₀` inherited from `o`
and `θ̂₁` inherited from `o'` (canonical orientations), a closed `0`-form `τ` has
`∫_θ̂₀ τ = ∫_θ̂₁ τ` and `∮_θ̂₀ τ = ∮_θ̂₁ τ`.  `θ̂₁` is inherited from `o` as well
(`isInheritedFromPoint_iff_of_correspondence`), and the cobordism in the model of `o` is
`hasOrientedCobordism_of_indexZeroInput`. -/
theorem theorem_16_6_6_index_zero_correspondence (hPU : c.polyfold.AdmitsScPartitionsOfUnity)
    (n : Y → ℝ) (U : Set Z) (hbd : c.polyfold.boundary = ∅)
    (hcs : s.1.HasCompactSolutionSet) (hn : c.IsAuxNorm n) (hU : IsOpen U)
    (hcc : s.1.ControlsCompactness n U) {o o' : OrientationRep s} (C : Correspondence o o')
    (H : IndexZeroInput o)
    (hidx' : ∀ x ∈ o'.a.S.A.X.PObj.smoothSet, o'.a.S.A.B.IsIndexAt o'.a.F x ((0 : ℕ) : ℤ))
    (Q₀ Q₁ : PointOrientedPerturbation s.1) (h₀ : Q₀.IsAdmissible n U)
    (hQ₀ : IsInheritedFromPoint (fun o P => P.IsCanonical o.hF.2 o.hsec o.o) o Q₀)
    (h₁ : Q₁.IsAdmissible n U)
    (hQ₁ : IsInheritedFromPoint (fun o P => P.IsCanonical o.hF.2 o.hsec o.o) o' Q₁)
    (τ : ScForm c.polyfold 0) (hτ : ScForm.d τ = 0) :
    Q₀.count τ = Q₁.count τ ∧ Q₀.countEff τ = Q₁.countEff τ := by
  have hidx : ∀ x ∈ o.a.S.A.X.PObj.smoothSet, o.a.S.A.B.IsIndexAt o.a.F x ((0 : ℕ) : ℤ) :=
    fun x hx => by exact_mod_cast H.index x hx
  have hQ₁' := (isInheritedFromPoint_iff_of_correspondence hPU hbd C H.tame hidx hidx' Q₁).2 hQ₁
  have key : theorem_16_6_6_index_zero_polyfold_statement s n U
      (fun o'' Q => o'' = o ∧
        IsInheritedFromPoint (fun o P => P.IsCanonical o.hF.2 o.hsec o.o) o'' Q) := by
    refine theorem_16_6_6_index_zero_polyfold_hyp s n U _ ?_
    rintro o'' P₀ P₁ - ⟨rfl, M₀, c₀, rfl⟩ - ⟨-, M₁, c₁, rfl⟩
    obtain ⟨h, he⟩ := hasOrientedCobordism_of_indexZeroInput hPU hbd hcs H M₀ M₁ c₀ c₁
    exact ⟨hasCobordism_pointSuborbifold h, hasCobordismEff_pointSuborbifold he⟩
  exact key hbd hcs hn hU hcc o Q₀ Q₁ h₀ ⟨rfl, hQ₀⟩ h₁ ⟨rfl, hQ₁'⟩ τ hτ

/-- **2021 Theorem 16.6.6 for Fredholm index `0` across two models, for perturbations in general
position** (the perturbations of the text, p. 739): the same conclusion for `θ̂₀`, `θ̂₁` inherited
along canonically oriented perturbations in general position. -/
theorem theorem_16_6_6_index_zero_correspondence_generalPosition
    (hPU : c.polyfold.AdmitsScPartitionsOfUnity) (n : Y → ℝ) (U : Set Z)
    (hbd : c.polyfold.boundary = ∅) (hcs : s.1.HasCompactSolutionSet) (hn : c.IsAuxNorm n)
    (hU : IsOpen U) (hcc : s.1.ControlsCompactness n U) {o o' : OrientationRep s}
    (C : Correspondence o o') (H : IndexZeroInput o)
    (hidx' : ∀ x ∈ o'.a.S.A.X.PObj.smoothSet, o'.a.S.A.B.IsIndexAt o'.a.F x ((0 : ℕ) : ℤ))
    (Q₀ Q₁ : PointOrientedPerturbation s.1) (h₀ : Q₀.IsAdmissible n U)
    (hQ₀ : IsInheritedFromPoint IsPointCanonicalInGeneralPosition o Q₀)
    (h₁ : Q₁.IsAdmissible n U)
    (hQ₁ : IsInheritedFromPoint IsPointCanonicalInGeneralPosition o' Q₁)
    (τ : ScForm c.polyfold 0) (hτ : ScForm.d τ = 0) :
    Q₀.count τ = Q₁.count τ ∧ Q₀.countEff τ = Q₁.countEff τ :=
  theorem_16_6_6_index_zero_correspondence hPU n U hbd hcs hn hU hcc C H hidx' Q₀ Q₁ h₀
    hQ₀.of_generalPosition h₁ hQ₁.of_generalPosition τ hτ

end StrongPolyfoldBundle

end Polyfold
