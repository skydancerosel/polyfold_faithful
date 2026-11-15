import Polyfold.Chapter16.CorrespondenceMiddleCanonical
import Polyfold.Chapter16.CanonicalModelPullback
import Polyfold.Chapter15.GeneralPositionLocal

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §16.6, p. 739:
**Definition 16.6.5** and **Theorem 16.6.6** (2017: Definition 16.42, Theorem 16.8), with
**Definition 15.3.5** (p. 693), **Definition 15.2.4** (p. 689), **Theorem 15.4.1**,
**Definition 15.4.2** (pp. 701–702), **Theorem 15.4.3 (3)** (p. 703) and **Theorem 10.4.5**
(p. 500).

# The inherited orientation of a perturbation in general position does not depend on the model

## The text, paraphrased

(Definition 16.6.5) An orientation of an sc-Fredholm section `f` of a tame strong polyfold
bundle is an orientation `o` of a representative `(W, F)`; through Theorem 12.5.7 it gives the
orientations of the other representatives.  (p. 739) For an sc⁺-multisection `λ` such that
`(f, λ)` is in general position, `θ = λ ∘ f` carries the orientation inherited from `(f, o)`
(Theorem 15.4.1, Definition 15.4.2).  (Theorem 16.6.6) For `∂Z = ∅` and `λ` controlled by
`(n, U)` with `(f, λ)` in general position, `∫_θ̂ τ` and `∮_θ̂ τ` of a closed `τ` do not depend
on `λ`.

## What is formalized

* `SDiagram.pushforward_eq_of_pullback_eq`: for a diagram `W ←Φ W'' →Ψ W'` with
  `Φ^* F = Ψ^* F'`, `[D]_* F = Ψ_* Φ^* F = F'`.
* `SDiagram.isInGeneralPosition_pushMult_iff_of_pullback_eq`: `(F, Λ)` is in general position
  (Definition 15.3.5) iff `(F', [D]_* Λ)` is.
* **`SDiagram.isGoodPositionAt_pushMult_of_isInGeneralPosition`**: if `(F, Λ)` is in general
  position, then `(F', [D]_* Λ)` is in good position (Definition 15.2.4) at every point of its
  support, in particular at the boundary points (the hypothesis of Theorem 15.4.3 (3)).
* `Correspondence.ofDiagram`: a correspondence from a diagram, with `F'' = Φ^* F₁` sc-Fredholm by
  Theorem 10.4.5 (`theorem_10_4_5_fred`); `Correspondence.isScFredholmSectionTame`: tame germ data
  of `F₂` from those of `F₁` (`F₂ = Ψ_* Φ^* F₁`, Theorem 10.4.5 and Definition 3.6.5).
* `IsCanonicalInGeneralPosition o P`: `P` carries the canonical orientation of `(F, o)` and
  `(F, Λ)` is in general position (the perturbations of Theorem 16.6.6).
* **`isInheritedFrom_of_correspondence_generalPosition`**: for every such `P` in the model of `o`
  and the standing hypotheses of Theorem 15.4.1 in the model of `o'`, the perturbation `[D]_* Λ`
  of the model of `o'`, with its canonical orientation, is again canonical and in general position
  and has the same oriented perturbed solution set.  No hypothesis on the middle bundle and none
  on the boundary.
* **`isInheritedFrom_generalPosition_iff_of_correspondence`**: for a tame strong polyfold bundle
  whose polyfold admits sc-smooth bump functions, any boundary, tame germ data in the model of `o`
  and index `m + 1` in both models: `IsInheritedFrom o Q ↔ IsInheritedFrom o' Q` for perturbations
  in general position.
* **`theorem_16_6_6_correspondence`**, **`theorem_16_6_6_correspondence_generalPosition`**:
  Theorem 16.6.6 across two models (`∂Z = ∅`): `∫` and `∮` agree for `θ̂₀` inherited from `o` and
  `θ̂₁` inherited from `o'`, with the standing hypotheses in the model of `o` and the index in the
  model of `o'` only.

## Reading

* Good position at the boundary points is not asked of the model of `o'`: it follows from
  general position in the model of `o`, the hypothesis of Theorem 16.6.6.  General position
  is transported along the diagram (Definition 15.3.5 is invariant), and general position at a
  point gives good position there (the last sentence of Theorem 15.2.5).
* For the orientation inherited along a canonical perturbation without general position the
  boundary hypothesis is not removed here: good position (Definition 15.2.4) is read in tame
  charts of the restricted bundles `W|O`, and its transport along a strong bundle equivalence is
  not formalized.
* The index `m + 1` in the model of `o'` is kept as a hypothesis.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

open EPLocalization EpGroupoid SBLocalization PolyfoldClass

namespace SBLocalization

namespace SDiagram

variable {A A' : SEP.{u}}

/-- **`[D]_* F = F'` when `Φ^* F = Ψ^* F'`** (Theorem 10.4.5: `Ψ_*` and `Ψ^*` are mutually
inverse on section functors). -/
theorem pushforward_eq_of_pullback_eq (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ)
    {F : A.Obj → A.W} {F' : A'.Obj → A'.W} (hF' : A'.E.IsScFredholmSectionFunctor F')
    (hpb : D.hΦ.pullback F = (sbe hΨ).pullback F') : D.pushforward hΨ F = F' := by
  change (sbe hΨ).pushforward (D.hΦ.pullback F) = F'
  rw [hpb]
  exact (sbe hΨ).pushforward_pullback hF'.1.1.1 hF'.1.2

/-- **General position along a diagram with `Φ^* F = Ψ^* F'`** (Definition 15.3.5):
`(F, Λ)` is in general position iff `(F', [D]_* Λ)` is. -/
theorem isInGeneralPosition_pushMult_iff_of_pullback_eq (D : SDiagram A A')
    (hΨ : SEP.equivalences D.Ψ) {F : A.Obj → A.W} {F' : A'.Obj → A'.W}
    (hF : A.E.IsScFredholmSectionFunctor F) (hF' : A'.E.IsScFredholmSectionFunctor F')
    (hpb : D.hΦ.pullback F = (sbe hΨ).pullback F') {Λ : A.W → ℚ≥0}
    (hΛ : IsScPlusMultisection A Λ) :
    IsInGeneralPosition A F Λ ↔ IsInGeneralPosition A' F' (D.pushMult hΨ Λ) := by
  rw [D.isInGeneralPosition_pushMult_iff hΨ hF hΛ, D.pushforward_eq_of_pullback_eq hΨ hF' hpb]

/-- **General position in one model gives good position in the other** (Definitions 15.3.5,
15.2.4; Theorem 15.4.3 (3)): for a diagram `W ←Φ W'' →Ψ W'` with `Φ^* F = Ψ^* F'`, `F'` with
tame germ data, and `(F, Λ)` in general position, `(F', [D]_* Λ)` is in good position at every
point of its support. -/
theorem isGoodPositionAt_pushMult_of_isInGeneralPosition (D : SDiagram A A')
    (hΨ : SEP.equivalences D.Ψ) {F : A.Obj → A.W} {F' : A'.Obj → A'.W}
    (hF : A.E.IsScFredholmSectionFunctor F) (hF' : A'.E.IsScFredholmSectionFunctor F')
    (hft' : A'.B.IsScFredholmSectionTame F') (hpb : D.hΦ.pullback F = (sbe hΨ).pullback F')
    {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ) (hgp : IsInGeneralPosition A F Λ)
    {x : A'.Obj} (hpos : 0 < D.pushMult hΨ Λ (F' x)) :
    IsGoodPositionAt F' (D.pushMult hΨ Λ) x := by
  have hΛ' := SDiagram.isScPlusMultisection_pushMult hΨ hΛ
  have h := (D.isInGeneralPosition_pushMult_iff_of_pullback_eq hΨ hF hF' hpb hΛ).1 hgp
  exact isGoodPositionAt_of_isInGeneralPositionAt hF' hft' hΛ' hpos
    ((isInGeneralPosition_iff_forall_at hF' hΛ').1 h x hpos)

end SDiagram

end SBLocalization

namespace StrongPolyfoldBundle

open StrongPolyfoldBundleStructure SEP

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p}

namespace OrientationRep

variable {s : FredholmSection c}

namespace Correspondence

/-- **A correspondence from a diagram** (Definition 16.6.5, Theorem 12.5.7 (2)): the middle
section `F'' = Φ^* F₁` is sc-Fredholm by Theorem 10.4.5, so only the diagram, `Γ₂ ∘ |D| = Γ₁`,
`Φ^* F₁ = Ψ^* F₂`, sc⁺-sections through the points of `W''` and `Φ^* o = Ψ^* o'` are asked. -/
def ofDiagram {o o' : OrientationRep s} (D : SDiagram o.a.S.A o'.a.S.A)
    (hΨ : SEP.equivalences D.Ψ) (hΓ : ⇑o'.a.S.Γ ∘ D.orbitMap = ⇑o.a.S.Γ)
    (hpb : D.hΦ.pullback o.a.F = (sbe hΨ).pullback o'.a.F)
    (hsec'' : D.B.B.HasScPlusSectionsThrough)
    (ho : D.hΦ.pullOr ((EpStrongBundle.theorem_10_4_5_fred D.hΦ).2.1 o.hF) o.hF rfl hsec''
        o.hsec o.o =
      (sbe hΨ).pullOr ((EpStrongBundle.theorem_10_4_5_fred D.hΦ).2.1 o.hF) o'.hF hpb hsec''
        o'.hsec o'.o) :
    Correspondence o o' where
  D := D
  hΨ := hΨ
  hΓ := hΓ
  f'' := D.hΦ.pullback o.a.F
  hF'' := (EpStrongBundle.theorem_10_4_5_fred D.hΦ).2.1 o.hF
  hpb₁ := rfl
  hpb₂ := hpb
  hsec'' := hsec''
  ho := ho

variable {o o' : OrientationRep s}

/-- **Tame germ data pass to the other model** (Theorem 10.4.5, Definition 3.6.5): `F₂ = Ψ_* F''`
with `F'' = Φ^* F₁`, and `Φ^*`, `Ψ_*` preserve tame germ data. -/
theorem isScFredholmSectionTame (C : Correspondence o o')
    (hft : o.a.S.A.B.IsScFredholmSectionTame o.a.F) :
    o'.a.S.A.B.IsScFredholmSectionTame o'.a.F := by
  have h1 : C.D.B.B.IsScFredholmSectionTame C.f'' := by
    rw [C.hpb₁]; exact C.D.hΦ.isScFredholmSectionTame_pullback hft
  have h2 := (sbe C.hΨ).isScFredholmSectionTame_pushforward C.hF''.1 h1
  rwa [C.hpb₂, (sbe C.hΨ).pushforward_pullback o'.hF.1.1.1 o'.hF.1.2] at h2

/-- **General position passes to the other model** (Definition 15.3.5): `(F₁, Λ)` is in general
position iff `(F₂, [D]_* Λ)` is. -/
theorem isInGeneralPosition_pushMult_iff (C : Correspondence o o') {Λ : o.a.S.A.W → ℚ≥0}
    (hΛ : IsScPlusMultisection o.a.S.A Λ) :
    IsInGeneralPosition o.a.S.A o.a.F Λ ↔
      IsInGeneralPosition o'.a.S.A o'.a.F (C.D.pushMult C.hΨ Λ) :=
  C.D.isInGeneralPosition_pushMult_iff_of_pullback_eq C.hΨ o.hF o'.hF
    (C.hpb₁.symm.trans C.hpb₂) hΛ

end Correspondence

end OrientationRep

/-! ### Canonical perturbations in general position -/

variable {s : FredholmSection c}

open OrientationRep

variable {m : ℕ} in
/-- **The perturbations of Theorem 16.6.6** (p. 739): `P` carries the canonical orientation of
`(F, o)` (Theorem 15.4.1, Definition 15.4.2) and `(F, Λ)` is in general position (Definition
15.3.5). -/
def IsCanonicalInGeneralPosition (o : OrientationRep s)
    (P : OrientedRegularPerturbation o.a.S.A o.a.F m) : Prop :=
  IsCanonicalPerturbation o.hF.2 o.hsec o.o P ∧ IsInGeneralPosition o.a.S.A o.a.F P.Λ

/-- An orientation inherited along a perturbation in general position is inherited along a
canonical perturbation. -/
theorem IsInheritedFrom.of_generalPosition {m : ℕ} {o : OrientationRep s}
    {Q : OrientedPerturbation s.1 m} (h : IsInheritedFrom IsCanonicalInGeneralPosition o Q) :
    IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o Q := by
  obtain ⟨P, hP, hQ⟩ := h
  exact ⟨P, hP.1, hQ⟩

/-- **The perturbed solution set inherited from `o` along a perturbation in general position is
inherited from `o'`** (§16.6, p. 739), for one perturbation.  Let `C` relate the models of `o`
and `o'`, and let the model of `o'` satisfy the standing hypotheses of Theorem 15.4.1 (tame,
sc-smooth bump functions, tame germ data, index `m + 1` at smooth points).  For a regular
perturbation `P` of the model of `o` with the canonical orientation of `(F₁, o)` and `(F₁, Λ)` in
general position, the perturbation `[D]_* Λ` of the model of `o'` with the canonical orientation
of `(F₂, o')` is again canonical and in general position (`isRegularPerturbation_pushMult`,
`SDiagram.isGoodPositionAt_pushMult_of_isInGeneralPosition`, Theorem 15.4.1), and has the same
oriented perturbed solution set `λ ∘ f` on `Z` (`toCompact_eq_of_diagram_pullSection`: the
pull-back of the canonical orientation to `W''` is canonical). -/
theorem isInheritedFrom_of_correspondence_generalPosition {o o' : OrientationRep s} {m : ℕ}
    (C : Correspondence o o') (hX : o'.a.S.A.X.PObj.IsTame)
    (hbump : o'.a.S.A.X.PObj.AdmitsBumpFunctions)
    (hft : o'.a.S.A.B.IsScFredholmSectionTame o'.a.F)
    (hidx : ∀ x ∈ o'.a.S.A.X.PObj.smoothSet, o'.a.S.A.B.IsIndexAt o'.a.F x ((m + 1 : ℕ) : ℤ))
    (P : OrientedRegularPerturbation o.a.S.A o.a.F m) (hP : IsCanonicalInGeneralPosition o P) :
    IsInheritedFrom IsCanonicalInGeneralPosition o'
      ((ModelPerturbation.ofRegular P).toOrientedPerturbation o.ha) := by
  have hgp₂ := (C.isInGeneralPosition_pushMult_iff P.isRegular.2.1.1).1 hP.2
  obtain ⟨D, hΨ, hΓ, f'', hF'', hpb₁, hpb₂, hsec'', ho⟩ := C
  subst hpb₁
  have hs : (⟦o.a⟧ : ScSection c) = ⟦o'.a⟧ := o.ha.trans o'.ha.symm
  have hreg := isRegularPerturbation_pushMult hs D hΨ hΓ o.hF o'.hF hpb₂ P.isRegular
  have hgood : ∀ x ∈ o'.a.S.A.X.PObj.boundary, 0 < D.pushMult hΨ P.Λ (o'.a.F x) →
      SBLocalization.IsGoodPositionAt o'.a.F (D.pushMult hΨ P.Λ) x := fun _ _ hpos =>
    D.isGoodPositionAt_pushMult_of_isInGeneralPosition hΨ o.hF o'.hF hft hpb₂
      P.isRegular.2.1.1 hP.2 hpos
  have ho' := o'.isSectionOrientation hX hbump hft
  have hidx' : ∀ x ∈ EpGroupoid.supp
      (fun z => ((D.pushMult hΨ P.Λ (o'.a.F z) : ℚ≥0) : ℚ)),
      o'.a.S.A.B.IsIndexAt o'.a.F x (m + 1 : ℕ) := fun x hx =>
    hidx x (mem_smoothSet_of_pos hft hreg.2.1.1 (by exact_mod_cast hx))
  have hC₂ := isCanonicalPerturbation_canonical hX hbump o'.hF hft o'.hsec o'.o
    o'.isOrientation.2 ho' hreg hgood hidx'
  refine ⟨_, ⟨hC₂, hgp₂⟩, ?_⟩
  have hΛ : ∀ w, P.Λ ((SEP.Hom.Φ D.Φ).obj w) =
      D.pushMult hΨ P.Λ ((SEP.Hom.Φ D.Ψ).obj w) := fun w =>
    (SBLocalization.pushMult_eq hΨ (P.isRegular.2.1.1.1.pullMult D.Φ) rfl).symm
  have heq := ModelPerturbation.toCompact_eq_of_diagram_pullSection
    (ModelPerturbation.ofRegular P)
    (ModelPerturbation.ofRegular (OrientedRegularPerturbation.canonical hX hbump o'.hF hft
      o'.hsec o'.o o'.isOrientation.2 ho' hreg hgood hidx'))
    D hΨ hΓ o.hF o'.hF hF'' hpb₂ o.hsec o'.hsec hsec'' hΛ ho
    (IsCanonicalFor.smoothPart hP.1) (IsCanonicalFor.smoothPart hC₂)
  exact OrientedPerturbation.ext_compact_t heq.symm
    (mk_ofFunctor_pushMult o.a.hS o'.a.hS D hΨ hΓ _ _)

/-- **The standing hypotheses of Theorem 15.4.1 in every model** (Definitions 16.3.5 (1),
16.1.5 (1)): for a tame strong polyfold bundle whose polyfold admits sc-smooth bump functions,
the model of every orientation representative is tame with sc-smooth bump functions. -/
theorem OrientationRep.tame_bump_of_polyfold (hc : c.IsTame)
    (hbump : c.polyfold.AdmitsBumpFunctions) (o : OrientationRep s) :
    o.a.S.A.X.PObj.IsTame ∧ o.a.S.A.X.PObj.AdmitsBumpFunctions :=
  ⟨(c.isTame_iff).1 hc o.a.S o.a.hS,
    (c.polyfold.definition_16_1_5_one).1 hbump _ (congrArg StrongPolyfoldBundle.polyfold o.a.hS)⟩

/-- **2021 §16.6, p. 739: the orientation inherited from `(f, o)` along a perturbation in
general position does not depend on the model of `o`** (gap (a″) of G.175, with boundary).  Let
`c` be a tame strong polyfold bundle whose polyfold admits sc-smooth bump functions (no
hypothesis on `∂Z`), and `o`, `o'` orientations of `f` on two representatives which correspond
over a diagram, with tame germ data in the model of `o` and index `m + 1` in both models.  Then
`θ̂` has the orientation inherited from `o` iff it has the one inherited from `o'`. -/
theorem isInheritedFrom_generalPosition_iff_of_correspondence (hc : c.IsTame)
    (hbump : c.polyfold.AdmitsBumpFunctions) {o o' : OrientationRep s}
    (C : Correspondence o o') {m : ℕ} (hft : o.a.S.A.B.IsScFredholmSectionTame o.a.F)
    (hidx : ∀ x ∈ o.a.S.A.X.PObj.smoothSet, o.a.S.A.B.IsIndexAt o.a.F x ((m + 1 : ℕ) : ℤ))
    (hidx' : ∀ x ∈ o'.a.S.A.X.PObj.smoothSet, o'.a.S.A.B.IsIndexAt o'.a.F x ((m + 1 : ℕ) : ℤ))
    (Q : OrientedPerturbation s.1 m) :
    IsInheritedFrom IsCanonicalInGeneralPosition o Q ↔
      IsInheritedFrom IsCanonicalInGeneralPosition o' Q := by
  obtain ⟨hX, hb⟩ := o.tame_bump_of_polyfold hc hbump
  obtain ⟨hX', hb'⟩ := o'.tame_bump_of_polyfold hc hbump
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact isInheritedFrom_of_correspondence_generalPosition C hX' hb'
      (C.isScFredholmSectionTame hft) hidx' P hP
  · rintro ⟨P, hP, rfl⟩
    exact isInheritedFrom_of_correspondence_generalPosition C.symm hX hb hft hidx P hP

/-! ### Theorem 16.6.6 across two models -/

/-- **2021 Theorem 16.6.6, p. 739, across two models of the orientation** (G.175 (a″)): let `Z`
admit sc-smooth partitions of unity, `∂Z = ∅`, `f` with compact solution set, `(n, U)`
controlling compactness, and `o`, `o'` orientations of `f` which correspond over a diagram
(`Correspondence`), with the standing hypotheses in the model of `o` (`CanonicalInput o (m + 1)`)
and index `m + 1` in the model of `o'`.  For admissible `θ̂₀` inherited from `o` and `θ̂₁`
inherited from `o'`, a closed `τ` has `∫_θ̂₀ τ = ∫_θ̂₁ τ` and `∮_θ̂₀ τ = ∮_θ̂₁ τ`.  The canonical
orientation on the middle bundle is `Correspondence.middleCanonical`, and the tame germ data of
the model of `o'` are `Correspondence.isScFredholmSectionTame`. -/
theorem theorem_16_6_6_correspondence (hPU : c.polyfold.AdmitsScPartitionsOfUnity)
    (n : Y → ℝ) (U : Set Z) {m : ℕ} (hbd : c.polyfold.boundary = ∅)
    (hcs : s.1.HasCompactSolutionSet) (hn : c.IsAuxNorm n) (hU : IsOpen U)
    (hcc : s.1.ControlsCompactness n U) {o o' : OrientationRep s} (C : Correspondence o o')
    (H : CanonicalInput o (m + 1))
    (hidx' : ∀ x ∈ o'.a.S.A.X.PObj.smoothSet, o'.a.S.A.B.IsIndexAt o'.a.F x ((m + 1 : ℕ) : ℤ))
    (Q₀ Q₁ : OrientedPerturbation s.1 m) (h₀ : Q₀.IsAdmissible n U)
    (hQ₀ : IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o Q₀)
    (h₁ : Q₁.IsAdmissible n U)
    (hQ₁ : IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o' Q₁)
    (τ : ScForm c.polyfold (m + 1)) (hτ : ScForm.d τ = 0) :
    Q₀.integral τ = Q₁.integral τ ∧ Q₀.integralEff τ = Q₁.integralEff τ :=
  integral_eq_of_correspondence hPU n U hbd hcs hn hU hcc C H
    (C.isScFredholmSectionTame H.tame) hidx' (C.middleCanonical m) (C.symm.middleCanonical m)
    Q₀ Q₁ h₀ hQ₀ h₁ hQ₁ τ hτ

/-- **2021 Theorem 16.6.6 across two models, for perturbations in general position** (the
perturbations of the text, p. 739): the same conclusion for `θ̂₀`, `θ̂₁` inherited along
canonically oriented perturbations in general position. -/
theorem theorem_16_6_6_correspondence_generalPosition
    (hPU : c.polyfold.AdmitsScPartitionsOfUnity) (n : Y → ℝ) (U : Set Z) {m : ℕ}
    (hbd : c.polyfold.boundary = ∅) (hcs : s.1.HasCompactSolutionSet) (hn : c.IsAuxNorm n)
    (hU : IsOpen U) (hcc : s.1.ControlsCompactness n U) {o o' : OrientationRep s}
    (C : Correspondence o o') (H : CanonicalInput o (m + 1))
    (hidx' : ∀ x ∈ o'.a.S.A.X.PObj.smoothSet, o'.a.S.A.B.IsIndexAt o'.a.F x ((m + 1 : ℕ) : ℤ))
    (Q₀ Q₁ : OrientedPerturbation s.1 m) (h₀ : Q₀.IsAdmissible n U)
    (hQ₀ : IsInheritedFrom IsCanonicalInGeneralPosition o Q₀) (h₁ : Q₁.IsAdmissible n U)
    (hQ₁ : IsInheritedFrom IsCanonicalInGeneralPosition o' Q₁)
    (τ : ScForm c.polyfold (m + 1)) (hτ : ScForm.d τ = 0) :
    Q₀.integral τ = Q₁.integral τ ∧ Q₀.integralEff τ = Q₁.integralEff τ :=
  theorem_16_6_6_correspondence hPU n U hbd hcs hn hU hcc C H hidx' Q₀ Q₁ h₀
    hQ₀.of_generalPosition h₁ hQ₁.of_generalPosition τ hτ

end StrongPolyfoldBundle

end Polyfold
