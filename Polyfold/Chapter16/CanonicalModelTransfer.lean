import Polyfold.Chapter16.CanonicalModelIndependence
import Polyfold.Chapter16.CanonicalIntegralInvariance
import Polyfold.Chapter16.GeneralPositionModels
import Polyfold.Chapter15.TransversalityEquivalence
import Polyfold.Chapter13.MultisectionPushforward

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §16.6, p. 739:
**Definition 16.6.5** and **Theorem 16.6.6** (2017: Definition 16.42, Theorem 16.8), with
**Theorem 15.4.1**, **Definition 15.4.2** (pp. 701–702), **Corollary 15.3.10 (1)** (p. 699),
**Definitions 16.3.9, 16.5.1, 16.5.4** (pp. 726, 733–734) and **Theorem 13.4.3** (p. 625).

# The orientation inherited from `(f, o)` does not depend on the model of `o`

## The text, paraphrased

(Definition 16.6.5) An orientation of an sc-Fredholm section `f` of `p : Y → Z` is an orientation
`o` of a representative `(W, F)`; it determines the orientations of all other representatives.
(p. 739) For a generic `λ`, `θ = λ ∘ f` carries the orientation inherited from `(f, o)`: in a
model, `θ̂` is `(Λ ∘ F, T̂)` with `T̂` the canonical orientation of Theorem 15.4.1 and Definition
15.4.2.  Two models are related by a generalized strong bundle isomorphism
`[W₁ ←Φ W'' →Ψ W₂]`, and the text takes the inherited orientation to be the same in both.

## What is formalized (namespace `Polyfold.StrongPolyfoldBundle`)

* `mk_ofFunctor_pushMult`: for structures `S₁`, `S₂` of `c̄` and a diagram `D` with
  `Γ₂ ∘ |D| = Γ₁`, the sc⁺-multisection functors `Λ` and `[D]_* Λ = Ψ_* Φ^* Λ` represent the same
  sc⁺-multisection `λ` of `p` (Definition 16.5.1).
* **`isRegularPerturbation_pushMult`**: a structurable regular perturbation `(N, U, Λ)` of `F₁`
  (Corollary 15.3.10 (1)) gives the structurable regular perturbation
  `(n_{S₂}, γ₂π₂⁻¹(γ₁π₁(U)), [D]_* Λ)` of `F₂`, with `n` the auxiliary norm of `p` read from `N`
  (Definition 16.3.9): compactness control through the polyfold (Definition 16.6.3), structurability
  (Theorems 13.4.1, 13.4.3), dom-supp and `N(Λ) < 1` through `λ` (Remark 16.5.3, (16.8)), and
  transversality (`SDiagram.isTransversal_iff_of_pullback_eq`).
* `OrientationRep.Correspondence o o'`: a diagram `W₁ ←Φ W'' →Ψ W₂` of strong bundle equivalences
  between the models of `o` and `o'` with `Γ₂ ∘ |D| = Γ₁`, `Φ^* F₁ = Ψ^* F₂`, and `Φ^* o = Ψ^* o'`
  (Definition 16.6.5, Theorem 12.5.7); `Correspondence.symm`.
* `Correspondence.MiddleCanonical`: the hypothesis `hT''` of
  `ModelPerturbation.toCompact_eq_of_diagram` for every canonically oriented perturbation of the
  model of `o`: `Λ ∘ Φ` has a canonical orientation on `W''` for `Φ^* o`.
* **`isInheritedFrom_of_diagram`**: for a canonically oriented regular perturbation `P` in the
  model of `o` and the standing hypotheses of Theorem 15.4.1 in the model of `o'` (tame, sc-smooth
  bump functions, tame germ data, index `m + 1`, good position of `[D]_* Λ` at the boundary points
  of its support), the perturbation `([D]_* Λ, T̂_((F₂, o'), [D]_* Λ))` of the model of `o'` has the
  same oriented perturbed solution set `λ ∘ f` on `Z`.  So
  `IsInheritedFrom Can o Q → IsInheritedFrom Can o' Q`.
* **`isInheritedFrom_iff_of_correspondence`**: for `∂Z = ∅` and `Z` with sc-smooth partitions of
  unity (Theorem 16.6.6's hypotheses), with tame germ data and index `m + 1` in both models:
  `IsInheritedFrom Can o Q ↔ IsInheritedFrom Can o' Q`.
* **`integral_eq_of_correspondence`**: hence, in Theorem 16.6.6, `∫_θ̂ τ` and `∮_θ̂ τ` of a closed
  `τ` agree for an admissible `θ̂` inherited from `o` and one inherited from `o'`.

## Reading and hypotheses

* `MiddleCanonical` (`hT''` of `toCompact_eq_of_diagram`) is kept as a hypothesis: it says that
  the pull-back of a canonical orientation along a strong bundle equivalence is canonical.
* Good position at the boundary points of the support (Theorem 15.4.3 (3)) is a hypothesis of
  `isInheritedFrom_of_diagram` in the model of `o'`; it is vacuous for `∂Z = ∅`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

open EPLocalization EpGroupoid SBLocalization PolyfoldClass

namespace SBLocalization

variable {A : SEP.{u}} {f : A.Obj → A.W}

/-- **A canonical orientation stays canonical when cut off outside `X_∞`** (Definition 15.4.2 reads
`T̂` only at smooth points). -/
theorem IsCanonicalFor.smoothPart {Λ : A.W → ℚ≥0} {hf : A.B.IsScFredholmSection f}
    {hsec : A.B.HasScPlusSectionsThrough}
    {o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf y hy} {n : ℕ}
    {T : A.Obj → A.X.PObj.OrTangent →₀ ℚ} (h : IsCanonicalFor Λ hf hsec o n T) :
    IsCanonicalFor Λ hf hsec o n (A.X.smoothPart T) := by
  refine ⟨h.1.smoothPart, fun x hx => ?_⟩
  obtain ⟨K, hc, hn, hR⟩ := h.2 x hx
  exact ⟨K, hc, hn, (K.toOrientedTame hc hn).represents_congr
    (fun _ hy => (smoothPart_of_mem hy).symm) hR⟩

end SBLocalization

namespace StrongPolyfoldBundle

open StrongPolyfoldBundleStructure SEP

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p}

/-- Two oriented perturbed solution sets with the same oriented suborbifold and the same `λ` are
equal. -/
theorem OrientedPerturbation.ext_compact_t {s : ScSection c} {m : ℕ}
    {P P' : OrientedPerturbation s m}
    (h₁ : P.toCompactOrientedSuborbifold = P'.toCompactOrientedSuborbifold) (h₂ : P.t = P'.t) :
    P = P' := by
  obtain ⟨a, t, hp⟩ := P
  obtain ⟨a', t', hp'⟩ := P'
  obtain rfl : a = a' := h₁
  obtain rfl : t = t' := h₂
  rfl

/-! ### Transport of a regular perturbation along a diagram -/

/-- **`Λ` and `[D]_* Λ` represent the same sc⁺-multisection** (Definition 16.5.1): for
structures `S₁`, `S₂` of `c̄` and a diagram `D : W₁ ←Φ W'' →Ψ W₂` of strong bundle equivalences
with `Γ₂ ∘ |D| = Γ₁`. -/
theorem mk_ofFunctor_pushMult {S₁ S₂ : StrongPolyfoldBundleStructure p} (hS₁ : ⟦S₁⟧ = c)
    (hS₂ : ⟦S₂⟧ = c) (D : SDiagram S₁.A S₂.A) (hΨ : SEP.equivalences D.Ψ)
    (hΓ : ⇑S₂.Γ ∘ D.orbitMap = ⇑S₁.Γ) {Λ : S₁.A.W → ℚ≥0} (hΛ : IsScPlusMultisection S₁.A Λ)
    (hΛ₂ : IsScPlusMultisection S₂.A (D.pushMult hΨ Λ)) :
    (⟦ofFunctor S₂ hS₂ (D.pushMult hΨ Λ) hΛ₂⟧ : ScPlusMultisection c) =
      ⟦ofFunctor S₁ hS₁ Λ hΛ⟧ := by
  refine mk_ofFunctor_eq _ hS₂ hΛ₂ fun w₂ => ?_
  set w₁ := (S₁.Γ.symm (S₂.Γ (S₂.A.E.toEpGroupoid.π w₂))).out
  have h₁ : S₁.A.E.toEpGroupoid.π w₁ = S₁.Γ.symm (S₂.Γ (S₂.A.E.toEpGroupoid.π w₂)) :=
    Quotient.out_eq _
  have h₂ : D.orbitMap (S₁.A.E.toEpGroupoid.π w₁) = S₂.A.E.toEpGroupoid.π w₂ := by
    apply S₂.Γ.injective
    have := congrFun hΓ (S₁.A.E.toEpGroupoid.π w₁)
    simp only [Function.comp_apply] at this
    rw [this, h₁, Homeomorph.apply_symm_apply]
  change Λ w₁ = D.pushMult hΨ Λ w₂
  exact (SDiagram.pushMult_eq hΛ.1 h₂).symm

/-- **A structurable regular perturbation carried to another model** (Corollary 15.3.10 (1),
Definitions 16.3.9, 16.6.3): let `a₁`, `a₂` represent the same section, `D : W₁ ←Φ W'' →Ψ W₂`
a diagram of strong bundle equivalences with `Γ₂ ∘ |D| = Γ₁` and `Φ^* F₁ = Ψ^* F₂`, and
`(N, U, Λ)` a structurable regular perturbation of `F₁`.  With `n` the auxiliary norm of `p`
read from `N`, `(n_{S₂}, γ₂π₂⁻¹(γ₁π₁(U)), [D]_* Λ)` is a structurable regular perturbation
of `F₂`. -/
theorem isRegularPerturbation_pushMult {a₁ a₂ : SectionRep c}
    (hs : (⟦a₁⟧ : ScSection c) = ⟦a₂⟧) (D : SDiagram a₁.S.A a₂.S.A) (hΨ : SEP.equivalences D.Ψ)
    (hΓ : ⇑a₂.S.Γ ∘ D.orbitMap = ⇑a₁.S.Γ) (hF₁ : a₁.S.A.E.IsScFredholmSectionFunctor a₁.F)
    (hF₂ : a₂.S.A.E.IsScFredholmSectionFunctor a₂.F)
    (hpb : D.hΦ.pullback a₁.F = (sbe hΨ).pullback a₂.F) {N : a₁.S.A.B.One → ℝ}
    {U : Set a₁.S.A.Obj} {Λ : a₁.S.A.W → ℚ≥0} (h : IsRegularPerturbation a₁.S.A a₁.F N U Λ) :
    IsRegularPerturbation a₂.S.A a₂.F (a₂.S.normOf (a₁.S.descend N)) (a₂.g ⁻¹' (a₁.g '' U))
      (D.pushMult hΨ Λ) := by
  obtain ⟨hcc, hst, hdom, hlt, htr⟩ := h
  have hN := hcc.1
  have hn : c.IsAuxNorm (a₁.S.descend N) := isAuxNorm_descend a₁.hS hN
  have hV : IsOpen (a₁.g '' U) := a₁.isOpen_g_image hcc.2.1
  have hUV : a₁.g ⁻¹' (a₁.g '' U) = U := a₁.preimage_g_image hcc.2.2.1
  have hcc₁ : SBLocalization.ControlsCompactness a₁.S.A a₁.F (a₁.S.normOf (a₁.S.descend N))
      (a₁.g ⁻¹' (a₁.g '' U)) := by
    rw [a₁.S.normOf_descend hN.isOneInvariant, hUV]; exact hcc
  have hcc₂ := (a₂.controlsCompactness_iff hn hV).1
    (hs ▸ (a₁.controlsCompactness_iff hn hV).2 hcc₁)
  have hΛ := hst.1
  have hst₂ := SDiagram.isStructurable_pushMult D hΨ hst
  have hΛ₂ := hst₂.1
  have hm := mk_ofFunctor_pushMult a₁.hS a₂.hS D hΨ hΓ hΛ hΛ₂
  refine ⟨hcc₂, hst₂, fun x hx => ?_, fun x => ?_, ?_⟩
  · have h₂ := remark_16_5_3 (ofFunctor a₂.S a₂.hS (D.pushMult hΨ Λ) hΛ₂)
    have h₁ := remark_16_5_3 (ofFunctor a₁.S a₁.hS Λ hΛ)
    rw [hm, ← h₁] at h₂
    obtain ⟨_, ⟨y, hy, rfl⟩, hyx⟩ := (Set.ext_iff.1 h₂ (a₂.g x)).1 ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨y, hdom hy, hyx⟩
  · obtain ⟨y, hy⟩ := a₁.S.surjective_γπ (a₂.g x)
    have hy' : a₁.S.γ (a₁.S.A.X.π y) = a₂.S.γ (a₂.S.A.X.π x) := hy
    have e₂ := normLam_eq a₂.hS (a₁.S.descend N) (D.pushMult hΨ Λ) _ x
      (fun w _ => toFun_of_mk_ofFunctor_eq hm w)
    have e₁ := normLam_eq a₁.hS (a₁.S.descend N) Λ _ y
      (fun w _ => (ofFunctor a₁.S a₁.hS Λ hΛ).comm w)
    have h1 := hlt y
    rw [← a₁.S.normOf_descend hN.isOneInvariant, ← e₁, hy'] at h1
    rw [← e₂]
    exact h1
  · exact (SDiagram.isTransversal_iff_of_pullback_eq D hΨ hF₁ hF₂ hpb hΛ hΛ₂
      fun _ _ h => (SDiagram.pushMult_eq hΛ.1 h).symm).1 htr

/-! ### Corresponding orientations of two models -/

namespace OrientationRep

variable {s : FredholmSection c}

/-- **Two orientations of `f` correspond over a diagram** (Definition 16.6.5, Theorem 12.5.7 (2)):
a diagram `W₁ ←Φ W'' →Ψ W₂` of strong bundle equivalences between the models of `o` and `o'`
with `Γ₂ ∘ |D| = Γ₁`, a section `F''` of `W''` with `F'' = Φ^* F₁ = Ψ^* F₂`, and
`Φ^* o = Ψ^* o'` on `W''`. -/
structure Correspondence (o o' : OrientationRep s) : Type (u + 1) where
  /-- The diagram `W₁ ←Φ W'' →Ψ W₂`. -/
  D : SDiagram o.a.S.A o'.a.S.A
  hΨ : SEP.equivalences D.Ψ
  hΓ : ⇑o'.a.S.Γ ∘ D.orbitMap = ⇑o.a.S.Γ
  /-- The common pull-back `F''`. -/
  f'' : D.B.Obj → D.B.W
  hF'' : D.B.E.IsScFredholmSectionFunctor f''
  hpb₁ : f'' = D.hΦ.pullback o.a.F
  hpb₂ : f'' = (sbe hΨ).pullback o'.a.F
  hsec'' : D.B.B.HasScPlusSectionsThrough
  ho : D.hΦ.pullOr hF'' o.hF hpb₁ hsec'' o.hsec o.o =
    (sbe hΨ).pullOr hF'' o'.hF hpb₂ hsec'' o'.hsec o'.o

namespace Correspondence

variable {o o' : OrientationRep s}

/-- **The reversed correspondence** `W₂ ←Ψ W'' →Φ W₁`. -/
def symm (C : Correspondence o o') : Correspondence o' o where
  D := C.D.symm C.hΨ
  hΨ := C.D.isEquivalence_Φ
  hΓ := by
    funext q'
    obtain ⟨q, hq⟩ := (C.D.total.isHomeomorph_orbitMap (sbe C.hΨ).isEquivalence).surjective q'
    subst hq
    change o.a.S.Γ ((C.D.symm C.hΨ).orbitMap (C.D.orbitMap q)) = o'.a.S.Γ (C.D.orbitMap q)
    rw [C.D.orbitMap_symm_orbitMap C.hΨ]
    exact (congrFun C.hΓ q).symm
  f'' := C.f''
  hF'' := C.hF''
  hpb₁ := C.hpb₂
  hpb₂ := C.hpb₁
  hsec'' := C.hsec''
  ho := C.ho.symm

variable (m : ℕ) in
/-- **The canonical orientation on the middle bundle** (the hypothesis `hT''` of
`ModelPerturbation.toCompact_eq_of_diagram`): for every regular perturbation `P` of the model of
`o` with the canonical orientation of `(F₁, o)`, `Λ ∘ Φ` has a canonical orientation on `W''`
for `(F'', Φ^* o)`. -/
def MiddleCanonical (C : Correspondence o o') : Prop :=
  ∀ P : OrientedRegularPerturbation o.a.S.A o.a.F m,
    IsCanonicalPerturbation o.hF.2 o.hsec o.o P →
      ∃ (n : ℕ) (T'' : C.D.B.Obj → C.D.B.X.PObj.OrTangent →₀ ℚ),
        IsCanonicalFor (fun w => P.Λ ((SEP.Hom.Φ C.D.Φ).obj w)) C.hF''.2 C.hsec''
          (C.D.hΦ.pullOr C.hF'' o.hF C.hpb₁ C.hsec'' o.hsec o.o) n T''

end Correspondence

end OrientationRep

/-! ### The inherited orientation in the other model -/

open OrientationRep

variable {s : FredholmSection c}

/-- **The perturbed solution set inherited from `o` is inherited from `o'`** (§16.6, p. 739),
for one perturbation.  Let `D : W₁ ←Φ W'' →Ψ W₂` relate the models of `o` and `o'` (as in
`Correspondence`, with `F'' = Φ^* F₁`), and let the model of `o'` satisfy the standing hypotheses
of Theorem 15.4.1 (tame, sc-smooth bump functions, tame germ data, index `m + 1` at smooth points).
For a regular perturbation `P` of the model of `o` with the canonical orientation of `(F₁, o)`,
such that `Λ ∘ Φ` has a canonical orientation on `W''` (`hT''`) and `[D]_* Λ` is in good position
at the boundary points of `supp([D]_* Λ ∘ F₂)` (Theorem 15.4.3 (3)), the canonically oriented
perturbation `[D]_* Λ` of the model of `o'` (`isRegularPerturbation_pushMult`, Theorem 15.4.1)
has the same oriented perturbed solution set `λ ∘ f` on `Z` (`toCompact_eq_of_diagram`). -/
theorem isInheritedFrom_of_diagram {o o' : OrientationRep s} {m : ℕ}
    (D : SDiagram o.a.S.A o'.a.S.A) (hΨ : SEP.equivalences D.Ψ)
    (hΓ : ⇑o'.a.S.Γ ∘ D.orbitMap = ⇑o.a.S.Γ)
    (hF'' : D.B.E.IsScFredholmSectionFunctor (D.hΦ.pullback o.a.F))
    (hpb : D.hΦ.pullback o.a.F = (sbe hΨ).pullback o'.a.F)
    (hsec'' : D.B.B.HasScPlusSectionsThrough)
    (ho : D.hΦ.pullOr hF'' o.hF rfl hsec'' o.hsec o.o =
      (sbe hΨ).pullOr hF'' o'.hF hpb hsec'' o'.hsec o'.o)
    (hX : o'.a.S.A.X.PObj.IsTame) (hbump : o'.a.S.A.X.PObj.AdmitsBumpFunctions)
    (hft : o'.a.S.A.B.IsScFredholmSectionTame o'.a.F)
    (hidx : ∀ x ∈ o'.a.S.A.X.PObj.smoothSet, o'.a.S.A.B.IsIndexAt o'.a.F x ((m + 1 : ℕ) : ℤ))
    (P : OrientedRegularPerturbation o.a.S.A o.a.F m)
    (hP : IsCanonicalPerturbation o.hF.2 o.hsec o.o P)
    {n : ℕ} {T'' : D.B.Obj → D.B.X.PObj.OrTangent →₀ ℚ}
    (hT'' : IsCanonicalFor (fun w => P.Λ ((SEP.Hom.Φ D.Φ).obj w)) hF''.2 hsec''
      (D.hΦ.pullOr hF'' o.hF rfl hsec'' o.hsec o.o) n T'')
    (hgood : ∀ x ∈ o'.a.S.A.X.PObj.boundary, 0 < D.pushMult hΨ P.Λ (o'.a.F x) →
      SBLocalization.IsGoodPositionAt o'.a.F (D.pushMult hΨ P.Λ) x) :
    IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o'
      ((ModelPerturbation.ofRegular P).toOrientedPerturbation o.ha) := by
  have hs : (⟦o.a⟧ : ScSection c) = ⟦o'.a⟧ := o.ha.trans o'.ha.symm
  have hreg := isRegularPerturbation_pushMult hs D hΨ hΓ o.hF o'.hF hpb P.isRegular
  have ho' := o'.isSectionOrientation hX hbump hft
  have hidx' : ∀ x ∈ EpGroupoid.supp
      (fun z => ((D.pushMult hΨ P.Λ (o'.a.F z) : ℚ≥0) : ℚ)),
      o'.a.S.A.B.IsIndexAt o'.a.F x (m + 1 : ℕ) := fun x hx =>
    hidx x (mem_smoothSet_of_pos hft hreg.2.1.1 (by exact_mod_cast hx))
  have hC₂ := isCanonicalPerturbation_canonical hX hbump o'.hF hft o'.hsec o'.o
    o'.isOrientation.2 ho' hreg hgood hidx'
  refine ⟨_, hC₂, ?_⟩
  have hΛ : ∀ w, P.Λ ((SEP.Hom.Φ D.Φ).obj w) =
      D.pushMult hΨ P.Λ ((SEP.Hom.Φ D.Ψ).obj w) := fun w =>
    (SBLocalization.pushMult_eq hΨ (P.isRegular.2.1.1.1.pullMult D.Φ) rfl).symm
  have heq := ModelPerturbation.toCompact_eq_of_diagram (ModelPerturbation.ofRegular P)
    (ModelPerturbation.ofRegular (OrientedRegularPerturbation.canonical hX hbump o'.hF hft
      o'.hsec o'.o o'.isOrientation.2 ho' hreg hgood hidx'))
    D hΨ hΓ o.hF o'.hF hF'' hpb o.hsec o'.hsec hsec'' hΛ ho (IsCanonicalFor.smoothPart hP)
    (IsCanonicalFor.smoothPart hC₂) hT''
  exact OrientedPerturbation.ext_compact_t heq.symm
    (mk_ofFunctor_pushMult o.a.hS o'.a.hS D hΨ hΓ _ _)

/-- **`IsInheritedFrom Can o Q → IsInheritedFrom Can o' Q` for corresponding orientations**
(§16.6, p. 739): under the standing hypotheses of Theorem 15.4.1 in the model of `o'`, the
canonical orientation on the middle bundle (`MiddleCanonical`) and good position at the boundary
points of the support of every carried perturbation. -/
theorem isInheritedFrom_of_correspondence {o o' : OrientationRep s} (C : Correspondence o o')
    {m : ℕ} (hX : o'.a.S.A.X.PObj.IsTame) (hbump : o'.a.S.A.X.PObj.AdmitsBumpFunctions)
    (hft : o'.a.S.A.B.IsScFredholmSectionTame o'.a.F)
    (hidx : ∀ x ∈ o'.a.S.A.X.PObj.smoothSet, o'.a.S.A.B.IsIndexAt o'.a.F x ((m + 1 : ℕ) : ℤ))
    (hT : C.MiddleCanonical m)
    (hgood : ∀ P : OrientedRegularPerturbation o.a.S.A o.a.F m,
      IsCanonicalPerturbation o.hF.2 o.hsec o.o P → ∀ x ∈ o'.a.S.A.X.PObj.boundary,
        0 < C.D.pushMult C.hΨ P.Λ (o'.a.F x) →
          SBLocalization.IsGoodPositionAt o'.a.F (C.D.pushMult C.hΨ P.Λ) x)
    {Q : OrientedPerturbation s.1 m} :
    IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o Q →
      IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o' Q := by
  rintro ⟨P, hP, rfl⟩
  obtain ⟨n, T'', hT''⟩ := hT P hP
  have hg := hgood P hP
  obtain ⟨D, hΨ, hΓ, f'', hF'', hpb₁, hpb₂, hsec'', ho⟩ := C
  subst hpb₁
  exact isInheritedFrom_of_diagram D hΨ hΓ hF'' hpb₂ hsec'' ho hX hbump hft hidx P hP hT'' hg

/-- For `∂Z = ∅` and `Z` with sc-smooth partitions of unity, every model is tame (`d_X ≡ 0`) with
sc-smooth bump functions (Theorem 12.3.2 (1)) and empty boundary. -/
theorem OrientationRep.tame_bump_of_boundary_eq_empty
    (hPU : c.polyfold.AdmitsScPartitionsOfUnity) (hbd : c.polyfold.boundary = ∅)
    (o : OrientationRep s) :
    o.a.S.A.X.PObj.IsTame ∧ o.a.S.A.X.PObj.AdmitsBumpFunctions ∧
      ∀ x, x ∉ o.a.S.A.X.PObj.boundary := by
  have hd : ∀ x, o.a.S.A.X.PObj.degIndex x = 0 :=
    degIndex_eq_zero_of_boundary_eq_empty hbd o.a.hS
  have hPUq := (c.polyfold.definition_16_1_5_two).1 hPU o.a.S.toPolyfoldStructure
    (toPolyfoldStructure_mem o.a.hS)
  exact ⟨o.a.S.A.X.isTame_of_degIndex_eq_zero hd, o.a.S.A.X.theorem_12_3_2_1.1
    (EpGroupoid.admitsBumpFunctionsPointwise_of_hasScPartitionsOfUnity hPUq),
    fun x hx => (Nat.one_le_iff_ne_zero.1 hx) (hd x)⟩

/-- **`IsInheritedFrom Can o Q → IsInheritedFrom Can o' Q` for `∂Z = ∅`** (Theorem 16.6.6's
hypotheses): with sc-smooth partitions of unity on `Z`, tame germ data and index `m + 1` in the
model of `o'`, and the canonical orientation on the middle bundle. -/
theorem isInheritedFrom_of_correspondence_of_boundary_eq_empty
    (hPU : c.polyfold.AdmitsScPartitionsOfUnity) (hbd : c.polyfold.boundary = ∅)
    {o o' : OrientationRep s} (C : Correspondence o o') {m : ℕ}
    (hft : o'.a.S.A.B.IsScFredholmSectionTame o'.a.F)
    (hidx : ∀ x ∈ o'.a.S.A.X.PObj.smoothSet, o'.a.S.A.B.IsIndexAt o'.a.F x ((m + 1 : ℕ) : ℤ))
    (hT : C.MiddleCanonical m) {Q : OrientedPerturbation s.1 m} :
    IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o Q →
      IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o' Q := by
  obtain ⟨hX, hbump, hbd'⟩ := o'.tame_bump_of_boundary_eq_empty hPU hbd
  exact isInheritedFrom_of_correspondence C hX hbump hft hidx hT
    fun _ _ x hx => absurd hx (hbd' x)

/-- **2021 §16.6, p. 739: the orientation inherited from `(f, o)` does not depend on the model of
`o`** (point (a″) of G.175, for `∂Z = ∅`).  Let `Z` admit sc-smooth partitions of unity, `∂Z = ∅`,
and let `o`, `o'` be orientations of `f` on two representatives which correspond over a diagram
(`Correspondence`), with tame germ data and Fredholm index `m + 1` in both models.  If the
canonical orientations pull back to canonical orientations on the middle bundle (`hT`, `hT'`),
then `θ̂` has the orientation inherited from `o` iff it has the one inherited from `o'`. -/
theorem isInheritedFrom_iff_of_correspondence (hPU : c.polyfold.AdmitsScPartitionsOfUnity)
    (hbd : c.polyfold.boundary = ∅) {o o' : OrientationRep s} (C : Correspondence o o')
    {m : ℕ} (hft : o.a.S.A.B.IsScFredholmSectionTame o.a.F)
    (hft' : o'.a.S.A.B.IsScFredholmSectionTame o'.a.F)
    (hidx : ∀ x ∈ o.a.S.A.X.PObj.smoothSet, o.a.S.A.B.IsIndexAt o.a.F x ((m + 1 : ℕ) : ℤ))
    (hidx' : ∀ x ∈ o'.a.S.A.X.PObj.smoothSet, o'.a.S.A.B.IsIndexAt o'.a.F x ((m + 1 : ℕ) : ℤ))
    (hT : C.MiddleCanonical m) (hT' : C.symm.MiddleCanonical m)
    (Q : OrientedPerturbation s.1 m) :
    IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o Q ↔
      IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o' Q :=
  ⟨isInheritedFrom_of_correspondence_of_boundary_eq_empty hPU hbd C hft' hidx' hT,
    isInheritedFrom_of_correspondence_of_boundary_eq_empty hPU hbd C.symm hft hidx hT'⟩

/-- **2021 Theorem 16.6.6, p. 739, across two models of the orientation**: let `Z` admit sc-smooth
partitions of unity, `∂Z = ∅`, `f` with compact solution set, `(n, U)` controlling compactness,
and `o`, `o'` corresponding orientations (`Correspondence`) with the standing hypotheses
(`CanonicalInput o (m + 1)`; tame germ data and index `m + 1` for `o'`) and the canonical
orientation on the middle bundle in both directions.  For admissible `θ̂₀` inherited from `o` and
`θ̂₁` inherited from `o'`, a closed `τ` has `∫_θ̂₀ τ = ∫_θ̂₁ τ` and `∮_θ̂₀ τ = ∮_θ̂₁ τ`. -/
theorem integral_eq_of_correspondence (hPU : c.polyfold.AdmitsScPartitionsOfUnity)
    (n : Y → ℝ) (U : Set Z) {m : ℕ} (hbd : c.polyfold.boundary = ∅)
    (hcs : s.1.HasCompactSolutionSet) (hn : c.IsAuxNorm n) (hU : IsOpen U)
    (hcc : s.1.ControlsCompactness n U) {o o' : OrientationRep s} (C : Correspondence o o')
    (H : CanonicalInput o (m + 1)) (hft' : o'.a.S.A.B.IsScFredholmSectionTame o'.a.F)
    (hidx' : ∀ x ∈ o'.a.S.A.X.PObj.smoothSet, o'.a.S.A.B.IsIndexAt o'.a.F x ((m + 1 : ℕ) : ℤ))
    (hT : C.MiddleCanonical m) (hT' : C.symm.MiddleCanonical m)
    (Q₀ Q₁ : OrientedPerturbation s.1 m) (h₀ : Q₀.IsAdmissible n U)
    (hQ₀ : IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o Q₀)
    (h₁ : Q₁.IsAdmissible n U)
    (hQ₁ : IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o' Q₁)
    (τ : ScForm c.polyfold (m + 1)) (hτ : ScForm.d τ = 0) :
    Q₀.integral τ = Q₁.integral τ ∧ Q₀.integralEff τ = Q₁.integralEff τ := by
  have hQ₁' := (isInheritedFrom_iff_of_correspondence hPU hbd C H.tame hft' H.index hidx' hT hT'
    Q₁).2 hQ₁
  exact (theorem_16_6_6_canonical hPU s n U m hbd hcs hn hU hcc o).2 Q₀ Q₁ h₀ ⟨H, hQ₀⟩ h₁
    ⟨H, hQ₁'⟩ τ hτ

end StrongPolyfoldBundle

end Polyfold
