import Polyfold.Chapter18.FredholmSectionFunctors
import Polyfold.Chapter18.ModelTransfer
import Polyfold.Chapter18.Linearization
import Polyfold.Chapter11.AuxiliaryNormTransport
import Polyfold.Chapter16.MixedTransfer
import Polyfold.Chapter16.ReflexivePush
import Polyfold.Chapter12.ReflexiveCompactnessEp
import Polyfold.Chapter17.BranchedSubcategory

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 18,
§18.1 pp. 846–848 and §18.2 pp. 849–851: **auxiliary norms `N : E → [0, ∞]` read through the
strong bundle models, and the sets `{z | |N| ∘ |f|(z) ≤ C}`** that the compactness notions of
§18.2 (Definitions 18.2.1, 18.2.3, 18.2.4, Remark 18.2.5, Theorem 18.2.6) are built from.
Numbers and pages are the 2021 text's.

## The text, paraphrased

(Definition 18.1.7, p. 846) An auxiliary norm is a functor `N : E → [0, ∞]` with `N = +∞` off
`E_{0,1}`, a complete norm on every fibre of `E_{0,1}`, and `|P(h_k)| → |α|`, `|N|(|h_k|) → 0`
giving `|h_k| → |0_α|`.  (Lemma 18.1.8, p. 847) `N` is an auxiliary norm iff for a covering
family the functor `N ∘ Γ̄_Ψ̄ : W_Ψ̄ → [0, ∞]` is one for the strong bundle `W_Ψ̄ → X_Ψ`
(Definition 12.2.1).  (Definitions 18.1.9, 18.1.11 and the paragraph before Theorem 18.1.12,
p. 848) Reflexive `(0, 1)`-fibres and reflexive auxiliary norms are seen in any sc-smooth model;
"the choice of local sc-smooth model does not matter since the notions around auxiliary norms
are well-behaved under generalized strong bundle isomorphisms".  (§18.2, p. 849) `|f|` and the
orbit spaces carry the compactness notions over.

## What is formalized (namespace `Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction`)

* `modelNorm Ψb N` (`N ∘ Γ̄_Ψ̄` on `W_{0,1}`, real valued), `IsAuxNormIn Ψb N` (`N ∘ Γ̄_Ψ̄` is
  `+∞` exactly off `W_{0,1}` and an auxiliary norm of Definition 8.3.5 / 12.2.1 there),
  `IsAuxNormFunctor N` (in every covering model); **independence of the model**
  `IsAuxNormIn.of_comparison` (through `f̄_{Ψ̄,Ψ̄'}` and Proposition 11.5.1) and
  `isAuxNormFunctor_iff_model` (one covering model suffices: the form of Lemma 18.1.8 used here).
* `HasReflexiveFibersIn`, `HasReflexiveFibers` (Definition 18.1.9 in a model, every model),
  `hasReflexiveFibersIn_iff` (independent of the model), `IsReflexiveAuxNormIn`,
  `IsReflexiveAuxNormFunctor` (Definition 18.1.11 in a model, every model),
  `IsReflexiveAuxNormIn.of_comparison`, `isReflexiveAuxNormFunctor_iff_model`.
* `refCoveringFamily` (a covering family from `F̄(α) ≠ ∅`), `pushNormFun` with
  `isAuxNormIn_pushNormFun`: **every model auxiliary norm is `N ∘ Γ̄_Ψ̄` for a functor
  `N : E → [0, ∞]`**; `exists_isAuxNormFunctor`, `exists_isReflexiveAuxNormFunctor` (existence,
  from Theorems 12.2.2 and 12.2.11 in a model, whose orbit space is metrizable).
* `sublevel N f c = {z ∈ |C| | |N| ∘ |f|(z) ≤ c}`, `mem_sublevel_iff`, the transfer
  `auxLe_modelNorm_iff` (`N(f^Ψ̄(x)) ≤ C` in the model iff `N(f(Γ(x))) ≤ C`) and
  `image_auxLe_eq` (`|Γ|(|{x ∈ A | N(f^Ψ̄ x) ≤ C}|) = |Γ|(|A|) ∩ {|N| ∘ |f| ≤ C}`).

## Readings

* Lemma 18.1.8 prints `N : C → [0, ∞]`; we read `N : E → [0, ∞]` (PLAN-18 §4 (2)).  We read
  Definition 18.1.7 through Lemma 18.1.8: `N` is a function on the objects of `E`, constant along
  morphisms (`IsMorInvariant`), and an auxiliary norm in every covering model.  In the model `N`
  takes the value `+∞` exactly off `W_{0,1}` (condition (1) and the finiteness of a norm), and the
  real function `N ∘ Γ̄_Ψ̄` on `W_{0,1}` is an auxiliary norm of Definition 12.2.1.  The direct
  form of Definition 18.1.7 (a topology on `|E_{0,1}|`) and the two variants of Definition 18.1.11
  are not compared here.
* Reflexive `(0, 1)`-fibres and reflexive auxiliary norms are read in the models, as the
  paragraphs after Definition 18.1.9 and before Theorem 18.1.12 do.
* `|N| ∘ |f|(z) ≤ C` with `0 < C < ∞` real is `N(f(α)) ≤ ENNReal.ofReal C` for a representative
  `α` of `z` (any representative, `mem_sublevel_iff`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory
open scoped ENNReal

noncomputable section

namespace Polyfold

universe u

namespace GCT.VectorBundle

open GroupoidalCategory GroupoidalCategory.BanachFunctor

variable {C : GCT.{u}} {V : C.VectorBundle}

/-! ### `|N| ∘ |f|` and its sublevel sets -/

namespace SectionFunctor

variable (f : V.SectionFunctor)

/-- For a functor `N : E → β` and a section functor `f`, `N ∘ f` is constant on isomorphism
classes of `C`. -/
theorem comp_eq_of_isomorphic {β : Type*} {N : V.EObj → β} (hN : IsMorInvariant N)
    {α α' : C.Obj} (h : C.toGroupoidStr.Isomorphic α α') : N (f.toFun α) = N (f.toFun α') := by
  obtain ⟨φ, hs, ht⟩ := h
  have hb : V.base (f.toFun α) = C.toGroupoidStr.src φ := (f.base_toFun α).trans hs.symm
  rw [f.toFun_eq_act hs ht hb]
  exact (hN ⟨(φ, f.toFun α), hb⟩).symm

/-- **The set `{z ∈ |C| | |N| ∘ |f|(z) ≤ c}`** (§18.2, p. 849): the classes of the objects `α`
with `N(f(α)) ≤ c`. -/
def sublevel (N : V.EObj → ℝ≥0∞) (c : ℝ≥0∞) : Set C.toGroupoidStr.OrbitSpace :=
  C.toGroupoidStr.π '' {α | N (f.toFun α) ≤ c}

/-- `|α| ∈ {|N| ∘ |f| ≤ c}` iff `N(f(α)) ≤ c` (for every representative). -/
theorem mem_sublevel_iff {N : V.EObj → ℝ≥0∞} (hN : IsMorInvariant N) (c : ℝ≥0∞) (α : C.Obj) :
    C.toGroupoidStr.π α ∈ f.sublevel N c ↔ N (f.toFun α) ≤ c := by
  constructor
  · rintro ⟨α', hα', he⟩
    rwa [← f.comp_eq_of_isomorphic hN ((GroupoidStr.π_eq_π_iff _).1 he)]
  · exact fun h => ⟨α, h, rfl⟩

theorem sublevel_mono (N : V.EObj → ℝ≥0∞) {c c' : ℝ≥0∞} (h : c ≤ c') :
    f.sublevel N c ⊆ f.sublevel N c' :=
  image_mono fun _ hα => le_trans hα h

end SectionFunctor

namespace StrongPolyfoldBundleConstruction

open StrongBundleUniformizerConstruction StrongBundleUniformizerData PolyfoldConstruction
  SBLocalization EPLocalization

variable {S : C.PolyfoldConstruction} (Q : V.StrongPolyfoldBundleConstruction S) {ι : Type u}
  (Ψb : ι → Q.Unif)

/-! ### Auxiliary norms in a model -/

/-- **`N ∘ Γ̄_Ψ̄` on `W_{0,1}`**, as a real function (the value `+∞` read as `0`; it does not
occur on `W_{0,1}` for an auxiliary norm). -/
def modelNorm (N : V.EObj → ℝ≥0∞) : (Q.modelSEP Ψb).B.One → ℝ :=
  fun k => (Q.bundlePull Ψb N ((Q.modelSEP Ψb).B.oneVal k)).toReal

/-- **`N : E → [0, ∞]` is an auxiliary norm in the model `W_Ψ̄ → X_Ψ`** (Lemma 18.1.8, the
right side, with the reading `N : E → [0, ∞]`): `N` is a functor (constant along morphisms),
`N ∘ Γ̄ = +∞` exactly off `W_{0,1}` (Definition 18.1.7 (1)), and `N ∘ Γ̄` on `W_{0,1}` is an
auxiliary norm of the strong bundle over the ep-groupoid (Definitions 8.3.5, 12.2.1). -/
structure IsAuxNormIn (N : V.EObj → ℝ≥0∞) : Prop where
  isMorInvariant : IsMorInvariant N
  eq_top : ∀ w, w ∉ (Q.modelSEP Ψb).B.oneSet → Q.bundlePull Ψb N w = ⊤
  ne_top : ∀ w ∈ (Q.modelSEP Ψb).B.oneSet, Q.bundlePull Ψb N w ≠ ⊤
  isAuxNorm : (Q.modelSEP Ψb).E.IsAuxNorm (Q.modelNorm Ψb N)

/-- **Auxiliary norm `N : E → [0, ∞]`** (Definition 18.1.7, read through Lemma 18.1.8): `N` is
an auxiliary norm in every covering model.  By `isAuxNormFunctor_iff_model` one covering model
suffices. -/
def IsAuxNormFunctor (N : V.EObj → ℝ≥0∞) : Prop :=
  ∀ c : Q.BundleCoveringFamily, Q.IsAuxNormIn c.Ψ N

/-- `N ∘ Γ̄(w) ≤ ofReal C` iff `w ∈ W_{0,1}` and `N ∘ Γ̄(w) ≤ C` on `W_{0,1}` (`0 ≤ C`). -/
theorem auxLe_iff {N : V.EObj → ℝ≥0∞} (hN : Q.IsAuxNormIn Ψb N) (w : Q.ModelW Ψb) {r : ℝ}
    (hr : 0 ≤ r) :
    (Q.modelSEP Ψb).B.AuxLe (Q.modelNorm Ψb N) w r ↔ Q.bundlePull Ψb N w ≤ ENNReal.ofReal r := by
  constructor
  · rintro ⟨hw, hle⟩
    exact (ENNReal.le_ofReal_iff_toReal_le (hN.ne_top w hw) hr).2 hle
  · intro h
    by_cases hw : w ∈ (Q.modelSEP Ψb).B.oneSet
    · exact ⟨hw, (ENNReal.le_ofReal_iff_toReal_le (hN.ne_top w hw) hr).1 h⟩
    · rw [hN.eq_top w hw, top_le_iff] at h
      exact absurd h ENNReal.ofReal_ne_top

/-! ### Independence of the model -/

variable {Q}

/-- **`Γ̄_Ψ̄'` of the representative of `|f̄_{Ψ̄,Ψ̄'}|(|e|)` is isomorphic to `Γ̄_Ψ̄(e)`**, for
`e ∈ W_{0,1}` (the representative in `|W'[1]|` of Proposition 11.5.1). -/
theorem π_bundleModelObj_oneOrbitMap (c c' : Q.BundleCoveringFamily)
    (e : (Q.modelSEP c.Ψ).B.One) :
    V.groupoid.π (Q.bundleModelObj c'.Ψ ((Q.modelSEP c'.Ψ).B.oneVal
      ((GenSBMap.rep (Q.isGeneralizedIso_bundleComparison c c')).oneOrbitMap
        (Quotient.mk _ e)).out)) =
      V.groupoid.π (Q.bundleModelObj c.Ψ ((Q.modelSEP c.Ψ).B.oneVal e)) := by
  set hF := Q.isGeneralizedIso_bundleComparison c c'
  set D := GenSBMap.rep hF
  have h0 := congrArg (oneToOrbit (SEPLoc.localizationFunctor.obj (Q.modelSEP c'.Ψ)).toSEP)
    (Quotient.out_eq (D.oneOrbitMap (Quotient.mk _ e)))
  have h1 := SDiagram.oneToOrbit_oneOrbitMap D (Quotient.mk _ e)
  have h3 := congrFun (congrArg GenSBMap.orbitMap (GenSBMap.cls_rep hF))
    ((Q.modelSEP c.Ψ).E.toEpGroupoid.π ((Q.modelSEP c.Ψ).B.oneVal e))
  have h2 := congrFun (Q.orbitMap_bundleComparison c c')
    ((Q.modelSEP c.Ψ).E.toEpGroupoid.π ((Q.modelSEP c.Ψ).B.oneVal e))
  exact (congrArg (Q.bundleModelFunctor c'.Ψ).orbitMap ((h0.trans h1).trans h3)).trans h2

/-- **`N ∘ Γ̄_Ψ̄ = [f̄_{Ψ̄,Ψ̄'}]^*(N ∘ Γ̄_Ψ̄')` on `W_{0,1}`** (the pull-back of Proposition 11.5.1
along the comparison map of Theorem 17.1.18, bundle form). -/
theorem modelNorm_eq_pullNorm {N : V.EObj → ℝ≥0∞} (hN : IsMorInvariant N)
    (c c' : Q.BundleCoveringFamily) :
    Q.modelNorm c.Ψ N =
      GenSBMap.pullNorm (Q.isGeneralizedIso_bundleComparison c c') (Q.modelNorm c'.Ψ N) := by
  funext e
  change (N (Q.bundleModelObj c.Ψ ((Q.modelSEP c.Ψ).B.oneVal e))).toReal =
    (N (Q.bundleModelObj c'.Ψ ((Q.modelSEP c'.Ψ).B.oneVal
      ((GenSBMap.rep (Q.isGeneralizedIso_bundleComparison c c')).oneOrbitMap
        (Quotient.mk _ e)).out))).toReal
  rw [hN.eq_of_isomorphic ((GroupoidStr.π_eq_π_iff _).1 (π_bundleModelObj_oneOrbitMap c c' e))]

/-- `Γ̄_Ψ̄` reflects isomorphism: `Γ̄(w) ≅ Γ̄(w')` gives `w ≅ w'` (covering family). -/
theorem isomorphic_of_bundleModelObj (c : Q.BundleCoveringFamily) {w w' : Q.ModelW c.Ψ}
    (h : V.groupoid.π (Q.bundleModelObj c.Ψ w) = V.groupoid.π (Q.bundleModelObj c.Ψ w')) :
    (Q.modelSEP c.Ψ).E.toEpGroupoid.π w = (Q.modelSEP c.Ψ).E.toEpGroupoid.π w' :=
  (isHomeomorph_bundleModelOrbitMap c.cover).injective h

/-- `W_{0,1}` is saturated: `w ≅ w'` and `w' ∈ W_{0,1}` give `w ∈ W_{0,1}`. -/
theorem mem_oneSet_of_π_eq {A : SEP.{u}} {w w' : A.W}
    (h : A.E.toEpGroupoid.π w = A.E.toEpGroupoid.π w') (hw' : w' ∈ A.B.oneSet) :
    w ∈ A.B.oneSet := by
  obtain ⟨ψ, hs, ht⟩ := (GroupoidStr.π_eq_π_iff _).1 h
  have hs' : (ψ : A.Mor × A.W).2 = w := hs
  have ht' : A.E.μ ψ = w' := ht
  rw [← hs']
  exact A.E.mem_oneSet_of_mor ψ (ht' ▸ hw')

/-- For `w ∈ W_Ψ̄` there is `w' ∈ W_Ψ̄'` with `Γ̄'(w') ≅ Γ̄(w)` (`Γ̄'` is essentially
surjective). -/
theorem exists_bundleModelObj_iso (c c' : Q.BundleCoveringFamily) (w : Q.ModelW c.Ψ) :
    ∃ w' : Q.ModelW c'.Ψ,
      V.groupoid.π (Q.bundleModelObj c'.Ψ w') = V.groupoid.π (Q.bundleModelObj c.Ψ w) := by
  obtain ⟨z, hz⟩ := (isHomeomorph_bundleModelOrbitMap c'.cover).surjective
    (V.groupoid.π (Q.bundleModelObj c.Ψ w))
  induction z using Quotient.inductionOn with | h w' => exact ⟨w', hz⟩

/-- **The membership in `W_{0,1}` is independent of the model**: if `Γ̄'(w') ≅ Γ̄(w)`, then
`w' ∈ W'_{0,1}` iff `w ∈ W_{0,1}`. -/
theorem mem_oneSet_iff_of_iso (c c' : Q.BundleCoveringFamily) {w : Q.ModelW c.Ψ}
    {w' : Q.ModelW c'.Ψ}
    (h : V.groupoid.π (Q.bundleModelObj c'.Ψ w') = V.groupoid.π (Q.bundleModelObj c.Ψ w)) :
    w' ∈ (Q.modelSEP c'.Ψ).B.oneSet ↔ w ∈ (Q.modelSEP c.Ψ).B.oneSet := by
  have key : ∀ (c c' : Q.BundleCoveringFamily) {w : Q.ModelW c.Ψ} {w' : Q.ModelW c'.Ψ},
      V.groupoid.π (Q.bundleModelObj c'.Ψ w') = V.groupoid.π (Q.bundleModelObj c.Ψ w) →
      w ∈ (Q.modelSEP c.Ψ).B.oneSet → w' ∈ (Q.modelSEP c'.Ψ).B.oneSet := by
    intro c c' w w' h hw
    set e : (Q.modelSEP c.Ψ).B.One := (Q.modelSEP c.Ψ).B.oneMk w hw
    have h1 := π_bundleModelObj_oneOrbitMap c c' e
    have h2 : V.groupoid.π (Q.bundleModelObj c'.Ψ w') = V.groupoid.π (Q.bundleModelObj c'.Ψ
        ((Q.modelSEP c'.Ψ).B.oneVal ((GenSBMap.rep (Q.isGeneralizedIso_bundleComparison c c')
          ).oneOrbitMap (Quotient.mk _ e)).out)) := h.trans h1.symm
    exact mem_oneSet_of_π_eq (isomorphic_of_bundleModelObj c' h2) ((Q.modelSEP c'.Ψ).B.oneVal_mem _)
  exact ⟨fun hw' => key c' c h.symm hw', fun hw => key c c' h hw⟩

/-- **Independence of the model** (Lemma 18.1.8 for two covering families): if `N` is an
auxiliary norm in the model `W_Ψ̄'`, it is one in `W_Ψ̄` (Proposition 11.5.1 for the generalized
strong bundle isomorphism `f̄_{Ψ̄,Ψ̄'}`, and the independence of `W_{0,1}`). -/
theorem IsAuxNormIn.of_comparison {N : V.EObj → ℝ≥0∞} (c c' : Q.BundleCoveringFamily)
    (h : Q.IsAuxNormIn c'.Ψ N) : Q.IsAuxNormIn c.Ψ N := by
  have hval : ∀ w : Q.ModelW c.Ψ, ∃ w' : Q.ModelW c'.Ψ,
      (w' ∈ (Q.modelSEP c'.Ψ).B.oneSet ↔ w ∈ (Q.modelSEP c.Ψ).B.oneSet) ∧
        Q.bundlePull c'.Ψ N w' = Q.bundlePull c.Ψ N w := by
    intro w
    obtain ⟨w', hw'⟩ := exists_bundleModelObj_iso c c' w
    exact ⟨w', mem_oneSet_iff_of_iso c c' hw',
      h.isMorInvariant.eq_of_isomorphic ((GroupoidStr.π_eq_π_iff _).1 hw')⟩
  refine ⟨h.isMorInvariant, fun w hw => ?_, fun w hw => ?_, ?_⟩
  · obtain ⟨w', hmem, he⟩ := hval w
    rw [← he]
    exact h.eq_top w' fun h' => hw (hmem.1 h')
  · obtain ⟨w', hmem, he⟩ := hval w
    rw [← he]
    exact h.ne_top w' (hmem.2 hw)
  · rw [modelNorm_eq_pullNorm h.isMorInvariant c c']
    exact GenSBMap.isAuxNorm_pullNorm _ h.isAuxNorm

variable (Q)

/-- **One covering model suffices** (the form of Lemma 18.1.8 used here): `N` is an auxiliary
norm (in every covering model) iff it is one in the model of a single covering family. -/
theorem isAuxNormFunctor_iff_model {N : V.EObj → ℝ≥0∞} (c : Q.BundleCoveringFamily) :
    Q.IsAuxNormFunctor N ↔ Q.IsAuxNormIn c.Ψ N :=
  ⟨fun h => h c, fun h c' => IsAuxNormIn.of_comparison c' c h⟩

/-! ### Reflexive fibres and reflexive auxiliary norms -/

/-- **Reflexive `(0, 1)`-fibres in the model `W_Ψ̄ → X_Ψ`** (Definition 18.1.9 read in a model,
as the paragraph after it does; Definition 5.1.4 for the object bundle). -/
def HasReflexiveFibersIn : Prop := (Q.modelSEP Ψb).B.HasReflexiveFibers

/-- **Reflexive `(0, 1)`-fibres** (Definition 18.1.9, read in the models): every covering model
has reflexive `(0, 1)`-fibres (`hasReflexiveFibersIn_iff`: one suffices). -/
def HasReflexiveFibers : Prop := ∀ c : Q.BundleCoveringFamily, Q.HasReflexiveFibersIn c.Ψ

variable {Q} in
/-- **Reflexive fibres do not depend on the model** (generalized strong bundle isomorphism
`f̄_{Ψ̄,Ψ̄'}`). -/
theorem hasReflexiveFibersIn_iff (c c' : Q.BundleCoveringFamily) :
    Q.HasReflexiveFibersIn c.Ψ ↔ Q.HasReflexiveFibersIn c'.Ψ :=
  GenSBMap.hasReflexiveFibers_iff (Q.isGeneralizedIso_bundleComparison c c')

theorem hasReflexiveFibers_iff_model (c : Q.BundleCoveringFamily) :
    Q.HasReflexiveFibers ↔ Q.HasReflexiveFibersIn c.Ψ :=
  ⟨fun h => h c, fun h c' => (hasReflexiveFibersIn_iff c' c).2 h⟩

/-- **`N` is a reflexive auxiliary norm in the model** (Definition 18.1.11 read in a model, as the
paragraph before Theorem 18.1.12 does): an auxiliary norm in the model whose `N ∘ Γ̄` is a
reflexive auxiliary norm of Definition 12.2.10. -/
structure IsReflexiveAuxNormIn (N : V.EObj → ℝ≥0∞) : Prop extends Q.IsAuxNormIn Ψb N where
  isReflexive : (Q.modelSEP Ψb).E.IsReflexiveAuxNorm (Q.modelNorm Ψb N)

/-- **Reflexive auxiliary norm `N : E → [0, ∞]`** (Definition 18.1.11, read in the models): a
reflexive auxiliary norm in every covering model. -/
def IsReflexiveAuxNormFunctor (N : V.EObj → ℝ≥0∞) : Prop :=
  ∀ c : Q.BundleCoveringFamily, Q.IsReflexiveAuxNormIn c.Ψ N

theorem IsReflexiveAuxNormFunctor.isAuxNormFunctor {N : V.EObj → ℝ≥0∞}
    (h : Q.IsReflexiveAuxNormFunctor N) : Q.IsAuxNormFunctor N :=
  fun c => (h c).toIsAuxNormIn

variable {Q} in
/-- **Reflexivity does not depend on the model** (Proposition 11.5.1 with Definition 12.2.10). -/
theorem IsReflexiveAuxNormIn.of_comparison {N : V.EObj → ℝ≥0∞} (c c' : Q.BundleCoveringFamily)
    (hB : Q.HasReflexiveFibersIn c'.Ψ) (h : Q.IsReflexiveAuxNormIn c'.Ψ N) :
    Q.IsReflexiveAuxNormIn c.Ψ N := by
  refine ⟨IsAuxNormIn.of_comparison c c' h.toIsAuxNormIn, ?_⟩
  rw [modelNorm_eq_pullNorm h.isMorInvariant c c']
  exact GenSBMap.isReflexiveAuxNorm_pullNorm _ hB h.isReflexive

/-- One covering model with reflexive fibres suffices for a reflexive auxiliary norm. -/
theorem isReflexiveAuxNormFunctor_iff_model {N : V.EObj → ℝ≥0∞} (c : Q.BundleCoveringFamily)
    (hB : Q.HasReflexiveFibersIn c.Ψ) :
    Q.IsReflexiveAuxNormFunctor N ↔ Q.IsReflexiveAuxNormIn c.Ψ N :=
  ⟨fun h => h c, fun h c' => IsReflexiveAuxNormIn.of_comparison c' c hB h⟩

/-! ### A covering family, and auxiliary norms from the models -/

/-- **A covering family of strong bundle uniformizers** from `F̄(α) ≠ ∅`: one `Ψ̄_α ∈ F̄(α)` for
every object `α`. -/
def refCoveringFamily (hF : Q.HasStrongBundleUniformizers) : Q.BundleCoveringFamily where
  ι := C.Obj
  Ψ α := Q.refBundleUnif (hF α)
  cover := by
    refine eq_univ_of_forall fun z => ?_
    obtain ⟨α, rfl⟩ := Quotient.exists_rep z
    refine mem_iUnion.2 ⟨α, (Q.baseUnif (Q.refBundleUnif (hF α))).1.mem_footprint_iff.2
      ⟨pointOf (Ψ := Q.baseUnif (Q.refBundleUnif (hF α)))
        (Q.base_mem α _ (Q.refBundleUnif_mem (hF α))), ?_⟩⟩
    rw [obj_pointOf]
    rfl

open Classical in
/-- The function `w ↦ N'(w)` on `W_{0,1}`, `+∞` off `W_{0,1}`, for an invariant `N'`. -/
def extendNorm (N' : (Q.modelSEP Ψb).B.One → ℝ) (w : (Q.modelSEP Ψb).W) : ℝ≥0∞ :=
  if hw : w ∈ (Q.modelSEP Ψb).B.oneSet then ENNReal.ofReal (N' ((Q.modelSEP Ψb).B.oneMk w hw))
  else ⊤

theorem extendNorm_of_mem {N' : (Q.modelSEP Ψb).B.One → ℝ} {w : (Q.modelSEP Ψb).W}
    (hw : w ∈ (Q.modelSEP Ψb).B.oneSet) :
    Q.extendNorm Ψb N' w = ENNReal.ofReal (N' ((Q.modelSEP Ψb).B.oneMk w hw)) := by
  classical
  exact dif_pos hw

theorem extendNorm_of_not_mem {N' : (Q.modelSEP Ψb).B.One → ℝ} {w : (Q.modelSEP Ψb).W}
    (hw : w ∉ (Q.modelSEP Ψb).B.oneSet) : Q.extendNorm Ψb N' w = ⊤ := by
  classical
  exact dif_neg hw

theorem extendNorm_oneVal (N' : (Q.modelSEP Ψb).B.One → ℝ) (k : (Q.modelSEP Ψb).B.One) :
    Q.extendNorm Ψb N' ((Q.modelSEP Ψb).B.oneVal k) = ENNReal.ofReal (N' k) :=
  Q.extendNorm_of_mem Ψb ((Q.modelSEP Ψb).B.oneVal_mem k)

theorem extendNorm_eq_of_π_eq {N' : (Q.modelSEP Ψb).B.One → ℝ}
    (hN' : IsOneInvariant (Q.modelSEP Ψb) N') {w w' : (Q.modelSEP Ψb).W}
    (h : (Q.modelSEP Ψb).E.toEpGroupoid.π w = (Q.modelSEP Ψb).E.toEpGroupoid.π w') :
    Q.extendNorm Ψb N' w = Q.extendNorm Ψb N' w' := by
  by_cases hw : w ∈ (Q.modelSEP Ψb).B.oneSet
  · have hw' : w' ∈ (Q.modelSEP Ψb).B.oneSet := mem_oneSet_of_π_eq h.symm hw
    rw [Q.extendNorm_of_mem Ψb hw, Q.extendNorm_of_mem Ψb hw',
      hN' ((Q.modelSEP Ψb).B.oneMk w hw) ((Q.modelSEP Ψb).B.oneMk w' hw') h]
  · have hw' : w' ∉ (Q.modelSEP Ψb).B.oneSet := fun hw' => hw (mem_oneSet_of_π_eq h hw')
    rw [Q.extendNorm_of_not_mem Ψb hw, Q.extendNorm_of_not_mem Ψb hw']

variable {Q Ψb}

/-- **The push-forward `Γ̄_* n` of an invariant function on `W_{0,1}`** (the paragraph before
Theorem 18.1.12): the functor `N : E → [0, ∞]` with `N ∘ Γ̄ = n` on `W_{0,1}` and `+∞` off it. -/
def pushNormFun (h : S.IsCoveringFamily (Q.modelBase Ψb)) (N' : (Q.modelSEP Ψb).B.One → ℝ)
    (hN' : IsOneInvariant (Q.modelSEP Ψb) N') : V.EObj → ℝ≥0∞ :=
  Q.bundlePush h (Q.extendNorm Ψb N') fun _ _ hw =>
    Q.extendNorm_eq_of_π_eq Ψb hN' (Quotient.sound hw)

theorem bundlePull_pushNormFun (h : S.IsCoveringFamily (Q.modelBase Ψb))
    (N' : (Q.modelSEP Ψb).B.One → ℝ) (hN' : IsOneInvariant (Q.modelSEP Ψb) N') :
    Q.bundlePull Ψb (pushNormFun h N' hN') = Q.extendNorm Ψb N' :=
  Q.bundlePull_bundlePush h _ _

theorem modelNorm_pushNormFun (h : S.IsCoveringFamily (Q.modelBase Ψb))
    {N' : (Q.modelSEP Ψb).B.One → ℝ} (hN' : (Q.modelSEP Ψb).E.IsAuxNorm N') :
    Q.modelNorm Ψb (pushNormFun h N' hN'.isOneInvariant) = N' := by
  funext k
  change (Q.bundlePull Ψb (pushNormFun h N' hN'.isOneInvariant)
    ((Q.modelSEP Ψb).B.oneVal k)).toReal = N' k
  rw [bundlePull_pushNormFun, Q.extendNorm_oneVal, ENNReal.toReal_ofReal (hN'.isAuxNorm.nonneg k)]

/-- **The push-forward of an auxiliary norm of the model is an auxiliary norm in the model**
(the paragraph before Theorem 18.1.12: "given an auxiliary norm `n` for `p`, the push-forward
`N := Γ̄_* n` is an auxiliary norm for `P`"). -/
theorem isAuxNormIn_pushNormFun (h : S.IsCoveringFamily (Q.modelBase Ψb))
    {N' : (Q.modelSEP Ψb).B.One → ℝ} (hN' : (Q.modelSEP Ψb).E.IsAuxNorm N') :
    Q.IsAuxNormIn Ψb (pushNormFun h N' hN'.isOneInvariant) := by
  have hpull := bundlePull_pushNormFun h N' hN'.isOneInvariant
  refine ⟨Q.isMorInvariant_bundlePush h _ _, fun w hw => ?_, fun w hw => ?_, ?_⟩
  · rw [hpull]; exact Q.extendNorm_of_not_mem Ψb hw
  · rw [hpull, Q.extendNorm_of_mem Ψb hw]; exact ENNReal.ofReal_ne_top
  · rw [modelNorm_pushNormFun h hN']; exact hN'

theorem isReflexiveAuxNormIn_pushNormFun (h : S.IsCoveringFamily (Q.modelBase Ψb))
    {N' : (Q.modelSEP Ψb).B.One → ℝ} (hN' : (Q.modelSEP Ψb).E.IsReflexiveAuxNorm N') :
    Q.IsReflexiveAuxNormIn Ψb (pushNormFun h N' hN'.toIsAuxNorm.isOneInvariant) :=
  ⟨isAuxNormIn_pushNormFun h hN'.toIsAuxNorm, by
    rw [modelNorm_pushNormFun h hN'.toIsAuxNorm]; exact hN'⟩

/-- The orbit space of a covering model is paracompact (it is homeomorphic to the metrizable
`|C|`). -/
theorem hasParacompactOrbitSpace_model (c : Q.BundleCoveringFamily) :
    (Q.modelSEP c.Ψ).X.HasParacompactOrbitSpace := by
  have := metrizableSpace_modelOrbitSpace_of_family (S := S) (Ψ := Q.modelBase c.Ψ)
  let _ := TopologicalSpace.metrizableSpaceMetric (S.modelEP (Q.modelBase c.Ψ)).X.OrbitSpace
  exact (inferInstance : ParacompactSpace (S.modelEP (Q.modelBase c.Ψ)).X.OrbitSpace)

variable (Q)

/-- **An auxiliary norm `N : E → [0, ∞]` exists** (Theorem 18.1.12 (1) in the model reading:
Theorem 12.2.2 in a covering model, pushed forward), when `F̄(α) ≠ ∅` for every `α`. -/
theorem exists_isAuxNormFunctor (hF : Q.HasStrongBundleUniformizers) :
    ∃ N : V.EObj → ℝ≥0∞, Q.IsAuxNormFunctor N := by
  set c := Q.refCoveringFamily hF
  obtain ⟨N', hN'⟩ := (Q.modelSEP c.Ψ).E.theorem_12_2_2 (hasParacompactOrbitSpace_model c)
  exact ⟨_, (Q.isAuxNormFunctor_iff_model c).2 (isAuxNormIn_pushNormFun c.cover hN')⟩

/-- **A reflexive auxiliary norm exists** for reflexive fibres (Theorem 12.2.11 in a covering
model, pushed forward). -/
theorem exists_isReflexiveAuxNormFunctor (hF : Q.HasStrongBundleUniformizers)
    (hB : Q.HasReflexiveFibers) : ∃ N : V.EObj → ℝ≥0∞, Q.IsReflexiveAuxNormFunctor N := by
  set c := Q.refCoveringFamily hF
  obtain ⟨N', hN'⟩ :=
    (Q.modelSEP c.Ψ).E.theorem_12_2_11_exists (hasParacompactOrbitSpace_model c) (hB c)
  exact ⟨_, (Q.isReflexiveAuxNormFunctor_iff_model c (hB c)).2
    (isReflexiveAuxNormIn_pushNormFun c.cover hN')⟩

/-! ### `|N| ∘ |f|` in the model -/

variable (f : V.SectionFunctor)

/-- `N(Γ̄(f^Ψ̄(x))) = N(f(Γ(x)))`. -/
theorem bundlePull_modelSection (N : V.EObj → ℝ≥0∞) (x : S.ModelObj (Q.modelBase Ψb)) :
    Q.bundlePull Ψb N (Q.modelSection Ψb f x) =
      N (f.toFun ((S.modelFunctor (Q.modelBase Ψb)).obj x)) :=
  congrArg N (Q.bundleModelFunctor_obj_modelSection Ψb f x)

variable {Q f}

/-- **`N(f^Ψ̄(x)) ≤ C` in the model iff `N(f(Γ(x))) ≤ C`** (`0 ≤ C`). -/
theorem auxLe_modelNorm_iff {N : V.EObj → ℝ≥0∞} (hN : Q.IsAuxNormIn Ψb N)
    (x : S.ModelObj (Q.modelBase Ψb)) {r : ℝ} (hr : 0 ≤ r) :
    (Q.modelSEP Ψb).B.AuxLe (Q.modelNorm Ψb N) (Q.modelSection Ψb f x) r ↔
      N (f.toFun ((S.modelFunctor (Q.modelBase Ψb)).obj x)) ≤ ENNReal.ofReal r := by
  rw [Q.auxLe_iff Ψb hN _ hr, Q.bundlePull_modelSection]

/-- **`|Γ|(|{x ∈ A | N(f^Ψ̄(x)) ≤ C}|) = |Γ|(|A|) ∩ {|N| ∘ |f| ≤ C}`** for every set `A` of
objects of `X_Ψ` (`0 ≤ C`). -/
theorem image_auxLe_eq {N : V.EObj → ℝ≥0∞} (hN : Q.IsAuxNormIn Ψb N)
    (A : Set (S.ModelObj (Q.modelBase Ψb))) {r : ℝ} (hr : 0 ≤ r) :
    (S.modelFunctor (Q.modelBase Ψb)).orbitMap '' ((Q.modelSEP Ψb).X.π ''
        {x ∈ A | (Q.modelSEP Ψb).B.AuxLe (Q.modelNorm Ψb N) (Q.modelSection Ψb f x) r}) =
      (S.modelFunctor (Q.modelBase Ψb)).orbitMap '' ((Q.modelSEP Ψb).X.π '' A) ∩
        f.sublevel N (ENNReal.ofReal r) := by
  ext z
  constructor
  · rintro ⟨_, ⟨x, ⟨hxA, hx⟩, rfl⟩, rfl⟩
    exact ⟨⟨_, ⟨x, hxA, rfl⟩, rfl⟩,
      (f.mem_sublevel_iff hN.isMorInvariant _ _).2 ((auxLe_modelNorm_iff hN x hr).1 hx)⟩
  · rintro ⟨⟨_, ⟨x, hxA, rfl⟩, rfl⟩, hz⟩
    exact ⟨_, ⟨x, ⟨hxA, (auxLe_modelNorm_iff hN x hr).2
      ((f.mem_sublevel_iff hN.isMorInvariant _ _).1 hz)⟩, rfl⟩, rfl⟩

end StrongPolyfoldBundleConstruction

end GCT.VectorBundle

end Polyfold
