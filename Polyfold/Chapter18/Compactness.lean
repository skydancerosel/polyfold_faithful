import Polyfold.Chapter18.AuxiliaryNorms

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 18,
§18.2 "Compactness Properties", pp. 849–851: **Definition 18.2.1, Theorem 18.2.2,
Definition 18.2.3 and the observation after it, Definition 18.2.4, Remark 18.2.5,
Theorem 18.2.6** (Remark 18.2.7 is commentary without a claim).  Numbers and pages are the 2021
text's.

## The text, paraphrased

(p. 849) For an sc-Fredholm section functor `f` of `P : E → C` and an sc-smooth model
`p : W → X`, `|Γ|` and `|Γ̄|` are homeomorphisms and `|f| = |Γ̄| ∘ |f^Ψ̄_Ψ| ∘ |Γ|⁻¹` (18.3), which
carries the compactness notions of §12.4 over.  `S_f` is the full subcategory of the objects with
`f(α) = 0`.  (Definition 18.2.1) `f` defines a compact moduli space if `|S_f|` is compact; `f` is
proper if moreover for every auxiliary norm `N` there is an open neighbourhood `U` of `|S_f|`
with `{x ∈ U | |N| ∘ |f|(x) ≤ 1}` of compact closure in `|C|`; proper`<∞` if one `U` works for
every `0 < C < ∞`.  (Theorem 18.2.2) For sc-Fredholm `f` the three are equivalent (from Theorem
12.4.2).  (Definition 18.2.3) `(N, U)` controls compactness if `cl_{|C|}{z ∈ U | |N| ∘ |f|(z) ≤ 1}`
is compact, strongly controls compactness if this holds for every `0 < C < ∞`; "(N, U) controls
compactness for a suitable `U`" is equivalent to "(N, U') strongly controls compactness for some
`U'`".  (Definition 18.2.4) With reflexive `(0, 1)`-fibres, `f` has the categorical reflexive
local compactness property if for every reflexive auxiliary norm `N` and every `z ∈ |C|` there is
an open `U(z) ∋ z` with `cl{y ∈ U(z) | |N| ∘ |f|(y) ≤ 1}` compact.  (Remark 18.2.5) For
`z ∈ |C|₀ ∖ |C|₁`, `|N| ∘ |f|(z) = +∞` (regularizing), and the lower semicontinuity gives `U(z)`
with `|N| ∘ |f| > 1` on it, so the set is empty.  (Theorem 18.2.6) Over a tame `C` with reflexive
fibres, `N` reflexive, `f` with compact moduli space and reflexive local compactness, and `U_∂` an
open neighbourhood in `|∂C|` of `|S_{∂f}|` with `cl_{|C|}{z ∈ U_∂ | |N| ∘ |f|(z) ≤ 1}` compact:
there is an open `U ⊇ |S_f|` with `U ∩ |∂C| = U_∂` such that `(N, U)` controls compactness (from
Theorem 12.4.6).

## What is formalized

* **Definition 18.2.1**: `SectionFunctor.HasCompactModuliSpace` (1),
  `StrongPolyfoldBundleConstruction.IsProper` (2), `IsProperLtInfty` (3).
* The model transfer: `isOpen_modelImage`, `isCompact_closure_modelImage_iff`
  (`cl_{|C|}(|Γ|(|A|) ∩ {|N| ∘ |f| ≤ C})` compact iff `cl_{|X|}(|{x ∈ A | N(f^Ψ̄(x)) ≤ C}|)` is),
  `isProperLtInfty_of_model`.
* **Theorem 18.2.2**: `theorem_18_2_2` (`TFAE`), from Theorem 12.4.2 in a covering model.
* **Definition 18.2.3**: `SectionFunctor.ControlsCompactness`, `StronglyControlsCompactness`;
  **the observation**: `definition_18_2_3_observation`, with the sharper
  `exists_stronglyControlsCompactness_subset` (inside every open neighbourhood of `|S_f|`).
* **Definition 18.2.4**: `HasReflexiveLocalCompactness`.
* **Remark 18.2.5**: `remark_18_2_5`.
* **Theorem 18.2.6**: `theorem_18_2_6` (from `theorem_12_4_6_of_continuous` in a covering model),
  with `mem_boundary_model_iff` (`x ∈ ∂X` iff `|Γ(x)| ∈ |∂C|`).

## Readings

* Auxiliary norms and reflexive auxiliary norms are those of `AuxiliaryNorms.lean` (read through
  the models, Lemma 18.1.8); Definition 18.2.4 and Theorem 18.2.6 print `N : C → [0, ∞]`, read
  `N : E → [0, ∞]` (PLAN-18 §4 (2)).  Reflexive `(0, 1)`-fibres are read in the models.
* The standing reading `F̄(α) ≠ ∅` for every `α` (`HasStrongBundleUniformizers`, as in
  `FredholmSectionFunctors.lean`) provides a covering family of strong bundle uniformizers
  (`refCoveringFamily`).
* `|S_f| = π(S_f) ⊆ |C|`; "`{x ∈ U | |N| ∘ |f|(x) ≤ C}`" is `U ∩ f.sublevel N C`.
* Definition 18.2.3: the open neighbourhood `U ⊇ |S_f|` is part of the definitions.
* Remark 18.2.5: "Using the reflexive local compactness property" — the argument printed uses
  only the lower semicontinuity of `|N| ∘ |f|` (the reflexivity of `N`) and the regularizing
  property; `remark_18_2_5` has no local compactness hypothesis.  `z ∈ |C|₀ ∖ |C|₁` is read as
  `¬ HasRegularity 1 α` for a representative `α`.
* Theorem 18.2.6: `∂f := f|∂C` and `S_{∂f}` are read as `S_f ∩ ∂C` (Definition 17.1.30);
  "`U_∂ ⊂ |∂C|` open" as `U_∂ = W' ∩ |∂C|` with `W'` open in `|C|` (as in Theorem 12.4.6).
  Tameness of `C` is kept as in the text and not used (as for Theorem 12.4.6).
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

namespace SectionFunctor

variable (f : V.SectionFunctor)

/-- `S_f` is saturated: an object isomorphic to a solution object is one. -/
theorem mem_zeroSet_of_isomorphic {α β : C.Obj} (h : C.toGroupoidStr.Isomorphic α β)
    (hα : α ∈ f.zeroSet) : β ∈ f.zeroSet := by
  obtain ⟨φ, hs, ht⟩ := h
  have hb : V.base (f.toFun α) = C.toGroupoidStr.src φ := (f.base_toFun α).trans hs.symm
  have hα' : f.toFun α = V.objMk α 0 := hα
  change f.toFun β = V.objMk β 0
  rw [f.toFun_eq_act hs ht hb, act_congr rfl hα' hb (by rw [← hs]), act_objMk_zero hs, ht]

/-- **Definition 18.2.1 (1), p. 849**: `f` defines a **compact moduli space**: the coarse
moduli space `|S_f| = π(S_f) ⊆ |C|` is compact. -/
def HasCompactModuliSpace : Prop := IsCompact (C.toGroupoidStr.π '' f.zeroSet)

/-- **Definition 18.2.3, p. 850**: for an open neighbourhood `U` of `|S_f|`, **`(N, U)` controls
compactness** for `f`: `cl_{|C|}{z ∈ U | |N| ∘ |f|(z) ≤ 1}` is compact. -/
def ControlsCompactness (N : V.EObj → ℝ≥0∞) (U : Set C.toGroupoidStr.OrbitSpace) : Prop :=
  IsOpen U ∧ C.toGroupoidStr.π '' f.zeroSet ⊆ U ∧ IsCompact (closure (U ∩ f.sublevel N 1))

/-- **Definition 18.2.3, p. 850**: **`(N, U)` strongly controls compactness**: for every
`0 < C < ∞` the closure of `{z ∈ U | |N| ∘ |f|(z) ≤ C}` in `|C|` is compact. -/
def StronglyControlsCompactness (N : V.EObj → ℝ≥0∞) (U : Set C.toGroupoidStr.OrbitSpace) :
    Prop :=
  IsOpen U ∧ C.toGroupoidStr.π '' f.zeroSet ⊆ U ∧
    ∀ r : ℝ, 0 < r → IsCompact (closure (U ∩ f.sublevel N (ENNReal.ofReal r)))

variable {f} in
theorem StronglyControlsCompactness.controlsCompactness {N : V.EObj → ℝ≥0∞}
    {U : Set C.toGroupoidStr.OrbitSpace} (h : f.StronglyControlsCompactness N U) :
    f.ControlsCompactness N U := by
  refine ⟨h.1, h.2.1, ?_⟩
  have := h.2.2 1 one_pos
  rwa [ENNReal.ofReal_one] at this

end SectionFunctor

namespace StrongPolyfoldBundleConstruction

open StrongBundleUniformizerConstruction StrongBundleUniformizerData PolyfoldConstruction
  SBLocalization EPLocalization

variable {S : C.PolyfoldConstruction} (Q : V.StrongPolyfoldBundleConstruction S)
  (f : V.SectionFunctor)

/-! ### Definition 18.2.1 -/

/-- **Definition 18.2.1 (2), p. 849**: `f` is **proper**: `|S_f|` is compact and for every
auxiliary norm `N` there is an open neighbourhood `U` of `|S_f|` such that
`{x ∈ U | |N| ∘ |f|(x) ≤ 1}` has compact closure in `|C|`. -/
def IsProper : Prop :=
  f.HasCompactModuliSpace ∧ ∀ N : V.EObj → ℝ≥0∞, Q.IsAuxNormFunctor N →
    ∃ U : Set C.toGroupoidStr.OrbitSpace, IsOpen U ∧ C.toGroupoidStr.π '' f.zeroSet ⊆ U ∧
      IsCompact (closure (U ∩ f.sublevel N 1))

/-- **Definition 18.2.1 (3), pp. 849–850**: `f` is **proper`<∞`**: `|S_f|` is compact and for
every auxiliary norm `N` there is an open neighbourhood `U` of `|S_f|` such that for every
`0 < C < ∞` the set `{x ∈ U | |N| ∘ |f|(x) ≤ C}` has compact closure in `|C|`. -/
def IsProperLtInfty : Prop :=
  f.HasCompactModuliSpace ∧ ∀ N : V.EObj → ℝ≥0∞, Q.IsAuxNormFunctor N →
    ∃ U : Set C.toGroupoidStr.OrbitSpace, IsOpen U ∧ C.toGroupoidStr.π '' f.zeroSet ⊆ U ∧
      ∀ r : ℝ, 0 < r → IsCompact (closure (U ∩ f.sublevel N (ENNReal.ofReal r)))

/-! ### Transfer from a covering model -/

variable {Q f}

/-- `|Γ|(|U|)` is open in `|C|` for `U` open in `X_Ψ`. -/
theorem isOpen_modelImage (c : Q.BundleCoveringFamily)
    {U : Set (S.ModelObj (Q.modelBase c.Ψ))} (hU : IsOpen U) :
    IsOpen ((S.modelFunctor (Q.modelBase c.Ψ)).orbitMap '' ((Q.modelSEP c.Ψ).X.π '' U)) :=
  (isHomeomorph_modelOrbitMap c.cover).isOpenMap _ ((Q.modelSEP c.Ψ).X.proposition_7_1_8 U hU)

/-- **Compactness transfers through the model** (18.3):
`cl_{|C|}(|Γ|(|A|) ∩ {|N| ∘ |f| ≤ C})` is compact iff `cl_{|X|}(|{x ∈ A | N(f^Ψ̄(x)) ≤ C}|)` is
(`|Γ|` is a homeomorphism, Lemma 17.1.15). -/
theorem isCompact_closure_modelImage_iff (c : Q.BundleCoveringFamily) {N : V.EObj → ℝ≥0∞}
    (hN : Q.IsAuxNormIn c.Ψ N) (A : Set (S.ModelObj (Q.modelBase c.Ψ))) {r : ℝ} (hr : 0 ≤ r) :
    IsCompact (closure ((S.modelFunctor (Q.modelBase c.Ψ)).orbitMap ''
        ((Q.modelSEP c.Ψ).X.π '' A) ∩ f.sublevel N (ENNReal.ofReal r))) ↔
      IsCompact (closure ((Q.modelSEP c.Ψ).X.π '' {x ∈ A | (Q.modelSEP c.Ψ).B.AuxLe
        (Q.modelNorm c.Ψ N) (Q.modelSection c.Ψ f x) r})) := by
  rw [← image_auxLe_eq hN A hr]
  set H := (isHomeomorph_modelOrbitMap c.cover).homeomorph
  change IsCompact (closure (H '' _)) ↔ _
  rw [← H.image_closure, H.isCompact_image]
  exact Iff.rfl

variable (Q f) in
/-- The model section of a covering family, sc-Fredholm when `f` is (Remark 18.1.2 (a)). -/
theorem modelSection_isScFredholm (c : Q.BundleCoveringFamily)
    (hf : Q.IsScFredholmSectionFunctor f) :
    (Q.modelSEP c.Ψ).E.IsScFredholmSectionFunctor (Q.modelSection c.Ψ f) :=
  (Q.remark_18_1_2_a_model f c).2 hf

/-- **Proper`<∞` in a covering model gives proper`<∞`** (18.3): the neighbourhood is
`|Γ|(|U|)`. -/
theorem isProperLtInfty_of_model (c : Q.BundleCoveringFamily)
    (h : (Q.modelSEP c.Ψ).E.IsProperLtInftyFunctor (Q.modelSection c.Ψ f)) :
    Q.IsProperLtInfty f := by
  refine ⟨(Q.isCompact_zeroSet_iff c.Ψ f c.cover).2 h.1, fun N hN => ?_⟩
  obtain ⟨U, hUo, -, hSU, hC⟩ := h.2 _ (hN c).isAuxNorm
  refine ⟨_, isOpen_modelImage c hUo, ?_, fun r hr =>
    (isCompact_closure_modelImage_iff c (hN c) U hr.le).2 (hC r hr)⟩
  rw [← Q.image_solutionSet_modelSection c.Ψ f c.cover]
  exact image_mono (image_mono hSU)

/-! ### Theorem 18.2.2 -/

variable (Q f) in
/-- **Theorem 18.2.2 (Stability of compactness), p. 850**: for an sc-Fredholm section functor `f`
of the strong polyfold bundle `P : E → C` the following are equivalent: (1) `f` has a compact
moduli space, (2) `f` is proper, (3) `f` is proper`<∞` (from Theorem 12.4.2 in a covering
model, (18.3)). -/
theorem theorem_18_2_2 (hF : Q.HasStrongBundleUniformizers)
    (hf : Q.IsScFredholmSectionFunctor f) :
    List.TFAE [f.HasCompactModuliSpace, Q.IsProper f, Q.IsProperLtInfty f] := by
  tfae_have 1 → 3 := by
    intro hS
    set c := Q.refCoveringFamily hF
    exact isProperLtInfty_of_model c
      (EpStrongBundle.isProperLtInftyFunctor_of_hasCompactSolutionSetEp
        (Q.modelSection_isScFredholm f c hf) ((Q.isCompact_zeroSet_iff c.Ψ f c.cover).1 hS))
  tfae_have 3 → 2 := by
    intro h
    refine ⟨h.1, fun N hN => ?_⟩
    obtain ⟨U, hUo, hSU, hC⟩ := h.2 N hN
    have := hC 1 one_pos
    rw [ENNReal.ofReal_one] at this
    exact ⟨U, hUo, hSU, this⟩
  tfae_have 2 → 1 := fun h => h.1
  tfae_finish

/-! ### The observation after Definition 18.2.3 -/

variable (Q) in
/-- **Inside every open neighbourhood of `|S_f|` there is one strongly controlling compactness**
(sc-Fredholm `f` with compact moduli space, Theorem 18.2.2 (3)). -/
theorem exists_stronglyControlsCompactness_subset (hF : Q.HasStrongBundleUniformizers)
    (hf : Q.IsScFredholmSectionFunctor f) (hS : f.HasCompactModuliSpace) {N : V.EObj → ℝ≥0∞}
    (hN : Q.IsAuxNormFunctor N) {U : Set C.toGroupoidStr.OrbitSpace} (hUo : IsOpen U)
    (hSU : C.toGroupoidStr.π '' f.zeroSet ⊆ U) :
    ∃ U' ⊆ U, f.StronglyControlsCompactness N U' := by
  obtain ⟨-, h⟩ := ((Q.theorem_18_2_2 f hF hf).out 0 2).1 hS
  obtain ⟨U'', hU''o, hSU'', hC⟩ := h N hN
  refine ⟨U ∩ U'', inter_subset_left, hUo.inter hU''o, subset_inter hSU hSU'', fun r hr =>
    (hC r hr).of_isClosed_subset isClosed_closure (closure_mono ?_)⟩
  exact inter_subset_inter_left _ inter_subset_right

variable (Q) in
/-- **The observation after Definition 18.2.3, p. 850**: for an sc-Fredholm section functor `f`
with compact moduli space and an auxiliary norm `N`, `(N, U)` controls compactness for a suitable
`U` iff `(N, U')` strongly controls compactness for some open neighbourhood `U'` of `|S_f|`. -/
theorem definition_18_2_3_observation (hF : Q.HasStrongBundleUniformizers)
    (hf : Q.IsScFredholmSectionFunctor f) (hS : f.HasCompactModuliSpace) {N : V.EObj → ℝ≥0∞}
    (hN : Q.IsAuxNormFunctor N) :
    (∃ U, f.ControlsCompactness N U) ↔ ∃ U', f.StronglyControlsCompactness N U' := by
  constructor
  · rintro ⟨U, hUo, hSU, -⟩
    obtain ⟨U', -, hU'⟩ := exists_stronglyControlsCompactness_subset Q hF hf hS hN hUo hSU
    exact ⟨U', hU'⟩
  · rintro ⟨U', hU'⟩
    exact ⟨U', hU'.controlsCompactness⟩

/-! ### Definition 18.2.4 -/

variable (Q f) in
/-- **Definition 18.2.4, p. 850**: `f` has the **(categorical) reflexive local compactness
property**: for every reflexive auxiliary norm `N` and every `z ∈ |C|` there is an open
neighbourhood `U(z)` of `z` in `|C|` such that the closure of `{y ∈ U(z) | |N| ∘ |f|(y) ≤ 1}` is
compact in `|C|`.  (The standing assumptions, reflexive `(0, 1)`-fibres and `f` sc-Fredholm, are
hypotheses of the statements using it.) -/
def HasReflexiveLocalCompactness : Prop :=
  ∀ N : V.EObj → ℝ≥0∞, Q.IsReflexiveAuxNormFunctor N → ∀ z : C.toGroupoidStr.OrbitSpace,
    ∃ U : Set C.toGroupoidStr.OrbitSpace, IsOpen U ∧ z ∈ U ∧
      IsCompact (closure (U ∩ f.sublevel N 1))

/-! ### Remark 18.2.5 -/

/-- `Γ(x)` is isomorphic to a given `α` for some `x`, for a covering family. -/
theorem exists_modelObj_iso (c : Q.BundleCoveringFamily) (α : C.Obj) :
    ∃ x : S.ModelObj (Q.modelBase c.Ψ),
      C.toGroupoidStr.Isomorphic ((S.modelFunctor (Q.modelBase c.Ψ)).obj x) α := by
  obtain ⟨x, φ, hs, ht⟩ := (GroupoidFunctor.essSurj_iff _).1 (modelFunctor_essSurj c.cover) α
  exact ⟨x, φ, hs, ht⟩

variable (Q) in
/-- **Remark 18.2.5, pp. 850–851**: let `P` have reflexive `(0, 1)`-fibres, `f` be sc-Fredholm and
`N` a reflexive auxiliary norm.  If `z = |α|` lies in `|C|₀ ∖ |C|₁` (no representative of
regularity `1`), then `|N| ∘ |f|(z) = +∞` (`f(α) ∉ E_{0,1}` by the regularizing property), and
there is an open neighbourhood `U(z)` with `{y ∈ U(z) | |N| ∘ |f|(y) ≤ 1} = ∅`, whose closure is
compact.  The text's argument uses only the lower semicontinuity of `|N| ∘ |f|`; no local
compactness hypothesis is needed. -/
theorem remark_18_2_5 (hF : Q.HasStrongBundleUniformizers) (hB : Q.HasReflexiveFibers)
    (hf : Q.IsScFredholmSectionFunctor f) {N : V.EObj → ℝ≥0∞}
    (hN : Q.IsReflexiveAuxNormFunctor N) {α : C.Obj} (hα : ¬ S.HasRegularity 1 α) :
    N (f.toFun α) = ⊤ ∧ ∃ U : Set C.toGroupoidStr.OrbitSpace, IsOpen U ∧
      C.toGroupoidStr.π α ∈ U ∧ U ∩ f.sublevel N 1 = ∅ ∧
        IsCompact (closure (U ∩ f.sublevel N 1)) := by
  set c := Q.refCoveringFamily hF
  have hf' := Q.modelSection_isScFredholm f c hf
  obtain ⟨hsm, -⟩ := hf'.1
  obtain ⟨x, hx⟩ := exists_modelObj_iso c α
  have hx1 : x ∉ (Q.modelSEP c.Ψ).X.PObj.levelSet 1 := fun h =>
    hα (((S.hasRegularity_modelFunctor_obj (Q.modelBase c.Ψ) x 1).2 h).of_isomorphic hx)
  have hfx : Q.modelSection c.Ψ f x ∉ (Q.modelSEP c.Ψ).B.oneSet := fun h =>
    hx1 (hf'.2.regularizing 0 x (by rw [MPolyfold.levelSet_zero]; trivial)
      (StrongBundle.oneSet_subset_doubleLevel h))
  have htop : N (f.toFun α) = ⊤ := by
    rw [← f.comp_eq_of_isomorphic (hN c).isMorInvariant hx]
    exact (Q.bundlePull_modelSection f N x).symm.trans ((hN c).eq_top _ hfx)
  refine ⟨htop, ?_⟩
  set A := {y | (Q.modelSEP c.Ψ).B.AuxLe (Q.modelNorm c.Ψ N) (Q.modelSection c.Ψ f y) 1}
  have hAc : IsClosed A := StrongBundle.isClosed_setOf_auxLe (hB c) hsm.1
    (continuousOn_univ.1 hsm.2.continuousOn) (hN c).isReflexive.toStrong
  have hxA : x ∉ A := fun h => hfx h.1
  set U0 := (S.modelFunctor (Q.modelBase c.Ψ)).orbitMap '' ((Q.modelSEP c.Ψ).X.π '' Aᶜ) with hU0
  have hempty : U0 ∩ f.sublevel N 1 = ∅ := by
    have e := image_auxLe_eq (f := f) (hN c).toIsAuxNormIn Aᶜ zero_le_one
    rw [ENNReal.ofReal_one] at e
    refine e.symm.trans (eq_empty_of_forall_notMem ?_)
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact hy.1 hy.2
  have hcl : closure (U0 ∩ f.sublevel N 1) = ∅ := (closure_empty_iff _).2 hempty
  refine ⟨U0, isOpen_modelImage c hAc.isOpen_compl, ⟨_, ⟨x, hxA, rfl⟩, Quotient.sound hx⟩,
    hempty, ?_⟩
  rw [hcl]
  exact isCompact_empty

/-! ### Theorem 18.2.6 -/

/-- **`x ∈ ∂X_Ψ` iff `|Γ(x)| ∈ |∂C|`** (Definition 17.1.30; the degeneracy index of `Γ(x)` is
that of `x`). -/
theorem mem_boundary_model_iff (c : Q.BundleCoveringFamily) (x : S.ModelObj (Q.modelBase c.Ψ)) :
    x ∈ (Q.modelSEP c.Ψ).X.PObj.boundary ↔
      (S.modelFunctor (Q.modelBase c.Ψ)).orbitMap ((Q.modelSEP c.Ψ).X.π x) ∈
        C.toGroupoidStr.π '' S.boundarySet := by
  change 1 ≤ (S.modelEP (Q.modelBase c.Ψ)).X.PObj.degIndex x ↔
    (S.modelFunctor (Q.modelBase c.Ψ)).obj x ∈
      C.toGroupoidStr.π ⁻¹' (C.toGroupoidStr.π '' S.boundarySet)
  rw [S.isSaturated_boundarySet, ← degIndex_modelFunctor_obj]
  rfl

variable (Q f) in
/-- **Theorem 18.2.6, p. 851**: let `P : E → C` be a strong polyfold bundle over the tame `C`
with reflexive `(0, 1)`-fibres, `N` a reflexive auxiliary norm, and `f` an sc-Fredholm section
functor with compact moduli space and the reflexive local compactness property.  Let
`U_∂ = W' ∩ |∂C|` (`W'` open in `|C|`) be an open neighbourhood in `|∂C|` of
`|S_{∂f}| = |S_f ∩ ∂C|` such that the closure of `{z ∈ U_∂ | |N| ∘ |f|(z) ≤ 1}` is compact in
`|C|`.  Then there is an open neighbourhood `U` of `|S_f|` with (1) `U ∩ |∂C| = U_∂` and
(2) `cl_{|C|}{z ∈ U | |N| ∘ |f|(z) ≤ 1}` compact, i.e. `(N, U)` controls compactness for `f`.
From Theorem 12.4.6 in a covering model; tameness is kept as in the text and not used. -/
theorem theorem_18_2_6 (hF : Q.HasStrongBundleUniformizers) (_hT : S.IsTame)
    (hB : Q.HasReflexiveFibers) {N : V.EObj → ℝ≥0∞} (hN : Q.IsReflexiveAuxNormFunctor N)
    (hf : Q.IsScFredholmSectionFunctor f) (hS : f.HasCompactModuliSpace)
    (hlc : Q.HasReflexiveLocalCompactness f) {Ub : Set C.toGroupoidStr.OrbitSpace}
    (hUb : ∃ W' : Set C.toGroupoidStr.OrbitSpace, IsOpen W' ∧
      Ub = W' ∩ C.toGroupoidStr.π '' S.boundarySet)
    (hSUb : C.toGroupoidStr.π '' (f.zeroSet ∩ S.boundarySet) ⊆ Ub)
    (hcpt : IsCompact (closure (Ub ∩ f.sublevel N 1))) :
    ∃ U : Set C.toGroupoidStr.OrbitSpace, U ∩ C.toGroupoidStr.π '' S.boundarySet = Ub ∧
      f.ControlsCompactness N U := by
  set c := Q.refCoveringFamily hF
  set X := (Q.modelSEP c.Ψ).X
  set h := (S.modelFunctor (Q.modelBase c.Ψ)).orbitMap with hh
  have hhc : Continuous h := (isHomeomorph_modelOrbitMap c.cover).continuous
  have hf' := Q.modelSection_isScFredholm f c hf
  obtain ⟨hsm, hfun⟩ := hf'.1
  have hNc := hN c
  have e1 : ENNReal.ofReal 1 = 1 := ENNReal.ofReal_one
  obtain ⟨W', hW'o, rfl⟩ := hUb
  set WX : Set (S.ModelObj (Q.modelBase c.Ψ)) := X.π ⁻¹' (h ⁻¹' W') with hWX
  have hWXo : IsOpen WX := (hW'o.preimage hhc).preimage X.continuous_π
  have hWXs : X.IsSaturated WX := by
    change X.π ⁻¹' (X.π '' (X.π ⁻¹' _)) = X.π ⁻¹' _
    rw [image_preimage_eq _ X.surjective_π]
  have hbs : X.IsSaturated X.PObj.boundary :=
    X.isSaturated_iff.2 fun φ h => (X.tgt_mem_boundary_iff φ).2 h
  set UbX := WX ∩ X.PObj.boundary with hUbX
  have hkey : h '' (X.π '' UbX) = W' ∩ C.toGroupoidStr.π '' S.boundarySet := by
    ext z
    constructor
    · rintro ⟨_, ⟨x, ⟨hxW, hxb⟩, rfl⟩, rfl⟩
      exact ⟨hxW, (mem_boundary_model_iff c x).1 hxb⟩
    · rintro ⟨hzW, hzb⟩
      obtain ⟨q, rfl⟩ := (isHomeomorph_modelOrbitMap c.cover).surjective z
      obtain ⟨x, rfl⟩ := X.surjective_π q
      exact ⟨_, ⟨x, ⟨hzW, (mem_boundary_model_iff c x).2 hzb⟩, rfl⟩, rfl⟩
  -- the hypotheses of Theorem 12.4.6 in the model
  have hSX : (Q.modelSEP c.Ψ).E.HasCompactSolutionSetEp (Q.modelSection c.Ψ f) :=
    (Q.isCompact_zeroSet_iff c.Ψ f c.cover).1 hS
  have hSUbX : solutionSet (Q.modelSEP c.Ψ).P (Q.modelSection c.Ψ f) ∩ X.PObj.boundary ⊆ UbX := by
    rintro x ⟨hxS, hxb⟩
    refine ⟨?_, hxb⟩
    have hz : h (X.π x) ∈ C.toGroupoidStr.π '' (f.zeroSet ∩ S.boundarySet) := by
      obtain ⟨β, hβ, he⟩ := (mem_boundary_model_iff c x).1 hxb
      refine ⟨β, ⟨f.mem_zeroSet_of_isomorphic ((GroupoidStr.π_eq_π_iff _).1 he.symm)
        ((Q.mem_modelSolutionSet_iff c.Ψ f x).1 hxS), hβ⟩, he⟩
    exact (hSUb hz).1
  have hcptX : IsCompact (closure (X.π '' {y ∈ UbX | (Q.modelSEP c.Ψ).B.AuxLe
      (Q.modelNorm c.Ψ N) (Q.modelSection c.Ψ f y) 1})) := by
    refine (isCompact_closure_modelImage_iff c hNc.toIsAuxNormIn UbX zero_le_one).1 ?_
    rw [hkey, e1]
    exact hcpt
  have hlcX : ∀ x, ∃ U, IsOpen U ∧ x ∈ U ∧ IsCompact (closure {y ∈ U |
      (Q.modelSEP c.Ψ).B.AuxLe (Q.modelNorm c.Ψ N) (Q.modelSection c.Ψ f y) 1}) := by
    intro x
    obtain ⟨U', hU'o, hxU', hU'c⟩ := hlc N hN (h (X.π x))
    set U2 : Set (S.ModelObj (Q.modelBase c.Ψ)) := X.π ⁻¹' (h ⁻¹' U') with hU2
    have hU2' : h '' (X.π '' U2) = U' := by
      ext z
      constructor
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        exact hy
      · intro hz
        obtain ⟨q, rfl⟩ := (isHomeomorph_modelOrbitMap c.cover).surjective z
        obtain ⟨y, rfl⟩ := X.surjective_π q
        exact ⟨_, ⟨y, hz, rfl⟩, rfl⟩
    have hc : IsCompact (closure (X.π '' {y ∈ U2 | (Q.modelSEP c.Ψ).B.AuxLe
        (Q.modelNorm c.Ψ N) (Q.modelSection c.Ψ f y) 1})) := by
      refine (isCompact_closure_modelImage_iff c hNc.toIsAuxNormIn U2 zero_le_one).1 ?_
      rw [hU2', e1]
      exact hU'c
    obtain ⟨V₀, hV₀o, hxV₀, hprop⟩ := X.exists_isProperMap x
    refine ⟨U2 ∩ V₀, ((hU'o.preimage hhc).preimage X.continuous_π).inter hV₀o,
      ⟨hxU', hxV₀⟩, ?_⟩
    refine X.isCompact_closure_of_isProperMap hprop (fun y hy => hy.1.2) ?_
    exact hc.of_isClosed_subset isClosed_closure
      (closure_mono (image_mono fun y hy => ⟨hy.1.1, hy.2⟩))
  obtain ⟨U, hUo, -, hSU, hUb, hUc⟩ := EpStrongBundle.theorem_12_4_6_of_continuous (hB c)
    hNc.isReflexive hsm.1 (continuousOn_univ.1 hsm.2.continuousOn) hfun hSX hlcX
    ⟨WX, hWXo, rfl⟩ (EpGroupoid.isSaturated_inter hWXs hbs) hSUbX hcptX
  refine ⟨h '' (X.π '' U), ?_, isOpen_modelImage c hUo, ?_, ?_⟩
  · ext z
    constructor
    · rintro ⟨⟨_, ⟨x, hxU, rfl⟩, rfl⟩, hzb⟩
      rw [← hkey]
      exact ⟨_, ⟨x, (Set.ext_iff.1 hUb x).1 ⟨hxU, (mem_boundary_model_iff c x).2 hzb⟩, rfl⟩,
        rfl⟩
    · intro hz
      rw [← hkey] at hz
      obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hz
      replace hx := (Set.ext_iff.1 hUb x).2 hx
      exact ⟨⟨_, ⟨x, hx.1, rfl⟩, rfl⟩, (mem_boundary_model_iff c x).1 hx.2⟩
  · rw [← Q.image_solutionSet_modelSection c.Ψ f c.cover]
    exact image_mono (image_mono hSU)
  · rw [← e1]
    exact (isCompact_closure_modelImage_iff c hNc.toIsAuxNormIn U zero_le_one).2 hUc

end StrongPolyfoldBundleConstruction

end GCT.VectorBundle

end Polyfold
