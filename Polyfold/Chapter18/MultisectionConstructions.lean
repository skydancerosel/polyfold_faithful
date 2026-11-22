import Polyfold.Chapter18.MultisectionFunctors
import Polyfold.Chapter16.PolyfoldBump
import Polyfold.Chapter16.PolyfoldPartitions
import Polyfold.Chapter13.AtomicConstruction
import Polyfold.Chapter13.AtomicStructurable
import Polyfold.Chapter7.PartitionsOfUnity
import Polyfold.Chapter12.BumpEp
import Polyfold.Chapter14.BoundaryExtensionTheorem
import Polyfold.Chapter18.Compactness

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 18,
§18.4 "Constructions and Extensions" (pp. 853–855): **Definition 18.4.1, Remark 18.4.2, the
construction of p. 854, Proposition 18.4.3 and Theorem 18.4.4**.  Numbers and pages are the
2021 text's.

## The text, paraphrased

(18.4.1) The polyfold `C` admits sc-smooth partitions of unity, or sc-smooth bump functions, if
an sc-smooth model does.  (18.4.2) This is preserved under generalized isomorphisms, so the model
does not matter; if the model `X` (metrizable `|X|`) admits sc-smooth partitions of unity as an
M-polyfold, it admits them in the ep-groupoid sense (§7.6.2).  (p. 854) For a smooth object `α`
and a smooth vector `(α, e)`, a bump section `s₁` through the preimage of `e` in one strong
bundle uniformizer, its translates `s_g`, and `Λ(Ψ̄(h)) = |G|⁻¹·#{g | s_g(p(h)) = h}`, extended
along morphisms and by `1_{e = 0}` elsewhere.  (18.4.3) This `Λ` is an sc⁺-multisection functor
with `Λ(α, e) > 0`; in a suitable model `Γ̄^*Λ` is atomic, hence structurable ("the easy proof is
left to the reader", Theorem 13.5.3).  (18.4.4, ∂-Extension Theorem) Over a tame polyfold with
sc-smooth partitions of unity, an auxiliary norm `N`, a structurable `Λ` on `E|∂C`, an open
`V ⊃ |dom-supp(Λ)|` and a continuous `β ≥ 0` with `|supp(β)| ⊂ V` and `N(Λ) < β` on
`dom-supp(Λ)` give a structurable `Λ'` on `E` with `N(Λ') ≤ β`, `|dom-supp(Λ')| ⊂ V` and
`Λ' = Λ` on `E|∂C`; "the categorical version of Theorem 14.1.9 … proved by using an sc-smooth
model".

## What is formalized

* Namespace `Polyfold.GCT.PolyfoldConstruction`: **`AdmitsModelPartitionsOfUnity`,
  `AdmitsModelBumpFunctions` (Definition 18.4.1)**; `hasScPartitionsOfUnity_model_iff`,
  `admitsBumpFunctionsPointwise_model_iff` (any two models), **`remark_18_4_2`** (independence of
  the model, the M-polyfold criterion of §7.6.2), `remark_18_4_2_generalizedIso` (invariance
  under generalized isomorphisms of ep-groupoids).
* Namespace `Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction`: `pos_count_of_mem`,
  **`proposition_18_4_3`** (an atomic, hence structurable, sc⁺-multisection functor `Λ` with
  `Λ(α, e) > 0`), `proposition_18_4_3_formula` (the formula of p. 854 in the model: `Γ̄^*Λ` is
  the multisection `|I|⁻¹·#{i | sᵢ(p(h)) = h}` of a symmetric family through the given vector,
  extended along morphisms and by `1_{e = 0}`).
* Namespace `Polyfold.GCT.VectorBundle`: `orbitDomSupp` (`|dom-supp(Λ)| ⊂ |C|`),
  `orbitBoundaryDomSupp` (`|dom-supp(Λ)| ⊂ |∂C|` for `Λ` on `E|∂C`),
  `IsMorInvariant.exists_ne_zero_pos_of_isomorphic`; namespace
  `….StrongPolyfoldBundleConstruction`: `pointwiseNorm_bundlePull_of_ne_top`,
  `mem_orbitBoundaryDomSupp_of_model`, `preimage_orbitDomSupp_subset`, **`theorem_18_4_4`**
  (Theorem 14.1.9 in the model, pushed forward along `Γ̄`).

## Readings

* Definition 18.4.1: "admits sc-smooth partitions of unity" is read in the ep-groupoid sense
  (Definition 7.5.5) and "sc-smooth bump functions" in the pointwise ep-groupoid sense
  (Definition 12.3.1 with `f(x) ≠ 0`, equivalent to Part I's Definition 5.3.1 for the object
  M-polyfold, Theorem 12.3.2 (1)); "an sc-smooth model" is the model `X_Ψ` of a covering family.
* The construction of p. 854 uses one strong bundle uniformizer `Ψ̄ ∈ F̄(α)` with `G = G_α`.  We
  carry it out in the model `W_Ψ̄ → X_Ψ` of a covering family (the "suitable sc-smooth model" of
  Proposition 18.4.3), where the rôle of `G ⋉ O` is played by a natural representation of
  `G_x` at a point `x` of the model over `α` (Theorem 7.1.13), and push the result forward along
  `Γ̄` (`bundlePush`).  "`α` smooth" and "`(α, e)` a smooth vector" are read in the model: a point
  `x` in the smooth part of `X_Ψ` and a smooth `w ∈ W_x` with `Γ̄(w) ≅ (α, e)`.  The
  multisection obtained is the text's: `proposition_18_4_3_formula` records its values.
* Theorem 18.4.4: stated for a covering family `c`.  "`C` admits sc-smooth partitions of unity"
  is read as the M-polyfold partitions of unity of the model `X_Ψ` (Theorem 14.1.9's
  hypothesis, which gives Definition 18.4.1 by `remark_18_4_2`); "`Λ : E|∂C → ℚ⁺` structurable"
  is read as a functor `Λ` on `E` (its values off `E|∂C` play no rôle) whose pull-back `Γ̄^*Λ` is
  structurable over `∂X_Ψ` (Definition 14.1.7) in that model, since Part III shows the
  independence of the model for tame `X` (`proposition_14_1_8`) and otherwise under a hypothesis
  (`proposition_14_1_8_hyp`); "continuous" is
  read as continuity of `β ∘ Γ` on `X_Ψ` (equivalently of `|β|` on `|C| ≅ |X_Ψ|`); `|supp(β)|` is
  the closure in `|C|` of the classes of the `α` with `β(α) ≠ 0`; `N(Λ)(α) < β(α)` and
  `N(Λ')(α) ≤ β(α)` are read in `[0, ∞]`, and `α ∈ dom-supp(Λ)` as `|α| ∈ |dom-supp(Λ)|`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology CategoryTheory
open scoped ENNReal

noncomputable section

namespace Polyfold

universe u

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} (S : C.PolyfoldConstruction)

/-! ### Definition 18.4.1 and Remark 18.4.2 -/

/-- **2021 Definition 18.4.1, p. 853 (partitions of unity)**: the polyfold `C` admits sc-smooth
partitions of unity if an sc-smooth model `X_Ψ` does (in the ep-groupoid sense,
Definition 7.5.5). -/
def AdmitsModelPartitionsOfUnity : Prop :=
  ∃ c : S.CoveringFamily, (S.modelEP c.Ψ).X.HasScPartitionsOfUnity

/-- **2021 Definition 18.4.1, p. 853 (bump functions)**: the polyfold `C` admits sc-smooth bump
functions if an sc-smooth model `X_Ψ` does (Definition 12.3.1, pointwise reading). -/
def AdmitsModelBumpFunctions : Prop :=
  ∃ c : S.CoveringFamily, (S.modelEP c.Ψ).X.AdmitsBumpFunctionsPointwise

/-- Partitions of unity in two models: `f_{Ψ,Ψ'}` is a generalized isomorphism (Theorem 17.1.18)
and partitions of unity pass along equivalences (Proposition 16.1.4 (2)'s proof). -/
theorem hasScPartitionsOfUnity_model_iff (c c' : S.CoveringFamily) :
    (S.modelEP c.Ψ).X.HasScPartitionsOfUnity ↔ (S.modelEP c'.Ψ).X.HasScPartitionsOfUnity :=
  EPLocalization.EPLoc.iff_of_isGeneralizedIso (fun B => B.X.HasScPartitionsOfUnity)
    (fun _ hF => EpFunctor.IsEquivalence.hasScPartitionsOfUnity_iff hF)
    (S.isGeneralizedIso_comparison c c')

/-- Bump functions in two models (Theorem 12.3.2 (1) and Proposition 16.1.4 (1)'s proof). -/
theorem admitsBumpFunctionsPointwise_model_iff (c c' : S.CoveringFamily) :
    (S.modelEP c.Ψ).X.AdmitsBumpFunctionsPointwise ↔
      (S.modelEP c'.Ψ).X.AdmitsBumpFunctionsPointwise := by
  rw [EpGroupoid.theorem_12_3_2_1, EpGroupoid.theorem_12_3_2_1]
  exact EPLocalization.EPLoc.iff_of_isGeneralizedIso (fun B => B.X.PObj.AdmitsBumpFunctions)
    (fun _ hF => hF.admitsBumpFunctions_iff) (S.isGeneralizedIso_comparison c c')

/-- **2021 Remark 18.4.2, pp. 853–854**: the existence of sc-smooth partitions of unity, or of
sc-smooth bump functions, does not depend on the sc-smooth model; and if the model `X_Ψ` (whose
orbit space `|X_Ψ| ≅ |C|` is metrizable) admits sc-smooth partitions of unity as an M-polyfold,
it admits them in the ep-groupoid sense (Theorem 7.5.7, §7.6.2). -/
theorem remark_18_4_2 (c : S.CoveringFamily) :
    (S.AdmitsModelPartitionsOfUnity ↔ (S.modelEP c.Ψ).X.HasScPartitionsOfUnity) ∧
      (S.AdmitsModelBumpFunctions ↔ (S.modelEP c.Ψ).X.AdmitsBumpFunctionsPointwise) ∧
      ((S.modelEP c.Ψ).X.PObj.AdmitsScPartitionsOfUnity →
        (S.modelEP c.Ψ).X.HasScPartitionsOfUnity) :=
  ⟨⟨fun ⟨c', h⟩ => (S.hasScPartitionsOfUnity_model_iff c' c).1 h, fun h => ⟨c, h⟩⟩,
    ⟨fun ⟨c', h⟩ => (S.admitsBumpFunctionsPointwise_model_iff c' c).1 h, fun h => ⟨c, h⟩⟩,
    fun h => (S.modelEP c.Ψ).X.theorem_7_5_7 (S.hasParacompactOrbitSpace_model c) h⟩

omit S in
/-- **Remark 18.4.2, first sentence**: the existence of sc-smooth partitions of unity and of
sc-smooth bump functions is preserved under generalized isomorphisms of ep-groupoids. -/
theorem remark_18_4_2_generalizedIso {X Y : EP.{u}}
    {f : EPLocalization.EPLoc.of X ⟶ EPLocalization.EPLoc.of Y}
    (hf : EPLocalization.EPLoc.IsGeneralizedIso f) :
    (X.X.HasScPartitionsOfUnity ↔ Y.X.HasScPartitionsOfUnity) ∧
      (X.X.AdmitsBumpFunctionsPointwise ↔ Y.X.AdmitsBumpFunctionsPointwise) := by
  refine ⟨EPLocalization.EPLoc.iff_of_isGeneralizedIso (fun B => B.X.HasScPartitionsOfUnity)
    (fun _ hF => EpFunctor.IsEquivalence.hasScPartitionsOfUnity_iff hF) hf, ?_⟩
  rw [EpGroupoid.theorem_12_3_2_1, EpGroupoid.theorem_12_3_2_1]
  exact EPLocalization.EPLoc.iff_of_isGeneralizedIso (fun B => B.X.PObj.AdmitsBumpFunctions)
    (fun _ hF => hF.admitsBumpFunctions_iff) hf

end GCT.PolyfoldConstruction

namespace GCT.VectorBundle.StrongPolyfoldBundleConstruction

open GroupoidalCategory GroupoidalCategory.BanachFunctor SBLocalization StrongBundle

variable {C : GCT.{u}} {V : C.VectorBundle} {S : C.PolyfoldConstruction}
  (Q : V.StrongPolyfoldBundleConstruction S)

/-- The base covering family `(Ψ_λ)` of a covering family of strong bundle uniformizers. -/
def baseCoveringFamily (c : Q.BundleCoveringFamily) : S.CoveringFamily :=
  ⟨c.ι, Q.modelBase c.Ψ, c.cover⟩

/-! ### The construction of p. 854 and Proposition 18.4.3 -/

omit Q in
/-- The count `|I|⁻¹·#{i | sᵢ(P(w)) = w}` is positive when some `sᵢ` passes through `w`. -/
theorem pos_count_of_mem {A : SEP.{u}} (D : AtomicData A) {w : A.W} {i₀ : D.I}
    (hi₀ : D.s i₀ (A.P w) = w) : 0 < D.count w := by
  classical
  unfold AtomicData.count
  refine mul_pos (inv_pos.2 (Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨i₀⟩))) ?_
  exact Nat.cast_pos.2 (Finset.card_pos.2 ⟨i₀, by simp [hi₀]⟩)

/-- An sc⁺-multisection functor of a model is constant on isomorphism classes of `W_Ψ̄`. -/
theorem eq_of_isomorphic_of_isWFunctor {ι : Type u} {Ψb : ι → Q.Unif}
    {Λ : Q.ModelW Ψb → ℚ≥0} (hΛ : IsWFunctor (Q.modelSEP Ψb) Λ) (w w' : Q.ModelW Ψb)
    (h : (Q.modelEpStrongBundle Ψb).toGroupoidStr.Isomorphic w w') : Λ w = Λ w' := by
  obtain ⟨a, hs, ht⟩ := h
  rw [← hs, ← ht]
  exact (hΛ a).symm

/-- **The construction of p. 854, in a model**: for a smooth point `x` of the model `X_Ψ` and a
smooth `w ∈ W_x`, the atomic data of Theorem 13.5.4 (1) (a natural representation of `G_x`
with the properness property, an invariant `V(x)`, the family `s_g` of translates of a bump
section through `w`). -/
theorem exists_atomicData (c : Q.BundleCoveringFamily) (hbump : S.AdmitsModelBumpFunctions)
    {w : Q.ModelW c.Ψ} (hx : Q.modelP c.Ψ w ∈ (Q.modelSEP c.Ψ).X.PObj.smoothSet)
    (hw : w ∈ (Q.modelSEP c.Ψ).B.toMPolyfold0.smoothSet) :
    ∃ D : AtomicData (Q.modelSEP c.Ψ), Nonempty D.I ∧ Q.modelP c.Ψ w ∈ D.R.U ∧
      ∃ i₀ : D.I, D.s i₀ (Q.modelP c.Ψ w) = w := by
  set A := Q.modelSEP c.Ψ
  have hb : A.X.AdmitsBumpFunctionsPointwise :=
    ((S.remark_18_4_2 (Q.baseCoveringFamily c)).2.1).1 hbump
  obtain ⟨V₀, hxV₀, hV₀⟩ := A.X.exists_hasPropernessProperty (Q.modelP c.Ψ w)
  obtain ⟨R, Vs, hVo, hxV, hVinv, hVcl, hRU, -⟩ :=
    EpGroupoid.exists_invariant_nhds_of_isOpen A.X (Q.modelP c.Ψ w) hV₀.1 hxV₀
  have hprop : A.X.HasPropernessProperty R.U := hV₀.mono R.isOpen_U hRU
  obtain ⟨F, hvan, i₀, hi₀⟩ := theorem_13_5_4_1 hb hx R hprop hVo hxV hVinv hVcl hw rfl
  exact ⟨AtomicData.ofFamily R hprop F hVo hxV hVinv hVcl hvan, ⟨i₀⟩, R.mem_U, i₀, hi₀⟩

/-- **2021 Proposition 18.4.3, p. 855** (proof left to the reader): let `C` admit sc-smooth bump
functions (Definition 18.4.1), `α` be a smooth object and `(α, e)` a smooth vector, read in a
model `W_Ψ̄ → X_Ψ` as a smooth `w` over a smooth point with `Γ̄(w) ≅ (α, e)`.  The construction of
p. 854 gives an sc⁺-multisection functor `Λ : E → ℚ⁺` with `Λ(α, e) > 0` whose pull-back `Γ̄^*Λ`
to the model is atomic (Definition 13.5.1), hence structurable (Theorem 13.5.3; `|X_Ψ|` is
paracompact), so `Λ` is a structurable sc⁺-multisection functor. -/
theorem proposition_18_4_3 (c : Q.BundleCoveringFamily) (hbump : S.AdmitsModelBumpFunctions)
    {w : Q.ModelW c.Ψ} (hx : Q.modelP c.Ψ w ∈ (Q.modelSEP c.Ψ).X.PObj.smoothSet)
    (hw : w ∈ (Q.modelSEP c.Ψ).B.toMPolyfold0.smoothSet) {e : V.EObj}
    (he : V.groupoid.Isomorphic (Q.bundleModelObj c.Ψ w) e) :
    ∃ Λ : V.EObj → ℚ≥0, Q.IsScPlusMultisectionFunctor Λ ∧ 0 < Λ e ∧
      IsAtomic (Q.modelSEP c.Ψ) (Q.bundlePull c.Ψ Λ) ∧ Q.IsStructurableFunctor Λ := by
  obtain ⟨D, hne, hDx, i₀, hi₀⟩ := Q.exists_atomicData c hbump hx hw
  have hD := D.isAtomic_mult
  have hiso := Q.eq_of_isomorphic_of_isWFunctor D.isWFunctor_mult
  set Λ := Q.bundlePush c.cover D.mult hiso
  have hpull : Q.bundlePull c.Ψ Λ = D.mult := Q.bundlePull_bundlePush c.cover _ _
  have hinv : IsMorInvariant Λ := Q.isMorInvariant_bundlePush c.cover _ hiso
  refine ⟨Λ, ⟨hinv, c, ?_⟩, ?_, ?_, ⟨hinv, c, ?_⟩⟩
  · unfold IsScPlusMultisectionIn; rw [hpull]; exact hD.1
  · rw [← hinv.eq_of_isomorphic he]
    change 0 < Q.bundlePull c.Ψ Λ w
    rw [hpull]
    exact lt_of_lt_of_eq (pos_count_of_mem D hi₀) (D.mult_of_mem hDx).symm
  · rw [hpull]; exact hD
  · unfold IsStructurableIn; rw [hpull]
    exact theorem_13_5_3_of_paracompact (Q.hasParacompactOrbitSpace_model c) hD

/-- **The formula of p. 854** for the multisection functor of Proposition 18.4.3, read in the
model: a symmetric family `(sᵢ)` of sc⁺-sections through `w` (the translates `s_g`), and a
functor `Λ : E → ℚ⁺` with `Λ(Γ̄(h)) = |I|⁻¹·#{i | sᵢ(p(h)) = h}` over `U(x)`, extended along the
morphisms into `U(x)` (`Γ̄^*Λ` is the multisection `mult` of Definition 13.5.1 (3)), and
`Λ(Γ̄(h)) = 1_{h = 0}` over the points joined to no point of `U(x)`. -/
theorem proposition_18_4_3_formula (c : Q.BundleCoveringFamily)
    (hbump : S.AdmitsModelBumpFunctions) {w : Q.ModelW c.Ψ}
    (hx : Q.modelP c.Ψ w ∈ (Q.modelSEP c.Ψ).X.PObj.smoothSet)
    (hw : w ∈ (Q.modelSEP c.Ψ).B.toMPolyfold0.smoothSet) :
    ∃ D : AtomicData (Q.modelSEP c.Ψ), Nonempty D.I ∧ Q.modelP c.Ψ w ∈ D.R.U ∧
      (∃ i₀ : D.I, D.s i₀ (Q.modelP c.Ψ w) = w) ∧
      ∃ Λ : V.EObj → ℚ≥0, IsMorInvariant Λ ∧ Q.bundlePull c.Ψ Λ = D.mult ∧
        (∀ h : Q.ModelW c.Ψ, Q.modelP c.Ψ h ∈ D.R.U →
          Λ (Q.bundleModelObj c.Ψ h) = D.count h) ∧
        ∀ h : Q.ModelW c.Ψ, ¬ D.Reach (Q.modelP c.Ψ h) →
          Λ (Q.bundleModelObj c.Ψ h) = zeroMultisection (Q.modelSEP c.Ψ) h := by
  obtain ⟨D, hne, hDx, i₀, hi₀⟩ := Q.exists_atomicData c hbump hx hw
  have hiso := Q.eq_of_isomorphic_of_isWFunctor D.isWFunctor_mult
  have hpull : Q.bundlePull c.Ψ (Q.bundlePush c.cover D.mult hiso) = D.mult :=
    Q.bundlePull_bundlePush c.cover _ _
  refine ⟨D, hne, hDx, ⟨i₀, hi₀⟩, Q.bundlePush c.cover D.mult hiso,
    Q.isMorInvariant_bundlePush c.cover _ hiso, hpull, fun h hh => ?_, fun h hh => ?_⟩
  · exact (congrFun hpull h).trans (D.mult_of_mem hh)
  · exact (congrFun hpull h).trans (D.mult_of_not_reach hh)

end GCT.VectorBundle.StrongPolyfoldBundleConstruction

/-! ### Theorem 18.4.4 -/

namespace GCT.VectorBundle

open GroupoidalCategory

variable {C : GCT.{u}} {V : C.VectorBundle}

/-- **`|dom-supp(Λ)| ⊂ |C|`** (Theorem 18.4.4 (2), the categorical form of Definition 13.2.3's
domain support): the closure in `|C|` of the classes of the objects `α` carrying a vector
`e ≠ 0` with `Λ(α, e) > 0`. -/
def orbitDomSupp (Λ : V.EObj → ℚ≥0) : Set C.toGroupoidStr.OrbitSpace :=
  closure (C.toGroupoidStr.π '' {α | ∃ v : V.V α, v ≠ 0 ∧ 0 < Λ (V.objMk α v)})

/-- **`|dom-supp(Λ)| ⊂ |∂C|`** for `Λ` on `E|∂C` (Theorem 18.4.4, the categorical form of
Definition 14.1.7's boundary domain support): the closure in `|C|` of the classes of the
boundary objects `α ∈ ∂C` carrying a vector `e ≠ 0` with `Λ(α, e) > 0`. -/
def orbitBoundaryDomSupp (S : C.PolyfoldConstruction) (Λ : V.EObj → ℚ≥0) :
    Set C.toGroupoidStr.OrbitSpace :=
  closure (C.toGroupoidStr.π ''
    {α | α ∈ S.boundarySet ∧ ∃ v : V.V α, v ≠ 0 ∧ 0 < Λ (V.objMk α v)})

/-- The objects carrying a vector `e ≠ 0` with `Λ(α, e) > 0` form a saturated set. -/
theorem IsMorInvariant.exists_ne_zero_pos_of_isomorphic {Λ : V.EObj → ℚ≥0}
    (hΛ : IsMorInvariant Λ) {α α' : C.Obj} (h : C.toGroupoidStr.Isomorphic α α')
    (hα : ∃ v : V.V α, v ≠ 0 ∧ 0 < Λ (V.objMk α v)) :
    ∃ v : V.V α', v ≠ 0 ∧ 0 < Λ (V.objMk α' v) := by
  obtain ⟨φ, rfl, rfl⟩ := h
  obtain ⟨v, hv, hpos⟩ := hα
  exact ⟨V.map φ v, fun h => hv ((V.map φ).map_eq_zero_iff.1 h), by
    rw [hΛ.apply_map φ v]; exact hpos⟩

namespace StrongPolyfoldBundleConstruction

open GroupoidalCategory.BanachFunctor SBLocalization StrongBundle PolyfoldConstruction

variable {S : C.PolyfoldConstruction} (Q : V.StrongPolyfoldBundleConstruction S)

/-- **`N(Λ)(Γ(x))` is the point-wise norm of `Γ̄^*Λ` at `x` whenever it is finite**, for any
`Λ` (Definition 13.2.3 and p. 852): a finite `N(Λ)(Γ(x))` forces `supp(Γ̄^*Λ)(x) ⊂ W_{0,1}`. -/
theorem pointwiseNorm_bundlePull_of_ne_top {ι : Type u} {Ψb : ι → Q.Unif}
    {N : V.EObj → ℝ≥0∞} (hN : Q.IsAuxNormIn Ψb N) (Λ : V.EObj → ℚ≥0)
    (x : S.ModelObj (Q.modelBase Ψb))
    (h : pointwiseNormFunctor N Λ ((S.modelFunctor (Q.modelBase Ψb)).obj x) ≠ ⊤) :
    (pointwiseNormFunctor N Λ ((S.modelFunctor (Q.modelBase Ψb)).obj x)).toReal =
      pointwiseNorm (A := Q.modelSEP Ψb) (Q.modelNorm Ψb N) (Q.bundlePull Ψb Λ) x := by
  have himg : (fun v => N (V.objMk ((S.modelFunctor (Q.modelBase Ψb)).obj x) v)) ''
        {v | 0 < Λ (V.objMk ((S.modelFunctor (Q.modelBase Ψb)).obj x) v)} =
      (fun w => N (Q.bundleModelObj Ψb w)) ''
        suppAt (A := Q.modelSEP Ψb) (Q.bundlePull Ψb Λ) x := by
    ext r
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨w, hw, hwe⟩ : V.objMk _ v ∈ (fun w => Q.bundleModelObj Ψb w) ''
          suppAt (A := Q.modelSEP Ψb) (Q.bundlePull Ψb Λ) x := by
        rw [Q.image_suppAt_bundlePull]; exact ⟨v, hv, rfl⟩
      exact ⟨w, hw, congrArg N hwe⟩
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨v, hv, hve⟩ : Q.bundleModelObj Ψb w ∈ V.objMk _ ''
          {v | 0 < Λ (V.objMk ((S.modelFunctor (Q.modelBase Ψb)).obj x) v)} := by
        rw [← Q.image_suppAt_bundlePull]; exact ⟨w, hw, rfl⟩
      exact ⟨v, hv, congrArg N hve⟩
  have hle : ∀ w ∈ suppAt (A := Q.modelSEP Ψb) (Q.bundlePull Ψb Λ) x,
      N (Q.bundleModelObj Ψb w) ≤
        pointwiseNormFunctor N Λ ((S.modelFunctor (Q.modelBase Ψb)).obj x) := by
    intro w hw
    unfold pointwiseNormFunctor
    rw [himg]
    exact le_sSup ⟨w, hw, rfl⟩
  have hsub : ∀ w ∈ suppAt (A := Q.modelSEP Ψb) (Q.bundlePull Ψb Λ) x,
      w ∈ (Q.modelSEP Ψb).B.oneSet := by
    intro w hw
    by_contra hn
    have htop : N (Q.bundleModelObj Ψb w) = ⊤ := hN.eq_top w hn
    exact h (top_le_iff.1 (htop ▸ hle w hw))
  have hnt : ∀ r ∈ (fun w => N (Q.bundleModelObj Ψb w)) ''
      suppAt (A := Q.modelSEP Ψb) (Q.bundlePull Ψb Λ) x, r ≠ ⊤ := by
    rintro _ ⟨w, hw, rfl⟩
    exact hN.ne_top w (hsub w hw)
  unfold pointwiseNormFunctor
  rw [himg, ENNReal.toReal_sSup _ hnt]
  unfold pointwiseNorm
  congr 1
  ext r
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, by rw [normW_of_mem _ (hsub w hw)]; rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨_, ⟨w, hw, rfl⟩, by rw [normW_of_mem _ (hsub w hw)]; rfl⟩

/-- The boundary domain support of `Γ̄^*Λ` in the model lies over `|dom-supp(Λ)| ⊂ |∂C|`. -/
theorem mem_orbitBoundaryDomSupp_of_model (c : Q.BundleCoveringFamily) (Λ : V.EObj → ℚ≥0)
    {x : S.ModelObj (Q.modelBase c.Ψ)}
    (hx : x ∈ boundaryDomSupp (A := Q.modelSEP c.Ψ) (Q.bundlePull c.Ψ Λ)) :
    C.toGroupoidStr.π ((S.modelFunctor (Q.modelBase c.Ψ)).obj x) ∈
      orbitBoundaryDomSupp S Λ := by
  have hg : Continuous fun x : S.ModelObj (Q.modelBase c.Ψ) =>
      C.toGroupoidStr.π ((S.modelFunctor (Q.modelBase c.Ψ)).obj x) :=
    (isHomeomorph_modelOrbitMap c.cover).continuous.comp (Q.modelSEP c.Ψ).X.continuous_π
  refine ((closure_mono ?_).trans (hg.closure_preimage_subset _)) hx
  rintro _ ⟨hb, w, rfl, hw0, hpos⟩
  refine ⟨_, ⟨?_, Q.bundleModelFiber c.Ψ _ ⟨w, rfl⟩, ?_, ?_⟩, rfl⟩
  · exact S.isSaturated_boundarySet.subset ((Q.mem_boundary_model_iff c _).1 hb)
  · intro h0
    exact hw0 (congrArg Subtype.val ((Q.bundleModelFiber c.Ψ _).map_eq_zero_iff.1 h0))
  · rw [Q.objMk_bundleModelFiber c.Ψ]; exact hpos

/-- The preimage of `|dom-supp(Λ)|` in the model lies in `dom-supp(Γ̄^*Λ)`. -/
theorem preimage_orbitDomSupp_subset (c : Q.BundleCoveringFamily) {Λ : V.EObj → ℚ≥0}
    (hΛ : IsMorInvariant Λ) :
    (fun x : S.ModelObj (Q.modelBase c.Ψ) =>
        C.toGroupoidStr.π ((S.modelFunctor (Q.modelBase c.Ψ)).obj x)) ⁻¹' orbitDomSupp Λ ⊆
      domSupp (A := Q.modelSEP c.Ψ) (Q.bundlePull c.Ψ Λ) := by
  have hh := isHomeomorph_modelOrbitMap c.cover
  change (S.modelEP (Q.modelBase c.Ψ)).X.π ⁻¹' ((S.modelFunctor (Q.modelBase c.Ψ)).orbitMap ⁻¹'
    orbitDomSupp Λ) ⊆ _
  unfold orbitDomSupp
  rw [hh.isOpenMap.preimage_closure_eq_closure_preimage hh.continuous,
    EpGroupoid.preimage_closure_π]
  unfold domSupp
  refine closure_mono fun (x : S.ModelObj (Q.modelBase c.Ψ)) hx => ?_
  obtain ⟨α, hα, hαx⟩ := hx
  have hαx' : C.toGroupoidStr.π α =
      C.toGroupoidStr.π ((S.modelFunctor (Q.modelBase c.Ψ)).obj x) := hαx
  obtain ⟨v, hv, hpos⟩ :=
    hΛ.exists_ne_zero_pos_of_isomorphic (C.toGroupoidStr.π_eq_π_iff.1 hαx') hα
  set u := (Q.bundleModelFiber c.Ψ x).symm v
  refine ⟨u.1, u.2, ?_, ?_⟩
  · intro h0
    apply hv
    have hu : u = 0 := Subtype.ext h0
    rw [← (Q.bundleModelFiber c.Ψ x).apply_symm_apply v]
    change Q.bundleModelFiber c.Ψ x u = 0
    rw [hu, map_zero]
  · change 0 < Λ (Q.bundleModelObj c.Ψ u.1)
    rw [← Q.objMk_bundleModelFiber c.Ψ x u, ContinuousLinearEquiv.apply_symm_apply]
    exact hpos

/-- **2021 Theorem 18.4.4 (∂-Extension Theorem), p. 855**, the categorical form of
Theorem 14.1.9, proved in an sc-smooth model as the text indicates.  Let `C` be tame, the model
`X_Ψ` of a covering family admit sc-smooth partitions of unity, `N : E → [0, ∞]` be an
auxiliary norm, and `Λ` a functor whose restriction to `E|∂C` is structurable (read in the
model: `Γ̄^*Λ` is boundary-structurable, Definition 14.1.7).  Let `V ⊂ |C|` be an open
neighbourhood of `|dom-supp(Λ)| ⊂ |∂C|` and `β : C → [0, ∞)` a continuous functor with
`|supp(β)| ⊂ V` and `N(Λ)(α) < β(α)` on `dom-supp(Λ)`.  Then there is a structurable
sc⁺-multisection functor `Λ' : E → ℚ⁺` with (1) `N(Λ') ≤ β`, (2) `|dom-supp(Λ')| ⊂ V`,
(3) `Λ' = Λ` on `E|∂C`.

Readings: "`C` admits sc-smooth partitions of unity" is read as the M-polyfold partitions of
unity of the model (Theorem 14.1.9's hypothesis; it gives Definition 18.4.1 by
`remark_18_4_2`); the structurability of `Λ` on `E|∂C` is read in the model `c`, as boundary
structurability is invariant under equivalences for tame `X` (`proposition_14_1_8`) and otherwise
under a hypothesis (`proposition_14_1_8_hyp`); continuity of `β` is read as continuity of `β ∘ Γ` on the model,
equivalently of `|β|` on `|C| ≅ |X_Ψ|`; `|supp(β)|` is the closure in `|C|` of the classes of
the `α` with `β(α) ≠ 0`; `N(Λ)(α) < β(α)` is read in `[0, ∞]`. -/
theorem theorem_18_4_4 (c : Q.BundleCoveringFamily) (hT : S.IsTame)
    (hPU : (Q.modelSEP c.Ψ).X.PObj.AdmitsScPartitionsOfUnity)
    {N : V.EObj → ℝ≥0∞} (hN : Q.IsAuxNormIn c.Ψ N) {Λ : V.EObj → ℚ≥0}
    (hΛi : IsMorInvariant Λ)
    (hΛ : IsBoundaryStructurable (Q.modelSEP c.Ψ) (Q.bundlePull c.Ψ Λ))
    {U : Set C.toGroupoidStr.OrbitSpace} (hUo : IsOpen U)
    (hΛU : orbitBoundaryDomSupp S Λ ⊆ U) {β : C.Obj → ℝ}
    (hβi : ∀ φ : C.Mor, β (C.toGroupoidStr.tgt φ) = β (C.toGroupoidStr.src φ))
    (hβ0 : ∀ α, 0 ≤ β α)
    (hβc : Continuous fun x => β ((S.modelFunctor (Q.modelBase c.Ψ)).obj x))
    (hβU : closure (C.toGroupoidStr.π '' {α | β α ≠ 0}) ⊆ U)
    (hNβ : ∀ α, C.toGroupoidStr.π α ∈ orbitBoundaryDomSupp S Λ →
      pointwiseNormFunctor N Λ α < ENNReal.ofReal (β α)) :
    ∃ Λ' : V.EObj → ℚ≥0, Q.IsStructurableFunctor Λ' ∧
      (∀ α, pointwiseNormFunctor N Λ' α ≤ ENNReal.ofReal (β α)) ∧
      orbitDomSupp Λ' ⊆ U ∧ ∀ e : V.EObj, V.base e ∈ S.boundarySet → Λ' e = Λ e := by
  set A := Q.modelSEP c.Ψ
  set Γ := S.modelFunctor (Q.modelBase c.Ψ)
  have hhh := isHomeomorph_modelOrbitMap c.cover
  have hg : Continuous fun x : S.ModelObj (Q.modelBase c.Ψ) => C.toGroupoidStr.π (Γ.obj x) :=
    hhh.continuous.comp A.X.continuous_π
  set Ut : Set A.Obj := A.X.π ⁻¹' (Γ.orbitMap ⁻¹' U)
  have hUto : IsOpen Ut := (hUo.preimage hhh.continuous).preimage A.X.continuous_π
  have hUts : A.X.IsSaturated Ut := by
    change A.X.π ⁻¹' (A.X.π '' (A.X.π ⁻¹' _)) = A.X.π ⁻¹' _
    rw [image_preimage_eq _ A.X.surjective_π]
  set f : A.Obj → ℝ := fun x => β (Γ.obj x)
  have hfi : ∀ φ, f (A.X.tgt φ) = f (A.X.src φ) := by
    intro φ
    exact (congrArg β (Γ.tgt_mor φ)).symm.trans ((hβi (Γ.mor φ)).trans
      (congrArg β (Γ.src_mor φ)))
  have hfs : tsupport f ⊆ Ut := by
    refine (closure_mono ?_).trans ((hg.closure_preimage_subset _).trans (preimage_mono hβU))
    intro x hx
    exact ⟨Γ.obj x, hx, rfl⟩
  have hdom : boundaryDomSupp (A := A) (Q.bundlePull c.Ψ Λ) ⊆ Ut :=
    fun x hx => hΛU (Q.mem_orbitBoundaryDomSupp_of_model c Λ hx)
  have hnorm : ∀ x ∈ boundaryDomSupp (A := A) (Q.bundlePull c.Ψ Λ),
      pointwiseNorm (A := A) (Q.modelNorm c.Ψ N) (Q.bundlePull c.Ψ Λ) x < f x := by
    intro x hx
    have h1 := hNβ _ (Q.mem_orbitBoundaryDomSupp_of_model c Λ hx)
    have hne := ne_top_of_lt h1
    rw [← Q.pointwiseNorm_bundlePull_of_ne_top hN Λ x hne]
    exact (ENNReal.lt_ofReal_iff_toReal_lt hne).1 h1
  obtain ⟨Λm, hΛm, hle, hdomm, hbd⟩ := theorem_14_1_9 (A := A)
    (S.isTame_modelEpGroupoid (Ψ := Q.modelBase c.Ψ) hT)
    (Q.hasParacompactOrbitSpace_model c) hPU _ hΛ _ hN.isAuxNorm Ut hUto hUts hdom f hβc
    (fun x => hβ0 _) hfi hfs hnorm
  have hiso := Q.eq_of_isomorphic_of_isWFunctor hΛm.1.1
  set Λ' := Q.bundlePush c.cover Λm hiso
  have hpull : Q.bundlePull c.Ψ Λ' = Λm := Q.bundlePull_bundlePush c.cover _ _
  have hinv : IsMorInvariant Λ' := Q.isMorInvariant_bundlePush c.cover _ hiso
  refine ⟨Λ', ⟨hinv, c, ?_⟩, ?_, ?_, ?_⟩
  · unfold IsStructurableIn; rw [hpull]; exact hΛm
  · intro α
    obtain ⟨x, ψ, hs, ht⟩ := (GroupoidFunctor.essSurj_iff _).1 (modelFunctor_essSurj c.cover) α
    rw [← pointwiseNormFunctor_eq_of_isomorphic hN.isMorInvariant hinv ⟨ψ, hs, ht⟩]
    have hβα : β α = β (Γ.obj x) := by rw [← ht, ← hs, hβi]
    rw [hβα]
    have hms : Q.IsScPlusMultisectionIn c.Ψ Λ' := by
      unfold IsScPlusMultisectionIn; rw [hpull]; exact hΛm.1
    obtain ⟨hnt, heq⟩ := Q.pointwiseNorm_bundlePull hN hms x
    rw [ENNReal.le_ofReal_iff_toReal_le hnt (hβ0 _), heq, hpull]
    exact hle x
  · intro y hy
    obtain ⟨z, rfl⟩ := hhh.surjective y
    obtain ⟨x, rfl⟩ := A.X.surjective_π z
    have h2 := Q.preimage_orbitDomSupp_subset c hinv (show x ∈ _ from hy)
    rw [hpull] at h2
    exact hdomm h2
  · intro e he
    obtain ⟨z, hz⟩ := (isHomeomorph_bundleModelOrbitMap c.cover).surjective (V.groupoid.π e)
    induction z using Quotient.inductionOn with
    | h w =>
    have hwe : V.groupoid.Isomorphic (Q.bundleModelObj c.Ψ w) e :=
      V.groupoid.π_eq_π_iff.1 hz
    rw [← hinv.eq_of_isomorphic hwe, ← hΛi.eq_of_isomorphic hwe]
    have hPw : A.P w ∈ A.X.PObj.boundary := by
      refine (Q.mem_boundary_model_iff c _).2 ⟨V.base e, he, ?_⟩
      obtain ⟨a, has, hat⟩ := hwe
      have h1 : C.toGroupoidStr.src a.φ = V.base (Q.bundleModelObj c.Ψ w) :=
        a.2.symm.trans (congrArg V.base has)
      have h2 : C.toGroupoidStr.tgt a.φ = V.base e := congrArg V.base hat
      have h3 : V.base (Q.bundleModelObj c.Ψ w) = Γ.obj (A.P w) := by
        rw [Q.bundleModelObj_eq_objMk c.Ψ w]; rfl
      refine (C.toGroupoidStr.π_eq_π_iff.2 ⟨a.φ, h1.trans h3, h2⟩).symm
    change Q.bundlePull c.Ψ Λ' w = Q.bundlePull c.Ψ Λ w
    rw [hpull]
    exact hbd w hPw

end StrongPolyfoldBundleConstruction

end GCT.VectorBundle

end Polyfold
