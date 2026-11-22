import Polyfold.Chapter18.Compactness
import Polyfold.Chapter18.MultisectionFunctors

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 18, §18.1,
pp. 846–848: **auxiliary norms on strong polyfold bundles in the direct form** (Definitions 18.1.7,
18.1.10, 18.1.11, Lemma 18.1.8, Theorem 18.1.12).  Numbers and pages are the 2021 text's.

## The text, paraphrased

Definition 18.1.7: an auxiliary norm for `P : E → C` is a functor `N : E → [0, ∞]` with
(1) `N(e) = +∞` off `E_{0,1}`, (2) a complete norm on every fibre of `E_{0,1}`, (3) if
`|h_k| ∈ |E_{0,1}|`, `|P(h_k)| → |α|` and `|N|(|h_k|) → 0`, then `|h_k| → |0_α|` in `|E_{0,1}|`.
Lemma 18.1.8: `N` is an auxiliary norm iff `N ∘ Γ̄` is one (Definition 12.2.1) for an sc-smooth
model.  Definition 18.1.10: mixed convergence `y_k → y` in `|E_{0,1}|`, read in a strong bundle
uniformizer.  Definition 18.1.11: `N` is reflexive if `N(e) ≤ liminf N(e_k)` for suitable
representatives of mixed convergent `y_k → y`; "alternatively" `|N|(y) ≤ liminf |N|(y_k)`.
Theorem 18.1.12: (1) auxiliary norms exist, (2) with reflexive `(0, 1)`-fibres every auxiliary
norm lies between two reflexive ones, (3) over a tame polyfold auxiliary norms (reflexive ones,
with reflexive fibres) on `E|∂C` extend.

## What is formalized

* `E_{0,1}` (`IsOneObj`, through the covering models), `|E_{0,1}|` (`oneOrbit`, `EOneOrbit`) with
  the topology of `|W[1]|` of a covering model (`oneTopology_eq`: it does not depend on the model;
  `oneHomeomorph`), `|N|` on it (`oneNorm`), `|P|` on it (`oneBase`).
* **Definition 18.1.7** as printed (`IsAuxNormBook`) and with the continuity of `|N|` on
  `|E_{0,1}|` (`IsAuxNormDirect`).  **Lemma 18.1.8** for the second: `lemma_18_1_8`,
  `isAuxNormDirect_iff_isAuxNormFunctor` (the model reading `IsAuxNormFunctor` of
  `AuxiliaryNorms.lean`); the "⇐" half also gives the printed form (`IsAuxNormIn.isAuxNormBook`).
* **Definition 18.1.10**: `MixedTendstoOne`.  **Definition 18.1.11**: the printed condition
  `HasMixedLscReps`, the alternative `HasMixedLsc`, and `hasMixedLscReps_iff_hasMixedLsc` (the two
  agree for a functor `N`); `IsReflexiveAuxNormDirect`, `isReflexiveAuxNormDirect_iff`.
  Relation to the model reading: `IsReflexiveAuxNormFunctor.isReflexiveAuxNormDirect` (every
  covering family), `IsReflexiveAuxNormDirect.isReflexiveAuxNormIn_hyp` and
  `isReflexiveAuxNormDirect_iff_hyp` (when the uniformizers of a covering family have reflexive
  `(0, 1)`-fibres, `HasReflexivePieces`).  Mixed convergence in a piece `K_λ` and in
  `W = ⊔ K_λ`: `StrongBundle.MixedTendsto.sigmaMk`, `StrongBundle.MixedTendsto.exists_summand`.
* **Theorem 18.1.12**: `theorem_18_1_12_one`, `theorem_18_1_12_two`, `theorem_18_1_12_three`,
  `theorem_18_1_12_three_reflexive`, with the auxiliary norms on `E|∂C` `IsBoundaryAuxNormIn`,
  `IsReflexiveBoundaryAuxNormIn` (restrictions of auxiliary norms are such:
  `IsAuxNormIn.isBoundaryAuxNormIn`, `IsReflexiveAuxNormIn.isReflexiveBoundaryAuxNormIn`).

## Readings

* The text does not define `E_{0,1}` for a strong polyfold bundle; we read `e ∈ E_{0,1}` as
  "`|e| = |Γ̄(w)|` for some `w ∈ W_{0,1}` of a covering model" (`isOneObj_iff`: one covering
  model suffices), and the topology of `|E_{0,1}|` as the one transported from `|W[1]|`.
* Definition 12.2.1, whose notion Definition 18.1.7 imports (l. 41710), requires `N` to be
  continuous on `W_{0,1}`; the printed clauses of Definition 18.1.7 do not ask for continuity of
  `|N|`.  We read Definition 18.1.7 with that continuity (`IsAuxNormDirect`), and Lemma 18.1.8 is
  proved for it (`lemma_18_1_8`).  For the printed clauses alone (`IsAuxNormBook`) "⇐" holds and
  "⇒" does not hold: a discontinuous factor `a(|P(e)|) ∈ {1, 2}` keeps (1)–(3) and breaks the continuity
  (`lemma_18_1_8_book_without_continuity`, `AuxiliaryNormsBookForm.lean`).
* Definition 18.1.10: "for a choice of uniformizer `Ψ̄`" is read as "for some strong bundle
  uniformizer of `F̄`"; `Ψ(x) = α` with `|α| = |P|(y)`; the representatives `e_k` are asked for
  large `k`.
* Theorem 18.1.12 (2), (3) take a covering family `c` (one exists when `F̄(α) ≠ ∅`,
  `refCoveringFamily`).  An auxiliary norm on `E|∂C` is read in the covering model `c`
  (`IsBoundaryAuxNormIn`: Definition 12.2.1 over `∂X`, as in Theorem 12.2.7), with `N` constant
  along the morphisms starting over `∂C`; "extended to `P`" means an auxiliary norm `Ñ` with
  `Ñ = N` over `∂C`.  Tameness of `C` enters through `isTame_modelEpGroupoid`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory
open scoped ENNReal

noncomputable section

namespace Polyfold

universe u

namespace StrongBundle

section SigmaMixed

variable {ι : Type*} {X : ι → Type u} [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)]
  [∀ i, ParacompactSpace (X i)] {PX : ∀ i, MPolyfold (X i)}
  {Y : ι → Type u} [∀ i, TopologicalSpace (Y i)] {p : ∀ i, Y i → X i}
  [∀ i x, AddCommGroup (p i ⁻¹' {x})] [∀ i x, Module ℝ (p i ⁻¹' {x})]
  [∀ i, T2Space (Y i)] [∀ i, ParacompactSpace (Y i)] {B : ∀ i, StrongBundle (PX i) (p i)}

/-- A strong bundle chart of a summand, pushed forward, is a strong bundle chart of the disjoint
union. -/
theorem isChart_sigmaPush {i : ι} {c : StrongBundleChart (PX i) (p i)} (hc : (B i).IsChart c) :
    (StrongBundle.sigma B).IsChart (c.sigmaPush (B i).continuous) := by
  rintro _ ⟨j, c', hc', rfl⟩
  by_cases hij : i = j
  · subst hij
    exact (hc c' hc').sigmaPush _
  · exact c.compatible_sigmaPush_of_ne _ hij c' _

theorem liftOneSnd_sigmaPush {i : ι} (c : StrongBundleChart (PX i) (p i)) (u : (B i).One) :
    (c.sigmaPush (B i).continuous).liftOneSnd
      ((StrongBundle.sigma B).oneVal ((sigmaOneEquiv B).symm ⟨i, u⟩)) =
        c.liftOneSnd ((B i).oneVal u) := by
  simp only [oneVal_sigmaOneEquiv_symm, StrongBundleChart.liftOneSnd,
    StrongBundleChart.liftOne, StrongBundleChart.sigmaPush_apply]
  rfl

/-- **Mixed convergence in a summand is mixed convergence in the disjoint union** (Definition
5.1.6 with the pushed chart). -/
theorem MixedTendsto.sigmaMk {i : ι} {w : ℕ → (B i).One} {y : (B i).One}
    (hm : (B i).MixedTendsto w y) :
    (StrongBundle.sigma B).MixedTendsto (fun k => (sigmaOneEquiv B).symm ⟨i, w k⟩)
      ((sigmaOneEquiv B).symm ⟨i, y⟩) := by
  obtain ⟨hP, c, hc, hx, hF, hh⟩ := hm
  refine ⟨(continuous_sigmaMk.tendsto _).comp hP, c.sigmaPush (B i).continuous,
    isChart_sigmaPush hc, mem_image_of_mem _ hx, hF, ?_⟩
  simp only [liftOneSnd_sigmaPush]
  exact hh

/-- Reflexive `(0, 1)`-fibres of the summands give reflexive `(0, 1)`-fibres of the disjoint
union. -/
theorem hasReflexiveFibers_sigma (h : ∀ i, (B i).HasReflexiveFibers) :
    (StrongBundle.sigma B).HasReflexiveFibers := by
  rintro ⟨i, x⟩
  obtain ⟨c, hc, hx, hF⟩ := h i x
  exact ⟨c.sigmaPush (B i).continuous, isChart_sigmaPush hc, mem_image_of_mem _ hx, hF⟩

/-- **Mixed convergence in the disjoint union is, for large `k`, mixed convergence in the summand
of the limit**, when that summand has reflexive `(0, 1)`-fibres (weak convergence in a pushed
chart with reflexive `F₁`, `MixedTendsto.weakTendsto_of_isChart`). -/
theorem MixedTendsto.exists_summand {w : ℕ → (StrongBundle.sigma B).One} {i : ι}
    {y : (B i).One} (hm : (StrongBundle.sigma B).MixedTendsto w ((sigmaOneEquiv B).symm ⟨i, y⟩))
    (hB : (B i).HasReflexiveFibers) :
    ∃ u : ℕ → (B i).One, (∀ᶠ k in atTop, (sigmaOneEquiv B).symm ⟨i, u k⟩ = w k) ∧
      (B i).MixedTendsto u y := by
  classical
  have hev : ∀ᶠ k in atTop, (sigmaOneEquiv B (w k)).1 = i := by
    filter_upwards [hm.1.eventually (isOpen_range_sigmaMk.mem_nhds ⟨_, rfl⟩)] with k hk
    obtain ⟨a, ha⟩ := hk
    exact (congrArg Sigma.fst ha).symm
  let u : ℕ → (B i).One := fun k =>
    if h : (sigmaOneEquiv B (w k)).1 = i then sigmaLift i (sigmaOneEquiv B (w k)) h else y
  have hev' : ∀ᶠ k in atTop, (sigmaOneEquiv B).symm ⟨i, u k⟩ = w k := by
    filter_upwards [hev] with k hk
    simp only [u, dif_pos hk, mk_sigmaLift]
    exact (sigmaOneEquiv B).symm_apply_apply _
  refine ⟨u, hev', ?_⟩
  have hm' : (StrongBundle.sigma B).MixedTendsto (fun k => (sigmaOneEquiv B).symm ⟨i, u k⟩)
      ((sigmaOneEquiv B).symm ⟨i, y⟩) := hm.congr_eventually (hev'.mono fun k hk => hk.symm)
  obtain ⟨c, hc, hx, hF⟩ := hB (p i ((B i).oneVal y))
  have hw := hm'.weakTendsto_of_isChart (isChart_sigmaPush hc) (mem_image_of_mem _ hx) hF
  simp only [liftOneSnd_sigmaPush] at hw
  exact ⟨IsOpenEmbedding.sigmaMk.isInducing.tendsto_nhds_iff.2 hm'.1, c, hc, hx, hF, hw⟩

end SigmaMixed

end StrongBundle

namespace GCT.VectorBundle

open GroupoidalCategory GroupoidalCategory.BanachFunctor

variable {C : GCT.{u}} {V : C.VectorBundle}

namespace StrongPolyfoldBundleConstruction

open StrongBundleUniformizerConstruction StrongBundleUniformizerData PolyfoldConstruction
  SBLocalization EPLocalization

variable {S : C.PolyfoldConstruction} (Q : V.StrongPolyfoldBundleConstruction S)

/-! ### `E_{0,1}` -/

/-- **The objects of bi-regularity `(0, 1)`**, `E_{0,1}`. -/
def IsOneObj (e : V.EObj) : Prop :=
  ∃ c : Q.BundleCoveringFamily, ∃ w : Q.ModelW c.Ψ, w ∈ (Q.modelSEP c.Ψ).B.oneSet ∧
    V.groupoid.π (Q.bundleModelObj c.Ψ w) = V.groupoid.π e

variable {Q}

theorem isOneObj_iff (c : Q.BundleCoveringFamily) (e : V.EObj) :
    Q.IsOneObj e ↔ ∃ w : Q.ModelW c.Ψ, w ∈ (Q.modelSEP c.Ψ).B.oneSet ∧
      V.groupoid.π (Q.bundleModelObj c.Ψ w) = V.groupoid.π e := by
  constructor
  · rintro ⟨c', w', hw', he⟩
    obtain ⟨w, hw⟩ := exists_bundleModelObj_iso c' c w'
    exact ⟨w, (mem_oneSet_iff_of_iso c' c hw).2 hw', hw.trans he⟩
  · rintro ⟨w, hw, he⟩
    exact ⟨c, w, hw, he⟩

theorem IsOneObj.of_π_eq {e e' : V.EObj} (h : Q.IsOneObj e)
    (he : V.groupoid.π e = V.groupoid.π e') : Q.IsOneObj e' := by
  obtain ⟨c, w, hw, h'⟩ := h
  exact ⟨c, w, hw, h'.trans he⟩

theorem isOneObj_bundleModelObj_iff (c : Q.BundleCoveringFamily) (w : Q.ModelW c.Ψ) :
    Q.IsOneObj (Q.bundleModelObj c.Ψ w) ↔ w ∈ (Q.modelSEP c.Ψ).B.oneSet := by
  rw [isOneObj_iff c]
  constructor
  · rintro ⟨w', hw', he⟩
    exact mem_oneSet_of_π_eq (isomorphic_of_bundleModelObj c he.symm) hw'
  · exact fun hw => ⟨w, hw, rfl⟩

variable (Q)

/-- **`|E_{0,1}|` as a subset of `|E|`**. -/
def oneOrbit : Set V.groupoid.OrbitSpace := {z | ∃ e, V.groupoid.π e = z ∧ Q.IsOneObj e}

variable {Q}

theorem π_mem_oneOrbit_iff (e : V.EObj) : V.groupoid.π e ∈ Q.oneOrbit ↔ Q.IsOneObj e :=
  ⟨fun ⟨_, he, h⟩ => h.of_π_eq he, fun h => ⟨e, rfl, h⟩⟩

variable (Q)

/-- `|W[1]| → |E|`, `|w| ↦ |Γ̄(w)|`. -/
def oneEmb (c : Q.BundleCoveringFamily) :
    (Q.modelSEP c.Ψ).E.OneOrbitSpace → V.groupoid.OrbitSpace :=
  (Q.bundleModelFunctor c.Ψ).orbitMap ∘ oneToOrbit (Q.modelSEP c.Ψ)

theorem oneEmb_mk (c : Q.BundleCoveringFamily) (a : (Q.modelSEP c.Ψ).B.One) :
    Q.oneEmb c (Quotient.mk _ a) =
      V.groupoid.π (Q.bundleModelObj c.Ψ ((Q.modelSEP c.Ψ).B.oneVal a)) := rfl

theorem oneEmb_injective (c : Q.BundleCoveringFamily) : Injective (Q.oneEmb c) :=
  (isHomeomorph_bundleModelOrbitMap c.cover).injective.comp (oneToOrbit_injective _)

theorem range_oneEmb (c : Q.BundleCoveringFamily) : range (Q.oneEmb c) = Q.oneOrbit := by
  ext z
  constructor
  · rintro ⟨q, rfl⟩
    induction q using Quotient.inductionOn with | h a => ?_
    exact ⟨_, rfl, (isOneObj_bundleModelObj_iff c _).2 ((Q.modelSEP c.Ψ).B.oneVal_mem a)⟩
  · rintro ⟨e, rfl, he⟩
    obtain ⟨w, hw, h⟩ := (isOneObj_iff c e).1 he
    exact ⟨Quotient.mk _ ((Q.modelSEP c.Ψ).B.oneMk w hw), h⟩

theorem oneEmb_oneOrbitMap (c c' : Q.BundleCoveringFamily) (q : (Q.modelSEP c.Ψ).E.OneOrbitSpace) :
    Q.oneEmb c' ((GenSBMap.rep (Q.isGeneralizedIso_bundleComparison c c')).oneOrbitMap q) =
      Q.oneEmb c q := by
  set hF := Q.isGeneralizedIso_bundleComparison c c'
  set D := GenSBMap.rep hF
  have h1 := SDiagram.oneToOrbit_oneOrbitMap D q
  have h3 := congrFun (congrArg GenSBMap.orbitMap (GenSBMap.cls_rep hF))
    (oneToOrbit (Q.modelSEP c.Ψ) q)
  have h2 := congrFun (Q.orbitMap_bundleComparison c c') (oneToOrbit (Q.modelSEP c.Ψ) q)
  exact (congrArg (Q.bundleModelFunctor c'.Ψ).orbitMap (h1.trans h3)).trans h2

/-- `|W[1]| ≃ |E_{0,1}|`. -/
def oneEquiv (c : Q.BundleCoveringFamily) : (Q.modelSEP c.Ψ).E.OneOrbitSpace ≃ Q.oneOrbit :=
  (Equiv.ofInjective _ (Q.oneEmb_injective c)).trans (Equiv.setCongr (Q.range_oneEmb c))

theorem coe_oneEquiv (c : Q.BundleCoveringFamily) (q : (Q.modelSEP c.Ψ).E.OneOrbitSpace) :
    (Q.oneEquiv c q : V.groupoid.OrbitSpace) = Q.oneEmb c q := rfl

/-- The comparison homeomorphism `|W[1]| ≃ₜ |W'[1]|` of two covering models. -/
def oneCompare (c c' : Q.BundleCoveringFamily) :
    (Q.modelSEP c.Ψ).E.OneOrbitSpace ≃ₜ (Q.modelSEP c'.Ψ).E.OneOrbitSpace where
  toFun := (GenSBMap.rep (Q.isGeneralizedIso_bundleComparison c c')).oneOrbitMap
  invFun := (GenSBMap.rep (Q.isGeneralizedIso_bundleComparison c' c)).oneOrbitMap
  left_inv q := Q.oneEmb_injective c
    ((Q.oneEmb_oneOrbitMap c' c _).trans (Q.oneEmb_oneOrbitMap c c' q))
  right_inv q := Q.oneEmb_injective c'
    ((Q.oneEmb_oneOrbitMap c c' _).trans (Q.oneEmb_oneOrbitMap c' c q))
  continuous_toFun := SDiagram.continuous_oneOrbitMap _
  continuous_invFun := SDiagram.continuous_oneOrbitMap _

theorem oneEquiv_oneCompare (c c' : Q.BundleCoveringFamily)
    (q : (Q.modelSEP c.Ψ).E.OneOrbitSpace) : Q.oneEquiv c' (Q.oneCompare c c' q) = Q.oneEquiv c q :=
  Subtype.ext (Q.oneEmb_oneOrbitMap c c' q)

/-- The topology of `|E_{0,1}|` read in the covering model `c`. -/
@[reducible] def oneTopology (c : Q.BundleCoveringFamily) : TopologicalSpace Q.oneOrbit :=
  TopologicalSpace.coinduced (Q.oneEquiv c) inferInstance

theorem oneTopology_eq (c c' : Q.BundleCoveringFamily) : Q.oneTopology c = Q.oneTopology c' := by
  have e : (Q.oneEquiv c : _ → Q.oneOrbit) = Q.oneEquiv c' ∘ Q.oneCompare c c' :=
    funext fun q => (Q.oneEquiv_oneCompare c c' q).symm
  unfold oneTopology
  rw [e, ← coinduced_compose, (Q.oneCompare c c').coinduced_eq]

/-- **`|E_{0,1}|`** with its topology. -/
def EOneOrbit : Type u := Q.oneOrbit

instance : TopologicalSpace Q.EOneOrbit := ⨅ c : Q.BundleCoveringFamily, Q.oneTopology c

theorem topology_eOneOrbit_eq (c : Q.BundleCoveringFamily) :
    (inferInstance : TopologicalSpace Q.EOneOrbit) = Q.oneTopology c :=
  le_antisymm (iInf_le _ c) (le_iInf fun c' => (Q.oneTopology_eq c c').le)

/-- `|W[1]| ≃ₜ |E_{0,1}|`. -/
def oneHomeomorph (c : Q.BundleCoveringFamily) :
    (Q.modelSEP c.Ψ).E.OneOrbitSpace ≃ₜ Q.EOneOrbit where
  toEquiv := Q.oneEquiv c
  continuous_toFun := by
    change @Continuous _ _ _ (inferInstance : TopologicalSpace Q.EOneOrbit) _
    rw [Q.topology_eOneOrbit_eq c]
    exact continuous_coinduced_rng
  continuous_invFun := by
    change @Continuous _ _ (inferInstance : TopologicalSpace Q.EOneOrbit) _ _
    rw [Q.topology_eOneOrbit_eq c]
    refine continuous_coinduced_dom.2 ?_
    exact continuous_id.congr fun q => ((Q.oneEquiv c).symm_apply_apply q).symm

/-- The class of `e ∈ E_{0,1}` in `|E_{0,1}|`. -/
def oneMk (e : V.EObj) (he : Q.IsOneObj e) : Q.EOneOrbit := ⟨V.groupoid.π e, e, rfl, he⟩

theorem oneHomeomorph_mk (c : Q.BundleCoveringFamily) (a : (Q.modelSEP c.Ψ).B.One) :
    Q.oneHomeomorph c (Quotient.mk _ a) =
      Q.oneMk _ ((isOneObj_bundleModelObj_iff c _).2 ((Q.modelSEP c.Ψ).B.oneVal_mem a)) := rfl


/-! ### Fibres of `E_{0,1}` -/

/-- **The fibre of `E_{0,1}` over `α`**, as a subset of `μ(α)`. -/
def oneFiberSet (α : C.Obj) : Set (V.V α) := {v | Q.IsOneObj (V.objMk α v)}

variable {Q}

theorem isMorInvariant_isOneObj : IsMorInvariant Q.IsOneObj := by
  intro a
  have e : V.groupoid.π (V.groupoid.src a) = V.groupoid.π (V.groupoid.tgt a) :=
    (GroupoidStr.π_eq_π_iff _).2 ⟨a, rfl, rfl⟩
  exact propext ⟨fun h => h.of_π_eq e.symm, fun h => h.of_π_eq e⟩

theorem π_objMk_map (φ : C.Mor) (v : V.V (C.toGroupoidStr.src φ)) :
    V.groupoid.π (V.objMk (C.toGroupoidStr.tgt φ) (V.map φ v)) =
      V.groupoid.π (V.objMk (C.toGroupoidStr.src φ) v) :=
  ((GroupoidStr.π_eq_π_iff _).2 ⟨(⟨(φ, V.objMk _ v), rfl⟩ : V.EMor), rfl, rfl⟩).symm

/-- **The fibre of `E_{0,1}` over `Γ_Ψ(x)` is the image of `(W_{0,1})_x`** under the fibre map of
`Γ̄`. -/
theorem oneFiberSet_model (c : Q.BundleCoveringFamily) (x : S.ModelObj (Q.modelBase c.Ψ)) :
    Q.oneFiberSet ((S.modelFunctor (Q.modelBase c.Ψ)).obj x) =
      Q.bundleModelFiber c.Ψ x '' {v | (v : Q.ModelW c.Ψ) ∈ (Q.modelSEP c.Ψ).B.oneSet} := by
  ext u
  constructor
  · intro hu
    refine ⟨(Q.bundleModelFiber c.Ψ x).symm u, ?_, (Q.bundleModelFiber c.Ψ x).apply_symm_apply u⟩
    have h := Q.objMk_bundleModelFiber c.Ψ x ((Q.bundleModelFiber c.Ψ x).symm u)
    rw [ContinuousLinearEquiv.apply_symm_apply] at h
    change Q.IsOneObj _ at hu
    rw [h] at hu
    exact (isOneObj_bundleModelObj_iff c _).1 hu
  · rintro ⟨v, hv, rfl⟩
    change Q.IsOneObj _
    rw [Q.objMk_bundleModelFiber c.Ψ x v]
    exact (isOneObj_bundleModelObj_iff c _).2 hv

/-! ### Complete norms on a fibre -/

/-- **`n` defines a complete norm on `A`** (Definition 18.1.7 (2), values in `[0, ∞]`): finite,
definite, homogeneous and subadditive on `A`, and `n`-Cauchy sequences in `A` converge in `n` to
a point of `A`. -/
structure IsCompleteNormOn {F : Type*} [AddCommGroup F] [Module ℝ F] (n : F → ℝ≥0∞)
    (A : Set F) : Prop where
  ne_top : ∀ v ∈ A, n v ≠ ⊤
  eq_zero : ∀ v ∈ A, n v = 0 → v = 0
  smul : ∀ (t : ℝ), ∀ v ∈ A, n (t • v) = ENNReal.ofReal |t| * n v
  add_le : ∀ v ∈ A, ∀ w ∈ A, n (v + w) ≤ n v + n w
  complete : ∀ u : ℕ → F, (∀ k, u k ∈ A) →
    (∀ ε > 0, ∃ m, ∀ i ≥ m, ∀ j ≥ m, n (u i - u j) < ε) →
      ∃ v ∈ A, Tendsto (fun k => n (u k - v)) atTop (𝓝 0)

/-- A complete norm transported along a linear isomorphism. -/
theorem IsCompleteNormOn.map {F G : Type*} [AddCommGroup F] [Module ℝ F] [AddCommGroup G]
    [Module ℝ G] (T : F ≃ₗ[ℝ] G) {n : F → ℝ≥0∞} {n' : G → ℝ≥0∞} {A : Set F} {A' : Set G}
    (hA : A' = T '' A) (hn : ∀ v, n' (T v) = n v) (h : IsCompleteNormOn n A) :
    IsCompleteNormOn n' A' := by
  subst hA
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    rw [hn]; exact h.ne_top v hv
  · rintro _ ⟨v, hv, rfl⟩ h0
    rw [hn] at h0
    rw [h.eq_zero v hv h0, map_zero]
  · rintro t _ ⟨v, hv, rfl⟩
    rw [← map_smul, hn, hn]; exact h.smul t v hv
  · rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
    rw [← map_add, hn, hn, hn]; exact h.add_le v hv w hw
  · intro u hu hC
    choose v hv hvu using hu
    have e : ∀ i j, n' (u i - u j) = n (v i - v j) := fun i j => by
      rw [← hvu i, ← hvu j, ← map_sub, hn]
    obtain ⟨v₀, hv₀, ht⟩ := h.complete v hv (fun ε hε => by
      obtain ⟨m, hm⟩ := hC ε hε
      exact ⟨m, fun i hi j hj => (e i j) ▸ hm i hi j hj⟩)
    refine ⟨T v₀, ⟨v₀, hv₀, rfl⟩, ?_⟩
    have e' : ∀ k, n' (u k - T v₀) = n (v k - v₀) := fun k => by
      rw [← hvu k, ← map_sub, hn]
    simp only [e']
    exact ht

variable (Q) in
/-- **Definition 18.1.7 (2) at `α`**: `N` defines a complete norm on the fibre of `E_{0,1}` over
`α`. -/
def FiberCond (N : V.EObj → ℝ≥0∞) (α : C.Obj) : Prop :=
  IsCompleteNormOn (fun v : V.V α => N (V.objMk α v)) (Q.oneFiberSet α)

/-- **The fibre condition moves along morphisms** (`μ(φ)` is a linear isomorphism preserving
`N` and `E_{0,1}`). -/
theorem fiberCond_tgt {N : V.EObj → ℝ≥0∞} (hN : IsMorInvariant N) (φ : C.Mor)
    (h : Q.FiberCond N (C.toGroupoidStr.src φ)) : Q.FiberCond N (C.toGroupoidStr.tgt φ) := by
  refine IsCompleteNormOn.map (V.map φ).toLinearEquiv ?_ (fun v => hN.apply_map φ v) h
  ext u
  constructor
  · intro hu
    refine ⟨(V.map φ).symm u, ?_, (V.map φ).apply_symm_apply u⟩
    change Q.IsOneObj _
    refine IsOneObj.of_π_eq ?_ (π_objMk_map φ _)
    change Q.IsOneObj _ at hu
    rwa [(V.map φ).apply_symm_apply]
  · rintro ⟨v, hv, rfl⟩
    exact IsOneObj.of_π_eq hv (π_objMk_map φ v).symm

theorem fiberCond_of_isomorphic {N : V.EObj → ℝ≥0∞} (hN : IsMorInvariant N) {α β : C.Obj}
    (h : C.toGroupoidStr.Isomorphic α β) (hα : Q.FiberCond N α) : Q.FiberCond N β := by
  obtain ⟨φ, hs, ht⟩ := h
  subst hs ht
  exact fiberCond_tgt hN φ hα


/-- **A real complete norm on `M` and a `[0, ∞]`-valued complete norm on `L(M)`** are the same
thing, for an injective linear `L` with `m = n ∘ L` (finite). -/
theorem isCompleteNormOn_range_iff {M F : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup F]
    [Module ℝ F] (L : M →ₗ[ℝ] F) (hL : Injective L) (n : F → ℝ≥0∞) (m : M → ℝ)
    (hfin : ∀ v, n (L v) ≠ ⊤) (hm : ∀ v, m v = (n (L v)).toReal) :
    ((∀ v, m v = 0 → v = 0) ∧ (∀ (t : ℝ) v, m (t • v) = |t| * m v) ∧
        (∀ v w, m (v + w) ≤ m v + m w) ∧
        (∀ u : ℕ → M, (∀ ε > 0, ∃ k, ∀ i ≥ k, ∀ j ≥ k, m (u i - u j) < ε) →
          ∃ v, Tendsto (fun k => m (u k - v)) atTop (𝓝 0))) ↔
      IsCompleteNormOn n (range L) := by
  have hn : ∀ v, n (L v) = ENNReal.ofReal (m v) := fun v => by
    rw [hm, ENNReal.ofReal_toReal (hfin v)]
  have hm0 : ∀ v, 0 ≤ m v := fun v => by rw [hm]; exact ENNReal.toReal_nonneg
  constructor
  · rintro ⟨h0, hs, ha, hc⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨v, rfl⟩; exact hfin v
    · rintro _ ⟨v, rfl⟩ hv
      rw [h0 v (by rw [hm, hv, ENNReal.toReal_zero]), map_zero]
    · rintro t _ ⟨v, rfl⟩
      rw [← map_smul, hn, hn, hs, ENNReal.ofReal_mul (abs_nonneg t)]
    · rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
      rw [← map_add, hn, hn, hn, ← ENNReal.ofReal_add (hm0 v) (hm0 w)]
      exact ENNReal.ofReal_le_ofReal (ha v w)
    · intro u hu hC
      choose v hv using hu
      have e : ∀ i j, n (u i - u j) = ENNReal.ofReal (m (v i - v j)) := fun i j => by
        rw [← hv i, ← hv j, ← map_sub, hn]
      obtain ⟨v₀, ht⟩ := hc v fun ε hε => by
        obtain ⟨k, hk⟩ := hC (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
        refine ⟨k, fun i hi j hj => ?_⟩
        have := hk i hi j hj
        rw [e] at this
        exact (ENNReal.ofReal_lt_ofReal_iff hε).1 this
      refine ⟨L v₀, ⟨v₀, rfl⟩, ?_⟩
      have e' : ∀ k, n (u k - L v₀) = ENNReal.ofReal (m (v k - v₀)) := fun k => by
        rw [← hv k, ← map_sub, hn]
      simp only [e']
      have := ENNReal.tendsto_ofReal ht
      rwa [ENNReal.ofReal_zero] at this
  · intro h
    refine ⟨fun v hv => ?_, fun t v => ?_, fun v w => ?_, fun u hu => ?_⟩
    · have h1 : n (L v) = 0 := by
        rw [hm, ENNReal.toReal_eq_zero_iff] at hv
        exact hv.resolve_right (hfin v)
      exact hL ((h.eq_zero _ ⟨v, rfl⟩ h1).trans (map_zero L).symm)
    · rw [hm, hm, map_smul, h.smul t _ ⟨v, rfl⟩, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (abs_nonneg t)]
    · rw [hm, hm, hm, map_add, ← ENNReal.toReal_add (hfin v) (hfin w)]
      exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin v, hfin w⟩)
        (h.add_le _ ⟨v, rfl⟩ _ ⟨w, rfl⟩)
    · obtain ⟨_, ⟨v₀, rfl⟩, ht⟩ := h.complete (fun k => L (u k)) (fun k => ⟨u k, rfl⟩)
        fun ε hε => by
          obtain ⟨r, -, hr0, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
          obtain ⟨k, hk⟩ := hu r (ENNReal.ofReal_pos.1 hr0)
          refine ⟨k, fun i hi j hj => ?_⟩
          rw [← map_sub, hn]
          exact ((ENNReal.ofReal_lt_ofReal_iff (ENNReal.ofReal_pos.1 hr0)).2
            (hk i hi j hj)).trans hrε
      refine ⟨v₀, ?_⟩
      have e : ∀ k, m (u k - v₀) = (n (L (u k) - L v₀)).toReal := fun k => by
        rw [hm, map_sub]
      simp only [e]
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht
      rwa [ENNReal.toReal_zero] at this

/-- **The fibre condition in a model at `x` is the fibre condition at `Γ_Ψ(x)`**: Definition
5.1.1 (1) for `N ∘ Γ̄` on `(W_{0,1})_x` iff Definition 18.1.7 (2) at `Γ_Ψ(x)`. -/
theorem isCompleteFiberNorm_iff_fiberCond (c : Q.BundleCoveringFamily) {N : V.EObj → ℝ≥0∞}
    (hfin : ∀ w ∈ (Q.modelSEP c.Ψ).B.oneSet, Q.bundlePull c.Ψ N w ≠ ⊤)
    (x : S.ModelObj (Q.modelBase c.Ψ)) :
    (Q.modelSEP c.Ψ).B.IsCompleteFiberNorm (Q.modelNorm c.Ψ N) x ↔
      Q.FiberCond N ((S.modelFunctor (Q.modelBase c.Ψ)).obj x) := by
  let _ : ∀ y : S.ModelObj (Q.modelBase c.Ψ), AddCommGroup ((Q.modelSEP c.Ψ).P ⁻¹' {y}) :=
    (Q.modelSEP c.Ψ).instAdd
  let _ : ∀ y : S.ModelObj (Q.modelBase c.Ψ), Module ℝ ((Q.modelSEP c.Ψ).P ⁻¹' {y}) :=
    (Q.modelSEP c.Ψ).instModule
  let L : (Q.modelSEP c.Ψ).B.oneFiber x →ₗ[ℝ] V.V ((S.modelFunctor (Q.modelBase c.Ψ)).obj x) :=
    (Q.bundleModelFiber c.Ψ x).toLinearMap.comp ((Q.modelSEP c.Ψ).B.oneFiber x).subtype
  have hL : Injective L := (Q.bundleModelFiber c.Ψ x).injective.comp Subtype.val_injective
  have hval : ∀ v : (Q.modelSEP c.Ψ).B.oneFiber x, V.objMk _ (L v) =
      Q.bundleModelObj c.Ψ v.1.1 := fun v =>
    Q.objMk_bundleModelFiber c.Ψ x v.1
  have hfin' : ∀ v, (fun u => N (V.objMk _ u)) (L v) ≠ ⊤ := fun v => by
    change N (V.objMk _ (L v)) ≠ ⊤
    rw [hval]; exact hfin _ v.2
  have hm : ∀ v, Q.modelNorm c.Ψ N ((Q.modelSEP c.Ψ).B.toOne v) =
      ((fun u => N (V.objMk _ u)) (L v)).toReal :=
    fun v => by
      change (N (Q.bundleModelObj c.Ψ _)).toReal = (N (V.objMk _ (L v))).toReal
      rw [hval]
      rfl
  have hA : Q.oneFiberSet ((S.modelFunctor (Q.modelBase c.Ψ)).obj x) = range L := by
    rw [oneFiberSet_model c x]
    ext u
    exact ⟨fun ⟨w, hw, he⟩ => ⟨⟨w, hw⟩, he⟩, fun ⟨v, he⟩ => ⟨v.1, v.2, he⟩⟩
  unfold FiberCond
  rw [hA, ← isCompleteNormOn_range_iff L hL _ _ hfin' hm]
  exact ⟨fun h => ⟨h.eq_zero, h.smul, h.add_le, h.complete⟩,
    fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩⟩


/-! ### Definition 18.1.7 -/

variable (Q) in
/-- The point of `|E|` of a point of `|E_{0,1}|`. -/
def oneClass (z : Q.EOneOrbit) : V.groupoid.OrbitSpace := (z : Q.oneOrbit).1

theorem EOneOrbit.ext {z z' : Q.EOneOrbit} (h : Q.oneClass z = Q.oneClass z') : z = z' :=
  Subtype.ext h

@[simp] theorem oneClass_oneMk (e : V.EObj) (he : Q.IsOneObj e) :
    Q.oneClass (Q.oneMk e he) = V.groupoid.π e := rfl

variable (Q) in
/-- **`|N| : |E_{0,1}| → [0, ∞]`**, the value of `N` at a representative. -/
def oneNorm (N : V.EObj → ℝ≥0∞) (z : Q.EOneOrbit) : ℝ≥0∞ := N (Q.oneClass z).out

theorem oneNorm_oneMk {N : V.EObj → ℝ≥0∞} (hN : IsMorInvariant N) (e : V.EObj)
    (he : Q.IsOneObj e) : Q.oneNorm N (Q.oneMk e he) = N e :=
  hN.eq_of_isomorphic ((GroupoidStr.π_eq_π_iff _).1 (Quotient.out_eq _))

variable (Q) in
/-- **Definition 18.1.7, p. 846, as printed**: a functor `N : E → [0, ∞]` with
(1) `N(e) = +∞` for `e ∉ E_{0,1}`,
(2) on every fibre of `E_{0,1}` a complete norm,
(3) if `|h_k| ∈ |E_{0,1}|`, `|P(h_k)| → |α|` and `|N|(|h_k|) → 0`, then `|h_k| → |0_α|` in
`|E_{0,1}|`. -/
structure IsAuxNormBook (N : V.EObj → ℝ≥0∞) : Prop where
  isMorInvariant : IsMorInvariant N
  eq_top : ∀ e, ¬ Q.IsOneObj e → N e = ⊤
  fiber : ∀ α, Q.FiberCond N α
  tendsto_zero : ∀ (h : ℕ → V.EObj) (hh : ∀ k, Q.IsOneObj (h k)) (α : C.Obj) (z : Q.EOneOrbit),
    Q.oneClass z = V.groupoid.π (V.objMk α 0) →
    Tendsto (fun k => C.toGroupoidStr.π (V.base (h k))) atTop (𝓝 (C.toGroupoidStr.π α)) →
    Tendsto (fun k => N (h k)) atTop (𝓝 0) →
    Tendsto (fun k => Q.oneMk (h k) (hh k)) atTop (𝓝 z)

variable (Q) in
/-- **Definition 18.1.7 with the continuity of `|N|` on `|E_{0,1}|`** (the continuity required in
Definition 12.2.1, whose notion the text imports). -/
structure IsAuxNormDirect (N : V.EObj → ℝ≥0∞) : Prop extends Q.IsAuxNormBook N where
  continuous : Continuous (Q.oneNorm N)

/-! ### Lemma 18.1.8 -/

theorem exists_bundleModelObj_eq (c : Q.BundleCoveringFamily) (e : V.EObj) :
    ∃ w : Q.ModelW c.Ψ, V.groupoid.π (Q.bundleModelObj c.Ψ w) = V.groupoid.π e := by
  obtain ⟨z, hz⟩ := (isHomeomorph_bundleModelOrbitMap c.cover).surjective (V.groupoid.π e)
  induction z using Quotient.inductionOn with | h w => exact ⟨w, hz⟩

theorem bundleModelObj_fiberZero (c : Q.BundleCoveringFamily) (x : S.ModelObj (Q.modelBase c.Ψ)) :
    Q.bundleModelObj c.Ψ (fiberZero (Q.modelP c.Ψ) x) =
      V.objMk ((S.modelFunctor (Q.modelBase c.Ψ)).obj x) 0 := by
  refine (Q.objMk_bundleModelFiber c.Ψ x 0).symm.trans ?_
  rw [map_zero]

theorem π_objMk_zero_of_isomorphic {α β : C.Obj} (h : C.toGroupoidStr.Isomorphic α β) :
    V.groupoid.π (V.objMk α 0) = V.groupoid.π (V.objMk β 0) := by
  obtain ⟨φ, hs, ht⟩ := h
  subst hs ht
  have := π_objMk_map (V := V) φ 0
  rw [map_zero] at this
  exact this.symm

/-- `|P|(|e|) = |P(e)|`, read through a model: `|Γ_Ψ|(|P_W(w)|) = |P(e)|` for `|Γ̄(w)| = |e|`. -/
theorem modelOrbit_base_eq (c : Q.BundleCoveringFamily) {w : Q.ModelW c.Ψ} {e : V.EObj}
    (h : V.groupoid.π (Q.bundleModelObj c.Ψ w) = V.groupoid.π e) :
    (S.modelFunctor (Q.modelBase c.Ψ)).orbitMap ((Q.modelSEP c.Ψ).X.π (Q.modelP c.Ψ w)) =
      C.toGroupoidStr.π (V.base e) :=
  congrArg V.proj.orbitMap h

/-- **Lemma 18.1.8, "⇐", condition (3)**: an auxiliary norm in a covering model satisfies
Definition 18.1.7 (3) (lift `|P(h_k)| → |α|` to the model, move the representatives along
morphisms, apply Definition 12.2.1 (2) there). -/
theorem IsAuxNormIn.tendsto_oneMk {c : Q.BundleCoveringFamily} {N : V.EObj → ℝ≥0∞}
    (hN : Q.IsAuxNormIn c.Ψ N) (h : ℕ → V.EObj) (hh : ∀ k, Q.IsOneObj (h k)) (α : C.Obj)
    (z : Q.EOneOrbit) (hz : Q.oneClass z = V.groupoid.π (V.objMk α 0))
    (hP : Tendsto (fun k => C.toGroupoidStr.π (V.base (h k))) atTop (𝓝 (C.toGroupoidStr.π α)))
    (h0 : Tendsto (fun k => N (h k)) atTop (𝓝 0)) :
    Tendsto (fun k => Q.oneMk (h k) (hh k)) atTop (𝓝 z) := by
  classical
  obtain ⟨x, φ, hs, ht⟩ := (GroupoidFunctor.essSurj_iff _).1 (modelFunctor_essSurj c.cover) α
  have hxα : C.toGroupoidStr.Isomorphic ((S.modelFunctor (Q.modelBase c.Ψ)).obj x) α :=
    ⟨φ, hs, ht⟩
  have hw : ∀ k, ∃ w : Q.ModelW c.Ψ, w ∈ (Q.modelSEP c.Ψ).B.oneSet ∧
      V.groupoid.π (Q.bundleModelObj c.Ψ w) = V.groupoid.π (h k) :=
    fun k => (isOneObj_iff c _).1 (hh k)
  choose w hwo hwe using hw
  set a : ℕ → (Q.modelSEP c.Ψ).B.One := fun k => (Q.modelSEP c.Ψ).B.oneMk (w k) (hwo k)
  let hH := (isHomeomorph_modelOrbitMap c.cover).homeomorph
  have h1 : Tendsto (fun k => (Q.modelSEP c.Ψ).X.π ((Q.modelSEP c.Ψ).P
      ((Q.modelSEP c.Ψ).B.oneVal (a k)))) atTop (𝓝 ((Q.modelSEP c.Ψ).X.π x)) := by
    have e1 : hH ((Q.modelSEP c.Ψ).X.π x) = C.toGroupoidStr.π α :=
      (GroupoidStr.π_eq_π_iff _).2 hxα
    have h2 := hP.congr fun k => (modelOrbit_base_eq c (hwe k)).symm
    rw [← e1] at h2
    exact hH.isInducing.tendsto_nhds_iff.2 h2
  obtain ⟨v, hv, hvx⟩ := EpGroupoid.exists_lift_tendsto (X := (Q.modelSEP c.Ψ).X) h1
  have hφ : ∀ k, ∃ ψ : (Q.modelSEP c.Ψ).Mor,
      (Q.modelSEP c.Ψ).X.src ψ = (Q.modelSEP c.Ψ).P ((Q.modelSEP c.Ψ).B.oneVal (a k)) ∧
      (Q.modelSEP c.Ψ).X.tgt ψ = v k := fun k => (GroupoidStr.π_eq_π_iff _).1 (hv k).symm
  choose ψ hψs hψt using hφ
  have hb := fun k => (Q.modelSEP c.Ψ).E.exists_oneVal_eq_μ (a k) (ψ k) (hψs k).symm
  choose b hb using hb
  have hπb : ∀ k, (Q.modelSEP c.Ψ).E.toEpGroupoid.π ((Q.modelSEP c.Ψ).B.oneVal (b k)) =
      (Q.modelSEP c.Ψ).E.toEpGroupoid.π ((Q.modelSEP c.Ψ).B.oneVal (a k)) := fun k => by
    rw [hb k, EpStrongBundle.π_μ]
  have hPb : ∀ k, (Q.modelSEP c.Ψ).P ((Q.modelSEP c.Ψ).B.oneVal (b k)) = v k := fun k => by
    rw [hb k, EpStrongBundle.P_μ (E := (Q.modelSEP c.Ψ).E)]
    exact hψt k
  have hEb : ∀ k, V.groupoid.π (Q.bundleModelObj c.Ψ ((Q.modelSEP c.Ψ).B.oneVal (b k))) =
      V.groupoid.π (h k) := fun k =>
    (congrArg (Q.bundleModelFunctor c.Ψ).orbitMap (hπb k)).trans (hwe k)
  have hNb : ∀ k, Q.modelNorm c.Ψ N (b k) = (N (h k)).toReal := fun k =>
    congrArg ENNReal.toReal (hN.isMorInvariant.eq_of_isomorphic
      ((GroupoidStr.π_eq_π_iff _).1 (hEb k)))
  have hbt : Tendsto b atTop (𝓝 ((Q.modelSEP c.Ψ).B.zeroOne x)) := by
    refine hN.isAuxNorm.isAuxNorm.tendsto_zeroOne b x ?_ ?_
    · simp only [hPb]; exact hvx
    · simp only [hNb]
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h0
      rwa [ENNReal.toReal_zero] at this
  have hlim := ((Q.oneHomeomorph c).continuous.tendsto _).comp
    ((continuous_quotient_mk'.tendsto _).comp hbt)
  have e1 : (fun k => Q.oneMk (h k) (hh k)) =
      (Q.oneHomeomorph c) ∘ (fun k => (Quotient.mk _ (b k) : (Q.modelSEP c.Ψ).E.OneOrbitSpace)) :=
    funext fun k => EOneOrbit.ext (hEb k).symm
  have e2 : Q.oneHomeomorph c (Quotient.mk _ ((Q.modelSEP c.Ψ).B.zeroOne x)) = z := by
    refine EOneOrbit.ext ?_
    rw [hz]
    change V.groupoid.π (Q.bundleModelObj c.Ψ (fiberZero (Q.modelP c.Ψ) x)) = _
    exact (congrArg V.groupoid.π (bundleModelObj_fiberZero c x)).trans
      (π_objMk_zero_of_isomorphic hxα)
  rw [e1, ← e2]
  exact hlim


/-- `|N|` read in a model: `|N|(|Γ̄(a)|) = N(Γ̄(a))`. -/
theorem oneNorm_oneHomeomorph_mk (c : Q.BundleCoveringFamily) {N : V.EObj → ℝ≥0∞}
    (hN : IsMorInvariant N) (a : (Q.modelSEP c.Ψ).B.One) :
    Q.oneNorm N (Q.oneHomeomorph c (Quotient.mk _ a)) =
      Q.bundlePull c.Ψ N ((Q.modelSEP c.Ψ).B.oneVal a) :=
  oneNorm_oneMk hN _ ((isOneObj_bundleModelObj_iff c _).2 ((Q.modelSEP c.Ψ).B.oneVal_mem a))

/-- **Lemma 18.1.8, "⇐", the continuity**: for an auxiliary norm in a covering model, `|N|` is
continuous on `|E_{0,1}|`. -/
theorem IsAuxNormIn.continuous_oneNorm {c : Q.BundleCoveringFamily} {N : V.EObj → ℝ≥0∞}
    (hN : Q.IsAuxNormIn c.Ψ N) : Continuous (Q.oneNorm N) := by
  let g : (Q.modelSEP c.Ψ).E.OneOrbitSpace → ℝ≥0∞ :=
    Quotient.lift (fun a => ENNReal.ofReal (Q.modelNorm c.Ψ N a)) fun a b hab =>
      congrArg ENNReal.ofReal (hN.isAuxNorm.isOneInvariant a b (Quotient.sound hab))
  have hg : Continuous g :=
    (ENNReal.continuous_ofReal.comp hN.isAuxNorm.isAuxNorm.continuous).quotient_lift _
  have e : Q.oneNorm N = g ∘ (Q.oneHomeomorph c).symm := by
    funext z
    obtain ⟨q, rfl⟩ := (Q.oneHomeomorph c).surjective z
    induction q using Quotient.inductionOn with | h a => ?_
    rw [Function.comp_apply, Homeomorph.symm_apply_apply, oneNorm_oneHomeomorph_mk c
      hN.isMorInvariant]
    exact (ENNReal.ofReal_toReal (hN.ne_top _ ((Q.modelSEP c.Ψ).B.oneVal_mem a))).symm
  rw [e]
  exact hg.comp (Q.oneHomeomorph c).symm.continuous

/-- **Lemma 18.1.8, "⇐"**: an auxiliary norm in a covering model (Definition 12.2.1 for
`N ∘ Γ̄_Ψ̄`) satisfies Definition 18.1.7 as printed. -/
theorem IsAuxNormIn.isAuxNormBook {c : Q.BundleCoveringFamily} {N : V.EObj → ℝ≥0∞}
    (hN : Q.IsAuxNormIn c.Ψ N) : Q.IsAuxNormBook N where
  isMorInvariant := hN.isMorInvariant
  eq_top e he := by
    obtain ⟨w, hw⟩ := exists_bundleModelObj_eq c e
    have hwo : w ∉ (Q.modelSEP c.Ψ).B.oneSet := fun h' =>
      he (((isOneObj_bundleModelObj_iff c w).2 h').of_π_eq hw)
    rw [← hN.isMorInvariant.eq_of_isomorphic ((GroupoidStr.π_eq_π_iff _).1 hw)]
    exact hN.eq_top w hwo
  fiber α := by
    obtain ⟨x, φ, hs, ht⟩ := (GroupoidFunctor.essSurj_iff _).1 (modelFunctor_essSurj c.cover) α
    refine fiberCond_of_isomorphic hN.isMorInvariant ⟨φ, hs, ht⟩ ?_
    exact (isCompleteFiberNorm_iff_fiberCond c hN.ne_top x).1 (hN.isAuxNorm.isAuxNorm.fiber x)
  tendsto_zero := hN.tendsto_oneMk

theorem IsAuxNormIn.isAuxNormDirect {c : Q.BundleCoveringFamily} {N : V.EObj → ℝ≥0∞}
    (hN : Q.IsAuxNormIn c.Ψ N) : Q.IsAuxNormDirect N :=
  ⟨hN.isAuxNormBook, hN.continuous_oneNorm⟩

/-- Definition 18.1.7 (2) gives finiteness on `E_{0,1}`. -/
theorem IsAuxNormBook.ne_top {N : V.EObj → ℝ≥0∞} (h : Q.IsAuxNormBook N) (e : V.EObj)
    (he : Q.IsOneObj e) : N e ≠ ⊤ :=
  (h.fiber e.1).ne_top e.2 he

theorem IsAuxNormBook.oneNorm_ne_top {N : V.EObj → ℝ≥0∞} (h : Q.IsAuxNormBook N)
    (z : Q.EOneOrbit) : Q.oneNorm N z ≠ ⊤ := by
  obtain ⟨e, he, hz⟩ := (z : Q.oneOrbit).2
  refine h.ne_top _ (hz.of_π_eq ?_)
  rw [he]
  exact (Quotient.out_eq _).symm

/-- **Lemma 18.1.8, "⇒"**: Definition 18.1.7 with the continuity of `|N|` gives an auxiliary norm
in every covering model.  Condition (3) of Definition 12.2.1 is reached through an auxiliary norm
`N₀` of the model (Theorem 12.2.2): `|h_k| → |0_x|` in `|W[1]|` and the continuity of `N₀` give
`N₀(h_k) → 0`, hence `h_k → 0_x` in `W_{0,1}`. -/
theorem IsAuxNormDirect.isAuxNormIn {N : V.EObj → ℝ≥0∞} (h : Q.IsAuxNormDirect N)
    (c : Q.BundleCoveringFamily) : Q.IsAuxNormIn c.Ψ N := by
  have hinv := h.isMorInvariant
  have hfin : ∀ w ∈ (Q.modelSEP c.Ψ).B.oneSet, Q.bundlePull c.Ψ N w ≠ ⊤ := fun w hw =>
    h.ne_top _ ((isOneObj_bundleModelObj_iff c w).2 hw)
  have hval : ∀ a : (Q.modelSEP c.Ψ).B.One, Q.modelNorm c.Ψ N a =
      (Q.oneNorm N (Q.oneHomeomorph c (Quotient.mk _ a))).toReal := fun a => by
    rw [oneNorm_oneHomeomorph_mk c hinv]; rfl
  refine ⟨hinv, fun w hw => h.eq_top _ fun h' => hw ((isOneObj_bundleModelObj_iff c w).1 h'),
    hfin, ⟨⟨?_, fun x => ?_, fun w x hP h0 => ?_⟩, fun a b ψ hb e => ?_⟩⟩
  · have e : Q.modelNorm c.Ψ N =
        (ENNReal.toReal ∘ Q.oneNorm N) ∘ (Q.oneHomeomorph c) ∘ Quotient.mk _ :=
      funext hval
    rw [e]
    refine (ENNReal.continuousOn_toReal.comp_continuous h.continuous fun z =>
      h.oneNorm_ne_top z).comp ((Q.oneHomeomorph c).continuous.comp continuous_quotient_mk')
  · exact (isCompleteFiberNorm_iff_fiberCond c hfin x).2 (h.fiber _)
  · -- Definition 18.1.7 (3) in the model, then an auxiliary norm `N₀` of the model
    obtain ⟨N₀, hN₀⟩ := (Q.modelSEP c.Ψ).E.theorem_12_2_2 (hasParacompactOrbitSpace_model c)
    have hP' : Tendsto (fun k => C.toGroupoidStr.π (V.base (Q.bundleModelObj c.Ψ
        ((Q.modelSEP c.Ψ).B.oneVal (w k))))) atTop
        (𝓝 (C.toGroupoidStr.π ((S.modelFunctor (Q.modelBase c.Ψ)).obj x))) :=
      (((isHomeomorph_modelOrbitMap c.cover).continuous.comp
        (Q.modelSEP c.Ψ).X.continuous_π).tendsto x).comp hP
    have h0' : Tendsto (fun k => N (Q.bundleModelObj c.Ψ ((Q.modelSEP c.Ψ).B.oneVal (w k))))
        atTop (𝓝 0) := by
      have e : ∀ k, N (Q.bundleModelObj c.Ψ ((Q.modelSEP c.Ψ).B.oneVal (w k))) =
          ENNReal.ofReal (Q.modelNorm c.Ψ N (w k)) := fun k =>
        (ENNReal.ofReal_toReal (hfin _ ((Q.modelSEP c.Ψ).B.oneVal_mem _))).symm
      simp only [e]
      have := ENNReal.tendsto_ofReal h0
      rwa [ENNReal.ofReal_zero] at this
    have hone : ∀ k, Q.IsOneObj (Q.bundleModelObj c.Ψ ((Q.modelSEP c.Ψ).B.oneVal (w k))) :=
      fun k => (isOneObj_bundleModelObj_iff c _).2 ((Q.modelSEP c.Ψ).B.oneVal_mem _)
    have h3 := h.tendsto_zero _ hone _
      (Q.oneHomeomorph c (Quotient.mk _ ((Q.modelSEP c.Ψ).B.zeroOne x)))
      (congrArg V.groupoid.π (bundleModelObj_fiberZero c x)) hP' h0'
    have h4 : Tendsto (fun k => (Quotient.mk _ (w k) : (Q.modelSEP c.Ψ).E.OneOrbitSpace)) atTop
        (𝓝 (Quotient.mk _ ((Q.modelSEP c.Ψ).B.zeroOne x))) := by
      have := ((Q.oneHomeomorph c).symm.continuous.tendsto _).comp h3
      simp only [Homeomorph.symm_apply_apply] at this
      refine this.congr fun k => ?_
      exact (Q.oneHomeomorph c).symm_apply_apply (Quotient.mk _ (w k))
    let g : (Q.modelSEP c.Ψ).E.OneOrbitSpace → ℝ :=
      Quotient.lift N₀ fun a b hab => hN₀.isOneInvariant a b (Quotient.sound hab)
    have hg : Continuous g := hN₀.isAuxNorm.continuous.quotient_lift _
    have h5 : Tendsto (fun k => N₀ (w k)) atTop (𝓝 0) := by
      have := (hg.tendsto _).comp h4
      have e0 : g (Quotient.mk _ ((Q.modelSEP c.Ψ).B.zeroOne x)) = 0 :=
        (hN₀.isAuxNorm.fiber x).map_zero
      rw [e0] at this
      exact this
    exact hN₀.isAuxNorm.tendsto_zeroOne w x hP h5
  · change (Q.bundlePull c.Ψ N ((Q.modelSEP c.Ψ).B.oneVal a)).toReal =
      (Q.bundlePull c.Ψ N ((Q.modelSEP c.Ψ).B.oneVal b)).toReal
    rw [e]
    exact congrArg ENNReal.toReal (Q.bundlePull_μ c.Ψ hinv _)

/-- **Lemma 18.1.8, p. 847** (with the continuity of `|N|` that Definition 12.2.1 requires):
`N : E → [0, ∞]` is an auxiliary norm iff `N ∘ Γ̄_Ψ̄` is an auxiliary norm of `W_Ψ̄ → X_Ψ`
(Definition 12.2.1) for a covering family. -/
theorem lemma_18_1_8 (c : Q.BundleCoveringFamily) {N : V.EObj → ℝ≥0∞} :
    Q.IsAuxNormDirect N ↔ Q.IsAuxNormIn c.Ψ N :=
  ⟨fun h => h.isAuxNormIn c, fun h => h.isAuxNormDirect⟩

/-- Lemma 18.1.8 with "every covering family": the direct form of Definition 18.1.7 is the model
reading `IsAuxNormFunctor` used in §18.2. -/
theorem isAuxNormDirect_iff_isAuxNormFunctor (c : Q.BundleCoveringFamily) {N : V.EObj → ℝ≥0∞} :
    Q.IsAuxNormDirect N ↔ Q.IsAuxNormFunctor N :=
  ⟨fun h c' => h.isAuxNormIn c', fun h => (h c).isAuxNormDirect⟩

/-! ### Theorem 18.1.12 -/

/-- For `|Γ̄(w)| = |e|`, the value of a functor `N` at `e` is `N ∘ Γ̄(w)`. -/
theorem bundlePull_eq_of_π_eq {c : Q.BundleCoveringFamily} {N : V.EObj → ℝ≥0∞}
    (hN : IsMorInvariant N) {w : Q.ModelW c.Ψ} {e : V.EObj}
    (h : V.groupoid.π (Q.bundleModelObj c.Ψ w) = V.groupoid.π e) : Q.bundlePull c.Ψ N w = N e :=
  hN.eq_of_isomorphic ((GroupoidStr.π_eq_π_iff _).1 h)

/-- **Theorem 18.1.12 (1), p. 848**: a strong polyfold bundle with `F̄(α) ≠ ∅` admits an
auxiliary norm (Definition 18.1.7 in the direct form). -/
theorem theorem_18_1_12_one (hF : Q.HasStrongBundleUniformizers) :
    ∃ N : V.EObj → ℝ≥0∞, Q.IsAuxNormDirect N := by
  obtain ⟨N, hN⟩ := Q.exists_isAuxNormFunctor hF
  exact ⟨N, (hN (Q.refCoveringFamily hF)).isAuxNormDirect⟩

/-- **Theorem 18.1.12 (2), p. 848**: with reflexive `(0, 1)`-fibres, every auxiliary norm `N'`
lies between two reflexive auxiliary norms, `N₁ ≤ N' ≤ N₂` (Theorem 12.2.11 in a covering model,
pushed forward by `Γ̄`). -/
theorem theorem_18_1_12_two (c : Q.BundleCoveringFamily) (hB : Q.HasReflexiveFibers)
    {N' : V.EObj → ℝ≥0∞} (hN' : Q.IsAuxNormFunctor N') :
    ∃ N₁ N₂ : V.EObj → ℝ≥0∞, Q.IsReflexiveAuxNormFunctor N₁ ∧ Q.IsReflexiveAuxNormFunctor N₂ ∧
      ∀ e, N₁ e ≤ N' e ∧ N' e ≤ N₂ e := by
  obtain ⟨n₁, n₂, h₁, h₂, hle⟩ := (Q.modelSEP c.Ψ).E.theorem_12_2_11_sandwich
    (hasParacompactOrbitSpace_model c) (hB c) (hN' c).isAuxNorm
  refine ⟨pushNormFun c.cover n₁ h₁.toIsAuxNorm.isOneInvariant,
    pushNormFun c.cover n₂ h₂.toIsAuxNorm.isOneInvariant,
    (Q.isReflexiveAuxNormFunctor_iff_model c (hB c)).2
      (isReflexiveAuxNormIn_pushNormFun c.cover h₁),
    (Q.isReflexiveAuxNormFunctor_iff_model c (hB c)).2
      (isReflexiveAuxNormIn_pushNormFun c.cover h₂),
    fun e => ?_⟩
  obtain ⟨w, hw⟩ := exists_bundleModelObj_eq c e
  rw [← bundlePull_eq_of_π_eq (isAuxNormIn_pushNormFun c.cover h₁.toIsAuxNorm).isMorInvariant hw,
    ← bundlePull_eq_of_π_eq (hN' c).isMorInvariant hw,
    ← bundlePull_eq_of_π_eq (isAuxNormIn_pushNormFun c.cover h₂.toIsAuxNorm).isMorInvariant hw,
    bundlePull_pushNormFun, bundlePull_pushNormFun]
  by_cases hw1 : w ∈ (Q.modelSEP c.Ψ).B.oneSet
  · rw [Q.extendNorm_of_mem c.Ψ hw1, Q.extendNorm_of_mem c.Ψ hw1,
      ← ENNReal.ofReal_toReal ((hN' c).ne_top w hw1)]
    exact ⟨ENNReal.ofReal_le_ofReal (hle ((Q.modelSEP c.Ψ).B.oneMk w hw1)).1,
      ENNReal.ofReal_le_ofReal (hle ((Q.modelSEP c.Ψ).B.oneMk w hw1)).2⟩
  · rw [Q.extendNorm_of_not_mem c.Ψ hw1, Q.extendNorm_of_not_mem c.Ψ hw1, (hN' c).eq_top w hw1]
    exact ⟨le_rfl, le_rfl⟩

variable (Q) in
/-- **An auxiliary norm on `E|∂C`** (Theorem 18.1.12 (3), read in the covering model `c`):
`N` is constant along the morphisms of `E` starting over `∂C`, `N ∘ Γ̄ = +∞` exactly off
`W_{0,1}` over `∂X`, and `N ∘ Γ̄` is an auxiliary norm of `W|∂X` (Definition 12.2.1 over `∂X`,
as in Theorem 12.2.7).  The values of `N` off `E|∂C` play no role. -/
structure IsBoundaryAuxNormIn (c : Q.BundleCoveringFamily) (N : V.EObj → ℝ≥0∞) : Prop where
  isMorInvariant : ∀ a : V.EMor, V.base (V.groupoid.src a) ∈ S.boundarySet →
    N (V.groupoid.tgt a) = N (V.groupoid.src a)
  eq_top : ∀ w, (Q.modelSEP c.Ψ).P w ∈ (Q.modelSEP c.Ψ).X.PObj.boundary →
    w ∉ (Q.modelSEP c.Ψ).B.oneSet → Q.bundlePull c.Ψ N w = ⊤
  ne_top : ∀ w, (Q.modelSEP c.Ψ).P w ∈ (Q.modelSEP c.Ψ).X.PObj.boundary →
    w ∈ (Q.modelSEP c.Ψ).B.oneSet → Q.bundlePull c.Ψ N w ≠ ⊤
  isAuxNormOn : (Q.modelSEP c.Ψ).E.IsAuxNormOn (Q.modelSEP c.Ψ).X.PObj.boundary (Q.modelNorm c.Ψ N)

variable (Q) in
/-- **A reflexive auxiliary norm on `E|∂C`** (Theorem 18.1.12 (3), read in the covering model
`c`): in addition, `N ∘ Γ̄` is lower semicontinuous along mixed convergent sequences of
`W_{0,1}|∂X` (Definition 12.2.10 over `∂X`, as in Theorem 12.2.13). -/
structure IsReflexiveBoundaryAuxNormIn (c : Q.BundleCoveringFamily) (N : V.EObj → ℝ≥0∞) : Prop
    extends Q.IsBoundaryAuxNormIn c N where
  le_liminf : ∀ (w : ℕ → (Q.modelSEP c.Ψ).B.One) (y : (Q.modelSEP c.Ψ).B.One),
    (∀ k, (Q.modelSEP c.Ψ).P ((Q.modelSEP c.Ψ).B.oneVal (w k)) ∈
      (Q.modelSEP c.Ψ).X.PObj.boundary) →
    (Q.modelSEP c.Ψ).P ((Q.modelSEP c.Ψ).B.oneVal y) ∈ (Q.modelSEP c.Ψ).X.PObj.boundary →
    (Q.modelSEP c.Ψ).E.MixedTendsto w y →
    (Q.modelNorm c.Ψ N y : EReal) ≤ liminf (fun k => (Q.modelNorm c.Ψ N (w k) : EReal)) atTop

/-- An auxiliary norm restricts to an auxiliary norm on `E|∂C`. -/
theorem IsAuxNormIn.isBoundaryAuxNormIn {c : Q.BundleCoveringFamily} {N : V.EObj → ℝ≥0∞}
    (hN : Q.IsAuxNormIn c.Ψ N) : Q.IsBoundaryAuxNormIn c N :=
  ⟨fun a _ => hN.isMorInvariant a, fun w _ hw => hN.eq_top w hw, fun w _ hw => hN.ne_top w hw,
    hN.isAuxNorm.isAuxNormOn _⟩

/-- A reflexive auxiliary norm restricts to a reflexive auxiliary norm on `E|∂C`. -/
theorem IsReflexiveAuxNormIn.isReflexiveBoundaryAuxNormIn {c : Q.BundleCoveringFamily}
    {N : V.EObj → ℝ≥0∞} (hN : Q.IsReflexiveAuxNormIn c.Ψ N) : Q.IsReflexiveBoundaryAuxNormIn c N :=
  ⟨hN.toIsAuxNormIn.isBoundaryAuxNormIn, fun w y _ _ hm => hN.isReflexive.le_liminf w y hm⟩

theorem IsReflexiveBoundaryAuxNormIn.isReflexiveAuxNormOn {c : Q.BundleCoveringFamily}
    {N : V.EObj → ℝ≥0∞} (hN : Q.IsReflexiveBoundaryAuxNormIn c N) :
    (Q.modelSEP c.Ψ).E.IsReflexiveAuxNormOn (Q.modelSEP c.Ψ).X.PObj.boundary
      (Q.modelNorm c.Ψ N) :=
  ⟨hN.isAuxNormOn, hN.le_liminf⟩

/-- The model of a point over `∂C` lies over `∂X`. -/
theorem modelP_mem_boundary (c : Q.BundleCoveringFamily) {w : Q.ModelW c.Ψ} {e : V.EObj}
    (hw : V.groupoid.π (Q.bundleModelObj c.Ψ w) = V.groupoid.π e) (he : V.base e ∈ S.boundarySet) :
    (Q.modelSEP c.Ψ).P w ∈ (Q.modelSEP c.Ψ).X.PObj.boundary := by
  refine (mem_boundary_model_iff c (Q.modelP c.Ψ w)).2 ?_
  rw [modelOrbit_base_eq c hw]
  exact mem_image_of_mem _ he

/-- The push-forward of an extension `n` of `N ∘ Γ̄` from `W|∂X` agrees with `N` over `∂C`. -/
theorem pushNormFun_eq_of_boundary (c : Q.BundleCoveringFamily) {N : V.EObj → ℝ≥0∞}
    (hN : Q.IsBoundaryAuxNormIn c N) {n : (Q.modelSEP c.Ψ).B.One → ℝ}
    (hn : (Q.modelSEP c.Ψ).E.IsAuxNorm n)
    (hnN : ∀ w : (Q.modelSEP c.Ψ).B.One, (Q.modelSEP c.Ψ).P ((Q.modelSEP c.Ψ).B.oneVal w) ∈
      (Q.modelSEP c.Ψ).X.PObj.boundary → n w = Q.modelNorm c.Ψ N w)
    {e : V.EObj} (he : V.base e ∈ S.boundarySet) :
    pushNormFun c.cover n hn.isOneInvariant e = N e := by
  obtain ⟨w, hw⟩ := exists_bundleModelObj_eq c e
  have hwb := modelP_mem_boundary c hw he
  have hNe : N e = Q.bundlePull c.Ψ N w := by
    obtain ⟨a, hs, ht⟩ := (GroupoidStr.π_eq_π_iff _).1 hw.symm
    have h := hN.isMorInvariant a (hs ▸ he)
    rw [hs, ht] at h
    exact h.symm
  rw [← bundlePull_eq_of_π_eq (isAuxNormIn_pushNormFun c.cover hn).isMorInvariant hw,
    bundlePull_pushNormFun, hNe]
  by_cases hw1 : w ∈ (Q.modelSEP c.Ψ).B.oneSet
  · rw [Q.extendNorm_of_mem c.Ψ hw1, hnN ((Q.modelSEP c.Ψ).B.oneMk w hw1) hwb]
    exact ENNReal.ofReal_toReal (hN.ne_top w hwb hw1)
  · rw [Q.extendNorm_of_not_mem c.Ψ hw1, hN.eq_top w hwb hw1]

/-- **Theorem 18.1.12 (3), p. 848, first part**: over a tame polyfold, an auxiliary norm on
`E|∂C` extends to an auxiliary norm of `P` (Theorem 12.2.7 in a covering model, pushed forward
by `Γ̄`). -/
theorem theorem_18_1_12_three (c : Q.BundleCoveringFamily) (hT : S.IsTame) {N : V.EObj → ℝ≥0∞}
    (hN : Q.IsBoundaryAuxNormIn c N) :
    ∃ Ñ : V.EObj → ℝ≥0∞, Q.IsAuxNormFunctor Ñ ∧ ∀ e, V.base e ∈ S.boundarySet → Ñ e = N e := by
  obtain ⟨n, hn, hnN⟩ := (Q.modelSEP c.Ψ).E.theorem_12_2_7
    (S.isTame_modelEpGroupoid (Q.modelBase c.Ψ) hT)
    (hasParacompactOrbitSpace_model c) hN.isAuxNormOn
  exact ⟨_, (Q.isAuxNormFunctor_iff_model c).2 (isAuxNormIn_pushNormFun c.cover hn),
    fun e he => pushNormFun_eq_of_boundary c hN hn hnN he⟩

/-- **Theorem 18.1.12 (3), p. 848, second part**: over a tame polyfold with reflexive
`(0, 1)`-fibres, a reflexive auxiliary norm on `E|∂C` extends to a reflexive auxiliary norm of
`P` (Theorem 12.2.13 in a covering model, pushed forward by `Γ̄`). -/
theorem theorem_18_1_12_three_reflexive (c : Q.BundleCoveringFamily) (hT : S.IsTame)
    (hB : Q.HasReflexiveFibers) {N : V.EObj → ℝ≥0∞} (hN : Q.IsReflexiveBoundaryAuxNormIn c N) :
    ∃ Ñ : V.EObj → ℝ≥0∞, Q.IsReflexiveAuxNormFunctor Ñ ∧
      ∀ e, V.base e ∈ S.boundarySet → Ñ e = N e := by
  obtain ⟨n, hn, hnN⟩ := (Q.modelSEP c.Ψ).E.theorem_12_2_13
    (S.isTame_modelEpGroupoid (Q.modelBase c.Ψ) hT)
    (hasParacompactOrbitSpace_model c) (hB c) hN.isReflexiveAuxNormOn
  exact ⟨_, (Q.isReflexiveAuxNormFunctor_iff_model c (hB c)).2
    (isReflexiveAuxNormIn_pushNormFun c.cover hn),
    fun e he => pushNormFun_eq_of_boundary c hN.toIsBoundaryAuxNormIn hn.toIsAuxNorm hnN he⟩

/-! ### Definitions 18.1.10 and 18.1.11 -/

/-- `|P| : |E_{0,1}| → |C|`. -/
def oneBase (z : Q.EOneOrbit) : C.toGroupoidStr.OrbitSpace := V.proj.orbitMap (Q.oneClass z)

variable (Q) in
/-- **Definition 18.1.10, p. 847 (mixed convergence in `|E_{0,1}|`)**: `y_k → y` if
`|P|(y_k) → |P|(y)` on level `0` and, for a strong bundle uniformizer `Ψ̄ : G ⋉ K → E` of the
structure covering `Ψ` with `Ψ(x) = α` representing `|P|(y)`, there are `e_k ∈ K_{0,1}` with
`|Ψ̄(e_k)| = y_k` for large `k` and `e ∈ K_{0,1}` with `p(e) = x`, `|Ψ̄(e)| = y`, and
`e_k →ᵐ e` (Definition 12.2.8, i.e. Definition 5.1.6 in `K`).  We read "for a choice of
uniformizer" as "for some uniformizer of `F̄`". -/
def MixedTendstoOne (y : ℕ → Q.EOneOrbit) (y₀ : Q.EOneOrbit) : Prop :=
  Tendsto (fun k => Q.oneBase (y k)) atTop (𝓝 (Q.oneBase y₀)) ∧
    ∃ (Ψ : Q.Unif) (x : Ψ.1.base.O), C.toGroupoidStr.π (Ψ.1.base.obj x) = Q.oneBase y₀ ∧
      ∃ (e : ℕ → Ψ.1.B.One) (e₀ : Ψ.1.B.One), Ψ.1.p (Ψ.1.B.oneVal e₀) = x ∧
        (∀ᶠ k in atTop, V.groupoid.π (Ψ.1.obj (Ψ.1.B.oneVal (e k))) = Q.oneClass (y k)) ∧
        V.groupoid.π (Ψ.1.obj (Ψ.1.B.oneVal e₀)) = Q.oneClass y₀ ∧ Ψ.1.B.MixedTendsto e e₀

variable (Q) in
/-- **The condition of Definition 18.1.11, p. 847, as printed**: if `y_k → y` mixed convergent,
then for suitable representatives `e_k` of `y_k` and `e` of `y`, `N(e) ≤ liminf N(e_k)`. -/
def HasMixedLscReps (N : V.EObj → ℝ≥0∞) : Prop :=
  ∀ y y₀, Q.MixedTendstoOne y y₀ → ∃ (e : ℕ → V.EObj) (e₀ : V.EObj),
    (∀ k, V.groupoid.π (e k) = Q.oneClass (y k)) ∧ V.groupoid.π e₀ = Q.oneClass y₀ ∧
      N e₀ ≤ liminf (fun k => N (e k)) atTop

variable (Q) in
/-- **The alternative condition of Definition 18.1.11, p. 848**: `|N|(y) ≤ liminf |N|(y_k)` for
mixed convergent `y_k → y`. -/
def HasMixedLsc (N : V.EObj → ℝ≥0∞) : Prop :=
  ∀ y y₀, Q.MixedTendstoOne y y₀ → Q.oneNorm N y₀ ≤ liminf (fun k => Q.oneNorm N (y k)) atTop

theorem oneNorm_eq_of_π_eq {N : V.EObj → ℝ≥0∞} (hN : IsMorInvariant N) {e : V.EObj}
    {z : Q.EOneOrbit} (h : V.groupoid.π e = Q.oneClass z) : Q.oneNorm N z = N e :=
  hN.eq_of_isomorphic ((GroupoidStr.π_eq_π_iff _).1 ((Quotient.out_eq _).trans h.symm))

/-- **The two forms of Definition 18.1.11 agree** for a functor `N`: the value of `N` at a
representative is `|N|`. -/
theorem hasMixedLscReps_iff_hasMixedLsc {N : V.EObj → ℝ≥0∞} (hN : IsMorInvariant N) :
    Q.HasMixedLscReps N ↔ Q.HasMixedLsc N := by
  constructor
  · intro h y y₀ hm
    obtain ⟨e, e₀, he, he₀, hle⟩ := h y y₀ hm
    have hfun : (fun k => N (e k)) = fun k => Q.oneNorm N (y k) :=
      funext fun k => (oneNorm_eq_of_π_eq hN (he k)).symm
    rw [oneNorm_eq_of_π_eq hN he₀, ← hfun]
    exact hle
  · intro h y y₀ hm
    exact ⟨fun k => (Q.oneClass (y k)).out, (Q.oneClass y₀).out, fun k => Quotient.out_eq _,
      Quotient.out_eq _, h y y₀ hm⟩

variable (Q) in
/-- **Definition 18.1.11, p. 847 (reflexive auxiliary norm)**, with the auxiliary norm of
Definition 18.1.7 in the direct form (`IsAuxNormDirect`) and the condition as printed. -/
structure IsReflexiveAuxNormDirect (N : V.EObj → ℝ≥0∞) : Prop extends Q.IsAuxNormDirect N where
  le_liminf : Q.HasMixedLscReps N

/-- **Definition 18.1.11 with the alternative condition `|N|(y) ≤ liminf |N|(y_k)`**: the same
notion. -/
theorem isReflexiveAuxNormDirect_iff {N : V.EObj → ℝ≥0∞} :
    Q.IsReflexiveAuxNormDirect N ↔ Q.IsAuxNormDirect N ∧ Q.HasMixedLsc N :=
  ⟨fun h => ⟨h.toIsAuxNormDirect, (hasMixedLscReps_iff_hasMixedLsc h.isMorInvariant).1 h.le_liminf⟩,
    fun h => ⟨h.1, (hasMixedLscReps_iff_hasMixedLsc h.1.isMorInvariant).2 h.2⟩⟩

/-- The covering family `c` with one more strong bundle uniformizer `Ψ̄` (the index `none`). -/
def BundleCoveringFamily.withUnif (c : Q.BundleCoveringFamily) (Ψ : Q.Unif) :
    Q.BundleCoveringFamily where
  ι := Option c.ι
  Ψ o := o.elim Ψ c.Ψ
  cover := eq_univ_of_forall fun z => by
    obtain ⟨i, hi⟩ := mem_iUnion.1 (c.cover.symm ▸ mem_univ z)
    exact mem_iUnion.2 ⟨some i, hi⟩

/-- `a ≤ liminf a_k` in `[0, ∞]` iff the same inequality holds for the real parts in `EReal`
(finite values). -/
theorem le_liminf_iff_toReal {a : ℕ → ℝ≥0∞} {a₀ : ℝ≥0∞} (ha : ∀ k, a k ≠ ⊤) (ha₀ : a₀ ≠ ⊤) :
    (a₀.toReal : EReal) ≤ liminf (fun k => ((a k).toReal : EReal)) atTop ↔
      a₀ ≤ liminf a atTop := by
  have hmono : Monotone ((↑) : ℝ≥0∞ → EReal) := fun _ _ h =>
    EReal.coe_ennreal_le_coe_ennreal_iff.2 h
  have e := hmono.map_liminf_of_continuousAt a continuous_coe_ennreal_ereal.continuousAt
    (F := atTop)
  have hfun : (fun k => ((a k).toReal : EReal)) = ((↑) : ℝ≥0∞ → EReal) ∘ a :=
    funext fun k => EReal.coe_ennreal_toReal (ha k)
  rw [hfun, ← e, EReal.coe_ennreal_toReal ha₀]
  exact EReal.coe_ennreal_le_coe_ennreal_iff

/-- **A reflexive auxiliary norm of the models satisfies Definition 18.1.11** (both forms): the
uniformizer `Ψ̄` of Definition 18.1.10 is a piece of the covering model `c.withUnif Ψ̄`, mixed
convergence in `K` is mixed convergence in `W = ⊔ K_λ` (`MixedTendsto.sigmaMk`), and Definition
12.2.10 (3) there gives `|N|(y) ≤ liminf |N|(y_k)`. -/
theorem IsReflexiveAuxNormFunctor.hasMixedLsc {N : V.EObj → ℝ≥0∞}
    (hN : Q.IsReflexiveAuxNormFunctor N) (c : Q.BundleCoveringFamily) : Q.HasMixedLsc N := by
  rintro y y₀ ⟨-, Ψ, x, -, e, e₀, -, hev, he₀, hm⟩
  set c' := c.withUnif Ψ
  have h' := (hN c').isReflexive
  have hbook := (hN c').toIsAuxNormIn.isAuxNormBook
  have hinv := (hN c').isMorInvariant
  have hm' := StrongBundle.MixedTendsto.sigmaMk (B := fun o => (c'.Ψ o).1.B) (i := none) hm
  have hle := h'.le_liminf _ _ hm'
  have hval : ∀ u : Ψ.1.B.One, Q.modelNorm c'.Ψ N
      ((StrongBundle.sigmaOneEquiv (fun o => (c'.Ψ o).1.B)).symm ⟨none, u⟩) =
      (N (Ψ.1.obj (Ψ.1.B.oneVal u))).toReal := fun u => rfl
  simp only [hval] at hle
  have hfin : ∀ k, Q.oneNorm N (y k) ≠ ⊤ := fun k => hbook.oneNorm_ne_top _
  refine (le_liminf_iff_toReal hfin (hbook.oneNorm_ne_top _)).1 ?_
  rw [oneNorm_eq_of_π_eq hinv he₀]
  refine hle.trans_eq (liminf_congr ?_)
  filter_upwards [hev] with k hk
  rw [oneNorm_eq_of_π_eq hinv hk]

/-- **A reflexive auxiliary norm of the models is a reflexive auxiliary norm in the sense of
Definition 18.1.11** (direct form, condition as printed). -/
theorem IsReflexiveAuxNormFunctor.isReflexiveAuxNormDirect {N : V.EObj → ℝ≥0∞}
    (hN : Q.IsReflexiveAuxNormFunctor N) (c : Q.BundleCoveringFamily) :
    Q.IsReflexiveAuxNormDirect N :=
  isReflexiveAuxNormDirect_iff.2 ⟨(hN c).toIsAuxNormIn.isAuxNormDirect, hN.hasMixedLsc c⟩

variable (Q) in
/-- The strong bundle uniformizers of the covering family `c` have reflexive `(0, 1)`-fibres
(Definition 5.1.4 for each `p : K_λ → O_λ`).  The text asserts this after Definition 18.1.9
(l. 41755: "any sc-smooth model has reflexive `(0, 1)`-fibers"), since each `K_λ` is an open
summand of the model; the passage from the model `W = ⊔ K_λ` to its summands (restricting a chart
of a sigma bundle) is `HasReflexiveFibersIn.hasReflexivePieces` (`ReflexivePieces.lean`), so the
statements here take it as a hypothesis. -/
def HasReflexivePieces (c : Q.BundleCoveringFamily) : Prop :=
  ∀ i, (c.Ψ i).1.B.HasReflexiveFibers

theorem HasReflexivePieces.hasReflexiveFibersIn {c : Q.BundleCoveringFamily}
    (hK : Q.HasReflexivePieces c) : Q.HasReflexiveFibersIn c.Ψ :=
  StrongBundle.hasReflexiveFibers_sigma hK

/-- **Definition 18.1.11 gives a reflexive auxiliary norm in the model `c`** when the strong
bundle uniformizers of `c` have reflexive `(0, 1)`-fibres (`HasReflexivePieces`, which the text
asserts after Definition 18.1.9, l. 41755, and which `ReflexivePieces.lean` derives; it makes the pushed
charts of the pieces available for the weak convergence): a mixed convergent sequence
`w_k →ᵐ w` of `W_{0,1}` lies for large `k` in the piece `K_λ` of `w` and is mixed convergent
there (`MixedTendsto.exists_summand`), so `|Γ̄(w_k)| → |Γ̄(w)|` in the sense of Definition 18.1.10
with `Ψ̄ = Ψ̄_λ`. -/
theorem IsReflexiveAuxNormDirect.isReflexiveAuxNormIn_hyp {N : V.EObj → ℝ≥0∞}
    (h : Q.IsReflexiveAuxNormDirect N) (c : Q.BundleCoveringFamily)
    (hK : Q.HasReflexivePieces c) : Q.IsReflexiveAuxNormIn c.Ψ N := by
  have hIn := h.isAuxNormIn c
  have hinv := h.isMorInvariant
  have hlsc := (hasMixedLscReps_iff_hasMixedLsc hinv).1 h.le_liminf
  refine ⟨hIn, hIn.isAuxNorm, fun w y hm => ?_⟩
  obtain ⟨i, u₀, rfl⟩ := StrongBundle.exists_sigmaOneEquiv_symm (fun o => (c.Ψ o).1.B) y
  obtain ⟨u, hev, hmu⟩ := StrongBundle.MixedTendsto.exists_summand
    (B := fun o => (c.Ψ o).1.B) hm (hK i)
  have hone : ∀ v : (Q.modelSEP c.Ψ).B.One,
      Q.IsOneObj (Q.bundleModelObj c.Ψ ((Q.modelSEP c.Ψ).B.oneVal v)) := fun v =>
    (isOneObj_bundleModelObj_iff c _).2 ((Q.modelSEP c.Ψ).B.oneVal_mem _)
  let yk : ℕ → Q.EOneOrbit := fun k => Q.oneMk _ (hone (w k))
  let y₀ : Q.EOneOrbit := Q.oneMk _ (hone ((StrongBundle.sigmaOneEquiv
    (fun o => (c.Ψ o).1.B)).symm ⟨i, u₀⟩))
  have hbase : ∀ v : (Q.modelSEP c.Ψ).B.One, Q.oneBase (Q.oneMk _ (hone v)) =
      (S.modelFunctor (Q.modelBase c.Ψ)).orbitMap
        ((Q.modelSEP c.Ψ).X.π ((Q.modelSEP c.Ψ).P ((Q.modelSEP c.Ψ).B.oneVal v))) := fun v =>
    (modelOrbit_base_eq c rfl).symm
  have hmix : Q.MixedTendstoOne yk y₀ := by
    refine ⟨?_, c.Ψ i, (c.Ψ i).1.p ((c.Ψ i).1.B.oneVal u₀), rfl, u, u₀, rfl, ?_, rfl, hmu⟩
    · simp only [yk, y₀, hbase]
      exact (((isHomeomorph_modelOrbitMap c.cover).continuous.comp
        (Q.modelSEP c.Ψ).X.continuous_π).tendsto _).comp hm.1
    · filter_upwards [hev] with k hk
      simp only [yk, oneClass_oneMk, ← hk]
      rfl
  have hle := hlsc yk y₀ hmix
  have hval : ∀ v : (Q.modelSEP c.Ψ).B.One, Q.modelNorm c.Ψ N v =
      (Q.oneNorm N (Q.oneMk _ (hone v))).toReal := fun v => by
    rw [oneNorm_oneMk hinv]
    rfl
  simp only [hval]
  exact (le_of_eq (congrArg _ (hval _))).trans
    ((le_liminf_iff_toReal (fun k => h.oneNorm_ne_top _) (h.oneNorm_ne_top _)).2 hle)

/-- **Definition 18.1.11 and the model reading agree** when the strong bundle uniformizers of a
covering family `c` have reflexive `(0, 1)`-fibres. -/
theorem isReflexiveAuxNormDirect_iff_hyp (c : Q.BundleCoveringFamily)
    (hK : Q.HasReflexivePieces c) {N : V.EObj → ℝ≥0∞} :
    Q.IsReflexiveAuxNormDirect N ↔ Q.IsReflexiveAuxNormFunctor N :=
  ⟨fun h => (Q.isReflexiveAuxNormFunctor_iff_model c hK.hasReflexiveFibersIn).2
      (h.isReflexiveAuxNormIn_hyp c hK),
    fun h => h.isReflexiveAuxNormDirect c⟩

end StrongPolyfoldBundleConstruction

end GCT.VectorBundle

end Polyfold
