import Polyfold.Chapter8.SigmaPolyfold
import Polyfold.Chapter10.StrongBundleEquivalenceNat

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17:
infrastructure for **the bundle model of §17.7** (pp. 826–828), the strong bundle
`W = ⊔_λ K_λ → X = ⊔_λ O_λ` of a family of strong bundle uniformizers.  Numbers and pages are
the 2021 text's.

# Disjoint unions of strong bundles

## The text, paraphrased

(§17.7, pp. 826–828) From a family of strong bundle uniformizers `Ψ_λ : K_λ → O_λ` the text forms
the strong bundle `W = ⊔_λ K_λ → X = ⊔_λ O_λ` over the disjoint union of the bases and takes
for granted that it is a strong bundle (Definition 2.6.5), that the inclusions of the summands are
strong bundle maps, and that maps defined summand by summand are strong bundle maps.

## What is formalized

* **The fibres**: `sigmaBundleProj p` (`(i, y) ↦ (i, p_i(y))`), `sigmaFiberEquiv`
  (`(sigmaBundleProj p)⁻¹(i, x) ≃ p_i⁻¹(x)`), the transported vector space structures (instances
  `sigmaFiber_addCommGroup`, `sigmaFiber_module`), `sigmaFiberLinearEquiv` and `sigmaFiberCLE`.
* **The strong bundle** `StrongBundle.sigma B` over Chapter 8's `MPolyfold.sigma PX`: the strong
  bundle charts of every `B i` pushed forward along `Sigma.mk i`
  (`StrongBundleChart.sigmaPush`); charts of different summands are compatible, their domains
  being disjoint.
* **The M-polyfolds `W[0]`, `W[1]`**: `StrongBundle.sigma_toMPolyfold0`
  (`W[0] = ⊔ K_λ[0]` as M-polyfolds), `mem_oneSet_sigma_iff`, and `sigmaOneEquiv`
  (`W[1] ≅ ⊔ K_λ[1]`) with `isScDiffeoOn_sigmaOneEquiv`.
* **Strong bundle maps**: `isStrongBundleMap_sigmaMk` (the inclusions),
  `isStrongBundleMap_sigma_iff`
  (maps out of the union, summand by summand), `isStrongBundleMap_sigmaMk_comp_iff` (maps into
  one summand), `isStrongBundleMap_sigmaMap` and `isStrongBundleIsoOn_sigmaMap` (maps between
  unions, and local strong bundle isomorphisms).
* **Pull-backs along maps of unions**: for `S = (j, z) ↦ (σ j, s_j(z))`, the pull-back
  `S*W` is the union of the pull-backs `s_j*K_{σ j}`: `pullbackSigmaIncl`, `pullbackSigmaProj`,
  `pullbackSigmaEquiv`, `isStrongBundleIso_pullbackSigma`; maps between such pull-backs
  `pullbackSigmaMap` with `isStrongBundleMap_pullbackSigmaMap`; the criteria
  `isStrongBundleMap_pullbackSigma_iff`,
  `isLocalScDiffeo_pullbackSigma_iff` and `isStrongBundleIsoOn_pullbackSigmaMap`.

## What the text leaves implicit, and the choices made

* The strong bundle structure of `⊔_λ K_λ` is read as the one whose charts are the strong
  bundle charts of the summands, transported along `Sigma.mk`; this is the strong bundle analogue
  of Chapter 8's reading of "the natural M-polyfold structure" of a disjoint union.
* Paracompactness of the pull-backs is an instance argument, as everywhere in the repository
  (`StrongBundle.paracompactSpace_pullback`).
-/

open Set Function Topology

noncomputable section

set_option maxSynthPendingDepth 3

namespace Polyfold

universe u v w

/-! ### Lifting the component of a point of a disjoint union -/

section Lift

variable {ι : Type*} {Y : ι → Type*}

/-- The component of `w : Σ i, Y i` as an element of `Y k`, for `w.1 = k`. -/
def sigmaLift (k : ι) (w : Σ i, Y i) (h : w.1 = k) : Y k := h ▸ w.2

/-- `sigmaLift` on a point of the summand `k` is its second component. -/
@[simp] lemma sigmaLift_mk (k : ι) (y : Y k) (h : (⟨k, y⟩ : Σ i, Y i).1 = k) :
    sigmaLift k ⟨k, y⟩ h = y := rfl

/-- Reinserting `sigmaLift k w h` into the summand `k` gives back `w`. -/
lemma mk_sigmaLift (k : ι) (w : Σ i, Y i) (h : w.1 = k) :
    (⟨k, sigmaLift k w h⟩ : Σ i, Y i) = w := by
  subst h; rfl

/-- `sigmaLift` recovers the second component of a point of the summand `k`. -/
lemma sigmaLift_eq_of_mk_eq {k : ι} {w : Σ i, Y i} (h : w.1 = k) {y : Y k}
    (hy : (⟨k, y⟩ : Σ i, Y i) = w) : sigmaLift k w h = y :=
  sigma_mk_injective ((mk_sigmaLift k w h).trans hy.symm)

end Lift

/-! ### The projection of a disjoint union of bundles and its fibres -/

section Fibres

variable {ι : Type*} {X : ι → Type*} {Y : ι → Type*} (p : ∀ i, Y i → X i)

/-- The projection `⊔ K_λ → ⊔ O_λ`, `(i, y) ↦ (i, p_i(y))`. -/
def sigmaBundleProj : (Σ i, Y i) → (Σ i, X i) := fun y => ⟨y.1, p y.1 y.2⟩

/-- `sigmaBundleProj p` acts summand-wise. -/
@[simp] lemma sigmaBundleProj_mk (i : ι) (y : Y i) :
    sigmaBundleProj p ⟨i, y⟩ = ⟨i, p i y⟩ := rfl

/-- The part of `W` over `mk i '' s` is `mk i '' (p i ⁻¹' s)`. -/
lemma sigmaBundleProj_preimage_image (i : ι) (s : Set (X i)) :
    sigmaBundleProj p ⁻¹' (Sigma.mk i '' s) = Sigma.mk i '' (p i ⁻¹' s) := by
  ext ⟨j, y⟩
  constructor
  · rintro ⟨x, hx, hxy⟩
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 hxy
    have h' : x = p i y := eq_of_heq h
    exact ⟨y, by rw [mem_preimage, ← h']; exact hx, rfl⟩
  · rintro ⟨y', hy', hyy⟩
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 hyy
    cases eq_of_heq h
    exact ⟨p i y', hy', rfl⟩

/-- The fibre of `sigmaBundleProj p` over `(i, x)` is the fibre of `p_i` over `x`. -/
def sigmaFiberEquiv (z : Σ i, X i) : (sigmaBundleProj p ⁻¹' {z}) ≃ (p z.1 ⁻¹' {z.2}) where
  toFun w := ⟨sigmaLift z.1 w.1 (congrArg Sigma.fst w.2), by
    have h1 := congrArg (sigmaBundleProj p) (mk_sigmaLift z.1 w.1 (congrArg Sigma.fst w.2))
    have h2 : sigmaBundleProj p w.1 = z := w.2
    exact sigma_mk_injective (h1.trans h2)⟩
  invFun y := ⟨⟨z.1, y.1⟩, by
    change (⟨z.1, p z.1 y.1⟩ : Σ i, X i) = z
    rw [show p z.1 y.1 = z.2 from y.2]⟩
  left_inv w := Subtype.ext (mk_sigmaLift _ _ _)
  right_inv _ := rfl

/-- The point of `Σ i, Y i` behind `sigmaFiberEquiv p z w`. -/
lemma mk_sigmaFiberEquiv (z : Σ i, X i) (w : sigmaBundleProj p ⁻¹' {z}) :
    (⟨z.1, (sigmaFiberEquiv p z w : Y z.1)⟩ : Σ i, Y i) = w :=
  mk_sigmaLift _ _ _

/-- The inverse of `sigmaFiberEquiv` inserts into the summand `z.1`. -/
@[simp] lemma sigmaFiberEquiv_symm_val (z : Σ i, X i) (y : p z.1 ⁻¹' {z.2}) :
    ((sigmaFiberEquiv p z).symm y : Σ i, Y i) = ⟨z.1, y⟩ := rfl

/-- `sigmaFiberEquiv` on a point of the summand is its second component. -/
@[simp] lemma sigmaFiberEquiv_mk (i : ι) (x : X i) (y : Y i)
    (hy : (⟨i, y⟩ : Σ i, Y i) ∈ sigmaBundleProj p ⁻¹' {(⟨i, x⟩ : Σ i, X i)}) :
    (sigmaFiberEquiv p ⟨i, x⟩ ⟨⟨i, y⟩, hy⟩ : Y i) = y := rfl

variable [∀ i x, AddCommGroup (p i ⁻¹' {x})]

/-- The fibre of `W` over `z` is a group, transported from the fibre of `K_{z.1}`. -/
instance sigmaFiber_addCommGroup (z : Σ i, X i) : AddCommGroup (sigmaBundleProj p ⁻¹' {z}) :=
  (sigmaFiberEquiv p z).addCommGroup

/-- `sigmaFiberEquiv` is additive. -/
lemma sigmaFiberEquiv_add (z : Σ i, X i) (v w : sigmaBundleProj p ⁻¹' {z}) :
    sigmaFiberEquiv p z (v + w) = sigmaFiberEquiv p z v + sigmaFiberEquiv p z w :=
  (sigmaFiberEquiv p z).apply_symm_apply _

variable [∀ i x, Module ℝ (p i ⁻¹' {x})]

/-- The fibre of `W` over `z` is a real vector space, transported from the fibre of `K_{z.1}`. -/
instance sigmaFiber_module (z : Σ i, X i) : Module ℝ (sigmaBundleProj p ⁻¹' {z}) :=
  (sigmaFiberEquiv p z).module ℝ

/-- `sigmaFiberEquiv` commutes with scalar multiplication. -/
lemma sigmaFiberEquiv_smul (z : Σ i, X i) (a : ℝ) (v : sigmaBundleProj p ⁻¹' {z}) :
    sigmaFiberEquiv p z (a • v) = a • sigmaFiberEquiv p z v :=
  (sigmaFiberEquiv p z).apply_symm_apply _

/-- `sigmaFiberEquiv` as a linear equivalence. -/
def sigmaFiberLinearEquiv (z : Σ i, X i) :
    (sigmaBundleProj p ⁻¹' {z}) ≃ₗ[ℝ] (p z.1 ⁻¹' {z.2}) where
  toFun := sigmaFiberEquiv p z
  invFun := (sigmaFiberEquiv p z).symm
  map_add' := sigmaFiberEquiv_add p z
  map_smul' := sigmaFiberEquiv_smul p z
  left_inv := (sigmaFiberEquiv p z).left_inv
  right_inv := (sigmaFiberEquiv p z).right_inv

/-- `sigmaFiberLinearEquiv` is `sigmaFiberEquiv`. -/
@[simp] lemma sigmaFiberLinearEquiv_apply (z : Σ i, X i) (w : sigmaBundleProj p ⁻¹' {z}) :
    sigmaFiberLinearEquiv p z w = sigmaFiberEquiv p z w := rfl

variable [∀ i, TopologicalSpace (Y i)]

/-- `sigmaFiberEquiv` as a continuous linear equivalence (subspace topologies). -/
def sigmaFiberCLE (z : Σ i, X i) : (sigmaBundleProj p ⁻¹' {z}) ≃L[ℝ] (p z.1 ⁻¹' {z.2}) where
  toLinearEquiv := sigmaFiberLinearEquiv p z
  continuous_toFun := by
    have hemb : IsEmbedding (fun y : p z.1 ⁻¹' {z.2} => (⟨z.1, y.1⟩ : Σ i, Y i)) :=
      IsEmbedding.sigmaMk.comp IsEmbedding.subtypeVal
    change Continuous (sigmaFiberEquiv p z)
    rw [hemb.continuous_iff]
    have : (fun y : p z.1 ⁻¹' {z.2} => (⟨z.1, y.1⟩ : Σ i, Y i)) ∘ sigmaFiberEquiv p z =
        Subtype.val := funext fun w => mk_sigmaFiberEquiv p z w
    rw [this]
    exact continuous_subtype_val
  continuous_invFun := (continuous_sigmaMk.comp continuous_subtype_val).subtype_mk _

/-- `sigmaFiberCLE` is `sigmaFiberEquiv`. -/
@[simp] lemma sigmaFiberCLE_apply (z : Σ i, X i) (w : sigmaBundleProj p ⁻¹' {z}) :
    sigmaFiberCLE p z w = sigmaFiberEquiv p z w := rfl

end Fibres

/-! ### The strong bundle `⊔ K_λ → ⊔ O_λ` -/

section SigmaBundle

variable {ι : Type*} {X : ι → Type u} [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)]
  [∀ i, ParacompactSpace (X i)] {PX : ∀ i, MPolyfold (X i)}
  {Y : ι → Type v} [∀ i, TopologicalSpace (Y i)] {p : ∀ i, Y i → X i}
  [∀ i x, AddCommGroup (p i ⁻¹' {x})] [∀ i x, Module ℝ (p i ⁻¹' {x})]

namespace StrongBundleChart

variable {i : ι} (c c' : StrongBundleChart (PX i) (p i)) (hP : Continuous (p i))

/-- A strong bundle chart of the summand `p_i : Y i → X i`, **pushed forward along `Sigma.mk i`**
to a strong bundle chart of `sigmaBundleProj p`: the base chart `sigmaChart i φ`, the same
`F`, `U`, `R`, and the chart `(i, y) ↦ Φ(y)` (Chapter 8's `MChart.pushforward` of `Φ`). -/
def sigmaPush : StrongBundleChart (MPolyfold.sigma PX) (sigmaBundleProj p) where
  φ := MPolyfold.sigmaChart i c.φ
  isChart := c.isChart.sigmaChart
  F := c.F
  U := c.U
  R := c.R
  relOpen := c.relOpen
  isRetraction := c.isRetraction
  base_retract := c.base_retract
  toPartialEquiv := ((c.toMChart hP).pushforward IsOpenEmbedding.sigmaMk).toPartialEquiv
  source_eq := by
    change Sigma.mk i '' c.toPartialEquiv.source = _
    rw [c.source_eq, MPolyfold.sigmaChart_source, sigmaBundleProj_preimage_image]
  target_eq := rfl
  continuousOn_toFun := ((c.toMChart hP).pushforward IsOpenEmbedding.sigmaMk).continuousOn_toFun
  continuousOn_invFun := ((c.toMChart hP).pushforward IsOpenEmbedding.sigmaMk).continuousOn_invFun
  covers := by
    rintro _ ⟨y, hy, rfl⟩
    change ((c.toMChart hP).pushforward IsOpenEmbedding.sigmaMk ⟨i, y⟩).1 =
      MPolyfold.sigmaChart i c.φ ⟨i, p i y⟩
    rw [MChart.pushforward_apply, MPolyfold.sigmaChart_apply]
    exact c.covers y hy
  fiber_linear := by
    rintro _ ⟨x, hx, rfl⟩
    have hfun : (fun v : sigmaBundleProj p ⁻¹' {(⟨i, x⟩ : Σ i, X i)} =>
        (((c.toMChart hP).pushforward IsOpenEmbedding.sigmaMk).toPartialEquiv v).2) =
        (c.fiber_linear x hx).mk'.comp (sigmaFiberLinearEquiv p ⟨i, x⟩).toLinearMap := by
      funext v
      change ((c.toMChart hP).pushforward IsOpenEmbedding.sigmaMk (v : Σ i, Y i)).2 =
        (c (sigmaFiberEquiv p ⟨i, x⟩ v : Y i)).2
      conv_lhs => rw [← mk_sigmaFiberEquiv p ⟨i, x⟩ v]
      rw [MChart.pushforward_apply]
      rfl
    rw [hfun]
    exact LinearMap.isLinear _

/-- The pushed chart on the summand `i` is the original chart. -/
lemma sigmaPush_apply (y : Y i) : c.sigmaPush hP ⟨i, y⟩ = c y :=
  MChart.pushforward_apply (c.toMChart hP) IsOpenEmbedding.sigmaMk y

/-- The source of the pushed chart is the image of the source. -/
lemma sigmaPush_source :
    (c.sigmaPush hP).toPartialEquiv.source = Sigma.mk i '' c.toPartialEquiv.source := rfl

/-- The inverse of the pushed chart inserts into the summand `i`. -/
lemma sigmaPush_symm (k : c.φ.model.E 0 × c.F 0) :
    (c.sigmaPush hP).toPartialEquiv.symm k = ⟨i, c.toPartialEquiv.symm k⟩ := rfl

/-- The pushed chart has the same local model. -/
lemma sigmaPush_K : (c.sigmaPush hP).K = c.K := rfl

/-- The chart of `W[0]` induced by a pushed-forward chart is the pushed-forward chart of
`K_i[0]`. -/
lemma sigmaPush_toMChart (hP' : Continuous (sigmaBundleProj p)) :
    (c.sigmaPush hP).toMChart hP' = MPolyfold.sigmaChart i (c.toMChart hP) := rfl

/-- Overlaps of pushed charts of one summand are images of overlaps. -/
lemma sigmaPush_overlap :
    (c.sigmaPush hP).overlap (c'.sigmaPush hP) = c.overlap c' :=
  MChart.pushforward_overlap (c.toMChart hP) (c'.toMChart hP) IsOpenEmbedding.sigmaMk

/-- Transition maps of pushed charts of one summand are the original transition maps. -/
lemma sigmaPush_transition :
    (c.sigmaPush hP).transition (c'.sigmaPush hP) = c.transition c' :=
  MChart.pushforward_transition (c.toMChart hP) (c'.toMChart hP) IsOpenEmbedding.sigmaMk

variable {c c'} in
/-- Pushing forward along `Sigma.mk i` preserves compatibility. -/
theorem Compatible.sigmaPush (h : c.Compatible c') :
    (c.sigmaPush hP).Compatible (c'.sigmaPush hP) := by
  unfold StrongBundleChart.Compatible
  rw [sigmaPush_overlap, sigmaPush_overlap, sigmaPush_transition, sigmaPush_transition]
  exact h

/-- The level-`[1]` part of the empty set is empty. -/
lemma strongShiftOne_empty {E F : ScBanach} : strongShiftOne (∅ : Set (E 0 × F 0)) = ∅ := rfl

/-- Pushed-forward charts of different summands are compatible: their domains are disjoint. -/
theorem compatible_sigmaPush_of_ne {j : ι} (hij : i ≠ j) (d : StrongBundleChart (PX j) (p j))
    (hP' : Continuous (p j)) : (c.sigmaPush hP).Compatible (d.sigmaPush hP') := by
  have hdisj : Disjoint (c.sigmaPush hP).toPartialEquiv.source
      (d.sigmaPush hP').toPartialEquiv.source :=
    (disjoint_range_sigmaMk hij).mono (image_subset_range _ _) (image_subset_range _ _)
  have h1 : (c.sigmaPush hP).overlap (d.sigmaPush hP') = ∅ := by
    rw [StrongBundleChart.overlap, hdisj.inter_eq, image_empty]
  have h2 : (d.sigmaPush hP').overlap (c.sigmaPush hP) = ∅ := by
    rw [StrongBundleChart.overlap, hdisj.symm.inter_eq, image_empty]
  unfold StrongBundleChart.Compatible
  rw [h1, h2, strongShiftOne_empty, strongShiftOne_empty]
  exact ⟨isScSmoothRetractMap_empty _, isScSmoothRetractMap_empty _,
    isScSmoothRetractMap_empty _, isScSmoothRetractMap_empty _,
    fun x hx => absurd hx (notMem_empty x), fun x hx => absurd hx (notMem_empty x)⟩

end StrongBundleChart

variable [∀ i, T2Space (Y i)] [∀ i, ParacompactSpace (Y i)] (B : ∀ i, StrongBundle (PX i) (p i))

/-- The strong bundle atlas of `⊔ K_λ`: the charts of the atlases of all `B i`, pushed forward. -/
def sigmaStrongBundleAtlas : StrongBundleAtlas (MPolyfold.sigma PX) (sigmaBundleProj p) where
  charts := {c | ∃ i, ∃ c' ∈ (B i).atlas.charts, c = c'.sigmaPush (B i).continuous}
  compatible := by
    rintro _ ⟨i, c, hc, rfl⟩ _ ⟨j, c', hc', rfl⟩
    by_cases hij : i = j
    · subst hij
      exact ((B i).atlas.compatible c hc c' hc').sigmaPush _
    · exact c.compatible_sigmaPush_of_ne _ hij c' _
  cover := by
    rintro ⟨i, y⟩
    obtain ⟨c, hc, hy⟩ := (B i).atlas.cover y
    exact ⟨_, ⟨i, c, hc, rfl⟩, y, hy, rfl⟩

/-- **The strong bundle `⊔ K_λ → ⊔ O_λ`** (§17.7, p. 826): the disjoint union of strong bundles
`B i : p_i : Y i → X i` (Definition 2.6.5) over the disjoint union `MPolyfold.sigma PX` of the
bases, with the strong bundle charts of the summands pushed forward along `Sigma.mk i`. -/
def StrongBundle.sigma : StrongBundle (MPolyfold.sigma PX) (sigmaBundleProj p) where
  continuous := continuous_sigma fun i => continuous_sigmaMk.comp (B i).continuous
  surjective := by
    rintro ⟨i, x⟩
    obtain ⟨y, rfl⟩ := (B i).surjective x
    exact ⟨⟨i, y⟩, rfl⟩
  banachable z := by
    obtain ⟨Bsp, h1, h2, h3, ⟨e⟩⟩ := (B z.1).banachable z.2
    exact ⟨Bsp, h1, h2, h3, ⟨(sigmaFiberCLE p z).trans e⟩⟩
  atlas := sigmaStrongBundleAtlas B

namespace StrongBundle

variable {B}

/-- Pushed charts of the summands belong to the atlas of `StrongBundle.sigma B`. -/
lemma sigmaPush_mem_sigma_atlas {i : ι} {c : StrongBundleChart (PX i) (p i)}
    (hc : c ∈ (B i).atlas.charts) :
    c.sigmaPush (B i).continuous ∈ (StrongBundle.sigma B).atlas.charts :=
  ⟨i, c, hc, rfl⟩

/-- Two atlases with the same charts are equal. -/
lemma _root_.Polyfold.MAtlas.ext_charts {Z : Type*} [TopologicalSpace Z] {A A' : MAtlas Z}
    (h : A.charts = A'.charts) : A = A' := by
  cases A; cases A'; cases h; rfl

variable (B) in
/-- **`W[0]` is the disjoint union of the `K_λ[0]`** as M-polyfolds: the charts of
`(StrongBundle.sigma B)[0]` are those of the `(B i)[0]`, pushed forward along `Sigma.mk i`. -/
theorem sigma_toMPolyfold0 :
    (StrongBundle.sigma B).toMPolyfold0 = MPolyfold.sigma fun i => (B i).toMPolyfold0 := by
  change MPolyfold.mk _ = MPolyfold.mk _
  congr 1
  refine MAtlas.ext_charts ?_
  ext χ
  constructor
  · rintro ⟨_, ⟨i, c, hc, rfl⟩, rfl⟩
    exact ⟨i, _, ⟨c, hc, rfl⟩, rfl⟩
  · rintro ⟨i, _, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨_, ⟨i, c, hc, rfl⟩, rfl⟩

/-- `W_{0,1}` is the union of the `(K_λ)_{0,1}`. -/
theorem mem_oneSet_sigma_iff {i : ι} (y : Y i) :
    (⟨i, y⟩ : Σ i, Y i) ∈ (StrongBundle.sigma B).oneSet ↔ y ∈ (B i).oneSet := by
  obtain ⟨c, hc, hy⟩ := (B i).atlas.cover y
  rw [(StrongBundle.sigma B).mem_oneSet_iff (sigmaPush_mem_sigma_atlas hc) ⟨y, hy, rfl⟩,
    (B i).mem_oneSet_iff hc hy, StrongBundleChart.sigmaPush_apply]
  rfl

end StrongBundle

end SigmaBundle

/-! ### Two facts on sc-diffeomorphisms -/

namespace MPolyfold

section DiffeoFacts

variable {X₁ : Type*} [TopologicalSpace X₁] [T2Space X₁] [ParacompactSpace X₁] {P₁ : MPolyfold X₁}
  {X₂ : Type*} [TopologicalSpace X₂] [T2Space X₂] [ParacompactSpace X₂] {P₂ : MPolyfold X₂}
  {X₃ : Type*} [TopologicalSpace X₃] [T2Space X₃] [ParacompactSpace X₃] {P₃ : MPolyfold X₃}
  {X₄ : Type*} [TopologicalSpace X₄] [T2Space X₄] [ParacompactSpace X₄] {P₄ : MPolyfold X₄}

/-- A global sc-diffeomorphism restricts to an sc-diffeomorphism `f⁻¹(T) → T` for open `T`. -/
theorem IsScDiffeoOn.restrict_preimage {f : X₁ → X₂} {g : X₂ → X₁}
    (he : P₁.IsScDiffeoOn P₂ f g univ univ) {T : Set X₂} (hT : IsOpen T) :
    P₁.IsScDiffeoOn P₂ f g (f ⁻¹' T) T := by
  have hc : Continuous f := continuousOn_univ.1 he.isScSmoothOn.continuousOn
  have h := he.restrict (hT.preimage hc) (subset_univ _)
  have hset : univ ∩ g ⁻¹' (f ⁻¹' T) = T := by
    ext y
    simp only [mem_inter_iff, mem_univ, mem_preimage, true_and, he.right_inv y (mem_univ y)]
  rwa [hset] at h

/-- An sc-diffeomorphism `A → B` conjugated by global sc-diffeomorphisms `f₁`, `f₂` is an
sc-diffeomorphism `f₁⁻¹(A) → f₂⁻¹(B)`. -/
theorem IsScDiffeoOn.conj {f₁ : X₁ → X₂} {g₁ : X₂ → X₁} {f₂ : X₃ → X₄} {g₂ : X₄ → X₃}
    {F : X₂ → X₄} {G : X₄ → X₂} {A : Set X₂} {B : Set X₄}
    (he₁ : P₁.IsScDiffeoOn P₂ f₁ g₁ univ univ) (he₂ : P₃.IsScDiffeoOn P₄ f₂ g₂ univ univ)
    (h : P₂.IsScDiffeoOn P₄ F G A B) :
    P₁.IsScDiffeoOn P₃ (g₂ ∘ F ∘ f₁) (g₁ ∘ G ∘ f₂) (f₁ ⁻¹' A) (f₂ ⁻¹' B) :=
  ((he₂.restrict_preimage h.isOpen_target).symm.comp
    (h.comp (he₁.restrict_preimage h.isOpen_source)))

end DiffeoFacts

section SigmaImage

variable {ι : Type*} {X : ι → Type u} [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)]
  [∀ i, ParacompactSpace (X i)] (P : ∀ i, MPolyfold (X i))
  {κ : Type*} {X' : κ → Type v} [∀ k, TopologicalSpace (X' k)] [∀ k, T2Space (X' k)]
  [∀ k, ParacompactSpace (X' k)] (R : ∀ k, MPolyfold (X' k))

omit [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)] [∀ i, ParacompactSpace (X i)] in
/-- `mk j ⁻¹' (mk i '' U)` is empty for `i ≠ j`. -/
lemma sigmaMk_preimage_image_of_ne {i j : ι} (hji : j ≠ i) (U : Set (X i)) :
    (Sigma.mk j : X j → Σ k, X k) ⁻¹' (Sigma.mk i '' U) = ∅ :=
  eq_empty_of_subset_empty fun _ hx =>
    (sigmaMk_preimage_range_of_ne (Ne.symm hji)).subset (image_subset_range _ _ hx)

/-- **A summand-wise sc-diffeomorphism `U → V` gives one of the pieces `{i} × U → {σ i} × V`**
of the disjoint unions, for `Sigma.map σ g` (the inverse uses the junk value `y₀`). -/
theorem isScDiffeoOn_sigmaMap_image {σ : ι → κ} {g : ∀ i, X i → X' (σ i)} {i : ι}
    {h : X' (σ i) → X i} {U : Set (X i)} {V : Set (X' (σ i))}
    (hd : (P i).IsScDiffeoOn (R (σ i)) (g i) h U V) (y₀ : X' (σ i)) :
    (sigma P).IsScDiffeoOn (sigma R) (Sigma.map σ g) (Sigma.mk i ∘ h ∘ sigmaProj (σ i) y₀)
      (Sigma.mk i '' U) (Sigma.mk (σ i) '' V) where
  isScSmoothOn := by
    rw [isScSmoothOn_sigma_iff P (IsOpenEmbedding.sigmaMk.isOpenMap U hd.isOpen_source)]
    intro j
    by_cases hji : j = i
    · subst hji
      rw [preimage_image_eq _ sigma_mk_injective]
      exact (isScSmoothOn_sigmaMk_comp_iff R).2 hd.isScSmoothOn
    · rw [sigmaMk_preimage_image_of_ne hji]
      exact isScSmoothOn_empty _
  isScSmoothOn_inv := by
    have hVo : IsOpen (Sigma.mk (σ i) '' V) :=
      IsOpenEmbedding.sigmaMk.isOpenMap V hd.isOpen_target
    have h1 : (sigma R).IsScSmoothOn (P i) (h ∘ sigmaProj (σ i) y₀) (Sigma.mk (σ i) '' V) :=
      IsScSmoothOn.comp hd.isScSmoothOn_inv
        ((isScSmoothOn_sigmaProj R (σ i) y₀).mono hVo (image_subset_range _ _)) (by
          rintro _ ⟨y, hy, rfl⟩
          rw [sigmaProj_mk]; exact hy)
    exact IsScSmoothOn.comp (isScSmoothMap_sigmaMk P i) h1 (mapsTo_univ _ _)
  mapsTo := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨g i x, hd.mapsTo hx, rfl⟩
  mapsTo_inv := by
    rintro _ ⟨y, hy, rfl⟩
    change Sigma.mk i (h (sigmaProj (σ i) y₀ ⟨σ i, y⟩)) ∈ _
    rw [sigmaProj_mk]
    exact ⟨_, hd.mapsTo_inv hy, rfl⟩
  left_inv := by
    rintro _ ⟨x, hx, rfl⟩
    change Sigma.mk i (h (sigmaProj (σ i) y₀ ⟨σ i, g i x⟩)) = ⟨i, x⟩
    rw [sigmaProj_mk, hd.left_inv x hx]
  right_inv := by
    rintro _ ⟨y, hy, rfl⟩
    change (⟨σ i, g i (h (sigmaProj (σ i) y₀ ⟨σ i, y⟩))⟩ : Σ k, X' k) = ⟨σ i, y⟩
    rw [sigmaProj_mk, hd.right_inv y hy]

end SigmaImage

end MPolyfold

/-! ### `W[1]` is the disjoint union of the `K_λ[1]` -/

section One

variable {ι : Type*} {X : ι → Type u} [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)]
  [∀ i, ParacompactSpace (X i)] {PX : ∀ i, MPolyfold (X i)}
  {Y : ι → Type v} [∀ i, TopologicalSpace (Y i)] [∀ i, T2Space (Y i)]
  [∀ i, ParacompactSpace (Y i)] {p : ∀ i, Y i → X i}
  [∀ i x, AddCommGroup (p i ⁻¹' {x})] [∀ i x, Module ℝ (p i ⁻¹' {x})]
  (B : ∀ i, StrongBundle (PX i) (p i))

namespace StrongBundle

/-- `W[1] ≃ ⊔ K_λ[1]`: a point of `W_{0,1}` is a point of some `(K_λ)_{0,1}`. -/
def sigmaOneEquiv : (StrongBundle.sigma B).One ≃ Σ i, (B i).One where
  toFun w := ⟨((StrongBundle.sigma B).oneVal w).1,
    (B _).oneMk ((StrongBundle.sigma B).oneVal w).2
      ((mem_oneSet_sigma_iff ((StrongBundle.sigma B).oneVal w).2).1
        ((StrongBundle.sigma B).oneVal_mem w))⟩
  invFun u := (StrongBundle.sigma B).oneMk ⟨u.1, (B u.1).oneVal u.2⟩
    ((mem_oneSet_sigma_iff _).2 ((B u.1).oneVal_mem u.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The inverse of `sigmaOneEquiv` inserts the underlying point into the summand. -/
@[simp] lemma oneVal_sigmaOneEquiv_symm (i : ι) (u : (B i).One) :
    (StrongBundle.sigma B).oneVal ((sigmaOneEquiv B).symm ⟨i, u⟩) = ⟨i, (B i).oneVal u⟩ := rfl

/-- `sigmaOneEquiv` on a point of `W_{0,1}` over the summand `i`. -/
lemma sigmaOneEquiv_apply_of_eq {w : (StrongBundle.sigma B).One} {i : ι} {u : (B i).One}
    (h : (StrongBundle.sigma B).oneVal w = ⟨i, (B i).oneVal u⟩) : sigmaOneEquiv B w = ⟨i, u⟩ :=
  (sigmaOneEquiv B).eq_symm_apply.1 ((StrongBundle.sigma B).oneVal_injective h)

/-- Every point of `W[1]` is `sigmaOneEquiv⁻¹ (i, u)`. -/
lemma exists_sigmaOneEquiv_symm (w : (StrongBundle.sigma B).One) :
    ∃ (i : ι) (u : (B i).One), (sigmaOneEquiv B).symm ⟨i, u⟩ = w :=
  ⟨(sigmaOneEquiv B w).1, (sigmaOneEquiv B w).2, (sigmaOneEquiv B).symm_apply_apply w⟩

/-- The inverse of `sigmaOneEquiv` is sc-smooth: on the summand `i` it is the identity in the
charts `Φ[1]` and `(sigmaPush Φ)[1]`. -/
theorem isScSmoothMap_sigmaOneEquiv_symm :
    (MPolyfold.sigma fun i => (B i).toMPolyfold1).IsScSmoothMap
      (StrongBundle.sigma B).toMPolyfold1 (sigmaOneEquiv B).symm := by
  rw [MPolyfold.isScSmoothMap_sigma_iff]
  intro i
  refine MPolyfold.isScSmoothMap_of_forall_charts fun u => ?_
  obtain ⟨c, hc, hu⟩ := (B i).atlas.cover ((B i).oneVal u)
  have hc' := sigmaPush_mem_sigma_atlas (B := B) hc
  refine ⟨oneChart hc u, oneChart hc' ((sigmaOneEquiv B).symm ⟨i, u⟩), (B i).isChart_oneChart hc u,
    (StrongBundle.sigma B).isChart_oneChart hc' _, hu, fun u' hu' => ⟨_, hu', rfl⟩, ?_⟩
  refine (isScSmoothRetractMap_id _).congr fun z hz => ?_
  change z = (c.sigmaPush (B i).continuous).liftOne ⟨i, (B i).oneVal ((oneChart hc u).symm z)⟩
  unfold StrongBundleChart.liftOne
  rw [StrongBundleChart.sigmaPush_apply]
  exact ((oneChart hc u).apply_symm_apply hz).symm

/-- `sigmaOneEquiv` is sc-smooth: in the charts `(sigmaPush Φ)[1]` and `sigmaChart i Φ[1]` it is
the identity. -/
theorem isScSmoothMap_sigmaOneEquiv :
    (StrongBundle.sigma B).toMPolyfold1.IsScSmoothMap
      (MPolyfold.sigma fun i => (B i).toMPolyfold1) (sigmaOneEquiv B) := by
  refine MPolyfold.isScSmoothMap_of_forall_charts fun w => ?_
  obtain ⟨i, u, rfl⟩ := exists_sigmaOneEquiv_symm B w
  obtain ⟨c, hc, hu⟩ := (B i).atlas.cover ((B i).oneVal u)
  have hc' := sigmaPush_mem_sigma_atlas (B := B) hc
  refine ⟨oneChart hc' ((sigmaOneEquiv B).symm ⟨i, u⟩), MPolyfold.sigmaChart i (oneChart hc u),
    (StrongBundle.sigma B).isChart_oneChart hc' _,
    MPolyfold.IsChart.sigmaChart (P := fun i => (B i).toMPolyfold1) (i := i)
      ((B i).isChart_oneChart hc u),
    ⟨_, hu, rfl⟩, ?_, ?_⟩
  · rintro w' ⟨y, hy, hyw⟩
    have hy1 : y ∈ (B i).oneSet := by
      rw [← mem_oneSet_sigma_iff (B := B), show (⟨i, y⟩ : Σ i, Y i) = _ from hyw]
      exact (StrongBundle.sigma B).oneVal_mem w'
    rw [sigmaOneEquiv_apply_of_eq B (u := (B i).oneMk y hy1) hyw.symm]
    exact ⟨_, hy, rfl⟩
  · refine (isScSmoothRetractMap_id _).congr fun z hz => ?_
    have hz' : z ∈ strongShiftOne c.K := hz
    have hy1 := symm_mem_oneSet hc hz'
    have hval : (StrongBundle.sigma B).oneVal
        ((oneChart hc' ((sigmaOneEquiv B).symm ⟨i, u⟩)).symm z) =
        ⟨i, (B i).oneVal ((B i).oneMk _ hy1)⟩ :=
      oneChart_symm_apply hc' _ hz
    change z = MPolyfold.sigmaChart i (oneChart hc u)
      (sigmaOneEquiv B ((oneChart hc' ((sigmaOneEquiv B).symm ⟨i, u⟩)).symm z))
    rw [sigmaOneEquiv_apply_of_eq B hval, MPolyfold.sigmaChart_apply]
    exact (liftOne_symm hz').symm

/-- **`W[1]` and `⊔ K_λ[1]` are sc-diffeomorphic** by `sigmaOneEquiv`. -/
theorem isScDiffeoOn_sigmaOneEquiv :
    (StrongBundle.sigma B).toMPolyfold1.IsScDiffeoOn
      (MPolyfold.sigma fun i => (B i).toMPolyfold1) (sigmaOneEquiv B) (sigmaOneEquiv B).symm
      univ univ where
  isScSmoothOn := isScSmoothMap_sigmaOneEquiv B
  isScSmoothOn_inv := isScSmoothMap_sigmaOneEquiv_symm B
  mapsTo _ _ := mem_univ _
  mapsTo_inv _ _ := mem_univ _
  left_inv w _ := (sigmaOneEquiv B).symm_apply_apply w
  right_inv u _ := (sigmaOneEquiv B).apply_symm_apply u

/-- The preimage of a piece `{i} × K_i[1]|U` under `sigmaOneEquiv` is `W[1]|({i} × U)`. -/
lemma sigmaOneEquiv_preimage_image {i : ι} (U : Set (X i)) :
    sigmaOneEquiv B ⁻¹' (Sigma.mk i '' ((p i ∘ (B i).oneVal) ⁻¹' U)) =
      (sigmaBundleProj p ∘ (StrongBundle.sigma B).oneVal) ⁻¹' (Sigma.mk i '' U) := by
  ext w
  obtain ⟨j, u, rfl⟩ := exists_sigmaOneEquiv_symm B w
  simp only [mem_preimage, Equiv.apply_symm_apply, Function.comp_apply,
    oneVal_sigmaOneEquiv_symm, sigmaBundleProj_mk]
  constructor
  · rintro ⟨a, ha, hau⟩
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 hau
    cases eq_of_heq h
    exact ⟨_, ha, rfl⟩
  · rintro ⟨x, hx, hxu⟩
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 hxu
    cases eq_of_heq h
    exact ⟨u, hx, rfl⟩

end StrongBundle

end One

/-! ### Strong bundle maps into, out of, and between disjoint unions -/

section Maps

universe u' v'

variable {ι : Type*} {X : ι → Type u} [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)]
  [∀ i, ParacompactSpace (X i)] {PX : ∀ i, MPolyfold (X i)}
  {Y : ι → Type v} [∀ i, TopologicalSpace (Y i)] [∀ i, T2Space (Y i)]
  [∀ i, ParacompactSpace (Y i)] {p : ∀ i, Y i → X i}
  [∀ i x, AddCommGroup (p i ⁻¹' {x})] [∀ i x, Module ℝ (p i ⁻¹' {x})]
  (B : ∀ i, StrongBundle (PX i) (p i))

namespace StrongBundle

/-- **The inclusion of a summand is a strong bundle map** `K_i → ⊔ K_λ` covering
`Sigma.mk i : O_i → ⊔ O_λ` (used for §17.7). -/
theorem isStrongBundleMap_sigmaMk (i : ι) :
    (B i).IsStrongBundleMap (StrongBundle.sigma B) (Sigma.mk i) (Sigma.mk i) where
  covers _ := rfl
  fiber_linear x := by
    have : fiberRestrict (p i) (sigmaBundleProj p) (Sigma.mk i) (Sigma.mk i) (fun _ => rfl) x =
        ⇑((sigmaFiberLinearEquiv p ⟨i, x⟩).symm.toLinearMap) := rfl
    rw [this]; exact LinearMap.isLinear _
  isScSmoothMap := by
    rw [sigma_toMPolyfold0]
    exact MPolyfold.isScSmoothMap_sigmaMk (fun i => (B i).toMPolyfold0) i
  mapsTo_oneSet y hy := (mem_oneSet_sigma_iff y).2 hy
  isScSmoothMap_one :=
    (isScSmoothMap_sigmaOneEquiv_symm B).comp
      (MPolyfold.isScSmoothMap_sigmaMk (fun i => (B i).toMPolyfold1) i)

variable {X' : Type*} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type*} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] (B' : StrongBundle PX' P')

/-- **Strong bundle maps out of `⊔ K_λ`** are the families of strong bundle maps out of the
`K_λ` (used for §17.7). -/
theorem isStrongBundleMap_sigma_iff {f : (Σ i, X i) → X'} {Φ : (Σ i, Y i) → Y'} :
    (StrongBundle.sigma B).IsStrongBundleMap B' f Φ ↔
      ∀ i, (B i).IsStrongBundleMap B' (f ∘ Sigma.mk i) (Φ ∘ Sigma.mk i) := by
  refine ⟨fun h i => h.comp (isStrongBundleMap_sigmaMk B i), fun h => ?_⟩
  have hcov : ∀ y, P' (Φ y) = f (sigmaBundleProj p y) := by
    rintro ⟨i, y⟩; exact (h i).covers y
  refine
    { covers := hcov
      fiber_linear := ?_
      isScSmoothMap := ?_
      mapsTo_oneSet := ?_
      isScSmoothMap_one := ?_ }
  · rintro ⟨i, x⟩
    have : fiberRestrict (sigmaBundleProj p) P' f Φ hcov ⟨i, x⟩ =
        ⇑(((h i).fiberLinearMap x).comp (sigmaFiberLinearEquiv p ⟨i, x⟩).toLinearMap) := by
      funext v
      apply Subtype.ext
      exact (congrArg Φ (mk_sigmaFiberEquiv p ⟨i, x⟩ v)).symm
    rw [this]; exact LinearMap.isLinear _
  · rw [sigma_toMPolyfold0, MPolyfold.isScSmoothMap_sigma_iff]
    exact fun i => (h i).isScSmoothMap
  · rintro ⟨i, y⟩ hy
    exact (h i).mapsTo_oneSet ((mem_oneSet_sigma_iff y).1 hy)
  · have hg : (MPolyfold.sigma fun i => (B i).toMPolyfold1).IsScSmoothMap B'.toMPolyfold1
        (fun u => oneRestrict (B u.1) B' (Φ ∘ Sigma.mk u.1) (h u.1).mapsTo_oneSet u.2) :=
      (MPolyfold.isScSmoothMap_sigma_iff (fun i => (B i).toMPolyfold1)).2 fun i =>
        (h i).isScSmoothMap_one
    exact (hg.comp (isScSmoothMap_sigmaOneEquiv B)).congr fun w _ => rfl

/-- **Strong bundle maps into one summand**: `Sigma.mk j ∘ Φ` is a strong bundle map into
`⊔ K_λ` covering `Sigma.mk j ∘ f` if and only if `Φ` is one into `K_j` covering `f` (used for
§17.7). -/
theorem isStrongBundleMap_sigmaMk_comp_iff {j : ι} {f : X' → X j} {Φ : Y' → Y j} :
    B'.IsStrongBundleMap (StrongBundle.sigma B) (Sigma.mk j ∘ f) (Sigma.mk j ∘ Φ) ↔
      B'.IsStrongBundleMap (B j) f Φ := by
  constructor
  · intro h
    have hcov : ∀ y, p j (Φ y) = f (P' y) := fun y => sigma_mk_injective (h.covers y)
    refine
      { covers := hcov
        fiber_linear := fun x => ?_
        isScSmoothMap := ?_
        mapsTo_oneSet := fun y hy => (mem_oneSet_sigma_iff _).1 (h.mapsTo_oneSet hy)
        isScSmoothMap_one := ?_ }
    · have : fiberRestrict P' (p j) f Φ hcov x =
          ⇑((sigmaFiberLinearEquiv p ⟨j, f x⟩).toLinearMap.comp (h.fiberLinearMap x)) := rfl
      rw [this]; exact LinearMap.isLinear _
    · have := h.isScSmoothMap
      rw [sigma_toMPolyfold0] at this
      exact (MPolyfold.isScSmoothMap_sigmaMk_comp_iff (fun i => (B i).toMPolyfold0)
        (i := j)).1 this
    · have := (isScSmoothMap_sigmaOneEquiv B).comp h.isScSmoothMap_one
      exact (MPolyfold.isScSmoothMap_sigmaMk_comp_iff (fun i => (B i).toMPolyfold1)
        (i := j)).1 this
  · intro h
    have hcov : ∀ y, sigmaBundleProj p ((Sigma.mk j ∘ Φ) y) = (Sigma.mk j ∘ f) (P' y) :=
      fun y => congrArg (Sigma.mk j) (h.covers y)
    refine
      { covers := hcov
        fiber_linear := fun x => ?_
        isScSmoothMap := ?_
        mapsTo_oneSet := fun y hy => (mem_oneSet_sigma_iff _).2 (h.mapsTo_oneSet hy)
        isScSmoothMap_one := ?_ }
    · have : fiberRestrict P' (sigmaBundleProj p) (Sigma.mk j ∘ f) (Sigma.mk j ∘ Φ) hcov x =
          ⇑((sigmaFiberLinearEquiv p ⟨j, f x⟩).symm.toLinearMap.comp (h.fiberLinearMap x)) := rfl
      rw [this]; exact LinearMap.isLinear _
    · rw [sigma_toMPolyfold0]
      exact (MPolyfold.isScSmoothMap_sigmaMk_comp_iff (fun i => (B i).toMPolyfold0)
        (i := j)).2 h.isScSmoothMap
    · exact (isScSmoothMap_sigmaOneEquiv_symm B).comp
        ((MPolyfold.isScSmoothMap_sigmaMk_comp_iff (fun i => (B i).toMPolyfold1)
          (i := j)).2 h.isScSmoothMap_one)

variable {κ : Type*} {X'' : κ → Type u'} [∀ k, TopologicalSpace (X'' k)] [∀ k, T2Space (X'' k)]
  [∀ k, ParacompactSpace (X'' k)] {PX'' : ∀ k, MPolyfold (X'' k)}
  {Y'' : κ → Type v'} [∀ k, TopologicalSpace (Y'' k)] [∀ k, T2Space (Y'' k)]
  [∀ k, ParacompactSpace (Y'' k)] {p'' : ∀ k, Y'' k → X'' k}
  [∀ k x, AddCommGroup (p'' k ⁻¹' {x})] [∀ k x, Module ℝ (p'' k ⁻¹' {x})]
  (B'' : ∀ k, StrongBundle (PX'' k) (p'' k))

/-- **Maps between disjoint unions**: `Sigma.map σ Φ` is a strong bundle map covering
`Sigma.map σ f` if every `Φ i : K_i → K''_{σ i}` is one covering `f i` (used for §17.7). -/
theorem isStrongBundleMap_sigmaMap {σ : ι → κ} {f : ∀ i, X i → X'' (σ i)}
    {Φ : ∀ i, Y i → Y'' (σ i)} (h : ∀ i, (B i).IsStrongBundleMap (B'' (σ i)) (f i) (Φ i)) :
    (StrongBundle.sigma B).IsStrongBundleMap (StrongBundle.sigma B'') (Sigma.map σ f)
      (Sigma.map σ Φ) :=
  (isStrongBundleMap_sigma_iff B (StrongBundle.sigma B'')).2 fun i =>
    (isStrongBundleMap_sigmaMk_comp_iff B'' (B i)).2 (h i)

/-- **Local strong bundle isomorphisms between disjoint unions, on one piece**: if
`Φ i : K_i|U → K''_{σ i}|U'` is a strong bundle isomorphism (Chapter 8's
`IsStrongBundleIsoOn`), so is `Sigma.map σ Φ : W|({i} × U) → W''|({σ i} × U')`. -/
theorem isStrongBundleIsoOn_sigmaMap_image {σ : ι → κ} {f : ∀ i, X i → X'' (σ i)}
    {Φ : ∀ i, Y i → Y'' (σ i)} (h : ∀ i, (B i).IsStrongBundleMap (B'' (σ i)) (f i) (Φ i))
    {i : ι} {U : Set (X i)} {U' : Set (X'' (σ i))}
    (hi : (B i).IsStrongBundleIsoOn (B'' (σ i)) (h i) U U') (hU : U.Nonempty) :
    (StrongBundle.sigma B).IsStrongBundleIsoOn (StrongBundle.sigma B'')
      (isStrongBundleMap_sigmaMap B B'' h) (Sigma.mk i '' U) (Sigma.mk (σ i) '' U') := by
  obtain ⟨x₀, -⟩ := hU
  obtain ⟨g, hg⟩ := hi.isScDiffeoOn_base
  obtain ⟨Ψ, hΨ⟩ := hi.isScDiffeoOn_zero
  obtain ⟨Ψ₁, hΨ₁⟩ := hi.isScDiffeoOn_one
  obtain ⟨y₀, -⟩ := (B'' (σ i)).surjective (f i x₀)
  refine ⟨⟨_, MPolyfold.isScDiffeoOn_sigmaMap_image PX PX'' hg (f i x₀)⟩, ?_, ?_⟩
  · rw [sigma_toMPolyfold0, sigma_toMPolyfold0, sigmaBundleProj_preimage_image,
      sigmaBundleProj_preimage_image]
    exact ⟨_, MPolyfold.isScDiffeoOn_sigmaMap_image _ _ hΨ y₀⟩
  · set u₀ : (B'' (σ i)).One :=
      (B'' (σ i)).oneMk (fiberZero (p'' (σ i)) (f i x₀)) ((B'' (σ i)).fiberZero_mem_oneSet _)
    have hmid := MPolyfold.isScDiffeoOn_sigmaMap_image (fun i => (B i).toMPolyfold1)
      (fun k => (B'' k).toMPolyfold1)
      (g := fun i => oneRestrict (B i) (B'' (σ i)) (Φ i) (h i).mapsTo_oneSet) hΨ₁ u₀
    have hc := MPolyfold.IsScDiffeoOn.conj (isScDiffeoOn_sigmaOneEquiv B)
      (isScDiffeoOn_sigmaOneEquiv B'') hmid
    rw [sigmaOneEquiv_preimage_image, sigmaOneEquiv_preimage_image] at hc
    exact ⟨_, hc.congr fun w _ => rfl⟩

/-- **Local strong bundle isomorphisms between disjoint unions** (the condition
`isLocalStrongBundleIso_obj` of Chapter 10's `IsStrongBundleEquivalence`, used for §17.7): if
every `Φ i` is a local strong bundle isomorphism around every point, so is `Sigma.map σ Φ`. -/
theorem isStrongBundleIsoOn_sigmaMap {σ : ι → κ} {f : ∀ i, X i → X'' (σ i)}
    {Φ : ∀ i, Y i → Y'' (σ i)} (h : ∀ i, (B i).IsStrongBundleMap (B'' (σ i)) (f i) (Φ i))
    (hiso : ∀ i (x : X i), ∃ (U : Set (X i)) (U' : Set (X'' (σ i))), x ∈ U ∧
      (B i).IsStrongBundleIsoOn (B'' (σ i)) (h i) U U') :
    ∀ x : Σ i, X i, ∃ (U : Set (Σ i, X i)) (U' : Set (Σ k, X'' k)), x ∈ U ∧
      (StrongBundle.sigma B).IsStrongBundleIsoOn (StrongBundle.sigma B'')
        (isStrongBundleMap_sigmaMap B B'' h) U U' := by
  rintro ⟨i, x⟩
  obtain ⟨U, U', hx, hi⟩ := hiso i x
  exact ⟨Sigma.mk i '' U, Sigma.mk (σ i) '' U', ⟨x, hx, rfl⟩,
    isStrongBundleIsoOn_sigmaMap_image B B'' h hi ⟨x, hx⟩⟩

end StrongBundle

end Maps

/-! ### Pull-backs along maps of disjoint unions -/

/-- The inverse of a bijective linear map is linear. -/
theorem isLinearMap_of_inverse {M N : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N]
    [Module ℝ N] (L : M →ₗ[ℝ] N) {g : N → M} (h1 : ∀ m, g (L m) = m) (h2 : ∀ n, L (g n) = n) :
    IsLinearMap ℝ g where
  map_add a b := by
    conv_lhs => rw [← h2 a, ← h2 b, ← map_add, h1]
  map_smul c a := by
    conv_lhs => rw [← h2 a, ← map_smul, h1]

section PullbackDefs

variable {ι : Type*} {X : ι → Type*} {Y : ι → Type*} {p : ∀ i, Y i → X i}
  {κ : Type*} {Z : κ → Type*} {σ : κ → ι} {s : ∀ j, Z j → X (σ j)}

/-- The inclusion `s_j*K_{σ j} → S*W`, `((z, y), h) ↦ (((j, z), (σ j, y)), _)`, of the pull-back
of the summand `K_{σ j}` along `s_j` into the pull-back of `W = ⊔ K_λ` along
`S = Sigma.map σ s : (j, z) ↦ (σ j, s_j(z))` (used for §17.7). -/
def pullbackSigmaIncl (j : κ) (q : pullbackSpace (p (σ j)) (s j)) :
    pullbackSpace (sigmaBundleProj p) (Sigma.map σ s) :=
  ⟨(⟨j, q.1.1⟩, ⟨σ j, q.1.2⟩), by
    change (⟨σ j, p (σ j) q.1.2⟩ : Σ i, X i) = ⟨σ j, s j q.1.1⟩
    rw [show p (σ j) q.1.2 = s j q.1.1 from q.2]⟩

/-- The underlying pair of `pullbackSigmaIncl j q`. -/
@[simp] lemma pullbackSigmaIncl_val (j : κ) (q : pullbackSpace (p (σ j)) (s j)) :
    (pullbackSigmaIncl j q : (Σ j, Z j) × Σ i, Y i) = (⟨j, q.1.1⟩, ⟨σ j, q.1.2⟩) := rfl

/-- The inverse `S*W → ⊔ s_j*K_{σ j}` of the inclusions `pullbackSigmaIncl j`. -/
def pullbackSigmaProj (q : pullbackSpace (sigmaBundleProj p) (Sigma.map σ s)) :
    Σ j, pullbackSpace (p (σ j)) (s j) :=
  ⟨q.1.1.1, ⟨(q.1.1.2, sigmaLift (σ q.1.1.1) q.1.2 (congrArg Sigma.fst q.2)), by
    have h1 := congrArg (sigmaBundleProj p)
      (mk_sigmaLift (σ q.1.1.1) q.1.2 (congrArg Sigma.fst q.2))
    exact sigma_mk_injective (h1.trans q.2)⟩⟩

/-- `pullbackSigmaProj` inverts `pullbackSigmaIncl j`. -/
@[simp] lemma pullbackSigmaProj_incl (j : κ) (q : pullbackSpace (p (σ j)) (s j)) :
    pullbackSigmaProj (pullbackSigmaIncl j q) = ⟨j, q⟩ := rfl

/-- `pullbackSigmaIncl` inverts `pullbackSigmaProj`. -/
lemma pullbackSigmaIncl_proj (q : pullbackSpace (sigmaBundleProj p) (Sigma.map σ s)) :
    pullbackSigmaIncl (pullbackSigmaProj q).1 (pullbackSigmaProj q).2 = q :=
  Subtype.ext (Prod.ext rfl (mk_sigmaLift _ _ _))

/-- **`S*W = ⊔ s_j*K_{σ j}`**: the pull-back of the disjoint union is the disjoint union of the
pull-backs (as sets; `isStrongBundleIso_pullbackSigma` for the strong bundles). -/
def pullbackSigmaEquiv :
    (Σ j, pullbackSpace (p (σ j)) (s j)) ≃ pullbackSpace (sigmaBundleProj p) (Sigma.map σ s) where
  toFun u := pullbackSigmaIncl u.1 u.2
  invFun := pullbackSigmaProj
  left_inv _ := rfl
  right_inv := pullbackSigmaIncl_proj

/-- `pullbackSigmaEquiv` on the summand `j` is `pullbackSigmaIncl j`. -/
@[simp] lemma pullbackSigmaEquiv_mk (j : κ) (q : pullbackSpace (p (σ j)) (s j)) :
    pullbackSigmaEquiv ⟨j, q⟩ = pullbackSigmaIncl j q := rfl

/-- The inverse of `pullbackSigmaEquiv` is `pullbackSigmaProj`. -/
@[simp] lemma pullbackSigmaEquiv_symm_apply
    (q : pullbackSpace (sigmaBundleProj p) (Sigma.map σ s)) :
    pullbackSigmaEquiv.symm q = pullbackSigmaProj q := rfl

/-- A point of `S*W` over the summand `j` comes from `s_j*K_{σ j}`. -/
lemma exists_pullbackSigmaIncl_of_mem {j : κ}
    {q : pullbackSpace (sigmaBundleProj p) (Sigma.map σ s)}
    (hq : q ∈ pullbackProj (sigmaBundleProj p) (Sigma.map σ s) ⁻¹' range (Sigma.mk j)) :
    ∃ q', pullbackSigmaIncl j q' = q := by
  obtain ⟨z, hz⟩ := hq
  obtain ⟨⟨⟨j', z'⟩, w⟩, hqw⟩ := q
  have hz' : (⟨j, z⟩ : Σ j, Z j) = ⟨j', z'⟩ := hz
  obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.1 hz'
  cases eq_of_heq hh
  exact ⟨_, pullbackSigmaIncl_proj ⟨(⟨j, z⟩, w), hqw⟩⟩

variable {ι' : Type*} {X'' : ι' → Type*} {Y'' : ι' → Type*} {p'' : ∀ i, Y'' i → X'' i}
  {κ' : Type*} {Z' : κ' → Type*} {σ' : κ' → ι'} {s' : ∀ j, Z' j → X'' (σ' j)}

/-- The map `S*W → S'*W''` assembled from maps `Φ_j : s_j*K_{σ j} → s'_{τ j}*K''_{σ' (τ j)}` of the
pieces: `pullbackSigmaIncl j q ↦ pullbackSigmaIncl (τ j) (Φ_j q)`. -/
def pullbackSigmaMap {τ : κ → κ'}
    (Φ : ∀ j, pullbackSpace (p (σ j)) (s j) → pullbackSpace (p'' (σ' (τ j))) (s' (τ j)))
    (q : pullbackSpace (sigmaBundleProj p) (Sigma.map σ s)) :
    pullbackSpace (sigmaBundleProj p'') (Sigma.map σ' s') :=
  pullbackSigmaEquiv (Sigma.map τ Φ (pullbackSigmaProj q))

/-- `pullbackSigmaMap Φ` on the piece `j` is `Φ_j`. -/
@[simp] lemma pullbackSigmaMap_incl {τ : κ → κ'}
    (Φ : ∀ j, pullbackSpace (p (σ j)) (s j) → pullbackSpace (p'' (σ' (τ j))) (s' (τ j)))
    (j : κ) (q : pullbackSpace (p (σ j)) (s j)) :
    pullbackSigmaMap Φ (pullbackSigmaIncl j q) = pullbackSigmaIncl (τ j) (Φ j q) := rfl

end PullbackDefs

section Pullback

universe u₁ v₁ w₁ w₂

variable {ι : Type*} {X : ι → Type u} [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)]
  [∀ i, ParacompactSpace (X i)] {PX : ∀ i, MPolyfold (X i)}
  {Y : ι → Type v} [∀ i, TopologicalSpace (Y i)] [∀ i, T2Space (Y i)]
  [∀ i, ParacompactSpace (Y i)] {p : ∀ i, Y i → X i}
  [∀ i x, AddCommGroup (p i ⁻¹' {x})] [∀ i x, Module ℝ (p i ⁻¹' {x})]
  (B : ∀ i, StrongBundle (PX i) (p i))
  {κ : Type*} {Z : κ → Type w} [∀ j, TopologicalSpace (Z j)] [∀ j, T2Space (Z j)]
  [∀ j, ParacompactSpace (Z j)] {PZ : ∀ j, MPolyfold (Z j)}
  {σ : κ → ι} {s : ∀ j, Z j → X (σ j)}
  [∀ j, ParacompactSpace (pullbackSpace (p (σ j)) (s j))]
  [ParacompactSpace (pullbackSpace (sigmaBundleProj p) (Sigma.map σ s))]
  (hs : ∀ j, (PZ j).IsScSmoothMap (PX (σ j)) (s j))
  (hS : (MPolyfold.sigma PZ).IsScSmoothMap (MPolyfold.sigma PX) (Sigma.map σ s))

namespace StrongBundle

/-- **The inclusion `s_j*K_{σ j} → S*W` is a strong bundle map** covering `Sigma.mk j` (Chapter
8's `isStrongBundleMap_pullbackMap` for the strong bundle map `Sigma.mk (σ j)`). -/
theorem isStrongBundleMap_pullbackSigmaIncl (j : κ) :
    ((B (σ j)).pullback (hs j)).IsStrongBundleMap ((StrongBundle.sigma B).pullback hS)
      (Sigma.mk j) (pullbackSigmaIncl j) :=
  StrongBundle.isStrongBundleMap_pullbackMap (hs j) hS (isStrongBundleMap_sigmaMk B (σ j))
    (MPolyfold.isScSmoothMap_sigmaMk PZ j) (fun _ => rfl)

/-- `⊔ s_j*K_{σ j} → S*W` is a strong bundle map covering the identity. -/
theorem isStrongBundleMap_pullbackSigmaEquiv :
    (StrongBundle.sigma fun j => (B (σ j)).pullback (hs j)).IsStrongBundleMap
      ((StrongBundle.sigma B).pullback hS) id pullbackSigmaEquiv :=
  (isStrongBundleMap_sigma_iff (fun j => (B (σ j)).pullback (hs j)) _).2 fun j =>
    isStrongBundleMap_pullbackSigmaIncl B hs hS j

/-- `S*W[0] → ⊔ s_j*K_{σ j}[0]` is sc-smooth: over the summand `j` it is
`q ↦ (P_S(q), P'(q))` read in `s_j*K_{σ j}` (the universal property of the pull-back). -/
theorem isScSmoothMap_pullbackSigmaProj :
    ((StrongBundle.sigma B).pullback hS).toMPolyfold0.IsScSmoothMap
      (StrongBundle.sigma fun j => (B (σ j)).pullback (hs j)).toMPolyfold0 pullbackSigmaProj := by
  rw [sigma_toMPolyfold0]
  have h0 := (StrongBundle.sigma B).isScSmoothMap_pullbackProj' hS
  rw [sigma_toMPolyfold0] at h0
  have hpiece : ∀ (j : κ) (q₀ : pullbackSpace (p (σ j)) (s j)),
      ((StrongBundle.sigma B).pullback hS).toMPolyfold0.IsScSmoothOn
        (MPolyfold.sigma fun j => ((B (σ j)).pullback (hs j)).toMPolyfold0) pullbackSigmaProj
        (pullbackProj (sigmaBundleProj p) (Sigma.map σ s) ⁻¹' range (Sigma.mk j)) := by
    intro j q₀
    have hW : IsOpen (pullbackProj (sigmaBundleProj p) (Sigma.map σ s) ⁻¹' range (Sigma.mk j)) :=
      isOpen_range_sigmaMk.preimage (continuous_pullbackProj _ _)
    have hmaps : MapsTo pullbackSigmaProj
        (pullbackProj (sigmaBundleProj p) (Sigma.map σ s) ⁻¹' range (Sigma.mk j))
        (range (Sigma.mk j)) := by
      intro q hq
      obtain ⟨q', rfl⟩ := exists_pullbackSigmaIncl_of_mem hq
      exact ⟨q', rfl⟩
    refine (MPolyfold.isScSmoothOn_sigma_iff_of_mapsTo
      (fun j => ((B (σ j)).pullback (hs j)).toMPolyfold0) q₀ hmaps).2 ?_
    have ha : ((StrongBundle.sigma B).pullback hS).toMPolyfold0.IsScSmoothOn (PZ j)
        (sigmaProj j q₀.1.1 ∘ pullbackProj (sigmaBundleProj p) (Sigma.map σ s))
        (pullbackProj (sigmaBundleProj p) (Sigma.map σ s) ⁻¹' range (Sigma.mk j)) :=
      MPolyfold.IsScSmoothOn.comp (MPolyfold.isScSmoothOn_sigmaProj PZ j q₀.1.1)
        (((StrongBundle.sigma B).pullback hS).isScSmoothMap_proj.mono hW (subset_univ _))
        fun q hq => hq
    have hb : ((StrongBundle.sigma B).pullback hS).toMPolyfold0.IsScSmoothOn
        (B (σ j)).toMPolyfold0
        (sigmaProj (σ j) q₀.1.2 ∘ pullbackProj' (sigmaBundleProj p) (Sigma.map σ s))
        (pullbackProj (sigmaBundleProj p) (Sigma.map σ s) ⁻¹' range (Sigma.mk j)) := by
      refine MPolyfold.IsScSmoothOn.comp
        (MPolyfold.isScSmoothOn_sigmaProj (fun i => (B i).toMPolyfold0) (σ j) q₀.1.2)
        (h0.mono hW (subset_univ _)) ?_
      intro q hq
      obtain ⟨q', rfl⟩ := exists_pullbackSigmaIncl_of_mem hq
      exact ⟨q'.1.2, rfl⟩
    refine (B (σ j)).isScSmoothOn_to_pullback_of_eqOn (hs j) ha hb ?_
    intro q hq
    obtain ⟨q', rfl⟩ := exists_pullbackSigmaIncl_of_mem hq
    change ((sigmaProj (X := fun j => ↥(pullbackSpace (p (σ j)) (s j))) j q₀ ⟨j, q'⟩ :
      pullbackSpace (p (σ j)) (s j)) : Z j × Y (σ j)) =
      (sigmaProj j q₀.1.1 ⟨j, q'.1.1⟩, sigmaProj (σ j) q₀.1.2 ⟨σ j, q'.1.2⟩)
    rw [sigmaProj_mk, sigmaProj_mk, sigmaProj_mk]
  refine MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun q _ =>
    ⟨_, isOpen_range_sigmaMk.preimage (continuous_pullbackProj _ _), ⟨q.1.1.2, rfl⟩,
      subset_univ _, hpiece q.1.1.1 (pullbackSigmaProj q).2⟩

/-- `(S*W)_{0,1}` corresponds to `(s_j*K_{σ j})_{0,1}`. -/
theorem mem_oneSet_pullbackSigmaIncl_iff (j : κ) (q : pullbackSpace (p (σ j)) (s j)) :
    pullbackSigmaIncl j q ∈ ((StrongBundle.sigma B).pullback hS).oneSet ↔
      q ∈ ((B (σ j)).pullback (hs j)).oneSet := by
  rw [(StrongBundle.sigma B).mem_oneSet_pullback_iff hS, (B (σ j)).mem_oneSet_pullback_iff (hs j)]
  exact mem_oneSet_sigma_iff (B := B) q.1.2

/-- `pullbackSigmaProj` maps `(S*W)_{0,1}` into `(⊔ s_j*K_{σ j})_{0,1}`. -/
theorem mapsTo_oneSet_pullbackSigmaProj :
    MapsTo pullbackSigmaProj ((StrongBundle.sigma B).pullback hS).oneSet
      (StrongBundle.sigma fun j => (B (σ j)).pullback (hs j)).oneSet := by
  intro q hq
  rw [← pullbackSigmaIncl_proj q, mem_oneSet_pullbackSigmaIncl_iff B hs hS] at hq
  exact (mem_oneSet_sigma_iff (B := fun j => (B (σ j)).pullback (hs j))
    (pullbackSigmaProj q).2).2 hq

/-- `S*W[1] → ⊔ s_j*K_{σ j}[1]` is sc-smooth (the universal property of the pull-back at level
`[1]`, Chapter 10's `isScSmoothOn_to_pullback_one`, over each summand). -/
theorem isScSmoothMap_one_pullbackSigmaProj :
    ((StrongBundle.sigma B).pullback hS).toMPolyfold1.IsScSmoothMap
      (StrongBundle.sigma fun j => (B (σ j)).pullback (hs j)).toMPolyfold1
      (oneRestrict _ _ pullbackSigmaProj (mapsTo_oneSet_pullbackSigmaProj B hs hS)) := by
  have hm := mapsTo_oneSet_pullbackSigmaProj B hs hS
  -- `F = sigmaOneEquiv ∘ oneRestrict pullbackSigmaProj`, a map into `⊔ s_j*K_{σ j}[1]`
  suffices hF : ((StrongBundle.sigma B).pullback hS).toMPolyfold1.IsScSmoothMap
      (MPolyfold.sigma fun j => ((B (σ j)).pullback (hs j)).toMPolyfold1)
      (sigmaOneEquiv (fun j => (B (σ j)).pullback (hs j)) ∘
        oneRestrict _ _ pullbackSigmaProj hm) by
    exact ((isScSmoothMap_sigmaOneEquiv_symm (fun j => (B (σ j)).pullback (hs j))).comp
      hF).congr fun w _ => (sigmaOneEquiv _).symm_apply_apply _
  have hpiece : ∀ (j : κ) (u₀ : ((B (σ j)).pullback (hs j)).One),
      ((StrongBundle.sigma B).pullback hS).toMPolyfold1.IsScSmoothOn
        (MPolyfold.sigma fun j => ((B (σ j)).pullback (hs j)).toMPolyfold1)
        (sigmaOneEquiv (fun j => (B (σ j)).pullback (hs j)) ∘
          oneRestrict _ _ pullbackSigmaProj hm)
        ((pullbackProj (sigmaBundleProj p) (Sigma.map σ s) ∘
          ((StrongBundle.sigma B).pullback hS).oneVal) ⁻¹' range (Sigma.mk j)) := by
    intro j u₀
    have hW : IsOpen ((pullbackProj (sigmaBundleProj p) (Sigma.map σ s) ∘
        ((StrongBundle.sigma B).pullback hS).oneVal) ⁻¹' range (Sigma.mk j)) :=
      isOpen_range_sigmaMk.preimage
        ((continuous_pullbackProj _ _).comp ((StrongBundle.sigma B).pullback hS).continuous_oneVal)
    -- the points over the summand `j`
    have hdesc : ∀ w ∈ (pullbackProj (sigmaBundleProj p) (Sigma.map σ s) ∘
        ((StrongBundle.sigma B).pullback hS).oneVal) ⁻¹' range (Sigma.mk j),
        ∃ (q' : pullbackSpace (p (σ j)) (s j)) (hq' : q' ∈ ((B (σ j)).pullback (hs j)).oneSet),
          ((StrongBundle.sigma B).pullback hS).oneVal w = pullbackSigmaIncl j q' := by
      intro w hw
      obtain ⟨q', hq'⟩ := exists_pullbackSigmaIncl_of_mem hw
      refine ⟨q', ?_, hq'.symm⟩
      rw [← mem_oneSet_pullbackSigmaIncl_iff B hs hS, hq']
      exact ((StrongBundle.sigma B).pullback hS).oneVal_mem w
    have hFw : ∀ w (q' : pullbackSpace (p (σ j)) (s j))
        (hq' : q' ∈ ((B (σ j)).pullback (hs j)).oneSet),
        ((StrongBundle.sigma B).pullback hS).oneVal w = pullbackSigmaIncl j q' →
        (sigmaOneEquiv (fun j => (B (σ j)).pullback (hs j)) ∘
          oneRestrict _ _ pullbackSigmaProj hm) w =
            ⟨j, ((B (σ j)).pullback (hs j)).oneMk q' hq'⟩ := by
      intro w q' hq' hw
      refine sigmaOneEquiv_apply_of_eq _ ?_
      rw [oneVal_oneRestrict, hw]
      rfl
    have hmaps : MapsTo (sigmaOneEquiv (fun j => (B (σ j)).pullback (hs j)) ∘
        oneRestrict _ _ pullbackSigmaProj hm) ((pullbackProj (sigmaBundleProj p) (Sigma.map σ s) ∘
          ((StrongBundle.sigma B).pullback hS).oneVal) ⁻¹' range (Sigma.mk j))
        (range (Sigma.mk j)) := by
      intro w hw
      obtain ⟨q', hq', hwq⟩ := hdesc w hw
      exact ⟨_, (hFw w q' hq' hwq).symm⟩
    refine (MPolyfold.isScSmoothOn_sigma_iff_of_mapsTo
      (fun j => ((B (σ j)).pullback (hs j)).toMPolyfold1) u₀ hmaps).2 ?_
    set z₀ : Z j := (((B (σ j)).pullback (hs j)).oneVal u₀ : Z j × Y (σ j)).1
    set y₀ : (B (σ j)).One := (B (σ j)).pullbackProj'One (hs j) u₀
    refine (B (σ j)).isScSmoothOn_to_pullback_one (hs j) ?_ ?_
    · refine (MPolyfold.IsScSmoothOn.comp (MPolyfold.isScSmoothOn_sigmaProj PZ j z₀)
        (((StrongBundle.sigma B).pullback hS).isScSmoothMap_proj1.mono hW (subset_univ _))
        fun w hw => hw).congr fun w hw => ?_
      obtain ⟨q', hq', hwq⟩ := hdesc w hw
      change sigmaProj j z₀ (pullbackProj _ _ (((StrongBundle.sigma B).pullback hS).oneVal w)) =
        pullbackProj _ _ (((B (σ j)).pullback (hs j)).oneVal (sigmaProj j u₀
          ((sigmaOneEquiv (fun j => (B (σ j)).pullback (hs j)) ∘
            oneRestrict _ _ pullbackSigmaProj hm) w)))
      rw [hFw w q' hq' hwq, sigmaProj_mk, hwq]
      exact sigmaProj_mk _ _ _
    · have hb0 := (isScSmoothMap_sigmaOneEquiv B).comp
        ((StrongBundle.sigma B).isScSmoothMap_one_pullbackProj' hS)
      have hval : ∀ w (q' : pullbackSpace (p (σ j)) (s j))
          (hq' : q' ∈ ((B (σ j)).pullback (hs j)).oneSet),
          ((StrongBundle.sigma B).pullback hS).oneVal w = pullbackSigmaIncl j q' →
          (sigmaOneEquiv B ∘ (StrongBundle.sigma B).pullbackProj'One hS) w =
            ⟨σ j, (B (σ j)).oneMk q'.1.2
              (((B (σ j)).mem_oneSet_pullback_iff (hs j) q').1 hq')⟩ := by
        intro w q' hq' hwq
        refine sigmaOneEquiv_apply_of_eq B ?_
        change pullbackProj' _ _ (((StrongBundle.sigma B).pullback hS).oneVal w) = _
        rw [hwq]
        rfl
      refine (MPolyfold.IsScSmoothOn.comp
        (MPolyfold.isScSmoothOn_sigmaProj (fun i => (B i).toMPolyfold1) (σ j) y₀)
        (hb0.mono hW (subset_univ _)) ?_).congr fun w hw => ?_
      · intro w hw
        obtain ⟨q', hq', hwq⟩ := hdesc w hw
        exact ⟨_, (hval w q' hq' hwq).symm⟩
      · obtain ⟨q', hq', hwq⟩ := hdesc w hw
        change sigmaProj (σ j) y₀
            ((sigmaOneEquiv B ∘ (StrongBundle.sigma B).pullbackProj'One hS) w) =
          (B (σ j)).pullbackProj'One (hs j) (sigmaProj j u₀
            ((sigmaOneEquiv (fun j => (B (σ j)).pullback (hs j)) ∘
              oneRestrict _ _ pullbackSigmaProj hm) w))
        rw [hval w q' hq' hwq, hFw w q' hq' hwq, sigmaProj_mk, sigmaProj_mk]
        rfl
  refine MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun w _ => ⟨_, ?_, ?_, subset_univ _,
    hpiece _ ((sigmaOneEquiv (fun j => (B (σ j)).pullback (hs j)) ∘
      oneRestrict _ _ pullbackSigmaProj hm) w).2⟩
  · exact isOpen_range_sigmaMk.preimage
      ((continuous_pullbackProj _ _).comp ((StrongBundle.sigma B).pullback hS).continuous_oneVal)
  · exact ⟨(((StrongBundle.sigma B).pullback hS).oneVal w).1.1.2, rfl⟩

/-- `S*W → ⊔ s_j*K_{σ j}` is a strong bundle map covering the identity. -/
theorem isStrongBundleMap_pullbackSigmaProj :
    ((StrongBundle.sigma B).pullback hS).IsStrongBundleMap
      (StrongBundle.sigma fun j => (B (σ j)).pullback (hs j)) id pullbackSigmaProj where
  covers _ := rfl
  fiber_linear x := isLinearMap_of_inverse
    ((isStrongBundleMap_pullbackSigmaEquiv B hs hS).fiberLinearMap x)
    (fun _ => Subtype.ext rfl) (fun _ => Subtype.ext (pullbackSigmaIncl_proj _))
  isScSmoothMap := isScSmoothMap_pullbackSigmaProj B hs hS
  mapsTo_oneSet := mapsTo_oneSet_pullbackSigmaProj B hs hS
  isScSmoothMap_one := isScSmoothMap_one_pullbackSigmaProj B hs hS

/-- **The pull-back of `⊔ K_λ` along `S = Sigma.map σ s` is the disjoint union of the pull-backs
`s_j*K_{σ j}`**, as strong bundles over `⊔ Z_j` (used for §17.7). -/
theorem isStrongBundleIso_pullbackSigma :
    (StrongBundle.sigma fun j => (B (σ j)).pullback (hs j)).IsStrongBundleIso
      ((StrongBundle.sigma B).pullback hS) id pullbackSigmaEquiv id pullbackSigmaProj :=
  ⟨isStrongBundleMap_pullbackSigmaEquiv B hs hS, isStrongBundleMap_pullbackSigmaProj B hs hS,
    fun _ => rfl, pullbackSigmaIncl_proj⟩

variable {X' : Type*} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type*} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] (B' : StrongBundle PX' P')

/-- **Strong bundle maps out of `S*W`** are the families of strong bundle maps out of the
pull-backs `s_j*K_{σ j}` (used for §17.7). -/
theorem isStrongBundleMap_pullbackSigma_iff {f : (Σ j, Z j) → X'}
    {Φ : pullbackSpace (sigmaBundleProj p) (Sigma.map σ s) → Y'} :
    ((StrongBundle.sigma B).pullback hS).IsStrongBundleMap B' f Φ ↔
      ∀ j, ((B (σ j)).pullback (hs j)).IsStrongBundleMap B' (f ∘ Sigma.mk j)
        (Φ ∘ pullbackSigmaIncl j) := by
  refine ⟨fun h j => h.comp (isStrongBundleMap_pullbackSigmaIncl B hs hS j), fun h => ?_⟩
  have h1 := ((isStrongBundleMap_sigma_iff (fun j => (B (σ j)).pullback (hs j)) B'
    (f := f) (Φ := Φ ∘ pullbackSigmaEquiv)).2 h).comp (isStrongBundleMap_pullbackSigmaProj B hs hS)
  have e : (Φ ∘ pullbackSigmaEquiv) ∘ pullbackSigmaProj = Φ :=
    funext fun q => congrArg Φ (pullbackSigmaIncl_proj q)
  rw [e] at h1
  exact h1

/-- **Local sc-diffeomorphisms out of `S*W[0]`** are the families of local sc-diffeomorphisms out
of the `s_j*K_{σ j}[0]` (used for §17.7). -/
theorem isLocalScDiffeo_pullbackSigma_iff {V : Type*} [TopologicalSpace V] [T2Space V]
    [ParacompactSpace V] {Q : MPolyfold V}
    {Φ : pullbackSpace (sigmaBundleProj p) (Sigma.map σ s) → V} :
    ((StrongBundle.sigma B).pullback hS).toMPolyfold0.IsLocalScDiffeo Q Φ ↔
      ∀ j, ((B (σ j)).pullback (hs j)).toMPolyfold0.IsLocalScDiffeo Q
        (Φ ∘ pullbackSigmaIncl j) := by
  have hd : (StrongBundle.sigma fun j => (B (σ j)).pullback (hs j)).toMPolyfold0.IsScDiffeoOn
      ((StrongBundle.sigma B).pullback hS).toMPolyfold0 pullbackSigmaEquiv pullbackSigmaProj
      univ univ :=
    ⟨(isStrongBundleMap_pullbackSigmaEquiv B hs hS).isScSmoothMap,
      (isStrongBundleMap_pullbackSigmaProj B hs hS).isScSmoothMap, mapsTo_univ _ _,
      mapsTo_univ _ _, fun _ _ => rfl, fun q _ => pullbackSigmaIncl_proj q⟩
  have hl : (StrongBundle.sigma fun j => (B (σ j)).pullback (hs j)).toMPolyfold0.IsLocalScDiffeo
      ((StrongBundle.sigma B).pullback hS).toMPolyfold0 pullbackSigmaEquiv :=
    fun x => ⟨univ, univ, _, mem_univ x, hd⟩
  have hl' : ((StrongBundle.sigma B).pullback hS).toMPolyfold0.IsLocalScDiffeo
      (StrongBundle.sigma fun j => (B (σ j)).pullback (hs j)).toMPolyfold0 pullbackSigmaProj :=
    fun x => ⟨univ, univ, _, mem_univ x, hd.symm⟩
  constructor
  · intro hΦ j
    have h1 := hΦ.comp hl
    rw [sigma_toMPolyfold0] at h1
    exact (MPolyfold.isLocalScDiffeo_sigma_iff
      (fun j => ((B (σ j)).pullback (hs j)).toMPolyfold0)).1 h1 j
  · intro h
    have h1 : (StrongBundle.sigma fun j => (B (σ j)).pullback (hs j)).toMPolyfold0.IsLocalScDiffeo
        Q (Φ ∘ pullbackSigmaEquiv) := by
      rw [sigma_toMPolyfold0]
      exact (MPolyfold.isLocalScDiffeo_sigma_iff
        (fun j => ((B (σ j)).pullback (hs j)).toMPolyfold0)).2 h
    have h2 := h1.comp hl'
    have e : (Φ ∘ pullbackSigmaEquiv) ∘ pullbackSigmaProj = Φ :=
      funext fun q => congrArg Φ (pullbackSigmaIncl_proj q)
    rwa [e] at h2

/-! #### Maps between pull-backs of disjoint unions -/

variable {ι' : Type*} {X'' : ι' → Type u₁} [∀ i, TopologicalSpace (X'' i)] [∀ i, T2Space (X'' i)]
  [∀ i, ParacompactSpace (X'' i)] {PX'' : ∀ i, MPolyfold (X'' i)}
  {Y'' : ι' → Type v₁} [∀ i, TopologicalSpace (Y'' i)] [∀ i, T2Space (Y'' i)]
  [∀ i, ParacompactSpace (Y'' i)] {p'' : ∀ i, Y'' i → X'' i}
  [∀ i x, AddCommGroup (p'' i ⁻¹' {x})] [∀ i x, Module ℝ (p'' i ⁻¹' {x})]
  (B'' : ∀ i, StrongBundle (PX'' i) (p'' i))
  {κ' : Type*} {Z' : κ' → Type w₁} [∀ j, TopologicalSpace (Z' j)] [∀ j, T2Space (Z' j)]
  [∀ j, ParacompactSpace (Z' j)] {PZ' : ∀ j, MPolyfold (Z' j)}
  {σ' : κ' → ι'} {s' : ∀ j, Z' j → X'' (σ' j)}
  [∀ j, ParacompactSpace (pullbackSpace (p'' (σ' j)) (s' j))]
  [ParacompactSpace (pullbackSpace (sigmaBundleProj p'') (Sigma.map σ' s'))]
  (hs' : ∀ j, (PZ' j).IsScSmoothMap (PX'' (σ' j)) (s' j))
  (hS' : (MPolyfold.sigma PZ').IsScSmoothMap (MPolyfold.sigma PX'') (Sigma.map σ' s'))

/-- **Maps between pull-backs of disjoint unions**: `pullbackSigmaMap Φ` is a strong bundle map
covering `Sigma.map τ g` if every `Φ_j` is one covering `g_j` (used for §17.7). -/
theorem isStrongBundleMap_pullbackSigmaMap {τ : κ → κ'} {g : ∀ j, Z j → Z' (τ j)}
    {Φ : ∀ j, pullbackSpace (p (σ j)) (s j) → pullbackSpace (p'' (σ' (τ j))) (s' (τ j))}
    (h : ∀ j, ((B (σ j)).pullback (hs j)).IsStrongBundleMap
      ((B'' (σ' (τ j))).pullback (hs' (τ j))) (g j) (Φ j)) :
    ((StrongBundle.sigma B).pullback hS).IsStrongBundleMap ((StrongBundle.sigma B'').pullback hS')
      (Sigma.map τ g) (pullbackSigmaMap Φ) :=
  (isStrongBundleMap_pullbackSigmaEquiv B'' hs' hS').comp
    ((isStrongBundleMap_sigmaMap (fun j => (B (σ j)).pullback (hs j))
      (fun j => (B'' (σ' j)).pullback (hs' j)) h).comp
      (isStrongBundleMap_pullbackSigmaProj B hs hS))

/-- **Local strong bundle isomorphisms between pull-backs of disjoint unions** (the condition
`isLocalStrongBundleIso_mor` of Chapter 10's `IsStrongBundleEquivalence`, used for §17.7): if every
`Φ_j` is a local strong bundle isomorphism around every point, so is `pullbackSigmaMap Φ`. -/
theorem isStrongBundleIsoOn_pullbackSigmaMap {τ : κ → κ'} {g : ∀ j, Z j → Z' (τ j)}
    {Φ : ∀ j, pullbackSpace (p (σ j)) (s j) → pullbackSpace (p'' (σ' (τ j))) (s' (τ j))}
    (h : ∀ j, ((B (σ j)).pullback (hs j)).IsStrongBundleMap
      ((B'' (σ' (τ j))).pullback (hs' (τ j))) (g j) (Φ j))
    (hiso : ∀ j (z : Z j), ∃ (U : Set (Z j)) (U' : Set (Z' (τ j))), z ∈ U ∧
      ((B (σ j)).pullback (hs j)).IsStrongBundleIsoOn ((B'' (σ' (τ j))).pullback (hs' (τ j)))
        (h j) U U') :
    ∀ z : Σ j, Z j, ∃ (U : Set (Σ j, Z j)) (U' : Set (Σ j, Z' j)), z ∈ U ∧
      ((StrongBundle.sigma B).pullback hS).IsStrongBundleIsoOn
        ((StrongBundle.sigma B'').pullback hS')
        (isStrongBundleMap_pullbackSigmaMap B hs hS B'' hs' hS' h) U U' := by
  intro z
  obtain ⟨U, U', hz, hi⟩ := isStrongBundleIsoOn_sigmaMap (fun j => (B (σ j)).pullback (hs j))
    (fun j => (B'' (σ' j)).pullback (hs' j)) h hiso z
  have hUo : IsOpen U := by
    obtain ⟨_, hg⟩ := hi.isScDiffeoOn_base
    exact hg.isOpen_source
  have hU'o : IsOpen U' := by
    obtain ⟨_, hg⟩ := hi.isScDiffeoOn_base
    exact hg.isOpen_target
  have e₁ := (isStrongBundleIsoOn_univ_of_inverse (isStrongBundleMap_pullbackSigmaProj B hs hS)
    (isStrongBundleMap_pullbackSigmaEquiv B hs hS) MPolyfold.isScSmoothMap_id
    MPolyfold.isScSmoothMap_id (fun _ => rfl) (fun _ => rfl) pullbackSigmaIncl_proj
    (fun _ => rfl)).restrict (MPolyfold.isScDiffeoOn_id isOpen_univ) hUo (subset_univ U)
  have e₂ := (isStrongBundleIsoOn_univ_of_inverse (isStrongBundleMap_pullbackSigmaEquiv B'' hs' hS')
    (isStrongBundleMap_pullbackSigmaProj B'' hs' hS') MPolyfold.isScSmoothMap_id
    MPolyfold.isScSmoothMap_id (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    pullbackSigmaIncl_proj).restrict (MPolyfold.isScDiffeoOn_id isOpen_univ) hU'o (subset_univ U')
  rw [show univ ∩ id ⁻¹' U = U from univ_inter _] at e₁
  rw [show univ ∩ id ⁻¹' U' = U' from univ_inter _] at e₂
  exact ⟨U, U', hz, e₂.comp (hi.comp e₁)⟩

end StrongBundle

end Pullback

end Polyfold
