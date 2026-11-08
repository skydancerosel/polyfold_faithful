import Polyfold.Chapter7.LocalDiffeo
import Polyfold.Chapter7.Discrete

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2017, arXiv 1707.08941), Part II,
Chapter 8: infrastructure for **Proposition 8.3** (p. 281), the **disjoint union of M-polyfolds**.
Numbers and pages are the 2017 text's (there is no 2014 preprint of Part II).

# Disjoint unions of M-polyfolds

## The text, paraphrased

(Proposition 8.3, p. 281) From open sets `U(y)`, `y ∈ D`, the proof forms an ep-groupoid whose
object set is the disjoint union `Y = ⊔_{y ∈ D} U(y)` and whose morphism set is the disjoint union
`𝐘 = ⊔_{(y, y') ∈ D × D} mor(y, y') × U(y)`; of the latter it says that it possesses a natural
M-polyfold structure.  The text does not describe that structure further.

## What is formalized

* **Paracompactness**: the instance `Polyfold.paracompactSpace_sigma` (a disjoint union of
  paracompact spaces is paracompact, for any index type); Hausdorffness is Mathlib's
  `Sigma.t2Space`.
* **Charts**: `MChart.pushforward` (a chart pushed forward along an open embedding), with
  `MChart.pushforward_overlap`, `MChart.pushforward_transition`,
  `MChart.compatible_pushforward_iff`, and `MChart.compatible_of_disjoint` (charts with disjoint
  domains are compatible: both transition maps live on `∅`, `isScSmoothRetractMap_empty`).
* **The M-polyfold `Σ i, X i`**: `MPolyfold.sigmaChart i φ` (a chart of `X i` as a chart of the
  union), `compatible_sigmaChart_of_ne`, `MPolyfold.sigma P` (atlas: the charts of all `X i`,
  transported), `isChart_sigmaChart_iff`.
* **The summands**: `sigmaProj i x₀` (the projection onto `X i`, junk value `x₀` off it),
  `isScSmoothMap_sigmaMk`, `isScSmoothOn_sigmaProj`, `isScDiffeoOn_sigmaMk` (`X i` is
  sc-diffeomorphic to the open piece `range (Sigma.mk i)`), `isLocalScDiffeo_sigmaMk`.
* **Levels, degeneracy, tameness**: `mem_levelSet_sigma_iff`, `levelSet_sigma`
  (`(Σ X)_m = ⊔ (X i)_m`), `mem_smoothSet_sigma_iff`, `degIndex_sigma`
  (`d_{Σ X}(i, x) = d_{X i}(x)`), `mem_boundary_sigma_iff`, `isTame_sigma_iff`.
* **Maps out of `Σ i, X i`**: `continuousOn_sigma_iff`, `isScSmoothOn_sigma_iff` (on an open
  set), `isScSmoothMap_sigma_iff`, `isLocalScDiffeo_sigma_iff`.
* **Maps into `Σ i, X i`**: `isScSmoothOn_sigmaMk_comp_iff`, `isScSmoothMap_sigmaMk_comp_iff`,
  `isScSmoothOn_sigma_iff_of_mapsTo` (a map landing in one summand on an open set),
  `isScSmoothOn_into_sigma_iff` (sc-smoothness piece by piece).
* **Maps between unions**: `isScSmoothMap_sigmaMap_iff`, `isScSmoothMap_sigmaMap`,
  `isLocalScDiffeo_sigmaMap` (for `Sigma.map σ g`, `g i : X i → Y (σ i)`), and
  `isScDiffeoOn_sigmaMap` (summand-wise sc-diffeomorphisms, `σ = id`).
* **Products**: `isScSmoothMap_sigmaMk_prod`, `isScDiffeoOn_sigmaProdDistrib` and
  `isLocalScDiffeo_sigmaProdDistrib` (`(Σ i, X i) × Z ≅ Σ i, (X i × Z)`, Mathlib's
  `Equiv.sigmaProdDistrib`), `isScDiffeoOn_prodSigmaDistrib` (`Z × Σ i, X i ≅ Σ i, (Z × X i)`),
  and `isScDiffeoOn_prod_discrete_sigma` (`G × X ≅ Σ (_ : G), X` for a discrete `G`, with
  Chapter 7's `discretePolyfold`).

## What the text leaves implicit, and the choices made

* "The natural M-polyfold structure" is read as the one whose charts are the charts of the
  summands, transported along the open embeddings `Sigma.mk i`.  Charts of different summands
  have disjoint domains; Definition 2.11's compatibility then asks for sc-smoothness of maps
  between empty retracts, which holds (`compatible_of_disjoint`), so no condition is added.
* The index type is arbitrary (no finiteness): paracompactness of the union is proved directly
  from that of the summands (refine the cover summand by summand), without metrizability.
* The transported chart `f(a) ↦ φ(a)` is extended by `0` off `f(A)` (`Function.extend`), so no
  summand needs to be nonempty.  The projection onto `X i`, needed as a total inverse of
  `Sigma.mk i` in `IsScDiffeoOn`, takes a junk value `x₀ : X i`.
* `mor(y, y') × U(y)`: pieces that are products are covered by taking the family
  `fun i => (P i).prod (S i)`; the paracompactness of the products is an instance argument, as in
  Part I's `MPolyfold.prod` (it holds by `MPolyfold.paracompactSpace_prod`).
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u v w uι

/-! ### Paracompactness of disjoint unions -/

section Paracompact

variable {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]

/-- **A disjoint union of paracompact spaces is paracompact**: refine the cover on each summand
and take the union of the refinements. -/
instance paracompactSpace_sigma [∀ i, ParacompactSpace (X i)] :
    ParacompactSpace (Σ i, X i) where
  locallyFinite_refinement α s hso hsc := by
    have key : ∀ i, ∃ t : α → Set (X i), (∀ a, IsOpen (t a)) ∧ ⋃ a, t a = univ ∧
        LocallyFinite t ∧ ∀ a, t a ⊆ Sigma.mk i ⁻¹' s a := fun i =>
      precise_refinement (fun a => Sigma.mk i ⁻¹' s a)
        (fun a => (hso a).preimage continuous_sigmaMk) (by
          rw [← preimage_iUnion, hsc, preimage_univ])
    choose t hto htc htlf hts using key
    refine ⟨α, fun a => ⋃ i, Sigma.mk i '' t i a, fun a => isOpen_iUnion fun i =>
      IsOpenEmbedding.sigmaMk.isOpenMap _ (hto i a), ?_, ?_, ?_⟩
    · refine eq_univ_of_forall fun p => ?_
      obtain ⟨i, x⟩ := p
      have hx : x ∈ ⋃ a, t i a := by rw [htc i]; exact mem_univ x
      obtain ⟨a, ha⟩ := mem_iUnion.1 hx
      exact mem_iUnion.2 ⟨a, mem_iUnion.2 ⟨i, x, ha, rfl⟩⟩
    · rintro ⟨i, x⟩
      obtain ⟨W, hW, hfin⟩ := htlf i x
      refine ⟨Sigma.mk i '' W, ?_, hfin.subset ?_⟩
      · rw [Sigma.nhds_mk]
        exact image_mem_map hW
      · rintro a ⟨p, hp1, hp2⟩
        obtain ⟨j, y, hy, rfl⟩ : ∃ j, p ∈ Sigma.mk j '' t j a := mem_iUnion.1 hp1
        obtain ⟨w, hw, hwy⟩ := hp2
        obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 hwy
        exact ⟨w, (eq_of_heq h) ▸ hy, hw⟩
    · intro a
      exact ⟨a, iUnion_subset fun i => image_subset_iff.2 (hts i a)⟩

end Paracompact

/-! ### Sc-smoothness on the empty retract -/

/-- Every map is sc-smooth on the empty retract. -/
theorem isScSmoothRetractMap_empty {E : ScBanach} {C : Set (E 0)} {E' : ScBanach}
    {C' O' : Set (E' 0)} (f : E 0 → E' 0) : IsScSmoothRetractMap E C ∅ E' C' O' f :=
  IsScSmoothRetractMap.of_locally (mapsTo_empty _ _) fun x hx => absurd hx (notMem_empty x)

/-! ### Pushing a chart forward along an open embedding -/

namespace MChart

variable {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]

/-- A chart `φ` of `A` **pushed forward along an open embedding** `f : A → B`: the same model,
the map `f(a) ↦ φ(a)` (extended by `0` off `f(A)`), the inverse `f ∘ φ⁻¹`, the domain
`f(dom φ)`. -/
def pushforward (φ : MChart A) {f : A → B} (hf : IsOpenEmbedding f) : MChart B where
  model := φ.model
  toPartialEquiv :=
    { toFun := Function.extend f φ 0
      invFun := f ∘ φ.symm
      source := f '' φ.source
      target := φ.model.O
      map_source' := by
        rintro _ ⟨a, ha, rfl⟩
        rw [hf.injective.extend_apply]
        exact φ.mapsTo_model a ha
      map_target' := fun z hz => ⟨φ.symm z, φ.symm_mapsTo hz, rfl⟩
      left_inv' := by
        rintro _ ⟨a, ha, rfl⟩
        change f (φ.symm (Function.extend f φ 0 (f a))) = f a
        rw [hf.injective.extend_apply, φ.symm_apply_apply ha]
      right_inv' := fun z hz => by
        change Function.extend f φ 0 (f (φ.symm z)) = z
        rw [hf.injective.extend_apply, φ.apply_symm_apply hz] }
  isOpen_source := hf.isOpenMap _ φ.isOpen_source
  target_eq := rfl
  continuousOn_toFun := by
    change ContinuousOn (Function.extend f φ 0) (f '' φ.source)
    rw [hf.isInducing.continuousOn_image_iff, extend_comp hf.injective]
    exact φ.continuousOn_toFun
  continuousOn_invFun := hf.continuous.comp_continuousOn φ.continuousOn_invFun

variable (φ ψ : MChart A) {f : A → B} (hf : IsOpenEmbedding f)

@[simp] lemma pushforward_model : (φ.pushforward hf).model = φ.model := rfl

@[simp] lemma pushforward_source : (φ.pushforward hf).source = f '' φ.source := rfl

@[simp] lemma pushforward_apply (a : A) : φ.pushforward hf (f a) = φ a :=
  hf.injective.extend_apply _ _ a

lemma pushforward_comp : (φ.pushforward hf : B → φ.model.E 0) ∘ f = φ :=
  extend_comp hf.injective _ _

@[simp] lemma pushforward_symm (z : φ.model.E 0) :
    (φ.pushforward hf).symm z = f (φ.symm z) := rfl

lemma pushforward_image (s : Set A) : φ.pushforward hf '' (f '' s) = φ '' s := by
  rw [← image_comp, pushforward_comp]; rfl

/-- The overlap of two pushed-forward charts is the overlap of the charts. -/
lemma pushforward_overlap : (φ.pushforward hf).overlap (ψ.pushforward hf) = φ.overlap ψ := by
  change φ.pushforward hf '' (f '' φ.source ∩ f '' ψ.source) = φ '' (φ.source ∩ ψ.source)
  rw [← image_inter hf.injective, pushforward_image]

/-- The transition map of two pushed-forward charts is that of the charts. -/
lemma pushforward_transition :
    (φ.pushforward hf).transition (ψ.pushforward hf) = φ.transition ψ := by
  change (ψ.pushforward hf : B → ψ.model.E 0) ∘ (f ∘ φ.symm) = ψ ∘ φ.symm
  rw [← Function.comp_assoc, pushforward_comp]; rfl

/-- Pushing forward along the same open embedding preserves and reflects compatibility. -/
theorem compatible_pushforward_iff :
    (φ.pushforward hf).Compatible (ψ.pushforward hf) ↔ φ.Compatible ψ := by
  unfold Compatible
  rw [pushforward_overlap, pushforward_overlap, pushforward_transition, pushforward_transition]
  rfl

/-- **Two charts with disjoint domains are compatible**: both transition maps live on `∅`. -/
theorem compatible_of_disjoint {X : Type*} [TopologicalSpace X] {φ ψ : MChart X}
    (h : Disjoint φ.source ψ.source) : φ.Compatible ψ := by
  have h1 : φ.overlap ψ = ∅ := by rw [overlap, h.inter_eq, image_empty]
  have h2 : ψ.overlap φ = ∅ := by rw [overlap, h.symm.inter_eq, image_empty]
  rw [Compatible, h1, h2]
  exact ⟨isScSmoothRetractMap_empty _, isScSmoothRetractMap_empty _⟩

end MChart

/-! ### The projection onto a summand -/

section Proj

variable {ι : Type*} {X : ι → Type*}

/-- The projection `Σ j, X j → X i` onto the `i`-th summand, with the junk value `x₀` off it. -/
def sigmaProj (i : ι) (x₀ : X i) : (Σ j, X j) → X i :=
  Function.extend (Sigma.mk i) id fun _ => x₀

@[simp] lemma sigmaProj_mk (i : ι) (x₀ : X i) (x : X i) : sigmaProj i x₀ ⟨i, x⟩ = x :=
  sigma_mk_injective.extend_apply _ _ x

lemma sigmaProj_comp_mk (i : ι) (x₀ : X i) : sigmaProj i x₀ ∘ Sigma.mk i = id :=
  extend_comp sigma_mk_injective _ _

lemma mk_sigmaProj {i : ι} (x₀ : X i) {p : Σ j, X j} (hp : p ∈ range (Sigma.mk i)) :
    Sigma.mk i (sigmaProj i x₀ p) = p := by
  obtain ⟨x, rfl⟩ := hp
  rw [sigmaProj_mk]

lemma disjoint_range_sigmaMk {i j : ι} (hij : i ≠ j) :
    Disjoint (range (Sigma.mk i : X i → Σ k, X k)) (range (Sigma.mk j)) :=
  disjoint_left.2 fun _ ⟨_, hx⟩ ⟨_, hy⟩ => hij (congrArg Sigma.fst (hx.trans hy.symm))

lemma sigmaMk_preimage_range_of_ne {i j : ι} (hij : i ≠ j) :
    (Sigma.mk j : X j → Σ k, X k) ⁻¹' range (Sigma.mk i) = ∅ :=
  eq_empty_of_forall_notMem fun _ ⟨_, hx⟩ => hij (congrArg Sigma.fst hx)

end Proj

/-! ### Two general facts on sc-smooth maps -/

namespace MPolyfold

universe u₁ u₂

variable {X₁ : Type u₁} [TopologicalSpace X₁] [T2Space X₁] [ParacompactSpace X₁]
  {P₁ : MPolyfold X₁} {X₂ : Type u₂} [TopologicalSpace X₂] [T2Space X₂] [ParacompactSpace X₂]
  {P₂ : MPolyfold X₂}

/-- Every map is sc-smooth on `∅`. -/
theorem isScSmoothOn_empty (f : X₁ → X₂) : P₁.IsScSmoothOn P₂ f ∅ where
  isOpen := isOpen_empty
  continuousOn := continuousOn_empty f
  smooth φ ψ _ _ V _ hV _ := by
    have : V = ∅ := eq_empty_of_subset_empty fun x hx => (hV hx).1
    subst this
    rw [image_empty]
    exact isScSmoothRetractMap_empty _

/-- An sc-diffeomorphism stays one when the map is changed off `U`. -/
theorem IsScDiffeoOn.congr {f f' : X₁ → X₂} {g : X₂ → X₁} {U : Set X₁} {V : Set X₂}
    (h : P₁.IsScDiffeoOn P₂ f g U V) (hff' : EqOn f f' U) : P₁.IsScDiffeoOn P₂ f' g U V where
  isScSmoothOn := h.isScSmoothOn.congr hff'
  isScSmoothOn_inv := h.isScSmoothOn_inv
  mapsTo x hx := by rw [← hff' hx]; exact h.mapsTo hx
  mapsTo_inv := h.mapsTo_inv
  left_inv x hx := by rw [← hff' hx]; exact h.left_inv x hx
  right_inv y hy := by rw [← hff' (h.mapsTo_inv hy)]; exact h.right_inv y hy

end MPolyfold

/-! ### The M-polyfold `Σ i, X i` -/

namespace MPolyfold

variable {ι : Type uι} {X : ι → Type u} [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)]
  [∀ i, ParacompactSpace (X i)] (P : ∀ i, MPolyfold (X i))

/-- A chart `φ` of `X i` as a chart of `Σ i, X i` (pushed forward along `Sigma.mk i`). -/
abbrev sigmaChart (i : ι) (φ : MChart (X i)) : MChart (Σ i, X i) :=
  φ.pushforward IsOpenEmbedding.sigmaMk

omit [∀ i, T2Space (X i)] [∀ i, ParacompactSpace (X i)] in
lemma sigmaChart_source (i : ι) (φ : MChart (X i)) :
    (sigmaChart i φ).source = Sigma.mk i '' φ.source := rfl

omit [∀ i, T2Space (X i)] [∀ i, ParacompactSpace (X i)] in
lemma sigmaChart_apply (i : ι) (φ : MChart (X i)) (x : X i) :
    sigmaChart i φ ⟨i, x⟩ = φ x :=
  MChart.pushforward_apply φ IsOpenEmbedding.sigmaMk x

omit [∀ i, T2Space (X i)] [∀ i, ParacompactSpace (X i)] in
lemma sigmaChart_symm (i : ι) (φ : MChart (X i)) (z : φ.model.E 0) :
    (sigmaChart i φ).symm z = ⟨i, φ.symm z⟩ := rfl

omit [∀ i, T2Space (X i)] [∀ i, ParacompactSpace (X i)] in
/-- Charts of different summands are compatible (their domains are disjoint). -/
theorem compatible_sigmaChart_of_ne {i j : ι} (hij : i ≠ j) (φ : MChart (X i))
    (ψ : MChart (X j)) : (sigmaChart i φ).Compatible (sigmaChart j ψ) :=
  MChart.compatible_of_disjoint ((disjoint_range_sigmaMk hij).mono (image_subset_range _ _)
    (image_subset_range _ _))

/-- **The M-polyfold structure of a disjoint union** `Σ i, X i` (the "natural M-polyfold
structure" of Proposition 8.3): the charts of every `X i`, pushed forward along `Sigma.mk i`. -/
def sigma : MPolyfold (Σ i, X i) where
  atlas :=
    { charts := {χ | ∃ i, ∃ φ ∈ (P i).atlas.charts, χ = sigmaChart i φ}
      compatible := by
        rintro _ ⟨i, φ, hφ, rfl⟩ _ ⟨j, ψ, hψ, rfl⟩
        by_cases hij : i = j
        · subst hij
          exact (MChart.compatible_pushforward_iff _ _ _).2 ((P i).atlas.compatible φ hφ ψ hψ)
        · exact compatible_sigmaChart_of_ne hij φ ψ
      cover := by
        rintro ⟨i, x⟩
        obtain ⟨φ, hφ, hx⟩ := (P i).atlas.cover x
        exact ⟨sigmaChart i φ, ⟨i, φ, hφ, rfl⟩, x, hx, rfl⟩ }

variable {P}

/-- The charts of `X i` are charts of `Σ i, X i`, and conversely. -/
theorem isChart_sigmaChart_iff {i : ι} {φ : MChart (X i)} :
    (sigma P).IsChart (sigmaChart i φ) ↔ (P i).IsChart φ := by
  constructor
  · intro h ψ hψ
    exact (MChart.compatible_pushforward_iff _ _ _).1 (h _ ⟨i, ψ, hψ, rfl⟩)
  · rintro hφ _ ⟨j, ψ, hψ, rfl⟩
    by_cases hij : i = j
    · subst hij
      exact (MChart.compatible_pushforward_iff _ _ _).2 (hφ ψ hψ)
    · exact compatible_sigmaChart_of_ne hij φ ψ

theorem IsChart.sigmaChart {i : ι} {φ : MChart (X i)} (hφ : (P i).IsChart φ) :
    (sigma P).IsChart (sigmaChart i φ) :=
  isChart_sigmaChart_iff.2 hφ

variable (P)

/-! #### The summands -/

/-- **The inclusion `Sigma.mk i : X i → Σ i, X i` is sc-smooth**: in the charts `φ` and
`sigmaChart i φ` it is the identity of `O`. -/
theorem isScSmoothMap_sigmaMk (i : ι) : (P i).IsScSmoothMap (sigma P) (Sigma.mk i) := by
  refine IsScSmoothOn.of_exists_charts isOpen_univ continuous_sigmaMk.continuousOn fun x _ => ?_
  obtain ⟨φ, hφ, hx⟩ := (P i).exists_isChart_mem_source x
  refine ⟨φ, sigmaChart i φ, φ.source, hφ, hφ.sigmaChart, φ.isOpen_source, hx,
    fun y hy => ⟨mem_univ y, hy⟩, fun y hy => ⟨y, hy, rfl⟩, ?_⟩
  rw [φ.image_source]
  refine (isScSmoothRetractMap_id φ.model.O).congr fun z hz => ?_
  change z = sigmaChart i φ ⟨i, φ.symm z⟩
  rw [sigmaChart_apply, φ.apply_symm_apply hz]

variable {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}

omit [∀ i, T2Space (X i)] [∀ i, ParacompactSpace (X i)] [T2Space Y] [ParacompactSpace Y] in
/-- Continuity on an open subset of `Σ i, X i` is continuity on each summand. -/
theorem continuousOn_sigma_iff {f : (Σ i, X i) → Y} {U : Set (Σ i, X i)} (hU : IsOpen U) :
    ContinuousOn f U ↔ ∀ i, ContinuousOn (f ∘ Sigma.mk i) (Sigma.mk i ⁻¹' U) := by
  refine ⟨fun h i => h.comp continuous_sigmaMk.continuousOn fun _ hx => hx, fun h => ?_⟩
  rintro ⟨i, x⟩ hp
  have hU' : IsOpen (Sigma.mk i ⁻¹' U) := hU.preimage continuous_sigmaMk
  have : ContinuousAt (f ∘ Sigma.mk i) x := (h i).continuousAt (hU'.mem_nhds hp)
  exact ((IsEmbedding.sigmaMk.isInducing.continuousAt_iff'
    (isOpen_range_sigmaMk.mem_nhds (mem_range_self x))).1 this).continuousWithinAt

/-- **Maps out of `Σ i, X i`**: `f` is sc-smooth on the open `U` if and only if every
`f ∘ Sigma.mk i` is sc-smooth on `(Sigma.mk i)⁻¹(U)`. -/
theorem isScSmoothOn_sigma_iff {f : (Σ i, X i) → Y} {U : Set (Σ i, X i)} (hU : IsOpen U) :
    (sigma P).IsScSmoothOn Q f U ↔
      ∀ i, (P i).IsScSmoothOn Q (f ∘ Sigma.mk i) (Sigma.mk i ⁻¹' U) := by
  constructor
  · intro hf i
    exact IsScSmoothOn.comp hf ((isScSmoothMap_sigmaMk P i).mono
      (hU.preimage continuous_sigmaMk) (subset_univ _)) fun _ hx => hx
  · intro hf
    refine IsScSmoothOn.of_exists_charts hU
      ((continuousOn_sigma_iff hU).2 fun i => (hf i).continuousOn) ?_
    rintro ⟨i, x⟩ hp
    obtain ⟨φ, hφ, hx⟩ := (P i).exists_isChart_mem_source x
    obtain ⟨ψ, hψ, hfx⟩ := Q.exists_isChart_mem_source (f ⟨i, x⟩)
    set V₀ := (Sigma.mk i ⁻¹' U ∩ φ.source) ∩ (f ∘ Sigma.mk i) ⁻¹' ψ.source with hV₀
    have hV₀o : IsOpen V₀ :=
      ((hf i).continuousOn.mono inter_subset_left).isOpen_inter_preimage
        ((hU.preimage continuous_sigmaMk).inter φ.isOpen_source) ψ.isOpen_source
    refine ⟨sigmaChart i φ, ψ, Sigma.mk i '' V₀, hφ.sigmaChart, hψ,
      IsOpenEmbedding.sigmaMk.isOpenMap _ hV₀o, ⟨x, ⟨⟨hp, hx⟩, hfx⟩, rfl⟩, ?_, ?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨hy.1.1, y, hy.1.2, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact hy.2
    · -- in the charts, `ψ ∘ f ∘ (sigmaChart i φ)⁻¹ = ψ ∘ (f ∘ Sigma.mk i) ∘ φ⁻¹`
      rw [MChart.pushforward_image]
      exact (hf i).smooth φ ψ hφ hψ V₀ hV₀o (fun y hy => hy.1) fun y hy => hy.2

/-- **Sc-smooth maps out of `Σ i, X i`** are the families of sc-smooth maps out of the `X i`. -/
theorem isScSmoothMap_sigma_iff {f : (Σ i, X i) → Y} :
    (sigma P).IsScSmoothMap Q f ↔ ∀ i, (P i).IsScSmoothMap Q (f ∘ Sigma.mk i) := by
  unfold IsScSmoothMap
  rw [isScSmoothOn_sigma_iff P isOpen_univ]
  simp only [preimage_univ]

/-- The projection onto the `i`-th summand is sc-smooth on that summand. -/
theorem isScSmoothOn_sigmaProj (i : ι) (x₀ : X i) :
    (sigma P).IsScSmoothOn (P i) (sigmaProj i x₀) (range (Sigma.mk i)) := by
  rw [isScSmoothOn_sigma_iff P isOpen_range_sigmaMk]
  intro j
  by_cases hji : j = i
  · subst hji
    rw [preimage_range, sigmaProj_comp_mk]
    exact isScSmoothMap_id
  · rw [sigmaMk_preimage_range_of_ne (Ne.symm hji)]
    exact isScSmoothOn_empty _

/-- **`X i` is sc-diffeomorphic to the open piece `range (Sigma.mk i)`**, with the inverse
`sigmaProj i x₀`. -/
theorem isScDiffeoOn_sigmaMk (i : ι) (x₀ : X i) :
    (P i).IsScDiffeoOn (sigma P) (Sigma.mk i) (sigmaProj i x₀) univ (range (Sigma.mk i)) where
  isScSmoothOn := isScSmoothMap_sigmaMk P i
  isScSmoothOn_inv := isScSmoothOn_sigmaProj P i x₀
  mapsTo x _ := mem_range_self x
  mapsTo_inv _ _ := mem_univ _
  left_inv x _ := sigmaProj_mk i x₀ x
  right_inv _ hp := mk_sigmaProj x₀ hp

/-- `Sigma.mk i` is a local sc-diffeomorphism. -/
theorem isLocalScDiffeo_sigmaMk (i : ι) : (P i).IsLocalScDiffeo (sigma P) (Sigma.mk i) :=
  fun x => ⟨univ, _, _, mem_univ x, isScDiffeoOn_sigmaMk P i x⟩

/-! #### Levels, degeneracy index, tameness -/

theorem mem_levelSet_sigma_iff {i : ι} (x : X i) (m : ℕ) :
    (⟨i, x⟩ : Σ i, X i) ∈ (sigma P).levelSet m ↔ x ∈ (P i).levelSet m :=
  (isLocalScDiffeo_sigmaMk P i).mem_levelSet_iff x m

/-- The levels of `Σ i, X i` are the disjoint unions of the levels of the `X i`. -/
theorem levelSet_sigma (m : ℕ) :
    (sigma P).levelSet m = ⋃ i, Sigma.mk i '' (P i).levelSet m := by
  ext ⟨i, x⟩
  rw [mem_levelSet_sigma_iff]
  constructor
  · intro h
    exact mem_iUnion.2 ⟨i, x, h, rfl⟩
  · intro h
    obtain ⟨j, y, hy, hyx⟩ := mem_iUnion.1 h
    obtain ⟨rfl, h'⟩ := Sigma.mk.inj_iff.1 hyx
    exact (eq_of_heq h') ▸ hy

theorem mem_smoothSet_sigma_iff {i : ι} (x : X i) :
    (⟨i, x⟩ : Σ i, X i) ∈ (sigma P).smoothSet ↔ x ∈ (P i).smoothSet :=
  (isLocalScDiffeo_sigmaMk P i).mem_smoothSet_iff x

/-- `d_{Σ X}(i, x) = d_{X i}(x)`. -/
theorem degIndex_sigma {i : ι} (x : X i) :
    (sigma P).degIndex ⟨i, x⟩ = (P i).degIndex x :=
  (isLocalScDiffeo_sigmaMk P i).degIndex_eq x

theorem mem_boundary_sigma_iff {i : ι} (x : X i) :
    (⟨i, x⟩ : Σ i, X i) ∈ (sigma P).boundary ↔ x ∈ (P i).boundary :=
  (isLocalScDiffeo_sigmaMk P i).mem_boundary_iff x

/-- `Σ i, X i` is tame if and only if every `X i` is. -/
theorem isTame_sigma_iff : (sigma P).IsTame ↔ ∀ i, (P i).IsTame := by
  refine ⟨fun h i => (isLocalScDiffeo_sigmaMk P i).isTame h, fun h => ?_⟩
  refine isTame_of_forall_exists_chart _ ?_
  rintro ⟨i, x⟩
  obtain ⟨φ, hφ, hx, ht⟩ := IsTame.exists_chart (P i) (h i) x
  exact ⟨sigmaChart i φ, hφ.sigmaChart, ⟨x, hx, rfl⟩, ht⟩

/-! #### Local sc-diffeomorphisms out of `Σ i, X i` -/

/-- **Local sc-diffeomorphisms out of `Σ i, X i`**: `f` is one if and only if every
`f ∘ Sigma.mk i` is. -/
theorem isLocalScDiffeo_sigma_iff {f : (Σ i, X i) → Y} :
    (sigma P).IsLocalScDiffeo Q f ↔ ∀ i, (P i).IsLocalScDiffeo Q (f ∘ Sigma.mk i) := by
  refine ⟨fun hf i => hf.comp (isLocalScDiffeo_sigmaMk P i), fun hf => ?_⟩
  rintro ⟨i, x⟩
  obtain ⟨U, V, g, hx, hd⟩ := hf i x
  have e := ((isScDiffeoOn_sigmaMk P i x).restrict hd.isOpen_source (subset_univ U)).symm
  refine ⟨range (Sigma.mk i) ∩ sigmaProj i x ⁻¹' U, V, Sigma.mk i ∘ g,
    ⟨mem_range_self x, by rwa [mem_preimage, sigmaProj_mk]⟩,
    (hd.comp e).congr fun p hp => ?_⟩
  change f (Sigma.mk i (sigmaProj i x p)) = f p
  rw [mk_sigmaProj x hp.1]

/-! #### Maps into `Σ i, X i` -/

/-- **Maps into one summand**: `Sigma.mk i ∘ g` is sc-smooth on `U` if and only if `g` is. -/
theorem isScSmoothOn_sigmaMk_comp_iff {i : ι} {g : Y → X i} {U : Set Y} :
    Q.IsScSmoothOn (sigma P) (Sigma.mk i ∘ g) U ↔ Q.IsScSmoothOn (P i) g U := by
  refine ⟨fun hg => ?_, fun hg => IsScSmoothOn.comp (isScSmoothMap_sigmaMk P i) hg
    (mapsTo_univ _ _)⟩
  refine IsScSmoothOn.of_locally hg.isOpen fun y hy => ⟨U, hg.isOpen, hy, subset_rfl, ?_⟩
  have := IsScSmoothOn.comp (isScSmoothOn_sigmaProj P i (g y)) hg fun z _ => mem_range_self _
  rwa [← Function.comp_assoc, sigmaProj_comp_mk, Function.id_comp] at this

theorem isScSmoothMap_sigmaMk_comp_iff {i : ι} {g : Y → X i} :
    Q.IsScSmoothMap (sigma P) (Sigma.mk i ∘ g) ↔ Q.IsScSmoothMap (P i) g :=
  isScSmoothOn_sigmaMk_comp_iff P

/-- **A map landing in one summand** on `U` is sc-smooth on `U` if and only if its projection to
that summand is. -/
theorem isScSmoothOn_sigma_iff_of_mapsTo {f : Y → Σ i, X i} {U : Set Y} {i : ι} (x₀ : X i)
    (hfU : MapsTo f U (range (Sigma.mk i))) :
    Q.IsScSmoothOn (sigma P) f U ↔ Q.IsScSmoothOn (P i) (sigmaProj i x₀ ∘ f) U := by
  refine ⟨fun hf => IsScSmoothOn.comp (isScSmoothOn_sigmaProj P i x₀) hf hfU, fun hf => ?_⟩
  refine ((isScSmoothOn_sigmaMk_comp_iff P).2 hf).congr fun y hy => ?_
  exact mk_sigmaProj x₀ (hfU hy)

/-- **Maps into `Σ i, X i` are sc-smooth piece by piece**: `f` is sc-smooth on `U` if and only if
`U` is open, `f` is continuous on `U`, and on each open `U ∩ f⁻¹(range (Sigma.mk i))` the
projection of `f` to `X i` is sc-smooth. -/
theorem isScSmoothOn_into_sigma_iff {f : Y → Σ i, X i} {U : Set Y} :
    Q.IsScSmoothOn (sigma P) f U ↔ IsOpen U ∧ ContinuousOn f U ∧
      ∀ i (x₀ : X i),
        Q.IsScSmoothOn (P i) (sigmaProj i x₀ ∘ f) (U ∩ f ⁻¹' range (Sigma.mk i)) := by
  constructor
  · intro hf
    refine ⟨hf.isOpen, hf.continuousOn, fun i x₀ => ?_⟩
    have hW : IsOpen (U ∩ f ⁻¹' range (Sigma.mk i)) :=
      hf.continuousOn.isOpen_inter_preimage hf.isOpen isOpen_range_sigmaMk
    exact (isScSmoothOn_sigma_iff_of_mapsTo P x₀ fun _ hy => hy.2).1
      (hf.mono hW inter_subset_left)
  · rintro ⟨hU, hcont, h⟩
    refine IsScSmoothOn.of_locally hU fun y hy => ?_
    rcases hp : f y with ⟨i, x⟩
    have hW : IsOpen (U ∩ f ⁻¹' range (Sigma.mk i)) :=
      hcont.isOpen_inter_preimage hU isOpen_range_sigmaMk
    exact ⟨_, hW, ⟨hy, x, hp.symm⟩, inter_subset_left,
      (isScSmoothOn_sigma_iff_of_mapsTo P x fun _ hz => hz.2).2 (h i x)⟩

/-! #### Maps between disjoint unions -/

section SigmaMap

variable {κ : Type*} {Y' : κ → Type v} [∀ k, TopologicalSpace (Y' k)] [∀ k, T2Space (Y' k)]
  [∀ k, ParacompactSpace (Y' k)] {R : ∀ k, MPolyfold (Y' k)}

/-- **Maps between disjoint unions**: `Sigma.map σ g` (`g i : X i → Y (σ i)`) is sc-smooth if
and only if every `g i` is. -/
theorem isScSmoothMap_sigmaMap_iff {σ : ι → κ} {g : ∀ i, X i → Y' (σ i)} :
    (sigma P).IsScSmoothMap (sigma R) (Sigma.map σ g) ↔
      ∀ i, (P i).IsScSmoothMap (R (σ i)) (g i) := by
  rw [isScSmoothMap_sigma_iff P]
  exact forall_congr' fun i => isScSmoothMap_sigmaMk_comp_iff R (i := σ i) (g := g i)

theorem isScSmoothMap_sigmaMap {σ : ι → κ} {g : ∀ i, X i → Y' (σ i)}
    (hg : ∀ i, (P i).IsScSmoothMap (R (σ i)) (g i)) :
    (sigma P).IsScSmoothMap (sigma R) (Sigma.map σ g) :=
  (isScSmoothMap_sigmaMap_iff P).2 hg

/-- `Sigma.map σ g` is a local sc-diffeomorphism if every `g i` is. -/
theorem isLocalScDiffeo_sigmaMap {σ : ι → κ} {g : ∀ i, X i → Y' (σ i)}
    (hg : ∀ i, (P i).IsLocalScDiffeo (R (σ i)) (g i)) :
    (sigma P).IsLocalScDiffeo (sigma R) (Sigma.map σ g) :=
  (isLocalScDiffeo_sigma_iff P).2 fun i =>
    (isLocalScDiffeo_sigmaMk R (σ i)).comp (f := g i) (hg i)

end SigmaMap

/-- **Summand-wise sc-diffeomorphisms** `g i : X i → Y i` (inverses `h i`) give an
sc-diffeomorphism `Sigma.map id g` of the disjoint unions. -/
theorem isScDiffeoOn_sigmaMap {Y' : ι → Type v} [∀ i, TopologicalSpace (Y' i)]
    [∀ i, T2Space (Y' i)] [∀ i, ParacompactSpace (Y' i)] (R : ∀ i, MPolyfold (Y' i))
    {g : ∀ i, X i → Y' i} {h : ∀ i, Y' i → X i}
    (hg : ∀ i, (P i).IsScDiffeoOn (R i) (g i) (h i) univ univ) :
    (sigma P).IsScDiffeoOn (sigma R) (Sigma.map id g) (Sigma.map id h) univ univ where
  isScSmoothOn := isScSmoothMap_sigmaMap P fun i => (hg i).isScSmoothOn
  isScSmoothOn_inv := isScSmoothMap_sigmaMap R fun i => (hg i).isScSmoothOn_inv
  mapsTo _ _ := mem_univ _
  mapsTo_inv _ _ := mem_univ _
  left_inv := by
    rintro ⟨i, x⟩ -
    change (⟨i, h i (g i x)⟩ : Σ i, X i) = ⟨i, x⟩
    rw [(hg i).left_inv x (mem_univ x)]
  right_inv := by
    rintro ⟨i, y⟩ -
    change (⟨i, g i (h i y)⟩ : Σ i, Y' i) = ⟨i, y⟩
    rw [(hg i).right_inv y (mem_univ y)]

/-! #### Products -/

section Prod

variable {Z : Type w} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] (S : MPolyfold Z)

section Right

variable [ParacompactSpace ((Σ i, X i) × Z)] [∀ i, ParacompactSpace (X i × Z)]

/-- The inclusion `(x, z) ↦ ((i, x), z)` of `X i × Z` into `(Σ i, X i) × Z` is sc-smooth. -/
theorem isScSmoothMap_sigmaMk_prod (i : ι) :
    ((P i).prod S).IsScSmoothMap ((sigma P).prod S) fun q : X i × Z => (⟨i, q.1⟩, q.2) :=
  IsScSmoothOn.prodMk ((isScSmoothMap_sigmaMk P i).comp (isScSmoothMap_fst (P i) S))
    (isScSmoothMap_snd (P i) S)

/-- **`(Σ i, X i) × Z` and `Σ i, (X i × Z)` are sc-diffeomorphic** (Mathlib's
`Equiv.sigmaProdDistrib`), with the product M-polyfold structures. -/
theorem isScDiffeoOn_sigmaProdDistrib :
    ((sigma P).prod S).IsScDiffeoOn (sigma fun i => (P i).prod S)
      (Equiv.sigmaProdDistrib X Z) (Equiv.sigmaProdDistrib X Z).symm univ univ where
  isScSmoothOn := by
    -- on the open piece `range (Sigma.mk i) × Z` the map is `Sigma.mk i ∘ (sigmaProj i x × id)`
    refine IsScSmoothOn.of_locally isOpen_univ ?_
    rintro ⟨⟨i, x⟩, z⟩ -
    have hWo : IsOpen (range (Sigma.mk i) ×ˢ univ : Set ((Σ i, X i) × Z)) :=
      isOpen_range_sigmaMk.prod isOpen_univ
    refine ⟨_, hWo, ⟨mem_range_self x, mem_univ z⟩, subset_univ _, ?_⟩
    have h1 : ((sigma P).prod S).IsScSmoothOn ((P i).prod S)
        (fun q => (sigmaProj i x q.1, q.2)) (range (Sigma.mk i) ×ˢ univ) :=
      IsScSmoothOn.prodMk (IsScSmoothOn.comp (isScSmoothOn_sigmaProj P i x)
        ((isScSmoothMap_fst (sigma P) S).mono hWo (subset_univ _)) fun q hq => hq.1)
        ((isScSmoothMap_snd (sigma P) S).mono hWo (subset_univ _))
    refine (IsScSmoothOn.comp (isScSmoothMap_sigmaMk (fun i => (P i).prod S) i) h1
      (mapsTo_univ _ _)).congr ?_
    rintro ⟨q₁, q₂⟩ ⟨⟨y, rfl⟩, -⟩
    change Sigma.mk i (sigmaProj i x ⟨i, y⟩, q₂) = (⟨i, (y, q₂)⟩ : Σ i, X i × Z)
    rw [sigmaProj_mk]
  isScSmoothOn_inv :=
    (isScSmoothMap_sigma_iff (fun i => (P i).prod S)).2 fun i =>
      isScSmoothMap_sigmaMk_prod P S i
  mapsTo _ _ := mem_univ _
  mapsTo_inv _ _ := mem_univ _
  left_inv p _ := (Equiv.sigmaProdDistrib X Z).symm_apply_apply p
  right_inv q _ := (Equiv.sigmaProdDistrib X Z).apply_symm_apply q

theorem isLocalScDiffeo_sigmaProdDistrib :
    ((sigma P).prod S).IsLocalScDiffeo (sigma fun i => (P i).prod S)
      (Equiv.sigmaProdDistrib X Z) :=
  fun p => ⟨univ, univ, _, mem_univ p, isScDiffeoOn_sigmaProdDistrib P S⟩

end Right

section Left

variable [ParacompactSpace (Z × Σ i, X i)] [∀ i, ParacompactSpace (Z × X i)]

/-- **`Z × Σ i, X i` and `Σ i, (Z × X i)` are sc-diffeomorphic**, by `(z, (i, x)) ↦ (i, (z, x))`,
with the product M-polyfold structures. -/
theorem isScDiffeoOn_prodSigmaDistrib :
    (S.prod (sigma P)).IsScDiffeoOn (sigma fun i => S.prod (P i))
      (fun p => ⟨p.2.1, (p.1, p.2.2)⟩) (fun q => (q.2.1, ⟨q.1, q.2.2⟩)) univ univ where
  isScSmoothOn := by
    -- on the open piece `Z × range (Sigma.mk i)` the map is `Sigma.mk i ∘ (id × sigmaProj i x)`
    refine IsScSmoothOn.of_locally isOpen_univ ?_
    rintro ⟨z, ⟨i, x⟩⟩ -
    have hWo : IsOpen (univ ×ˢ range (Sigma.mk i) : Set (Z × Σ i, X i)) :=
      isOpen_univ.prod isOpen_range_sigmaMk
    refine ⟨_, hWo, ⟨mem_univ z, mem_range_self x⟩, subset_univ _, ?_⟩
    have h1 : (S.prod (sigma P)).IsScSmoothOn (S.prod (P i))
        (fun q => (q.1, sigmaProj i x q.2)) (univ ×ˢ range (Sigma.mk i)) :=
      IsScSmoothOn.prodMk ((isScSmoothMap_fst S (sigma P)).mono hWo (subset_univ _))
        (IsScSmoothOn.comp (isScSmoothOn_sigmaProj P i x)
          ((isScSmoothMap_snd S (sigma P)).mono hWo (subset_univ _)) fun q hq => hq.2)
    refine (IsScSmoothOn.comp (isScSmoothMap_sigmaMk (fun i => S.prod (P i)) i) h1
      (mapsTo_univ _ _)).congr ?_
    rintro ⟨q₁, q₂⟩ ⟨-, ⟨y, rfl⟩⟩
    change Sigma.mk i (q₁, sigmaProj i x ⟨i, y⟩) = (⟨i, (q₁, y)⟩ : Σ i, Z × X i)
    rw [sigmaProj_mk]
  isScSmoothOn_inv :=
    (isScSmoothMap_sigma_iff (fun i => S.prod (P i))).2 fun i =>
      IsScSmoothOn.prodMk (isScSmoothMap_fst S (P i))
        ((isScSmoothMap_sigmaMk P i).comp (isScSmoothMap_snd S (P i)))
  mapsTo _ _ := mem_univ _
  mapsTo_inv _ _ := mem_univ _
  left_inv _ _ := rfl
  right_inv _ _ := rfl

end Left

end Prod

end MPolyfold

/-! ### A discrete factor -/

section Discrete

variable {G : Type u} [TopologicalSpace G] [DiscreteTopology G]
  {X : Type v} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
  [ParacompactSpace (G × X)]

/-- **A product `G × X` with a discrete `G` is the disjoint union `Σ (_ : G), X`** of copies of
`X` (sc-diffeomorphic by `(g, x) ↦ (g, x)`), with Chapter 7's `discretePolyfold G`. -/
theorem isScDiffeoOn_prod_discrete_sigma :
    ((discretePolyfold G).prod PX).IsScDiffeoOn (MPolyfold.sigma fun _ : G => PX)
      (fun p => ⟨p.1, p.2⟩) (fun q => (q.1, q.2)) univ univ where
  isScSmoothOn := isScSmoothMap_prod_discrete_iff.2 fun g =>
    MPolyfold.isScSmoothMap_sigmaMk (fun _ : G => PX) g
  isScSmoothOn_inv := (MPolyfold.isScSmoothMap_sigma_iff (fun _ : G => PX)).2 fun g =>
    isScSmoothMap_sheet g
  mapsTo _ _ := mem_univ _
  mapsTo_inv _ _ := mem_univ _
  left_inv _ _ := rfl
  right_inv _ _ := rfl

end Discrete

end Polyfold
