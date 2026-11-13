import Polyfold.Chapter15.ProductStrongBundle

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2021), §15.3, the products remark after
**Definition 15.3.3** (pp. 692–693; 2017: after Definition 15.3): the product strong bundle
`W × W' → X × X'` of Part I strong bundles and the product of sections (gap G.160 (a)).

# The product strong bundle `W × W' → X × X'`

## The text, paraphrased

For strong bundles `P : W → X`, `P' : W' → X'` and sections `f`, `f'` the text takes the product
`P × P' : W × W' → X × X'` with the section `f × f'`; it does not spell out the strong bundle
structure.

## What is formalized

* `prodFiberEquiv`, the vector space structures `prodFiber_addCommGroup`, `prodFiber_module` on
  the fibres `(P × P')⁻¹(x, x') ≅ P⁻¹(x) × P'⁻¹(x')`, `prodFiberCLE` (a topological linear
  isomorphism), `IsBanachable.prod`.
* `StrongBundleChart.prod` (the product chart `Φ × Φ'` after the swap
  `(E ⊕ F) ⊕ (E' ⊕ F') ≅ (E ⊕ E') ⊕ (F ⊕ F')`, with the strong bundle retraction `R × R'`),
  `overlap_prod`, `transition_prod`, `StrongBundleChart.Compatible.prod` (on `[0]` and `[1]`).
* `StrongBundle.prodAtlas`, `StrongBundle.prod` (**the product strong bundle**, Definition 2.6.5
  (preprint 2.51)), `StrongBundle.paracompactSpace_prod`.
* `IsSection.prodMap`, `StrongBundle.IsScSmoothSection.prod` (**`f × f'` is an sc-smooth
  section**), `StrongBundle.IsScPlusSection.prod` (products of sc⁺-sections are sc⁺).

## Choices

* The fibre model of the product chart is `F ⊕ F'` and the base model `E ⊕ E'`; the chart is
  `y ↦ swap(Φ(y₁), Φ'(y₂))`.  The atlas consists of the products of charts of the two atlases
  (as `MPolyfold.prod` for M-polyfolds).
-/

open Set Function

noncomputable section

namespace Polyfold

universe u v u' v'

/-! ### The fibres of `P × P'` -/

section ProdFibres

variable {X : Type u} {Y : Type v} {X' : Type u'} {Y' : Type v'} (P : Y → X) (P' : Y' → X')

/-- The fibre of `P × P'` over `(x, x')` is `P⁻¹(x) × P'⁻¹(x')`. -/
def prodFiberEquiv (p : X × X') : (Prod.map P P' ⁻¹' {p}) ≃ (P ⁻¹' {p.1}) × (P' ⁻¹' {p.2}) where
  toFun y := (⟨y.1.1, show P y.1.1 = p.1 from congrArg Prod.fst (y.2 : Prod.map P P' y.1 = p)⟩,
    ⟨y.1.2, show P' y.1.2 = p.2 from congrArg Prod.snd (y.2 : Prod.map P P' y.1 = p)⟩)
  invFun z := ⟨(z.1.1, z.2.1), show Prod.map P P' (z.1.1, z.2.1) = p from
    Prod.ext (z.1.2 : P z.1.1 = p.1) (z.2.2 : P' z.2.1 = p.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, AddCommGroup (P' ⁻¹' {x})]

instance prodFiber_addCommGroup (p : X × X') : AddCommGroup (Prod.map P P' ⁻¹' {p}) :=
  (prodFiberEquiv P P' p).addCommGroup

lemma prodFiberEquiv_add (p : X × X') (v w : Prod.map P P' ⁻¹' {p}) :
    prodFiberEquiv P P' p (v + w) = prodFiberEquiv P P' p v + prodFiberEquiv P P' p w :=
  (prodFiberEquiv P P' p).apply_symm_apply _

variable [∀ x, Module ℝ (P ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]

instance prodFiber_module (p : X × X') : Module ℝ (Prod.map P P' ⁻¹' {p}) :=
  (prodFiberEquiv P P' p).module ℝ

lemma prodFiberEquiv_smul (p : X × X') (a : ℝ) (v : Prod.map P P' ⁻¹' {p}) :
    prodFiberEquiv P P' p (a • v) = a • prodFiberEquiv P P' p v :=
  (prodFiberEquiv P P' p).apply_symm_apply _

variable [TopologicalSpace Y] [TopologicalSpace Y']

/-- The fibre identification as a topological linear isomorphism. -/
def prodFiberCLE (p : X × X') : (Prod.map P P' ⁻¹' {p}) ≃L[ℝ] (P ⁻¹' {p.1}) × (P' ⁻¹' {p.2}) where
  toFun := prodFiberEquiv P P' p
  invFun := (prodFiberEquiv P P' p).symm
  map_add' := prodFiberEquiv_add P P' p
  map_smul' := prodFiberEquiv_smul P P' p
  left_inv := (prodFiberEquiv P P' p).left_inv
  right_inv := (prodFiberEquiv P P' p).right_inv
  continuous_toFun :=
    ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _

end ProdFibres

/-- A product of Banachable spaces is Banachable. -/
lemma IsBanachable.prod {V V' : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [AddCommGroup V'] [Module ℝ V'] [TopologicalSpace V'] (h : IsBanachable V)
    (h' : IsBanachable V') : IsBanachable (V × V') := by
  obtain ⟨B, i₁, i₂, i₃, ⟨e⟩⟩ := h
  obtain ⟨B', j₁, j₂, j₃, ⟨e'⟩⟩ := h'
  exact ⟨B × B', inferInstance, inferInstance, inferInstance, ⟨e.prodCongr e'⟩⟩

/-- Banachability is invariant under topological linear isomorphisms. -/
lemma IsBanachable.of_equiv {V V' : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [AddCommGroup V'] [Module ℝ V'] [TopologicalSpace V'] (e : V ≃L[ℝ] V')
    (h : IsBanachable V') : IsBanachable V := by
  obtain ⟨B, i₁, i₂, i₃, ⟨e'⟩⟩ := h
  exact ⟨B, i₁, i₂, i₃, ⟨e.trans e'⟩⟩

/-! ### Product strong bundle charts -/

section ProdChart

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {X' : Type u'} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type v'} [TopologicalSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]
  [ParacompactSpace (X × X')]

namespace StrongBundleChart

variable (c : StrongBundleChart PX P) (c' : StrongBundleChart PX' P')

/-- The product chart map `y ↦ swap(Φ(y₁), Φ'(y₂))` as a partial equivalence. -/
def prodPartialEquiv :
    PartialEquiv (Y × Y') ((c.φ.model.E.prod c'.φ.model.E) 0 × (c.F.prod c'.F) 0) where
  toFun y := bundleSwap (c y.1, c' y.2)
  invFun k := (c.toPartialEquiv.symm (bundleSwap k).1, c'.toPartialEquiv.symm (bundleSwap k).2)
  source := c.toPartialEquiv.source ×ˢ c'.toPartialEquiv.source
  target := bundleSwap ⁻¹' (c.toPartialEquiv.target ×ˢ c'.toPartialEquiv.target)
  map_source' y hy := mem_preimage.2 ⟨c.toPartialEquiv.map_source hy.1,
    c'.toPartialEquiv.map_source hy.2⟩
  map_target' k hk := ⟨c.toPartialEquiv.map_target hk.1, c'.toPartialEquiv.map_target hk.2⟩
  left_inv' y hy := Prod.ext (c.toPartialEquiv.left_inv hy.1) (c'.toPartialEquiv.left_inv hy.2)
  right_inv' k hk := by
    change bundleSwap (c.toPartialEquiv (c.toPartialEquiv.symm (bundleSwap k).1),
      c'.toPartialEquiv (c'.toPartialEquiv.symm (bundleSwap k).2)) = k
    rw [c.toPartialEquiv.right_inv hk.1, c'.toPartialEquiv.right_inv hk.2]
    rfl

/-- **The product strong bundle chart** `Φ × Φ' : (P × P')⁻¹(V × V') → K × K'` (after the
swap), over the product chart `φ × φ'` of `X × X'`, with fibre model `F ⊕ F'` and strong bundle
retraction `R × R'`. -/
def prod : StrongBundleChart (PX.prod PX') (Prod.map P P') where
  φ := c.φ.prod c'.φ
  isChart := c.isChart.prod c'.isChart
  F := c.F.prod c'.F
  U := c.U ×ˢ c'.U
  R := prodBundleMap c.R c'.R
  relOpen := c.relOpen.prod c'.relOpen
  isRetraction := c.isRetraction.prod c.relOpen c'.relOpen c'.isRetraction
  base_retract :=
    (retract_baseRetraction_prod c.relOpen c'.relOpen c.isRetraction c'.isRetraction).trans
      (by rw [c.base_retract, c'.base_retract]; rfl)
  toPartialEquiv := c.prodPartialEquiv c'
  source_eq := by
    change c.toPartialEquiv.source ×ˢ c'.toPartialEquiv.source = _
    rw [c.source_eq, c'.source_eq]; rfl
  target_eq := by
    change bundleSwap ⁻¹' (c.toPartialEquiv.target ×ˢ c'.toPartialEquiv.target) = _
    rw [c.target_eq, c'.target_eq]
    exact image_prodBundleMap.symm
  continuousOn_toFun :=
    continuous_bundleSwap.comp_continuousOn (c.continuousOn_toFun.prodMap c'.continuousOn_toFun)
  continuousOn_invFun :=
    (c.continuousOn_invFun.prodMap c'.continuousOn_invFun).comp
      continuous_bundleSwap.continuousOn fun _ hk => hk
  covers y hy := by
    change ((c y.1).1, (c' y.2).1) = (c.φ (P y.1), c'.φ (P' y.2))
    rw [c.covers _ hy.1, c'.covers _ hy.2]
  fiber_linear x hx := by
    have l₁ := c.fiber_linear x.1 hx.1
    have l₂ := c'.fiber_linear x.2 hx.2
    constructor
    · intro v w
      have h₁ := l₁.map_add (prodFiberEquiv P P' x v).1 (prodFiberEquiv P P' x w).1
      have h₂ := l₂.map_add (prodFiberEquiv P P' x v).2 (prodFiberEquiv P P' x w).2
      rw [← Prod.fst_add, ← prodFiberEquiv_add] at h₁
      rw [← Prod.snd_add, ← prodFiberEquiv_add] at h₂
      exact Prod.ext h₁ h₂
    · intro a v
      have h₁ := l₁.map_smul a (prodFiberEquiv P P' x v).1
      have h₂ := l₂.map_smul a (prodFiberEquiv P P' x v).2
      rw [← Prod.smul_fst, ← prodFiberEquiv_smul] at h₁
      rw [← Prod.smul_snd, ← prodFiberEquiv_smul] at h₂
      exact Prod.ext h₁ h₂

lemma prod_apply (y : Y × Y') : c.prod c' y = bundleSwap (c y.1, c' y.2) := rfl

lemma prod_source :
    (c.prod c').toPartialEquiv.source = c.toPartialEquiv.source ×ˢ c'.toPartialEquiv.source := rfl

lemma prod_K : (c.prod c').K = bundleSwap ⁻¹' (c.K ×ˢ c'.K) := image_prodBundleMap

variable (d : StrongBundleChart PX P) (d' : StrongBundleChart PX' P')

lemma overlap_prod :
    (c.prod c').overlap (d.prod d') = bundleSwap ⁻¹' (c.overlap d ×ˢ c'.overlap d') := by
  ext k
  constructor
  · rintro ⟨y, ⟨hy₁, hy₂⟩, rfl⟩
    exact ⟨⟨y.1, ⟨hy₁.1, hy₂.1⟩, rfl⟩, ⟨y.2, ⟨hy₁.2, hy₂.2⟩, rfl⟩⟩
  · rintro ⟨⟨y, hy, hyk⟩, ⟨y', hy', hyk'⟩⟩
    refine ⟨(y, y'), ⟨⟨hy.1, hy'.1⟩, ⟨hy.2, hy'.2⟩⟩, ?_⟩
    change bundleSwap (c y, c' y') = k
    rw [hyk, hyk']
    rfl

lemma transition_prod :
    (c.prod c').transition (d.prod d') = prodBundleMap (c.transition d) (c'.transition d') := rfl

variable {c c' d d'}

/-- **Products of compatible strong bundle charts are compatible** (Definition 2.6.4 (preprint
2.50)), on `[0]` and on `[1]`. -/
theorem Compatible.prod (h : c.Compatible d) (h' : c'.Compatible d') :
    (c.prod c').Compatible (d.prod d') := by
  have hS₀ := (c.prod c').isScRetract_overlap' (d.prod d')
  have hT₀ := (d.prod d').isScRetract_overlap' (c.prod c')
  have hS₁ := (c.prod c').isScRetract_overlap_one' (d.prod d')
  have hT₁ := (d.prod d').isScRetract_overlap_one' (c.prod c')
  rw [overlap_prod] at hS₀ hT₀ hS₁ hT₁
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [overlap_prod, overlap_prod, transition_prod]
    exact IsScSmoothRetractMap.prodBundleMap (c.isScRetract_overlap' d)
      (c'.isScRetract_overlap' d') (d.isScRetract_overlap' c) (d'.isScRetract_overlap' c') hS₀
      h.1 h'.1
  · rw [overlap_prod, overlap_prod, transition_prod]
    exact IsScSmoothRetractMap.prodBundleMap (d.isScRetract_overlap' c)
      (d'.isScRetract_overlap' c') (c.isScRetract_overlap' d) (c'.isScRetract_overlap' d') hT₀
      h.2.1 h'.2.1
  · rw [overlap_prod, overlap_prod, transition_prod]
    have key := IsScSmoothRetractMap.prodBundleMap (c.isScRetract_overlap_one' d)
      (c'.isScRetract_overlap_one' d') (d.isScRetract_overlap_one' c)
      (d'.isScRetract_overlap_one' c') hS₁ h.2.2.1 h'.2.2.1
    refine key.congr fun p hp => (shiftFiber_prodBundleMap ?_ ?_).symm
    · exact h.2.2.2.2.1 _ hp.1 ⟨p.2.1, rfl⟩
    · exact h'.2.2.2.2.1 _ hp.2 ⟨p.2.2, rfl⟩
  · rw [overlap_prod, overlap_prod, transition_prod]
    have key := IsScSmoothRetractMap.prodBundleMap (d.isScRetract_overlap_one' c)
      (d'.isScRetract_overlap_one' c') (c.isScRetract_overlap_one' d)
      (c'.isScRetract_overlap_one' d') hT₁ h.2.2.2.1 h'.2.2.2.1
    refine key.congr fun p hp => (shiftFiber_prodBundleMap ?_ ?_).symm
    · exact h.2.2.2.2.2 _ hp.1 ⟨p.2.1, rfl⟩
    · exact h'.2.2.2.2.2 _ hp.2 ⟨p.2.2, rfl⟩
  · intro x hx hx₂
    rw [overlap_prod] at hx
    have hx₂' := (ScBanach.mem_range_prod_toBase (E := c.F) (F := c'.F)).1 hx₂
    exact (ScBanach.mem_range_prod_toBase (E := d.F) (F := d'.F)).2
      ⟨h.2.2.2.2.1 _ hx.1 hx₂'.1, h'.2.2.2.2.1 _ hx.2 hx₂'.2⟩
  · intro x hx hx₂
    rw [overlap_prod] at hx
    have hx₂' := (ScBanach.mem_range_prod_toBase (E := d.F) (F := d'.F)).1 hx₂
    exact (ScBanach.mem_range_prod_toBase (E := c.F) (F := c'.F)).2
      ⟨h.2.2.2.2.2 _ hx.1 hx₂'.1, h'.2.2.2.2.2 _ hx.2 hx₂'.2⟩

end StrongBundleChart

end ProdChart

/-! ### The product strong bundle and products of sections -/

section ProdSection

variable {X : Type u} {Y : Type v} {X' : Type u'} {Y' : Type v'} {P : Y → X} {P' : Y' → X'}

/-- `f × f'` is a section of `P × P'`. -/
theorem IsSection.prodMap {f : X → Y} {f' : X' → Y'} (hf : IsSection P f)
    (hf' : IsSection P' f') : IsSection (Prod.map P P') (Prod.map f f') :=
  fun p => Prod.ext (hf p.1) (hf' p.2)

end ProdSection

section ProdBundle

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {X' : Type u'} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type v'} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]
  [ParacompactSpace (X × X')]

namespace StrongBundle

omit [ParacompactSpace (X × X')] in
/-- `W × W'` is paracompact (it is metrizable, Theorem 2.3.10 (preprint 2.16) for `W[0]` and
`W'[0]`). -/
theorem paracompactSpace_prod (B : StrongBundle PX P) (B' : StrongBundle PX' P') :
    ParacompactSpace (Y × Y') :=
  MPolyfold.paracompactSpace_prod B.toMPolyfold0 B'.toMPolyfold0

/-- The product strong bundle atlas: the products `Φ × Φ'` of charts of the two atlases. -/
def prodAtlas (B : StrongBundle PX P) (B' : StrongBundle PX' P') :
    StrongBundleAtlas (PX.prod PX') (Prod.map P P') where
  charts := {χ | ∃ c ∈ B.atlas.charts, ∃ c' ∈ B'.atlas.charts, χ = c.prod c'}
  compatible := by
    rintro _ ⟨c, hc, c', hc', rfl⟩ _ ⟨d, hd, d', hd', rfl⟩
    exact (B.atlas.compatible c hc d hd).prod (B'.atlas.compatible c' hc' d' hd')
  cover y := by
    obtain ⟨c, hc, h₁⟩ := B.atlas.cover y.1
    obtain ⟨c', hc', h₂⟩ := B'.atlas.cover y.2
    exact ⟨c.prod c', ⟨c, hc, c', hc', rfl⟩, h₁, h₂⟩

variable [ParacompactSpace (Y × Y')]

/-- **The product strong bundle** `P × P' : W × W' → X × X'` (Definition 2.6.5 (preprint 2.51);
used in the products remark after Definition 15.3.3, p. 692): a continuous surjection with
Banachable fibres `(P × P')⁻¹(x, x') ≅ P⁻¹(x) × P'⁻¹(x')`, with the atlas `prodAtlas`. -/
def prod (B : StrongBundle PX P) (B' : StrongBundle PX' P') :
    StrongBundle (PX.prod PX') (Prod.map P P') where
  continuous := B.continuous.prodMap B'.continuous
  surjective := B.surjective.prodMap B'.surjective
  banachable p :=
    IsBanachable.of_equiv (prodFiberCLE P P' p) ((B.banachable p.1).prod (B'.banachable p.2))
  atlas := B.prodAtlas B'

variable (B : StrongBundle PX P) (B' : StrongBundle PX' P')

lemma prod_mem_charts {c : StrongBundleChart PX P} {c' : StrongBundleChart PX' P'}
    (hc : c ∈ B.atlas.charts) (hc' : c' ∈ B'.atlas.charts) :
    c.prod c' ∈ (B.prod B').atlas.charts :=
  ⟨c, hc, c', hc', rfl⟩

end StrongBundle

variable [ParacompactSpace (Y × Y')] {B : StrongBundle PX P} {B' : StrongBundle PX' P'}

/-- The chart data around a point at which an sc-smooth section is represented. -/
lemma StrongBundle.exists_chart_rep {f : X → Y} (hf : B.IsScSmoothSection f) (x : X) :
    ∃ (φ : MChart X) (c : StrongBundleChart PX P) (V : Set X), PX.IsChart φ ∧
      c ∈ B.atlas.charts ∧ IsOpen V ∧ x ∈ V ∧ V ⊆ φ.source ∧
      MapsTo f V c.toPartialEquiv.source ∧
      IsScSmoothRetractMap φ.model.E φ.model.C (φ '' V) (c.φ.model.E.prod c.F)
        (c.φ.model.C ×ˢ univ) c.K (c ∘ f ∘ φ.symm) := by
  have hfc : Continuous f := continuousOn_univ.1 hf.2.continuousOn
  obtain ⟨c, hc, hy⟩ := B.atlas.cover (f x)
  obtain ⟨φ, hφ, hx⟩ := PX.exists_isChart_mem_source x
  have hV : IsOpen (φ.source ∩ f ⁻¹' c.toPartialEquiv.source) :=
    φ.isOpen_source.inter ((c.isOpen_source B.continuous).preimage hfc)
  refine ⟨φ, c, _, hφ, hc, hV, ⟨hx, hy⟩, inter_subset_left, fun z hz => hz.2, ?_⟩
  exact hf.2.smooth φ (c.toMChart B.continuous) hφ (B.isChart_toMChart hc) _ hV
    (fun z hz => ⟨mem_univ _, hz.1⟩) fun z hz => hz.2

/-- **Products of sc-smooth sections are sc-smooth** (the section `f × f'` of the products
remark after Definition 15.3.3, p. 692; Definition 2.6.6 (preprint 2.52)). -/
theorem StrongBundle.IsScSmoothSection.prod {f : X → Y} {f' : X' → Y'}
    (hf : B.IsScSmoothSection f) (hf' : B'.IsScSmoothSection f') :
    (B.prod B').IsScSmoothSection (Prod.map f f') := by
  refine ⟨hf.1.prodMap hf'.1, MPolyfold.IsScSmoothOn.of_exists_charts isOpen_univ
    ((hf.2.continuousOn.prodMap hf'.2.continuousOn).mono fun _ _ => ⟨mem_univ _, mem_univ _⟩)
    fun p _ => ?_⟩
  obtain ⟨φ, c, V, hφ, hc, hV, hpV, hVφ, hfV, hrep⟩ := B.exists_chart_rep hf p.1
  obtain ⟨φ', c', V', hφ', hc', hV', hpV', hVφ', hfV', hrep'⟩ := B'.exists_chart_rep hf' p.2
  refine ⟨φ.prod φ', (c.prod c').toMChart (B.prod B').continuous, V ×ˢ V', hφ.prod hφ',
    (B.prod B').isChart_toMChart (StrongBundle.prod_mem_charts B B' hc hc'), hV.prod hV',
    ⟨hpV, hpV'⟩, fun q hq => ⟨mem_univ _, hVφ hq.1, hVφ' hq.2⟩,
    fun q hq => ⟨hfV hq.1, hfV' hq.2⟩, ?_⟩
  have himg : (φ.prod φ') '' (V ×ˢ V') = (φ '' V) ×ˢ (φ' '' V') := (prod_image_image_eq).symm
  have hK : ((c.prod c').toMChart (B.prod B').continuous).model.O =
      bundleSwap ⁻¹' (c.K ×ˢ c'.K) := StrongBundleChart.prod_K c c'
  have h₁ := IsScSmoothRetractMap.prodMap (φ.isScRetract_image hVφ hV)
    (φ'.isScRetract_image hVφ' hV') hrep hrep'
  have hσ : IsScSmoothRetractMap ((c.φ.model.E.prod c.F).prod (c'.φ.model.E.prod c'.F))
      ((c.φ.model.C ×ˢ univ) ×ˢ (c'.φ.model.C ×ˢ univ)) (c.K ×ˢ c'.K)
      ((c.φ.model.E.prod c'.φ.model.E).prod (c.F.prod c'.F)) ((c.φ.model.C ×ˢ c'.φ.model.C) ×ˢ univ)
      (bundleSwap ⁻¹' (c.K ×ˢ c'.K)) (ScBanach.bundleSwapOp c.φ.model.E c.F c'.φ.model.E c'.F 0) :=
    (ScBanach.bundleSwapOp _ _ _ _).isScSmoothRetractMap (c.isScRetract.prod c'.isScRetract)
      fun _ hk => hk
  rw [himg, hK]
  exact hσ.comp h₁ (c.isScRetract.prod c'.isScRetract)

/-- **Products of sc⁺-sections are sc⁺** (Definition 2.6.6 (preprint 2.52)), for the product
atlas. -/
theorem StrongBundle.IsScPlusSection.prod {f : X → Y} {f' : X' → Y'}
    (hf : B.IsScPlusSection f) (hf' : B'.IsScPlusSection f') :
    (B.prod B').IsScPlusSection (Prod.map f f') := by
  refine ⟨hf.1.prodMap hf'.1, ?_⟩
  rintro _ ⟨c, hc, c', hc', rfl⟩
  obtain ⟨hr, hs⟩ := hf.2 c hc
  obtain ⟨hr', hs'⟩ := hf'.2 c' hc'
  refine ⟨fun x hx => (ScBanach.mem_range_prod_toBase (E := c.F) (F := c'.F)).2
    ⟨hr x.1 hx.1, hr' x.2 hx.2⟩, ?_⟩
  have h₁ := IsScSmoothRetractMap.prodMap c.φ.model.isScRetract c'.φ.model.isScRetract hs hs'
  have hσ : IsScSmoothRetractMap ((c.φ.model.E.prod c.F.shift).prod (c'.φ.model.E.prod c'.F.shift))
      ((c.φ.model.C ×ˢ univ) ×ˢ (c'.φ.model.C ×ˢ univ)) (strongShiftOne c.K ×ˢ strongShiftOne c'.K)
      ((c.φ.model.E.prod c'.φ.model.E).prod (c.F.shift.prod c'.F.shift))
      ((c.φ.model.C ×ˢ c'.φ.model.C) ×ˢ univ)
      (bundleSwap ⁻¹' (strongShiftOne c.K ×ˢ strongShiftOne c'.K))
      (ScBanach.bundleSwapOp c.φ.model.E c.F.shift c'.φ.model.E c'.F.shift 0) :=
    (ScBanach.bundleSwapOp _ _ _ _).isScSmoothRetractMap
      (c.isScRetract_one.prod c'.isScRetract_one) fun _ hk => hk
  have h₂ := hσ.comp h₁ (c.isScRetract_one.prod c'.isScRetract_one)
  rw [StrongBundleChart.prod_K]
  refine h₂.congr fun z hz => ?_
  have hz₁ : c.φ.symm z.1 ∈ c.φ.source := c.φ.symm_mapsTo hz.1
  have hz₂ : c'.φ.symm z.2 ∈ c'.φ.source := c'.φ.symm_mapsTo hz.2
  change bundleSwap (StrongBundle.localRepOne c f z.1, StrongBundle.localRepOne c' f' z.2) =
    (_, invFun ((c.F.prod c'.F).toBase 1) ((c (f (c.φ.symm z.1))).2, (c' (f' (c'.φ.symm z.2))).2))
  rw [ScBanach.invFun_prod_toBase_one (hr _ hz₁) (hr' _ hz₂)]
  rfl

end ProdBundle

end Polyfold
