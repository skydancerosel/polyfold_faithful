import Polyfold.Chapter3.IndexAlongPathsDevice
import Polyfold.Chapter3.StrongBundleMaximalAtlas
import Polyfold.Chapter5.Homotopy

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §2.2 and §2.5:
the restriction of an M-polyfold and of a strong bundle to an open subset (used implicitly
throughout the text: "a locally defined sc⁺-section", "in a chart, `s(y) = R(y, f(x))`", the
proof of Proposition 6.2: "we do not need a sc-smooth partition of unity").  Round-trip item
V3.98 (a); Findings, Chapter 3, items 360–369.

# Restriction of M-polyfolds and strong bundles to open subsets

## The text, paraphrased

The text freely restricts a strong bundle `P : Y → X` to an open subset `V ⊆ X` (the domain of
a chart, say) and speaks of sections of `P|V`: the stabilizing sections `R(·, e)` of the proof of
Proposition 6.2 and of Theorem 3.54, the local sc⁺-sections of Definition 6.1.  No partition of
unity is needed for these constructions because the sections live on `V` only.

## What is formalized

* `Polyfold.MChart.restrictTo`: a chart of `X` with source inside the open `V` transported to a
  chart of the subtype `V` (same model, `φ ∘ ι`); `MChart.Compatible.restrictTo`.
* `Polyfold.MPolyfold.restrictOpen PX hV : MPolyfold V`: the M-polyfold structure of the open
  subset `V` (atlas: all charts of `X` inside `V`, transported); `isChart_restrictTo`,
  `mem_levelSet_restrictOpen_iff`, `mem_smoothSet_restrictOpen_iff` (the levels of `V` are the
  traces of those of `X`), `IsScSmoothMap.codRestrict_restrictOpen` (an sc-smooth map with values
  in `V` is sc-smooth into `V`).
* `Polyfold.StrongBundleChart.restrictTo`: a strong bundle chart with base source inside `V`
  transported to a chart of the pull-back `ι*P : ι*Y → V` (same `F`, `U`, `R`, `K`; `Φ ∘ ι`);
  `StrongBundleChart.Compatible.restrictTo`.
* `Polyfold.StrongBundle.restrictOpen B hV : StrongBundle (PX.restrictOpen hV) (ι*P)` (**the
  restriction `P|V`**, atlas: all strong bundle charts of `P` inside `V`, transported;
  `isChart_restrictTo`), with `restrictOpen_isChart_restrictTo`.
* The restricted section `f|V = restrictSection P V f hf` (`Chapter5/Homotopy.lean`):
  `StrongBundle.IsScSmoothSection.restrictOpen`, `IsScPlusSection.restrictOpen`,
  `regularizing_restrictOpen`, and (`RestrictOpenGerms.lean`) the germ data.
* `Polyfold.StrongBundleChart.principal_restrictTo`: the principal part of `f|V` in a transported
  chart is that of `f` on `O`.

## What the text leaves implicit, and the choices made

* The total space of `P|V` is the pull-back `ι*Y = {(v, y) | P(y) = v}` along the inclusion
  (Definition 2.53), as in Definition 5.20 (`restrictSection`); its fibres are those of `P`
  (`pullbackFiberEquiv`).  The atlas consists of all charts of `P` whose base domain lies in `V`;
  every chart of `P` restricts to such a chart (`StrongBundleChart.restrict`).
* The paracompactness of `V` and of `ι*Y` are instance arguments, supplied by
  `MPolyfold.paracompactSpace_subtype` and `paracompactSpace_pullbackSpace` (Theorem 2.16).
  The junk values of the transported inverse charts need `V` nonempty (`[Nonempty V]`).
-/

open Set Filter Topology Function Module ContinuousLinearMap
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v w

/-! ### Charts of an open subset -/

namespace MChart

variable {X : Type u} [TopologicalSpace X] (φ ψ : MChart X) {V : Set X} [Nonempty V]

open scoped Classical

/-- A chart `φ` of `X` with `dom φ ⊆ V` as a chart of the subtype `V`: the same model, the map
`v ↦ φ(v)`, the inverse `z ↦ φ⁻¹(z)` (with a junk value off `O`). -/
def restrictTo (hsub : φ.source ⊆ V) : MChart V where
  model := φ.model
  toPartialEquiv :=
    { toFun := fun v => φ v.1
      invFun := fun z => if h : z ∈ φ.model.O then ⟨φ.symm z, hsub (φ.symm_mapsTo h)⟩
        else Classical.arbitrary V
      source := Subtype.val ⁻¹' φ.source
      target := φ.model.O
      map_source' := fun v hv => φ.mapsTo_model v.1 hv
      map_target' := fun z hz => by
        change (if h : z ∈ φ.model.O then (⟨φ.symm z, hsub (φ.symm_mapsTo h)⟩ : V)
          else Classical.arbitrary V) ∈ Subtype.val ⁻¹' φ.source
        rw [dif_pos hz]; exact φ.symm_mapsTo hz
      left_inv' := fun v hv => by
        change (if h : φ v.1 ∈ φ.model.O then (⟨φ.symm (φ v.1), hsub (φ.symm_mapsTo h)⟩ : V)
          else Classical.arbitrary V) = v
        rw [dif_pos (φ.mapsTo_model v.1 hv)]
        exact Subtype.ext (φ.symm_apply_apply hv)
      right_inv' := fun z hz => by
        change φ (if h : z ∈ φ.model.O then (⟨φ.symm z, hsub (φ.symm_mapsTo h)⟩ : V)
          else Classical.arbitrary V).1 = z
        rw [dif_pos hz]; exact φ.apply_symm_apply hz }
  isOpen_source := φ.isOpen_source.preimage continuous_subtype_val
  target_eq := rfl
  continuousOn_toFun :=
    φ.continuousOn_toFun.comp continuous_subtype_val.continuousOn fun _ hv => hv
  continuousOn_invFun := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine φ.continuousOn_invFun.congr fun z hz => ?_
    change (if h : z ∈ φ.model.O then (⟨φ.symm z, hsub (φ.symm_mapsTo h)⟩ : V)
      else Classical.arbitrary V).1 = φ.symm z
    rw [dif_pos hz]

variable {φ ψ}

@[simp] lemma restrictTo_source (hsub : φ.source ⊆ V) :
    (φ.restrictTo hsub).source = Subtype.val ⁻¹' φ.source := rfl

@[simp] lemma restrictTo_apply (hsub : φ.source ⊆ V) (v : V) : φ.restrictTo hsub v = φ v.1 := rfl

@[simp] lemma restrictTo_model (hsub : φ.source ⊆ V) : (φ.restrictTo hsub).model = φ.model := rfl

lemma restrictTo_symm_val (hsub : φ.source ⊆ V) {z : φ.model.E 0} (hz : z ∈ φ.model.O) :
    ((φ.restrictTo hsub).symm z).1 = φ.symm z := by
  change (if h : z ∈ φ.model.O then (⟨φ.symm z, hsub (φ.symm_mapsTo h)⟩ : V)
    else Classical.arbitrary V).1 = φ.symm z
  rw [dif_pos hz]

/-- The overlap of two transported charts is the overlap of the charts. -/
lemma restrictTo_overlap (hsub : φ.source ⊆ V) (hsub' : ψ.source ⊆ V) :
    (φ.restrictTo hsub).overlap (ψ.restrictTo hsub') = φ.overlap ψ := by
  ext z
  constructor
  · rintro ⟨v, ⟨hv, hv'⟩, rfl⟩
    exact ⟨v.1, ⟨hv, hv'⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hx'⟩, rfl⟩
    exact ⟨⟨x, hsub hx⟩, ⟨hx, hx'⟩, rfl⟩

/-- The transition map of two transported charts is that of the charts, on the overlap. -/
lemma restrictTo_transition_eqOn (hsub : φ.source ⊆ V) (hsub' : ψ.source ⊆ V) :
    EqOn ((φ.restrictTo hsub).transition (ψ.restrictTo hsub')) (φ.transition ψ) (φ.overlap ψ) := by
  intro z hz
  change ψ ((φ.restrictTo hsub).symm z).1 = ψ (φ.symm z)
  rw [restrictTo_symm_val hsub (φ.overlap_subset ψ hz)]

/-- Compatibility passes to the transported charts. -/
theorem Compatible.restrictTo (h : φ.Compatible ψ) (hsub : φ.source ⊆ V)
    (hsub' : ψ.source ⊆ V) : (φ.restrictTo hsub).Compatible (ψ.restrictTo hsub') := by
  refine ⟨?_, ?_⟩
  · rw [restrictTo_overlap hsub hsub', restrictTo_overlap hsub' hsub]
    exact h.1.congr fun z hz => (restrictTo_transition_eqOn hsub hsub' hz).symm
  · rw [restrictTo_overlap hsub hsub', restrictTo_overlap hsub' hsub]
    exact h.2.congr fun z hz => (restrictTo_transition_eqOn hsub' hsub hz).symm

end MChart

/-! ### The M-polyfold structure of an open subset -/

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
  {V : Set X} [Nonempty V]

/-- The atlas of the open subset `V`: all charts of `X` with source inside `V`, transported. -/
def restrictOpenAtlas (hV : IsOpen V) : MAtlas V where
  charts := {χ | ∃ (φ : MChart X) (_ : PX.IsChart φ) (hsub : φ.source ⊆ V), χ = φ.restrictTo hsub}
  compatible := by
    rintro _ ⟨φ, hφ, hsub, rfl⟩ _ ⟨ψ, hψ, hsub', rfl⟩
    exact (hφ.compatible hψ (P := PX)).restrictTo hsub hsub'
  cover v := by
    obtain ⟨φ, hφ, hv⟩ := PX.exists_isChart_mem_source v.1
    refine ⟨(φ.restrict (s := φ.source ∩ V) inter_subset_left
      (φ.isOpen_source.inter hV)).restrictTo inter_subset_right,
      ⟨_, MPolyfold.IsChart.restrict PX hφ _ _, _, rfl⟩, ?_⟩
    exact ⟨hv, v.2⟩

variable [ParacompactSpace V]

/-- **The M-polyfold structure of an open subset** `V ⊆ X` (the charts of `X` inside `V`). -/
def restrictOpen (hV : IsOpen V) : MPolyfold V := ⟨PX.restrictOpenAtlas hV⟩

variable {PX}

/-- A chart of `X` inside `V` is a chart of `V`. -/
theorem isChart_restrictTo (hV : IsOpen V) {φ : MChart X} (hφ : PX.IsChart φ)
    (hsub : φ.source ⊆ V) : (PX.restrictOpen hV).IsChart (φ.restrictTo hsub) :=
  (PX.restrictOpen hV).isChart_of_mem ⟨φ, hφ, hsub, rfl⟩

/-- The levels of `V` are the traces of the levels of `X`. -/
theorem mem_levelSet_restrictOpen_iff (hV : IsOpen V) (v : V) (m : ℕ) :
    v ∈ (PX.restrictOpen hV).levelSet m ↔ v.1 ∈ PX.levelSet m := by
  obtain ⟨φ, hφ, hv⟩ := PX.exists_isChart_mem_source v.1
  set φ' := φ.restrict (s := φ.source ∩ V) inter_subset_left (φ.isOpen_source.inter hV) with hφ'
  have hφ'c : PX.IsChart φ' := MPolyfold.IsChart.restrict PX hφ _ _
  have hv' : v.1 ∈ φ'.source := ⟨hv, v.2⟩
  rw [(PX.restrictOpen hV).mem_levelSet_iff (isChart_restrictTo hV hφ'c inter_subset_right) hv',
    PX.mem_levelSet_iff hφ'c hv']
  rfl

/-- The smooth points of `V` are the smooth points of `X` in `V`. -/
theorem mem_smoothSet_restrictOpen_iff (hV : IsOpen V) (v : V) :
    v ∈ (PX.restrictOpen hV).smoothSet ↔ v.1 ∈ PX.smoothSet := by
  simp only [MPolyfold.smoothSet, mem_iInter, mem_levelSet_restrictOpen_iff]

variable {Z : Type w} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {PZ : MPolyfold Z}

/-- **An sc-smooth map with values in the open `V` is sc-smooth into `V`.** -/
theorem IsScSmoothMap.codRestrict_restrictOpen (hV : IsOpen V) {g : Z → X}
    (hg : PZ.IsScSmoothMap PX g) (hgV : ∀ z, g z ∈ V) :
    PZ.IsScSmoothMap (PX.restrictOpen hV) fun z => (⟨g z, hgV z⟩ : V) := by
  have hgc : Continuous g := continuousOn_univ.1 hg.continuousOn
  refine MPolyfold.isScSmoothMap_of_local fun z => ?_
  obtain ⟨χ, hχ, hz⟩ := PZ.exists_isChart_mem_source z
  obtain ⟨φ, hφ, hgz⟩ := PX.exists_isChart_mem_source (g z)
  set φ' := φ.restrict (s := φ.source ∩ V) inter_subset_left (φ.isOpen_source.inter hV) with hφ'
  have hφ'c : PX.IsChart φ' := MPolyfold.IsChart.restrict PX hφ _ _
  set W := χ.source ∩ g ⁻¹' φ'.source with hW
  have hWo : IsOpen W := χ.isOpen_source.inter (φ'.isOpen_source.preimage hgc)
  refine ⟨χ, φ'.restrictTo (V := V) inter_subset_right, W, hχ,
    isChart_restrictTo hV hφ'c inter_subset_right, hWo, ⟨hz, ⟨hgz, hgV z⟩⟩, inter_subset_left,
    fun z' hz' => hz'.2, ?_⟩
  exact hg.smooth χ φ' hχ hφ'c W hWo (fun z' hz' => ⟨mem_univ _, hz'.1⟩) fun z' hz' => hz'.2

end MPolyfold

/-! ### Strong bundle charts of an open subset -/

namespace StrongBundleChart

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  (c c' : StrongBundleChart PX P) {V : Set X} [Nonempty V] [ParacompactSpace V]

/-- The base point of an element of `ι*Y` is the projection of its fibre point. -/
lemma pullbackSpace_val_proj (q : pullbackSpace P (Subtype.val : V → X)) : P q.1.2 = q.1.1.1 := q.2

open scoped Classical in
/-- The inverse of the transported bundle chart: `k ↦ (P(Φ⁻¹ k), Φ⁻¹ k)` on `K`, the junk
value `q₀` elsewhere. -/
def restrictToInv (hsub : c.φ.source ⊆ V) (q₀ : pullbackSpace P (Subtype.val : V → X))
    (k : c.φ.model.E 0 × c.F 0) : pullbackSpace P (Subtype.val : V → X) :=
  if h : k ∈ c.K then
    ⟨(⟨P (c.toPartialEquiv.symm k), hsub (c.mem_base_of_mem_source
      (c.toPartialEquiv.map_target (by rw [c.target_eq]; exact h)))⟩, c.toPartialEquiv.symm k), rfl⟩
  else q₀

variable {c c'}

lemma restrictToInv_of_mem (hsub : c.φ.source ⊆ V) (q₀ : pullbackSpace P (Subtype.val : V → X))
    {k : c.φ.model.E 0 × c.F 0} (hk : k ∈ c.K) :
    (c.restrictToInv hsub q₀ k).1.2 = c.toPartialEquiv.symm k := by
  unfold restrictToInv; rw [dif_pos hk]

lemma mem_source_of_mem_restrictTo_source
    {q : pullbackSpace P (Subtype.val : V → X)} (hq : q.1.1.1 ∈ c.φ.source) :
    q.1.2 ∈ c.toPartialEquiv.source :=
  c.mem_source_of_mem_base (by rw [pullbackSpace_val_proj q]; exact hq)

lemma restrictToInv_fst_val (hsub : c.φ.source ⊆ V) (q₀ : pullbackSpace P (Subtype.val : V → X))
    {k : c.φ.model.E 0 × c.F 0} (hk : k ∈ c.K) :
    (c.restrictToInv hsub q₀ k).1.1.1 = P (c.toPartialEquiv.symm k) := by
  unfold restrictToInv; rw [dif_pos hk]

variable (c) (hP : Continuous P) (hV : IsOpen V)

include hP hV in
/-- **A strong bundle chart `Φ` of `P` with base domain inside `V`, as a strong bundle chart of
`P|V = ι*P`**: the same `F`, `U`, `R` and `K`, the base chart `φ ∘ ι`, and `Φ ∘ ι` on
`P_ι⁻¹(ι⁻¹(dom φ))`. -/
def restrictTo (hsub : c.φ.source ⊆ V) (q₀ : pullbackSpace P (Subtype.val : V → X)) :
    StrongBundleChart (PX.restrictOpen hV) (pullbackProj P (Subtype.val : V → X)) where
  φ := c.φ.restrictTo hsub
  isChart := MPolyfold.isChart_restrictTo hV c.isChart hsub
  F := c.F
  U := c.U
  R := c.R
  relOpen := c.relOpen
  isRetraction := c.isRetraction
  base_retract := c.base_retract
  toPartialEquiv :=
    { toFun := fun q => c q.1.2
      invFun := c.restrictToInv hsub q₀
      source := pullbackProj P Subtype.val ⁻¹' (Subtype.val ⁻¹' c.φ.source)
      target := c.R '' (c.U ×ˢ univ)
      map_source' := fun q hq => by
        have := c.toPartialEquiv.map_source (mem_source_of_mem_restrictTo_source hq)
        rwa [c.target_eq] at this
      map_target' := fun k hk => by
        change (c.restrictToInv hsub q₀ k).1.1.1 ∈ c.φ.source
        rw [restrictToInv_fst_val hsub q₀ hk]
        exact c.mem_base_of_mem_source (c.toPartialEquiv.map_target (by rw [c.target_eq]; exact hk))
      left_inv' := fun q hq => by
        have hqs := mem_source_of_mem_restrictTo_source hq
        have hk : c q.1.2 ∈ c.K := by
          have := c.toPartialEquiv.map_source hqs; rwa [c.target_eq] at this
        unfold restrictToInv; rw [dif_pos hk]
        refine Subtype.ext (Prod.ext (Subtype.ext ?_) ?_)
        · change P (c.toPartialEquiv.symm (c q.1.2)) = q.1.1.1
          rw [c.toPartialEquiv.left_inv hqs, pullbackSpace_val_proj q]
        · exact c.toPartialEquiv.left_inv hqs
      right_inv' := fun k hk => by
        change c (c.restrictToInv hsub q₀ k).1.2 = k
        rw [restrictToInv_of_mem hsub q₀ hk]
        exact c.toPartialEquiv.right_inv (by rw [c.target_eq]; exact hk) }
  source_eq := rfl
  target_eq := rfl
  continuousOn_toFun :=
    c.continuousOn_toFun.comp (continuous_snd.comp continuous_subtype_val).continuousOn
      fun q hq => mem_source_of_mem_restrictTo_source hq
  continuousOn_invFun := by
    change ContinuousOn (c.restrictToInv hsub q₀) c.K
    rw [continuousOn_iff_continuous_domRestrict]
    have hsymm : Continuous fun k : c.K => c.toPartialEquiv.symm k.1 := by
      have := c.continuousOn_invFun
      rw [c.target_eq] at this
      exact continuousOn_iff_continuous_domRestrict.1 this
    have : (c.K.domRestrict (c.restrictToInv hsub q₀)) = fun k : c.K =>
        (⟨(⟨P (c.toPartialEquiv.symm k.1), hsub (c.mem_base_of_mem_source
          (c.toPartialEquiv.map_target (by rw [c.target_eq]; exact k.2)))⟩,
          c.toPartialEquiv.symm k.1), rfl⟩ : pullbackSpace P (Subtype.val : V → X)) := by
      funext k
      change c.restrictToInv hsub q₀ k.1 = _
      unfold restrictToInv; rw [dif_pos k.2]
    rw [this]
    exact (((hP.comp hsymm).subtype_mk _).prodMk hsymm).subtype_mk _
  covers := fun q hq => by
    change (c q.1.2).1 = c.φ q.1.1.1
    rw [c.covers q.1.2 (mem_source_of_mem_restrictTo_source hq), pullbackSpace_val_proj q]
  fiber_linear := fun v hv => by
    have h := c.fiber_linear v.1 hv
    set e := pullbackFiberEquiv P (Subtype.val : V → X) v with he
    exact
      { map_add := fun w w' => by
          have := h.map_add (e w) (e w')
          rw [← pullbackFiberEquiv_add] at this
          exact this
        map_smul := fun a w => by
          have := h.map_smul a (e w)
          rw [← pullbackFiberEquiv_smul] at this
          exact this }

variable {c}

@[simp] lemma restrictTo_φ (hsub : c.φ.source ⊆ V) (q₀ : pullbackSpace P (Subtype.val : V → X)) :
    (c.restrictTo hP hV hsub q₀).φ = c.φ.restrictTo hsub := rfl

@[simp] lemma restrictTo_F (hsub : c.φ.source ⊆ V) (q₀ : pullbackSpace P (Subtype.val : V → X)) :
    (c.restrictTo hP hV hsub q₀).F = c.F := rfl

@[simp] lemma restrictTo_U (hsub : c.φ.source ⊆ V) (q₀ : pullbackSpace P (Subtype.val : V → X)) :
    (c.restrictTo hP hV hsub q₀).U = c.U := rfl

@[simp] lemma restrictTo_R (hsub : c.φ.source ⊆ V) (q₀ : pullbackSpace P (Subtype.val : V → X)) :
    (c.restrictTo hP hV hsub q₀).R = c.R := rfl

@[simp] lemma restrictTo_apply (hsub : c.φ.source ⊆ V) (q₀ : pullbackSpace P (Subtype.val : V → X))
    (q : pullbackSpace P (Subtype.val : V → X)) : c.restrictTo hP hV hsub q₀ q = c q.1.2 := rfl

lemma restrictTo_K (hsub : c.φ.source ⊆ V) (q₀ : pullbackSpace P (Subtype.val : V → X)) :
    (c.restrictTo hP hV hsub q₀).K = c.K := rfl

lemma restrictTo_source (hsub : c.φ.source ⊆ V) (q₀ : pullbackSpace P (Subtype.val : V → X)) :
    (c.restrictTo hP hV hsub q₀).toPartialEquiv.source =
      {q | q.1.1.1 ∈ c.φ.source} := rfl

lemma restrictTo_symm_val (hsub : c.φ.source ⊆ V) (q₀ : pullbackSpace P (Subtype.val : V → X))
    {k : c.φ.model.E 0 × c.F 0} (hk : k ∈ c.K) :
    ((c.restrictTo hP hV hsub q₀).toPartialEquiv.symm k).1.2 = c.toPartialEquiv.symm k :=
  restrictToInv_of_mem hsub q₀ hk

/-- The overlap of two transported charts is the overlap of the charts. -/
lemma restrictTo_overlap (hsub : c.φ.source ⊆ V) (q₀ : pullbackSpace P (Subtype.val : V → X))
    (hsub' : c'.φ.source ⊆ V) (q₀' : pullbackSpace P (Subtype.val : V → X)) :
    (c.restrictTo hP hV hsub q₀).overlap (c'.restrictTo hP hV hsub' q₀') = c.overlap c' := by
  ext k
  constructor
  · rintro ⟨q, ⟨hq, hq'⟩, rfl⟩
    exact ⟨q.1.2, ⟨mem_source_of_mem_restrictTo_source hq,
      mem_source_of_mem_restrictTo_source hq'⟩, rfl⟩
  · rintro ⟨y, ⟨hy, hy'⟩, rfl⟩
    refine ⟨⟨(⟨P y, hsub (c.mem_base_of_mem_source hy)⟩, y), rfl⟩,
      ⟨c.mem_base_of_mem_source hy, c'.mem_base_of_mem_source hy'⟩, rfl⟩

/-- The transition map of two transported charts is that of the charts, on the overlap. -/
lemma restrictTo_transition_eqOn (hsub : c.φ.source ⊆ V)
    (q₀ : pullbackSpace P (Subtype.val : V → X)) (hsub' : c'.φ.source ⊆ V)
    (q₀' : pullbackSpace P (Subtype.val : V → X)) :
    EqOn ((c.restrictTo hP hV hsub q₀).transition (c'.restrictTo hP hV hsub' q₀'))
      (c.transition c') (c.overlap c') := by
  rintro _ ⟨y, hy, rfl⟩
  have hk : c y ∈ c.K := by
    have := c.toPartialEquiv.map_source hy.1; rwa [c.target_eq] at this
  change c' ((c.restrictTo hP hV hsub q₀).toPartialEquiv.symm (c y)).1.2 =
    c' (c.toPartialEquiv.symm (c y))
  rw [restrictTo_symm_val hP hV hsub q₀ hk]

lemma mem_overlap_of_mem_strongShiftOne {p : (c.φ.model.E.prod c.F.shift) 0}
    (hp : p ∈ strongShiftOne (c.overlap c')) : (p.1, c.F.toBase 1 p.2) ∈ c.overlap c' := hp

/-- **Compatibility passes to the transported charts.** -/
theorem Compatible.restrictTo (h : c.Compatible c') (hsub : c.φ.source ⊆ V)
    (q₀ : pullbackSpace P (Subtype.val : V → X)) (hsub' : c'.φ.source ⊆ V)
    (q₀' : pullbackSpace P (Subtype.val : V → X)) :
    (c.restrictTo hP hV hsub q₀).Compatible (c'.restrictTo hP hV hsub' q₀') := by
  have e1 := restrictTo_overlap hP hV hsub q₀ hsub' q₀'
  have e2 := restrictTo_overlap hP hV hsub' q₀' hsub q₀
  have t1 := restrictTo_transition_eqOn hP hV hsub q₀ hsub' q₀'
  have t2 := restrictTo_transition_eqOn hP hV hsub' q₀' hsub q₀
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e1, e2]; exact h1.congr fun z hz => (t1 hz).symm
  · rw [e1, e2]; exact h2.congr fun z hz => (t2 hz).symm
  · rw [e1, e2]
    refine h3.congr fun p hp => ?_
    have := t1 (mem_overlap_of_mem_strongShiftOne hp)
    exact (congrArg (fun k : c'.φ.model.E 0 × c'.F 0 =>
      (k.1, Function.invFun (c'.F.toBase 1) k.2)) this).symm
  · rw [e1, e2]
    refine h4.congr fun p hp => ?_
    have := t2 (mem_overlap_of_mem_strongShiftOne hp)
    exact (congrArg (fun k : c.φ.model.E 0 × c.F 0 =>
      (k.1, Function.invFun (c.F.toBase 1) k.2)) this).symm
  · rw [e1]; intro p hp hp2; rw [t1 hp]; exact h5 p hp hp2
  · rw [e2]; intro p hp hp2; rw [t2 hp]; exact h6 p hp hp2

end StrongBundleChart

/-! ### The restriction of a strong bundle to an open subset -/

namespace StrongBundle

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] (B : StrongBundle PX P)
  {V : Set X} [Nonempty V] [ParacompactSpace V] (hV : IsOpen V)

/-- The atlas of `P|V`: all strong bundle charts of `P` with base domain inside `V`,
transported. -/
def restrictOpenAtlas : StrongBundleAtlas (PX.restrictOpen hV) (pullbackProj P (Subtype.val : V → X))
    where
  charts := {Φ | ∃ (c : StrongBundleChart PX P) (_ : B.IsChart c) (hsub : c.φ.source ⊆ V)
    (q₀ : pullbackSpace P (Subtype.val : V → X)), Φ = c.restrictTo B.continuous hV hsub q₀}
  compatible := by
    rintro _ ⟨c, hc, hsub, q₀, rfl⟩ _ ⟨c', hc', hsub', q₀', rfl⟩
    exact (hc.compatible hc').restrictTo B.continuous hV hsub q₀ hsub' q₀'
  cover q := by
    obtain ⟨c, hc, hy⟩ := B.atlas.cover q.1.2
    have hq : q.1.1.1 ∈ c.φ.source := by
      rw [← StrongBundleChart.pullbackSpace_val_proj q]; exact c.mem_base_of_mem_source hy
    refine ⟨(c.restrict (s := c.φ.source ∩ V) inter_subset_left
      (c.φ.isOpen_source.inter hV)).restrictTo B.continuous hV inter_subset_right q,
      ⟨_, (B.isChart_of_mem hc).restrict _ _, _, q, rfl⟩, ?_⟩
    exact show q.1.1.1 ∈ c.φ.source ∩ V from ⟨hq, q.1.1.2⟩

variable [ParacompactSpace (pullbackSpace P (Subtype.val : V → X))]

/-- **The restriction `P|V` of a strong bundle to an open subset** `V ⊆ X`: the pull-back
`ι*P : ι*Y → V` along the inclusion, with the charts of `P` inside `V`. -/
def restrictOpen : StrongBundle (PX.restrictOpen hV) (pullbackProj P (Subtype.val : V → X)) where
  continuous := continuous_pullbackProj P _
  surjective v := by
    obtain ⟨y, hy⟩ := B.surjective v.1
    exact ⟨⟨(v, y), hy⟩, rfl⟩
  banachable v := by
    obtain ⟨Bsp, h1, h2, h3, ⟨e⟩⟩ := B.banachable v.1
    exact ⟨Bsp, h1, h2, h3, ⟨(pullbackFiberCLE (P := P) (f := (Subtype.val : V → X)) v).trans e⟩⟩
  atlas := B.restrictOpenAtlas hV

variable {B}

/-- A strong bundle chart of `P` inside `V` is a chart of the atlas of `P|V`. -/
theorem restrictTo_mem_restrictOpen_atlas {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (hsub : c.φ.source ⊆ V) (q₀ : pullbackSpace P (Subtype.val : V → X)) :
    c.restrictTo B.continuous hV hsub q₀ ∈ (B.restrictOpen hV).atlas.charts :=
  ⟨c, hc, hsub, q₀, rfl⟩

/-- A strong bundle chart of `P` inside `V` is a strong bundle chart of `P|V`. -/
theorem restrictOpen_isChart_restrictTo {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (hsub : c.φ.source ⊆ V) (q₀ : pullbackSpace P (Subtype.val : V → X)) :
    (B.restrictOpen hV).IsChart (c.restrictTo B.continuous hV hsub q₀) :=
  (B.restrictOpen hV).isChart_of_mem (restrictTo_mem_restrictOpen_atlas hV hc hsub q₀)

end StrongBundle

/-! ### The restriction of a chart to `dom φ ∩ V` -/

namespace StrongBundleChart

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  (c : StrongBundleChart PX P) {V : Set X} (hV : IsOpen V)

/-- The restriction of a strong bundle chart to `dom φ ∩ V` (`StrongBundleChart.restrict`): a
chart of `P` with base domain inside `V`, with the same `F`, `R`, and `Φ`. -/
abbrev restrictInter : StrongBundleChart PX P :=
  c.restrict (s := c.φ.source ∩ V) inter_subset_left (c.φ.isOpen_source.inter hV)

lemma restrictInter_source : (c.restrictInter hV).φ.source = c.φ.source ∩ V := rfl

lemma restrictInter_source_subset : (c.restrictInter hV).φ.source ⊆ V := inter_subset_right

lemma mem_restrictInter_source {x : X} (hx : x ∈ c.φ.source) (hxV : x ∈ V) :
    x ∈ (c.restrictInter hV).φ.source := ⟨hx, hxV⟩

lemma restrictInter_apply (y : Y) : c.restrictInter hV y = c y := rfl

lemma restrictInter_φ_apply (x : X) : (c.restrictInter hV).φ x = c.φ x := rfl

lemma restrictInter_R : (c.restrictInter hV).R = c.R := rfl

lemma restrictInter_model_O : (c.restrictInter hV).φ.model.O = c.φ '' (c.φ.source ∩ V) := rfl

lemma restrictInter_U :
    (c.restrictInter hV).U =
      {u ∈ c.U | IsStrongBundleMap.base c.R u ∈ c.φ '' (c.φ.source ∩ V)} :=
  c.restrict_U _ _

lemma restrictInter_U_subset : (c.restrictInter hV).U ⊆ c.U := by
  rw [restrictInter_U]; exact fun _ hu => hu.1

variable {c}

variable [T2Space Y] [ParacompactSpace Y] {B : StrongBundle PX P} in
lemma _root_.Polyfold.StrongBundle.IsChart.restrictInter (hc : B.IsChart c) :
    B.IsChart (c.restrictInter hV) :=
  hc.restrict _ _

end StrongBundleChart

namespace StrongBundle

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {V : Set X} [Nonempty V] [ParacompactSpace V]
  [ParacompactSpace (pullbackSpace P (Subtype.val : V → X))] (hV : IsOpen V)

/-- The restriction of a chart of `P` to `dom φ ∩ V`, transported, is a chart of the atlas of
`P|V`. -/
theorem restrictInter_restrictTo_mem {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (q₀ : pullbackSpace P (Subtype.val : V → X)) :
    (c.restrictInter hV).restrictTo B.continuous hV (c.restrictInter_source_subset hV) q₀ ∈
      (B.restrictOpen hV).atlas.charts :=
  restrictTo_mem_restrictOpen_atlas hV (hc.restrictInter hV) _ q₀

end StrongBundle

/-! ### Sections of `P|V` -/

section Sections

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {V : Set X} [Nonempty V] [ParacompactSpace V]
  [ParacompactSpace (pullbackSpace P (Subtype.val : V → X))] (hV : IsOpen V) {f : X → Y}

omit [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
  [∀ x, Module ℝ (P ⁻¹' {x})] [Nonempty V] [ParacompactSpace V]
  [ParacompactSpace (pullbackSpace P Subtype.val)] in
lemma isSection_restrictSection (hf : IsSection P f) :
    IsSection (pullbackProj P (Subtype.val : V → X)) (restrictSection P V f hf) := fun _ => rfl

omit [T2Space Y] [ParacompactSpace Y] [ParacompactSpace (pullbackSpace P Subtype.val)] in
/-- The principal part of `f|V` in a transported chart is that of `f`, on `O`. -/
lemma StrongBundleChart.principal_restrictTo (hP : Continuous P) {c : StrongBundleChart PX P}
    (hsub : c.φ.source ⊆ V) (q₀ : pullbackSpace P (Subtype.val : V → X)) (hf : IsSection P f)
    {z : c.φ.model.E 0} (hz : z ∈ c.φ.model.O) :
    (c.restrictTo hP hV hsub q₀).principal (restrictSection P V f hf) z = c.principal f z := by
  change (c (f ((c.φ.restrictTo hsub).symm z).1)).2 = (c (f (c.φ.symm z))).2
  rw [MChart.restrictTo_symm_val hsub hz]

omit [T2Space Y] [ParacompactSpace Y] [ParacompactSpace (pullbackSpace P Subtype.val)] in
/-- The lifted local representative of `f|V` in a transported chart is that of `f`, on `O`. -/
lemma StrongBundleChart.localRepOne_restrictTo (hP : Continuous P) {c : StrongBundleChart PX P}
    (hsub : c.φ.source ⊆ V) (q₀ : pullbackSpace P (Subtype.val : V → X)) (hf : IsSection P f)
    {z : c.φ.model.E 0} (hz : z ∈ c.φ.model.O) :
    StrongBundle.localRepOne (c.restrictTo hP hV hsub q₀) (restrictSection P V f hf) z =
      StrongBundle.localRepOne c f z := by
  simp only [StrongBundle.localRepOne]
  change ((c (f ((c.φ.restrictTo hsub).symm z).1)).1, Function.invFun (c.F.toBase 1)
    (c (f ((c.φ.restrictTo hsub).symm z).1)).2) = _
  rw [MChart.restrictTo_symm_val hsub hz]

/-- **The restriction of an sc-smooth section is sc-smooth.** -/
theorem StrongBundle.IsScSmoothSection.restrictOpen (hf : B.IsScSmoothSection f) :
    (B.restrictOpen hV).IsScSmoothSection (restrictSection P V f hf.1) := by
  refine ⟨isSection_restrictSection hf.1, ?_⟩
  refine MPolyfold.isScSmoothMap_of_local fun v => ?_
  obtain ⟨c, hc, hv⟩ := StrongBundle.exists_chart_mem B v.1
  set c' := c.restrictInter hV with hc'def
  have hc' : B.IsChart c' := (B.isChart_of_mem hc).restrictInter hV
  have hsub : c'.φ.source ⊆ V := c.restrictInter_source_subset hV
  have hv' : v.1 ∈ c'.φ.source := c.mem_restrictInter_source hV hv v.2
  set q₀ : pullbackSpace P (Subtype.val : V → X) := restrictSection P V f hf.1 v with hq₀
  set cV := c'.restrictTo B.continuous hV hsub q₀ with hcV
  have hcVmem : cV ∈ (B.restrictOpen hV).atlas.charts :=
    StrongBundle.restrictTo_mem_restrictOpen_atlas hV hc' hsub q₀
  refine ⟨cV.φ, cV.toMChart (B.restrictOpen hV).continuous, cV.φ.source,
    MPolyfold.isChart_restrictTo hV c'.isChart hsub,
    (B.restrictOpen hV).isChart_toMChart hcVmem, cV.φ.isOpen_source, hv', subset_rfl,
    fun w hw => cV.mem_source_of_proj (by exact hw), ?_⟩
  rw [cV.φ.image_source]
  have h := hf.2.smooth c'.φ (c'.toMChart B.continuous) c'.isChart hc'.toMChart c'.φ.source
    c'.φ.isOpen_source (fun x hx => ⟨mem_univ _, hx⟩)
    (fun x hx => c'.mem_source_of_proj (by rw [hf.1 x]; exact hx))
  rw [c'.φ.image_source] at h
  refine h.congr fun z hz => ?_
  change c' (f (c'.φ.symm z)) = c' (f ((c'.φ.restrictTo hsub).symm z).1)
  rw [MChart.restrictTo_symm_val hsub hz]

/-- **The restriction of an sc⁺-section is an sc⁺-section.** -/
theorem StrongBundle.IsScPlusSection.restrictOpen {s : X → Y} (hs : B.IsScPlusSection s) :
    (B.restrictOpen hV).IsScPlusSection (restrictSection P V s hs.1) := by
  refine ⟨isSection_restrictSection hs.1, ?_⟩
  rintro _ ⟨c, hc, hsub, q₀, rfl⟩
  refine ⟨fun v hv => ?_, ?_⟩
  · change (c (s v.1)).2 ∈ range (c.F.toBase 1)
    have := hs.principal_mem_range hc (c.φ.mapsTo_model v.1 hv)
    unfold StrongBundleChart.principal at this
    rwa [c.φ.symm_apply_apply hv] at this
  · have h := hs.isScSmoothRetractMap_one hc
    refine h.congr fun z hz => ?_
    rw [StrongBundleChart.localRepOne_restrictTo hV B.continuous hsub q₀ hs.1 hz,
      c.localRepOne_eq s z]
    refine Prod.ext ?_ rfl
    change z = (c (s (c.φ.symm z))).1
    rw [c.fst_apply (by rw [hs.1]; exact c.φ.symm_mapsTo hz), hs.1, c.φ.apply_symm_apply hz]

/-- **The restriction of a regularizing section is regularizing** (the double filtration of
`P|V` is tested in the transported charts, `mem_doubleLevel_iff`). -/
theorem StrongBundle.regularizing_restrictOpen (hf : B.IsScFredholmSection f) :
    ∀ m, ∀ v ∈ (PX.restrictOpen hV).levelSet m,
      restrictSection P V f hf.isScSmooth.1 v ∈ (B.restrictOpen hV).doubleLevel m (m + 1) →
        v ∈ (PX.restrictOpen hV).levelSet (m + 1) := by
  intro m v hv hdl
  rw [MPolyfold.mem_levelSet_restrictOpen_iff] at hv ⊢
  refine hf.regularizing m v.1 hv fun c hc hmem => ?_
  have hvV : v.1 ∈ c.φ.source := by
    rw [c.source_eq, mem_preimage, hf.isScSmooth.1 v.1] at hmem; exact hmem
  have hv' : v.1 ∈ (c.restrictInter hV).φ.source := c.mem_restrictInter_source hV hvV v.2
  exact hdl _ (StrongBundle.restrictInter_restrictTo_mem hV (B.isChart_of_mem hc)
    (restrictSection P V f hf.isScSmooth.1 v)) hv'

end Sections

end Polyfold
