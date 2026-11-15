import Polyfold.Chapter3.FredholmPullbackIso
import Polyfold.Chapter7.LocalDiffeo
import Polyfold.Chapter8.TangentLocal
import Polyfold.Chapter10.StrongBundleEquivalence

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §2.6,
Definition 2.6.5, p. 68 (strong bundles and their restrictions to open subsets of the base), and
the local strong bundle isomorphisms of Part II, Definitions 8.3.5 and 10.4.1; this file supports
Chapter 12, §12.5, pp. 592–595 (orientations of sc-Fredholm section functors), where the
linearizations at a point are formed in a strong bundle chart around the point.

# The inclusion of a restricted strong bundle as a local strong bundle isomorphism

## The text, paraphrased

A strong bundle `P : Y → X` restricts to a strong bundle `P|V : Y|V → V` over every open subset
`V` of the base, and the inclusion `Y|V → Y` is a strong bundle isomorphism onto `P⁻¹(V)`.
Local strong bundle isomorphisms compose.  The constructions of §12.5 are local: around a point
one works in a strong bundle chart, i.e. in the restriction of the bundle to the base domain of
the chart, and two such restrictions are compared on the intersection of their bases.

## What is formalized

* `MPolyfold.IsScDiffeoOn.comp_inter`: the composite of two sc-diffeomorphisms `U → U'`,
  `V → V'` on `U ∩ f⁻¹(V)`.
* `StrongBundle.LocalIso.trans`: **the composite of two local strong bundle isomorphisms**
  `Y|U → Y'|U'` and `Y'|V → Y''|V'`, on `U ∩ ϕ⁻¹(V)`; `LocalIso.ofEq`: change of the domains
  along equalities.
* `StrongBundle.restrictIso hV`: **the inclusion `Y|V → Y`** as a local strong bundle isomorphism
  `(P|V)|univ → P|V` (`StrongBundle.restrictOpen` of `Chapter3/RestrictOpen.lean`); in the charts
  `c|V` of `P|V` and `c` of `P` all its maps are the identity of the model.
* `StrongBundle.restrictSection_eqOn_restrictIso`: the restriction `f|V` of a section is the
  pull-back of `f` along the inclusion.
* `StrongBundle.restrictIsoInter hW hV`: the identification `(P|W)|(W ∩ V) → (P|V)|(V ∩ W)` of
  two restrictions over the intersection of their bases; `restrictIsoOf hW hV hWV` for `W ⊆ V`;
  the restrictions of a section correspond (`restrictSection_eqOn_restrictIsoInter`,
  `restrictSection_eqOn_restrictIsoOf`).
* `StrongBundle.exists_chart_source_eq_univ_restrictOpen_of_subset`: the restriction of a strong
  bundle to an open subset of the base domain of a chart of the atlas has a chart of its atlas
  over its whole base.

## What the text leaves implicit, and the choices made

* The inverse maps of the inclusion take a chosen value off `V`, resp. off `P⁻¹(V)`; on the level
  `[1]` this uses that `Y|V[1]` is not empty (it contains the zero vectors,
  `StrongBundle.nonempty_one`).
* `(Y|V)_{0,1}` is the part of `Y_{0,1}` over `V` (`mem_oneSet_restrictOpen_iff`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u v

/-! ### Composition of sc-diffeomorphisms between open subsets -/

namespace MPolyfold

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
  {Z : Type*} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {S : MPolyfold Z}

/-- **The composite of two sc-diffeomorphisms** `f : U → U'` and `f₂ : V → V'` (with `U'`, `V`
open in the same M-polyfold) is an sc-diffeomorphism `U ∩ f⁻¹(V) → V' ∩ g₂⁻¹(U')`. -/
theorem IsScDiffeoOn.comp_inter {f : X → Y} {g : Y → X} {U : Set X} {U' : Set Y} {f₂ : Y → Z}
    {g₂ : Z → Y} {V : Set Y} {V' : Set Z} (h₁ : P.IsScDiffeoOn Q f g U U')
    (h₂ : Q.IsScDiffeoOn S f₂ g₂ V V') :
    P.IsScDiffeoOn S (f₂ ∘ f) (g ∘ g₂) (U ∩ f ⁻¹' V) (V' ∩ g₂ ⁻¹' U') where
  isScSmoothOn := IsScSmoothOn.comp h₂.isScSmoothOn
    (h₁.isScSmoothOn.mono (h₁.isScSmoothOn.continuousOn.isOpen_inter_preimage
      h₁.isScSmoothOn.isOpen h₂.isScSmoothOn.isOpen) inter_subset_left) fun _ hx => hx.2
  isScSmoothOn_inv := IsScSmoothOn.comp h₁.isScSmoothOn_inv
    (h₂.isScSmoothOn_inv.mono (h₂.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage
      h₂.isScSmoothOn_inv.isOpen h₁.isScSmoothOn_inv.isOpen) inter_subset_left) fun _ hz => hz.2
  mapsTo x hx := ⟨h₂.mapsTo hx.2, by
    rw [mem_preimage, Function.comp_apply, h₂.left_inv _ hx.2]; exact h₁.mapsTo hx.1⟩
  mapsTo_inv z hz := ⟨h₁.mapsTo_inv hz.2, by
    rw [mem_preimage, Function.comp_apply, h₁.right_inv _ hz.2]; exact h₂.mapsTo_inv hz.1⟩
  left_inv x hx := by
    simp only [Function.comp_apply, h₂.left_inv _ hx.2, h₁.left_inv _ hx.1]
  right_inv z hz := by
    simp only [Function.comp_apply, h₁.right_inv _ hz.2, h₂.right_inv _ hz.1]

end MPolyfold

namespace StrongBundle

/-! ### Composition of local strong bundle isomorphisms -/

section Trans

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {X' : Type*} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type*} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]
  {X'' : Type*} [TopologicalSpace X''] [T2Space X''] [ParacompactSpace X''] {PX'' : MPolyfold X''}
  {Y'' : Type*} [TopologicalSpace Y''] [T2Space Y''] [ParacompactSpace Y''] {P'' : Y'' → X''}
  [∀ x, AddCommGroup (P'' ⁻¹' {x})] [∀ x, Module ℝ (P'' ⁻¹' {x})]
  {B : StrongBundle PX P} {B' : StrongBundle PX' P'} {B'' : StrongBundle PX'' P''}
  {U : Set X} {U' : Set X'} {V : Set X'} {V' : Set X''}

namespace LocalIso

/-- Over `U`, the part of `Y` over `ϕ⁻¹(V)` is the preimage under `Φ` of the part of `Y'` over
`V`. -/
lemma preimage_inter_zero (L : LocalIso B B' U U') (V : Set X') :
    P ⁻¹' (U ∩ L.ϕ ⁻¹' V) = P ⁻¹' U ∩ L.Φ ⁻¹' (P' ⁻¹' V) := by
  ext y
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [mem_preimage, mem_preimage, L.covers y h1]; exact h2⟩
  · rintro ⟨h1, h2⟩
    rw [mem_preimage, mem_preimage, L.covers y h1] at h2
    exact ⟨h1, h2⟩

/-- The level `[1]` form of `preimage_inter_zero`. -/
lemma preimage_inter_one (L : LocalIso B B' U U') (V : Set X') :
    (P ∘ B.oneVal) ⁻¹' (U ∩ L.ϕ ⁻¹' V) =
      (P ∘ B.oneVal) ⁻¹' U ∩ L.Φ₁ ⁻¹' ((P' ∘ B'.oneVal) ⁻¹' V) := by
  ext w
  have key : ∀ h1 : P (B.oneVal w) ∈ U, P' (B'.oneVal (L.Φ₁ w)) = L.ϕ (P (B.oneVal w)) :=
    fun h1 => by rw [L.oneVal_Φ₁ w h1, L.covers _ h1]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    change P' (B'.oneVal (L.Φ₁ w)) ∈ V
    rw [key h1]; exact h2
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    change L.ϕ (P (B.oneVal w)) ∈ V
    rw [← key h1]; exact h2

/-- **The composite of two local strong bundle isomorphisms** `Φ : Y|U → Y'|U'` and
`Φ' : Y'|V → Y''|V'`: the local strong bundle isomorphism `Φ' ∘ Φ` from `Y|(U ∩ ϕ⁻¹(V))` onto
`Y''|(V' ∩ g'⁻¹(U'))`. -/
def trans (L : LocalIso B B' U U') (M : LocalIso B' B'' V V') :
    LocalIso B B'' (U ∩ L.ϕ ⁻¹' V) (V' ∩ M.g ⁻¹' U') where
  ϕ := M.ϕ ∘ L.ϕ
  g := L.g ∘ M.g
  Φ := M.Φ ∘ L.Φ
  Ψ := L.Ψ ∘ M.Ψ
  Φ₁ := M.Φ₁ ∘ L.Φ₁
  Ψ₁ := L.Ψ₁ ∘ M.Ψ₁
  base := L.base.comp_inter M.base
  zero := by
    have h2 : P'' ⁻¹' (V' ∩ M.g ⁻¹' U') = P'' ⁻¹' V' ∩ M.Ψ ⁻¹' (P' ⁻¹' U') :=
      M.symm.preimage_inter_zero U'
    rw [L.preimage_inter_zero V, h2]
    exact L.zero.comp_inter M.zero
  one := by
    have h2 : (P'' ∘ B''.oneVal) ⁻¹' (V' ∩ M.g ⁻¹' U') =
        (P'' ∘ B''.oneVal) ⁻¹' V' ∩ M.Ψ₁ ⁻¹' ((P' ∘ B'.oneVal) ⁻¹' U') :=
      M.symm.preimage_inter_one U'
    rw [L.preimage_inter_one V, h2]
    exact L.one.comp_inter M.one
  covers y hy := by
    have h1 : P' (L.Φ y) = L.ϕ (P y) := L.covers y hy.1
    have h2 : P' (L.Φ y) ∈ V := by rw [h1]; exact hy.2
    simp only [Function.comp_apply, M.covers _ h2, h1]
  oneVal_Φ₁ w hw := by
    have h1 : B'.oneVal (L.Φ₁ w) = L.Φ (B.oneVal w) := L.oneVal_Φ₁ w hw.1
    have h2 : P' (B'.oneVal (L.Φ₁ w)) ∈ V := by rw [h1, L.covers _ hw.1]; exact hw.2
    simp only [Function.comp_apply, M.oneVal_Φ₁ _ h2, h1]
  fiber_linear x x'' hx hx' := by
    have hL := L.fiber_linear x (L.ϕ x) hx.1 rfl
    have hM := M.fiber_linear (L.ϕ x) x'' hx.2 hx'
    exact ((hM.mk' _).comp (hL.mk' _)).isLinear

@[simp] lemma trans_ϕ (L : LocalIso B B' U U') (M : LocalIso B' B'' V V') :
    (L.trans M).ϕ = M.ϕ ∘ L.ϕ := rfl

@[simp] lemma trans_g (L : LocalIso B B' U U') (M : LocalIso B' B'' V V') :
    (L.trans M).g = L.g ∘ M.g := rfl

@[simp] lemma trans_Φ (L : LocalIso B B' U U') (M : LocalIso B' B'' V V') :
    (L.trans M).Φ = M.Φ ∘ L.Φ := rfl

@[simp] lemma trans_Ψ (L : LocalIso B B' U U') (M : LocalIso B' B'' V V') :
    (L.trans M).Ψ = L.Ψ ∘ M.Ψ := rfl

@[simp] lemma trans_Φ₁ (L : LocalIso B B' U U') (M : LocalIso B' B'' V V') :
    (L.trans M).Φ₁ = M.Φ₁ ∘ L.Φ₁ := rfl

@[simp] lemma trans_Ψ₁ (L : LocalIso B B' U U') (M : LocalIso B' B'' V V') :
    (L.trans M).Ψ₁ = L.Ψ₁ ∘ M.Ψ₁ := rfl

/-- A local strong bundle isomorphism `Y|U → Y'|U'`, with its domains rewritten along
equalities `U = W`, `U' = W'`. -/
def ofEq {W : Set X} {W' : Set X'} (L : LocalIso B B' U U') (hU : U = W) (hU' : U' = W') :
    LocalIso B B' W W' where
  ϕ := L.ϕ
  g := L.g
  Φ := L.Φ
  Ψ := L.Ψ
  Φ₁ := L.Φ₁
  Ψ₁ := L.Ψ₁
  base := hU ▸ hU' ▸ L.base
  zero := hU ▸ hU' ▸ L.zero
  one := hU ▸ hU' ▸ L.one
  covers y hy := L.covers y (hU ▸ hy)
  oneVal_Φ₁ w hw := L.oneVal_Φ₁ w (hU ▸ hw)
  fiber_linear x x' hx hx' := L.fiber_linear x x' (hU ▸ hx) hx'

section OfEq

variable {W : Set X} {W' : Set X'} (L : LocalIso B B' U U') (hU : U = W) (hU' : U' = W')

@[simp] lemma ofEq_ϕ : (L.ofEq hU hU').ϕ = L.ϕ := rfl

@[simp] lemma ofEq_g : (L.ofEq hU hU').g = L.g := rfl

@[simp] lemma ofEq_Φ : (L.ofEq hU hU').Φ = L.Φ := rfl

@[simp] lemma ofEq_Ψ : (L.ofEq hU hU').Ψ = L.Ψ := rfl

@[simp] lemma ofEq_Φ₁ : (L.ofEq hU hU').Φ₁ = L.Φ₁ := rfl

@[simp] lemma ofEq_Ψ₁ : (L.ofEq hU hU').Ψ₁ = L.Ψ₁ := rfl

end OfEq

end LocalIso

end Trans

/-! ### The inclusion `Y|V → Y` -/

section Restrict

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] (B : StrongBundle PX P)

/-- `Y[1]` is not empty over a nonempty base: it contains the zero vectors of the fibres. -/
theorem nonempty_one [Nonempty X] : Nonempty B.One := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have hP0 : P ((0 : P ⁻¹' {x}) : Y) = x := (0 : P ⁻¹' {x}).2
  obtain ⟨c, hc, hyc⟩ := B.atlas.cover ((0 : P ⁻¹' {x}) : Y)
  have hx : x ∈ c.φ.source := by
    have := c.mem_base_of_mem_source hyc
    rwa [hP0] at this
  refine ⟨B.oneMk _ ((B.mem_oneSet_iff hc hyc).2 ⟨0, ?_⟩)⟩
  rw [map_zero]; exact ((c.fiber_linear x hx).map_zero).symm

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- The base point of a point of `Y|V` is the projection of its fibre point. -/
lemma pullbackSpace_subtypeVal_proj {V : Set X} (q : pullbackSpace P (Subtype.val : V → X)) :
    P q.1.2 = q.1.1.1 := q.2

variable (V : Set X) [Nonempty V]

include B in
/-- The total space of `P|V` is not empty. -/
lemma nonempty_pullbackSpace_subtypeVal :
    Nonempty (pullbackSpace P (Subtype.val : V → X)) := by
  obtain ⟨v⟩ := ‹Nonempty V›
  obtain ⟨y, hy⟩ := B.surjective v.1
  exact ⟨⟨(v, y), hy⟩⟩

open scoped Classical in
/-- **The inverse of the inclusion `Y|V → Y`**: `y ↦ (P(y), y)` on `P⁻¹(V)` (a chosen point of
`Y|V` elsewhere). -/
def restrictIsoInv (y : Y) : pullbackSpace P (Subtype.val : V → X) :=
  if h : P y ∈ V then ⟨(⟨P y, h⟩, y), rfl⟩
  else Classical.choice (B.nonempty_pullbackSpace_subtypeVal V)

variable {V}

lemma restrictIsoInv_of_mem {y : Y} (h : P y ∈ V) :
    B.restrictIsoInv V y = ⟨(⟨P y, h⟩, y), rfl⟩ := dif_pos h

lemma restrictIsoInv_snd {y : Y} (h : P y ∈ V) : (B.restrictIsoInv V y).1.2 = y := by
  rw [B.restrictIsoInv_of_mem h]

lemma restrictIsoInv_fst_val {y : Y} (h : P y ∈ V) : (B.restrictIsoInv V y).1.1.1 = P y := by
  rw [B.restrictIsoInv_of_mem h]

lemma restrictIsoInv_snd_self (q : pullbackSpace P (Subtype.val : V → X)) :
    B.restrictIsoInv V q.1.2 = q := by
  have h : P q.1.2 ∈ V := by rw [pullbackSpace_subtypeVal_proj q]; exact q.1.1.2
  rw [B.restrictIsoInv_of_mem h]
  exact Subtype.ext (Prod.ext (Subtype.ext (pullbackSpace_subtypeVal_proj q)) rfl)

variable [ParacompactSpace V] [ParacompactSpace (pullbackSpace P (Subtype.val : V → X))]
  (hV : IsOpen V)

variable {B} in
/-- The charts used for the inclusion at a point `y` over `V`: a chart `c` of the atlas of `P`
around `y`, its restriction `c'` to `dom φ ∩ V` and the transported chart `c'|V` of the atlas of
`P|V`. -/
lemma exists_restrictIso_charts (y : Y) (q₀ : pullbackSpace P (Subtype.val : V → X)) :
    ∃ c ∈ B.atlas.charts, y ∈ c.toPartialEquiv.source ∧ B.IsChart (c.restrictInter hV) ∧
      (c.restrictInter hV).restrictTo B.continuous hV (c.restrictInter_source_subset hV) q₀ ∈
        (B.restrictOpen hV).atlas.charts ∧ (c.restrictInter hV).K ⊆ c.K := by
  obtain ⟨c, hc, hy⟩ := B.atlas.cover y
  refine ⟨c, hc, hy, (B.isChart_of_mem hc).restrictInter hV,
    restrictInter_restrictTo_mem hV (B.isChart_of_mem hc) q₀, ?_⟩
  rw [StrongBundleChart.restrict_K]
  exact fun _ h => h.1

/-- **`(Y|V)_{0,1}` is the part of `Y_{0,1}` over `V`.** -/
theorem mem_oneSet_restrictOpen_iff (q : pullbackSpace P (Subtype.val : V → X)) :
    q ∈ (B.restrictOpen hV).oneSet ↔ q.1.2 ∈ B.oneSet := by
  obtain ⟨c, hc, hy, -, hmem, -⟩ := exists_restrictIso_charts (B := B) hV q.1.2 q
  have hq : q.1.1.1 ∈ c.φ.source ∩ V :=
    ⟨by rw [← pullbackSpace_subtypeVal_proj q]; exact c.mem_base_of_mem_source hy,
      q.1.1.2⟩
  rw [(B.restrictOpen hV).mem_oneSet_iff hmem hq, B.mem_oneSet_iff hc hy]
  rfl

/-- The inclusion `Y|V[1] → Y[1]`. -/
def restrictIsoOne : (B.restrictOpen hV).One → B.One :=
  oneRestrict (B.restrictOpen hV) B (fun q => q.1.2)
    fun q hq => (B.mem_oneSet_restrictOpen_iff hV q).1 hq

@[simp] lemma oneVal_restrictIsoOne (w : (B.restrictOpen hV).One) :
    B.oneVal (B.restrictIsoOne hV w) = ((B.restrictOpen hV).oneVal w).1.2 := rfl

open scoped Classical in
/-- The inverse `Y[1]|V → Y|V[1]` of the inclusion (a chosen point elsewhere). -/
def restrictIsoInvOne (w : B.One) : (B.restrictOpen hV).One :=
  if h : P (B.oneVal w) ∈ V then
    (B.restrictOpen hV).oneMk ⟨(⟨P (B.oneVal w), h⟩, B.oneVal w), rfl⟩
      ((B.mem_oneSet_restrictOpen_iff hV _).2 (B.oneVal_mem w))
  else Classical.choice (B.restrictOpen hV).nonempty_one

lemma oneVal_restrictIsoInvOne {w : B.One} (h : P (B.oneVal w) ∈ V) :
    (B.restrictOpen hV).oneVal (B.restrictIsoInvOne hV w) =
      ⟨(⟨P (B.oneVal w), h⟩, B.oneVal w), rfl⟩ := by
  unfold restrictIsoInvOne; rw [dif_pos h]; rfl

/-- The inclusion `Y|V → Y` is sc-smooth on level `[0]`: in the charts `c|V` and `c` it is the
identity of `K`. -/
theorem isScSmoothMap_restrictIso_zero :
    (B.restrictOpen hV).toMPolyfold0.IsScSmoothMap B.toMPolyfold0
      (fun q : pullbackSpace P (Subtype.val : V → X) => q.1.2) := by
  refine MPolyfold.isScSmoothMap_of_forall_charts fun q => ?_
  obtain ⟨c, hc, hy, hc', hmem, -⟩ := exists_restrictIso_charts (B := B) hV q.1.2 q
  have hq : q.1.1.1 ∈ c.φ.source ∩ V :=
    ⟨by rw [← pullbackSpace_subtypeVal_proj q]; exact c.mem_base_of_mem_source hy,
      q.1.1.2⟩
  set c' := c.restrictInter hV with hc'def
  have hsub : c'.φ.source ⊆ V := c.restrictInter_source_subset hV
  set cV := c'.restrictTo B.continuous hV hsub q with hcV
  refine ⟨cV.toMChart (B.restrictOpen hV).continuous, c'.toMChart B.continuous,
    (B.restrictOpen hV).isChart_toMChart hmem, hc'.toMChart, hq, fun q' hq' => ?_, ?_⟩
  · exact StrongBundleChart.mem_source_of_mem_restrictTo_source (c := c') hq'
  · refine (isScSmoothRetractMap_id _).congr fun k hk => ?_
    change k = c' ((c'.restrictTo B.continuous hV hsub q).toPartialEquiv.symm k).1.2
    rw [StrongBundleChart.restrictTo_symm_val B.continuous hV hsub q hk]
    exact (c'.toPartialEquiv.right_inv (by rw [c'.target_eq]; exact hk)).symm

/-- The inverse of the inclusion is sc-smooth on `P⁻¹(V)`, on level `[0]`. -/
theorem isScSmoothOn_restrictIsoInv_zero :
    B.toMPolyfold0.IsScSmoothOn (B.restrictOpen hV).toMPolyfold0 (B.restrictIsoInv V)
      (P ⁻¹' V) := by
  refine MPolyfold.isScSmoothOn_of_forall_charts (hV.preimage B.continuous) fun y hyV => ?_
  obtain ⟨c, hc, hy, hc', hmem, -⟩ :=
    exists_restrictIso_charts (B := B) hV y (B.restrictIsoInv V y)
  set c' := c.restrictInter hV with hc'def
  have hsub : c'.φ.source ⊆ V := c.restrictInter_source_subset hV
  set cV := c'.restrictTo B.continuous hV hsub (B.restrictIsoInv V y) with hcV
  refine ⟨c'.toMChart B.continuous, cV.toMChart (B.restrictOpen hV).continuous, hc'.toMChart,
    (B.restrictOpen hV).isChart_toMChart hmem, ⟨c.mem_base_of_mem_source hy, hyV⟩,
    fun z hz => hz.2, fun z hz => ?_, ?_⟩
  · change (B.restrictIsoInv V z).1.1.1 ∈ c'.φ.source
    rw [B.restrictIsoInv_fst_val hz.2]; exact hz
  · refine (isScSmoothRetractMap_id _).congr fun k hk => ?_
    have hk' : k ∈ c'.toPartialEquiv.target := by rw [c'.target_eq]; exact hk
    have hz : P (c'.toPartialEquiv.symm k) ∈ V := (c'.toPartialEquiv.map_target hk').2
    change k = c' (B.restrictIsoInv V (c'.toPartialEquiv.symm k)).1.2
    rw [B.restrictIsoInv_snd hz]
    exact (c'.toPartialEquiv.right_inv hk').symm

/-- The inclusion `Y|V[1] → Y[1]` is sc-smooth: in the charts `(c|V)[1]` and `c[1]` it is the
identity of `K[1]`. -/
theorem isScSmoothMap_restrictIsoOne :
    (B.restrictOpen hV).toMPolyfold1.IsScSmoothMap B.toMPolyfold1 (B.restrictIsoOne hV) := by
  refine MPolyfold.isScSmoothMap_of_forall_charts fun w => ?_
  set q := (B.restrictOpen hV).oneVal w with hqdef
  obtain ⟨c, hc, hy, hc', hmem, hK⟩ := exists_restrictIso_charts (B := B) hV q.1.2 q
  have hq : q.1.1.1 ∈ c.φ.source ∩ V :=
    ⟨by rw [← pullbackSpace_subtypeVal_proj q]; exact c.mem_base_of_mem_source hy,
      q.1.1.2⟩
  set c' := c.restrictInter hV with hc'def
  have hsub : c'.φ.source ⊆ V := c.restrictInter_source_subset hV
  set cV := c'.restrictTo B.continuous hV hsub q with hcV
  refine ⟨oneChart hmem w, oneChart hc (B.restrictIsoOne hV w),
    (B.restrictOpen hV).isChart_oneChart hmem w, B.isChart_oneChart hc _, hq,
    fun w' hw' => ?_, ?_⟩
  · have h1 : ((B.restrictOpen hV).oneVal w').1.2 ∈ c'.toPartialEquiv.source :=
      StrongBundleChart.mem_source_of_mem_restrictTo_source (c := c') hw'
    exact c.mem_source_of_mem_base (c'.mem_base_of_mem_source h1).1
  · have hmaps : MapsTo (_root_.id : (c.φ.model.E.prod c.F.shift) 0 → _)
        (strongShiftOne cV.K) (strongShiftOne c.K) := fun p hp => hK hp
    refine ((isScSmoothRetractMap_id _).mono_target hmaps).congr fun p hp => ?_
    have hp' : (p.1, c.F.toBase 1 p.2) ∈ c'.K := hp
    change p = c.liftOne ((B.restrictOpen hV).oneVal ((oneChart hmem w).symm p)).1.2
    rw [oneChart_symm_apply hmem w hp]
    have e := StrongBundleChart.restrictTo_symm_val B.continuous hV hsub q hp'
    exact (liftOne_symm (c := c) (z := p) (hK hp')).symm.trans (congrArg c.liftOne e.symm)

/-- The inverse of the inclusion is sc-smooth over `V`, on level `[1]`. -/
theorem isScSmoothOn_restrictIsoInvOne :
    B.toMPolyfold1.IsScSmoothOn (B.restrictOpen hV).toMPolyfold1 (B.restrictIsoInvOne hV)
      ((P ∘ B.oneVal) ⁻¹' V) := by
  have hO : IsOpen ((P ∘ B.oneVal) ⁻¹' V) :=
    hV.preimage (B.continuous.comp B.continuous_oneVal)
  refine MPolyfold.isScSmoothOn_of_forall_charts hO fun w hwV => ?_
  obtain ⟨c, hc, hy, hc', hmem, -⟩ :=
    exists_restrictIso_charts (B := B) hV (B.oneVal w) (B.restrictIsoInv V (B.oneVal w))
  set c' := c.restrictInter hV with hc'def
  have hsub : c'.φ.source ⊆ V := c.restrictInter_source_subset hV
  set cV := c'.restrictTo B.continuous hV hsub (B.restrictIsoInv V (B.oneVal w)) with hcV
  set s : Set B.One := (oneChart hc w).source ∩ (P ∘ B.oneVal) ⁻¹' V with hs
  have hso : IsOpen s := (oneChart hc w).isOpen_source.inter hO
  have hval : ∀ z ∈ s, cV.liftOne ((B.restrictOpen hV).oneVal (B.restrictIsoInvOne hV z)) =
      c.liftOne (B.oneVal z) := fun z hz => by
    rw [B.oneVal_restrictIsoInvOne hV hz.2]; rfl
  refine ⟨(oneChart hc w).restrict inter_subset_left hso,
    oneChart hmem (B.restrictIsoInvOne hV w),
    MPolyfold.IsChart.restrict _ (B.isChart_oneChart hc w) _ _,
    (B.restrictOpen hV).isChart_oneChart hmem _, ⟨hy, hwV⟩, fun z hz => hz.2,
    fun z hz => ?_, ?_⟩
  · change ((B.restrictOpen hV).oneVal (B.restrictIsoInvOne hV z)).1.1.1 ∈ c'.φ.source
    rw [B.oneVal_restrictIsoInvOne hV hz.2]
    exact ⟨c.mem_base_of_mem_source hz.1, hz.2⟩
  · have hmaps : MapsTo (_root_.id : (c.φ.model.E.prod c.F.shift) 0 → _)
        ((oneChart hc w) '' s) (strongShiftOne cV.K) := by
      rintro _ ⟨z, hz, rfl⟩
      have hz1 : (c (B.oneVal z)).2 ∈ range (c.F.toBase 1) :=
        (B.mem_oneSet_iff hc hz.1).1 (B.oneVal_mem z)
      change ((c.liftOne (B.oneVal z)).1, c.F.toBase 1 (c.liftOne (B.oneVal z)).2) ∈ c'.K
      rw [c.toBase_liftOne hz1, ← c'.image_source]
      exact ⟨B.oneVal z, ⟨c.mem_base_of_mem_source hz.1, hz.2⟩, rfl⟩
    refine ((isScSmoothRetractMap_id _).mono_target hmaps).congr ?_
    rintro _ ⟨z, hz, rfl⟩
    change oneChart hc w z = cV.liftOne ((B.restrictOpen hV).oneVal
      (B.restrictIsoInvOne hV ((oneChart hc w).symm (oneChart hc w z))))
    rw [(oneChart hc w).symm_apply_apply hz.1, hval z hz]
    rfl

/-- **The inclusion `Y|V → Y` of the restriction of a strong bundle to an open subset `V` of the
base, as a local strong bundle isomorphism** from `P|V` (over all of `V`) onto `P` over `V`: the
base map is the inclusion `V → X`, the bundle map is `(v, y) ↦ y`; the inverses are `x ↦ x` and
`y ↦ (P(y), y)` over `V`. -/
def restrictIso : LocalIso (B.restrictOpen hV) B univ V where
  ϕ := Subtype.val
  g := MPolyfold.openRetraction V
  Φ := fun q => q.1.2
  Ψ := B.restrictIsoInv V
  Φ₁ := B.restrictIsoOne hV
  Ψ₁ := B.restrictIsoInvOne hV
  base := MPolyfold.isScDiffeoOn_subtypeVal hV
  zero := by
    rw [preimage_univ]
    exact ⟨B.isScSmoothMap_restrictIso_zero hV, B.isScSmoothOn_restrictIsoInv_zero hV,
      fun q _ => by
        rw [mem_preimage, pullbackSpace_subtypeVal_proj q]; exact q.1.1.2,
      fun _ _ => mem_univ _, fun q _ => B.restrictIsoInv_snd_self q,
      fun y hy => B.restrictIsoInv_snd hy⟩
  one := by
    rw [preimage_univ]
    exact ⟨B.isScSmoothMap_restrictIsoOne hV, B.isScSmoothOn_restrictIsoInvOne hV,
      fun w _ => by
        change P ((B.restrictOpen hV).oneVal w).1.2 ∈ V
        rw [pullbackSpace_subtypeVal_proj ((B.restrictOpen hV).oneVal w)]
        exact ((B.restrictOpen hV).oneVal w).1.1.2,
      fun _ _ => mem_univ _,
      fun w _ => (B.restrictOpen hV).oneVal_injective (by
        have h : P ((B.restrictOpen hV).oneVal w).1.2 ∈ V := by
          rw [pullbackSpace_subtypeVal_proj ((B.restrictOpen hV).oneVal w)]
          exact ((B.restrictOpen hV).oneVal w).1.1.2
        rw [B.oneVal_restrictIsoInvOne hV (w := B.restrictIsoOne hV w) h]
        exact Subtype.ext (Prod.ext
          (Subtype.ext (pullbackSpace_subtypeVal_proj _)) rfl)),
      fun w hw => B.oneVal_injective (by
        rw [oneVal_restrictIsoOne, B.oneVal_restrictIsoInvOne hV hw])⟩
  covers q _ := q.2
  oneVal_Φ₁ _ _ := rfl
  fiber_linear v x' _ hx' := by
    subst hx'
    exact (pullbackFiberCLE (P := P) (f := (Subtype.val : V → X)) v).toLinearMap.isLinear

@[simp] lemma restrictIso_ϕ : (B.restrictIso hV).ϕ = Subtype.val := rfl

@[simp] lemma restrictIso_Φ_apply (q : pullbackSpace P (Subtype.val : V → X)) :
    (B.restrictIso hV).Φ q = q.1.2 := rfl

lemma restrictIso_g : (B.restrictIso hV).g = MPolyfold.openRetraction V := rfl

lemma restrictIso_Ψ : (B.restrictIso hV).Ψ = B.restrictIsoInv V := rfl

lemma restrictIso_g_of_mem {x : X} (hx : x ∈ V) : (B.restrictIso hV).g x = ⟨x, hx⟩ :=
  MPolyfold.openRetraction_of_mem hx

lemma restrictIso_Ψ_of_mem {y : Y} (hy : P y ∈ V) :
    (B.restrictIso hV).Ψ y = ⟨(⟨P y, hy⟩, y), rfl⟩ :=
  B.restrictIsoInv_of_mem hy

@[simp] lemma restrictIso_Ψ_snd {y : Y} (hy : P y ∈ V) : ((B.restrictIso hV).Ψ y).1.2 = y :=
  B.restrictIsoInv_snd hy

@[simp] lemma restrictIso_Ψ_fst_val {y : Y} (hy : P y ∈ V) :
    ((B.restrictIso hV).Ψ y).1.1.1 = P y :=
  B.restrictIsoInv_fst_val hy

@[simp] lemma restrictIso_g_val {x : X} (hx : x ∈ V) : ((B.restrictIso hV).g x).1 = x := by
  rw [B.restrictIso_g_of_mem hV hx]

@[simp] lemma oneVal_restrictIso_Φ₁ (w : (B.restrictOpen hV).One) :
    B.oneVal ((B.restrictIso hV).Φ₁ w) = ((B.restrictOpen hV).oneVal w).1.2 := rfl

/-- **The restriction `f|V` of a section is the pull-back of `f` along the inclusion**
`Y|V → Y`: `f|V = Ψ ∘ f ∘ ϕ`. -/
theorem restrictSection_eqOn_restrictIso {f : X → Y} (hf : IsSection P f) :
    EqOn (restrictSection P V f hf) ((B.restrictIso hV).Ψ ∘ f ∘ (B.restrictIso hV).ϕ) univ := by
  intro v _
  have h : P (f v.1) ∈ V := by rw [hf v.1]; exact v.2
  change restrictSection P V f hf v = B.restrictIsoInv V (f v.1)
  rw [B.restrictIsoInv_of_mem h]
  exact Subtype.ext (Prod.ext (Subtype.ext (hf v.1).symm) rfl)

end Restrict

/-! ### Two restrictions over the intersection of their bases -/

section Inter

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] (B : StrongBundle PX P)
  {W : Set X} [Nonempty W] [ParacompactSpace W]
  [ParacompactSpace (pullbackSpace P (Subtype.val : W → X))] (hW : IsOpen W)
  {V : Set X} [Nonempty V] [ParacompactSpace V]
  [ParacompactSpace (pullbackSpace P (Subtype.val : V → X))] (hV : IsOpen V)

/-- **The identification of two restrictions `P|W`, `P|V` over `W ∩ V`**, as a local strong
bundle isomorphism from `P|W` over `{w ∈ W | w ∈ V}` onto `P|V` over `{v ∈ V | v ∈ W}`: the
inclusion `Y|W → Y` followed by the inverse of the inclusion `Y|V → Y`. -/
def restrictIsoInter :
    LocalIso (B.restrictOpen hW) (B.restrictOpen hV) {w : W | w.1 ∈ V} {v : V | v.1 ∈ W} :=
  ((B.restrictIso hW).trans (B.restrictIso hV).symm).ofEq (univ_inter _) (univ_inter _)

lemma restrictIsoInter_ϕ :
    (B.restrictIsoInter hW hV).ϕ = MPolyfold.openRetraction V ∘ Subtype.val := rfl

lemma restrictIsoInter_g :
    (B.restrictIsoInter hW hV).g = MPolyfold.openRetraction W ∘ Subtype.val := rfl

lemma restrictIsoInter_ϕ_of_mem {w : W} (hw : w.1 ∈ V) :
    (B.restrictIsoInter hW hV).ϕ w = ⟨w.1, hw⟩ :=
  MPolyfold.openRetraction_of_mem hw

lemma restrictIsoInter_g_of_mem {v : V} (hv : v.1 ∈ W) :
    (B.restrictIsoInter hW hV).g v = ⟨v.1, hv⟩ :=
  MPolyfold.openRetraction_of_mem hv

@[simp] lemma restrictIsoInter_Φ_apply (q : pullbackSpace P (Subtype.val : W → X)) :
    (B.restrictIsoInter hW hV).Φ q = B.restrictIsoInv V q.1.2 := rfl

@[simp] lemma restrictIsoInter_Ψ_apply (q : pullbackSpace P (Subtype.val : V → X)) :
    (B.restrictIsoInter hW hV).Ψ q = B.restrictIsoInv W q.1.2 := rfl

lemma restrictIsoInter_Φ_of_mem {q : pullbackSpace P (Subtype.val : W → X)}
    (hq : q.1.1.1 ∈ V) :
    (B.restrictIsoInter hW hV).Φ q =
      ⟨(⟨P q.1.2, by rw [pullbackSpace_subtypeVal_proj q]; exact hq⟩, q.1.2), rfl⟩ :=
  B.restrictIsoInv_of_mem _

lemma restrictIsoInter_Ψ_of_mem {q : pullbackSpace P (Subtype.val : V → X)}
    (hq : q.1.1.1 ∈ W) :
    (B.restrictIsoInter hW hV).Ψ q =
      ⟨(⟨P q.1.2, by rw [pullbackSpace_subtypeVal_proj q]; exact hq⟩, q.1.2), rfl⟩ :=
  B.restrictIsoInv_of_mem _

/-- **The restrictions `f|W` and `f|V` of a section correspond** under the identification of
`P|W` and `P|V` over `W ∩ V`: `f|W = Ψ ∘ f|V ∘ ϕ` on `{w ∈ W | w ∈ V}`. -/
theorem restrictSection_eqOn_restrictIsoInter {f : X → Y} (hf : IsSection P f) :
    EqOn (restrictSection P W f hf)
      ((B.restrictIsoInter hW hV).Ψ ∘ restrictSection P V f hf ∘ (B.restrictIsoInter hW hV).ϕ)
      {w : W | w.1 ∈ V} := by
  intro w hw
  have h : P (f w.1) ∈ W := by rw [hf w.1]; exact w.2
  have e : (B.restrictIsoInter hW hV).ϕ w = ⟨w.1, hw⟩ := B.restrictIsoInter_ϕ_of_mem hW hV hw
  change restrictSection P W f hf w =
    B.restrictIsoInv W (restrictSection P V f hf ((B.restrictIsoInter hW hV).ϕ w)).1.2
  rw [e]
  change restrictSection P W f hf w = B.restrictIsoInv W (f w.1)
  rw [B.restrictIsoInv_of_mem h]
  exact Subtype.ext (Prod.ext (Subtype.ext (hf w.1).symm) rfl)

/-- **The inclusion `Y|W → Y|V` for open `W ⊆ V`**, as a local strong bundle isomorphism from
`P|W` (over all of `W`) onto `P|V` over `{v ∈ V | v ∈ W}`. -/
def restrictIsoOf (hWV : W ⊆ V) :
    LocalIso (B.restrictOpen hW) (B.restrictOpen hV) univ {v : V | v.1 ∈ W} :=
  (B.restrictIsoInter hW hV).ofEq (eq_univ_of_forall fun w => hWV w.2) rfl

@[simp] lemma restrictIsoOf_ϕ (hWV : W ⊆ V) (w : W) :
    (B.restrictIsoOf hW hV hWV).ϕ w = ⟨w.1, hWV w.2⟩ :=
  MPolyfold.openRetraction_of_mem (hWV w.2)

lemma restrictIsoOf_g_of_mem (hWV : W ⊆ V) {v : V} (hv : v.1 ∈ W) :
    (B.restrictIsoOf hW hV hWV).g v = ⟨v.1, hv⟩ :=
  MPolyfold.openRetraction_of_mem hv

@[simp] lemma restrictIsoOf_Φ_apply (hWV : W ⊆ V)
    (q : pullbackSpace P (Subtype.val : W → X)) :
    (B.restrictIsoOf hW hV hWV).Φ q =
      ⟨(⟨P q.1.2, by
        rw [pullbackSpace_subtypeVal_proj q]; exact hWV q.1.1.2⟩, q.1.2), rfl⟩ :=
  B.restrictIsoInv_of_mem _

@[simp] lemma restrictIsoOf_Ψ_apply (hWV : W ⊆ V)
    (q : pullbackSpace P (Subtype.val : V → X)) :
    (B.restrictIsoOf hW hV hWV).Ψ q = B.restrictIsoInv W q.1.2 := rfl

/-- For `W ⊆ V`: `f|W = Ψ ∘ f|V ∘ ϕ` on all of `W`. -/
theorem restrictSection_eqOn_restrictIsoOf (hWV : W ⊆ V) {f : X → Y} (hf : IsSection P f) :
    EqOn (restrictSection P W f hf)
      ((B.restrictIsoOf hW hV hWV).Ψ ∘ restrictSection P V f hf ∘ (B.restrictIsoOf hW hV hWV).ϕ)
      univ :=
  fun w _ => B.restrictSection_eqOn_restrictIsoInter hW hV hf (hWV w.2)

end Inter

/-! ### Charts over the whole base of a restriction -/

section ChartDomain

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

/-- **The restriction of a strong bundle to an open subset of the base domain of a chart has a
chart over its whole base**: for a chart `c` of the atlas of `P` and an open nonempty
`W ⊆ dom φ_c`, the chart `c` restricted to `W` and transported is a chart of the atlas of `P|W`
with base domain `W`. -/
theorem exists_chart_source_eq_univ_restrictOpen_of_subset {c : StrongBundleChart PX P}
    (hc : c ∈ B.atlas.charts) {W : Set X} [Nonempty W] [ParacompactSpace W]
    [ParacompactSpace (pullbackSpace P (Subtype.val : W → X))] (hW : IsOpen W)
    (hWc : W ⊆ c.φ.source) :
    ∃ c' ∈ (B.restrictOpen hW).atlas.charts, c'.φ.source = univ := by
  obtain ⟨q₀⟩ := B.nonempty_pullbackSpace_subtypeVal W
  exact ⟨(c.restrictInter hW).restrictTo B.continuous hW (c.restrictInter_source_subset hW) q₀,
    restrictInter_restrictTo_mem hW (B.isChart_of_mem hc) q₀,
    eq_univ_of_forall fun w => ⟨hWc w.2, w.2⟩⟩

end ChartDomain

end StrongBundle

end Polyfold
