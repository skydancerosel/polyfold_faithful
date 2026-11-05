import Polyfold.Chapter3.RestrictOpen
import Polyfold.Chapter3.SectionCompactness

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.1 and §3.6,
Definitions 3.11, 3.50, 3.51 and §6.1, for the restriction `P|V` of a strong bundle to an open
subset: the germ data of an sc-Fredholm section restrict to `P|V`, and the Fredholm index of
the linearization at a zero (`IsLinOfIndex`) is the same for `P` and for `P|V`.  Round-trip item
V3.98 (a); Findings, Chapter 3, items 360–369.

# Germ data and the index on the restriction `P|V`

## The text, paraphrased

Definition 3.11 is local: the data of an sc-Fredholm germ at `x₀` live in a chart centred at
`x₀`, on a germ of neighbourhoods of `0`; so does the index of the linearization at a zero.
Restricting the bundle to an open subset `V ∋ x₀` changes nothing — the text never remarks on it.

## What is formalized

* **Germ data on a smaller domain**: `Polyfold.IsFillingGerm.of_subset`,
  `Polyfold.IsScPlusGerm.of_subset`, `Polyfold.ConjugationData.ofSubset` and
  `Polyfold.IsConjugateToBasicGerm.of_subset`: the data of Definition 3.11 on a relatively open
  `U` restrict to every relatively open `U₀ ⊆ U` containing `0` (the germs are intersected with
  `U₀`, the strong bundle isomorphism `Ψ` is restricted to `U₀ ◁ F → ψ(U₀) ◁ F'`, the basic germ is
  shrunk to the points `ψ'` maps into `U₀`, `ConjugationData.shrinkGerm`).
* **The restricted chart** `c.restrictInter hV` (`StrongBundleChart.restrict` to `dom φ ∩ V`)
  keeps the germ data (`IsScFredholmGerm.restrictInter`, `IsScFredholmGermTame.restrictInter`;
  it is tame when `c` is, `StrongBundle.IsTameChart.restrictInter`).
* **Transport to `P|V`**: `StrongBundle.IsScFredholmGerm.restrictOpen`,
  `IsScFredholmGermTame.restrictOpen`, `IsScFredholmSection.restrictOpen`,
  `IsScFredholmSectionTame.restrictOpen` (**an sc-Fredholm section with tame germ data restricts
  to one on `P|V`**).
* **The index**: `StrongBundle.isLinOfIndex_restrictOpen_of_conjugationData` (the index of a
  germ datum, `dim Pn − dim Q`, read on `P|V`), `IsLinOfIndex.restrictOpen` and
  `IsLinOfIndex.of_restrictOpen` (**at a zero, `f'(x)` has index `i` in every chart of `P` iff
  `(f|V)'(x)` has index `i` in every chart of `P|V`**), `restrictSection_sectionAdd` and
  `IsIndexAt.restrictOpen` (**Definition 6.1 restricts**: a global sc⁺-section `s` restricts).

## What the text leaves implicit, and the choices made

* Restricting `U` to `U₀` in Definition 3.11 is harmless, but the strong bundle isomorphism of
  the conjugation is a map of the whole `U ◁ F`, so its restriction needs the relatively open
  image `ψ(U₀) = U' ∩ ψ'⁻¹(U₀)` (continuity of `ψ'`) and the shrinking of the basic germ to
  `G ∩ ψ'⁻¹(U₀)` (`shrinkGerm`), as in `BasicGermShrink.lean`.
* The transport of the index between `P` and `P|V` goes through the germ datum (the index is
  `dim Pn − dim Q` in every chart of either bundle, `isLinOfIndex_of_conjugationData`), not
  through a comparison of the charts of `P|V` with those of `P`: a chart of `P|V` need not come
  from a chart of `P`.
-/

open Set Filter Topology Function Module ContinuousLinearMap
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

/-! ### Germ data on a smaller domain -/

section GermSubset

variable {E F : ScBanach} {C U U₀ : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

open StrongRetr

/-- The derivative of `r` at `0` does not depend on the (relatively open) domain. -/
lemma scDeriv_r_of_subset (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (hU₀ : IsRelOpenInQuadrant E C U₀) (hR₀ : IsStrongBundleRetraction U₀ R) (hsub : U₀ ⊆ U)
    (h0₀ : (0 : E 0) ∈ U₀) : scDeriv U₀ (r R) 0 = scDeriv U (r R) 0 := by
  refine scDeriv_eq_of_eqOn_relOpen hU₀ (hR₀.baseRetraction hU₀).isSc1 (hR.baseRetraction hU).isSc1
    subset_rfl hsub (fun _ _ => rfl) ?_
  rw [ScBanach.mem_lvlSet, map_zero]; exact h0₀

/-- A filling germ restricts to a smaller relatively open domain `U₀ ∋ 0`. -/
theorem IsFillingGerm.of_subset (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (hU₀ : IsRelOpenInQuadrant E C U₀) (hR₀ : IsStrongBundleRetraction U₀ R) (hsub : U₀ ⊆ U)
    (h0 : (0 : E 0) ∈ U) (h0₀ : (0 : E 0) ∈ U₀) {fb g : E 0 → F 0}
    (hfill : IsFillingGerm hU hR h0 fb g) : IsFillingGerm hU₀ hR₀ h0₀ fb g where
  eq_on := hfill.eq_on.mono fun _ hx hxO => hx (image_mono hsub hxO)
  mem_of_fixed := by
    filter_upwards [hfill.mem_of_fixed] with y hy hyU₀ hfix
    have hyO := hy (hsub hyU₀) hfix
    exact ⟨y, hyU₀, r_eq_self hR hyO⟩
  germ := by
    obtain ⟨G, hG, hgsm, Dk, hDk, Φ, hΦ⟩ := hfill.germ
    have hC : IsQuadrantLike E C := hU.isPartialQuadrant.isQuadrantLike
    set G₀ := G.inter (ScNbhdGerm.ofSet hU₀.relOpen h0₀) with hG₀
    have hsub' : ∀ m, G₀.U m ⊆ G.U m := fun m => ScNbhdGerm.inter_subset_left _ _ m
    refine ⟨G₀, fun x hx => ?_, hgsm.mono hC hsub', Dk, hDk.mono hsub', ?_⟩
    · have := (ScNbhdGerm.inter_subset_right G _ 0) hx
      simpa using this
    · have hD := scDeriv_r_of_subset hU hR hU₀ hR₀ hsub h0₀
      have hρ : ρCLM hR₀ h0₀ = ρCLM hR h0 := ContinuousLinearMap.ext fun _ => rfl
      rw [hD, hρ]
      exact ⟨Φ, hΦ⟩

/-- A local sc⁺-section germ restricts to a smaller relatively open domain `U₀ ∋ 0`. -/
theorem IsScPlusGerm.of_subset (hU : IsRelOpenInQuadrant E C U)
    (hU₀ : IsRelOpenInQuadrant E C U₀) (h0₀ : (0 : E 0) ∈ U₀) {s : E 0 → F 1}
    (hs : IsScPlusGerm C U s) : IsScPlusGerm C U₀ s := by
  obtain ⟨G, hG, hsm⟩ := hs
  have hC : IsQuadrantLike E C := hU.isPartialQuadrant.isQuadrantLike
  refine ⟨G.inter (ScNbhdGerm.ofSet hU₀.relOpen h0₀), fun x hx => ?_,
    hsm.mono hC fun m => ScNbhdGerm.inter_subset_left _ _ m⟩
  have := (ScNbhdGerm.inter_subset_right G _ 0) hx
  simpa using this

namespace ConjugationData

variable {k : E 0 → F 0} (d : ConjugationData U k)

/-- The image `ψ(U₀) = U' ∩ ψ'⁻¹(U₀)` of `U₀ ⊆ U` under the base map of the conjugation. -/
def subsetImage (U₀ : Set (E 0)) : Set ((ScBanach.paramProd d.Pn d.W) 0) :=
  {p ∈ d.U' | IsStrongBundleMap.base d.Ψ' p ∈ U₀}

lemma subsetImage_subset (U₀ : Set (E 0)) : d.subsetImage U₀ ⊆ d.U' := fun _ hp => hp.1

/-- `ψ(U₀)` is relatively open in the quadrant `C̃ ⊕ W` when `U₀` is relatively open in `C`. -/
lemma subsetImage_relOpen (hU : IsRelOpenInQuadrant E C U) (hU₀ : IsRelOpenInQuadrant E C U₀)
    (hsub : U₀ ⊆ U) : IsRelOpenInQuadrant (ScBanach.paramProd d.Pn d.W) (d.Ct ×ˢ univ)
      (d.subsetImage U₀) := by
  refine ⟨d.relOpen.isPartialQuadrant, ?_⟩
  obtain ⟨O₀, hO₀, hU₀eq⟩ := hU₀.relOpen
  obtain ⟨O₁, hO₁, hU'eq⟩ := d.relOpen.relOpen
  have hcont : ContinuousOn (IsStrongBundleMap.base d.Ψ') d.U' :=
    (d.iso.invFun.base_isScSmooth d.relOpen).isSc1.isSc0.continuousOn_base
  obtain ⟨u, hu, huU⟩ := continuousOn_iff'.1 hcont O₀ hO₀
  have hUC : U ⊆ C := by
    obtain ⟨O, -, hUO⟩ := hU.relOpen
    rw [hUO]; exact inter_subset_right
  refine ⟨u ∩ O₁, hu.inter hO₁, ?_⟩
  ext p
  constructor
  · rintro ⟨hp, hp₀⟩
    have : p ∈ IsStrongBundleMap.base d.Ψ' ⁻¹' O₀ ∩ d.U' := by
      refine ⟨?_, hp⟩
      rw [hU₀eq] at hp₀; exact hp₀.1
    rw [huU] at this
    have hpC : p ∈ d.Ct ×ˢ univ := by
      rw [hU'eq] at hp; exact hp.2
    exact ⟨⟨this.1, by rw [hU'eq] at hp; exact hp.1⟩, hpC⟩
  · rintro ⟨⟨hpu, hpO₁⟩, hpC⟩
    have hp : p ∈ d.U' := by rw [hU'eq]; exact ⟨hpO₁, hpC⟩
    refine ⟨hp, ?_⟩
    have : p ∈ u ∩ d.U' := ⟨hpu, hp⟩
    rw [← huU] at this
    rw [hU₀eq]
    exact ⟨this.1, hUC (d.iso.invFun.base_mem hp)⟩

/-- The strong bundle isomorphism of the conjugation restricted to `U₀ ◁ F → ψ(U₀) ◁ F'`. -/
theorem iso_subset (hU : IsRelOpenInQuadrant E C U) (hU₀ : IsRelOpenInQuadrant E C U₀)
    (hsub : U₀ ⊆ U) : IsStrongBundleIso U₀ (d.subsetImage U₀) d.Ψ d.Ψ' := by
  have hrel := d.subsetImage_relOpen hU hU₀ hsub
  refine ⟨?_, ?_, fun p hp => d.iso.left_inv p ⟨hsub hp.1, hp.2⟩,
    fun p hp => d.iso.right_inv p ⟨hp.1.1, hp.2⟩⟩
  · refine ⟨fun p hp => ⟨⟨(d.iso.toFun.mapsTo ⟨hsub hp.1, hp.2⟩).1, ?_⟩, mem_univ _⟩,
      fun u hu => d.iso.toFun.fst_independent u (hsub hu),
      fun u hu => d.iso.toFun.fiber_linear u (hsub hu),
      fun m k hk u hu => d.iso.toFun.preserves_filtration m k hk u (hsub hu),
      d.iso.toFun.isScSmooth_zero.of_subset (hU₀.prod_univ _).isScDomain
        (prod_mono hsub subset_rfl),
      d.iso.toFun.isScSmooth_one.of_subset (hU₀.prod_univ _).isScDomain
        (prod_mono hsub subset_rfl)⟩
    -- `ψ'(ψ(p₁)) = p₁`
    have h1 := d.iso.invFun.fst_independent (d.Ψ p).1 (d.iso.toFun.mapsTo ⟨hsub hp.1, hp.2⟩).1
      0 (d.Ψ p).2
    have h2 := d.iso.left_inv p ⟨hsub hp.1, hp.2⟩
    change (d.Ψ' ((d.Ψ p).1, 0)).1 ∈ U₀
    rw [h1, Prod.mk.eta, h2]
    exact hp.1
  · refine ⟨fun p hp => ⟨?_, mem_univ _⟩,
      fun u hu => d.iso.invFun.fst_independent u hu.1,
      fun u hu => d.iso.invFun.fiber_linear u hu.1,
      fun m k hk u hu => d.iso.invFun.preserves_filtration m k hk u hu.1,
      d.iso.invFun.isScSmooth_zero.of_subset (hrel.prod_univ _).isScDomain
        (prod_mono (fun _ h => h.1) subset_rfl),
      d.iso.invFun.isScSmooth_one.of_subset (hrel.prod_univ _).isScDomain
        (prod_mono (fun _ h => h.1) subset_rfl)⟩
    have h1 := d.iso.invFun.fst_independent p.1 hp.1.1 p.2 0
    rw [Prod.mk.eta] at h1
    change (d.Ψ' p).1 ∈ U₀
    rw [h1]
    exact hp.1.2

/-- **Conjugation data restricted to a smaller domain** `U₀ ⊆ U`, `0 ∈ U₀` relatively open: the
same `Pn`, `Q`, `W`, `Ψ`, `h`, `B`, the domain `ψ(U₀)` and the basic germ on `G ∩ ψ'⁻¹(U₀)`. -/
def ofSubset (hU : IsRelOpenInQuadrant E C U) (h0 : (0 : E 0) ∈ U)
    (hU₀ : IsRelOpenInQuadrant E C U₀) (hsub : U₀ ⊆ U) (h0₀ : (0 : E 0) ∈ U₀) :
    ConjugationData U₀ k where
  Pn := d.Pn
  Q := d.Q
  W := d.W
  Ct := d.Ct
  U' := d.subsetImage U₀
  Ψ := d.Ψ
  Ψ' := d.Ψ'
  G := d.shrinkGerm hU h0 (ScNbhdGerm.ofSet hU₀.relOpen h0₀)
  h := d.h
  Bc := d.Bc
  quadrant := d.quadrant
  relOpen := d.subsetImage_relOpen hU hU₀ hsub
  iso := d.iso_subset hU hU₀ hsub
  base_zero := d.base_zero
  germ_subset := fun x hx => ⟨d.germ_subset hx.1, by simpa using hx.2⟩
  basic := d.basic_shrinkGerm hU h0 _
  conj := d.conj.mono fun u hu huU₀ => hu (hsub huU₀)

@[simp] lemma ofSubset_Pn (hU : IsRelOpenInQuadrant E C U) (h0 : (0 : E 0) ∈ U)
    (hU₀ : IsRelOpenInQuadrant E C U₀) (hsub : U₀ ⊆ U) (h0₀ : (0 : E 0) ∈ U₀) :
    (d.ofSubset hU h0 hU₀ hsub h0₀).Pn = d.Pn := rfl

@[simp] lemma ofSubset_Q (hU : IsRelOpenInQuadrant E C U) (h0 : (0 : E 0) ∈ U)
    (hU₀ : IsRelOpenInQuadrant E C U₀) (hsub : U₀ ⊆ U) (h0₀ : (0 : E 0) ∈ U₀) :
    (d.ofSubset hU h0 hU₀ hsub h0₀).Q = d.Q := rfl

end ConjugationData

/-- Conjugation to a basic germ restricts to a smaller relatively open domain `U₀ ∋ 0`. -/
theorem IsConjugateToBasicGerm.of_subset (hU : IsRelOpenInQuadrant E C U) (h0 : (0 : E 0) ∈ U)
    (hU₀ : IsRelOpenInQuadrant E C U₀) (hsub : U₀ ⊆ U) (h0₀ : (0 : E 0) ∈ U₀) {k : E 0 → F 0}
    (h : IsConjugateToBasicGerm U k) : IsConjugateToBasicGerm U₀ k := by
  obtain ⟨d⟩ := isConjugateToBasicGerm_iff_nonempty.1 h
  exact isConjugateToBasicGerm_iff_nonempty.2 ⟨d.ofSubset hU h0 hU₀ hsub h0₀⟩

end GermSubset

/-! ### Germ data in the restricted chart `c|dom φ ∩ V` -/

section ChartRestrict

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {V : Set X} (hV : IsOpen V) {c : StrongBundleChart PX P} {f : X → Y}

open StrongRetr

omit [T2Space Y] [ParacompactSpace Y] in
/-- `0 ∈ U` for the restricted chart `c|dom φ ∩ V` centred at `x ∈ V`. -/
lemma StrongBundleChart.zero_mem_restrictInter_U {x : X} (hxV : x ∈ c.φ.source) (hφ0 : c.φ x = 0)
    (hxV' : x ∈ V) : (0 : c.φ.model.E 0) ∈ (c.restrictInter hV).U := by
  rw [c.restrictInter_U]
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := hφ0 ▸ c.φ.mapsTo_model x hxV
  refine ⟨mem_U_of_mem_O c.isRetraction (c.r_image ▸ h0O), ?_⟩
  change r c.R 0 ∈ c.φ '' (c.φ.source ∩ V)
  rw [r_eq_self c.isRetraction (c.r_image ▸ h0O)]
  exact ⟨x, ⟨hxV, hxV'⟩, hφ0⟩

omit [T2Space Y] [ParacompactSpace Y] in
/-- The principal part of `f` in `c|dom φ ∩ V` is that in `c`. -/
lemma StrongBundleChart.principal_restrictInter (f : X → Y) :
    (c.restrictInter hV).principal f = c.principal f := rfl

omit [T2Space Y] [ParacompactSpace Y] in
/-- The relatively open domain of the restricted chart is contained in that of the chart. -/
lemma StrongBundleChart.restrictInter_relOpen :
    IsRelOpenInQuadrant c.φ.model.E c.φ.model.C (c.restrictInter hV).U :=
  (c.restrictInter hV).relOpen

/-- **The germ data of Definition 3.11 in `c` are germ data in `c|dom φ ∩ V`.** -/
theorem StrongBundleChart.germData_restrictInter {x : X} (hxV : x ∈ c.φ.source) (hφ0 : c.φ x = 0)
    (hxV' : x ∈ V) (h0 : (0 : c.φ.model.E 0) ∈ c.U) {g : c.φ.model.E 0 → c.F 0}
    {s : c.φ.model.E 0 → c.F 1} (hfill : IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g)
    (hs : IsScPlusGerm c.φ.model.C c.U s)
    (hconj : IsConjugateToBasicGerm c.U (fun u => g u - c.F.toBase 1 (s u))) :
    IsFillingGerm (c.restrictInter hV).relOpen (c.restrictInter hV).isRetraction
        (c.zero_mem_restrictInter_U hV hxV hφ0 hxV') ((c.restrictInter hV).principal f) g ∧
      IsScPlusGerm (c.restrictInter hV).φ.model.C (c.restrictInter hV).U s ∧
      IsConjugateToBasicGerm (c.restrictInter hV).U (fun u => g u - c.F.toBase 1 (s u)) := by
  have hsub := c.restrictInter_U_subset hV
  have h0' := c.zero_mem_restrictInter_U hV hxV hφ0 hxV'
  refine ⟨?_, hs.of_subset c.relOpen (c.restrictInter hV).relOpen h0', hconj.of_subset c.relOpen h0
    (c.restrictInter hV).relOpen hsub h0'⟩
  exact hfill.of_subset c.relOpen c.isRetraction (c.restrictInter hV).relOpen
    (c.restrictInter hV).isRetraction hsub h0 h0'

/-- The restriction of a tame chart to `dom φ ∩ V` is tame (`ScRetraction.restrict_isTame`). -/
theorem StrongBundle.IsTameChart.restrictInter (hc : B.IsTameChart c) :
    B.IsTameChart (c.restrictInter hV) :=
  ⟨hc.1.restrictInter hV, (c.isRetraction.baseRetraction c.relOpen).restrict_isTame
    (c.isOpen_restrictOpen (s := c.φ.source ∩ V) inter_subset_left
      (c.φ.isOpen_source.inter hV)) hc.2⟩

end ChartRestrict

/-! ### Germ data and sections on `P|V` -/

section Transport

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {V : Set X} [Nonempty V] [ParacompactSpace V]
  [ParacompactSpace (pullbackSpace P (Subtype.val : V → X))] (hV : IsOpen V) {f : X → Y}

open StrongRetr

/-- **The germ data of `f` at `x ∈ V` in a chart `c` are germ data of `f|V` in the transported
restricted chart.** -/
theorem StrongBundleChart.germData_restrictTo (hP : Continuous P) (hf : IsSection P f) {c : StrongBundleChart PX P}
    {x : X} (hxV : x ∈ c.φ.source) (hφ0 : c.φ x = 0) (hxV' : x ∈ V)
    (h0 : (0 : c.φ.model.E 0) ∈ c.U) {g : c.φ.model.E 0 → c.F 0} {s : c.φ.model.E 0 → c.F 1}
    (hfill : IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g)
    (hs : IsScPlusGerm c.φ.model.C c.U s)
    (hconj : IsConjugateToBasicGerm c.U (fun u => g u - c.F.toBase 1 (s u)))
    (q₀ : pullbackSpace P (Subtype.val : V → X)) :
    IsFillingGerm ((c.restrictInter hV).restrictTo hP hV
          (c.restrictInter_source_subset hV) q₀).relOpen
        ((c.restrictInter hV).restrictTo hP hV
          (c.restrictInter_source_subset hV) q₀).isRetraction
        (c.zero_mem_restrictInter_U hV hxV hφ0 hxV')
        (((c.restrictInter hV).restrictTo hP hV
          (c.restrictInter_source_subset hV) q₀).principal (restrictSection P V f hf)) g ∧
      IsScPlusGerm ((c.restrictInter hV).restrictTo hP hV
          (c.restrictInter_source_subset hV) q₀).φ.model.C
        ((c.restrictInter hV).restrictTo hP hV
          (c.restrictInter_source_subset hV) q₀).U s ∧
      IsConjugateToBasicGerm ((c.restrictInter hV).restrictTo hP hV
          (c.restrictInter_source_subset hV) q₀).U (fun u => g u - c.F.toBase 1 (s u)) := by
  obtain ⟨hfill', hs', hconj'⟩ := c.germData_restrictInter hV hxV hφ0 hxV' h0 hfill hs hconj
  refine ⟨?_, hs', hconj'⟩
  refine { hfill' with eq_on := ?_ }
  filter_upwards [hfill'.eq_on] with z hz hzO
  rw [← hz hzO]
  exact StrongBundleChart.principal_restrictTo hV hP _ q₀ hf
    (((c.restrictInter hV).r_image) ▸ hzO)

/-- **An sc-Fredholm germ at `x ∈ V` is an sc-Fredholm germ of `f|V`** (Definition 3.11 on
`P|V`). -/
theorem StrongBundle.IsScFredholmGerm.restrictOpen (hf : IsSection P f) {x : X}
    (h : B.IsScFredholmGerm f x) (hxV : x ∈ V) :
    (B.restrictOpen hV).IsScFredholmGerm (restrictSection P V f hf) ⟨x, hxV⟩ := by
  obtain ⟨hxs, c, hc, hxc, hφ0, h0, g, s, hfill, hs, hs0, hconj⟩ := h
  set q₀ : pullbackSpace P (Subtype.val : V → X) := restrictSection P V f hf ⟨x, hxV⟩ with hq₀
  obtain ⟨hfill', hs', hconj'⟩ :=
    StrongBundleChart.germData_restrictTo hV B.continuous hf hxc hφ0 hxV h0 hfill hs hconj q₀
  refine ⟨(MPolyfold.mem_smoothSet_restrictOpen_iff hV _).2 hxs,
    (c.restrictInter hV).restrictTo B.continuous hV (c.restrictInter_source_subset hV) q₀,
    StrongBundle.restrictOpen_isChart_restrictTo hV (hc.restrictInter hV) _ q₀,
    c.mem_restrictInter_source hV hxc hxV, hφ0, c.zero_mem_restrictInter_U hV hxc hφ0 hxV, g, s,
    hfill', hs', hs0, hconj'⟩

/-- **An sc-Fredholm germ in a tame chart at `x ∈ V` is one of `f|V`** (Definition 3.50 on
`P|V`). -/
theorem StrongBundle.IsScFredholmGermTame.restrictOpen (hf : IsSection P f) {x : X}
    (h : B.IsScFredholmGermTame f x) (hxV : x ∈ V) :
    (B.restrictOpen hV).IsScFredholmGermTame (restrictSection P V f hf) ⟨x, hxV⟩ := by
  obtain ⟨hxs, c, hc, hxc, hφ0, h0, g, s, hfill, hs, hs0, hconj⟩ := h
  set q₀ : pullbackSpace P (Subtype.val : V → X) := restrictSection P V f hf ⟨x, hxV⟩ with hq₀
  obtain ⟨hfill', hs', hconj'⟩ :=
    StrongBundleChart.germData_restrictTo hV B.continuous hf hxc hφ0 hxV h0 hfill hs hconj q₀
  refine ⟨(MPolyfold.mem_smoothSet_restrictOpen_iff hV _).2 hxs,
    (c.restrictInter hV).restrictTo B.continuous hV (c.restrictInter_source_subset hV) q₀,
    ⟨StrongBundle.restrictOpen_isChart_restrictTo hV (hc.restrictInter hV).1 _ q₀,
      (hc.restrictInter hV).2⟩,
    c.mem_restrictInter_source hV hxc hxV, hφ0, c.zero_mem_restrictInter_U hV hxc hφ0 hxV, g, s,
    hfill', hs', hs0, hconj'⟩

/-- **The restriction of an sc-Fredholm section to an open subset is an sc-Fredholm section**
(Definition 3.14 on `P|V`). -/
theorem StrongBundle.IsScFredholmSection.restrictOpen (hf : B.IsScFredholmSection f) :
    (B.restrictOpen hV).IsScFredholmSection (restrictSection P V f hf.isScSmooth.1) where
  isScSmooth := hf.isScSmooth.restrictOpen hV
  regularizing := StrongBundle.regularizing_restrictOpen hV hf
  germ v hv :=
    (hf.germ v.1 ((MPolyfold.mem_smoothSet_restrictOpen_iff hV v).1 hv)).restrictOpen hV _ v.2

/-- **The restriction of an sc-Fredholm section with tame germ data to an open subset has tame
germ data** (Definition 3.51 on `P|V`). -/
theorem StrongBundle.IsScFredholmSectionTame.restrictOpen (hf : B.IsScFredholmSectionTame f) :
    (B.restrictOpen hV).IsScFredholmSectionTame (restrictSection P V f hf.isScSmooth.1) :=
  { hf.toIsScFredholmSection.restrictOpen hV with
    germTame := fun v hv =>
      (hf.germTame v.1 ((MPolyfold.mem_smoothSet_restrictOpen_iff hV v).1 hv)).restrictOpen hV
        _ v.2 }

omit [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
  [∀ x, Module ℝ (P ⁻¹' {x})] [ParacompactSpace V]
  [ParacompactSpace (pullbackSpace P Subtype.val)] in
/-- The zeros of `f|V` are the zeros of `f` in `V`. -/
lemma isZeroAt_restrictSection_iff' (hf : IsSection P f) (v : V) :
    IsZeroAt (pullbackProj P (Subtype.val : V → X)) (restrictSection P V f hf) v ↔
      IsZeroAt P f v.1 :=
  isZeroAt_restrictSection_iff hf v

omit [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
  [∀ x, Module ℝ (P ⁻¹' {x})] [ParacompactSpace V]
  [ParacompactSpace (pullbackSpace P Subtype.val)] in
/-- The restriction of `f + s` is `f|V + s|V` (fibrewise, `pullbackFiberEquiv`). -/
lemma restrictSection_sectionAdd {s : X → Y} (hf : IsSection P f) (hs : IsSection P s) :
    restrictSection P V (sectionAdd P f s) (hf.sectionAdd hs) =
      sectionAdd (pullbackProj P (Subtype.val : V → X)) (restrictSection P V f hf)
        (restrictSection P V s hs) := by
  funext v
  set e := pullbackFiberEquiv P (Subtype.val : V → X) v with he
  have h1 : e ⟨restrictSection P V f hf v, rfl⟩ = ⟨f v.1, hf v.1⟩ := Subtype.ext rfl
  have h2 : e ⟨restrictSection P V s hs v, rfl⟩ = ⟨s v.1, hs v.1⟩ := Subtype.ext rfl
  have h3 := pullbackFiberEquiv_add P (Subtype.val : V → X) v
    ⟨restrictSection P V f hf v, rfl⟩ ⟨restrictSection P V s hs v, rfl⟩
  rw [h1, h2] at h3
  rw [sectionAdd_apply (isSection_restrictSection hf) (isSection_restrictSection hs)]
  apply Subtype.ext
  refine Prod.ext rfl ?_
  change sectionAdd P f s v.1 = _
  rw [sectionAdd_apply hf hs]
  have := congrArg Subtype.val h3
  exact this.symm

/-! ### The index on `P|V` -/

/-- **The index of a germ datum of `f` at a zero `x ∈ V`, read on `P|V`**: `(f|V)'(x)` is Fredholm
of index `dim Pn − dim Q` in every chart of `P|V` (`isLinOfIndex_of_conjugationData` on `P|V`
for the transported germ datum, whose conjugation data have the same `Pn` and `Q`). -/
theorem StrongBundle.isLinOfIndex_restrictOpen_of_conjugationData (hf : B.IsScSmoothSection f)
    {x : X} (hx0 : IsZeroAt P f x) (hxV : x ∈ V) {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (hxc : x ∈ c.φ.source) (hφ0 : c.φ x = 0) (h0 : (0 : c.φ.model.E 0) ∈ c.U)
    {g : c.φ.model.E 0 → c.F 0} {s : c.φ.model.E 0 → c.F 1}
    (hfill : IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g)
    (hs : IsScPlusGerm c.φ.model.C c.U s) (hs0 : c.F.toBase 1 (s 0) = g 0)
    (dc : ConjugationData c.U fun u => g u - c.F.toBase 1 (s u)) :
    (B.restrictOpen hV).IsLinOfIndex (restrictSection P V f hf.1) ⟨x, hxV⟩
      (finrank ℝ dc.Pn - finrank ℝ dc.Q) := by
  set q₀ : pullbackSpace P (Subtype.val : V → X) := restrictSection P V f hf.1 ⟨x, hxV⟩ with hq₀
  have hsub := c.restrictInter_U_subset hV
  have h0' := c.zero_mem_restrictInter_U hV hxc hφ0 hxV
  obtain ⟨hfill', hs', -⟩ := StrongBundleChart.germData_restrictTo hV B.continuous hf.1 hxc hφ0 hxV h0 hfill hs
    (isConjugateToBasicGerm_iff_nonempty.2 ⟨dc⟩) q₀
  have hx0' : IsZeroAt (pullbackProj P (Subtype.val : V → X)) (restrictSection P V f hf.1)
      ⟨x, hxV⟩ := (isZeroAt_restrictSection_iff' hf.1 _).2 hx0
  have := StrongBundle.isLinOfIndex_of_conjugationData (hf.restrictOpen hV) hx0'
    (StrongBundle.restrictOpen_isChart_restrictTo hV (hc.restrictInter hV) _ q₀)
    (c.mem_restrictInter_source hV hxc hxV) hφ0 h0' hfill' hs' hs0
    (dc.ofSubset c.relOpen h0 (c.restrictInter hV).relOpen hsub h0')
  exact this

/-- **The index at a zero restricts to `P|V`**: if `f'(x)` is Fredholm of index `i` in every chart
of `P` (`IsLinOfIndex`), then `(f|V)'(x)` is Fredholm of index `i` in every chart of `P|V`. -/
theorem StrongBundle.IsLinOfIndex.restrictOpen (hf : B.IsScFredholmSection f) {x : X}
    (hx0 : IsZeroAt P f x) (hxV : x ∈ V) {i : ℤ} (hi : B.IsLinOfIndex f x i) :
    (B.restrictOpen hV).IsLinOfIndex (restrictSection P V f hf.isScSmooth.1) ⟨x, hxV⟩ i := by
  have hxs : x ∈ PX.smoothSet := hf.mem_smoothSet_of_isZeroAt hx0
  obtain ⟨-, c, hc, hxc, hφ0, h0, g, s, hfill, hs, hs0, hconj⟩ := hf.germ x hxs
  obtain ⟨dc⟩ := isConjugateToBasicGerm_iff_nonempty.1 hconj
  have hd := StrongBundle.isLinOfIndex_of_conjugationData hf.isScSmooth hx0 hc hxc hφ0 h0 hfill hs
    hs0 dc
  have hid : i = finrank ℝ dc.Pn - finrank ℝ dc.Q := hi.unique hf hx0 hd
  rw [hid]
  exact StrongBundle.isLinOfIndex_restrictOpen_of_conjugationData hV hf.isScSmooth hx0 hxV hc hxc
    hφ0 h0 hfill hs hs0 dc

/-- **The index at a zero is determined on `P|V`**: if `(f|V)'(x)` is Fredholm of index `i` in
every chart of `P|V`, then `f'(x)` is Fredholm of index `i` in every chart of `P`. -/
theorem StrongBundle.IsLinOfIndex.of_restrictOpen (hf : B.IsScFredholmSection f) {x : X}
    (hx0 : IsZeroAt P f x) (hxV : x ∈ V) {i : ℤ}
    (hi : (B.restrictOpen hV).IsLinOfIndex (restrictSection P V f hf.isScSmooth.1) ⟨x, hxV⟩ i) :
    B.IsLinOfIndex f x i := by
  have hxs : x ∈ PX.smoothSet := hf.mem_smoothSet_of_isZeroAt hx0
  obtain ⟨-, c, hc, hxc, hφ0, h0, g, s, hfill, hs, hs0, hconj⟩ := hf.germ x hxs
  obtain ⟨dc⟩ := isConjugateToBasicGerm_iff_nonempty.1 hconj
  have hd := StrongBundle.isLinOfIndex_of_conjugationData hf.isScSmooth hx0 hc hxc hφ0 h0 hfill hs
    hs0 dc
  have hd' := StrongBundle.isLinOfIndex_restrictOpen_of_conjugationData hV hf.isScSmooth hx0 hxV hc
    hxc hφ0 h0 hfill hs hs0 dc
  have hx0' : IsZeroAt (pullbackProj P (Subtype.val : V → X))
      (restrictSection P V f hf.isScSmooth.1) ⟨x, hxV⟩ :=
    (isZeroAt_restrictSection_iff' hf.isScSmooth.1 _).2 hx0
  have hid : i = finrank ℝ dc.Pn - finrank ℝ dc.Q := hi.unique (hf.restrictOpen hV) hx0' hd'
  rw [hid]
  exact hd

/-- **Definition 6.1 restricts to `P|V`**: `ind(f, x) = i` with a global sc⁺-section `s` gives
`ind(f|V, x) = i` with `s|V`. -/
theorem StrongBundle.IsIndexAt.restrictOpen (hf : B.IsScFredholmSection f) {x : X} (hxV : x ∈ V)
    {i : ℤ} (hi : B.IsIndexAt f x i) :
    (B.restrictOpen hV).IsIndexAt (restrictSection P V f hf.isScSmooth.1) ⟨x, hxV⟩ i := by
  obtain ⟨s, hs, hsx, hL⟩ := hi
  have hfs : IsSection P f := hf.isScSmooth.1
  refine ⟨restrictSection P V s hs.1, hs.restrictOpen hV, ?_, ?_⟩
  · rw [← restrictSection_sectionAdd hfs hs.1]
    exact (isZeroAt_restrictSection_iff' (hfs.sectionAdd hs.1) _).2 hsx
  · have := StrongBundle.IsLinOfIndex.restrictOpen hV (theorem_3_15 hf hs) hsx hxV hL
    rwa [restrictSection_sectionAdd hfs hs.1] at this

end Transport

end Polyfold
