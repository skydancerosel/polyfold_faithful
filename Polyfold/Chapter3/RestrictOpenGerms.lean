import Polyfold.Chapter3.SectionCompactness
import Polyfold.Chapter3.BasicGermShrink
import Polyfold.Chapter3.LinearizationCharts

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.1 and §3.6,
Definitions 3.1.11, 3.6.3, 3.6.4 (preprint 3.11, 3.50, 3.51) and §6.1, for the restriction `P|V` of a strong bundle to an open
subset: the germ data of an sc-Fredholm section restrict to `P|V`, and the Fredholm index of
the linearization at a zero (`IsLinOfIndex`) is the same for `P` and for `P|V`.  Round-trip item
V3.98 (a); Findings, Chapter 3, items 360–369.

# Germ data and the index on the restriction `P|V`

## The text, paraphrased

Definition 3.1.11 (preprint 3.11) is local: the data of an sc-Fredholm germ at `x₀` live in a chart centred at
`x₀`, on a germ of neighbourhoods of `0`; so does the index of the linearization at a zero.
Restricting the bundle to an open subset `V ∋ x₀` changes nothing — the text never remarks on it.

## What is formalized

* **Germ data on a smaller domain**: `Polyfold.IsFillingGerm.of_subset`,
  `Polyfold.IsScPlusGerm.of_subset`, `Polyfold.ConjugationData.ofSubset` and
  `Polyfold.IsConjugateToBasicGerm.of_subset`: the data of Definition 3.1.11 (preprint 3.11) on a relatively open
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
  `IsIndexAt.restrictOpen` (**Definition 6.2.1 (preprint 6.1) restricts**: a global sc⁺-section `s` restricts).

## What the text leaves implicit, and the choices made

* Restricting `U` to `U₀` in Definition 3.1.11 (preprint 3.11) is harmless, but the strong bundle isomorphism of
  the conjugation is a map of the whole `U ◁ F`, so its restriction needs the relatively open
  image `ψ(U₀) = U' ∩ ψ'⁻¹(U₀)` (continuity of `ψ'`) and the shrinking of the basic germ to
  `G ∩ ψ'⁻¹(U₀)` (`shrinkGerm`), as in `BasicGermShrink.lean`.
* The transport of the index between `P` and `P|V` goes through the germ datum (the index is
  `dim Pn − dim Q` in every chart of either bundle, `isLinOfIndex_of_conjugationData`), not
  through a comparison of the charts of `P|V` with those of `P`: a chart of `P|V` need not come
  from a chart of `P`.

Restrictions to open sets (`restrictSection_sectionAdd`, `isZeroAt_restrictSection_iff'`,
`StrongBundle.IsIndexAt.restrictOpen`, `StrongBundleChart.germData_restrictTo`, …):
`Chapter5/RestrictOpenGermData.lean`.
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

/-! ### Germ data and sections on `P|V` -/

end Polyfold
