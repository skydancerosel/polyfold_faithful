import Polyfold.Chapter3.FredholmGermIndex
import Polyfold.Chapter3.FredholmGermLinearizationG

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.6,
**Proposition 3.52 with its index clause, in the text's germ reading of Definition 3.11**
(phase 2): the filling `g` and the sc⁺-section `s` are sc-smooth germs; the index of the
linearization is `n − N` for the dimensions `n = dim Pn`, `N = dim Q` of every conjugation of
`g − s` to a basic germ.

# The index in Proposition 3.52, germ reading

## What is formalized

* `Polyfold.ConjugationData.scDeriv_isFredholm_index` (the germ version of
  `ConjugationData.scDeriv_isFredholm_index_wholeChart`): for `k` an sc¹-germ on a germ `G_k ⊆ U` with
  derivative family `Dk`, `k(0) = 0`, and conjugation data `d` of `k`, `Dk(0)` is Fredholm of index
  `dim d.Pn − dim d.Q`; `Polyfold.ConjugationData.index_eq`: this number does not depend on
  the conjugation.
* `Polyfold.proposition_3_52_local_index` (the germ version of
  `proposition_3_52_local_index_wholeChart`) and `Polyfold.proposition_3_52_index` (the germ version of
  `proposition_3_52_index_wholeChart`, hypothesis `B.IsScFredholmGerm f x₀`): `Dg(0)` and
  `Tf(x₀) = Dg(0)|_{T₀O}` are Fredholm with `ind Tf(x₀) = ind Dg(0) = dim d.Pn − dim d.Q` for
  every conjugation `d` of `g − s`.

## What the text leaves implicit, and the choices made

As in `FredholmGermIndex.lean` and `FredholmGermLinearizationG.lean`: `Dg(0)` is the value at `0`
of any derivative family of the filling germ on any germ `G ⊆ U` (it is unique); only the
level-`0` Fredholm property is proved here (the sc form is `FredholmGermLinearizationScG.lean`).
-/

open Set Filter Topology Function Module ContinuousLinearMap

noncomputable section

namespace Polyfold

variable {E F : ScBanach}

/-! ### Conjugation data of a germ -/

section Conjugate

variable {C U : Set (E 0)} {Gk : ScNbhdGerm E C} {k : E 0 → F 0} {Dk : E 1 → E 0 →L[ℝ] F 0}

/-- **The derivative at `0` of a germ conjugated to a basic germ is Fredholm of index
`dim d.Pn − dim d.Q`** (Propositions 3.10 and 3.52, germ reading, phase 2; the germ version of
`ConjugationData.scDeriv_isFredholm_index_wholeChart`): `k` an sc¹-germ on `G_k ⊆ U` with derivative family
`Dk`, `k(0) = 0`, `d` conjugation data of `k`. -/
theorem ConjugationData.scDeriv_isFredholm_index (hU : IsRelOpenInQuadrant E C U)
    (h0 : (0 : E 0) ∈ U) (hGk : Gk.U 0 ⊆ U) (hk : IsSc1GermWith Gk k Dk) (hk0 : k 0 = 0)
    (d : ConjugationData U k) :
    IsFredholm (Dk 0) ∧ fredholmIndex (Dk 0) = finrank ℝ d.Pn - finrank ℝ d.Q :=
  d.iso.deriv_zero_isFredholm_germ hU h0 hGk hk hk0 d.quadrant d.relOpen d.base_zero d.basic
    d.conj

/-- **The index `n − N` does not depend on the conjugation** (germ reading, phase 2; the germ
version of `ConjugationData.index_eq_wholeChart`): for two conjugations `d`, `d'` of the same sc¹-germ `k`
with `k(0) = 0`, `dim d.Pn − dim d.Q = dim d'.Pn − dim d'.Q`. -/
theorem ConjugationData.index_eq (hU : IsRelOpenInQuadrant E C U) (h0 : (0 : E 0) ∈ U)
    (hGk : Gk.U 0 ⊆ U) (hk : IsSc1GermWith Gk k Dk) (hk0 : k 0 = 0)
    (d d' : ConjugationData U k) :
    (finrank ℝ d.Pn : ℤ) - finrank ℝ d.Q = (finrank ℝ d'.Pn : ℤ) - finrank ℝ d'.Q := by
  rw [← (d.scDeriv_isFredholm_index hU h0 hGk hk hk0).2,
    (d'.scDeriv_isFredholm_index hU h0 hGk hk hk0).2]

end Conjugate

/-! ### Proposition 3.52 with the index of the conjugation, germ reading -/

section Prop352

variable {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

open StrongRetr

/-- **Proposition 3.52 in the chart of Definition 3.11, with the index, germ reading** (phase 2;
the germ version of `proposition_3_52_local_index_wholeChart`): let `g` be a filling germ of the principal
part `f̂` of a section at a zero, with a derivative family `Dg` on a germ `G ⊆ U`, `s` an sc¹-germ
into `F¹` on `G_s` with `s(0) = g(0)` and `d` conjugation data of `g − s` to a basic germ
`h : O(C̃ ⊕ W, 0) → ℝᴺ ⊕ W`, `C̃ ⊆ ℝⁿ`, `n = dim d.Pn`, `N = dim d.Q`.  Then `Dg(0)` and
`Tf(0) = Dg(0)|_{T₀O} : T₀O → K₀` are Fredholm (level `0`) of index `n − N`. -/
theorem proposition_3_52_local_index (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U) (h0O : (0 : E 0) ∈ r R '' U)
    {fb g : E 0 → F 0} (hfill : IsFillingGerm hU hR h0 fb g) (hfb0 : fb 0 = 0)
    (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ)) {G : ScNbhdGerm E C} (hG : G.U 0 ⊆ U)
    {Dg : E 1 → E 0 →L[ℝ] F 0} (hg : IsSc1GermWith G g Dg) {Gs : ScNbhdGerm E C}
    {s : E 0 → F 1} {Ds : E 1 → E 0 →L[ℝ] F.shift 0} (hs : IsSc1GermWith (F := F.shift) Gs s Ds)
    (hs0 : F.toBase 1 (s 0) = g 0) (d : ConjugationData U fun u => g u - F.toBase 1 (s u)) :
    ∃ (h1 : ∀ x, ρCLM hR h0 (Dg 0 (scDeriv U (r R) 0 x)) = Dg 0 (scDeriv U (r R) 0 x)),
      IsFredholm (Dg 0) ∧ fredholmIndex (Dg 0) = finrank ℝ d.Pn - finrank ℝ d.Q ∧
      IsFredholm (fillerRestrict (scDeriv U (r R) 0) (ρCLM hR h0) (Dg 0) h1) ∧
      fredholmIndex (fillerRestrict (scDeriv U (r R) 0) (ρCLM hR h0) (Dg 0) h1) =
        finrank ℝ d.Pn - finrank ℝ d.Q := by
  have hg0 : g 0 = 0 := by rw [← hfill.eq_on.self_of_nhds h0O, hfb0]
  have hk := hg.sub_toBase_shift hs
  have hk0 : (fun u => g u - F.toBase 1 (s u)) 0 = 0 := by
    change g 0 - F.toBase 1 (s 0) = 0
    rw [hs0, hg0, sub_self]
  obtain ⟨hDkF, hDkind⟩ :=
    d.scDeriv_isFredholm_index hU h0 ((G.inter_subset_left Gs 0).trans hG) hk hk0
  set S : ScPlus E F := hs.isScOperator_deriv_zero.toScOperator with hS
  have hDg : Dg 0 = (Dg 0 - (F.toBase 1).comp (Ds 0)) + S.toScOperator 0 :=
    hs.deriv_zero_eq_add_scPlus
  have hcompact : IsCompactOperator (S.toScOperator 0) := S.isCompactOperator 0
  have hDgF : IsFredholm (Dg 0) := by
    rw [hDg]; exact isFredholm_add_isCompactOperator hDkF hcompact
  have hDgind : fredholmIndex (Dg 0) = finrank ℝ d.Pn - finrank ℝ d.Q := by
    rw [hDg, fredholmIndex_add_isCompactOperator hDkF hcompact, hDkind]
  obtain ⟨h1, -, hFiff, hindeq⟩ := hfill.proposition_3_5 hU hR h0 hg0 h0O hfK hG hg
  exact ⟨h1, hDgF, hDgind, hFiff.2 hDgF, by rw [hindeq, hDgind]⟩

end Prop352

/-! ### Proposition 3.52 for sections of strong bundles, with the index, germ reading -/

section Bundle

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

open StrongRetr

/-- **Proposition 3.52, with the index, germ reading** (phase 2; the germ version of
`proposition_3_52_index_wholeChart`, hypothesis `B.IsScFredholmGerm f x₀`): let `f` be a section with
`(f, x₀)` an sc-Fredholm germ and `f(x₀) = 0`.  In the strong bundle chart of Definition 3.11
centred at `x₀`, with the filling germ `g` of `f̂` (on `G ⊆ U`, derivative family `Dg`) and the
sc⁺-germ `s` (`s(0) = g(0)`) for which `g − s` is conjugated to a basic germ, `Dg(0)` and
`Tf(x₀) = Dg(0)|_{T₀O} : T₀O → K₀` are Fredholm, and for **every** conjugation `d` of `g − s` to a
basic germ `h : O(C̃ ⊕ W, 0) → ℝᴺ ⊕ W`, `C̃ ⊆ ℝⁿ`, their index is `n − N = dim d.Pn − dim d.Q`. -/
theorem proposition_3_52_index (hf : IsSection P f) {x₀ : X}
    (hg : B.IsScFredholmGerm f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ (c : StrongBundleChart PX P) (_ : B.IsChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
      (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0) (s : c.φ.model.E 0 → c.F 1)
      (_ : IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g)
      (_ : IsScPlusGerm c.φ.model.C c.U s) (_ : c.F.toBase 1 (s 0) = g 0)
      (_ : Nonempty (ConjugationData c.U fun u => g u - c.F.toBase 1 (s u)))
      (G : ScNbhdGerm c.φ.model.E c.φ.model.C) (_ : G.U 0 ⊆ c.U) (_ : IsScSmoothGerm G g)
      (Dg : c.φ.model.E 1 → c.φ.model.E 0 →L[ℝ] c.F 0) (_ : IsSc1GermWith G g Dg)
      (h1 : ∀ x, ρCLM c.isRetraction h0 (Dg 0 (scDeriv c.U (r c.R) 0 x)) =
        Dg 0 (scDeriv c.U (r c.R) 0 x)),
      IsFredholm (Dg 0) ∧
      IsFredholm (fillerRestrict (scDeriv c.U (r c.R) 0) (ρCLM c.isRetraction h0) (Dg 0) h1) ∧
      ∀ d : ConjugationData c.U (fun u => g u - c.F.toBase 1 (s u)),
        fredholmIndex (Dg 0) = finrank ℝ d.Pn - finrank ℝ d.Q ∧
        fredholmIndex (fillerRestrict (scDeriv c.U (r c.R) 0) (ρCLM c.isRetraction h0) (Dg 0)
          h1) = finrank ℝ d.Pn - finrank ℝ d.Q := by
  obtain ⟨-, c, hc, hxV, hφ0, h0U, g, s, hfill, hsp, hs0, hconj⟩ := hg
  obtain ⟨Gs, -, hs⟩ := id hsp
  obtain ⟨h0O, hfb0, hfK⟩ := c.zero_data hf hxV hφ0 hx₀
  obtain ⟨G, hGU, hgG, -⟩ := hfill.germ
  have hg1 := (hgG 1).1.isSc1GermWith_scDerivGerm
  have hs1 := (hs 1).1.isSc1GermWith_scDerivGerm
  obtain ⟨d₀⟩ := isConjugateToBasicGerm_iff_nonempty.1 hconj
  obtain ⟨h1, hDgF, -, hTF, -⟩ :=
    proposition_3_52_local_index c.relOpen c.isRetraction h0U h0O hfill hfb0 hfK hGU hg1 hs1
      hs0 d₀
  refine ⟨c, hc, hxV, hφ0, h0U, g, s, hfill, hsp, hs0, ⟨d₀⟩, G, hGU, hgG, _, hg1, h1, hDgF, hTF,
    fun d => ?_⟩
  obtain ⟨h1', -, hDgind, -, hTind⟩ :=
    proposition_3_52_local_index c.relOpen c.isRetraction h0U h0O hfill hfb0 hfK hGU hg1 hs1
      hs0 d
  exact ⟨hDgind, hTind⟩

end Bundle

end Polyfold
