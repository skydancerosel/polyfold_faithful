import Polyfold.Chapter3.GlobalIFTIndex
import Polyfold.Chapter3.GlobalIFTNearbyOntoG
import Polyfold.Chapter3.FredholmGermIndexG
import Polyfold.Chapter3.TameGermsAddG

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.1 and §3.6:
**the dimension of the solution set is the Fredholm index**, the index of `f'(x₀)`,
"`ker f'(y) = T_yS`" in a chart, the local constancy of the index along the solution set, and
"good position = surjectivity" when `∂X = ∅` — **in the text's germ reading of Definition 3.1.11 (preprint 3.11)**
(phase 2).

# The Fredholm index and the solution set, germ reading

## The text, paraphrased

See `GlobalIFTIndex.lean`.  (Theorem 3.1.22 (preprint 3.19)) the solution set is a manifold "whose dimension agrees
with the Fredholm index of `f'(x₀)`", `f'(y)` is onto and `ker f'(y) = T_yS(f, U)`; (proof of
Theorem 3.6.8 (preprint 3.54)) `d = dim ker f'(x)`; (before Theorem 3.6.10 (preprint 3.56)) for `∂X = ∅` good position is
surjectivity; (proof of Proposition 6.2.2 (preprint 6.2)) the index is locally constant along the solution set.
The germs of Definition 3.1.11 (preprint 3.11) are germs: the filling `g` and the sc⁺-section `s` are sc-smooth on a
germ of neighbourhoods whose levels may shrink.

## What is formalized

The germ forms of the declarations of `GlobalIFTIndex.lean` that use germ data, with the
hypotheses in the germ reading (`IsScFredholmGerm`, `IsScFredholmSection`,
`IsScFredholmSectionTame`, `IsGoodPositionGerm`, `IsGoodPositionGermTame`,
`IsGoodPositionGermFilled`) and the **same conclusions** (where an old conclusion exposed the
filled version `g` and `scDeriv U g 0`, the germ form exposes the filling germ, a germ `G`, a
derivative family `Dg` and `Dg(0)`).  `StrongBundle.IsSurjLinOfIndex`, `StrongBundle.IsLinSurjAt`
and `IsLinSurjAt.linAt_surjective` are statements about `linAt` (the derivative of the
whole-chart map `f̂ ∘ r`) and need no germ form.

* Chart level: `Polyfold.normal_injective_of_exists_range_deriv_eq_ρ_germ`,
  `Polyfold.exists_range_deriv_eq_ρ_iff_normal_injective_germ` (Finding 100's equivalence for a
  derivative `Dg(z)` of a germ, at `z ∈ G₁`).
* `Polyfold.StrongBundle.linAt_index_of_conjugationData`,
  `StrongBundle.isSurjLinOfIndex_of_conjugationData`,
  `StrongBundle.IsGoodPositionGerm.exists_isSurjLinOfIndex`: Proposition 3.6.5 (preprint 3.52) with the index in
  the centred chart (`proposition_3_6_5_local_index`), `Tf̃(0) = Lin(0)` for a filling germ
  (`IsFillingGerm.fillerRestrict_eq_linAt`), and the chart independence.
* `StrongBundle.IsGoodPositionGerm.isLinSurjAt`,
  `StrongBundle.isGoodPositionGerm_of_linAt_surj_of_degIndex_eq_zero`,
  `StrongBundle.isGoodPositionGerm_of_isLinSurjAt`,
  `StrongBundle.isGoodPositionGerm_iff_isLinSurjAt`:
  good position and surjectivity when `d_X(y) = 0`.
* `Polyfold.theorem_3_1_22_linearization_index`, `theorem_3_6_8_tangentGermChart_index`,
  `theorem_3_6_8_tangentGermChart_solutionSet_index`, `theorem_3_6_8_two_index`,
  `isSurjLinOfIndex_of_forall_dim`, `theorem_3_6_8_index_locally_constant`,
  `theorem_3_6_8_index`, `theorem_3_1_26_index`, `theorem_3_1_22_index`,
  `theorem_3_1_22_of_surjective`, `theorem_3_6_11_index`, `theorem_3_6_10_tame`,
  `theorem_3_6_10_of_surjective`: dimension = index, and the main theorems with the index.
* `Polyfold.theorem_3_6_8_ker_eq_tangent` ("`ker f'(y) = T_yS`" in a chart) and
  `Polyfold.isGoodPositionGermFilled_of_isGoodPositionGerm` (the filler condition of
  `IsGoodPositionGermFilled` follows from good position).

## What the text leaves implicit, and the choices made (the findings)

* **The index in the centred chart is that of `Dg(0)` for a derivative family of the filling
  germ.**  The old proofs used `proposition_3_6_5_local_index_wholeChart` for a filled version `g` on the whole
  `U`; here `proposition_3_6_5_local_index` gives `Tf̃(0) = Dg(0)|_{T₀O}` Fredholm of index
  `dim Pn − dim Q`, and the bridge `Tf̃(0) = Lin(0)` (`IsFillingGerm.fillerRestrict_eq_linAt`)
  carries it to `Lin(0)`, whence to every chart.  The sc⁺-germ enters only through its derivative
  at `0` (`IsScPlusGerm` gives a germ and the family `scDerivGerm`).
* **At the nearby zeros the bridge `Lin(z) = Dg(z)` is used at the level-`1` point `z₀₁` of
  `theorem_3_6_8_nearby_kernel`, which lies in the germ `G_g`** (the G″ design); for the filler
  condition of `IsGoodPositionGermFilled` the point `z₁ ∈ G₁` is part of the condition, so the
  bridge applies there directly.
* Nothing else changes: the dimension count, the re-centring, Theorem 3.2.3 (preprint 3.27) and the transport
  between charts are on the `E'`-side, in `X`, or about `linAt`.
-/

open Set Filter Topology Function Module ContinuousLinearMap

noncomputable section

namespace Polyfold

variable {E F : ScBanach}

/-! ### Condition (3) of Definition 3.1.4 (preprint 3.4) at a nearby zero, for a derivative of a germ -/

section Normal

variable {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

open StrongRetr

/-- **The converse of `exists_range_deriv_eq_ρ_of_normal_injective_germ`** (Finding 100's "iff",
germ reading, phase 2; the germ form of `normal_injective_of_exists_range_scDeriv_eq_ρ`): at a
point `z` of the retract and for any operator `D : E₀ → F₀` (the value `Dg(z)` of a derivative
family of a germ `g`) with `ker D ⊆ T_zO`, if `D` maps `T_zO` onto `ρ(z)F`, then
`(1 − ρ(z))D` is injective on `ker Dr(z)`: for `b ∈ ker Dr(z)` with `ρ(z)Db = Db` choose
`a ∈ T_zO` with `Da = Db`; then `a − b ∈ ker D ⊆ T_zO`, so `b ∈ T_zO ∩ ker Dr(z) = 0`. -/
theorem normal_injective_of_exists_range_deriv_eq_ρ_germ (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) {z : E 1} (hzO : E.toBase 1 z ∈ r R '' U)
    {D : E 0 →L[ℝ] F 0} (hker : LinearMap.ker (D : E 0 →ₗ[ℝ] F 0) ≤ rangeS (scDeriv U (r R) z))
    (honto : ∀ k : F 0, ∃ x ∈ rangeS (scDeriv U (r R) z), D x = ρ R (E.toBase 1 z) k) :
    ∀ b : E 0, scDeriv U (r R) z b = 0 → ρ R (E.toBase 1 z) (D b) = D b → b = 0 := by
  intro b hb hρb
  obtain ⟨a, ha, hab⟩ := honto (D b)
  rw [hρb] at hab
  have hmem : a - b ∈ LinearMap.ker (D : E 0 →ₗ[ℝ] F 0) := by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, hab, sub_self]
  have hbT : b ∈ rangeS (scDeriv U (r R) z) := by
    have := (rangeS (scDeriv U (r R) z)).sub_mem ha (hker hmem)
    rwa [sub_sub_cancel] at this
  obtain ⟨w, rfl⟩ := hbT
  change scDeriv U (r R) z (scDeriv U (r R) z w) = 0 at hb
  rw [scDeriv_r_idem_at hU hR hzO] at hb
  exact hb

/-- **Finding 100's equivalence, germ reading** (phase 2; the germ form of
`exists_range_scDeriv_eq_ρ_iff_normal_injective`): for `g` an sc¹-germ on `G₁` with derivative
family `Dg`, at a level-`1` point `z ∈ G₁` over a zero of `f̂` in `O` with `f̂ = g` on `O` near
`ι z`, `Dg(z)` onto and `ker Dg(z) ⊆ T_zO`: `Dg(z)` maps `T_zO` onto `K_z = ρ(z)F` iff
`(1 − ρ(z))Dg(z)` is injective on `ker Dr(z)` (condition (3) of Definition 3.1.4 (preprint 3.4) at `z`). -/
theorem exists_range_deriv_eq_ρ_iff_normal_injective_germ (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U) (h0O : (0 : E 0) ∈ r R '' U)
    {fb g : E 0 → F 0} (hfr : IsSc1 U (fb ∘ r R)) {G₁ : ScNbhdGerm E C}
    {Dg : E 1 → E 0 →L[ℝ] F 0} (hg : IsSc1GermWith G₁ g Dg)
    (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ)) {z : E 1}
    (hzO : E.toBase 1 z ∈ r R '' U) (hzG : z ∈ G₁.U 1) (hfz : fb (E.toBase 1 z) = 0)
    (heq : ∀ᶠ x in 𝓝 (E.toBase 1 z), x ∈ r R '' U → fb x = g x)
    (hsurj : Surjective (Dg z))
    (hker : LinearMap.ker (Dg z : E 0 →ₗ[ℝ] F 0) ≤ rangeS (scDeriv U (r R) z)) :
    (∀ k : F 0, ∃ x ∈ rangeS (scDeriv U (r R) z), Dg z x = ρ R (E.toBase 1 z) k) ↔
      ∀ b : E 0, scDeriv U (r R) z b = 0 →
        ρ R (E.toBase 1 z) (Dg z b) = Dg z b → b = 0 :=
  ⟨normal_injective_of_exists_range_deriv_eq_ρ_germ hU hR hzO hker,
    exists_range_deriv_eq_ρ_of_normal_injective_germ hU hR h0 h0O hfr hg hfK hzO hzG hfz heq
      hsurj⟩

end Normal

/-! ### The index of the linearization at a zero, in every chart, germ reading -/

section Bundle

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

open StrongRetr

/-- **Proposition 3.6.5 (preprint 3.52) in every chart, germ reading** (phase 2; the germ form of
`StrongBundle.linAt_index_of_conjugationData_wholeChart`): let `c` be the chart of Definition 3.1.11 (preprint 3.11) at the
zero `x₀` (centred, with a filling germ `g` of `f̂`, a derivative family `Dg` of `g` on a germ
`G ⊆ U`, an sc⁺-germ `s`, `s(0) = g(0)`) and `dc` conjugation data of `g − s` to a basic germ
`h : O(C̃ ⊕ W, 0) → ℝᴺ ⊕ W`, `C̃ ⊆ ℝⁿ`.  Then for every strong bundle chart `c'` around `x₀` and the
level-`1` point `z'` over `ϕ'(x₀)`, the linearization `Lin'(z') : T_{z'}O' → K'_{z'}` is Fredholm of
index `n − N = dim dc.Pn − dim dc.Q`, and it is onto if the germ is in good position at `Dg(0)`
(`IsGoodPositionAtGerm`).  Proposition 3.6.5 (preprint 3.52) for germs in `c` (`proposition_3_6_5_local_index`),
`Tf̃(0) = Lin(0)` (`IsFillingGerm.fillerRestrict_eq_linAt`), and the chart independence
(`linAt_chart_independence`). -/
theorem StrongBundle.linAt_index_of_conjugationData (hf : B.IsScSmoothSection f) {x₀ : X}
    (hx₀ : IsZeroAt P f x₀) {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (hxV : x₀ ∈ c.φ.source) (hφ0 : c.φ x₀ = 0) (h0 : (0 : c.φ.model.E 0) ∈ c.U)
    {g : c.φ.model.E 0 → c.F 0} {s : c.φ.model.E 0 → c.F 1}
    (hfill : IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g)
    {G : ScNbhdGerm c.φ.model.E c.φ.model.C} (hG : G.U 0 ⊆ c.U)
    {Dg : c.φ.model.E 1 → c.φ.model.E 0 →L[ℝ] c.F 0} (hg : IsSc1GermWith G g Dg)
    (hs : IsScPlusGerm c.φ.model.C c.U s) (hs0 : c.F.toBase 1 (s 0) = g 0)
    (dc : ConjugationData c.U fun u => g u - c.F.toBase 1 (s u))
    {c' : StrongBundleChart PX P} (hc' : B.IsChart c') (hxV' : x₀ ∈ c'.φ.source)
    {z' : c'.φ.model.E 1} (hz' : c'.φ.model.E.toBase 1 z' = c'.φ x₀)
    (hzU' : c'.φ.model.E.toBase 1 z' ∈ c'.U)
    (L' : ↥(rangeS (scDeriv c'.U (r c'.R) z')) →L[ℝ] ↥(rangeS (ρCLM c'.isRetraction hzU')))
    (hL' : ∀ x, (L' x : c'.F 0) = linAt c'.U c'.R (c'.principal f) z' x) :
    L'.IsFredholm ∧ fredholmIndex L' = finrank ℝ dc.Pn - finrank ℝ dc.Q ∧
      (IsGoodPositionAtGerm c.relOpen c.isRetraction h0 (Dg 0) → Surjective L') := by
  classical
  have hU := c.relOpen
  obtain ⟨h0O, hfb0, hfK⟩ := c.zero_data hf.1 hxV hφ0 hx₀
  obtain ⟨Gs, -, hsm⟩ := hs
  have hs1 := (hsm 1).1.isSc1GermWith_scDerivGerm
  obtain ⟨h1, -, -, hTF, hTind⟩ :=
    proposition_3_6_5_local_index hU c.isRetraction h0 h0O hfill hfb0 hfK hG hg hs1 hs0 dc
  set F₀ := fillerRestrict (scDeriv c.U (r c.R) 0) (ρCLM c.isRetraction h0) (Dg 0) h1
    with hF₀
  -- the chart independence, with `z = 0` in the centred chart
  obtain ⟨n, Wq, T, hT⟩ := c.φ.model.isPartialQuadrant
  obtain ⟨n', Wq', T', hT'⟩ := c'.φ.model.isPartialQuadrant
  have hz : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) = c.φ x₀ := by rw [map_zero, hφ0]
  have hzU : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) ∈ c.U := by rw [map_zero]; exact h0
  obtain ⟨L, L₁, hL, hL₁, hsurjiff, hFiff, hind, -⟩ := StrongBundle.linAt_chart_independence hf
    hc hc' hxV hxV' hx₀ hz hz' hzU hzU' T hT T' hT'
  have hL₁L' : L₁ = L' := by
    ext x
    rw [hL₁, hL']
  subst hL₁L'
  -- `L = Tf̃(0)` up to the identification of the fibres `ρ(0)F = ρ(ι 0)F`
  obtain ⟨e, he⟩ := exists_rangeS_ρCLM_equiv c.isRetraction h0 hzU (map_zero _).symm
  have hfr : IsSc1 c.U (c.principal f ∘ r c.R) := hf.isSc1_principal_comp_r hc
  have hconj : ∀ x, L ((ContinuousLinearEquiv.refl ℝ _) x) = e (F₀ x) := fun x => by
    apply Subtype.ext
    rw [he, ContinuousLinearEquiv.refl_apply, hL, hF₀,
      hfill.fillerRestrict_eq_linAt hU c.isRetraction h0O hfr hg h1 x]
  have hzO : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) ∈ r c.R '' c.U := by
    rw [map_zero]; exact h0O
  have : CompleteSpace ↥(rangeS (scDeriv c.U (r c.R) 0)) :=
    (isClosed_range_of_idem _ (scDeriv_r_idem_at c.relOpen c.isRetraction hzO)).completeSpace_coe
  have : CompleteSpace ↥(rangeS (ρCLM c.isRetraction h0)) :=
    (isClosed_range_of_idem _ fun k => ρ_ρ c.isRetraction h0O k).completeSpace_coe
  have : CompleteSpace ↥(rangeS (ρCLM c.isRetraction hzU)) :=
    (isClosed_range_of_idem _ fun k => ρ_ρ c.isRetraction hzO k).completeSpace_coe
  have hLF : L.IsFredholm := (isFredholm_iff_of_conj hconj).1.1 hTF
  have hLind : fredholmIndex L = fredholmIndex F₀ := (isFredholm_iff_of_conj hconj).2 hTF
  refine ⟨hFiff.1 hLF, by rw [hind hLF, hLind, hTind], fun hgp => ?_⟩
  exact hsurjiff.1 ((surjective_iff_of_conj hconj).1 (hgp.surjective_fillerRestrict h1))

/-- **The linearization at a zero in good position is onto of index `d = n − N`, in every chart,
germ reading** (phase 2; the germ form of `StrongBundle.isSurjLinOfIndex_of_conjugationData_wholeChart`):
with the data of Definition 3.6.6 (preprint 3.53) at `x₀` in the germ reading (good position at `Dg(0)`), for every
`d : ℕ` with `d = dim dc.Pn − dim dc.Q`, `IsSurjLinOfIndex f x₀ d`. -/
theorem StrongBundle.isSurjLinOfIndex_of_conjugationData (hf : B.IsScSmoothSection f)
    {x₀ : X} (hx₀ : IsZeroAt P f x₀) {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (hxV : x₀ ∈ c.φ.source) (hφ0 : c.φ x₀ = 0) (h0 : (0 : c.φ.model.E 0) ∈ c.U)
    {g : c.φ.model.E 0 → c.F 0} {s : c.φ.model.E 0 → c.F 1}
    (hfill : IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g)
    {G : ScNbhdGerm c.φ.model.E c.φ.model.C} (hG : G.U 0 ⊆ c.U)
    {Dg : c.φ.model.E 1 → c.φ.model.E 0 →L[ℝ] c.F 0} (hg : IsSc1GermWith G g Dg)
    (hs : IsScPlusGerm c.φ.model.C c.U s) (hs0 : c.F.toBase 1 (s 0) = g 0)
    (hgp : IsGoodPositionAtGerm c.relOpen c.isRetraction h0 (Dg 0))
    (dc : ConjugationData c.U fun u => g u - c.F.toBase 1 (s u)) {d : ℕ}
    (hd : (d : ℤ) = finrank ℝ dc.Pn - finrank ℝ dc.Q) : B.IsSurjLinOfIndex f x₀ d := by
  intro c' hc' hxV' z' hz' hzU' L' hL'
  obtain ⟨hF, hind, hsurj⟩ := StrongBundle.linAt_index_of_conjugationData hf hx₀ hc hxV hφ0
    h0 hfill hG hg hs hs0 dc hc' hxV' hz' hzU' L' hL'
  have hs' := hsurj hgp
  refine ⟨hs', hF, by rw [hind, hd], ?_⟩
  have h := finrank_ker_eq_fredholmIndex_of_surjective hF hs'
  rw [hind, ← hd] at h
  exact_mod_cast h

/-- **At a zero in good position, `f'(x₀)` is onto with `ind f'(x₀) = dim ker f'(x₀) = d` in every
chart, germ reading** (phase 2; the germ form of
`StrongBundle.IsGoodPositionGermWholeChart.exists_isSurjLinOfIndex`),
and `d = n − N` for every conjugation to a basic germ in the chart of Definition 3.6.6 (preprint 3.53), whose germ
data (filling germ `g`, sc⁺-germ `s`, derivative family `Dg` on `G`, good position at `Dg(0)`) are
exposed. -/
theorem StrongBundle.IsGoodPositionGerm.exists_isSurjLinOfIndex (hf : B.IsScSmoothSection f)
    {x₀ : X} (hg : B.IsGoodPositionGerm f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ d : ℕ, B.IsSurjLinOfIndex f x₀ d ∧
      ∃ (c : StrongBundleChart PX P) (_ : B.IsChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
        (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0)
        (s : c.φ.model.E 0 → c.F 1)
        (_ : IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g)
        (_ : IsScPlusGerm c.φ.model.C c.U s) (_ : c.F.toBase 1 (s 0) = g 0)
        (G : ScNbhdGerm c.φ.model.E c.φ.model.C)
        (Dg : c.φ.model.E 1 → c.φ.model.E 0 →L[ℝ] c.F 0) (_ : G.U 0 ⊆ c.U)
        (_ : IsSc1GermWith G g Dg) (_ : IsGoodPositionAtGerm c.relOpen c.isRetraction h0 (Dg 0)),
        Nonempty (ConjugationData c.U fun u => g u - c.F.toBase 1 (s u)) ∧
        ∀ dc : ConjugationData c.U (fun u => g u - c.F.toBase 1 (s u)),
          (d : ℤ) = finrank ℝ dc.Pn - finrank ℝ dc.Q := by
  obtain ⟨-, c, hc, hxV, hφ0, h0, g, s, hfill, hs, hs0, hconj, G, Dg, hG, hDg, hgp⟩ := hg
  obtain ⟨dc₀⟩ := isConjugateToBasicGerm_iff_nonempty.1 hconj
  -- the index of `Lin(0)` in the centred chart
  have hz : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) = c.φ x₀ := by rw [map_zero, hφ0]
  have hzU : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) ∈ c.U := by rw [map_zero]; exact h0
  have hzO : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) ∈ r c.R '' c.U := by
    rw [map_zero, c.r_image, ← hφ0]; exact c.φ.mapsTo_model x₀ hxV
  have hmem : ∀ x : ↥(rangeS (scDeriv c.U (r c.R) 0)),
      linAt c.U c.R (c.principal f) 0 x ∈ rangeS (ρCLM c.isRetraction hzU) := fun x =>
    ⟨_, rho_scDeriv_comp_r c.relOpen c.isRetraction (hf.isSc1_principal_comp_r hc)
      (fun x hx => c.principal_mem_K hf.1 (c.r_image ▸ hx)) hzO
      (by rw [hz]; exact (c.isZeroAt_iff hf.1 hxV).1 hx₀) x⟩
  set L := (linAt c.U c.R (c.principal f) 0).codRestrict _ hmem with hLdef
  obtain ⟨hF, hind, hsurj⟩ := StrongBundle.linAt_index_of_conjugationData hf hx₀ hc hxV
    hφ0 h0 hfill hG hDg hs hs0 dc₀ hc hxV hz hzU L fun _ => rfl
  have hk := finrank_ker_eq_fredholmIndex_of_surjective hF (hsurj hgp)
  refine ⟨finrank ℝ (LinearMap.ker (L : ↥(rangeS (scDeriv c.U (r c.R) 0)) →ₗ[ℝ]
    ↥(rangeS (ρCLM c.isRetraction hzU)))), ?_, c, hc, hxV, hφ0, h0, g, s, hfill, hs, hs0, G, Dg,
    hG, hDg, hgp, ⟨dc₀⟩, fun dc => ?_⟩
  · exact StrongBundle.isSurjLinOfIndex_of_conjugationData hf hx₀ hc hxV hφ0 h0 hfill hG
      hDg hs hs0 hgp dc₀ (by rw [hk, hind])
  · rw [hk, (StrongBundle.linAt_index_of_conjugationData hf hx₀ hc hxV hφ0 h0 hfill hG hDg
      hs hs0 dc hc hxV hz hzU L fun _ => rfl).2.1]

/-- **Definition 3.6.6 (preprint 3.53) is surjectivity of `f'(y)` plus the kernel condition, germ reading** (phase
2; the germ form of `StrongBundle.IsGoodPositionGermWholeChart.isLinSurjAt`): at a zero in good position in
the germ reading, `f'(y)` is onto in the chart of Definition 3.6.6 (preprint 3.53) (`IsLinSurjAt`;
`Lin(0) = Dg(0)` on `T₀O` for the derivative family `Dg` of the filling germ, `linAt_eq_germDeriv`
at the point `0` of the germ). -/
theorem StrongBundle.IsGoodPositionGerm.isLinSurjAt (hf : B.IsScSmoothSection f) {y : X}
    (hg : B.IsGoodPositionGerm f y) : B.IsLinSurjAt f y := by
  obtain ⟨-, c, hc, hyV, hφ0, h0, g, s, hfill, -, -, -, G, Dg, -, hDg, hgp⟩ := hg
  have h0O : (0 : c.φ.model.E 0) ∈ r c.R '' c.U := by
    rw [c.r_image, ← hφ0]; exact c.φ.mapsTo_model y hyV
  have hz : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) = c.φ y := by rw [map_zero, hφ0]
  refine ⟨c, hc, hyV, 0, hz, fun k hk => ?_⟩
  rw [hφ0] at hk
  obtain ⟨x, hx, hxk⟩ := hgp.surj k ((mem_rangeS_ρCLM_iff c.isRetraction h0O h0).2 hk)
  refine ⟨⟨x, hx⟩, ?_⟩
  rw [linAt_eq_germDeriv c.relOpen c.isRetraction h0 h0O (hf.isSc1_principal_comp_r hc) hDg
    (by rw [map_zero]; exact h0O) (G.zero_mem 1) (by rw [map_zero]; exact hfill.eq_on)]
  exact hxk

/-- **Good position is surjectivity when `d_X(y) = 0`, germ reading** (phase 2; the germ form of
`StrongBundle.isGoodPositionGerm_of_linAt_surj_of_degIndex_eq_zero_wholeChart`; the text before Theorem
3.56).  Let `(f, y)` be an sc-Fredholm germ in the germ reading at a zero `y` with `d_X(y) = 0`,
and let the linearization `Lin(z)` in a strong bundle chart `c` with tame base retraction, at the
level-`1` point `z` over `ϕ(y)`, map onto `K_z`.  Then `(f, y)` is in good position in the germ
reading: in the tame chart the partial quadrant `C_{ϕ(y)}` is the whole space, so the kernel
condition holds for any subspace, and `isGoodPositionGerm_of_linAt_surj` (no Proposition 3.6.5 (preprint 3.52))
applies. -/
theorem StrongBundle.isGoodPositionGerm_of_linAt_surj_of_degIndex_eq_zero
    (hf : B.IsScSmoothSection f) {y : X} (hy : B.IsScFredholmGerm f y) (hy0 : IsZeroAt P f y)
    (hd : PX.degIndex y = 0) {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (hyV : y ∈ c.φ.source) (htame : (c.isRetraction.baseRetraction c.relOpen).IsTame)
    {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z = c.φ y)
    (hsurj : ∀ k, (c.φ y, k) ∈ c.K → ∃ x, linAt c.U c.R (c.principal f) z x = k) :
    B.IsGoodPositionGerm f y := by
  obtain ⟨n, Wq, T, hT⟩ := c.φ.model.isPartialQuadrant
  have htameO : IsTameRetract c.φ.model.E c.φ.model.C c.φ.model.O :=
    ⟨c.isRetraction.baseRetraction c.relOpen, c.base_retract, htame⟩
  -- `d_C(ϕ(y)) = d_X(y) = 0` in the tame chart: no coordinate vanishes at `ϕ(y)`
  have hdeg : degIndexWith T (c.φ y) = 0 := by
    have h1 := PX.degIndex_eq_chartDegIndex_of_isTameRetract c.isChart htameO hyV
    rw [hd, MPolyfold.chartDegIndex, degIndex_eq T hT (c.φ.apply_mem_C hyV)] at h1
    exact h1.symm
  have hcoord : ∀ i, (T 0 (c.φ y)).1 i ≠ 0 := by
    simp only [degIndexWith, quadrantDeg, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
      Finset.mem_univ, true_implies] at hdeg
    exact hdeg
  have huniv : partialQuadrantAtWith T (c.φ y) = univ :=
    eq_univ_of_forall fun v i hi => absurd hi (hcoord i)
  refine StrongBundle.isGoodPositionGerm_of_linAt_surj hf hy hy0 hc hyV hz T hT hsurj ?_
  rw [huniv]
  exact isInGoodPositionIn_of_subset (Submodule.map_subtype_le _ _) (subset_univ _)

/-- **Good position from "`f'(y)` surjective" when `d_X(y) = 0`, germ reading** (phase 2; the germ
form of `StrongBundle.isGoodPositionGerm_of_isLinSurjAt_wholeChart`), for an sc-Fredholm section with tame
germ data in the germ reading (`IsScFredholmSectionTame`; `IsLinSurjAt`, the text's hypothesis of
Theorems 3.1.22 and 3.6.10 (preprint 3.19 and 3.56)): the surjectivity holds in the tame chart `c` of the germ data at `y`
(`IsLinSurjAt.linAt_surjective`), where `d_C(ϕ(y)) = d_X(y) = 0`
(`isGoodPositionGerm_of_linAt_surj_of_degIndex_eq_zero`); the good position is then read in that
tame chart (`IsGoodPositionGerm.toTame`). -/
theorem StrongBundle.isGoodPositionGerm_of_isLinSurjAt (hf : B.IsScFredholmSectionTame f)
    {y : X} (hy0 : IsZeroAt P f y) (hd : PX.degIndex y = 0)
    (hsurj : B.IsLinSurjAt f y) : B.IsGoodPositionGermTame f y := by
  have hys := hf.mem_smoothSet_of_isZeroAt hy0
  obtain ⟨-, c, hct, hyV, hφ0, -⟩ := hf.germTame y hys
  have hz : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) = c.φ y := by rw [map_zero, hφ0]
  exact (StrongBundle.isGoodPositionGerm_of_linAt_surj_of_degIndex_eq_zero hf.isScSmooth
    (hf.germ y hys) hy0 hd hct.1 hyV hct.2 hz
    (hsurj.linAt_surjective hf.isScSmooth hy0 hct.1 hyV hz)).toTame hf.isScSmooth
    (hf.germTame y hys) hy0

/-- **"Good position = surjectivity" when `d_X(y) = 0`, germ reading** (phase 2; the germ form of
`StrongBundle.isGoodPositionGerm_iff_isLinSurjAt_wholeChart`): for an sc-Fredholm section with tame germ data
in the germ reading and a zero `y` with `d_X(y) = 0`, `(f, y)` is in good position in a tame chart
(germ reading) iff `f'(y)` is surjective. -/
theorem StrongBundle.isGoodPositionGerm_iff_isLinSurjAt (hf : B.IsScFredholmSectionTame f)
    {y : X} (hy0 : IsZeroAt P f y) (hd : PX.degIndex y = 0) :
    B.IsGoodPositionGermTame f y ↔ B.IsLinSurjAt f y :=
  ⟨fun hg => hg.isGoodPositionGerm.isLinSurjAt hf.isScSmooth,
    StrongBundle.isGoodPositionGerm_of_isLinSurjAt hf hy0 hd⟩

/-- **Theorem 3.1.22 (preprint 3.19), the first clause, with the index, germ reading** (phase 2; the germ form of
`theorem_3_1_22_linearization_index_wholeChart`): for an sc-Fredholm section in the germ reading and a zero
`x₀` in good position (germ reading), in the chart of Definition 3.6.6 (preprint 3.53) with the filling germ `g`
(sc-smooth on the germ `G ⊆ U`, derivative family `Dg`), `Dg(0)` and
`f'(x₀) = Tf̃(0) = Dg(0)|_{T₀O} : T₀O → K₀` are Fredholm, `Tf̃(0)` is onto, and for **every**
conjugation `d` of `g − s` to a basic germ: `ind Dg(0) = ind Tf̃(0) = dim ker Tf̃(0) = n − N`
(`proposition_3_6_5_local_index`). -/
theorem theorem_3_1_22_linearization_index (hf : B.IsScFredholmSection f) {x₀ : X}
    (hx₀ : IsZeroAt P f x₀) (hg : B.IsGoodPositionGerm f x₀) :
    ∃ (c : StrongBundleChart PX P) (_ : B.IsChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
      (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0) (s : c.φ.model.E 0 → c.F 1)
      (_ : IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g)
      (_ : IsScPlusGerm c.φ.model.C c.U s) (_ : c.F.toBase 1 (s 0) = g 0)
      (_ : Nonempty (ConjugationData c.U fun u => g u - c.F.toBase 1 (s u)))
      (G : ScNbhdGerm c.φ.model.E c.φ.model.C) (_ : G.U 0 ⊆ c.U) (_ : IsScSmoothGerm G g)
      (Dg : c.φ.model.E 1 → c.φ.model.E 0 →L[ℝ] c.F 0) (_ : IsSc1GermWith G g Dg)
      (h1 : ∀ x, ρCLM c.isRetraction h0 (Dg 0 (scDeriv c.U (r c.R) 0 x)) =
        Dg 0 (scDeriv c.U (r c.R) 0 x)),
      (Dg 0).IsFredholm ∧
      (fillerRestrict (scDeriv c.U (r c.R) 0) (ρCLM c.isRetraction h0) (Dg 0) h1).IsFredholm ∧
      Surjective (fillerRestrict (scDeriv c.U (r c.R) 0) (ρCLM c.isRetraction h0) (Dg 0) h1) ∧
      ∀ d : ConjugationData c.U (fun u => g u - c.F.toBase 1 (s u)),
        fredholmIndex (Dg 0) = finrank ℝ d.Pn - finrank ℝ d.Q ∧
        fredholmIndex (fillerRestrict (scDeriv c.U (r c.R) 0) (ρCLM c.isRetraction h0)
          (Dg 0) h1) = finrank ℝ d.Pn - finrank ℝ d.Q ∧
        (finrank ℝ (LinearMap.ker (fillerRestrict (scDeriv c.U (r c.R) 0)
          (ρCLM c.isRetraction h0) (Dg 0) h1 : ↥(rangeS (scDeriv c.U (r c.R) 0)) →ₗ[ℝ]
            ↥(rangeS (ρCLM c.isRetraction h0)))) : ℤ) = finrank ℝ d.Pn - finrank ℝ d.Q := by
  obtain ⟨-, c, hc, hxV, hφ0, h0U, g, s, hfill, hsp, hs0, hconj, G₀, Dg₀, -, hDg₀, hgp₀⟩ := hg
  obtain ⟨Gs, -, hs⟩ := id hsp
  obtain ⟨h0O, hfb0, hfK⟩ := c.zero_data hf.isScSmooth.1 hxV hφ0 hx₀
  obtain ⟨G, hGU, hgG, -⟩ := hfill.germ
  have hg1 := (hgG 1).1.isSc1GermWith_scDerivGerm
  have hs1 := (hs 1).1.isSc1GermWith_scDerivGerm
  have hgp : IsGoodPositionAtGerm c.relOpen c.isRetraction h0U (scDerivGerm G g 0) :=
    hgp₀.of_isSc1GermWith c.isQuadrantLike hDg₀ hg1
  obtain ⟨d₀⟩ := isConjugateToBasicGerm_iff_nonempty.1 hconj
  obtain ⟨h1, hDgF, -, hTF, -⟩ :=
    proposition_3_6_5_local_index c.relOpen c.isRetraction h0U h0O hfill hfb0 hfK hGU hg1 hs1
      hs0 d₀
  have hTs := hgp.surjective_fillerRestrict h1
  refine ⟨c, hc, hxV, hφ0, h0U, g, s, hfill, hsp, hs0, ⟨d₀⟩, G, hGU, hgG, _, hg1, h1, hDgF, hTF,
    hTs, fun d => ?_⟩
  obtain ⟨h1', -, hDgind, -, hTind⟩ :=
    proposition_3_6_5_local_index c.relOpen c.isRetraction h0U h0O hfill hfb0 hfK hGU hg1 hs1
      hs0 d
  exact ⟨hDgind, hTind, by rw [finrank_ker_eq_fredholmIndex_of_surjective hTF hTs, hTind]⟩

end Bundle

/-! ### Dimension = index, germ reading -/

section DimIndex

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

open StrongRetr

/-- **Theorem 3.6.8 (preprint 3.54) (2) at the centre, with "dimension = Fredholm index", germ reading** (phase 2;
the germ form of `theorem_3_6_8_tangentGermChart_index_wholeChart`): the data of Definition 3.2.1 (preprint 3.25) (2) for
`S = {y ∈ Vx | f(y) = 0}` at `x₀` of `theorem_3_6_8_tangentGermChart_proj` have dimension `d`
with `IsSurjLinOfIndex f x₀ d`: in every strong bundle chart around `x₀`, `f'(x₀)` is onto,
Fredholm, and `ind f'(x₀) = dim ker f'(x₀) = d`
(`theorem_3_6_8_tangentGermChart_proj_conj`: `d = n − N`;
`isSurjLinOfIndex_of_conjugationData`). -/
theorem theorem_3_6_8_tangentGermChart_index (hf : B.IsScSmoothSection f) {x₀ : X}
    (hg : B.IsGoodPositionGermTame f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ (Vx : Set X) (d : ℕ), IsOpen Vx ∧ x₀ ∈ Vx ∧
      (∃ D : PX.TangentGermChart {y ∈ Vx | IsZeroAt P f y} x₀ d,
        ∀ z ∈ D.φ.model.O, (D.π z : D.φ.model.E 0) ∈ D.φ.model.C) ∧
      B.IsSurjLinOfIndex f x₀ d := by
  obtain ⟨Vx, d, hVxo, hx₀Vx, hD, c, hc, hxV, hφ0, h0, g, s, hfill, hs, hs0, G, Dg, hG, hDg, hgp,
    dc, hd⟩ := theorem_3_6_8_tangentGermChart_proj_conj hf.1 hg hx₀
  exact ⟨Vx, d, hVxo, hx₀Vx, hD, StrongBundle.isSurjLinOfIndex_of_conjugationData hf hx₀
    hc.1 hxV hφ0 h0 hfill hG hDg hs hs0 hgp dc hd⟩

/-- **The data of Definition 3.2.1 (preprint 3.25) (2) for the global solution set at a zero in good position,
with the dimension the Fredholm index, germ reading** (phase 2; the germ form of
`theorem_3_6_8_tangentGermChart_solutionSet_index_wholeChart`). -/
theorem theorem_3_6_8_tangentGermChart_solutionSet_index (hf : B.IsScSmoothSection f)
    {x₀ : X} (hg : B.IsGoodPositionGermTame f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ d : ℕ, (∃ D : PX.TangentGermChart (solutionSet P f) x₀ d,
      ∀ z ∈ D.φ.model.O, (D.π z : D.φ.model.E 0) ∈ D.φ.model.C) ∧ B.IsSurjLinOfIndex f x₀ d := by
  obtain ⟨Vx, d, hVxo, hx₀Vx, ⟨D, hπ⟩, hind⟩ :=
    theorem_3_6_8_tangentGermChart_index hf hg hx₀
  have hs : D.φ.source ∩ Vx ⊆ D.φ.source := inter_subset_left
  have hso : IsOpen (D.φ.source ∩ Vx) := D.φ.isOpen_source.inter hVxo
  have hxs : x₀ ∈ D.φ.source ∩ Vx := ⟨D.mem_source, hx₀Vx⟩
  have himage : D.φ '' (solutionSet P f ∩ (D.φ.source ∩ Vx)) =
      (fun v : D.N => (v : D.φ.model.E 0) + D.δ v) '' D.V := by
    rw [← D.image_eq]
    congr 1
    ext y
    constructor
    · rintro ⟨hyS, hysrc, hyVx⟩; exact ⟨⟨hyVx, hyS⟩, hysrc⟩
    · rintro ⟨⟨hyVx, hyS⟩, hysrc⟩; exact ⟨hyS, hysrc, hyVx⟩
  refine ⟨d, ⟨D.shrink (solutionSet P f) hs hso hxs D.V_relOpen D.zero_mem_V subset_rfl himage,
    fun z hz => ?_⟩, hind⟩
  rw [D.shrink_π]
  exact hπ z (D.φ.image_subset_model hs hz)

/-- **Theorem 3.6.8 (preprint 3.54) (2) with "dimension = Fredholm index", germ reading** (phase 2; the germ form of
`theorem_3_6_8_two_index_wholeChart`): `theorem_3_6_8_two` with in addition `IsSurjLinOfIndex f x₀ d`. -/
theorem theorem_3_6_8_two_index (hf : B.IsScSmoothSection f) {x₀ : X}
    (hg : B.IsGoodPositionGermTame f x₀) (hx₀ : IsZeroAt P f x₀)
    {Vx₀ : Set X} (hVx₀ : IsOpen Vx₀) (hx₀V : x₀ ∈ Vx₀)
    (hall : ∀ y ∈ Vx₀, IsZeroAt P f y → B.IsGoodPositionGermTame f y) :
    ∃ d : ℕ, ∃ D : PX.TangentGermChart (solutionSet P f) x₀ d, D.IsRegular ∧ D.φ.source ⊆ Vx₀ ∧
      (∀ y ∈ solutionSet P f ∩ D.φ.source,
        ∀ (n' : ℕ) (_ : PX.TangentGermChart (solutionSet P f) y n'), n' = d) ∧
      B.IsSurjLinOfIndex f x₀ d := by
  obtain ⟨d, ⟨D, hπ⟩, hind⟩ := theorem_3_6_8_tangentGermChart_solutionSet_index hf hg hx₀
  have hM : ∀ y ∈ solutionSet P f ∩ Vx₀,
      ∃ n' : ℕ, Nonempty (PX.TangentGermChart (solutionSet P f) y n') := fun y hy => by
    obtain ⟨d', D', -⟩ :=
      theorem_3_6_8_tangentGermChart_solutionSet hf.1 (hall y hy.2 hy.1) hy.1
    exact ⟨d', ⟨D'⟩⟩
  obtain ⟨D', hreg, hsub, hdim⟩ := D.exists_isRegular_of_locally hπ hVx₀ hx₀V hM
  exact ⟨d, D', hreg, hsub, hdim, hind⟩

/-- At a zero `y` in good position (germ reading) at which every datum of Definition 3.2.1 (preprint 3.25) (2) of
the solution set has dimension `d`, `f'(y)` is onto of index `d` (germ reading, phase 2; the germ
form of `isSurjLinOfIndex_of_forall_dim_wholeChart`). -/
theorem isSurjLinOfIndex_of_forall_dim (hf : B.IsScSmoothSection f)
    {y : X} (hgy : B.IsGoodPositionGermTame f y) (hy0 : IsZeroAt P f y) {d : ℕ}
    (hdim : ∀ (n' : ℕ) (_ : PX.TangentGermChart (solutionSet P f) y n'), n' = d) :
    B.IsSurjLinOfIndex f y d := by
  obtain ⟨dy, ⟨Dy, -⟩, hindy⟩ := theorem_3_6_8_tangentGermChart_solutionSet_index hf hgy hy0
  rw [← hdim dy Dy]
  exact hindy

/-- **The Fredholm index is locally constant along the solution set, germ reading** (phase 2; the
germ form of `theorem_3_6_8_index_locally_constant_wholeChart`; Proposition 6.2.2 (preprint 6.2) of the text along `S`).  For an
sc-Fredholm section with tame germ data in the germ reading (`IsScFredholmSectionTame`),
`f(x₀) = 0` and `(f, x₀)` in good position in a tame chart (germ reading), there are an open
`Vx ∋ x₀` and `d` such that at every zero `y ∈ Vx`, `f'(y)` is onto with
`ind f'(y) = dim ker f'(y) = d` (`IsSurjLinOfIndex`, in every chart).  Proof: Theorem 3.6.8 (preprint 3.54) (1)
(`theorem_3_6_8_one'`), the local constancy of the dimension (`theorem_3_6_8_two_index`),
dimension = index at each zero (`isSurjLinOfIndex_of_forall_dim`). -/
theorem theorem_3_6_8_index_locally_constant (hf : B.IsScFredholmSectionTame f) {x₀ : X}
    (hg : B.IsGoodPositionGermTame f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ (Vx : Set X) (d : ℕ), IsOpen Vx ∧ x₀ ∈ Vx ∧
      ∀ y ∈ Vx, IsZeroAt P f y → B.IsSurjLinOfIndex f y d := by
  obtain ⟨Vx₁, hVx₁o, hx₀Vx₁, hall⟩ := theorem_3_6_8_one' hf hg hx₀
  obtain ⟨d, D, -, hsub, hdim, -⟩ :=
    theorem_3_6_8_two_index hf.isScSmooth hg hx₀ hVx₁o hx₀Vx₁ hall
  exact ⟨D.φ.source, d, D.φ.isOpen_source, D.mem_source, fun y hy hy0 =>
    isSurjLinOfIndex_of_forall_dim hf.isScSmooth (hall y (hsub hy) hy0) hy0
      (hdim y ⟨hy0, hy⟩)⟩

/-- **Theorem 3.6.8 (preprint 3.54) (1) and (2) with the text's hypotheses and the index, germ reading** (phase 2;
the germ form of `theorem_3_6_8_index_wholeChart`): for an sc-Fredholm section with tame germ data in the germ
reading, `f(x₀) = 0` and `(f, x₀)` in good position in a tame chart, there are an open `Vx ∋ x₀`
and `d` with: (1) at every zero `y ∈ Vx`, `(f, y)` is in good position in a tame chart (germ
reading) and `f'(y)` is onto with `ind f'(y) = dim ker f'(y) = d`; (2) the solution set has at
`x₀` regular data of Definition 3.2.1 (preprint 3.25) (2) of dimension `d` on the chart domain `Vx`, every datum at
a point of `Vx` having dimension `d`. -/
theorem theorem_3_6_8_index (hf : B.IsScFredholmSectionTame f) {x₀ : X}
    (hg : B.IsGoodPositionGermTame f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ (Vx : Set X) (d : ℕ), IsOpen Vx ∧ x₀ ∈ Vx ∧
      (∀ y ∈ Vx, IsZeroAt P f y → B.IsGoodPositionGermTame f y ∧ B.IsSurjLinOfIndex f y d) ∧
      ∃ D : PX.TangentGermChart (solutionSet P f) x₀ d, D.IsRegular ∧ D.φ.source = Vx ∧
        ∀ y ∈ solutionSet P f ∩ D.φ.source,
          ∀ (n' : ℕ) (_ : PX.TangentGermChart (solutionSet P f) y n'), n' = d := by
  obtain ⟨Vx₁, hVx₁o, hx₀Vx₁, hall⟩ := theorem_3_6_8_one' hf hg hx₀
  obtain ⟨d, D, hreg, hsub, hdim, -⟩ :=
    theorem_3_6_8_two_index hf.isScSmooth hg hx₀ hVx₁o hx₀Vx₁ hall
  exact ⟨D.φ.source, d, D.φ.isOpen_source, D.mem_source, fun y hy hy0 =>
    ⟨hall y (hsub hy) hy0, isSurjLinOfIndex_of_forall_dim hf.isScSmooth
      (hall y (hsub hy) hy0) hy0 (hdim y ⟨hy0, hy⟩)⟩, D, hreg, rfl, hdim⟩

/-- **Theorem 3.1.26 (preprint 3.23) with the text's hypotheses, the dimension equal to the Fredholm index, germ
reading** (phase 2; the germ form of `theorem_3_1_26_index_wholeChart`): an sc-Fredholm section with tame germ
data in the germ reading, `f(x) = 0`, `(f, x)` in good position in a tame chart.  Then there are an
open `U ∋ x` and `d` such that every zero `y ∈ U` is in good position in a tame chart with `f'(y)`
onto and `ind f'(y) = dim ker f'(y) = d`, `S(f, U)` consists of smooth points, is a sub-M-polyfold
of `X`, and its induced structure is tame and that of a `d`-dimensional manifold with boundary
with corners. -/
theorem theorem_3_1_26_index (hf : B.IsScFredholmSectionTame f) {x : X}
    (hx : IsZeroAt P f x) (hg : B.IsGoodPositionGermTame f x) :
    ∃ (U : Set X) (d : ℕ), IsOpen U ∧ x ∈ U ∧
      (∀ y ∈ U, IsZeroAt P f y → B.IsGoodPositionGermTame f y ∧ B.IsSurjLinOfIndex f y d) ∧
      (∀ y ∈ U, IsZeroAt P f y → y ∈ PX.smoothSet) ∧
      ∃ hsub : PX.IsSubMPolyfold {y ∈ U | IsZeroAt P f y},
        haveI := PX.paracompactSpace_subtype {y ∈ U | IsZeroAt P f y}
        (MPolyfold.subPolyfold hsub).IsTame ∧
          (MPolyfold.subPolyfold hsub).IsManifoldWithCorners d := by
  obtain ⟨Vx, hVxo, hxVx, hall⟩ := theorem_3_6_8_one' hf hg hx
  obtain ⟨d, D, -, hsub, hdim, -⟩ :=
    theorem_3_6_8_two_index hf.isScSmooth hg hx hVxo hxVx hall
  set U := D.φ.source with hU
  set S' := {y ∈ U | IsZeroAt P f y} with hS'
  -- every point of `S(f, U)` has regular data of Definition 3.2.1 (preprint 3.25) (2) for `S(f, U)` of dimension `d`
  have hS'reg : ∀ y ∈ S', ∃ d' : PX.TangentGermChart S' y d, d'.IsRegular := by
    intro y hy
    obtain ⟨dy, Dy, hregy, hsuby, -⟩ := theorem_3_6_8_two hf.isScSmooth.1
      (hall y (hsub hy.1) hy.2) hy.2 (D.φ.isOpen_source.inter hVxo) ⟨hy.1, hsub hy.1⟩
      fun z hz hz0 => hall z hz.2 hz0
    have hdy : dy = d := hdim y ⟨hy.2, hy.1⟩ dy Dy
    subst hdy
    have himage : Dy.φ '' (S' ∩ Dy.φ.source) =
        (fun v : Dy.N => (v : Dy.φ.model.E 0) + Dy.δ v) '' Dy.V := by
      rw [← Dy.image_eq]
      congr 1
      ext z
      constructor
      · rintro ⟨⟨-, hz0⟩, hzsrc⟩; exact ⟨hz0, hzsrc⟩
      · rintro ⟨hz0, hzsrc⟩; exact ⟨⟨(hsuby hzsrc).1, hz0⟩, hzsrc⟩
    exact ⟨Dy.shrink S' subset_rfl Dy.φ.isOpen_source Dy.mem_source Dy.V_relOpen Dy.zero_mem_V
      subset_rfl himage, Dy.shrink_isRegular S' subset_rfl Dy.φ.isOpen_source Dy.mem_source
      Dy.V_relOpen Dy.zero_mem_V subset_rfl himage hregy.isScSmooth hregy.π_mem⟩
  have hne : S'.Nonempty := ⟨x, D.mem_source, hx⟩
  obtain ⟨hsubM, htameS, hman, -⟩ := theorem_3_2_3_of_isRegular PX hne hS'reg
  exact ⟨U, d, D.φ.isOpen_source, D.mem_source, fun y hy hy0 =>
    ⟨hall y (hsub hy) hy0, isSurjLinOfIndex_of_forall_dim hf.isScSmooth
      (hall y (hsub hy) hy0) hy0 (hdim y ⟨hy0, hy⟩)⟩,
    fun y _ hy => hf.mem_smoothSet_of_isZeroAt hy, hsubM, htameS, hman⟩

/-- **Theorem 3.1.22 (preprint 3.19) (implicit function theorem, interior case) with the text's hypotheses, the
index and tameness, germ reading** (phase 2; the germ form of `theorem_3_1_22_index_wholeChart`): for an
M-polyfold without boundary, an sc-Fredholm section with tame germ data in the germ reading,
`f(x₀) = 0` and `(f, x₀)` in good position in a tame chart, there are an open `U ∋ x₀` and `d`
such that at every zero `y ∈ U`, `(f, y)` is in good position in a tame chart and `f'(y)` is onto
with `ind f'(y) = dim ker f'(y) = d`; `S(f, U)` consists of smooth points and is a sub-M-polyfold
whose induced structure is tame and that of a `d`-dimensional manifold without boundary — "whose
dimension agrees with the Fredholm index of `f'(x₀)`". -/
theorem theorem_3_1_22_index (hX : PX.IsWithoutBoundary) (hf : B.IsScFredholmSectionTame f)
    {x₀ : X} (hx₀ : IsZeroAt P f x₀) (hg : B.IsGoodPositionGermTame f x₀) :
    ∃ (U : Set X) (d : ℕ), IsOpen U ∧ x₀ ∈ U ∧
      (∀ y ∈ U, IsZeroAt P f y → B.IsGoodPositionGermTame f y ∧ B.IsSurjLinOfIndex f y d) ∧
      (∀ y ∈ U, IsZeroAt P f y → y ∈ PX.smoothSet) ∧
      ∃ hsub : PX.IsSubMPolyfold {y ∈ U | IsZeroAt P f y},
        haveI := PX.paracompactSpace_subtype {y ∈ U | IsZeroAt P f y}
        (MPolyfold.subPolyfold hsub).IsTame ∧
          (MPolyfold.subPolyfold hsub).IsManifoldWithCorners d ∧
          (MPolyfold.subPolyfold hsub).IsWithoutBoundary := by
  obtain ⟨U, d, hUo, hxU, hgood, hsm, hsub, h1, h2⟩ := theorem_3_1_26_index hf hx₀ hg
  have := PX.paracompactSpace_subtype {y ∈ U | IsZeroAt P f y}
  refine ⟨U, d, hUo, hxU, hgood, hsm, hsub, h1, h2, fun y => ?_⟩
  have := lemma_2_4_6 hsub y
  rw [hX y.1] at this
  exact Nat.le_zero.1 this

/-- **Theorem 3.1.22 (preprint 3.19) with the text's hypothesis "`f'(x₀)` surjective", germ reading** (phase 2; the
germ form of `theorem_3_1_22_of_surjective_wholeChart`): for an M-polyfold without boundary good position is
surjectivity (`isGoodPositionGerm_of_isLinSurjAt`), and `theorem_3_1_22_index` applies. -/
theorem theorem_3_1_22_of_surjective (hX : PX.IsWithoutBoundary)
    (hf : B.IsScFredholmSectionTame f) {x₀ : X} (hx₀ : IsZeroAt P f x₀)
    (hsurj : B.IsLinSurjAt f x₀) :
    ∃ (U : Set X) (d : ℕ), IsOpen U ∧ x₀ ∈ U ∧
      (∀ y ∈ U, IsZeroAt P f y → B.IsGoodPositionGermTame f y ∧ B.IsSurjLinOfIndex f y d) ∧
      (∀ y ∈ U, IsZeroAt P f y → y ∈ PX.smoothSet) ∧
      ∃ hsub : PX.IsSubMPolyfold {y ∈ U | IsZeroAt P f y},
        haveI := PX.paracompactSpace_subtype {y ∈ U | IsZeroAt P f y}
        (MPolyfold.subPolyfold hsub).IsTame ∧
          (MPolyfold.subPolyfold hsub).IsManifoldWithCorners d ∧
          (MPolyfold.subPolyfold hsub).IsWithoutBoundary :=
  theorem_3_1_22_index hX hf hx₀
    (StrongBundle.isGoodPositionGerm_of_isLinSurjAt hf hx₀ (hX x₀) hsurj)

/-- **Theorem 3.6.11 (preprint 3.57) with the index, germ reading** (phase 2; the germ form of `theorem_3_6_11_index_wholeChart`):
`theorem_3_6_11` with, at every zero `x`, regular data of Definition 3.2.1 (preprint 3.25) (2) of a dimension `d`
which is constant near `x` along the solution set and equal to `ind f'(y) = dim ker f'(y)` at
every zero `y` of the chart domain. -/
theorem theorem_3_6_11_index (hf : B.IsScFredholmSection f)
    (hall : ∀ x, IsZeroAt P f x → B.IsGoodPositionGermTame f x)
    (hne : (solutionSet P f).Nonempty) :
    ∃ hsub : PX.IsSubMPolyfold (solutionSet P f),
      haveI := PX.paracompactSpace_subtype (solutionSet P f)
      (MPolyfold.subPolyfold hsub).IsTame ∧
        (MPolyfold.subPolyfold hsub).IsManifoldWithCornersLoc ∧
        ∀ x ∈ solutionSet P f, ∃ d : ℕ, ∃ D : PX.TangentGermChart (solutionSet P f) x d,
          D.IsRegular ∧ (∀ y ∈ solutionSet P f ∩ D.φ.source,
            ∀ (n' : ℕ) (_ : PX.TangentGermChart (solutionSet P f) y n'), n' = d) ∧
          ∀ y ∈ solutionSet P f ∩ D.φ.source, B.IsSurjLinOfIndex f y d := by
  obtain ⟨hsub, h1, h2, -⟩ := theorem_3_6_11 hf hall hne
  refine ⟨hsub, h1, h2, fun x hx => ?_⟩
  obtain ⟨d, D, hreg, -, hdim, -⟩ := theorem_3_6_8_two_index hf.isScSmooth (hall x hx) hx
    isOpen_univ (mem_univ x) fun y _ hy => hall y hy
  exact ⟨d, D, hreg, hdim, fun y hy =>
    isSurjLinOfIndex_of_forall_dim hf.isScSmooth (hall y hy.1) hy.1 (hdim y hy)⟩

/-- **Theorem 3.6.10 (preprint 3.56) with the tameness and the regular data, germ reading** (phase 2; the germ form
of `theorem_3_6_10_tame_wholeChart`): for an M-polyfold without boundary and an sc-Fredholm section in the germ
reading in good position in a tame chart at every zero, the solution set is a sub-M-polyfold whose
induced structure is tame, that of a manifold without boundary of locally constant dimension,
with regular data of Definition 3.2.1 (preprint 3.25) (2) at every zero whose dimension is the Fredholm index. -/
theorem theorem_3_6_10_tame (hX : PX.IsWithoutBoundary) (hf : B.IsScFredholmSection f)
    (hall : ∀ x, IsZeroAt P f x → B.IsGoodPositionGermTame f x)
    (hne : (solutionSet P f).Nonempty) :
    ∃ hsub : PX.IsSubMPolyfold (solutionSet P f),
      haveI := PX.paracompactSpace_subtype (solutionSet P f)
      (MPolyfold.subPolyfold hsub).IsTame ∧
        (MPolyfold.subPolyfold hsub).IsManifoldWithCornersLoc ∧
        (MPolyfold.subPolyfold hsub).IsWithoutBoundary ∧
        ∀ x ∈ solutionSet P f, ∃ d : ℕ, ∃ D : PX.TangentGermChart (solutionSet P f) x d,
          D.IsRegular ∧ (∀ y ∈ solutionSet P f ∩ D.φ.source,
            ∀ (n' : ℕ) (_ : PX.TangentGermChart (solutionSet P f) y n'), n' = d) ∧
          ∀ y ∈ solutionSet P f ∩ D.φ.source, B.IsSurjLinOfIndex f y d := by
  have := PX.paracompactSpace_subtype (solutionSet P f)
  obtain ⟨hsub, h1, h2, h3⟩ := theorem_3_6_11_index hf hall hne
  refine ⟨hsub, h1, h2, fun y => ?_, h3⟩
  have := lemma_2_4_6 hsub y
  rw [hX y.1] at this
  exact Nat.le_zero.1 this

/-- **Theorem 3.6.10 (preprint 3.56) with the text's hypothesis "`f'(x)` surjective at every zero", germ reading**
(phase 2; the germ form of `theorem_3_6_10_of_surjective_wholeChart`): for an M-polyfold without boundary good
position is surjectivity (`isGoodPositionGerm_of_isLinSurjAt`), and `theorem_3_6_10_tame`
applies. -/
theorem theorem_3_6_10_of_surjective (hX : PX.IsWithoutBoundary)
    (hf : B.IsScFredholmSectionTame f) (hall : ∀ x, IsZeroAt P f x → B.IsLinSurjAt f x)
    (hne : (solutionSet P f).Nonempty) :
    ∃ hsub : PX.IsSubMPolyfold (solutionSet P f),
      haveI := PX.paracompactSpace_subtype (solutionSet P f)
      (MPolyfold.subPolyfold hsub).IsTame ∧
        (MPolyfold.subPolyfold hsub).IsManifoldWithCornersLoc ∧
        (MPolyfold.subPolyfold hsub).IsWithoutBoundary ∧
        ∀ x ∈ solutionSet P f, ∃ d : ℕ, ∃ D : PX.TangentGermChart (solutionSet P f) x d,
          D.IsRegular ∧ (∀ y ∈ solutionSet P f ∩ D.φ.source,
            ∀ (n' : ℕ) (_ : PX.TangentGermChart (solutionSet P f) y n'), n' = d) ∧
          ∀ y ∈ solutionSet P f ∩ D.φ.source, B.IsSurjLinOfIndex f y d :=
  theorem_3_6_10_tame hX hf.toIsScFredholmSection
    (fun x hx => StrongBundle.isGoodPositionGerm_of_isLinSurjAt hf hx (hX x) (hall x hx)) hne

set_option maxHeartbeats 1600000 in
-- destructuring the large existential conclusion of `theorem_3_6_8_nearby_kernel`
/-- **"`ker f'(y) = T_yS`", in a chart, germ reading** (phase 2; the germ form of
`theorem_3_6_8_ker_eq_tangent_wholeChart`; Theorem 3.1.22 (preprint 3.19) (3) and Theorem 3.6.8 (preprint 3.54) (4)).  For a section of a strong
bundle, `f(x₀) = 0` and `(f, x₀)` in good position in a tame chart in the germ reading, there are
the tame strong bundle chart `c` centred at `x₀`, the conjugating sc-diffeomorphism
`ψ : U → U' ⊆ C'` (inverse `ψ'`, `ψ(0) = 0`), the finite-dimensional kernel `K = ker D(h + t)(0)`,
the solution graph `σ : V' → E'`, an open `Vx ∋ x₀` with
`ψ ∘ ϕ({y ∈ Vx | f(y) = 0}) = {v + σ(v) | v ∈ V'}`, and an open `Vx₂ ⊆ Vx` containing `x₀`, such
that for every zero `y ∈ Vx₂`, with `ψ(ϕ(y)) = v + σ(v)`, `v ∈ V'`, and the level-`1` point `z` over
`ϕ(y)`: `Dψ(z)` maps the kernel of `Lin(z) : T_zO → K_z` onto `N_v = {n + Dσ(v)n | n ∈ K}`.  From
`theorem_3_6_8_nearby_kernel`: `z ∈ (G_g)₁`, `ker Dg(z) = Dψ'(ψ z)(ker D(h + t)(ψ z))`,
`ker D(h + t)(ψ z) = N_v`, `ker Dg(z) ⊆ T_zO`, and `Lin(z) = Dg(z)` on `T_zO` for the derivative
family `Dg` of the filling germ (`linAt_eq_germDeriv`, at the point `z` of the germ). -/
theorem theorem_3_6_8_ker_eq_tangent (hf : B.IsScSmoothSection f) {x₀ : X}
    (hg : B.IsGoodPositionGermTame f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ (c : StrongBundleChart PX P) (_ : B.IsTameChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
      (E' : ScBanach) (C' U' : Set (E' 0)) (hU' : IsRelOpenInQuadrant E' C' U')
      (ψ : c.φ.model.E 0 → E' 0) (ψ' : E' 0 → c.φ.model.E 0)
      (_ : IsScDiffeoQuadrant c.relOpen hU' ψ ψ') (_ : ψ 0 = 0)
      (K : Submodule ℝ (E' 0)) (_ : FiniteDimensional ℝ K) (V' : Set K) (σ : K → E' 0)
      (Vx Vx₂ : Set X),
      IsOpen Vx ∧ x₀ ∈ Vx ∧ Vx ⊆ c.φ.source ∧
      (∃ O, IsOpen O ∧ V' = O ∩ Subtype.val ⁻¹' C') ∧ (0 : K) ∈ V' ∧
      ContDiffOn ℝ 1 σ V' ∧ σ 0 = 0 ∧ fderivWithin ℝ σ V' 0 = 0 ∧
      (ψ ∘ c.φ) '' {y ∈ Vx | IsZeroAt P f y} = (fun v : K => (v : E' 0) + σ v) '' V' ∧
      IsOpen Vx₂ ∧ x₀ ∈ Vx₂ ∧ Vx₂ ⊆ Vx ∧
      ∀ y ∈ Vx₂, IsZeroAt P f y → ∃ v ∈ V', ψ (c.φ y) = (v : E' 0) + σ v ∧
        ∀ z : c.φ.model.E 1, c.φ.model.E.toBase 1 z = c.φ y →
          (LinearMap.ker (linAt c.U c.R (c.principal f) z :
              ↥(rangeS (scDeriv c.U (r c.R) z)) →ₗ[ℝ] c.F 0)).map
            (((scDeriv c.U ψ z).comp (rangeS (scDeriv c.U (r c.R) z)).subtypeL :
              ↥(rangeS (scDeriv c.U (r c.R) z)) →L[ℝ] E' 0) :
              ↥(rangeS (scDeriv c.U (r c.R) z)) →ₗ[ℝ] E' 0) =
            graphSpace K (fderivWithin ℝ σ V' v) := by
  classical
  obtain ⟨c, hc, hxV, h0, h0U, g, t₀, Gg, Dg, Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, hCt, U', hU',
    Ψ, Ψ', hΨ, hψ0, 𝒮, h', Bc, hh'𝒮, hsurj, hpos, Yc, V', σ, Vx, n', Wq, T, Vx₂, hfill, ht₀,
    ht₀0, hconj, hGg, hgsm, hDg, hgp, hYc, hYcc, hKsm, hV'rel, h0V', hσY, hσ1, hσC, hσ0, hDσ, hsol,
    hlift, hVxo, hx₀Vx, hVxsub, hinj, hzero, himage, hT, hVx₂o, hx₀Vx₂, hVx₂Vx, hker⟩ :=
    theorem_3_6_8_nearby_kernel hf.1 hg hx₀
  have hKfin : FiniteDimensional ℝ (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) :=
    (𝒮.isFredholm_Dfs hCt hh'𝒮).1.finite_ker
  have hd : IsScDiffeoQuadrant c.relOpen hU' (IsStrongBundleMap.base Ψ)
      (IsStrongBundleMap.base Ψ') :=
    ⟨hΨ.toFun.base_isScSmooth c.relOpen, hΨ.invFun.base_isScSmooth hU',
      fun u hu => hΨ.toFun.base_mem hu, fun u hu => hΨ.invFun.base_mem hu,
      fun u hu => hΨ.base_base hu, fun u' hu' => hΨ.base_base' hu'⟩
  have hfr : IsSc1 c.U (c.principal f ∘ r c.R) := hf.isSc1_principal_comp_r hc.1
  obtain ⟨h0O, -, -⟩ := c.zero_data hf.1 hxV h0 hx₀
  refine ⟨c, hc, hxV, h0, ScBanach.paramProd Pn W, Ct ×ˢ univ, U', hU', IsStrongBundleMap.base Ψ,
    IsStrongBundleMap.base Ψ', hd, hψ0, LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0), hKfin,
    V', σ, Vx, Vx₂, hVxo, hx₀Vx, hVxsub, hV'rel, h0V', hσC, hσ0, hDσ, himage, hVx₂o, hx₀Vx₂,
    hVx₂Vx, ?_⟩
  intro y hy hy0
  obtain ⟨heqfg, -, v, hv, z₀₁, x₁, hz₀₁, hz₀₁U, hz₀₁G, -, -, hlev, hveq, -, -, -, hker', -,
    hkerb, -, hcle, -⟩ := hker y hy hy0
  refine ⟨v, hv, hveq, fun z hz => ?_⟩
  have hzz : z = z₀₁ := c.φ.model.E.toBase_injective 1 (hz.trans hz₀₁.symm)
  subst hzz
  have hzO : c.φ.model.E.toBase 1 z ∈ r c.R '' c.U := by
    rw [hz, c.r_image]; exact c.φ.mapsTo_model y (hVxsub (hVx₂Vx hy))
  have heq : ∀ᶠ x in 𝓝 (c.φ.model.E.toBase 1 z), x ∈ r c.R '' c.U → c.principal f x = g x := by
    rw [hz]
    filter_upwards [heqfg] with x hx hxO
    exact hx (c.r_image ▸ hxO)
  have hlin : ∀ x : ↥(rangeS (scDeriv c.U (r c.R) z)),
      linAt c.U c.R (c.principal f) z x = Dg z x :=
    linAt_eq_germDeriv c.relOpen c.isRetraction h0U h0O hfr hDg hzO hz₀₁G heq
  have hinv : ∀ w, scDeriv c.U (IsStrongBundleMap.base Ψ) z
      (scDeriv U' (IsStrongBundleMap.base Ψ') x₁ w) = w := fun w => by
    rw [← hlev]; exact hΨ.scDeriv_base_base_inv c.relOpen hU' hz₀₁U w
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxk : (x : c.φ.model.E 0) ∈
        LinearMap.ker (Dg z : c.φ.model.E 0 →ₗ[ℝ] c.F 0) := by
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ← hlin]
      exact hx
    rw [hkerb] at hxk
    obtain ⟨u, hu, hux⟩ := hxk
    change scDeriv c.U (IsStrongBundleMap.base Ψ) z (x : c.φ.model.E 0) ∈ _
    rw [← hux, ContinuousLinearMap.coe_coe, hinv, hker']
    exact hu
  · intro hw
    rw [hker'] at hw
    have hx'k : scDeriv U' (IsStrongBundleMap.base Ψ') x₁ w ∈
        LinearMap.ker (Dg z : c.φ.model.E 0 →ₗ[ℝ] c.F 0) := by
      rw [hkerb]; exact ⟨w, hw, rfl⟩
    refine ⟨⟨_, hcle hx'k⟩, ?_, ?_⟩
    · change linAt c.U c.R (c.principal f) z ⟨_, hcle hx'k⟩ = 0
      rw [hlin]
      exact hx'k
    · change scDeriv c.U (IsStrongBundleMap.base Ψ) z
        (scDeriv U' (IsStrongBundleMap.base Ψ') x₁ w) = w
      exact hinv w

set_option maxHeartbeats 1600000 in
-- destructuring the large existential conclusion of `theorem_3_6_8_nearby_kernel`
/-- **The filler condition of `IsGoodPositionGermFilled` follows from good position, germ
reading** (phase 2; the germ form of `isGoodPositionGermFilled_of_isGoodPositionGerm_wholeChart`): the added
hypothesis of `theorem_3_6_8_one` is a consequence of the text's hypotheses.  For an
sc-Fredholm section with tame germ data in the germ reading and a zero `x₀` in good position in a
tame chart (germ reading), the filling germ `g` in the chart of `theorem_3_6_8_nearby_kernel`,
with its derivative family `Dg` on the germ `G_g`, satisfies condition (3) of Definition 3.1.4 (preprint 3.4) at
every level-`1` point `z₁ ∈ (G_g)₁` over a zero of `g` in `O` near `0`: such a zero is
`z₀ = ϕ(y)` for a zero `y` of `f` near `x₀`, which is in good position (`theorem_3_6_8_one'`),
so `Lin(z₁)` maps onto `K_{z₀}` in the chart `c` (`IsGoodPositionGerm.exists_isSurjLinOfIndex`),
`Lin(z₁) = Dg(z₁)` on `T_{z₀}O` (`linAt_eq_germDeriv`, `z₁ ∈ (G_g)₁`),
`ker Dg(z₁) ⊆ T_{z₀}O` (`theorem_3_6_8_nearby_kernel` (c)), and the converse direction of
Finding 100 (`normal_injective_of_exists_range_deriv_eq_ρ_germ`) gives the injectivity of
`(1 − ρ(z₀))Dg(z₁)` on `ker Dr(z₁)`. -/
theorem isGoodPositionGermFilled_of_isGoodPositionGerm (hf : B.IsScFredholmSectionTame f)
    {x₀ : X} (hg : B.IsGoodPositionGermTame f x₀) (hx₀ : IsZeroAt P f x₀) :
    B.IsGoodPositionGermFilled f x₀ := by
  classical
  have hfs : IsSection P f := hf.isScSmooth.1
  obtain ⟨c, hc, hxV, h0, h0U, g, t₀, Gg, Dg, Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, hCt, U', hU',
    Ψ, Ψ', hΨ, hψ0, 𝒮, h', Bc, hh'𝒮, hsurj, hpos, Yc, V', σ, Vx, n', Wq, T, Vx₂, hfill, ht₀,
    ht₀0, hconj, hGg, hgsm, hDg, hgp, hYc, hYcc, hKsm, hV'rel, h0V', hσY, hσ1, hσC, hσ0, hDσ, hsol,
    hlift, hVxo, hx₀Vx, hVxsub, hinj, hzero, himage, hT, hVx₂o, hx₀Vx₂, hVx₂Vx, hker⟩ :=
    theorem_3_6_8_nearby_kernel hfs hg hx₀
  obtain ⟨Vx₁, hVx₁o, hx₀Vx₁, hall⟩ := theorem_3_6_8_one' hf hg hx₀
  obtain ⟨h0O, -, hfK⟩ := c.zero_data hfs hxV h0 hx₀
  -- the neighbourhood `N = W₁ ∩ W₂` of `0`: `f̂ = g` on `O ∩ W₁`, `O ∩ W₂ = ϕ(Vx₂ ∩ Vx₁)`
  obtain ⟨W₁, hW₁sub, hW₁o, h0W₁⟩ := mem_nhds_iff.1 hfill.eq_on
  have hsV : Vx₂ ∩ Vx₁ ⊆ c.φ.source := fun y hy => hVxsub (hVx₂Vx hy.1)
  obtain ⟨W₂, hW₂o, hW₂⟩ := c.φ.exists_isOpen_image_eq hsV (hVx₂o.inter hVx₁o)
  have h0W₂ : (0 : c.φ.model.E 0) ∈ W₂ := by
    have : c.φ x₀ ∈ c.φ '' (Vx₂ ∩ Vx₁) := ⟨x₀, ⟨hx₀Vx₂, hx₀Vx₁⟩, rfl⟩
    rw [hW₂, h0] at this
    exact this.2
  refine ⟨hf.mem_smoothSet_of_isZeroAt hx₀, c, hc, hxV, h0, h0U, g, t₀, hfill, ht₀, ht₀0, hconj,
    Gg, Dg, hGg, hDg, hgp, W₁ ∩ W₂, hW₁o.inter hW₂o, ⟨h0W₁, h0W₂⟩, ?_⟩
  rintro z₁ hz₁G ⟨hz₁O, hz₁W₁, hz₁W₂⟩ hgz b hb hρb
  -- the zero `y = ϕ⁻¹(z₀)` of `f`
  obtain ⟨y, ⟨hy₂, hy₁⟩, hyz⟩ : c.φ.model.E.toBase 1 z₁ ∈ c.φ '' (Vx₂ ∩ Vx₁) := by
    rw [hW₂]; exact ⟨hz₁O, hz₁W₂⟩
  have hyV : y ∈ c.φ.source := hsV ⟨hy₂, hy₁⟩
  have hz₁O' : c.φ.model.E.toBase 1 z₁ ∈ r c.R '' c.U := c.r_image ▸ hz₁O
  have hfz : c.principal f (c.φ.model.E.toBase 1 z₁) = 0 := by
    rw [hW₁sub hz₁W₁ hz₁O']; exact hgz
  have hy0 : IsZeroAt P f y := by
    rw [c.isZeroAt_iff hfs hyV, hyz]; exact hfz
  obtain ⟨heqfg, -, v, hv, z₀₁, x₁, hz₀₁, hz₀₁U, -, -, -, -, -, -, -, -, -, -, -, -, hcle, -⟩ :=
    hker y hy₂ hy0
  have hzz : z₁ = z₀₁ := c.φ.model.E.toBase_injective 1 (hyz.symm.trans hz₀₁.symm)
  subst hzz
  -- `Lin(z₁)` is onto in the chart `c`: `y` is in good position
  obtain ⟨d, hd, -⟩ :=
    StrongBundle.IsGoodPositionGerm.exists_isSurjLinOfIndex hf.isScSmooth
      (hall y hy₁ hy0).isGoodPositionGerm hy0
  have hzU : c.φ.model.E.toBase 1 z₁ ∈ c.U := mem_U_of_mem_O c.isRetraction hz₁O'
  have hfr : IsSc1 c.U (c.principal f ∘ r c.R) := hf.isScSmooth.isSc1_principal_comp_r hc.1
  have hmem : ∀ x : ↥(rangeS (scDeriv c.U (r c.R) z₁)),
      linAt c.U c.R (c.principal f) z₁ x ∈ rangeS (ρCLM c.isRetraction hzU) := fun x =>
    ⟨_, rho_scDeriv_comp_r c.relOpen c.isRetraction hfr hfK hz₁O' hfz x⟩
  obtain ⟨hLs, -, -, -⟩ := hd c hc.1 hyV z₁ hyz.symm hzU
    ((linAt c.U c.R (c.principal f) z₁).codRestrict _ hmem) fun _ => rfl
  have heq : ∀ᶠ x in 𝓝 (c.φ.model.E.toBase 1 z₁), x ∈ r c.R '' c.U →
      c.principal f x = g x := by
    rw [← hyz]
    filter_upwards [heqfg] with x hx hxO
    exact hx (c.r_image ▸ hxO)
  have hlin := linAt_eq_germDeriv c.relOpen c.isRetraction h0U h0O hfr hDg hz₁O' hz₁G heq
  refine normal_injective_of_exists_range_deriv_eq_ρ_germ c.relOpen c.isRetraction hz₁O' hcle
    (fun k => ?_) b hb hρb
  obtain ⟨x, hx⟩ := hLs ⟨ρ c.R (c.φ.model.E.toBase 1 z₁) k, ⟨k, rfl⟩⟩
  refine ⟨x, x.2, ?_⟩
  rw [← hlin]
  exact congrArg Subtype.val hx

end DimIndex

end Polyfold
