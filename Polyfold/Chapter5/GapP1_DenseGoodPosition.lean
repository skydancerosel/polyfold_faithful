import Polyfold.Chapter5.GeneralPosition

/-!
# A dense form of Theorem 5.3.12

2021 Theorem 5.3.12, p. 222 (2017: Theorem 5.7; preprint: Theorem 5.19, p. 180).  The book states
the theorem with "an arbitrarily small section `s ∈ Γ^{+,1}_U(P)` satisfying `s(x) = 0` near
`∂X`"; that statement is `theorem_5_3_12` (`Chapter5/MainTheoremsBookForm.lean`).  Theorems 5.3.5
and 5.3.10 are stated with a dense set of good perturbations.  This file proves the dense form of
Theorem 5.3.12 as well (gap G.45).

## What is formalized

* `theorem_5_3_12_param_rel`: the generic form of the proof of Theorem 5.3.12 around a given
  allowable section `s₀` with `N(s₀) ≤ 1 − ε` vanishing near `∂X` (the proof of
  `theorem_5_3_12_param` is the case `s₀ = 0`).  The open set `U` is any open `U ⊇ S_f` with
  `cl{x ∈ U | N(f(x)) ≤ 1}` compact.
* `theorem_5_3_12_dense`: the sections `s ∈ Γ^{+,1}_U(P)` vanishing near `∂X` for which `f + s` is
  transversal and in good position at every zero are dense, for `ρ(s, s') = sup_x N(s(x) − s'(x))`
  read pointwise, among the sections of `Γ^{+,1}_U(P)` vanishing near `∂X`.

## Readings

As in `theorem_5_3_12`.  Density is taken inside the subset of `Γ^{+,1}_U(P)` of sections vanishing
near `∂X`, the class in which the theorem's perturbations lie: a section that does not vanish near
`∂X` cannot in general be approximated by sections that do.  Near `∂X` the section `f + s` equals
`f`, so its zeros on `∂X` are in good position by the hypothesis on `f`.
-/

open Set Filter Topology Function MeasureTheory

noncomputable section

namespace Polyfold

universe u v

section DenseGoodPosition

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

open StrongRetr

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
/-- At a point where all `tᵢ` vanish, the slice `g + Σ λᵢ tᵢ` equals `g`. -/
lemma paramSlice_apply_of_isZeroAt {m : ℕ} {g : X → Y} (hg : IsSection P g)
    {t : Fin m → X → Y} (ht : ∀ i, IsSection P (t i)) (lam : Fin m → ℝ) {y : X}
    (h0 : ∀ i, IsZeroAt P (t i) y) : paramSlice g hg t ht lam y = g y := by
  have ht0 : ∀ i, (⟨t i y, ht i y⟩ : P ⁻¹' {y}) = 0 := fun i => Subtype.ext (h0 i)
  change ((((⟨g y, hg y⟩ : P ⁻¹' {y}) + fiberComb t ht (lam, y)) : P ⁻¹' {y}) : Y) = g y
  have hfc : fiberComb t ht (lam, y) = 0 := by
    unfold fiberComb
    exact Finset.sum_eq_zero fun i _ => by rw [ht0 i, smul_zero]
  rw [hfc, add_zero]

omit [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
  [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- Off the support of `s`, `f + s = f`. -/
lemma sectionAdd_eq_of_not_mem_support {f s : X → Y} (hf : IsSection P f) (hs : IsSection P s)
    {y : X} (hy : y ∉ sectionSupport P s) : sectionAdd P f s y = f y := by
  have hz : s y = fiberZero P y := not_not.1 fun hne => hy (subset_closure hne)
  rw [sectionAdd_apply hf hs]
  have h0 : (⟨s y, hs y⟩ : P ⁻¹' {y}) = 0 := Subtype.ext hz
  rw [h0, add_zero]

omit [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
  [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- "`s(x) = 0` near `A`" is "the support of `s` misses `A`". -/
lemma eventually_isZeroAt_nhdsSet_iff {s : X → Y} {A : Set X} :
    (∀ᶠ x in 𝓝ˢ A, IsZeroAt P s x) ↔ Disjoint (sectionSupport P s) A := by
  constructor
  · intro h
    obtain ⟨O, hOo, hAO, hO⟩ := eventually_nhdsSet_iff_exists.1 h
    refine Set.disjoint_right.2 fun x hxA hxs => ?_
    have hsub : {y | s y ≠ fiberZero P y} ⊆ Oᶜ := fun y hy hyO => hy (hO y hyO)
    exact closure_minimal hsub hOo.isClosed_compl hxs (hAO hxA)
  · intro h
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhdsSet.2 h.subset_compl_left] with y hy
    by_contra hne
    exact hy (subset_closure hne)

set_option maxHeartbeats 6400000 in
-- the assembly of the proof: several large existentials are destructured, as in
-- `theorem_5_3_12_param`
/-- **2021 Theorem 5.3.12, p. 222 (preprint 5.19), generic form around a given section.**  Let `f`
be an sc-Fredholm section with tame germ data, `N` an auxiliary norm, `U ⊇ S_f` open with
`cl{x ∈ U | N(f(x)) ≤ 1}` compact (Theorem 5.2.2), `(f, x)` in good position at every zero
`x ∈ ∂X`, and `s₀` an sc⁺-section supported in `U`, with `N(s₀) ≤ 1 − ε` and support disjoint from
`∂X`.  Then there are allowable sc⁺-sections `t₁, …, t_m` supported in `U` and off `∂X`, a `δ > 0`
and a null set `CV` such that for `|λ| < δ`, `λ ∉ CV`, the section `s₀ + Σ λᵢ tᵢ` is allowable,
its support misses `∂X`, and `f + s₀ + Σ λᵢ tᵢ` is transversal and in good position at every
zero.  The proof is that of `theorem_5_3_12_param` (the case `s₀ = 0`) with `g = f + s₀` in place
of `f`; near `∂X`, `g = f`. -/
theorem theorem_5_3_12_param_rel (hbump : PX.AdmitsBumpFunctions) {f : X → Y}
    (hf : B.IsScFredholmSectionTame f) {N : B.One → ℝ} (hN : B.IsAuxNorm N)
    (hbd : ∀ x ∈ PX.boundary, IsZeroAt P f x → B.IsGoodPositionGermTame f x)
    {U : Set X} (hUo : IsOpen U) (hSU : solutionSet P f ⊆ U)
    (hK : IsCompact (closure {x ∈ U | B.AuxLe N (f x) 1}))
    {s₀ : X → Y} (hs₀ : B.IsScPlusSection s₀) (hs₀supp : sectionSupport P s₀ ⊆ U)
    (hs₀bd : Disjoint (sectionSupport P s₀) PX.boundary) {ε : ℝ} (hε : 0 < ε)
    (hs₀N : ∀ x (hx : s₀ x ∈ B.oneSet), N (B.oneMk (s₀ x) hx) ≤ 1 - ε) :
    ∃ (m : ℕ) (t : Fin m → X → Y) (ht : ∀ i, B.IsScPlusSection (t i)),
      (∀ i, sectionSupport P (t i) ⊆ U) ∧ (∀ i, Disjoint (sectionSupport P (t i)) PX.boundary) ∧
      (∀ i x (hx : t i x ∈ B.oneSet), N (B.oneMk (t i x) hx) ≤ 1) ∧
      ∃ δ > 0, ∃ CV : Set (Fin m → ℝ), volume CV = 0 ∧
        ∀ lam : Fin m → ℝ, ‖lam‖ < δ → lam ∉ CV →
          paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam ∈ B.allowableSections N U ∧
          Disjoint (sectionSupport P (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam))
            PX.boundary ∧
          B.IsTransversal (sectionAdd P f (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam)) ∧
          (∀ x, IsZeroAt P (sectionAdd P f (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam)) x →
            B.IsGoodPositionGermTame
              (sectionAdd P f (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam)) x) := by
  classical
  have hfs : IsSection P f := hf.isScSmooth.1
  have := PX.metrizableSpace
  -- `g = f + s₀`
  set g := sectionAdd P f s₀ with hgdef
  have hgFt : B.IsScFredholmSectionTame g := theorem_3_1_18_tame hf hs₀
  have hgF : B.IsScFredholmSection g := hgFt.toIsScFredholmSection
  -- `g = f` off the support of `s₀`, an open set containing `∂X`
  set O := (sectionSupport P s₀)ᶜ with hOdef
  have hOo : IsOpen O := isClosed_closure.isOpen_compl
  have hgO : ∀ y ∈ O, f y = g y := fun y hy =>
    (sectionAdd_eq_of_not_mem_support hfs hs₀.1 hy).symm
  have hbdg : ∀ x ∈ PX.boundary, IsZeroAt P g x → B.IsGoodPositionGermTame g x := by
    intro x hxb hx0
    have hxO : x ∈ O := fun h => Set.disjoint_left.1 hs₀bd h hxb
    have hfx : IsZeroAt P f x := by change f x = _; rw [hgO x hxO]; exact hx0
    exact (hbd x hxb hfx).congr_nhds hOo hxO hgO
  -- `S_g` is compact
  have hsU₀ : ∀ x ∉ U, IsZeroAt P s₀ x := fun x hx =>
    not_not.1 fun hne => hx (hs₀supp (subset_closure hne))
  have hs₀N' : ∀ x, B.AuxLe N (s₀ x) 1 := fun x =>
    ⟨hs₀.mem_oneSet x, (hs₀N x _).trans (by linarith)⟩
  have hSg : IsCompact (solutionSet P g) := by
    obtain ⟨-, hcl⟩ := remark_5_3_4 hN hfs hSU hK hs₀.1 hsU₀ hs₀N'
    exact hcl.of_isClosed_subset (isClosed_solutionSet hgF.isScSmooth) subset_closure
  -- `Vbd`: the zeros of `g` near the boundary zeros are in good position
  have hlocB : ∀ x : (solutionSet P g ∩ PX.boundary : Set X), ∃ V : Set X, IsOpen V ∧
      (x : X) ∈ V ∧ ∀ y ∈ V, IsZeroAt P g y → B.IsGoodPositionGermTame g y := fun x =>
    theorem_3_6_8_one' hgFt (hbdg x x.2.2 x.2.1) x.2.1
  choose Vb hVbo hxVb hVb using hlocB
  set Vbd := ⋃ x, Vb x with hVbd
  have hVbdo : IsOpen Vbd := isOpen_iUnion hVbo
  have hVbdgood : ∀ y ∈ Vbd, IsZeroAt P g y → B.IsGoodPositionGermTame g y := fun y hy hy0 => by
    obtain ⟨x, hx⟩ := mem_iUnion.1 hy; exact hVb x y hx hy0
  have hSb : solutionSet P g ∩ PX.boundary ⊆ Vbd := fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hxVb _⟩
  have hbcl : IsClosed PX.boundary := PX.isClosed_boundary
  have hSbcl : IsClosed (solutionSet P g ∩ PX.boundary) := hSg.isClosed.inter hbcl
  obtain ⟨V₁, hV₁o, hSbV₁, hclV₁⟩ := normal_exists_closure_subset hSbcl hVbdo hSb
  -- the zeros outside `Vbd` are interior points
  set K₁ := solutionSet P g \ Vbd with hK₁
  have hK₁c : IsCompact K₁ := hSg.diff hVbdo
  have hSgU : solutionSet P g ⊆ U := fun x hx => by
    by_contra hxU
    have h1 : f x = g x := hgO x fun h => hxU (hs₀supp h)
    exact hxU (hSU (show f x = fiberZero P x by rw [h1]; exact hx))
  set G := U ∩ (PX.boundary)ᶜ ∩ (closure V₁)ᶜ with hGdef
  have hGo : IsOpen G := (hUo.inter hbcl.isOpen_compl).inter isClosed_closure.isOpen_compl
  have hK₁G : K₁ ⊆ G := by
    rintro x ⟨hxS, hxV⟩
    refine ⟨⟨hSgU hxS, fun hxb => hxV (hSb ⟨hxS, hxb⟩)⟩, fun hxc => hxV (hclV₁ hxc)⟩
  -- spanning sections at the points of `K₁`, supported in `G`
  have hspan : ∀ x : K₁,
      ∃ (k : ℕ) (s : Fin k → X → Y) (hsp : ∀ i, B.IsScPlusSection (s i)),
        (∀ i, sectionSupport P (s i) ⊆ G) ∧
        (∀ i x (hx : s i x ∈ B.oneSet), N (B.oneMk (s i x) hx) ≤ 1) ∧
        ∃ Ux : Set X, IsOpen Ux ∧ (x : X) ∈ Ux ∧ ∀ y ∈ Ux, IsZeroAt P g y →
          haveI := MPolyfold.paracompactSpace_prod (rnPolyfold k) PX
          haveI := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin k → ℝ) × X → X))
            ((rnPolyfold k).prod PX) B
          (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold k) PX)).IsLinSurjAt
            (paramSection g hgF.isScSmooth.1 s fun i => (hsp i).1) (0, y) := by
    intro x
    obtain ⟨x, hx⟩ := x
    have hx0 : IsZeroAt P g x := hx.1
    obtain ⟨k, s, hsp, hsupp, hsN, c, hc, hxV, hφ0, hsp_span⟩ :=
      exists_spanning_sections hbump hN hgF hx0 hGo (hK₁G hx)
    have := MPolyfold.paracompactSpace_prod (rnPolyfold k) PX
    have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin k → ℝ) × X → X))
      ((rnPolyfold k).prod PX) B
    have hsurj := isLinSurjAt_paramSection_zero_of_spanning hgF hsp hc hxV hφ0
      (paramSection g hgF.isScSmooth.1 s (fun i => (hsp i).1) (0, x)) hsp_span
    have hF := theorem_3_1_21_tame hgFt hsp
    have hz0 : ∀ y, IsZeroAt P g y → IsZeroAt (pullbackProj P Prod.snd)
        (paramSection g hgF.isScSmooth.1 s fun i => (hsp i).1) (0, y) := fun y hy => by
      rw [isZeroAt_paramSection_iff]
      change IsZeroAt P (paramSlice g hgF.isScSmooth.1 s (fun i => (hsp i).1) 0) y
      rw [paramSlice_zero]; exact hy
    have hxb : x ∉ PX.boundary := fun hxb => hx.2 (hSb ⟨hx.1, hxb⟩)
    have hd0 : ((rnPolyfold k).prod PX).degIndex ((0 : Fin k → ℝ), x) = 0 := by
      have h1 := MPolyfold.degIndex_prod_le (rnPolyfold k) PX 0 x
      have h2 : PX.degIndex x = 0 := by
        by_contra h; exact hxb (Nat.one_le_iff_ne_zero.2 h)
      rw [rnPolyfold_degIndex, h2] at h1
      exact Nat.le_zero.1 h1
    have hgp := StrongBundle.isGoodPositionGerm_of_isLinSurjAt hF (hz0 x hx0) hd0 hsurj
    obtain ⟨V, hVo, hxV', hall⟩ := theorem_3_6_8_one' hF hgp (hz0 x hx0)
    refine ⟨k, s, hsp, hsupp, hsN, Prod.mk 0 ⁻¹' V,
      hVo.preimage (continuous_const.prodMk continuous_id), hxV', fun y hy hy0 => ?_⟩
    exact (hall (0, y) hy (hz0 y hy0)).isGoodPositionGerm.isLinSurjAt hF.isScSmooth
  choose k s hsp hsupp hsN Ux hUxo hxUx hUx using hspan
  obtain ⟨T, hT⟩ := hK₁c.elim_finite_subcover Ux hUxo
    (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hxUx ⟨x, hx⟩⟩)
  let e := Fintype.equivFin (Σ x : T, Fin (k x.1))
  set m := Fintype.card (Σ x : T, Fin (k x.1)) with hm
  set t : Fin m → X → Y := fun j => s (e.symm j).1.1 (e.symm j).2 with htdef
  have ht : ∀ j, B.IsScPlusSection (t j) := fun j => hsp _ _
  have htG : ∀ j, sectionSupport P (t j) ⊆ G := fun j => hsupp _ _
  have htsupp : ∀ j, sectionSupport P (t j) ⊆ U := fun j x hx => (htG j hx).1.1
  have htbd : ∀ j, Disjoint (sectionSupport P (t j)) PX.boundary := fun j =>
    Set.disjoint_left.2 fun x hx hxb => (htG j hx).1.2 hxb
  have htN : ∀ j x (hx : t j x ∈ B.oneSet), N (B.oneMk (t j x) hx) ≤ 1 := fun j x hx =>
    hsN _ _ x hx
  have := MPolyfold.paracompactSpace_prod (rnPolyfold m) PX
  have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin m → ℝ) × X → X))
    ((rnPolyfold m).prod PX) B
  have hFt := theorem_3_1_21_tame hgFt ht
  have hz0 : ∀ y, IsZeroAt P g y → IsZeroAt (pullbackProj P Prod.snd)
      (paramSection g hgF.isScSmooth.1 t fun i => (ht i).1) (0, y) := fun y hy => by
    rw [isZeroAt_paramSection_iff]
    change IsZeroAt P (paramSlice g hgF.isScSmooth.1 t (fun i => (ht i).1) 0) y
    rw [paramSlice_zero]; exact hy
  -- `F` is onto at every `(0, y)`, `y ∈ S_g`
  have hsurjAll : ∀ y, IsZeroAt P g y →
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsLinSurjAt
        (paramSection g hgF.isScSmooth.1 t fun i => (ht i).1) (0, y) := by
    intro y hy
    by_cases hyV : y ∈ Vbd
    · have hgy : B.IsGoodPositionGermTame g y := hVbdgood y hyV hy
      have hlin := hgy.isGoodPositionGerm.isLinSurjAt hgF.isScSmooth
      obtain ⟨-, c, hc, hyc, hφ0, -⟩ := hgFt.germTame y (hgF.mem_smoothSet_of_isZeroAt hy)
      have hz : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) = c.φ y := by rw [map_zero, hφ0]
      have hs' := hlin.linAt_surjective hgF.isScSmooth hy hc.1 hyc hz
      refine isLinSurjAt_paramSection_zero_of_spanning hgF ht hc.1 hyc hφ0
        (paramSection g hgF.isScSmooth.1 t (fun i => (ht i).1) (0, y)) fun k' hk' => ?_
      rw [hφ0] at hs'
      obtain ⟨u, hu⟩ := hs' k' hk'
      exact ⟨u, 0, by simp [hu]⟩
    · obtain ⟨x, hxT, hyUx⟩ := mem_iUnion₂.1 (hT ⟨hy, hyV⟩)
      have := MPolyfold.paracompactSpace_prod (rnPolyfold (k x)) PX
      have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin (k x) → ℝ) × X → X))
        ((rnPolyfold (k x)).prod PX) B
      refine isLinSurjAt_paramSection_zero_of_comp hgF ht (fun i => e ⟨⟨x, hxT⟩, i⟩) (hsp x)
        (fun i => ?_) hy (hUx x y hyUx hy)
      have := congrArg (fun σ : (Σ x : T, Fin (k x.1)) => s σ.1.1 σ.2)
        (e.symm_apply_apply ⟨⟨x, hxT⟩, i⟩)
      exact this.symm
  -- the open set `W ⊇ {0} × (S_g ∖ V₁)` of zeros of `F` in good position, off `ℝᵐ × ∂X`
  have hlocW : ∀ y : (solutionSet P g \ V₁ : Set X), ∃ W : Set ((Fin m → ℝ) × X), IsOpen W ∧
      ((0 : Fin m → ℝ), (y : X)) ∈ W ∧ W ⊆ {z | z.2 ∉ PX.boundary} ∧
      ∀ z ∈ W, IsZeroAt (pullbackProj P Prod.snd)
        (paramSection g hgF.isScSmooth.1 t fun i => (ht i).1) z →
        (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsGoodPositionGermTame
          (paramSection g hgF.isScSmooth.1 t fun i => (ht i).1) z := by
    intro y
    obtain ⟨y, hyS, hyV₁⟩ := y
    have hyb : y ∉ PX.boundary := fun hyb => hyV₁ (hSbV₁ ⟨hyS, hyb⟩)
    have hd0 : ((rnPolyfold m).prod PX).degIndex ((0 : Fin m → ℝ), y) = 0 := by
      have h1 := MPolyfold.degIndex_prod_le (rnPolyfold m) PX 0 y
      have h2 : PX.degIndex y = 0 := by
        by_contra h; exact hyb (Nat.one_le_iff_ne_zero.2 h)
      rw [rnPolyfold_degIndex, h2] at h1
      exact Nat.le_zero.1 h1
    have hgp := StrongBundle.isGoodPositionGerm_of_isLinSurjAt hFt (hz0 y hyS) hd0
      (hsurjAll y hyS)
    obtain ⟨V, hVo, hyV, hall⟩ := theorem_3_6_8_one' hFt hgp (hz0 y hyS)
    refine ⟨V ∩ {z | z.2 ∉ PX.boundary}, hVo.inter (hbcl.isOpen_compl.preimage continuous_snd),
      ⟨hyV, hyb⟩, inter_subset_right, fun z hz hz0' => hall z hz.1 hz0'⟩
  choose Wy hWyo hyWy hWyb hWy using hlocW
  set W := ⋃ y, Wy y with hWdef
  have hWo : IsOpen W := isOpen_iUnion hWyo
  have hWgood : ∀ z ∈ W, IsZeroAt (pullbackProj P Prod.snd)
      (paramSection g hgF.isScSmooth.1 t fun i => (ht i).1) z →
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsGoodPositionGermTame
        (paramSection g hgF.isScSmooth.1 t fun i => (ht i).1) z :=
    fun z hz hz0' => by obtain ⟨y, hzy⟩ := mem_iUnion.1 hz; exact hWy y z hzy hz0'
  have hWb : ∀ z ∈ W, z.2 ∉ PX.boundary := fun z hz => by
    obtain ⟨y, hzy⟩ := mem_iUnion.1 hz; exact hWyb y hzy
  -- the perturbations are allowable for `|λ| ≤ δ₁ = ε/(m + 1)`
  set δ₁ : ℝ := ε / (m + 1) with hδ₁
  have hδ₁pos : 0 < δ₁ := div_pos hε (by positivity)
  have hallow : ∀ lam : Fin m → ℝ, ‖lam‖ ≤ δ₁ →
      ∀ x, B.AuxLe N (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam x) 1 :=
    fun lam hlam x =>
    auxLe_paramSlice hN hs₀ ht hs₀N htN (by
      calc (m : ℝ) * ‖lam‖ ≤ m * δ₁ := mul_le_mul_of_nonneg_left hlam (by positivity)
        _ = ε * (m / (m + 1)) := by rw [hδ₁]; ring
        _ ≤ ε * 1 := mul_le_mul_of_nonneg_left
            ((div_le_one (by positivity)).2 (by linarith)) hε.le
        _ = ε := mul_one _) x
  have hsuppl : ∀ lam : Fin m → ℝ, ∀ x ∉ U,
      IsZeroAt P (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam) x := fun lam x hx =>
    isZeroAt_paramSlice_of_not_mem_support hs₀.1 _ lam (fun h => hx (hs₀supp h))
      fun i h => hx (htsupp i h)
  have hslice : ∀ lam : Fin m → ℝ,
      sectionAdd P f (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam) =
      paramSlice g hgF.isScSmooth.1 t (fun i => (ht i).1) lam :=
    fun lam => sectionAdd_paramSlice hfs hs₀.1 _ lam
  -- the zeros of `F` over `|λ| ≤ δ₁` off `V₁` form a compact set `Z₁`
  set Z : Set ((Fin m → ℝ) × X) := {z | ‖z.1‖ ≤ δ₁ ∧ IsZeroAt (pullbackProj P Prod.snd)
    (paramSection g hgF.isScSmooth.1 t fun i => (ht i).1) z} with hZdef
  have hZsub : Z ⊆ Metric.closedBall (0 : Fin m → ℝ) δ₁ ×ˢ closure {x ∈ U | B.AuxLe N (f x) 1} := by
    rintro ⟨lam, x⟩ ⟨hlam, hz⟩
    refine ⟨mem_closedBall_zero_iff.2 hlam, ?_⟩
    have hx' : IsZeroAt P (paramSlice g hgF.isScSmooth.1 t (fun i => (ht i).1) lam) x :=
      (isZeroAt_paramSection_iff (lam, x)).1 hz
    rw [← hslice lam] at hx'
    exact subset_closure ((remark_5_3_4 hN hfs hSU hK (isSection_paramSlice lam) (hsuppl lam)
      (hallow lam hlam)).1 hx')
  have hZclosed : IsClosed Z :=
    (isClosed_le (continuous_norm.comp continuous_fst) continuous_const).inter
      (isClosed_solutionSet (theorem_3_1_21_preprint hgF ht).isScSmooth)
  have hZ : IsCompact Z :=
    ((isCompact_closedBall _ _).prod hK).of_isClosed_subset hZclosed hZsub
  set Z₁ := Z ∩ {z | z.2 ∉ V₁} with hZ₁def
  have hZ₁closed : IsClosed Z₁ :=
    hZclosed.inter (hV₁o.isClosed_compl.preimage continuous_snd)
  have hZ₁ : IsCompact Z₁ := hZ.of_isClosed_subset hZ₁closed inter_subset_left
  obtain ⟨δ₀, hδ₀, hδ₀W⟩ := exists_pos_forall_mem_of_isCompact hZ₁ hWo fun z hz hz1 => by
    have hz2 : IsZeroAt P g z.2 := by
      have := (isZeroAt_paramSection_iff z).1 hz.1.2
      rw [hz1, paramSlice_zero] at this; exact this
    have hz' : z = (0, z.2) := Prod.ext hz1 rfl
    rw [hz']; exact mem_iUnion.2 ⟨⟨z.2, hz2, hz.2⟩, hyWy _⟩
  -- the Sard step on `Z₀ = Z₁ ∩ {|λ| ≤ δ/2}`
  set δ : ℝ := min δ₀ δ₁ with hδ
  have hδpos : 0 < δ := lt_min hδ₀ hδ₁pos
  set Z₀ : Set ((Fin m → ℝ) × X) := Z₁ ∩ {z | ‖z.1‖ ≤ δ / 2} with hZ₀def
  have hZ₀closed : IsClosed Z₀ :=
    hZ₁closed.inter (isClosed_le (continuous_norm.comp continuous_fst) continuous_const)
  have hZ₀ : IsCompact Z₀ := hZ₁.of_isClosed_subset hZ₀closed inter_subset_left
  have hZ₀W : ∀ z ∈ Z₀, z ∈ W := fun z hz =>
    hδ₀W z hz.1 (by
      have h2 : ‖z.1‖ ≤ δ / 2 := hz.2
      linarith [min_le_left δ₀ δ₁, hδpos])
  have hlocS : ∀ z : Z₀, ∃ W' : Set ((Fin m → ℝ) × X), IsOpen W' ∧ (z : (Fin m → ℝ) × X) ∈ W' ∧
      ∃ CV : Set (Fin m → ℝ), volume CV = 0 ∧
        ∀ z' ∈ W', IsZeroAt (pullbackProj P Prod.snd)
          (paramSection g hgF.isScSmooth.1 t fun i => (ht i).1) z' →
          z'.1 ∉ CV → B.IsLinSurjAt (paramSlice g hgF.isScSmooth.1 t (fun i => (ht i).1) z'.1)
            z'.2 := fun z =>
    exists_null_isLinSurjAt_paramSlice_near hgFt ht z.2.1.1.2
      (hWgood z (hZ₀W z z.2) z.2.1.1.2)
  choose W' hW'o hzW' CV hCV hW'tr using hlocS
  obtain ⟨T', hT'⟩ := hZ₀.elim_finite_subcover W' hW'o
    (fun z hz => mem_iUnion.2 ⟨⟨z, hz⟩, hzW' ⟨z, hz⟩⟩)
  refine ⟨m, t, ht, htsupp, htbd, htN, δ / 2, by positivity, ⋃ z ∈ T', CV z,
    (measure_biUnion_null_iff T'.countable_toSet).2 fun z _ => hCV z, fun lam hlam hlamCV => ?_⟩
  have hlam₁ : ‖lam‖ ≤ δ₁ := by linarith [min_le_right δ₀ δ₁]
  have hsl : B.IsScPlusSection (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam) :=
    isScPlusSection_paramSlice hs₀ ht lam
  have hslsupp := sectionSupport_paramSlice_subset hs₀.1 (fun i => (ht i).1) lam
  have halw : paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam ∈ B.allowableSections N U := by
    refine ⟨hsl, hslsupp.trans (union_subset hs₀supp (iUnion_subset htsupp)), fun x hx => ?_⟩
    obtain ⟨hx', h⟩ := hallow lam hlam₁ x
    exact h
  have hbd' : Disjoint (sectionSupport P (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam))
      PX.boundary :=
    Set.disjoint_of_subset_left hslsupp
      (Set.disjoint_union_left.2 ⟨hs₀bd, Set.disjoint_iUnion_left.2 htbd⟩)
  set h := sectionAdd P f (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam) with hhdef
  have hhF : B.IsScFredholmSectionTame h := theorem_3_1_18_tame hf hsl
  -- `h = g` on `V₁`
  have hhV₁ : ∀ y ∈ V₁, g y = h y := fun y hy => by
    rw [hhdef, hslice lam]
    refine (paramSlice_apply_of_isZeroAt hgF.isScSmooth.1 (fun i => (ht i).1) lam
      fun i => ?_).symm
    exact not_not.1 fun hne => (htG i (subset_closure hne)).2 (subset_closure hy)
  have hgood : ∀ y, IsZeroAt P h y → B.IsGoodPositionGermTame h y ∧ B.IsLinSurjAt h y := by
    intro y hy0
    by_cases hyV₁ : y ∈ V₁
    · have hgy : IsZeroAt P g y := by
        change g y = fiberZero P y; rw [hhV₁ y hyV₁]; exact hy0
      have hg' := (hVbdgood y (hclV₁ (subset_closure hyV₁)) hgy).congr_nhds hV₁o hyV₁ hhV₁
      exact ⟨hg', hg'.isGoodPositionGerm.isLinSurjAt hhF.isScSmooth⟩
    · have hy0' : IsZeroAt P (paramSlice g hgF.isScSmooth.1 t (fun i => (ht i).1) lam) y := by
        rw [← hslice lam]; exact hy0
      have hzF := (isZeroAt_paramSection_iff (lam, y)).2 hy0'
      have hzZ₀ : (lam, y) ∈ Z₀ := ⟨⟨⟨hlam₁, hzF⟩, hyV₁⟩, hlam.le⟩
      obtain ⟨z, hzT', hzW'⟩ := mem_iUnion₂.1 (hT' hzZ₀)
      have hlamCV' : lam ∉ CV z := fun h' => hlamCV (mem_iUnion₂.2 ⟨z, hzT', h'⟩)
      have hsurj : B.IsLinSurjAt h y := by
        rw [hhdef, hslice lam]; exact hW'tr z (lam, y) hzW' hzF hlamCV'
      have hyb : y ∉ PX.boundary := hWb (lam, y) (hZ₀W _ hzZ₀)
      have hd : PX.degIndex y = 0 := by
        by_contra hne; exact hyb (Nat.one_le_iff_ne_zero.2 hne)
      exact ⟨StrongBundle.isGoodPositionGerm_of_isLinSurjAt hhF hy0 hd hsurj, hsurj⟩
  exact ⟨halw, hbd', fun y hy => (hgood y hy).2, fun y hy => (hgood y hy).1⟩

set_option maxHeartbeats 1600000 in
-- the fibre arithmetic in `(Y_{0,1})_x`, as in `theorem_5_3_10_dense`
/-- **2021 Theorem 5.3.12, p. 222 (preprint 5.19), dense form.**  Let `P : Y → X` be a strong bundle
over an M-polyfold admitting sc-smooth bump functions, `f` an sc-Fredholm section with tame germ
data and compact solution set, `N` an auxiliary norm, and `(f, x)` in good position at every zero
`x ∈ ∂X`.  There is an open `U ⊇ S_f` such that `S_{f+s}` is compact for every
`s ∈ Γ^{+,1}_U(P)`, and for every `s' ∈ Γ^{+,1}_U(P)` vanishing near `∂X` and every `ε > 0` there
is `s ∈ Γ^{+,1}_U(P)` vanishing near `∂X` with `N(s(x) − s'(x)) ≤ ε` for all `x`, such that
`f + s` is transversal to the zero section and in good position at every point of `S_{f+s}`;
`S_{f+s}` is compact and, if non-empty, a tame sub-M-polyfold whose induced structure is that of a
manifold with boundary with corners.  The book states "an arbitrarily small `s`"
(`theorem_5_3_12`, the case `s' = 0`); this is the dense form, as in Theorems 5.3.5 and 5.3.10.
*Proof*: `theorem_5_3_12_param_rel` around `s₀ = (1 − ε'/2)s'`, and a parameter outside the null
set in a small ball (the proof of `theorem_5_3_10_dense`). -/
theorem theorem_5_3_12_dense (hbump : PX.AdmitsBumpFunctions) {f : X → Y}
    (hf : B.IsScFredholmSectionTame f) (hS : IsCompact (solutionSet P f)) {N : B.One → ℝ}
    (hN : B.IsAuxNorm N)
    (hbd : ∀ x ∈ PX.boundary, IsZeroAt P f x → B.IsGoodPositionGermTame f x) :
    ∃ U : Set X, IsOpen U ∧ solutionSet P f ⊆ U ∧
      (∀ s ∈ B.allowableSections N U, IsCompact (solutionSet P (sectionAdd P f s))) ∧
      ∀ (s' : X → Y) (hs' : B.IsScPlusSection s'), s' ∈ B.allowableSections N U →
        (∀ᶠ x in 𝓝ˢ PX.boundary, IsZeroAt P s' x) → ∀ ε > 0,
        ∃ (s : X → Y) (hs : B.IsScPlusSection s), s ∈ B.allowableSections N U ∧
          (∀ x, B.sectionDistAt N hs hs' x ≤ ε) ∧
          (∀ᶠ x in 𝓝ˢ PX.boundary, IsZeroAt P s x) ∧
          B.IsTransversal (sectionAdd P f s) ∧
          (∀ x ∈ solutionSet P (sectionAdd P f s), B.IsGoodPositionGermTame (sectionAdd P f s) x) ∧
          IsCompact (solutionSet P (sectionAdd P f s)) ∧
          ((solutionSet P (sectionAdd P f s)).Nonempty →
            ∃ hsub : PX.IsSubMPolyfold (solutionSet P (sectionAdd P f s)),
              haveI := PX.paracompactSpace_subtype (solutionSet P (sectionAdd P f s))
              (MPolyfold.subPolyfold hsub).IsTame ∧
                (MPolyfold.subPolyfold hsub).IsManifoldWithCornersLoc) := by
  classical
  have hfs : IsSection P f := hf.isScSmooth.1
  have hfF := hf.toIsScFredholmSection
  have := PX.metrizableSpace
  obtain ⟨-, hprop⟩ := theorem_5_2_2_preprint hfF hS
  obtain ⟨U, hUo, hSU, hK⟩ := hprop N hN
  have hcpt : ∀ s ∈ B.allowableSections N U, IsCompact (solutionSet P (sectionAdd P f s)) := by
    rintro s ⟨hs, hssupp, hsN⟩
    have hsU : ∀ x ∉ U, IsZeroAt P s x := fun x hx =>
      not_not.1 fun hne => hx (hssupp (subset_closure hne))
    have hsN' : ∀ x, B.AuxLe N (s x) 1 := fun x => ⟨hs.mem_oneSet x, hsN x _⟩
    obtain ⟨-, hcl⟩ := remark_5_3_4 hN hfs hSU hK hs.1 hsU hsN'
    exact hcl.of_isClosed_subset
      (isClosed_solutionSet (theorem_3_1_18_preprint hfF hs).isScSmooth) subset_closure
  refine ⟨U, hUo, hSU, hcpt, fun s' hs' hs'alw hs'bd ε hε => ?_⟩
  obtain ⟨-, hs'supp, hs'N⟩ := hs'alw
  rw [eventually_isZeroAt_nhdsSet_iff] at hs'bd
  -- `ε' = min ε 1`, `θ = 1 − ε'/2`, `s₀ = θ s'`
  set ε' : ℝ := min ε 1 with hε'
  have hε'pos : 0 < ε' := lt_min hε one_pos
  have hε'le : ε' ≤ ε := min_le_left _ _
  have hε'le1 : ε' ≤ 1 := min_le_right _ _
  set θ : ℝ := 1 - ε' / 2 with hθ
  have hθpos : 0 < θ := by rw [hθ]; linarith
  set s₀ : X → Y := sectionSmul P (fun _ => θ) s' with hs₀def
  have hs₀ : B.IsScPlusSection s₀ := hs'.smul_left (isScSmoothMap_real_const _)
  have hs₀supp' : sectionSupport P s₀ ⊆ sectionSupport P s' :=
    sectionSupport_sectionSmul_const_subset hs'.1 θ
  have hs₀N : ∀ x (hx : s₀ x ∈ B.oneSet), N (B.oneMk (s₀ x) hx) ≤ 1 - ε' / 2 := fun x hx => by
    rw [hN.oneMk_sectionSmul_const hs' θ x hx, abs_of_pos hθpos]
    calc θ * N (B.oneMk (s' x) (hs'.mem_oneSet x)) ≤ θ * 1 :=
          mul_le_mul_of_nonneg_left (hs'N x _) hθpos.le
      _ = 1 - ε' / 2 := by rw [mul_one]
  obtain ⟨m, t, ht, htsupp, -, htN, δ, hδ, CV, hCV, hlam⟩ :=
    theorem_5_3_12_param_rel hbump hf hN hbd hUo hSU hK hs₀ (hs₀supp'.trans hs'supp)
      (Set.disjoint_of_subset_left hs₀supp' hs'bd) (by positivity : 0 < ε' / 2) hs₀N
  -- a parameter `λ ∉ CV` with `|λ| < δ` and `m|λ| ≤ ε'/2`
  set r : ℝ := min δ (ε' / (2 * (m + 1))) with hr
  have hrpos : 0 < r := lt_min hδ (by positivity)
  obtain ⟨lam, hlamr, hlamCV⟩ : ∃ lam ∈ Metric.ball (0 : Fin m → ℝ) r, lam ∉ CV := by
    by_contra h
    have h1 : Metric.ball (0 : Fin m → ℝ) r ⊆ CV := fun lam hl => by
      by_contra hc
      exact h ⟨lam, hl, hc⟩
    exact (Metric.measure_ball_pos volume (0 : Fin m → ℝ) hrpos).ne' (measure_mono_null h1 hCV)
  have hlamδ : ‖lam‖ < δ := lt_of_lt_of_le (mem_ball_zero_iff.1 hlamr) (min_le_left _ _)
  have hlamε : (m : ℝ) * ‖lam‖ ≤ ε' / 2 := by
    have h1 : ‖lam‖ ≤ ε' / (2 * (m + 1)) :=
      (mem_ball_zero_iff.1 hlamr).le.trans (min_le_right _ _)
    calc (m : ℝ) * ‖lam‖ ≤ m * (ε' / (2 * (m + 1))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (ε' / 2) * (m / (m + 1)) := by field_simp
      _ ≤ (ε' / 2) * 1 := mul_le_mul_of_nonneg_left
          ((div_le_one (by positivity)).2 (by linarith)) (by positivity)
      _ = ε' / 2 := mul_one _
  obtain ⟨halw, hbd', htr, hgood⟩ := hlam lam hlamδ hlamCV
  have hsl : B.IsScPlusSection (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam) :=
    isScPlusSection_paramSlice hs₀ ht lam
  have hhF : B.IsScFredholmSectionTame
      (sectionAdd P f (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam)) :=
    theorem_3_1_18_tame hf hsl
  refine ⟨_, hsl, halw, fun x => ?_, eventually_isZeroAt_nhdsSet_iff.2 hbd', htr,
    fun x hx => hgood x hx, hcpt _ halw, fun hne => ?_⟩
  · -- the distance: `s(x) − s'(x) = (θ − 1) s'(x) + Σ λᵢ tᵢ(x)` in the fibre
    set u' : B.oneFiber x := ⟨⟨s' x, hs'.1 x⟩, hs'.mem_oneSet x⟩ with hu'
    set w : Fin m → B.oneFiber x := fun i => ⟨⟨t i x, (ht i).1 x⟩, (ht i).mem_oneSet x⟩ with hw
    have hu : (⟨⟨paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam x, hsl.1 x⟩, hsl.mem_oneSet x⟩ :
        B.oneFiber x) = θ • u' + ∑ i, lam i • w i := by
      apply Subtype.ext
      rw [Submodule.coe_add, Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      apply Subtype.ext
      change paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam x = _
      unfold paramSlice
      have h1 : (⟨s₀ x, hs₀.1 x⟩ : P ⁻¹' {x}) = θ • ⟨s' x, hs'.1 x⟩ :=
        Subtype.ext (sectionSmul_apply (f := fun _ => θ) hs'.1 x)
      rw [h1]
      rfl
    have hdiff : (⟨⟨paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam x, hsl.1 x⟩,
        hsl.mem_oneSet x⟩ : B.oneFiber x) - u' = (θ - 1) • u' + ∑ i, lam i • w i := by
      rw [hu, add_sub_right_comm, hθ]
      simp only [sub_smul, one_smul]
    have hli : ∀ i, |lam i| ≤ ‖lam‖ := fun i => by
      have := norm_le_pi_norm lam i
      rwa [Real.norm_eq_abs] at this
    have hwN : ∀ i, N (B.toOne (w i)) ≤ 1 := fun i => htN i x ((ht i).mem_oneSet x)
    have hu'N : N (B.toOne u') ≤ 1 := hs'N x _
    change N (B.toOne (_ - u')) ≤ ε
    rw [hdiff]
    calc N (B.toOne ((θ - 1) • u' + ∑ i, lam i • w i))
        ≤ N (B.toOne ((θ - 1) • u')) + N (B.toOne (∑ i, lam i • w i)) :=
          (hN.fiber x).add_le _ _
      _ = |θ - 1| * N (B.toOne u') + N (B.toOne (∑ i, lam i • w i)) := by rw [hN.smul]
      _ ≤ (ε' / 2) * 1 + ∑ i, N (B.toOne (lam i • w i)) := by
          refine add_le_add ?_ (hN.toOne_sum_le _ _)
          have hθ1 : |θ - 1| = ε' / 2 := by
            rw [hθ, show (1 - ε' / 2 - 1 : ℝ) = -(ε' / 2) by ring, abs_neg,
              abs_of_pos (by positivity)]
          rw [hθ1]
          exact mul_le_mul_of_nonneg_left hu'N (by positivity)
      _ = ε' / 2 + ∑ i, |lam i| * N (B.toOne (w i)) := by
          rw [mul_one]
          congr 1
          exact Finset.sum_congr rfl fun i _ => hN.smul (w i) (lam i)
      _ ≤ ε' / 2 + ∑ _i : Fin m, ‖lam‖ * 1 :=
          add_le_add le_rfl (Finset.sum_le_sum fun i _ =>
            mul_le_mul (hli i) (hwN i) (hN.nonneg _) (norm_nonneg _))
      _ = ε' / 2 + (m : ℝ) * ‖lam‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      _ ≤ ε := by linarith
  · obtain ⟨hsub, htameS, hloc, -⟩ :=
      theorem_3_6_11 hhF.toIsScFredholmSection (fun y hy => hgood y hy) hne
    exact ⟨hsub, htameS, hloc⟩

end DenseGoodPosition

end Polyfold
