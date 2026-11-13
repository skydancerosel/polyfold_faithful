import Polyfold.Chapter5.CylinderPerturbation2021

/-!
# Remark 5.3.8 for a general sc-Fredholm arc

2021 Remark 5.3.8, p. 219 (2017: Remark 5.4; preprint: Remark 5.16, pp. 176–177).  The remark
considers sc-Fredholm sections `f₀`, `f₁` of `P` that are transversal and have compact solution
sets, joined by an arc `t ↦ f_t` such that `(t, x) ↦ f_t(x)` is sc-Fredholm on `[0, 1] × X` with a
compact solution set.  A small perturbation `s`, supported near the solution set and with
`s(t, ·) = 0` for `t` close to `0` and `1`, makes the arc transversal.  Its solution set is then a
compact cobordism between `S_{f₀}` and `S_{f₁}`.

`Chapter5/CylinderPerturbation2021.lean` (`exists_cobordism`) and `Chapter6/ProperHomotopy2021.lean`
(`exists_homotopy_cobordism`) treat the arcs of the form `f₀ + S(t, ·)` with `S` an sc⁺-section.
This file treats a general sc-Fredholm arc.

## What is formalized

* `exists_margin_of_isCompact`: for a compact set `K` of zeros of an sc-Fredholm section `f` and
  an open `V ⊇ K`, some open `K ⊆ W ⊆ V` has `cl{x ∈ W | N(f(x)) ≤ 1}` compact (the local step of
  Theorem 5.2.2 over `K`).
* `remark_5_3_8_relative`: the remark for a section `F` over any tame M-polyfold with bump
  functions and a continuous "time" `τ`.  Suppose `F` is in general position at its zeros with
  `τ ∉ (a, b)` and its zeros with `τ ∈ [c, d]` form a compact set, where `c < a`, `b < d`.  Then
  for every `ε > 0` there is an sc⁺-section `p` with `N(p) ≤ ε`, vanishing where `τ ≤ c'` or
  `τ ≥ d'` for some `c < c' < a`, `b < d' < d`, such that `F + p` is in general position at every
  zero and its zeros with `τ ∈ [c, d]` form a compact set.
* `remark_5_3_8_arc`: the case of the remark, `F(t, x) = f_t(x)` a section of the pull-back of `P`
  to `ℝ¹ × X`, `τ = t`, `[c, d] = [0, 1]`.

## Readings

* `[0, 1] × X` is read as `ℝ¹ × X` with the time window `[0, 1]` (decision D2 of the Theorem 6.7.1
  plan), so that no tame structure on `[0, 1] × X` is needed.
* "`f₀`, `f₁` transversal ... (we already have transversality at the boundaries)" is read as:
  `F` is in general position at its zeros with `t ∉ (a, b)` for some `0 < a`, `b < 1`.  For `X`
  without boundary and `F` stationary near `t = 0, 1` this is the transversality of `f₀`, `f₁`.
* "The section has a compact solution set" is read as: the zeros of `F` over `[0, 1]` form a
  compact set.
* "A perturbation `s` supported in `U`, small": the perturbation `p` is supported in an open
  `W ⊆ (c', d') × X` around the zeros over `[a, b]` with `cl{z ∈ W | N(F(z)) ≤ 1}` compact, and
  `N(p) ≤ ε`.
-/

open Set Filter Topology Function MeasureTheory

noncomputable section

namespace Polyfold

universe u v

section Remark538

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

open StrongBundle

/-- **The margin of Theorem 5.2.2 (2021 p. 210) over a compact set of zeros**: for an sc-Fredholm
section `f`, an auxiliary norm `N`, a compact set `K` of zeros of `f` and an open `V ⊇ K`, there is
an open `W` with `K ⊆ W ⊆ V` and `cl{x ∈ W | N(f(x)) ≤ 1}` compact.  (The local step of the proof
of Theorem 5.2.2, `theorem_5_2_2_preprint`, at the points of `K`.) -/
theorem exists_margin_of_isCompact {f : X → Y} (hf : B.IsScFredholmSection f) {N : B.One → ℝ}
    (hN : B.IsAuxNorm N) {K : Set X} (hK : IsCompact K) (hK0 : ∀ x ∈ K, IsZeroAt P f x)
    {V : Set X} (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ W : Set X, IsOpen W ∧ K ⊆ W ∧ W ⊆ V ∧ IsCompact (closure {x ∈ W | B.AuxLe N (f x) 1}) := by
  have hsec := hf.isScSmooth.1
  have hloc : ∀ x ∈ K, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧
      IsCompact (closure {y ∈ W | B.AuxLe N (f y) 1}) := by
    intro x hx
    obtain ⟨c, hc, hxc, W, hWo, hxW, hWc, hKc⟩ :=
      exists_nbhd_isCompact_closure_bdd (hf.germ x (hf.mem_smoothSet_of_isZeroAt (hK0 x hx)))
    obtain ⟨V₁, hV₁o, hxV₁, -, A, hA, hV₁⟩ := hN.exists_norm_liftOne_le hc hxc
    refine ⟨W ∩ V₁, hWo.inter hV₁o, ⟨hxW, hxV₁⟩,
      (hKc A).of_isClosed_subset isClosed_closure (closure_mono ?_)⟩
    rintro y ⟨⟨hyW, hyV₁⟩, hy1, hyN⟩
    refine ⟨hyW, (c.liftOne (f y)).2, ?_, ?_⟩
    · exact toBase_liftOne_snd hc (c.mem_source_of_proj (by rw [hsec y]; exact hWc hyW)) hy1
    · have := hV₁ (B.oneMk (f y) hy1) (by rw [oneVal_oneMk, hsec y]; exact hyV₁)
      rw [oneVal_oneMk] at this
      calc ‖(c.liftOne (f y)).2‖ ≤ A * N (B.oneMk (f y) hy1) := this
        _ ≤ A * 1 := mul_le_mul_of_nonneg_left hyN hA.le
        _ = A := mul_one A
  choose! W hWo hxW hWK using hloc
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover W fun x hx => (hWo x hx).mem_nhds (hxW x hx)
  refine ⟨(⋃ x ∈ t, W x) ∩ V, (isOpen_biUnion fun x hx => hWo x (htK x hx)).inter hV,
    subset_inter hcover hKV, inter_subset_right, ?_⟩
  have hKt : IsCompact (⋃ x ∈ t, closure {y ∈ W x | B.AuxLe N (f y) 1}) :=
    t.isCompact_biUnion fun x hx => hWK x (htK x hx)
  refine hKt.of_isClosed_subset isClosed_closure (closure_minimal ?_ hKt.isClosed)
  rintro y ⟨⟨hyU, -⟩, hyN⟩
  obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 hyU
  exact mem_iUnion₂.2 ⟨x, hx, subset_closure ⟨hyx, hyN⟩⟩

/-- **2021 Remark 5.3.8, p. 219 (preprint Remark 5.16), relative to a time function.**  Let `X` be
tame with sc-smooth bump functions, `F` an sc-Fredholm section with tame germ data, `N` an
auxiliary norm, `τ : X → ℝ` continuous and `c < a`, `b < d`.  Suppose `(F, x)` is in general
position at every zero with `τ(x) ∉ (a, b)`, and the zeros of `F` with `τ ∈ [c, d]` form a compact
set.  Then for every `ε > 0` there are `c < c' < a`, `b < d' < d` and an sc⁺-section `p` with
`N(p) ≤ ε`, vanishing where `τ ∉ (c', d')`, such that `(F + p, x)` is in general position at every
zero and the zeros of `F + p` with `τ ∈ [c, d]` form a compact set.  *Proof*: the margin
`exists_margin_of_isCompact` around the zeros over `[a, b]` inside `τ⁻¹(c', d')`, and Theorem 5.3.10
relative to that compact set (`theorem_5_3_10_relative_hyp`). -/
theorem remark_5_3_8_relative (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    {F : X → Y} (hF : B.IsScFredholmSectionTame F) {N : B.One → ℝ} (hN : B.IsAuxNorm N)
    {τ : X → ℝ} (hτ : Continuous τ) {a b c d : ℝ} (hca : c < a) (hbd : b < d)
    (hgp : ∀ x, IsZeroAt P F x → τ x ∉ Ioo a b → B.IsGeneralPositionGerm F x)
    (hK : IsCompact {x ∈ solutionSet P F | τ x ∈ Icc c d}) {ε : ℝ} (hε : 0 < ε) :
    ∃ c' d' : ℝ, c < c' ∧ c' < a ∧ b < d' ∧ d' < d ∧
      ∃ p : X → Y, B.IsScPlusSection p ∧ (∀ x, τ x ∉ Ioo c' d' → IsZeroAt P p x) ∧
        (∀ x, B.AuxLe N (p x) ε) ∧
        (∀ x, IsZeroAt P (sectionAdd P F p) x → B.IsGeneralPositionGerm (sectionAdd P F p) x) ∧
        IsCompact {x ∈ solutionSet P (sectionAdd P F p) | τ x ∈ Icc c d} := by
  have hFs : IsSection P F := hF.isScSmooth.1
  have hFF := hF.toIsScFredholmSection
  set c' := (c + a) / 2 with hc'
  set d' := (b + d) / 2 with hd'
  -- the compact `K` of zeros over `[a, b]`, inside `τ⁻¹(c', d')`
  set K := {x ∈ solutionSet P F | τ x ∈ Icc a b} with hKdef
  have hKc : IsCompact K := by
    refine hK.of_isClosed_subset ((isClosed_solutionSet hF.isScSmooth).inter
      (isClosed_Icc.preimage hτ)) fun x hx => ⟨hx.1, ?_, ?_⟩
    · linarith [hx.2.1]
    · linarith [hx.2.2]
  set V := τ ⁻¹' Ioo c' d' with hVdef
  have hVo : IsOpen V := isOpen_Ioo.preimage hτ
  have hKV : K ⊆ V := fun x hx => ⟨by linarith [hx.2.1], by linarith [hx.2.2]⟩
  obtain ⟨W, hWo, hKW, hWV, hWc⟩ :=
    exists_margin_of_isCompact hFF hN hKc (fun x hx => hx.1) hVo hKV
  -- the perturbation
  set η := min ε 1 with hη
  have hηpos : 0 < η := lt_min hε one_pos
  have hgpK : ∀ x, IsZeroAt P F x → x ∉ K → B.IsGeneralPositionGerm F x := fun x hx hxK =>
    hgp x hx fun h => hxK ⟨hx, h.1.le, h.2.le⟩
  obtain ⟨p, hp, hpW, hpN, hgpp⟩ :=
    theorem_5_3_10_relative_hyp hX hbump hF hN hWo hKc hKW hgpK hWc hηpos
  have hp0 : ∀ x ∉ W, IsZeroAt P p x := fun x hx =>
    not_not.1 fun hne => hx (hpW (subset_closure hne))
  refine ⟨c', d', by linarith, by linarith, by linarith, by linarith, p, hp,
    fun x hx => hp0 x fun h => hx (hWV h), fun x => (hpN x).mono (min_le_left _ _), hgpp, ?_⟩
  -- the zeros of `F + p` over `[c, d]` lie in the union of two compact sets
  have hcl : IsClosed {x ∈ solutionSet P (sectionAdd P F p) | τ x ∈ Icc c d} :=
    (isClosed_solutionSet (theorem_3_1_18_tame hF hp).isScSmooth).inter
      (isClosed_Icc.preimage hτ)
  refine (hK.union hWc).of_isClosed_subset hcl fun x hx => ?_
  by_cases hxW : x ∈ W
  · refine Or.inr (subset_closure ⟨hxW, ?_⟩)
    exact (hN.auxLe_of_sectionAdd hFs hp.1 hx.1 (hpN x)).mono (min_le_right _ _)
  · refine Or.inl ⟨?_, hx.2⟩
    have h1 : IsZeroAt P (sectionAdd P F p) x := hx.1
    change F x = fiberZero P x
    unfold IsZeroAt at h1
    rw [sectionAdd_apply hFs hp.1] at h1
    have e : (⟨p x, hp.1 x⟩ : P ⁻¹' {x}) = 0 := Subtype.ext (hp0 x hxW)
    rw [e, add_zero] at h1
    exact h1

variable [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))]

/-- **2021 Remark 5.3.8, p. 219 (preprint Remark 5.16), for a general sc-Fredholm arc.**  Let `X`
be tame with sc-smooth bump functions, and let `F(t, x) = f_t(x)` be an sc-Fredholm section (tame
germ data) of the pull-back of `P` to `ℝ¹ × X`, with an auxiliary norm `N`.  Suppose that for some
`0 < a`, `b < 1` the arc is in general position at its zeros with `t ∉ (a, b)` (the
transversality of `f₀`, `f₁` near the ends), and that its zeros over `[0, 1]` form a compact set.
Then for every `ε > 0` there is an sc⁺-section `s` of the pull-back with `N(s) ≤ ε` and
`s(t, ·) = 0` for `t` close to `0` and `1` (`t ∉ (c', d')`, `0 < c' < a`, `b < d' < 1`), such that
`(t, x) ↦ f_t(x) + s(t, x)` is in general position at every zero and its zeros over `[0, 1]` form a
compact set (the cobordism of the remark, a manifold with boundary by Theorem 3.6.11). -/
theorem remark_5_3_8_arc (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    {F : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
    (hF : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScFredholmSectionTame F)
    {N : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).One → ℝ}
    (hN : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsAuxNorm N)
    {a b : ℝ} (ha : 0 < a) (hb : b < 1)
    (hgp : ∀ z, IsZeroAt (pullbackProj P Prod.snd) F z → z.1 0 ∉ Ioo a b →
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsGeneralPositionGerm F z)
    (hK : IsCompact {z ∈ solutionSet (pullbackProj P Prod.snd) F | z.1 0 ∈ Icc (0 : ℝ) 1})
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c' d' : ℝ, 0 < c' ∧ c' < a ∧ b < d' ∧ d' < 1 ∧
      ∃ s : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X),
        (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection s ∧
        (∀ z : (Fin 1 → ℝ) × X, z.1 0 ∉ Ioo c' d' → IsZeroAt (pullbackProj P Prod.snd) s z) ∧
        (∀ z, (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).AuxLe N (s z) ε) ∧
        (∀ z, IsZeroAt (pullbackProj P Prod.snd) (sectionAdd (pullbackProj P Prod.snd) F s) z →
          (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsGeneralPositionGerm
            (sectionAdd (pullbackProj P Prod.snd) F s) z) ∧
        IsCompact {z ∈ solutionSet (pullbackProj P Prod.snd)
          (sectionAdd (pullbackProj P Prod.snd) F s) | z.1 0 ∈ Icc (0 : ℝ) 1} :=
  remark_5_3_8_relative (prod_rn_isTame hX) (MPolyfold.admitsBumpFunctions_prod_rn hbump) hF hN
    (continuous_fst_apply_zero (X := X)) ha hb hgp hK hε

end Remark538

end Polyfold
