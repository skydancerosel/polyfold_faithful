import Polyfold.Chapter12.P3W3O_StabTransfer

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
p. 594: a step of the proof of the last sentence of **Theorem 12.5.3** (2017: Theorem 12.11).

# Push-forward data carried along a local strong bundle isomorphism

Part I's push-forward of orientations along a short path (`IsPush`, §6.6) is made from sc⁺-sections
of the pull-back bundle over `ℝ × X` and stabilized kernels in one chart.  For a local strong
bundle isomorphism `L : Y|U → Y'|U'` over `ϕ`, with `f = Ψ ∘ f' ∘ ϕ` on `U`:

* `LocalIso.isZeroAt_of_transportChart`: zeros of `f' + S'` at `ϕ(x)` are zeros of `f + S` at `x`
  when `S` has in `cT` the principal part of `S'` in `c`;
* `LocalIso.isPush_mpull`: **a push-forward `e'` of `f'` along `ϕ ∘ γ` in a chart `c_W` of `Y'`
  is carried to a push-forward of `f` along `γ` in the transported chart**, namely
  `morPull⁻¹ ∘ e' ∘ morPull`.  The sections are carried by `exists_pullSection` from a larger
  chart `c₀ ⊇ c_W` with a cut-off `β` equal to `1` on the domain of the transported `c_W`; the
  stabilized kernels by `isStabKernels_mpull`; the push-forwards correspond by `push_mpull`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter Module

noncomputable section

namespace Polyfold

open StrongRetr

universe u v u' v'

section PushPull

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {X' : Type u'} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type v'} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle PX' P'}
  {f : X → Y} {f' : X' → Y'}

namespace StrongBundle.LocalIso

variable {U : Set X} {U' : Set X'} (L : LocalIso B B' U U')

/-- **Zeros are carried along `L`**: if `S` has in the transported chart `cT` the principal part
of `S'` in `c`, then a zero of `f' + S'` at `ϕ(x)` is a zero of `f + S` at `x`. -/
theorem isZeroAt_of_transportChart {c : StrongBundleChart PX' P'} (hsub : c.φ.source ⊆ U')
    (hfs : IsSection P f) (hfs' : IsSection P' f') (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U)
    {S : X → Y} {S' : X' → Y'} (hS : IsSection P S) (hS' : IsSection P' S')
    (hSe : ∀ x ∈ (L.transportChart c hsub).φ.source,
      ((L.transportChart c hsub) (S x)).2 = (c (S' (L.ϕ x))).2)
    {x : X} (hx : x ∈ (L.transportChart c hsub).φ.source)
    (h0 : IsZeroAt P' (sectionAdd P' f' S') (L.ϕ x)) : IsZeroAt P (sectionAdd P f S) x := by
  have h0' := (c.isZeroAt_iff (hfs'.sectionAdd hS') hx.2).1 h0
  refine ((L.transportChart c hsub).isZeroAt_iff (hfs.sectionAdd hS) hx).2 ?_
  exact (L.principal_transportChart_sectionAdd hsub hfs hfs' hfL hS hS' hSe
    (c.φ.mapsTo_model _ hx.2)).trans h0'

variable [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X')]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P' (Prod.snd : (Fin n → ℝ) × X' → X'))]

/-- **A push-forward carried along `L`** (§6.6, pp. 223–224, with §12.5, p. 594): let `c₀` be a
chart of `Y'` with domain in `U'`, `c_W = c₀|W` its restriction to an open `W`, `cT` the
transported chart of `c_W`, and `β` an sc-smooth function supported in the domain of the
transported chart of `c₀` and equal to `1` on the domain of `cT`.  Then a push-forward `e'` of
`f'` along `ϕ ∘ γ` in `c_W` gives the push-forward `morPull⁻¹ ∘ e' ∘ morPull` of `f` along `γ`
in `cT`. -/
theorem isPush_mpull (hf : B.IsScFredholmSection f) (hf' : B'.IsScFredholmSection f')
    (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) (hsec : B.HasScPlusSectionsThrough)
    (hsec' : B'.HasScPlusSectionsThrough) {c₀ : StrongBundleChart PX' P'} (hc₀ : B'.IsChart c₀)
    (hsub₀ : c₀.φ.source ⊆ U') {W : Set X'} (hW : IsOpen W) {β : X → ℝ}
    (hβ : PX.IsScSmoothMap realPolyfold β)
    (hβs : tsupport β ⊆ (L.transportChart c₀ hsub₀).φ.source)
    (hβ1 : ∀ x ∈ (L.transportChart (c₀.restrictInter hW) fun _ hy => hsub₀ hy.1).φ.source,
      β x = 1)
    {γ : (Fin 1 → ℝ) → X} (hγc : Continuous γ)
    (hγ : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1,
      γ q ∈ (L.transportChart (c₀.restrictInter hW) fun _ hy => hsub₀ hy.1).φ.source)
    (hs₀ : γ (pt1 0) ∈ PX.smoothSet) (hs₁ : γ (pt1 1) ∈ PX.smoothSet)
    (hs₀' : L.ϕ (γ (pt1 0)) ∈ PX'.smoothSet) (hs₁' : L.ϕ (γ (pt1 1)) ∈ PX'.smoothSet)
    {e' : (chartPtOf (c₀.restrictInter hW) (hc₀.restrictInter hW)
        (hγ _ (pt1_mem_Icc (left_mem_Icc.2 zero_le_one))).2 hs₀').Or f' hf' ≃
      (chartPtOf (c₀.restrictInter hW) (hc₀.restrictInter hW)
        (hγ _ (pt1_mem_Icc (right_mem_Icc.2 zero_le_one))).2 hs₁').Or f' hf'}
    (he' : IsPush f' hf' (c₀.restrictInter hW) (hc₀.restrictInter hW) (fun q => L.ϕ (γ q))
      (fun q hq => (hγ q hq).2) rfl rfl
      (hγ _ (pt1_mem_Icc (left_mem_Icc.2 zero_le_one))).2
      (hγ _ (pt1_mem_Icc (right_mem_Icc.2 zero_le_one))).2 hs₀' hs₁' e') :
    IsPush f hf (L.transportChart (c₀.restrictInter hW) fun _ hy => hsub₀ hy.1)
      (L.isChart_transportChart _ _ (hc₀.restrictInter hW)) γ hγ rfl rfl
      (hγ _ (pt1_mem_Icc (left_mem_Icc.2 zero_le_one)))
      (hγ _ (pt1_mem_Icc (right_mem_Icc.2 zero_le_one))) hs₀ hs₁
      (((L.morPull hf hf' (chartPtOf (c₀.restrictInter hW) (hc₀.restrictInter hW)
          (hγ _ (pt1_mem_Icc (left_mem_Icc.2 zero_le_one))).2 hs₀') (fun _ hy => hsub₀ hy.1)
          (hγ _ (pt1_mem_Icc (left_mem_Icc.2 zero_le_one))).1 rfl
          (linSet_mpullPt hf hf' hfL hsec hsec' hs₀ hs₀')).symm.trans e').trans
        (L.morPull hf hf' (chartPtOf (c₀.restrictInter hW) (hc₀.restrictInter hW)
          (hγ _ (pt1_mem_Icc (right_mem_Icc.2 zero_le_one))).2 hs₁') (fun _ hy => hsub₀ hy.1)
          (hγ _ (pt1_mem_Icc (right_mem_Icc.2 zero_le_one))).1 rfl
          (linSet_mpullPt hf hf' hfL hsec hsec' hs₁ hs₁'))) := by
  have hsubW : (c₀.restrictInter hW).φ.source ⊆ U' := fun _ hy => hsub₀ hy.1
  have hfs := hf.isScSmooth.1
  have hfs' := hf'.isScSmooth.1
  obtain ⟨S', hS', hz', k, s', hs', Λ, hΛ, rfl⟩ := he'
  obtain ⟨S, hS, hSv⟩ := L.exists_pullSection hc₀ hsub₀ hβ hβs hS'
  choose s hs hsv using fun i => L.exists_pullSection hc₀ hsub₀ hβ hβs (hs' i)
  have hSe : ∀ q : Fin 1 → ℝ, ∀ x ∈ (L.transportChart (c₀.restrictInter hW) hsubW).φ.source,
      ((L.transportChart (c₀.restrictInter hW) hsubW) (pullbackSlice S q x)).2 =
        ((c₀.restrictInter hW) (pullbackSlice S' q (L.ϕ x))).2 := fun q x hx => by
    have h := hSv q x ⟨hx.1, hx.2.1⟩
    rw [hβ1 x hx, one_smul] at h
    exact h
  have hse : ∀ i, ∀ q : Fin 1 → ℝ,
      ∀ x ∈ (L.transportChart (c₀.restrictInter hW) hsubW).φ.source,
      ((L.transportChart (c₀.restrictInter hW) hsubW) (pullbackSlice (s i) q x)).2 =
        ((c₀.restrictInter hW) (pullbackSlice (s' i) q (L.ϕ x))).2 := fun i q x hx => by
    have h := hsv i q x ⟨hx.1, hx.2.1⟩
    rw [hβ1 x hx, one_smul] at h
    exact h
  have hy : ∀ q : Icc (0 : Fin 1 → ℝ) 1,
      (q : Fin 1 → ℝ) ∈ γ ⁻¹' (L.transportChart (c₀.restrictInter hW) hsubW).φ.source :=
    fun q => hγ q q.2
  have hΛT := L.isStabKernels_mpull (c := c₀.restrictInter hW) (hc := hc₀.restrictInter hW)
    hsubW hf.isScSmooth hf'.isScSmooth hfL (y := fun q : Icc (0 : Fin 1 → ℝ) 1 => γ q) hy hΛ
    (S := fun q => pullbackSlice S q) (s := fun i q => pullbackSlice (s i) q)
    (fun q => hS.pullbackSlice q) (fun i q => (hs i).1.pullbackSlice q) (fun q => hSe q)
    (fun i q => hse i q)
  refine ⟨S, hS, ?_, k, s, hs, Λ, hΛT, ?_⟩
  · have hO : IsOpen (γ ⁻¹' (L.transportChart (c₀.restrictInter hW) hsubW).φ.source) :=
      (L.transportChart (c₀.restrictInter hW) hsubW).φ.isOpen_source.preimage hγc
    filter_upwards [hz', hO.mem_nhdsSet.2 (fun q hq => hγ q hq)] with q hq hqO
    have hL : IsSection (pullbackProj P Prod.snd) (paramLift (n := 1) f hfs) :=
      isSection_pullbackLift _
    have hL' : IsSection (pullbackProj P' Prod.snd) (paramLift (n := 1) f' hfs') :=
      isSection_pullbackLift _
    rw [isZeroAt_pullback_iff_pullbackSlice (hL.sectionAdd hS.1) q (γ q),
      pullbackSlice_sectionAdd_paramLift hfs hS.1 q]
    rw [isZeroAt_pullback_iff_pullbackSlice (hL'.sectionAdd hS'.1) q _,
      pullbackSlice_sectionAdd_paramLift hfs' hS'.1 q] at hq
    exact L.isZeroAt_of_transportChart hsubW hfs hfs' hfL (hS.pullbackSlice q).1
      (hS'.pullbackSlice q).1 (hSe q) hqO hq
  · refine Equiv.ext fun o => ?_
    have key := L.push_mpull (c := c₀.restrictInter hW) (hc := hc₀.restrictInter hW) hsubW hf hf'
      hfL hy hΛ (S := fun q => pullbackSlice S q) (s := fun i q => pullbackSlice (s i) q)
      (fun q => hS.pullbackSlice q) (fun i q => (hs i).1.pullbackSlice q) (fun q => hSe q)
      (fun i q => hse i q) ⟨pt1 0, pt1_mem_Icc (left_mem_Icc.2 zero_le_one)⟩
      ⟨pt1 1, pt1_mem_Icc (right_mem_Icc.2 zero_le_one)⟩ hs₀ hs₀' hs₁ hs₁'
      _ (exists_lift_of_smooth (c₀.restrictInter hW)
        (hγ _ (pt1_mem_Icc (left_mem_Icc.2 zero_le_one))).2 hs₀').choose_spec
      _ (exists_lift_of_smooth (c₀.restrictInter hW)
        (hγ _ (pt1_mem_Icc (right_mem_Icc.2 zero_le_one))).2 hs₁').choose_spec
      (linSet_mpullPt hf hf' hfL hsec hsec' hs₀ hs₀')
      (linSet_mpullPt hf hf' hfL hsec hsec' hs₁ hs₁')
      ((L.morPull hf hf' (chartPtOf (c₀.restrictInter hW) (hc₀.restrictInter hW)
          (hγ _ (pt1_mem_Icc (left_mem_Icc.2 zero_le_one))).2 hs₀') (fun _ hy => hsub₀ hy.1)
          (hγ _ (pt1_mem_Icc (left_mem_Icc.2 zero_le_one))).1 rfl
          (linSet_mpullPt hf hf' hfL hsec hsec' hs₀ hs₀')).symm o)
    erw [Equiv.apply_symm_apply] at key
    exact key.symm

end StrongBundle.LocalIso

end PushPull

end Polyfold
