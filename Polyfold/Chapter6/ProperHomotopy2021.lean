import Polyfold.Chapter5.CylinderPerturbation2021
import Polyfold.Chapter6.PerturbedOrientation

/-!
# Proper oriented homotopies and their cobordisms (2021 Theorem 6.7.1 (2))

Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021): the homotopy part (2) of
Theorem 6.7.1 (p. 277; preprint Theorem 6.43), and the cobordism its proof uses ("the same
homotopy argument as in (1)", p. 279).

* `StrongBundle.IsScPlusSection.reparamSmooth`: for an sc⁺-section `S` of the pull-back
  `π*P → ℝⁿ × X` and a `C^∞` map `g : ℝᵐ → ℝⁿ`, `S ∘ (g × 1)` is an sc⁺-section of
  `π*P → ℝᵐ × X` (the existing `IsScPlusSection.reparam` treats affine `g`).
* `exists_isOpen_isCompact_closure_auxLe`: Theorem 5.2.2 (p. 210) near a compact part `K` of the
  solution set of an sc-Fredholm section.
* `slabZeros G a b`: the zeros of a section `G` of `π*P → ℝ¹ × X` over the slab `[a, b] × X`.
* `StrongBundle.IsProperOrientedHomotopy f₀ hf₀ S`: the proper homotopy of (2), in reading R-d
  of the Theorem 6.7.1 plan. The text does not define a proper oriented homotopy; the only oriented
  homotopy in it is that of Remark 6.6.19 (p. 276), `f̂(t, x) = f₀(x) + S(t, x)` for an
  sc⁺-section `S` over `[0, 1] × X`, oriented by the standard orientation of `[0, 1]` and `o₀`. We
  read `[0, 1] × X` as `ℝ¹ × X` (decision D2): `S` is an sc⁺-section of the pull-back over
  `ℝ¹ × X`, `S(0, ·) = 0`, the zeros of `F = f̃₀ + S` over the slab `t ∈ [0, 1]` form a compact
  set, and `F` satisfies the properness clause of Definition 5.2.1 (3) on the slab. Then
  `f₁ = f₀ + S(1, ·)` (`IsProperOrientedHomotopy.isProper_one`: proper) with the orientation
  `o₁ = o₀.sectionAdd` (`IsProperOrientedHomotopyBetween`).
* `isProperOrientedHomotopy_of_isCompact`: the properness clause follows from the compactness of
  the slab (the analogue of Theorem 5.2.2); `witness_isProperOrientedHomotopy`: `S = 0`.
* `IsProperOrientedHomotopy.exists_slab_nbhd`: the slab-adapted neighbourhoods `W` of the zeros
  over the slab, with `cl{z ∈ W | t ∈ [0, 1], N(F(z)) ≤ C}` compact.
* `StrongBundle.IsCobordismData f hf σ₀ σ₁ Ŝ`: an sc⁺-section `Ŝ` over `ℝ¹ × X` with
  `Ŝ(t, ·) = σ₀` for `t ≤ 1/8`, `Ŝ(t, ·) = σ₁` for `t ≥ 7/8`, `f + σᵢ` and `f̃ + Ŝ` in general
  position at every zero, and the zeros of `f̃ + Ŝ` over every `[a, b]` compact. Both cobordisms of
  the proof of Theorem 6.7.1 produce it: part (1) (`exists_isCobordismData`, from
  `exists_cobordism`) and part (2) (`exists_homotopy_cobordism`).
* `exists_homotopy_cobordism`: for a proper homotopy `S` from `f₀` to `f₁`, an auxiliary norm `N`,
  a slab-adapted `W` and `s₀`, `s₁` admissible for `f₀`, `f₁` with supports in the ends of `W`,
  there is `Ŝ` with `IsCobordismData f₀ s₀ (S(1, ·) + s₁) Ŝ`, so that `f̃₀ + Ŝ` is `f₀ + s₀` for
  `t ≤ 1/8` and `f₁ + s₁` for `t ≥ 7/8`. `exists_homotopy_cobordism_data`: such `s₀`, `s₁` exist
  inside any given neighbourhoods of `S_{f₀}`, `S_{f₁}`.

The orientation of the cobordism (Remark 6.6.19, gap G.66) is not built here.
-/

open Set Filter Topology Function
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

/-! ### Smooth reparametrizations of sections over `ℝⁿ × X` -/

section Reparam

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

/-- **An sc⁺-section reparametrized along a smooth map is sc⁺** (the reparametrization
`Ŝ ∘ (χ × 1)` of the proof of 2021 Theorem 6.7.1 (2), p. 279): for an sc⁺-section `S` of
`π*P → ℝⁿ × X` and a `C^∞` map `g : ℝᵐ → ℝⁿ`, `(q, y) ↦ S(g(q), y)` is an sc⁺-section of
`π*P → ℝᵐ × X`. In the product charts at `(q, x)` and `(g(q), x)` its representative is that of
`S` composed with `(a, u) ↦ (g(a + q) − g(q), u)`, which is sc-smooth (the constant structure on
`ℝᵐ`). `IsScPlusSection.reparam` is the affine case. -/
theorem StrongBundle.IsScPlusSection.reparamSmooth {m n : ℕ}
    [ParacompactSpace ((Fin n → ℝ) × X)]
    [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
    [ParacompactSpace ((Fin m → ℝ) × X)]
    [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))]
    {S : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection S)
    {g : (Fin m → ℝ) → (Fin n → ℝ)} (hg : ContDiff ℝ ∞ g) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsScPlusSection
      (reparamSection g S hS.1) := by
  set S' := reparamSection g S hS.1 with hS'
  have hsec : IsSection (pullbackProj P (Prod.snd : (Fin m → ℝ) × X → X)) S' :=
    isSection_pullbackLift _
  refine StrongBundle.isScPlusSection_of_local hsec fun z => ?_
  obtain ⟨c, hc, hxc⟩ := StrongBundle.exists_chart_mem B z.2
  -- the product charts at `z = (q, x)` and at `(g(q), x)`
  set c' := (PullbackChartData.ofProd c z.1).toChart (S' z) with hc'
  set pc := (PullbackChartData.ofProd c (g z.1)).toChart (S (g z.1, z.2)) with hpc
  have hmem' : c' ∈ (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).atlas.charts :=
    ⟨_, _, hc, rfl⟩
  have hmem : pc ∈ (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).atlas.charts :=
    ⟨_, _, hc, rfl⟩
  obtain ⟨hrange, hsm⟩ := hS.2 pc hmem
  have hsrc : ∀ w ∈ c'.φ.source, ((g w.1, w.2) : (Fin n → ℝ) × X) ∈ pc.φ.source :=
    fun w hw => ⟨mem_univ _, hw.2⟩
  refine ⟨c', hmem', ⟨mem_univ _, hxc⟩, fun w hw => hrange _ (hsrc w hw), ?_⟩
  have hO : IsScRetract c'.φ.model.E c'.φ.model.C c'.φ.model.O := c'.φ.model.isScRetract
  -- the map `(a, u) ↦ (g(a + q) − g(q), u)` of retracts `ℝᵐ × O → ℝⁿ × O`
  set h : (Fin m → ℝ) → (Fin n → ℝ) := fun a => g (a + z.1) - g z.1 with hh
  have hhs : ContDiff ℝ ∞ h := (hg.comp (contDiff_id.add contDiff_const)).sub contDiff_const
  have h1 : IsScSmoothRetractMap c'.φ.model.E c'.φ.model.C c'.φ.model.O (rnSc m) univ univ
      (ScBanach.prodFstOp (rnSc m) c.φ.model.E 0) :=
    (ScBanach.prodFstOp _ _).isScSmoothRetractMap hO (mapsTo_univ _ _)
  have h2 : IsScSmoothRetractMap (rnSc m) univ univ (rnSc n) univ univ h :=
    isScSmoothRetractMap_const_of_contDiff hhs
  have h3 := h2.comp h1 (isScRetract_univ (rnSc m))
  have h4 : IsScSmoothRetractMap c'.φ.model.E c'.φ.model.C c'.φ.model.O c.φ.model.E
      c.φ.model.C c.φ.model.O (ScBanach.prodSndOp (rnSc m) c.φ.model.E 0) :=
    (ScBanach.prodSndOp _ _).isScSmoothRetractMap hO fun p hp => hp.2
  have hT : IsScSmoothRetractMap c'.φ.model.E c'.φ.model.C c'.φ.model.O pc.φ.model.E
      pc.φ.model.C pc.φ.model.O
      (scPair (h ∘ ScBanach.prodFstOp (rnSc m) c.φ.model.E 0)
        (ScBanach.prodSndOp (rnSc m) c.φ.model.E 0)) :=
    h3.scPair h4 fun p hp => show ((h p.1, p.2) : (Fin n → ℝ) × c.φ.model.E 0) ∈
      univ ×ˢ c.φ.model.O from ⟨mem_univ _, hp.2⟩
  have hcomp := hsm.comp hT pc.φ.model.isScRetract
  refine ⟨fun w hw => ?_, fun R hR => ?_⟩
  · have hws := c'.φ.symm_mapsTo hw
    exact c'.liftOne_mem (c'.mem_source_of_proj (by rw [hsec]; exact hws))
      (hrange _ (hsrc _ hws))
  · have hU := R.isScDomain
    have h1 := (hcomp.comp_isScSmooth R hR).snd hU
    have h2 := R.isScSmooth.scPair hU h1
    refine h2.congr hU fun w hw => ?_
    have hRw : R w ∈ c'.φ.model.O := by rw [← hR]; exact R.apply_mem_retract hw
    -- `(p, pr₂ (localRepOne pc S (h(a), u))) = localRepOne c' S' p` for `p = (a, u)`
    change (R w, (StrongBundle.localRepOne pc S ((h (R w).1, (R w).2))).2) =
      StrongBundle.localRepOne c' S' (R w)
    generalize R w = p at hRw ⊢
    obtain ⟨a, u⟩ := p
    have hu : u ∈ c.φ.model.O := hRw.2
    set a' : Fin m → ℝ := a
    change ((a', u),
        Function.invFun (c.F.toBase 1) (c (S (h a' + g z.1, c.φ.symm u)).1.2).2) =
      ((a' + z.1 - z.1, c.φ (c.φ.symm u)),
        Function.invFun (c.F.toBase 1) (c (S (g (a' + z.1), c.φ.symm u)).1.2).2)
    rw [c.φ.apply_symm_apply hu, add_sub_cancel_right, hh, sub_add_cancel]

end Reparam

/-! ### Theorem 5.2.2 near a compact part of the solution set -/

section LocalProper

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

open StrongBundle

/-- **Theorem 5.2.2 near a compact part of the solution set** (2021 Theorem 5.2.2, p. 210;
preprint Theorem 5.5, with the proof of appendix 5.4.1): for an sc-Fredholm section `f`, a compact
`K ⊆ f⁻¹(0)` and an auxiliary norm `N` there is an open `U ⊇ K` with `cl{x ∈ U | N(f(x)) ≤ 1}`
compact. The text's theorem is the case `K = f⁻¹(0)`; the proof is the same (the local step at
each zero, `exists_nbhd_isCompact_closure_bdd` and Lemma 5.1.2, and a finite cover of `K`). -/
theorem exists_isOpen_isCompact_closure_auxLe (hf : B.IsScFredholmSection f) {K : Set X}
    (hK : IsCompact K) (hKS : K ⊆ solutionSet P f) {N : B.One → ℝ} (hN : B.IsAuxNorm N) :
    ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧ IsCompact (closure {x ∈ U | B.AuxLe N (f x) 1}) := by
  have hsec := hf.isScSmooth.1
  -- the local step at each zero
  have hloc : ∀ x ∈ K, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      IsCompact (closure {y ∈ V | B.AuxLe N (f y) 1}) := by
    intro x hxK
    have hx := hKS hxK
    obtain ⟨c, hc, hxc, V, hVo, hxV, hVc, hK⟩ :=
      exists_nbhd_isCompact_closure_bdd (hf.germ x (hf.mem_smoothSet_of_isZeroAt hx))
    obtain ⟨V₁, hV₁o, hxV₁, -, A, hA, hV₁⟩ := hN.exists_norm_liftOne_le hc hxc
    refine ⟨V ∩ V₁, hVo.inter hV₁o, ⟨hxV, hxV₁⟩,
      (hK A).of_isClosed_subset isClosed_closure (closure_mono ?_)⟩
    rintro y ⟨⟨hyV, hyV₁⟩, hy1, hyN⟩
    refine ⟨hyV, (c.liftOne (f y)).2, ?_, ?_⟩
    · exact toBase_liftOne_snd hc (c.mem_source_of_proj (by rw [hsec y]; exact hVc hyV)) hy1
    · have := hV₁ (B.oneMk (f y) hy1) (by rw [oneVal_oneMk, hsec y]; exact hyV₁)
      rw [oneVal_oneMk] at this
      calc ‖(c.liftOne (f y)).2‖ ≤ A * N (B.oneMk (f y) hy1) := this
        _ ≤ A * 1 := mul_le_mul_of_nonneg_left hyN hA.le
        _ = A := mul_one A
  choose! V hVo hxV hVK using hloc
  -- finitely many of the `V(x)` cover `K`
  obtain ⟨t, htS, hcover⟩ := hK.elim_nhds_subcover V fun x hx => (hVo x hx).mem_nhds (hxV x hx)
  refine ⟨⋃ x ∈ t, V x, isOpen_biUnion fun x hx => hVo x (htS x hx), hcover, ?_⟩
  have hK' : IsCompact (⋃ x ∈ t, closure {y ∈ V x | B.AuxLe N (f y) 1}) :=
    t.isCompact_biUnion fun x hx => hVK x (htS x hx)
  refine hK'.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK'.isClosed)
  rintro y ⟨hyU, hyN⟩
  obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 hyU
  exact mem_iUnion₂.2 ⟨x, hx, subset_closure ⟨hyx, hyN⟩⟩

end LocalProper

/-! ### Zeros over slabs `[a, b] × X` -/

section Slab

variable {X : Type u} [TopologicalSpace X] {Y : Type v} {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})]

/-- The section `F = f̃ + S` of `π*P → ℝ¹ × X` (`f̃(t, x) = f(x)`): the homotopy
`F(t, x) = f(x) + S(t, x)` of Remark 6.6.19 (2021, p. 276) and of the proof of Theorem 6.7.1. -/
abbrev homotopySection (f : X → Y) (hf : IsSection P f)
    (S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)) :
    (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X) :=
  sectionAdd (pullbackProj P Prod.snd) (paramLift f hf) S

/-- The zeros of a section `G` of `π*P → ℝ¹ × X` over the slab `[a, b] × X`. -/
def slabZeros (G : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))
    (a b : ℝ) : Set ((Fin 1 → ℝ) × X) :=
  {z ∈ solutionSet (pullbackProj P Prod.snd) G | z.1 0 ∈ Icc a b}

lemma isClosed_slabZeros {G : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
    (hG : IsClosed (solutionSet (pullbackProj P Prod.snd) G)) (a b : ℝ) :
    IsClosed (slabZeros G a b) :=
  hG.inter (isClosed_Icc.preimage ((continuous_apply 0).comp continuous_fst))

/-- **A slab of zeros lying over a compact set is compact**: if the solution set of `G` is closed
and the zeros over `[a, b]` lie over a compact `K ⊆ X`, they form a compact set (a closed part of
`[a, b] × K`). -/
lemma isCompact_slabZeros_of_subset
    {G : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
    (hG : IsClosed (solutionSet (pullbackProj P Prod.snd) G)) {a b : ℝ} {K : Set X}
    (hK : IsCompact K) (h : ∀ z ∈ slabZeros G a b, z.2 ∈ K) : IsCompact (slabZeros G a b) :=
  ((isCompact_Icc (a := fun _ : Fin 1 => a) (b := fun _ => b)).prod hK).of_isClosed_subset
    (isClosed_slabZeros hG a b) fun z hz => ⟨mem_Icc_of_apply_zero hz.2, h z hz⟩

/-- **The solution set of a slice is compact** when the slab containing it is: `S_{G(t, ·)}` is the
image under `pr_X` of the zeros over `{t}` (`isZeroAt_pullback_iff_pullbackSlice`). -/
lemma isCompact_solutionSet_pullbackSlice
    {G : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
    (hGs : IsSection (pullbackProj P Prod.snd) G) {a b : ℝ} (hK : IsCompact (slabZeros G a b))
    {t : Fin 1 → ℝ} (ht : t 0 ∈ Icc a b) : IsCompact (solutionSet P (pullbackSlice G t)) := by
  have hK' : IsCompact (slabZeros G a b ∩ Prod.fst ⁻¹' {t}) :=
    hK.inter_right (isClosed_singleton.preimage continuous_fst)
  have heq : solutionSet P (pullbackSlice G t) =
      Prod.snd '' (slabZeros G a b ∩ Prod.fst ⁻¹' {t}) := by
    ext x
    constructor
    · intro hx
      exact ⟨(t, x), ⟨⟨(isZeroAt_pullback_iff_pullbackSlice hGs t x).2 hx, ht⟩, rfl⟩, rfl⟩
    · rintro ⟨⟨t', x'⟩, ⟨⟨hz, -⟩, ht'⟩, rfl⟩
      have ht'' : t' = t := ht'
      subst ht''
      exact (isZeroAt_pullback_iff_pullbackSlice hGs t' x').1 hz
  rw [heq]
  exact hK'.image continuous_snd

end Slab

/-! ### Proper oriented homotopies (reading R-d) -/

section Homotopy

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

namespace StrongBundle

variable (B) in
/-- **A proper homotopy starting at `f₀`** (2021 Theorem 6.7.1 (2), p. 277, in reading R-d of the
Theorem 6.7.1 plan; the homotopy of Remark 6.6.19, p. 276): an sc⁺-section `S` of the pull-back
`π*P → ℝ¹ × X` with
* `S(0, ·) = 0`, so that `F = f̃₀ + S` (`F(t, x) = f₀(x) + S(t, x)`) starts at `f₀`;
* the zeros of `F` over the slab `t ∈ [0, 1]` form a compact set;
* the properness clause of Definition 5.2.1 (3) (p. 209) on the slab: for every auxiliary norm `N`
  of `π*P` there is an open `W` containing these zeros with `cl{z ∈ W | t ∈ [0, 1], N(F(z)) ≤ 1}`
  compact.
It ends at `f₁ = f₀ + S(1, ·)`. The text does not define a proper oriented homotopy; the text's
`[0, 1] × X` is read as `ℝ¹ × X` restricted to the slab (decision D2), and the orientation part,
`o₁ = o₀.sectionAdd` (the orientation `e ∧ o₀` of Remark 6.6.19 at `t = 1`), is stated separately
(`IsProperOrientedHomotopyBetween`). The properness clause follows from the compactness of the slab
(`isProperOrientedHomotopy_of_isCompact`, as in Theorem 5.2.2); `S = 0` is an instance
(`witness_isProperOrientedHomotopy`). -/
structure IsProperOrientedHomotopy (f₀ : X → Y) (hf₀ : B.IsScFredholmSectionTame f₀)
    (S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)) : Prop where
  isScPlusSection :
    haveI := paracompactSpace_rn_prod PX 1
    haveI := paracompactSpace_rn_pullback B 1
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection S
  slice_zero : pullbackSlice S 0 = fiberZero P
  isCompact_slab : IsCompact (slabZeros (homotopySection f₀ hf₀.isScSmooth.1 S) 0 1)
  proper :
    haveI := paracompactSpace_rn_prod PX 1
    haveI := paracompactSpace_rn_pullback B 1
    ∀ N : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).One → ℝ,
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsAuxNorm N →
        ∃ W : Set ((Fin 1 → ℝ) × X), IsOpen W ∧
          slabZeros (homotopySection f₀ hf₀.isScSmooth.1 S) 0 1 ⊆ W ∧
          IsCompact (closure {z ∈ W | z.1 0 ∈ Icc (0 : ℝ) 1 ∧
            (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).AuxLe N
              (homotopySection f₀ hf₀.isScSmooth.1 S z) 1})

namespace IsProperOrientedHomotopy

variable {f₀ : X → Y} {hf₀ : B.IsScFredholmSectionTame f₀}
  {S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}

/-- `S` is a section of `π*P`. -/
theorem isSection (hH : B.IsProperOrientedHomotopy f₀ hf₀ S) :
    IsSection (pullbackProj P Prod.snd) S :=
  hH.isScPlusSection.1

/-- The slices `S(t, ·)` are sc⁺-sections of `P`. -/
theorem slice (hH : B.IsProperOrientedHomotopy f₀ hf₀ S) (t : Fin 1 → ℝ) :
    B.IsScPlusSection (pullbackSlice S t) := by
  have := paracompactSpace_rn_prod PX 1
  have := paracompactSpace_rn_pullback B 1
  exact hH.isScPlusSection.pullbackSlice t

/-- The end `S(1, ·)` is an sc⁺-section of `P`, so `f₁ = f₀ + S(1, ·)` is sc-Fredholm. -/
theorem slice_one (hH : B.IsProperOrientedHomotopy f₀ hf₀ S) :
    B.IsScPlusSection (pullbackSlice S 1) :=
  hH.slice 1

/-- **The end `f₁ = f₀ + S(1, ·)` is sc-Fredholm with tame germ data** (Theorem 3.1.18). -/
theorem isScFredholmSectionTame_one (hH : B.IsProperOrientedHomotopy f₀ hf₀ S) :
    B.IsScFredholmSectionTame (sectionAdd P f₀ (pullbackSlice S 1)) :=
  theorem_3_1_18_tame hf₀ hH.slice_one

/-- `F = f̃₀ + S` is a section of `π*P`. -/
theorem isSection_homotopySection (hH : B.IsProperOrientedHomotopy f₀ hf₀ S) :
    IsSection (pullbackProj P Prod.snd) (homotopySection f₀ hf₀.isScSmooth.1 S) :=
  (isSection_pullbackLift _).sectionAdd hH.isSection

/-- The slices of `F = f̃₀ + S` are `f₀ + S(t, ·)`. -/
theorem pullbackSlice_homotopySection (hH : B.IsProperOrientedHomotopy f₀ hf₀ S)
    (t : Fin 1 → ℝ) :
    pullbackSlice (homotopySection f₀ hf₀.isScSmooth.1 S) t =
      sectionAdd P f₀ (pullbackSlice S t) :=
  pullbackSlice_sectionAdd_paramLift hf₀.isScSmooth.1 hH.isSection t

/-- The zeros of `F` over the slab: the solution sets of `f₀ + S(t, ·)`, `t ∈ [0, 1]`, are
compact. -/
theorem isCompact_solutionSet_slice (hH : B.IsProperOrientedHomotopy f₀ hf₀ S)
    {t : Fin 1 → ℝ} (ht : t 0 ∈ Icc (0 : ℝ) 1) :
    IsCompact (solutionSet P (sectionAdd P f₀ (pullbackSlice S t))) := by
  rw [← hH.pullbackSlice_homotopySection t]
  exact isCompact_solutionSet_pullbackSlice hH.isSection_homotopySection hH.isCompact_slab ht

/-- **The sections `f₀ + S(t, ·)`, `t ∈ [0, 1]`, are proper** (Definition 5.2.1 (3); Theorem 5.2.2
from the compactness of the solution sets). -/
theorem isProper_slice (hH : B.IsProperOrientedHomotopy f₀ hf₀ S) {t : Fin 1 → ℝ}
    (ht : t 0 ∈ Icc (0 : ℝ) 1) : B.IsProper (sectionAdd P f₀ (pullbackSlice S t)) :=
  theorem_5_2_2_preprint (theorem_3_1_18_preprint hf₀.toIsScFredholmSection (hH.slice t))
    (hH.isCompact_solutionSet_slice ht)

/-- `S_{f₁}` is compact, `f₁ = f₀ + S(1, ·)`. -/
theorem isCompact_solutionSet_one (hH : B.IsProperOrientedHomotopy f₀ hf₀ S) :
    IsCompact (solutionSet P (sectionAdd P f₀ (pullbackSlice S 1))) :=
  hH.isCompact_solutionSet_slice (t := 1) ⟨zero_le_one, le_rfl⟩

/-- **The end `f₁ = f₀ + S(1, ·)` of a proper homotopy is proper** (Definition 5.2.1 (3)). -/
theorem isProper_one (hH : B.IsProperOrientedHomotopy f₀ hf₀ S) :
    B.IsProper (sectionAdd P f₀ (pullbackSlice S 1)) :=
  hH.isProper_slice (t := 1) ⟨zero_le_one, le_rfl⟩

/-- `S_{f₀}` is compact. -/
theorem isCompact_solutionSet_zero (hH : B.IsProperOrientedHomotopy f₀ hf₀ S) :
    IsCompact (solutionSet P f₀) := by
  have h := hH.isCompact_solutionSet_slice (t := 0) ⟨le_rfl, zero_le_one⟩
  rwa [hH.slice_zero, sectionAdd_fiberZero hf₀.isScSmooth.1] at h

/-- **The start `f₀` of a proper homotopy is proper.** -/
theorem isProper_zero (hH : B.IsProperOrientedHomotopy f₀ hf₀ S) : B.IsProper f₀ :=
  theorem_5_2_2_preprint hf₀.toIsScFredholmSection hH.isCompact_solutionSet_zero

/-- **Slab-adapted neighbourhoods** (the properness clause for the pulled-back norm `N/C`): for an
auxiliary norm `N` of `P` and `C > 0` there is an open `W ⊆ ℝ¹ × X` containing the zeros of
`F = f̃₀ + S` over the slab `t ∈ [0, 1]` with `cl{z ∈ W | t ∈ [0, 1], N(F(z)) ≤ C}` compact. -/
theorem exists_slab_nbhd (hH : B.IsProperOrientedHomotopy f₀ hf₀ S) {N : B.One → ℝ}
    (hN : B.IsAuxNorm N) {C : ℝ} (hC : 0 < C) :
    ∃ W : Set ((Fin 1 → ℝ) × X), IsOpen W ∧
      slabZeros (homotopySection f₀ hf₀.isScSmooth.1 S) 0 1 ⊆ W ∧
      IsCompact (closure {z ∈ W | z.1 0 ∈ Icc (0 : ℝ) 1 ∧
        B.AuxLe N (pullbackSlice (homotopySection f₀ hf₀.isScSmooth.1 S) z.1 z.2) C}) := by
  have := paracompactSpace_rn_prod PX 1
  have := paracompactSpace_rn_pullback B 1
  have hπ := MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX
  have hN' := (hN.const_mul (inv_pos.2 hC)).pullback hπ
  obtain ⟨W, hWo, hSW, hWc⟩ := hH.proper _ hN'
  refine ⟨W, hWo, hSW, hWc.of_isClosed_subset isClosed_closure (closure_mono ?_)⟩
  rintro z ⟨hzW, ht, hzN⟩
  refine ⟨hzW, ht, ?_⟩
  rw [StrongBundle.auxLe_pullbackAuxNorm_iff, StrongBundle.auxLe_const_mul_iff (inv_pos.2 hC),
    div_inv_eq_mul, one_mul]
  exact hzN

end IsProperOrientedHomotopy

end StrongBundle

open StrongBundle

/-- **The properness clause is automatic** (the analogue of Theorem 5.2.2, 2021 p. 210, on the
slab): an sc⁺-section `S` of `π*P → ℝ¹ × X` with `S(0, ·) = 0` whose homotopy `F = f̃₀ + S` has
compact zeros over the slab `t ∈ [0, 1]` is a proper homotopy (`F` is sc-Fredholm,
`exists_isOpen_isCompact_closure_auxLe` with `K` the zeros over the slab). -/
theorem isProperOrientedHomotopy_of_isCompact {f₀ : X → Y} (hf₀ : B.IsScFredholmSectionTame f₀)
    {S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
    (hS : haveI := paracompactSpace_rn_prod PX 1
      haveI := paracompactSpace_rn_pullback B 1
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection S)
    (h0 : pullbackSlice S 0 = fiberZero P)
    (hK : IsCompact (slabZeros (homotopySection f₀ hf₀.isScSmooth.1 S) 0 1)) :
    B.IsProperOrientedHomotopy f₀ hf₀ S := by
  have := paracompactSpace_rn_prod PX 1
  have := paracompactSpace_rn_pullback B 1
  refine ⟨hS, h0, hK, fun N hN => ?_⟩
  have hF := theorem_3_1_18_preprint hf₀.toIsScFredholmSection.param hS
  obtain ⟨W, hWo, hKW, hWc⟩ := exists_isOpen_isCompact_closure_auxLe hF hK (fun z hz => hz.1) hN
  exact ⟨W, hWo, hKW,
    hWc.of_isClosed_subset isClosed_closure (closure_mono fun z hz => ⟨hz.1, hz.2.2⟩)⟩

/-- **The constant homotopy `S = 0` is a proper homotopy** from a proper `f₀` to `f₀ + 0` (the
hypotheses of `IsProperOrientedHomotopy` are satisfiable): the zeros of `f̃₀` over the slab are
`[0, 1] × S_{f₀}`. -/
theorem witness_isProperOrientedHomotopy {f₀ : X → Y} (hf₀ : B.IsScFredholmSectionTame f₀)
    (hP : B.IsProper f₀) :
    B.IsProperOrientedHomotopy f₀ hf₀ (fiberZero (pullbackProj P Prod.snd)) := by
  have := paracompactSpace_rn_prod PX 1
  have := paracompactSpace_rn_pullback B 1
  have hfs : IsSection P f₀ := hf₀.isScSmooth.1
  have hL : IsSection (pullbackProj P Prod.snd) (paramLift (n := 1) f₀ hfs) :=
    isSection_pullbackLift _
  have heq : homotopySection f₀ hfs (fiberZero (pullbackProj P Prod.snd)) = paramLift f₀ hfs :=
    sectionAdd_fiberZero hL
  refine isProperOrientedHomotopy_of_isCompact hf₀ StrongBundle.isScPlusSection_fiberZero
    (funext fun _ => rfl) ?_
  have hcl : IsClosed (solutionSet (pullbackProj P Prod.snd)
      (homotopySection f₀ hfs (fiberZero (pullbackProj P Prod.snd)))) :=
    isClosed_solutionSet (theorem_3_1_18_tame hf₀.param
      StrongBundle.isScPlusSection_fiberZero).isScSmooth
  refine isCompact_slabZeros_of_subset hcl hP.1 fun z hz => ?_
  have h1 := hz.1
  change IsZeroAt (pullbackProj P Prod.snd)
    (homotopySection f₀ hfs (fiberZero (pullbackProj P Prod.snd))) (z.1, z.2) at h1
  rw [heq] at h1
  exact (isZeroAt_pullback_iff_pullbackSlice hL z.1 z.2).1 h1

/-- **A proper oriented homotopy between `(f₀, o₀)` and `(f₁, o₁)`** (2021 Theorem 6.7.1 (2),
p. 277, in reading R-d): a proper homotopy `S` from `f₀` (`IsProperOrientedHomotopy`) ending at
`f₁ = f₀ + S(1, ·)`, and `o₁` the orientation of `f₁` induced by `o₀`
(`SectionOrientation.sectionAdd`, Theorem 6.6.18, last paragraph, p. 276). -/
def IsProperOrientedHomotopyBetween {f₀ : X → Y} (hf₀ : B.IsScFredholmSectionTame f₀)
    (o₀ : SectionOrientation f₀ hf₀.toIsScFredholmSection)
    (S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))
    {h₁ : B.IsScFredholmSection (sectionAdd P f₀ (pullbackSlice S 1))}
    (o₁ : SectionOrientation (sectionAdd P f₀ (pullbackSlice S 1)) h₁) : Prop :=
  ∃ hH : B.IsProperOrientedHomotopy f₀ hf₀ S, o₁ = o₀.sectionAdd hH.slice_one

/-- **Proper oriented homotopies exist**: `S = 0` with `o₁ = o₀.sectionAdd` (for a proper `f₀`). -/
theorem witness_isProperOrientedHomotopyBetween {f₀ : X → Y} (hf₀ : B.IsScFredholmSectionTame f₀)
    (hP : B.IsProper f₀) (o₀ : SectionOrientation f₀ hf₀.toIsScFredholmSection) :
    IsProperOrientedHomotopyBetween hf₀ o₀ (fiberZero (pullbackProj P Prod.snd))
      (o₀.sectionAdd (witness_isProperOrientedHomotopy hf₀ hP).slice_one) :=
  ⟨witness_isProperOrientedHomotopy hf₀ hP, rfl⟩

end Homotopy

/-! ### Cobordism data over `ℝ¹ × X`, shared by parts (1) and (2) -/

section CobordismData

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

namespace StrongBundle

variable (B) in
/-- **The data of a cobordism over `ℝ¹ × X`** (the section `F(x, t) = f(x) + s_t(x)` of the proof
of 2021 Theorem 6.7.1, p. 278, Remark 5.3.8, in reading D2: `ℝ¹ × X` in place of `[0, 1] × X`,
stationary near the ends): an sc⁺-section `Ŝ` of `π*P → ℝ¹ × X` with `Ŝ(t, ·) = σ₀` for
`t ≤ 1/8` and `Ŝ(t, ·) = σ₁` for `t ≥ 7/8`, the ends `f + σᵢ` in general position at every zero,
`F = f̃ + Ŝ` in general position at every zero, and the zeros of `F` over every `[a, b]` compact.
Part (1) uses it with `σᵢ = sᵢ` (`exists_isCobordismData`), part (2) with `f = f₀`, `σ₀ = s₀`,
`σ₁ = S(1, ·) + s₁` (`exists_homotopy_cobordism`). -/
structure IsCobordismData (f : X → Y) (hf : IsSection P f) (σ₀ σ₁ : X → Y)
    (Ŝ : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)) : Prop where
  isScPlusSection :
    haveI := paracompactSpace_rn_prod PX 1
    haveI := paracompactSpace_rn_pullback B 1
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection Ŝ
  slice_le : ∀ t : Fin 1 → ℝ, t 0 ≤ 1 / 8 → pullbackSlice Ŝ t = σ₀
  slice_ge : ∀ t : Fin 1 → ℝ, 7 / 8 ≤ t 0 → pullbackSlice Ŝ t = σ₁
  gp_left : ∀ x, IsZeroAt P (sectionAdd P f σ₀) x → B.IsGeneralPositionGerm (sectionAdd P f σ₀) x
  gp_right : ∀ x, IsZeroAt P (sectionAdd P f σ₁) x →
    B.IsGeneralPositionGerm (sectionAdd P f σ₁) x
  gp :
    haveI := paracompactSpace_rn_prod PX 1
    haveI := paracompactSpace_rn_pullback B 1
    ∀ z, IsZeroAt (pullbackProj P Prod.snd) (homotopySection f hf Ŝ) z →
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsGeneralPositionGerm
        (homotopySection f hf Ŝ) z
  isCompact_slab : ∀ a b : ℝ, IsCompact (slabZeros (homotopySection f hf Ŝ) a b)

namespace IsCobordismData

variable {f : X → Y} {hf : IsSection P f} {σ₀ σ₁ : X → Y}
  {Ŝ : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}

theorem isSection (hC : B.IsCobordismData f hf σ₀ σ₁ Ŝ) :
    IsSection (pullbackProj P Prod.snd) Ŝ :=
  hC.isScPlusSection.1

/-- The end `σ₀` is an sc⁺-section. -/
theorem isScPlusSection_left (hC : B.IsCobordismData f hf σ₀ σ₁ Ŝ) : B.IsScPlusSection σ₀ := by
  have := paracompactSpace_rn_prod PX 1
  have := paracompactSpace_rn_pullback B 1
  rw [← hC.slice_le (fun _ => 0) (by norm_num)]
  exact hC.isScPlusSection.pullbackSlice _

/-- The end `σ₁` is an sc⁺-section. -/
theorem isScPlusSection_right (hC : B.IsCobordismData f hf σ₀ σ₁ Ŝ) : B.IsScPlusSection σ₁ := by
  have := paracompactSpace_rn_prod PX 1
  have := paracompactSpace_rn_pullback B 1
  rw [← hC.slice_ge (fun _ => 1) (by norm_num)]
  exact hC.isScPlusSection.pullbackSlice _

/-- `F = f̃ + Ŝ` is `f + σ₀` for `t ≤ 1/8`. -/
theorem pullbackSlice_le (hC : B.IsCobordismData f hf σ₀ σ₁ Ŝ) {t : Fin 1 → ℝ}
    (ht : t 0 ≤ 1 / 8) :
    pullbackSlice (homotopySection f hf Ŝ) t = sectionAdd P f σ₀ := by
  rw [pullbackSlice_sectionAdd_paramLift hf hC.isSection, hC.slice_le t ht]

/-- `F = f̃ + Ŝ` is `f + σ₁` for `t ≥ 7/8`. -/
theorem pullbackSlice_ge (hC : B.IsCobordismData f hf σ₀ σ₁ Ŝ) {t : Fin 1 → ℝ}
    (ht : 7 / 8 ≤ t 0) :
    pullbackSlice (homotopySection f hf Ŝ) t = sectionAdd P f σ₁ := by
  rw [pullbackSlice_sectionAdd_paramLift hf hC.isSection, hC.slice_ge t ht]

/-- `F = (f + σ₀)~` over `t ≤ 1/8`. -/
theorem eq_paramLift_left (hC : B.IsCobordismData f hf σ₀ σ₁ Ŝ) {z : (Fin 1 → ℝ) × X}
    (hz : z.1 0 ≤ 1 / 8) :
    homotopySection f hf Ŝ z =
      paramLift (sectionAdd P f σ₀) (hf.sectionAdd hC.isScPlusSection_left.1) z :=
  eq_paramLift_of_pullbackSlice ((isSection_pullbackLift _).sectionAdd hC.isSection) _
    (by rw [hC.pullbackSlice_le hz])

/-- `F = (f + σ₁)~` over `t ≥ 7/8`. -/
theorem eq_paramLift_right (hC : B.IsCobordismData f hf σ₀ σ₁ Ŝ) {z : (Fin 1 → ℝ) × X}
    (hz : 7 / 8 ≤ z.1 0) :
    homotopySection f hf Ŝ z =
      paramLift (sectionAdd P f σ₁) (hf.sectionAdd hC.isScPlusSection_right.1) z :=
  eq_paramLift_of_pullbackSlice ((isSection_pullbackLift _).sectionAdd hC.isSection) _
    (by rw [hC.pullbackSlice_ge hz])

/-- The ends `S_{f+σ₀}` and `S_{f+σ₁}` are compact. -/
theorem isCompact_solutionSet_left (hC : B.IsCobordismData f hf σ₀ σ₁ Ŝ) :
    IsCompact (solutionSet P (sectionAdd P f σ₀)) := by
  rw [← hC.pullbackSlice_le (t := fun _ => 0) (by norm_num)]
  exact isCompact_solutionSet_pullbackSlice ((isSection_pullbackLift _).sectionAdd hC.isSection)
    (hC.isCompact_slab 0 0) ⟨le_rfl, le_rfl⟩

theorem isCompact_solutionSet_right (hC : B.IsCobordismData f hf σ₀ σ₁ Ŝ) :
    IsCompact (solutionSet P (sectionAdd P f σ₁)) := by
  rw [← hC.pullbackSlice_ge (t := fun _ => 1) (by norm_num)]
  exact isCompact_solutionSet_pullbackSlice ((isSection_pullbackLift _).sectionAdd hC.isSection)
    (hC.isCompact_slab 1 1) ⟨le_rfl, le_rfl⟩

end IsCobordismData

end StrongBundle

open StrongBundle

/-- **Part (1): the cobordism between two admissible sections gives cobordism data** (2021
Remark 5.3.8 and the proof of Theorem 6.7.1 (1), p. 278): `exists_cobordism` in the form
`IsCobordismData f s₀ s₁`. -/
theorem exists_isCobordismData (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions) {f : X → Y}
    (hf : B.IsScFredholmSectionTame f) {N : B.One → ℝ} (hN : B.IsAuxNorm N) {U : Set X}
    (hU : IsOpen U) (hSU : solutionSet P f ⊆ U)
    (hcpt : IsCompact (closure {x ∈ U | B.AuxLe N (f x) 2})) {s₀ s₁ : X → Y}
    (hs₀ : s₀ ∈ B.allowableSections N U) (hs₁ : s₁ ∈ B.allowableSections N U)
    (hgp₀ : ∀ x, IsZeroAt P (sectionAdd P f s₀) x →
      B.IsGeneralPositionGerm (sectionAdd P f s₀) x)
    (hgp₁ : ∀ x, IsZeroAt P (sectionAdd P f s₁) x →
      B.IsGeneralPositionGerm (sectionAdd P f s₁) x) :
    ∃ Ŝ : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X),
      B.IsCobordismData f hf.isScSmooth.1 s₀ s₁ Ŝ := by
  have := paracompactSpace_rn_prod PX 1
  have := paracompactSpace_rn_pullback B 1
  obtain ⟨Ŝ, hŜ, h0, h1, -, -, hgp, hK⟩ :=
    exists_cobordism hX hbump hf hN hU hSU hcpt hs₀ hs₁ hgp₀ hgp₁
  exact ⟨Ŝ, hŜ, h0, h1, hgp₀, hgp₁, hgp, hK⟩

end CobordismData

/-! ### The cut-offs of the homotopy cobordism -/

section HomCutoff

/-- The weight of `s₀` in the homotopy cobordism: `1` for `t ≤ 3/16`, `0` for `t ≥ 5/16`. -/
def homWeightZero (t : ℝ) : ℝ := 1 - Real.smoothTransition ((t - 3 / 16) * 8)

/-- The time change of the homotopy: `0` for `t ≤ 3/8`, `1` for `t ≥ 5/8`. -/
def homTime (t : ℝ) : ℝ := Real.smoothTransition ((t - 3 / 8) * 4)

/-- The weight of `s₁` in the homotopy cobordism: `0` for `t ≤ 11/16`, `1` for `t ≥ 13/16`. -/
def homWeightOne (t : ℝ) : ℝ := Real.smoothTransition ((t - 11 / 16) * 8)

lemma contDiff_homWeightZero : ContDiff ℝ ∞ homWeightZero :=
  contDiff_const.sub
    (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).mul contDiff_const))

lemma contDiff_homTime : ContDiff ℝ ∞ homTime :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).mul contDiff_const)

lemma contDiff_homWeightOne : ContDiff ℝ ∞ homWeightOne :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).mul contDiff_const)

lemma homWeightZero_of_le {t : ℝ} (ht : t ≤ 3 / 16) : homWeightZero t = 1 := by
  rw [homWeightZero, Real.smoothTransition.zero_of_nonpos (by linarith), sub_zero]

lemma homWeightZero_of_ge {t : ℝ} (ht : 5 / 16 ≤ t) : homWeightZero t = 0 := by
  rw [homWeightZero, Real.smoothTransition.one_of_one_le (by linarith), sub_self]

lemma abs_homWeightZero_le (t : ℝ) : |homWeightZero t| ≤ 1 := by
  rw [abs_le]
  constructor <;> simp only [homWeightZero] <;>
    linarith [Real.smoothTransition.nonneg ((t - 3 / 16) * 8),
      Real.smoothTransition.le_one ((t - 3 / 16) * 8)]

lemma homTime_of_le {t : ℝ} (ht : t ≤ 3 / 8) : homTime t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma homTime_of_ge {t : ℝ} (ht : 5 / 8 ≤ t) : homTime t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma homTime_mem (t : ℝ) : homTime t ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

lemma homWeightOne_of_le {t : ℝ} (ht : t ≤ 11 / 16) : homWeightOne t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma homWeightOne_of_ge {t : ℝ} (ht : 13 / 16 ≤ t) : homWeightOne t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma abs_homWeightOne_le (t : ℝ) : |homWeightOne t| ≤ 1 := by
  rw [homWeightOne, abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

/-- The time change `r ↦ χ(r)` on `ℝ¹`. -/
def homReparam (r : Fin 1 → ℝ) : Fin 1 → ℝ := fun _ => homTime (r 0)

lemma contDiff_homReparam : ContDiff ℝ ∞ homReparam :=
  contDiff_pi.2 fun _ => contDiff_homTime.comp (contDiff_apply ℝ ℝ 0)

lemma homReparam_of_le {r : Fin 1 → ℝ} (hr : r 0 ≤ 3 / 8) : homReparam r = 0 :=
  funext fun _ => homTime_of_le hr

lemma homReparam_of_ge {r : Fin 1 → ℝ} (hr : 5 / 8 ≤ r 0) : homReparam r = 1 :=
  funext fun _ => homTime_of_ge hr

end HomCutoff

/-! ### The interpolation `w₀(t)·s₀ + w₁(t)·s₁` -/

section HomInterp

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

/-- **The interpolation `ŝ(t, x) = w₀(t)·s₀(x) + w₁(t)·s₁(x)`** of the homotopy cobordism: `s₀` is
switched off on `[3/16, 5/16]`, while the homotopy is still at `t = 0`, and `s₁` is switched on on
`[11/16, 13/16]`, when the homotopy has reached `t = 1`. -/
def homInterp (s₀ s₁ : X → Y) (h₀ : IsSection P s₀) (h₁ : IsSection P s₁) :
    (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X) :=
  sectionAdd (pullbackProj P Prod.snd)
    (sectionSmul (pullbackProj P Prod.snd) (fun z => homWeightZero (z.1 0)) (constLift s₀ h₀))
    (sectionSmul (pullbackProj P Prod.snd) (fun z => homWeightOne (z.1 0)) (constLift s₁ h₁))

variable {s₀ s₁ : X → Y} (h₀ : IsSection P s₀) (h₁ : IsSection P s₁)

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
lemma isSection_homInterp : IsSection (pullbackProj P Prod.snd) (homInterp s₀ s₁ h₀ h₁) :=
  ((isSection_constLift s₀ h₀).sectionSmul).sectionAdd (isSection_constLift s₁ h₁).sectionSmul

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
/-- The slices of `ŝ`: `ŝ(t, ·) = w₀(t)·s₀ + w₁(t)·s₁`. -/
lemma pullbackSlice_homInterp (t : Fin 1 → ℝ) :
    pullbackSlice (homInterp s₀ s₁ h₀ h₁) t =
      sectionAdd P (sectionSmul P (fun _ => homWeightZero (t 0)) s₀)
        (sectionSmul P (fun _ => homWeightOne (t 0)) s₁) := by
  rw [homInterp, pullbackSlice_sectionAdd (isSection_constLift s₀ h₀).sectionSmul
      (isSection_constLift s₁ h₁).sectionSmul,
    pullbackSlice_sectionSmul (isSection_constLift s₀ h₀),
    pullbackSlice_sectionSmul (isSection_constLift s₁ h₁), pullbackSlice_constLift,
    pullbackSlice_constLift]

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
lemma pullbackSlice_homInterp_apply (t : Fin 1 → ℝ) (x : X) :
    pullbackSlice (homInterp s₀ s₁ h₀ h₁) t x =
      ((homWeightZero (t 0) • (⟨s₀ x, h₀ x⟩ : P ⁻¹' {x}) +
        homWeightOne (t 0) • ⟨s₁ x, h₁ x⟩ : P ⁻¹' {x}) : Y) := by
  rw [pullbackSlice_homInterp, sectionAdd_sectionSmul_apply h₀ h₁]

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
/-- `ŝ(t, ·) = s₀` for `t ≤ 3/16`. -/
lemma pullbackSlice_homInterp_of_le {t : Fin 1 → ℝ} (ht : t 0 ≤ 3 / 16) :
    pullbackSlice (homInterp s₀ s₁ h₀ h₁) t = s₀ := by
  funext x
  rw [pullbackSlice_homInterp_apply, homWeightZero_of_le ht, homWeightOne_of_le (by linarith)]
  simp

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
/-- `ŝ(t, ·) = s₁` for `t ≥ 13/16`. -/
lemma pullbackSlice_homInterp_of_ge {t : Fin 1 → ℝ} (ht : 13 / 16 ≤ t 0) :
    pullbackSlice (homInterp s₀ s₁ h₀ h₁) t = s₁ := by
  funext x
  rw [pullbackSlice_homInterp_apply, homWeightZero_of_ge (by linarith), homWeightOne_of_ge ht]
  simp

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] in
/-- `ŝ(t, x) = 0` when each term vanishes (its weight or its section). -/
lemma isZeroAt_pullbackSlice_homInterp {t : Fin 1 → ℝ} {x : X}
    (hx₀ : homWeightZero (t 0) = 0 ∨ IsZeroAt P s₀ x)
    (hx₁ : homWeightOne (t 0) = 0 ∨ IsZeroAt P s₁ x) :
    IsZeroAt P (pullbackSlice (homInterp s₀ s₁ h₀ h₁) t) x := by
  have e₀ : homWeightZero (t 0) • (⟨s₀ x, h₀ x⟩ : P ⁻¹' {x}) = 0 := by
    rcases hx₀ with h | h
    · rw [h, zero_smul]
    · rw [show (⟨s₀ x, h₀ x⟩ : P ⁻¹' {x}) = 0 from Subtype.ext h, smul_zero]
  have e₁ : homWeightOne (t 0) • (⟨s₁ x, h₁ x⟩ : P ⁻¹' {x}) = 0 := by
    rcases hx₁ with h | h
    · rw [h, zero_smul]
    · rw [show (⟨s₁ x, h₁ x⟩ : P ⁻¹' {x}) = 0 from Subtype.ext h, smul_zero]
  unfold IsZeroAt
  rw [pullbackSlice_homInterp_apply, e₀, e₁, add_zero]
  rfl

/-- `N(ŝ(t, x)) ≤ 1` when `N(s₀(x)), N(s₁(x)) ≤ 1`: at each `t` one of the weights vanishes. -/
lemma auxLe_pullbackSlice_homInterp {N : B.One → ℝ} (hN : B.IsAuxNorm N) {x : X}
    (hx₀ : B.AuxLe N (s₀ x) 1) (hx₁ : B.AuxLe N (s₁ x) 1) (t : Fin 1 → ℝ) :
    B.AuxLe N (pullbackSlice (homInterp s₀ s₁ h₀ h₁) t x) 1 := by
  rw [pullbackSlice_homInterp]
  refine (hN.auxLe_sectionAdd h₀.sectionSmul h₁.sectionSmul (hN.auxLe_sectionSmul h₀ _ hx₀)
    (hN.auxLe_sectionSmul h₁ _ hx₁)).mono ?_
  show |homWeightZero (t 0)| * 1 + |homWeightOne (t 0)| * 1 ≤ 1
  rcases le_total (t 0) (11 / 16) with ht | ht
  · rw [homWeightOne_of_le ht, abs_zero]
    linarith [abs_homWeightZero_le (t 0)]
  · rw [homWeightZero_of_ge (by linarith), abs_zero]
    linarith [abs_homWeightOne_le (t 0)]

variable [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))]

/-- `ŝ` is an sc⁺-section of `π*P` for sc⁺-sections `s₀`, `s₁`. -/
theorem isScPlusSection_homInterp {s₀ s₁ : X → Y} (h₀ : B.IsScPlusSection s₀)
    (h₁ : B.IsScPlusSection s₁) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection
      (homInterp s₀ s₁ h₀.1 h₁.1) :=
  ((isScPlusSection_constLift h₀).smul_left (isScSmoothMap_of_contDiff_fst
      (g := fun r => homWeightZero (r 0)) (contDiff_homWeightZero.comp (contDiff_apply ℝ ℝ 0)))).add
    ((isScPlusSection_constLift h₁).smul_left (isScSmoothMap_of_contDiff_fst
      (g := fun r => homWeightOne (r 0)) (contDiff_homWeightOne.comp (contDiff_apply ℝ ℝ 0))))

end HomInterp

/-! ### Part (2): the cobordism of a proper homotopy -/

section HomotopyCobordism

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

open StrongBundle

/-- **The cobordism of a proper homotopy** (the proof of 2021 Theorem 6.7.1 (2), p. 279: "the
same homotopy argument as in (1)"; preprint Theorem 6.43): let `X` be tame with sc-smooth bump
functions, `S` a proper homotopy from `f₀` to `f₁ = f₀ + S(1, ·)` (`IsProperOrientedHomotopy`), `N`
an auxiliary norm, and `W` a slab-adapted neighbourhood (`IsProperOrientedHomotopy.exists_slab_nbhd`
with `C = 2`). Let `s₀` be admissible for `(N, U₀)` and `f₀`, and `s₁` admissible for `(N, U₁)`
and `f₁`, with `{0} × U₀ ⊆ W` and `{1} × U₁ ⊆ W`. Then there is an sc⁺-section `Ŝ` of `π*P` over
`ℝ¹ × X` with `IsCobordismData f₀ s₀ (S(1, ·) + s₁) Ŝ`: `f̃₀ + Ŝ` is `f₀ + s₀` for `t ≤ 1/8` and
`f₁ + s₁` for `t ≥ 7/8`, it is in general position at every zero, and its zeros over every
`[a, b]` form a compact set.
*Proof*: `Ŝ = S ∘ (χ × 1) + w₀·s̃₀ + w₁·s̃₁ + p`, with the time change `χ` (`0` for `t ≤ 3/8`, `1`
for `t ≥ 5/8`), `s₀` switched off before and `s₁` switched on after the homotopy moves, and `p`
from `theorem_5_3_10_relative_hyp` with `W' = (1/8, 7/8) × χ⁻¹(W)`. The zeros lie over
`pr_X cl{w ∈ W | t ∈ [0, 1], N(F(w)) ≤ 2}`, which is compact. Hypotheses beyond the text: the
slab-adapted `W` and the supports of `s₀`, `s₁` in its ends; they can be met inside any given
neighbourhoods of `S_{f₀}`, `S_{f₁}` (`exists_homotopy_cobordism_data`). -/
theorem exists_homotopy_cobordism (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    {f₀ : X → Y} {hf₀ : B.IsScFredholmSectionTame f₀}
    {S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
    (hH : B.IsProperOrientedHomotopy f₀ hf₀ S) {N : B.One → ℝ} (hN : B.IsAuxNorm N)
    {W : Set ((Fin 1 → ℝ) × X)} (hW : IsOpen W)
    (hWS : slabZeros (homotopySection f₀ hf₀.isScSmooth.1 S) 0 1 ⊆ W)
    (hWc : IsCompact (closure {w ∈ W | w.1 0 ∈ Icc (0 : ℝ) 1 ∧
      B.AuxLe N (pullbackSlice (homotopySection f₀ hf₀.isScSmooth.1 S) w.1 w.2) 2}))
    {U₀ U₁ : Set X} (hU₀ : ∀ x ∈ U₀, ((0 : Fin 1 → ℝ), x) ∈ W)
    (hU₁ : ∀ x ∈ U₁, ((1 : Fin 1 → ℝ), x) ∈ W) {s₀ s₁ : X → Y}
    (hs₀ : s₀ ∈ B.allowableSections N U₀)
    (hgp₀ : ∀ x, IsZeroAt P (sectionAdd P f₀ s₀) x →
      B.IsGeneralPositionGerm (sectionAdd P f₀ s₀) x)
    (hs₁ : s₁ ∈ B.allowableSections N U₁)
    (hgp₁ : ∀ x, IsZeroAt P (sectionAdd P (sectionAdd P f₀ (pullbackSlice S 1)) s₁) x →
      B.IsGeneralPositionGerm (sectionAdd P (sectionAdd P f₀ (pullbackSlice S 1)) s₁) x) :
    ∃ Ŝ : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X),
      B.IsCobordismData f₀ hf₀.isScSmooth.1 s₀ (sectionAdd P (pullbackSlice S 1) s₁) Ŝ ∧
      (∀ t : Fin 1 → ℝ, t 0 ≤ 1 / 8 →
        pullbackSlice (homotopySection f₀ hf₀.isScSmooth.1 Ŝ) t = sectionAdd P f₀ s₀) ∧
      ∀ t : Fin 1 → ℝ, 7 / 8 ≤ t 0 →
        pullbackSlice (homotopySection f₀ hf₀.isScSmooth.1 Ŝ) t =
          sectionAdd P (sectionAdd P f₀ (pullbackSlice S 1)) s₁ := by
  have := paracompactSpace_rn_prod PX 1
  have := paracompactSpace_rn_pullback B 1
  have hfs : IsSection P f₀ := hf₀.isScSmooth.1
  obtain ⟨hs₀p, hs₀U, hs₀N⟩ := hs₀
  obtain ⟨hs₁p, hs₁U, hs₁N⟩ := hs₁
  have hs₀N' : ∀ x, B.AuxLe N (s₀ x) 1 := fun x => ⟨hs₀p.mem_oneSet x, hs₀N x _⟩
  have hs₁N' : ∀ x, B.AuxLe N (s₁ x) 1 := fun x => ⟨hs₁p.mem_oneSet x, hs₁N x _⟩
  have hSp : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection S :=
    hH.isScPlusSection
  have hL : IsSection (pullbackProj P Prod.snd) (paramLift (n := 1) f₀ hfs) :=
    isSection_pullbackLift _
  -- the homotopy `H = f̃₀ + S`, its time change `T = S ∘ (χ × 1)`, the interpolation `ŝ`
  set H := homotopySection f₀ hfs S with hHdef
  have hHs : IsSection (pullbackProj P Prod.snd) H := hL.sectionAdd hSp.1
  set T := reparamSection homReparam S hSp.1 with hTdef
  have hT := hSp.reparamSmooth contDiff_homReparam
  set ŝ := homInterp s₀ s₁ hs₀p.1 hs₁p.1 with hŝdef
  have hŝ := isScPlusSection_homInterp (B := B) hs₀p hs₁p
  set Ŝ₁ := sectionAdd (pullbackProj P Prod.snd) T ŝ with hŜ₁def
  have hŜ₁ := hT.add hŝ
  set G := homotopySection f₀ hfs Ŝ₁ with hGdef
  have hGs : IsSection (pullbackProj P Prod.snd) G := hL.sectionAdd hŜ₁.1
  -- the end `σ₁ = S(1, ·) + s₁`
  set σ₁ := sectionAdd P (pullbackSlice S 1) s₁ with hσ₁def
  have hσ₁ : B.IsScPlusSection σ₁ := hH.slice_one.add hs₁p
  have hgpσ₁ : ∀ x, IsZeroAt P (sectionAdd P f₀ σ₁) x →
      B.IsGeneralPositionGerm (sectionAdd P f₀ σ₁) x := by
    rw [hσ₁def, ← sectionAdd_assoc hfs hH.slice_one.1 hs₁p.1]
    exact hgp₁
  -- the slices of `Ŝ₁` near the ends
  have hŜ₁_le : ∀ t : Fin 1 → ℝ, t 0 ≤ 3 / 16 → pullbackSlice Ŝ₁ t = s₀ := by
    intro t ht
    rw [pullbackSlice_sectionAdd hT.1 hŝ.1, pullbackSlice_reparamSection,
      homReparam_of_le (by linarith), hH.slice_zero,
      pullbackSlice_homInterp_of_le hs₀p.1 hs₁p.1 ht, fiberZero_sectionAdd hs₀p.1]
  have hŜ₁_ge : ∀ t : Fin 1 → ℝ, 13 / 16 ≤ t 0 → pullbackSlice Ŝ₁ t = σ₁ := by
    intro t ht
    rw [pullbackSlice_sectionAdd hT.1 hŝ.1, pullbackSlice_reparamSection,
      homReparam_of_ge (by linarith), pullbackSlice_homInterp_of_ge hs₀p.1 hs₁p.1 ht]
  -- `G(t, ·) = H(χ(t), ·) + ŝ(t, ·)`
  have hGslice : ∀ t : Fin 1 → ℝ, pullbackSlice G t =
      sectionAdd P (pullbackSlice H (homReparam t)) (pullbackSlice ŝ t) := by
    intro t
    rw [pullbackSlice_sectionAdd_paramLift hfs hŜ₁.1, pullbackSlice_sectionAdd hT.1 hŝ.1,
      ← sectionAdd_assoc hfs (hT.1.pullbackSlice t) (hŝ.1.pullbackSlice t),
      pullbackSlice_sectionAdd_paramLift hfs hSp.1]
    rfl
  -- the zeros of `G` lie over `W` after the time change
  have hGW : ∀ z : (Fin 1 → ℝ) × X, IsZeroAt (pullbackProj P Prod.snd) G z →
      (homReparam z.1, z.2) ∈ W := by
    rintro ⟨t, x⟩ hz
    change (homReparam t, x) ∈ W
    have hz' := (isZeroAt_pullback_iff_pullbackSlice hGs t x).1 hz
    rw [hGslice] at hz'
    by_cases h₀ : x ∈ U₀ ∧ t 0 ≤ 5 / 16
    · rw [homReparam_of_le (by linarith [h₀.2])]
      exact hU₀ x h₀.1
    by_cases h₁ : x ∈ U₁ ∧ 11 / 16 ≤ t 0
    · rw [homReparam_of_ge (by linarith [h₁.2])]
      exact hU₁ x h₁.1
    have hŝ0 : IsZeroAt P (pullbackSlice ŝ t) x := by
      refine isZeroAt_pullbackSlice_homInterp hs₀p.1 hs₁p.1 ?_ ?_
      · by_cases ht : t 0 ≤ 5 / 16
        · exact Or.inr (isZeroAt_of_not_mem_of_support_subset hs₀U fun hx => h₀ ⟨hx, ht⟩)
        · exact Or.inl (homWeightZero_of_ge (by linarith))
      · by_cases ht : 11 / 16 ≤ t 0
        · exact Or.inr (isZeroAt_of_not_mem_of_support_subset hs₁U fun hx => h₁ ⟨hx, ht⟩)
        · exact Or.inl (homWeightOne_of_le (by linarith))
    have hH0 := isZeroAt_left_of_isZeroAt_sectionAdd (hHs.pullbackSlice _)
      (hŝ.1.pullbackSlice t) hz' hŝ0
    exact hWS ⟨(isZeroAt_pullback_iff_pullbackSlice hHs _ x).2 hH0, homTime_mem (t 0)⟩
  -- `N(H(χ(t), x)) ≤ N(G(t, x)) + 1`
  have hHbound : ∀ (z : (Fin 1 → ℝ) × X) (a : ℝ), B.AuxLe N (pullbackSlice G z.1 z.2) a →
      B.AuxLe N (pullbackSlice H (homReparam z.1) z.2) (a + 1) := by
    intro z a h
    rw [hGslice] at h
    exact hN.auxLe_of_sectionAdd_le (hHs.pullbackSlice _) (hŝ.1.pullbackSlice _) h
      (auxLe_pullbackSlice_homInterp hs₀p.1 hs₁p.1 hN (hs₀N' z.2) (hs₁N' z.2) z.1)
  -- the compact `K' = pr_X cl{w ∈ W | t ∈ [0, 1], N(H(w)) ≤ 2}`
  set K' := Prod.snd '' closure {w ∈ W | w.1 0 ∈ Icc (0 : ℝ) 1 ∧
    B.AuxLe N (pullbackSlice H w.1 w.2) 2} with hK'def
  have hK' : IsCompact K' := hWc.image continuous_snd
  have hmemK' : ∀ z : (Fin 1 → ℝ) × X, (homReparam z.1, z.2) ∈ W →
      B.AuxLe N (pullbackSlice H (homReparam z.1) z.2) 2 → z.2 ∈ K' := fun z hzW hzN =>
    ⟨(homReparam z.1, z.2), subset_closure ⟨hzW, homTime_mem _, hzN⟩, rfl⟩
  have hGK' : ∀ z, IsZeroAt (pullbackProj P Prod.snd) G z → z.2 ∈ K' := by
    intro z hz
    have hz' := (isZeroAt_pullback_iff_pullbackSlice hGs z.1 z.2).1 hz
    have h0 : B.AuxLe N (pullbackSlice G z.1 z.2) 0 :=
      (hN.auxLe_fiberZero z.2 le_rfl).congr hz'.symm
    exact hmemK' z (hGW z hz) ((hHbound z 0 h0).mono (by norm_num))
  have hGt := theorem_3_1_18_tame (hf₀.param (n := 1)) hŜ₁
  have hGcl : IsClosed (solutionSet (pullbackProj P Prod.snd) G) :=
    isClosed_solutionSet hGt.isScSmooth
  -- `K` the zeros of `G` over `[3/16, 13/16]`, `W' = (1/8, 7/8) × χ⁻¹(W)`
  set K := slabZeros G (3 / 16) (13 / 16) with hKdef
  have hK : IsCompact K := isCompact_slabZeros_of_subset hGcl hK' fun z hz => hGK' z hz.1
  have hΛ : Continuous fun z : (Fin 1 → ℝ) × X => (homReparam z.1, z.2) :=
    (contDiff_homReparam.continuous.comp continuous_fst).prodMk continuous_snd
  set W' : Set ((Fin 1 → ℝ) × X) :=
    {z | z.1 0 ∈ Ioo (1 / 8 : ℝ) (7 / 8) ∧ (homReparam z.1, z.2) ∈ W} with hW'def
  have hW'o : IsOpen W' :=
    (isOpen_Ioo.preimage continuous_fst_apply_zero).inter (hW.preimage hΛ)
  have hKW' : K ⊆ W' := fun z hz =>
    ⟨⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩, hGW z hz.1⟩
  -- off `K`, `G` is `(f₀ + s₀)~` or `(f₀ + σ₁)~` near its zeros
  have hgpK : ∀ z, IsZeroAt (pullbackProj P Prod.snd) G z → z ∉ K →
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsGeneralPositionGerm
        G z := by
    intro z hz hzK
    have ht : z.1 0 < 3 / 16 ∨ 13 / 16 < z.1 0 := by
      by_contra h
      simp only [not_or, not_lt] at h
      exact hzK ⟨hz, h⟩
    rcases ht with ht | ht
    · exact isGeneralPositionGerm_paramLift_add_of_eq hf₀ hŜ₁ hs₀p
        (isOpen_lt continuous_fst_apply_zero continuous_const)
        (fun w hw => congrFun (hŜ₁_le w.1 (le_of_lt (hw : w.1 0 < 3 / 16))) w.2) hgp₀ ht hz
    · exact isGeneralPositionGerm_paramLift_add_of_eq hf₀ hŜ₁ hσ₁
        (isOpen_lt continuous_const continuous_fst_apply_zero)
        (fun w hw => congrFun (hŜ₁_ge w.1 (le_of_lt (hw : 13 / 16 < w.1 0))) w.2) hgpσ₁ ht hz
  -- the compact `cl{z ∈ W' | N(G(z)) ≤ 1}`
  have hN₁ := hN.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)
  have hcpt₁ : IsCompact (closure {z ∈ W' |
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).AuxLe
        (B.pullbackAuxNorm (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX) N) (G z) 1}) := by
    refine ((isCompact_Icc (a := fun _ : Fin 1 => (1 / 8 : ℝ)) (b := fun _ => 7 / 8)).prod
      hK').of_isClosed_subset isClosed_closure (closure_minimal ?_
        (isClosed_Icc.prod hK'.isClosed))
    rintro z ⟨hzW, hzN⟩
    have h1 : B.AuxLe N (pullbackSlice G z.1 z.2) 1 :=
      (StrongBundle.auxLe_pullbackAuxNorm_iff _).1 hzN
    exact ⟨mem_Icc_of_apply_zero ⟨hzW.1.1.le, hzW.1.2.le⟩,
      hmemK' z hzW.2 ((hHbound z 1 h1).mono (by norm_num))⟩
  -- the perturbation `p`
  obtain ⟨p, hp, hpW, hpN, hgpp⟩ := theorem_5_3_10_relative_hyp (prod_rn_isTame hX)
    (MPolyfold.admitsBumpFunctions_prod_rn hbump) hGt hN₁ hW'o hK hKW' hgpK hcpt₁ one_pos
  have hpZ : ∀ z ∉ W', IsZeroAt P (pullbackSlice p z.1) z.2 := fun z hz =>
    (isZeroAt_pullback_iff_pullbackSlice hp.1 z.1 z.2).1
      (StrongBundle.isZeroAt_of_not_mem_of_support_subset hpW hz)
  have hpN' : ∀ z : (Fin 1 → ℝ) × X, B.AuxLe N (pullbackSlice p z.1 z.2) 1 := fun z =>
    (StrongBundle.auxLe_pullbackAuxNorm_iff _).1 (hpN z)
  have hp0 : ∀ t : Fin 1 → ℝ, t 0 ∉ Ioo (1 / 8 : ℝ) (7 / 8) →
      pullbackSlice p t = fiberZero P :=
    fun t ht => funext fun x => hpZ (t, x) fun h => ht h.1
  -- the final section `Ŝ = Ŝ₁ + p`
  have hslice : ∀ t, pullbackSlice (sectionAdd (pullbackProj P Prod.snd) Ŝ₁ p) t =
      sectionAdd P (pullbackSlice Ŝ₁ t) (pullbackSlice p t) := fun t =>
    pullbackSlice_sectionAdd hŜ₁.1 hp.1 t
  have hFeq : homotopySection f₀ hfs (sectionAdd (pullbackProj P Prod.snd) Ŝ₁ p) =
      sectionAdd (pullbackProj P Prod.snd) G p :=
    (sectionAdd_assoc hL hŜ₁.1 hp.1).symm
  have hle : ∀ t : Fin 1 → ℝ, t 0 ≤ 1 / 8 →
      pullbackSlice (sectionAdd (pullbackProj P Prod.snd) Ŝ₁ p) t = s₀ := by
    intro t ht
    rw [hslice, hp0 t fun h => by linarith [h.1], sectionAdd_fiberZero (hŜ₁.1.pullbackSlice t),
      hŜ₁_le t (by linarith)]
  have hge : ∀ t : Fin 1 → ℝ, 7 / 8 ≤ t 0 →
      pullbackSlice (sectionAdd (pullbackProj P Prod.snd) Ŝ₁ p) t = σ₁ := by
    intro t ht
    rw [hslice, hp0 t fun h => by linarith [h.2], sectionAdd_fiberZero (hŜ₁.1.pullbackSlice t),
      hŜ₁_ge t (by linarith)]
  have hC : B.IsCobordismData f₀ hfs s₀ σ₁ (sectionAdd (pullbackProj P Prod.snd) Ŝ₁ p) := by
    refine ⟨hŜ₁.add hp, hle, hge, hgp₀, hgpσ₁, fun z hz => ?_, fun a b => ?_⟩
    · rw [hFeq] at hz ⊢
      exact hgpp z hz
    · rw [hFeq]
      have hFcl : IsClosed (solutionSet (pullbackProj P Prod.snd)
          (sectionAdd (pullbackProj P Prod.snd) G p)) :=
        isClosed_solutionSet (theorem_3_1_18_tame hGt hp).isScSmooth
      refine isCompact_slabZeros_of_subset hFcl hK' fun z hz => ?_
      have hz' := (isZeroAt_pullback_iff_pullbackSlice (hGs.sectionAdd hp.1) z.1 z.2).1 hz.1
      rw [pullbackSlice_sectionAdd hGs hp.1] at hz'
      by_cases hzW : z ∈ W'
      · have h1 := hN.auxLe_of_sectionAdd (hGs.pullbackSlice z.1) (hp.1.pullbackSlice z.1) hz'
          (hpN' z)
        exact hmemK' z hzW.2 ((hHbound z 1 h1).mono (by norm_num))
      · have hG0 := isZeroAt_left_of_isZeroAt_sectionAdd (hGs.pullbackSlice z.1)
          (hp.1.pullbackSlice z.1) hz' (hpZ z hzW)
        exact hGK' z ((isZeroAt_pullback_iff_pullbackSlice hGs z.1 z.2).2 hG0)
  refine ⟨_, hC, fun t ht => hC.pullbackSlice_le ht, fun t ht => ?_⟩
  rw [hC.pullbackSlice_ge ht, hσ₁def, ← sectionAdd_assoc hfs hH.slice_one.1 hs₁p.1]

/-- **The hypotheses of `exists_homotopy_cobordism` are satisfiable inside given neighbourhoods**
(for part (2) of 2021 Theorem 6.7.1, p. 277): for a proper homotopy `S` from `f₀` to
`f₁ = f₀ + S(1, ·)`, an auxiliary norm `N` and open `V₀ ⊇ S_{f₀}`, `V₁ ⊇ S_{f₁}`, there are `s₀`
admissible for `(N, V₀)` and `f₀`, `s₁` admissible for `(N, V₁)` and `f₁`, and cobordism data
`IsCobordismData f₀ s₀ (S(1, ·) + s₁) Ŝ`. Taking `Vᵢ` the neighbourhoods `U` of part (1) for `fᵢ`
and `N`, this joins `S_{f₀+s₀}` to `S_{f₁+s₁}` (`exists_slab_nbhd`, `exists_admissible`,
`exists_homotopy_cobordism` with `Uᵢ = Vᵢ ∩ {x | (i, x) ∈ W}`). -/
theorem exists_homotopy_cobordism_data (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    {f₀ : X → Y} {hf₀ : B.IsScFredholmSectionTame f₀}
    {S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
    (hH : B.IsProperOrientedHomotopy f₀ hf₀ S) {N : B.One → ℝ} (hN : B.IsAuxNorm N)
    {V₀ V₁ : Set X} (hV₀ : IsOpen V₀) (hSV₀ : solutionSet P f₀ ⊆ V₀) (hV₁ : IsOpen V₁)
    (hSV₁ : solutionSet P (sectionAdd P f₀ (pullbackSlice S 1)) ⊆ V₁) :
    ∃ (s₀ s₁ : X → Y)
      (Ŝ : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)),
      s₀ ∈ B.allowableSections N V₀ ∧
      (∀ x, IsZeroAt P (sectionAdd P f₀ s₀) x →
        B.IsGeneralPositionGerm (sectionAdd P f₀ s₀) x) ∧
      s₁ ∈ B.allowableSections N V₁ ∧
      (∀ x, IsZeroAt P (sectionAdd P (sectionAdd P f₀ (pullbackSlice S 1)) s₁) x →
        B.IsGeneralPositionGerm (sectionAdd P (sectionAdd P f₀ (pullbackSlice S 1)) s₁) x) ∧
      B.IsCobordismData f₀ hf₀.isScSmooth.1 s₀ (sectionAdd P (pullbackSlice S 1) s₁) Ŝ := by
  obtain ⟨W, hWo, hSW, hWc⟩ := hH.exists_slab_nbhd hN two_pos
  have hfs : IsSection P f₀ := hf₀.isScSmooth.1
  have hι : ∀ t : Fin 1 → ℝ, Continuous fun x : X => (t, x) := fun t =>
    continuous_const.prodMk continuous_id
  have hU₀o : IsOpen (V₀ ∩ (fun x : X => ((0 : Fin 1 → ℝ), x)) ⁻¹' W) :=
    hV₀.inter (hWo.preimage (hι 0))
  have hU₁o : IsOpen (V₁ ∩ (fun x : X => ((1 : Fin 1 → ℝ), x)) ⁻¹' W) :=
    hV₁.inter (hWo.preimage (hι 1))
  have hslab : ∀ t : Fin 1 → ℝ, t 0 ∈ Icc (0 : ℝ) 1 →
      ∀ x ∈ solutionSet P (sectionAdd P f₀ (pullbackSlice S t)), (t, x) ∈ W := by
    intro t ht x hx
    refine hSW ⟨(isZeroAt_pullback_iff_pullbackSlice hH.isSection_homotopySection t x).2 ?_, ht⟩
    rw [hH.pullbackSlice_homotopySection]
    exact hx
  have hSU₀ : solutionSet P f₀ ⊆ V₀ ∩ (fun x : X => ((0 : Fin 1 → ℝ), x)) ⁻¹' W :=
    fun x hx => ⟨hSV₀ hx, hslab 0 ⟨le_rfl, zero_le_one⟩ x
      (by rwa [hH.slice_zero, sectionAdd_fiberZero hfs])⟩
  have hSU₁ : solutionSet P (sectionAdd P f₀ (pullbackSlice S 1)) ⊆
      V₁ ∩ (fun x : X => ((1 : Fin 1 → ℝ), x)) ⁻¹' W :=
    fun x hx => ⟨hSV₁ hx, hslab 1 ⟨zero_le_one, le_rfl⟩ x hx⟩
  obtain ⟨s₀, hs₀, hgp₀⟩ :=
    exists_admissible hX hbump hf₀ hH.isCompact_solutionSet_zero hN hU₀o hSU₀
  obtain ⟨s₁, hs₁, hgp₁⟩ := exists_admissible hX hbump hH.isScFredholmSectionTame_one
    hH.isCompact_solutionSet_one hN hU₁o hSU₁
  obtain ⟨Ŝ, hC, -, -⟩ := exists_homotopy_cobordism hX hbump hH hN hWo hSW hWc
    (fun x hx => hx.2) (fun x hx => hx.2) hs₀ hgp₀ hs₁ hgp₁
  exact ⟨s₀, s₁, Ŝ, allowableSections_mono (fun _ => le_rfl) inter_subset_left hs₀, hgp₀,
    allowableSections_mono (fun _ => le_rfl) inter_subset_left hs₁, hgp₁, hC⟩

end HomotopyCobordism

end Polyfold
