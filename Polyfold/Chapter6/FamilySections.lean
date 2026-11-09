import Polyfold.Chapter6.Lemma629
import Polyfold.Chapter3.IndexAlongPathsDevice

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.5,
pp. 224–226: two facts about sections over parameter families used in the proofs of
Proposition 6.6.7 (preprint 6.32), Lemmas 6.33–6.34 and Theorem 6.6.11 (preprint 6.35) *(book 2017: Proposition 6.13,
Lemmas 6.15–6.16, Theorem 6.1; see `BookConcordance.md`)*.

# Sections over parameter families

## What is formalized

* `reparamSection g S`: `(q, y) ↦ S(g(q), y)` for a section `S` of `π*P → ℝⁿ × X` and
  `g : ℝᵐ → ℝⁿ`; `pullbackSlice_reparamSection`.
* `StrongBundle.IsScPlusSection.reparam`: for `g` affine, `S ∘ (g × 1)` is again an sc⁺-section
  (the text views the sections `s(y, t)` of a path as sections over a square, `s(y, τ, t)`).
* `StrongBundle.isGeneralPositionGerm_paramSection_of_comp`: **adding sections keeps general
  position** at `(0, y)` (the text: "adding more sections, the properties will still hold").
* Helpers: `StrongBundle.isScPlusSection_of_local` (an sc⁺-section may be checked in one chart of
  the atlas around each point) and `rnProdMapOp` (the sc-operator `(a, u) ↦ (Aa, u)`).
-/

open Topology Set

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

/-- **Reparametrizing a section of `π*P → ℝⁿ × X`** along `g : ℝᵐ → ℝⁿ`: `(q, y) ↦ S(g(q), y)`. -/
def reparamSection {m n : ℕ} (g : (Fin m → ℝ) → (Fin n → ℝ))
    (S : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))
    (hS : IsSection (pullbackProj P Prod.snd) S) :
    (Fin m → ℝ) × X → pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X) :=
  pullbackLift Prod.snd (fun z => pullbackSlice S (g z.1) z.2)
    (fun z => IsSection.pullbackSlice hS (g z.1) z.2)

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})] in
theorem pullbackSlice_reparamSection {m n : ℕ} (g : (Fin m → ℝ) → (Fin n → ℝ))
    (S : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))
    (hS : IsSection (pullbackProj P Prod.snd) S) (q : Fin m → ℝ) :
    pullbackSlice (reparamSection g S hS) q = pullbackSlice S (g q) :=
  rfl

/-- The sc-operator `ℝᵐ ⊕ E → ℝⁿ ⊕ E`, `(a, u) ↦ (Aa, u)`, of a linear map `A : ℝᵐ → ℝⁿ`. -/
def rnProdMapOp {m n : ℕ} (A : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) (E : ScBanach) :
    ScOperator ((rnSc m).prod E) ((rnSc n).prod E) where
  lvl k := A.prodMap (ContinuousLinearMap.id ℝ (E k))
  incl_comm _ _ := rfl

/-- **Sc⁺-sections are local**: a section whose representative is sc-smooth into `K[1]` in one
chart of the atlas around each point is an sc⁺-section (`isScPlusSection_iff`, sc-smoothness into
`Y[1]` being checked in one pair of charts around each point). -/
theorem StrongBundle.isScPlusSection_of_local {f : X → Y} (hsec : IsSection P f)
    (h : ∀ x, ∃ c ∈ B.atlas.charts, x ∈ c.φ.source ∧
      (∀ x' ∈ c.φ.source, (c (f x')).2 ∈ range (c.F.toBase 1)) ∧
      IsScSmoothRetractMap c.φ.model.E c.φ.model.C c.φ.model.O (c.φ.model.E.prod c.F.shift)
        (c.φ.model.C ×ˢ univ) (strongShiftOne c.K) (StrongBundle.localRepOne c f)) :
    B.IsScPlusSection f := by
  have hsrc : ∀ {c : StrongBundleChart PX P}, ∀ x ∈ c.φ.source, f x ∈ c.toPartialEquiv.source :=
    fun {c} x hx => by rw [c.source_eq, mem_preimage, hsec x]; exact hx
  have hmem : ∀ x, f x ∈ B.oneSet := fun x => by
    obtain ⟨c, hc, hx, hr, -⟩ := h x
    exact (B.mem_oneSet_iff hc (hsrc x hx)).2 (hr x hx)
  refine (B.isScPlusSection_iff f).2 ⟨hsec, fun x => B.oneMk (f x) (hmem x), rfl, ?_⟩
  refine MPolyfold.isScSmoothMap_of_local fun x => ?_
  obtain ⟨c, hc, hx, -, hsm⟩ := h x
  refine ⟨c.φ, StrongBundle.oneChart hc (B.oneMk (f x) (hmem x)), c.φ.source, c.isChart,
    B.isChart_oneChart hc _, c.φ.isOpen_source, hx, subset_rfl, fun z hz => hsrc z hz, ?_⟩
  rw [c.φ.image_source]
  exact hsm

/-- **An sc⁺-section reparametrized along an affine map is sc⁺**: in the pulled-back charts the
representative is that of `S` composed with `(q, u) ↦ (Aq + b, u)`. -/
theorem StrongBundle.IsScPlusSection.reparam {m n : ℕ}
    [ParacompactSpace ((Fin n → ℝ) × X)]
    [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
    [ParacompactSpace ((Fin m → ℝ) × X)]
    [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))]
    {S : (Fin n → ℝ) × X → pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)}
    (hS : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).IsScPlusSection S)
    (A : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) (b : Fin n → ℝ) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsScPlusSection
      (reparamSection (fun q => A q + b) S hS.1) := by
  set S' := reparamSection (fun q => A q + b) S hS.1 with hS'
  have hsec : IsSection (pullbackProj P (Prod.snd : (Fin m → ℝ) × X → X)) S' :=
    isSection_pullbackLift _
  refine StrongBundle.isScPlusSection_of_local hsec fun z => ?_
  obtain ⟨c, hc, hxc⟩ := StrongBundle.exists_chart_mem B z.2
  -- the product charts at `z = (q, x)` and at `(Aq + b, x)`
  set c' := (PullbackChartData.ofProd c z.1).toChart (S' z) with hc'
  set pc := (PullbackChartData.ofProd c (A z.1 + b)).toChart (S (A z.1 + b, z.2)) with hpc
  have hmem' : c' ∈ (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).atlas.charts :=
    ⟨_, _, hc, rfl⟩
  have hmem : pc ∈ (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX)).atlas.charts :=
    ⟨_, _, hc, rfl⟩
  obtain ⟨hrange, hsm⟩ := hS.2 pc hmem
  have hsrc : ∀ w ∈ c'.φ.source, ((A w.1 + b, w.2) : (Fin n → ℝ) × X) ∈ pc.φ.source :=
    fun w hw => ⟨mem_univ _, hw.2⟩
  refine ⟨c', hmem', ⟨mem_univ _, hxc⟩, fun w hw => hrange _ (hsrc w hw), ?_⟩
  -- `(a, u) ↦ (Aa, u)` as a map of retracts `ℝᵐ × O → ℝⁿ × O`
  have hO : IsScRetract c'.φ.model.E c'.φ.model.C c'.φ.model.O := c'.φ.model.isScRetract
  have hT : IsScSmoothRetractMap c'.φ.model.E c'.φ.model.C c'.φ.model.O pc.φ.model.E
      pc.φ.model.C pc.φ.model.O (rnProdMapOp A c.φ.model.E 0) :=
    (rnProdMapOp A c.φ.model.E).isScSmoothRetractMap hO fun p hp =>
      show ((A p.1, p.2) : (Fin n → ℝ) × c.φ.model.E 0) ∈ univ ×ˢ c.φ.model.O from
        ⟨mem_univ _, hp.2⟩
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
    -- `(p, pr₂ (localRepOne pc S (Aa, u))) = localRepOne c' S' p` for `p = (a, u)`
    change (R w, (StrongBundle.localRepOne pc S (rnProdMapOp A c.φ.model.E 0 (R w))).2) =
      StrongBundle.localRepOne c' S' (R w)
    generalize R w = p at hRw ⊢
    obtain ⟨a, u⟩ := p
    have hu : u ∈ c.φ.model.O := hRw.2
    set a' : Fin m → ℝ := a
    change ((a', u),
        Function.invFun (c.F.toBase 1) (c (S (A a' + (A z.1 + b), c.φ.symm u)).1.2).2) =
      ((a' + z.1 - z.1, c.φ (c.φ.symm u)),
        Function.invFun (c.F.toBase 1) (c (S (A (a' + z.1) + b, c.φ.symm u)).1.2).2)
    rw [c.φ.apply_symm_apply hu, add_sub_cancel_right, map_add, add_assoc]

/-- **Adding sections keeps general position**: if `g + Σ λᵢ sᵢ` is in general position at
`(0, y)` and every `sᵢ` is one of the `tⱼ` (`sᵢ = t_{ι(i)}`), then so is `g + Σ μⱼ tⱼ`
(`isParamGP_of_isGeneralPositionGerm`, `IsParamGP.comp`,
`isGeneralPositionGerm_paramSection_of_isParamGP`, in a tame chart centred at `y`). -/
theorem StrongBundle.isGeneralPositionGerm_paramSection_of_comp (_hX : PX.IsTame) {g : X → Y}
    (hg : B.IsScFredholmSectionTame g) {k m : ℕ} {s : Fin k → X → Y} {t : Fin m → X → Y}
    (hs : ∀ i, B.IsScPlusSection (s i)) (ht : ∀ j, B.IsScPlusSection (t j)) (ι : Fin k → Fin m)
    (hst : ∀ i, s i = t (ι i)) {y : X} (hy0 : IsZeroAt P g y)
    [ParacompactSpace ((Fin k → ℝ) × X)]
    [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin k → ℝ) × X → X))]
    [ParacompactSpace ((Fin m → ℝ) × X)]
    [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))]
    (h : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold k) PX)).IsGeneralPositionGerm
      (paramSection g hg.isScSmooth.1 s fun i => (hs i).1) (0, y)) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsGeneralPositionGerm
      (paramSection g hg.isScSmooth.1 t fun j => (ht j).1) (0, y) := by
  obtain ⟨-, c, hc, hyc, hφ0, -⟩ :=
    hg.germTame y (hg.toIsScFredholmSection.mem_smoothSet_of_isZeroAt hy0)
  obtain ⟨n, Wq, T, hT⟩ := c.φ.model.isPartialQuadrant
  have hp := isParamGP_of_isGeneralPositionGerm hg hs hy0 hc hyc hφ0 T hT h
  exact isGeneralPositionGerm_paramSection_of_isParamGP hg ht hy0 hc hyc hφ0 T hT (hp.comp ι hst)

end Polyfold
