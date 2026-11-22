import Polyfold.Chapter18.Linearization
import Polyfold.Chapter5.SolutionTangentKernel
import Polyfold.Chapter5.IndexLocallyConstantG

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 18,
§18.1, p. 845: **Definition 18.1.4** (the set `Lin(f, α)` of linearizations and the index
`ind(f, α)`) with the claims made before it, and **`φ_* : Lin(f, α) → Lin(f, α')`**.

# The set of linearizations of a section functor

## The text, paraphrased

At a smooth object `α`, take `Ψ̄ ∈ F̄(α)` and `q₀` with `Ψ(q₀) = α`.  For every local
sc⁺-section `s` near `q₀` with `s(q₀) = f_Ψ̄(q₀)`,
`f'_s(α)[α, Ψ, h] = (α, Ψ̄(q₀)((f_Ψ̄ − s)'(q₀) h))`.
"The collection of all `f'_s(α)` consists of linear sc-Fredholm operators, which all differ by
sc⁺-operators and therefore have the same index.  The collection is independent of the choice of
`Ψ̄` at `α`."  (Definition 18.1.4) `Lin(f, α)` is this set; `ind(f, α)` is the Fredholm index of
any of its elements.  For `φ : α → α'`, `φ_*(L) = φ̂ ∘ L ∘ Tφ⁻¹` maps `Lin(f, α)` to `Lin(f, α')`.

## What is formalized

* Part I (namespace `Polyfold.StrongBundle`): `linZeroAt_hasFiniteIndex` — at a zero `x` of an
  sc-smooth section `g` whose chart linearization is Fredholm of index `i` (`IsLinOfIndex`), the
  chart-free linearization `g'(x) : T_xX → Y_x` (`linZeroAt`) has finite-dimensional kernel and
  cokernel and index `i` (it is `Φ_x⁻¹ ∘ Lin(z) ∘ Tφ` with the restriction
  `Lin(z) : T_zO → K_z` of `IsLinOfIndex`, `range_fiberLin_eq_rangeS`); and
  `linZeroAt_sectionAdd_index` — for an sc-Fredholm `f`, an sc⁺-section `s` and a zero of `f + s`,
  `(f + s)'(x)` has finite index `ind(f, x)` (Definition 6.2.1, `IsIndexAt`).
* `StrongPolyfoldBundleConstruction.linSetAt hf α hΨ x hx`: the set of the text for **one**
  `Ψ̄ ∈ F̄(α)` and the point `x` over `α`; `mem_linSet_iff`: `Lin(f, α)` (`linSet`, module
  `Linearization`) is their union over all `(Ψ̄, x)`.
* `linSetAt_index`: for an sc-Fredholm section functor (Definition 18.1.1) every element of
  `linSetAt` has finite index `ind(f_Ψ̄, q₀)`.
* `transAct_fiberZero`, `transAct_sectionAdd`, `sectionAdd_localRep_transAct`: `T(a, ·)`
  preserves `0` and sums of sections related by `t̄`.
* `transSec`, `isScSmoothSection_transSec`, `linZeroAt_transAct_of_eqOn`: the transition law
  `g''(y)(Tσ(x) h) = T(a, g'(x) h)` for sc-smooth sections `g`, `g'` with `g'(t b) = T(b, g(s b))`
  for `b` near `a ∈ M(Ψ, Ψ')` (`linZeroAt_transTangent` is the case `g = f_Ψ̄`).
* `HasTransportedScPlusSections` (the hypothesis below), `exists_linZeroAt_transAct_hyp`,
  **`linSetAt_subset_hyp`** (with the reverse inclusion: the set does not depend on `(Ψ̄, x)`),
  **`linSet_eq_linSetAt_hyp`**, **`exists_index_linSet_hyp`** (one index `ind(f, α)` for all
  elements), **`linPush_mem_linSetAt_hyp`**, **`linPush_mem_linSet_hyp`** (`φ_*` maps
  `Lin(f, α)` into `Lin(f, α')`); **`definition_18_1_4_hyp`** collects them.

## Readings

* As in `linSet` (module `Linearization`), the text's `f − s` with `s(q₀) = f_Ψ̄(q₀)` is
  `f + s` with `(f + s)(q₀) = 0`, the sections `s` are sc⁺-sections of `K → O`, and `T_αC`
  carries its linear structure for `α ∈ C¹` with `F(α) ≠ ∅` (`Fact (S.TangentObj α)`).
* "sc-Fredholm of the same index" is read on level `0`, where the project's linearizations live:
  every element has finite-dimensional kernel and cokernel (`HasFiniteIndex`), and its index
  `dim ker − dim coker` (`linIndex`) is the same for all elements.  In a chart the elements are
  Part I's sc-Fredholm operators `T_zO → K_z` (`StrongBundle.linAt_isScFredholm`); the
  intrinsic operators are conjugate to them by linear isomorphisms.
* The independence of `Ψ̄` compares an sc⁺-section `s` of `K → O` with one of `K' → O'` near a
  point of the transition `M(Ψ, Ψ')`.  The sections `s` being sections over all of `O`, this
  needs that the transported section `t̄ ∘ s̄⁻¹ ∘ s` near `q₀'` agrees near `q₀'` with an
  sc⁺-section over all of `O'`.  This is the hypothesis `HasTransportedScPlusSections`
  (`_hyp`), which the text does not state; we read the text's "local sc⁺-section near `q₀`" as
  needing it.  It is meant for `O'` with sc-smooth bump functions (cut off the transported
  section; not formalized here), and it holds for the reflection bundle, where the transitions
  are global (`LinearizationSetExamples`).
* `φ_*` maps into `Lin(f, α')` when `F̄(α') ≠ ∅` (as in `equation_18_2`).
-/

set_option maxSynthPendingDepth 3

open Set Function Module

noncomputable section

namespace Polyfold

universe u v

/-! ### Linear algebra: the index of a conjugate -/

section Conj

variable {E E' F F' : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup E'] [Module ℝ E']
  [AddCommGroup F] [Module ℝ F] [AddCommGroup F'] [Module ℝ F']

/-- **Conjugating by linear isomorphisms keeps finite index and the index.** -/
theorem hasFiniteIndex_conj (e₁ : E' ≃ₗ[ℝ] E) (e₂ : F ≃ₗ[ℝ] F') {u : E →ₗ[ℝ] F}
    (hu : HasFiniteIndex u) :
    HasFiniteIndex ((e₂ : F →ₗ[ℝ] F') ∘ₗ u ∘ₗ (e₁ : E' →ₗ[ℝ] E)) ∧
      linIndex ((e₂ : F →ₗ[ℝ] F') ∘ₗ u ∘ₗ (e₁ : E' →ₗ[ℝ] E)) = linIndex u := by
  have h1 := HasFiniteIndex.comp (HasFiniteIndex.equiv e₁) hu
  have i1 := linIndex_comp (HasFiniteIndex.equiv e₁) hu
  refine ⟨HasFiniteIndex.comp h1 (HasFiniteIndex.equiv e₂), ?_⟩
  rw [linIndex_comp h1 (HasFiniteIndex.equiv e₂), i1, linIndex_equiv, linIndex_equiv]
  ring

end Conj

/-! ### Part I: the index of the chart-free linearization -/

section PartI

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f g s : X → Y}

open StrongRetr MPolyfold

omit [T2Space Y] [ParacompactSpace Y] in
/-- **The fibre `Φ_x(Y_x)` of a strong bundle chart is `K_z = ρ(z)F`**, for the level-`1` point
`z` over `φ(x)`. -/
theorem StrongBundleChart.range_fiberLin_eq_rangeS (c : StrongBundleChart PX P) {x : PX.Level 1}
    (hx : PX.levelVal 1 x ∈ c.φ.source)
    (hzU : c.φ.model.E.toBase 1 (levelLift c.φ 1 (PX.levelVal 1 x)) ∈ c.U) :
    LinearMap.range (c.fiberLin hx) = rangeS (ρCLM c.isRetraction hzU) := by
  have ha : c.φ.model.E.toBase 1 (levelLift c.φ 1 (PX.levelVal 1 x)) =
      c.φ (PX.levelVal 1 x) := PX.toBase_levelLift c.isChart hx (levelVal_mem x)
  have hyO : c.φ (PX.levelVal 1 x) ∈ c.φ.model.O := c.φ.mapsTo_model _ hx
  ext k
  constructor
  · rintro ⟨v, rfl⟩
    have hK : (c.φ (PX.levelVal 1 x), c.fiberLin hx v) ∈ c.K := by
      rw [← c.apply_fiberLin hx v, ← c.image_source]; exact ⟨_, c.fiberLin_src hx v, rfl⟩
    have hU : c.φ (PX.levelVal 1 x) ∈ c.U :=
      mem_U_of_mem_O c.isRetraction (by rw [c.r_image]; exact hyO)
    refine ⟨c.fiberLin hx v, ?_⟩
    change ρ c.R _ (c.fiberLin hx v) = _
    rw [ha]
    exact ρ_eq_self_of_mem_K c.isRetraction hU hK
  · rintro ⟨k', rfl⟩
    apply c.mem_range_fiberLin hx
    change (_, ρ c.R _ k') ∈ c.K
    rw [ha]
    exact c.mem_K_ρ hyO k'

/-- **The chart-free linearization has the index of the chart linearization**: at a zero `x` of
an sc-smooth section `g` with `IsLinOfIndex g x i`, `g'(x) = linZeroAt` has finite-dimensional
kernel and cokernel and `dim ker − dim coker = i`.  Proof: `g'(x) = Φ_x⁻¹ ∘ Lin(z) ∘ Tφ` in a
chart, with linear isomorphisms `Tφ : T_xX ≅ T_zO` (`tangentFiberLinearEquiv`,
`mem_tangentFiberModel_iff_rangeS`) and `Φ_x : Y_x ≅ K_z` (`range_fiberLin_eq_rangeS`). -/
theorem StrongBundle.linZeroAt_hasFiniteIndex (hg : B.IsScSmoothSection g) {x : PX.Level 1}
    (h0 : IsZeroAt P g (PX.levelVal 1 x)) {i : ℤ}
    (hi : B.IsLinOfIndex g (PX.levelVal 1 x) i) :
    HasFiniteIndex (B.linZeroAt hg x h0) ∧ linIndex (B.linZeroAt hg x h0) = i := by
  obtain ⟨c, hcm, hxc⟩ := B.exists_chart_mem (PX.levelVal 1 x)
  have hc := B.isChart_of_mem hcm
  rw [StrongBundle.linZeroAt_eq hg h0 hc hxc]
  set z := levelLift c.φ 1 (PX.levelVal 1 x) with hzdef
  have hz : c.φ.model.E.toBase 1 z = c.φ (PX.levelVal 1 x) :=
    PX.toBase_levelLift c.isChart hxc (levelVal_mem x)
  have hzO : c.φ.model.E.toBase 1 z ∈ r c.R '' c.U := by
    rw [c.r_image, hz]; exact c.φ.mapsTo_model _ hxc
  have hzU : c.φ.model.E.toBase 1 z ∈ c.U := mem_U_of_mem_O c.isRetraction hzO
  have hmem : ∀ v : ↥(rangeS (scDeriv c.U (r c.R) z)),
      linAt c.U c.R (c.principal g) z v ∈ rangeS (ρCLM c.isRetraction hzU) := fun v =>
    ⟨_, rho_scDeriv_comp_r c.relOpen c.isRetraction (hg.isSc1_principal_comp_r hc)
      (fun y hy => c.principal_mem_K hg.1 (c.r_image ▸ hy)) hzO
      (by rw [hz]; exact (c.isZeroAt_iff hg.1 hxc).1 h0) v⟩
  set L₁ := (linAt c.U c.R (c.principal g) z).codRestrict _ hmem with hL₁
  obtain ⟨hF, hind⟩ := hi c hc hxc z hz hzU L₁ fun _ => rfl
  have hT : tangentFiberModel c.isChart hxc = rangeS (scDeriv c.U (r c.R) z) :=
    Submodule.ext fun w => c.mem_tangentFiberModel_iff_rangeS hxc w
  let e₁ : PX.tangentFiber x ≃ₗ[ℝ] ↥(rangeS (scDeriv c.U (r c.R) z)) :=
    (tangentFiberLinearEquiv c.isChart hxc).trans (LinearEquiv.ofEq _ _ hT)
  let e₂ : ↥(rangeS (ρCLM c.isRetraction hzU)) ≃ₗ[ℝ] P ⁻¹' {PX.levelVal 1 x} :=
    (LinearEquiv.ofEq _ _ (c.range_fiberLin_eq_rangeS hxc hzU).symm).trans
      (LinearEquiv.ofInjective (c.fiberLin hxc) (c.fiberLin_injective hxc)).symm
  have he : B.linIntr hg hc hxc h0 =
      e₂.toLinearMap ∘ₗ (L₁ : _ →ₗ[ℝ] _) ∘ₗ e₁.toLinearMap := by
    refine LinearMap.ext fun α => c.fiberLin_injective hxc ?_
    rw [StrongBundle.fiberLin_linIntr, StrongBundleChart.linChart_apply]
    set w := L₁ (e₁ α)
    have hw : c.fiberLin hxc (e₂ w) = (w : c.F 0) := by
      have h := congrArg Subtype.val ((LinearEquiv.ofInjective (c.fiberLin hxc)
        (c.fiberLin_injective hxc)).apply_symm_apply ⟨(w : c.F 0),
          (c.range_fiberLin_eq_rangeS hxc hzU).symm ▸ w.2⟩)
      exact h
    change _ = c.fiberLin hxc (e₂ w)
    rw [hw]
    rfl
  rw [he]
  have hc' := hasFiniteIndex_conj e₁ e₂ (Polyfold.IsFredholm.hasFiniteIndex hF)
  exact ⟨hc'.1, hc'.2.trans hind⟩

/-- **`(f + s)'(x)` has the index `ind(f, x)`** (Definition 6.2.1): for an sc-Fredholm section
`f`, an sc⁺-section `s` and a zero `x` of `f + s` on level `1`, with `IsIndexAt f x i`, the
chart-free linearization `(f + s)'(x)` has finite index `i`. -/
theorem StrongBundle.linZeroAt_sectionAdd_index (hf : B.IsScFredholmSection f)
    (hs : B.IsScPlusSection s) {x : PX.Level 1}
    (h0 : IsZeroAt P (sectionAdd P f s) (PX.levelVal 1 x)) {i : ℤ}
    (hi : B.IsIndexAt f (PX.levelVal 1 x) i) :
    HasFiniteIndex (B.linZeroAt (hf.isScSmooth.sectionAdd hs) x h0) ∧
      linIndex (B.linZeroAt (hf.isScSmooth.sectionAdd hs) x h0) = i := by
  have hF := theorem_3_1_18_preprint hf hs
  have hxs := hF.mem_smoothSet_of_isZeroAt h0
  obtain ⟨-, c, hc, hxV, hφ0, h0U, g₀, t₀, hfill, ht₀, ht₀0, hconj⟩ := hF.germ _ hxs
  obtain ⟨dc⟩ := isConjugateToBasicGerm_iff_nonempty.1 hconj
  have hlin := StrongBundle.isLinOfIndex_of_conjugationData hF.isScSmooth h0 hc hxV hφ0 h0U
    hfill ht₀ ht₀0 dc
  have hj : B.IsIndexAt f (PX.levelVal 1 x) (finrank ℝ dc.Pn - finrank ℝ dc.Q) :=
    ⟨s, hs, h0, hlin⟩
  rw [hi.unique hf hj]
  exact StrongBundle.linZeroAt_hasFiniteIndex _ h0 hlin

/-- At a zero of `f + s`, `(f, x)` has an index (Definition 6.2.1). -/
theorem StrongBundle.exists_isIndexAt_of_isZeroAt_sectionAdd (hf : B.IsScFredholmSection f)
    (hs : B.IsScPlusSection s) {x : X} (h0 : IsZeroAt P (sectionAdd P f s) x) :
    ∃ i, B.IsIndexAt f x i := by
  have hF := theorem_3_1_18_preprint hf hs
  have hxs := hF.mem_smoothSet_of_isZeroAt h0
  obtain ⟨-, c, hc, hxV, hφ0, h0U, g₀, t₀, hfill, ht₀, ht₀0, hconj⟩ := hF.germ _ hxs
  obtain ⟨dc⟩ := isConjugateToBasicGerm_iff_nonempty.1 hconj
  exact ⟨_, s, hs, h0, StrongBundle.isLinOfIndex_of_conjugationData hF.isScSmooth h0 hc hxV hφ0
    h0U hfill ht₀ ht₀0 dc⟩

end PartI


/-! ### The fibre maps of the transitions -/

namespace GCT.VectorBundle.StrongBundleUniformizerData

variable {C : GCT.{u}} {V : C.VectorBundle} {Ψ Ψ' : V.StrongBundleUniformizerData}

/-- `Ψ̄(g + s)(q) = (Ψ(q), Ψ̄(q)(g q) + Ψ̄(q)(s q))`. -/
theorem obj_sectionAdd {g s : Ψ.base.O → Ψ.K} (hg : IsSection Ψ.p g) (hs : IsSection Ψ.p s)
    (q : Ψ.base.O) :
    Ψ.obj (sectionAdd Ψ.p g s q) =
      V.objMk (Ψ.base.obj q) (Ψ.fiber q ⟨g q, hg q⟩ + Ψ.fiber q ⟨s q, hs q⟩) := by
  rw [sectionAdd_apply hg hs, Ψ.obj_of_eq (((⟨g q, hg q⟩ : Ψ.p ⁻¹' {q}) + ⟨s q, hs q⟩ :
    Ψ.p ⁻¹' {q}).2), ← map_add]

/-- **The fibre map of `t̄` over `a = (q, φ, q')` is `φ̂ = μ(φ)`** read through `Ψ̄(q)`, `Ψ̄'(q')`:
for `k' = T(a, k)`, `Ψ̄'(q')(k') = μ(φ)(Ψ̄(q)(k))`. -/
theorem fiber_transAct (a : Ψ.base.Trans Ψ'.base) {k : Ψ.K} (hk : Ψ.p k = a.src) {k' : Ψ'.K}
    (hk' : Ψ'.p k' = a.tgt) (h : k' = transAct a k hk) :
    Ψ'.fiber a.tgt ⟨k', hk'⟩ = V.morFiber a.mor a.src_mor a.tgt_mor (Ψ.fiber a.src ⟨k, hk⟩) := by
  refine GroupoidalCategory.BanachFunctor.objMk_eq_iff.1 ?_
  calc V.objMk (Ψ'.base.obj a.tgt) (Ψ'.fiber a.tgt ⟨k', hk'⟩) = Ψ'.obj k' :=
        (Ψ'.obj_of_eq hk').symm
    _ = Ψ'.obj (transAct a k hk) := congrArg Ψ'.obj h
    _ = V.act a.mor (Ψ.obj k) ((congrArg Ψ.base.obj hk).trans a.src_mor.symm) :=
        obj_transAct a k hk
    _ = V.act a.mor (V.objMk (Ψ.base.obj a.src) (Ψ.fiber a.src ⟨k, hk⟩)) a.src_mor.symm :=
        V.act_congr rfl (Ψ.obj_of_eq hk) _ _
    _ = _ := act_objMk_morFiber a.mor a.src_mor a.tgt_mor _ a.src_mor.symm

/-- `T(a, 0) = 0`. -/
theorem transAct_fiberZero (a : Ψ.base.Trans Ψ'.base) :
    transAct a (fiberZero Ψ.p a.src) (proj_fiberZero Ψ.p a.src) = fiberZero Ψ'.p a.tgt := by
  have h := fiber_transAct a (proj_fiberZero Ψ.p a.src) (p_transAct a _ _) rfl
  have e0 : (⟨fiberZero Ψ.p a.src, proj_fiberZero Ψ.p a.src⟩ : Ψ.p ⁻¹' {a.src}) = 0 := rfl
  rw [e0, map_zero, map_zero] at h
  exact congrArg Subtype.val ((Ψ'.fiber a.tgt).injective (h.trans (map_zero _).symm))

/-- `T(a, k) = 0` for `k = 0`. -/
theorem transAct_eq_fiberZero (a : Ψ.base.Trans Ψ'.base) {k : Ψ.K} (hk : Ψ.p k = a.src)
    (h0 : k = fiberZero Ψ.p a.src) : transAct a k hk = fiberZero Ψ'.p a.tgt := by
  subst h0
  exact transAct_fiberZero a

/-- **`T(a, ·)` is additive on sections**: if `g'(t a) = T(a, g(s a))` and
`s'(t a) = T(a, s(s a))`, then `(g' + s')(t a) = T(a, (g + s)(s a))`. -/
theorem transAct_sectionAdd (a : Ψ.base.Trans Ψ'.base) {g s : Ψ.base.O → Ψ.K}
    {g' s' : Ψ'.base.O → Ψ'.K} (hg : IsSection Ψ.p g) (hs : IsSection Ψ.p s)
    (hg' : IsSection Ψ'.p g') (hs' : IsSection Ψ'.p s')
    (h1 : g' a.tgt = transAct a (g a.src) (hg a.src))
    (h2 : s' a.tgt = transAct a (s a.src) (hs a.src)) :
    sectionAdd Ψ'.p g' s' a.tgt =
      transAct a (sectionAdd Ψ.p g s a.src) ((hg.sectionAdd hs) a.src) := by
  have e : (⟨sectionAdd Ψ.p g s a.src, (hg.sectionAdd hs) a.src⟩ : Ψ.p ⁻¹' {a.src}) =
      ⟨g a.src, hg a.src⟩ + ⟨s a.src, hs a.src⟩ := Subtype.ext (sectionAdd_apply hg hs _)
  have e' : (⟨sectionAdd Ψ'.p g' s' a.tgt, (hg'.sectionAdd hs') a.tgt⟩ : Ψ'.p ⁻¹' {a.tgt}) =
      ⟨g' a.tgt, hg' a.tgt⟩ + ⟨s' a.tgt, hs' a.tgt⟩ := Subtype.ext (sectionAdd_apply hg' hs' _)
  have hT := fiber_transAct a ((hg.sectionAdd hs) a.src) (p_transAct a _ _) rfl
  have k1 := fiber_transAct a (hg a.src) (hg' a.tgt) h1
  have k2 := fiber_transAct a (hs a.src) (hs' a.tgt) h2
  have : (⟨sectionAdd Ψ'.p g' s' a.tgt, (hg'.sectionAdd hs') a.tgt⟩ : Ψ'.p ⁻¹' {a.tgt}) =
      ⟨transAct a _ _, p_transAct a _ ((hg.sectionAdd hs) a.src)⟩ :=
    (Ψ'.fiber a.tgt).injective (by rw [hT, e, e', map_add, map_add, map_add, k1, k2])
  exact congrArg Subtype.val this

end GCT.VectorBundle.StrongBundleUniformizerData

namespace GCT.VectorBundle.StrongPolyfoldBundleConstruction

open GroupoidalCategory GroupoidalCategory.BanachFunctor StrongBundleUniformizerConstruction
  StrongBundleUniformizerData PolyfoldConstruction

variable {C : GCT.{u}} {V : C.VectorBundle} {S : C.PolyfoldConstruction}
  (Q : V.StrongPolyfoldBundleConstruction S) {f : V.SectionFunctor}

/-! ### `Lin(f, α)` through one strong bundle uniformizer -/

variable (f) in
/-- The operator `f'_s(α) : e ↦ Ψ̄(x)((f_Ψ̄ + s)'(x)(S_Ψ e))` of Definition 18.1.4 for one
`Ψ̄ ∈ F̄(α)`, its point `x` over `α` and an sc⁺-section `s` with `(f_Ψ̄ + s)(x) = 0`. -/
def linOp (hf : Q.IsScSmoothSectionFunctor f) (α : C.Obj) [Fact (S.TangentObj α)]
    {Ψ : Q.Unif} (hΨ : Ψ.1 ∈ Q.F α) (x : Ψ.1.base.P.Level 1)
    (hx : Ψ.1.base.obj (Ψ.1.base.P.levelVal 1 x) = α) {s : Ψ.1.base.O → Ψ.1.K}
    (hs : Ψ.1.B.IsScPlusSection s)
    (h0 : IsZeroAt Ψ.1.p (sectionAdd Ψ.1.p (Ψ.1.localRep f) s) (Ψ.1.base.P.levelVal 1 x)) :
    S.TangentSpaceAt α →ₗ[ℝ] V.V α :=
  (V.fiberCast hx).toLinearMap ∘ₗ (Ψ.1.fiber (Ψ.1.base.P.levelVal 1 x)).toLinearMap ∘ₗ
    Ψ.1.B.linZeroAt ((hf α Ψ.1 hΨ).sectionAdd hs) x h0 ∘ₗ
      (S.tangentChartCLE α (Q.baseUnif Ψ) x hx).toLinearMap

variable (f) in
/-- **`Lin(f, α)` read through one `Ψ̄ ∈ F̄(α)`** and its level-`1` point `x` over `α`: the
operators `f'_s(α)` for the sc⁺-sections `s` of `K → O` with `(f_Ψ̄ + s)(x) = 0`
(Definition 18.1.4, before "The collection is independent of the choice of `Ψ̄`"). -/
def linSetAt (hf : Q.IsScSmoothSectionFunctor f) (α : C.Obj) [Fact (S.TangentObj α)]
    {Ψ : Q.Unif} (hΨ : Ψ.1 ∈ Q.F α) (x : Ψ.1.base.P.Level 1)
    (hx : Ψ.1.base.obj (Ψ.1.base.P.levelVal 1 x) = α) : Set (S.TangentSpaceAt α →ₗ[ℝ] V.V α) :=
  {L | ∃ (s : Ψ.1.base.O → Ψ.1.K) (hs : Ψ.1.B.IsScPlusSection s)
    (h0 : IsZeroAt Ψ.1.p (sectionAdd Ψ.1.p (Ψ.1.localRep f) s) (Ψ.1.base.P.levelVal 1 x)),
    L = Q.linOp f hf α hΨ x hx hs h0}

/-- **`Lin(f, α)` is the union of the sets read through the `Ψ̄ ∈ F̄(α)`.** -/
theorem mem_linSet_iff (hf : Q.IsScSmoothSectionFunctor f) (α : C.Obj) [Fact (S.TangentObj α)]
    (L : S.TangentSpaceAt α →ₗ[ℝ] V.V α) :
    L ∈ Q.linSet f hf α ↔ ∃ (Ψ : Q.Unif) (hΨ : Ψ.1 ∈ Q.F α) (x : Ψ.1.base.P.Level 1)
      (hx : Ψ.1.base.obj (Ψ.1.base.P.levelVal 1 x) = α), L ∈ Q.linSetAt f hf α hΨ x hx :=
  Iff.rfl

/-- `(α, f'_s(α) e) = Ψ̄((f_Ψ̄ + s)'(x)(S_Ψ e))`. -/
theorem objMk_linOp (hf : Q.IsScSmoothSectionFunctor f) (α : C.Obj) [Fact (S.TangentObj α)]
    {Ψ : Q.Unif} (hΨ : Ψ.1 ∈ Q.F α) (x : Ψ.1.base.P.Level 1)
    (hx : Ψ.1.base.obj (Ψ.1.base.P.levelVal 1 x) = α) {s : Ψ.1.base.O → Ψ.1.K}
    (hs : Ψ.1.B.IsScPlusSection s)
    (h0 : IsZeroAt Ψ.1.p (sectionAdd Ψ.1.p (Ψ.1.localRep f) s) (Ψ.1.base.P.levelVal 1 x))
    (e : S.TangentSpaceAt α) :
    V.objMk α (Q.linOp f hf α hΨ x hx hs h0 e) =
      Ψ.1.obj (Ψ.1.B.linZeroAt ((hf α Ψ.1 hΨ).sectionAdd hs) x h0
        (S.tangentChartCLE α (Q.baseUnif Ψ) x hx e)) := by
  set k := Ψ.1.B.linZeroAt ((hf α Ψ.1 hΨ).sectionAdd hs) x h0
    (S.tangentChartCLE α (Q.baseUnif Ψ) x hx e)
  rw [Ψ.1.obj_of_eq k.2]
  exact V.objMk_fiberCast hx _

/-- **The elements of `Lin(f, α)` read through one `Ψ̄` have the index `ind(f_Ψ̄, q₀)`**
(Definition 18.1.4: "linear sc-Fredholm operators … which have the same index"): for an
sc-Fredholm section functor `f` (Definition 18.1.1) and `IsIndexAt f_Ψ̄ q₀ i`, every element of
`linSetAt` has finite-dimensional kernel and cokernel and index `i`. -/
theorem linSetAt_index (hF : Q.IsScFredholmSectionFunctor f) (α : C.Obj)
    [Fact (S.TangentObj α)] {Ψ : Q.Unif} (hΨ : Ψ.1 ∈ Q.F α) (x : Ψ.1.base.P.Level 1)
    (hx : Ψ.1.base.obj (Ψ.1.base.P.levelVal 1 x) = α) {i : ℤ}
    (hi : Ψ.1.B.IsIndexAt (Ψ.1.localRep f) (Ψ.1.base.P.levelVal 1 x) i)
    {L : S.TangentSpaceAt α →ₗ[ℝ] V.V α}
    (hL : L ∈ Q.linSetAt f hF.isScSmoothSectionFunctor α hΨ x hx) :
    HasFiniteIndex L ∧ linIndex L = i := by
  obtain ⟨s, hs, h0, rfl⟩ := hL
  obtain ⟨h1, h2⟩ := StrongBundle.linZeroAt_sectionAdd_index (hF α Ψ.1 hΨ) hs h0 hi
  have hc := hasFiniteIndex_conj (S.tangentChartCLE α (Q.baseUnif Ψ) x hx).toLinearEquiv
    ((Ψ.1.fiber (Ψ.1.base.P.levelVal 1 x)).toLinearEquiv.trans (V.fiberCast hx).toLinearEquiv) h1
  exact ⟨hc.1, hc.2.trans h2⟩

/-- Every element of `Lin(f, α)` read through `Ψ̄` comes with an index of `(f_Ψ̄, q₀)`. -/
theorem exists_isIndexAt_of_mem_linSetAt (hF : Q.IsScFredholmSectionFunctor f) (α : C.Obj)
    [Fact (S.TangentObj α)] {Ψ : Q.Unif} (hΨ : Ψ.1 ∈ Q.F α) (x : Ψ.1.base.P.Level 1)
    (hx : Ψ.1.base.obj (Ψ.1.base.P.levelVal 1 x) = α) {L : S.TangentSpaceAt α →ₗ[ℝ] V.V α}
    (hL : L ∈ Q.linSetAt f hF.isScSmoothSectionFunctor α hΨ x hx) :
    ∃ i, Ψ.1.B.IsIndexAt (Ψ.1.localRep f) (Ψ.1.base.P.levelVal 1 x) i := by
  obtain ⟨s, hs, h0, -⟩ := hL
  exact StrongBundle.exists_isIndexAt_of_isZeroAt_sectionAdd (hF α Ψ.1 hΨ) hs h0


/-! ### Sections related by `t̄` near a point of `M(Ψ, Ψ')` -/

open StrongRetr MPolyfold

/-- **The sum of sections related by `t̄` is related by `t̄`**: if `s'(q') = T(a, s(q))` at
`a = (q, φ, q')`, then `(f_Ψ̄' + s')(q') = T(a, (f_Ψ̄ + s)(q))` (`localRep_transAct`). -/
theorem sectionAdd_localRep_transAct (Ψ Ψ' : Q.Unif) {s : Ψ.1.base.O → Ψ.1.K}
    {s' : Ψ'.1.base.O → Ψ'.1.K} (hs : IsSection Ψ.1.p s) (hs' : IsSection Ψ'.1.p s')
    (b : S.Tr (Q.baseUnif Ψ) (Q.baseUnif Ψ')) (hb : s' b.tgt = transAct b (s b.src) (hs b.src)) :
    sectionAdd Ψ'.1.p (Ψ'.1.localRep f) s' b.tgt =
      transAct b (sectionAdd Ψ.1.p (Ψ.1.localRep f) s b.src)
        ((Ψ.1.isSection_localRep f).sectionAdd hs b.src) :=
  transAct_sectionAdd (Ψ := Ψ.1.toStrongBundleUniformizerData)
    (Ψ' := Ψ'.1.toStrongBundleUniformizerData) b (Ψ.1.isSection_localRep f) hs
    (Ψ'.1.isSection_localRep f) hs' (Ψ.1.localRep_transAct f b) hb

/-- **2021 p. 845, hypothesis read with Definition 18.1.4 (`_hyp`)**: sc⁺-sections can be
carried along the transitions.  For `Ψ̄, Ψ̄' ∈ F̄`, `a ∈ M(Ψ, Ψ')` and an sc⁺-section `s` of
`K → O`, there is an sc⁺-section `s'` of `K' → O'` with `s'(t b) = T(b, s(s b))` for `b` near
`a`: the transported section `t̄ ∘ s̄⁻¹ ∘ s` agrees near `t(a)` with a section over all of `O'`.
It is meant for `O'` with sc-smooth bump functions; for the reflection bundle it holds with
the global transitions `k ↦ g ∗ k` (`ReflectionBundle.reflQ_hasTransportedScPlusSections`). -/
def HasTransportedScPlusSections : Prop :=
  ∀ (Ψ Ψ' : Q.Unif) (a : S.Tr (Q.baseUnif Ψ) (Q.baseUnif Ψ')) (s : Ψ.1.base.O → Ψ.1.K)
    (hs : Ψ.1.B.IsScPlusSection s), ∃ s' : Ψ'.1.base.O → Ψ'.1.K, Ψ'.1.B.IsScPlusSection s' ∧
      ∃ N : Set (S.Tr (Q.baseUnif Ψ) (Q.baseUnif Ψ')), IsOpen N ∧ a ∈ N ∧
        ∀ b ∈ N, s' b.tgt = transAct b (s b.src) (hs.1 b.src)

/-- `a ↦ (a, g(s a))`: the pull-back `s*g` of a section `g` of `K → O` to `M(Ψ, Ψ')`. -/
def transSec (Ψ Ψ' : Q.Unif) {g : Ψ.1.base.O → Ψ.1.K} (hg : IsSection Ψ.1.p g)
    (a : S.Tr (Q.baseUnif Ψ) (Q.baseUnif Ψ')) : Q.TransSpace Ψ Ψ' :=
  ⟨(a, g a.src), hg a.src⟩

/-- On a sheet `W` of `s̄`, `s*g = s̄⁻¹ ∘ g ∘ s`. -/
theorem eqOn_transSec_src (Ψ Ψ' : Q.Unif) {g : Ψ.1.base.O → Ψ.1.K} (hg : IsSection Ψ.1.p g)
    {W : Set (S.Tr (Q.baseUnif Ψ) (Q.baseUnif Ψ'))} {W' : Set Ψ.1.base.O}
    (hi : (Q.transBundle Ψ Ψ').IsStrongBundleIsoOn Ψ.1.B
      (Ψ.1.B.isStrongBundleMap_pullbackProj' (Q.isScSmoothMap_trSrc Ψ Ψ')) W W') :
    EqOn (Q.transSec Ψ Ψ' hg) (hi.toLocalIso.Ψ ∘ g ∘ hi.toLocalIso.ϕ) W :=
  fun b hb => (hi.toLocalIso.zero.left_inv (Q.transSec Ψ Ψ' hg b) hb).symm

/-- `s*g` is sc-smooth if `g` is. -/
theorem isScSmoothSection_transSec (Ψ Ψ' : Q.Unif) {g : Ψ.1.base.O → Ψ.1.K}
    (hg : Ψ.1.B.IsScSmoothSection g) :
    (Q.transBundle Ψ Ψ').IsScSmoothSection (Q.transSec Ψ Ψ' hg.1) := by
  refine ⟨fun _ => rfl, MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun a _ => ?_⟩
  obtain ⟨W, W', ha, hi⟩ := Q.isLocalStrongBundleIso_src Ψ Ψ' a
  have hmaps : MapsTo (g ∘ hi.toLocalIso.ϕ) W (Ψ.1.p ⁻¹' W') := fun b hb => by
    change Ψ.1.p (g (hi.toLocalIso.ϕ b)) ∈ W'
    rw [hg.1]; exact hi.toLocalIso.base.mapsTo hb
  exact ⟨W, hi.toLocalIso.isOpen_U, ha, subset_univ _,
    (MPolyfold.IsScSmoothOn.comp hi.toLocalIso.zero.isScSmoothOn_inv
      (MPolyfold.IsScSmoothOn.comp hg.2 hi.toLocalIso.base.isScSmoothOn (mapsTo_univ _ _))
      hmaps).congr (Q.eqOn_transSec_src Ψ Ψ' hg.1 hi).symm⟩

/-- **The transition law of the linearizations for sections related by `t̄` near `a`**: for
sc-smooth sections `g` of `K → O` and `g'` of `K' → O'` with `g'(t b) = T(b, g(s b))` for `b` in
an open `N ∋ a`, and zeros `x` of `g` over `s(a)` and `y` of `g'` over `t(a)` on level `1`,
`g''(y)(Tσ(x) h) = T(a, g'(x) h)` (`linZeroAt_transTangent` is the case `g = f_Ψ̄`,
`g' = f_Ψ̄'`, `N = M(Ψ, Ψ')`). -/
theorem linZeroAt_transAct_of_eqOn (Ψ Ψ' : Q.Unif) (a : S.Tr (Q.baseUnif Ψ) (Q.baseUnif Ψ'))
    {g : Ψ.1.base.O → Ψ.1.K} {g' : Ψ'.1.base.O → Ψ'.1.K}
    (hg : Ψ.1.B.IsScSmoothSection g) (hg' : Ψ'.1.B.IsScSmoothSection g')
    {N : Set (S.Tr (Q.baseUnif Ψ) (Q.baseUnif Ψ'))} (hN : IsOpen N) (haN : a ∈ N)
    (hrel : ∀ b ∈ N, g' b.tgt = transAct b (g b.src) (hg.1 b.src))
    {x : Ψ.1.base.P.Level 1} {y : Ψ'.1.base.P.Level 1} (hx : Ψ.1.base.P.levelVal 1 x = a.src)
    (hy : Ψ'.1.base.P.levelVal 1 y = a.tgt)
    (h0 : IsZeroAt Ψ.1.p g (Ψ.1.base.P.levelVal 1 x))
    (h0' : IsZeroAt Ψ'.1.p g' (Ψ'.1.base.P.levelVal 1 y))
    (v : Ψ.1.base.P.tangentFiber x) :
    (Ψ'.1.B.linZeroAt hg' y h0' (S.transTangent a hx hy v) : Ψ'.1.K) =
      transAct a (Ψ.1.B.linZeroAt hg x h0 v)
        ((show Ψ.1.p (Ψ.1.B.linZeroAt hg x h0 v : Ψ.1.K) = _ from
          (Ψ.1.B.linZeroAt hg x h0 v).2).trans hx) := by
  obtain ⟨Ws, Ws', has, his⟩ := Q.isLocalStrongBundleIso_src Ψ Ψ' a
  obtain ⟨Wt₁, Wt₁', hat₁, hit₁⟩ := Q.isLocalStrongBundleIso_trans Ψ Ψ' a
  obtain ⟨gb, hgb⟩ := hit₁.isScDiffeoOn_base
  have hWt : IsOpen (Wt₁ ∩ N) := hgb.isOpen_source.inter hN
  have hit := hit₁.restrict hgb hWt inter_subset_left
  have hat : a ∈ Wt₁ ∩ N := ⟨hat₁, haN⟩
  set Ls := his.toLocalIso with hLs
  set Lt := hit.toLocalIso with hLt
  have heqT : EqOn (Q.transSec Ψ Ψ' hg.1) (Lt.Ψ ∘ g' ∘ Lt.ϕ) (Wt₁ ∩ N) := by
    intro b hb
    have h1 := Lt.zero.left_inv (Q.transSec Ψ Ψ' hg.1 b) hb
    have h2 : Lt.Φ (Q.transSec Ψ Ψ' hg.1 b) = g' b.tgt := (hrel b hb.2).symm
    rw [← h1, h2]
    rfl
  have hgs := Q.isScSmoothSection_transSec Ψ Ψ' hg
  have hqs : Ψ.1.base.P.levelVal 1 x ∈ Ws' := by rw [hx]; exact Ls.base.mapsTo has
  have hga : Ls.g (Ψ.1.base.P.levelVal 1 x) = a := by rw [hx]; exact Ls.base.left_inv a has
  have ha1 : a ∈ (S.transPolyfold (Q.baseUnif Ψ) (Q.baseUnif Ψ')).levelSet 1 :=
    (Ls.mem_levelSet_iff has 1).2 (by
      change a.src ∈ _
      rw [← hx]; exact Ψ.1.base.P.levelVal_mem x)
  set xa := (S.transPolyfold (Q.baseUnif Ψ) (Q.baseUnif Ψ')).levelMk 1 a ha1 with hxadef
  have hxa : (S.transPolyfold (Q.baseUnif Ψ) (Q.baseUnif Ψ')).levelVal 1 xa = a :=
    MPolyfold.levelVal_levelMk _ _ _
  have hxxa : Ls.symm.ϕ (Ψ.1.base.P.levelVal 1 x) =
      (S.transPolyfold (Q.baseUnif Ψ) (Q.baseUnif Ψ')).levelVal 1 xa := hga.trans hxa.symm
  have hxaU : (S.transPolyfold (Q.baseUnif Ψ) (Q.baseUnif Ψ')).levelVal 1 xa ∈ Wt₁ ∩ N := by
    rw [hxa]; exact hat
  have hxay : Lt.ϕ ((S.transPolyfold (Q.baseUnif Ψ) (Q.baseUnif Ψ')).levelVal 1 xa) =
      Ψ'.1.base.P.levelVal 1 y := by rw [hxa, hy]; rfl
  have h0g : IsZeroAt _ (Q.transSec Ψ Ψ' hg.1)
      ((S.transPolyfold (Q.baseUnif Ψ) (Q.baseUnif Ψ')).levelVal 1 xa) :=
    Lt.isZeroAt_of_eqOn heqT hxaU (by rw [hxay]; exact h0')
  have heqA : EqOn g (Ls.symm.Ψ ∘ Q.transSec Ψ Ψ' hg.1 ∘ Ls.symm.ϕ) Ws' :=
    fun q hq => by
      change g q = g (Ls.ϕ (Ls.g q))
      rw [Ls.base.right_inv q hq]
  have hA := Ls.symm.linZeroAt_transport hg hgs heqA hqs hxxa h0 h0g v
  set w := tangentMapOnCLM Ls.symm.base.isScSmoothOn hqs hxxa v with hwdef
  have hB := Lt.linZeroAt_transport hgs hg' heqT hxaU hxay h0g h0' w
  have hW : IsOpen (Ws ∩ (Wt₁ ∩ N)) := Ls.isOpen_U.inter Lt.isOpen_U
  let T : S.AdmissibleTriple a := ⟨_, Ws ∩ (Wt₁ ∩ N), _, Ls.g, Lt.g, ⟨has, hat⟩,
    Ls.base.restrict hW inter_subset_left, Lt.base.restrict hW inter_subset_right⟩
  have hTo : IsOpen T.srcSet := T.isScDiffeoOn_src.isOpen_target
  have hfs : Ψ.1.base.P.IsScSmoothOn _ Ls.g T.srcSet :=
    Ls.base.isScSmoothOn_inv.mono hTo inter_subset_left
  have hmaps : MapsTo Ls.g T.srcSet (Wt₁ ∩ N) := fun p hp => hp.2.2
  have hvmem : v.1 ∈ Ψ.1.base.P.tangentPreimage T.srcSet := by
    rw [MPolyfold.mem_tangentPreimage, levelVal_tangentProj_of_mem v.2, hx]; exact T.src_mem
  have hT : S.transTangent a hx hy v = tangentMapOnCLM Lt.base.isScSmoothOn hxaU hxay w := by
    refine Subtype.ext ?_
    rw [transTangent_apply, tangentMapOnCLM_apply, hwdef, tangentMapOnCLM_apply,
      transMap_eq T ((levelVal_tangentProj_of_mem v.2).trans hx)]
    refine (MPolyfold.tangentMapOn_comp Lt.base.isScSmoothOn hfs hmaps hvmem).trans ?_
    exact congrArg _ (MPolyfold.tangentMapOn_congr hfs Ls.base.isScSmoothOn_inv hTo subset_rfl
      inter_subset_left (fun _ _ => rfl) hvmem)
  rw [hT, ← hB, ← hA]
  set k := (Ψ.1.B.linZeroAt hg x h0 v : Ψ.1.K) with hkdef
  have hk : Ψ.1.p k = a.src := (show Ψ.1.p k = _ from (Ψ.1.B.linZeroAt hg x h0 v).2).trans hx
  have hkW : Ψ.1.p k ∈ Ws' := by rw [hk]; exact Ls.base.mapsTo has
  have e : Ls.Ψ k = (⟨(a, k), hk⟩ : Q.TransSpace Ψ Ψ') := by
    refine Subtype.ext (Prod.ext ?_ ?_)
    · change pullbackProj Ψ.1.p _ (Ls.Ψ k) = a
      rw [Ls.covers_inv k hkW, hk]; exact Ls.base.left_inv a has
    · exact Ls.zero.right_inv k hkW
  change Q.transT Ψ Ψ' (Ls.Ψ k) = _
  rw [e]
  rfl


/-- **Transport of an element of `Lin(f, α)` along `a ∈ M(Ψ, Ψ')`** (under
`HasTransportedScPlusSections`): for an sc⁺-section `s` with `(f_Ψ̄ + s)(x) = 0`, `x` over
`s(a)`, there is an sc⁺-section `s'` of `K' → O'` with `(f_Ψ̄' + s')(y) = 0`, `y` over `t(a)`, and
`(f_Ψ̄' + s')'(y)(Tσ(x) h) = T(a, (f_Ψ̄ + s)'(x) h)`. -/
theorem exists_linZeroAt_transAct_hyp (hT : Q.HasTransportedScPlusSections) (Ψ Ψ' : Q.Unif)
    (a : S.Tr (Q.baseUnif Ψ) (Q.baseUnif Ψ'))
    (hfΨ : Ψ.1.B.IsScSmoothSection (Ψ.1.localRep f))
    (hfΨ' : Ψ'.1.B.IsScSmoothSection (Ψ'.1.localRep f))
    {x : Ψ.1.base.P.Level 1} {y : Ψ'.1.base.P.Level 1} (hx : Ψ.1.base.P.levelVal 1 x = a.src)
    (hy : Ψ'.1.base.P.levelVal 1 y = a.tgt) {s : Ψ.1.base.O → Ψ.1.K}
    (hs : Ψ.1.B.IsScPlusSection s)
    (h0 : IsZeroAt Ψ.1.p (sectionAdd Ψ.1.p (Ψ.1.localRep f) s) (Ψ.1.base.P.levelVal 1 x)) :
    ∃ (s' : Ψ'.1.base.O → Ψ'.1.K) (hs' : Ψ'.1.B.IsScPlusSection s')
      (h0' : IsZeroAt Ψ'.1.p (sectionAdd Ψ'.1.p (Ψ'.1.localRep f) s') (Ψ'.1.base.P.levelVal 1 y)),
      ∀ v : Ψ.1.base.P.tangentFiber x,
        (Ψ'.1.B.linZeroAt (hfΨ'.sectionAdd hs') y h0' (S.transTangent a hx hy v) : Ψ'.1.K) =
          transAct a (Ψ.1.B.linZeroAt (hfΨ.sectionAdd hs) x h0 v)
            ((show Ψ.1.p (Ψ.1.B.linZeroAt (hfΨ.sectionAdd hs) x h0 v : Ψ.1.K) = _ from
              (Ψ.1.B.linZeroAt (hfΨ.sectionAdd hs) x h0 v).2).trans hx) := by
  obtain ⟨s', hs', N, hN, haN, hrel⟩ := hT Ψ Ψ' a s hs
  have hrel' : ∀ b ∈ N, sectionAdd Ψ'.1.p (Ψ'.1.localRep f) s' b.tgt =
      transAct b (sectionAdd Ψ.1.p (Ψ.1.localRep f) s b.src) ((hfΨ.sectionAdd hs).1 b.src) :=
    fun b hb => Q.sectionAdd_localRep_transAct Ψ Ψ' hs.1 hs'.1 b (hrel b hb)
  have h0a : sectionAdd Ψ.1.p (Ψ.1.localRep f) s a.src = fiberZero Ψ.1.p a.src := by
    have h := h0
    unfold IsZeroAt at h
    rwa [hx] at h
  have h0' : IsZeroAt Ψ'.1.p (sectionAdd Ψ'.1.p (Ψ'.1.localRep f) s')
      (Ψ'.1.base.P.levelVal 1 y) := by
    unfold IsZeroAt
    rw [hy, hrel' a haN]
    exact transAct_eq_fiberZero (Ψ := Ψ.1.toStrongBundleUniformizerData)
      (Ψ' := Ψ'.1.toStrongBundleUniformizerData) a _ h0a
  exact ⟨s', hs', h0', fun v => Q.linZeroAt_transAct_of_eqOn Ψ Ψ' a (hfΨ.sectionAdd hs)
    (hfΨ'.sectionAdd hs') hN haN hrel' hx hy h0 h0' v⟩

/-! ### Definition 18.1.4: independence of `Ψ̄`, the index, and `φ_*` -/

/-- **`Lin(f, α)` read through `Ψ̄₁` lies in `Lin(f, α)` read through `Ψ̄₂`** (under
`HasTransportedScPlusSections`), along `(q₁, 1_α, q₂) ∈ M(Ψ₁, Ψ₂)`. -/
theorem linSetAt_subset_hyp (hT : Q.HasTransportedScPlusSections)
    (hf : Q.IsScSmoothSectionFunctor f) (α : C.Obj) [Fact (S.TangentObj α)] {Ψ₁ Ψ₂ : Q.Unif}
    (hΨ₁ : Ψ₁.1 ∈ Q.F α) (hΨ₂ : Ψ₂.1 ∈ Q.F α) (x₁ : Ψ₁.1.base.P.Level 1)
    (hx₁ : Ψ₁.1.base.obj (Ψ₁.1.base.P.levelVal 1 x₁) = α) (x₂ : Ψ₂.1.base.P.Level 1)
    (hx₂ : Ψ₂.1.base.obj (Ψ₂.1.base.P.levelVal 1 x₂) = α) :
    Q.linSetAt f hf α hΨ₁ x₁ hx₁ ⊆ Q.linSetAt f hf α hΨ₂ x₂ hx₂ := by
  rintro L ⟨s, hs, h0, rfl⟩
  set a := S.unitTr (Ψ := Q.baseUnif Ψ₁) (Ψ' := Q.baseUnif Ψ₂) _ _ hx₁ hx₂
  obtain ⟨s', hs', h0', hlin⟩ := Q.exists_linZeroAt_transAct_hyp hT Ψ₁ Ψ₂ a (hf α Ψ₁.1 hΨ₁)
    (hf α Ψ₂.1 hΨ₂) (x := x₁) (y := x₂) rfl rfl hs h0
  refine ⟨s', hs', h0', LinearMap.ext fun e => objMk_eq_iff.1 ?_⟩
  rw [objMk_linOp, objMk_linOp]
  have hTc : S.tangentChartCLE α (Q.baseUnif Ψ₂) x₂ hx₂ e =
      S.transTangent a rfl rfl (S.tangentChartCLE α (Q.baseUnif Ψ₁) x₁ hx₁ e) := by
    have h := tangentChart_symm_trans (S := S) (Q.baseUnif Ψ₁) (Q.base_mem α _ hΨ₁) x₁ hx₁
      (Q.baseUnif Ψ₂) (Q.base_mem α _ hΨ₂) x₂ hx₂ (S.tangentChartCLE α (Q.baseUnif Ψ₁) x₁ hx₁ e)
    rw [coe_tangentChartCLE α (Q.baseUnif Ψ₁) (Q.base_mem α _ hΨ₁) x₁ hx₁,
      Equiv.symm_apply_apply] at h
    rw [coe_tangentChartCLE α (Q.baseUnif Ψ₁) (Q.base_mem α _ hΨ₁) x₁ hx₁,
      coe_tangentChartCLE α (Q.baseUnif Ψ₂) (Q.base_mem α _ hΨ₂) x₂ hx₂]
    exact h
  rw [hTc, hlin]
  erw [obj_transAct]
  exact (act_unit' _ _).symm

/-- **Definition 18.1.4, "the collection is independent of the choice of `Ψ̄`"** (under
`HasTransportedScPlusSections`): `Lin(f, α)` is the set read through any one `Ψ̄ ∈ F̄(α)` and
any one point `x` of `Ψ̄` over `α`. -/
theorem linSet_eq_linSetAt_hyp (hT : Q.HasTransportedScPlusSections)
    (hf : Q.IsScSmoothSectionFunctor f) (α : C.Obj) [Fact (S.TangentObj α)] {Ψ : Q.Unif}
    (hΨ : Ψ.1 ∈ Q.F α) (x : Ψ.1.base.P.Level 1)
    (hx : Ψ.1.base.obj (Ψ.1.base.P.levelVal 1 x) = α) :
    Q.linSet f hf α = Q.linSetAt f hf α hΨ x hx := by
  refine Set.Subset.antisymm (fun L hL => ?_) fun L hL => (Q.mem_linSet_iff hf α L).2
    ⟨Ψ, hΨ, x, hx, hL⟩
  obtain ⟨Ψ₁, hΨ₁, x₁, hx₁, hL₁⟩ := (Q.mem_linSet_iff hf α L).1 hL
  exact Q.linSetAt_subset_hyp hT hf α hΨ₁ hΨ x₁ hx₁ x hx hL₁

/-- **Definition 18.1.4, "linear sc-Fredholm operators … which have the same index"** (under
`HasTransportedScPlusSections`): there is one `i` with every `L ∈ Lin(f, α)` of finite index
`i`.  Read through one `Ψ̄` this holds with no hypothesis (`linSetAt_index`). -/
theorem exists_index_linSet_hyp (hT : Q.HasTransportedScPlusSections)
    (hF : Q.IsScFredholmSectionFunctor f) (α : C.Obj) [Fact (S.TangentObj α)] :
    ∃ i : ℤ, ∀ L ∈ Q.linSet f hF.isScSmoothSectionFunctor α, HasFiniteIndex L ∧ linIndex L = i := by
  by_cases h : (Q.linSet f hF.isScSmoothSectionFunctor α).Nonempty
  · obtain ⟨L₀, hL₀⟩ := h
    obtain ⟨Ψ, hΨ, x, hx, hL₀'⟩ := (Q.mem_linSet_iff _ α L₀).1 hL₀
    obtain ⟨i, hi⟩ := Q.exists_isIndexAt_of_mem_linSetAt hF α hΨ x hx hL₀'
    refine ⟨i, fun L hL => Q.linSetAt_index hF α hΨ x hx hi ?_⟩
    rw [← Q.linSet_eq_linSetAt_hyp hT _ α hΨ x hx]
    exact hL
  · exact ⟨0, fun L hL => (h ⟨L, hL⟩).elim⟩

/-- **`φ_*` maps `Lin(f, α)` read through `Ψ̄` into `Lin(f, α')` read through `Ψ̄'`** (under
`HasTransportedScPlusSections`), along `(q, φ, q') ∈ M(Ψ, Ψ')`. -/
theorem linPush_mem_linSetAt_hyp (hT : Q.HasTransportedScPlusSections)
    (hf : Q.IsScSmoothSectionFunctor f) {α α' : C.Obj} [Fact (S.TangentObj α)]
    [Fact (S.TangentObj α')] (φ : C.Mor) (hs : C.toGroupoidStr.src φ = α)
    (ht : C.toGroupoidStr.tgt φ = α') {Ψ Ψ' : Q.Unif} (hΨ : Ψ.1 ∈ Q.F α) (hΨ' : Ψ'.1 ∈ Q.F α')
    (x : Ψ.1.base.P.Level 1) (hx : Ψ.1.base.obj (Ψ.1.base.P.levelVal 1 x) = α)
    (x' : Ψ'.1.base.P.Level 1) (hx' : Ψ'.1.base.obj (Ψ'.1.base.P.levelVal 1 x') = α')
    {L : S.TangentSpaceAt α →ₗ[ℝ] V.V α} (hL : L ∈ Q.linSetAt f hf α hΨ x hx) :
    linPush φ hs ht L ∈ Q.linSetAt f hf α' hΨ' x' hx' := by
  obtain ⟨s, hsP, h0, rfl⟩ := hL
  set a := S.morTr (Ψ := Q.baseUnif Ψ) (Ψ' := Q.baseUnif Ψ') (Ψ.1.base.P.levelVal 1 x) φ
    (Ψ'.1.base.P.levelVal 1 x') hx hs hx' ht
  obtain ⟨s', hs', h0', hlin⟩ := Q.exists_linZeroAt_transAct_hyp hT Ψ Ψ' a (hf α Ψ.1 hΨ)
    (hf α' Ψ'.1 hΨ') (x := x) (y := x') rfl rfl hsP h0
  refine ⟨s', hs', h0', LinearMap.ext fun e' => objMk_eq_iff.1 ?_⟩
  obtain ⟨e, rfl⟩ : ∃ e, e' = S.tangentMorCLE φ hs ht e :=
    ⟨(S.tangentMorCLE φ hs ht).symm e', (ContinuousLinearEquiv.apply_symm_apply _ _).symm⟩
  rw [objMk_linOp, tangentChartCLE_tangentMorCLE φ hs ht (Q.baseUnif Ψ) (Q.baseUnif Ψ') x hx x'
    hx' e, hlin]
  change V.objMk α' (V.morFiber φ hs ht (Q.linOp f hf α hΨ x hx hsP h0
    ((S.tangentMorCLE φ hs ht).symm (S.tangentMorCLE φ hs ht e)))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply, ← act_objMk_morFiber φ hs ht _ hs.symm]
  erw [obj_transAct]
  exact act_congr rfl (Q.objMk_linOp hf α hΨ x hx hsP h0 e) _ _

/-- **Definition 18.1.4, "`φ_*` maps `Lin(f, α)` into `Lin(f, α')`"** (under
`HasTransportedScPlusSections`, for `F̄(α') ≠ ∅`). -/
theorem linPush_mem_linSet_hyp (hT : Q.HasTransportedScPlusSections)
    (hf : Q.IsScSmoothSectionFunctor f) {α α' : C.Obj} [Fact (S.TangentObj α)]
    [hα' : Fact (S.TangentObj α')] (φ : C.Mor) (hs : C.toGroupoidStr.src φ = α)
    (ht : C.toGroupoidStr.tgt φ = α') (hne' : (Q.F α').Nonempty)
    {L : S.TangentSpaceAt α →ₗ[ℝ] V.V α} (hL : L ∈ Q.linSet f hf α) :
    linPush φ hs ht L ∈ Q.linSet f hf α' := by
  obtain ⟨Ψ, hΨ, x, hx, hL⟩ := (Q.mem_linSet_iff hf α L).1 hL
  exact (Q.mem_linSet_iff hf α' _).2 ⟨Q.refBundleUnif hne', Q.refBundleUnif_mem hne', _,
    Q.obj_refBundlePoint hα'.out.1 hne', Q.linPush_mem_linSetAt_hyp hT hf φ hs ht hΨ
      (Q.refBundleUnif_mem hne') x hx _ _ hL⟩

/-- **Definition 18.1.4, p. 845, its further claims** (under `HasTransportedScPlusSections`):
`Lin(f, α)` is the set read through any `Ψ̄ ∈ F̄(α)`; its elements have finite index, all the
same; and `φ_*` maps `Lin(f, α)` into `Lin(f, α')` for `φ : α → α'` with `F̄(α') ≠ ∅`. -/
theorem definition_18_1_4_hyp (hT : Q.HasTransportedScPlusSections)
    (hF : Q.IsScFredholmSectionFunctor f) (α : C.Obj) [Fact (S.TangentObj α)] :
    (∀ (Ψ : Q.Unif) (hΨ : Ψ.1 ∈ Q.F α) (x : Ψ.1.base.P.Level 1)
        (hx : Ψ.1.base.obj (Ψ.1.base.P.levelVal 1 x) = α),
        Q.linSet f hF.isScSmoothSectionFunctor α =
          Q.linSetAt f hF.isScSmoothSectionFunctor α hΨ x hx) ∧
      (∃ i : ℤ, ∀ L ∈ Q.linSet f hF.isScSmoothSectionFunctor α,
        HasFiniteIndex L ∧ linIndex L = i) ∧
      ∀ (α' : C.Obj) [Fact (S.TangentObj α')] (φ : C.Mor) (hs : C.toGroupoidStr.src φ = α)
        (ht : C.toGroupoidStr.tgt φ = α'), (Q.F α').Nonempty →
        ∀ L ∈ Q.linSet f hF.isScSmoothSectionFunctor α,
          linPush φ hs ht L ∈ Q.linSet f hF.isScSmoothSectionFunctor α' :=
  ⟨fun _ hΨ x hx => Q.linSet_eq_linSetAt_hyp hT _ α hΨ x hx, Q.exists_index_linSet_hyp hT hF α,
    fun _ _ φ hs ht hne' _ hL => Q.linPush_mem_linSet_hyp hT _ φ hs ht hne' hL⟩

end GCT.VectorBundle.StrongPolyfoldBundleConstruction

end Polyfold
