import Polyfold.Chapter2.StrongBundleOne
import Polyfold.Chapter2.TangentMap
import Polyfold.Chapter5.BumpFunctions

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2017, arXiv 1707.08941), Part II, §8.3,
pp. 270–275: the infrastructure behind "`µ : 𝐗 ₛ×_P W → W` a strong bundle map covering the
target map `t`" in the definition of strong bundles over ep-groupoids (Definitions 8.4–8.5):
global strong bundle maps between strong bundles over M-polyfolds, and the pull-back strong
bundle `𝐗 ₛ×_P W` along the source map as a usable object.  Built on Part I's Definitions
2.22–2.28 [2.47–2.53] and Proposition 2.16 [2.54].

# Strong bundle maps and the pull-back strong bundle

## The text, paraphrased

(§8.3) A strong bundle over an ep-groupoid `X` consists of a strong M-polyfold bundle
`P : W → X` over the object M-polyfold and a map `µ : 𝐗 ₛ×_P W → W`, defined on "the pull-back of
a strong M-polyfold bundle" `P` along the source map `s : 𝐗 → X` (Part I's Definition 2.28 [2.53]
and Proposition 2.16 [2.54]), which is a strong bundle map covering the target map `t`, with
(1) `µ` a surjective local sc-diffeomorphism, linear on the fibres, (2) `µ(1_x, w) = w`,
(3) `µ(ψ ∘ γ, w) = µ(ψ, µ(γ, w))` (Definition 8.4, p. 271).
Part I defines strong bundle maps only between the local models
`U ◁ F → U' ◁ F'` (Definition 2.22 [2.47]: preserving the double filtration, linear on the fibres,
sc-smooth on `[0]` and `[1]`); the text uses the global notion without defining it.

## What is formalized

* **The pull-back bundle** is Part I's `Polyfold.StrongBundle.pullback B hf`
  (`Chapter3/ParamPerturbation.lean`: Proposition 2.16 [2.54] as a definition, atlas
  `pullbackAtlas B hf`), with the paracompactness of `f*Y` as an instance argument.  The
  pattern is `have := B.paracompactSpace_pullback PZ f` in a proof (`haveI` in a definition;
  `StrongBundle.paracompactSpace_pullback`, Part I's `paracompactSpace_pullbackSpace`), then
  `B.pullback hf`.  Here:
  `StrongBundle.pullback_atlas`, `toChart_mem_pullback_atlas`, `PullbackChartData.exists_mem_atlas`
  (every point of `f*Y` lies in a pulled-back chart through a chart of the atlas of `Y`),
  `PullbackChartData.isScSmoothRetractMap_gPair`, `isScSmoothRetractMap_gPairOne`
  (`(w, h) ↦ (g(w), h) : K_g[i] → K[i]` is sc-smooth).
* **The projections**: `StrongBundle.isScSmoothMap_pullbackProj` (`P_f : f*Y[0] → Z`) and
  `StrongBundle.isScSmoothMap_pullbackProj'` (`P' : f*Y[0] → Y[0]`).
* **The universal property**: `StrongBundle.isScSmoothOn_to_pullback` (a map into `f*Y[0]` is
  sc-smooth on an open set when its two components are), `isScSmoothOn_to_pullback_iff`,
  `isScSmoothOn_to_pullback_of_eqOn`, `isScSmoothMap_to_pullback`, and
  `isScSmoothMap_pullbackPair` (`v ↦ (a(v), b(v))`, `Polyfold.pullbackPair`).
* **Along a local sc-diffeomorphism** (the case `f = s` of §8.3):
  `StrongBundle.isScDiffeoOn_pullbackProj'` (over a sheet `f|_U : U → V` with inverse `σ`, `P'` is
  an sc-diffeomorphism `P_f⁻¹(U) → P⁻¹(V)` with inverse `w ↦ (σ(P w), w)`,
  `Polyfold.pullbackSheetInv`) and `StrongBundle.isLocalScDiffeo_pullbackProj'`.
* **Global strong bundle maps** (a reading, below): `StrongBundle.IsStrongBundleMap B B' f Φ`, with
  the fibre maps `Polyfold.fiberRestrict`, `IsStrongBundleMap.fiberLinearMap`,
  `IsStrongBundleMap.fiberMap` (bounded linear `P⁻¹(x) → P'⁻¹(f(x))`), the induced map
  `StrongBundle.oneRestrict : Y[1] → Y'[1]`; `IsStrongBundleMap.continuous`,
  `IsStrongBundleMap.isScSmoothMap_base` (the base map is sc-smooth), `IsStrongBundleMap.id`,
  `IsStrongBundleMap.comp`.
* **The double filtration**: `StrongBundle.mem_levelSet0_iff_mem_doubleLevel` (`Y[0]_m = Y_{m,m}`),
  `mem_levelSet1_iff_mem_doubleLevel` (`Y[1]_m = Y_{m,m+1}`), `zero_mem_doubleLevel`, and
  `IsStrongBundleMap.mapsTo_doubleLevel` (**a strong bundle map preserves `Y_{m,k}`,
  `k ≤ m + 1`**).
* **Strong bundle isomorphisms**: `StrongBundle.IsStrongBundleIso` with `refl`, `symm`, `trans`,
  `base_left_inv`, `base_right_inv`.
* **`P'` is a strong bundle map covering `f`**: `StrongBundle.mem_oneSet_pullback_iff`
  (`(f*Y)_{0,1} = {(z, y) | y ∈ Y_{0,1}}`), `mapsTo_oneSet_pullbackProj'`,
  `isScSmoothMap_one_pullbackProj'` (`P'[1] : f*Y[1] → Y[1]` sc-smooth),
  `isStrongBundleMap_pullbackProj'`, and `fiberMap_pullbackProj'` (its fibre maps are Part I's
  `pullbackFiberCLE`).
* `Polyfold.MPolyfold.isScSmoothMap_of_forall_charts`: Definition 2.9 [2.14] checked on whole chart
  domains, with continuity read off from the charts.

## What the text leaves implicit, and the choices made

* **"Strong bundle map covering `t`" between strong bundles over M-polyfolds** is read as
  `StrongBundle.IsStrongBundleMap B B' f Φ` for `B : P : Y → X`, `B' : P' : Y' → X'`,
  `f : X → X'`, `Φ : Y → Y'`: (i) `P' ∘ Φ = f ∘ P`; (ii) `Φ` is linear on the fibres, i.e. the
  restrictions `P⁻¹(x) → P'⁻¹(f(x))` (`fiberRestrict`) are linear for the fibre structures of the
  strong bundles; (iii) `Φ : Y[0] → Y'[0]` is sc-smooth; (iv) `Φ(Y_{0,1}) ⊆ Y'_{0,1}` and the
  induced `Y[1] → Y'[1]` is sc-smooth.  This is the global form of Definition 2.22 [2.47], in the
  way Definition 2.25 [2.50] treats the transition maps: in the charts, (iii) and (iv) say that the
  local representatives `K[i] → K'[i]` are sc-smooth.  Preservation of the double filtration,
  part of Definition 2.22 [2.47], is not assumed: it follows (`mapsTo_doubleLevel`; for `k ≤ m`
  from (iii) on `Y_{k,k}` and at the zero of the fibre, for `k = m + 1` from (iv)).  Boundedness of
  the fibre maps follows from (iii) (`fiberMap`), and so does the sc-smoothness of the base map `f`
  (`isScSmoothMap_base`: `f = P' ∘ Φ ∘ 0` with the zero section).
* A strong bundle isomorphism (`IsStrongBundleIso`) is a pair of strong bundle maps inverse to each
  other; this extends Part I's local `Polyfold.IsStrongBundleIso` (Chapter 3) to strong bundles.
* The paracompactness of `f*Y` (Definition 2.26 [2.51] requires a paracompact total space) is an
  instance argument, as in Part I; it is a `Prop`, so the instance supplied by
  `paracompactSpace_pullback` agrees with any other.
* The inverse `w ↦ (σ(P w), w)` of `P'` over a sheet takes a junk value off `P⁻¹(V)`.

## Elsewhere, and not formalized

* Strong bundle maps defined on an open subset of the base are not formalized here (they would be
  strong bundle maps on the restrictions `StrongBundle.restrictOpen` of
  `Chapter3/RestrictOpen.lean`).
-/

open Set Filter Topology Function TopologicalSpace

noncomputable section

namespace Polyfold

universe u v w

/-! ### Maps into the pull-back -/

section Lift

variable {X Y Z V : Type*} (P : Y → X) (f : Z → X)

/-- The map `v ↦ (a(v), b(v))` into the pull-back `f*Y`, for `P ∘ b = f ∘ a`.  (Part I's
`pullbackLift f τ hτ` is `pullbackPair P f id τ hτ`.) -/
def pullbackPair (a : V → Z) (b : V → Y) (hab : ∀ v, P (b v) = f (a v)) :
    V → pullbackSpace P f :=
  fun v => ⟨(a v, b v), hab v⟩

@[simp] lemma pullbackPair_val (a : V → Z) (b : V → Y) (hab : ∀ v, P (b v) = f (a v)) (v : V) :
    (pullbackPair P f a b hab v : Z × Y) = (a v, b v) := rfl

open scoped Classical in
/-- The inverse `w ↦ (σ(P w), w)` of `P' : f*Y → Y` over a sheet of `f` with inverse
`σ : V → Z` (`f ∘ σ = id` on `V`); junk value `q₀` off `P⁻¹(V)`. -/
def pullbackSheetInv (σ : X → Z) (W : Set X) (hσ : ∀ x ∈ W, f (σ x) = x)
    (q₀ : pullbackSpace P f) (w : Y) : pullbackSpace P f :=
  if h : P w ∈ W then ⟨(σ (P w), w), (hσ (P w) h).symm⟩ else q₀

lemma pullbackSheetInv_val {σ : X → Z} {W : Set X} (hσ : ∀ x ∈ W, f (σ x) = x)
    (q₀ : pullbackSpace P f) {w : Y} (hw : P w ∈ W) :
    (pullbackSheetInv P f σ W hσ q₀ w : Z × Y) = (σ (P w), w) := by
  unfold pullbackSheetInv; rw [dif_pos hw]

end Lift

/-! ### Locality of sc-smoothness on whole chart domains -/

namespace MPolyfold

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {PY : MPolyfold Y}

/-- The locality of Definition 2.9 [2.14] with whole chart domains: `f` is sc-smooth if every point
lies in the domain of a chart `φ` with `f(dom φ) ⊆ dom ψ` and `ψ ∘ f ∘ φ⁻¹ : O → O'` sc-smooth
(the continuity of `f` follows from the charts). -/
theorem isScSmoothMap_of_forall_charts {f : X → Y}
    (h : ∀ x, ∃ (φ : MChart X) (ψ : MChart Y), PX.IsChart φ ∧ PY.IsChart ψ ∧ x ∈ φ.source ∧
      MapsTo f φ.source ψ.source ∧
      IsScSmoothRetractMap φ.model.E φ.model.C φ.model.O ψ.model.E ψ.model.C ψ.model.O
        (ψ ∘ f ∘ φ.symm)) :
    PX.IsScSmoothMap PY f := by
  have hloc : ∀ x, ∃ φ : MChart X, x ∈ φ.source ∧ ContinuousOn f φ.source := fun x => by
    obtain ⟨φ, ψ, -, -, hx, hmaps, hsm⟩ := h x
    refine ⟨φ, hx, ?_⟩
    have h1 : ContinuousOn (ψ.symm ∘ (ψ ∘ f ∘ φ.symm) ∘ φ) φ.source :=
      (ψ.continuousOn_invFun.comp (hsm.continuousOn φ.model.isScRetract) hsm.mapsTo).comp
        φ.continuousOn_toFun fun z hz => φ.mapsTo_model z hz
    refine h1.congr fun z hz => ?_
    simp only [Function.comp_apply, φ.symm_apply_apply hz, ψ.symm_apply_apply (hmaps hz)]
  have hc : Continuous f := continuous_iff_continuousAt.2 fun x => by
    obtain ⟨φ, hx, hcont⟩ := hloc x
    exact hcont.continuousAt (φ.isOpen_source.mem_nhds hx)
  refine IsScSmoothOn.of_exists_charts isOpen_univ hc.continuousOn fun x _ => ?_
  obtain ⟨φ, ψ, hφ, hψ, hx, hmaps, hsm⟩ := h x
  refine ⟨φ, ψ, φ.source, hφ, hψ, φ.isOpen_source, hx, fun z hz => ⟨mem_univ _, hz⟩, hmaps, ?_⟩
  rw [φ.image_source]; exact hsm

end MPolyfold

/-! ### The pull-back strong bundle -/

section Pullback

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {Z : Type w} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {PZ : MPolyfold Z}
  {f : Z → X}

namespace PullbackChartData

/-- Every point of `f*Y` lies in the domain of a pulled-back chart `d.toChart q₀` with `d.c` in the
atlas of `Y`. -/
theorem exists_mem_atlas [T2Space Y] [ParacompactSpace Y] (B : StrongBundle PX P)
    (hf : PZ.IsScSmoothMap PX f) (q : pullbackSpace P f) :
    ∃ d : PullbackChartData PX P PZ f, d.c ∈ B.atlas.charts ∧ (q : Z × Y).1 ∈ d.ψ.source := by
  obtain ⟨c, hc, hy⟩ := B.atlas.cover (q : Z × Y).2
  have hfz : f (q : Z × Y).1 ∈ c.φ.source := by
    rw [c.source_eq, mem_preimage, show P (q : Z × Y).2 = f (q : Z × Y).1 from q.2] at hy
    exact hy
  obtain ⟨d, rfl, hz⟩ := exists_pullbackChartData hf c hfz
  exact ⟨d, hc, hz⟩

variable (d : PullbackChartData PX P PZ f) (q₀ : pullbackSpace P f)

lemma toChart_K : (d.toChart q₀).K = d.Kg := d.image_eq_Kg

/-- `G(w, h) = (g(w), h) : K_g → K` is sc-smooth. -/
theorem isScSmoothRetractMap_gPair :
    IsScSmoothRetractMap (d.ψ.model.E.prod d.c.F) (d.ψ.model.C ×ˢ univ) (d.toChart q₀).K
      (d.c.φ.model.E.prod d.c.F) (d.c.φ.model.C ×ˢ univ) d.c.K d.gPair := by
  have hK := (d.toChart q₀).isScRetract
  have hfstR : IsScSmoothRetractMap (d.ψ.model.E.prod d.c.F) (d.ψ.model.C ×ˢ univ)
      (d.toChart q₀).K d.ψ.model.E d.ψ.model.C d.RZ.retract Prod.fst :=
    (d.ψ.model.E.prodFstOp d.c.F).isScSmoothRetractMap hK fun k hk => by
      rw [toChart_K] at hk; exact hk.1
  have hg := d.g_smooth.comp hfstR ⟨d.RZ, rfl⟩
  have hsnd : IsScSmoothRetractMap (d.ψ.model.E.prod d.c.F) (d.ψ.model.C ×ˢ univ)
      (d.toChart q₀).K d.c.F univ univ Prod.snd :=
    (d.ψ.model.E.prodSndOp d.c.F).isScSmoothRetractMap hK (mapsTo_univ _ _)
  exact IsScSmoothRetractMap.scPair hg hsnd fun k hk => by
    rw [toChart_K] at hk; exact hk.2

/-- `G[1](w, h) = (g(w), h) : K_g[1] → K[1]` is sc-smooth. -/
theorem isScSmoothRetractMap_gPairOne :
    IsScSmoothRetractMap (d.ψ.model.E.prod d.c.F.shift) (d.ψ.model.C ×ˢ univ)
      (strongShiftOne (d.toChart q₀).K) (d.c.φ.model.E.prod d.c.F.shift)
      (d.c.φ.model.C ×ˢ univ) (strongShiftOne d.c.K) d.gPairOne := by
  have hK := (d.toChart q₀).isScRetract_one
  have hfstR : IsScSmoothRetractMap (d.ψ.model.E.prod d.c.F.shift) (d.ψ.model.C ×ˢ univ)
      (strongShiftOne (d.toChart q₀).K) d.ψ.model.E d.ψ.model.C d.RZ.retract Prod.fst :=
    (d.ψ.model.E.prodFstOp d.c.F.shift).isScSmoothRetractMap hK fun p hp => by
      have hp' : (p.1, d.c.F.toBase 1 p.2) ∈ (d.toChart q₀).K := hp
      rw [toChart_K] at hp'; exact hp'.1
  have hg := d.g_smooth.comp hfstR ⟨d.RZ, rfl⟩
  have hsnd : IsScSmoothRetractMap (d.ψ.model.E.prod d.c.F.shift) (d.ψ.model.C ×ˢ univ)
      (strongShiftOne (d.toChart q₀).K) d.c.F.shift univ univ Prod.snd :=
    (d.ψ.model.E.prodSndOp d.c.F.shift).isScSmoothRetractMap hK (mapsTo_univ _ _)
  exact IsScSmoothRetractMap.scPair hg hsnd fun p hp => by
    have hp' : (p.1, d.c.F.toBase 1 p.2) ∈ (d.toChart q₀).K := hp
    rw [toChart_K] at hp'; exact hp'.2

end PullbackChartData

variable [T2Space Y] [ParacompactSpace Y]

namespace StrongBundle

variable (B : StrongBundle PX P)

include B in
/-- `f*Y` is paracompact (Part I's `paracompactSpace_pullbackSpace`, by Theorem 2.2 [2.16]); use
`have := B.paracompactSpace_pullback PZ f` (`haveI` in a definition) before `B.pullback hf`. -/
theorem paracompactSpace_pullback (PZ : MPolyfold Z) (f : Z → X) :
    ParacompactSpace (pullbackSpace P f) :=
  paracompactSpace_pullbackSpace PZ B

variable [ParacompactSpace (pullbackSpace P f)] (hf : PZ.IsScSmoothMap PX f)

lemma pullback_atlas : (B.pullback hf).atlas = pullbackAtlas B hf := rfl

lemma toChart_mem_pullback_atlas {d : PullbackChartData PX P PZ f} (hd : d.c ∈ B.atlas.charts)
    (q₀ : pullbackSpace P f) : d.toChart q₀ ∈ (B.pullback hf).atlas.charts :=
  ⟨d, q₀, hd, rfl⟩

/-- `P_f : f*Y[0] → Z` is sc-smooth (Part I's `isScSmoothMap_proj` for the pull-back bundle). -/
theorem isScSmoothMap_pullbackProj :
    (B.pullback hf).toMPolyfold0.IsScSmoothMap PZ (pullbackProj P f) :=
  (B.pullback hf).isScSmoothMap_proj

/-- `P' : f*Y[0] → Y[0]`, `(z, y) ↦ y`, is sc-smooth: in the charts `Φ_f` and `Φ` it is
`(w, h) ↦ (g(w), h)`. -/
theorem isScSmoothMap_pullbackProj' :
    (B.pullback hf).toMPolyfold0.IsScSmoothMap B.toMPolyfold0 (pullbackProj' P f) := by
  refine MPolyfold.IsScSmoothOn.of_exists_charts isOpen_univ
    (continuous_snd.comp continuous_subtype_val).continuousOn fun q _ => ?_
  obtain ⟨d, hd, hq⟩ := PullbackChartData.exists_mem_atlas B hf q
  have hmem := B.toChart_mem_pullback_atlas hf hd q
  refine ⟨(d.toChart q).toMChart (B.pullback hf).continuous, d.c.toMChart B.continuous,
    (d.toChart q).toPartialEquiv.source, (B.pullback hf).isChart_toMChart hmem,
    B.isChart_toMChart hd, (d.toChart q).isOpen_source (B.pullback hf).continuous, hq,
    fun z hz => ⟨mem_univ _, hz⟩, fun z hz => d.mem_c_source hz, ?_⟩
  have h := d.isScSmoothRetractMap_gPair q
  rw [← (d.toChart q).image_source] at h
  refine h.congr fun k hk => ?_
  rw [(d.toChart q).image_source] at hk
  have hk' : k ∈ d.Kg := by rw [← d.toChart_K q]; exact hk
  change d.gPair k = d.c ((d.invFun q k : Z × Y).2)
  rw [d.invFun_of_mem q hk']
  exact (d.c.toPartialEquiv.right_inv (by rw [d.c.target_eq]; exact hk'.2)).symm

/-! ### The universal property -/

section Universal

variable {V : Type*} [TopologicalSpace V] [T2Space V] [ParacompactSpace V] {Q : MPolyfold V}

/-- **The universal property of the pull-back**, on an open set: a map `ι : V → f*Y` is sc-smooth
on `U` as soon as its components `P_f ∘ ι : V → Z` and `P' ∘ ι : V → Y[0]` are (in the charts,
`Φ_f ∘ ι = (ψ ∘ P_f ∘ ι, pr_F Φ ∘ P' ∘ ι)`). -/
theorem isScSmoothOn_to_pullback {ι : V → pullbackSpace P f} {U : Set V}
    (ha : Q.IsScSmoothOn PZ (pullbackProj P f ∘ ι) U)
    (hb : Q.IsScSmoothOn B.toMPolyfold0 (pullbackProj' P f ∘ ι) U) :
    Q.IsScSmoothOn (B.pullback hf).toMPolyfold0 ι U := by
  have hcont : ContinuousOn ι U := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    exact ha.continuousOn.prodMk hb.continuousOn
  refine MPolyfold.IsScSmoothOn.of_exists_charts ha.isOpen hcont fun v hv => ?_
  obtain ⟨d, hd, hq⟩ := PullbackChartData.exists_mem_atlas B hf (ι v)
  have hmem := B.toChart_mem_pullback_atlas hf hd (ι v)
  obtain ⟨φ, hφ, hvφ⟩ := Q.exists_isChart_mem_source v
  set W := (U ∩ φ.source) ∩ (pullbackProj P f ∘ ι) ⁻¹' d.ψ.source with hW
  have hWo : IsOpen W := (ha.continuousOn.mono inter_subset_left).isOpen_inter_preimage
    (ha.isOpen.inter φ.isOpen_source) d.ψ.isOpen_source
  refine ⟨φ, (d.toChart (ι v)).toMChart (B.pullback hf).continuous, W, hφ,
    (B.pullback hf).isChart_toMChart hmem, hWo, ⟨⟨hv, hvφ⟩, hq⟩, fun x hx => hx.1,
    fun x hx => hx.2, ?_⟩
  have h1 := ha.smooth φ d.ψ hφ d.isChart W hWo (fun x hx => hx.1) fun x hx => hx.2
  have h2 := hb.smooth φ (d.c.toMChart B.continuous) hφ (B.isChart_toMChart hd) W hWo
    (fun x hx => hx.1) fun x hx => d.mem_c_source hx.2
  have h3 : IsScSmoothRetractMap (d.c.φ.model.E.prod d.c.F) (d.c.φ.model.C ×ˢ univ) d.c.K
      d.c.F univ univ Prod.snd :=
    (d.c.φ.model.E.prodSndOp d.c.F).isScSmoothRetractMap d.c.isScRetract (mapsTo_univ _ _)
  have h4 := h3.comp h2 d.c.isScRetract
  refine (IsScSmoothRetractMap.scPair h1 h4 ?_).congr fun _ _ => rfl
  rintro _ ⟨x, hx, rfl⟩
  change ((d.ψ ((ι (φ.symm (φ x))) : Z × Y).1, (d.c ((ι (φ.symm (φ x))) : Z × Y).2).2)) ∈
    (d.toChart (ι v)).K
  rw [φ.symm_apply_apply hx.1.2, ← (d.toChart (ι v)).image_source]
  exact ⟨ι x, hx.2, rfl⟩

/-- **The universal property of the pull-back**: a map `ι : V → f*Y` is sc-smooth as soon as its
components `P_f ∘ ι` and `P' ∘ ι` are. -/
theorem isScSmoothMap_to_pullback {ι : V → pullbackSpace P f}
    (ha : Q.IsScSmoothMap PZ (pullbackProj P f ∘ ι))
    (hb : Q.IsScSmoothMap B.toMPolyfold0 (pullbackProj' P f ∘ ι)) :
    Q.IsScSmoothMap (B.pullback hf).toMPolyfold0 ι :=
  B.isScSmoothOn_to_pullback hf ha hb

/-- A map into `f*Y[0]` is sc-smooth on `U` iff its two components are. -/
theorem isScSmoothOn_to_pullback_iff {ι : V → pullbackSpace P f} {U : Set V} :
    Q.IsScSmoothOn (B.pullback hf).toMPolyfold0 ι U ↔
      Q.IsScSmoothOn PZ (pullbackProj P f ∘ ι) U ∧
        Q.IsScSmoothOn B.toMPolyfold0 (pullbackProj' P f ∘ ι) U :=
  ⟨fun h => ⟨MPolyfold.IsScSmoothOn.comp (B.isScSmoothMap_pullbackProj hf) h (mapsTo_univ _ _),
    MPolyfold.IsScSmoothOn.comp (B.isScSmoothMap_pullbackProj' hf) h (mapsTo_univ _ _)⟩,
    fun h => B.isScSmoothOn_to_pullback hf h.1 h.2⟩

/-- The universal property with prescribed components: if `ι(v) = (a(v), b(v))` on `U` with `a`,
`b` sc-smooth on `U`, then `ι` is sc-smooth on `U`. -/
theorem isScSmoothOn_to_pullback_of_eqOn {ι : V → pullbackSpace P f} {U : Set V} {a : V → Z}
    {b : V → Y} (ha : Q.IsScSmoothOn PZ a U) (hb : Q.IsScSmoothOn B.toMPolyfold0 b U)
    (hι : ∀ v ∈ U, (ι v : Z × Y) = (a v, b v)) :
    Q.IsScSmoothOn (B.pullback hf).toMPolyfold0 ι U :=
  B.isScSmoothOn_to_pullback hf (ha.congr fun v hv => (congrArg Prod.fst (hι v hv)).symm)
    (hb.congr fun v hv => (congrArg Prod.snd (hι v hv)).symm)

/-- **The universal property of the pull-back**: for sc-smooth `a : V → Z` and `b : V → Y[0]` with
`P ∘ b = f ∘ a`, the map `v ↦ (a(v), b(v))` into `f*Y[0]` is sc-smooth. -/
theorem isScSmoothMap_pullbackPair {a : V → Z} {b : V → Y} (ha : Q.IsScSmoothMap PZ a)
    (hb : Q.IsScSmoothMap B.toMPolyfold0 b) (hab : ∀ v, P (b v) = f (a v)) :
    Q.IsScSmoothMap (B.pullback hf).toMPolyfold0 (pullbackPair P f a b hab) :=
  B.isScSmoothMap_to_pullback hf ha hb

end Universal

/-! ### The pull-back along a local sc-diffeomorphism -/

/-- Over a sheet `f|_U : U → V` of `f` with inverse `σ`, `P' : f*Y[0] → Y[0]` is an
sc-diffeomorphism `P_f⁻¹(U) → P⁻¹(V)` with inverse `w ↦ (σ(P w), w)`. -/
theorem isScDiffeoOn_pullbackProj' {σ : X → Z} {U : Set Z} {W : Set X}
    (hd : PZ.IsScDiffeoOn PX f σ U W) (q₀ : pullbackSpace P f) :
    (B.pullback hf).toMPolyfold0.IsScDiffeoOn B.toMPolyfold0 (pullbackProj' P f)
      (pullbackSheetInv P f σ W hd.right_inv q₀) (pullbackProj P f ⁻¹' U) (P ⁻¹' W) where
  isScSmoothOn := (B.isScSmoothMap_pullbackProj' hf).mono
    (hd.isScSmoothOn.isOpen.preimage (continuous_pullbackProj P f)) (subset_univ _)
  isScSmoothOn_inv := by
    have hWo : IsOpen (P ⁻¹' W) := hd.isScSmoothOn_inv.isOpen.preimage B.continuous
    have ha : B.toMPolyfold0.IsScSmoothOn PZ (σ ∘ P) (P ⁻¹' W) :=
      MPolyfold.IsScSmoothOn.comp hd.isScSmoothOn_inv
        (B.isScSmoothMap_proj.mono hWo (subset_univ _)) fun w hw => hw
    have hb : B.toMPolyfold0.IsScSmoothOn B.toMPolyfold0 id (P ⁻¹' W) :=
      MPolyfold.isScSmoothMap_id.mono hWo (subset_univ _)
    exact B.isScSmoothOn_to_pullback_of_eqOn hf ha hb fun w hw =>
      pullbackSheetInv_val P f hd.right_inv q₀ hw
  mapsTo q hq := by
    change P (q : Z × Y).2 ∈ W
    rw [show P (q : Z × Y).2 = f (q : Z × Y).1 from q.2]; exact hd.mapsTo hq
  mapsTo_inv w hw := by
    change (pullbackSheetInv P f σ W hd.right_inv q₀ w : Z × Y).1 ∈ U
    rw [pullbackSheetInv_val P f hd.right_inv q₀ hw]; exact hd.mapsTo_inv hw
  left_inv q hq := by
    have hPq : P (q : Z × Y).2 ∈ W := by
      rw [show P (q : Z × Y).2 = f (q : Z × Y).1 from q.2]; exact hd.mapsTo hq
    apply Subtype.ext
    change (pullbackSheetInv P f σ W hd.right_inv q₀ (q : Z × Y).2 : Z × Y) = (q : Z × Y)
    rw [pullbackSheetInv_val P f hd.right_inv q₀ hPq,
      show P (q : Z × Y).2 = f (q : Z × Y).1 from q.2, hd.left_inv (q : Z × Y).1 hq]
  right_inv w hw := by
    change (pullbackSheetInv P f σ W hd.right_inv q₀ w : Z × Y).2 = w
    rw [pullbackSheetInv_val P f hd.right_inv q₀ hw]

/-- **The pull-back along a local sc-diffeomorphism** (the case `f = s : 𝐗 → X` of §8.3):
`P' : f*Y[0] → Y[0]` is a local sc-diffeomorphism. -/
theorem isLocalScDiffeo_pullbackProj' (hl : PZ.IsLocalScDiffeo PX f) :
    (B.pullback hf).toMPolyfold0.IsLocalScDiffeo B.toMPolyfold0 (pullbackProj' P f) := fun q => by
  obtain ⟨U, W, σ, hz, hd⟩ := hl (q : Z × Y).1
  exact ⟨_, _, _, hz, B.isScDiffeoOn_pullbackProj' hf hd q⟩

end StrongBundle

end Pullback

/-! ### Strong bundle maps between strong bundles over M-polyfolds -/

section Maps

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {X' : Type*} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type*} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]
  {X'' : Type*} [TopologicalSpace X''] [T2Space X''] [ParacompactSpace X''] {PX'' : MPolyfold X''}
  {Y'' : Type*} [TopologicalSpace Y''] [T2Space Y''] [ParacompactSpace Y''] {P'' : Y'' → X''}
  [∀ x, AddCommGroup (P'' ⁻¹' {x})] [∀ x, Module ℝ (P'' ⁻¹' {x})]

/-- The fibre map `P⁻¹(x) → P'⁻¹(f(x))`, `v ↦ Φ(v)`, of a map `Φ : Y → Y'` covering `f`. -/
def fiberRestrict {X Y X' Y' : Type*} (P : Y → X) (P' : Y' → X') (f : X → X') (Φ : Y → Y')
    (hΦ : ∀ y, P' (Φ y) = f (P y)) (x : X) : P ⁻¹' {x} → P' ⁻¹' {f x} :=
  fun v => ⟨Φ v, show P' (Φ v) = f x from (hΦ v).trans (congrArg f v.2)⟩

@[simp] lemma fiberRestrict_val {X Y X' Y' : Type*} {P : Y → X} {P' : Y' → X'} {f : X → X'}
    {Φ : Y → Y'} (hΦ : ∀ y, P' (Φ y) = f (P y)) (x : X) (v : P ⁻¹' {x}) :
    (fiberRestrict P P' f Φ hΦ x v : Y') = Φ v := rfl

namespace StrongBundle

/-- The map `Y[1] → Y'[1]` induced by a map `Φ : Y → Y'` with `Φ(Y_{0,1}) ⊆ Y'_{0,1}`. -/
def oneRestrict (B : StrongBundle PX P) (B' : StrongBundle PX' P') (Φ : Y → Y')
    (hΦ : MapsTo Φ B.oneSet B'.oneSet) : B.One → B'.One :=
  fun y => B'.oneMk (Φ (B.oneVal y)) (hΦ (B.oneVal_mem y))

@[simp] lemma oneVal_oneRestrict (B : StrongBundle PX P) (B' : StrongBundle PX' P') (Φ : Y → Y')
    (hΦ : MapsTo Φ B.oneSet B'.oneSet) (y : B.One) :
    B'.oneVal (oneRestrict B B' Φ hΦ y) = Φ (B.oneVal y) := rfl

/-- **A strong bundle map covering `f`** (a reading of §8.3's "strong bundle map covering `t`"):
`Φ : Y → Y'` with (i) `P' ∘ Φ = f ∘ P`, (ii) linear on the fibres, (iii) sc-smooth `Y[0] → Y'[0]`,
(iv) mapping `Y_{0,1}` into `Y'_{0,1}` with the induced map `Y[1] → Y'[1]` sc-smooth.  Part I
defines strong bundle maps only between local models (Definition 2.22 [2.47]); the preservation
of the double filtration required there follows from (i)–(iv)
(`IsStrongBundleMap.mapsTo_doubleLevel`). -/
structure IsStrongBundleMap (B : StrongBundle PX P) (B' : StrongBundle PX' P') (f : X → X')
    (Φ : Y → Y') : Prop where
  covers : ∀ y, P' (Φ y) = f (P y)
  fiber_linear : ∀ x, IsLinearMap ℝ (fiberRestrict P P' f Φ covers x)
  isScSmoothMap : B.toMPolyfold0.IsScSmoothMap B'.toMPolyfold0 Φ
  mapsTo_oneSet : MapsTo Φ B.oneSet B'.oneSet
  isScSmoothMap_one :
    B.toMPolyfold1.IsScSmoothMap B'.toMPolyfold1 (oneRestrict B B' Φ mapsTo_oneSet)

variable {B : StrongBundle PX P} {B' : StrongBundle PX' P'} {B'' : StrongBundle PX'' P''}
  {f : X → X'} {Φ : Y → Y'} {f' : X' → X''} {Ψ : Y' → Y''}

namespace IsStrongBundleMap

section Fiber

variable (h : B.IsStrongBundleMap B' f Φ)
include h

lemma continuous : Continuous Φ := continuousOn_univ.1 h.isScSmoothMap.continuousOn

/-- The fibre map `P⁻¹(x) → P'⁻¹(f(x))` of a strong bundle map, as a linear map. -/
def fiberLinearMap (x : X) : P ⁻¹' {x} →ₗ[ℝ] P' ⁻¹' {f x} := (h.fiber_linear x).mk'

/-- The fibre map `P⁻¹(x) → P'⁻¹(f(x))` of a strong bundle map: a bounded linear operator (its
continuity comes from that of `Φ`). -/
def fiberMap (x : X) : P ⁻¹' {x} →L[ℝ] P' ⁻¹' {f x} where
  toLinearMap := h.fiberLinearMap x
  cont := (h.continuous.comp continuous_subtype_val).subtype_mk _

@[simp] lemma fiberMap_apply (x : X) (v : P ⁻¹' {x}) : (h.fiberMap x v : Y') = Φ v := rfl

/-- The base map of a strong bundle map is sc-smooth: `f = P' ∘ Φ ∘ 0`, the zero section being an
sc⁺-section (`isScPlusSection_fiberZero`), hence sc-smooth into `Y[0]`. -/
theorem isScSmoothMap_base : PX.IsScSmoothMap PX' f := by
  obtain ⟨-, g, hg, hgs⟩ :=
    (B.isScPlusSection_iff (fiberZero P)).1 (StrongBundle.isScPlusSection_fiberZero (B := B))
  have h0 : PX.IsScSmoothMap B.toMPolyfold0 (fiberZero P) := by
    rw [← hg]; exact B.isScSmoothMap_oneVal.comp hgs
  refine ((B'.isScSmoothMap_proj.comp h.isScSmoothMap).comp h0).congr fun x _ => ?_
  change P' (Φ (fiberZero P x)) = f x
  rw [h.covers]; exact congrArg f (isSection_fiberZero x)

end Fiber

/-- Composition of strong bundle maps: `Ψ ∘ Φ` covers `f' ∘ f`. -/
theorem comp (h₂ : B'.IsStrongBundleMap B'' f' Ψ) (h₁ : B.IsStrongBundleMap B' f Φ) :
    B.IsStrongBundleMap B'' (f' ∘ f) (Ψ ∘ Φ) where
  covers y := (h₂.covers (Φ y)).trans (congrArg f' (h₁.covers y))
  fiber_linear x := ((h₂.fiberLinearMap (f x)).comp (h₁.fiberLinearMap x)).isLinear
  isScSmoothMap := h₂.isScSmoothMap.comp h₁.isScSmoothMap
  mapsTo_oneSet := h₂.mapsTo_oneSet.comp h₁.mapsTo_oneSet
  isScSmoothMap_one := h₂.isScSmoothMap_one.comp h₁.isScSmoothMap_one

end IsStrongBundleMap

variable (B) in
/-- The identity is a strong bundle map covering the identity. -/
theorem IsStrongBundleMap.id : B.IsStrongBundleMap B id id where
  covers _ := rfl
  fiber_linear _ := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  isScSmoothMap := MPolyfold.isScSmoothMap_id
  mapsTo_oneSet := mapsTo_id _
  isScSmoothMap_one := MPolyfold.isScSmoothMap_id

/-! ### The double filtration is preserved -/

variable (B) in
/-- `Y[0]_m = Y_{m,m}`: the levels of the M-polyfold `Y[0]` are the diagonal of the double
filtration. -/
theorem mem_levelSet0_iff_mem_doubleLevel (y : Y) (m : ℕ) :
    y ∈ B.toMPolyfold0.levelSet m ↔ y ∈ B.doubleLevel m m := by
  obtain ⟨c, hc, hy⟩ := B.atlas.cover y
  rw [B.toMPolyfold0.mem_levelSet_iff (B.isChart_toMChart hc) hy,
    B.mem_doubleLevel_iff hc hy (Nat.le_succ m)]
  change c y ∈ range ((c.φ.model.E.prod c.F).toBase m) ↔ _
  constructor
  · rintro ⟨w, hw⟩
    rw [ScBanach.prod_toBase] at hw
    exact ⟨⟨w.1, congrArg Prod.fst hw⟩, ⟨w.2, congrArg Prod.snd hw⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨((a, b) : (c.φ.model.E.prod c.F) m), by rw [ScBanach.prod_toBase]; exact Prod.ext ha hb⟩

variable (B) in
/-- `Y[1]_m = Y_{m,m+1}`: the levels of the M-polyfold `Y[1]`. -/
theorem mem_levelSet1_iff_mem_doubleLevel (y : B.One) (m : ℕ) :
    y ∈ B.toMPolyfold1.levelSet m ↔ B.oneVal y ∈ B.doubleLevel m (m + 1) := by
  obtain ⟨c, hc, hy⟩ := B.atlas.cover (B.oneVal y)
  have h1 : (c (B.oneVal y)).2 ∈ range (c.F.toBase 1) := (B.mem_oneSet_iff hc hy).1 (B.oneVal_mem y)
  rw [B.toMPolyfold1.mem_levelSet_iff (B.isChart_oneChart hc y)
    (show y ∈ (oneChart hc y).source from hy), B.mem_doubleLevel_iff hc hy le_rfl, oneChart_apply]
  change c.liftOne (B.oneVal y) ∈ range ((c.φ.model.E.prod c.F.shift).toBase m) ↔ _
  constructor
  · rintro ⟨w, hw⟩
    rw [ScBanach.prod_toBase] at hw
    refine ⟨⟨w.1, congrArg Prod.fst hw⟩, ⟨w.2, ?_⟩⟩
    rw [ScBanach.shiftScale_toBase c.F.toScScale m w.2]
    change c.F.toBase 1 (c.F.shift.toBase m w.2) = _
    rw [show c.F.shift.toBase m w.2 = (c.liftOne (B.oneVal y)).2 from congrArg Prod.snd hw]
    exact Function.invFun_eq h1
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨((a, b) : (c.φ.model.E.prod c.F.shift) m), ?_⟩
    rw [ScBanach.prod_toBase]
    refine Prod.ext ha (c.F.toBase_injective 1 ?_)
    change c.F.toBase 1 (c.F.shift.toBase m b) =
      c.F.toBase 1 (Function.invFun (c.F.toBase 1) (c (B.oneVal y)).2)
    rw [Function.invFun_eq h1, ← hb]
    exact (ScBanach.shiftScale_toBase c.F.toScScale m b).symm

/-- The zero of the fibre through a point of `Y_{m,k}` lies in `Y_{m,m}` (in a chart it is
`(φ(x), 0)`). -/
theorem zero_mem_doubleLevel {y : Y} {m k : ℕ} (hk : k ≤ m + 1) (hy : y ∈ B.doubleLevel m k) :
    ((0 : P ⁻¹' {P y}) : Y) ∈ B.doubleLevel m m := by
  obtain ⟨c, hc, hyc⟩ := B.atlas.cover y
  have hx : P y ∈ c.φ.source := by rw [c.source_eq] at hyc; exact hyc
  have hP0 : P ((0 : P ⁻¹' {P y}) : Y) = P y := (0 : P ⁻¹' {P y}).2
  have h0 : ((0 : P ⁻¹' {P y}) : Y) ∈ c.toPartialEquiv.source := by
    rw [c.source_eq, mem_preimage, hP0]; exact hx
  rw [B.mem_doubleLevel_iff hc h0 (Nat.le_succ m)]
  refine ⟨?_, ⟨0, ?_⟩⟩
  · rw [c.covers _ h0, hP0, ← c.covers _ hyc]
    exact ((B.mem_doubleLevel_iff hc hyc hk).1 hy).1
  · rw [map_zero]; exact ((c.fiber_linear (P y) hx).map_zero).symm

/-- **A strong bundle map preserves the double filtration** `Y_{m,k}`, `k ≤ m + 1` (part of
Definition 2.22 [2.47] for local models): for `k ≤ m` from the sc-smoothness on `Y[0]` (on
`Y_{k,k}` for the fibre component, at the zero of the fibre for the base component), for
`k = m + 1` from the sc-smoothness on `Y[1]`. -/
theorem IsStrongBundleMap.mapsTo_doubleLevel (h : B.IsStrongBundleMap B' f Φ) {m k : ℕ}
    (hk : k ≤ m + 1) : MapsTo Φ (B.doubleLevel m k) (B'.doubleLevel m k) := by
  intro y hy
  rcases Nat.lt_or_ge k (m + 1) with hkm | hkm
  · have hkm' : k ≤ m := Nat.lt_succ_iff.1 hkm
    obtain ⟨c', hc', hyc'⟩ := B'.atlas.cover (Φ y)
    rw [B'.mem_doubleLevel_iff hc' hyc' hk]
    set y₀ : Y := ((0 : P ⁻¹' {P y}) : Y) with hy₀
    have hy₀P : P y₀ = P y := (0 : P ⁻¹' {P y}).2
    have hΦy₀ : Φ y₀ ∈ B'.doubleLevel m m := by
      rw [← B'.mem_levelSet0_iff_mem_doubleLevel]
      exact h.isScSmoothMap.mapsTo_levelSet m
        ((B.mem_levelSet0_iff_mem_doubleLevel _ m).2 (zero_mem_doubleLevel hk hy))
    have hPΦ : P' (Φ y₀) = P' (Φ y) := by rw [h.covers, h.covers, hy₀P]
    have hy₀c' : Φ y₀ ∈ c'.toPartialEquiv.source := by
      rw [c'.source_eq, mem_preimage, hPΦ, ← mem_preimage, ← c'.source_eq]; exact hyc'
    refine ⟨?_, ?_⟩
    · have := ((B'.mem_doubleLevel_iff hc' hy₀c' (Nat.le_succ m)).1 hΦy₀).1
      rwa [c'.covers _ hy₀c', hPΦ, ← c'.covers _ hyc'] at this
    · have hykk : y ∈ B.doubleLevel k k := fun c hc hyc =>
        ⟨range_toBase_mono _ hkm' (hy c hc hyc).1, (hy c hc hyc).2⟩
      have := h.isScSmoothMap.mapsTo_levelSet k
        ((B.mem_levelSet0_iff_mem_doubleLevel y k).2 hykk)
      rw [B'.mem_levelSet0_iff_mem_doubleLevel] at this
      exact (this c' hc' hyc').2
  · have hk' : k = m + 1 := le_antisymm hk hkm
    subst hk'
    have hy1 : y ∈ B.oneSet := fun c hc hyc =>
      range_toBase_mono c.F (Nat.le_add_left 1 m) (hy c hc hyc).2
    have := h.isScSmoothMap_one.mapsTo_levelSet m
      ((B.mem_levelSet1_iff_mem_doubleLevel (B.oneMk y hy1) m).2 hy)
    rw [B'.mem_levelSet1_iff_mem_doubleLevel] at this
    exact this

/-! ### Strong bundle isomorphisms -/

/-- A **strong bundle isomorphism** `Φ` covering `f`, with inverse `Ψ` covering `g`: strong bundle
maps inverse to each other. -/
structure IsStrongBundleIso (B : StrongBundle PX P) (B' : StrongBundle PX' P') (f : X → X')
    (Φ : Y → Y') (g : X' → X) (Ψ : Y' → Y) : Prop where
  toMap : B.IsStrongBundleMap B' f Φ
  invMap : B'.IsStrongBundleMap B g Ψ
  left_inv : ∀ y, Ψ (Φ y) = y
  right_inv : ∀ y', Φ (Ψ y') = y'

namespace IsStrongBundleIso

variable {g : X' → X} {Ψ : Y' → Y}

theorem symm (h : B.IsStrongBundleIso B' f Φ g Ψ) : B'.IsStrongBundleIso B g Ψ f Φ :=
  ⟨h.invMap, h.toMap, h.right_inv, h.left_inv⟩

variable (B) in
theorem refl : B.IsStrongBundleIso B id id id id :=
  ⟨IsStrongBundleMap.id B, IsStrongBundleMap.id B, fun _ => rfl, fun _ => rfl⟩

theorem trans {g' : X'' → X'} {Ψ' : Y'' → Y'} {Φ' : Y' → Y''}
    (h : B.IsStrongBundleIso B' f Φ g Ψ) (h' : B'.IsStrongBundleIso B'' f' Φ' g' Ψ') :
    B.IsStrongBundleIso B'' (f' ∘ f) (Φ' ∘ Φ) (g ∘ g') (Ψ ∘ Ψ') :=
  ⟨h'.toMap.comp h.toMap, h.invMap.comp h'.invMap,
    fun y => by simp only [Function.comp_apply, h'.left_inv, h.left_inv],
    fun y => by simp only [Function.comp_apply, h.right_inv, h'.right_inv]⟩

/-- The base maps of a strong bundle isomorphism are inverse to each other (`P` is surjective). -/
theorem base_left_inv (h : B.IsStrongBundleIso B' f Φ g Ψ) (x : X) : g (f x) = x := by
  obtain ⟨y, rfl⟩ := B.surjective x
  rw [← h.toMap.covers, ← h.invMap.covers, h.left_inv]

theorem base_right_inv (h : B.IsStrongBundleIso B' f Φ g Ψ) (x' : X') : f (g x') = x' :=
  h.symm.base_left_inv x'

end IsStrongBundleIso

end StrongBundle

end Maps

/-! ### `P' : f*Y → Y` is a strong bundle map covering `f` -/

section PullbackMap

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {Z : Type w} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {PZ : MPolyfold Z}
  {f : Z → X} [ParacompactSpace (pullbackSpace P f)]

namespace StrongBundle

variable (B : StrongBundle PX P) (hf : PZ.IsScSmoothMap PX f)

/-- `(f*Y)_{0,1} = {(z, y) | y ∈ Y_{0,1}}`. -/
theorem mem_oneSet_pullback_iff (q : pullbackSpace P f) :
    q ∈ (B.pullback hf).oneSet ↔ (q : Z × Y).2 ∈ B.oneSet := by
  obtain ⟨d, hd, hq⟩ := PullbackChartData.exists_mem_atlas B hf q
  rw [(B.pullback hf).mem_oneSet_iff (B.toChart_mem_pullback_atlas hf hd q)
    (show q ∈ (d.toChart q).toPartialEquiv.source from hq), B.mem_oneSet_iff hd (d.mem_c_source hq)]
  rfl

theorem mapsTo_oneSet_pullbackProj' :
    MapsTo (pullbackProj' P f) (B.pullback hf).oneSet B.oneSet :=
  fun q hq => (B.mem_oneSet_pullback_iff hf q).1 hq

/-- `P'[1] : f*Y[1] → Y[1]` is sc-smooth (in the charts `Φ_f[1]`, `Φ[1]` it is
`(w, h) ↦ (g(w), h)`). -/
theorem isScSmoothMap_one_pullbackProj' :
    (B.pullback hf).toMPolyfold1.IsScSmoothMap B.toMPolyfold1
      (oneRestrict (B.pullback hf) B (pullbackProj' P f) (B.mapsTo_oneSet_pullbackProj' hf)) := by
  refine MPolyfold.isScSmoothMap_of_forall_charts fun y => ?_
  obtain ⟨d, hd, hq⟩ := PullbackChartData.exists_mem_atlas B hf ((B.pullback hf).oneVal y)
  have hmem := B.toChart_mem_pullback_atlas hf hd ((B.pullback hf).oneVal y)
  set y' := oneRestrict (B.pullback hf) B (pullbackProj' P f) (B.mapsTo_oneSet_pullbackProj' hf) y
  refine ⟨oneChart hmem y, oneChart hd y', (B.pullback hf).isChart_oneChart hmem y,
    B.isChart_oneChart hd y', hq, fun z hz => d.mem_c_source hz, ?_⟩
  refine (d.isScSmoothRetractMap_gPairOne _).congr fun p hp => ?_
  have hp' : (p.1, d.c.F.toBase 1 p.2) ∈ d.Kg := by rw [← d.toChart_K]; exact hp
  change d.gPairOne p =
    d.c.liftOne (((B.pullback hf).oneVal ((oneChart hmem y).symm p) : Z × Y).2)
  rw [oneChart_symm_apply hmem y hp]
  change d.gPairOne p = d.c.liftOne ((d.invFun _ (p.1, d.c.F.toBase 1 p.2) : Z × Y).2)
  rw [d.invFun_of_mem _ hp']
  exact (liftOne_symm (c := d.c) (z := d.gPairOne p) hp'.2).symm

/-- **`P' : f*Y → Y` is a strong bundle map covering `f`**; its fibre maps are the identifications
`P_f⁻¹(z) ≅ P⁻¹(f(z))` (`fiberMap_pullbackProj'`). -/
theorem isStrongBundleMap_pullbackProj' :
    (B.pullback hf).IsStrongBundleMap B f (pullbackProj' P f) where
  covers q := q.2
  fiber_linear z := (pullbackFiberCLE (P := P) (f := f) z).toLinearMap.isLinear
  isScSmoothMap := B.isScSmoothMap_pullbackProj' hf
  mapsTo_oneSet := B.mapsTo_oneSet_pullbackProj' hf
  isScSmoothMap_one := B.isScSmoothMap_one_pullbackProj' hf

/-- The fibre map of `P'` over `z` is Part I's `pullbackFiberCLE : P_f⁻¹(z) ≅ P⁻¹(f(z))`. -/
theorem fiberMap_pullbackProj' (z : Z) :
    (B.isStrongBundleMap_pullbackProj' hf).fiberMap z =
      ((pullbackFiberCLE (P := P) (f := f) z : _ ≃L[ℝ] _) : _ →L[ℝ] _) :=
  ContinuousLinearMap.ext fun _ => rfl

end StrongBundle

end PullbackMap

end Polyfold
