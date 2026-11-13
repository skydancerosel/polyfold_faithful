import Polyfold.Chapter6.CobordismOrientationEnds2021b

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), **Remark 6.6.19**, p. 276
(preprint Remark 6.42), and the proof of **Theorem 6.7.1**, p. 278: the orientation of the
cobordism on its product ends, in charts.

# The product orientation in a chart point and its product chart point

* `chartChangeDeriv_eq_of_eqOnSource_right`: the chart change derivative depends on the target
  chart only up to `EqOnSource`.
* `ChartPoint.linZero_congr_of_eventuallyEq`: `F'(x)` depends on `F` near `x` only;
  `ChartPoint.linZero_prodPt_paramLift`: `g̃'(t, x) = (g'(x))^` for `g̃(t, x) = g(x)`.
* `ChartPoint.tangentOr_eq_tangentOrOf`: a tangent orientation depends on the value of the
  orientation at the linearization only.
* `modelDeriv_prodRn`: the tangent map of `S' ↪ ℝ¹ × X` on a product end `(a, b) × S` is
  `(s, w) ↦ (s, Tι(w))` in the corner coordinates `κ.prodRn` and a product chart.
* `ChartPoint.pullOr_tangentOrOf_prodOrFirst₀_iff`, `pullOr_tangentOrOf_prodOrLift_iff`: for
  sections `g` over `X` and `G` over `ℝ¹ × X` with `G = g̃` near `(t, x)`, whose linearizations
  belong to `Lin(f, x)` and `Lin(f̃, (t, x))`, and coordinates `ι̂(s, w) = (s, ι w)` of
  `ker G'(t, x) = ℝ × ker g'(x)`: the orientation of `ker G'(t, x)` given by `e ∧ o` is the
  standard orientation of `ℝ^{k+1}` iff the orientation of `ker g'(x)` given by `o` is the
  standard orientation of `ℝ^k`.
* `tangentOr_toChartOr_prodFirst`: the tangent orientation of `SectionOrientation.prodFirst`
  in a product chart is the one given by `e ∧ (o` read in the chart `)`.
-/

open Set Filter Topology Manifold Module

noncomputable section

namespace Polyfold

universe u v

local notation "𝓠" => modelWithCornersEuclideanQuadrant

local notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-! ### Charts that agree on their source -/

section Charts

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]

/-- The chart change derivative depends on the target chart only up to `EqOnSource`. -/
theorem chartChangeDeriv_eq_of_eqOnSource_right {e e' : OpenPartialHomeomorph M H} (h : e ≈ e')
    (c : OpenPartialHomeomorph M H) {x : M} (hxc : x ∈ c.source) (hx : x ∈ e.source) :
    chartChangeDeriv I c e x = chartChangeDeriv I c e' x := by
  have hT : (c.extend I).target ∩ (c.extend I).symm ⁻¹' e.source ∈
      𝓝[range I] (c.extend I x) := by
    refine inter_mem (c.extend_target_mem_nhdsWithin hxc) (nhdsWithin_le_nhds ?_)
    refine (c.continuousAt_extend_symm hxc).preimage_mem_nhds (e.open_source.mem_nhds ?_)
    rw [c.extend_left_inv hxc]; exact hx
  have hEq : ∀ z ∈ (c.extend I).target ∩ (c.extend I).symm ⁻¹' e.source,
      I.extendCoordChange c e z = I.extendCoordChange c e' z := fun z hz => by
    simp only [ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans, Function.comp_apply,
      OpenPartialHomeomorph.extend_coe]
    rw [h.eqOn hz.2]
  unfold chartChangeDeriv
  exact Filter.EventuallyEq.fderivWithin_eq (Filter.eventually_of_mem hT hEq)
    (hEq _ ⟨(c.extend I).map_source (by rwa [c.extend_source]),
      by rw [mem_preimage, c.extend_left_inv hxc]; exact hx⟩)

end Charts

/-! ### The linearization at a zero is local, and the linearization of `g̃` -/

section Local

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

namespace ChartPoint

variable {x : X} (p : ChartPoint B x)

/-- **`F'(x)` depends on `F` near `x` only**: two sc-Fredholm sections which agree near a common
zero `x` have the same linearization there. -/
theorem linZero_congr_of_eventuallyEq {F G : X → Y} (hF : B.IsScFredholmSection F)
    (hG : B.IsScFredholmSection G) (hxF : IsZeroAt P F x) (hxG : IsZeroAt P G x)
    (h : ∀ᶠ y in 𝓝 x, F y = G y) : p.linZero hF hxF = p.linZero hG hxG := by
  obtain ⟨W, hWsub, hWo, hxW⟩ := mem_nhds_iff.1 h
  obtain ⟨W', hW'o, hW'⟩ := continuousOn_iff'.1 p.c.φ.continuousOn_invFun W hWo
  have hV : IsRelOpenInQuadrant p.c.φ.model.E p.c.φ.model.C
      (p.c.U ∩ StrongRetr.r p.c.R ⁻¹' W') :=
    (p.c.isRetraction.baseRetraction p.c.relOpen).relOpen_inter_preimage hW'o
  have hzO : p.c.φ.model.E.toBase 1 p.z ∈ p.c.φ.model.O := by
    rw [p.toBase_z]; exact p.c.φ.mapsTo_model x p.mem_source
  have hzV : p.z ∈ p.c.φ.model.E.lvlSet (p.c.U ∩ StrongRetr.r p.c.R ⁻¹' W') 1 := by
    refine ⟨p.mem_U, ?_⟩
    change StrongRetr.r p.c.R (p.c.φ.model.E.toBase 1 p.z) ∈ W'
    rw [StrongRetr.r_eq_self p.c.isRetraction p.mem_O]
    have : p.c.φ.model.E.toBase 1 p.z ∈ p.c.φ.symm ⁻¹' W ∩ p.c.φ.model.O := by
      refine ⟨?_, hzO⟩
      rw [mem_preimage, p.toBase_z, p.c.φ.symm_apply_apply p.mem_source]
      exact hxW
    rw [hW'] at this
    exact this.1
  have hEq : EqOn (p.c.principal F ∘ StrongRetr.r p.c.R) (p.c.principal G ∘ StrongRetr.r p.c.R)
      (p.c.U ∩ StrongRetr.r p.c.R ⁻¹' W') := fun u hu => by
    have hrO : StrongRetr.r p.c.R u ∈ p.c.φ.model.O := by
      rw [← p.c.r_image]; exact ⟨u, hu.1, rfl⟩
    have hW1 : StrongRetr.r p.c.R u ∈ p.c.φ.symm ⁻¹' W ∩ p.c.φ.model.O := by
      rw [hW']; exact ⟨hu.2, hrO⟩
    change (p.c (F (p.c.φ.symm (StrongRetr.r p.c.R u)))).2 =
      (p.c (G (p.c.φ.symm (StrongRetr.r p.c.R u)))).2
    rw [hWsub hW1.1]
  have hD := scDeriv_eq_of_eqOn_relOpen hV (hF.isScSmooth.isSc1_principal_comp_r p.isChart)
    (hG.isScSmooth.isSc1_principal_comp_r p.isChart) inter_subset_left inter_subset_left hEq hzV
  refine ContinuousLinearMap.ext fun v => Subtype.ext ?_
  rw [coe_linZero, coe_linZero, linAt_apply, linAt_apply, hD]

/-- **A tangent orientation depends on the value at `g'(x)` only**: if the orientation `O` of
`DET(g, x)` and the orientation `o` of `DET(f, x)` have the same value at `g'(x) ∈ Lin(f, x)`,
the tangent orientation of `O` is the orientation of `ker g'(x)` given by `o`. -/
theorem tangentOr_eq_tangentOrOf {f g : X → Y} (hf : B.IsScFredholmSection f)
    (hg : B.IsScFredholmSection g) (hx : IsZeroAt P g x) (hL : B.IsLinSurjAt g x)
    (hmem : p.linZero hg hx ∈ p.linSet f) (O : p.Or g hg) (o : p.Or f hf)
    (h : O ⟨p.linZero hg hx, p.linZero_mem_linSet hg hx⟩ = o ⟨p.linZero hg hx, hmem⟩) :
    p.tangentOr hg hx hL O = p.tangentOrOf hf hg hx hL hmem o :=
  congrArg (surjRay (p.linZero_surjective hg hx hL) p.T.subtypeL Subtype.val_injective
    (p.map_ker_linZero hg hx)) h

variable [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))]

/-- **`g̃'(t, x) = (g'(x))^`** in the product chart point. -/
theorem linZero_prodPt_paramLift (t : Fin 1 → ℝ)
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)) {g : X → Y}
    (hg : B.IsScFredholmSection g) (hx0 : IsZeroAt P g x)
    (hz0 : IsZeroAt (pullbackProj P Prod.snd) (paramLift (n := 1) g hg.isScSmooth.1) (t, x)) :
    (p.prodPt t q₀).linZero hg.param hz0 = p.prodLin t q₀ (p.linZero hg hx0) := by
  refine ContinuousLinearMap.ext fun v => Subtype.ext ?_
  rw [coe_linZero]
  exact (p.linAt_prodPt_paramLift t q₀ hg.isScSmooth v).trans
    ((p.coe_linZero hg hx0 _).symm.trans (p.coe_prodLin_apply t q₀ (p.linZero hg hx0) v).symm)

end ChartPoint

end Local

/-! ### The statement in a chart point and its product chart point -/

section ChartLevel

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))] {f : X → Y}

namespace ChartPoint

variable {x : X} (p : ChartPoint B x) (t : Fin 1 → ℝ)
  (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))

/-- **The tangent orientation of the product orientation** (2021 Remark 6.6.19, p. 276, and the
proof of Theorem 6.7.1, p. 278): let `g` have a zero at `x` with `g'(x)` onto and in
`Lin(f, x)`, and let `G` over `ℝ¹ × X` have a zero at `(t, x)` with `G'(t, x) = (g'(x))^` in
`Lin(f̃, (t, x))`. In coordinates `ι̂(s, w) = (s, ι w)` of `ker G'(t, x) = ℝ × ker g'(x)`, the
orientation of `ker G'(t, x)` given by `e ∧ o` is the standard orientation of `ℝ^{k+1}` iff the
orientation of `ker g'(x)` given by `o` is the standard orientation of `ℝ^k`. -/
theorem pullOr_tangentOrOf_prodOrFirst₀_iff (hf : B.IsScFredholmSection f)
    (hxs : x ∈ PX.smoothSet) (hne : (p.linSet f).Nonempty) (o : p.Or f hf) {g : X → Y}
    (hg : B.IsScFredholmSection g) (hx0 : IsZeroAt P g x) (hgL : B.IsLinSurjAt g x)
    (hmem : p.linZero hg hx0 ∈ p.linSet f)
    {G : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
    (hG : (prodBundle B).IsScFredholmSection G)
    (hz0 : IsZeroAt (pullbackProj P Prod.snd) G (t, x))
    (hGL : (prodBundle B).IsLinSurjAt G (t, x))
    (hmem' : (p.prodPt t q₀).linZero hG hz0 ∈
      (p.prodPt t q₀).linSet (paramLift (n := 1) f hf.isScSmooth.1))
    (hE : (p.prodPt t q₀).linZero hG hz0 = p.prodLin t q₀ (p.linZero hg hx0))
    {k : ℕ} (ι : EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ] p.c.linKer g p.z)
    (ι' : EuclideanSpace ℝ (Fin (k + 1)) ≃ₗ[ℝ]
      (p.prodPt t q₀).c.linKer G (p.prodPt t q₀).z)
    (hι : ∀ s w, ((ι' (consE s w)).1 : (Fin 1 → ℝ) × p.c.φ.model.E 0) =
      ((fun _ => s), (ι w : p.c.φ.model.E 0))) :
    pullOr finrank_euclideanSpace_fin ι'
        ((p.prodPt t q₀).tangentOrOf hf.param hG hz0 hGL hmem'
          (p.prodOrFirst₀ t q₀ hf hxs hne o)) = stdOrientation (k + 1) ↔
      pullOr finrank_euclideanSpace_fin ι (p.tangentOrOf hf hg hx0 hgL hmem o) =
        stdOrientation k := by
  have aux : ∀ (T₁ : ↥(p.prodPt t q₀).T →L[ℝ] ↥(p.prodPt t q₀).K)
      (_ : T₁ = p.prodLin t q₀ (p.linZero hg hx0))
      (hT₁m : T₁ ∈ (p.prodPt t q₀).linSet (paramLift (n := 1) f hf.isScSmooth.1))
      (hT₁s : Function.Surjective T₁) (N' : Submodule ℝ ((Fin 1 → ℝ) × p.c.φ.model.E 0))
      (hN' : (LinearMap.ker ((T₁ : ↥(p.prodPt t q₀).T →L[ℝ] ↥(p.prodPt t q₀).K) :
        ↥(p.prodPt t q₀).T →ₗ[ℝ] ↥(p.prodPt t q₀).K)).map
          (p.prodIncl t q₀ : ↥(p.prodPt t q₀).T →ₗ[ℝ] (Fin 1 → ℝ) × p.c.φ.model.E 0) = N')
      (ι' : EuclideanSpace ℝ (Fin (k + 1)) ≃ₗ[ℝ] N')
      (_ : ∀ s w, ((ι' (consE s w) : N') : (Fin 1 → ℝ) × p.c.φ.model.E 0) =
        ((fun _ => s), (ι w : p.c.φ.model.E 0))),
      (pullOr finrank_euclideanSpace_fin ι'
          (surjRay hT₁s (p.prodIncl t q₀) (p.prodIncl_injective t q₀) hN'
            ((p.prodPt t q₀).orEquivRay hf.param hT₁m (p.prodOrFirst₀ t q₀ hf hxs hne o))) =
          stdOrientation (k + 1) ↔
        pullOr finrank_euclideanSpace_fin ι
          (surjRay (p.linZero_surjective hg hx0 hgL) p.T.subtypeL Subtype.val_injective
            (p.map_ker_linZero hg hx0) (p.orEquivRay hf hmem o)) = stdOrientation k) := by
    intro T₁ hT₁e
    subst hT₁e
    intro hT₁m hT₁s N' hN' ι' hι'
    have hFr := p.isFredholm_of_mem_linSet hf _ hmem
    have hFr' := (p.prodPt t q₀).isFredholm_of_mem_linSet hf.param _ hT₁m
    have hval : (p.prodPt t q₀).orEquivRay hf.param hT₁m (p.prodOrFirst₀ t q₀ hf hxs hne o) =
        Module.Ray.map (extConjDetFirst (p.prodT t q₀) (p.prodK t q₀) hFr hFr')
          (p.orEquivRay hf hmem o) :=
      p.prodOrFirst₀_apply t q₀ hf hxs hne o _ hmem
    refine (iff_of_eq (congrArg (fun r => pullOr finrank_euclideanSpace_fin ι'
      (surjRay hT₁s (p.prodIncl t q₀) (p.prodIncl_injective t q₀) hN' r) =
        stdOrientation (k + 1)) hval)).trans ?_
    exact pullOr_surjRay_extConjDetFirst_iff (p.prodT t q₀) (p.prodK t q₀) hFr hFr'
      (p.linZero_surjective hg hx0 hgL) hT₁s p.T.subtypeL Subtype.val_injective
      (p.prodIncl t q₀) (p.prodIncl_injective t q₀) (fun _ => rfl) (p.map_ker_linZero hg hx0)
      hN' ι ι' hι' (p.orEquivRay hf hmem o)
  exact aux _ hE hmem' ((p.prodPt t q₀).linZero_surjective hG hz0 hGL) _
    ((p.prodPt t q₀).map_ker_linZero hG hz0) ι' hι

end ChartPoint

end ChartLevel

/-! ### The lift form, and the reading of `SectionOrientation.prodFirst` -/

section Lift

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))] {f : X → Y}

/-- **The tangent orientation of the product orientation, for chart points with given lifts**
(`ChartPoint.pullOr_tangentOrOf_prodOrFirst₀_iff` for `prodOrLift`): `G` agrees with `g̃` to
first order at `(t, x)` (`hE`). -/
theorem pullOr_tangentOrOf_prodOrLift_iff {c : StrongBundleChart PX P} (hc : B.IsChart c)
    {x : X} (hx : x ∈ c.φ.source) (z : c.φ.model.E 1) (hz : c.φ.model.E.toBase 1 z = c.φ x)
    (t : Fin 1 → ℝ) (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))
    (hxc : ((t, x) : (Fin 1 → ℝ) × X) ∈ (prodChart c q₀).φ.source)
    (z' : (prodChart c q₀).φ.model.E 1)
    (hz' : (prodChart c q₀).φ.model.E.toBase 1 z' = (prodChart c q₀).φ (t, x))
    (hzz : z' = (t, z)) (hf : B.IsScFredholmSection f) (hxs : x ∈ PX.smoothSet)
    (hne : ((chartPt c hc hx z hz).linSet f).Nonempty) (o : (chartPt c hc hx z hz).Or f hf)
    {g : X → Y} (hg : B.IsScFredholmSection g) (hx0 : IsZeroAt P g x)
    (hgL : B.IsLinSurjAt g x)
    (hmem : (chartPt c hc hx z hz).linZero hg hx0 ∈ (chartPt c hc hx z hz).linSet f)
    {G : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
    (hG : (prodBundle B).IsScFredholmSection G)
    (hz0 : IsZeroAt (pullbackProj P Prod.snd) G (t, x))
    (hGL : (prodBundle B).IsLinSurjAt G (t, x))
    (hmem' : (chartPt (B := prodBundle B) (prodChart c q₀) (isChart_prodChart hc q₀) hxc z'
        hz').linZero hG hz0 ∈
      (chartPt (B := prodBundle B) (prodChart c q₀) (isChart_prodChart hc q₀) hxc z'
        hz').linSet (paramLift (n := 1) f hf.isScSmooth.1))
    (hz0g : IsZeroAt (pullbackProj P Prod.snd) (paramLift (n := 1) g hg.isScSmooth.1) (t, x))
    (hE : (chartPt (B := prodBundle B) (prodChart c q₀) (isChart_prodChart hc q₀) hxc z'
        hz').linZero hG hz0 =
      (chartPt (B := prodBundle B) (prodChart c q₀) (isChart_prodChart hc q₀) hxc z'
        hz').linZero hg.param hz0g)
    {k : ℕ} (ι : EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ] c.linKer g z)
    (ι' : EuclideanSpace ℝ (Fin (k + 1)) ≃ₗ[ℝ] (prodChart c q₀).linKer G z')
    (hι : ∀ s w, ((ι' (consE s w)).1 : (Fin 1 → ℝ) × c.φ.model.E 0) =
      ((fun _ => s), (ι w : c.φ.model.E 0))) :
    pullOr finrank_euclideanSpace_fin ι'
        ((chartPt (B := prodBundle B) (prodChart c q₀) (isChart_prodChart hc q₀) hxc z'
          hz').tangentOrOf hf.param hG hz0 hGL hmem'
          (prodOrLift hc hx z hz t q₀ hxc z' hz' hzz hf hxs hne o)) = stdOrientation (k + 1) ↔
      pullOr finrank_euclideanSpace_fin ι
        ((chartPt c hc hx z hz).tangentOrOf hf hg hx0 hgL hmem o) = stdOrientation k := by
  subst hzz
  exact (chartPt c hc hx z hz).pullOr_tangentOrOf_prodOrFirst₀_iff t q₀ hf hxs hne o hg hx0 hgL
    hmem hG hz0 hGL hmem'
    (hE.trans ((chartPt c hc hx z hz).linZero_prodPt_paramLift t q₀ hg hx0 hz0g)) ι ι' hι

/-- **The tangent orientation of `SectionOrientation.prodFirst` in a product chart** (2021
Remark 6.6.19): at a zero `(t, x)` of `F = f̃ + Ŝ` with `F'(t, x)` onto, the tangent orientation
of the orientation `e ∧ o` of `F` is the orientation of `ker F'(t, x)` given by
`e ∧ (o_x` read in `c)` (`toChartOr_prodFirstFun`, `toChartOr_orSectionAdd`). -/
theorem tangentOr_toChartOr_prodFirst (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) (o : SectionOrientation f hf.toIsScFredholmSection)
    {Ŝ : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)}
    (hŜ : (prodBundle B).IsScPlusSection Ŝ) {t : Fin 1 → ℝ} {x : X} (hxs : x ∈ PX.smoothSet)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (hxc : x ∈ c.φ.source)
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))
    (hz0 : IsZeroAt (pullbackProj P Prod.snd) (sectionAdd (pullbackProj P Prod.snd)
      (paramLift (n := 1) f hf.isScSmooth.1) Ŝ) (t, x))
    (hL : (prodBundle B).IsLinSurjAt (sectionAdd (pullbackProj P Prod.snd)
      (paramLift (n := 1) f hf.isScSmooth.1) Ŝ) (t, x))
    (hne : ((chartPtOf c hc hxc hxs).linSet f).Nonempty) :
    (chartPtOf (B := prodBundle B) (prodChart c q₀) (isChart_prodChart hc q₀)
        (mem_prodChart_source q₀ hxc t) (prod_rn_mem_smoothSet_iff.2 hxs)).tangentOr
        (theorem_3_1_18_preprint hf.toIsScFredholmSection.param hŜ) hz0 hL
        (toChartOr (theorem_3_1_18_preprint hf.toIsScFredholmSection.param hŜ)
          (prod_rn_mem_smoothSet_iff.2 hxs) (prodChart c q₀) (isChart_prodChart hc q₀)
          (mem_prodChart_source q₀ hxc t)
          ((SectionOrientation.prodFirst hX hbump hf o hŜ).1 (t, x)
            (prod_rn_mem_smoothSet_iff.2 hxs))) =
      (chartPtOf (B := prodBundle B) (prodChart c q₀) (isChart_prodChart hc q₀)
        (mem_prodChart_source q₀ hxc t) (prod_rn_mem_smoothSet_iff.2 hxs)).pertTangentOr
        hf.toIsScFredholmSection.param hŜ hz0 hL
        (prodOrOf hc hxc hxs t q₀ hf.toIsScFredholmSection hne
          (toChartOr hf.toIsScFredholmSection hxs c hc hxc (o.1 x hxs))) := by
  have hzs : ((t, x) : (Fin 1 → ℝ) × X) ∈ ((rnPolyfold 1).prod PX).smoothSet :=
    prod_rn_mem_smoothSet_iff.2 hxs
  have e1 := toChartOr_orSectionAdd hf.toIsScFredholmSection.param hŜ hzs
    ((SectionOrientation.prodFirst₀ hX hbump hf o).1 (t, x) hzs) (prodChart c q₀)
    (isChart_prodChart hc q₀) (mem_prodChart_source q₀ hxc t)
  have e2 := toChartOr_prodFirstFun hf.toIsScFredholmSection
    (MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough hbump) o.1 (t, x) hzs hc hxc q₀
    (isChart_prodChart hc q₀) (mem_prodChart_source q₀ hxc t) hne
  have e3 := DFunLike.congr_fun (ChartPoint.orTransfer_self
    (chartPtOf (B := prodBundle B) (prodChart c q₀) (isChart_prodChart hc q₀)
      (mem_prodChart_source q₀ hxc t) hzs) hf.toIsScFredholmSection.param hzs)
    (prodOrOf hc hxc hxs t q₀ hf.toIsScFredholmSection hne
      (toChartOr hf.toIsScFredholmSection hxs c hc hxc (o.1 x hxs)))
  exact (congrArg _ (e1.trans (congrArg _ (e2.trans e3)))).trans
    (ChartPoint.tangentOr_orSectionAdd _ hf.toIsScFredholmSection.param hŜ hz0 hL _)

end Lift

/-! ### The tangent map of `S' ↪ ℝ¹ × X` on a product end, in a product chart -/

section ModelDeriv

open MPolyfold MPolyfold.CornerCoords

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))]
  {A : Set X} [ParacompactSpace A]
  {hA : PX.IsSubMPolyfold A} {A' : Set ((Fin 1 → ℝ) × X)} [ParacompactSpace A']
  (hA' : ((rnPolyfold 1).prod PX).IsSubMPolyfold A') {a b : ℝ} (hab : a < b)
  (hend : ∀ z : (Fin 1 → ℝ) × X, z.1 0 ∈ Ioo a b → (z ∈ A' ↔ z.2 ∈ A)) (x₀ : A) {k : ℕ}

omit [T2Space Y] [ParacompactSpace Y]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))] in
/-- **The tangent map of `A' ↪ ℝ¹ × X` on a product end** (proof of 2021 Theorem 6.7.1, p. 278),
in the corner coordinates `κ.prodRn` and the product chart over a chart `c` of `X`:
`v ↦ (v₀, Tι(v₁, …, v_k))` for the tangent map `Tι` of `A ↪ X` in `κ` and `c`. -/
theorem modelDeriv_prodRn (κ : CornerCoords (subPolyfold hA) k) (c : StrongBundleChart PX P)
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)) (d : PX.SubData A) (a₀ : A)
    (d' : ((rnPolyfold 1).prod PX).SubData A') (a₀' : A') {p : A'}
    (hp : p ∈ (κ.prodRn hA' hab hend x₀).s)
    (hpσ : p ∈ (subChart d' (prodChart c q₀).isChart a₀').source)
    (hyσ : endProj A x₀ p ∈ (subChart d c.isChart a₀).source)
    {z' : (κ.prodRn hA' hab hend x₀).χ.model.E 1}
    (hz' : (κ.prodRn hA' hab hend x₀).χ.model.E.toBase 1 z' = (κ.prodRn hA' hab hend x₀).χ p)
    {z : κ.χ.model.E 1} (hz : κ.χ.model.E.toBase 1 z = κ.χ (endProj A x₀ p))
    (v : EuclideanSpace ℝ (Fin (k + 1))) :
    (modelDeriv (κ.prodRn hA' hab hend x₀) (prodChart c q₀).isChart d' a₀' z' v :
        (Fin 1 → ℝ) × c.φ.model.E 0) =
      ((fun _ => v 0), modelDeriv κ c.isChart d a₀ z (tailE v)) := by
  obtain ⟨hpt, hpκ⟩ := (mem_prodRn_s hA' hab hend x₀ κ).1 hp
  rw [← derivIn_incl (κ.prodRn hA' hab hend x₀) (prodChart c q₀).isChart d' a₀' hp hpσ hz']
  refine derivIn_prodRn hA' hab hend x₀ κ (fun b : A => c.φ b.1)
    (fun b : A' => ((prodChart c q₀).φ b.1 : (Fin 1 → ℝ) × c.φ.model.E 0)) (fun q hq => ?_) hp
    (hasFDerivWithinAt_incl κ c.isChart d a₀ hpκ hyσ hz) v
  change ((q.1.1 - 0, c.φ q.1.2) : (Fin 1 → ℝ) × c.φ.model.E 0) = _
  rw [sub_zero, endProj_val_of_mem hend x₀ hq]

end ModelDeriv

end Polyfold
