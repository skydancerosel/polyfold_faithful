import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_92

/-!
Round trip for V3_92 (the linearization of `f̃(r, x) = f(x) + Σ rᵢ sᵢ(x)` at `(0, x₀)`).  `A` is
the conjunction of the types of the theorems among the decls (`PullbackChartData.ofProd` is a
definition, vocabulary): `linAt_paramSection_zero`, `linAt_paramSection`, `scDeriv_paramSection`,
`PullbackChartData.ofProd_mem_tangent`, universes instantiated at `0`.

Refresh 2026-11-02: the three linearization theorems now take `f` an sc-Fredholm section in the
germ reading (`IsScFredholmSection`; only its sc-smoothness is used, through
`scDeriv_paramSection_of_isScSmoothSection`), as does B.  The germ reading was not the obstacle
here: the audit's gap was that A states the formula only in charts centred at the point.

* `A → B` (proved, `A_to_B`): from A's third conjunct `scDeriv_paramSection` (taken as the
  hypothesis instead of `hA : A`: the statement of A's conjunct `linAt_paramSection` contains the
  proof term `ofProd_mem_tangent`, so a hypothesis `hA : A` makes `#rt_check` and `#rt_check_soft`
  see that banned theorem through the definition `A`).  For an arbitrary chart `c` around `x₀` and
  a lift `z₁` of `e = φ(x₀)`: `x₀` is smooth (a zero of an sc-Fredholm section), so `e` is a smooth
  vector; the re-centred chart `c_e` (`StrongBundleChart.recentre`, `Chapter4/Recentre.lean`, a
  chart of the bundle by `StrongBundle.IsChart.recentre`) is centred at `x₀`, A's formula holds in
  `c_e` and its product chart, and both sides are transported back along the translations by `e`
  and by `(0, e)` (`scDeriv_translate`: chain rule `scDeriv_comp_apply_of_isScDomain`, derivative
  of a translation = identity, `levelMap (· + e) 1 0 = z₁`), using
  `f̂_e ∘ r_e = (f̂ ∘ r)(· + e)` on `U_e` and `ofProd_principal_paramSection` in both product charts.
  The audit's `A_to_B_centred` (the centred case) is kept.
* `B → A` is not proved: genuine difference of scope.  B assumes a tame bundle, `f(x₀) = 0` and
  `r₀ = 0`; A holds without tameness, at any `r₀` (`Ĝ = f̂ + Σ r₀ᵢ ŝᵢ`), in `linAt` form, and
  includes the tangent-space lemma `ofProd_mem_tangent`, which B does not state.
-/

namespace RoundTrip.V3_92
open Polyfold Set

/-- The project's statement, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.linAt_paramSection_zero.{0, 0} ∧
    type_of% @Polyfold.linAt_paramSection.{0, 0} ∧
    type_of% @Polyfold.scDeriv_paramSection.{0, 0} ∧
    type_of% @Polyfold.PullbackChartData.ofProd_mem_tangent.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.linAt_paramSection_zero.{0, 0}, @Polyfold.linAt_paramSection.{0, 0},
    @Polyfold.scDeriv_paramSection.{0, 0}, @Polyfold.PullbackChartData.ofProd_mem_tangent.{0, 0}⟩

/-- **`B` in the charts centred at `x₀`**, from the hypothesis `A`: only its third conjunct
`scDeriv_paramSection` is used, and it is taken as the hypothesis (the type of `A`'s conjunct
`linAt_paramSection` contains the proof term `ofProd_mem_tangent`, so a hypothesis `hA : A` would
make `#rt_check` see that banned theorem through the statement of `A`). -/
theorem A_to_B_centred (hA : type_of% @Polyfold.scDeriv_paramSection.{0, 0}) :
    ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
      {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
      [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
      (Bd : StrongBundle PX P) (n : ℕ) [ParacompactSpace ((Fin n → ℝ) × X)]
      (f : X → Y) (s : Fin n → X → Y) (hf : IsSection P f) (hs : ∀ i, IsSection P (s i)) (x₀ : X),
      IsTameStrongBundle Bd → Bd.IsScFredholmSection f → (∀ i, Bd.IsScPlusSection (s i)) →
      IsZeroAt P f x₀ →
        ∀ (c : StrongBundleChart PX P), Bd.IsChart c → x₀ ∈ c.φ.source →
          c.φ.toPartialEquiv x₀ = 0 →
          ∀ (y : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)) (z₁ : c.φ.model.E.lvl 1),
            c.φ.model.E.toBase 1 z₁ = c.φ.toPartialEquiv x₀ →
              LinFormulaInChart n c y f s hf hs x₀ z₁ := by
  intro X _ _ _ PX Y _ _ _ P _ _ Bd n _ f s hf hs x₀ _ hfF hsP _ c hc hx₀ hφ0 y z₁ hz₁
  have hz0 : z₁ = 0 := c.φ.model.E.toBase_injective 1 (by rw [hz₁, hφ0, map_zero])
  subst hz0
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := hφ0 ▸ c.φ.mapsTo_model x₀ hx₀
  have hprin : ∀ i, c.principal (s i) 0 = (c.toPartialEquiv (s i x₀)).2 := by
    intro i
    change (c (s i (c.φ.symm 0))).2 = _
    rw [← hφ0, c.φ.symm_apply_apply hx₀]
  have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin n → ℝ) × X → X))
    ((rnPolyfold n).prod PX) Bd
  intro w _
  have h := hA hfF hsP hc h0O 0 y w
  have e : (fun u => c.principal f u + ∑ i, (0 : Fin n → ℝ) i • c.principal (s i) u) =
      c.principal f := funext fun u => by simp
  rw [e] at h
  simp only [hprin] at h
  exact h

#rt_check RoundTrip.V3_92.A_to_B_centred [Polyfold.linAt_paramSection_zero,
  Polyfold.linAt_paramSection, Polyfold.scDeriv_paramSection,
  Polyfold.PullbackChartData.ofProd_mem_tangent]

/-! ### Translation by a smooth vector: the derivative is transported -/

/-- The derivative of `v ↦ v + a` at `0` is the identity. -/
lemma scDeriv_add_const_zero {E : ScBanach} {V : Set (E 0)} (hV : IsScDomain E V) {a : E 0}
    (ha : a ∈ E.smooth) (h0V : (0 : E 0) ∈ V) :
    scDeriv V (fun v => v + a) (0 : E 1) = ContinuousLinearMap.id ℝ (E 0) := by
  have hτ : IsSc1 V (fun v => v + a) := (isScSmooth_add_const ha hV).isSc1
  have h01 : (0 : E 1) ∈ E.lvlSet V 1 := by
    show E.toBase 1 0 ∈ V
    rw [map_zero]; exact h0V
  have hd1 := hτ.isSc1With_scDeriv.hasFDerivWithinAt 0 h01
  have hd2 : HasFDerivWithinAt ((fun v : E 0 => v + a) ∘ E.toBase 1)
      ((ContinuousLinearMap.id ℝ (E 0)).comp (E.toBase 1)) (E.lvlSet V 1) 0 :=
    (((E.toBase 1).hasFDerivWithinAt).add_const a).congr_fderiv
      (ContinuousLinearMap.id_comp _).symm
  exact ContinuousLinearMap.ext_of_comp_toBase_one ((hV.uniqueDiffWithinAt 1 0 h01).eq hd1 hd2)

/-- **Transport of `scDeriv` along a translation**: if `g' = g ∘ (· + a)` on `V`, `a` smooth with
level-`1` lift `z`, then `Dg'(0) = Dg(z)`. -/
lemma scDeriv_translate {E F : ScBanach} {U V : Set (E 0)} (hU : IsScDomain E U)
    (hV : IsScDomain E V) {g g' : E 0 → F 0} (hg : IsSc1 U g) {a : E 0} (ha : a ∈ E.smooth)
    (hVU : MapsTo (fun v => v + a) V U) (hgg' : ∀ v ∈ V, g' v = g (v + a))
    (h0V : (0 : E 0) ∈ V) {z : E 1} (hz : E.toBase 1 z = a) (h : E 0) :
    scDeriv V g' (0 : E 1) h = scDeriv U g z h := by
  have hτ : IsSc1 V (fun v => v + a) := (isScSmooth_add_const ha hV).isSc1
  have h01 : (0 : E 1) ∈ E.lvlSet V 1 := by
    show E.toBase 1 0 ∈ V
    rw [map_zero]; exact h0V
  have hchain := scDeriv_comp_apply_of_isScDomain hV hU hτ hg hVU h01 h
  have hlev : levelMap (fun v : E 0 => v + a) 1 (0 : E 1) = z :=
    levelMap_eq_of_toBase_eq (by show E.toBase 1 z = E.toBase 1 0 + a; rw [hz, map_zero, zero_add])
  rw [hlev, scDeriv_add_const_zero hV ha h0V, ContinuousLinearMap.id_apply] at hchain
  have hgτ : IsSc1 V (g ∘ fun v => v + a) := (theorem_1_3_1' hV hU hτ hg hVU).1
  have hcong : IsSc1With V g' (scDeriv V (g ∘ fun v => v + a)) :=
    hgτ.isSc1With_scDeriv.congr fun v hv => (hgg' v hv).symm
  rw [IsSc1.scDeriv_eqOn hcong (hV.uniqueDiffWithinAt 1) h01]
  exact hchain.symm

/-- **B from A's third conjunct** (`scDeriv_paramSection`, the formula in charts centred at the
point), in every chart: re-centre the chart at `x₀` (`StrongBundleChart.recentre`, a chart of the
bundle by `StrongBundle.IsChart.recentre`), apply the centred formula there, and transport both
sides back along the translation by `φ(x₀)` (base chart) and by `(0, φ(x₀))` (product chart). -/
theorem A_to_B (hA : type_of% @Polyfold.scDeriv_paramSection.{0, 0}) : B := by
  intro X _ _ _ PX Y _ _ _ P _ _ Bd n _ f s hf hs x₀ _ hfF hsP hzero c hc hx₀ y z₁ hz₁
  have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin n → ℝ) × X → X))
    ((rnPolyfold n).prod PX) Bd
  intro w _
  -- `x₀` is smooth, so `e = φ(x₀)` is a smooth vector
  have hxs : x₀ ∈ PX.smoothSet := hfF.mem_smoothSet_of_isZeroAt hzero
  set e : c.φ.model.E 0 := c.φ x₀ with he_def
  have he : e ∈ c.φ.model.E.smooth := c.φ.model.E.mem_smooth_iff.2 fun m =>
    (PX.mem_levelSet_iff c.isChart hx₀).1 (mem_iInter.1 hxs m)
  -- the re-centred chart
  obtain ⟨nT, WT, T, hT⟩ := c.relOpen.isPartialQuadrant
  have hce : Bd.IsChart (c.recentre T hT e he) := hc.recentre T hT e he
  have hxe : x₀ ∈ (c.recentre T hT e he).φ.source :=
    c.φ.mem_recentre_source T hT e he hx₀ rfl
  have hφe : (c.recentre T hT e he).φ x₀ = 0 := c.φ.recentre_apply_self T hT e he rfl
  have h0Oe : (0 : c.φ.model.E 0) ∈ (c.recentre T hT e he).φ.model.O :=
    hφe ▸ (c.recentre T hT e he).φ.mapsTo_model x₀ hxe
  have h0Ue : (0 : c.φ.model.E 0) ∈ (c.recentre T hT e he).U :=
    (c.recentre T hT e he).zero_mem_U hxe hφe
  have hUeU : MapsTo (fun v : c.φ.model.E 0 => v + e) (c.recentre T hT e he).U c.U :=
    fun v hv => hv.1.1
  -- the principal parts in the re-centred chart
  have hprinc : ∀ (σ : X → Y) (v : c.φ.model.E 0),
      (c.recentre T hT e he).principal σ (StrongRetr.r (c.recentre T hT e he).R v) =
        c.principal σ (StrongRetr.r c.R (v + e)) := fun σ v => by
    show c.principal σ (StrongRetr.r c.R (v + e) - e + e) = c.principal σ (StrongRetr.r c.R (v + e))
    rw [sub_add_cancel]
  have hprin0 : ∀ i, (c.recentre T hT e he).principal (s i) 0 = (c.toPartialEquiv (s i x₀)).2 :=
    fun i => by
      show (c (s i (c.φ.symm (0 + e)))).2 = _
      rw [zero_add, he_def, c.φ.symm_apply_apply hx₀]
  -- A's centred formula in the re-centred chart
  have H := hA hfF hsP hce h0Oe 0 y w
  have e1 : (fun u => (c.recentre T hT e he).principal f u +
      ∑ i, (0 : Fin n → ℝ) i • (c.recentre T hT e he).principal (s i) u) =
      (c.recentre T hT e he).principal f := funext fun u => by simp
  rw [e1] at H
  simp only [hprin0] at H
  -- transport of the base term
  have T2 := scDeriv_translate (g' := (c.recentre T hT e he).principal f ∘
      StrongRetr.r (c.recentre T hT e he).R) c.relOpen.isScDomain
    (c.recentre T hT e he).relOpen.isScDomain
    (hfF.isScSmooth.isSc1_principal_comp_r hc) he hUeU
    (fun v _ => hprinc f v) h0Ue hz₁ w.2
  -- transport of the product-chart term
  have hπ := MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX
  have hFs : (Bd.pullback hπ).IsScSmoothSection (paramSection f hf s hs) := by
    rw [paramSection_eq_sectionAdd]
    exact (hfF.isScSmooth.pullback hπ).sectionAdd (StrongBundle.isScPlusSection_paramComb hsP)
  have hc' := (PullbackChartData.ofProd c 0).isChart_toChart Bd hπ hc y
  have hae : (((0 : Fin n → ℝ), e) : ((rnSc n).prod c.φ.model.E) 0) ∈
      ((rnSc n).prod c.φ.model.E).smooth := by
    refine ((rnSc n).prod c.φ.model.E).mem_smooth_iff.2 fun m => ?_
    obtain ⟨em, hem⟩ := c.φ.model.E.mem_smooth_iff.1 he m
    exact ⟨((0 : Fin n → ℝ), em), by rw [ScBanach.prod_toBase, hem, map_zero]⟩
  have hgg : ∀ v : ((rnSc n).prod c.φ.model.E) 0, v ∈ univ ×ˢ (c.recentre T hT e he).U →
      (((PullbackChartData.ofProd (c.recentre T hT e he) 0).toChart y).principal
          (paramSection f hf s hs) ∘
        StrongRetr.r ((PullbackChartData.ofProd (c.recentre T hT e he) 0).toChart y).R) v =
      (((PullbackChartData.ofProd c 0).toChart y).principal (paramSection f hf s hs) ∘
        StrongRetr.r ((PullbackChartData.ofProd c 0).toChart y).R)
        (v + (((0 : Fin n → ℝ), e) : ((rnSc n).prod c.φ.model.E) 0)) := by
    intro v hv
    have hO : (StrongRetr.r ((PullbackChartData.ofProd (c.recentre T hT e he) 0).toChart y).R
        v).2 ∈ (c.recentre T hT e he).φ.model.O :=
      (c.recentre T hT e he).r_mem_O hv.2
    have hO' : (StrongRetr.r ((PullbackChartData.ofProd c 0).toChart y).R
        (v + (((0 : Fin n → ℝ), e) : ((rnSc n).prod c.φ.model.E) 0))).2 ∈ c.φ.model.O :=
      c.r_mem_O (hUeU hv.2)
    refine (PullbackChartData.ofProd_principal_paramSection (c.recentre T hT e he) 0 y hf hs
      hO).trans (Eq.trans ?_ (PullbackChartData.ofProd_principal_paramSection c 0 y hf hs hO').symm)
    show (c.recentre T hT e he).principal f (StrongRetr.r (c.recentre T hT e he).R v.2) +
        ∑ i, (v.1 + 0) i •
          (c.recentre T hT e he).principal (s i) (StrongRetr.r (c.recentre T hT e he).R v.2) =
      c.principal f (StrongRetr.r c.R (v.2 + e)) +
        ∑ i, ((v + (((0 : Fin n → ℝ), e) : ((rnSc n).prod c.φ.model.E) 0)).1 + 0) i •
          c.principal (s i) (StrongRetr.r c.R (v.2 + e))
    simp only [hprinc, Prod.fst_add, add_zero]
    rfl
  have hmaps : MapsTo (fun v : ((rnSc n).prod c.φ.model.E) 0 =>
      v + (((0 : Fin n → ℝ), e) : ((rnSc n).prod c.φ.model.E) 0))
      (univ ×ˢ (c.recentre T hT e he).U) (univ ×ˢ c.U) :=
    fun v hv => ⟨mem_univ _, hUeU hv.2⟩
  have h0V : (0 : ((rnSc n).prod c.φ.model.E) 0) ∈ univ ×ˢ (c.recentre T hT e he).U :=
    ⟨mem_univ _, h0Ue⟩
  have T1 := scDeriv_translate (U := univ ×ˢ c.U) (V := univ ×ˢ (c.recentre T hT e he).U)
    ((PullbackChartData.ofProd c 0).toChart y).relOpen.isScDomain
    ((PullbackChartData.ofProd (c.recentre T hT e he) 0).toChart y).relOpen.isScDomain
    (hFs.isSc1_principal_comp_r hc') hae hmaps hgg h0V
    (z := ((0 : Fin n → ℝ), z₁)) (by rw [ScBanach.prod_toBase, hz₁, map_zero]) w
  exact T1.symm.trans (H.trans
    (congrArg (fun t => t + ∑ i, w.1 i • (c.toPartialEquiv (s i x₀)).2) T2))

#rt_check RoundTrip.V3_92.A_to_B [Polyfold.linAt_paramSection_zero,
  Polyfold.linAt_paramSection, Polyfold.scDeriv_paramSection,
  Polyfold.PullbackChartData.ofProd_mem_tangent]
#rt_overlap RoundTrip.V3_92.A_to_B [Polyfold.linAt_paramSection_zero,
  Polyfold.linAt_paramSection, Polyfold.scDeriv_paramSection,
  Polyfold.PullbackChartData.ofProd_mem_tangent]

end RoundTrip.V3_92
