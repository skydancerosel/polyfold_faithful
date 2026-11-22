import Polyfold.Chapter18.FredholmSectionFunctors
import Polyfold.Chapter17.TangentVectors
import Polyfold.Chapter12.RestrictionLocalIso
import Polyfold.Chapter9.SubmanifoldTangentImage
import Polyfold.Chapter3.LinearizationIntrinsic
import Polyfold.Chapter3.TameGermsG

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 18,
§18.1, pp. 844–845: the Part I facts behind (18.1) and Definition 18.1.3: the linearization
`f'(q₀) : T_{q₀}O → K_{q₀}` of a representative `f_Ψ̄` at a zero (Part I, §3.1, before
Definition 3.1.4), carried along local strong bundle isomorphisms and along the transition maps
of a strong polyfold bundle construction (Definition 17.7.4, p. 827).

# Linearizations along local strong bundle isomorphisms

* `StrongBundle.linZeroAt hf x h0 : T_xX →ₗ[ℝ] Y_x`: Part I's linearization `f'(x)` at a zero
  (`StrongBundle.linIntr`) read through a chosen chart; `linZeroAt_eq`: it is the one read
  through every chart.
* `StrongBundle.LocalIso.linIntr_transport`, `linZeroAt_transport`: **for a local strong bundle
  isomorphism `(ϕ, Φ) : Y|U → Y'|U'` and `f = Ψ ∘ f' ∘ ϕ` on `U`, `Φ ∘ f'(x) = f''(ϕ x) ∘ Tϕ(x)`**
  at a zero `x` on level `1`.  The proof reads both sides in a chart `c'` at `ϕ(x)` and in the
  transported chart `c' ∘ Φ` at `x`: the principal parts agree on the domain of the chart
  (`principal_transportChart`), and the chart vectors of `α` and `Tϕ(α)` agree
  (`chartVec_tangentMapOn_of_isScDiffeoOn`).
* `StrongBundle.LocalIso.isZeroAt_of_eqOn`: zeros correspond.
* `StrongBundle.LocalIso.isGoodPositionGermTame`: **Part I's good position in a tame chart
  (Definition 3.6.6) is carried along a local strong bundle isomorphism**, in the transported
  restricted chart, with the same filling, sc⁺-germ, conjugation and derivative family
  (`StrongBundleChart.goodPositionData_restrictInter` for the restriction to `dom φ ∩ U'`).
* `StrongPolyfoldBundleConstruction.transSection`, `isScSmoothSection_transSection`: the section
  `a ↦ (a, f_Ψ̄(s a))` of `M(Ψ̄, Ψ̄') → M(Ψ, Ψ')`.
* **`StrongPolyfoldBundleConstruction.linZeroAt_transTangent`** (the transition law behind the
  independence statement after (18.1)): for `a = (q, φ, q') ∈ M(Ψ, Ψ')` with `f_Ψ̄(q) = 0`,
  `f_Ψ̄'(q') = 0` on level `1`, `f'_Ψ̄'(q') (Tσ(q) h) = T(a, f'_Ψ̄(q) h)`.  The proof transports
  `f'_Ψ̄(q)` to `M(Ψ̄, Ψ̄')` along `s̄` (`isLocalStrongBundleIso_src`) and from there to `K'`
  along `t̄` (`isLocalStrongBundleIso_trans`), and identifies `Tt ∘ T(s|U)⁻¹` with `Tσ` through
  the admissible triple of the two sheets (`transMap_eq`).
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

open StrongRetr MPolyfold

section Transport

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {X' : Type*} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type*} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]

/-! ### Good position along local strong bundle isomorphisms -/

omit [T2Space Y] [ParacompactSpace Y] in
/-- **The good-position data of Definition 3.6.6 in `c` are good-position data in
`c|dom φ ∩ V`**: the derivative family on the germ cut down to the restricted domain, and the
same operator `Dg(0)` (the tangent `Dr(0)E` and the fibre `ρ(0)F` do not change,
`scDeriv_r_of_subset`). -/
theorem StrongBundleChart.goodPositionData_restrictInter {c : StrongBundleChart PX P} {V : Set X}
    (hV : IsOpen V) {x : X} (hxV : x ∈ c.φ.source) (hφ0 : c.φ x = 0) (hxV' : x ∈ V)
    (h0 : (0 : c.φ.model.E 0) ∈ c.U) {g : c.φ.model.E 0 → c.F 0}
    (h : ∃ (G : ScNbhdGerm c.φ.model.E c.φ.model.C)
      (Dg : c.φ.model.E 1 → c.φ.model.E 0 →L[ℝ] c.F 0),
      G.U 0 ⊆ c.U ∧ IsSc1GermWith G g Dg ∧
        IsGoodPositionAtGerm c.relOpen c.isRetraction h0 (Dg 0)) :
    ∃ (G : ScNbhdGerm (c.restrictInter hV).φ.model.E (c.restrictInter hV).φ.model.C)
      (Dg : (c.restrictInter hV).φ.model.E 1 → (c.restrictInter hV).φ.model.E 0 →L[ℝ]
        (c.restrictInter hV).F 0),
      G.U 0 ⊆ (c.restrictInter hV).U ∧ IsSc1GermWith G g Dg ∧
        IsGoodPositionAtGerm (c.restrictInter hV).relOpen (c.restrictInter hV).isRetraction
          (c.zero_mem_restrictInter_U hV hxV hφ0 hxV') (Dg 0) := by
  obtain ⟨G, Dg, -, hDg, hgp⟩ := h
  have h0' := c.zero_mem_restrictInter_U hV hxV hφ0 hxV'
  set G₀ := ScNbhdGerm.ofSet (c.restrictInter hV).relOpen.relOpen h0' with hG₀
  have hD : scDeriv (c.restrictInter hV).U (r c.R) 0 = scDeriv c.U (r c.R) 0 :=
    scDeriv_r_of_subset c.relOpen c.isRetraction (c.restrictInter hV).relOpen
      (c.restrictInter hV).isRetraction (c.restrictInter_U_subset hV) h0'
  refine ⟨G.inter G₀, Dg, fun u hu => hu.2, hDg.mono (G.inter_subset_left G₀), ?_, ?_⟩
  · intro y hy
    obtain ⟨v, hv, hvy⟩ := hgp.surj y hy
    exact ⟨v, hD.symm ▸ hv, hvy⟩
  · exact hD.symm ▸ hgp.kernel

/-! ### The linearization at a zero, chart-free -/

namespace StrongBundle

variable (B : StrongBundle PX P) {f : X → Y}

/-- **Part I's linearization `f'(x) : T_xX → Y_x` at a zero `x` on level `1`** (2021 §3.1, before
Definition 3.1.4), read through a chosen strong bundle chart around `x` (`linIntr`); by
`linIntr_chart_independent` it is the one read through every chart (`linZeroAt_eq`). -/
def linZeroAt (hf : B.IsScSmoothSection f) (x : PX.Level 1)
    (h0 : IsZeroAt P f (PX.levelVal 1 x)) : PX.tangentFiber x →ₗ[ℝ] P ⁻¹' {PX.levelVal 1 x} :=
  B.linIntr hf (B.isChart_of_mem (B.exists_chart_mem (PX.levelVal 1 x)).choose_spec.1)
    (B.exists_chart_mem (PX.levelVal 1 x)).choose_spec.2 h0

variable {B}

theorem linZeroAt_eq (hf : B.IsScSmoothSection f) {x : PX.Level 1}
    (h0 : IsZeroAt P f (PX.levelVal 1 x)) {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (hx : PX.levelVal 1 x ∈ c.φ.source) : B.linZeroAt hf x h0 = B.linIntr hf hc hx h0 :=
  B.linIntr_chart_independent hf _ hc _ hx h0

/-- `linZeroAt` depends only on the section. -/
theorem linZeroAt_congr {g : X → Y} (hfg : f = g) (hf : B.IsScSmoothSection f)
    (hg : B.IsScSmoothSection g) (x : PX.Level 1) (h0f : IsZeroAt P f (PX.levelVal 1 x))
    (h0g : IsZeroAt P g (PX.levelVal 1 x)) : B.linZeroAt hf x h0f = B.linZeroAt hg x h0g := by
  subst hfg; rfl

end StrongBundle

namespace StrongBundle.LocalIso

variable {B : StrongBundle PX P} {B' : StrongBundle PX' P'} {U : Set X} {U' : Set X'}
  (L : LocalIso B B' U U') {f : X → Y} {f' : X' → Y'}

/-- **The linearization at a zero is carried along a local strong bundle isomorphism**:
`Φ (f'(x) α) = f''(x') (Tϕ(x) α)` for `f = Ψ ∘ f' ∘ ϕ` on `U`, `ϕ(x) = x'`, read through any
charts `c` at `x` and `c'` at `x'`. -/
theorem linIntr_transport (hf : B.IsScSmoothSection f) (hf' : B'.IsScSmoothSection f')
    (heq : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) {x : PX.Level 1} {x' : PX'.Level 1}
    (hxU : PX.levelVal 1 x ∈ U) (hxx' : L.ϕ (PX.levelVal 1 x) = PX'.levelVal 1 x')
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (hx : PX.levelVal 1 x ∈ c.φ.source)
    {c' : StrongBundleChart PX' P'} (hc' : B'.IsChart c') (hx' : PX'.levelVal 1 x' ∈ c'.φ.source)
    (h0 : IsZeroAt P f (PX.levelVal 1 x)) (h0' : IsZeroAt P' f' (PX'.levelVal 1 x'))
    (α : PX.tangentFiber x) :
    L.Φ (B.linIntr hf hc hx h0 α : Y) =
      (B'.linIntr hf' hc' hx' h0' (tangentMapOnCLM L.base.isScSmoothOn hxU hxx' α) : Y') := by
  have hU' := L.isOpen_U'
  have hx'U' : PX'.levelVal 1 x' ∈ U' := hxx' ▸ L.base.mapsTo hxU
  set c₁ := c'.restrictInter hU' with hc₁def
  have hc₁ : B'.IsChart c₁ := hc'.restrictInter hU'
  have hx₁ : PX'.levelVal 1 x' ∈ c₁.φ.source := c'.mem_restrictInter_source hU' hx' hx'U'
  have hsub : c₁.φ.source ⊆ U' := c'.restrictInter_source_subset hU'
  set d := L.transportChart c₁ hsub with hddef
  have hd : B.IsChart d := L.isChart_transportChart c₁ hsub hc₁
  have hxd : PX.levelVal 1 x ∈ d.φ.source := ⟨hxU, by
    change L.ϕ (PX.levelVal 1 x) ∈ c₁.φ.source
    rw [hxx']; exact hx₁⟩
  rw [B.linIntr_chart_independent hf hc hd hx hxd h0,
    B'.linIntr_chart_independent hf' hc' hc₁ hx' hx₁ h0']
  set v := B.linIntr hf hd hxd h0 α
  set w := B'.linIntr hf' hc₁ hx₁ h0' (tangentMapOnCLM L.base.isScSmoothOn hxU hxx' α)
  have hPv : P' (L.Φ (v : Y)) = PX'.levelVal 1 x' := by
    rw [L.covers _ (by rw [show P v = _ from v.2]; exact hxU), show P v = _ from v.2, hxx']
  have key : c₁.fiberLin hx₁ ⟨L.Φ v, hPv⟩ = c₁.fiberLin hx₁ w := by
    rw [StrongBundle.fiberLin_linIntr]
    have h1 : c₁.fiberLin hx₁ ⟨L.Φ v, hPv⟩ = d.fiberLin hxd v := rfl
    rw [h1, StrongBundle.fiberLin_linIntr, StrongBundleChart.linChart_apply,
      StrongBundleChart.linChart_apply]
    have hlift : levelLift d.φ 1 (PX.levelVal 1 x) = levelLift c₁.φ 1 (PX'.levelVal 1 x') := by
      change Function.invFun _ (c₁.φ (L.ϕ (PX.levelVal 1 x))) = _
      rw [hxx']; rfl
    have hz : levelLift c₁.φ 1 (PX'.levelVal 1 x') ∈ c₁.φ.model.E.lvlSet c₁.U 1 := by
      rw [ScBanach.mem_lvlSet, PX'.toBase_levelLift c₁.isChart hx₁ (levelVal_mem x')]
      exact mem_U_of_mem_O c₁.isRetraction (c₁.r_image ▸ c₁.φ.mapsTo_model _ hx₁)
    have heqU : EqOn (d.principal f ∘ r d.R) (c₁.principal f' ∘ r c₁.R) c₁.U := fun u hu =>
      L.principal_transportChart c₁ hsub heq hf'.1 (c₁.r_image ▸ ⟨u, hu, rfl⟩)
    have hD := scDeriv_eq_of_eqOn_relOpen c₁.relOpen (StrongBundle.isSc1_principal_comp_r hf hd)
      (StrongBundle.isSc1_principal_comp_r hf' hc₁) subset_rfl subset_rfl heqU hz
    have hα : PX.levelVal 1 (PX.tangentProj α.1) ∈ U ∩ L.ϕ ⁻¹' c₁.φ.source := by
      rw [show PX.tangentProj α.1 = x from α.2]; exact hxd
    have hvec := chartVec_tangentMapOn_of_isScDiffeoOn L.base c₁.isChart hα
    rw [hlift]
    change scDeriv c₁.U (d.principal f ∘ r d.R) _ _ = _
    erw [hD]
    rw [coe_tangentFiberEquiv_apply, coe_tangentFiberEquiv_apply, tangentMapOnCLM_apply]
    exact congrArg _ hvec.symm
  exact congrArg Subtype.val (c₁.fiberLin_injective hx₁ key)

/-- **Zeros correspond** under `f = Ψ ∘ f' ∘ ϕ` on `U`. -/
theorem isZeroAt_of_eqOn (heq : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) {x : X} (hx : x ∈ U)
    (h0 : IsZeroAt P' f' (L.ϕ x)) : IsZeroAt P f x := by
  have hlin := L.fiber_linear_inv (L.ϕ x) x (L.base.mapsTo hx) (L.base.left_inv x hx)
  have h := congrArg Subtype.val hlin.map_zero
  rw [IsZeroAt, heq hx]
  exact (congrArg L.Ψ h0).trans h

/-- `linIntr_transport` for the chart-free `linZeroAt`. -/
theorem linZeroAt_transport (hf : B.IsScSmoothSection f) (hf' : B'.IsScSmoothSection f')
    (heq : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) {x : PX.Level 1} {x' : PX'.Level 1}
    (hxU : PX.levelVal 1 x ∈ U) (hxx' : L.ϕ (PX.levelVal 1 x) = PX'.levelVal 1 x')
    (h0 : IsZeroAt P f (PX.levelVal 1 x)) (h0' : IsZeroAt P' f' (PX'.levelVal 1 x'))
    (α : PX.tangentFiber x) :
    L.Φ (B.linZeroAt hf x h0 α : Y) =
      (B'.linZeroAt hf' x' h0' (tangentMapOnCLM L.base.isScSmoothOn hxU hxx' α) : Y') :=
  L.linIntr_transport hf hf' heq hxU hxx' _ _ _ _ h0 h0' α

/-- **Part I's good position in a tame chart is carried along a local strong bundle
isomorphism** (Definition 3.6.6): if `f = Ψ ∘ f' ∘ ϕ` on `U` and `f'` is in good position at
`ϕ(x)` in a tame chart `c'`, then `f` is in good position at `x` in the transported chart of the
restriction of `c'` to `dom φ' ∩ U'`, with the same filling, sc⁺-germ, conjugation and
derivative family (as `isScFredholmGermTame`). -/
theorem isGoodPositionGermTame (hf : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) (hf' : IsSection P' f') {x : X}
    (hx : x ∈ U) (h : B'.IsGoodPositionGermTame f' (L.ϕ x)) : B.IsGoodPositionGermTame f x := by
  obtain ⟨hs, c', hc', hxc', hφ0, h0, g, s, hfill, hsm, hs0, hconj, hgp⟩ := h
  have hU' := L.isOpen_U'
  have hsub : (c'.restrictInter hU').φ.source ⊆ U' := c'.restrictInter_source_subset hU'
  have hxU' : L.ϕ x ∈ U' := L.base.mapsTo hx
  have h0₁ := c'.zero_mem_restrictInter_U hU' hxc' hφ0 hxU'
  obtain ⟨hfill₁, hsm₁, hconj₁⟩ :=
    c'.germData_restrictInter hU' hxc' hφ0 hxU' h0 hfill hsm hconj
  obtain ⟨G, Dg, hG, hDg, hgp₁⟩ :=
    StrongBundleChart.goodPositionData_restrictInter hU' hxc' hφ0 hxU' h0 hgp
  refine ⟨(L.mem_smoothSet_iff hx).2 hs, L.transportChart (c'.restrictInter hU') hsub,
    L.isTameChart_transportChart _ hsub (hc'.restrictInter hU'),
    ⟨hx, c'.mem_restrictInter_source hU' hxc' hxU'⟩, hφ0, h0₁, g, s, ?_, hsm₁, hs0, hconj₁,
    G, Dg, hG, hDg, hgp₁⟩
  refine { hfill₁ with eq_on := ?_ }
  filter_upwards [hfill₁.eq_on] with z hz hzO
  rw [← hz hzO]
  exact L.principal_transportChart _ hsub hf hf' ((c'.restrictInter hU').r_image ▸ hzO)

end StrongBundle.LocalIso

end Transport

/-! ### The transition law of the linearizations of the representatives -/

namespace GCT.VectorBundle.StrongPolyfoldBundleConstruction

universe u

open StrongBundleUniformizerConstruction StrongBundleUniformizerData PolyfoldConstruction

variable {C : GCT.{u}} {V : C.VectorBundle} {S : C.PolyfoldConstruction}
  (Q : V.StrongPolyfoldBundleConstruction S) (f : V.SectionFunctor)

/-- **The section `a ↦ (a, f_Ψ̄(s a))` of `M(Ψ̄, Ψ̄') → M(Ψ, Ψ')`** (the pull-back `s*f_Ψ̄`). -/
def transSection (Ψ Ψ' : Q.Unif) (a : S.Tr (Q.baseUnif Ψ) (Q.baseUnif Ψ')) :
    Q.TransSpace Ψ Ψ' :=
  ⟨(a, Ψ.1.localRep f a.src), Ψ.1.p_localRep f a.src⟩

theorem isSection_transSection (Ψ Ψ' : Q.Unif) :
    IsSection (pullbackProj Ψ.1.p fun a : S.Tr (Q.baseUnif Ψ) (Q.baseUnif Ψ') => a.src)
      (Q.transSection f Ψ Ψ') := fun _ => rfl

/-- On a sheet `W` of `s̄`, `s*f_Ψ̄ = s̄⁻¹ ∘ f_Ψ̄ ∘ s`. -/
theorem eqOn_transSection_src (Ψ Ψ' : Q.Unif) {W : Set (S.Tr (Q.baseUnif Ψ) (Q.baseUnif Ψ'))}
    {W' : Set Ψ.1.base.O}
    (hi : (Q.transBundle Ψ Ψ').IsStrongBundleIsoOn Ψ.1.B
      (Ψ.1.B.isStrongBundleMap_pullbackProj' (Q.isScSmoothMap_trSrc Ψ Ψ')) W W') :
    EqOn (Q.transSection f Ψ Ψ') (hi.toLocalIso.Ψ ∘ Ψ.1.localRep f ∘ hi.toLocalIso.ϕ) W :=
  fun b hb => (hi.toLocalIso.zero.left_inv (Q.transSection f Ψ Ψ' b) hb).symm

/-- On a sheet `W` of `t̄`, `s*f_Ψ̄ = t̄⁻¹ ∘ f_Ψ̄' ∘ t` (`localRep_transAct`). -/
theorem eqOn_transSection_tgt (Ψ Ψ' : Q.Unif) {W : Set (S.Tr (Q.baseUnif Ψ) (Q.baseUnif Ψ'))}
    {W' : Set Ψ'.1.base.O}
    (hi : (Q.transBundle Ψ Ψ').IsStrongBundleIsoOn Ψ'.1.B (Q.isStrongBundleMap_trans Ψ Ψ') W W') :
    EqOn (Q.transSection f Ψ Ψ') (hi.toLocalIso.Ψ ∘ Ψ'.1.localRep f ∘ hi.toLocalIso.ϕ) W := by
  intro b hb
  have h1 := hi.toLocalIso.zero.left_inv (Q.transSection f Ψ Ψ' b) hb
  have h2 : hi.toLocalIso.Φ (Q.transSection f Ψ Ψ' b) = Ψ'.1.localRep f b.tgt :=
    (Ψ.1.localRep_transAct f b).symm
  rw [← h1, h2]
  rfl

/-- **`s*f_Ψ̄` is sc-smooth** if `f_Ψ̄` is (locally it is `s̄⁻¹ ∘ f_Ψ̄ ∘ s`). -/
theorem isScSmoothSection_transSection (Ψ Ψ' : Q.Unif)
    (hf : Ψ.1.B.IsScSmoothSection (Ψ.1.localRep f)) :
    (Q.transBundle Ψ Ψ').IsScSmoothSection (Q.transSection f Ψ Ψ') := by
  refine ⟨Q.isSection_transSection f Ψ Ψ', MPolyfold.IsScSmoothOn.of_locally isOpen_univ
    fun a _ => ?_⟩
  obtain ⟨W, W', ha, hi⟩ := Q.isLocalStrongBundleIso_src Ψ Ψ' a
  have hmaps : MapsTo (Ψ.1.localRep f ∘ hi.toLocalIso.ϕ) W (Ψ.1.p ⁻¹' W') := fun b hb => by
    change Ψ.1.p (Ψ.1.localRep f (hi.toLocalIso.ϕ b)) ∈ W'
    rw [Ψ.1.p_localRep]; exact hi.toLocalIso.base.mapsTo hb
  exact ⟨W, hi.toLocalIso.isOpen_U, ha, subset_univ _,
    (MPolyfold.IsScSmoothOn.comp hi.toLocalIso.zero.isScSmoothOn_inv
      (MPolyfold.IsScSmoothOn.comp hf.2 hi.toLocalIso.base.isScSmoothOn (mapsTo_univ _ _))
      hmaps).congr (Q.eqOn_transSection_src f Ψ Ψ' hi).symm⟩

/-- **The transition law of the linearizations** (behind "the definition does not depend on
the choice of `Ψ̄`" after (18.1), p. 845): for `a = (q, φ, q') ∈ M(Ψ, Ψ')`, `q`, `q'` on level
`1` and zeros of `f_Ψ̄`, `f_Ψ̄'`, `f'_Ψ̄'(q') (Tσ(q) h) = T(a, f'_Ψ̄(q) h)`, `T(a, ·)` the fibre
map `K_q → K'_{q'}` of `t̄` (the lift of `μ(φ)`). -/
theorem linZeroAt_transTangent (Ψ Ψ' : Q.Unif) (a : S.Tr (Q.baseUnif Ψ) (Q.baseUnif Ψ'))
    (hf : Ψ.1.B.IsScSmoothSection (Ψ.1.localRep f))
    (hf' : Ψ'.1.B.IsScSmoothSection (Ψ'.1.localRep f)) {x : Ψ.1.base.P.Level 1}
    {y : Ψ'.1.base.P.Level 1} (hx : Ψ.1.base.P.levelVal 1 x = a.src)
    (hy : Ψ'.1.base.P.levelVal 1 y = a.tgt)
    (h0 : IsZeroAt Ψ.1.p (Ψ.1.localRep f) (Ψ.1.base.P.levelVal 1 x))
    (h0' : IsZeroAt Ψ'.1.p (Ψ'.1.localRep f) (Ψ'.1.base.P.levelVal 1 y))
    (v : Ψ.1.base.P.tangentFiber x) :
    (Ψ'.1.B.linZeroAt hf' y h0' (S.transTangent a hx hy v) : Ψ'.1.K) =
      transAct a (Ψ.1.B.linZeroAt hf x h0 v)
        ((show Ψ.1.p (Ψ.1.B.linZeroAt hf x h0 v : Ψ.1.K) = _ from
          (Ψ.1.B.linZeroAt hf x h0 v).2).trans hx) := by
  obtain ⟨Ws, Ws', has, his⟩ := Q.isLocalStrongBundleIso_src Ψ Ψ' a
  obtain ⟨Wt, Wt', hat, hit⟩ := Q.isLocalStrongBundleIso_trans Ψ Ψ' a
  set Ls := his.toLocalIso with hLs
  set Lt := hit.toLocalIso with hLt
  have hg := Q.isScSmoothSection_transSection f Ψ Ψ' hf
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
  have hxaU : (S.transPolyfold (Q.baseUnif Ψ) (Q.baseUnif Ψ')).levelVal 1 xa ∈ Wt := by
    rw [hxa]; exact hat
  have hxay : Lt.ϕ ((S.transPolyfold (Q.baseUnif Ψ) (Q.baseUnif Ψ')).levelVal 1 xa) =
      Ψ'.1.base.P.levelVal 1 y := by rw [hxa, hy]; rfl
  have h0g : IsZeroAt _ (Q.transSection f Ψ Ψ')
      ((S.transPolyfold (Q.baseUnif Ψ) (Q.baseUnif Ψ')).levelVal 1 xa) :=
    Lt.isZeroAt_of_eqOn (Q.eqOn_transSection_tgt f Ψ Ψ' hit) hxaU (by rw [hxay]; exact h0')
  have heqA : EqOn (Ψ.1.localRep f) (Ls.symm.Ψ ∘ Q.transSection f Ψ Ψ' ∘ Ls.symm.ϕ) Ws' :=
    fun q hq => by
      change Ψ.1.localRep f q = Ψ.1.localRep f (Ls.ϕ (Ls.g q))
      rw [Ls.base.right_inv q hq]
  have hA := Ls.symm.linZeroAt_transport hf hg heqA hqs hxxa h0 h0g v
  set w := tangentMapOnCLM Ls.symm.base.isScSmoothOn hqs hxxa v with hwdef
  have hB := Lt.linZeroAt_transport hg hf' (Q.eqOn_transSection_tgt f Ψ Ψ' hit) hxaU hxay h0g
    h0' w
  -- `Tσ(q) = Tt ∘ T(s|W)⁻¹` at `v`, through the admissible triple of the two sheets
  have hW : IsOpen (Ws ∩ Wt) := Ls.isOpen_U.inter Lt.isOpen_U
  let T : S.AdmissibleTriple a := ⟨_, Ws ∩ Wt, _, Ls.g, Lt.g, ⟨has, hat⟩,
    Ls.base.restrict hW inter_subset_left, Lt.base.restrict hW inter_subset_right⟩
  have hTo : IsOpen T.srcSet := T.isScDiffeoOn_src.isOpen_target
  have hfs : Ψ.1.base.P.IsScSmoothOn _ Ls.g T.srcSet :=
    Ls.base.isScSmoothOn_inv.mono hTo inter_subset_left
  have hmaps : MapsTo Ls.g T.srcSet Wt := fun p hp => hp.2.2
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
  -- `t̄ ∘ s̄⁻¹ = T(a, ·)` on `K_q`
  set k := (Ψ.1.B.linZeroAt hf x h0 v : Ψ.1.K) with hkdef
  have hk : Ψ.1.p k = a.src := (show Ψ.1.p k = _ from (Ψ.1.B.linZeroAt hf x h0 v).2).trans hx
  have hkW : Ψ.1.p k ∈ Ws' := by rw [hk]; exact Ls.base.mapsTo has
  have e : Ls.Ψ k = (⟨(a, k), hk⟩ : Q.TransSpace Ψ Ψ') := by
    refine Subtype.ext (Prod.ext ?_ ?_)
    · change pullbackProj Ψ.1.p _ (Ls.Ψ k) = a
      rw [Ls.covers_inv k hkW, hk]; exact Ls.base.left_inv a has
    · exact Ls.zero.right_inv k hkW
  change Q.transT Ψ Ψ' (Ls.Ψ k) = _
  rw [e]
  rfl

end GCT.VectorBundle.StrongPolyfoldBundleConstruction

end Polyfold
