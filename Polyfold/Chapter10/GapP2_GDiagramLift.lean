import Polyfold.Chapter10.GapP2_GDiagram

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 10, §10.5 (pp. 505–506; 2017: pp. 365–366): **the lift `Q` of the germ `q` and
the commutative diagram (10.25)**.  Numbers and pages are the 2021 text's.

# The local expression `Q` of a diagram of strong bundles

## The text, paraphrased

(p. 506) For a diagram `D : W ←Φ W'' →Ψ W'` covering `d : X ←φ X'' →ψ X'` and the data
`(x'', a, b)` of the germ `q` (`EPLocalization.Diagram.exists_germ_q`), there is a natural lift
`Q : W|O(X, x) → W'|O(X', x')`, a strong bundle map with `P' ∘ Q = q ∘ P`, (10.25), "of
equivariant maps"; `q` and `Q` depend on the representative `D`.

## What is formalized

* `StrongBundle.IsLocalMap₂ B B' f Φ U`: a strong bundle map `Y|U → Y'` covering `f` (linear on
  the fibres over `U`, sc-smooth on `Y|U` at level `[0]` and, through a map agreeing with it, at
  level `[1]`), with no condition off `Y|U`; `covers`, `comp`, `mono`,
  `IsLocalIso₂.isLocalMap₂`, `IsStrongBundleMap.isLocalMap₂`.
* **`SBLocalization.SDiagram.exists_lift_Q`**: for the data `(x'', a, b)` there are natural
  representations `U(x)`, `U(x')`, the germ `q = Q_b ∘ ψ ∘ Q_a⁻¹ : U(x) → U(x')` with
  `q(x) = x'` and `q(g ∗ z) = γ(g) ∗ q(z)`, and `Q = H_b ∘ Ψ ∘ H_a⁻¹ : W|U(x) → W'`, a local strong
  bundle map covering `q` (`P' ∘ Q = q ∘ P`, (10.25)) with `Q(g ∗ w) = γ(g) ∗ Q(w)` for the
  natural lifts; `H_a(v) = μ(a_{P(v)}, Φ(v))` and `H_b(u) = μ'(b_{P'(u)}, u)` are the transports of
  `IsStrongBundleEquivalence.exists_transport`.

## The choices made

* "Strong bundle map `W|O(X, x) → W'|O(X', x')`" is read as `IsLocalMap₂` on `W|U(x)`, the germ
  being represented on the natural representation `U(x)`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

section LocalMap₂

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {X' : Type*} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type*} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]
  {X'' : Type*} [TopologicalSpace X''] [T2Space X''] [ParacompactSpace X''] {PX'' : MPolyfold X''}
  {Y'' : Type*} [TopologicalSpace Y''] [T2Space Y''] [ParacompactSpace Y''] {P'' : Y'' → X''}
  [∀ x, AddCommGroup (P'' ⁻¹' {x})] [∀ x, Module ℝ (P'' ⁻¹' {x})]

namespace StrongBundle

/-- **A strong bundle map `Y|U → Y'` covering `f`**, with no condition off `Y|U`: linear from
`Y_x` to `Y'_{f(x)}` for `x ∈ U`, sc-smooth on `Y|U` at level `[0]`, and, through a map `Φ₁` of
`Y[1]` agreeing with `Φ`, at level `[1]`. -/
structure IsLocalMap₂ (B : StrongBundle PX P) (B' : StrongBundle PX' P') (f : X → X')
    (Φ : Y → Y') (U : Set X) : Prop where
  fiber_linear : ∀ x ∈ U, ∃ L : P ⁻¹' {x} →ₗ[ℝ] P' ⁻¹' {f x}, ∀ v, (L v : Y') = Φ v
  zero : B.toMPolyfold0.IsScSmoothOn B'.toMPolyfold0 Φ (P ⁻¹' U)
  one : ∃ Φ₁ : B.One → B'.One, (∀ y, P (B.oneVal y) ∈ U → B'.oneVal (Φ₁ y) = Φ (B.oneVal y)) ∧
    B.toMPolyfold1.IsScSmoothOn B'.toMPolyfold1 Φ₁ ((P ∘ B.oneVal) ⁻¹' U)

variable {B : StrongBundle PX P} {B' : StrongBundle PX' P'} {B'' : StrongBundle PX'' P''}
  {f : X → X'} {Φ : Y → Y'} {U : Set X}

namespace IsLocalMap₂

theorem covers (h : B.IsLocalMap₂ B' f Φ U) {w : Y} (hw : P w ∈ U) : P' (Φ w) = f (P w) := by
  obtain ⟨L, hL⟩ := h.fiber_linear (P w) hw
  rw [← hL ⟨w, rfl⟩]
  exact (L ⟨w, rfl⟩).2

/-- Restriction to an open subset. -/
theorem mono (h : B.IsLocalMap₂ B' f Φ U) {U₀ : Set X} (hU₀ : IsOpen U₀) (hsub : U₀ ⊆ U) :
    B.IsLocalMap₂ B' f Φ U₀ where
  fiber_linear x hx := h.fiber_linear x (hsub hx)
  zero := h.zero.mono (hU₀.preimage B.continuous) (preimage_mono hsub)
  one := let ⟨Φ₁, h₁, h₂⟩ := h.one
    ⟨Φ₁, fun y hy => h₁ y (hsub hy),
      h₂.mono (hU₀.preimage (B.continuous.comp B.continuous_oneVal)) (preimage_mono hsub)⟩

/-- **Composition** `Y|U → Y'|U' → Y''` for `f(U) ⊆ U'`. -/
theorem comp {f₂ : X' → X''} {Φ₂ : Y' → Y''} {U' : Set X'} (h₂ : B'.IsLocalMap₂ B'' f₂ Φ₂ U')
    (h₁ : B.IsLocalMap₂ B' f Φ U) (hf : MapsTo f U U') :
    B.IsLocalMap₂ B'' (f₂ ∘ f) (Φ₂ ∘ Φ) U where
  fiber_linear x hx := by
    obtain ⟨L₁, hL₁⟩ := h₁.fiber_linear x hx
    obtain ⟨L₂, hL₂⟩ := h₂.fiber_linear (f x) (hf hx)
    exact ⟨L₂.comp L₁, fun v => by
      simp only [LinearMap.coe_comp, Function.comp_apply, hL₂, hL₁]⟩
  zero := MPolyfold.IsScSmoothOn.comp h₂.zero h₁.zero fun w hw => by
    change P' (Φ w) ∈ U'; rw [h₁.covers hw]; exact hf hw
  one := by
    obtain ⟨Φ₁, a₁, b₁⟩ := h₁.one
    obtain ⟨Φ₂₁, a₂, b₂⟩ := h₂.one
    have hm : ∀ y, P (B.oneVal y) ∈ U → P' (B'.oneVal (Φ₁ y)) ∈ U' := fun y hy => by
      rw [a₁ y hy, h₁.covers hy]; exact hf hy
    exact ⟨Φ₂₁ ∘ Φ₁, fun y hy => by simp only [Function.comp_apply, a₂ _ (hm y hy), a₁ y hy],
      MPolyfold.IsScSmoothOn.comp b₂ b₁ fun y hy => hm y hy⟩

end IsLocalMap₂

/-- A local strong bundle isomorphism is a local strong bundle map. -/
theorem IsLocalIso₂.isLocalMap₂ {g : X' → X} {Ψ : Y' → Y} {U' : Set X'}
    (h : B.IsLocalIso₂ B' f g Φ Ψ U U') : B.IsLocalMap₂ B' f Φ U where
  fiber_linear := h.fiber_linear
  zero := h.zero.isScSmoothOn
  one := let ⟨Φ₁, _, h₁, _, h₃⟩ := h.one; ⟨Φ₁, h₁, h₃.isScSmoothOn⟩

/-- A strong bundle map is a local strong bundle map over every open set. -/
theorem IsStrongBundleMap.isLocalMap₂ (h : B.IsStrongBundleMap B' f Φ) (hU : IsOpen U) :
    B.IsLocalMap₂ B' f Φ U where
  fiber_linear x _ := ⟨h.fiberLinearMap x, fun _ => rfl⟩
  zero := h.isScSmoothMap.mono (hU.preimage B.continuous) (subset_univ _)
  one := ⟨oneRestrict B B' Φ h.mapsTo_oneSet, fun _ _ => rfl,
    h.isScSmoothMap_one.mono (hU.preimage (B.continuous.comp B.continuous_oneVal))
      (subset_univ _)⟩

end StrongBundle

end LocalMap₂

/-! ### The lift `Q` -/

namespace SBLocalization

open EPLocalization EpStrongBundle StrongBundle

variable {A A' : SEP.{u}}

/-- **The local expressions `q`, `Q` of (10.25)** (2021 pp. 505–506): for a diagram
`D : W ←Φ W'' →Ψ W'` covering `d : X ←φ X'' →ψ X'`, `x''` and `a : φ(x'') → x`,
`b : ψ(x'') → x'`, there are natural representations `U(x)`, `U(x')`, an sc-smooth
`q : U(x) → U(x')` with `q(x) = x'` and `q(g ∗ z) = γ(g) ∗ q(z)` (`γ = d.isotropyHom a b`), and a
strong bundle map `Q : W|U(x) → W'` covering `q` (`P' ∘ Q = q ∘ P`, (10.25)) with
`Q(g ∗ w) = γ(g) ∗ Q(w)` for the natural lifts. -/
theorem SDiagram.exists_lift_Q (D : SDiagram A A') {x : A.Obj} {x' : A'.Obj} {x'' : D.B.Obj}
    (a : A.Mor) (ha : A.X.src a = (SEP.Hom.ϕ D.Φ).obj x'') (ha' : A.X.tgt a = x) (b : A'.Mor)
    (hb : A'.X.src b = (SEP.Hom.ϕ D.Ψ).obj x'') (hb' : A'.X.tgt b = x') :
    ∃ (R : A.X.NaturalRep x) (R' : A'.X.NaturalRep x') (q : A.Obj → A'.Obj) (Q : A.W → A'.W),
      A.X.PObj.IsScSmoothOn A'.X.PObj q R.U ∧ MapsTo q R.U R'.U ∧ q x = x' ∧
      (∀ g, ∀ z ∈ R.U, q (R.Φ g z) = R'.Φ (D.base.isotropyHom a ha ha' b hb hb' g) (q z)) ∧
      A.B.IsLocalMap₂ A'.B q Q R.U ∧ (∀ w, A.P w ∈ R.U → A'.P (Q w) = q (A.P w)) ∧
      ∀ g w (hw : A.P w ∈ R.U) (hw' : A'.P (Q w) ∈ R'.U),
        Q (A.E.natLift R g w hw) =
          A'.E.natLift R' (D.base.isotropyHom a ha ha' b hb hb' g) (Q w) hw' := by
  have hΦ := D.hΦ
  have hF := hΦ.isEquivalence_base
  have hsΨ := SEP.Hom.isStrongBundleFunctor D.Ψ
  obtain ⟨Ta, hTa⟩ := EpFunctor.exists_transportChart hF.isLocalScDiffeo_obj ha ha'
  obtain ⟨Tb, hTb⟩ := EpFunctor.exists_transportChart
    (EpFunctor.IsEquivalence.id A'.X).isLocalScDiffeo_obj hb hb'
  obtain ⟨Sa, hSao, hx''Sa, hSaW, Ha', hHa⟩ := hΦ.exists_transport Ta
  obtain ⟨Sb, hSbo, hySb, hSbW, Hb', hHb⟩ :=
    (isStrongBundleEquivalence_id A'.E).exists_transport Tb
  -- natural representations at `x'`, `ψ(x'')`, `x''`, `x`
  obtain ⟨R', -⟩ := A'.X.theorem_7_1_13 x' isOpen_univ (mem_univ _)
  have hOb : IsOpen (Sb ∩ Tb.Q ⁻¹' R'.U) :=
    (Tb.continuousOn_Q.mono hSbW).isOpen_inter_preimage hSbo R'.isOpen_U
  obtain ⟨Rb, hRb⟩ := A'.X.theorem_7_1_13 ((SEP.Hom.ϕ D.Ψ).obj x'') hOb
    ⟨hySb, by rw [mem_preimage, Tb.Q_self]; exact R'.mem_U⟩
  have hRbS : Rb.U ⊆ Sb := fun v hv => (hRb hv).1
  have hRbW : Rb.U ⊆ Tb.W := fun v hv => hSbW (hRbS hv)
  obtain ⟨R₀, -⟩ := A.X.theorem_7_1_13 x isOpen_univ (mem_univ _)
  have hO'' : IsOpen ((Sa ∩ Ta.Q ⁻¹' R₀.U) ∩ (SEP.Hom.ϕ D.Ψ).obj ⁻¹' Rb.U) :=
    ((Ta.continuousOn_Q.mono hSaW).isOpen_inter_preimage hSao R₀.isOpen_U).inter
      (Rb.isOpen_U.preimage (SEP.Hom.ϕ D.Ψ).continuous_obj')
  obtain ⟨R'', hR''⟩ := D.B.X.theorem_7_1_13 x'' hO''
    ⟨⟨hx''Sa, by rw [mem_preimage, Ta.Q_self]; exact R₀.mem_U⟩, Rb.mem_U⟩
  have hR''S : R''.U ⊆ Sa := fun v hv => (hR'' hv).1.1
  have hR''W : R''.U ⊆ Ta.W := fun v hv => hSaW (hR''S hv)
  obtain ⟨R, hRU, -, hRΓ, hRequiv⟩ :=
    Ta.exists_naturalRep_push hF R'' R₀ fun v hv => ⟨hR''W hv, (hR'' hv).1.2⟩
  have hd := Ta.isScDiffeoOn_image R''.isOpen_U hR''W
  rw [← hRU] at hd
  have hQinv : ∀ z ∈ R.U, Ta.Qinv z ∈ R''.U := fun z hz => hd.mapsTo_inv hz
  have hψb : ∀ v ∈ R''.U, (SEP.Hom.ϕ D.Ψ).obj v ∈ Rb.U := fun v hv => (hR'' hv).2
  have hbQ := Tb.Q_Φ_of_subset Rb R' fun v hv => ⟨hRbW hv, (hRb hv).2⟩
  -- the three local maps
  have hHaR := hHa.restrict_image R''.isOpen_U hR''S
  rw [← hRU] at hHaR
  have hM₁ := hHaR.symm.isLocalMap₂
  have hM₂ := hsΨ.isStrongBundleMap_obj.isLocalMap₂ R''.isOpen_U
  have hM₃ := hHb.isLocalMap₂.mono Rb.isOpen_U hRbS
  have hM := hM₃.comp (hM₂.comp hM₁ fun z hz => hQinv z hz) fun z hz => hψb _ (hQinv z hz)
  refine ⟨R, R', _, _, ?_, fun z hz => (hRb (hψb _ (hQinv z hz))).2, ?_, fun g z hz => ?_, hM,
    fun w hw => hM.covers hw, fun g w hw hw' => ?_⟩
  · exact MPolyfold.IsScSmoothOn.comp Tb.isScDiffeoOn_Q.isScSmoothOn
      (MPolyfold.IsScSmoothOn.comp ((SEP.Hom.ϕ D.Ψ).isScSmoothMap_obj.mono isOpen_univ (subset_univ _))
        hd.isScSmoothOn_inv (mapsTo_univ _ _)) fun z hz => hRbW (hψb _ (hQinv z hz))
  · have hx : Ta.Qinv x = x'' :=
      (congrArg Ta.Qinv Ta.Q_self).symm.trans (Ta.isScDiffeoOn_Q.left_inv _ Ta.mem_W)
    simp only [hx, Tb.Q_self]
  · obtain ⟨k, rfl⟩ := (Ta.bijective_conj hF).2 g
    have hv := hQinv z hz
    have hzv : Ta.Q (Ta.Qinv z) = z := hd.right_inv z hz
    have h1 : Ta.Qinv (R.Φ (Ta.conj k) z) = R''.Φ k (Ta.Qinv z) := by
      rw [← hzv, ← hRequiv k _ hv, hzv]
      exact Ta.isScDiffeoOn_Q.left_inv _ (hR''W (R''.mapsTo_Φ k hv))
    have h2 := (SEP.Hom.ϕ D.Ψ).obj_Φ R'' Rb subset_rfl R''.isConnected_U.isPreconnected R''.mem_U hψb k _ hv
    have h3 := hbQ ((SEP.Hom.ϕ D.Ψ).isotropyHom x'' k) _ (hψb _ hv)
    have hγ := D.base.isotropyHom_conj a ha ha' b hb hb' Ta hTa Tb hTb k
    simp only [h1, h2, h3]
    exact congrArg (fun h => R'.Φ h (Tb.Q ((SEP.Hom.ϕ D.Ψ).obj (Ta.Qinv z)))) hγ.symm
  · obtain ⟨k, rfl⟩ := (Ta.bijective_conj hF).2 g
    have hv : D.B.P (Ha' w) ∈ R''.U := hHaR.symm.mapsTo hw
    have hHv : A.E.lrAct (Ta.ψ (D.B.P (Ha' w))) ((SEP.Hom.Φ D.Φ).obj (Ha' w)) = w :=
      hHaR.right_inv hw
    have hPw : A.P w = Ta.Q (D.B.P (Ha' w)) := by
      have := hHaR.covers hv
      rwa [hHv] at this
    -- `H_a⁻¹(conj_a(k) ∗ w) = k ∗ H_a⁻¹(w)`
    have hn : D.B.P (D.B.E.lrAct (R''.Γ k (D.B.P (Ha' w))) (Ha' w)) ∈ R''.U := by
      rw [P_lrAct (R''.src_Γ k _ hv).symm, R''.tgt_Γ k _ hv]; exact R''.mapsTo_Φ k hv
    have hA := hΦ.transport_Γ Ta R'' R₀ k subset_rfl hR''W
      (fun u hu => hR''W (R''.mapsTo_Φ k hu)) R''.isConnected_U.isPreconnected R''.mem_U
      (fun u hu => (hR'' hu).1.2) hv
    rw [hHv, ← hPw, ← hRΓ] at hA
    have hA' : Ha' (A.E.lrAct (R.Γ (Ta.conj k) (A.P w)) w) =
        D.B.E.lrAct (R''.Γ k (D.B.P (Ha' w))) (Ha' w) := by
      rw [← hA]; exact hHaR.left_inv hn
    -- `Ψ(k ∗ v) = ψ(k) ∗ Ψ(v)`
    have hΨv : A'.P ((SEP.Hom.Φ D.Ψ).obj (Ha' w)) = (SEP.Hom.ϕ D.Ψ).obj (D.B.P (Ha' w)) :=
      hsΨ.isStrongBundleMap_obj.covers _
    have hΨvU : A'.P ((SEP.Hom.Φ D.Ψ).obj (Ha' w)) ∈ Rb.U := by rw [hΨv]; exact hψb _ hv
    have hB : (SEP.Hom.Φ D.Ψ).obj (D.B.E.lrAct (R''.Γ k (D.B.P (Ha' w))) (Ha' w)) =
        A'.E.lrAct (Rb.Γ ((SEP.Hom.ϕ D.Ψ).isotropyHom x'' k)
          (A'.P ((SEP.Hom.Φ D.Ψ).obj (Ha' w)))) ((SEP.Hom.Φ D.Ψ).obj (Ha' w)) := by
      rw [hsΨ.obj_lrAct (R''.src_Γ k _ hv).symm, hΨv,
        (SEP.Hom.ϕ D.Ψ).mor_Γ R'' Rb subset_rfl R''.isConnected_U.isPreconnected R''.mem_U hψb k
          _ hv]
    -- `H_b(h ∗ u) = conj_b(h) ∗ H_b(u)`
    have hC := (isStrongBundleEquivalence_id A'.E).transport_Γ Tb Rb R'
      ((SEP.Hom.ϕ D.Ψ).isotropyHom x'' k) subset_rfl hRbW
      (fun u hu => hRbW (Rb.mapsTo_Φ _ hu)) Rb.isConnected_U.isPreconnected Rb.mem_U
      (fun u hu => (hRb hu).2) hΨvU
    have hPQ : A'.P (A'.E.lrAct (Tb.ψ (A'.P ((SEP.Hom.Φ D.Ψ).obj (Ha' w))))
        ((SEP.Hom.Φ D.Ψ).obj (Ha' w))) = Tb.Q (A'.P ((SEP.Hom.Φ D.Ψ).obj (Ha' w))) :=
      (isStrongBundleEquivalence_id A'.E).P_transport Tb (hRbW hΨvU)
    have hγ := D.base.isotropyHom_conj a ha ha' b hb hb' Ta hTa Tb hTb k
    rw [natLift_eq_lrAct, natLift_eq_lrAct]
    refine Eq.trans ?_ (congrArg (fun h => A'.E.lrAct (R'.Γ h (A'.P (A'.E.lrAct
      (Tb.ψ (A'.P ((SEP.Hom.Φ D.Ψ).obj (Ha' w)))) ((SEP.Hom.Φ D.Ψ).obj (Ha' w)))))
      (A'.E.lrAct (Tb.ψ (A'.P ((SEP.Hom.Φ D.Ψ).obj (Ha' w)))) ((SEP.Hom.Φ D.Ψ).obj (Ha' w))))
      hγ.symm)
    simp only [Function.comp_apply]
    rw [hA', hB, hPQ]
    exact hC

end SBLocalization

end Polyfold
