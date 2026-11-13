import Polyfold.Chapter16.P3W7W6_ReflexivePush
import Polyfold.Chapter12.P3R2_ReflexiveAuxNormEp
import Polyfold.Chapter11.AuxiliaryNormTransport2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Definitions 16.3.13 and
16.3.14, Proposition 16.3.16 (2), pp. 727–728 (2017: Definitions 16.25, 16.26, Proposition
16.5), with Definition 12.2.8 and Proposition 11.5.1: **mixed convergence and reflexive
auxiliary norms do not depend on the model** (parts (ii) and (iii) of gap G.166).  Numbers and
pages are the 2021 text's.

## What is formalized

* Part I level (namespace `StrongBundle`): `MixedTendsto.congr_eventually`;
  `LocalIso.isFiberSeminorm_comp` (a fibre seminorm pulls back along a local strong bundle
  isomorphism); **`LocalIso.mixedTendsto`**: a local strong bundle isomorphism `Y|U → Y'|U'`
  maps mixed convergent sequences over `U` to mixed convergent sequences (level-0 continuity of
  `Φ`, the local bound `N' ∘ Φ ≤ C·N` of `exists_le_mul_auxNorm`, `mixedTendsto_of_bounded`).
* Diagrams (namespace `SBLocalization`): **`SDiagram.exists_mixedTendsto_transfer`**: for
  `[W ←Φ W'' →Ψ W']` with `Ψ` an equivalence and `W'` with reflexive fibres, a sequence
  `w_k →ᵐ y` in `W_{0,1}` has representatives `w'_k →ᵐ y'` in `W'_{0,1}` of the images,
  `|w'_k| = |D|(|w_k|)` for large `k`, `|y'| = |D|(|y|)`.  The proof moves `w_k` along a morphism
  `P(y) → Φ(b₀)` (`exists_mixedTendsto_μ`), then through the local inverse of `Φ` and the local
  isomorphism `Ψ` at `b₀`.
* **(iii)** `SDiagram.isReflexiveAuxNorm_pullNorm`, `SDiagram.isReflexiveAuxNorm_pushNorm`,
  `GenSBMap.isReflexiveAuxNorm_pullNorm`, `GenSBMap.isReflexiveAuxNorm_pushNorm`: pull-backs
  and push-forwards of reflexive auxiliary norms along generalized strong bundle isomorphisms
  are reflexive (Proposition 11.5.1's transport, Definition 12.2.10 (3)).
* Strong polyfold bundles: `StrongPolyfoldBundleStructure.mixedTendstoIn_of_equiv`
  (**(ii)**: mixed convergence read in one structure gives it in every equivalent one, when
  that one has reflexive fibres), `StrongPolyfoldBundle.mixedTendsto_iff_forall`,
  `StrongPolyfoldBundle.IsReflexiveAuxNorm.of_mem` (a reflexive auxiliary norm is reflexive in
  every model), and **`proposition_16_3_16_two`** (Proposition 16.3.16 (2) as printed: for
  `y_k →ᵐ y` in the sense of Definition 16.3.14 and any reflexive auxiliary norm `n`,
  `n(y) ≤ liminf n(y_k)`).

## Reading

* Definition 16.3.13 and Proposition 16.3.16 are stated for strong polyfold bundles with
  reflexive `1`-fibres; that is the hypothesis `c.HasReflexiveFibers` here (by
  `hasReflexiveFibers_iff_forall` it holds in every model).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace StrongBundle

section PartI

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {X' : Type*} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type*} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]
  {B : StrongBundle PX P} {B' : StrongBundle PX' P'} {U : Set X} {U' : Set X'}

/-- Mixed convergence only depends on the tail of the sequence. -/
theorem MixedTendsto.congr_eventually {w w' : ℕ → B.One} {y : B.One} (hm : B.MixedTendsto w y)
    (h : ∀ᶠ k in atTop, w k = w' k) : B.MixedTendsto w' y := by
  obtain ⟨hP, c, hc, hx, hF, hh⟩ := hm
  exact ⟨hP.congr' (h.mono fun k hk => by simp only [hk]), c, hc, hx, hF,
    fun g => (hh g).congr' (h.mono fun k hk => by simp only [hk])⟩

/-- **A fibre seminorm pulls back along a local strong bundle isomorphism**: for `x ∈ U` and a
seminorm `M` on `(Y'_{0,1})_{ϕ(x)}`, `M ∘ Φ[1]` is a seminorm on `(Y_{0,1})_x`. -/
theorem LocalIso.isFiberSeminorm_comp (L : LocalIso B B' U U') {M : B'.One → ℝ} {x : X}
    (hx : x ∈ U) (hM : B'.IsFiberSeminorm M (L.ϕ x)) : B.IsFiberSeminorm (M ∘ L.Φ₁) x := by
  have hcov : ∀ v : P ⁻¹' {x}, P' (L.Φ v) = L.ϕ x := fun v => by
    have hv : P v = x := v.2
    rw [L.covers v (by rw [hv]; exact hx), hv]
  have hlin := L.fiber_linear x (L.ϕ x) hx rfl
  have hmem : ∀ v : B.oneFiber x,
      ((fiberMapOf P P' L.Φ hcov (v : P ⁻¹' {x}) : P' ⁻¹' {L.ϕ x}) : Y') ∈ B'.oneSet :=
    fun v => L.mem_oneSet_Φ (by rw [show P (v : P ⁻¹' {x}) = x from (v : P ⁻¹' {x}).2]; exact hx)
      v.2
  let ℓ : B.oneFiber x →ₗ[ℝ] B'.oneFiber (L.ϕ x) :=
    { toFun := fun v => ⟨fiberMapOf P P' L.Φ hcov v, hmem v⟩
      map_add' := fun v w => Subtype.ext (hlin.map_add _ _)
      map_smul' := fun t v => Subtype.ext (hlin.map_smul _ _) }
  have hL : ∀ v, L.Φ₁ (B.toOne v) = B'.toOne (ℓ v) := fun v => by
    apply B'.oneVal_injective
    rw [L.oneVal_Φ₁ _ (by rw [B.proj_oneVal_toOne]; exact hx)]
    rfl
  exact ⟨fun t v => by simp only [comp_apply, hL, map_smul]; exact hM.smul t _,
    fun v w => by simp only [comp_apply, hL, map_add]; exact hM.add_le _ _⟩

/-- **A local strong bundle isomorphism preserves mixed convergence** (Definition 5.1.6): if
`Y'` has reflexive `(0, 1)`-fibres, `w_k →ᵐ y` in `Y_{0,1}` and `P(y) ∈ U`, then
`Φ[1](w_k) →ᵐ Φ[1](y)`. -/
theorem LocalIso.mixedTendsto (L : LocalIso B B' U U') (hB' : B'.HasReflexiveFibers)
    {w : ℕ → B.One} {y : B.One} (hm : B.MixedTendsto w y) (hy : P (B.oneVal y) ∈ U) :
    B'.MixedTendsto (fun k => L.Φ₁ (w k)) (L.Φ₁ y) := by
  obtain ⟨N₀, hN₀⟩ := proposition_5_1_3_exists (B := B)
  obtain ⟨N₁, hN₁⟩ := proposition_5_1_3_exists (B := B')
  have hU : IsOpen U := L.base.isOpen_source
  have hev : ∀ᶠ k in atTop, P (B.oneVal (w k)) ∈ U := hm.1.eventually (hU.mem_nhds hy)
  have hY : Tendsto (fun k => B'.oneVal (L.Φ₁ (w k))) atTop (𝓝 (B'.oneVal (L.Φ₁ y))) := by
    have hc : ContinuousAt L.Φ (B.oneVal y) :=
      L.zero.isScSmoothOn.continuousOn.continuousAt ((hU.preimage B.continuous).mem_nhds hy)
    rw [L.oneVal_Φ₁ y hy]
    exact (hc.tendsto.comp hm.tendsto_oneVal).congr'
      (hev.mono fun k hk => (L.oneVal_Φ₁ (w k) hk).symm)
  obtain ⟨r, hr⟩ := hm.exists_eventually_le hN₀
  obtain ⟨V, hVo, hyV, C, hC, hV⟩ := StrongBundle.exists_le_mul_auxNorm hN₀
    (M := N₁ ∘ L.Φ₁) hU (hN₁.continuous.comp_continuousOn L.one.isScSmoothOn.continuousOn)
    (fun z hz => L.isFiberSeminorm_comp hz (hN₁.fiber _).isFiberSeminorm) hy
  refine StrongBundle.mixedTendsto_of_bounded hB' hN₁ hY (r := C * r) ?_
  filter_upwards [hr, hm.1.eventually (hVo.mem_nhds hyV)] with k hk hkV
  exact (hV (w k) hkV).trans (mul_le_mul_of_nonneg_left hk hC.le)

end PartI

end StrongBundle

namespace SBLocalization

open EPLocalization

variable {A A' : SEP.{u}}

/-- `|μ(α(P w), w)| = |w|` in `|W[1]|`. -/
theorem mk_actOne (A : SEP.{u}) (α : A.Obj → A.Mor) (e : A.B.One) :
    (Quotient.mk A.E.oneOrbitSetoid (A.E.actOne α e)) = Quotient.mk _ e := by
  refine mk_eq_mk_of_π_eq ?_
  change A.E.toEpGroupoid.π (A.E.μ (A.X.actPair A.P α (A.B.oneVal e))) = _
  rw [EpStrongBundle.π_μ, A.X.actPair_snd]

/-- **Transfer of mixed convergence along a diagram** `[W ←Φ W'' →Ψ W']` of strong bundle
equivalences (`W'` with reflexive `(0, 1)`-fibres): a sequence `w_k →ᵐ y` in `W_{0,1}` has
representatives `w'_k →ᵐ y'` of `|D|(|w_k|)` (for large `k`) and of `|D|(|y|)`. -/
theorem SDiagram.exists_mixedTendsto_transfer (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ)
    (hA' : A'.B.HasReflexiveFibers) {w : ℕ → A.B.One} {y : A.B.One}
    (hm : A.B.MixedTendsto w y) :
    ∃ (w' : ℕ → A'.B.One) (y' : A'.B.One),
      (∀ᶠ k in atTop, D.oneOrbitMap (Quotient.mk _ (w k)) = Quotient.mk _ (w' k)) ∧
      D.oneOrbitMap (Quotient.mk _ y) = Quotient.mk _ y' ∧ A'.B.MixedTendsto w' y' := by
  have hB : D.B.B.HasReflexiveFibers := (sbe hΨ).hasReflexiveFibers_of hA'
  have hA : A.B.HasReflexiveFibers := D.hΦ.hasReflexiveFibers_push hB
  set x := A.P (A.B.oneVal y) with hxdef
  -- `b₀` with a morphism `σ : x → Φ(b₀)`
  obtain ⟨ξ, hξ⟩ := D.hΦ.isEquivalence_base.isHomeomorph_orbitMap.surjective (A.X.π x)
  induction ξ using Quotient.inductionOn with | h b₀ => ?_
  have h1 : A.X.π x = A.X.π ((SEP.Hom.ϕ D.Φ).obj b₀) := hξ.symm
  obtain ⟨σ, hs, ht⟩ := (GroupoidStr.π_eq_π_iff _).1 h1
  obtain ⟨S, α, -, hxS, hασ, hsrcα, htrans⟩ := A.E.exists_mixedTendsto_μ hA σ hs.symm
  have hm₁ := htrans w hm
  set w₁ : ℕ → A.B.One := fun k => A.E.actOne α (w k) with hw₁
  set y₁ := A.E.actOne α y with hy₁
  have hPy₁ : A.P (A.B.oneVal y₁) = (SEP.Hom.ϕ D.Φ).obj b₀ := by
    change A.P (A.E.sectionAct α (A.B.oneVal y)) = _
    rw [A.E.P_sectionAct_of_eq α (hsrcα _ hxS).symm, ← hxdef, hασ]
    exact ht
  -- the local inverse of `Φ` at `b₀`
  obtain ⟨U, U', hb₀U, hi⟩ := D.hΦ.isLocalStrongBundleIso_obj b₀
  set L₀ := hi.toLocalIso
  have hy₁U' : A.P (A.B.oneVal y₁) ∈ U' := by rw [hPy₁]; exact L₀.base.mapsTo hb₀U
  have hm₂ := L₀.symm.mixedTendsto hB hm₁ hy₁U'
  set w₂ : ℕ → D.B.B.One := fun k => L₀.Ψ₁ (w₁ k) with hw₂
  set y₂ := L₀.Ψ₁ y₁ with hy₂
  have hPy₂ : D.B.P (D.B.B.oneVal y₂) = b₀ := by
    rw [hy₂, L₀.oneVal_Ψ₁ y₁ hy₁U', L₀.covers_inv _ hy₁U', hPy₁]
    exact L₀.base.left_inv b₀ hb₀U
  -- the local isomorphism `Ψ` at `b₀`
  obtain ⟨V, V', hb₀V, hi'⟩ := (sbe hΨ).isLocalStrongBundleIso_obj b₀
  set L₁ := hi'.toLocalIso
  have hy₂V : D.B.P (D.B.B.oneVal y₂) ∈ V := by rw [hPy₂]; exact hb₀V
  have hm₃ := L₁.mixedTendsto hA' hm₂ hy₂V
  -- the orbit identity
  have key : ∀ e : A.B.One, A.P (A.B.oneVal (A.E.actOne α e)) ∈ U' →
      D.B.P (D.B.B.oneVal (L₀.Ψ₁ (A.E.actOne α e))) ∈ V →
      D.oneOrbitMap (Quotient.mk _ e) =
        Quotient.mk _ (L₁.Φ₁ (L₀.Ψ₁ (A.E.actOne α e))) := by
    intro e he1 he2
    set e₁ := A.E.actOne α e
    set e₂ := L₀.Ψ₁ e₁
    have hΦe₂ : oneMap D.Φ (Quotient.mk _ e₂) = Quotient.mk _ e₁ := by
      change Quotient.mk _ (StrongBundle.oneRestrict D.B.B A.B (SEP.Hom.Φ D.Φ).obj _ e₂) = _
      congr 1
      apply A.B.oneVal_injective
      rw [StrongBundle.oneVal_oneRestrict]
      change L₀.Φ (D.B.B.oneVal (L₀.Ψ₁ e₁)) = _
      rw [L₀.oneVal_Ψ₁ e₁ he1]
      exact L₀.zero.right_inv _ he1
    rw [← mk_actOne A α e, ← hΦe₂, SDiagram.oneOrbitMap_oneMap]
    change Quotient.mk _ (StrongBundle.oneRestrict D.B.B A'.B (SEP.Hom.Φ D.Ψ).obj _ e₂) = _
    congr 1
  have hev1 : ∀ᶠ k in atTop, A.P (A.B.oneVal (w₁ k)) ∈ U' :=
    hm₁.1.eventually (L₀.base.isOpen_target.mem_nhds hy₁U')
  have hev2 : ∀ᶠ k in atTop, D.B.P (D.B.B.oneVal (w₂ k)) ∈ V :=
    hm₂.1.eventually (L₁.base.isOpen_source.mem_nhds hy₂V)
  refine ⟨fun k => L₁.Φ₁ (w₂ k), L₁.Φ₁ y₂, ?_, key y hy₁U' hy₂V, hm₃⟩
  filter_upwards [hev1, hev2] with k hk1 hk2
  exact key (w k) hk1 hk2

/-- **The pull-back of a reflexive auxiliary norm is reflexive** (Definition 12.2.10 (3) for
`[D]^*N'`; with Proposition 11.5.1 for the other clauses). -/
theorem SDiagram.isReflexiveAuxNorm_pullNorm (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ)
    (hA' : A'.B.HasReflexiveFibers) {N' : A'.B.One → ℝ} (hN' : A'.E.IsReflexiveAuxNorm N')
    (hpull : A.E.IsAuxNorm (D.pullNorm N')) : A.E.IsReflexiveAuxNorm (D.pullNorm N') := by
  refine ⟨hpull, fun w y hm => ?_⟩
  obtain ⟨w', y', hw', hy', hm'⟩ := D.exists_mixedTendsto_transfer hΨ hA' hm
  have hinv := hN'.toIsAuxNorm.isOneInvariant
  have e1 : D.pullNorm N' y = N' y' := SDiagram.pullNorm_eq hinv hy'
  have e2 : (fun k => ((D.pullNorm N' (w k) : ℝ) : EReal)) =ᶠ[atTop]
      fun k => ((N' (w' k) : ℝ) : EReal) :=
    hw'.mono fun k hk => by simp only [SDiagram.pullNorm_eq hinv hk]
  rw [e1, Filter.liminf_congr e2]
  exact hN'.le_liminf w' y' hm'

/-- **The push-forward of a reflexive auxiliary norm is reflexive** (the pull-back along the
reversed diagram). -/
theorem SDiagram.isReflexiveAuxNorm_pushNorm (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ)
    (hA : A.B.HasReflexiveFibers) {N : A.B.One → ℝ} (hN : A.E.IsReflexiveAuxNorm N) :
    A'.E.IsReflexiveAuxNorm (D.pushNorm hΨ N) :=
  (D.symm hΨ).isReflexiveAuxNorm_pullNorm D.isEquivalence_Φ hA hN
    (D.isAuxNorm_pushNorm hΨ hN.toIsAuxNorm)

namespace GenSBMap

variable {F : GenSBMap A A'} (hF : F.IsGeneralizedIso)

/-- **2021 Proposition 11.5.1 with Definition 12.2.10**: the pull-back of a reflexive auxiliary
norm along a generalized strong bundle isomorphism is a reflexive auxiliary norm. -/
theorem isReflexiveAuxNorm_pullNorm (hA' : A'.B.HasReflexiveFibers) {N' : A'.B.One → ℝ}
    (hN' : A'.E.IsReflexiveAuxNorm N') : A.E.IsReflexiveAuxNorm (pullNorm hF N') :=
  (rep hF).isReflexiveAuxNorm_pullNorm (isEquivalence_rep_Ψ hF) hA' hN'
    (isAuxNorm_pullNorm hF hN'.toIsAuxNorm)

/-- **2021 Proposition 11.5.1 with Definition 12.2.10**: the push-forward of a reflexive
auxiliary norm along a generalized strong bundle isomorphism is a reflexive auxiliary norm. -/
theorem isReflexiveAuxNorm_pushNorm (hA : A.B.HasReflexiveFibers) {N : A.B.One → ℝ}
    (hN : A.E.IsReflexiveAuxNorm N) : A'.E.IsReflexiveAuxNorm (pushNorm hF N) :=
  (rep hF).isReflexiveAuxNorm_pushNorm (isEquivalence_rep_Ψ hF) hA hN

end GenSBMap

end SBLocalization

namespace StrongPolyfoldBundleStructure

open SBLocalization EPLocalization

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}

/-- **A reflexive auxiliary norm in one structure is reflexive in every equivalent one**
(`S'` with reflexive `1`-fibres; (16.7) and the pull-back along the equivalence). -/
theorem isReflexiveAuxNorm_of_equiv {S S' : StrongPolyfoldBundleStructure p} (h : Equiv S S')
    (hS' : S'.A.E.HasReflexiveFibers) {n : Y → ℝ}
    (hn : S'.A.E.IsReflexiveAuxNorm (S'.normOf n)) : S.A.E.IsReflexiveAuxNorm (S.normOf n) := by
  obtain ⟨F, hF, -, hΓ⟩ := h
  rw [normOf_pull hF hΓ]
  exact GenSBMap.isReflexiveAuxNorm_pullNorm hF hS' hn

/-- `oneToY` of a representative of `|D|(|e|)` is `oneToY e`, for any `e'` in that class. -/
theorem oneToY_of_oneOrbitMap {S S' : StrongPolyfoldBundleStructure p} {F : GenSBMap S.A S'.A}
    (hF : F.IsGeneralizedIso) (hΓ : ⇑S'.Γ ∘ F.orbitMap = ⇑S.Γ) {e : S.A.B.One}
    {e' : S'.A.B.One}
    (h : (GenSBMap.rep hF).oneOrbitMap (Quotient.mk _ e) = Quotient.mk _ e') :
    S'.oneToY e' = S.oneToY e := by
  rw [← oneToY_pull hF hΓ e]
  unfold oneToY
  congr 1
  change oneToOrbit S'.A (Quotient.mk _ e') = oneToOrbit S'.A (Quotient.mk _ _)
  rw [Quotient.out_eq, h]

/-- **(ii): mixed convergence does not depend on the model** (Definition 16.3.14): mixed
convergence read in `S` gives it in every equivalent `S'` with reflexive `1`-fibres. -/
theorem mixedTendstoIn_of_equiv {S S' : StrongPolyfoldBundleStructure p} (h : Equiv S S')
    (hS' : S'.A.E.HasReflexiveFibers) {y : ℕ → Y} {y₀ : Y}
    (hm : StrongPolyfoldBundle.MixedTendstoIn S y y₀) :
    StrongPolyfoldBundle.MixedTendstoIn S' y y₀ := by
  obtain ⟨F, hF, -, hΓ⟩ := h
  obtain ⟨w, w₀, hw, hw₀, hmw⟩ := hm
  obtain ⟨w', y', hw', hy', hm'⟩ :=
    (GenSBMap.rep hF).exists_mixedTendsto_transfer (GenSBMap.isEquivalence_rep_Ψ hF) hS' hmw
  obtain ⟨K, hK⟩ := eventually_atTop.1 hw'
  classical
  set w'' : ℕ → S'.A.B.One := fun k =>
    if K ≤ k then w' k else ((GenSBMap.rep hF).oneOrbitMap (Quotient.mk _ (w k))).out
  refine ⟨w'', y', fun k => ?_, ?_, hm'.congr_eventually ?_⟩
  · rw [← hw k]
    by_cases hk : K ≤ k
    · simp only [w'', if_pos hk]
      exact oneToY_of_oneOrbitMap hF hΓ (hK k hk)
    · simp only [w'', if_neg hk]
      exact oneToY_of_oneOrbitMap hF hΓ (Quotient.out_eq _).symm
  · rw [← hw₀]; exact oneToY_of_oneOrbitMap hF hΓ hy'
  · exact eventually_atTop.2 ⟨K, fun k hk => by simp only [w'', if_pos hk]⟩

end StrongPolyfoldBundleStructure

namespace StrongPolyfoldBundle

open StrongPolyfoldBundleStructure

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p}

/-- **Definition 16.3.13: a reflexive auxiliary norm is reflexive in every model** (for
`(p, c̄)` with reflexive `1`-fibres). -/
theorem IsReflexiveAuxNorm.of_mem (hc : c.HasReflexiveFibers) {n : Y → ℝ}
    (hn : c.IsReflexiveAuxNorm n) {S : StrongPolyfoldBundleStructure p} (hS : ⟦S⟧ = c) :
    S.A.E.IsReflexiveAuxNorm (S.normOf n) := by
  obtain ⟨-, S₀, hS₀, h₀⟩ := hn
  exact isReflexiveAuxNorm_of_equiv (Quotient.exact (hS.trans hS₀.symm)) (hc.of_mem hS₀) h₀

/-- **Definition 16.3.13, model independence**: `n` is a reflexive auxiliary norm iff it is
represented by a reflexive auxiliary norm in every structure of `c̄`. -/
theorem isReflexiveAuxNorm_iff_forall (hc : c.HasReflexiveFibers) {n : Y → ℝ} :
    c.IsReflexiveAuxNorm n ↔ c.IsAuxNorm n ∧
      ∀ S : StrongPolyfoldBundleStructure p, ⟦S⟧ = c → S.A.E.IsReflexiveAuxNorm (S.normOf n) := by
  refine ⟨fun hn => ⟨hn.1, fun S hS => hn.of_mem hc hS⟩, fun ⟨h1, h2⟩ => ?_⟩
  obtain ⟨S, hS⟩ := Quotient.exists_rep c
  exact ⟨h1, S, hS, h2 S hS⟩

/-- **Definition 16.3.14, model independence**: with reflexive `1`-fibres, `y_k →ᵐ y` iff the
representatives are mixed convergent in every structure of `c̄`. -/
theorem mixedTendsto_iff_forall (hc : c.HasReflexiveFibers) {y : ℕ → Y} {y₀ : Y} :
    c.MixedTendsto y y₀ ↔
      ∀ S : StrongPolyfoldBundleStructure p, ⟦S⟧ = c → MixedTendstoIn S y y₀ := by
  refine ⟨fun hm S hS => ?_, fun h => ?_⟩
  · obtain ⟨S₀, hS₀, -, -, hm⟩ := hm
    exact mixedTendstoIn_of_equiv (Quotient.exact (hS₀.trans hS.symm)) (hc.of_mem hS) hm
  · obtain ⟨S, hS, hB⟩ := hc
    obtain ⟨N, hN⟩ := S.A.E.theorem_12_2_11_exists S.paracompact hB
    exact ⟨S, hS, hB, ⟨N, hN⟩, h S hS⟩

/-- **2021 Proposition 16.3.16 (2), p. 728 (2017: Proposition 16.5 (2)), as printed**: for
`(p, c̄)` with reflexive `1`-fibres, a reflexive auxiliary norm `n` and `y_k →ᵐ y`
(Definition 16.3.14, in any model), `n(y) ≤ liminf n(y_k)`. -/
theorem proposition_16_3_16_two (hc : c.HasReflexiveFibers) {n : Y → ℝ}
    (hn : c.IsReflexiveAuxNorm n) {y : ℕ → Y} {y₀ : Y} (hm : c.MixedTendsto y y₀) :
    (n y₀ : EReal) ≤ liminf (fun k => (n (y k) : EReal)) atTop := by
  obtain ⟨S, hS, -, -, hmS⟩ := hm
  exact proposition_16_3_16_two_of_mem (hn.of_mem hc hS) hmS

end StrongPolyfoldBundle

end Polyfold
