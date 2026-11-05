import Polyfold.Chapter3.GermFilling
import Polyfold.Chapter3.FillerLinearization
import Polyfold.Chapter3.SectionCompactness

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.6,
**Proposition 3.52** (the linearization of an sc-Fredholm section at a zero is Fredholm, of the
index `n − N` of the conjugating basic germ), in the chart of Definition 3.11, together with the
pieces of the proof of Theorem 3.54 that only involve the linearization: the derivative of the
push-forward `Ψ_*(g − s)` is `Γ(0) ∘ D(g − s)(0) = Dh(0) ∘ Dψ(0)`, so `D(g − s)(0)` is Fredholm of
index `n − N` (Proposition 3.10), `Dg(0) = D(g − s)(0) + ιDs(0)` is a compact perturbation, and
`Tf(0) = Dg(0)|_{T₀O}` is Fredholm of the same index (Proposition 3.5).

# The linearization of an sc-Fredholm germ

## The text, paraphrased

(Proposition 3.52) If `f` is an sc-Fredholm section of the tame strong bundle `P : Y → X` and
`f(x) = 0`, then `Tf(x) : T_xX → Y_x` is an sc-Fredholm operator.  Proof: in the chart of the
sc-Fredholm germ, `D(g − s)(0)` is sc-Fredholm by Proposition 3.10, `Dg(0)` by Proposition 1.10
(`Ds(0)` is sc⁺), and `Tf̃(0) : T₀O → K₀` is sc-Fredholm of index `ind Dg(0) = ind D(g − s)(0)`
by Proposition 3.5.  (Proof of Theorem 3.54) "`Ψ_*(g) = h + t` … `D(h + t)(0)` is sc-Fredholm …
`Dg(0)` is also sc-Fredholm … `Tf̃(0)` is surjective … by Proposition 3.5 `Dg(0)` is surjective."

## What is formalized

* `Polyfold.ScNbhdGerm.preimage` (in `GermFilling.lean`): the germ `{x ∈ G₀ | f(x) ∈ G'}` on which an sc⁰-germ `f` maps
  into a given germ `G'` (the shrinking of germs the text performs silently: "near `0`").
* `Polyfold.IsStrongBundleMap.fiberCLM` (`Γ(0) : F → F'`, bounded linear) and
  `IsStrongBundleMap.scDeriv_fiber_zero` (`D(pr_{F'} ∘ Ψ)(0, 0)(h, k) = Γ(0)k`).
* `Polyfold.isFredholm_equiv_comp_equiv`: Fredholm property and index are invariant under
  composition with linear isomorphisms on both sides.
* `Polyfold.proposition_3_10_basic`: Proposition 3.10 for a basic germ alone (`s = 0`).
* `Polyfold.IsConjugateToBasicGerm.scDeriv_isFredholm_wholeChart`: for `k` sc-smooth with `k(0) = 0`
  conjugated to a basic germ, `Dk(0)` is Fredholm (on level `0`) of index `n − N`.
* `Polyfold.proposition_3_52_local_wholeChart` and `Polyfold.proposition_3_52_wholeChart`: in the chart of Definition
  3.11 centred at a zero `x₀` of a section `f` with `(f, x₀)` an sc-Fredholm germ, `Dg(0)` and
  `Tf(0) = Dg(0)|_{T₀O} : T₀O → K₀` are Fredholm operators with `ind Tf(0) = ind Dg(0) = n − N`.

## What the text leaves implicit, and the choices made (the findings)

* **Only the level-`0` (classical) Fredholm property is proved in this file**, with the index.
  The text's "sc-Fredholm operator" `Tf(x) : T_xX → Y_x` (all levels, Definition 1.8) is
  `proposition_3_52_local_sc_wholeChart` / `proposition_3_52_sc_wholeChart` in `FredholmGermLinearizationSc.lean`:
  `T₀O = Dr(0)E` and `K₀ = ρ(0)F` are sc-subspaces, `Dg(0)` and its restriction `T₀O → K₀`
  (`ScOperator.restrict`) are sc-Fredholm, by the criterion "Fredholm on level `0` + regularizing"
  (`isScFredholm_of_isRegularizing`, `Chapter1/ScFredholmCriterion.lean`; Findings, Chapter 3,
  items 233–236).  The level-`0` statements here are what Proposition 3.5 and Theorem 3.54 use.
* **The derivative of the conjugation.**  The identity `Ψ(u, (g − s)(u)) = (ψ(u), h(ψ(u)))` holds
  for `u ∈ U` near `0`; linearizing it needs the chain rule for the germ `h ∘ ψ` on a germ of
  neighbourhoods small enough that `ψ` maps it into the germ of `h` (`ScNbhdGerm.preimage`), the
  derivative of `u ↦ Γ(u, k(u))` at `0` (which is `Γ(0)Dk(0)` because `k(0) = 0` and `Γ(u, ·)` is
  linear, `scDeriv_fiber_zero`), and the invertibility of `Dψ(0)` (inverse `Dψ'(0)`, chain rule
  for `ψ' ∘ ψ = id`) and of `Γ(0)` (inverse `Γ'(0)`).
* `k(0) = (g − s)(0) = 0` is `s(0) = g(0)` of Definition 3.11; `g(0) = f̂(0) = 0` is `f(x₀) = 0`
  through condition (1) of the filler.
-/

open Set Filter Topology Function Module ContinuousLinearMap

noncomputable section

namespace Polyfold

variable {E F E' F' : ScBanach}


/-! ### The fibre map of a strong bundle map at `0` and its role in the linearization -/

namespace IsStrongBundleMap

variable {C : Set (E 0)} {U : Set (E 0)} {U' : Set (E' 0)} {Ψ : E 0 × F 0 → E' 0 × F' 0}
  (hΨ : IsStrongBundleMap U U' Ψ)
include hΨ

/-- `k ↦ (Ψ(u, k))₂` is continuous (`Ψ` is sc⁰ on level `0`). -/
lemma fiber_continuous {u : E 0} (hu : u ∈ U) : Continuous fun k : F 0 => (Ψ (u, k)).2 := by
  have hc : ContinuousOn Ψ (U ×ˢ univ) := hΨ.isScSmooth_zero.isSc1.isSc0.continuousOn_base
  have : Continuous fun k : F 0 => Ψ (u, k) :=
    hc.comp_continuous (f := fun k : F 0 => ((u, k) : E 0 × F 0)) (by fun_prop)
      fun _ => ⟨hu, mem_univ _⟩
  exact continuous_snd.comp this

/-- The fibre map `Γ(u) = (Ψ(u, ·))₂ : F → F'` as a bounded operator, `u ∈ U`. -/
def fiberCLM {u : E 0} (hu : u ∈ U) : F 0 →L[ℝ] F' 0 where
  toFun k := (Ψ (u, k)).2
  map_add' := (hΨ.fiber_linear u hu).map_add
  map_smul' := (hΨ.fiber_linear u hu).map_smul
  cont := hΨ.fiber_continuous hu

@[simp] lemma fiberCLM_apply {u : E 0} (hu : u ∈ U) (k : F 0) : hΨ.fiberCLM hu k = (Ψ (u, k)).2 :=
  rfl

/-- The fibre part `(u, k) ↦ (Ψ(u, k))₂` is sc¹ on `U ⊕ F`. -/
lemma fiber_isSc1 (hU : IsRelOpenInQuadrant E C U) :
    IsSc1 (U ×ˢ univ) fun p : (E.prod F) 0 => (Ψ p).2 :=
  (hΨ.isScSmooth_zero.snd (hU.prod_univ F).isScDomain).isSc1

/-- **The linearization of `Γ(u)k` at `(0, 0)`**: `D(pr_{F'} ∘ Ψ)(0, 0)(h, k) = Γ(0)k` (the fibre
direction: `k ↦ Γ(0)k` is linear; the base direction: `Γ(u)0 = 0`; both on the dense level `1`). -/
theorem scDeriv_fiber_zero (hU : IsRelOpenInQuadrant E C U) (h0 : (0 : E 0) ∈ U) (h : E 0)
    (k : F 0) :
    scDeriv (U ×ˢ univ) (fun p : (E.prod F) 0 => (Ψ p).2) 0 (h, k) = hΨ.fiberCLM h0 k := by
  set D := scDeriv (U ×ˢ univ) (fun p : (E.prod F) 0 => (Ψ p).2) (0 : (E.prod F) 1) with hD
  have h01 : (0 : (E.prod F) 1) ∈ (E.prod F).lvlSet (U ×ˢ univ) 1 := by
    rw [ScBanach.mem_lvlSet, map_zero]; exact ⟨h0, mem_univ _⟩
  have h01' : (0 : E 1) ∈ E.lvlSet U 1 := by rw [ScBanach.mem_lvlSet, map_zero]; exact h0
  have hder := (hΨ.fiber_isSc1 hU).isSc1With_scDeriv.hasFDerivWithinAt 0 h01
  -- the fibre direction
  have hinr : D.comp (ContinuousLinearMap.inr ℝ (E 0) (F 0)) = hΨ.fiberCLM h0 := by
    apply ContinuousLinearMap.ext_of_comp_toBase_one (E := F)
    have hmaps : MapsTo ⇑(ContinuousLinearMap.inr ℝ (E 1) (F 1)) univ
        ((E.prod F).lvlSet (U ×ˢ univ) 1) := by
      intro k₁ _
      change (((0 : E 1), k₁) : (E.prod F) 1) ∈ _
      rw [ScBanach.mem_lvlSet, ScBanach.prod_toBase, map_zero]; exact ⟨h0, mem_univ _⟩
    have h1 : HasFDerivWithinAt
        (((fun p : (E.prod F) 0 => (Ψ p).2) ∘ (E.prod F).toBase 1) ∘
          ⇑(ContinuousLinearMap.inr ℝ (E 1) (F 1)))
        ((D.comp ((E.prod F).toBase 1)).comp (ContinuousLinearMap.inr ℝ (E 1) (F 1))) univ 0 :=
      HasFDerivWithinAt.comp (f := ⇑(ContinuousLinearMap.inr ℝ (E 1) (F 1))) 0 hder
        (ContinuousLinearMap.inr ℝ (E 1) (F 1)).hasFDerivWithinAt hmaps
    have h2 : HasFDerivWithinAt
        (((fun p : (E.prod F) 0 => (Ψ p).2) ∘ (E.prod F).toBase 1) ∘
          ⇑(ContinuousLinearMap.inr ℝ (E 1) (F 1)))
        ((hΨ.fiberCLM h0).comp (F.toBase 1)) univ 0 := by
      have : (((fun p : (E.prod F) 0 => (Ψ p).2) ∘ (E.prod F).toBase 1) ∘
          ⇑(ContinuousLinearMap.inr ℝ (E 1) (F 1))) = fun k₁ => hΨ.fiberCLM h0 (F.toBase 1 k₁) := by
        funext k₁
        simp only [Function.comp_apply, ContinuousLinearMap.inr_apply]
        change (Ψ ((E.prod F).toBase 1 ((0 : E 1), k₁))).2 = _
        rw [ScBanach.prod_toBase, map_zero]
        rfl
      rw [this]
      exact ((hΨ.fiberCLM h0).comp (F.toBase 1)).hasFDerivAt.hasFDerivWithinAt
    have huniq := uniqueDiffWithinAt_univ.eq h1 h2
    ext k₁
    have := congrArg (fun T : F 1 →L[ℝ] F' 0 => T k₁) huniq
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] at this ⊢
    rw [ScBanach.prod_toBase, map_zero] at this
    exact this
  -- the base direction
  have hinl : D.comp (ContinuousLinearMap.inl ℝ (E 0) (F 0)) = 0 := by
    apply ContinuousLinearMap.ext_of_comp_toBase_one (E := E)
    have hmaps : MapsTo ⇑(ContinuousLinearMap.inl ℝ (E 1) (F 1)) (E.lvlSet U 1)
        ((E.prod F).lvlSet (U ×ˢ univ) 1) := by
      intro u₁ hu₁
      change ((u₁, (0 : F 1)) : (E.prod F) 1) ∈ _
      rw [ScBanach.mem_lvlSet, ScBanach.prod_toBase]; exact ⟨hu₁, mem_univ _⟩
    have h1 : HasFDerivWithinAt
        (((fun p : (E.prod F) 0 => (Ψ p).2) ∘ (E.prod F).toBase 1) ∘
          ⇑(ContinuousLinearMap.inl ℝ (E 1) (F 1)))
        ((D.comp ((E.prod F).toBase 1)).comp (ContinuousLinearMap.inl ℝ (E 1) (F 1)))
        (E.lvlSet U 1) 0 :=
      HasFDerivWithinAt.comp (f := ⇑(ContinuousLinearMap.inl ℝ (E 1) (F 1))) 0 hder
        (ContinuousLinearMap.inl ℝ (E 1) (F 1)).hasFDerivWithinAt hmaps
    have hzero : ∀ u₁ ∈ E.lvlSet U 1,
        (((fun p : (E.prod F) 0 => (Ψ p).2) ∘ (E.prod F).toBase 1) ∘
          ⇑(ContinuousLinearMap.inl ℝ (E 1) (F 1))) u₁ = 0 := by
      intro u₁ hu₁
      simp only [Function.comp_apply, ContinuousLinearMap.inl_apply]
      change (Ψ ((E.prod F).toBase 1 (u₁, (0 : F 1)))).2 = 0
      rw [ScBanach.prod_toBase, map_zero]
      exact (hΨ.fiber_linear _ hu₁).map_zero
    have h2 : HasFDerivWithinAt
        (((fun p : (E.prod F) 0 => (Ψ p).2) ∘ (E.prod F).toBase 1) ∘
          ⇑(ContinuousLinearMap.inl ℝ (E 1) (F 1)))
        (0 : E 1 →L[ℝ] F' 0) (E.lvlSet U 1) 0 :=
      (hasFDerivWithinAt_const (0 : F' 0) 0 (E.lvlSet U 1)).congr hzero (hzero 0 h01')
    have huniq := (hU.isScDomain.uniqueDiffWithinAt 1 0 h01').eq h1 h2
    ext u₁
    have := congrArg (fun T : E 1 →L[ℝ] F' 0 => T u₁) huniq
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, zero_apply] at this ⊢
    rw [ScBanach.prod_toBase, map_zero] at this
    exact this
  have hhk : ((h, k) : (E.prod F) 0) = ContinuousLinearMap.inl ℝ (E 0) (F 0) h +
      ContinuousLinearMap.inr ℝ (E 0) (F 0) k := by simp
  rw [hhk, map_add]
  have e1 := congrArg (fun T : E 0 →L[ℝ] F' 0 => T h) hinl
  have e2 := congrArg (fun T : F 0 →L[ℝ] F' 0 => T k) hinr
  simp only [ContinuousLinearMap.comp_apply, zero_apply] at e1 e2
  rw [e1, e2, zero_add]

/-- **The derivative of `u ↦ Γ(u)k(u)` at `0`** for an sc-smooth `k` with `k(0) = 0`: `Γ(0)Dk(0)`. -/
theorem scDeriv_fiber_comp (hU : IsRelOpenInQuadrant E C U) (h0 : (0 : E 0) ∈ U) {k : E 0 → F 0}
    (hk : IsScSmooth U k) (hk0 : k 0 = 0) :
    scDeriv U (fun u => (Ψ (u, k u)).2) 0 = (hΨ.fiberCLM h0).comp (scDeriv U k 0) := by
  have hUF := (hU.prod_univ F).isScDomain
  have h01 : (0 : E 1) ∈ E.lvlSet U 1 := by rw [ScBanach.mem_lvlSet, map_zero]; exact h0
  have huniq := hU.isScDomain.uniqueDiffWithinAt 1 0 h01
  have hid : IsSc1 U (_root_.id : E 0 → E 0) := (isScSmooth_id hU.isScDomain).isSc1
  set Dk := scDeriv U k 0 with hDk
  have hpair : IsSc1 U (scPair (_root_.id : E 0 → E 0) k) :=
    (IsSck.scPair (k := 1) hU.isScDomain (isScSmooth_id hU.isScDomain 1) (hk 1)).1
  have hmaps : MapsTo (scPair (_root_.id : E 0 → E 0) k) U (U ×ˢ univ) := fun u hu =>
    ⟨hu, mem_univ _⟩
  have hDpair : scDeriv U (scPair (_root_.id : E 0 → E 0) k) 0 =
      (ContinuousLinearMap.id ℝ (E 0)).prod Dk := by
    apply ContinuousLinearMap.ext_of_comp_toBase_one (E := E)
    have h1 := hpair.isSc1With_scDeriv.hasFDerivWithinAt 0 h01
    have hDid : scDeriv U (_root_.id : E 0 → E 0) 0 = ContinuousLinearMap.id ℝ (E 0) :=
      IsSc1.scDeriv_eqOn (isSc1With_id U) (hU.isScDomain.uniqueDiffWithinAt 1) h01
    have h2 := (hid.isSc1With_scDeriv.hasFDerivWithinAt 0 h01).prodMk
      (hk.isSc1.isSc1With_scDeriv.hasFDerivWithinAt 0 h01)
    rw [hDid] at h2
    rw [ContinuousLinearMap.prod_comp']
    exact huniq.eq h1 h2
  have hlev : levelMap (scPair (_root_.id : E 0 → E 0) k) 1 (0 : E 1) = 0 := by
    apply levelMap_eq_of_toBase_eq
    rw [map_zero, map_zero]
    show (0 : (E.prod F) 0) = (0, k 0)
    rw [hk0]; rfl
  have hcomp : scDeriv U ((fun p : (E.prod F) 0 => (Ψ p).2) ∘ scPair (_root_.id : E 0 → E 0) k) 0 =
      (hΨ.fiberCLM h0).comp Dk := by
    ext h
    have := scDeriv_comp_apply' hU (hU.prod_univ F) hpair (hΨ.fiber_isSc1 hU) hmaps h01 h
    rw [hlev, hDpair] at this
    rw [← this, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]
    exact hΨ.scDeriv_fiber_zero hU h0 _ _
  exact hcomp

end IsStrongBundleMap

/-! ### Fredholm operators and isomorphisms -/

section FredholmEquiv

variable {E₀ F₀ E₁ F₁ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [CompleteSpace E₀]
  [NormedAddCommGroup F₀] [NormedSpace ℝ F₀] [CompleteSpace F₀]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [CompleteSpace F₁]

omit [CompleteSpace E₀] [CompleteSpace F₀] in
/-- **Fredholm operators are stable under composition with isomorphisms** on both sides, with the
same index: `e₂ ∘ T ∘ e₁` is Fredholm of index `ind T`. -/
theorem isFredholm_equiv_comp_equiv {T : E₀ →L[ℝ] F₀} (hT : IsFredholm T) (e₁ : E₁ ≃L[ℝ] E₀)
    (e₂ : F₀ ≃L[ℝ] F₁) :
    IsFredholm ((e₂ : F₀ →L[ℝ] F₁).comp (T.comp (e₁ : E₁ →L[ℝ] E₀))) ∧
      fredholmIndex ((e₂ : F₀ →L[ℝ] F₁).comp (T.comp (e₁ : E₁ →L[ℝ] E₀))) = fredholmIndex T := by
  have hcoe : (((e₂ : F₀ →L[ℝ] F₁).comp (T.comp (e₁ : E₁ →L[ℝ] E₀)) : E₁ →L[ℝ] F₁) : E₁ →ₗ[ℝ] F₁) =
      (e₂.toLinearEquiv : F₀ →ₗ[ℝ] F₁) ∘ₗ ((T : E₀ →ₗ[ℝ] F₀) ∘ₗ (e₁.toLinearEquiv : E₁ →ₗ[ℝ] E₀)) :=
    LinearMap.ext fun _ => rfl
  have h1 : HasFiniteIndex ((T : E₀ →ₗ[ℝ] F₀) ∘ₗ (e₁.toLinearEquiv : E₁ →ₗ[ℝ] E₀)) :=
    (HasFiniteIndex.equiv e₁.toLinearEquiv).comp (Polyfold.IsFredholm.hasFiniteIndex hT)
  have h2 : HasFiniteIndex ((e₂.toLinearEquiv : F₀ →ₗ[ℝ] F₁) ∘ₗ
      ((T : E₀ →ₗ[ℝ] F₀) ∘ₗ (e₁.toLinearEquiv : E₁ →ₗ[ℝ] E₀))) :=
    h1.comp (HasFiniteIndex.equiv e₂.toLinearEquiv)
  have hrange : (LinearMap.range (((e₂ : F₀ →L[ℝ] F₁).comp (T.comp (e₁ : E₁ →L[ℝ] E₀)) :
      E₁ →L[ℝ] F₁) : E₁ →ₗ[ℝ] F₁) : Set F₁) = e₂ '' (LinearMap.range (T : E₀ →ₗ[ℝ] F₀) : Set F₀) := by
    rw [hcoe, LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _ e₁.toLinearEquiv.range]
    rfl
  have hclosed : IsClosed (LinearMap.range (((e₂ : F₀ →L[ℝ] F₁).comp (T.comp (e₁ : E₁ →L[ℝ] E₀)) :
      E₁ →L[ℝ] F₁) : E₁ →ₗ[ℝ] F₁) : Set F₁) := by
    rw [hrange]
    exact e₂.toHomeomorph.isClosed_image.2 hT.isClosed_range
  refine ⟨isFredholm_of_banach _ ?_ hclosed ?_, ?_⟩
  · rw [hcoe]; exact h2.finite_ker
  · rw [hcoe]; exact h2.finite_coker
  · unfold fredholmIndex
    rw [hcoe, linIndex_comp h1 (HasFiniteIndex.equiv e₂.toLinearEquiv),
      linIndex_comp (HasFiniteIndex.equiv e₁.toLinearEquiv) (Polyfold.IsFredholm.hasFiniteIndex hT),
      linIndex_equiv, linIndex_equiv]
    ring

end FredholmEquiv

/-! ### Proposition 3.10 for a basic germ alone -/

/-- The zero sc-operator. -/
def ScOperator.zero (E F : ScBanach) : ScOperator E F where
  lvl _ := 0
  incl_comm _ _ := by simp

section Basic

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] {W : ScBanach}
  {Ct : Set P} {G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ univ)} {Q : Type}
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]

/-- **Proposition 3.10 for a basic germ** (`s = 0`): `Dh(0)` is an sc-Fredholm operator of index
`n − N`. -/
theorem proposition_3_10_basic (hC : IsPartialQuadrant (ScBanach.const P) Ct) {h : P × W 0 → Q × W 0}
    {Bc : P × W 0 → W 0} (hh : IsBasicGerm Ct G h Bc) :
    ∃ hop : IsScOperator (scDerivGerm (F := ScBanach.paramProd Q W) G h 0),
      IsScFredholm hop.toScOperator ∧ scIndex hop.toScOperator = finrank ℝ P - finrank ℝ Q := by
  have hCq : IsQuadrantLike (ScBanach.paramProd P W) (Ct ×ˢ univ) := (hC.prod_univ W).isQuadrantLike
  set Z := ScOperator.zero (ScBanach.paramProd P W) (ScBanach.paramProd Q W).shift with hZ
  have hs : IsSc1GermWith (F := (ScBanach.paramProd Q W).shift) G (Z 0) (scDerivGerm G (Z 0)) :=
    ((Z.isScSmoothGerm G hCq) 1).1.isSc1GermWith_scDerivGerm
  have hh1 : IsSc1GermWith (F := ScBanach.paramProd Q W) G h
      (scDerivGerm (F := ScBanach.paramProd Q W) G h) :=
    (hh.isScSmooth 1).1.isSc1GermWith_scDerivGerm
  have hF : IsSc1GermWith (F := ScBanach.paramProd Q W) G
      (fun x => h x + (ScBanach.paramProd Q W).toBase 1 (Z 0 x))
      (scDerivGerm (F := ScBanach.paramProd Q W) G h) :=
    hh1.congr fun x _ => by
      change h x = h x + (ScBanach.paramProd Q W).toBase 1 0
      rw [map_zero, add_zero]
  exact proposition_3_10 hC hh hs hF

/-- The level-`0` consequence: `Dh(0)` is Fredholm of index `n − N`. -/
theorem proposition_3_10_basic_level_zero (hC : IsPartialQuadrant (ScBanach.const P) Ct)
    {h : P × W 0 → Q × W 0} {Bc : P × W 0 → W 0} (hh : IsBasicGerm Ct G h Bc) :
    IsFredholm (scDerivGerm (F := ScBanach.paramProd Q W) G h 0) ∧
      fredholmIndex (scDerivGerm (F := ScBanach.paramProd Q W) G h 0) = finrank ℝ P - finrank ℝ Q := by
  obtain ⟨hop, hFred, hind⟩ := proposition_3_10_basic hC hh
  obtain ⟨sp⟩ := hFred
  have h1 := sp.isFredholm 0
  rw [hop.toScOperator_zero] at h1
  rw [scIndex_eq_fredholmIndex, hop.toScOperator_zero] at hind
  exact ⟨h1, hind⟩

end Basic

/-! ### The linearization of a map conjugated to a basic germ -/

section Conjugate

variable {C U : Set (E 0)}

/-- **The derivative of a map conjugated to a basic germ is Fredholm of index `n − N`**: if
`k : U → F` is sc-smooth with `k(0) = 0` and `(Ψ(u, k(u)))₂ = h(ψ(u))` near `0` for a basic germ
`h` and a strong bundle isomorphism `Ψ` covering `ψ`, then `Γ(0)Dk(0) = Dh(0)Dψ(0)`, so
`Dk(0) = Γ(0)⁻¹ Dh(0) Dψ(0)` is Fredholm (level `0`) of index `ind Dh(0) = n − N`. -/
theorem IsConjugateToBasicGerm.scDeriv_isFredholm_wholeChart (hU : IsRelOpenInQuadrant E C U)
    (h0 : (0 : E 0) ∈ U) {k : E 0 → F 0} (hk : IsScSmooth U k) (hk0 : k 0 = 0)
    (hconj : IsConjugateToBasicGerm U k) :
    IsFredholm (scDeriv U k 0) ∧ ∃ n N : ℕ, fredholmIndex (scDeriv U k 0) = n - N := by
  obtain ⟨Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, U', Ψ, Ψ', G, h, Bc, hCt, hU', hΨ, hψ0, hG, hh,
    hev⟩ := hconj
  have hC : IsQuadrantLike E C := hU.isPartialQuadrant.isQuadrantLike
  have hC' : IsQuadrantLike (ScBanach.paramProd Pn W) (Ct ×ˢ univ) :=
    hU'.isPartialQuadrant.isQuadrantLike
  have hU'C : U' ⊆ Ct ×ˢ univ := by
    obtain ⟨Uo, -, rfl⟩ := hU'.relOpen; exact inter_subset_right
  have h01 : (0 : E 1) ∈ E.lvlSet U 1 := by rw [ScBanach.mem_lvlSet, map_zero]; exact h0
  have h0U' : (0 : (ScBanach.paramProd Pn W) 0) ∈ U' := hψ0 ▸ hΨ.toFun.base_mem h0
  have h01' : (0 : (ScBanach.paramProd Pn W) 1) ∈ (ScBanach.paramProd Pn W).lvlSet U' 1 := by
    rw [ScBanach.mem_lvlSet, map_zero]; exact h0U'
  set ψ := IsStrongBundleMap.base Ψ with hψdef
  set ψ' := IsStrongBundleMap.base Ψ' with hψ'def
  have hψψ' : ∀ u ∈ U, ψ' (ψ u) = u := fun u hu => hΨ.base_base hu
  have hψ'ψ : ∀ u' ∈ U', ψ (ψ' u') = u' := fun u' hu' => hΨ.base_base' hu'
  have hψ'0 : ψ' 0 = 0 := hΨ.base_zero' h0 hψ0
  have hψsm : IsScSmooth U ψ := hΨ.toFun.base_isScSmooth hU
  have hψ'sm : IsScSmooth U' ψ' := hΨ.invFun.base_isScSmooth hU'
  have hψU' : MapsTo ψ U U' := fun u hu => hΨ.toFun.base_mem hu
  have hψ'U : MapsTo ψ' U' U := fun u hu => hΨ.invFun.base_mem hu
  set Dk := scDeriv U k 0 with hDk
  set Dψ := scDeriv U ψ 0 with hDψ
  set Dψ' := scDeriv U' ψ' 0 with hDψ'
  set Dh := scDerivGerm (F := ScBanach.paramProd Q W) G h 0 with hDh
  set Γ := hΨ.toFun.fiberCLM h0 with hΓ
  set Γ' := hΨ.invFun.fiberCLM h0U' with hΓ'
  -- (a) `Dh(0)` is Fredholm of index `n − N`
  obtain ⟨hDhF, hDhind⟩ := proposition_3_10_basic_level_zero hCt hh
  -- (b) `Γ(0)Dk(0) = Dh(0)Dψ(0)`
  have hlhs : scDeriv U (fun u => (Ψ (u, k u)).2) 0 = Γ.comp Dk :=
    hΨ.toFun.scDeriv_fiber_comp hU h0 hk hk0
  have hlevψ : levelMap ψ 1 (0 : E 1) = 0 :=
    levelMap_eq_of_toBase_eq (by rw [map_zero, map_zero, hψ0])
  have hrhs : scDeriv U (fun u => (Ψ (u, k u)).2) 0 = Dh.comp Dψ := by
    -- the neighbourhood `N₁` where the conjugation identity holds
    obtain ⟨N₁, hN₁sub, hN₁open, h0N₁⟩ := mem_nhds_iff.1 hev
    have hU₁ : IsRelOpenInQuadrant E C (U ∩ N₁) := hU.inter_isOpen hN₁open
    have h0₁ : (0 : E 0) ∈ U ∩ N₁ := ⟨h0, h0N₁⟩
    set G₀ := ScNbhdGerm.ofSet hU₁.relOpen h0₁ with hG₀
    have hψG₀ : IsSc0Germ (F := ScBanach.paramProd Pn W) G₀ ψ :=
      ((hψsm.of_subset hU₁.isScDomain inter_subset_left).isScSmoothGerm hC hU₁.relOpen h0₁) 0
    have hψC' : MapsTo ψ (G₀.U 0) (Ct ×ˢ univ) := fun u hu => hU'C (hψU' hu.1)
    set G₁ := G₀.preimage G hψG₀ hψ0 hψC' with hG₁
    have hG₁sub : ∀ m, G₁.U m ⊆ (ScNbhdGerm.ofSet hU.relOpen h0).U m := fun m x hx =>
      E.lvlSet_mono inter_subset_left m (G₀.preimage_subset G hψG₀ hψ0 hψC' m hx)
    -- the germs involved
    have hhG : IsSc1GermWith (F := ScBanach.paramProd Q W) G h
        (scDerivGerm (F := ScBanach.paramProd Q W) G h) :=
      (hh.isScSmooth 1).1.isSc1GermWith_scDerivGerm
    have hbridge : ∀ {F₁ : ScBanach} {φ : E 0 → F₁ 0}, IsSc1 U φ →
        IsSc1GermWith (ScNbhdGerm.ofSet hU.relOpen h0) φ (scDeriv U φ) := fun {F₁ φ} hφ =>
      ⟨hφ.isSc0.isSc0Germ hU.relOpen h0, hφ.isSc1With_scDeriv.hasFDerivWithinAt, by
        have := hφ.tangentMap_isSc0
        rw [ScNbhdGerm.ofSet_tangent]
        exact this.isSc0Germ _ _⟩
    have hψG₁ : IsSc1GermWith (F := ScBanach.paramProd Pn W) G₁ ψ (scDeriv U ψ) :=
      (hbridge hψsm.isSc1).mono hG₁sub
    have hcomp : IsSc1GermWith (F := ScBanach.paramProd Q W) G₁ (h ∘ ψ)
        (fun x => (scDerivGerm (F := ScBanach.paramProd Q W) G h (levelMap ψ 1 x)).comp
          (scDeriv U ψ x)) :=
      hhG.comp (G.relOpenConvex hC' 1) hψG₁ (G₀.preimage_mapsToGerm G hψG₀ hψ0 hψC')
    -- the set-sc-smoothness of `u ↦ (Ψ(u, k(u)))₂`
    have hUF := (hU.prod_univ F).isScDomain
    have hpairsm : IsScSmooth U (scPair (_root_.id : E 0 → E 0) k) :=
      (isScSmooth_id hU.isScDomain).scPair hU.isScDomain hk
    have hksm : IsScSmooth U fun u => (Ψ (u, k u)).2 :=
      (IsScSmooth.comp hU.isScDomain hUF (hΨ.toFun.isScSmooth_zero.snd hUF) hpairsm
        fun u hu => ⟨hu, mem_univ _⟩).congr hU.isScDomain fun _ _ => rfl
    have hkG₁ : IsSc1GermWith G₁ (h ∘ ψ) (scDeriv U fun u => (Ψ (u, k u)).2) :=
      ((hbridge hksm.isSc1).mono hG₁sub).congr fun u hu => by
        have hu' : u ∈ U ∩ N₁ := G₀.preimage_subset G hψG₀ hψ0 hψC' 0 hu
        exact hN₁sub hu'.2 hu'.1
    have e1 := IsSc1Germ.scDerivGerm_eqOn hC hkG₁ (G₁.zero_mem 1)
    have e2 := IsSc1Germ.scDerivGerm_eqOn hC hcomp (G₁.zero_mem 1)
    rw [← e1, e2, hlevψ]
  have hkey : Γ.comp Dk = Dh.comp Dψ := by rw [← hlhs, hrhs]
  -- (c) `Dψ(0)` and `Γ(0)` are isomorphisms
  have hlevψ' : levelMap ψ' 1 (0 : (ScBanach.paramProd Pn W) 1) = 0 :=
    levelMap_eq_of_toBase_eq (by rw [map_zero, map_zero, hψ'0])
  have hψψ'D : ∀ x, Dψ' (Dψ x) = x := fun x => by
    have := scDeriv_comp_eq_self hU hU' hψsm.isSc1 hψ'sm.isSc1 hψU' hψψ' h01 x
    rwa [hlevψ] at this
  have hψ'ψD : ∀ x, Dψ (Dψ' x) = x := fun x => by
    have := scDeriv_comp_eq_self hU' hU hψ'sm.isSc1 hψsm.isSc1 hψ'U hψ'ψ h01' x
    rwa [hlevψ'] at this
  set e₁ : E 0 ≃L[ℝ] (ScBanach.paramProd Pn W) 0 :=
    ContinuousLinearEquiv.equivOfInverse Dψ Dψ' hψψ'D hψ'ψD with he₁
  have hΓΓ' : ∀ y, Γ (Γ' y) = y := fun y => by
    simp only [hΓ, hΓ']
    have h1 : Ψ' (0, y) = (ψ' 0, (Ψ' (0, y)).2) := hΨ.invFun.apply_eq h0U' y
    rw [hψ'0] at h1
    have h2 := congrArg Prod.snd (hΨ.right_inv (0, y) ⟨h0U', mem_univ _⟩)
    rw [h1] at h2
    exact h2
  have hΓ'Γ : ∀ y, Γ' (Γ y) = y := fun y => by
    simp only [hΓ, hΓ']
    have h1 : Ψ (0, y) = (ψ 0, (Ψ (0, y)).2) := hΨ.toFun.apply_eq h0 y
    rw [hψ0] at h1
    have h2 := congrArg Prod.snd (hΨ.left_inv (0, y) ⟨h0, mem_univ _⟩)
    rw [h1] at h2
    exact h2
  set e₂ : (ScBanach.paramProd Q W) 0 ≃L[ℝ] F 0 :=
    ContinuousLinearEquiv.equivOfInverse Γ' Γ hΓΓ' hΓ'Γ with he₂
  -- (d) `Dk(0) = Γ(0)⁻¹ Dh(0) Dψ(0)`
  have hDk_eq : Dk = (e₂ : (ScBanach.paramProd Q W) 0 →L[ℝ] F 0).comp
      (Dh.comp (e₁ : E 0 →L[ℝ] (ScBanach.paramProd Pn W) 0)) := by
    ext x
    have := congrArg (fun T : E 0 →L[ℝ] (ScBanach.paramProd Q W) 0 => Γ' (T x)) hkey
    simp only [ContinuousLinearMap.comp_apply] at this
    rw [hΓ'Γ] at this
    exact this
  obtain ⟨hF, hind⟩ := isFredholm_equiv_comp_equiv hDhF e₁ e₂
  rw [← hDk_eq] at hF hind
  exact ⟨hF, finrank ℝ Pn, finrank ℝ Q, by rw [hind, hDhind]⟩

end Conjugate

/-! ### Proposition 3.52 -/

section Prop352

variable {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

open StrongRetr

/-- **Proposition 3.52 in the chart of Definition 3.11**: let `g` be a filled version of the
principal part `f̂` of a section at a zero (`f̂(0) = 0`), `s` a local sc⁺-section with
`s(0) = g(0)` and `g − s` conjugated to a basic germ.  Then `Dg(0) : E → F` is a Fredholm
operator (on level `0`) of index `n − N`, and so is `Tf(0) = Dg(0)|_{T₀O} : T₀O → K₀`
(Propositions 3.10, 1.10 and 3.5). -/
theorem proposition_3_52_local_wholeChart (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (h0 : (0 : E 0) ∈ U) (h0O : (0 : E 0) ∈ r R '' U) {fb g : E 0 → F 0}
    (hfill : IsFilledVersion hU hR h0 fb g) (hfb0 : fb 0 = 0)
    (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ)) {s : E 0 → F 1}
    (hs : IsScSmooth (F := F.shift) U s) (hs0 : F.toBase 1 (s 0) = g 0)
    (hconj : IsConjugateToBasicGerm U fun u => g u - F.toBase 1 (s u)) :
    ∃ (h1 : ∀ x, ρCLM hR h0 (scDeriv U g 0 (scDeriv U (r R) 0 x)) =
        scDeriv U g 0 (scDeriv U (r R) 0 x)) (n N : ℕ),
      IsFredholm (scDeriv U g 0) ∧ fredholmIndex (scDeriv U g 0) = n - N ∧
      IsFredholm (fillerRestrict (scDeriv U (r R) 0) (ρCLM hR h0) (scDeriv U g 0) h1) ∧
      fredholmIndex (fillerRestrict (scDeriv U (r R) 0) (ρCLM hR h0) (scDeriv U g 0) h1) = n - N := by
  have hg : IsScSmooth U g := hfill.isScSmooth
  have hg0 : g 0 = 0 := by rw [← hfill.filler.eq_on.self_of_nhds h0O, hfb0]
  have h01 : (0 : E 1) ∈ E.lvlSet U 1 := by rw [ScBanach.mem_lvlSet, map_zero]; exact h0
  have huniq := hU.isScDomain.uniqueDiffWithinAt 1 0 h01
  set k : E 0 → F 0 := fun u => g u - F.toBase 1 (s u) with hkdef
  have hk : IsScSmooth U k := hg.sub hU.isScDomain (hs.toBase_shift hU.isScDomain)
  have hk0 : k 0 = 0 := by simp only [hkdef]; rw [hs0, hg0, sub_self]
  obtain ⟨hDkF, n, N, hDkind⟩ := hconj.scDeriv_isFredholm_wholeChart hU h0 hk hk0
  -- `Dg(0) = Dk(0) + ιDs(0)`, with `ιDs(0)` compact
  have hDsop : IsScOperator (scDeriv (F := F.shift) U s 0) :=
    hs.isSc1.isSc1With_scDeriv.scOperator_deriv h01 (by
      show E.toBase 1 0 ∈ (E.smooth : Set (E 0))
      rw [map_zero]; exact E.smooth.zero_mem)
  set S : ScPlus E F := hDsop.toScOperator with hS
  have hDg : scDeriv U g 0 = scDeriv U k 0 + S.toScOperator 0 := by
    apply ContinuousLinearMap.ext_of_comp_toBase_one (E := E)
    have h1 := hg.isSc1.isSc1With_scDeriv.hasFDerivWithinAt 0 h01
    have h2 := (hk.isSc1.isSc1With_scDeriv.hasFDerivWithinAt 0 h01).add
      ((F.toBase 1).hasFDerivAt.comp_hasFDerivWithinAt (0 : E 1)
        (hs.isSc1.isSc1With_scDeriv.hasFDerivWithinAt 0 h01))
    have h2' : HasFDerivWithinAt (g ∘ E.toBase 1)
        ((scDeriv U k 0).comp (E.toBase 1) +
          (F.toBase 1).comp ((scDeriv (F := F.shift) U s 0).comp (E.toBase 1)))
        (E.lvlSet U 1) 0 := by
      refine h2.congr (fun x _ => ?_) ?_
      · simp only [Function.comp_apply, hkdef, Pi.add_apply]; abel
      · simp only [Function.comp_apply, hkdef, Pi.add_apply]; abel
    have := huniq.eq h1 h2'
    rw [this, ContinuousLinearMap.add_comp]
    congr 1
    ext x
    show F.toBase 1 (scDeriv (F := F.shift) U s 0 (E.toBase 1 x)) = F.incl 0 (S 0 (E.toBase 1 x))
    rw [hS, hDsop.toScOperator_zero]
    rfl
  have hcompact : IsCompactOperator (S.toScOperator 0) := S.isCompactOperator 0
  have hDgF : IsFredholm (scDeriv U g 0) := by
    rw [hDg]; exact isFredholm_add_isCompactOperator hDkF hcompact
  have hDgind : fredholmIndex (scDeriv U g 0) = n - N := by
    rw [hDg, fredholmIndex_add_isCompactOperator hDkF hcompact, hDkind]
  -- Proposition 3.5
  obtain ⟨h1, -, hFiff, hindeq⟩ := hfill.filler.proposition_3_5 hg hg0 h0O hfK
  exact ⟨h1, n, N, hDgF, hDgind, hFiff.2 hDgF, by rw [hindeq, hDgind]⟩

end Prop352

/-! ### Proposition 3.52 for sections of strong bundles -/

section Bundle

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

open StrongRetr

/-- **Proposition 3.52**: let `f` be a section of the strong bundle `P : Y → X` with `(f, x₀)` an
sc-Fredholm germ and `f(x₀) = 0`.  Then in the strong bundle chart of Definition 3.11 (centred at
`x₀`, with filled version `g` of the principal part `f̂`) the linearization
`Tf(x₀) = Dg(0)|_{T₀O} : T₀O → K₀` (`fillerRestrict`) is a Fredholm operator of index `n − N`,
`n − N` the index of the conjugating basic germ, and so is `Dg(0) : E → F`.  (The text: "`Tf(x) :
T_xX → Y_x` is an sc-Fredholm operator"; here the level-`0` Fredholm property with the index, in
the chart.) -/
theorem proposition_3_52_wholeChart (hf : IsSection P f) {x₀ : X} (hg : B.IsScFredholmGermWholeChart f x₀)
    (hx₀ : IsZeroAt P f x₀) :
    ∃ (c : StrongBundleChart PX P) (_ : B.IsChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
      (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0)
      (_ : IsFilledVersion c.relOpen c.isRetraction h0 (c.principal f) g)
      (h1 : ∀ x, ρCLM c.isRetraction h0 (scDeriv c.U g 0 (scDeriv c.U (r c.R) 0 x)) =
        scDeriv c.U g 0 (scDeriv c.U (r c.R) 0 x)) (n N : ℕ),
      IsFredholm (scDeriv c.U g 0) ∧ fredholmIndex (scDeriv c.U g 0) = n - N ∧
      IsFredholm (fillerRestrict (scDeriv c.U (r c.R) 0) (ρCLM c.isRetraction h0)
        (scDeriv c.U g 0) h1) ∧
      fredholmIndex (fillerRestrict (scDeriv c.U (r c.R) 0) (ρCLM c.isRetraction h0)
        (scDeriv c.U g 0) h1) = n - N := by
  obtain ⟨-, c, hc, hxV, hφ0, h0U, g, s, hfill, hs, hs0, hconj⟩ := hg
  have h0O : (0 : c.φ.model.E 0) ∈ r c.R '' c.U := by
    rw [c.r_image, ← hφ0]; exact c.φ.mapsTo_model x₀ hxV
  have hfb0 : c.principal f 0 = 0 := by
    have := (c.isZeroAt_iff hf hxV).1 hx₀
    rwa [hφ0] at this
  have hfK : ∀ x ∈ r c.R '' c.U, (x, c.principal f x) ∈ c.R '' (c.U ×ˢ univ) := by
    intro x hx
    rw [c.r_image] at hx
    rw [← c.apply_section hf hx]
    change c (f (c.φ.symm x)) ∈ c.K
    rw [← c.image_source]
    exact ⟨_, c.mem_source_of_proj (by rw [hf]; exact c.φ.symm_mapsTo hx), rfl⟩
  obtain ⟨h1, n, N, hDgF, hDgind, hTF, hTind⟩ :=
    proposition_3_52_local_wholeChart c.relOpen c.isRetraction h0U h0O hfill hfb0 hfK hs hs0 hconj
  exact ⟨c, hc, hxV, hφ0, h0U, g, hfill, h1, n, N, hDgF, hDgind, hTF, hTind⟩

end Bundle

end Polyfold
