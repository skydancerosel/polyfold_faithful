import Polyfold.Chapter3.QuadrantClassCk
import Polyfold.Chapter2.FibredProduct

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §3.8.5: **Lemma 3.8.20**
(preprint 3.76), p. 167: the iterated tangent maps of the map of Proposition 3.8.17.

# The iterated tangent maps `T^k f` are smooth homeomorphisms

## The text, paraphrased

Under the assumptions of Proposition 3.8.17, `T^k f : T^k U → T^k V` is a smooth homeomorphism.
*Proof.*  `T^k C` is a partial quadrant in `T^k ℝⁿ`, `T^k U`, `T^k V` are relatively open in it, and
`T^k f` is smooth; its inverse is `Φ_{k+1}(y, l) = ((T^k f)⁻¹(y), [D(T^k f)((T^k f)⁻¹(y))]⁻¹ l)`,
continuous by induction.  The proof of Proposition 3.8.17 then applies Lemma 3.8.21 to each
`T^k f`.

## What is formalized

The induction runs over the bundled data `Polyfold.QuadMapData` (a finite-dimensional `V`, sets
`C`, `U` and a map `f`), whose tangent `QuadMapData.tangent` is `(V × V, C × V, U × V, Tf)` with
`Tf(x, h) = (f(x), Df(x)h)` (Definition 3.8.14, `bookTangentMap`), so that `T^k f` is
`(tangent^[k] d).f`.  `QuadMapData.IsSmoothHomeo`: `C` a partial quadrant, `U` and `f(U)`
relatively open in `C`, `f` smooth (`C^∞`, which is the text's smooth by
`isClassSmoothOn_iff_contDiffOn`) on `U`, a continuous inverse on `f(U)`, and `Df(x)` invertible
on `U` — the hypotheses of Lemma 3.8.21 (`lemma_3_8_21`).

* `Polyfold.QuadMapData.IsSmoothHomeo.tangent`: these are inherited by `Tf : TU → TV`; also
  `Tf(TU) = T(f(U)) = f(U) × V` (`image_tangentSet`).
* `Polyfold.lemma_3_8_20`: **Lemma 3.8.20** in general form: for every `k`, `T^k f` is a smooth
  homeomorphism of relatively open subsets of the partial quadrant `T^k C`, with invertible
  derivative, and its inverse is smooth (Lemma 3.8.21 for `T^k f`, `lemma_3_8_21_smooth`).
* `Polyfold.lemma_3_8_20_printed`: the hypotheses of Proposition 3.8.17 (`InvData`, for every
  `j`) give the data, so the lemma as printed is a special case.

The derivative of `Tf` at `(x, h)` is `(a, b) ↦ (Df(x)a, D²f(x)(a, h) + Df(x)b)`, injective since
`Df(x)` is, hence invertible in finite dimensions (`isUnit_fderivWithin_tangentMap`); this is the
fact behind the text's `[D(T^k f)(…)]⁻¹`.
-/

open Set Filter Topology Function
open scoped ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace Polyfold

/-! ### `C × V` is a partial quadrant of `V × V` -/

section ProdQuadrant

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The constant sc-structure on `V × V` is that of the product of the constant structures. -/
def constProdIso (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ScIso (ScBanach.const (V × V)) ((ScBanach.const V).prod (ScBanach.const V)) where
  lvl _ := ContinuousLinearEquiv.refl ℝ (V × V)
  incl_comm _ _ := rfl

/-- The tangent quadrant `TC = C × V` of a partial quadrant `C ⊆ V` is a partial quadrant of
`V × V`. -/
theorem IsPartialQuadrant.tangent_const {C : Set V} (hC : IsPartialQuadrant (ScBanach.const V) C) :
    IsPartialQuadrant (ScBanach.const (V × V)) (C ×ˢ (univ : Set V)) := by
  obtain ⟨n, W, T, hT⟩ := hC.prod (isPartialQuadrant_univ (ScBanach.const V))
  exact ⟨n, W, (constProdIso V).trans T, hT⟩

/-- `TU = U × V` is relatively open in `TC = C × V`. -/
theorem IsRelOpenInQuadrant.tangent_const {C U : Set V}
    (hU : IsRelOpenInQuadrant (ScBanach.const V) C U) :
    IsRelOpenInQuadrant (ScBanach.const (V × V)) (C ×ˢ (univ : Set V)) (U ×ˢ (univ : Set V)) := by
  refine ⟨hU.isPartialQuadrant.tangent_const, ?_⟩
  obtain ⟨O, hO, rfl⟩ := hU.relOpen
  exact ⟨O ×ˢ univ, hO.prod isOpen_univ, by rw [prod_inter_prod, inter_univ]⟩

end ProdQuadrant

/-! ### The tangent map of a smooth homeomorphism -/

section Tangent

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {U : Set V} {f : V → V}

/-- An injective endomorphism of a finite-dimensional space is a unit. -/
theorem isUnit_of_injective_clm {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] (L : Z →L[ℝ] Z) (hL : Injective L) : IsUnit L := by
  let e : Z ≃L[ℝ] Z := (LinearEquiv.ofInjectiveEndo (L : Z →ₗ[ℝ] Z) hL).toContinuousLinearEquiv
  refine ⟨(ContinuousLinearEquiv.unitsEquiv ℝ Z).symm e, ?_⟩
  ext z; rfl

/-- A unit of `Z →L[ℝ] Z` is injective. -/
theorem injective_of_isUnit_clm {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {L : Z →L[ℝ] Z} (hL : IsUnit L) : Injective L := by
  obtain ⟨u, rfl⟩ := hL
  intro x y hxy
  have h : ((↑u⁻¹ * ↑u : Z →L[ℝ] Z)) x = ((↑u⁻¹ * ↑u : Z →L[ℝ] Z)) y := by
    change (↑u⁻¹ : Z →L[ℝ] Z) ((u : Z →L[ℝ] Z) x) = (↑u⁻¹ : Z →L[ℝ] Z) ((u : Z →L[ℝ] Z) y)
    rw [hxy]
  rwa [Units.inv_mul] at h

/-- The derivative of `Tf` at `(x, h)`: `(a, b) ↦ (Df(x)a, Df(x)b + D²f(x)(a)h)`. -/
theorem hasFDerivWithinAt_tangentMap (hU : UniqueDiffOn ℝ U) (hf : ContDiffOn ℝ 2 f U)
    {p : V × V} (hp : p ∈ U ×ˢ (univ : Set V)) :
    HasFDerivWithinAt (bookTangentMap U f)
      (((fderivWithin ℝ f U p.1).comp (ContinuousLinearMap.fst ℝ V V)).prod
        ((fderivWithin ℝ f U p.1).comp (ContinuousLinearMap.snd ℝ V V) +
          ((fderivWithin ℝ (fderivWithin ℝ f U) U p.1).comp
            (ContinuousLinearMap.fst ℝ V V)).flip p.2))
      (U ×ˢ (univ : Set V)) p := by
  have hfst : MapsTo Prod.fst (U ×ˢ (univ : Set V)) U := fun q hq => hq.1
  have h1 : HasFDerivWithinAt f (fderivWithin ℝ f U p.1) U p.1 :=
    ((hf.differentiableOn (by norm_num)) _ hp.1).hasFDerivWithinAt
  have hD : ContDiffOn ℝ 1 (fderivWithin ℝ f U) U := hf.fderivWithin hU (by norm_num)
  have h2 : HasFDerivWithinAt (fderivWithin ℝ f U) (fderivWithin ℝ (fderivWithin ℝ f U) U p.1)
      U p.1 := ((hD.differentiableOn one_ne_zero) _ hp.1).hasFDerivWithinAt
  have h1' := h1.comp p (hasFDerivWithinAt_fst (p := p) (s := U ×ˢ (univ : Set V))) hfst
  have h2' := h2.comp p (hasFDerivWithinAt_fst (p := p) (s := U ×ˢ (univ : Set V))) hfst
  exact h1'.prodMk (h2'.clm_apply (hasFDerivWithinAt_snd (p := p)))

/-- **`D(Tf)` is invertible** where `Df` is (in finite dimensions). -/
theorem isUnit_fderivWithin_tangentMap (hU : UniqueDiffOn ℝ U) (hf : ContDiffOn ℝ 2 f U)
    {p : V × V} (hp : p ∈ U ×ˢ (univ : Set V)) (hDf : IsUnit (fderivWithin ℝ f U p.1)) :
    IsUnit (fderivWithin ℝ (bookTangentMap U f) (U ×ˢ (univ : Set V)) p) := by
  have h := hasFDerivWithinAt_tangentMap hU hf hp
  rw [h.fderivWithin ((uniqueDiffOn_tangentSet hU) p hp)]
  refine isUnit_of_injective_clm _ fun a b hab => ?_
  have hinj : Injective (fderivWithin ℝ f U p.1) := injective_of_isUnit_clm hDf
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_comp, comp_apply,
    ContinuousLinearMap.coe_fst', FunLike.coe_add, Pi.add_apply,
    ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.flip_apply, Prod.mk.injEq] at hab
  have h1 : a.1 = b.1 := hinj hab.1
  rw [h1] at hab
  exact Prod.ext h1 (hinj (add_right_cancel hab.2))

/-- `Tf` is smooth on `TU` when `f` is smooth on `U`. -/
theorem contDiffOn_tangentMap_infty (hU : UniqueDiffOn ℝ U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (bookTangentMap U f) (U ×ˢ (univ : Set V)) := by
  rw [contDiffOn_infty] at hf ⊢
  intro k
  exact (((contDiffOn_add_two_iff_tangentMap hU k).1 (hf (k + 2))).2).of_le
    (by exact_mod_cast (show k ≤ k + 1 by omega))

end Tangent

/-! ### The bundled data and the induction -/

/-- The data `(V, C, U, f)` of Lemmas 3.8.20 and 3.8.21: a finite-dimensional space `V`, sets
`C`, `U ⊆ V` and a map `f : V → V`. -/
structure QuadMapData where
  /-- The space `V` (the text: `T^k ℝⁿ`). -/
  V : Type
  [ng : NormedAddCommGroup V]
  [ns : NormedSpace ℝ V]
  [fd : FiniteDimensional ℝ V]
  /-- The partial quadrant `C`. -/
  C : Set V
  /-- The domain `U`. -/
  U : Set V
  /-- The map `f`. -/
  f : V → V

attribute [instance] QuadMapData.ng QuadMapData.ns QuadMapData.fd

namespace QuadMapData

/-- The tangent data `(V × V, TC, TU, Tf)` (Definition 3.8.14). -/
def tangent (d : QuadMapData) : QuadMapData where
  V := d.V × d.V
  C := d.C ×ˢ univ
  U := d.U ×ˢ univ
  f := bookTangentMap d.U d.f

/-- The hypotheses of Lemma 3.8.21: `U` and `f(U)` relatively open in the partial quadrant `C`,
`f` smooth on `U` and a homeomorphism `U → f(U)` (a continuous inverse `g`), `Df(x)` invertible. -/
structure IsSmoothHomeo (d : QuadMapData) : Prop where
  relOpen : IsRelOpenInQuadrant (ScBanach.const d.V) d.C d.U
  relOpen_image : IsRelOpenInQuadrant (ScBanach.const d.V) d.C (d.f '' d.U)
  smooth : ContDiffOn ℝ ∞ d.f d.U
  exists_inv : ∃ g : d.V → d.V, ContinuousOn g (d.f '' d.U) ∧ ∀ x ∈ d.U, g (d.f x) = x
  isUnit : ∀ x ∈ d.U, IsUnit (fderivWithin ℝ d.f d.U x)

variable {d : QuadMapData}

/-- `Tf(TU) = T(f(U)) = f(U) × V`. -/
theorem image_tangentSet (h : d.IsSmoothHomeo) :
    d.tangent.f '' d.tangent.U = (d.f '' d.U) ×ˢ (univ : Set d.V) := by
  ext ⟨y, l⟩
  constructor
  · rintro ⟨⟨x, k⟩, hx, he⟩
    simp only [tangent, bookTangentMap, Prod.mk.injEq] at he
    exact ⟨⟨x, hx.1, he.1⟩, mem_univ _⟩
  · rintro ⟨⟨x, hx, rfl⟩, -⟩
    obtain ⟨u, hu⟩ := h.isUnit x hx
    refine ⟨(x, (↑u⁻¹ : d.V →L[ℝ] d.V) l), ⟨hx, mem_univ _⟩, ?_⟩
    simp only [tangent, bookTangentMap, ← hu]
    change (d.f x, ((u : d.V →L[ℝ] d.V) * ↑u⁻¹) l) = (d.f x, l)
    rw [Units.mul_inv]; rfl

/-- **The inductive step of Lemma 3.8.20**: the tangent map of a smooth homeomorphism with
invertible derivative between relatively open subsets of a partial quadrant is again one, between
`TU` and `T(f(U))` in `TC`, with inverse `Φ(y, l) = (g(y), [Df(g(y))]⁻¹ l)`. -/
theorem IsSmoothHomeo.tangent (h : d.IsSmoothHomeo) : d.tangent.IsSmoothHomeo := by
  have hU := h.relOpen.uniqueDiffOn_const
  have hf2 : ContDiffOn ℝ 2 d.f d.U := by exact_mod_cast contDiffOn_infty.1 h.smooth 2
  have hf1 : ContDiffOn ℝ ((0 + 1 : ℕ) : WithTop ℕ∞) d.f d.U := by
    exact_mod_cast contDiffOn_infty.1 h.smooth 1
  obtain ⟨g, hg, hgf⟩ := h.exists_inv
  have hgU : ∀ y ∈ d.f '' d.U, g y ∈ d.U := by
    rintro _ ⟨x, hx, rfl⟩; rw [hgf x hx]; exact hx
  refine ⟨h.relOpen.tangent_const, ?_, contDiffOn_tangentMap_infty hU h.smooth, ?_, ?_⟩
  · rw [image_tangentSet h]; exact h.relOpen_image.tangent_const
  · refine ⟨fun q => (g q.1, Ring.inverse (fderivWithin ℝ d.f d.U (g q.1)) q.2), ?_, ?_⟩
    · rw [image_tangentSet h]
      have hfst : MapsTo Prod.fst ((d.f '' d.U) ×ˢ (univ : Set d.V)) (d.f '' d.U) :=
        fun q hq => hq.1
      have hg1 : ContinuousOn (fun q : d.V × d.V => g q.1) ((d.f '' d.U) ×ˢ univ) :=
        hg.comp continuous_fst.continuousOn hfst
      have hinv : ContinuousOn (fun y => Ring.inverse (fderivWithin ℝ d.f d.U (g y)))
          (d.f '' d.U) := by
        have := contDiffOn_inverse_deriv_comp hU hf1 (by exact_mod_cast contDiffOn_zero.2 hg)
          hgf h.isUnit
        exact contDiffOn_zero.1 this
      refine hg1.prodMk ?_
      exact (hinv.comp continuous_fst.continuousOn hfst).clm_apply continuous_snd.continuousOn
    · rintro ⟨x, k⟩ hx
      obtain ⟨u, hu⟩ := h.isUnit x hx.1
      have e1 : d.tangent.f (x, k) = (d.f x, fderivWithin ℝ d.f d.U x k) := rfl
      rw [e1]
      dsimp only
      rw [hgf x hx.1, ← hu, Ring.inverse_unit]
      change (x, ((↑u⁻¹ : d.V →L[ℝ] d.V) * ↑u) k) = (x, k)
      rw [Units.inv_mul]; rfl
  · rintro p hp
    exact isUnit_fderivWithin_tangentMap hU hf2 hp (h.isUnit p.1 hp.1)

/-- The iterated tangent data `T^k d`. -/
def iterTangent (d : QuadMapData) (k : ℕ) : QuadMapData := QuadMapData.tangent^[k] d

theorem iterTangent_succ (d : QuadMapData) (k : ℕ) :
    d.iterTangent (k + 1) = (d.iterTangent k).tangent :=
  Function.iterate_succ_apply' _ _ _

end QuadMapData

open QuadMapData in
/-- **Lemma 3.8.20 (preprint 3.76)**, 2021 p. 167, in general form: if `f : U → f(U)` is a smooth
homeomorphism with invertible derivative between relatively open subsets of a partial quadrant `C`
(the hypotheses of Lemma 3.8.21), then for every `k` the iterated tangent map
`T^k f : T^k U → T^k(f(U))` is again one, between relatively open subsets of the partial quadrant
`T^k C`, and its inverse is smooth (Lemma 3.8.21 applied to `T^k f`, as in the proof of
Proposition 3.8.17). -/
theorem lemma_3_8_20 {d : QuadMapData} (h : d.IsSmoothHomeo) (k : ℕ) :
    (d.iterTangent k).IsSmoothHomeo ∧
      ∃ g : (d.iterTangent k).V → (d.iterTangent k).V,
        ContDiffOn ℝ ∞ g ((d.iterTangent k).f '' (d.iterTangent k).U) ∧
          ∀ x ∈ (d.iterTangent k).U, g ((d.iterTangent k).f x) = x := by
  have hk : (d.iterTangent k).IsSmoothHomeo := by
    induction k with
    | zero => exact h
    | succ k ih => rw [iterTangent_succ]; exact ih.tangent
  obtain ⟨g, hg, hgf⟩ := hk.exists_inv
  exact ⟨hk, g, lemma_3_8_21_smooth hk.relOpen hk.relOpen_image hk.smooth hg hgf hk.isUnit, hgf⟩

/-- **Lemma 3.8.20 as printed**: under the hypotheses of Proposition 3.8.17 for a smooth `f`
(`InvData C U f j` for every `j`), every iterated tangent map `T^k f : T^k U → T^k V`,
`V = f(U)`, is a smooth homeomorphism (of relatively open subsets of `T^k C`, with invertible
derivative). -/
theorem lemma_3_8_20_printed {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {C U : Set V} {f : V → V} (hd : ∀ j, InvData C U f j) (k : ℕ) :
    (QuadMapData.iterTangent ⟨V, C, U, f⟩ k).IsSmoothHomeo := by
  have h0 := hd 1
  have hsm : ContDiffOn ℝ ∞ f U := contDiffOn_infty.2 fun j => by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · exact contDiffOn_zero.2 h0.continuousOn
    · exact (hd j).contDiffOn
  obtain ⟨O', hO', hV⟩ := h0.image_relOpen
  have h : QuadMapData.IsSmoothHomeo ⟨V, C, U, f⟩ :=
    ⟨⟨h0.isPartialQuadrant, h0.relOpen⟩, ⟨h0.isPartialQuadrant, O', hO', hV⟩, hsm,
      ⟨InvData.inv U f, h0.continuousOn_inv, fun _ hx => h0.inv_apply hx⟩,
      fun _ hx => h0.isUnit_deriv hx⟩
  exact (lemma_3_8_20 h k).1

end Polyfold
