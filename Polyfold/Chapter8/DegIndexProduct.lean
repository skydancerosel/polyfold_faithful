import Polyfold.Chapter2.FibredProduct
import Polyfold.Chapter2.TameRetracts
import Polyfold.Chapter8.ProperCovering

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §8.5, after Definition 8.5.1
(p. 383): the degeneracy index of `X ×_F Y` in `X × Y` (comparison item V8.28), and Part I's product
formula `d_{X × Y}(x, y) = d_X(x) + d_Y(y)`.

# The product formula for the degeneracy index beyond tameness

Part I's formalization proves `d_{X × Y} ≤ d_X + d_Y` for all M-polyfolds
(`MPolyfold.degIndex_prod_le`) and equality for tame ones (`MPolyfold.isTame_prod`).  Here
equality is proved at every pair of points at which the lower bound of Theorem 2.4.12 (p. 63) is
attained:

* `MPolyfold.IsDegSharpAt P x`: some chart `φ` of `X` around `x`, a retraction `r` onto its
  retract `O`, a presentation `T` of its partial quadrant and a level-`1` point `z` over `φ(x)` with
  `d_X(x) ≤ dim(T_zO / T^R_zO)` (by Theorem 2.4.12 this is then an equality).
* `quotDim_prod`: `dim((A ⊕ A') / (B ⊕ B')) = dim(A/B) + dim(A'/B')` for finite-dimensional
  quotients.
* `MPolyfold.degIndex_prod_of_isDegSharpAt`: if `x` and `y` are such points, then
  `d_{X × Y}(x, y) = d_X(x) + d_Y(y)` and `(x, y)` is such a point of `X × Y`.  The lower bound is
  Theorem 2.4.12 in the product chart: `T_{(z, z')}(O × O') = T_zO ⊕ T_{z'}O'` and the reduced
  tangent spaces are products.
* `MPolyfold.isDegSharpAt_of_isTameWith`: at a smooth point of the domain of a tame chart the
  bound is attained (so the notion contains the smooth points of tame M-polyfolds); and
  `MPolyfold.isDegSharpAt_of_degIndex_eq_zero`: every point with `d_X(x) = 0` over a level-`1`
  point of some chart is one.

* `EpFunctor.IsProperCovering.degIndex_prod_fibredMap_of_isDegSharpAt` (V8.28): for a proper
  covering `F : Y → X`, if the bound is attained at `F(φ) ∈ 𝐗` and at `s(φ) ∈ Y`, then
  `d_{𝐗 × Y}(F(φ), s(φ)) = 2 d_𝐘(φ)` and `2 d_{𝐗 ₛ×_F Y}(F(φ), s(φ)) = d_{𝐗 × Y}(F(φ), s(φ))`,
  without tameness.

## What is left

Whether `d_{X × Y} = d_X + d_Y` holds at every pair of points of arbitrary M-polyfolds is not
settled: at a point where `d_X(x)` exceeds `dim(T_zO / T^R_zO)` in every chart, the minimum of
Definition 2.4.1 over the non-product charts of `X × Y` is not controlled by this argument.
-/

open Set Filter Topology Function Module

noncomputable section

namespace Polyfold

/-! ### Linear algebra: quotients of products -/

section QuotDimProd

variable {V V' : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup V'] [Module ℝ V']

/-- The map `A ⊕ A' → A/B × A'/B'`. -/
def quotProdMap (A B : Submodule ℝ V) (A' B' : Submodule ℝ V') :
    (A.prod A') →ₗ[ℝ] (A ⧸ B.comap A.subtype) × (A' ⧸ B'.comap A'.subtype) where
  toFun x := (Submodule.Quotient.mk ⟨x.1.1, x.2.1⟩, Submodule.Quotient.mk ⟨x.1.2, x.2.2⟩)
  map_add' x y := by
    refine Prod.ext ?_ ?_
    · change Submodule.Quotient.mk (⟨x.1.1, x.2.1⟩ + ⟨y.1.1, y.2.1⟩ : A) = _
      rw [Submodule.Quotient.mk_add]; rfl
    · change Submodule.Quotient.mk (⟨x.1.2, x.2.2⟩ + ⟨y.1.2, y.2.2⟩ : A') = _
      rw [Submodule.Quotient.mk_add]; rfl
  map_smul' c x := by
    refine Prod.ext ?_ ?_
    · change Submodule.Quotient.mk (c • ⟨x.1.1, x.2.1⟩ : A) = _
      rw [Submodule.Quotient.mk_smul]; rfl
    · change Submodule.Quotient.mk (c • ⟨x.1.2, x.2.2⟩ : A') = _
      rw [Submodule.Quotient.mk_smul]; rfl

lemma quotProdMap_surjective (A B : Submodule ℝ V) (A' B' : Submodule ℝ V') :
    Surjective (quotProdMap A B A' B') := by
  rintro ⟨q, q'⟩
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨a', rfl⟩ := Submodule.Quotient.mk_surjective _ q'
  exact ⟨⟨(a.1, a'.1), a.2, a'.2⟩, rfl⟩

lemma ker_quotProdMap (A B : Submodule ℝ V) (A' B' : Submodule ℝ V') :
    LinearMap.ker (quotProdMap A B A' B') = (B.prod B').comap (A.prod A').subtype := by
  ext x
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_prod]
  change (Submodule.Quotient.mk _, Submodule.Quotient.mk _) = (0 : _ × _) ↔ _
  rw [Prod.mk_eq_zero, Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_eq_zero]
  rfl

/-- **`dim((A ⊕ A') / (B ⊕ B')) = dim(A/B) + dim(A'/B')`** for finite-dimensional quotients. -/
theorem quotDim_prod (A B : Submodule ℝ V) (A' B' : Submodule ℝ V')
    (h : FiniteDimensional ℝ (A ⧸ B.comap A.subtype))
    (h' : FiniteDimensional ℝ (A' ⧸ B'.comap A'.subtype)) :
    quotDim (A.prod A') (B.prod B') = quotDim A B + quotDim A' B' := by
  have e := (LinearMap.quotKerEquivOfSurjective _ (quotProdMap_surjective A B A' B'))
  rw [ker_quotProdMap] at e
  rw [quotDim, e.finrank_eq, Module.finrank_prod]
  rfl

end QuotDimProd

namespace MPolyfold

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : MPolyfold X) (Q : MPolyfold Y)

/-- `x` is a point at which **the lower bound of Theorem 2.4.12 (p. 63) is attained**: some chart
`φ` around `x`, retraction `r` onto `O = φ(V)`, presentation `T` of `C` and level-`1` point `z` over
`φ(x)` have `d_X(x) ≤ dim(T_zO / T^R_zO)` (hence `=`, by Theorem 2.4.12). -/
def IsDegSharpAt (x : X) : Prop :=
  ∃ (φ : MChart X) (_ : P.IsChart φ) (_ : x ∈ φ.source) (R : ScRetraction φ.model.E φ.model.C)
    (_ : R.retract = φ.model.O) (n : ℕ) (W : ScBanach)
    (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W))
    (_ : φ.model.C = T 0 ⁻¹' quadrant n W 0) (z : φ.model.E 1) (_ : φ.model.E.toBase 1 z = φ x),
    P.degIndex x ≤ quotDim (LinearMap.range (scDeriv R.U R z : φ.model.E 0 →ₗ[ℝ] φ.model.E 0))
      (reducedTangentSpaceWith R T z)

variable {P Q}

/-- At a point with `d_X(x) = 0` over a level-`1` point of a chart the bound is attained. -/
theorem isDegSharpAt_of_degIndex_eq_zero {x : X} (h0 : P.degIndex x = 0) {φ : MChart X}
    (hφ : P.IsChart φ) (hx : x ∈ φ.source) {z : φ.model.E 1} (hz : φ.model.E.toBase 1 z = φ x) :
    P.IsDegSharpAt x := by
  obtain ⟨R, hR⟩ := φ.model.isScRetract
  obtain ⟨n, W, T, hT⟩ := φ.model.isPartialQuadrant
  exact ⟨φ, hφ, hx, R, hR, n, W, T, hT, z, hz, by rw [h0]; exact Nat.zero_le _⟩

/-- **Tame charts attain the bound at smooth points** (equations (15)–(16) of §2.5 and
`degIndex_eq_chartDegIndex_of_isTameWith`). -/
theorem isDegSharpAt_of_isTameWith {φ : MChart X} (hφ : P.IsChart φ)
    (R : ScRetraction φ.model.E φ.model.C) (hR : R.retract = φ.model.O) {n : ℕ} {W : ScBanach}
    {T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)}
    (hT : φ.model.C = T 0 ⁻¹' quadrant n W 0) (htame : R.IsTameWith T) {x : X}
    (hx : x ∈ φ.source) (hxs : φ x ∈ φ.model.E.smooth) : P.IsDegSharpAt x := by
  obtain ⟨z, hz, hzs⟩ := exists_smoothLvl_one_of_mem_smooth hxs
  have hzO : z ∈ φ.model.E.lvlSet R.retract 1 := by
    rw [ScBanach.mem_lvlSet, hz, hR]; exact φ.mapsTo_model x hx
  refine ⟨φ, hφ, hx, R, hR, n, W, T, hT, z, hz, ?_⟩
  rw [quotDim_reducedTangentSpaceWith_eq htame hzO hzs,
    P.degIndex_eq_chartDegIndex_of_isTameWith hφ R hR hT htame hx, chartDegIndex,
    degIndex_eq T hT (φ.apply_mem_C hx), hz]

/-- **The product formula at points attaining the bound of Theorem 2.4.12** (Part I's product
formula, used after Definition 8.5.1, p. 383; comparison item V8.28): if the lower bound of
Theorem 2.4.12 is attained at `x ∈ X` and at `y ∈ Y`, then `d_{X × Y}(x, y) = d_X(x) + d_Y(y)`,
and the bound is attained at `(x, y)`.  No tameness is assumed. -/
theorem degIndex_prod_of_isDegSharpAt [ParacompactSpace (X × Y)] {x : X} {y : Y}
    (hx : P.IsDegSharpAt x) (hy : Q.IsDegSharpAt y) :
    (P.prod Q).degIndex (x, y) = P.degIndex x + Q.degIndex y ∧ (P.prod Q).IsDegSharpAt (x, y) := by
  obtain ⟨φ, hφ, hxφ, R, hR, n, W, T, hT, z, hz, hdx⟩ := hx
  obtain ⟨ψ, hψ, hyψ, R', hR', n', W', T', hT', z', hz', hdy⟩ := hy
  have hTT' := prod_eq_prodPresentation T T' hT hT'
  have hret : (R.prod R').retract = (φ.prod ψ).model.O := by
    rw [R.prod_retract, hR, hR']; rfl
  set zz : (φ.model.E.prod ψ.model.E) 1 := (z, z') with hzz
  have hzz0 : (φ.model.E.prod ψ.model.E).toBase 1 zz = (φ.prod ψ) (x, y) := by
    rw [ScBanach.prod_toBase, hz, hz']; rfl
  have hzU : zz ∈ (φ.model.E.prod ψ.model.E).lvlSet (R.U ×ˢ R'.U) 1 := by
    rw [lvlSet_prod]
    refine ⟨?_, ?_⟩
    · rw [ScBanach.mem_lvlSet, hz]
      exact R.retract_subset (hR ▸ φ.mapsTo_model x hxφ)
    · rw [ScBanach.mem_lvlSet, hz']
      exact R'.retract_subset (hR' ▸ ψ.mapsTo_model y hyψ)
  -- the tangent and reduced tangent spaces of `O × O'` at `(z, z')` are products
  have hD := scDeriv_prodMap R.relOpen R'.relOpen R.isScSmooth R'.isScSmooth hzU
  have hrange : LinearMap.range (scDeriv (R.prod R').U (R.prod R') zz :
        (φ.model.E.prod ψ.model.E) 0 →ₗ[ℝ] (φ.model.E.prod ψ.model.E) 0) =
      (LinearMap.range (scDeriv R.U R z : φ.model.E 0 →ₗ[ℝ] φ.model.E 0)).prod
        (LinearMap.range (scDeriv R'.U R' z' : ψ.model.E 0 →ₗ[ℝ] ψ.model.E 0)) := by
    change LinearMap.range (scDeriv (E := φ.model.E.prod ψ.model.E)
      (F := φ.model.E.prod ψ.model.E) (R.U ×ˢ R'.U) (Prod.map R R') zz :
        (φ.model.E.prod ψ.model.E) 0 →ₗ[ℝ] (φ.model.E.prod ψ.model.E) 0) = _
    rw [hD, ContinuousLinearMap.coe_prodMap, LinearMap.range_prodMap]
  have hred : reducedTangentSpaceWith (R.prod R') (prodPresentation T T') zz =
      (reducedTangentSpaceWith R T z).prod (reducedTangentSpaceWith R' T' z') := by
    rw [reducedTangentSpaceWith, hrange, ScBanach.prod_toBase,
      minimalSubspaceWith_prodPresentation, Submodule.prod_inf_prod]
    rfl
  have hquot : quotDim (LinearMap.range (scDeriv (R.prod R').U (R.prod R') zz :
        (φ.model.E.prod ψ.model.E) 0 →ₗ[ℝ] (φ.model.E.prod ψ.model.E) 0))
        (reducedTangentSpaceWith (R.prod R') (prodPresentation T T') zz) =
      quotDim (LinearMap.range (scDeriv R.U R z : φ.model.E 0 →ₗ[ℝ] φ.model.E 0))
          (reducedTangentSpaceWith R T z) +
        quotDim (LinearMap.range (scDeriv R'.U R' z' : ψ.model.E 0 →ₗ[ℝ] ψ.model.E 0))
          (reducedTangentSpaceWith R' T' z') := by
    rw [hrange, hred]
    exact quotDim_prod _ _ _ _ (finiteDimensional_quot_inf_minimalSubspace T _ _)
      (finiteDimensional_quot_inf_minimalSubspace T' _ _)
  -- Theorem 2.4.12 in the product chart
  have h2412 := theorem_2_4_12 (P.prod Q) (hφ.prod hψ) (R.prod R') hret (prodPresentation T T')
    hTT' (x := (x, y)) ⟨hxφ, hyψ⟩ hzz0
  replace h2412 := hquot.symm.le.trans h2412
  have heq : (P.prod Q).degIndex (x, y) = P.degIndex x + Q.degIndex y :=
    le_antisymm (P.degIndex_prod_le Q x y) ((add_le_add hdx hdy).trans h2412)
  refine ⟨heq, φ.prod ψ, hφ.prod hψ, ⟨hxφ, hyψ⟩, R.prod R', hret, n + n', W.prod W',
    prodPresentation T T', hTT', zz, hzz0, ?_⟩
  rw [heq]
  exact (add_le_add hdx hdy).trans_eq hquot.symm

end MPolyfold

/-! ### The remark after Definition 8.5.1 without tameness -/

section Fibres

variable {ObjY MorY : Type u} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  {ObjX MorX : Type v} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {Y : EpGroupoid ObjY MorY} {X : EpGroupoid ObjX MorX} {F : EpFunctor Y X}

/-- **The degeneracy remark after Definition 8.5.1 (p. 383), at points attaining the bound of
Theorem 2.4.12** (comparison item V8.28): for a proper covering `F`, if the lower bound of Theorem
2.4.12 is attained at `F(φ) ∈ 𝐗` and at `s(φ) ∈ Y`, then `d_{𝐗 × Y}(F(φ), s(φ)) = 2 · d_𝐘(φ)` and
`2 · d_{𝐗 ₛ×_F Y}(F(φ), s(φ)) = d_{𝐗 × Y}(F(φ), s(φ))`.  No tameness of `X` or `Y` is assumed. -/
theorem EpFunctor.IsProperCovering.degIndex_prod_fibredMap_of_isDegSharpAt
    (hF : F.IsProperCovering) (φ : MorY) (h1 : X.PMor.IsDegSharpAt (F.mor φ))
    (h2 : Y.PObj.IsDegSharpAt (Y.src φ)) :
    letI := MPolyfold.paracompactSpace_prod X.PMor Y.PObj
    letI := (X.PMor.prod Y.PObj).paracompactSpace_subtype (MPolyfold.fibredProduct X.src F.obj)
    (X.PMor.prod Y.PObj).degIndex (F.mor φ, Y.src φ) = 2 * Y.PMor.degIndex φ ∧
      2 * (MPolyfold.subPolyfold (MPolyfold.isSubMPolyfold_fibredProduct
        X.isLocalScDiffeo_src F.isScSmoothMap_obj)).degIndex (F.fibredMap φ) =
        (X.PMor.prod Y.PObj).degIndex (F.mor φ, Y.src φ) := by
  let _ := MPolyfold.paracompactSpace_prod X.PMor Y.PObj
  let _ := (X.PMor.prod Y.PObj).paracompactSpace_subtype (MPolyfold.fibredProduct X.src F.obj)
  have h : (X.PMor.prod Y.PObj).degIndex (F.mor φ, Y.src φ) = 2 * Y.PMor.degIndex φ := by
    rw [(MPolyfold.degIndex_prod_of_isDegSharpAt h1 h2).1, hF.degIndex_mor, ← Y.degIndex_src]
    ring
  exact ⟨h, by rw [h, ← hF.degIndex_fibredMap]⟩

end Fibres

end Polyfold
