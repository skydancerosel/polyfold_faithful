import Polyfold.Chapter8.DegIndexProductSmooth

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Definition 2.4.1 (p. 54),
Theorem 2.4.12 (p. 63), and §8.5, after Definition 8.5.1 (p. 383) (comparison item V8.28).

# The product formula at a level-`1` point and a point attaining the bound of Theorem 2.4.12

`MPolyfold.degIndex_prod_of_mem_smoothSet_of_isDegSharpAt` asks for a smooth point `x`.  Here
`x ∈ X₁` suffices:

* `IsSc1With.eventually_zeroCoord_imp_along_cone`: for an sc¹ map `f : U → C'` and `x ∈ U₁`,
  `e ∈ E₁ ∩ C_x`, the quadrant coordinates `i` of `f(x)` with `(Df(x)e)_i > 0` are positive at
  `f(x + t e)` for small `t > 0`.
* `ScRetraction.IsDiffeoGerm.quotDim_le_card_of_dominated`: along a germ of sc-diffeomorphisms
  `F : (O, x) → (O', y)`, a family of tangent vectors dominated in `C_x` by multiples of one vector
  `e₀` has, modulo the reduced tangent space, at most as many dimensions as `D(F ∘ r)(x)e₀` has
  positive coordinates among those vanishing at `y` (Proposition 2.4.10).
* **`MPolyfold.degIndex_prod_of_mem_levelSet_of_isDegSharpAt`**,
  **`MPolyfold.degIndex_prod_of_isDegSharpAt_of_mem_levelSet`**:
  `d_{X × Y}(x, y) = d_X(x) + d_Y(y)` if one point lies on level `1` and the bound of Theorem
  2.4.12 is attained at the other one.  In a chart `χ` of `X × Y` realizing `d_{X × Y}(x, y)` the
  curve `t ↦ χ(x, y_t)`, `y_t = ψ⁻¹(r'(ψ(y) + t u))`, is differentiable at `t = 0` because
  `(φ(x), ψ(y) + t u)` is a curve on level `1`; along it at least `d_Y(y)` of the coordinates
  vanishing at `χ(x, y)` become positive, and `d_X(x) ≤ d_{X × Y}(x, y_t)`
  (`degIndex_le_degIndex_prod_left`).
* `MPolyfold.isScDiffeoOn_prodSwap`, `MPolyfold.degIndex_prod_swap`: `X × Y ≅ Y × X`.
* `MPolyfold.degIndex_prod_of_frequently_levelSet_of_isDegSharpAt`: the same for an arbitrary
  `x`, if `d_X(x)` is attained at level-`1` points arbitrarily close to `x`.
* V8.28: `EpFunctor.IsProperCovering.degIndex_prod_fibredMap_of_mem_levelSet`.

## What is left

For `x` on level `0` only, the curve `t ↦ χ(x, y_t)` need not be differentiable, and whether
`d_X(x)` is attained at level-`1` points near `x` is not settled here.
-/

open Set Filter Topology Function Module

noncomputable section

namespace Polyfold

section Curve

variable {E E' : ScBanach} {n n' : ℕ} {W W' : ScBanach} {C : Set (E 0)} {U : Set (E 0)}
  {f : E 0 → E' 0} {D : E 1 → E 0 →L[ℝ] E' 0}

/-- **Coordinates with positive derivative become positive** (the one-sided sign argument of Lemma
2.4.9 read forwards): for an sc¹ map `f` on `U ⊆ C`, `x ∈ U₁` and `e ∈ E₁ ∩ C_x`, for small
`t > 0` the point `x + t e` lies in `U₁`, and every quadrant coordinate `i` vanishing at
`f(x + t e)` vanishes at `f(x)` and has `(Df(x)e)_i ≤ 0`. -/
theorem IsSc1With.eventually_zeroCoord_imp_along_cone
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (hT : C = T 0 ⁻¹' quadrant n W 0)
    (T' : ScIso E' ((ScBanach.const (Fin n' → ℝ)).prod W'))
    (hU : IsRelOpenInQuadrant E C U) (hf : IsSc1With U f D) {x : E 1} (hx : x ∈ E.lvlSet U 1)
    {e : E 1} (he : E.toBase 1 e ∈ partialQuadrantAtWith T (E.toBase 1 x)) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, x + t • e ∈ E.lvlSet U 1 ∧
      ∀ i, (T' 0 (f (E.toBase 1 (x + t • e)))).1 i = 0 →
        (T' 0 (f (E.toBase 1 x))).1 i = 0 ∧ ¬ 0 < (T' 0 (D x (E.toBase 1 e))).1 i := by
  set ι := E.toBase 1 with hι
  set γ : ℝ → E 1 := fun t => x + t • e with hγ
  have hev := eventually_add_smul_mem_lvlSet_of_cone T hT hU hx he
  set s : Set ℝ := {t | γ t ∈ E.lvlSet U 1} with hs
  have hs0 : s ∈ 𝓝[≥] (0 : ℝ) := hev
  have hγ' : HasDerivAt γ e 0 := by
    simpa [hγ] using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x
  have hγ0 : γ 0 = x := by simp [hγ]
  have hcurve : HasDerivWithinAt ((f ∘ ι) ∘ γ) (D x (ι e)) (Ici 0) 0 := by
    have h1 : HasDerivWithinAt ((f ∘ ι) ∘ γ) (((D x).comp ι) e) s 0 := by
      have hfx : HasFDerivWithinAt (f ∘ ι) ((D x).comp ι) (E.lvlSet U 1) (γ 0) := by
        rw [hγ0]; exact hf.hasFDerivWithinAt x hx
      exact HasFDerivWithinAt.comp_hasDerivWithinAt (l := f ∘ ι) (f := γ)
        (t := E.lvlSet U 1) (s := s) (0 : ℝ) hfx hγ'.hasDerivWithinAt fun t ht => ht
    exact h1.mono_of_mem_nhdsWithin hs0
  have h00 : ((f ∘ ι) ∘ γ) 0 = f (ι x) := by
    simp only [Function.comp_apply, hγ0]
  let L : Fin n' → E' 0 →L[ℝ] ℝ := fun i => (ContinuousLinearMap.proj i).comp
    ((ContinuousLinearMap.fst ℝ (Fin n' → ℝ) (W' 0)).comp (T' 0 : E' 0 →L[ℝ] _))
  have hder : ∀ i, HasDerivWithinAt (fun t => L i (((f ∘ ι) ∘ γ) t)) (L i (D x (ι e))) (Ici 0) 0 :=
    fun i => (L i).hasFDerivAt.comp_hasDerivWithinAt (0 : ℝ) hcurve
  have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝[≥] 0 := nhdsWithin_mono _ Ioi_subset_Ici_self
  have hcoord : ∀ i, ∀ᶠ t in 𝓝[>] (0 : ℝ), (T' 0 (((f ∘ ι) ∘ γ) t)).1 i = 0 →
      (T' 0 (f (ι x))).1 i = 0 ∧ ¬ 0 < (T' 0 (D x (ι e))).1 i := by
    intro i
    by_cases hi : (T' 0 (f (ι x))).1 i = 0
    · by_cases hiS : 0 < (T' 0 (D x (ι e))).1 i
      · have h0 : (fun t => L i (((f ∘ ι) ∘ γ) t)) 0 = 0 := by
          change L i (((f ∘ ι) ∘ γ) 0) = 0
          rw [h00]; exact hi
        filter_upwards [eventually_pos_of_hasDerivWithinAt_Ici (hder i) h0 hiS] with t ht h
        exact absurd h (ne_of_gt ht)
      · exact Eventually.of_forall fun t _ => ⟨hi, hiS⟩
    · have hc : ContinuousWithinAt (fun t => L i (((f ∘ ι) ∘ γ) t)) (Ici 0) 0 :=
        (hder i).continuousWithinAt
      have h0 : (fun t => L i (((f ∘ ι) ∘ γ) t)) 0 ≠ 0 := by
        change L i (((f ∘ ι) ∘ γ) 0) ≠ 0
        rw [h00]; exact hi
      have : ∀ᶠ t in 𝓝[≥] (0 : ℝ), L i (((f ∘ ι) ∘ γ) t) ≠ 0 :=
        hc.eventually (isOpen_ne.mem_nhds h0)
      filter_upwards [hle this] with t ht h
      exact absurd h ht
  filter_upwards [hle hev, eventually_all.2 hcoord] with t ht1 ht2
  exact ⟨ht1, ht2⟩

/-- Counting vanishing quadrant coordinates: if every coordinate vanishing at `q` vanishes at `p`
and lies outside `S`, and the coordinates in `S` vanish at `p`, then
`d(q) + #S ≤ d(p)`. -/
lemma degIndexWith_add_card_le_of_zeroCoord
    (T' : ScIso E' ((ScBanach.const (Fin n' → ℝ)).prod W')) {q p : E' 0} (S : Finset (Fin n'))
    (h : ∀ i, (T' 0 q).1 i = 0 → (T' 0 p).1 i = 0 ∧ i ∉ S)
    (hS : ∀ i ∈ S, (T' 0 p).1 i = 0) :
    degIndexWith T' q + S.card ≤ degIndexWith T' p := by
  classical
  set Zq : Finset (Fin n') := Finset.univ.filter fun i => (T' 0 q).1 i = 0 with hZq
  set Z : Finset (Fin n') := Finset.univ.filter fun i => (T' 0 p).1 i = 0 with hZ
  have hdisj : Disjoint Zq S := by
    rw [Finset.disjoint_left]
    intro i hi hiS
    simp only [hZq, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact (h i hi).2 hiS
  have hsub : Zq ∪ S ⊆ Z := by
    intro i hi
    simp only [hZ, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases Finset.mem_union.1 hi with hi | hi
    · simp only [hZq, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact (h i hi).1
    · exact hS i hi
  have hcard : Zq.card + S.card ≤ Z.card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card hsub
  exact hcard

end Curve

namespace ScRetraction.IsDiffeoGerm

variable {E E' : ScBanach} {n n' : ℕ} {W W' : ScBanach} {C : Set (E 0)} {C' : Set (E' 0)}
  {R : ScRetraction E C} {R' : ScRetraction E' C'} {F : E 0 → E' 0} {G : E' 0 → E 0}

/-- Along a germ of sc-diffeomorphisms `F : (O, x) → (O', y)`: let `j : V → E` be linear, `A` a
subspace of `V` mapped into `T_xO` whose vectors are dominated in `C_x` by multiples of one
`e₀ ∈ C_x`, and `B` the preimage in `A` of `T^R_xO`.  Then `dim(A / (A ∩ B))` is at most the number
of coordinates vanishing at `y` in which `D(F ∘ r)(x)e₀` is positive (Proposition 2.4.10 and the
one-sided sign argument). -/
theorem quotDim_le_card_of_dominated (h : R.IsDiffeoGerm R' F G)
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (hT : C = T 0 ⁻¹' quadrant n W 0)
    (T' : ScIso E' ((ScBanach.const (Fin n' → ℝ)).prod W')) (hT' : C' = T' 0 ⁻¹' quadrant n' W' 0)
    {x : E 1} (hx : x ∈ E.lvlSet R.retract 1)
    {V : Type*} [AddCommGroup V] [Module ℝ V] (j : V →ₗ[ℝ] E 0) (A B : Submodule ℝ V)
    (hjA : ∀ m ∈ A, j m ∈ LinearMap.range (scDeriv R.U R x : E 0 →ₗ[ℝ] E 0))
    (hjB : ∀ m ∈ A, (j m ∈ reducedTangentSpaceWith R T x ↔ m ∈ B))
    {e₀ : E 0} (he₀ : e₀ ∈ partialQuadrantAtWith T (E.toBase 1 x))
    (hdom : ∀ m ∈ A, ∃ c : ℝ, c • e₀ + j m ∈ partialQuadrantAtWith T (E.toBase 1 x) ∧
      c • e₀ - j m ∈ partialQuadrantAtWith T (E.toBase 1 x))
    (S : Finset (Fin n'))
    (hS : ∀ i, i ∈ S ↔ (T' 0 (F (E.toBase 1 x))).1 i = 0 ∧
      0 < (T' 0 (scDeriv R.U (F ∘ R) x e₀)).1 i) :
    quotDim A B ≤ S.card := by
  set y : E' 1 := levelMap (F ∘ R) 1 x with hy
  have hy' : y ∈ E'.lvlSet R'.retract 1 := h.image_mem hx
  have hιy : E'.toBase 1 y = F (E.toBase 1 x) := h.toBase_image hx
  set D : E 0 →L[ℝ] E' 0 := scDeriv R.U (F ∘ R) x with hD
  set D' : E' 0 →L[ℝ] E 0 := scDeriv R'.U (G ∘ R') y with hD'
  set P : E 0 →L[ℝ] E 0 := scDeriv R.U R x with hP
  have hD'D : ∀ v, D' (D v) = P v := h.deriv_inv_deriv hx
  have hPP : ∀ v, P (P v) = P v := fun v =>
    congrArg (fun L : E 0 →L[ℝ] E 0 => L v) (R.scDeriv_comp_self hx)
  have hpos : MapsTo D (partialQuadrantAtWith T (E.toBase 1 x))
      (partialQuadrantAtWith T' (F (E.toBase 1 x))) := h.deriv_mapsTo_partialQuadrant hx T hT T' hT'
  have hfwd : (reducedTangentSpaceWith R T x).map (D : E 0 →ₗ[ℝ] E' 0) =
      reducedTangentSpaceWith R' T' y := proposition_2_4_10_reduced h hx T hT T' hT'
  have hbwd : (reducedTangentSpaceWith R' T' y).map (D' : E' 0 →ₗ[ℝ] E 0) =
      reducedTangentSpaceWith R T x := by
    have := proposition_2_4_10_reduced h.symm hy' T' hT' T hT
    rwa [h.image_image hx] at this
  -- vectors of `A` vanish in the coordinates `i ∈ I(y) \ S`
  have hzero : ∀ m ∈ A, ∀ i, (T' 0 (F (E.toBase 1 x))).1 i = 0 → i ∉ S →
      (T' 0 (D (j m))).1 i = 0 := by
    intro m hm i hi hiS
    have hwi : (T' 0 (D e₀)).1 i = 0 := by
      have h1 : 0 ≤ (T' 0 (D e₀)).1 i := hpos he₀ i hi
      have h2 : ¬ 0 < (T' 0 (D e₀)).1 i := fun h' => hiS ((hS i).2 ⟨hi, h'⟩)
      exact le_antisymm (not_lt.1 h2) h1
    obtain ⟨c, hplus, hminus⟩ := hdom m hm
    have h1 := hpos hplus i hi
    have h2 := hpos hminus i hi
    simp only [map_add, map_sub, map_smul, Prod.fst_add, Prod.fst_sub, Prod.smul_fst,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hwi, mul_zero, zero_add,
      zero_sub] at h1 h2
    exact le_antisymm (neg_nonneg.1 h2) h1
  let Ψ : A →ₗ[ℝ] (S → ℝ) :=
    { toFun := fun w i => (T' 0 (D (j w.1))).1 i.1
      map_add' := fun a b => by funext i; simp
      map_smul' := fun a b => by funext i; simp }
  have hker : LinearMap.ker Ψ = B.comap A.subtype := by
    ext ⟨m, hm⟩
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · intro hΨ
      have hmin : D (j m) ∈ minimalSubspaceWith T' (E'.toBase 1 y) := by
        rw [hιy]
        refine (mem_minimalSubspaceWith T').2 fun i hi => ?_
        by_cases hiS : i ∈ S
        · exact congrFun hΨ ⟨i, hiS⟩
        · exact hzero m hm i hi hiS
      have hrange : D (j m) ∈ LinearMap.range (scDeriv R'.U R' y : E' 0 →ₗ[ℝ] E' 0) := by
        obtain ⟨m', hm'⟩ := hjA m hm
        obtain ⟨u, hu⟩ := h.deriv_mem_range hx (v := j m) ⟨m', hm'⟩
        exact ⟨u, hu⟩
      have hred : D (j m) ∈ reducedTangentSpaceWith R' T' y := ⟨hrange, hmin⟩
      have h1 : D' (D (j m)) ∈ reducedTangentSpaceWith R T x :=
        hbwd ▸ Submodule.mem_map_of_mem hred
      obtain ⟨m', hm'⟩ := hjA m hm
      have h2 : D' (D (j m)) = j m := by
        rw [hD'D]
        have : P m' = j m := hm'
        rw [← this]; exact hPP m'
      rw [h2] at h1
      exact (hjB m hm).1 h1
    · intro hmB
      have h1 : j m ∈ reducedTangentSpaceWith R T x := (hjB m hm).2 hmB
      have h2 : D (j m) ∈ reducedTangentSpaceWith R' T' y :=
        hfwd ▸ Submodule.mem_map_of_mem h1
      have h3 : D (j m) ∈ minimalSubspaceWith T' (E'.toBase 1 y) := h2.2
      rw [hιy] at h3
      funext i
      exact (mem_minimalSubspaceWith T').1 h3 i.1 ((hS i.1).1 i.2).1
  have hemb : (A ⧸ B.comap A.subtype) ≃ₗ[ℝ] LinearMap.range Ψ := hker ▸ Ψ.quotKerEquivRange
  rw [quotDim, hemb.finrank_eq]
  refine (Submodule.finrank_le _).trans ?_
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]

end ScRetraction.IsDiffeoGerm

namespace MPolyfold

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : MPolyfold X} {Q : MPolyfold Y}

/-- **The product formula at a level-`1` point `x` and a point `y` attaining the bound of Theorem
2.4.12** (Definition 2.4.1, p. 54; Theorem 2.4.12, p. 63):
`d_{X × Y}(x, y) = d_X(x) + d_Y(y)`.  No tameness, and no condition on the charts of `X`. -/
theorem degIndex_prod_of_mem_levelSet_of_isDegSharpAt [ParacompactSpace (X × Y)] {x : X} {y : Y}
    (hx : x ∈ P.levelSet 1) (hy : Q.IsDegSharpAt y) :
    (P.prod Q).degIndex (x, y) = P.degIndex x + Q.degIndex y := by
  classical
  obtain ⟨ψ, hψ, hyψ, R', hR', n', W', T', hT', z', hz', hdy⟩ := hy
  obtain ⟨φ, hφ, hxφ⟩ := P.exists_isChart_mem_source x
  obtain ⟨z, hz⟩ := (P.mem_levelSet_iff hφ hxφ).1 hx
  obtain ⟨R, hR⟩ := φ.model.isScRetract
  obtain ⟨n, W, T, hT⟩ := φ.model.isPartialQuadrant
  obtain ⟨χ, hχ, hxyχ, hd⟩ := (P.prod Q).exists_isChart_degIndex_eq (x, y)
  obtain ⟨Rχ, hRχ⟩ := χ.model.isScRetract
  obtain ⟨nχ, Wχ, Tχ, hTχ⟩ := χ.model.isPartialQuadrant
  have hπ : (P.prod Q).IsChart (φ.prod ψ) := hφ.prod hψ
  have hTπ := prod_eq_prodPresentation T T' hT hT'
  have hret : (R.prod R').retract = (φ.prod ψ).model.O := by
    rw [R.prod_retract, hR, hR']; rfl
  obtain ⟨W₀, hW₀, hW₀eq⟩ := (φ.prod ψ).exists_isOpen_image_eq
    (s := (φ.prod ψ).source ∩ χ.source) inter_subset_left
    ((φ.prod ψ).isOpen_source.inter χ.isOpen_source)
  obtain ⟨W₀', hW₀', hW₀'eq⟩ := χ.exists_isOpen_image_eq
    (s := χ.source ∩ (φ.prod ψ).source) inter_subset_left
    (χ.isOpen_source.inter (φ.prod ψ).isOpen_source)
  have germ := (hπ.compatible hχ (P := P.prod Q)).isDiffeoGerm (R.prod R') hret Rχ hRχ hW₀ hW₀eq
    hW₀' hW₀'eq
  set Rπ : ScRetraction (φ.prod ψ).model.E (φ.prod ψ).model.C :=
    (R.prod R').restrict hW₀ with hRπ
  set F := (φ.prod ψ).transition χ with hF
  let Tπ : ScIso (φ.prod ψ).model.E ((ScBanach.const (Fin (n + n') → ℝ)).prod (W.prod W')) :=
    prodPresentation T T'
  have hTπ : (φ.prod ψ).model.C = Tπ 0 ⁻¹' quadrant (n + n') (W.prod W') 0 :=
    prod_eq_prodPresentation T T' hT hT'
  have hRπret : Rπ.retract = (φ.prod ψ).overlap χ :=
    (ScRetraction.restrict_retract (R.prod R') hW₀).trans
      ((congrArg (fun s => s ∩ W₀) hret).trans hW₀eq.symm)
  let zz : (φ.prod ψ).model.E 1 := ((z, z') : (φ.model.E.prod ψ.model.E) 1)
  have hzz0 : (φ.prod ψ).model.E.toBase 1 zz = (φ.prod ψ) (x, y) := by
    show (φ.model.E.prod ψ.model.E).toBase 1 ((z, z') : (φ.model.E.prod ψ.model.E) 1) = _
    rw [ScBanach.prod_toBase, hz, hz']; rfl
  have hzzO : zz ∈ (φ.prod ψ).model.E.lvlSet Rπ.retract 1 := by
    show (φ.prod ψ).model.E.toBase 1 zz ∈ Rπ.retract
    rw [hzz0, hRπret]
    exact (φ.prod ψ).mem_overlap χ ⟨hxφ, hyψ⟩ hxyχ
  have hzzU : zz ∈ (φ.prod ψ).model.E.lvlSet Rπ.U 1 := Rπ.lvlSet_retract_subset 1 hzzO
  have hzzU' : ((z, z') : (φ.model.E.prod ψ.model.E) 1) ∈
      (φ.model.E.prod ψ.model.E).lvlSet (R.U ×ˢ R'.U) 1 := hzzU.1
  have hFzz' : F ((φ.prod ψ).model.E.toBase 1 zz) = χ (x, y) := by
    rw [hzz0, hF, (φ.prod ψ).transition_apply χ ⟨hxφ, hyψ⟩]
  have hFzz : (F ∘ Rπ) ((φ.prod ψ).model.E.toBase 1 zz) = χ (x, y) := by
    show F (Rπ ((φ.prod ψ).model.E.toBase 1 zz)) = χ (x, y)
    rw [Rπ.apply_eq_self_of_mem_retract hzzO, hFzz']
  -- the vector `u` of `E'` with all quadrant coordinates `1`, and `e = (0, u)`
  let u : ψ.model.E 1 := (T' 1).symm ((fun _ => 1, 0) : ((ScBanach.const (Fin n' → ℝ)).prod W') 1)
  have hu : ∀ i, (T' 0 (ψ.model.E.toBase 1 u)).1 i = 1 := by
    intro i
    have h1 : T' 0 (ψ.model.E.toBase 1 u) =
        ((ScBanach.const (Fin n' → ℝ)).prod W').toBase 1 (T' 1 u) := (T'.toBase_comm 1 u).symm
    rw [h1]
    simp only [u, ContinuousLinearEquiv.apply_symm_apply]
    rfl
  let e : (φ.prod ψ).model.E 1 := ((0, u) : (φ.model.E.prod ψ.model.E) 1)
  have he0 : (φ.prod ψ).model.E.toBase 1 e =
      ((0, ψ.model.E.toBase 1 u) : (φ.model.E.prod ψ.model.E) 0) := by
    show (φ.model.E.prod ψ.model.E).toBase 1 ((0, u) : (φ.model.E.prod ψ.model.E) 1) = _
    rw [ScBanach.prod_toBase]
    exact Prod.ext (map_zero _) rfl
  have hzz2 : ((φ.model.E.prod ψ.model.E).toBase 1 ((z, z') : (φ.model.E.prod ψ.model.E) 1)).2 =
      ψ.model.E.toBase 1 z' := by
    rw [ScBanach.prod_toBase]
  have hcone : ∀ m : ψ.model.E 0,
      (∀ j, (T' 0 (ψ.model.E.toBase 1 z')).1 j = 0 → 0 ≤ (T' 0 m).1 j) →
      ((0, m) : (φ.model.E.prod ψ.model.E) 0) ∈
        partialQuadrantAtWith Tπ ((φ.prod ψ).model.E.toBase 1 zz) := by
    intro m hm l
    refine Fin.addCases (fun i => ?_) (fun j => ?_) l
    · intro _
      have h1 := prodPresentation_castAdd T T' ((0, m) : (φ.model.E.prod ψ.model.E) 0) i
      have h0 : (T 0 ((0, m) : (φ.model.E.prod ψ.model.E) 0).1).1 i = 0 := by
        show (T 0 (0 : φ.model.E 0)).1 i = 0
        simp
      exact le_of_eq (h1.trans h0).symm
    · intro hj
      have h1 := prodPresentation_natAdd T T' ((0, m) : (φ.model.E.prod ψ.model.E) 0) j
      have h2 := prodPresentation_natAdd T T'
        ((φ.model.E.prod ψ.model.E).toBase 1 ((z, z') : (φ.model.E.prod ψ.model.E) 1)) j
      rw [hzz2] at h2
      exact (hm j (h2.symm.trans hj)).trans_eq h1.symm
  have hecone : (φ.prod ψ).model.E.toBase 1 e ∈
      partialQuadrantAtWith Tπ ((φ.prod ψ).model.E.toBase 1 zz) := by
    rw [he0]
    exact hcone _ fun j _ => by rw [hu]; exact zero_le_one
  set D := scDeriv Rπ.U (F ∘ Rπ) zz with hD
  set S : Finset (Fin nχ) := Finset.univ.filter fun i =>
    (Tχ 0 (F ((φ.prod ψ).model.E.toBase 1 zz))).1 i = 0 ∧
      0 < (Tχ 0 (D ((φ.prod ψ).model.E.toBase 1 e))).1 i with hSdef
  -- `d_Y(y) ≤ dim(T_yO' / T^R_yO') ≤ #S`
  have hDπ : ∀ m' : ψ.model.E 0, scDeriv Rπ.U Rπ zz ((0, m') : (φ.model.E.prod ψ.model.E) 0) =
      ((0, scDeriv R'.U R' z' m') : (φ.model.E.prod ψ.model.E) 0) := by
    intro m'
    have h1 := (R.prod R').scDeriv_restrict hW₀ hzzU
    have h2 := scDeriv_prodMap R.relOpen R'.relOpen R.isScSmooth R'.isScSmooth hzzU'
    have h3 := congrArg (fun L : (φ.model.E.prod ψ.model.E) 0 →L[ℝ] (φ.model.E.prod ψ.model.E) 0 =>
      L ((0, m') : (φ.model.E.prod ψ.model.E) 0)) (h1.trans h2)
    refine h3.trans (Prod.ext ?_ rfl)
    show scDeriv R.U R z (0 : φ.model.E 0) = 0
    exact map_zero _
  have hrange : LinearMap.range (scDeriv (R.prod R').U (R.prod R')
        ((z, z') : (φ.model.E.prod ψ.model.E) 1) :
        (φ.model.E.prod ψ.model.E) 0 →ₗ[ℝ] (φ.model.E.prod ψ.model.E) 0) =
      (LinearMap.range (scDeriv R.U R z : φ.model.E 0 →ₗ[ℝ] φ.model.E 0)).prod
        (LinearMap.range (scDeriv R'.U R' z' : ψ.model.E 0 →ₗ[ℝ] ψ.model.E 0)) := by
    change LinearMap.range (scDeriv (E := φ.model.E.prod ψ.model.E)
      (F := φ.model.E.prod ψ.model.E) (R.U ×ˢ R'.U) (Prod.map R R')
        ((z, z') : (φ.model.E.prod ψ.model.E) 1) :
        (φ.model.E.prod ψ.model.E) 0 →ₗ[ℝ] (φ.model.E.prod ψ.model.E) 0) = _
    rw [scDeriv_prodMap R.relOpen R'.relOpen R.isScSmooth R'.isScSmooth hzzU',
      ContinuousLinearMap.coe_prodMap, LinearMap.range_prodMap]
  have hredp : reducedTangentSpaceWith (R.prod R') (prodPresentation T T')
      ((z, z') : (φ.model.E.prod ψ.model.E) 1) =
      (reducedTangentSpaceWith R T z).prod (reducedTangentSpaceWith R' T' z') := by
    rw [reducedTangentSpaceWith, hrange, ScBanach.prod_toBase,
      minimalSubspaceWith_prodPresentation, Submodule.prod_inf_prod]
    rfl
  have hred : ∀ m : ψ.model.E 0, ((0, m) : (φ.model.E.prod ψ.model.E) 0) ∈
      reducedTangentSpaceWith Rπ Tπ zz ↔ m ∈ reducedTangentSpaceWith R' T' z' := by
    intro m
    have h1 := reducedTangentSpaceWith_restrict (R.prod R') hW₀ (prodPresentation T T') hzzU
    have h2 := SetLike.ext_iff.1 (h1.trans hredp) ((0, m) : (φ.model.E.prod ψ.model.E) 0)
    exact h2.trans ⟨fun h => (Submodule.mem_prod.1 h).2,
      fun h => Submodule.mem_prod.2 ⟨Submodule.zero_mem _, h⟩⟩
  let j : ψ.model.E 0 →ₗ[ℝ] (φ.prod ψ).model.E 0 :=
    LinearMap.inr ℝ (φ.model.E 0) (ψ.model.E 0)
  have hj : ∀ m, j m = ((0, m) : (φ.model.E.prod ψ.model.E) 0) := fun _ => rfl
  have hk : quotDim (LinearMap.range (scDeriv R'.U R' z' : ψ.model.E 0 →ₗ[ℝ] ψ.model.E 0))
      (reducedTangentSpaceWith R' T' z') ≤ S.card := by
    refine germ.quotDim_le_card_of_dominated Tπ hTπ Tχ hTχ hzzO j _ _ ?_ ?_ hecone ?_ S ?_
    · rintro m ⟨m', rfl⟩
      exact ⟨((0, m') : (φ.model.E.prod ψ.model.E) 0), hDπ m'⟩
    · intro m _
      exact hred m
    · intro m _
      set c := ‖(T' 0 m).1‖ with hc
      have hcj : ∀ k, |(T' 0 m).1 k| ≤ c := fun k => by
        have := norm_le_pi_norm (T' 0 m).1 k
        rwa [Real.norm_eq_abs] at this
      refine ⟨c, ?_, ?_⟩
      · have : c • (φ.prod ψ).model.E.toBase 1 e + j m =
            ((0, c • ψ.model.E.toBase 1 u + m) : (φ.model.E.prod ψ.model.E) 0) := by
          rw [he0]
          refine Prod.ext ?_ rfl
          show c • (0 : φ.model.E 0) + 0 = 0
          simp
        rw [this]
        refine hcone _ fun k _ => ?_
        simp only [map_add, map_smul, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul, hu, mul_one]
        have := neg_abs_le ((T' 0 m).1 k)
        have := hcj k
        linarith
      · have : c • (φ.prod ψ).model.E.toBase 1 e - j m =
            ((0, c • ψ.model.E.toBase 1 u - m) : (φ.model.E.prod ψ.model.E) 0) := by
          rw [he0]
          refine Prod.ext ?_ rfl
          show c • (0 : φ.model.E 0) - 0 = 0
          simp
        rw [this]
        refine hcone _ fun k _ => ?_
        simp only [map_sub, map_smul, Prod.fst_sub, Prod.smul_fst, Pi.sub_apply, Pi.smul_apply,
          smul_eq_mul, hu, mul_one]
        have := le_abs_self ((T' 0 m).1 k)
        have := hcj k
        linarith
    · intro i
      simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and]
      rfl
  -- the curve `t ↦ χ(x, y_t)`
  have hf := germ.isSc1.isSc1With_scDeriv
  obtain ⟨t, htU, htc⟩ := (hf.eventually_zeroCoord_imp_along_cone Tπ hTπ Tχ Rπ.relOpen hzzU
    hecone).exists
  set c₀ := (φ.prod ψ).model.E.toBase 1 (zz + t • e) with hc₀
  have hc₀U : c₀ ∈ Rπ.U := htU
  obtain ⟨p, ⟨hpπ, hpχ⟩, hp⟩ : Rπ c₀ ∈ (φ.prod ψ).overlap χ := hRπret ▸ Rπ.apply_mem_retract hc₀U
  have hc₀1 : c₀.1 = φ x := by
    have h1 : c₀ = (φ.prod ψ).model.E.toBase 1 zz +
        t • (φ.prod ψ).model.E.toBase 1 e := by
      rw [hc₀, map_add, map_smul]
    rw [h1, hzz0, he0]
    change φ x + t • (0 : φ.model.E 0) = φ x
    rw [smul_zero, add_zero]
  have hp1 : p.1 = x := by
    have h1 : φ p.1 = φ x := by
      have h2 : ((φ.prod ψ) p).1 = (Rπ c₀).1 := congrArg Prod.fst hp
      have h3 : (Rπ c₀).1 = R c₀.1 := rfl
      have h4 : ((φ.prod ψ) p).1 = φ p.1 := rfl
      rw [h4, h3, hc₀1, R.apply_eq_self_of_mem_retract (hR ▸ φ.mapsTo_model x hxφ)] at h2
      exact h2
    rw [← φ.symm_apply_apply hpπ.1, h1, φ.symm_apply_apply hxφ]
  have hq : (F ∘ Rπ) c₀ = χ p := by
    show F (Rπ c₀) = χ p
    rw [← hp, hF, (φ.prod ψ).transition_apply χ hpπ]
  have hpeq : p = (x, p.2) := Prod.ext hp1 rfl
  have hXle : P.degIndex x ≤ chartDegIndex χ p := by
    have h1 := P.degIndex_le_degIndex_prod_left Q x p.2
    have h2 := (P.prod Q).degIndex_le hχ hpχ
    rw [hpeq] at h2 ⊢
    exact h1.trans h2
  have e1 : chartDegIndex χ p = degIndexWith Tχ ((F ∘ Rπ) c₀) := by
    rw [chartDegIndex, degIndex_eq Tχ hTχ (χ.apply_mem_C hpχ), hq]
  have e2 : chartDegIndex χ (x, y) = degIndexWith Tχ (χ (x, y)) := by
    rw [chartDegIndex, degIndex_eq Tχ hTχ (χ.apply_mem_C hxyχ)]
  have hcount : degIndexWith Tχ ((F ∘ Rπ) c₀) + S.card ≤ degIndexWith Tχ (χ (x, y)) := by
    refine degIndexWith_add_card_le_of_zeroCoord Tχ S (fun i hi => ?_) (fun i hi => ?_)
    · obtain ⟨h1, h2⟩ := htc i hi
      refine ⟨(congrArg (fun v => (Tχ 0 v).1 i) hFzz).symm.trans h1, fun hiS => h2 ?_⟩
      simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and] at hiS
      exact hiS.2
    · simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [← hFzz']; exact hi.1
  refine le_antisymm (P.degIndex_prod_le Q x y) ?_
  rw [hd, e2]
  rw [e1] at hXle
  have := hdy.trans hk
  omega

/-! ### The symmetry `X × Y ≅ Y × X` -/

/-- `X × Y → Y × X` is an sc-diffeomorphism. -/
theorem isScDiffeoOn_prodSwap [ParacompactSpace (X × Y)] [ParacompactSpace (Y × X)] :
    (P.prod Q).IsScDiffeoOn (Q.prod P) Prod.swap Prod.swap univ univ where
  isScSmoothOn := IsScSmoothOn.prodMk (isScSmoothMap_snd (P := P) (Q := Q))
    (isScSmoothMap_fst (P := P) (Q := Q))
  isScSmoothOn_inv := IsScSmoothOn.prodMk (isScSmoothMap_snd (P := Q) (Q := P))
    (isScSmoothMap_fst (P := Q) (Q := P))
  mapsTo := mapsTo_univ _ _
  mapsTo_inv := mapsTo_univ _ _
  left_inv _ _ := rfl
  right_inv _ _ := rfl

/-- `d_{X × Y}(x, y) = d_{Y × X}(y, x)` (Proposition 2.4.4). -/
theorem degIndex_prod_swap [ParacompactSpace (X × Y)] [ParacompactSpace (Y × X)] (x : X) (y : Y) :
    (P.prod Q).degIndex (x, y) = (Q.prod P).degIndex (y, x) :=
  proposition_2_4_4 (isScDiffeoOn_prodSwap (P := P) (Q := Q)) (mem_univ (x, y))

/-- **The product formula at a point `x` attaining the bound of Theorem 2.4.12 and a level-`1`
point `y`.** -/
theorem degIndex_prod_of_isDegSharpAt_of_mem_levelSet [ParacompactSpace (X × Y)] {x : X} {y : Y}
    (hx : P.IsDegSharpAt x) (hy : y ∈ Q.levelSet 1) :
    (P.prod Q).degIndex (x, y) = P.degIndex x + Q.degIndex y := by
  have := paracompactSpace_prod Q P
  rw [degIndex_prod_swap (P := P) (Q := Q) x y, degIndex_prod_of_mem_levelSet_of_isDegSharpAt hy hx,
    add_comm]

variable (P) in
/-- **The product formula at an arbitrary point `x` and a point `y` attaining the bound of Theorem
2.4.12**, when `d_X(x)` is attained at level-`1` points arbitrarily close to `x`. -/
theorem degIndex_prod_of_frequently_levelSet_of_isDegSharpAt [ParacompactSpace (X × Y)] {x : X}
    {y : Y} (hx : ∃ᶠ x' in 𝓝 x, x' ∈ P.levelSet 1 ∧ P.degIndex x ≤ P.degIndex x')
    (hy : Q.IsDegSharpAt y) :
    (P.prod Q).degIndex (x, y) = P.degIndex x + Q.degIndex y := by
  have hev : ∀ᶠ x' in 𝓝 x, (P.prod Q).degIndex (x', y) ≤ (P.prod Q).degIndex (x, y) :=
    (Continuous.prodMk_left y).continuousAt.eventually (lemma_2_4_3 (P.prod Q) (x, y))
  obtain ⟨x', ⟨hx's, hx'd⟩, hle⟩ := (hx.and_eventually hev).exists
  refine le_antisymm (P.degIndex_prod_le Q x y) ?_
  rw [degIndex_prod_of_mem_levelSet_of_isDegSharpAt hx's hy] at hle
  omega

end MPolyfold

/-! ### The remark after Definition 8.5.1 (comparison item V8.28) -/

section Fibres

universe u v

variable {ObjY MorY : Type u} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  {ObjX MorX : Type v} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {Y : EpGroupoid ObjY MorY} {X : EpGroupoid ObjX MorX} {F : EpFunctor Y X}

/-- **The degeneracy remark after Definition 8.5.1 (p. 383)** (comparison item V8.28) for a proper
covering `F`, at a morphism `φ` with `F(φ)` on level `1` of `𝐗` and the bound of Theorem 2.4.12
attained at `s(φ) ∈ Y`: `d_{𝐗 × Y}(F(φ), s(φ)) = 2 · d_𝐘(φ)` and
`2 · d_{𝐗 ₛ×_F Y}(F(φ), s(φ)) = d_{𝐗 × Y}(F(φ), s(φ))`. -/
theorem EpFunctor.IsProperCovering.degIndex_prod_fibredMap_of_mem_levelSet
    (hF : F.IsProperCovering) (φ : MorY) (h1 : F.mor φ ∈ X.PMor.levelSet 1)
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
    rw [MPolyfold.degIndex_prod_of_mem_levelSet_of_isDegSharpAt h1 h2, hF.degIndex_mor,
      ← Y.degIndex_src]
    ring
  exact ⟨h, by rw [h, ← hF.degIndex_fibredMap]⟩

end Fibres

end Polyfold

#print axioms Polyfold.IsSc1With.eventually_zeroCoord_imp_along_cone
#print axioms Polyfold.ScRetraction.IsDiffeoGerm.quotDim_le_card_of_dominated
#print axioms Polyfold.MPolyfold.degIndex_prod_of_mem_levelSet_of_isDegSharpAt
#print axioms Polyfold.MPolyfold.degIndex_prod_of_isDegSharpAt_of_mem_levelSet
#print axioms Polyfold.MPolyfold.degIndex_prod_swap
#print axioms Polyfold.MPolyfold.degIndex_prod_of_frequently_levelSet_of_isDegSharpAt
#print axioms Polyfold.EpFunctor.IsProperCovering.degIndex_prod_fibredMap_of_mem_levelSet
