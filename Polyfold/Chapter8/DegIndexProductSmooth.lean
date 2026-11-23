import Polyfold.Chapter8.DegIndexProductGeneral

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Definition 2.4.1 (p. 54),
Theorem 2.4.12 (p. 63), and §8.5, after Definition 8.5.1 (p. 383) (comparison item V8.28).

# The product formula at a smooth point and a point attaining the bound of Theorem 2.4.12

* `ScRetraction.exists_degIndexWith_add_quotDim_le`: in a retract `(O, C, E)` with retraction `r`
  and `x ∈ O₁`, every neighbourhood of `x` contains a point `q ∈ O` with
  `d_C(q) + dim(T_xO / T^R_xO) ≤ d_C(x)`.  The point is `q = r(x + t u)` for the vector `u` with all
  quadrant coordinates `1` and small `t > 0`: `Dr(x)` preserves the partial quadrant `C_x`
  (Lemma 2.4.9), every `w ∈ T_xO` is dominated by a multiple of `v = Dr(x)u` in the coordinates
  vanishing at `x`, so `T_xO / T^R_xO` lives on the coordinates with `v_i > 0`, and these become
  positive along the curve.
* `ScRetraction.IsDiffeoGerm.quotDim_le_quotDim`: `dim(T_xO / T^R_xO)` does not decrease along a
  germ of sc-diffeomorphisms (Proposition 2.4.10).
* `MPolyfold.exists_chartDegIndex_add_le`: if the bound of Theorem 2.4.12 is attained at `y`, then
  in **every** chart `ψ` around `y`, every neighbourhood of `y` contains `y'` with
  `d_{C}(ψ(y')) + d_Y(y) ≤ d_C(ψ(y))`.
* **`MPolyfold.degIndex_prod_of_mem_smoothSet_of_isDegSharpAt`**,
  **`MPolyfold.degIndex_prod_of_isDegSharpAt_of_mem_smoothSet`**: `d_{X × Y}(x, y) = d_X(x) +
  d_Y(y)` if one of the two points is smooth and the bound of Theorem 2.4.12 is attained at the
  other one.  (`MPolyfold.degIndex_prod_of_isDegSharpAt` asks for the bound at both points.)
* `MPolyfold.degIndex_prod_of_mem_smoothSet_of_isTame`: `X` arbitrary, `x` smooth, `Y` tame,
  `y` smooth (for instance `Y = [0, ∞)`, `y = 0`).
* `MPolyfold.degIndex_prod_of_frequently`: the product formula at `(x, y)` follows from the
  inequality `d_X(x) + d_Y(y) ≤ d_{X × Y}(p)` at points `p` arbitrarily close to `(x, y)`
  (Lemma 2.4.3).
* `MPolyfold.degIndex_prod_of_frequently_smoothSet_of_isDegSharpAt`: the same for an arbitrary
  `x`, if `d_X(x)` is attained at smooth points arbitrarily close to `x`.
* V8.28: `EpFunctor.IsProperCovering.degIndex_prod_fibredMap_of_mem_smoothSet`.

## What is left

Whether `d_X(x)` is always attained at smooth points near `x`, and the product formula at pairs of
points at neither of which the bound of Theorem 2.4.12 is attained, are not settled here.
-/

open Set Filter Topology Function Module

noncomputable section

namespace Polyfold

/-! ### A one-sided derivative argument -/

/-- A function on `[0, ε)` with `g(0) = 0` and positive one-sided derivative at `0` is positive
for small `t > 0`. -/
lemma eventually_pos_of_hasDerivWithinAt_Ici {g : ℝ → ℝ} {c : ℝ}
    (hg : HasDerivWithinAt g c (Ici 0) 0) (h0 : g 0 = 0) (hc : 0 < c) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < g t := by
  have hslope := hasDerivWithinAt_iff_tendsto_slope.1 hg
  have hI : Ici (0 : ℝ) \ {0} = Ioi 0 := by
    ext t; simp
  rw [hI] at hslope
  filter_upwards [hslope.eventually (lt_mem_nhds hc), self_mem_nhdsWithin] with t ht ht0
  rw [slope_def_field, h0, sub_zero, sub_zero] at ht
  have ht0' : (0 : ℝ) < t := ht0
  have := mul_pos ht ht0'
  rwa [div_mul_cancel₀ _ (ne_of_gt ht0')] at this

/-! ### Retracts: the index drops by `dim(T_xO / T^R_xO)` near `x` -/

section Retract

variable {E : ScBanach} {C : Set (E 0)} {n : ℕ} {W : ScBanach}

/-- **The index drops by `dim(T_xO / T^R_xO)` at points of `O` near `x ∈ O₁`** (the mechanism of
Theorem 2.4.12, p. 63, read inside one chart). -/
theorem ScRetraction.exists_degIndexWith_add_quotDim_le (R : ScRetraction E C)
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (hT : C = T 0 ⁻¹' quadrant n W 0)
    {x : E 1} (hx : x ∈ E.lvlSet R.retract 1) {N : Set (E 0)} (hN : N ∈ 𝓝 (E.toBase 1 x)) :
    ∃ q ∈ R.retract ∩ N, degIndexWith T q +
      quotDim (LinearMap.range (scDeriv R.U R x : E 0 →ₗ[ℝ] E 0)) (reducedTangentSpaceWith R T x)
        ≤ degIndexWith T (E.toBase 1 x) := by
  classical
  set ι := E.toBase 1 with hι
  set P : E 0 →L[ℝ] E 0 := scDeriv R.U R x with hP
  have hxU : x ∈ E.lvlSet R.U 1 := R.lvlSet_retract_subset 1 hx
  have hRx : R (ι x) = ι x := R.apply_eq_self_of_mem_retract hx
  have hD := R.isSc1.isSc1With_scDeriv
  have hpos : MapsTo P (partialQuadrantAtWith T (ι x)) (partialQuadrantAtWith T (ι x)) := by
    have := hD.mapsTo_partialQuadrant T hT T hT R.relOpen
      (fun z hz => R.U_subset_C (R.mapsTo hz)) hxU
    rwa [hRx] at this
  have hPP : ∀ z, P (P z) = P z := fun z =>
    congrArg (fun L : E 0 →L[ℝ] E 0 => L z) (R.scDeriv_comp_self hx)
  -- the vector `u` with all quadrant coordinates `1`
  let u : E 1 := (T 1).symm ((fun _ => 1, 0) : ((ScBanach.const (Fin n → ℝ)).prod W) 1)
  have hu : ∀ i, (T 0 (ι u)).1 i = 1 := by
    intro i
    have h1 : T 0 (ι u) = ((ScBanach.const (Fin n → ℝ)).prod W).toBase 1 (T 1 u) :=
      (T.toBase_comm 1 u).symm
    rw [h1]
    simp only [u, ContinuousLinearEquiv.apply_symm_apply]
    rfl
  have hucone : ι u ∈ partialQuadrantAtWith T (ι x) := fun i _ => by rw [hu]; exact zero_le_one
  set v := P (ι u) with hv
  have hvcone : v ∈ partialQuadrantAtWith T (ι x) := hpos hucone
  set S : Finset (Fin n) :=
    Finset.univ.filter fun i => (T 0 (ι x)).1 i = 0 ∧ 0 < (T 0 v).1 i with hS
  set Z : Finset (Fin n) := Finset.univ.filter fun i => (T 0 (ι x)).1 i = 0 with hZ
  set A : Submodule ℝ (E 0) := LinearMap.range (P : E 0 →ₗ[ℝ] E 0) with hA
  -- every `w ∈ T_xO` vanishes in the coordinates `i ∈ I(x)` with `v_i = 0`
  have hdom : ∀ w ∈ A, ∀ i, (T 0 (ι x)).1 i = 0 → i ∉ S → (T 0 w).1 i = 0 := by
    rintro w ⟨w', rfl⟩ i hi hiS
    set w := P w' with hw
    have hvi : (T 0 v).1 i = 0 := by
      have h1 : 0 ≤ (T 0 v).1 i := hvcone i hi
      have h2 : ¬ 0 < (T 0 v).1 i := fun h => hiS (by simp [hS, hi, h])
      exact le_antisymm (not_lt.1 h2) h1
    set c := ‖(T 0 w).1‖ with hc
    have hcj : ∀ j, |(T 0 w).1 j| ≤ c := fun j => by
      have := norm_le_pi_norm (T 0 w).1 j
      rwa [Real.norm_eq_abs] at this
    have hplus : c • ι u + w ∈ partialQuadrantAtWith T (ι x) := fun j _ => by
      simp only [map_add, map_smul, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, hu, mul_one]
      have := neg_abs_le ((T 0 w).1 j)
      have := hcj j
      linarith
    have hminus : c • ι u - w ∈ partialQuadrantAtWith T (ι x) := fun j _ => by
      simp only [map_sub, map_smul, Prod.fst_sub, Prod.smul_fst, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul, hu, mul_one]
      have := le_abs_self ((T 0 w).1 j)
      have := hcj j
      linarith
    have h1 := hpos hplus i hi
    have h2 := hpos hminus i hi
    have hPw : P w = w := hPP w'
    rw [map_add, map_smul, hPw] at h1
    rw [map_sub, map_smul, hPw] at h2
    simp only [map_add, map_sub, map_smul, Prod.fst_add, Prod.fst_sub, Prod.smul_fst,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← hv, hvi, mul_zero, zero_add,
      zero_sub] at h1 h2
    exact le_antisymm (neg_nonneg.1 h2) h1
  -- hence `dim(T_xO / T^R_xO) ≤ #S`
  have hk : quotDim A (reducedTangentSpaceWith R T x) ≤ S.card := by
    let Ψ : A →ₗ[ℝ] (S → ℝ) :=
      { toFun := fun w i => (T 0 w.1).1 i.1
        map_add' := fun a b => by funext i; simp
        map_smul' := fun a b => by funext i; simp }
    have hker : LinearMap.ker Ψ = (reducedTangentSpaceWith R T x).comap A.subtype := by
      ext ⟨w, hw⟩
      simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply,
        reducedTangentSpaceWith, Submodule.mem_inf]
      constructor
      · intro h
        refine ⟨hw, (mem_minimalSubspaceWith T).2 fun i hi => ?_⟩
        by_cases hiS : i ∈ S
        · exact congrFun h ⟨i, hiS⟩
        · exact hdom w hw i hi hiS
      · rintro ⟨-, h⟩
        funext i
        have hi : (T 0 (ι x)).1 i.1 = 0 := by
          have := i.2; simp only [hS, Finset.mem_filter] at this; exact this.2.1
        exact (mem_minimalSubspaceWith T).1 h i.1 hi
    have hemb : (A ⧸ (reducedTangentSpaceWith R T x).comap A.subtype) ≃ₗ[ℝ] LinearMap.range Ψ :=
      hker ▸ Ψ.quotKerEquivRange
    rw [quotDim, hemb.finrank_eq]
    refine (Submodule.finrank_le _).trans ?_
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  -- the curve `t ↦ r(x + t u)`
  set γ : ℝ → E 1 := fun t => x + t • u with hγ
  have hev := eventually_add_smul_mem_lvlSet_of_cone T hT R.relOpen hxU hucone
  set s : Set ℝ := {t | γ t ∈ E.lvlSet R.U 1} with hs
  have hs0 : s ∈ 𝓝[≥] (0 : ℝ) := hev
  have hγ' : HasDerivAt γ u 0 := by
    simpa [hγ] using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add x
  have hγ0 : γ 0 = x := by simp [hγ]
  have hcurve : HasDerivWithinAt ((R ∘ ι) ∘ γ) v (Ici 0) 0 := by
    have h1 : HasDerivWithinAt ((R ∘ ι) ∘ γ) ((P.comp ι) u) s 0 := by
      have hfx : HasFDerivWithinAt (R ∘ ι) (P.comp ι) (E.lvlSet R.U 1) (γ 0) := by
        rw [hγ0]; exact hD.hasFDerivWithinAt x hxU
      exact HasFDerivWithinAt.comp_hasDerivWithinAt (l := R ∘ ι) (f := γ)
        (t := E.lvlSet R.U 1) (s := s) (0 : ℝ) hfx hγ'.hasDerivWithinAt fun t ht => ht
    exact h1.mono_of_mem_nhdsWithin hs0
  have h00 : ((R ∘ ι) ∘ γ) 0 = ι x := by
    simp only [Function.comp_apply, hγ0, hRx]
  let L : Fin n → E 0 →L[ℝ] ℝ := fun i => (ContinuousLinearMap.proj i).comp
    ((ContinuousLinearMap.fst ℝ (Fin n → ℝ) (W 0)).comp (T 0 : E 0 →L[ℝ] _))
  have hL : ∀ i z, L i z = (T 0 z).1 i := fun _ _ => rfl
  have hder : ∀ i, HasDerivWithinAt (fun t => L i (((R ∘ ι) ∘ γ) t)) (L i v) (Ici 0) 0 :=
    fun i => (L i).hasFDerivAt.comp_hasDerivWithinAt (0 : ℝ) hcurve
  have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝[≥] 0 := nhdsWithin_mono _ Ioi_subset_Ici_self
  have hcoord : ∀ i, ∀ᶠ t in 𝓝[>] (0 : ℝ), (T 0 (((R ∘ ι) ∘ γ) t)).1 i = 0 →
      (T 0 (ι x)).1 i = 0 ∧ i ∉ S := by
    intro i
    by_cases hi : (T 0 (ι x)).1 i = 0
    · by_cases hiS : i ∈ S
      · have hvi : 0 < L i v := by
          have := hiS; simp only [hS, Finset.mem_filter] at this; exact this.2.2
        have h0 : (fun t => L i (((R ∘ ι) ∘ γ) t)) 0 = 0 := by
          change L i (((R ∘ ι) ∘ γ) 0) = 0
          rw [h00]; exact hi
        filter_upwards [eventually_pos_of_hasDerivWithinAt_Ici (hder i) h0 hvi] with t ht h
        exact absurd h (ne_of_gt ht)
      · exact Eventually.of_forall fun t _ => ⟨hi, hiS⟩
    · have hc : ContinuousWithinAt (fun t => L i (((R ∘ ι) ∘ γ) t)) (Ici 0) 0 :=
        (hder i).continuousWithinAt
      have h0 : (fun t => L i (((R ∘ ι) ∘ γ) t)) 0 ≠ 0 := by
        change L i (((R ∘ ι) ∘ γ) 0) ≠ 0
        rw [h00]; exact hi
      have : ∀ᶠ t in 𝓝[≥] (0 : ℝ), L i (((R ∘ ι) ∘ γ) t) ≠ 0 :=
        hc.eventually (isOpen_ne.mem_nhds h0)
      filter_upwards [hle this] with t ht h
      exact absurd h ht
  have hNev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ((R ∘ ι) ∘ γ) t ∈ N := by
    have hc : ContinuousWithinAt ((R ∘ ι) ∘ γ) (Ici 0) 0 := hcurve.continuousWithinAt
    have : ∀ᶠ t in 𝓝[≥] (0 : ℝ), ((R ∘ ι) ∘ γ) t ∈ N := hc.eventually (by rw [h00]; exact hN)
    exact hle this
  obtain ⟨t, htc, htN, htU⟩ := ((eventually_all.2 hcoord).and (hNev.and (hle hev))).exists
  refine ⟨((R ∘ ι) ∘ γ) t, ⟨R.apply_mem_retract htU, htN⟩, ?_⟩
  set q := ((R ∘ ι) ∘ γ) t with hq
  set Zq : Finset (Fin n) := Finset.univ.filter fun i => (T 0 q).1 i = 0 with hZq
  have hdisj : Disjoint Zq S := by
    rw [Finset.disjoint_left]
    intro i hi hiS
    simp only [hZq, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact (htc i hi).2 hiS
  have hsub : Zq ∪ S ⊆ Z := by
    intro i hi
    rcases Finset.mem_union.1 hi with hi | hi
    · simp only [hZq, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [hZ, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (htc i hi).1
    · simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [hZ, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hi.1
  have hcard : Zq.card + S.card ≤ Z.card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card hsub
  calc degIndexWith T q + quotDim A (reducedTangentSpaceWith R T x)
      ≤ Zq.card + S.card := Nat.add_le_add_left hk _
    _ ≤ Z.card := hcard

end Retract

/-! ### `dim(T_xO / T^R_xO)` along a germ of sc-diffeomorphisms -/

namespace ScRetraction.IsDiffeoGerm

variable {E E' : ScBanach} {n n' : ℕ} {W W' : ScBanach} {C : Set (E 0)} {C' : Set (E' 0)}
  {R : ScRetraction E C} {R' : ScRetraction E' C'} {F : E 0 → E' 0} {G : E' 0 → E 0}

/-- Along a germ of sc-diffeomorphisms `F : (O, x) → (O', y)`, `dim(T_xO / T^R_xO) ≤
dim(T_yO' / T^R_yO')` (Proposition 2.4.10; applied to the inverse germ this is an equality). -/
theorem quotDim_le_quotDim (h : R.IsDiffeoGerm R' F G)
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (hT : C = T 0 ⁻¹' quadrant n W 0)
    (T' : ScIso E' ((ScBanach.const (Fin n' → ℝ)).prod W')) (hT' : C' = T' 0 ⁻¹' quadrant n' W' 0)
    {x : E 1} (hx : x ∈ E.lvlSet R.retract 1) :
    quotDim (LinearMap.range (scDeriv R.U R x : E 0 →ₗ[ℝ] E 0)) (reducedTangentSpaceWith R T x) ≤
      quotDim (LinearMap.range (scDeriv R'.U R' (levelMap (F ∘ R) 1 x) : E' 0 →ₗ[ℝ] E' 0))
        (reducedTangentSpaceWith R' T' (levelMap (F ∘ R) 1 x)) := by
  set y : E' 1 := levelMap (F ∘ R) 1 x with hy
  have hy' : y ∈ E'.lvlSet R'.retract 1 := h.image_mem hx
  set D : E 0 →L[ℝ] E' 0 := scDeriv R.U (F ∘ R) x with hD
  set D' : E' 0 →L[ℝ] E 0 := scDeriv R'.U (G ∘ R') y with hD'
  set P : E 0 →L[ℝ] E 0 := scDeriv R.U R x with hP
  set A : Submodule ℝ (E 0) := LinearMap.range (P : E 0 →ₗ[ℝ] E 0) with hA
  set A' : Submodule ℝ (E' 0) :=
    LinearMap.range (scDeriv R'.U R' y : E' 0 →ₗ[ℝ] E' 0) with hA'
  set B := reducedTangentSpaceWith R T x with hB
  set B' := reducedTangentSpaceWith R' T' y with hB'
  have hD'D : ∀ v, D' (D v) = P v := h.deriv_inv_deriv hx
  have hPP : ∀ v, P (P v) = P v := fun v =>
    congrArg (fun L : E 0 →L[ℝ] E 0 => L v) (R.scDeriv_comp_self hx)
  have hDA : ∀ w ∈ A, (D : E 0 →ₗ[ℝ] E' 0) w ∈ A' := by
    rintro w ⟨w', rfl⟩
    obtain ⟨u, hu⟩ := h.deriv_mem_range hx (v := P w') ⟨w', rfl⟩
    exact ⟨u, hu⟩
  have hfwd : B.map (D : E 0 →ₗ[ℝ] E' 0) = B' := proposition_2_4_10_reduced h hx T hT T' hT'
  have hbwd : B'.map (D' : E' 0 →ₗ[ℝ] E 0) = B := by
    have := proposition_2_4_10_reduced h.symm hy' T' hT' T hT
    rwa [h.image_image hx] at this
  let D₀ : A →ₗ[ℝ] A' := (D : E 0 →ₗ[ℝ] E' 0).restrict hDA
  let Φ : A →ₗ[ℝ] A' ⧸ B'.comap A'.subtype := (B'.comap A'.subtype).mkQ ∘ₗ D₀
  have hker : LinearMap.ker Φ = B.comap A.subtype := by
    ext ⟨w, hw⟩
    simp only [Φ, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
    change D w ∈ B' ↔ w ∈ B
    constructor
    · intro hDw
      have h1 : D' (D w) ∈ B := hbwd ▸ Submodule.mem_map_of_mem hDw
      obtain ⟨w', rfl⟩ := hw
      have h2 : D' (D (P w')) = P w' := by rw [hD'D]; exact hPP w'
      change D' (D (P w')) ∈ B at h1
      rwa [h2] at h1
    · intro hwB
      exact hfwd ▸ Submodule.mem_map_of_mem hwB
  have hemb : (A ⧸ B.comap A.subtype) ≃ₗ[ℝ] LinearMap.range Φ := hker ▸ Φ.quotKerEquivRange
  have : FiniteDimensional ℝ (A' ⧸ B'.comap A'.subtype) :=
    finiteDimensional_quot_inf_minimalSubspace T' A' (E'.toBase 1 y)
  rw [quotDim, quotDim, hemb.finrank_eq]
  exact Submodule.finrank_le _

end ScRetraction.IsDiffeoGerm

namespace MPolyfold

universe u v

section Drop

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- **In every chart, the index drops by `d_X(y)` near a point attaining the bound of Theorem
2.4.12**: if `y` is such a point (`IsDegSharpAt`) and `ψ` is any chart of the structure around
`y`, then every neighbourhood of `y` contains `y'` with `d_C(ψ(y')) + d_X(y) ≤ d_C(ψ(y))`. -/
theorem exists_chartDegIndex_add_le {ψ : MChart X} (hψ : P.IsChart ψ) {y : X} (hy : y ∈ ψ.source)
    (hsharp : P.IsDegSharpAt y) {N : Set X} (hN : N ∈ 𝓝 y) :
    ∃ y' ∈ N ∩ ψ.source, chartDegIndex ψ y' + P.degIndex y ≤ chartDegIndex ψ y := by
  obtain ⟨φ, hφ, hyφ, R, hR, n, W, T, hT, z, hz, hd⟩ := hsharp
  obtain ⟨W₀, hW₀, hW₀eq⟩ := φ.exists_isOpen_image_eq (s := φ.source ∩ ψ.source) inter_subset_left
    (φ.isOpen_source.inter ψ.isOpen_source)
  obtain ⟨W₀', hW₀', hW₀'eq⟩ := ψ.exists_isOpen_image_eq (s := ψ.source ∩ φ.source) inter_subset_left
    (ψ.isOpen_source.inter φ.isOpen_source)
  obtain ⟨R', hR'⟩ := ψ.model.isScRetract
  obtain ⟨n', W', T', hT'⟩ := ψ.model.isPartialQuadrant
  have germ := (hφ.compatible hψ (P := P)).isDiffeoGerm R hR R' hR' hW₀ hW₀eq hW₀' hW₀'eq
  have hzO : z ∈ φ.model.E.lvlSet (R.restrict hW₀).retract 1 := by
    rw [ScBanach.mem_lvlSet, hz, R.restrict_retract, hR, ← hW₀eq]
    exact φ.mem_overlap ψ hyφ hy
  have hzU : z ∈ φ.model.E.lvlSet (R.restrict hW₀).U 1 :=
    (R.restrict hW₀).lvlSet_retract_subset 1 hzO
  set w : ψ.model.E 1 := levelMap (φ.transition ψ ∘ R.restrict hW₀) 1 z with hw
  have hwO : w ∈ ψ.model.E.lvlSet (R'.restrict hW₀').retract 1 := germ.image_mem hzO
  have hwbase : ψ.model.E.toBase 1 w = ψ y := by
    rw [hw, germ.toBase_image hzO, hz, φ.transition_apply ψ hyφ]
  have hkk := germ.quotDim_le_quotDim T hT T' hT' hzO
  rw [reducedTangentSpaceWith_restrict R hW₀ T hzU, R.scDeriv_restrict hW₀ hzU] at hkk
  -- a neighbourhood `N'` of `ψ(y)` with `ψ⁻¹(O ∩ N') ⊆ N`
  have hcont : ContinuousWithinAt ψ.symm ψ.model.O (ψ y) :=
    ψ.continuousOn_invFun.continuousWithinAt (ψ.mapsTo_model y hy)
  have hpre : ψ.symm ⁻¹' N ∈ 𝓝[ψ.model.O] (ψ y) :=
    hcont (by rw [ψ.symm_apply_apply hy]; exact hN)
  obtain ⟨N', hN', hN'sub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hpre
  obtain ⟨q, ⟨hqO, hqN⟩, hq⟩ := (R'.restrict hW₀').exists_degIndexWith_add_quotDim_le T' hT' hwO
    (N := N') (by rw [hwbase]; exact hN')
  rw [hwbase] at hq
  have hqO' : q ∈ ψ.model.O := by
    rw [R'.restrict_retract, hR'] at hqO; exact hqO.1
  refine ⟨ψ.symm q, ⟨hN'sub ⟨hqN, hqO'⟩, ψ.symm_mapsTo hqO'⟩, ?_⟩
  have hqs : ψ.symm q ∈ ψ.source := ψ.symm_mapsTo hqO'
  have e1 : chartDegIndex ψ (ψ.symm q) = degIndexWith T' q := by
    rw [chartDegIndex, degIndex_eq T' hT' (ψ.apply_mem_C hqs), ψ.apply_symm_apply hqO']
  have e2 : chartDegIndex ψ y = degIndexWith T' (ψ y) := by
    rw [chartDegIndex, degIndex_eq T' hT' (ψ.apply_mem_C hy)]
  rw [e1, e2]
  exact (Nat.add_le_add_left (hd.trans hkk) _).trans hq

end Drop

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : MPolyfold X} {Q : MPolyfold Y}

/-- **The product formula at a smooth point `x` and a point `y` attaining the bound of Theorem
2.4.12** (Definition 2.4.1, p. 54; Theorem 2.4.12, p. 63): `d_{X × Y}(x, y) = d_X(x) + d_Y(y)`.
No tameness, and no condition on the charts of `X` at `x`.

A chart `χ` of `X × Y` realizing `d_{X × Y}(x, y)` restricts to a chart of the slice
`{x} × Y ≅ Y`; in it the index drops by `d_Y(y)` at some `(x, y')`
(`exists_chartDegIndex_add_le`), and `d_X(x) ≤ d_{X × Y}(x, y')`
(`degIndex_le_degIndex_prod_left`). -/
theorem degIndex_prod_of_mem_smoothSet_of_isDegSharpAt [ParacompactSpace (X × Y)] {x : X} {y : Y}
    (hx : x ∈ P.smoothSet) (hy : Q.IsDegSharpAt y) :
    (P.prod Q).degIndex (x, y) = P.degIndex x + Q.degIndex y := by
  have := (P.prod Q).paracompactSpace_subtype (sliceRight (Y := Y) x)
  obtain ⟨χ, hχ, hxy, hd⟩ := (P.prod Q).exists_isChart_degIndex_eq (x, y)
  have hA := isSubMPolyfold_sliceRight (Q := Q) hx
  let a : sliceRight (Y := Y) x := ⟨(x, y), rfl⟩
  set d := hA.data a.2 with hdd
  have hψA := subPolyfold_isChart hA d hχ a
  have hdiff := isScDiffeoOn_sliceRight (Q := Q) hx
  have hψ := transportChart_isChart hdiff hψA
  have haS : (x, y) ∈ d.shrink χ := d.mem_shrink χ a.2 (hA.mem_data_V a.2) hxy
  have hyψ : y ∈ (transportChart hdiff (subChart d hχ a)).source := ⟨mem_univ _, haS⟩
  obtain ⟨y', ⟨-, hy'⟩, hle⟩ := exists_chartDegIndex_add_le hψ hyψ hy univ_mem
  have hy'S : (x, y') ∈ d.shrink χ := hy'.2
  have hy'χ : (x, y') ∈ χ.source := d.shrink_subset_source χ hy'S
  have e1 : chartDegIndex (transportChart hdiff (subChart d hχ a)) y' = chartDegIndex χ (x, y') :=
    rfl
  have e2 : chartDegIndex (transportChart hdiff (subChart d hχ a)) y = chartDegIndex χ (x, y) :=
    rfl
  rw [e1, e2, ← hd] at hle
  exact P.degIndex_prod_of_exists_slice Q
    ⟨y', (Nat.add_le_add_right ((P.prod Q).degIndex_le hχ hy'χ) _).trans hle⟩

/-- **The product formula at a point `x` attaining the bound of Theorem 2.4.12 and a smooth point
`y`.** -/
theorem degIndex_prod_of_isDegSharpAt_of_mem_smoothSet [ParacompactSpace (X × Y)] {x : X} {y : Y}
    (hx : P.IsDegSharpAt x) (hy : y ∈ Q.smoothSet) :
    (P.prod Q).degIndex (x, y) = P.degIndex x + Q.degIndex y := by
  have := (P.prod Q).paracompactSpace_subtype (sliceLeft (X := X) y)
  obtain ⟨χ, hχ, hxy, hd⟩ := (P.prod Q).exists_isChart_degIndex_eq (x, y)
  have hA := isSubMPolyfold_sliceLeft (P := P) hy
  let a : sliceLeft (X := X) y := ⟨(x, y), rfl⟩
  set d := hA.data a.2 with hdd
  have hψA := subPolyfold_isChart hA d hχ a
  have hdiff := isScDiffeoOn_sliceLeft (P := P) hy
  have hψ := transportChart_isChart hdiff hψA
  have haS : (x, y) ∈ d.shrink χ := d.mem_shrink χ a.2 (hA.mem_data_V a.2) hxy
  have hxψ : x ∈ (transportChart hdiff (subChart d hχ a)).source := ⟨mem_univ _, haS⟩
  obtain ⟨x', ⟨-, hx'⟩, hle⟩ := exists_chartDegIndex_add_le hψ hxψ hx univ_mem
  have hx'S : (x', y) ∈ d.shrink χ := hx'.2
  have hx'χ : (x', y) ∈ χ.source := d.shrink_subset_source χ hx'S
  have e1 : chartDegIndex (transportChart hdiff (subChart d hχ a)) x' = chartDegIndex χ (x', y) :=
    rfl
  have e2 : chartDegIndex (transportChart hdiff (subChart d hχ a)) x = chartDegIndex χ (x, y) :=
    rfl
  rw [e1, e2, ← hd] at hle
  refine le_antisymm (P.degIndex_prod_le Q x y) ?_
  have h1 : Q.degIndex y ≤ (P.prod Q).degIndex (x', y) := P.degIndex_le_degIndex_prod_right Q x' y
  have h2 := (P.prod Q).degIndex_le hχ hx'χ
  omega

/-- A smooth point of a tame M-polyfold attains the bound of Theorem 2.4.12. -/
theorem isDegSharpAt_of_isTame_of_mem_smoothSet (hP : P.IsTame) {x : X} (hx : x ∈ P.smoothSet) :
    P.IsDegSharpAt x := by
  obtain ⟨φ, hφ, hxφ, R, hRO, hRt⟩ := IsTame.exists_chart P hP x
  obtain ⟨n, W, T, hT⟩ := φ.model.isPartialQuadrant
  have hsm : φ x ∈ φ.model.E.smooth := φ.model.E.mem_smooth_iff.2 fun k =>
    (P.mem_levelSet_iff hφ hxφ).1 (mem_iInter.1 hx k)
  exact isDegSharpAt_of_isTameWith hφ R hRO hT (hRt n W T hT) hxφ hsm

/-- **The product formula for an arbitrary `X` at a smooth point and a tame `Y` at a smooth
point** (for instance `Y = [0, ∞)`, `y = 0`). -/
theorem degIndex_prod_of_mem_smoothSet_of_isTame [ParacompactSpace (X × Y)] {x : X} {y : Y}
    (hx : x ∈ P.smoothSet) (hQ : Q.IsTame) (hy : y ∈ Q.smoothSet) :
    (P.prod Q).degIndex (x, y) = P.degIndex x + Q.degIndex y :=
  degIndex_prod_of_mem_smoothSet_of_isDegSharpAt hx (isDegSharpAt_of_isTame_of_mem_smoothSet hQ hy)

variable (P Q) in
/-- **Reduction to nearby points** (Lemma 2.4.3): if `d_X(x) + d_Y(y) ≤ d_{X × Y}(p)` at points
`p` arbitrarily close to `(x, y)`, then `d_{X × Y}(x, y) = d_X(x) + d_Y(y)`. -/
theorem degIndex_prod_of_frequently [ParacompactSpace (X × Y)] {x : X} {y : Y}
    (h : ∃ᶠ p in 𝓝 (x, y), P.degIndex x + Q.degIndex y ≤ (P.prod Q).degIndex p) :
    (P.prod Q).degIndex (x, y) = P.degIndex x + Q.degIndex y := by
  obtain ⟨p, hp, hle⟩ := (h.and_eventually (lemma_2_4_3 (P.prod Q) (x, y))).exists
  exact le_antisymm (P.degIndex_prod_le Q x y) (hp.trans hle)

variable (P Q) in
/-- The product formula at `(x, y)` follows from the product formula at smooth points `(x', y')`
arbitrarily close to `(x, y)` at which `d_X(x') = d_X(x)`, `d_Y(y') = d_Y(y)` and the bound of
Theorem 2.4.12 is attained at `y'`. -/
theorem degIndex_prod_of_frequently_smooth [ParacompactSpace (X × Y)] {x : X} {y : Y}
    (h : ∃ᶠ p : X × Y in 𝓝 (x, y), p.1 ∈ P.smoothSet ∧ Q.IsDegSharpAt p.2 ∧
      P.degIndex p.1 = P.degIndex x ∧ Q.degIndex p.2 = Q.degIndex y) :
    (P.prod Q).degIndex (x, y) = P.degIndex x + Q.degIndex y := by
  refine P.degIndex_prod_of_frequently Q (h.mono ?_)
  rintro ⟨x', y'⟩ ⟨h1, h2, h3, h4⟩
  rw [degIndex_prod_of_mem_smoothSet_of_isDegSharpAt h1 h2, h3, h4]

variable (P) in
/-- **The product formula at an arbitrary point `x` and a point `y` attaining the bound of Theorem
2.4.12**, when `d_X(x)` is attained at smooth points arbitrarily close to `x` (by Lemma 2.4.3 this
says that `d_X` restricted to the smooth points is not smaller near `x` than at `x`). -/
theorem degIndex_prod_of_frequently_smoothSet_of_isDegSharpAt [ParacompactSpace (X × Y)] {x : X}
    {y : Y} (hx : ∃ᶠ x' in 𝓝 x, x' ∈ P.smoothSet ∧ P.degIndex x ≤ P.degIndex x')
    (hy : Q.IsDegSharpAt y) :
    (P.prod Q).degIndex (x, y) = P.degIndex x + Q.degIndex y := by
  have hev : ∀ᶠ x' in 𝓝 x, (P.prod Q).degIndex (x', y) ≤ (P.prod Q).degIndex (x, y) :=
    (Continuous.prodMk_left y).continuousAt.eventually (lemma_2_4_3 (P.prod Q) (x, y))
  obtain ⟨x', ⟨hx's, hx'd⟩, hle⟩ := (hx.and_eventually hev).exists
  refine le_antisymm (P.degIndex_prod_le Q x y) ?_
  rw [degIndex_prod_of_mem_smoothSet_of_isDegSharpAt hx's hy] at hle
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
covering `F`, at a morphism `φ` with `F(φ)` smooth in `𝐗` and the bound of Theorem 2.4.12 attained
at `s(φ) ∈ Y`: `d_{𝐗 × Y}(F(φ), s(φ)) = 2 · d_𝐘(φ)` and
`2 · d_{𝐗 ₛ×_F Y}(F(φ), s(φ)) = d_{𝐗 × Y}(F(φ), s(φ))`. -/
theorem EpFunctor.IsProperCovering.degIndex_prod_fibredMap_of_mem_smoothSet
    (hF : F.IsProperCovering) (φ : MorY) (h1 : F.mor φ ∈ X.PMor.smoothSet)
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
    rw [MPolyfold.degIndex_prod_of_mem_smoothSet_of_isDegSharpAt h1 h2, hF.degIndex_mor,
      ← Y.degIndex_src]
    ring
  exact ⟨h, by rw [h, ← hF.degIndex_fibredMap]⟩

end Fibres

end Polyfold

#print axioms Polyfold.ScRetraction.exists_degIndexWith_add_quotDim_le
#print axioms Polyfold.ScRetraction.IsDiffeoGerm.quotDim_le_quotDim
#print axioms Polyfold.MPolyfold.exists_chartDegIndex_add_le
#print axioms Polyfold.MPolyfold.degIndex_prod_of_mem_smoothSet_of_isDegSharpAt
#print axioms Polyfold.MPolyfold.degIndex_prod_of_isDegSharpAt_of_mem_smoothSet
#print axioms Polyfold.MPolyfold.degIndex_prod_of_mem_smoothSet_of_isTame
#print axioms Polyfold.MPolyfold.degIndex_prod_of_frequently
#print axioms Polyfold.MPolyfold.degIndex_prod_of_frequently_smooth
#print axioms Polyfold.MPolyfold.degIndex_prod_of_frequently_smoothSet_of_isDegSharpAt
#print axioms Polyfold.EpFunctor.IsProperCovering.degIndex_prod_fibredMap_of_mem_smoothSet
