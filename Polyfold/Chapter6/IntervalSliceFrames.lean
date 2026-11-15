import Polyfold.Chapter6.IntervalSliceOrientation

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, p. 276:
**Remark 6.6.19** (preprint Remark 6.42, p. 230) and the proof of Theorem 6.7.1 (p. 278): the
orientation `e ∧ o` of `ker G'(t, x)` for a section `G` over `[0, 1] × X`, in terms of frames.

# Frames of `ker G'(t, x)` with the `t`-direction first

## What is formalized

* `consE_one_zero`, `consE_zero_single`, `consELin`, `exists_basis_stdOrientation`: the
  coordinates `ℝ^{k+1} = ℝ × ℝ^k` on the standard basis; `prodSlice_sectionSmul_const`.
* `exists_timeFirst_coordinates`: coordinates of a subspace `N' ⊆ ℝ × E` of dimension
  `dim N + 1` with `N' ∩ ({0} × E) = {0} × N`, the `ℝ`-direction first.
* `ChartPoint.mem_linKer_ivPt_iff_of_fst_eq_zero`: in the product chart `χ_b × φ`, a vector
  `(0, v)` lies in `ker G'(t, x)` iff `v` lies in the kernel of the linearization of the slice
  `G(t, ·)` at `x`.
* **`ChartPoint.exists_timeFirst_wedge_of_slice`**: let `(t, x)` be a zero of `G` with
  `G'(t, x)` onto and in `Lin(f̃, (t, x))`, such that the slice `g = G(t, ·)` has `g'(x)` onto
  and in `Lin(f, x)`, and let `a₁, …, a_k` be a basis of `ker g'(x)` whose wedge spans the
  orientation given by `o`.  Then there is `ν ∈ ker G'(t, x)` whose `t`-component is the
  direction of increasing `t` such that `ν ∧ (0, a₁) ∧ … ∧ (0, a_k)` spans the orientation of
  `ker G'(t, x)` given by `e ∧ o`.
* `exists_timeFirst_wedge_ivOrLift`: the same for the chart point of the product chart with a
  given level-one lift of the base point.
-/

open Set Filter Topology Manifold Module
open scoped ContDiff

noncomputable section

namespace Polyfold

open StrongRetr UnitCube

universe u v

/-! ### The coordinates `ℝ^{k+1} = ℝ × ℝ^k` on the standard basis -/

section Coordinates

variable {k : ℕ}

/-- `(1, 0)` is the first vector of the standard basis. -/
theorem consE_one_zero :
    consE 1 (0 : EuclideanSpace ℝ (Fin k)) = EuclideanSpace.single (0 : Fin (k + 1)) (1 : ℝ) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp [Fin.succ_ne_zero]

/-- `(0, e_l) = e_{l+1}`. -/
theorem consE_zero_single (l : Fin k) :
    consE 0 (EuclideanSpace.single l (1 : ℝ)) = EuclideanSpace.single l.succ (1 : ℝ) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [(Fin.succ_ne_zero l).symm]
  · simp [Fin.succ_inj]

variable (k) in
/-- The standard basis of `ℝ^k` and its orientation. -/
theorem exists_basis_stdOrientation : ∃ sb : Basis (Fin k) ℝ (EuclideanSpace ℝ (Fin k)),
    (∀ i, sb i = EuclideanSpace.single i (1 : ℝ)) ∧ sb.orientation = stdOrientation k :=
  ⟨(EuclideanSpace.basisFun (Fin k) ℝ).toBasis, fun i => by
    rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply], rfl⟩

variable (k) in
/-- `w ↦ (0, w)` as a linear map `ℝ^k → ℝ^{k+1}`. -/
def consELin : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin (k + 1)) where
  toFun := consE 0
  map_add' x y := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' c x := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

@[simp] theorem consELin_apply (w : EuclideanSpace ℝ (Fin k)) : consELin k w = consE 0 w := rfl

end Coordinates

/-! ### The slice of a scalar multiple -/

section SliceSmul

variable {T : Type*} {X : Type u} {Y : Type v} {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})]
  [∀ x, Module ℝ (P ⁻¹' {x})]

/-- The slice of `c · S` is `c · S(t, ·)`. -/
theorem prodSlice_sectionSmul_const {S : T × X → pullbackSpace P (Prod.snd : T × X → X)}
    (hS : IsSection (pullbackProj P Prod.snd) S) (c : ℝ) (t : T) :
    prodSlice (sectionSmul (pullbackProj P Prod.snd) (fun _ => c) S) t =
      sectionSmul P (fun _ => c) (prodSlice S t) := by
  funext x
  change (sectionSmul (pullbackProj P Prod.snd) (fun _ => c) S (t, x)).1.2 = _
  rw [sectionSmul_apply hS, sectionSmul_apply (hS.prodSlice t)]
  exact congrArg Subtype.val
    (pullbackFiberEquiv_smul P (Prod.snd : T × X → X) (t, x) c ⟨S (t, x), hS (t, x)⟩)

end SliceSmul

/-! ### Coordinates of a subspace of `ℝ × E` with the `ℝ`-direction first -/

section TimeFirstCoordinates

variable {E₀ : Type*} [AddCommGroup E₀] [Module ℝ E₀]

/-- **Coordinates with the `ℝ`-direction first.**  Let `N ⊆ E` have dimension `k` and
`N' ⊆ ℝ × E` dimension `k + 1`, with `N' ∩ ({0} × E) = {0} × N`, let `a₁, …, a_k` be a basis of
`N` and `s ≠ 0`.  Then there are `ν ∈ N'` with `ℝ`-component `s` and coordinates
`ι : ℝ^k ≅ N`, `ι' : ℝ^{k+1} ≅ N'` with `ι'(0, w) = (0, ι w)` and `ι'(1, 0) = ν`, such that a ray
of `λ(N)` is that of `a₁ ∧ … ∧ a_k` only if it gives the standard orientation in `ι`, and a ray
of `λ(N')` giving the standard orientation in `ι'` is that of `ν ∧ (0, a₁) ∧ … ∧ (0, a_k)`. -/
theorem exists_timeFirst_coordinates {N : Submodule ℝ E₀}
    {N' : Submodule ℝ ((Fin 1 → ℝ) × E₀)} [FiniteDimensional ℝ N] [FiniteDimensional ℝ N']
    {k : ℕ} (hk : finrank ℝ N = k) (hk' : finrank ℝ N' = k + 1)
    (hiff : ∀ w : (Fin 1 → ℝ) × E₀, w.1 = 0 → (w ∈ N' ↔ w.2 ∈ N)) {s : ℝ} (hs : s ≠ 0)
    (a : Fin k → N) (hna : wedge a hk.symm ≠ 0) :
    ∃ (ν : N') (a' : Fin k → N') (hna' : wedge (Fin.cons ν a' : Fin (k + 1) → N') hk'.symm ≠ 0)
      (ι : EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ] N) (ι' : EuclideanSpace ℝ (Fin (k + 1)) ≃ₗ[ℝ] N'),
      ((ν : (Fin 1 → ℝ) × E₀).1 = fun _ => s) ∧
      (∀ l, ((a' l : N') : (Fin 1 → ℝ) × E₀) = (0, (a l : E₀))) ∧
      (∀ w, ((ι' (consE 0 w) : N') : (Fin 1 → ℝ) × E₀) = (0, (ι w : E₀))) ∧
      (((ι' (consE 1 0) : N') : (Fin 1 → ℝ) × E₀).1 = fun _ => s) ∧
      (∀ r : Module.Ray ℝ (maxPow N), r = rayOfNeZero ℝ _ hna →
        pullOr finrank_euclideanSpace_fin ι r = stdOrientation k) ∧
      ∀ r' : Module.Ray ℝ (maxPow N'),
        pullOr finrank_euclideanSpace_fin ι' r' = stdOrientation (k + 1) →
          r' = rayOfNeZero ℝ _ hna' := by
  have hli : LinearIndependent ℝ a := (wedge_ne_zero_iff hk.symm).1 hna
  -- coordinates of `N`
  obtain ⟨bA, hbA⟩ : ∃ bA : Basis (Fin k) ℝ N, ∀ i, bA i = a i :=
    ⟨basisOfLinearIndependentOfCardEqFinrank' a hli (by rw [Fintype.card_fin, hk]), fun i => by
      rw [coe_basisOfLinearIndependentOfCardEqFinrank']⟩
  obtain ⟨sb, hsbi, hsbo⟩ := exists_basis_stdOrientation k
  obtain ⟨ι, hι⟩ : ∃ ι : EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ] N, ∀ i, ι (sb i) = a i :=
    ⟨sb.equiv bA (Equiv.refl _), fun i => by rw [Basis.equiv_apply]; exact hbA i⟩
  -- `v ↦ (0, v)`
  obtain ⟨J, hJ⟩ : ∃ J : N →ₗ[ℝ] N', ∀ n, ((J n : N') : (Fin 1 → ℝ) × E₀) = (0, (n : E₀)) := by
    refine ⟨{ toFun := fun n => ⟨((0 : Fin 1 → ℝ), (n : E₀)), (hiff (0, (n : E₀)) rfl).2 n.2⟩
              map_add' := fun n m => Subtype.ext ?_
              map_smul' := fun c n => Subtype.ext ?_ }, fun n => rfl⟩
    · change (((0 : Fin 1 → ℝ), ((n : E₀) + (m : E₀))) : (Fin 1 → ℝ) × E₀) =
        (0, (n : E₀)) + (0, (m : E₀))
      rw [Prod.mk_add_mk, add_zero]
    · change (((0 : Fin 1 → ℝ), c • (n : E₀)) : (Fin 1 → ℝ) × E₀) =
        c • ((0 : Fin 1 → ℝ), (n : E₀))
      rw [Prod.smul_mk, smul_zero]
  have hJinj : Function.Injective J := fun n m h => by
    have h1 := congrArg (fun u : N' => (u : (Fin 1 → ℝ) × E₀).2) h
    simp only [hJ] at h1
    exact Subtype.ext h1
  -- the `ℝ`-component on `N'`
  obtain ⟨τ, hτ⟩ : ∃ τ : N' →ₗ[ℝ] ℝ, ∀ u, τ u = (u : (Fin 1 → ℝ) × E₀).1 0 :=
    ⟨(LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) ∘ₗ
      (LinearMap.fst ℝ (Fin 1 → ℝ) E₀) ∘ₗ N'.subtype, fun _ => rfl⟩
  have hτJ : ∀ n, τ (J n) = 0 := fun n => by rw [hτ, hJ]; rfl
  obtain ⟨w₀, hw₀⟩ : ∃ w₀, τ w₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hfst : ∀ u : N', (u : (Fin 1 → ℝ) × E₀).1 = 0 := fun u => funext fun i => by
      obtain rfl : i = 0 := Subsingleton.elim _ _
      exact (hτ u).symm.trans (hcon u)
    obtain ⟨Q, hQ⟩ : ∃ Q : N' →ₗ[ℝ] N, ∀ u, (Q u : E₀) = (u : (Fin 1 → ℝ) × E₀).2 :=
      ⟨{ toFun := fun u => ⟨(u : (Fin 1 → ℝ) × E₀).2, (hiff u.1 (hfst u)).1 u.2⟩
         map_add' := fun _ _ => rfl
         map_smul' := fun _ _ => rfl }, fun _ => rfl⟩
    have hQinj : Function.Injective Q := fun u u' h =>
      Subtype.ext (Prod.ext ((hfst u).trans (hfst u').symm)
        ((hQ u).symm.trans ((congrArg Subtype.val h).trans (hQ u'))))
    have hle := LinearMap.finrank_le_finrank_of_injective hQinj
    rw [hk, hk'] at hle
    exact absurd hle (Nat.not_succ_le_self k)
  obtain ⟨ν, hν⟩ : ∃ ν : N', τ ν = s :=
    ⟨(s / τ w₀) • w₀, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hw₀]⟩
  have hν1 : (ν : (Fin 1 → ℝ) × E₀).1 = fun _ => s := funext fun i => by
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact (hτ ν).symm.trans hν
  -- the frame `(ν, (0, a))`
  have hliJ : LinearIndependent ℝ (J ∘ a) := hli.map' J (LinearMap.ker_eq_bot.2 hJinj)
  have hνnot : ν ∉ Submodule.span ℝ (Set.range (J ∘ a)) := fun hmemν => by
    have hsub : Submodule.span ℝ (Set.range (J ∘ a)) ≤ LinearMap.ker τ :=
      Submodule.span_le.2 (by rintro _ ⟨l, rfl⟩; exact LinearMap.mem_ker.2 (hτJ (a l)))
    have h0 : τ ν = 0 := LinearMap.mem_ker.1 (hsub hmemν)
    exact hs (hν.symm.trans h0)
  have hlic : LinearIndependent ℝ (Fin.cons ν (J ∘ a) : Fin (k + 1) → N') :=
    hliJ.finCons hνnot
  obtain ⟨bC, hbC⟩ : ∃ bC : Basis (Fin (k + 1)) ℝ N',
      ∀ i, bC i = (Fin.cons ν (J ∘ a) : Fin (k + 1) → N') i :=
    ⟨basisOfLinearIndependentOfCardEqFinrank' _ hlic (by rw [Fintype.card_fin, hk']), fun i => by
      rw [coe_basisOfLinearIndependentOfCardEqFinrank']⟩
  obtain ⟨sb', hsbi', hsbo'⟩ := exists_basis_stdOrientation (k + 1)
  obtain ⟨ι', hι'⟩ : ∃ ι' : EuclideanSpace ℝ (Fin (k + 1)) ≃ₗ[ℝ] N',
      ∀ i, ι' (sb' i) = (Fin.cons ν (J ∘ a) : Fin (k + 1) → N') i :=
    ⟨sb'.equiv bC (Equiv.refl _), fun i => by rw [Basis.equiv_apply]; exact hbC i⟩
  have hι₁ : ((ι' (consE 1 0) : N') : (Fin 1 → ℝ) × E₀).1 = fun _ => s := by
    rw [consE_one_zero, ← hsbi' 0, hι' 0]
    exact hν1
  have hlin : (ι' : EuclideanSpace ℝ (Fin (k + 1)) →ₗ[ℝ] N') ∘ₗ consELin k =
      J ∘ₗ (ι : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] N) := by
    refine sb.ext fun l => ?_
    change ι' (consE 0 (sb l)) = J (ι (sb l))
    rw [hsbi l, consE_zero_single, ← hsbi' l.succ, hι' l.succ, ← hsbi l, hι l]
    rfl
  have hι₀ : ∀ w, ((ι' (consE 0 w) : N') : (Fin 1 → ℝ) × E₀) = (0, (ι w : E₀)) := fun w => by
    have h := LinearMap.congr_fun hlin w
    change ι' (consE 0 w) = J (ι w) at h
    rw [h, hJ]
  refine ⟨ν, J ∘ a, (wedge_ne_zero_iff hk'.symm).2 hlic, ι, ι', hν1, fun l => hJ (a l), hι₀, hι₁,
    fun r hr => ?_, fun r' hr' => ?_⟩
  · refine ((orientation_eq_pullOr_iff finrank_euclideanSpace_fin ι _ sb).2 ?_).symm.trans hsbo
    rw [hr]
    refine rayOfNeZero_congr ?_ _ _
    congr 1
    exact funext fun i => (hι i).symm
  · have hray := (orientation_eq_pullOr_iff finrank_euclideanSpace_fin ι' _ sb').1
      (hsbo'.trans hr'.symm)
    refine hray.trans (rayOfNeZero_congr ?_ _ _)
    congr 1
    exact funext fun i => hι' i

end TimeFirstCoordinates

section IvFrames

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] {f : X → Y}

namespace ChartPoint

variable {x : X} (p : ChartPoint B x) (b : Fin 1 → Bool) {t : Fin 1 → unitInterval}
  (ht : t ∈ (chart b).source)
  (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))

/-- **`(0, v) ∈ ker G'(t, x)` iff `v ∈ ker G_t'(x)`**, in the product chart `χ_b × φ`, at a zero
`(t, x)` of `G`. -/
theorem mem_linKer_ivPt_iff_of_fst_eq_zero
    {G : (Fin 1 → unitInterval) × X → pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hG : (ivBundle B).IsScFredholmSection G) (hg : B.IsScFredholmSection (prodSlice G t))
    (hz0 : IsZeroAt (pullbackProj P Prod.snd) G (t, x)) (hx0 : IsZeroAt P (prodSlice G t) x)
    (w : (Fin 1 → ℝ) × p.c.φ.model.E 0) (hw : w.1 = 0) :
    w ∈ (p.ivPt b ht q₀).c.linKer G (p.ivPt b ht q₀).z ↔
      w.2 ∈ p.c.linKer (prodSlice G t) p.z := by
  rw [← (p.ivPt b ht q₀).map_ker_linZero hG hz0, ← p.map_ker_linZero hg hx0]
  constructor
  · rintro ⟨u, hu, huw⟩
    have huw' : (u.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0) = w := huw
    have hu1 : (u.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).1 = 0 := by rw [huw']; exact hw
    have h0 : (p.ivPt b ht q₀).linZero hG hz0 u = 0 := LinearMap.mem_ker.1 hu
    rw [p.linZero_ivPt_eq_ivLin_of_fst_eq_zero b ht q₀ hG hg hz0 hx0 u hu1] at h0
    have h1 := p.coe_ivLin_apply b ht q₀ (p.linZero hg hx0) u
    rw [h0] at h1
    refine ⟨(p.ivT b ht q₀ u).1, LinearMap.mem_ker.2 (Subtype.ext h1.symm), ?_⟩
    change ((p.ivT b ht q₀ u).1 : p.c.φ.model.E 0) = w.2
    rw [coe_ivT_fst, huw']
  · rintro ⟨v, hv, hvw⟩
    have hvw' : (v : p.c.φ.model.E 0) = w.2 := hvw
    have hwT : w ∈ (p.ivPt b ht q₀).T := (p.mem_ivPt_T_iff b ht q₀ w).2 (hvw' ▸ v.2)
    have hT : (p.ivT b ht q₀ ⟨w, hwT⟩).1 = v := Subtype.ext hvw'.symm
    refine ⟨⟨w, hwT⟩, LinearMap.mem_ker.2 ?_, rfl⟩
    change (p.ivPt b ht q₀).linZero hG hz0 ⟨w, hwT⟩ = 0
    rw [p.linZero_ivPt_eq_ivLin_of_fst_eq_zero b ht q₀ hG hg hz0 hx0 ⟨w, hwT⟩ hw]
    refine Subtype.ext ?_
    rw [p.coe_ivLin_apply b ht q₀ (p.linZero hg hx0) ⟨w, hwT⟩, hT]
    have h0 : p.linZero hg hx0 v = 0 := LinearMap.mem_ker.1 hv
    rw [h0]
    rfl

set_option maxHeartbeats 1600000 in
-- the model of the product chart is identified with `ℝ × E`
/-- **Frames of `ker G'(t, x)` with the `t`-direction first** (2021 Remark 6.6.19, p. 276, and
the proof of Theorem 6.7.1, p. 278): let `(t, x)` be a zero of a section `G` over `[0, 1] × X`
with `G'(t, x)` onto and in `Lin(f̃, (t, x))`, such that the slice `g = G(t, ·)` has `g'(x)` onto
and in `Lin(f, x)`; let `dim ker g'(x) = k`, `dim ker G'(t, x) = k + 1`, and let `a₁, …, a_k` be
vectors of `ker g'(x)` whose wedge spans the orientation of `ker g'(x)` given by `o`.  Then there
is `ν ∈ ker G'(t, x)` with `t`-component the direction of increasing `t` (`± 1` in the chart
`χ_b × φ`, the sign that of `χ_b`) such that `ν ∧ (0, a₁) ∧ … ∧ (0, a_k)` spans the orientation
of `ker G'(t, x)` given by `e ∧ o`. -/
theorem exists_timeFirst_wedge_of_slice (hf : B.IsScFredholmSection f)
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
    (hxs : x ∈ PX.smoothSet) (hne : (p.linSet f).Nonempty) (o : p.Or f hf)
    {G : (Fin 1 → unitInterval) × X → pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hG : (ivBundle B).IsScFredholmSection G) (hg : B.IsScFredholmSection (prodSlice G t))
    (hz0 : IsZeroAt (pullbackProj P Prod.snd) G (t, x)) (hx0 : IsZeroAt P (prodSlice G t) x)
    (hgL : B.IsLinSurjAt (prodSlice G t) x) (hGL : (ivBundle B).IsLinSurjAt G (t, x))
    (hmem : p.linZero hg hx0 ∈ p.linSet f)
    (hmem' : (p.ivPt b ht q₀).linZero hG hz0 ∈
      (p.ivPt b ht q₀).linSet (cubeLift (n := 1) f hf.isScSmooth.1))
    {k : ℕ} (hk : finrank ℝ (p.c.linKer (prodSlice G t) p.z) = k)
    (hk' : finrank ℝ ((p.ivPt b ht q₀).c.linKer G (p.ivPt b ht q₀).z) = k + 1)
    (a : Fin k → p.c.linKer (prodSlice G t) p.z) (hna : wedge a hk.symm ≠ 0)
    (ha : p.tangentOrOf hf hg hx0 hgL hmem o = rayOfNeZero ℝ _ hna) :
    ∃ (ν : (p.ivPt b ht q₀).c.linKer G (p.ivPt b ht q₀).z)
      (a' : Fin k → (p.ivPt b ht q₀).c.linKer G (p.ivPt b ht q₀).z)
      (hna' : wedge (Fin.cons ν a' : Fin (k + 1) →
        (p.ivPt b ht q₀).c.linKer G (p.ivPt b ht q₀).z) hk'.symm ≠ 0),
      ((ν.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).1 = fun _ => ivSign b) ∧
      (∀ l, ((a' l).1 : (Fin 1 → ℝ) × p.c.φ.model.E 0) = (0, (a l : p.c.φ.model.E 0))) ∧
      (p.ivPt b ht q₀).tangentOrOf hfc hG hz0 hGL hmem'
          (p.ivOrFirst₀ b ht q₀ hf hfc hxs hne o) = rayOfNeZero ℝ _ hna' := by
  have hfdN : FiniteDimensional ℝ (p.c.linKer (prodSlice G t) p.z) := by
    have := (p.isFredholm_of_mem_linSet hf _ hmem).finite_ker
    exact (kerEquivOfMap (p.linZero hg hx0) p.T.subtypeL Subtype.val_injective
      (p.map_ker_linZero hg hx0)).finiteDimensional
  have hfdN' : FiniteDimensional ℝ ((p.ivPt b ht q₀).c.linKer G (p.ivPt b ht q₀).z) :=
    Module.finite_of_finrank_pos (by rw [hk']; exact Nat.succ_pos k)
  have aux := fun (N' : Submodule ℝ ((Fin 1 → ℝ) × p.c.φ.model.E 0))
      (hfd : FiniteDimensional ℝ N') (hk' : finrank ℝ N' = k + 1)
      (hiff : ∀ w : (Fin 1 → ℝ) × p.c.φ.model.E 0, w.1 = 0 →
        (w ∈ N' ↔ w.2 ∈ p.c.linKer (prodSlice G t) p.z)) =>
    exists_timeFirst_coordinates (E₀ := p.c.φ.model.E 0)
      (N := p.c.linKer (prodSlice G t) p.z) (N' := N') hk hk' hiff (ivSign_ne_zero b) a hna
  obtain ⟨ν, a', hna', ι, ι', hν1, ha', hι₀, hι₁, hstd, hray⟩ :=
    aux ((p.ivPt b ht q₀).c.linKer G (p.ivPt b ht q₀).z) hfdN' hk'
      (p.mem_linKer_ivPt_iff_of_fst_eq_zero b ht q₀ hG hg hz0 hx0)
  exact ⟨ν, a', hna', hν1, ha', hray _
    ((p.pullOr_tangentOrOf_ivOrFirst₀_iff_of_slice b ht q₀ hf hfc hxs hne o hG hg hz0 hx0 hgL hGL
      hmem hmem' ι ι' hι₀ hι₁).2 (hstd _ ha))⟩

end ChartPoint

/-- **Frames of `ker G'(t, x)` with the `t`-direction first, in the chart point of the product
chart with a given lift** `z' = (χ_b(t), z)` of the base point: the statement of
`ChartPoint.exists_timeFirst_wedge_of_slice` for the orientation `ivOrLift`. -/
theorem exists_timeFirst_wedge_ivOrLift (b : Fin 1 → Bool) {c : StrongBundleChart PX P}
    (hc : B.IsChart c) {x : X} (hx : x ∈ c.φ.source) (z : c.φ.model.E 1)
    (hz : c.φ.model.E.toBase 1 z = c.φ x) {t : Fin 1 → unitInterval}
    (ht : t ∈ (chart b).source)
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))
    (hxc : ((t, x) : (Fin 1 → unitInterval) × X) ∈ (ivChart b c q₀).φ.source)
    (z' : (ivChart b c q₀).φ.model.E 1)
    (hz' : (ivChart b c q₀).φ.model.E.toBase 1 z' = (ivChart b c q₀).φ (t, x))
    (hzz : z' = ((chart b t : Fin 1 → ℝ), z)) (hf : B.IsScFredholmSection f)
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
    (hxs : x ∈ PX.smoothSet) (hne : ((chartPt c hc hx z hz).linSet f).Nonempty)
    (o : (chartPt c hc hx z hz).Or f hf)
    {G : (Fin 1 → unitInterval) × X → pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hG : (ivBundle B).IsScFredholmSection G) {g : X → Y} (hgs : prodSlice G t = g)
    (hg : B.IsScFredholmSection g)
    (hz0 : IsZeroAt (pullbackProj P Prod.snd) G (t, x)) (hx0 : IsZeroAt P g x)
    (hgL : B.IsLinSurjAt g x) (hGL : (ivBundle B).IsLinSurjAt G (t, x))
    (hmem : (chartPt c hc hx z hz).linZero hg hx0 ∈ (chartPt c hc hx z hz).linSet f)
    (hmem' : (chartPt (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀) hxc z'
        hz').linZero hG hz0 ∈
      (chartPt (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀) hxc z' hz').linSet
        (cubeLift (n := 1) f hf.isScSmooth.1))
    {k : ℕ} (hk : finrank ℝ (c.linKer g z) = k)
    (hk' : finrank ℝ ((ivChart b c q₀).linKer G z') = k + 1)
    (a : Fin k → c.linKer g z) (hna : wedge a hk.symm ≠ 0)
    (ha : (chartPt c hc hx z hz).tangentOrOf hf hg hx0 hgL hmem o = rayOfNeZero ℝ _ hna) :
    ∃ (ν : (ivChart b c q₀).linKer G z') (a' : Fin k → (ivChart b c q₀).linKer G z')
      (hna' : wedge (Fin.cons ν a' : Fin (k + 1) → (ivChart b c q₀).linKer G z') hk'.symm ≠ 0),
      ((ν.1 : (Fin 1 → ℝ) × c.φ.model.E 0).1 = fun _ => ivSign b) ∧
      (∀ l, ((a' l).1 : (Fin 1 → ℝ) × c.φ.model.E 0) = (0, (a l : c.φ.model.E 0))) ∧
      (chartPt (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀) hxc z'
          hz').tangentOrOf hfc hG hz0 hGL hmem'
          (ivOrLift b hc hx z hz ht q₀ hxc z' hz' hzz hf hfc hxs hne o) =
        rayOfNeZero ℝ _ hna' := by
  subst hzz
  subst hgs
  exact (chartPt c hc hx z hz).exists_timeFirst_wedge_of_slice b ht q₀ hf hfc hxs hne o hG hg hz0
    hx0 hgL hGL hmem hmem' hk hk' a hna ha

end IvFrames

end Polyfold
