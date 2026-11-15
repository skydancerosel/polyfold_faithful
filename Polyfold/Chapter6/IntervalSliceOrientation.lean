import Polyfold.Chapter6.IntervalEndOrientation
import Polyfold.Chapter6.KernelPathOrientation

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, p. 276:
**Remark 6.6.19** (preprint Remark 6.42, p. 230) and the proof of Theorem 6.7.1 (p. 278): the
orientation `e ∧ o` of `S_F ⊆ [0, 1] × X` at a point `(t, x)` and the orientation of the slice
`S_{F_t} ⊆ X`, `F_t = F(t, ·)`, for a section `F = f̃ + S` that need not be constant in `t`.

# The orientation `e ∧ o` and the slices, for a general section over `[0, 1] × X`

## What is formalized

* `ChartPoint.linAt_ivPt_slice`: in the product chart `χ_b × φ` the linearization of a section
  `G` over `[0, 1] × X` at `(t, x)`, on the vectors `(0, v)`, is the linearization of the slice
  `G(t, ·)` at `x` (the chain rule for `u ↦ (χ_b(t), u)`).
* `ChartPoint.linZero_ivPt_eq_ivLin_of_fst_eq_zero`: the same for the linearizations at a zero.
* `ChartPoint.exists_shear_linZero_ivPt`: for `G_t'(x)` onto there is `n₀ = (0, v₀)` with
  `G'(t, x) w = (G_t'(x))^ (w + τ(w) n₀)`, `τ(w)` the component of `w` in the direction of
  increasing `t`; so `ker G'(t, x) = \{w − τ(w) n₀ \mid w ∈ ℝ × ker G_t'(x)\}`.
* `ChartPoint.pullOr_tangentOrOf_ivOrFirst₀_iff_of_slice`: at a zero `(t, x)` of `G` with
  `G_t'(x)` onto, in coordinates `ι̂` of `ker G'(t, x)` with `ι̂(0, w) = (0, ι w)` and
  `ι̂(s, 0)` of `t`-component `± s` (sign of the chart: `s` is the direction of increasing `t`),
  the orientation `e ∧ o` of `ker G'(t, x)` is the standard orientation of `ℝ^{k+1}` iff the
  orientation of `ker G_t'(x)` given by `o` is the standard orientation of `ℝ^k` in `ι`.

At `t = 1` the vector `ι̂(1, 0)` points out of `[0, 1] × X` and at `t = 0` into it, so with the
outward normal first the end `\{1\} × S_{F_1}` of `S_F` carries the orientation given by `o` and
the end `\{0\} × S_{F_0}` the opposite one.
-/

open Set Filter Topology Manifold Module
open scoped ContDiff

noncomputable section

namespace Polyfold

open StrongRetr UnitCube

universe u v

/-- `consE s w = s · consE 1 0 + consE 0 w`. -/
theorem consE_eq_smul_add {k : ℕ} (s : ℝ) (w : EuclideanSpace ℝ (Fin k)) :
    consE s w = s • consE 1 (0 : EuclideanSpace ℝ (Fin k)) + consE 0 w := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp

/-- `a − b = a + c` for `b = −c`. -/
theorem sub_eq_add_of_eq_neg_right {V : Type*} [AddGroup V] {a b c : V} (h : b = -c) :
    a - b = a + c := by
  rw [h, sub_neg_eq_add]

/-- **Coordinates of a sheared kernel**: let `e : N₀ ≅ N₁` be `(σ, v) ↦ (σ, v + a σ₀ ν₂)` on
subspaces of `ℝ¹ × V` (`a² = 1`), and `ι̂ : ℝ^{k+1} ≅ N₁` with `ι̂(0, w) = (0, ι w)` and
`ι̂(1, 0) = (a, ν₂)`.  Then `e⁻¹ ι̂ (s, w) = (a s, ι w)`. -/
theorem shear_coords {V : Type*} [AddCommGroup V] [Module ℝ V] {k : ℕ} (a : ℝ) (ha : a * a = 1)
    {N₀ N₁ : Submodule ℝ ((Fin 1 → ℝ) × V)} (e : N₀ ≃ₗ[ℝ] N₁) (ν₂ : V)
    (he : ∀ y : N₀, ((e y : N₁) : (Fin 1 → ℝ) × V) =
      ((y : (Fin 1 → ℝ) × V).1, (y : (Fin 1 → ℝ) × V).2 + (a * (y : (Fin 1 → ℝ) × V).1 0) • ν₂))
    (ι : EuclideanSpace ℝ (Fin k) → V) (ι' : EuclideanSpace ℝ (Fin (k + 1)) ≃ₗ[ℝ] N₁)
    (hι₀ : ∀ w, ((ι' (consE 0 w) : N₁) : (Fin 1 → ℝ) × V) = (0, ι w))
    (hι₁ : ((ι' (consE 1 (0 : EuclideanSpace ℝ (Fin k))) : N₁) : (Fin 1 → ℝ) × V) =
      ((fun _ => a), ν₂)) (s : ℝ) (w : EuclideanSpace ℝ (Fin k)) :
    (((ι'.trans e.symm) (consE s w) : N₀) : (Fin 1 → ℝ) × V) = ((fun _ => a * s), ι w) := by
  have hey : e ((ι'.trans e.symm) (consE s w)) = ι' (consE s w) := e.apply_symm_apply _
  have h1 := he ((ι'.trans e.symm) (consE s w))
  rw [hey] at h1
  have h2 : ((ι' (consE s w) : N₁) : (Fin 1 → ℝ) × V) =
      s • ((fun _ => a : Fin 1 → ℝ), ν₂) + ((0 : Fin 1 → ℝ), ι w) := by
    rw [consE_eq_smul_add, map_add, map_smul, ← hι₁, ← hι₀ w]
    rfl
  rw [h2] at h1
  have h1a : (((ι'.trans e.symm) (consE s w) : N₀) : (Fin 1 → ℝ) × V).1 = fun _ => a * s := by
    refine (congrArg Prod.fst h1).symm.trans ?_
    funext i
    change s * a + 0 = a * s
    rw [add_zero, mul_comm]
  have h1b : s • ν₂ + ι w = (((ι'.trans e.symm) (consE s w) : N₀) : (Fin 1 → ℝ) × V).2 +
      (a * (((ι'.trans e.symm) (consE s w) : N₀) : (Fin 1 → ℝ) × V).1 0) • ν₂ :=
    congrArg Prod.snd h1
  rw [h1a] at h1b
  have hss : a * (a * s) = s := by rw [← mul_assoc, ha, one_mul]
  rw [hss] at h1b
  exact Prod.ext h1a (add_right_cancel ((add_comm _ _).trans h1b)).symm

section IvSlice

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] {f : X → Y}

namespace ChartPoint

variable {x : X} (p : ChartPoint B x) (b : Fin 1 → Bool) {t : Fin 1 → unitInterval}
  (ht : t ∈ (chart b).source)
  (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))

/-- **The linearization on the slice directions, in the product chart point of `[0, 1] × X`**:
`Lin_G(t, x)(0, v) = Lin_{G(t, ·)}(x) v`, at every `t ∈ [0, 1]`.  The chain rule for
`Ĝ ∘ (id × r)` composed with `u ↦ (χ_b(t), u)`. -/
theorem linAt_ivPt_slice
    {G : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hG : (ivBundle B).IsScSmoothSection G) (v : ↥(p.ivPt b ht q₀).T)
    (hv : (v.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).1 = 0) :
    linAt (p.ivPt b ht q₀).c.U (p.ivPt b ht q₀).c.R ((p.ivPt b ht q₀).c.principal G)
        (p.ivPt b ht q₀).z v =
      linAt p.c.U p.c.R (p.c.principal (prodSlice G t)) p.z (p.ivT b ht q₀ v).1 := by
  set pc := ivChart b p.c q₀ with hpc
  have hH : IsSc1 pc.U (pc.principal G ∘ r pc.R) :=
    hG.isSc1_principal_comp_r (isChart_ivChart b p.isChart q₀)
  set a : Fin 1 → ℝ := (chart b t : Fin 1 → ℝ) with ha
  set ι : p.c.φ.model.E 0 → pc.φ.model.E 0 :=
    scPair (E := p.c.φ.model.E) (F := rnSc 1) (G := p.c.φ.model.E) (fun _ => a) _root_.id with hι
  have hdom := p.c.relOpen.isScDomain
  have hιs : IsScSmooth (E := p.c.φ.model.E) (F := pc.φ.model.E) p.c.U ι :=
    IsScSmooth.scPair hdom (isScSmooth_const_of_mem_smooth hdom (mem_smooth_rnSc a))
      (isScSmooth_id hdom)
  have hι1 : IsSc1 (E := p.c.φ.model.E) (F := pc.φ.model.E) p.c.U ι := hιs.isSc1
  have hmaps : MapsTo ι p.c.U pc.U := fun w hw =>
    show ((a, w) : (Fin 1 → ℝ) × p.c.φ.model.E 0) ∈ (chart b).model.O ×ˢ p.c.U from
      ⟨chart_mem_modelO ht, hw⟩
  have hz : p.z ∈ p.c.φ.model.E.lvlSet p.c.U 1 := p.mem_U
  have hchain := scDeriv_comp_apply' p.c.relOpen pc.relOpen hι1 hH hmaps hz
    (v.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).2
  have hlvl : levelMap (E := p.c.φ.model.E) (F := pc.φ.model.E) ι 1 p.z =
      (p.ivPt b ht q₀).z := by
    apply pc.φ.model.E.toBase_injective 1
    refine (IsSc0.toBase_levelMap (hιs 0) (x := p.z) hz).trans ?_
    exact (p.ivPt_toBase b ht q₀).symm
  have hDι : scDeriv (E := p.c.φ.model.E) (F := pc.φ.model.E) p.c.U ι p.z =
      ContinuousLinearMap.inr ℝ (Fin 1 → ℝ) (p.c.φ.model.E 0) :=
    scDeriv_eq_of_hasFDerivAt p.c.relOpen hι1 hz
      ((hasFDerivAt_const a _).prodMk (hasFDerivAt_id _))
  rw [hlvl, hDι] at hchain
  have hHι : (pc.principal G ∘ r pc.R) ∘ ι = p.c.principal (prodSlice G t) ∘ r p.c.R := by
    funext w
    change (p.c (G ((chart b).symm a, p.c.φ.symm (r p.c.R w))).1.2).2 =
      (p.c (G (t, p.c.φ.symm (r p.c.R w))).1.2).2
    rw [(chart b).symm_apply_apply ht]
  rw [hHι] at hchain
  have hv' : (v.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0) =
      ContinuousLinearMap.inr ℝ (Fin 1 → ℝ) (p.c.φ.model.E 0)
        (v.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).2 := Prod.ext hv rfl
  change scDeriv pc.U (pc.principal G ∘ r pc.R) (p.ivPt b ht q₀).z
      (v.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0) =
    scDeriv p.c.U (p.c.principal (prodSlice G t) ∘ r p.c.R) p.z
      (v.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).2
  conv_lhs => rw [hv']
  exact hchain

/-- **`G'(t, x)(0, v) = G_t'(x) v`** at a zero `(t, x)` of `G`: on the vectors with vanishing
`t`-component the linearization of `G` is `(G(t, ·)'(x))^`. -/
theorem linZero_ivPt_eq_ivLin_of_fst_eq_zero
    {G : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hG : (ivBundle B).IsScFredholmSection G) (hg : B.IsScFredholmSection (prodSlice G t))
    (hz0 : IsZeroAt (pullbackProj P Prod.snd) G (t, x)) (hx0 : IsZeroAt P (prodSlice G t) x)
    (w : ↥(p.ivPt b ht q₀).T) (hw : (w.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).1 = 0) :
    (p.ivPt b ht q₀).linZero hG hz0 w = p.ivLin b ht q₀ (p.linZero hg hx0) w := by
  refine Subtype.ext ?_
  rw [coe_linZero]
  exact (p.linAt_ivPt_slice b ht q₀ hG.isScSmooth w hw).trans
    ((p.coe_linZero hg hx0 _).symm.trans (p.coe_ivLin_apply b ht q₀ (p.linZero hg hx0) w).symm)

/-- `L̂` depends on the `X`-component only. -/
theorem ivLin_eq_of_snd_eq (L : ↥p.T →L[ℝ] ↥p.K) {u u' : ↥(p.ivPt b ht q₀).T}
    (h : (u.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).2 = (u'.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).2) :
    p.ivLin b ht q₀ L u = p.ivLin b ht q₀ L u' := by
  refine Subtype.ext ?_
  rw [coe_ivLin_apply, coe_ivLin_apply]
  have h' : (p.ivT b ht q₀ u).1 = (p.ivT b ht q₀ u').1 := Subtype.ext h
  rw [h']

/-- **The shear between `G'(t, x)` and `(G_t'(x))^`**: let `T₁ : ℝ × T_x → Y_x` agree with `L̂`
on the vectors `(0, v)`, and let `ν ∈ ker T₁` have the `t`-component of the direction of
increasing `t` (`± 1` in the chart).  Then `T₁ w = L̂ (w + N w)` with
`N w = τ(w) · (0, −ν₂)`, `τ(w)` the component of `w` in the direction of increasing `t`; and
`N² = 0`. -/
theorem exists_shear_of_eq_on_slice (L : ↥p.T →L[ℝ] ↥p.K)
    (T₁ : ↥(p.ivPt b ht q₀).T →L[ℝ] ↥(p.ivPt b ht q₀).K)
    (hE : ∀ w : ↥(p.ivPt b ht q₀).T, (w.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).1 = 0 →
      T₁ w = p.ivLin b ht q₀ L w)
    (ν : ↥(p.ivPt b ht q₀).T) (hν : T₁ ν = 0)
    (hν1 : (ν.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).1 = fun _ => ivSign b) :
    ∃ N : ↥(p.ivPt b ht q₀).T →L[ℝ] ↥(p.ivPt b ht q₀).T, (∀ w, N (N w) = 0) ∧
      (∀ w, T₁ w = p.ivLin b ht q₀ L (w + N w)) ∧
      ∀ w : ↥(p.ivPt b ht q₀).T, ((N w).1 : (Fin 1 → ℝ) × p.c.φ.model.E 0) =
        (0, -((ivSign b * (w.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).1 0) •
          (ν.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).2)) := by
  let n₀ : ↥(p.ivPt b ht q₀).T :=
    ⟨((0 : Fin 1 → ℝ), -(ν.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).2),
      (p.mem_ivPt_T_iff b ht q₀ _).2 (neg_mem ((p.mem_ivPt_T_iff b ht q₀ _).1 ν.2))⟩
  let τ : ↥(p.ivPt b ht q₀).T →L[ℝ] ℝ :=
    ivSign b • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).comp
      ((ContinuousLinearMap.fst ℝ (Fin 1 → ℝ) (p.c.φ.model.E 0)).comp
        (p.ivPt b ht q₀).T.subtypeL))
  have hτ : ∀ w : ↥(p.ivPt b ht q₀).T,
      τ w = ivSign b * (w.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).1 0 := fun w => rfl
  have hτn : τ n₀ = 0 := by
    rw [hτ]
    exact mul_zero _
  refine ⟨τ.smulRight n₀, fun w => ?_, fun w => ?_, fun w => ?_⟩
  · change τ (τ w • n₀) • n₀ = 0
    rw [map_smul, hτn, smul_zero, zero_smul]
  · have hw' : ((w - τ w • ν : ↥(p.ivPt b ht q₀).T).1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).1 = 0 := by
      funext i
      obtain rfl : i = 0 := Subsingleton.elim _ _
      change (w.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).1 0 -
        τ w * (ν.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).1 0 = 0
      rw [hν1, hτ]
      linear_combination (-(w.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).1 0) * ivSign_mul_self b
    have h1 : T₁ w = T₁ (w - τ w • ν) := by
      rw [map_sub, map_smul, hν, smul_zero, sub_zero]
    rw [h1, hE _ hw']
    refine p.ivLin_eq_of_snd_eq b ht q₀ L ?_
    change (w.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).2 -
        τ w • (ν.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).2 =
      (w.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).2 +
        τ w • (-(ν.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).2)
    rw [smul_neg, sub_eq_add_neg]
  · change (τ w • ((0 : Fin 1 → ℝ), -(ν.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).2) :
      (Fin 1 → ℝ) × p.c.φ.model.E 0) = _
    rw [hτ, Prod.smul_mk, smul_zero, smul_neg]
    rfl

/-- `L̂` is onto when `L` is. -/
theorem ivLin_surjective {L : ↥p.T →L[ℝ] ↥p.K} (hL : Function.Surjective L) :
    Function.Surjective (p.ivLin b ht q₀ L) := fun y => by
  obtain ⟨v, hv⟩ := hL (p.ivK b ht q₀ y)
  refine ⟨(p.ivT b ht q₀).symm (v, 0), (p.ivK b ht q₀).injective ?_⟩
  rw [← p.ivLin_conj b ht q₀ L, ContinuousLinearEquiv.apply_symm_apply, extOp_apply, hv]

/-- `shearMapEquiv` for the shear of `exists_shear_of_eq_on_slice`, in the coordinates of
`ℝ¹ × E₀`: `(σ, v) ↦ (σ, v + τ ν₂)`, `τ = ± σ` the component in the direction of increasing
`t`. -/
theorem coe_shearMapEquiv_ivPt {T₀ T₁ : ↥(p.ivPt b ht q₀).T →L[ℝ] ↥(p.ivPt b ht q₀).K}
    (N : ↥(p.ivPt b ht q₀).T →L[ℝ] ↥(p.ivPt b ht q₀).T) (hNN : ∀ w, N (N w) = 0)
    (hT : ∀ w, T₁ w = T₀ (w + N w)) (ν₂ : p.c.φ.model.E 0)
    (hNform : ∀ w : ↥(p.ivPt b ht q₀).T, ((N w).1 : (Fin 1 → ℝ) × p.c.φ.model.E 0) =
      (0, -((ivSign b * (w.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).1 0) • ν₂)))
    {N₀ N₁ : Submodule ℝ ((Fin 1 → ℝ) × p.c.φ.model.E 0)}
    (hN₀ : (LinearMap.ker (T₀ : ↥(p.ivPt b ht q₀).T →ₗ[ℝ] ↥(p.ivPt b ht q₀).K)).map
      (p.ivIncl b ht q₀ : ↥(p.ivPt b ht q₀).T →ₗ[ℝ] (Fin 1 → ℝ) × p.c.φ.model.E 0) = N₀)
    (hN₁ : (LinearMap.ker (T₁ : ↥(p.ivPt b ht q₀).T →ₗ[ℝ] ↥(p.ivPt b ht q₀).K)).map
      (p.ivIncl b ht q₀ : ↥(p.ivPt b ht q₀).T →ₗ[ℝ] (Fin 1 → ℝ) × p.c.φ.model.E 0) = N₁)
    (y : N₀) :
    ((shearMapEquiv N hNN hT (p.ivIncl b ht q₀) (p.ivIncl_injective b ht q₀) hN₀ hN₁ y : N₁) :
        (Fin 1 → ℝ) × p.c.φ.model.E 0) =
      ((y : (Fin 1 → ℝ) × p.c.φ.model.E 0).1, (y : (Fin 1 → ℝ) × p.c.φ.model.E 0).2 +
        (ivSign b * (y : (Fin 1 → ℝ) × p.c.φ.model.E 0).1 0) • ν₂) := by
  have hsurj := (kerEquivOfMap T₀ (p.ivIncl b ht q₀) (p.ivIncl_injective b ht q₀)
    hN₀).surjective y
  obtain ⟨v, hv⟩ := hsurj
  have h1 := coe_shearMapEquiv N hNN hT (p.ivIncl b ht q₀) (p.ivIncl_injective b ht q₀) hN₀ hN₁ v
  have h2 := coe_kerEquivOfMap T₀ (p.ivIncl b ht q₀) (p.ivIncl_injective b ht q₀) hN₀ v
  have hy : (y : (Fin 1 → ℝ) × p.c.φ.model.E 0) =
      ((v.1 : ↥(p.ivPt b ht q₀).T).1 : (Fin 1 → ℝ) × p.c.φ.model.E 0) :=
    (congrArg Subtype.val hv).symm.trans h2
  have h3 := hNform v.1
  have h3a : ((N v.1 : ↥(p.ivPt b ht q₀).T).1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).1 = 0 :=
    congrArg Prod.fst h3
  have h3b : ((N v.1 : ↥(p.ivPt b ht q₀).T).1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).2 =
      -((ivSign b * ((v.1 : ↥(p.ivPt b ht q₀).T).1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).1 0) • ν₂) :=
    congrArg Prod.snd h3
  refine ((congrArg (fun y' : N₀ => ((shearMapEquiv N hNN hT (p.ivIncl b ht q₀)
    (p.ivIncl_injective b ht q₀) hN₀ hN₁ y' : N₁) : (Fin 1 → ℝ) × p.c.φ.model.E 0))
    hv).symm.trans h1).trans ?_
  rw [hy]
  refine Prod.ext ?_ ?_
  · change ((v.1 : ↥(p.ivPt b ht q₀).T).1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).1 -
      ((N v.1 : ↥(p.ivPt b ht q₀).T).1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).1 =
      ((v.1 : ↥(p.ivPt b ht q₀).T).1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).1
    rw [h3a, sub_zero]
  · change ((v.1 : ↥(p.ivPt b ht q₀).T).1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).2 -
      ((N v.1 : ↥(p.ivPt b ht q₀).T).1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).2 =
      ((v.1 : ↥(p.ivPt b ht q₀).T).1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).2 +
        (ivSign b * ((v.1 : ↥(p.ivPt b ht q₀).T).1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).1 0) • ν₂
    exact sub_eq_add_of_eq_neg_right h3b

/-- **The operator form of the end identity**: for `T₁ ∈ Lin(f̃, (t, x))` onto with
`T₁ = L̂ (1 + N)`, `N` the shear of `exists_shear_of_eq_on_slice`, `L ∈ Lin(f, x)` onto, and
coordinates `ι̂` of `ker T₁` with `ι̂(0, w) = (0, ι w)`, `ι̂(1, 0) = (± 1, ν₂)`: `e ∧ o` on
`ker T₁` is the standard orientation iff `o` on `ker L` is. -/
theorem pullOr_surjRay_ivOrFirst₀_iff_of_shear (hf : B.IsScFredholmSection f)
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
    (hxs : x ∈ PX.smoothSet) (hne : (p.linSet f).Nonempty) (o : p.Or f hf)
    {L : ↥p.T →L[ℝ] ↥p.K} (hmem : L ∈ p.linSet f) (hLs : Function.Surjective L)
    {N₀ : Submodule ℝ (p.c.φ.model.E 0)}
    (hN₀ : (LinearMap.ker (L : ↥p.T →ₗ[ℝ] ↥p.K)).map
      (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0) = N₀)
    {T₁ : ↥(p.ivPt b ht q₀).T →L[ℝ] ↥(p.ivPt b ht q₀).K}
    (hT₁m : T₁ ∈ (p.ivPt b ht q₀).linSet (cubeLift (n := 1) f hf.isScSmooth.1))
    (hT₁s : Function.Surjective T₁)
    (N : ↥(p.ivPt b ht q₀).T →L[ℝ] ↥(p.ivPt b ht q₀).T) (hNN : ∀ w, N (N w) = 0)
    (hT : ∀ w, T₁ w = p.ivLin b ht q₀ L (w + N w)) (ν₂ : p.c.φ.model.E 0)
    (hNform : ∀ w : ↥(p.ivPt b ht q₀).T, ((N w).1 : (Fin 1 → ℝ) × p.c.φ.model.E 0) =
      (0, -((ivSign b * (w.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).1 0) • ν₂)))
    {N' : Submodule ℝ ((Fin 1 → ℝ) × p.c.φ.model.E 0)}
    (hN' : (LinearMap.ker (T₁ : ↥(p.ivPt b ht q₀).T →ₗ[ℝ] ↥(p.ivPt b ht q₀).K)).map
      (p.ivIncl b ht q₀ : ↥(p.ivPt b ht q₀).T →ₗ[ℝ] (Fin 1 → ℝ) × p.c.φ.model.E 0) = N')
    {N'₀ : Submodule ℝ ((Fin 1 → ℝ) × p.c.φ.model.E 0)}
    (hN'₀ : (LinearMap.ker ((p.ivLin b ht q₀ L : ↥(p.ivPt b ht q₀).T →L[ℝ]
      ↥(p.ivPt b ht q₀).K) : ↥(p.ivPt b ht q₀).T →ₗ[ℝ] ↥(p.ivPt b ht q₀).K)).map
      (p.ivIncl b ht q₀ : ↥(p.ivPt b ht q₀).T →ₗ[ℝ] (Fin 1 → ℝ) × p.c.φ.model.E 0) = N'₀)
    {k : ℕ} (ι : EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ] N₀)
    (ι' : EuclideanSpace ℝ (Fin (k + 1)) ≃ₗ[ℝ] N')
    (hι₀ : ∀ w, ((ι' (consE 0 w) : N') : (Fin 1 → ℝ) × p.c.φ.model.E 0) =
      (0, (ι w : p.c.φ.model.E 0)))
    (hι₁ : ((ι' (consE 1 (0 : EuclideanSpace ℝ (Fin k))) : N') :
      (Fin 1 → ℝ) × p.c.φ.model.E 0) = ((fun _ => ivSign b), ν₂)) :
    pullOr finrank_euclideanSpace_fin ι'
        (surjRay hT₁s (p.ivIncl b ht q₀) (p.ivIncl_injective b ht q₀) hN'
          ((p.ivPt b ht q₀).orEquivRay hfc hT₁m (p.ivOrFirst₀ b ht q₀ hf hfc hxs hne o))) =
        stdOrientation (k + 1) ↔
      pullOr finrank_euclideanSpace_fin ι
        (surjRay hLs p.T.subtypeL Subtype.val_injective hN₀ (p.orEquivRay hf hmem o)) =
        stdOrientation k := by
  have hT₀m := p.ivLin_mem_linSet_cubeLift b ht q₀ hf hxs hmem
  have hT₀s := p.ivLin_surjective b ht q₀ hLs
  have hFr := p.isFredholm_of_mem_linSet hf _ hmem
  have hFr' := (p.ivPt b ht q₀).isFredholm_of_mem_linSet hfc _ hT₀m
  have hι'₀ := shear_coords (ivSign b) (ivSign_mul_self b)
    (shearMapEquiv N hNN hT (p.ivIncl b ht q₀) (p.ivIncl_injective b ht q₀) hN'₀ hN') ν₂
    (p.coe_shearMapEquiv_ivPt b ht q₀ N hNN hT ν₂ hNform hN'₀ hN')
    (fun w => (ι w : p.c.φ.model.E 0)) ι' hι₀ hι₁
  have key1 := surjRay_shearMapEquiv ((p.ivPt b ht q₀).convex_linSet hfc)
    (p.ivOrFirst₀ b ht q₀ hf hfc hxs hne o) hT₀m hT₁m hT₀s hT₁s N hNN hT (p.ivIncl b ht q₀)
    (p.ivIncl_injective b ht q₀) hN'₀ hN'
  have hval : (p.ivOrFirst₀ b ht q₀ hf hfc hxs hne o) ⟨_, hT₀m⟩ =
      Module.Ray.map (extConjDetFirst (p.ivT b ht q₀) (p.ivK b ht q₀) hFr hFr')
        (p.orEquivRay hf hmem o) :=
    p.ivOrFirst₀_apply b ht q₀ hf hfc hxs hne o _ hmem
  have key2 := pullOr_eq_of_comp (finrank_euclideanSpace_fin (n := k + 1))
    (L := ι'.trans (shearMapEquiv N hNN hT (p.ivIncl b ht q₀) (p.ivIncl_injective b ht q₀)
      hN'₀ hN').symm) (L' := ι')
    (T := shearMapEquiv N hNN hT (p.ivIncl b ht q₀) (p.ivIncl_injective b ht q₀) hN'₀ hN')
    (fun v => (LinearEquiv.apply_symm_apply _ _).symm)
    (surjRay hT₀s (p.ivIncl b ht q₀) (p.ivIncl_injective b ht q₀) hN'₀
      ((p.ivOrFirst₀ b ht q₀ hf hfc hxs hne o) ⟨_, hT₀m⟩))
  have key3 := pullOr_surjRay_extConjDetFirst_iff_of_smul (ivSign b) (ivSign_ne_zero b)
    (p.ivT b ht q₀) (p.ivK b ht q₀) hFr hFr' hLs hT₀s p.T.subtypeL Subtype.val_injective
    (p.ivIncl b ht q₀) (p.ivIncl_injective b ht q₀) (fun v => Prod.ext (by
      have h : ivSign b • ivSign b • Prod.fst (α := Fin 1 → ℝ) (β := p.c.φ.model.E 0) v.1 =
          Prod.fst (α := Fin 1 → ℝ) (β := p.c.φ.model.E 0) v.1 := by
        rw [smul_smul, ivSign_mul_self, one_smul]
      exact h.symm) rfl) hN₀ hN'₀ ι
    (ι'.trans (shearMapEquiv N hNN hT (p.ivIncl b ht q₀) (p.ivIncl_injective b ht q₀)
      hN'₀ hN').symm) hι'₀ (p.orEquivRay hf hmem o)
  refine Iff.trans (iff_of_eq (congrArg (· = stdOrientation (k + 1)) ?_)) key3
  refine (congrArg (pullOr finrank_euclideanSpace_fin ι') key1).trans (key2.trans ?_)
  exact congrArg (fun r => pullOr finrank_euclideanSpace_fin
    (ι'.trans (shearMapEquiv N hNN hT (p.ivIncl b ht q₀) (p.ivIncl_injective b ht q₀)
      hN'₀ hN').symm)
    (surjRay hT₀s (p.ivIncl b ht q₀) (p.ivIncl_injective b ht q₀) hN'₀ r)) hval

/-- **The orientation `e ∧ o` on `ker G'(t, x)` and the orientation of the slice** (2021 Remark
6.6.19, p. 276, and the proof of Theorem 6.7.1, p. 278), for a section `G` over `[0, 1] × X`
that need not be constant in `t`: let `(t, x)` be a zero of `G` with `G'(t, x)` onto and in
`Lin(f̃, (t, x))`, such that the slice `g = G(t, ·)` has `g'(x)` onto and in `Lin(f, x)`.  Let
`ι : ℝ^k ≅ ker g'(x)` and `ι̂ : ℝ^{k+1} ≅ ker G'(t, x)` be coordinates with `ι̂(0, w) = (0, ι w)`
and `ι̂(1, 0)` of `t`-component `± 1` in the chart `χ_b × φ`, the sign that of `χ_b` (the
direction of increasing `t`).  Then the orientation of `ker G'(t, x)` given by `e ∧ o` is the
standard orientation of `ℝ^{k+1}` iff the orientation of `ker g'(x)` given by `o` is the standard
orientation of `ℝ^k`.  At `t = 1` the vector `ι̂(1, 0)` points out of `[0, 1] × X`, at `t = 0`
into it. -/
theorem pullOr_tangentOrOf_ivOrFirst₀_iff_of_slice (hf : B.IsScFredholmSection f)
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
    (hxs : x ∈ PX.smoothSet) (hne : (p.linSet f).Nonempty) (o : p.Or f hf)
    {G : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hG : (ivBundle B).IsScFredholmSection G) (hg : B.IsScFredholmSection (prodSlice G t))
    (hz0 : IsZeroAt (pullbackProj P Prod.snd) G (t, x)) (hx0 : IsZeroAt P (prodSlice G t) x)
    (hgL : B.IsLinSurjAt (prodSlice G t) x) (hGL : (ivBundle B).IsLinSurjAt G (t, x))
    (hmem : p.linZero hg hx0 ∈ p.linSet f)
    (hmem' : (p.ivPt b ht q₀).linZero hG hz0 ∈
      (p.ivPt b ht q₀).linSet (cubeLift (n := 1) f hf.isScSmooth.1))
    {k : ℕ} (ι : EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ] p.c.linKer (prodSlice G t) p.z)
    (ι' : EuclideanSpace ℝ (Fin (k + 1)) ≃ₗ[ℝ]
      (p.ivPt b ht q₀).c.linKer G (p.ivPt b ht q₀).z)
    (hι₀ : ∀ w, ((ι' (consE 0 w)).1 : (Fin 1 → ℝ) × p.c.φ.model.E 0) =
      (0, (ι w : p.c.φ.model.E 0)))
    (hι₁ : ((ι' (consE 1 (0 : EuclideanSpace ℝ (Fin k)))).1 :
      (Fin 1 → ℝ) × p.c.φ.model.E 0).1 = fun _ => ivSign b) :
    pullOr finrank_euclideanSpace_fin ι'
        ((p.ivPt b ht q₀).tangentOrOf hfc hG hz0 hGL hmem'
          (p.ivOrFirst₀ b ht q₀ hf hfc hxs hne o)) = stdOrientation (k + 1) ↔
      pullOr finrank_euclideanSpace_fin ι (p.tangentOrOf hf hg hx0 hgL hmem o) =
        stdOrientation k := by
  have hLs := p.linZero_surjective hg hx0 hgL
  have aux : ∀ (T₁ : ↥(p.ivPt b ht q₀).T →L[ℝ] ↥(p.ivPt b ht q₀).K)
      (_ : ∀ w : ↥(p.ivPt b ht q₀).T, (w.1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).1 = 0 →
        T₁ w = p.ivLin b ht q₀ (p.linZero hg hx0) w)
      (hT₁m : T₁ ∈ (p.ivPt b ht q₀).linSet (cubeLift (n := 1) f hf.isScSmooth.1))
      (hT₁s : Function.Surjective T₁) (N' : Submodule ℝ ((Fin 1 → ℝ) × p.c.φ.model.E 0))
      (hN' : (LinearMap.ker ((T₁ : ↥(p.ivPt b ht q₀).T →L[ℝ] ↥(p.ivPt b ht q₀).K) :
        ↥(p.ivPt b ht q₀).T →ₗ[ℝ] ↥(p.ivPt b ht q₀).K)).map
          (p.ivIncl b ht q₀ : ↥(p.ivPt b ht q₀).T →ₗ[ℝ] (Fin 1 → ℝ) × p.c.φ.model.E 0) = N')
      (ι' : EuclideanSpace ℝ (Fin (k + 1)) ≃ₗ[ℝ] N')
      (_ : ∀ w, ((ι' (consE 0 w) : N') : (Fin 1 → ℝ) × p.c.φ.model.E 0) =
        (0, (ι w : p.c.φ.model.E 0)))
      (_ : ((ι' (consE 1 (0 : EuclideanSpace ℝ (Fin k))) : N') :
        (Fin 1 → ℝ) × p.c.φ.model.E 0).1 = fun _ => ivSign b),
      (pullOr finrank_euclideanSpace_fin ι'
          (surjRay hT₁s (p.ivIncl b ht q₀) (p.ivIncl_injective b ht q₀) hN'
            ((p.ivPt b ht q₀).orEquivRay hfc hT₁m (p.ivOrFirst₀ b ht q₀ hf hfc hxs hne o))) =
          stdOrientation (k + 1) ↔
        pullOr finrank_euclideanSpace_fin ι
          (surjRay hLs p.T.subtypeL Subtype.val_injective
            (p.map_ker_linZero hg hx0) (p.orEquivRay hf hmem o)) = stdOrientation k) := by
    intro T₁ hE hT₁m hT₁s N' hN' ι' hι₀' hι₁'
    have hsurj := (kerEquivOfMap T₁ (p.ivIncl b ht q₀) (p.ivIncl_injective b ht q₀)
      hN').surjective (ι' (consE 1 (0 : EuclideanSpace ℝ (Fin k))))
    obtain ⟨ν', hν'1⟩ := hsurj
    have hνker : T₁ ν'.1 = 0 := LinearMap.mem_ker.1 ν'.2
    have hνeq : ((ν'.1 : ↥(p.ivPt b ht q₀).T).1 : (Fin 1 → ℝ) × p.c.φ.model.E 0) =
        ((ι' (consE 1 (0 : EuclideanSpace ℝ (Fin k))) : N') :
          (Fin 1 → ℝ) × p.c.φ.model.E 0) :=
      (coe_kerEquivOfMap T₁ (p.ivIncl b ht q₀) (p.ivIncl_injective b ht q₀) hN' ν').symm.trans
        (congrArg Subtype.val hν'1)
    have hν1 : ((ν'.1 : ↥(p.ivPt b ht q₀).T).1 : (Fin 1 → ℝ) × p.c.φ.model.E 0).1 =
        fun _ => ivSign b := (congrArg Prod.fst hνeq).trans hι₁'
    have hsh := p.exists_shear_of_eq_on_slice b ht q₀ (p.linZero hg hx0) T₁ hE ν'.1 hνker hν1
    obtain ⟨N, hNN, hT, hNform⟩ := hsh
    exact p.pullOr_surjRay_ivOrFirst₀_iff_of_shear b ht q₀ hf hfc hxs hne o hmem hLs
      (p.map_ker_linZero hg hx0) hT₁m hT₁s N hNN hT _ hNform hN' rfl ι ι' hι₀'
      (Prod.ext hι₁' (congrArg Prod.snd hνeq).symm)
  exact aux _ (p.linZero_ivPt_eq_ivLin_of_fst_eq_zero b ht q₀ hG hg hz0 hx0) hmem'
    ((p.ivPt b ht q₀).linZero_surjective hG hz0 hGL) _
    ((p.ivPt b ht q₀).map_ker_linZero hG hz0) ι' hι₀ hι₁

end ChartPoint

end IvSlice

end Polyfold
