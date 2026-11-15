import Polyfold.Chapter6.IntervalEndGeneralPosition
import Polyfold.Chapter6.IntervalSliceFrames
import Polyfold.Chapter6.InvariantSingle

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6–6.7, pp. 275–278:
**Theorem 6.6.18** (preprint Theorem 6.41), **Remark 6.6.19** (preprint Remark 6.42) and the
proof of **Theorem 6.7.1**: the ends `S_{F_0}`, `S_{F_1}` of the cobordism `S_F ⊆ [0, 1] × X`,
`F = f̃ + S`, `F_i = f + S(i, ·)`.

# The ends of the cobordism are compact oriented manifolds

## What is formalized

* `solutionSet_slice_eq_preimage`, `isCompact_solutionSet_slice`, `isProper_slice`: for every
  `t ∈ [0, 1]`, `S_{F_t} = \{x ∣ (t, x) ∈ S_F\}`, compact when `S_F` is, and `F_t` is proper
  when `F` is.
* **`slice_end_isProper_generalPosition_index`**: if `F` is proper and in general position at
  every zero and `f` has index `k` at every smooth point, then for `i ∈ \{0, 1\}` the section
  `F_i` is proper, in general position at every zero and of index `k` at every zero: the
  hypotheses of Theorem 6.6.18 for `F_i`.
* **`theorem_6_6_18_oriented_end`**: so `S_{F_i}` is a compact smooth manifold with boundary
  and corners of dimension `k` with a continuous tangent orientation equal to `o` (the
  orientation `o.sectionAdd` of `F_i`) on `T_xS_{F_i} = ker F_i'(x)`.
* `exists_timeFirst_coordinates_of_bases`: bases `b'` of `ℝ^{k+1}`, `b` of `ℝ^k` and
  coordinates `ι'`, `ι` of subspaces `N' ⊆ ℝ × E`, `N ⊆ E` with `ι' b'_{l+1} = (0, ι b_l)` and
  `ι' b'_0` of `ℝ`-component `s` give coordinates `κ'`, `κ` with `κ'(0, w) = (0, κ w)`,
  `κ'(1, 0)` of `ℝ`-component `s`, for which "standard orientation" means "the ray of
  `ι' b'_0 ∧ … ∧ ι' b'_k`", resp. "of `ι b_0 ∧ … ∧ ι b_{k-1}`".
* `exists_timeFirst_basis`: such a basis `b'` exists for every `ι'`, `ι`, `b` when
  `N' ∩ (\{0\} × E) = \{0\} × N` (for the kernels:
  `ChartPoint.mem_linKer_ivPt_iff_of_fst_eq_zero`).
* **`tangentOr_ivFirst_eq_ray_iff_slice`**, **`tangentOr_ivFirst_eq_ray_iff_of_end`**: the end
  identity for bases.  Let `(t, x)` be a zero of `F`, `ι' : ℝ^{k+1} ≅ ker F'(t, x)` and
  `ι : ℝ^k ≅ ker F_t'(x)` any coordinates and `b'`, `b` bases with `ι' b'_{l+1} = (0, ι b_l)`
  and `ι' b'_0` of `t`-component the direction of increasing `t`.  Then `b'` spans the
  orientation `e ∧ o` of `ker F'(t, x)` iff `b` spans the orientation `o` of `ker F_t'(x)`.
  At `t ∈ \{0, 1\}` general position of `F` at `(t, x)` is the only hypothesis on the
  linearizations.
* `orientation_end_iff_of_specs`: with the conclusions of `theorem_6_6_18_oriented_interval`
  at `(t, x)` and of `theorem_6_6_18_oriented_end` at `x`: `b'` is positive for the tangent
  orientation of `S_F` at `(t, x)` iff `b` is positive for the tangent orientation of `S_{F_t}`
  at `x`.

At `t = 1` the vector `ι' b'_0` points out of `[0, 1] × X` and at `t = 0` into it: with the
outward normal first (Definition 9.3.8) the boundary orientation of `S_F` on `\{1\} × S_{F_1}`
is that of `S_{F_1}`, and on `\{0\} × S_{F_0}` the opposite of that of `S_{F_0}`.
-/

open Set Filter Topology Manifold Module
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

open StrongRetr StrongBundle UnitCube MPolyfold

local notation "𝓠" => modelWithCornersEuclideanQuadrant

/-! ### Coordinates from bases with the `ℝ`-direction first -/

section BasesCoordinates

variable {E₀ : Type*} [AddCommGroup E₀] [Module ℝ E₀]

/-- **Coordinates from bases with the `ℝ`-direction first.**  Let `ι : ℝ^k ≅ N ⊆ E` and
`ι' : ℝ^{k+1} ≅ N' ⊆ ℝ × E` be coordinates and `b`, `b'` bases of `ℝ^k`, `ℝ^{k+1}` with
`ι' b'_{l+1} = (0, ι b_l)` and `ι' b'_0` of `ℝ`-component `s`.  Then there are coordinates `κ`,
`κ'` with `κ'(0, w) = (0, κ w)` and `κ'(1, 0)` of `ℝ`-component `s` such that a ray of `λ(N)`
gives the standard orientation in `κ` iff it is the ray of `ι b_0 ∧ … ∧ ι b_{k-1}`, and a ray of
`λ(N')` gives the standard orientation in `κ'` iff it is the ray of `ι' b'_0 ∧ … ∧ ι' b'_k`. -/
theorem exists_timeFirst_coordinates_of_bases {N : Submodule ℝ E₀}
    {N' : Submodule ℝ ((Fin 1 → ℝ) × E₀)} {k : ℕ}
    (ι : EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ] N) (ι' : EuclideanSpace ℝ (Fin (k + 1)) ≃ₗ[ℝ] N')
    (bb : Basis (Fin k) ℝ (EuclideanSpace ℝ (Fin k)))
    (bb' : Basis (Fin (k + 1)) ℝ (EuclideanSpace ℝ (Fin (k + 1))))
    (h₀ : ∀ l : Fin k, ((ι' (bb' l.succ) : N') : (Fin 1 → ℝ) × E₀) = (0, (ι (bb l) : E₀)))
    {s : ℝ} (h₁ : ((ι' (bb' 0) : N') : (Fin 1 → ℝ) × E₀).1 = fun _ => s) :
    ∃ (κ : EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ] N) (κ' : EuclideanSpace ℝ (Fin (k + 1)) ≃ₗ[ℝ] N'),
      (∀ w, ((κ' (consE 0 w) : N') : (Fin 1 → ℝ) × E₀) = (0, (κ w : E₀))) ∧
      (((κ' (consE 1 0) : N') : (Fin 1 → ℝ) × E₀).1 = fun _ => s) ∧
      (∀ r : Module.Ray ℝ (maxPow N),
        pullOr finrank_euclideanSpace_fin κ r = stdOrientation k ↔
          r = rayOfNeZero ℝ _ (wedge_equiv_ne_zero finrank_euclideanSpace_fin ι bb)) ∧
      ∀ r' : Module.Ray ℝ (maxPow N'),
        pullOr finrank_euclideanSpace_fin κ' r' = stdOrientation (k + 1) ↔
          r' = rayOfNeZero ℝ _ (wedge_equiv_ne_zero finrank_euclideanSpace_fin ι' bb') := by
  obtain ⟨sb, hsbi, hsbo⟩ := exists_basis_stdOrientation k
  obtain ⟨sb', hsbi', hsbo'⟩ := exists_basis_stdOrientation (k + 1)
  obtain ⟨κ, hκ⟩ : ∃ κ : EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ] N, ∀ i, κ (sb i) = ι (bb i) :=
    ⟨(sb.equiv bb (Equiv.refl _)).trans ι, fun i => by
      rw [LinearEquiv.trans_apply, Basis.equiv_apply]; rfl⟩
  obtain ⟨κ', hκ'⟩ : ∃ κ' : EuclideanSpace ℝ (Fin (k + 1)) ≃ₗ[ℝ] N',
      ∀ i, κ' (sb' i) = ι' (bb' i) :=
    ⟨(sb'.equiv bb' (Equiv.refl _)).trans ι', fun i => by
      rw [LinearEquiv.trans_apply, Basis.equiv_apply]; rfl⟩
  have hlin : N'.subtype ∘ₗ (κ' : EuclideanSpace ℝ (Fin (k + 1)) →ₗ[ℝ] N') ∘ₗ consELin k =
      LinearMap.inr ℝ (Fin 1 → ℝ) E₀ ∘ₗ N.subtype ∘ₗ
        (κ : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] N) := by
    refine sb.ext fun l => ?_
    change ((κ' (consE 0 (sb l)) : N') : (Fin 1 → ℝ) × E₀) = (0, (κ (sb l) : E₀))
    rw [hsbi l, consE_zero_single, ← hsbi' l.succ, hκ' l.succ, ← hsbi l, hκ l]
    exact h₀ l
  refine ⟨κ, κ', fun w => LinearMap.congr_fun hlin w, ?_, fun r => ?_, fun r' => ?_⟩
  · rw [consE_one_zero, ← hsbi' 0, hκ' 0]
    exact h₁
  · have h := orientation_eq_pullOr_iff finrank_euclideanSpace_fin κ r sb
    rw [hsbo] at h
    refine (eq_comm.trans h).trans (Eq.congr_right (rayOfNeZero_congr ?_ _ _))
    congr 1
    exact funext fun i => hκ i
  · have h := orientation_eq_pullOr_iff finrank_euclideanSpace_fin κ' r' sb'
    rw [hsbo'] at h
    refine (eq_comm.trans h).trans (Eq.congr_right (rayOfNeZero_congr ?_ _ _))
    congr 1
    exact funext fun i => hκ' i

/-- **Bases with the `ℝ`-direction first exist for any coordinates.**  Let `ι : ℝ^k ≅ N ⊆ E`
and `ι' : ℝ^{k+1} ≅ N' ⊆ ℝ × E` be coordinates of subspaces with
`N' ∩ (\{0\} × E) = \{0\} × N`, `s ≠ 0` and `b` a basis of `ℝ^k`.  Then there is a basis `b'` of
`ℝ^{k+1}` with `ι' b'_{l+1} = (0, ι b_l)` and `ι' b'_0` of `ℝ`-component `s`: the hypotheses of
`exists_timeFirst_coordinates_of_bases` can be met for every `ι`, `ι'`, `b`. -/
theorem exists_timeFirst_basis {N : Submodule ℝ E₀} {N' : Submodule ℝ ((Fin 1 → ℝ) × E₀)}
    {k : ℕ} (ι : EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ] N)
    (ι' : EuclideanSpace ℝ (Fin (k + 1)) ≃ₗ[ℝ] N')
    (hiff : ∀ w : (Fin 1 → ℝ) × E₀, w.1 = 0 → (w ∈ N' ↔ w.2 ∈ N)) {s : ℝ} (hs : s ≠ 0)
    (bb : Basis (Fin k) ℝ (EuclideanSpace ℝ (Fin k))) :
    ∃ bb' : Basis (Fin (k + 1)) ℝ (EuclideanSpace ℝ (Fin (k + 1))),
      (∀ l : Fin k, ((ι' (bb' l.succ) : N') : (Fin 1 → ℝ) × E₀) = (0, (ι (bb l) : E₀))) ∧
      ((ι' (bb' 0) : N') : (Fin 1 → ℝ) × E₀).1 = fun _ => s := by
  have : FiniteDimensional ℝ N := ι.finiteDimensional
  have : FiniteDimensional ℝ N' := ι'.finiteDimensional
  have hk : finrank ℝ N = k := by rw [← ι.finrank_eq, finrank_euclideanSpace_fin]
  have hk' : finrank ℝ N' = k + 1 := by rw [← ι'.finrank_eq, finrank_euclideanSpace_fin]
  have hna : wedge (fun i => ι (bb i)) hk.symm ≠ 0 :=
    wedge_equiv_ne_zero finrank_euclideanSpace_fin ι bb
  obtain ⟨ν, a', hna', -, -, hν1, ha', -⟩ :=
    exists_timeFirst_coordinates hk hk' hiff hs (fun i => ι (bb i)) hna
  have hli : LinearIndependent ℝ (Fin.cons ν a' : Fin (k + 1) → N') :=
    (wedge_ne_zero_iff hk'.symm).1 hna'
  obtain ⟨bC, hbC⟩ : ∃ bC : Basis (Fin (k + 1)) ℝ N',
      ∀ i, bC i = (Fin.cons ν a' : Fin (k + 1) → N') i :=
    ⟨basisOfLinearIndependentOfCardEqFinrank' _ hli (by rw [Fintype.card_fin, hk']), fun i => by
      rw [coe_basisOfLinearIndependentOfCardEqFinrank']⟩
  refine ⟨bC.map ι'.symm, fun l => ?_, ?_⟩
  · rw [Basis.map_apply, LinearEquiv.apply_symm_apply, hbC, Fin.cons_succ]
    exact ha' l
  · rw [Basis.map_apply, LinearEquiv.apply_symm_apply, hbC, Fin.cons_zero]
    exact hν1

end BasesCoordinates

/-! ### The slices of a proper section over `[0, 1] × X` -/

section Slices

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] {f : X → Y}

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] in
/-- **`S_{F_t}` is the slice of `S_F` at `t`**: `x ∈ S_{F_t}` iff `(t, x) ∈ S_F`, for
`F = f̃ + S` and `F_t = f + S(t, ·)`. -/
theorem solutionSet_slice_eq_preimage (hf : IsSection P f)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : IsSection (pullbackProj P Prod.snd) S) (t : Fin 1 → unitInterval) :
    solutionSet P (sectionAdd P f (prodSlice S t)) =
      (fun x : X => ((t, x) : (Fin 1 → unitInterval) × X)) ⁻¹'
        solutionSet (pullbackProj P Prod.snd)
          (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf) S) := by
  ext x
  rw [← prodSlice_sectionAdd_cubeLift hf hS t]
  exact (isZeroAt_iff_prodSlice ((isSection_pullbackLift _).sectionAdd hS) t x).symm

omit [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
  [∀ x, Module ℝ (P ⁻¹' {x})]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] in
/-- **The slices of a compact solution set are compact.** -/
theorem isCompact_solutionSet_slice (hf : IsSection P f)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : IsSection (pullbackProj P Prod.snd) S)
    (hc : IsCompact (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf) S)))
    (t : Fin 1 → unitInterval) : IsCompact (solutionSet P (sectionAdd P f (prodSlice S t))) := by
  have hK : IsCompact (solutionSet (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf) S) ∩
        ({t} ×ˢ (univ : Set X))) :=
    hc.inter_right (isClosed_singleton.prod isClosed_univ)
  have he : solutionSet P (sectionAdd P f (prodSlice S t)) =
      Prod.snd '' (solutionSet (pullbackProj P Prod.snd)
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf) S) ∩
          ({t} ×ˢ (univ : Set X))) := by
    rw [solutionSet_slice_eq_preimage hf hS t]
    ext x
    constructor
    · intro hx
      exact ⟨(t, x), ⟨hx, rfl, mem_univ _⟩, rfl⟩
    · rintro ⟨⟨t', x'⟩, ⟨hz, ht', -⟩, rfl⟩
      obtain rfl : t' = t := ht'
      exact hz
  rw [he]
  exact hK.image continuous_snd

/-- **The slices of a proper `F = f̃ + S` are proper** (2021 Theorem 5.2.2, p. 210): for every
`t ∈ [0, 1]`, `F_t = f + S(t, ·)` is sc-Fredholm with compact solution set. -/
theorem isProper_slice (hf : B.IsScFredholmSectionTame f)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : (ivBundle B).IsScPlusSection S)
    (hP : (ivBundle B).IsProper
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S))
    (t : Fin 1 → unitInterval) : B.IsProper (sectionAdd P f (prodSlice S t)) :=
  theorem_5_2_2_preprint (theorem_3_1_18_preprint hf.toIsScFredholmSection (hS.cubeSlice t))
    (isCompact_solutionSet_slice hf.isScSmooth.1 hS.1 hP.1 t)

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] in
/-- A zero `x` of `F_t` gives the zero `(t, x)` of `F`. -/
theorem isZeroAt_of_isZeroAt_slice (hf : IsSection P f)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : IsSection (pullbackProj P Prod.snd) S) {t : Fin 1 → unitInterval} {x : X}
    (hx : IsZeroAt P (sectionAdd P f (prodSlice S t)) x) :
    IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf) S) (t, x) := by
  have h : x ∈ solutionSet P (sectionAdd P f (prodSlice S t)) := hx
  rw [solutionSet_slice_eq_preimage hf hS t] at h
  exact h

/-- **The ends satisfy the hypotheses of Theorem 6.6.18** (the proof of 2021 Theorem 6.7.1,
p. 278): let `F = f̃ + S` over `[0, 1] × X` be proper and in general position at every zero, and
let `f` have index `k` at every smooth point.  Then for `t ∈ \{0, 1\}` the section
`F_t = f + S(t, ·)` is proper, in general position at every zero and of index `k` at every
zero. -/
theorem slice_end_isProper_generalPosition_index (hf : B.IsScFredholmSectionTame f)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : (ivBundle B).IsScPlusSection S)
    (hP : (ivBundle B).IsProper
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S))
    (hgp : ∀ z, IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z →
      (ivBundle B).IsGeneralPositionGerm
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z)
    {k : ℕ} (hk : ∀ x ∈ PX.smoothSet, B.IsIndexAt f x k) {t : Fin 1 → unitInterval}
    (ht : (t 0 : ℝ) = 0 ∨ (t 0 : ℝ) = 1) :
    B.IsProper (sectionAdd P f (prodSlice S t)) ∧
      (∀ x, IsZeroAt P (sectionAdd P f (prodSlice S t)) x →
        B.IsGeneralPositionGerm (sectionAdd P f (prodSlice S t)) x) ∧
      ∀ x, IsZeroAt P (sectionAdd P f (prodSlice S t)) x →
        B.IsLinOfIndex (sectionAdd P f (prodSlice S t)) x k := by
  have hf' := hf.toIsScFredholmSection
  have hs := hS.cubeSlice t
  refine ⟨isProper_slice hf hS hP t, fun x hx => ?_, fun x hx => ?_⟩
  · have hz := isZeroAt_of_isZeroAt_slice hf.isScSmooth.1 hS.1 hx
    exact isGeneralPositionGerm_slice_of_end hf hS ht hz (hgp _ hz)
  · exact isLinOfIndex_sectionAdd_of_isIndexAt hf' hs hx
      (hk x ((theorem_3_1_18_preprint hf' hs).mem_smoothSet_of_isZeroAt hx))

/-- **The ends of the cobordism are compact oriented manifolds** (2021 Theorem 6.6.18, p. 275,
for `F_i`, and the proof of Theorem 6.7.1, p. 278): let `X` be tame with sc-smooth bump
functions, `f` a tame sc-Fredholm section of index `k` at every smooth point with an orientation
`o`, and `S` an sc⁺-section over `[0, 1] × X` such that `F = f̃ + S` is proper and in general
position at every zero.  Then for `t ∈ \{0, 1\}` the hypotheses of Theorem 6.6.18 hold for
`F_t = f + S(t, ·)`, and `S_{F_t}` is compact and a smooth manifold with boundary and corners of
dimension `k` with a continuous tangent orientation which at every zero `x` is the orientation
`o` (`o.sectionAdd`) on `T_xS_{F_t} = ker F_t'(x)`. -/
theorem theorem_6_6_18_oriented_end (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) (o : SectionOrientation f hf.toIsScFredholmSection)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : (ivBundle B).IsScPlusSection S)
    (hP : (ivBundle B).IsProper
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S))
    (hgp : ∀ z, IsZeroAt (pullbackProj P Prod.snd)
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z →
      (ivBundle B).IsGeneralPositionGerm
        (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S) z)
    {k : ℕ} (hk : ∀ x ∈ PX.smoothSet, B.IsIndexAt f x k) {t : Fin 1 → unitInterval}
    (ht : (t 0 : ℝ) = 0 ∨ (t 0 : ℝ) = 1) :
    ∃ (hPt : B.IsProper (sectionAdd P f (prodSlice S t)))
      (hgpt : ∀ x, IsZeroAt P (sectionAdd P f (prodSlice S t)) x →
        B.IsGeneralPositionGerm (sectionAdd P f (prodSlice S t)) x)
      (hidxt : ∀ x, IsZeroAt P (sectionAdd P f (prodSlice S t)) x →
        B.IsLinOfIndex (sectionAdd P f (prodSlice S t)) x k),
      IsCompact (solutionSet P (sectionAdd P f (prodSlice S t))) ∧
      letI := PX.paracompactSpace_subtype (solutionSet P (sectionAdd P f (prodSlice S t)))
      letI := (MPolyfold.subPolyfold ((theorem_6_6_18_solutionSet hX
        (theorem_3_1_18_tame hf (hS.cubeSlice t)) hPt hgpt).isSubmanifoldOfDim
        (theorem_3_1_18_tame hf (hS.cubeSlice t)) hidxt).1.isSubMPolyfold).cornerChartedSpace
        (((theorem_6_6_18_solutionSet hX (theorem_3_1_18_tame hf (hS.cubeSlice t)) hPt
          hgpt).isSubmanifoldOfDim
          (theorem_3_1_18_tame hf (hS.cubeSlice t)) hidxt).hasCornerStructureOfDim_of_tame
          hX ((theorem_6_6_18_solutionSet hX (theorem_3_1_18_tame hf (hS.cubeSlice t)) hPt
            hgpt).isGoodPositionAt hX))
      IsManifold (𝓠 k) ∞ (solutionSet P (sectionAdd P f (prodSlice S t))) ∧
      ∃ oS : TangentOrientation (𝓠 k) (solutionSet P (sectionAdd P f (prodSlice S t))) k,
        oS.IsContinuous (𝓠 k) ∞ ∧
        ∀ (x : solutionSet P (sectionAdd P f (prodSlice S t))) (c : StrongBundleChart PX P)
          (hc : B.IsChart c) (hxc : x.1 ∈ c.φ.source),
          ∃ ι : EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ] c.linKer (sectionAdd P f (prodSlice S t))
              (chartPtOf c hc hxc ((theorem_3_1_18_tame hf
                (hS.cubeSlice t)).toIsScFredholmSection.mem_smoothSet_of_isZeroAt x.2)).z,
            (∀ v, (ι v : c.φ.model.E 0) = derivIn (𝓠 k) (chartAt (EuclideanQuadrant k) x)
              (fun y : solutionSet P (sectionAdd P f (prodSlice S t)) => c.φ y.1) x v) ∧
            ∀ b : Basis (Fin k) ℝ (EuclideanSpace ℝ (Fin k)),
              b.orientation = tangentOrToModel (oS x) ↔
                (chartPtOf c hc hxc ((theorem_3_1_18_tame hf
                    (hS.cubeSlice t)).toIsScFredholmSection.mem_smoothSet_of_isZeroAt
                    x.2)).tangentOr
                  (theorem_3_1_18_tame hf (hS.cubeSlice t)).toIsScFredholmSection x.2
                  (hgpt x.1 x.2).isLinSurjAt
                  (toChartOr (theorem_3_1_18_tame hf (hS.cubeSlice t)).toIsScFredholmSection
                    ((theorem_3_1_18_tame hf
                      (hS.cubeSlice t)).toIsScFredholmSection.mem_smoothSet_of_isZeroAt x.2)
                    c hc hxc
                    ((o.sectionAdd (hS.cubeSlice t)).1 x.1 ((theorem_3_1_18_tame hf
                      (hS.cubeSlice t)).toIsScFredholmSection.mem_smoothSet_of_isZeroAt
                      x.2))) =
                  rayOfNeZero ℝ _ (wedge_equiv_ne_zero finrank_euclideanSpace_fin ι b) := by
  obtain ⟨hPt, hgpt, hidxt⟩ := slice_end_isProper_generalPosition_index hf hS hP hgp hk ht
  exact ⟨hPt, hgpt, hidxt, theorem_6_6_18_oriented hX hbump
    (theorem_3_1_18_tame hf (hS.cubeSlice t)) hPt hgpt hidxt (o.sectionAdd (hS.cubeSlice t))⟩

end Slices

/-! ### The end identity for bases -/

section BasesIdentity

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace ((Fin 1 → unitInterval) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))] {f : X → Y}

/-- **The end identity for bases** (2021 Remark 6.6.19, p. 276, and the proof of Theorem 6.7.1,
p. 278): let `o` be an orientation of the tame sc-Fredholm section `f`, `S` an sc⁺-section over
`[0, 1] × X`, `F = f̃ + S` and `(t, x)` a zero of `F` at which `F'(t, x)` and `F_t'(x)` are onto.
Let `ι : ℝ^k ≅ ker F_t'(x)` and `ι' : ℝ^{k+1} ≅ ker F'(t, x)` be any coordinates in the charts
`c` and `χ_b × φ_c`, and `bb`, `bb'` bases of `ℝ^k`, `ℝ^{k+1}` with
`ι' bb'_{l+1} = (0, ι bb_l)` and `ι' bb'_0` of `t`-component `± 1`, the sign that of `χ_b` (the
direction of increasing `t`).  Then `ι' bb'_0 ∧ … ∧ ι' bb'_k` spans the tangent orientation of
`S_F` at `(t, x)` given by `e ∧ o` iff `ι bb_0 ∧ … ∧ ι bb_{k-1}` spans the tangent orientation
of `S_{F_t}` at `x` given by `o`. -/
theorem tangentOr_ivFirst_eq_ray_iff_slice (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) (o : SectionOrientation f hf.toIsScFredholmSection)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : (ivBundle B).IsScPlusSection S) {t : Fin 1 → unitInterval} {x : X}
    (hxs : x ∈ PX.smoothSet) (b : Fin 1 → Bool) (hb : t ∈ (chart b).source)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (hxc : x ∈ c.φ.source)
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))
    (hz0 : IsZeroAt (pullbackProj P Prod.snd) (sectionAdd (pullbackProj P Prod.snd)
      (cubeLift (n := 1) f hf.isScSmooth.1) S) (t, x))
    (hL : (ivBundle B).IsLinSurjAt (sectionAdd (pullbackProj P Prod.snd)
      (cubeLift (n := 1) f hf.isScSmooth.1) S) (t, x))
    (hx0 : IsZeroAt P (sectionAdd P f (prodSlice S t)) x)
    (hLt : B.IsLinSurjAt (sectionAdd P f (prodSlice S t)) x)
    {k : ℕ} (ι : EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ]
      c.linKer (sectionAdd P f (prodSlice S t)) (chartPtOf c hc hxc hxs).z)
    (ι' : EuclideanSpace ℝ (Fin (k + 1)) ≃ₗ[ℝ] (ivChart b c q₀).linKer
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)
      (chartPtOf (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀)
        (mem_ivChart_source q₀ hxc hb) (prod_cube_mem_smoothSet_iff.2 hxs)).z)
    (bb : Basis (Fin k) ℝ (EuclideanSpace ℝ (Fin k)))
    (bb' : Basis (Fin (k + 1)) ℝ (EuclideanSpace ℝ (Fin (k + 1))))
    (h₀ : ∀ l : Fin k, ((ι' (bb' l.succ)).1 : (Fin 1 → ℝ) × c.φ.model.E 0) =
      (0, (ι (bb l) : c.φ.model.E 0)))
    (h₁ : ((ι' (bb' 0)).1 : (Fin 1 → ℝ) × c.φ.model.E 0).1 = fun _ => ivSign b) :
    (chartPtOf (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀)
          (mem_ivChart_source q₀ hxc hb) (prod_cube_mem_smoothSet_iff.2 hxs)).tangentOr
          (theorem_3_1_18_preprint (hf.paramCube (n := 1)).toIsScFredholmSection hS) hz0 hL
          (toChartOr (theorem_3_1_18_preprint (hf.paramCube (n := 1)).toIsScFredholmSection hS)
            (prod_cube_mem_smoothSet_iff.2 hxs) (ivChart b c q₀) (isChart_ivChart b hc q₀)
            (mem_ivChart_source q₀ hxc hb)
            ((SectionOrientation.ivFirst hX hbump hf o hS).1 (t, x)
              (prod_cube_mem_smoothSet_iff.2 hxs))) =
        rayOfNeZero ℝ _ (wedge_equiv_ne_zero finrank_euclideanSpace_fin ι' bb') ↔
      (chartPtOf c hc hxc hxs).tangentOr
          (theorem_3_1_18_preprint hf.toIsScFredholmSection (hS.cubeSlice t)) hx0 hLt
          (toChartOr (theorem_3_1_18_preprint hf.toIsScFredholmSection (hS.cubeSlice t)) hxs c
            hc hxc ((o.sectionAdd (hS.cubeSlice t)).1 x hxs)) =
        rayOfNeZero ℝ _ (wedge_equiv_ne_zero finrank_euclideanSpace_fin ι bb) := by
  have aux := fun (N' : Submodule ℝ ((Fin 1 → ℝ) × c.φ.model.E 0))
      (ι'' : EuclideanSpace ℝ (Fin (k + 1)) ≃ₗ[ℝ] N')
      (h₀' : ∀ l : Fin k, ((ι'' (bb' l.succ) : N') : (Fin 1 → ℝ) × c.φ.model.E 0) =
        (0, (ι (bb l) : c.φ.model.E 0)))
      (h₁' : ((ι'' (bb' 0) : N') : (Fin 1 → ℝ) × c.φ.model.E 0).1 = fun _ => ivSign b) =>
    exists_timeFirst_coordinates_of_bases (E₀ := c.φ.model.E 0) ι ι'' bb bb' h₀' h₁'
  have h := aux _ ι' h₀ h₁
  obtain ⟨κ, κ', hκ₀, hκ₁, hr, hr'⟩ := h
  exact (hr' _).symm.trans ((pullOr_tangentOr_ivFirst_iff_slice hX hbump hf o hS hxs b hb hc hxc
    q₀ hz0 hL hx0 hLt κ κ' hκ₀ hκ₁).trans (hr _))

/-- **The end identity for bases at `t ∈ \{0, 1\}`, from general position of `F` alone**:
`tangentOr_ivFirst_eq_ray_iff_slice` at a zero `(t, x)` of `F = f̃ + S` with `t ∈ \{0, 1\}` at
which `F` is in general position (`isLinSurjAt_slice_of_end`). -/
theorem tangentOr_ivFirst_eq_ray_iff_of_end (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) (o : SectionOrientation f hf.toIsScFredholmSection)
    {S : (Fin 1 → unitInterval) × X →
      pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X)}
    (hS : (ivBundle B).IsScPlusSection S) {t : Fin 1 → unitInterval}
    (ht : (t 0 : ℝ) = 0 ∨ (t 0 : ℝ) = 1) {x : X}
    (hxs : x ∈ PX.smoothSet) (b : Fin 1 → Bool) (hb : t ∈ (chart b).source)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (hxc : x ∈ c.φ.source)
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))
    (hz0 : IsZeroAt (pullbackProj P Prod.snd) (sectionAdd (pullbackProj P Prod.snd)
      (cubeLift (n := 1) f hf.isScSmooth.1) S) (t, x))
    (hgp : (ivBundle B).IsGeneralPositionGerm (sectionAdd (pullbackProj P Prod.snd)
      (cubeLift (n := 1) f hf.isScSmooth.1) S) (t, x))
    {k : ℕ} (ι : EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ]
      c.linKer (sectionAdd P f (prodSlice S t)) (chartPtOf c hc hxc hxs).z)
    (ι' : EuclideanSpace ℝ (Fin (k + 1)) ≃ₗ[ℝ] (ivChart b c q₀).linKer
      (sectionAdd (pullbackProj P Prod.snd) (cubeLift (n := 1) f hf.isScSmooth.1) S)
      (chartPtOf (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀)
        (mem_ivChart_source q₀ hxc hb) (prod_cube_mem_smoothSet_iff.2 hxs)).z)
    (bb : Basis (Fin k) ℝ (EuclideanSpace ℝ (Fin k)))
    (bb' : Basis (Fin (k + 1)) ℝ (EuclideanSpace ℝ (Fin (k + 1))))
    (h₀ : ∀ l : Fin k, ((ι' (bb' l.succ)).1 : (Fin 1 → ℝ) × c.φ.model.E 0) =
      (0, (ι (bb l) : c.φ.model.E 0)))
    (h₁ : ((ι' (bb' 0)).1 : (Fin 1 → ℝ) × c.φ.model.E 0).1 = fun _ => ivSign b) :
    (chartPtOf (B := ivBundle B) (ivChart b c q₀) (isChart_ivChart b hc q₀)
          (mem_ivChart_source q₀ hxc hb) (prod_cube_mem_smoothSet_iff.2 hxs)).tangentOr
          (theorem_3_1_18_preprint (hf.paramCube (n := 1)).toIsScFredholmSection hS) hz0
          hgp.isLinSurjAt
          (toChartOr (theorem_3_1_18_preprint (hf.paramCube (n := 1)).toIsScFredholmSection hS)
            (prod_cube_mem_smoothSet_iff.2 hxs) (ivChart b c q₀) (isChart_ivChart b hc q₀)
            (mem_ivChart_source q₀ hxc hb)
            ((SectionOrientation.ivFirst hX hbump hf o hS).1 (t, x)
              (prod_cube_mem_smoothSet_iff.2 hxs))) =
        rayOfNeZero ℝ _ (wedge_equiv_ne_zero finrank_euclideanSpace_fin ι' bb') ↔
      (chartPtOf c hc hxc hxs).tangentOr
          (theorem_3_1_18_preprint hf.toIsScFredholmSection (hS.cubeSlice t))
          (isZeroAt_slice_of_isZeroAt hf hS hz0) (isLinSurjAt_slice_of_end hf hS ht hz0 hgp)
          (toChartOr (theorem_3_1_18_preprint hf.toIsScFredholmSection (hS.cubeSlice t)) hxs c
            hc hxc ((o.sectionAdd (hS.cubeSlice t)).1 x hxs)) =
        rayOfNeZero ℝ _ (wedge_equiv_ne_zero finrank_euclideanSpace_fin ι bb) :=
  tangentOr_ivFirst_eq_ray_iff_slice hX hbump hf o hS hxs b hb hc hxc q₀ hz0 hgp.isLinSurjAt
    (isZeroAt_slice_of_isZeroAt hf hS hz0) (isLinSurjAt_slice_of_end hf hS ht hz0 hgp) ι ι' bb
    bb' h₀ h₁

end BasesIdentity

/-! ### The tangent orientations of `S_F` and of its ends -/

section Specs

variable {k : ℕ}

/-- **The boundary orientation of the cobordism at an end point, from the two orientation
formulas**: let `oF`, `oE` be orientations of `ℝ^{k+1}`, `ℝ^k` (the tangent orientations of
`S_F` at `(t, x)` and of `S_{F_t}` at `x`, read in charts), `r'`, `r` rays of `λ(N')`, `λ(N)`
(the orientations `e ∧ o` of `ker F'(t, x)` and `o` of `ker F_t'(x)`) and `ι'`, `ι` coordinates
such that a basis is positive for `oF`, resp. `oE`, iff its image spans `r'`, resp. `r` (the
conclusions of `theorem_6_6_18_oriented_interval` and `theorem_6_6_18_oriented_end`).  If for
the bases `bb'`, `bb` the image of `bb'` spans `r'` iff the image of `bb` spans `r`
(`tangentOr_ivFirst_eq_ray_iff_of_end`), then `bb'` is positive for `oF` iff `bb` is positive for
`oE`. -/
theorem orientation_end_iff_of_specs {N N' : Type*} [AddCommGroup N] [Module ℝ N]
    [AddCommGroup N'] [Module ℝ N']
    {oF : Orientation ℝ (EuclideanSpace ℝ (Fin (k + 1))) (Fin (k + 1))}
    {oE : Orientation ℝ (EuclideanSpace ℝ (Fin k)) (Fin k)}
    {r' : Module.Ray ℝ (maxPow N')} {r : Module.Ray ℝ (maxPow N)}
    (ι : EuclideanSpace ℝ (Fin k) ≃ₗ[ℝ] N) (ι' : EuclideanSpace ℝ (Fin (k + 1)) ≃ₗ[ℝ] N')
    (hF : ∀ b' : Basis (Fin (k + 1)) ℝ (EuclideanSpace ℝ (Fin (k + 1))),
      b'.orientation = oF ↔
        r' = rayOfNeZero ℝ _ (wedge_equiv_ne_zero finrank_euclideanSpace_fin ι' b'))
    (hE : ∀ b : Basis (Fin k) ℝ (EuclideanSpace ℝ (Fin k)),
      b.orientation = oE ↔
        r = rayOfNeZero ℝ _ (wedge_equiv_ne_zero finrank_euclideanSpace_fin ι b))
    (bb : Basis (Fin k) ℝ (EuclideanSpace ℝ (Fin k)))
    (bb' : Basis (Fin (k + 1)) ℝ (EuclideanSpace ℝ (Fin (k + 1))))
    (h : r' = rayOfNeZero ℝ _ (wedge_equiv_ne_zero finrank_euclideanSpace_fin ι' bb') ↔
      r = rayOfNeZero ℝ _ (wedge_equiv_ne_zero finrank_euclideanSpace_fin ι bb)) :
    bb'.orientation = oF ↔ bb.orientation = oE :=
  (hF bb').trans (h.trans (hE bb).symm)

end Specs

end Polyfold
