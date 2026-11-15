import Polyfold.Chapter9.BoundaryOrientation

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §9.3, Definition 9.3.8,
p. 427 (2017: Definition 9.9), as used in the proof of Corollary 15.4.4 (p. 703).

# The boundary orientation from one frame

## The text, paraphrased

For an oriented submanifold `(M, o)` and `y ∈ ∂M` with `d_M(y) = 1`, a basis `a₁, …, a_m` of
`T_y∂M` is positive for `o_{∂M}` if `(e, a₁, …, a_m)` is positive for `o`, where `e ∈ T_yM`
points outward.

## What is formalized

The convention of the library (`MPolyfold.boundaryOp`): the outward vector comes **first**, and
"outward" means "not in the partial cone `C_yX`" of the ambient M-polyfold.

* `MPolyfold.IsOrientedAt.frames_eq_of_mem`: two orientations of one tangent set with a common
  positive frame are equal.
* `MPolyfold.mem_boundaryOp_frames_of_outward`: if `e` is outward and `(e, a)` is positive, then
  `a` is positive for the boundary orientation.
* `MPolyfold.notMem_boundaryOp_frames_of_inward`: if `w ∈ C_yX ∖ T^R_yX` (inward) and `(w, a)`
  is positive, then `a` is not positive for the boundary orientation.
* `MPolyfold.not_isInwardVec_of_coord_neg`, `MPolyfold.isInwardVec_of_coord_pos`: outward and
  inward vectors of `T_yM` from the sign of one coordinate of a presented chart that vanishes
  at `y`; `MPolyfold.isReducedVec_iff_coord_eq_zero`: `T_y∂M` is cut out of `T_yM` by that
  coordinate.
* **`MPolyfold.SubmanifoldOrientation.stratumOrientation_tangent_eq_of_outward`**,
  **`MPolyfold.SubmanifoldOrientation.stratumOrientation_tangent_ne_of_inward`**: for an
  orientation `o'` of the stratum `∂₁M` and a frame `a` positive for `o'`: if `(e, a)` is
  positive for `o` with `e` outward, then `T_y(∂₁M, o_{∂M}) = T_y(∂₁M, o')`; if `(w, a)` is
  positive for `o` with `w` inward and not in `T^R_yX`, the two oriented tangent spaces differ.
-/

set_option maxSynthPendingDepth 3

open Set Module Submodule

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- **Two orientations of a tangent set with a common positive frame are equal.** -/
theorem IsOrientedAt.frames_eq_of_mem {y : X} {n : ℕ} {L : Set P.TangentSpace}
    {O O' : Set (Fin n → P.TangentSpace)} (hO : P.IsOrientedAt y ⟨n, L, O⟩)
    (hO' : P.IsOrientedAt y ⟨n, L, O'⟩) {v : Fin n → P.TangentSpace} (hv : v ∈ O)
    (hv' : v ∈ O') : O = O' := by
  obtain ⟨φ, hφ, hyφ⟩ := P.exists_isChart_mem_source y
  obtain ⟨N, hN, -, -, ω, hω⟩ := hO.isChartOrientation hφ hyφ
  obtain ⟨N', hN', -, -, ω', hω'⟩ := hO'.isChartOrientation hφ hyφ
  have hNN : N = N' := SetLike.coe_injective (hN.trans hN'.symm)
  subst hNN
  have e1 : O = chartFrames hφ L N ω := hω
  have e2 : O' = chartFrames hφ L N ω' := hω'
  rw [e1] at hv
  rw [e2] at hv'
  obtain ⟨-, b, hb, hbo⟩ := hv
  obtain ⟨-, b', hb', hbo'⟩ := hv'
  have hbb : b = b' := Basis.eq_of_apply_eq fun i => Subtype.ext ((hb i).trans (hb' i).symm)
  rw [e1, e2, ← hbo, ← hbo', hbb]

/-- Equal oriented tangent sets of the same dimension have the same frames. -/
theorem OrTangent.frames_eq_of_mk_eq {n : ℕ} {L L' : Set P.TangentSpace}
    {O O' : Set (Fin n → P.TangentSpace)}
    (h : (⟨n, L, O⟩ : OrTangent P) = ⟨n, L', O'⟩) : O = O' := by
  cases h
  rfl

/-- If `chartVec e' = c · chartVec e + k` with `c < 0` and `k` in the chart image of `K`, a
frame of `K` cannot be a boundary frame for both `e` and `e'`. -/
theorem boundaryFrames_disjoint_of_neg {φ : MChart X} {y : X} {m : ℕ}
    {L K : Set P.TangentSpace} {O : Set (Fin (m + 1) → P.TangentSpace)}
    (hO : P.IsOrientedAt y ⟨m + 1, L, O⟩) (hKL : K ⊆ L) (hφ : P.IsChart φ) (hyφ : y ∈ φ.source)
    (NK : Submodule ℝ (φ.model.E 0)) (hNK : (NK : Set (φ.model.E 0)) = chartVec hφ '' K)
    (hrank : finrank ℝ NK = m) {e e' : P.TangentSpace} (he : e ∈ L) (he' : e' ∈ L) {c : ℝ}
    (hc : c < 0) (hk : chartVec hφ e' - c • chartVec hφ e ∈ NK) {a : Fin m → P.TangentSpace}
    (ha : a ∈ boundaryFrames O K e) : a ∉ boundaryFrames O K e' := by
  obtain ⟨NL, hNL, hfin, hrankL, ωL, hOeq⟩ := hO.isChartOrientation hφ hyφ
  have hle : NK ≤ NL := fun v hv => by
    rw [← SetLike.mem_coe, hNK] at hv
    obtain ⟨α, hα, rfl⟩ := hv
    rw [← SetLike.mem_coe, hNL]
    exact ⟨α, hKL hα, rfl⟩
  have hv₀ : chartVec hφ e ∈ NL := by rw [← SetLike.mem_coe, hNL]; exact ⟨e, he, rfl⟩
  have hv₀' : chartVec hφ e' ∈ NL := by rw [← SetLike.mem_coe, hNL]; exact ⟨e', he', rfl⟩
  let B₀ : Basis (Fin (m + 1)) ℝ NL :=
    (Module.finBasisOfFinrankEq ℝ NL hrankL).adjustToOrientation ωL
  have hB₀ : B₀.orientation = ωL := Basis.orientation_adjustToOrientation _ _
  have hsplit : (⟨chartVec hφ e', hv₀'⟩ : NL) =
      c • (⟨chartVec hφ e, hv₀⟩ : NL) + Submodule.inclusion hle ⟨_, hk⟩ :=
    Subtype.ext (by simp)
  rintro ⟨-, ha'⟩
  obtain ⟨haK, ha⟩ := ha
  rw [show O = chartFrames hφ L NL ωL from hOeq, ← hB₀,
    cons_mem_chartFrames_iff hφ hKL hle hNK B₀ he hv₀ haK] at ha
  rw [show O = chartFrames hφ L NL ωL from hOeq, ← hB₀,
    cons_mem_chartFrames_iff hφ hKL hle hNK B₀ he' hv₀' haK, hsplit,
    det_cons_smul_add hle B₀ hrank] at ha'
  nlinarith

/-- The frames of the boundary operation are the boundary frames of any outward vector. -/
theorem boundaryOp_frames_eq {y : X} {m : ℕ} {L : Set P.TangentSpace}
    {O : Set (Fin (m + 1) → P.TangentSpace)} (hO : P.IsOrientedAt y ⟨m + 1, L, O⟩)
    (hadm : P.IsBoundaryAdmissible y ⟨m + 1, L, O⟩) {e : P.TangentSpace} (he : e ∈ L)
    (heo : ¬ P.IsInwardVec y e) :
    (P.boundaryOp ⟨m + 1, L, O⟩).frames = boundaryFrames O (P.boundaryCarrier L) e :=
  OrTangent.frames_eq_of_mk_eq (boundaryOp_eq hO hadm he heo)

/-- **Outward normal first** (Definition 9.3.8): in the situation of Definition 9.3.8, if
`e ∈ L` is outward, the `aᵢ` lie in `T_y∂M` and `(e, a₁, …, a_m)` is positive, then
`(a₁, …, a_m)` is positive for the boundary orientation. -/
theorem mem_boundaryOp_frames_of_outward {y : X} {m : ℕ} {L : Set P.TangentSpace}
    {O : Set (Fin (m + 1) → P.TangentSpace)} (hO : P.IsOrientedAt y ⟨m + 1, L, O⟩)
    (hadm : P.IsBoundaryAdmissible y ⟨m + 1, L, O⟩) {e : P.TangentSpace} (he : e ∈ L)
    (heo : ¬ P.IsInwardVec y e) {a : Fin m → P.TangentSpace}
    (ha : ∀ i, a i ∈ P.boundaryCarrier L) (hcons : (Fin.cons e a : Fin (m + 1) → _) ∈ O) :
    a ∈ (P.boundaryOp ⟨m + 1, L, O⟩).frames := by
  have h := boundaryOp_frames_eq hO hadm he heo
  exact h ▸ ⟨ha, hcons⟩

/-- **Inward normal first gives the opposite orientation**: in the situation of
Definition 9.3.8, if `w ∈ L` lies in `C_yX ∖ T^R_yX` and `(w, a₁, …, a_m)` is positive, then
`(a₁, …, a_m)` is not positive for the boundary orientation. -/
theorem notMem_boundaryOp_frames_of_inward {y : X} {m : ℕ} {L : Set P.TangentSpace}
    {O : Set (Fin (m + 1) → P.TangentSpace)} (hO : P.IsOrientedAt y ⟨m + 1, L, O⟩)
    (hadm : P.IsBoundaryAdmissible y ⟨m + 1, L, O⟩) {w : P.TangentSpace} (hw : w ∈ L)
    (hwin : P.IsInwardVec y w) (hwred : ¬ P.IsReducedVec y w) {a : Fin m → P.TangentSpace}
    (ha : ∀ i, a i ∈ P.boundaryCarrier L) (hcons : (Fin.cons w a : Fin (m + 1) → _) ∈ O) :
    a ∉ (P.boundaryOp ⟨m + 1, L, O⟩).frames := by
  obtain ⟨c⟩ := P.nonempty_presentedChart y
  obtain ⟨N, -, hspan, hfin, hrank, hNK⟩ := hO.chartData c
  have hL : ∀ α ∈ L, P.levelVal 1 (P.tangentProj α) = y := hO.1
  have hcod : quotDim N c.red = 1 := hspan ▸ hadm.1 c
  have hrankK : finrank ℝ ↥(N ⊓ c.red) = m := by
    have := finrank_inf_eq_of_quotDim_eq_one hcod
    omega
  obtain ⟨e, he, heo⟩ := hadm.exists_outward hO
  have hwN : c.vec w ∈ N := by rw [← hspan]; exact subset_span (mem_image_of_mem _ hw)
  have heN : c.vec e ∈ N := by rw [← hspan]; exact subset_span (mem_image_of_mem _ he)
  obtain ⟨t, ht, htS⟩ := exists_coeff_halfSpace (S := c.cone)
    (fun a ha b hb => c.add_mem_cone ha hb) (fun t ht a ha => c.smul_mem_cone ht ha)
    c.red_subset_cone (fun a ha ha' => c.mem_red_of_mem_cone ha ha') hcod hwN
    ((isInwardVec_iff c (hL w hw)).1 hwin) (fun h => hwred ((isReducedVec_iff c (hL w hw)).2 h))
    (c.vec e) heN
  have ht0 : t < 0 := lt_of_not_ge fun h => heo ((isInwardVec_iff c (hL e he)).2 (htS.2 h))
  have hmem : chartVec c.isChart e - t • chartVec c.isChart w ∈ N ⊓ c.red :=
    Submodule.mem_inf.2 ⟨Submodule.sub_mem _ heN (Submodule.smul_mem _ _ hwN), ht⟩
  have h := boundaryOp_frames_eq hO hadm he heo
  intro hmemf
  exact boundaryFrames_disjoint_of_neg hO (fun α hα => hα.1) c.isChart c.mem_source (N ⊓ c.red)
    hNK hrankK hw he ht0 hmem ⟨ha, hcons⟩ (h ▸ hmemf)

/-! ### Outward and inward vectors from one coordinate -/

/-- A vector over `y` whose `i`-th quadrant coordinate in a presented chart is negative, where
the `i`-th coordinate of `y` vanishes, does not lie in `C_yX`: it points outward. -/
theorem not_isInwardVec_of_coord_neg {y : X} (c : P.PresentedChart y) (i : Fin c.n)
    (hi : (c.T 0 (c.φ y)).1 i = 0) {w : P.TangentSpace} (hneg : (c.T 0 (c.vec w)).1 i < 0) :
    ¬ P.IsInwardVec y w := fun h => absurd (h c i hi) (not_le.2 hneg)

/-- **In the situation of Definition 9.3.8, a vector of `T_yM` with a positive quadrant
coordinate lies in `C_yX ∖ T^R_yX`**, if that coordinate of `y` vanishes. -/
theorem isInwardVec_of_coord_pos {y : X} {g : OrTangent P} (hO : P.IsOrientedAt y g)
    (hadm : P.IsBoundaryAdmissible y g) (c : P.PresentedChart y) (i : Fin c.n)
    (hi : (c.T 0 (c.φ y)).1 i = 0) {w : P.TangentSpace} (hw : w ∈ g.carrier)
    (hpos : 0 < (c.T 0 (c.vec w)).1 i) : P.IsInwardVec y w ∧ ¬ P.IsReducedVec y w := by
  obtain ⟨s, hs, hsin, hsred⟩ := hadm.2
  have hL := hO.1
  have hsN : c.vec s ∈ span ℝ (c.vec '' g.carrier) := subset_span (mem_image_of_mem _ hs)
  have hwN : c.vec w ∈ span ℝ (c.vec '' g.carrier) := subset_span (mem_image_of_mem _ hw)
  obtain ⟨t, ht, htS⟩ := exists_coeff_halfSpace (S := c.cone)
    (fun a ha b hb => c.add_mem_cone ha hb) (fun t ht a ha => c.smul_mem_cone ht ha)
    c.red_subset_cone (fun a ha ha' => c.mem_red_of_mem_cone ha ha') (hadm.1 c) hsN
    ((isInwardVec_iff c (hL s hs)).1 hsin) (fun h => hsred ((isReducedVec_iff c (hL s hs)).2 h))
    (c.vec w) hwN
  have hred0 : ∀ v ∈ c.red, (c.T 0 v).1 i = 0 := fun v hv =>
    (mem_minimalSubspaceWith c.T).1 hv i hi
  have h1 : (c.T 0 (c.vec w)).1 i = t * (c.T 0 (c.vec s)).1 i := by
    have h := hred0 _ ht
    simp only [map_sub, map_smul, Prod.fst_sub, Prod.smul_fst, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at h
    linarith
  have hs0 : 0 ≤ (c.T 0 (c.vec s)).1 i := hsin c i hi
  have ht0 : 0 < t := by
    by_contra h
    have := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 h) hs0
    linarith
  refine ⟨(isInwardVec_iff c (hL w hw)).2 (htS.2 ht0.le), fun h => ?_⟩
  have := hred0 _ ((isReducedVec_iff c (hL w hw)).1 h)
  linarith

/-- **In the situation of Definition 9.3.8, `T_y∂M` is cut out of `T_yM` by one coordinate**:
if some vector of `T_yM` has a nonzero `i`-th quadrant coordinate, where the `i`-th coordinate
of `y` vanishes, then a vector of `T_yM` lies in `T^R_yX` iff its `i`-th coordinate vanishes. -/
theorem isReducedVec_iff_coord_eq_zero {y : X} {g : OrTangent P} (hO : P.IsOrientedAt y g)
    (hadm : P.IsBoundaryAdmissible y g) (c : P.PresentedChart y) (i : Fin c.n)
    (hi : (c.T 0 (c.φ y)).1 i = 0) {w : P.TangentSpace} (hw : w ∈ g.carrier)
    (hw0 : (c.T 0 (c.vec w)).1 i ≠ 0) {v : P.TangentSpace} (hv : v ∈ g.carrier) :
    P.IsReducedVec y v ↔ (c.T 0 (c.vec v)).1 i = 0 := by
  obtain ⟨s, hs, hsin, hsred⟩ := hadm.2
  have hL := hO.1
  have hred0 : ∀ u ∈ c.red, (c.T 0 u).1 i = 0 := fun u hu =>
    (mem_minimalSubspaceWith c.T).1 hu i hi
  refine ⟨fun h => hred0 _ ((isReducedVec_iff c (hL v hv)).1 h), fun h0 => ?_⟩
  have hsN : c.vec s ∈ span ℝ (c.vec '' g.carrier) := subset_span (mem_image_of_mem _ hs)
  have hcoef : ∀ u ∈ g.carrier, ∃ t : ℝ, c.vec u - t • c.vec s ∈ c.red := fun u hu => by
    obtain ⟨t, ht, -⟩ := exists_coeff_halfSpace (S := c.cone)
      (fun a ha b hb => c.add_mem_cone ha hb) (fun t ht a ha => c.smul_mem_cone ht ha)
      c.red_subset_cone (fun a ha ha' => c.mem_red_of_mem_cone ha ha') (hadm.1 c) hsN
      ((isInwardVec_iff c (hL s hs)).1 hsin)
      (fun h => hsred ((isReducedVec_iff c (hL s hs)).2 h)) (c.vec u)
      (subset_span (mem_image_of_mem _ hu))
    exact ⟨t, ht⟩
  have hval : ∀ u (t : ℝ), c.vec u - t • c.vec s ∈ c.red →
      (c.T 0 (c.vec u)).1 i = t * (c.T 0 (c.vec s)).1 i := fun u t ht => by
    have h := hred0 _ ht
    simp only [map_sub, map_smul, Prod.fst_sub, Prod.smul_fst, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at h
    linarith
  obtain ⟨a, ha⟩ := hcoef w hw
  obtain ⟨b, hb⟩ := hcoef v hv
  have hs0 : (c.T 0 (c.vec s)).1 i ≠ 0 := fun h => hw0 (by rw [hval w a ha, h, mul_zero])
  have hb0 : b = 0 := by
    have := hval v b hb
    rw [h0] at this
    exact (mul_eq_zero.1 this.symm).resolve_right hs0
  rw [hb0, zero_smul, sub_zero] at hb
  exact (isReducedVec_iff c (hL v hv)).2 hb

/-! ### The boundary orientation of the stratum from one frame -/

namespace SubmanifoldOrientation

variable {M N : Set X} {m : ℕ}

/-- The situation of Definition 9.3.8 at the points of the stratum `∂₁M`. -/
theorem isBoundaryAdmissible_tangent (o : P.SubmanifoldOrientation M (m + 1))
    (hM : P.IsSmoothSubmanifold M) {y : X} (hy : y ∈ P.boundaryStratum M) :
    P.IsBoundaryAdmissible y ⟨m + 1, P.submanifoldTangent M y, o.frames y⟩ :=
  isBoundaryAdmissible_of_submanifold hM hy.1 (o.isOrientedAt y hy.1) rfl
    ((o.hasReducedCodim_iff_mem_boundaryStratum hy.1).2 hy)

/-- **The boundary orientation agrees with an orientation `o'` of the stratum if one frame
`(e, a)`, `e` outward, `a` positive for `o'`, is positive for `o`** (Definition 9.3.8, outward
normal first). -/
theorem stratumOrientation_tangent_eq_of_outward (o : P.SubmanifoldOrientation M (m + 1))
    (hM : P.IsSubmanifoldOfDim M (m + 1)) (ht : P.HasTameInducedStructure M)
    (hN : P.boundaryStratum M = N) (o' : P.SubmanifoldOrientation N m) {y : X} (hy : y ∈ N)
    {a : Fin m → P.TangentSpace} (ha : a ∈ o'.frames y) {e : P.TangentSpace}
    (he : e ∈ P.submanifoldTangent M y) (heo : ¬ P.IsInwardVec y e)
    (hcons : (Fin.cons e a : Fin (m + 1) → _) ∈ o.frames y) :
    (o.stratumOrientation hM ht).tangent y = o'.tangent y := by
  subst hN
  have hO' := o'.isOrientedAt y hy
  have hOs := (o.stratumOrientation hM ht).isOrientedAt y hy
  have haK : ∀ i, a i ∈ P.boundaryCarrier (P.submanifoldTangent M y) := fun i => by
    rw [← submanifoldTangent_boundaryStratum hM ht hy]
    exact hO'.mem_carrier ha i
  have hmem : a ∈ (o.stratumOrientation hM ht).frames y :=
    mem_boundaryOp_frames_of_outward (o.isOrientedAt y hy.1)
      (o.isBoundaryAdmissible_tangent hM.1 hy) he heo haK hcons
  change (⟨m, _, _⟩ : OrTangent P) = ⟨m, _, _⟩
  rw [hOs.frames_eq_of_mem hO' hmem ha]

/-- **The boundary orientation is opposite to an orientation `o'` of the stratum if one frame
`(w, a)`, `w ∈ C_yX ∖ T^R_yX` inward, `a` positive for `o'`, is positive for `o`.** -/
theorem stratumOrientation_tangent_ne_of_inward (o : P.SubmanifoldOrientation M (m + 1))
    (hM : P.IsSubmanifoldOfDim M (m + 1)) (ht : P.HasTameInducedStructure M)
    (hN : P.boundaryStratum M = N) (o' : P.SubmanifoldOrientation N m) {y : X} (hy : y ∈ N)
    {a : Fin m → P.TangentSpace} (ha : a ∈ o'.frames y) {w : P.TangentSpace}
    (hw : w ∈ P.submanifoldTangent M y) (hwin : P.IsInwardVec y w)
    (hwred : ¬ P.IsReducedVec y w) (hcons : (Fin.cons w a : Fin (m + 1) → _) ∈ o.frames y) :
    (o.stratumOrientation hM ht).tangent y ≠ o'.tangent y := by
  subst hN
  have hO' := o'.isOrientedAt y hy
  have haK : ∀ i, a i ∈ P.boundaryCarrier (P.submanifoldTangent M y) := fun i => by
    rw [← submanifoldTangent_boundaryStratum hM ht hy]
    exact hO'.mem_carrier ha i
  have hnot : a ∉ (o.stratumOrientation hM ht).frames y :=
    notMem_boundaryOp_frames_of_inward (o.isOrientedAt y hy.1)
      (o.isBoundaryAdmissible_tangent hM.1 hy) hw hwin hwred haK hcons
  intro h
  have h' : (o.stratumOrientation hM ht).frames y = o'.frames y := OrTangent.frames_eq_of_mk_eq h
  exact hnot (h' ▸ ha)

end SubmanifoldOrientation

end MPolyfold

end Polyfold
