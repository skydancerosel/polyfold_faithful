import Polyfold.Chapter9.MathlibSolutionSets
import Polyfold.Chapter6.OrientationMainClean
import Polyfold.Chapter6.ManifoldOrientation

/-!
# The natural orientation of the solution set as a Mathlib manifold

Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), **Theorem 6.6.18**
(p. 275, proof pp. 275–276; preprint Theorem 6.41), the orientation part (gap G.67).
`theorem_6_6_18` gives the natural orientation of `S = f⁻¹(0)` as a family `o_x` of orientations
of the kernels `ker f'(x)` (`IsNaturalSolutionOrientation`), and `theorem_6_6_18_isManifold`
makes `S` a Mathlib manifold with boundary and corners (`IsManifold (𝓠 d) ∞ S`).  Here the two
are joined:
`theorem_6_6_18_oriented` gives a continuous tangent orientation of that Mathlib manifold
(`TangentOrientation.IsContinuous`, `Polyfold/Chapter6/ManifoldOrientation.lean`) which at every
zero `x` is `o_x`, transported along the tangent map of `S ↪ X`.

## The construction

* `modelDeriv`, `derivIn_incl`: the tangent map of the inclusion `S ↪ X` at `x`, read in a corner
  chart `κ` of `S` (the Mathlib chart) and a chart `c` of `X`; it is injective
  (`modelDeriv_injective`) with values in `ker f'(x)` (`modelDeriv_mem_linKer`), so it is an
  isomorphism `ℝ^d ≅ ker f'(x)` (`solKerEquiv`, by the dimension count `finrank_linKer_of`).
* `pullOr`: an orientation of `ℝ^d` pulled back from an orientation of the top power of `N` along
  `ℝ^d ≅ N`.  `solReadOr`: the pull-back of `tangentOr (o_x)` read in `c`; it does not depend on
  `c` (`solReadOr_chartChange`, via `transDeriv_subChart_change`), and a change of the corner
  chart acts by the sign of the chart change (`signMap_solReadOr`).
* `solOr`: the orientation of `T_xS` so obtained; `solOr_spec` states the agreement with `o_x`
  in every chart `c` of `X` in terms of Mathlib's own chart at `x` and `derivIn`.
* Continuity (`isContinuous_solOr`): along a segment in corner coordinates
  (`eventually_exists_segPath`) the kernels form a line bundle with a continuous frame
  (`isLineOrientation_solKer`), and `o` is continuous along it (`exists_isOrientableNbhd`,
  `IsNaturalSolutionOrientation.continuous`); two orientations of a line bundle over a connected
  base agree everywhere once they agree at one point (`IsLineOrientation.eq_iff_eq`).

## Relation to the book

The book's sentence is that `S` is a compact manifold with boundary with corners with a natural
orientation; the proof says that `o_x` orients `T_xS = ker f'(x)` and that the local prolongation
of this orientation on `S` is the Fredholm one, which is `isContinuous_solOr`.  The one hypothesis
beyond `theorem_6_6_18` is `hbump : PX.AdmitsBumpFunctions`, the one of `theorem_6_6_13` and
`theorem_6_6_17` (the standing hypotheses of Theorem 6.6.11 as read here): it gives the orientable
neighbourhoods (`exists_isOrientableNbhd`) on which Definition 6.6.16 makes `o` continuous; it
holds on Hilbert models (`MPolyfold.admitsBumpFunctions_of_hilbert`).
-/

open Set Filter Topology Manifold Module Bundle WithLp
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

/-! ### sc¹ maps with a finite-dimensional domain are differentiable -/

/-- **An sc¹ map with finite-dimensional domain is differentiable on `U`** (the levels of `E` are
all `E₀`, `ScBanach.scIsoConst`), with derivative `scDeriv`. -/
theorem IsSc1.hasFDerivWithinAt_of_finiteDimensional {E F : ScBanach} [FiniteDimensional ℝ (E 0)]
    {U : Set (E 0)} {f : E 0 → F 0} (hf : IsSc1 U f) {x : E 1} (hx : E.toBase 1 x ∈ U) :
    HasFDerivWithinAt f (scDeriv U f x) U (E.toBase 1 x) := by
  set e := E.scIsoConst 1
  have he : ∀ y, E.toBase 1 (e.symm y) = y := fun y => e.apply_symm_apply y
  have hx' : e.symm (E.toBase 1 x) = x := e.symm_apply_apply x
  have hD : HasFDerivWithinAt (f ∘ E.toBase 1) ((scDeriv U f x).comp (E.toBase 1))
      (E.lvlSet U 1) (e.symm (E.toBase 1 x)) := by
    rw [hx']; exact hf.isSc1With_scDeriv.hasFDerivWithinAt x hx
  have h2 := hD.comp (E.toBase 1 x) e.symm.hasFDerivAt.hasFDerivWithinAt
    (fun y hy => by change E.toBase 1 (e.symm y) ∈ U; rw [he]; exact hy)
  refine (h2.congr_fderiv ?_).congr (fun y _ => ?_) ?_
  · ext v
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearEquiv.coe_coe]
    rw [he]
  · simp only [Function.comp_apply, he]
  · simp only [Function.comp_apply, he]

/-! ### Orientations pulled back along linear isomorphisms -/

section PullOr

/-- **In a line every ray is that of `v` or of `-v`.** -/
theorem ray_eq_or_eq_neg_of_finrank_eq_one {L : Type*} [AddCommGroup L] [Module ℝ L]
    (h1 : finrank ℝ L = 1) {v : L} (hv : v ≠ 0) (r : Module.Ray ℝ L) :
    r = rayOfNeZero ℝ v hv ∨ r = -rayOfNeZero ℝ v hv := by
  induction r using Module.Ray.ind with | h w hw => ?_
  obtain ⟨c, rfl⟩ := exists_smul_eq_of_finrank_eq_one h1 hv w
  have hc : c ≠ 0 := by rintro rfl; exact hw (zero_smul ℝ v)
  rcases hc.lt_or_gt with hc | hc
  · right
    rw [neg_rayOfNeZero, ray_eq_iff]
    have : c • v = (-c) • (-v) := by rw [neg_smul_neg]
    rw [this]
    exact SameRay.sameRay_pos_smul_left _ (neg_pos.2 hc)
  · left
    rw [ray_eq_iff]
    exact SameRay.sameRay_pos_smul_left _ hc

/-- The case analysis behind `orientation_eq_pullOr_iff`. -/
theorem ite_neg_eq_ite_iff {α β : Type*} [Neg α] [Neg β] {o : α} {ρ r : β}
    (ho : o ≠ -o) (hρ : ρ ≠ -ρ) (hr : r = ρ ∨ r = -ρ) (p : Prop) [Decidable p]
    [Decidable (r = ρ)] :
    ((if p then o else -o) = if r = ρ then o else -o) ↔ r = if p then ρ else -ρ := by
  have h' : -ρ ≠ ρ := fun h => hρ h.symm
  rcases hr with rfl | rfl
  · by_cases hp : p
    · rw [if_pos hp, if_pos rfl, if_pos hp]; exact iff_of_true rfl rfl
    · rw [if_neg hp, if_pos rfl, if_neg hp]; exact iff_of_false (Ne.symm ho) hρ
  · by_cases hp : p
    · rw [if_pos hp, if_neg h', if_pos hp]; exact iff_of_false ho h'
    · rw [if_neg hp, if_neg h', if_neg hp]; exact iff_of_true rfl rfl

variable {E N : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup N] [Module ℝ N] {k : ℕ} (hk : finrank ℝ E = k)

/-- The basis of `E` used to define `pullOr`. -/
abbrev pullBasis : Basis (Fin k) ℝ E := Module.finBasisOfFinrankEq ℝ E hk

/-- The wedge of the image of a basis under an isomorphism is not zero. -/
theorem wedge_equiv_ne_zero (L : E ≃ₗ[ℝ] N) (b : Basis (Fin k) ℝ E) :
    wedge (fun i => L (b i)) (hk.symm.trans L.finrank_eq) ≠ 0 := by
  have := L.finiteDimensional
  exact (wedge_ne_zero_iff _).2 (b.linearIndependent.map' L.toLinearMap L.ker)

open scoped Classical in
/-- **The orientation of `E` pulled back from a ray `r` of `λ(N)` along `L : E ≅ N`**: a basis
`b` of `E` is positive iff `L(b₁) ∧ … ∧ L(bₖ)` lies in `r` (`orientation_eq_pullOr_iff`). -/
def pullOr (L : E ≃ₗ[ℝ] N) (r : Module.Ray ℝ (maxPow N)) : Orientation ℝ E (Fin k) :=
  if r = rayOfNeZero ℝ _ (wedge_equiv_ne_zero hk L (pullBasis hk)) then (pullBasis hk).orientation
  else -(pullBasis hk).orientation

omit [FiniteDimensional ℝ E] in
/-- The orientation of a basis `b` is that of a basis `b₀` or its opposite, by the sign of
`det_{b₀} b`. -/
theorem orientation_eq_ite_det_pos (b₀ b : Basis (Fin k) ℝ E) :
    b.orientation = if 0 < b₀.det b then b₀.orientation else -b₀.orientation := by
  split_ifs with h
  · exact ((b₀.orientation_eq_iff_det_pos b).2 h).symm
  · refine (b₀.orientation_ne_iff_eq_neg b.orientation).1 fun he => h ?_
    exact (b₀.orientation_eq_iff_det_pos b).1 he.symm

/-- **The characterization of `pullOr`**: `b` is positive for `pullOr L r` iff
`L(b₁) ∧ … ∧ L(bₖ) ∈ r`. -/
theorem orientation_eq_pullOr_iff (L : E ≃ₗ[ℝ] N) (r : Module.Ray ℝ (maxPow N))
    (b : Basis (Fin k) ℝ E) :
    b.orientation = pullOr hk L r ↔ r = rayOfNeZero ℝ _ (wedge_equiv_ne_zero hk L b) := by
  have := L.finiteDimensional
  set b₀ := pullBasis hk
  have hw : wedge (fun i => L (b i)) (hk.symm.trans L.finrank_eq) =
      b₀.det b • wedge (fun i => L (b₀ i)) (hk.symm.trans L.finrank_eq) :=
    wedge_comp_basis (L : E →ₗ[ℝ] N) b₀ b _
  have hdet : b₀.det b ≠ 0 := (b₀.isUnit_det b).ne_zero
  set ρ₀ := rayOfNeZero ℝ _ (wedge_equiv_ne_zero hk L b₀)
  have hρ : rayOfNeZero ℝ _ (wedge_equiv_ne_zero hk L b) = if 0 < b₀.det b then ρ₀ else -ρ₀ := by
    split_ifs with h
    · rw [ray_eq_iff, hw]; exact SameRay.sameRay_pos_smul_left _ h
    · have h' : b₀.det b < 0 := lt_of_le_of_ne (not_lt.1 h) hdet
      rw [neg_rayOfNeZero, ray_eq_iff, hw]
      have : b₀.det b • wedge (fun i => L (b₀ i)) (hk.symm.trans L.finrank_eq) =
          (-b₀.det b) • -wedge (fun i => L (b₀ i)) (hk.symm.trans L.finrank_eq) := by
        rw [neg_smul_neg]
      rw [this]
      exact SameRay.sameRay_pos_smul_left _ (neg_pos.2 h')
  rw [hρ, orientation_eq_ite_det_pos b₀ b]
  unfold pullOr
  classical
  convert ite_neg_eq_ite_iff (Module.Ray.ne_neg_self b₀.orientation) (Module.Ray.ne_neg_self ρ₀)
    (ray_eq_or_eq_neg_of_finrank_eq_one finrank_maxPow (wedge_equiv_ne_zero hk L b₀) r)
    (0 < b₀.det b)

/-- **`pullOr` is natural in the target**: for `T : N ≅ N'`, pulling `λ(T) r` back along `T ∘ L`
is pulling `r` back along `L`. -/
theorem pullOr_trans {N' : Type*} [AddCommGroup N'] [Module ℝ N'] (L : E ≃ₗ[ℝ] N)
    (T : N ≃ₗ[ℝ] N') (r : Module.Ray ℝ (maxPow N)) :
    pullOr hk (L.trans T) (Module.Ray.map (maxPowEquiv T) r) = pullOr hk L r := by
  have hmap : Module.Ray.map (maxPowEquiv T)
      (rayOfNeZero ℝ _ (wedge_equiv_ne_zero hk L (pullBasis hk))) =
      rayOfNeZero ℝ _ (wedge_equiv_ne_zero hk (L.trans T) (pullBasis hk)) := by
    rw [Module.Ray.map_apply]
    congr 1
    rw [maxPowEquiv_wedge]
    rfl
  unfold pullOr
  rw [← hmap, (Module.Ray.map (maxPowEquiv T)).injective.eq_iff]

/-- **`pullOr` is natural in the source**: for an automorphism `A` of `E`,
`A_* (pullOr (L ∘ A) r) = pullOr L r`. -/
theorem map_pullOr_comp (L : E ≃ₗ[ℝ] N) (A : E ≃ₗ[ℝ] E) (r : Module.Ray ℝ (maxPow N)) :
    Orientation.map (Fin k) A (pullOr hk (A.trans L) r) = pullOr hk L r := by
  set b₀ := pullBasis hk
  have key : (b₀.orientation = pullOr hk (A.trans L) r) ↔
      ((b₀.map A).orientation = pullOr hk L r) := by
    rw [orientation_eq_pullOr_iff, orientation_eq_pullOr_iff]
    constructor <;> intro h <;> rw [h] <;> rfl
  rcases b₀.orientation_eq_or_eq_neg (pullOr hk (A.trans L) r) with h | h
  · rw [h, ← b₀.orientation_map]
    exact key.1 h.symm
  · have hne : (b₀.map A).orientation ≠ pullOr hk L r := fun h' =>
      (Module.Ray.ne_neg_self b₀.orientation) (h.symm.trans (key.2 h').symm).symm
    rw [h, Orientation.map_neg, ← b₀.orientation_map]
    exact ((b₀.map A).orientation_ne_iff_eq_neg _).1 (Ne.symm hne) |>.symm

end PullOr

section PullOrMore

variable {E N : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E] [AddCommGroup N]
  [Module ℝ N] {k : ℕ} (hk : finrank ℝ E = k)

/-- `pullOr` along `L'` equals `pullOr` along `L` when `L' = T ∘ L` and the ray is moved by `T`
(`pullOr_trans`). -/
theorem pullOr_eq_of_comp {N' : Type*} [AddCommGroup N'] [Module ℝ N'] {L : E ≃ₗ[ℝ] N}
    {L' : E ≃ₗ[ℝ] N'} {T : N ≃ₗ[ℝ] N'} (hL : ∀ v, L' v = T (L v)) (r : Module.Ray ℝ (maxPow N)) :
    pullOr hk L' (Module.Ray.map (maxPowEquiv T) r) = pullOr hk L r := by
  obtain rfl : L' = L.trans T := LinearEquiv.ext hL
  exact pullOr_trans hk L T r

/-- `pullOr hk L r = pullOr hk L' r'` as soon as `r` is the ray of `L(b₀)` exactly when `r'` is the
ray of `L'(b₀)`, `b₀ = pullBasis hk`. -/
theorem pullOr_eq_of_iff {N' : Type*} [AddCommGroup N'] [Module ℝ N'] {L : E ≃ₗ[ℝ] N}
    {L' : E ≃ₗ[ℝ] N'} {r : Module.Ray ℝ (maxPow N)} {r' : Module.Ray ℝ (maxPow N')}
    (h : r = rayOfNeZero ℝ _ (wedge_equiv_ne_zero hk L (pullBasis hk)) ↔
      r' = rayOfNeZero ℝ _ (wedge_equiv_ne_zero hk L' (pullBasis hk))) :
    pullOr hk L r = pullOr hk L' r' := by
  unfold pullOr
  classical
  exact if_congr h rfl rfl

end PullOrMore

section SignMapPullOr

variable {E N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup N] [Module ℝ N] {k : ℕ} (hk : finrank ℝ E = k)

/-- **`pullOr` under a change of the linear coordinates**: if `L ∘ D = L'`, then `D` moves
`pullOr hk L' r` to `pullOr hk L r` (`signMap`, `map_eq_signMap`). -/
theorem signMap_pullOr {L L' : E ≃ₗ[ℝ] N} {D : E →L[ℝ] E} (hD : ∀ v, L (D v) = L' v)
    (r : Module.Ray ℝ (maxPow N)) : signMap D (pullOr hk L' r) = pullOr hk L r := by
  set A : E ≃ₗ[ℝ] E := L.trans L'.symm
  have hA : A.trans L' = L := LinearEquiv.ext fun v => by simp [A]
  have h1 := map_pullOr_comp hk L' A r
  rw [hA] at h1
  have hAD : ∀ v, A.symm v = D v := fun v => by
    simp only [A, LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm, ← hD v,
      LinearEquiv.symm_apply_apply]
  rw [← h1, ← map_eq_signMap A.symm hAD (by rw [Fintype.card_fin]; exact hk.symm),
    ← Orientation.map_symm, Equiv.symm_apply_apply]

end SignMapPullOr

/-! ### Comparing two orientations of a line bundle over a connected base -/

section LineOr

/-- **A frame over the whole base orients `λ(Λ)`**: `q ↦ [e₁(q) ∧ … ∧ eₙ(q)]`. -/
theorem SubspaceFamily.Frame.isLineOrientation {Q : Type*} [TopologicalSpace Q] {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] {Λ : SubspaceFamily Q W} (ε : Λ.Frame)
    (hU : ε.U = univ) :
    IsLineOrientation Λ.det fun q =>
      rayOfNeZero ℝ (ε.wedgeAt q) (ε.wedgeAt_ne_zero (hU ▸ mem_univ q)) := by
  intro q₀
  refine ⟨univ, univ_mem, ε.wedgeAt, ?_, fun q _ => ⟨_, rfl⟩⟩
  rw [← hU]
  exact SubspaceFamily.Frame.continuousOn_wedgeAt Λ ε

theorem IsLineOrientation.congr {Q : Type*} [TopologicalSpace Q] {L : Q → Type*}
    [∀ q, AddCommMonoid (L q)] [∀ q, Module ℝ (L q)] [TopologicalSpace (TotalSpace ℝ L)]
    {o o' : ∀ q, Module.Ray ℝ (L q)} (ho : IsLineOrientation L o) (h : ∀ q, o q = o' q) :
    IsLineOrientation L o' := by
  obtain rfl : o = o' := funext h
  exact ho

variable {Q : Type*} [TopologicalSpace Q] {L : Q → Type*} [∀ q, AddCommMonoid (L q)]
  [∀ q, Module ℝ (L q)] [TopologicalSpace (TotalSpace ℝ L)] [∀ q, TopologicalSpace (L q)]
  [FiberBundle ℝ L] [VectorBundle ℝ ℝ L]

/-- **Two orientations of a line bundle over a preconnected base agree everywhere or nowhere**:
the set where they agree is open and closed (the argument of `LineOrientation.eq_of_apply_eq`). -/
theorem IsLineOrientation.eq_iff_eq [PreconnectedSpace Q] {o o' : ∀ q, Module.Ray ℝ (L q)}
    (ho : IsLineOrientation L o) (ho' : IsLineOrientation L o') (q q' : Q) :
    o q = o' q ↔ o q' = o' q' := by
  have hloc : ∀ q₀, ∀ᶠ q in 𝓝 q₀, (o q = o' q ↔ o q₀ = o' q₀) := by
    intro q₀
    have hq₀ := FiberBundle.mem_baseSet_trivializationAt ℝ L q₀
    filter_upwards [ho.eventually_posRay_iff _ hq₀, ho'.eventually_posRay_iff _ hq₀,
      (trivializationAt ℝ L q₀).open_baseSet.mem_nhds hq₀] with q h1 h2 hq
    exact (eq_iff_posRay_iff _ hq _ _).trans
      ((iff_congr h1 h2).trans (eq_iff_posRay_iff _ hq₀ _ _).symm)
  have hA : IsClopen {q | o q = o' q} :=
    ⟨isOpen_compl_iff.1 (isOpen_iff_mem_nhds.2 fun q₀ hq₀ =>
        (hloc q₀).mono fun _ hq hq' => hq₀ (hq.1 hq')),
      isOpen_iff_mem_nhds.2 fun q₀ hq₀ => (hloc q₀).mono fun _ hq => hq.2 hq₀⟩
  change q ∈ {q | o q = o' q} ↔ q' ∈ {q | o q = o' q}
  rcases isClopen_iff.1 hA with h | h <;> rw [h] <;> simp

end LineOr

/-! ### The derivative of the transition from a corner chart -/

section CornerTransition

variable {Z : Type u} [TopologicalSpace Z] {χ : MChart Z} (hc : χ.IsCornerChart)

/-- The identity retraction onto the overlap `χ(dom χ ∩ dom σ)` of a corner chart `χ` (relatively
open in the partial quadrant, `MChart.isRelOpenInQuadrant_overlap`). -/
def overlapRet (σ : MChart Z) : ScRetraction χ.model.E χ.model.C :=
  ScRetraction.id (MChart.isRelOpenInQuadrant_overlap hc.isRelOpenInQuadrant σ)

theorem overlapRet_retract (σ : MChart Z) : (overlapRet hc σ).retract = χ.overlap σ :=
  image_id _

omit hc in
/-- A retraction onto the overlap `σ(dom σ ∩ dom χ)`. -/
def overlapRet' (σ χ : MChart Z) : ScRetraction σ.model.E σ.model.C :=
  (σ.isScRetract_overlap χ).choose

omit hc in
theorem overlapRet'_retract (σ χ : MChart Z) : (overlapRet' σ χ).retract = σ.overlap χ :=
  (σ.isScRetract_overlap χ).choose_spec

/-- **The derivative of the transition `σ ∘ χ⁻¹`** from a corner chart at a level-`1` point. -/
def transDeriv (σ : MChart Z) (z : χ.model.E 1) : χ.model.E 0 →L[ℝ] σ.model.E 0 :=
  scDeriv (overlapRet hc σ).U (χ.transition σ ∘ overlapRet hc σ) z

/-- `D r(z) = id` for the identity retraction onto the overlap. -/
theorem scDeriv_overlapRet (σ : MChart Z) {z : χ.model.E 1}
    (hz : z ∈ χ.model.E.lvlSet (overlapRet hc σ).U 1) :
    scDeriv (overlapRet hc σ).U (overlapRet hc σ) z = ContinuousLinearMap.id ℝ _ :=
  IsSc1.scDeriv_eqOn (isSc1With_id _)
    ((MChart.isRelOpenInQuadrant_overlap hc.isRelOpenInQuadrant σ).isScDomain.uniqueDiffWithinAt
      1) hz

variable [T2Space Z] [ParacompactSpace Z] {Q : MPolyfold Z} {σ : MChart Z}

omit [T2Space Z] [ParacompactSpace Z] in
theorem mem_lvlSet_overlapRet {a : Z} (ha : a ∈ χ.source) (ha' : a ∈ σ.source)
    {z : χ.model.E 1} (hz : χ.model.E.toBase 1 z = χ a) :
    z ∈ χ.model.E.lvlSet (overlapRet hc σ).retract 1 := by
  rw [ScBanach.mem_lvlSet, hz, overlapRet_retract]
  exact χ.mem_overlap σ ha ha'

/-- **The transition from a corner chart is a germ of sc-diffeomorphisms** between the overlaps. -/
theorem isDiffeoGerm_transition (hχ : Q.IsChart χ) (hσ : Q.IsChart σ) :
    (overlapRet hc σ).IsDiffeoGerm (overlapRet' σ χ) (χ.transition σ) (σ.transition χ) := by
  have hcomp := MPolyfold.IsChart.compatible Q hχ hσ
  refine IsScSmoothRetractMap.isDiffeoGerm ?_ ?_ ?_ ?_
  · rw [overlapRet_retract, overlapRet'_retract]; exact hcomp.1
  · rw [overlapRet_retract, overlapRet'_retract]; exact hcomp.2
  · rw [overlapRet_retract]
    rintro _ ⟨a, ha, rfl⟩
    rw [χ.transition_apply σ ha.1, σ.transition_apply χ ha.2]
  · rw [overlapRet'_retract]
    rintro _ ⟨a, ha, rfl⟩
    rw [σ.transition_apply χ ha.1, χ.transition_apply σ ha.2]

variable (hχ : Q.IsChart χ) (hσ : Q.IsChart σ) {a : Z} (ha : a ∈ χ.source) (ha' : a ∈ σ.source)
  {z : χ.model.E 1} (hz : χ.model.E.toBase 1 z = χ a)
include hχ hσ ha ha' hz

/-- **`D(σ ∘ χ⁻¹)` is the derivative of the transition** on the overlap (a finite-dimensional
domain). -/
theorem hasFDerivWithinAt_transition :
    HasFDerivWithinAt (χ.transition σ) (transDeriv hc σ z) (χ.overlap σ) (χ a) := by
  have := hc.finiteDimensional
  have hx : χ.model.E.toBase 1 z ∈ (overlapRet hc σ).U := by
    rw [hz]; exact χ.mem_overlap σ ha ha'
  have h := IsSc1.hasFDerivWithinAt_of_finiteDimensional
    (isDiffeoGerm_transition hc hχ hσ).isSc1 hx
  rw [hz] at h
  exact h

/-- **`D(σ ∘ χ⁻¹)(z)` is injective**: `D(χ ∘ σ⁻¹ ∘ r')(y) ∘ D(σ ∘ χ⁻¹)(z) = id`
(`IsDiffeoGerm.deriv_inv_deriv`, the derivative of the identity retraction being `id`). -/
theorem transDeriv_injective : Function.Injective (transDeriv hc σ z) := by
  have hzR := mem_lvlSet_overlapRet hc ha ha' hz
  have hid := scDeriv_overlapRet hc σ ((overlapRet hc σ).lvlSet_retract_subset 1 hzR)
  intro v w hvw
  have h := fun u => (isDiffeoGerm_transition hc hχ hσ).deriv_inv_deriv hzR u
  have hv := h v
  have hw := h w
  rw [hid] at hv hw
  change _ = v at hv
  change _ = w at hw
  rw [← hv, ← hw]
  unfold transDeriv at hvw
  rw [hvw]

/-- **`D(σ ∘ χ⁻¹)(z)` takes values in the tangent space of the overlap in `σ`**
(`IsDiffeoGerm.deriv_mem_range`). -/
theorem transDeriv_mem_tangentSpace (v : χ.model.E 0) :
    transDeriv hc σ z v ∈ tangentSpace σ.model.E σ.model.C (σ.overlap χ)
      (levelMap (χ.transition σ ∘ overlapRet hc σ) 1 z) := by
  have hzR := mem_lvlSet_overlapRet hc ha ha' hz
  have hG := isDiffeoGerm_transition hc hχ hσ
  have hid := scDeriv_overlapRet hc σ ((overlapRet hc σ).lvlSet_retract_subset 1 hzR)
  have h := hG.deriv_mem_range hzR (v := v) ⟨v, by rw [hid]; rfl⟩
  rw [← overlapRet'_retract σ χ, tangentSpace_eq_range _ (hG.image_mem hzR)]
  exact h

/-- The level-`1` point `(σ ∘ χ⁻¹)₁(z)` lies over `σ(a)`. -/
theorem toBase_levelMap_transition :
    σ.model.E.toBase 1 (levelMap (χ.transition σ ∘ overlapRet hc σ) 1 z) = σ a := by
  have hzR := mem_lvlSet_overlapRet hc ha ha' hz
  rw [(isDiffeoGerm_transition hc hχ hσ).toBase_image hzR, hz, χ.transition_apply σ ha]

end CornerTransition

/-! ### The tangent map of the inclusion of a sub-M-polyfold, read in the Mathlib charts -/

section Inclusion

local notation "𝓠" => modelWithCornersEuclideanQuadrant

/-- The coordinates `ℝⁿ → ℝⁿ` (`ofLp`) as a continuous linear map. -/
abbrev ofLpCLM (n : ℕ) : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin n → ℝ) :=
  (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin n => ℝ).toContinuousLinearMap

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {A : Set X} [ParacompactSpace A] {hY : PX.IsSubMPolyfold A} {n : ℕ}
  (κ : MPolyfold.CornerCoords (MPolyfold.subPolyfold hY) n)

namespace MPolyfold.CornerCoords

/-- The Mathlib chart of `κ`, extended to `ℝⁿ`: `x ↦ Ψ χ(x) + c`. -/
theorem extend_apply {x : A} (hx : x ∈ κ.s) :
    κ.toQuadrantChart.extend (𝓠 n) x = toLp 2 (κ.coord x) := by
  rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply, κ.toQuadrantChart_apply]
  exact quadrant_right_inv fun i => κ.coord_nonneg hx i

/-- On `range I = [0,∞)ⁿ`, the inverse of the extended chart is `y ↦ χ⁻¹(Ψ⁻¹(y − c))`. -/
theorem extend_symm_apply {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ range (𝓠 n)) :
    (κ.toQuadrantChart.extend (𝓠 n)).symm y = κ.coordInv (ofLp y) := by
  rw [OpenPartialHomeomorph.extend_coe_symm, Function.comp_apply, κ.toQuadrantChart_symm_apply]
  congr 2
  exact (𝓠 n).right_inv hy

/-- A point of the target of the extended chart lies over `W ∩ [0,∞)ⁿ`. -/
theorem mem_W_of_mem_extend_target {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ (κ.toQuadrantChart.extend (𝓠 n)).target) : ofLp y ∈ κ.W ∧ ∀ i, 0 ≤ y i := by
  rw [OpenPartialHomeomorph.extend_target] at hy
  obtain ⟨hy1, q, rfl⟩ := hy
  refine ⟨?_, fun i => q.2 i⟩
  have h := κ.mem_toQuadrantChart_target.1 hy1
  rw [(𝓠 n).left_inv] at h
  exact h

end MPolyfold.CornerCoords

open MPolyfold

variable {φ : MChart X} (hφ : PX.IsChart φ) (d : PX.SubData A) (a₀ : A)

/-- **The tangent map of the inclusion `A → X`, read in the corner chart `κ` of `A` and the chart
`φ` of `X`**: `D(σ ∘ χ⁻¹)(z) ∘ Ψ⁻¹`, for `σ` the induced chart of `A` (`subChart`). -/
def modelDeriv (z : κ.χ.model.E 1) : EuclideanSpace ℝ (Fin n) →L[ℝ] φ.model.E 0 :=
  (transDeriv κ.isCornerChart (subChart d hφ a₀) z).comp
    (κ.Ψ.symm.toContinuousLinearMap.comp (ofLpCLM n))

variable {x : A} (hxκ : x ∈ κ.s) (hxσ : x ∈ (subChart d hφ a₀).source) {z : κ.χ.model.E 1}
  (hz : κ.χ.model.E.toBase 1 z = κ.χ x)
include hxκ hxσ hz

/-- **The inclusion is differentiable in the charts**, with derivative `modelDeriv`:
`φ ∘ ι ∘ (κ.extend)⁻¹ = (σ ∘ χ⁻¹) ∘ (y ↦ Ψ⁻¹(y − c))` near `κ(x)` in `[0,∞)ⁿ`. -/
theorem hasFDerivWithinAt_incl :
    HasFDerivWithinAt ((fun b : A => φ b.1) ∘ (κ.toQuadrantChart.extend (𝓠 n)).symm)
      (modelDeriv κ hφ d a₀ z) (range (𝓠 n)) (κ.toQuadrantChart.extend (𝓠 n) x) := by
  set e := κ.toQuadrantChart
  set σ := subChart d hφ a₀
  have hχ : (subPolyfold hY).IsChart κ.χ := κ.isChart
  have hσ : (subPolyfold hY).IsChart σ := subPolyfold_isChart hY d hφ a₀
  have hxe : x ∈ e.source := hxκ
  set T := (e.extend (𝓠 n)).target ∩ (e.extend (𝓠 n)).symm ⁻¹' σ.source
  have hT : T ∈ 𝓝[range (𝓠 n)] (e.extend (𝓠 n) x) := by
    refine inter_mem (e.extend_target_mem_nhdsWithin hxe) (nhdsWithin_le_nhds ?_)
    refine (e.continuousAt_extend_symm hxe).preimage_mem_nhds (σ.isOpen_source.mem_nhds ?_)
    rw [e.extend_left_inv hxe]; exact hxσ
  set Aff : EuclideanSpace ℝ (Fin n) → κ.χ.model.E 0 := fun y => κ.Ψ.symm (ofLp y - κ.c)
  have hAff : HasFDerivAt Aff (κ.Ψ.symm.toContinuousLinearMap.comp (ofLpCLM n))
      (e.extend (𝓠 n) x) := by
    have h := ((κ.Ψ.symm.toContinuousLinearMap.comp (ofLpCLM n)).hasFDerivAt
      (x := e.extend (𝓠 n) x)).sub_const (κ.Ψ.symm κ.c)
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
    simp only [Aff, map_sub, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    rfl
  have hAffx : Aff (e.extend (𝓠 n) x) = κ.χ x := by
    rw [show e.extend (𝓠 n) x = toLp 2 (κ.coord x) from κ.extend_apply hxκ]
    simp only [Aff, MPolyfold.CornerCoords.coord, add_sub_cancel_right,
      ContinuousLinearEquiv.symm_apply_apply]
  have hpt : ∀ y ∈ T, κ.coordInv (ofLp y) ∈ κ.s ∧ κ.coordInv (ofLp y) ∈ σ.source ∧
      Aff y = κ.χ (κ.coordInv (ofLp y)) := by
    intro y hy
    have hyr : y ∈ range (𝓠 n) := e.extend_target_subset_range hy.1
    have hsym := κ.extend_symm_apply hyr
    obtain ⟨hyW, hy0⟩ := κ.mem_W_of_mem_extend_target hy.1
    refine ⟨κ.coordInv_mem hyW hy0, ?_, (κ.apply_coordInv hyW hy0).symm⟩
    have := hy.2
    rwa [mem_preimage, hsym] at this
  have hmaps : MapsTo Aff T (κ.χ.overlap σ) := fun y hy => by
    obtain ⟨h1, h2, h3⟩ := hpt y hy
    rw [h3]; exact κ.χ.mem_overlap σ (κ.s_subset h1) h2
  have hF := hasFDerivWithinAt_transition κ.isCornerChart hχ hσ (κ.s_subset hxκ) hxσ hz
  rw [← hAffx] at hF
  have h := hF.comp (e.extend (𝓠 n) x) hAff.hasFDerivWithinAt hmaps
  refine (HasFDerivWithinAt.congr' h (fun y hy => ?_) ?_).mono_of_mem_nhdsWithin hT
  · obtain ⟨h1, h2, h3⟩ := hpt y hy
    simp only [Function.comp_apply]
    rw [h3, κ.χ.transition_apply σ (κ.s_subset h1),
      κ.extend_symm_apply (e.extend_target_subset_range hy.1)]
    rfl
  · exact ⟨(e.extend (𝓠 n)).map_source (by rwa [e.extend_source]),
      by rw [mem_preimage, e.extend_left_inv hxe]; exact hxσ⟩

/-- **The tangent map of the inclusion read in charts is `modelDeriv`** (`derivIn` of
`ManifoldOrientation.lean`). -/
theorem derivIn_incl :
    derivIn (𝓠 n) κ.toQuadrantChart (fun b : A => φ b.1) x = modelDeriv κ hφ d a₀ z := by
  have h := hasFDerivWithinAt_incl κ hφ d a₀ hxκ hxσ hz
  refine h.fderivWithin ?_
  rw [OpenPartialHomeomorph.extend_coe]
  exact (𝓠 n).uniqueDiffWithinAt_image

/-- **The tangent map of the inclusion is injective** (`transDeriv_injective`). -/
theorem modelDeriv_injective : Function.Injective (modelDeriv κ hφ d a₀ z) := by
  have hσ := subPolyfold_isChart hY d hφ a₀
  refine (transDeriv_injective κ.isCornerChart κ.isChart hσ (κ.s_subset hxκ) hxσ hz).comp ?_
  exact κ.Ψ.symm.injective.comp (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin n => ℝ).injective

end Inclusion

/-! ### The tangent map of `S ↪ X` takes values in `ker f'(x)` -/

section SolutionSet

open MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y} [ParacompactSpace (solutionSet P f)] {hY : PX.IsSubMPolyfold (solutionSet P f)}
  {n : ℕ} (κ : CornerCoords (subPolyfold hY) n)

omit [ParacompactSpace ↑(solutionSet P f)] in
/-- **The tangent space of `S` in an induced chart is the kernel**: for the chart
`σ = subChart d c a₀` of `S` induced by a strong bundle chart `c`, at a zero `x` in general
position and the level-`1` point `w` over `c(x)`, the tangent space of the overlap `σ(dom σ ∩ V)`
(`V` open in `S`) is `ker Lin(w)` (`tangentSpace_solutionSet_eq_linKer`, the tangent space of a
retract being a germ, `tangentSpace_inter_isOpen`). -/
theorem tangentSpace_subChart_overlap (hft : B.IsScFredholmSectionTame f)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (d : PX.SubData (solutionSet P f))
    (a₀ : solutionSet P f) (χ : MChart (solutionSet P f)) {x : solutionSet P f}
    (hxσ : x ∈ (subChart d c.isChart a₀).source) (hxχ : x ∈ χ.source)
    (hgp : B.IsGeneralPositionGerm f x.1) {w : c.φ.model.E 1}
    (hw : c.φ.model.E.toBase 1 w = c.φ x.1) :
    tangentSpace c.φ.model.E c.φ.model.C ((subChart d c.isChart a₀).overlap χ) w =
      c.linKer f w := by
  obtain ⟨W, hWo, hxW, hW⟩ :=
    tangentSpace_solutionSet_eq_linKer hft hgp (show IsZeroAt P f x.1 from x.2)
  have hxs : x.1 ∈ d.shrink c.φ := hxσ
  have hxG : x.1 ∈ d.shrink c.φ ∩ W := ⟨hxs, hxW⟩
  have hGS : c.φ '' ((d.shrink c.φ ∩ W) ∩ solutionSet P f) =
      (subChart d c.isChart a₀) '' ((subChart d c.isChart a₀).source ∩ Subtype.val ⁻¹' W) := by
    ext u
    constructor
    · rintro ⟨y, ⟨⟨hy, hyW⟩, hyS⟩, rfl⟩
      exact ⟨⟨y, hyS⟩, ⟨hy, hyW⟩, rfl⟩
    · rintro ⟨y, ⟨hy, hyW⟩, rfl⟩
      exact ⟨y.1, ⟨⟨hy, hyW⟩, y.2⟩, rfl⟩
  have hs : (subChart d c.isChart a₀).source ∩ Subtype.val ⁻¹' W ⊆
      (subChart d c.isChart a₀).source := inter_subset_left
  have hso : IsOpen ((subChart d c.isChart a₀).source ∩ Subtype.val ⁻¹' W) :=
    (subChart d c.isChart a₀).isOpen_source.inter (hWo.preimage continuous_subtype_val)
  have hQ : IsScRetract c.φ.model.E c.φ.model.C
      (c.φ '' ((d.shrink c.φ ∩ W) ∩ solutionSet P f)) := by
    rw [hGS]; exact (subChart d c.isChart a₀).isScRetract_image hs hso
  have hker := hW c hc (d.shrink_subset_source c.φ hxs) (d.shrink c.φ ∩ W)
    ((d.isOpen_shrink c.φ).inter hWo) (inter_subset_left.trans (d.shrink_subset_source c.φ))
    inter_subset_right hxG hQ w hw
  obtain ⟨W₁, hW₁, hW₁eq⟩ := (subChart d c.isChart a₀).exists_isOpen_image_eq
    (s := (subChart d c.isChart a₀).source ∩ χ.source) inter_subset_left
    ((subChart d c.isChart a₀).isOpen_source.inter χ.isOpen_source)
  obtain ⟨W₂, hW₂, hW₂eq⟩ := (subChart d c.isChart a₀).exists_isOpen_image_eq hs hso
  have hwσ : c.φ.model.E.toBase 1 w = subChart d c.isChart a₀ x := hw
  have hO := (subChart d c.isChart a₀).model.isScRetract
  have hm₁ : (subChart d c.isChart a₀).model.E.toBase 1 w ∈
      (subChart d c.isChart a₀).model.O ∩ W₁ := by
    rw [← hW₁eq]; exact ⟨x, ⟨hxσ, hxχ⟩, hwσ.symm⟩
  have hm₂ : (subChart d c.isChart a₀).model.E.toBase 1 w ∈
      (subChart d c.isChart a₀).model.O ∩ W₂ := by
    rw [← hW₂eq]; exact ⟨x, ⟨hxσ, hxW⟩, hwσ.symm⟩
  have h1 : tangentSpace c.φ.model.E c.φ.model.C ((subChart d c.isChart a₀).overlap χ) w =
      tangentSpace c.φ.model.E c.φ.model.C (subChart d c.isChart a₀).model.O w :=
    (congrArg (fun Q => tangentSpace c.φ.model.E c.φ.model.C Q w) hW₁eq).trans
      (tangentSpace_inter_isOpen hO hW₁ hm₁)
  have h2 : tangentSpace c.φ.model.E c.φ.model.C
      (c.φ '' ((d.shrink c.φ ∩ W) ∩ solutionSet P f)) w =
      tangentSpace c.φ.model.E c.φ.model.C (subChart d c.isChart a₀).model.O w :=
    (congrArg (fun Q => tangentSpace c.φ.model.E c.φ.model.C Q w) (hGS.trans hW₂eq)).trans
      (tangentSpace_inter_isOpen hO hW₂ hm₂)
  exact h1.trans (h2.symm.trans hker)

/-- **The tangent map of the inclusion takes values in `ker f'(x)`**: at a zero `x` in general
position, `modelDeriv` (the tangent map of `S ↪ X` in the corner chart `κ` and the chart `c`) maps
into `ker Lin(w)`, `w` over `c(x)`. -/
theorem modelDeriv_mem_linKer (hft : B.IsScFredholmSectionTame f) {c : StrongBundleChart PX P}
    (hc : B.IsChart c) (d : PX.SubData (solutionSet P f)) (a₀ : solutionSet P f)
    {x : solutionSet P f} (hxκ : x ∈ κ.s) (hxσ : x ∈ (subChart d c.isChart a₀).source)
    {z : κ.χ.model.E 1} (hz : κ.χ.model.E.toBase 1 z = κ.χ x)
    (hgp : B.IsGeneralPositionGerm f x.1) {w : c.φ.model.E 1}
    (hw : c.φ.model.E.toBase 1 w = c.φ x.1) (v : EuclideanSpace ℝ (Fin n)) :
    modelDeriv κ c.isChart d a₀ z v ∈ c.linKer f w := by
  set σ := subChart d c.isChart a₀
  have hσ := subPolyfold_isChart hY d c.isChart a₀
  have hmem := transDeriv_mem_tangentSpace κ.isCornerChart κ.isChart hσ (κ.s_subset hxκ) hxσ hz
    (κ.Ψ.symm (ofLp v))
  have hy := toBase_levelMap_transition κ.isCornerChart κ.isChart hσ (κ.s_subset hxκ) hxσ hz
  have hyw : levelMap (κ.χ.transition σ ∘ overlapRet κ.isCornerChart σ) 1 z = w :=
    c.φ.model.E.toBase_injective 1 (hy.trans hw.symm)
  rw [hyw] at hmem
  have := tangentSpace_subChart_overlap hft hc d a₀ κ.χ hxσ (κ.s_subset hxκ) hgp hw
  rw [← SetLike.mem_coe, ← this]
  exact hmem

end SolutionSet

/-! ### The tangent map of the inclusion in two charts of `X` -/

section AmbientChange

open MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {A : Set X} [ParacompactSpace A] {hY : PX.IsSubMPolyfold A}

/-- **The chain rule for the inclusion read in two charts of `X`**: for strong bundle charts `c`,
`c'` at the smooth point `x` and a corner chart `χ` of `A`,
`D(σ' ∘ χ⁻¹)(z) = D(τ ∘ r)(w) ∘ D(σ ∘ χ⁻¹)(z)`, with `τ ∘ r` the base transition of
`ChartPoint.baseDeriv`; on the common overlap `σ' ∘ χ⁻¹ = (τ ∘ r) ∘ (σ ∘ χ⁻¹)`, so this is the
chain rule (Theorem 1.3.1, `scDeriv_comp_apply'`). -/
theorem transDeriv_subChart_change {χ : MChart A} (hχ : (subPolyfold hY).IsChart χ)
    (hcχ : χ.IsCornerChart) {c c' : StrongBundleChart PX P} (hc : B.IsChart c)
    (hc' : B.IsChart c') (d d' : PX.SubData A) (a₀ a₀' : A) {x : A} (hxχ : x ∈ χ.source)
    (hxσ : x ∈ (subChart d c.isChart a₀).source)
    (hxσ' : x ∈ (subChart d' c'.isChart a₀').source) {z : χ.model.E 1}
    (hz : χ.model.E.toBase 1 z = χ x) (hs : x.1 ∈ PX.smoothSet) (u : χ.model.E 0) :
    transDeriv hcχ (subChart d' c'.isChart a₀') z u =
      (chartPtOf c hc (d.shrink_subset_source c.φ hxσ) hs).baseDeriv
        (chartPtOf c' hc' (d'.shrink_subset_source c'.φ hxσ') hs)
        (transDeriv hcχ (subChart d c.isChart a₀) z u) := by
  set σ := subChart d c.isChart a₀
  set σ' := subChart d' c'.isChart a₀'
  set p := chartPtOf c hc (d.shrink_subset_source c.φ hxσ) hs
  set p' := chartPtOf c' hc' (d'.shrink_subset_source c'.φ hxσ') hs
  have hσ := subPolyfold_isChart hY d c.isChart a₀
  have hσ' := subPolyfold_isChart hY d' c'.isChart a₀'
  -- the common overlap `U'' = χ(dom χ ∩ dom σ) ∩ W'`
  obtain ⟨W', hW', hW'eq⟩ := χ.exists_isOpen_image_eq (s := χ.source ∩ σ'.source)
    inter_subset_left (χ.isOpen_source.inter σ'.isOpen_source)
  have hU := (MChart.isRelOpenInQuadrant_overlap hcχ.isRelOpenInQuadrant σ).inter_isOpen hW'
  set U'' := χ.overlap σ ∩ W'
  have hpt : ∀ v ∈ U'', ∃ b, b ∈ χ.source ∧ b ∈ σ.source ∧ b ∈ σ'.source ∧ v = χ b := by
    rintro v ⟨⟨b, ⟨hb, hbσ⟩, rfl⟩, hvW⟩
    have : χ b ∈ χ '' (χ.source ∩ σ'.source) := by
      rw [hW'eq]; exact ⟨χ.mapsTo_model b hb, hvW⟩
    obtain ⟨b', ⟨hb', hb'σ⟩, hbb⟩ := this
    have : b' = b := by
      rw [← χ.symm_apply_apply hb', hbb, χ.symm_apply_apply hb]
    exact ⟨b, hb, hbσ, this ▸ hb'σ, rfl⟩
  have hU''σ : U'' ⊆ χ.overlap σ := inter_subset_left
  have hU''σ' : U'' ⊆ χ.overlap σ' := fun v hv => by
    obtain ⟨b, hb, -, hbσ', rfl⟩ := hpt v hv
    exact χ.mem_overlap σ' hb hbσ'
  have hcomp := MPolyfold.IsChart.compatible (subPolyfold hY) hχ hσ
  have hF : IsSc1 U'' (χ.transition σ) :=
    ((hcomp.1.mono_source (χ.isScRetract_overlap σ) hU''σ).comp_isScSmooth
      (ScRetraction.id hU) (image_id _)).isSc1
  have hg := p.isSc1_transition p'
  have hmaps : MapsTo (χ.transition σ) U'' (p.baseRet p').U := fun v hv => by
    obtain ⟨b, hb, hbσ, hbσ', rfl⟩ := hpt v hv
    rw [χ.transition_apply σ hb]
    refine (p.baseRet p').retract_subset ?_
    rw [ChartPoint.baseRet_retract]
    exact c.φ.mem_overlap c'.φ (d.shrink_subset_source c.φ hbσ)
      (d'.shrink_subset_source c'.φ hbσ')
  have hzU : z ∈ χ.model.E.lvlSet U'' 1 := by
    rw [ScBanach.mem_lvlSet, hz]
    have h' : χ x ∈ χ.model.O ∩ W' := by rw [← hW'eq]; exact ⟨x, ⟨hxχ, hxσ'⟩, rfl⟩
    exact ⟨χ.mem_overlap σ hxχ hxσ, h'.2⟩
  have hchain := scDeriv_comp_apply' hU (p.baseRet p').relOpen hF hg hmaps hzU u
  have hlev : levelMap (χ.transition σ) 1 z = p.z := by
    apply levelMap_eq_of_toBase_eq
    change p.c.φ.model.E.toBase 1 p.z = _
    rw [p.toBase_z, hz, χ.transition_apply σ hxχ]
    rfl
  have h1 : scDeriv U'' (χ.transition σ) z = transDeriv hcχ σ z :=
    scDeriv_eq_of_eqOn_relOpen hU hF (isDiffeoGerm_transition hcχ hχ hσ).isSc1 subset_rfl
      hU''σ (fun _ _ => rfl) hzU
  have heq : EqOn ((p.c.φ.transition p'.c.φ ∘ p.baseRet p') ∘ χ.transition σ)
      (χ.transition σ' ∘ overlapRet hcχ σ') U'' := fun v hv => by
    obtain ⟨b, hb, hbσ, hbσ', rfl⟩ := hpt v hv
    have hbc : b.1 ∈ c.φ.source := d.shrink_subset_source c.φ hbσ
    have hbc' : b.1 ∈ c'.φ.source := d'.shrink_subset_source c'.φ hbσ'
    have hret : (p.baseRet p') (c.φ b.1) = c.φ b.1 := by
      refine (p.baseRet p').apply_eq_self_of_mem_retract ?_
      rw [ChartPoint.baseRet_retract]
      exact c.φ.mem_overlap c'.φ hbc hbc'
    refine (congrArg (fun w : c.φ.model.E 0 => c.φ.transition c'.φ (p.baseRet p' w))
      (χ.transition_apply σ hb)).trans ?_
    change c.φ.transition c'.φ (p.baseRet p' (c.φ b.1)) = χ.transition σ' (χ b)
    rw [hret]
    exact (c.φ.transition_apply c'.φ hbc).trans (χ.transition_apply σ' hb).symm
  have h2 : scDeriv U'' ((p.c.φ.transition p'.c.φ ∘ p.baseRet p') ∘ χ.transition σ) z =
      transDeriv hcχ σ' z :=
    scDeriv_eq_of_eqOn_relOpen hU (theorem_1_3_1 hU (p.baseRet p').relOpen hF hg hmaps).1
      (isDiffeoGerm_transition hcχ hχ hσ').isSc1 subset_rfl hU''σ' heq hzU
  refine (congrFun (congrArg DFunLike.coe h2) u).symm.trans (hchain.symm.trans ?_)
  exact congr (congrArg (fun w => ⇑(scDeriv (p.baseRet p').U
    (p.c.φ.transition p'.c.φ ∘ p.baseRet p') w)) hlev) (congrFun (congrArg DFunLike.coe h1) u)

variable {n : ℕ} (κ : CornerCoords (subPolyfold hY) n)

/-- `modelDeriv` changes by the base transition derivative under a change of the ambient strong
bundle chart (`transDeriv_subChart_change` with `χ` the corner chart of `κ`). -/
theorem modelDeriv_chartChange {c c' : StrongBundleChart PX P} (hc : B.IsChart c)
    (hc' : B.IsChart c') (d d' : PX.SubData A) (a₀ a₀' : A) {x : A} (hxκ : x ∈ κ.s)
    (hxσ : x ∈ (subChart d c.isChart a₀).source)
    (hxσ' : x ∈ (subChart d' c'.isChart a₀').source) {z : κ.χ.model.E 1}
    (hz : κ.χ.model.E.toBase 1 z = κ.χ x) (hs : x.1 ∈ PX.smoothSet)
    (v : EuclideanSpace ℝ (Fin n)) :
    modelDeriv κ c'.isChart d' a₀' z v =
      (chartPtOf c hc (d.shrink_subset_source c.φ hxσ) hs).baseDeriv
        (chartPtOf c' hc' (d'.shrink_subset_source c'.φ hxσ') hs)
        (modelDeriv κ c.isChart d a₀ z v) :=
  transDeriv_subChart_change κ.isChart κ.isCornerChart hc hc' d d' a₀ a₀' (κ.s_subset hxκ) hxσ
    hxσ' hz hs _

end AmbientChange

/-! ### Segments in corner coordinates -/

section SegPath

open MPolyfold

local notation "𝓠" => modelWithCornersEuclideanQuadrant

/-- The quadrant `[0,∞)ⁿ ⊆ ℝⁿ` is convex. -/
theorem convex_range_quadrant (n : ℕ) : Convex ℝ (range (𝓠 n)) := by
  change Convex ℝ (range Subtype.val)
  rw [range_euclideanQuadrant]
  intro u hu v hv a b ha hb _
  refine fun i => ?_
  simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact add_nonneg (mul_nonneg ha (hu i)) (mul_nonneg hb (hv i))

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {A : Set X} [ParacompactSpace A] {hY : PX.IsSubMPolyfold A} {n : ℕ}
  (κ : CornerCoords (subPolyfold hY) n)

/-- **Segments in corner coordinates**: near `x₀ ∈ κ.s`, every `y` is joined to `x₀` by an
sc-smooth path of `A` (`chartSegPath`) which reads in the chart `χ` of `κ` as the segment
`χ(x₀) + τ(t)(χ(y) − χ(x₀))` and stays in `κ.s` and in a given open neighbourhood `G` of `x₀`
(the quadrant being convex). -/
theorem eventually_exists_segPath {x₀ : A} (hx₀ : x₀ ∈ κ.s) {G : Set A} (hG : IsOpen G)
    (hx₀G : x₀ ∈ G) :
    ∀ᶠ y in 𝓝 x₀, y ∈ κ.s ∧ ∃ γ : (Fin 1 → ℝ) → A,
      (rnPolyfold 1).IsScSmoothMap (subPolyfold hY) γ ∧ γ 0 = x₀ ∧ γ 1 = y ∧
      (∀ p, γ p ∈ κ.s ∧ γ p ∈ G) ∧
      ∀ p, κ.χ (γ p) = κ.χ x₀ + Real.smoothTransition (p 0) • (κ.χ y - κ.χ x₀) := by
  set e := κ.toQuadrantChart
  have hx₀e : x₀ ∈ e.source := hx₀
  have hT : (e.extend (𝓠 n)).target ∩ (e.extend (𝓠 n)).symm ⁻¹' G ∈
      𝓝[range (𝓠 n)] (e.extend (𝓠 n) x₀) := by
    refine inter_mem (e.extend_target_mem_nhdsWithin hx₀e) (nhdsWithin_le_nhds ?_)
    refine (e.continuousAt_extend_symm hx₀e).preimage_mem_nhds (hG.mem_nhds ?_)
    rw [e.extend_left_inv hx₀e]; exact hx₀G
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhdsWithin_iff.1 hT
  have hconv : Convex ℝ (Metric.ball (e.extend (𝓠 n) x₀) r ∩ range (𝓠 n)) :=
    (convex_ball _ _).inter (convex_range_quadrant n)
  have hrange : ∀ z, e.extend (𝓠 n) z ∈ range (𝓠 n) := fun z => by
    rw [e.extend_coe]; exact mem_range_self _
  have hAff : ∀ z ∈ κ.s, κ.Ψ.symm (ofLp (e.extend (𝓠 n) z) - κ.c) = κ.χ z := fun z hz => by
    rw [show e.extend (𝓠 n) z = toLp 2 (κ.coord z) from κ.extend_apply hz]
    simp only [MPolyfold.CornerCoords.coord, add_sub_cancel_right,
      ContinuousLinearEquiv.symm_apply_apply]
  filter_upwards [e.open_source.mem_nhds hx₀e,
    (e.continuousAt_extend hx₀e).preimage_mem_nhds (Metric.ball_mem_nhds (e.extend (𝓠 n) x₀) hr)]
    with y hy hyb
  refine ⟨hy, ?_⟩
  have hseg : ∀ p : Fin 1 → ℝ, ∃ b, b ∈ κ.s ∧ b ∈ G ∧
      κ.χ b = κ.χ x₀ + Real.smoothTransition (p 0) • (κ.χ y - κ.χ x₀) := by
    intro p
    have ht : Real.smoothTransition (p 0) ∈ Icc (0 : ℝ) 1 :=
      ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
    have hξ := hball (hconv.add_smul_sub_mem ⟨Metric.mem_ball_self hr, hrange x₀⟩
      ⟨hyb, hrange y⟩ ht)
    obtain ⟨hyW, hy0⟩ := κ.mem_W_of_mem_extend_target hξ.1
    have hsym := κ.extend_symm_apply (e.extend_target_subset_range hξ.1)
    refine ⟨_, κ.coordInv_mem hyW hy0, ?_, ?_⟩
    · have := hξ.2; rwa [mem_preimage, hsym] at this
    · rw [κ.apply_coordInv hyW hy0, ← hAff x₀ hx₀, ← hAff y hy]
      simp only [WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_sub, map_sub, map_add, map_smul]
      module
  set R := ScRetraction.id κ.isCornerChart.isRelOpenInQuadrant
  have hγ : ∀ p, chartSegPath κ.χ R (κ.χ x₀) (κ.χ y) p = (hseg p).choose := fun p => by
    obtain ⟨hb, -, hbχ⟩ := (hseg p).choose_spec
    change κ.χ.symm (κ.χ x₀ + Real.smoothTransition (p 0) • (κ.χ y - κ.χ x₀)) = _
    exact (congrArg κ.χ.symm hbχ).symm.trans (κ.χ.symm_apply_apply (κ.s_subset hb))
  have hU : ∀ p : Fin 1 → ℝ,
      κ.χ x₀ + Real.smoothTransition (p 0) • (κ.χ y - κ.χ x₀) ∈ R.U := fun p => by
    obtain ⟨hb, -, hbχ⟩ := (hseg p).choose_spec
    rw [← hbχ]; exact κ.χ.mapsTo_model _ (κ.s_subset hb)
  refine ⟨chartSegPath κ.χ R (κ.χ x₀) (κ.χ y),
    isScSmoothMap_chartSegPath (R := R) κ.isChart (show R.retract = κ.χ.model.O from image_id _)
      (κ.isCornerChart.mem_smooth _)
      (κ.isCornerChart.mem_smooth _) hU, ?_, ?_, fun p => ?_, fun p => ?_⟩
  · change κ.χ.symm (κ.χ x₀ + Real.smoothTransition ((0 : Fin 1 → ℝ) 0) • (κ.χ y - κ.χ x₀)) = x₀
    rw [Pi.zero_apply, Real.smoothTransition.zero, zero_smul, add_zero,
      κ.χ.symm_apply_apply (κ.s_subset hx₀)]
  · change κ.χ.symm (κ.χ x₀ + Real.smoothTransition ((1 : Fin 1 → ℝ) 0) • (κ.χ y - κ.χ x₀)) = y
    rw [Pi.one_apply, Real.smoothTransition.one, one_smul, add_sub_cancel,
      κ.χ.symm_apply_apply (κ.s_subset hy)]
  · rw [hγ p]; exact ⟨(hseg p).choose_spec.1, (hseg p).choose_spec.2.1⟩
  · rw [hγ p]; exact (hseg p).choose_spec.2.2

end SegPath

/-! ### The orientation of the Mathlib manifold `S` -/

section Orient

open MPolyfold

local notation "𝓠" => modelWithCornersEuclideanQuadrant

/-- Two rays of equal nonzero vectors are equal. -/
theorem rayOfNeZero_congr {M : Type*} [AddCommMonoid M] [Module ℝ M] {a b : M} (h : a = b)
    (ha : a ≠ 0) (hb : b ≠ 0) : rayOfNeZero ℝ a ha = rayOfNeZero ℝ b hb := by
  subst h; rfl

namespace MPolyfold.CornerCoords

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {Q : MPolyfold Z}
  {n : ℕ} (κ : CornerCoords Q n)

/-- **The level-`1` point over `χ(x)`**: the levels of the finite-dimensional model of a corner
chart are all `E₀` (`ScBanach.scIsoConst`). -/
def zOf (x : Z) : κ.χ.model.E 1 :=
  haveI := κ.isCornerChart.finiteDimensional
  (κ.χ.model.E.scIsoConst 1).symm (κ.χ x)

theorem toBase_zOf (x : Z) : κ.χ.model.E.toBase 1 (κ.zOf x) = κ.χ x := by
  have := κ.isCornerChart.finiteDimensional
  exact (κ.χ.model.E.scIsoConst 1).apply_symm_apply _

end MPolyfold.CornerCoords

section CornerCharted

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {Q : MPolyfold Z}
  {n : ℕ} (hcs : Q.HasCornerStructureOfDim n) [inst : ChartedSpace (EuclideanQuadrant n) Z]
  (hch : inst = Q.cornerChartedSpace hcs)
include hch

/-- The chart at `x` of `cornerChartedSpace hcs` is that of the chosen corner coordinates. -/
theorem chartAt_eq_of_eq (x : Z) :
    chartAt (EuclideanQuadrant n) x = (hcs.exists_cornerCoords x).choose.toQuadrantChart := by
  subst hch; rfl

theorem isManifold_of_eq : IsManifold (𝓠 n) ∞ Z := by
  subst hch; exact Q.isManifold_cornerChartedSpace hcs

/-- Every coordinate corner chart is in the maximal atlas of `cornerChartedSpace hcs`. -/
theorem mem_maximalAtlas_of_eq (κ : CornerCoords Q n) :
    κ.toQuadrantChart ∈ IsManifold.maximalAtlas (𝓠 n) ∞ Z := by
  have := isManifold_of_eq hcs hch
  exact IsManifold.subset_maximalAtlas (by subst hch; exact ⟨κ, rfl⟩)

end CornerCharted

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y} [ParacompactSpace (solutionSet P f)] {hY : PX.IsSubMPolyfold (solutionSet P f)}
  {n : ℕ}

omit [ParacompactSpace ↑(solutionSet P f)] in
/-- `ker f'(y)` has dimension `n` at a zero in general position where `f` has index `n`
(`StrongBundle.IsSurjLinOfIndex.finrank_linKer`). -/
theorem finrank_linKer_of (hft : B.IsScFredholmSectionTame f) {y : X} (hy0 : IsZeroAt P f y)
    (hgp : B.IsGeneralPositionGerm f y) (hidx : B.IsLinOfIndex f y n)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (hyc : y ∈ c.φ.source) (w : c.φ.model.E 1)
    (hw : c.φ.model.E.toBase 1 w = c.φ y) :
    FiniteDimensional ℝ (c.linKer f w) ∧ finrank ℝ (c.linKer f w) = n :=
  (StrongBundle.isSurjLinOfIndex_of_isLinSurjAt hft.isScSmooth hy0 hgp.isLinSurjAt
    hidx).finrank_linKer hft.isScSmooth hy0 hc hyc w hw

variable (hft : B.IsScFredholmSectionTame f) (κ : CornerCoords (subPolyfold hY) n)

/-- **The tangent map of `S ↪ X` at `x` as an isomorphism `ℝⁿ ≅ ker f'(x)`**: `modelDeriv` (the
tangent map read in the corner coordinates `κ` and the chart `c`) is injective with values in
`ker Lin(w)` (`modelDeriv_mem_linKer`), and both sides have dimension `n`. -/
def solKerEquiv {c : StrongBundleChart PX P} (hc : B.IsChart c) (d : PX.SubData (solutionSet P f))
    (a₀ : solutionSet P f) {x : solutionSet P f} (hxκ : x ∈ κ.s)
    (hxσ : x ∈ (subChart d c.isChart a₀).source) (hgp : B.IsGeneralPositionGerm f x.1)
    {w : c.φ.model.E 1} (hw : c.φ.model.E.toBase 1 w = c.φ x.1)
    (hdim : FiniteDimensional ℝ (c.linKer f w) ∧ finrank ℝ (c.linKer f w) = n) :
    EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] c.linKer f w :=
  haveI := hdim.1
  LinearMap.linearEquivOfInjective
    ((modelDeriv κ c.isChart d a₀ (κ.zOf x) :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] c.φ.model.E 0).codRestrict (c.linKer f w)
      (modelDeriv_mem_linKer κ hft hc d a₀ hxκ hxσ (κ.toBase_zOf x) hgp hw))
    (fun _ _ h => modelDeriv_injective κ c.isChart d a₀ hxκ hxσ (κ.toBase_zOf x)
      (congrArg Subtype.val h))
    (by rw [finrank_euclideanSpace_fin, hdim.2])

theorem coe_solKerEquiv {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (d : PX.SubData (solutionSet P f)) (a₀ : solutionSet P f) {x : solutionSet P f}
    (hxκ : x ∈ κ.s) (hxσ : x ∈ (subChart d c.isChart a₀).source)
    (hgp : B.IsGeneralPositionGerm f x.1) {w : c.φ.model.E 1}
    (hw : c.φ.model.E.toBase 1 w = c.φ x.1)
    (hdim : FiniteDimensional ℝ (c.linKer f w) ∧ finrank ℝ (c.linKer f w) = n)
    (v : EuclideanSpace ℝ (Fin n)) :
    (solKerEquiv hft κ hc d a₀ hxκ hxσ hgp hw hdim v : c.φ.model.E 0) =
      modelDeriv κ c.isChart d a₀ (κ.zOf x) v := by
  have := hdim.1
  rfl

variable (o : SectionOrientation f hft.toIsScFredholmSection)
  (hgp : ∀ x, IsZeroAt P f x → B.IsGeneralPositionGerm f x)
  (hidx : ∀ y, IsZeroAt P f y → B.IsLinOfIndex f y n)

/-- **The orientation `o_x` read in the corner coordinates `κ` of `S` and the chart `c` of `X`**:
the orientation of `ℝⁿ` pulled back from `tangentOr(o_x)` on `ker f'(x)` along `solKerEquiv`
(`pullOr`). -/
def solReadOr {c : StrongBundleChart PX P} (hc : B.IsChart c) (d : PX.SubData (solutionSet P f))
    (a₀ : solutionSet P f) {x : solutionSet P f} (hxκ : x ∈ κ.s)
    (hxσ : x ∈ (subChart d c.isChart a₀).source) :
    Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n) :=
  pullOr finrank_euclideanSpace_fin
    (solKerEquiv hft κ hc d a₀ hxκ hxσ (hgp x.1 x.2)
      (chartPtOf c hc (d.shrink_subset_source c.φ hxσ)
        (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt x.2)).toBase_z
      (finrank_linKer_of hft x.2 (hgp x.1 x.2) (hidx x.1 x.2) hc (d.shrink_subset_source c.φ hxσ)
        _ (chartPtOf c hc (d.shrink_subset_source c.φ hxσ)
          (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt x.2)).toBase_z))
    ((chartPtOf c hc (d.shrink_subset_source c.φ hxσ)
        (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt x.2)).tangentOr
      hft.toIsScFredholmSection x.2 (hgp x.1 x.2).isLinSurjAt
      (toChartOr hft.toIsScFredholmSection
        (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt x.2) c hc
        (d.shrink_subset_source c.φ hxσ)
        (o.1 x.1 (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt x.2))))

theorem solReadOr_congr {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (d : PX.SubData (solutionSet P f)) (a₀ : solutionSet P f) {x x' : solutionSet P f}
    (h : x = x') (hxκ : x ∈ κ.s) (hxσ : x ∈ (subChart d c.isChart a₀).source) (hxκ' : x' ∈ κ.s)
    (hxσ' : x' ∈ (subChart d c.isChart a₀).source) :
    solReadOr hft κ o hgp hidx hc d a₀ hxκ hxσ = solReadOr hft κ o hgp hidx hc d a₀ hxκ' hxσ' := by
  subst h; rfl

/-- **The reading does not depend on the chart of `X`**: by the chain rule
(`modelDeriv_chartChange`), the two isomorphisms `ℝⁿ ≅ ker f'(x)` differ by the tangent map of
the transition, which also relates the two tangent orientations (`tangentOrAt_toChartOr`). -/
theorem solReadOr_chartChange {c c' : StrongBundleChart PX P} (hc : B.IsChart c)
    (hc' : B.IsChart c') (d d' : PX.SubData (solutionSet P f)) (a₀ a₀' : solutionSet P f)
    {x : solutionSet P f} (hxκ : x ∈ κ.s) (hxσ : x ∈ (subChart d c.isChart a₀).source)
    (hxσ' : x ∈ (subChart d' c'.isChart a₀').source) :
    solReadOr hft κ o hgp hidx hc d a₀ hxκ hxσ =
      solReadOr hft κ o hgp hidx hc' d' a₀' hxκ hxσ' := by
  have hs := hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt x.2
  have h := tangentOrAt_toChartOr hft.toIsScFredholmSection hs x.2 (hgp x.1 x.2).isLinSurjAt
    (o.1 x.1 hs) hc hc' (d.shrink_subset_source c.φ hxσ) (d'.shrink_subset_source c'.φ hxσ')
  unfold solReadOr
  rw [h]
  have hxc := d.shrink_subset_source c.φ hxσ
  have hdim := finrank_linKer_of hft x.2 (hgp x.1 x.2) (hidx x.1 x.2) hc hxc _
    (chartPtOf c hc hxc hs).toBase_z
  refine (pullOr_eq_of_comp _ (fun v => Subtype.ext ?_) _).symm
  refine (coe_solKerEquiv _ _ _ _ _ _ _ _ _ _ v).trans
    ((modelDeriv_chartChange κ hc hc' d d' a₀ a₀' hxκ hxσ hxσ' (κ.toBase_zOf x) hs v).trans ?_)
  rw [← coe_solKerEquiv hft κ hc d a₀ hxκ hxσ (hgp x.1 x.2) (chartPtOf c hc hxc hs).toBase_z hdim v]
  exact (ChartPoint.coe_tangentKerEquiv (chartPtOf c hc hxc hs)
    (chartPtOf c' hc' (d'.shrink_subset_source c'.φ hxσ') hs) hft.toIsScFredholmSection x.2
    _).symm

/-- **The reading changes with the corner coordinates by the chart change of `S`**:
`signMap D(κ' ∘ κ⁻¹)` moves the reading in `κ` to the reading in `κ'` (the chain rule
`derivIn_comp_chartChangeDeriv` for the tangent map of `S ↪ X`, `derivIn_incl`). -/
theorem signMap_solReadOr [ChartedSpace (EuclideanQuadrant n) (solutionSet P f)]
    (κ' : CornerCoords (subPolyfold hY) n)
    (he : κ.toQuadrantChart ∈ IsManifold.maximalAtlas (𝓠 n) ∞ (solutionSet P f))
    (he' : κ'.toQuadrantChart ∈ IsManifold.maximalAtlas (𝓠 n) ∞ (solutionSet P f))
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (d : PX.SubData (solutionSet P f))
    (a₀ : solutionSet P f) {x : solutionSet P f} (hxκ : x ∈ κ.s) (hxκ' : x ∈ κ'.s)
    (hxσ : x ∈ (subChart d c.isChart a₀).source) :
    signMap (chartChangeDeriv (𝓠 n) κ.toQuadrantChart κ'.toQuadrantChart x)
        (solReadOr hft κ o hgp hidx hc d a₀ hxκ hxσ) =
      solReadOr hft κ' o hgp hidx hc d a₀ hxκ' hxσ := by
  have h1 := derivIn_incl κ' c.isChart d a₀ hxκ' hxσ (κ'.toBase_zOf x)
  have h2 := derivIn_incl κ c.isChart d a₀ hxκ hxσ (κ.toBase_zOf x)
  have h3 := derivIn_comp_chartChangeDeriv (by simp) he he' hxκ hxκ'
    (hasFDerivWithinAt_incl κ' c.isChart d a₀ hxκ' hxσ (κ'.toBase_zOf x)).differentiableWithinAt
  rw [h1, h2] at h3
  unfold solReadOr
  refine signMap_pullOr _ (fun v => Subtype.ext ?_) _
  exact (coe_solKerEquiv _ _ _ _ _ _ _ _ _ _ _).trans
    ((DFunLike.congr_fun h3 v).trans (coe_solKerEquiv _ _ _ _ _ _ _ _ _ _ v).symm)

variable (hcs : (subPolyfold hY).HasCornerStructureOfDim n)

/-- **The orientation of `T_xS`** (Theorem 6.6.18): `o_x` read in the corner coordinates of the
charted space `cornerChartedSpace hcs` at `x` and the chosen chart `orChart B x` of `X`
(`solReadOr`). -/
def solOr (x : solutionSet P f) : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n) :=
  solReadOr hft (hcs.exists_cornerCoords x).choose o hgp hidx (isChart_orChart x.1)
    (hY.data x.2) x (hcs.exists_cornerCoords x).choose_spec
    ((hY.data x.2).mem_shrink (orChart B x.1).φ x.2 (hY.mem_data_V x.2) (mem_orChart x.1))

/-- **`solOr` read in any corner coordinates `κ` and any chart `c` of `X`** is the reading
`solReadOr` there (`solReadOr_chartChange`, `signMap_solReadOr`). -/
theorem orientationIn_solOr [inst : ChartedSpace (EuclideanQuadrant n) (solutionSet P f)]
    (hch : inst = (subPolyfold hY).cornerChartedSpace hcs) {c : StrongBundleChart PX P}
    (hc : B.IsChart c) (d : PX.SubData (solutionSet P f)) (a₀ : solutionSet P f)
    {x : solutionSet P f} (hxκ : x ∈ κ.s) (hxσ : x ∈ (subChart d c.isChart a₀).source) :
    orientationIn (I := 𝓠 n) κ.toQuadrantChart x
        (modelOrToTangent x (solOr hft o hgp hidx hcs x)) =
      solReadOr hft κ o hgp hidx hc d a₀ hxκ hxσ := by
  have := isManifold_of_eq hcs hch
  have hκ₀ := (hcs.exists_cornerCoords x).choose_spec
  have h := solReadOr_chartChange hft _ o hgp hidx (isChart_orChart x.1) hc (hY.data x.2) d x a₀
    hκ₀ ((hY.data x.2).mem_shrink _ x.2 (hY.mem_data_V x.2) (mem_orChart x.1)) hxσ
  unfold orientationIn
  rw [chartAt_eq_of_eq hcs hch x]
  refine (congrArg (signMap _) h).trans ?_
  exact signMap_solReadOr hft _ o hgp hidx κ (mem_maximalAtlas_of_eq hcs hch _)
    (mem_maximalAtlas_of_eq hcs hch κ) hc d a₀ hκ₀ hxκ hxσ

/-- **`solOr` agrees with `o_x` on `ker f'(x)`**: for every chart `c` of `X` at `x`, the tangent
map of `S ↪ X` at `x` (read in Mathlib's chart at `x` and in `c`) is an isomorphism
`ι : T_xS = ℝⁿ ≅ ker f'(x)`, and a basis `b` of `T_xS` is positive for `solOr` iff
`ι b₁ ∧ … ∧ ι bₙ` is positive for `tangentOr(o_x)`. -/
theorem solOr_spec [inst : ChartedSpace (EuclideanQuadrant n) (solutionSet P f)]
    (hch : inst = (subPolyfold hY).cornerChartedSpace hcs) (x : solutionSet P f)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (hxc : x.1 ∈ c.φ.source) :
    ∃ ι : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] c.linKer f (chartPtOf c hc hxc
        (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt x.2)).z,
      (∀ v, (ι v : c.φ.model.E 0) = derivIn (𝓠 n) (chartAt (EuclideanQuadrant n) x)
        (fun y : solutionSet P f => c.φ y.1) x v) ∧
      ∀ b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)),
        b.orientation = solOr hft o hgp hidx hcs x ↔
          (chartPtOf c hc hxc (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt x.2)).tangentOr
              hft.toIsScFredholmSection x.2 (hgp x.1 x.2).isLinSurjAt
              (toChartOr hft.toIsScFredholmSection
                (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt x.2) c hc hxc
                (o.1 x.1 (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt x.2))) =
            rayOfNeZero ℝ _ (wedge_equiv_ne_zero finrank_euclideanSpace_fin ι b) := by
  have hs := hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt x.2
  have hκ₀ := (hcs.exists_cornerCoords x).choose_spec
  have hxσ : x ∈ (subChart (hY.data x.2) c.isChart x).source :=
    (hY.data x.2).mem_shrink c.φ x.2 (hY.mem_data_V x.2) hxc
  have hdim := finrank_linKer_of hft x.2 (hgp x.1 x.2) (hidx x.1 x.2) hc hxc _
    (chartPtOf c hc hxc hs).toBase_z
  refine ⟨solKerEquiv hft _ hc (hY.data x.2) x hκ₀ hxσ (hgp x.1 x.2)
    (chartPtOf c hc hxc hs).toBase_z hdim, fun v => ?_, fun b => ?_⟩
  · refine (coe_solKerEquiv _ _ _ _ _ _ _ _ _ _ v).trans ?_
    rw [chartAt_eq_of_eq hcs hch x]
    exact (DFunLike.congr_fun (derivIn_incl _ c.isChart _ x hκ₀ hxσ
      (MPolyfold.CornerCoords.toBase_zOf _ x)) v).symm
  · have h : solOr hft o hgp hidx hcs x =
        solReadOr hft _ o hgp hidx hc (hY.data x.2) x hκ₀ hxσ :=
      solReadOr_chartChange hft _ o hgp hidx (isChart_orChart x.1) hc (hY.data x.2) (hY.data x.2)
        x x hκ₀ ((hY.data x.2).mem_shrink _ x.2 (hY.mem_data_V x.2) (mem_orChart x.1)) hxσ
    exact (Eq.congr_right h).trans (orientation_eq_pullOr_iff _ _ _ b)

/-- **The frame of `ker f'` given by the tangent map of `S ↪ X` along a path of `S`**: along a
path `γ` of `S` in the corner coordinates `κ` and the chart `c`, the wedges
`ι_q b₁ ∧ … ∧ ι_q bₙ` (`ι_q = solKerEquiv` at `γ(q)`, `b = pullBasis`) orient the kernel line
bundle `λ(tangentFamily)` (`continuousOn_deriv`: `D(σ ∘ χ⁻¹)` is continuous). -/
theorem isLineOrientation_solKer {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (d : PX.SubData (solutionSet P f)) (a₀ : solutionSet P f)
    {γ : (Fin 1 → ℝ) → solutionSet P f}
    (hγs : (rnPolyfold 1).IsScSmoothMap PX (Subtype.val ∘ γ)) (hγκ : ∀ p, γ p ∈ κ.s)
    (hγσ : ∀ p, γ p ∈ (subChart d c.isChart a₀).source) (hγχ : Continuous fun p => κ.χ (γ p))
    (hγc : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, (Subtype.val ∘ γ) q ∈ c.φ.source)
    (hγ0 : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, IsZeroAt P f ((Subtype.val ∘ γ) q))
    (hγgp : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, B.IsGeneralPositionGerm f ((Subtype.val ∘ γ) q)) :
    IsLineOrientation (tangentFamily hft hc hγs hγc hγ0 hγgp).det fun q =>
      rayOfNeZero ℝ _ (wedge_equiv_ne_zero finrank_euclideanSpace_fin
        (solKerEquiv hft κ hc d a₀ (hγκ q) (hγσ q) (hgp _ (γ q).2)
          (chartPtOf c hc (hγc q q.2)
            (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt (hγ0 q q.2))).toBase_z
          (finrank_linKer_of hft (γ q).2 (hgp _ (γ q).2) (hidx _ (γ q).2) hc (hγc q q.2) _
            (chartPtOf c hc (hγc q q.2)
              (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt (hγ0 q q.2))).toBase_z))
        (pullBasis finrank_euclideanSpace_fin)) := by
  have hfin := κ.isCornerChart.finiteDimensional
  have hσ := subPolyfold_isChart hY d c.isChart a₀
  have q₀ : Icc (0 : Fin 1 → ℝ) 1 := ⟨0, left_mem_Icc.2 fun _ => zero_le_one⟩
  have hΛn : (tangentFamily hft hc hγs hγc hγ0 hγgp).n = n :=
    ((tangentFamily hft hc hγs hγc hγ0 hγgp).finrank_eq q₀).symm.trans
      (finrank_linKer_of hft (γ q₀).2 (hgp _ (γ q₀).2) (hidx _ (γ q₀).2) hc (hγc q₀ q₀.2) _
        (chartPtOf c hc (hγc q₀ q₀.2)
          (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt (hγ0 q₀ q₀.2))).toBase_z).2
  have hz : Continuous fun q : Icc (0 : Fin 1 → ℝ) 1 => κ.zOf (γ q) :=
    (ContinuousLinearEquiv.continuous _).comp (hγχ.comp continuous_subtype_val)
  have hD := (isDiffeoGerm_transition κ.isCornerChart κ.isChart hσ).isSc1.isSc1With_scDeriv
    |>.continuousOn_deriv
  have hli : ∀ q : Icc (0 : Fin 1 → ℝ) 1, LinearIndependent ℝ fun i => modelDeriv κ c.isChart d a₀
      (κ.zOf (γ q)) (pullBasis finrank_euclideanSpace_fin (Fin.cast hΛn i)) := fun q => by
    have h1 := (pullBasis (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n))).linearIndependent.comp _
      (Fin.cast_injective hΛn)
    have h2 := h1.map' (modelDeriv κ c.isChart d a₀ (κ.zOf (γ q))).toLinearMap
      (LinearMap.ker_eq_bot.2
        (modelDeriv_injective κ c.isChart d a₀ (hγκ q) (hγσ q) (κ.toBase_zOf _)))
    exact h2
  have hcont : ∀ w : EuclideanSpace ℝ (Fin n), Continuous fun q : Icc (0 : Fin 1 → ℝ) 1 =>
      modelDeriv κ c.isChart d a₀ (κ.zOf (γ q)) w := fun w => by
    have h := hD.comp_continuous (hz.prodMk (continuous_const (y := κ.Ψ.symm (ofLp w))))
      fun q => by
        change κ.χ.model.E.toBase 1 (κ.zOf (γ q)) ∈
          (overlapRet κ.isCornerChart (subChart d c.isChart a₀)).U
        rw [κ.toBase_zOf]
        exact κ.χ.mem_overlap _ (κ.s_subset (hγκ q)) (hγσ q)
    exact h
  let ε : (tangentFamily hft hc hγs hγc hγ0 hγgp).Frame :=
    { U := univ
      isOpen := isOpen_univ
      e := fun i q => modelDeriv κ c.isChart d a₀ (κ.zOf (γ q))
        (pullBasis finrank_euclideanSpace_fin (Fin.cast hΛn i))
      continuousOn := fun i => (hcont _).continuousOn
      mem := fun q _ i => modelDeriv_mem_linKer κ hft hc d a₀ (hγκ q) (hγσ q) (κ.toBase_zOf _)
        (hgp _ (γ q).2) (chartPtOf c hc (hγc q q.2)
          (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt (hγ0 q q.2))).toBase_z _
      linearIndependent := fun q _ => hli q }
  refine (ε.isLineOrientation rfl).congr fun q => rayOfNeZero_congr ?_ _ _
  rw [SubspaceFamily.Frame.wedgeAt_of_mem _ (mem_univ q)]
  refine Eq.trans ?_ (wedge_cast _ _ hΛn)
  congr 1


/-- **The reading of `o` is locally constant on `S`** (the continuity in Theorem 6.6.18): near
`x₀`, in an orientable neighbourhood of `x₀` (`exists_isOrientableNbhd`, which needs the bump
functions) and the corner coordinates `κ`, every `y` is joined to `x₀` by a segment
(`eventually_exists_segPath`); along it `tangentOr(o)` and the frame of `isLineOrientation_solKer`
are two orientations of the kernel line bundle (`IsNaturalSolutionOrientation.continuous`), which
agree at both ends or at neither (`IsLineOrientation.eq_iff_eq`). -/
theorem eventually_solReadOr_eq (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hnat : IsNaturalSolutionOrientation f hft hgp o) {x₀ : solutionSet P f} (hx₀ : x₀ ∈ κ.s) :
    ∃ (c : StrongBundleChart PX P) (hc : B.IsChart c) (d : PX.SubData (solutionSet P f))
      (hxσ₀ : x₀ ∈ (subChart d c.isChart x₀).source),
      ∀ᶠ y in 𝓝 x₀, ∃ (hyκ : y ∈ κ.s) (hyσ : y ∈ (subChart d c.isChart x₀).source),
        solReadOr hft κ o hgp hidx hc d x₀ hyκ hyσ =
          solReadOr hft κ o hgp hidx hc d x₀ hx₀ hxσ₀ := by
  have := paracompactSpace_rn_prod PX
  have := paracompactSpace_rn_pullback B
  have := paracompactSpace_rn_rn_prod PX
  have := paracompactSpace_rn_rn_pullback B
  have hs₀ := hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt x₀.2
  obtain ⟨c, hc, U, V, hN⟩ := exists_isOrientableNbhd hX hbump hft hs₀
  have hVc : ∀ {y : X}, y ∈ V → y ∈ c.φ.source := fun hy =>
    hN.hasLocalPropagation.subset (hN.subset hy)
  have hxσ₀ : x₀ ∈ (subChart (hY.data x₀.2) c.isChart x₀).source :=
    (hY.data x₀.2).mem_shrink c.φ x₀.2 (hY.mem_data_V x₀.2) (hVc hN.mem)
  refine ⟨c, hc, hY.data x₀.2, hxσ₀, ?_⟩
  have hG : IsOpen ((subChart (hY.data x₀.2) c.isChart x₀).source ∩ Subtype.val ⁻¹' V) :=
    (subChart _ c.isChart x₀).isOpen_source.inter (hN.isOpen_V.preimage continuous_subtype_val)
  filter_upwards [eventually_exists_segPath κ hx₀ hG ⟨hxσ₀, hN.mem⟩] with y hy
  obtain ⟨hyκ, γ, hγs, hγ0', hγ1', hγG, hγχ⟩ := hy
  have hyσ : y ∈ (subChart (hY.data x₀.2) c.isChart x₀).source := hγ1' ▸ (hγG 1).2.1
  refine ⟨hyκ, hyσ, ?_⟩
  have hγsX : (rnPolyfold 1).IsScSmoothMap PX (Subtype.val ∘ γ) :=
    (subPolyfold_inclusion_isScSmooth hY).comp hγs
  have hγV : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, (Subtype.val ∘ γ) q ∈ V := fun q _ => (hγG q).2.2
  have hγZ : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, IsZeroAt P f ((Subtype.val ∘ γ) q) := fun q _ =>
    (γ q).2
  have hγcont : Continuous fun p => κ.χ (γ p) := by
    simp only [hγχ]
    exact continuous_const.add ((Real.smoothTransition.continuous.comp (continuous_apply 0)).smul
      continuous_const)
  have hT := hnat.continuous x₀.1 hs₀ c hc U V hN _ hγsX hγV hγZ
  have hL := isLineOrientation_solKer hft κ hgp hidx hc (hY.data x₀.2) x₀ hγsX (fun p => (hγG p).1)
    (fun p => (hγG p).2.1) hγcont (fun q hq => hVc (hγV q hq)) hγZ
    (fun q hq => hgp _ (hγZ q hq))
  have : PreconnectedSpace (Icc (0 : Fin 1 → ℝ) 1) :=
    isPreconnected_iff_preconnectedSpace.1 (convex_Icc 0 1).isPreconnected
  have hiff := IsLineOrientation.eq_iff_eq hT hL ⟨1, right_mem_Icc.2 fun _ => zero_le_one⟩
    ⟨0, left_mem_Icc.2 fun _ => zero_le_one⟩
  refine (solReadOr_congr hft κ o hgp hidx hc _ x₀ hγ1'.symm hyκ hyσ (hγG 1).1
    (hγG 1).2.1).trans ?_
  refine (pullOr_eq_of_iff _ hiff).trans ?_
  exact solReadOr_congr hft κ o hgp hidx hc _ x₀ hγ0' (hγG 0).1 (hγG 0).2.1 hx₀ hxσ₀

/-- **`solOr` is a continuous tangent orientation of the Mathlib manifold `S`**: read in the
corner coordinates at `x₀` it is locally constant (`eventually_solReadOr_eq`,
`orientationIn_solOr`, `TangentOrientation.isContinuous_of_forall`). -/
theorem isContinuous_solOr (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hnat : IsNaturalSolutionOrientation f hft hgp o)
    [inst : ChartedSpace (EuclideanQuadrant n) (solutionSet P f)]
    (hch : inst = (subPolyfold hY).cornerChartedSpace hcs) :
    TangentOrientation.IsContinuous (𝓠 n) ∞
      (fun x => modelOrToTangent x (solOr hft o hgp hidx hcs x)) := by
  have := isManifold_of_eq hcs hch
  refine TangentOrientation.isContinuous_of_forall (by simp) fun x₀ => ?_
  obtain ⟨κ, hx₀⟩ := hcs.exists_cornerCoords x₀
  obtain ⟨c, hc, d, hxσ₀, hev⟩ := eventually_solReadOr_eq hft κ o hgp hidx hX hbump hnat hx₀
  refine ⟨κ.toQuadrantChart, mem_maximalAtlas_of_eq hcs hch κ, hx₀, ?_⟩
  filter_upwards [hev] with y hy
  obtain ⟨hyκ, hyσ, hy⟩ := hy
  rw [orientationIn_solOr hft κ o hgp hidx hcs hch hc d x₀ hyκ hyσ,
    orientationIn_solOr hft κ o hgp hidx hcs hch hc d x₀ hx₀ hxσ₀, hy]

end Orient

/-! ### Theorem 6.6.18 with the orientation of the Mathlib manifold `S` -/

section Main

open MPolyfold

local notation "𝓠" => modelWithCornersEuclideanQuadrant

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- **Theorem 6.6.18** (2021, p. 275; preprint Theorem 6.41), **with the natural orientation of
`S` as a manifold**: over a tame `X` with sc-smooth bump functions, for a proper sc-Fredholm
section `f` (tame germ data) of index `d` in general position at every zero and an orientation
`o` of `f` (Definition 6.6.16), `S = f⁻¹(0)` is compact and, with the charted space of
`theorem_6_6_18_isManifold`, a smooth manifold with boundary and corners carrying a continuous
tangent orientation `oS` (`TangentOrientation.IsContinuous`) which at every zero `x` is `o_x` on
`T_xS = ker f'(x)`: for every chart `c` of `X` at `x` the tangent map `ι` of `S ↪ X` at `x`
(`derivIn`, read in Mathlib's chart at `x` and in `c`) is an isomorphism `T_xS ≅ ker f'(x)`, and a
basis `b` of `T_xS` is positive for `oS` iff `ι b₁ ∧ … ∧ ι bₙ` is positive for `tangentOr(o_x)`.
Added hypothesis: the bump functions (`hbump`), as in `theorem_6_6_13` and `theorem_6_6_17`; they
give the orientable neighbourhoods (`exists_isOrientableNbhd`) on which `o` is continuous, and
hold on Hilbert models (`MPolyfold.admitsBumpFunctions_of_hilbert`). -/
theorem theorem_6_6_18_oriented (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hft : B.IsScFredholmSectionTame f) (hP : B.IsProper f)
    (hgp : ∀ x, IsZeroAt P f x → B.IsGeneralPositionGerm f x) {d : ℕ}
    (hidx : ∀ y, IsZeroAt P f y → B.IsLinOfIndex f y d)
    (o : SectionOrientation f hft.toIsScFredholmSection) :
    IsCompact (solutionSet P f) ∧
      letI := PX.paracompactSpace_subtype (solutionSet P f)
      letI := (MPolyfold.subPolyfold ((theorem_6_6_18_solutionSet hX hft hP hgp).isSubmanifoldOfDim
        hft hidx).1.isSubMPolyfold).cornerChartedSpace
        (((theorem_6_6_18_solutionSet hX hft hP hgp).isSubmanifoldOfDim
          hft hidx).hasCornerStructureOfDim_of_tame
          hX ((theorem_6_6_18_solutionSet hX hft hP hgp).isGoodPositionAt hX))
      IsManifold (𝓠 d) ∞ (solutionSet P f) ∧
      ∃ oS : TangentOrientation (𝓠 d) (solutionSet P f) d, oS.IsContinuous (𝓠 d) ∞ ∧
        ∀ (x : solutionSet P f) (c : StrongBundleChart PX P) (hc : B.IsChart c)
          (hxc : x.1 ∈ c.φ.source),
          ∃ ι : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ] c.linKer f (chartPtOf c hc hxc
              (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt x.2)).z,
            (∀ v, (ι v : c.φ.model.E 0) = derivIn (𝓠 d) (chartAt (EuclideanQuadrant d) x)
              (fun y : solutionSet P f => c.φ y.1) x v) ∧
            ∀ b : Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)),
              b.orientation = tangentOrToModel (oS x) ↔
                (chartPtOf c hc hxc
                    (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt x.2)).tangentOr
                  hft.toIsScFredholmSection x.2 (hgp x.1 x.2).isLinSurjAt
                  (toChartOr hft.toIsScFredholmSection
                    (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt x.2) c hc hxc
                    (o.1 x.1 (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt x.2))) =
                  rayOfNeZero ℝ _ (wedge_equiv_ne_zero finrank_euclideanSpace_fin ι b) := by
  refine ⟨(theorem_6_6_18_isManifold hX hft hP hgp hidx).1, ?_⟩
  let := PX.paracompactSpace_subtype (solutionSet P f)
  have h := theorem_6_6_18_solutionSet hX hft hP hgp
  have hcs := (h.isSubmanifoldOfDim hft hidx).hasCornerStructureOfDim_of_tame hX
    (h.isGoodPositionAt hX)
  let := (MPolyfold.subPolyfold
    (h.isSubmanifoldOfDim hft hidx).1.isSubMPolyfold).cornerChartedSpace hcs
  have hnat := (theorem_6_6_18 hX hft hP hgp o).2
  exact ⟨isManifold_of_eq hcs rfl, fun x => modelOrToTangent x (solOr hft o hgp hidx hcs x),
    isContinuous_solOr hft o hgp hidx hcs hX hbump hnat rfl,
    fun x c hc hxc => solOr_spec hft o hgp hidx hcs rfl x hc hxc⟩

end Main

end Polyfold
