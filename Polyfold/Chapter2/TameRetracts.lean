import Polyfold.Chapter2.Boundary
import Polyfold.Chapter2.SubMPolyfold
import Polyfold.Chapter1.ExpositionLemmas

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §2.4,
Propositions 2.5.3, 2.5.6 (preprint 2.35, 2.36), Lemma 2.5.12 (preprint 2.40), Corollary 2.5.13 (preprint 2.41), Propositions 2.5.14, 2.5.15 (preprint 2.42, 2.43) and Theorem 2.5.17 (preprint 2.45) (in
part): the boundary geometry of tame retracts and tame M-polyfolds.

# Tame retracts: the degeneracy index and the faces

## The text, paraphrased

(Proposition 2.5.3 (preprint 2.35)) For a tame retraction `r` and a smooth `x ∈ O`, `(1 − Dr(x))E ⊆ E_x`, so the
sc-complement in Definition 2.5.2 (preprint 2.34) (2) can be taken to be `(1 − Dr(x))E`.  (Proposition 2.5.6 (preprint 2.36)) For a
tame retract and smooth `x`, `dim(T_xO/T_x^R O) = d_O(x)`, `C_xO` is a partial quadrant in `T_xO`,
and `d_O(x) = d_C(x)` for every `x ∈ O`.  (Lemma 2.5.12 (preprint 2.40)) The faces of a tame retract are the connected
components of the sets `f ∩ O`, `f` an extended face; the components of `f ∩ O`, `f' ∩ O` through
`x` agree only if `f = f'`.  (Corollary 2.5.13 (preprint 2.41)) Every `x ∈ O` lies in exactly `d_O(x)` faces.
(Proposition 2.5.14 (preprint 2.42)) In a tame M-polyfold every `x` has a neighbourhood `V` in which each `y` lies in
exactly `d_X(y)` faces of `V` and `d_V = d_X`; globally `x` lies in at most `d_X(x)` faces.
(Proposition 2.5.15 (preprint 2.43)) A face `F` of a tame retract has an open neighbourhood `U*` in `U` with an
sc-smooth retraction `s : U* → U*` onto `F`; `F` is a sub-M-polyfold of `O`, tame, with
`d_F = d_O − 1`.  (Theorem 2.5.17 (preprint 2.45)) The interior of a face is a sub-M-polyfold; in the face-structured
case faces are tame sub-M-polyfolds with `d_X = d_F + 1`; local and global face counts.

## What is formalized

* `Polyfold.proposition_2_5_3` (**Proposition 2.5.3 (preprint 2.35)**): `(1 − Dr(x))E ⊆ E_x` and `E = Dr(x)E ⊕
  (1 − Dr(x))E` is an sc-splitting; in coordinates `coord_scDeriv_eq` (`λ_j ∘ Dr(x) = λ_j` for
  `j ∈ I(x)`).  `ScRetraction.scDeriv_mapsTo_minimalSubspace` (`Dr(x)E_x ⊆ E_x`, the sign argument).
* `Polyfold.quotDim_reducedTangentSpaceWith_eq` (equations (15)–(16)), the general
  `MPolyfold.degIndex_eq_chartDegIndex_of_isTameWith` / `_of_isTameRetract` (a tame chart realizes
  the minimum of Definition 2.4.1 (preprint 2.22) at every point of its domain: `d_X(y) = d_C(φ(y))`), and from it
  `Polyfold.proposition_2_5_6` (**(13)**: `dim(T_xO/T_x^R O) = d_O(x) = d_C(x)` at smooth `x`) and
  `Polyfold.proposition_2_5_6_degIndex` (**(14)**: `d_O = d_C` on `O`), also for any local model
  (`LocalModel.degIndex_toMPolyfold_of_isTameWith`).
* The local geometry the text's proofs of Lemma 2.5.12 (preprint 2.40) and Proposition 2.5.15 (preprint 2.43) skip (exposition
  Lemmas 4.A–4.C): `subset_coordHyper_of_isPreconnected` (a connected piece of `{d_C = 1}` lies in
  one extended face `f_i = coordHyper T i`), `Polyfold.ray_zeroSet` (**rays stay in their face**,
  Lemma 4.B, via `IsSc1With.apply_deriv_eq_zero_of_ray` and Proposition 2.5.3 (preprint 2.35)) and
  `Polyfold.local_face_structure` (Lemma 4.C).
* Faces in `E₀`: `ScRetraction.faceStratum` (`S = {x ∈ O | d_C(x) = 1}`),
  `ScRetraction.IsRetractFace`; `Polyfold.closure_connectedComponentIn_faceStratum` and
  `Polyfold.lemma_2_5_12` (**Lemma 2.5.12 (preprint 2.40)**), `Polyfold.lemma_2_5_12_injective` (its second statement),
  `Polyfold.corollary_2_5_13_retract`.  Transfer to the M-polyfold `O`:
  `LocalModel.isFace_toMPolyfold_iff`, and `Polyfold.corollary_2_5_13` (**Corollary 2.5.13 (preprint 2.41)**: a tame
  retract is face-structured).
* `Polyfold.proposition_2_5_14` (**Proposition 2.5.14 (preprint 2.42)**) with `MPolyfold.faces_encard_le` (the global
  bound) and `MPolyfold.IsTame.exists_chart`.
* `Polyfold.proposition_2_5_15` (**Proposition 2.5.15 (preprint 2.43)**, the retraction `s = r ∘ P_i` of a
  neighbourhood `U*` of `F` onto `F`, `P_i = killCoord T i` the sc-projection onto `f_i`) and
  `LocalModel.isSubMPolyfold_of_isFace` (`F` is a sub-M-polyfold of `O`).
* `MPolyfold.theorem_2_5_17_interior` (**Theorem 2.5.17 (preprint 2.45)**, the interior of a face: `F ∩ {d_X = 1} = G`
  for `F = closure(G)`).

## What the text leaves implicit, and the choices made

* Everything is computed in a presentation `T : E ≅ ℝⁿ ⊕ W` of `C` (`λ_i(z) = (T z)_i`,
  `I(z) = zeroSet T z`); the hypotheses are `R.IsTameWith T` for that `T` (implied by
  `ScRetraction.IsTame`).  The intrinsic extended faces of the text are the hyperplanes
  `f_i = {λ_i = 0}`.
* Proposition 2.5.3 (preprint 2.35) needs only condition (2) of tameness: `Dr(x)E_x ⊆ E_x` holds for every
  retraction at every point of `O₁` by the sign argument (the text derives it from condition (1)).
* "Smooth point" in condition (2) of Definition 2.5.2 (preprint 2.34) is kept; the smooth approximants
  `r(T⁻¹(a, w_j))`, `w_j ∈ W_∞`, of the proof of Proposition 2.5.6 (preprint 2.36) are
  `exists_tendsto_smooth_degIndexWith`.
* Lemma 2.5.12 (preprint 2.40)'s proof is a sketch; the key step "the retraction maps points of `U ∩ f_i` near
  `f_i ∩ O` into `f_i`" needs tameness (2) through Proposition 2.5.3 (preprint 2.35) (`ray_zeroSet`), and the
  identification of faces with components uses that faces are relatively open in `f_i ∩ O`
  (`subset_of_relClopen_of_isPreconnected`).
* Faces of the retract are handled in `E₀` (`IsRetractFace`) and transferred to the subtype
  `↥O` carrying the M-polyfold structure (`isFace_toMPolyfold_iff`).
* Proposition 2.5.14 (preprint 2.42)'s "faces of `V`" are expressed through the tame chart `φ : V → O`, an
  sc-diffeomorphism onto the M-polyfold `O`: `d_X(y) = d_O(φ(y))` and `O` is face-structured.
* Proposition 2.5.15 (preprint 2.43): the neighbourhoods of the text are balls `B_e` *and* their preimages under
  `P_i`, since `P_i` need not be norm-decreasing for the norm of `E₀`.

## Elsewhere

* Proposition 2.5.6 (preprint 2.36)'s "`C_xO` is a partial quadrant in `T_xO`" and "`T_x^R O` is an sc-subspace"
  are in `Polyfold.Chapter2.PartialCone` (proved directly for tame retracts; the general second
  statement of Theorem 2.4.12 (preprint 2.31) is not formalized: gap G.11 of the report).
* Proposition 2.5.15 (preprint 2.43)'s "`F` is tame and `d_F = d_O − 1`", Proposition 2.5.16 (preprint 2.44) and the remaining
  statements of Theorem 2.5.17 (preprint 2.45) are in `Polyfold.Chapter2.TameFaces`.
* Proposition 2.5.20 (preprint 2.46) (fibred products) is in `Polyfold.Chapter2.FibredProduct`.
-/

open Set Filter Topology Function Module

noncomputable section

namespace Polyfold

variable {E : ScBanach}

section Prop235

variable {n : ℕ} {W : ScBanach} {C : Set (E 0)}

/-- If `V = A ⊕ B` and `B ≤ K`, then `A / (A ∩ K) ≅ V / K`, so `dim(A/(A ∩ K)) = dim(V/K)`. -/
theorem quotDim_eq_finrank_quotient_of_isCompl {V : Type*} [AddCommGroup V] [Module ℝ V]
    {A B K : Submodule ℝ V} (hAB : IsCompl A B) (hBK : B ≤ K) :
    quotDim A (A ⊓ K) = finrank ℝ (V ⧸ K) := by
  let Ψ : A →ₗ[ℝ] V ⧸ K := K.mkQ.comp A.subtype
  have hΨker : LinearMap.ker Ψ = (A ⊓ K).comap A.subtype := by
    ext ⟨w, hw⟩
    simp only [Ψ, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.mem_inf]
    exact ⟨fun h => ⟨hw, h⟩, fun h => h.2⟩
  have hΨsurj : Surjective Ψ := by
    intro q
    obtain ⟨v, rfl⟩ := K.mkQ_surjective q
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hAB.sup_eq_top ▸ Submodule.mem_top (x := v))
    refine ⟨⟨a, ha⟩, ?_⟩
    simp only [Ψ, LinearMap.comp_apply, Submodule.subtype_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    simpa using K.neg_mem (hBK hb)
  have hiso : (A ⧸ (A ⊓ K).comap A.subtype) ≃ₗ[ℝ] V ⧸ K :=
    hΨker ▸ Ψ.quotKerEquivOfSurjective hΨsurj
  exact hiso.finrank_eq

/-- `Dr(x)` maps `E_x` into `E_x` at a point `x ∈ O₁` (the sign argument for `r`, with
`r(x) = x`); this is the step "`Dr(x)E_x ⊆ E_x`" of the proof of Proposition 2.5.3 (preprint 2.35).  Tameness is
not needed for it. -/
theorem ScRetraction.scDeriv_mapsTo_minimalSubspace (R : ScRetraction E C)
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (hT : C = T 0 ⁻¹' quadrant n W 0)
    {x : E 1} (hx : x ∈ E.lvlSet R.retract 1) :
    MapsTo (scDeriv R.U R x) (minimalSubspaceWith T (E.toBase 1 x))
      (minimalSubspaceWith T (E.toBase 1 x)) := by
  have h := IsSc1With.mapsTo_minimalSubspace T hT T hT R.relOpen R.isSc1.isSc1With_scDeriv
    (fun _ hz => R.U_subset_C (R.mapsTo hz)) (R.lvlSet_retract_subset 1 hx)
  rwa [R.apply_eq_self_of_mem_retract hx] at h

/-- At a smooth point `x ∈ O`, `Dr(x)` is an sc-operator (Proposition 1.2.1 (preprint 1.16)'s remark). -/
theorem ScRetraction.isScOperator_scDeriv (R : ScRetraction E C) {x : E 1}
    (hx : x ∈ E.lvlSet R.U 1) (hs : x ∈ E.smoothLvl 1) : IsScOperator (scDeriv R.U R x) :=
  R.isSc1.isSc1With_scDeriv.scOperator_deriv hx hs

/-- At a smooth point `x ∈ O`, `E = Dr(x)E ⊕ (1 − Dr(x))E` is an sc-splitting. -/
theorem ScRetraction.isScSplitting_range_scDeriv (R : ScRetraction E C) {x : E 1}
    (hx : x ∈ E.lvlSet R.retract 1) (hs : x ∈ E.smoothLvl 1) :
    E.IsScSplitting (LinearMap.range (scDeriv R.U R x : E 0 →ₗ[ℝ] E 0))
      (LinearMap.range (ContinuousLinearMap.id ℝ (E 0) - scDeriv R.U R x : E 0 →ₗ[ℝ] E 0)) := by
  set D := scDeriv R.U R x with hD
  have hop := R.isScOperator_scDeriv (R.lvlSet_retract_subset 1 hx) hs
  set P := hop.toScOperator with hP
  have hP0 : P 0 = D := hop.toScOperator_zero
  have hDD : ∀ v, D (D v) = D v := fun v =>
    congrArg (fun L : E 0 →L[ℝ] E 0 => L v) (R.scDeriv_comp_self hx)
  have hidem : ∀ v, P 0 (P 0 v) = P 0 v := by rw [hP0]; exact hDD
  have h := ScBanach.isScSplitting_of_idem P hidem
  rw [hP0] at h
  have hker : LinearMap.ker (D : E 0 →ₗ[ℝ] E 0) =
      LinearMap.range (ContinuousLinearMap.id ℝ (E 0) - D : E 0 →ₗ[ℝ] E 0) := by
    ext v
    constructor
    · intro hv
      refine ⟨v, ?_⟩
      have : D v = 0 := hv
      simp [this]
    · rintro ⟨u, rfl⟩
      change D (u - D u) = 0
      rw [map_sub, hDD, sub_self]
  rwa [hker] at h

/-- **Proposition 2.5.3 (preprint 2.35)**: let `r : U → U` be a tame sc-smooth retraction and `x ∈ O = r(U)` a
smooth point.  Then `(1 − Dr(x))E ⊆ E_x`, and `A = (1 − Dr(x))E` is an sc-complement of
`T_xO = Dr(x)E`: in condition (2) of Definition 2.5.2 (preprint 2.34) one can take `A = (1 − Dr(x))E`.

*Proof* (as in the text): with `A ⊆ E_x` from Definition 2.5.2 (preprint 2.34) (2), `E = T_xO ⊕ A` and
`(1 − Dr(x))T_xO = 0` give `(1 − Dr(x))E = (1 − Dr(x))A`; and `Dr(x)E_x ⊆ E_x` by the sign
argument.  The sc-splitting is that of the sc-projection `Dr(x)`.  Only condition (2) of
tameness is used (the text uses condition (1) for `Dr(x)E_x ⊆ E_x`; the sign argument, which holds
for every retraction at a point of `O₁`, makes it unnecessary). -/
theorem proposition_2_5_3 {R : ScRetraction E C} {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)}
    (hT : C = T 0 ⁻¹' quadrant n W 0) (hR : R.IsTameWith T) {x : E 1}
    (hx : x ∈ E.lvlSet R.retract 1) (hs : x ∈ E.smoothLvl 1) :
    LinearMap.range (ContinuousLinearMap.id ℝ (E 0) - scDeriv R.U R x : E 0 →ₗ[ℝ] E 0) ≤
        minimalSubspaceWith T (E.toBase 1 x) ∧
      E.IsScSplitting (LinearMap.range (scDeriv R.U R x : E 0 →ₗ[ℝ] E 0))
        (LinearMap.range (ContinuousLinearMap.id ℝ (E 0) - scDeriv R.U R x : E 0 →ₗ[ℝ] E 0)) := by
  refine ⟨?_, R.isScSplitting_range_scDeriv hx hs⟩
  set D := scDeriv R.U R x with hD
  have hDD : ∀ v, D (D v) = D v := fun v =>
    congrArg (fun L : E 0 →L[ℝ] E 0 => L v) (R.scDeriv_comp_self hx)
  obtain ⟨A, hA, hAE⟩ := hR.exists_complement x hx hs
  have hcompl : IsCompl (LinearMap.range (D : E 0 →ₗ[ℝ] E 0)) A := by
    have := hA.2.2 0
    rwa [ScBanach.levelSub_zero, ScBanach.levelSub_zero] at this
  rintro _ ⟨v, rfl⟩
  obtain ⟨t, ht, a, ha, rfl⟩ :=
    Submodule.mem_sup.1 (hcompl.sup_eq_top ▸ Submodule.mem_top (x := v))
  obtain ⟨u, rfl⟩ := ht
  have haE : a ∈ minimalSubspaceWith T (E.toBase 1 x) := hAE ha
  have hDa : D a ∈ minimalSubspaceWith T (E.toBase 1 x) :=
    R.scDeriv_mapsTo_minimalSubspace T hT hx haE
  change (D u + a) - D (D u + a) ∈ _
  rw [map_add, hDD, add_sub_add_left_eq_sub]
  exact Submodule.sub_mem _ haE hDa

/-- At a smooth point of a tame retract, `dim(T_xO/T_x^R O) = dim(E/E_x) = d_C(x)` (equations
(15)–(16) of the proof of Proposition 2.5.6 (preprint 2.36)). -/
theorem quotDim_reducedTangentSpaceWith_eq {R : ScRetraction E C}
    {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)} (hR : R.IsTameWith T) {x : E 1}
    (hx : x ∈ E.lvlSet R.retract 1) (hs : x ∈ E.smoothLvl 1) :
    quotDim (LinearMap.range (scDeriv R.U R x : E 0 →ₗ[ℝ] E 0)) (reducedTangentSpaceWith R T x) =
      degIndexWith T (E.toBase 1 x) := by
  obtain ⟨A, hA, hAE⟩ := hR.exists_complement x hx hs
  have hcompl : IsCompl (LinearMap.range (scDeriv R.U R x : E 0 →ₗ[ℝ] E 0)) A := by
    have := hA.2.2 0
    rwa [ScBanach.levelSub_zero, ScBanach.levelSub_zero] at this
  rw [← finrank_quotient_minimalSubspaceWith T]
  exact quotDim_eq_finrank_quotient_of_isCompl hcompl hAE

end Prop235

/-! ### Smooth approximation keeping the degeneracy index -/

section Approx

variable {n : ℕ} {W : ScBanach}

/-- Smooth points of the partial quadrant with the same degeneracy index accumulate at every point:
for `x` with `T x = (a, w)`, the points `T⁻¹(a, w')`, `w' ∈ W_∞` (the text's "`(a, w_j)`,
`w_j ∈ W_∞`, `w_j → w`" in the proof of Proposition 2.5.6 (preprint 2.36)). -/
theorem exists_tendsto_smooth_degIndexWith (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (x : E 0) : ∃ (ι : Type) (l : Filter ι) (σ : ι → E 0), l.NeBot ∧ Tendsto σ l (𝓝 x) ∧
      (∀ᶠ i in l, σ i ∈ E.smooth) ∧ (∀ i, degIndexWith T (σ i) = degIndexWith T x) ∧
      (∀ i, T 0 (σ i) ∈ quadrant n W 0 ↔ T 0 x ∈ quadrant n W 0) := by
  set a := (T 0 x).1 with ha
  set w := (T 0 x).2 with hw
  let Ws : Set (W 0) := (W.smooth : Set (W 0))
  have hdense : Dense Ws := W.dense_smooth 0
  let σ : W 0 → E 0 := fun w' => (T 0).symm (a, w')
  have hcont : Continuous σ := (T 0).symm.continuous.comp (continuous_const.prodMk continuous_id)
  have hx : σ w = x := by
    simp only [σ, ha, hw, Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply]
  refine ⟨W 0, 𝓝[Ws] w, σ, mem_closure_iff_nhdsWithin_neBot.1 (hdense w), ?_, ?_, ?_, ?_⟩
  · rw [← hx]
    exact (hcont.tendsto w).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with w' hw'
    have hp : ((a, w') : ((ScBanach.const (Fin n → ℝ)).prod W) 0) ∈
        (((ScBanach.const (Fin n → ℝ)).prod W).smoothLvl 0) := by
      rw [ScBanach.prod_smoothLvl]
      refine ⟨?_, hw'⟩
      rw [ScBanach.constScale_smoothLvl]; exact mem_univ _
    exact T.symm.toScOperator.mapsTo_smoothLvl 0 hp
  · intro w'
    change quadrantDeg (T 0 ((T 0).symm (a, w'))) = quadrantDeg (T 0 x)
    rw [ContinuousLinearEquiv.apply_symm_apply]
    rfl
  · intro w'
    change T 0 ((T 0).symm (a, w')) ∈ quadrant n W 0 ↔ _
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact Iff.rfl

/-- An sc⁰ map sends the smooth points of `U` to smooth points. -/
lemma IsSc0.mem_smooth {F : ScBanach} {U : Set (E 0)} {f : E 0 → F 0} (hf : IsSc0 E F U f)
    {y : E 0} (hyU : y ∈ U) (hy : y ∈ E.smooth) : f y ∈ F.smooth := by
  rw [ScScale.mem_smooth_iff] at hy ⊢
  intro m
  obtain ⟨z, hz⟩ := hy m
  have hzU : z ∈ E.lvlSet U m := by rw [ScBanach.mem_lvlSet, hz]; exact hyU
  obtain ⟨u, hu⟩ := hf.mem_range m z hzU
  exact ⟨u, by rw [hu, hz]⟩

/-- A smooth point of `E₀` as a point of `E₁` in `E_∞`. -/
lemma exists_smoothLvl_one_of_mem_smooth {y : E 0} (hy : y ∈ E.smooth) :
    ∃ z : E 1, E.toBase 1 z = y ∧ z ∈ E.smoothLvl 1 := by
  obtain ⟨z, hz⟩ := (ScScale.mem_smooth_iff _).1 hy 1
  exact ⟨z, hz, by change E.toBase 1 z ∈ E.smooth; rw [hz]; exact hy⟩

end Approx

/-! ### Tame charts realize the degeneracy index; Proposition 2.5.6 (preprint 2.36) -/

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)
  {n : ℕ} {W : ScBanach}

/-- A chart modelled on a tame retract realizes the minimum of Definition 2.4.1 (preprint 2.22) at every point
of its domain: `d_X(x) = d_C(φ(x))`.  At a smooth point this is `d_C(φ x) = dim(T/T^R) ≤ d_X(x)`
(tameness (2) and Theorem 2.4.12 (preprint 2.31)); at a general point one approximates `φ(x)` by the smooth points
`r(T⁻¹(a, w_j))` of the same index (tameness (1)) and uses Lemma 2.4.3 (preprint 2.23), as in the proof of
Proposition 2.5.6 (preprint 2.36). -/
theorem degIndex_eq_chartDegIndex_of_isTameWith {φ : MChart X} (hφ : P.IsChart φ)
    (R : ScRetraction φ.model.E φ.model.C) (hR : R.retract = φ.model.O)
    {T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)}
    (hT : φ.model.C = T 0 ⁻¹' quadrant n W 0) (htame : R.IsTameWith T) {x : X}
    (hx : x ∈ φ.source) : P.degIndex x = chartDegIndex φ x := by
  -- the smooth case
  have hsmooth : ∀ y ∈ φ.source, φ y ∈ φ.model.E.smooth → P.degIndex y = chartDegIndex φ y := by
    intro y hy hys
    obtain ⟨z, hz, hzs⟩ := exists_smoothLvl_one_of_mem_smooth hys
    have hzO : z ∈ φ.model.E.lvlSet R.retract 1 := by
      rw [ScBanach.mem_lvlSet, hz, hR]; exact φ.mapsTo_model y hy
    have h1 := quotDim_reducedTangentSpaceWith_eq htame hzO hzs
    have h2 := theorem_2_4_12 P hφ R hR T hT hy hz
    refine le_antisymm (P.degIndex_le hφ hy) ?_
    rw [chartDegIndex, degIndex_eq T hT (φ.apply_mem_C hy), ← hz, ← h1]
    exact h2
  refine le_antisymm (P.degIndex_le hφ hx) ?_
  -- approximate `o = φ(x)` by smooth points of `O` of the same index
  set o := φ x with ho
  have hoO : o ∈ φ.model.O := φ.mapsTo_model x hx
  have hoC : o ∈ φ.model.C := φ.apply_mem_C hx
  have hoU : o ∈ R.U := R.retract_subset (hR ▸ hoO)
  obtain ⟨ι, l, σ, hl, hσ, hσs, hσdeg, hσC⟩ := exists_tendsto_smooth_degIndexWith T o
  obtain ⟨V₀, hV₀, hUV⟩ := R.relOpen.relOpen
  have hoq : T 0 o ∈ quadrant n W 0 := by rw [hT] at hoC; exact hoC
  have hσU : ∀ᶠ i in l, σ i ∈ R.U := by
    filter_upwards [hσ.eventually (hV₀.mem_nhds (hUV ▸ hoU).1)] with i hi
    rw [hUV]; exact ⟨hi, by rw [hT, mem_preimage, hσC]; exact hoq⟩
  have hRσ : Tendsto (fun i => R (σ i)) l (𝓝 o) := by
    have hc := (R.isSc1.isSc0.continuousOn_base o hoU).tendsto
    rw [R.apply_eq_self_of_mem_retract (hR ▸ hoO)] at hc
    exact hc.comp (tendsto_nhdsWithin_iff.2 ⟨hσ, hσU⟩)
  have hRσO : ∀ᶠ i in l, R (σ i) ∈ φ.model.O := by
    filter_upwards [hσU] with i hi; rw [← hR]; exact R.apply_mem_retract hi
  have hy : Tendsto (fun i => φ.symm (R (σ i))) l (𝓝 x) := by
    have hc := (φ.continuousOn_invFun o hoO).tendsto
    have h1 : φ.symm o = x := φ.symm_apply_apply hx
    have := hc.comp (tendsto_nhdsWithin_iff.2 ⟨hRσ, hRσO⟩)
    rwa [show (φ.toPartialEquiv.symm o : X) = x from h1] at this
  have hev : ∀ᶠ i in l, chartDegIndex φ x ≤ P.degIndex x := by
    filter_upwards [hσU, hRσO, hσs, hy.eventually (lemma_2_4_3 P x)] with i hiU hiO his hile
    have hyi : φ.symm (R (σ i)) ∈ φ.source := φ.symm_mapsTo hiO
    have hφyi : φ (φ.symm (R (σ i))) = R (σ i) := φ.apply_symm_apply hiO
    have hsm : φ (φ.symm (R (σ i))) ∈ φ.model.E.smooth := by
      rw [hφyi]; exact R.isSc1.isSc0.mem_smooth hiU his
    have hiC : σ i ∈ φ.model.C := R.U_subset_C hiU
    have hRiC : R (σ i) ∈ φ.model.C := R.U_subset_C (R.mapsTo hiU)
    calc chartDegIndex φ x = degIndexWith T o := degIndex_eq T hT hoC
      _ = degIndexWith T (σ i) := (hσdeg i).symm
      _ = Polyfold.degIndex φ.model.E φ.model.C (σ i) := (degIndex_eq T hT hiC).symm
      _ = Polyfold.degIndex φ.model.E φ.model.C (R (σ i)) := (htame.degIndex_apply _ hiU).symm
      _ = chartDegIndex φ (φ.symm (R (σ i))) := by rw [chartDegIndex, hφyi]
      _ = P.degIndex (φ.symm (R (σ i))) := (hsmooth _ hyi hsm).symm
      _ ≤ P.degIndex x := hile
  have := hl
  exact hev.exists.elim fun _ h => h

/-- A chart of the structure modelled on a tame retract (Definition 2.5.2 (preprint 2.34)) realizes `d_X`. -/
theorem degIndex_eq_chartDegIndex_of_isTameRetract {φ : MChart X} (hφ : P.IsChart φ)
    (htame : IsTameRetract φ.model.E φ.model.C φ.model.O) {x : X} (hx : x ∈ φ.source) :
    P.degIndex x = chartDegIndex φ x := by
  obtain ⟨R, hR, hRt⟩ := htame
  obtain ⟨n, W, T, hT⟩ := φ.model.isPartialQuadrant
  exact P.degIndex_eq_chartDegIndex_of_isTameWith hφ R hR hT (hRt n W T hT) hx

end MPolyfold

/-- The local model `(O, C, E)` of a retraction `r` with `O = r(U)`. -/
def ScRetraction.toLocalModel {C : Set (E 0)} (R : ScRetraction E C) : LocalModel :=
  ⟨E, C, R.retract, R.isScRetract⟩

section Prop236

variable {n : ℕ} {W : ScBanach} {C : Set (E 0)}

/-- Proposition 2.5.6 (preprint 2.36), equation (14), for a local model `(O, C, E)` with a tame retraction `r` onto
`O`: the degeneracy index of the M-polyfold `O` is `d_O(x) = d_C(x)`. -/
theorem LocalModel.degIndex_toMPolyfold_of_isTameWith (M : LocalModel) (hne : M.O.Nonempty)
    (R : ScRetraction M.E M.C) (hRM : R.retract = M.O)
    {T : ScIso M.E ((ScBanach.const (Fin n → ℝ)).prod W)} (hT : M.C = T 0 ⁻¹' quadrant n W 0)
    (hR : R.IsTameWith T) (x : M.O) :
    (M.toMPolyfold hne).degIndex x = degIndex M.E M.C x :=
  (M.toMPolyfold hne).degIndex_eq_chartDegIndex_of_isTameWith
    ((M.toMPolyfold hne).isChart_of_mem (mem_singleton _)) R hRM hT hR (mem_univ x)

/-- **Proposition 2.5.6 (preprint 2.36)**, equation (14): for a tame retraction `r : U → U` (with respect to the
presentation `T` of `C`) the degeneracy index of the retract `O = r(U)`, viewed as an M-polyfold,
is `d_O(x) = d_C(x)` for every `x ∈ O`. -/
theorem proposition_2_5_6_degIndex {R : ScRetraction E C}
    {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)} (hT : C = T 0 ⁻¹' quadrant n W 0)
    (hR : R.IsTameWith T) (hne : R.retract.Nonempty) (x : R.retract) :
    (R.toLocalModel.toMPolyfold hne).degIndex x = degIndex E C x :=
  R.toLocalModel.degIndex_toMPolyfold_of_isTameWith hne R rfl hT hR x

/-- **Proposition 2.5.6 (preprint 2.36)**, equation (13): at a smooth point `x ∈ O`,
`dim(T_xO / T_x^R O) = d_O(x)` (and `= d_C(x)`). -/
theorem proposition_2_5_6 {R : ScRetraction E C}
    {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)} (hT : C = T 0 ⁻¹' quadrant n W 0)
    (hR : R.IsTameWith T) {x : E 1} (hx : x ∈ E.lvlSet R.retract 1) (hs : x ∈ E.smoothLvl 1) :
    quotDim (LinearMap.range (scDeriv R.U R x : E 0 →ₗ[ℝ] E 0)) (reducedTangentSpaceWith R T x) =
        (R.toLocalModel.toMPolyfold ⟨_, hx⟩).degIndex ⟨E.toBase 1 x, hx⟩ ∧
      (R.toLocalModel.toMPolyfold ⟨_, hx⟩).degIndex ⟨E.toBase 1 x, hx⟩ =
        degIndex E C (E.toBase 1 x) := by
  have h14 := proposition_2_5_6_degIndex hT hR ⟨_, hx⟩ ⟨E.toBase 1 x, hx⟩
  refine ⟨?_, h14⟩
  rw [quotDim_reducedTangentSpaceWith_eq hR hx hs, ← degIndex_eq T hT (R.retract_subset_C hx)]
  exact h14.symm

end Prop236

/-! ### Coordinates of a presented partial quadrant -/

section Coord

variable {n : ℕ} {W : ScBanach} (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))

/-- `I(z) = {i | λ_i(z) = 0}`, the vanishing half-line coordinates of `z` (presentation `T`). -/
def zeroSet (z : E 0) : Finset (Fin n) := Finset.univ.filter fun i => (T 0 z).1 i = 0

lemma degIndexWith_eq_card_zeroSet (z : E 0) : degIndexWith T z = (zeroSet T z).card := rfl

lemma mem_zeroSet {z : E 0} {i : Fin n} : i ∈ zeroSet T z ↔ (T 0 z).1 i = 0 := by
  simp [zeroSet]

lemma continuous_coord (i : Fin n) : Continuous fun z : E 0 => (T 0 z).1 i :=
  (continuous_apply i).comp (continuous_fst.comp (T 0).continuous)

/-- The coordinate hyperplane `f_i = {λ_i = 0}`, the extended face of Lemma 2.5.12 (preprint 2.40). -/
def coordHyper (i : Fin n) : Set (E 0) := {z | (T 0 z).1 i = 0}

lemma isClosed_coordHyper (i : Fin n) : IsClosed (coordHyper T i) :=
  isClosed_eq (continuous_coord T i) continuous_const

/-- Semicontinuity of the vanishing set: `I(z) ⊆ I(e)` for `z` near `e`. -/
theorem eventually_zeroSet_subset (e : E 0) : ∀ᶠ z in 𝓝 e, zeroSet T z ⊆ zeroSet T e := by
  have h : ∀ i : Fin n, ∀ᶠ z in 𝓝 e, (T 0 z).1 i = 0 → (T 0 e).1 i = 0 := by
    intro i
    by_cases hi : (T 0 e).1 i = 0
    · exact Eventually.of_forall fun _ _ => hi
    · exact (((continuous_coord T i).tendsto e).eventually (isOpen_ne.mem_nhds hi)).mono
        fun z hz h0 => (hz h0).elim
  filter_upwards [eventually_all.2 h] with z hz
  intro i hi
  rw [mem_zeroSet] at hi ⊢
  exact hz i hi

variable {T} {C : Set (E 0)}

lemma coord_nonneg (hT : C = T 0 ⁻¹' quadrant n W 0) {z : E 0} (hz : z ∈ C) (i : Fin n) :
    0 ≤ (T 0 z).1 i := by
  rw [hT] at hz; exact hz i

/-- A point of `C` with `d = 1` and `λ_i = 0` has `I = {i}`. -/
lemma zeroSet_eq_singleton {z : E 0} {i : Fin n} (h1 : degIndexWith T z = 1)
    (hi : (T 0 z).1 i = 0) : zeroSet T z = {i} := by
  rw [degIndexWith_eq_card_zeroSet, Finset.card_eq_one] at h1
  obtain ⟨j, hj⟩ := h1
  have : i ∈ zeroSet T z := (mem_zeroSet T).2 hi
  rw [hj, Finset.mem_singleton] at this
  rw [hj, this]

/-- **The label of a stratum piece** (Lemma 2.5.12 (preprint 2.40)'s "there exists an index `i` such that `F̂` lies
in `{a_i = 0}`", Lemma 4.A of the exposition): a preconnected subset of `{z ∈ C | d_C(z) = 1}`
containing a point with `λ_i = 0` lies in the hyperplane `f_i`. -/
theorem subset_coordHyper_of_isPreconnected (hT : C = T 0 ⁻¹' quadrant n W 0) {S : Set (E 0)}
    (hS : IsPreconnected S) (hSC : S ⊆ C) (h1 : ∀ z ∈ S, degIndexWith T z = 1) {p : E 0}
    (hp : p ∈ S) {i : Fin n} (hpi : (T 0 p).1 i = 0) : S ⊆ coordHyper T i := by
  set u : Set (E 0) := ⋂ l ∈ ({i}ᶜ : Set (Fin n)), {w | 0 < (T 0 w).1 l} with hu
  set v : Set (E 0) := {w | 0 < (T 0 w).1 i} with hv
  have huo : IsOpen u := (Set.toFinite _).isOpen_biInter fun l _ =>
    isOpen_lt continuous_const (continuous_coord T l)
  have hvo : IsOpen v := isOpen_lt continuous_const (continuous_coord T i)
  have hcover : S ⊆ u ∪ v := by
    intro w hw
    by_cases hwi : (T 0 w).1 i = 0
    · left
      have hI := zeroSet_eq_singleton (h1 w hw) hwi
      simp only [hu, mem_iInter₂, mem_ofPred_eq]
      intro l hl
      refine lt_of_le_of_ne (coord_nonneg hT (hSC hw) l) (Ne.symm fun h0 => hl ?_)
      have : l ∈ zeroSet T w := (mem_zeroSet T).2 h0
      rw [hI] at this
      exact Finset.mem_singleton.1 this
    · right
      exact lt_of_le_of_ne (coord_nonneg hT (hSC hw) i) (Ne.symm hwi)
  have hdisj : S ∩ (u ∩ v) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun w ⟨hw, hwu, hwv⟩ => ?_
    have h0 : zeroSet T w = ∅ := by
      refine Finset.eq_empty_iff_forall_notMem.2 fun l hl => ?_
      rw [mem_zeroSet] at hl
      by_cases hli : l = i
      · subst hli; exact absurd hl (ne_of_gt hwv)
      · have := mem_iInter₂.1 hwu l hli
        exact absurd hl (ne_of_gt this)
    have := h1 w hw
    rw [degIndexWith_eq_card_zeroSet, h0, Finset.card_empty] at this
    exact zero_ne_one this
  rcases isPreconnected_iff_subset_of_disjoint.1 hS u v huo hvo hcover hdisj with hSu | hSv
  · intro w hw
    have hwu := hSu hw
    by_contra hwi
    have hI : zeroSet T w = ∅ := by
      refine Finset.eq_empty_iff_forall_notMem.2 fun l hl => ?_
      rw [mem_zeroSet] at hl
      by_cases hli : l = i
      · subst hli; exact hwi hl
      · exact absurd hl (ne_of_gt (mem_iInter₂.1 hwu l hli))
    have := h1 w hw
    rw [degIndexWith_eq_card_zeroSet, hI, Finset.card_empty] at this
    exact zero_ne_one this
  · exact absurd hpi (ne_of_gt (hSv hp))

end Coord

/-! ### The derivative along a ray on which a coordinate vanishes -/

section Ray

variable {E' : ScBanach} {U : Set (E 0)} {f : E 0 → E' 0} {D : E 1 → E 0 →L[ℝ] E' 0}

/-- If `f` is sc¹ on `U`, `x ∈ U₁`, `v ∈ E₁`, `x + tv ∈ U₁` for small `t ≥ 0`, and the functional
`L ∘ f` vanishes along the ray `t ↦ x + tv`, `t ∈ [0, ε)`, then `L(Df(x)v) = 0`. -/
theorem IsSc1With.apply_deriv_eq_zero_of_ray (hf : IsSc1With U f D) {x : E 1}
    (hx : x ∈ E.lvlSet U 1) {v : E 1} (hev : ∀ᶠ t : ℝ in 𝓝[≥] 0, x + t • v ∈ E.lvlSet U 1)
    (L : E' 0 →L[ℝ] ℝ) (hzero : ∀ᶠ t : ℝ in 𝓝[≥] 0, L (f (E.toBase 1 (x + t • v))) = 0) :
    L (D x (E.toBase 1 v)) = 0 := by
  set γ : ℝ → E 1 := fun t => x + t • v with hγ
  set s : Set ℝ := {t | γ t ∈ E.lvlSet U 1} with hs
  have hs0 : s ∈ 𝓝[≥] (0 : ℝ) := hev
  set g : ℝ → ℝ := fun t => L (f (E.toBase 1 (γ t))) with hg
  have hγ' : HasDerivAt γ v 0 := by
    simpa [hγ] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hγ0 : γ 0 = x := by simp [hγ]
  have hder : HasDerivWithinAt g (L (D x (E.toBase 1 v))) (Ici 0) 0 := by
    have h1 : HasDerivWithinAt ((f ∘ E.toBase 1) ∘ γ) (((D x).comp (E.toBase 1)) v) s 0 := by
      have hfx : HasFDerivWithinAt (f ∘ E.toBase 1) ((D x).comp (E.toBase 1)) (E.lvlSet U 1)
          (γ 0) := by
        rw [hγ0]; exact hf.hasFDerivWithinAt x hx
      exact HasFDerivWithinAt.comp_hasDerivWithinAt (l := f ∘ E.toBase 1) (f := γ)
        (t := E.lvlSet U 1) (s := s) (0 : ℝ) hfx hγ'.hasDerivWithinAt fun t ht => ht
    have h2 : HasDerivWithinAt ((f ∘ E.toBase 1) ∘ γ) (((D x).comp (E.toBase 1)) v) (Ici 0) 0 :=
      h1.mono_of_mem_nhdsWithin hs0
    exact L.hasFDerivAt.comp_hasDerivWithinAt (0 : ℝ) h2
  have h0 : g 0 = 0 := (hzero.self_of_nhdsWithin (Set.mem_Ici.2 le_rfl))
  have hpos : ∀ᶠ t in 𝓝[≥] (0 : ℝ), 0 ≤ g t := hzero.mono fun t ht => ht.symm ▸ le_rfl
  have hneg : ∀ᶠ t in 𝓝[≥] (0 : ℝ), 0 ≤ (-g) t :=
    hzero.mono fun t ht => by simp only [Pi.neg_apply, hg]; rw [ht, neg_zero]
  have c1 := nonneg_of_hasDerivWithinAt_Ici hder h0 hpos
  have c2 := nonneg_of_hasDerivWithinAt_Ici hder.neg (by simp [h0]) hneg
  linarith

end Ray

/-! ### Rays stay in their face (Lemma 4.B of the exposition) -/

section RayLemma

variable {n : ℕ} {W : ScBanach} {C : Set (E 0)} {R : ScRetraction E C}
  {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)}

/-- The coordinate functional `λ_j` as a continuous linear map. -/
def coordL (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (j : Fin n) : E 0 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j).comp
    ((ContinuousLinearMap.fst ℝ (Fin n → ℝ) (W 0)).comp (T 0 : E 0 →L[ℝ] _))

@[simp] lemma coordL_apply (j : Fin n) (z : E 0) : coordL T j z = (T 0 z).1 j := rfl

/-- **Proposition 2.5.3 (preprint 2.35)**, in coordinates: at a smooth point `x` of a tame retract,
`λ_j ∘ Dr(x) = λ_j` for every `j ∈ I(x)`. -/
theorem coord_scDeriv_eq (hT : C = T 0 ⁻¹' quadrant n W 0) (hR : R.IsTameWith T) {x : E 1}
    (hx : x ∈ E.lvlSet R.retract 1) (hs : x ∈ E.smoothLvl 1) {j : Fin n}
    (hj : (T 0 (E.toBase 1 x)).1 j = 0) (v : E 0) :
    (T 0 (scDeriv R.U R x v)).1 j = (T 0 v).1 j := by
  have h := (proposition_2_5_3 hT hR hx hs).1 ⟨v, rfl⟩
  rw [mem_minimalSubspaceWith] at h
  have := h j hj
  change (T 0 (v - scDeriv R.U R x v)).1 j = 0 at this
  rw [map_sub, Prod.fst_sub, Pi.sub_apply, sub_eq_zero] at this
  exact this.symm

/-- **Rays stay in their face** (Lemma 4.B of the exposition; the step of Lemma 2.5.12 (preprint 2.40) and
Proposition 2.5.15 (preprint 2.43) that the text leaves out).  Let `r` be tame, `x ∈ O` smooth, `i ∈ I(x)`, and `y`
a direction with `λ_i(y) = 0` and `λ_l(y) > 0` for the other `l ∈ I(x)`.  Then for small `τ > 0`
the point `x + τy` lies in `U` with `I(x + τy) = {i}`, and `I(r(x + τy)) = {i}`.

*Proof.* By tameness (1) `r(x + τy)` has `d_C = 1`, by continuity `I(r(x + τy)) ⊆ I(x)`, and by
connectedness of `(0, τ₀]` the vanishing coordinate `j` of `r(x + τy)` does not depend on `τ`;
differentiating `λ_j(r(x + τy)) = 0` at `τ = 0` gives `λ_j(Dr(x)y) = 0`, which equals `λ_j(y)` by
Proposition 2.5.3 (preprint 2.35) (`j ∈ I(x)`); hence `j = i`. -/
theorem ray_zeroSet (hT : C = T 0 ⁻¹' quadrant n W 0) (hR : R.IsTameWith T) {x : E 1}
    (hx : x ∈ E.lvlSet R.retract 1) (hs : x ∈ E.smoothLvl 1) {i : Fin n}
    (hi : (T 0 (E.toBase 1 x)).1 i = 0) {y : E 1} (hyi : (T 0 (E.toBase 1 y)).1 i = 0)
    (hypos : ∀ l, l ≠ i → (T 0 (E.toBase 1 x)).1 l = 0 → 0 < (T 0 (E.toBase 1 y)).1 l) :
    ∀ᶠ τ in 𝓝[>] (0 : ℝ), E.toBase 1 (x + τ • y) ∈ R.U ∧
      zeroSet T (E.toBase 1 (x + τ • y)) = {i} ∧ zeroSet T (R (E.toBase 1 (x + τ • y))) = {i} := by
  classical
  set ι := E.toBase 1 with hι
  have hlin : ∀ (τ : ℝ) l, (T 0 (ι (x + τ • y))).1 l = (T 0 (ι x)).1 l + τ * (T 0 (ι y)).1 l :=
    fun τ l => by
      simp only [hι, map_add, map_smul, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
  have hxO : ι x ∈ R.retract := hx
  have hxU1 : x ∈ E.lvlSet R.U 1 := R.lvlSet_retract_subset 1 hx
  have hxC : ι x ∈ C := R.retract_subset_C hxO
  have hRx : R (ι x) = ι x := R.apply_eq_self_of_mem_retract hxO
  have hcone : ι y ∈ partialQuadrantAtWith T (ι x) := by
    intro l hl
    by_cases hli : l = i
    · subst hli; rw [hyi]
    · exact le_of_lt (hypos l hli hl)
  have hU1 := eventually_add_smul_mem_lvlSet_of_cone T hT R.relOpen hxU1 hcone
  -- the vanishing set of `x + τ y`
  have hIl : ∀ l, ∀ᶠ τ in 𝓝[>] (0 : ℝ), ((T 0 (ι (x + τ • y))).1 l = 0 ↔ l = i) := by
    intro l
    by_cases hli : l = i
    · subst hli
      exact Eventually.of_forall fun τ => by simp [hi, hyi]
    · by_cases hl0 : (T 0 (ι x)).1 l = 0
      · filter_upwards [self_mem_nhdsWithin] with τ hτ
        rw [hlin, hl0, zero_add]
        exact ⟨fun h => absurd h (mul_pos hτ (hypos l hli hl0)).ne', fun h => absurd h hli⟩
      · have hpos : 0 < (T 0 (ι x)).1 l := lt_of_le_of_ne (coord_nonneg hT hxC l) (Ne.symm hl0)
        have hc : Tendsto (fun τ : ℝ => (T 0 (ι x)).1 l + τ * (T 0 (ι y)).1 l) (𝓝 0)
            (𝓝 ((T 0 (ι x)).1 l)) := by
          have := (by fun_prop : Continuous fun τ : ℝ =>
            (T 0 (ι x)).1 l + τ * (T 0 (ι y)).1 l).tendsto (0 : ℝ)
          simpa using this
        exact ((hc.eventually (lt_mem_nhds hpos)).filter_mono nhdsWithin_le_nhds).mono
          fun τ hτ => by rw [hlin]; exact ⟨fun h => absurd h hτ.ne', fun h => absurd h hli⟩
  have hI : ∀ᶠ τ in 𝓝[>] (0 : ℝ), zeroSet T (ι (x + τ • y)) = {i} := by
    filter_upwards [eventually_all.2 hIl] with τ hτ
    ext l
    rw [mem_zeroSet, Finset.mem_singleton]
    exact hτ l
  -- semicontinuity of the vanishing set of `r(x + τ y)`
  have hγ : Tendsto (fun τ : ℝ => ι (x + τ • y)) (𝓝[≥] 0) (𝓝[R.U] (ι x)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, hU1⟩
    have : Continuous fun τ : ℝ => ι (x + τ • y) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hRγ : Tendsto (fun τ : ℝ => R (ι (x + τ • y))) (𝓝[≥] 0) (𝓝 (ι x)) := by
    have hc := (R.isSc1.isSc0.continuousOn_base (ι x) (R.retract_subset hxO)).tendsto
    rw [hRx] at hc
    exact hc.comp hγ
  have hsemi : ∀ᶠ τ in 𝓝[≥] (0 : ℝ), zeroSet T (R (ι (x + τ • y))) ⊆ zeroSet T (ι x) :=
    hRγ.eventually (eventually_zeroSet_subset T (ι x))
  have hall : ∀ᶠ τ in 𝓝[>] (0 : ℝ), x + τ • y ∈ E.lvlSet R.U 1 ∧
      zeroSet T (ι (x + τ • y)) = {i} ∧ zeroSet T (R (ι (x + τ • y))) ⊆ zeroSet T (ι x) := by
    filter_upwards [nhdsWithin_mono _ Ioi_subset_Ici_self hU1, hI,
      nhdsWithin_mono _ Ioi_subset_Ici_self hsemi] with τ h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hall
  set τ₀ := u / 2 with hτ₀
  have hτ₀pos : 0 < τ₀ := half_pos hu
  have hIoc : Ioc 0 τ₀ ⊆ Ioo 0 u := fun τ hτ => ⟨hτ.1, lt_of_le_of_lt hτ.2 (half_lt_self hu)⟩
  have hP : ∀ τ ∈ Ioc 0 τ₀, x + τ • y ∈ E.lvlSet R.U 1 ∧
      zeroSet T (ι (x + τ • y)) = {i} ∧ zeroSet T (R (ι (x + τ • y))) ⊆ zeroSet T (ι x) :=
    fun τ hτ => hsub (hIoc hτ)
  have hdeg1 : ∀ τ ∈ Ioc 0 τ₀, degIndexWith T (R (ι (x + τ • y))) = 1 := by
    intro τ hτ
    obtain ⟨h1, h2, _⟩ := hP τ hτ
    have hzU : ι (x + τ • y) ∈ R.U := h1
    rw [← degIndex_eq T hT (R.U_subset_C (R.mapsTo hzU)), hR.degIndex_apply _ hzU,
      degIndex_eq T hT (R.U_subset_C hzU), degIndexWith_eq_card_zeroSet, h2,
      Finset.card_singleton]
  -- the image of `(0, τ₀]` is preconnected and lies in one face hyperplane `f_j`
  set S := (fun τ : ℝ => R (ι (x + τ • y))) '' Ioc 0 τ₀ with hS
  have hScont : ContinuousOn (fun τ : ℝ => R (ι (x + τ • y))) (Ioc 0 τ₀) := by
    refine (R.isSc1.isSc0.continuousOn_base).comp (by fun_prop : Continuous fun τ : ℝ =>
      ι (x + τ • y)).continuousOn fun τ hτ => (hP τ hτ).1
  have hSconn : IsPreconnected S := isPreconnected_Ioc.image _ hScont
  have hSC : S ⊆ C := by
    rintro _ ⟨τ, hτ, rfl⟩
    exact R.U_subset_C (R.mapsTo (hP τ hτ).1)
  have hS1 : ∀ z ∈ S, degIndexWith T z = 1 := by
    rintro _ ⟨τ, hτ, rfl⟩; exact hdeg1 τ hτ
  have hτ₀mem : τ₀ ∈ Ioc 0 τ₀ := ⟨hτ₀pos, le_rfl⟩
  obtain ⟨j, hj⟩ := Finset.card_eq_one.1
    ((degIndexWith_eq_card_zeroSet T _).symm.trans (hdeg1 τ₀ hτ₀mem))
  have hpj : (T 0 (R (ι (x + τ₀ • y)))).1 j = 0 := by
    rw [← mem_zeroSet T, hj]; exact Finset.mem_singleton_self j
  have hjx : (T 0 (ι x)).1 j = 0 := by
    rw [← mem_zeroSet T]
    exact (hP τ₀ hτ₀mem).2.2 (by rw [hj]; exact Finset.mem_singleton_self j)
  have hSj := subset_coordHyper_of_isPreconnected hT hSconn hSC hS1 ⟨τ₀, hτ₀mem, rfl⟩ hpj
  -- differentiate `λ_j(r(x + τ y)) = 0` at `τ = 0`
  have hzero : ∀ᶠ t : ℝ in 𝓝[≥] 0, coordL T j (R (ι (x + t • y))) = 0 := by
    filter_upwards [Icc_mem_nhdsGE hτ₀pos] with t ht
    rcases eq_or_lt_of_le ht.1 with h0 | hpos
    · subst h0; simp [hRx, hjx]
    · exact hSj ⟨t, ⟨hpos, ht.2⟩, rfl⟩
  have hD := R.isSc1.isSc1With_scDeriv.apply_deriv_eq_zero_of_ray hxU1 hU1 (coordL T j) hzero
  rw [coordL_apply, coord_scDeriv_eq hT hR hx hs hjx] at hD
  have hji : j = i := by
    by_contra hne
    exact absurd hD (hypos j hne hjx).ne'
  subst hji
  filter_upwards [Ioo_mem_nhdsGT hτ₀pos] with τ hτ
  have hτ' : τ ∈ Ioc 0 τ₀ := ⟨hτ.1, hτ.2.le⟩
  obtain ⟨h1, h2, _⟩ := hP τ hτ'
  refine ⟨h1, h2, zeroSet_eq_singleton (hdeg1 τ hτ') (hSj ⟨τ, hτ', rfl⟩)⟩

end RayLemma

/-! ### The local structure of a face (Lemma 4.C of the exposition) -/

section LocalFace

variable {n : ℕ} {W : ScBanach} {C : Set (E 0)} {R : ScRetraction E C}
  {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)}

/-- The stratum `S = {x ∈ O | d_C(x) = 1}` of a retract `O = r(U)` (for a tame `r` this is
`{d_O = 1}` by Proposition 2.5.6 (preprint 2.36)). -/
def ScRetraction.faceStratum (R : ScRetraction E C) : Set (E 0) :=
  {z | z ∈ R.retract ∧ degIndex E C z = 1}

lemma ScRetraction.faceStratum_subset (R : ScRetraction E C) : R.faceStratum ⊆ R.retract :=
  fun _ h => h.1

/-- The point `T⁻¹(b, 0)` for `b ∈ ℝⁿ` (a vector with prescribed half-line coordinates). -/
def coordVec (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (b : Fin n → ℝ) : E 0 :=
  (T 0).symm (b, 0)

lemma coord_coordVec (b : Fin n → ℝ) (l : Fin n) : (T 0 (coordVec T b)).1 l = b l := by
  simp [coordVec]

/-- `T⁻¹(b, 0)` lifts to level `1`. -/
lemma exists_lvl1_coordVec (b : Fin n → ℝ) : ∃ y : E 1, E.toBase 1 y = coordVec T b := by
  refine ⟨(T 1).symm ((b, 0) : ((ScBanach.const (Fin n → ℝ)).prod W) 1), ?_⟩
  rw [T.symm_toBase_comm, ScBanach.prod_toBase]
  simp only [coordVec, map_zero]
  rfl

/-- The direction of Lemma 4.C: `1` on the coordinates of `I \ {i}`, `0` elsewhere. -/
def rayDir (I : Finset (Fin n)) (i : Fin n) : Fin n → ℝ :=
  fun l => if l ∈ I ∧ l ≠ i then 1 else 0

lemma rayDir_self (I : Finset (Fin n)) (i : Fin n) : rayDir I i i = 0 := by simp [rayDir]

lemma rayDir_nonneg (I : Finset (Fin n)) (i l : Fin n) : 0 ≤ rayDir I i l := by
  unfold rayDir; split_ifs <;> norm_num

lemma rayDir_pos {I : Finset (Fin n)} {i l : Fin n} (hl : l ∈ I) (hli : l ≠ i) :
    0 < rayDir I i l := by simp [rayDir, hl, hli]

lemma rayDir_eq_zero {I : Finset (Fin n)} {i l : Fin n} (hl : l ∉ I) : rayDir I i l = 0 := by
  simp [rayDir, hl]

/-- The set `A_i ∩ B = {z ∈ C | |z − e| < ε, I(z) = {i}}` is convex. -/
lemma convex_ball_inter_zeroSet_eq (hT : C = T 0 ⁻¹' quadrant n W 0) (hC : Convex ℝ C) (e : E 0)
    (ε : ℝ) (i : Fin n) :
    Convex ℝ {z | z ∈ Metric.ball e ε ∩ C ∧ zeroSet T z = {i}} := by
  intro z hz z' hz' a b ha hb hab
  refine ⟨⟨convex_ball e ε hz.1.1 hz'.1.1 ha hb hab, hC hz.1.2 hz'.1.2 ha hb hab⟩, ?_⟩
  have hlin : ∀ l, (T 0 (a • z + b • z')).1 l = a * (T 0 z).1 l + b * (T 0 z').1 l := fun l => by
    simp only [map_add, map_smul, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
  ext l
  rw [mem_zeroSet, Finset.mem_singleton, hlin]
  have hzl : (T 0 z).1 l = 0 ↔ l = i := by rw [← mem_zeroSet T, hz.2, Finset.mem_singleton]
  have hzl' : (T 0 z').1 l = 0 ↔ l = i := by rw [← mem_zeroSet T, hz'.2, Finset.mem_singleton]
  constructor
  · intro h0
    by_contra hli
    have p1 : 0 < (T 0 z).1 l :=
      lt_of_le_of_ne (coord_nonneg hT hz.1.2 l) (Ne.symm fun h => hli (hzl.1 h))
    have p2 : 0 < (T 0 z').1 l :=
      lt_of_le_of_ne (coord_nonneg hT hz'.1.2 l) (Ne.symm fun h => hli (hzl'.1 h))
    rcases eq_or_lt_of_le ha with ha0 | hapos
    · subst ha0
      have hb1 : b = 1 := by linarith
      subst hb1
      linarith
    · nlinarith [mul_pos hapos p1, mul_nonneg hb p2.le]
  · intro hli
    rw [hzl.2 hli, hzl'.2 hli]; ring

/-- **The local structure of a face** (Lemma 4.C of the exposition, which supplies what the
text's proof of Lemma 2.5.12 (preprint 2.40) sketches).  Let `r` be tame, `e ∈ O` with `λ_i(e) = 0`.  There are
`ε > 0` and a point `p ∈ S` with `λ_i(p) = 0` such that, with `B = {z ∈ C | |z − e| < ε}`:
`B ⊆ U`; `I(z) ⊆ I(e)` and `I(r(z)) ⊆ I(e)` on `B`; `r` maps `A_i ∩ B = {z ∈ B | I(z) = {i}}` into
the connected component `F̂(e)` of `S` through `p`; and every `e' ∈ f_i ∩ O ∩ B` lies in the
closure of `F̂(e)`. -/
theorem local_face_structure (hT : C = T 0 ⁻¹' quadrant n W 0) (hR : R.IsTameWith T) {e : E 0}
    (he : e ∈ R.retract) {i : Fin n} (hei : (T 0 e).1 i = 0) :
    ∃ ε > 0, ∃ p ∈ R.faceStratum, (T 0 p).1 i = 0 ∧
      Metric.ball e ε ∩ C ⊆ R.U ∧
      (∀ z ∈ Metric.ball e ε ∩ C, zeroSet T z ⊆ zeroSet T e) ∧
      (∀ z ∈ Metric.ball e ε ∩ C, zeroSet T (R z) ⊆ zeroSet T e) ∧
      (∀ z ∈ Metric.ball e ε ∩ C, zeroSet T z = {i} → R z ∈ connectedComponentIn R.faceStratum p) ∧
      (∀ e' ∈ Metric.ball e ε ∩ C, (T 0 e').1 i = 0 →
        R e' ∈ closure (connectedComponentIn R.faceStratum p)) := by
  classical
  have heU : e ∈ R.U := R.retract_subset he
  have heC : e ∈ C := R.U_subset_C heU
  have hRe : R e = e := R.apply_eq_self_of_mem_retract he
  have hRcont : ContinuousOn R R.U := R.isSc1.isSc0.continuousOn_base
  obtain ⟨V₀, hV₀, hUV⟩ := R.relOpen.relOpen
  have heV₀ : e ∈ V₀ := (hUV ▸ heU).1
  -- (a) the radius
  obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.isOpen_iff.1 hV₀ e heV₀
  obtain ⟨ε₂, hε₂, hb₂⟩ := Metric.mem_nhds_iff.1 (eventually_zeroSet_subset T e)
  have h3 : ∀ᶠ z in 𝓝[R.U] e, zeroSet T (R z) ⊆ zeroSet T e := by
    have hc := (hRcont e heU).tendsto
    rw [hRe] at hc
    exact hc.eventually (eventually_zeroSet_subset T e)
  obtain ⟨ε₃, hε₃, hb₃⟩ := Metric.mem_nhdsWithin_iff.1 h3
  set ε := min ε₁ (min ε₂ ε₃) with hε
  have hεpos : 0 < ε := lt_min hε₁ (lt_min hε₂ hε₃)
  have hball₁ : Metric.ball e ε ⊆ Metric.ball e ε₁ := Metric.ball_subset_ball (min_le_left _ _)
  have hball₂ : Metric.ball e ε ⊆ Metric.ball e ε₂ :=
    Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))
  have hball₃ : Metric.ball e ε ⊆ Metric.ball e ε₃ :=
    Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))
  have hBU : Metric.ball e ε ∩ C ⊆ R.U := fun z hz => by
    rw [hUV]; exact ⟨hb₁ (hball₁ hz.1), hz.2⟩
  have hBI : ∀ z ∈ Metric.ball e ε ∩ C, zeroSet T z ⊆ zeroSet T e := fun z hz =>
    hb₂ (hball₂ hz.1)
  have hBRI : ∀ z ∈ Metric.ball e ε ∩ C, zeroSet T (R z) ⊆ zeroSet T e := fun z hz =>
    hb₃ ⟨hball₃ hz.1, hBU hz⟩
  -- the set `A_i ∩ B` and its image
  set A := {z | z ∈ Metric.ball e ε ∩ C ∧ zeroSet T z = {i}} with hA
  have hAconv : Convex ℝ A :=
    convex_ball_inter_zeroSet_eq hT R.relOpen.isPartialQuadrant.convex e ε i
  have hAU : A ⊆ R.U := fun z hz => hBU hz.1
  have hRAS : R '' A ⊆ R.faceStratum := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨R.apply_mem_retract (hAU hz), ?_⟩
    rw [hR.degIndex_apply _ (hAU hz), degIndex_eq T hT hz.1.2, degIndexWith_eq_card_zeroSet, hz.2,
      Finset.card_singleton]
  have hRAconn : IsPreconnected (R '' A) :=
    hAconv.isPreconnected.image _ (hRcont.mono hAU)
  -- (b) a point of `R(A)`: a smooth `u ∈ O ∩ B` with `I(u) = I(e)` and the ray of Lemma 4.B
  obtain ⟨ι', l, σ, hl, hσ, hσs, hσdeg, hσC⟩ := exists_tendsto_smooth_degIndexWith T e
  have heq : T 0 e ∈ quadrant n W 0 := by rw [hT] at heC; exact heC
  have hσU : ∀ᶠ k in l, σ k ∈ R.U := by
    filter_upwards [hσ.eventually (hV₀.mem_nhds heV₀)] with k hk
    rw [hUV]; exact ⟨hk, by rw [hT, mem_preimage, hσC]; exact heq⟩
  have hRσ : Tendsto (fun k => R (σ k)) l (𝓝 e) := by
    have hc := (hRcont e heU).tendsto
    rw [hRe] at hc
    exact hc.comp (tendsto_nhdsWithin_iff.2 ⟨hσ, hσU⟩)
  obtain ⟨k, hkU, hks, hkB⟩ := (hσU.and (hσs.and
    (hRσ.eventually (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hεpos))))).exists
  set u := R (σ k) with hu
  have huO : u ∈ R.retract := R.apply_mem_retract hkU
  have huC : u ∈ C := R.retract_subset_C huO
  have hus : u ∈ E.smooth := R.isSc1.isSc0.mem_smooth hkU hks
  have hIu : zeroSet T u = zeroSet T e := by
    refine Finset.eq_of_subset_of_card_le (hBI u ⟨hkB, huC⟩) ?_
    rw [← degIndexWith_eq_card_zeroSet, ← degIndexWith_eq_card_zeroSet, ← degIndex_eq T hT huC,
      hR.degIndex_apply _ hkU, degIndex_eq T hT (R.U_subset_C hkU), hσdeg k]
  obtain ⟨xu, hxu, hxus⟩ := exists_smoothLvl_one_of_mem_smooth hus
  have hxuO : xu ∈ E.lvlSet R.retract 1 := by rw [ScBanach.mem_lvlSet, hxu]; exact huO
  obtain ⟨y, hy⟩ := exists_lvl1_coordVec (T := T) (rayDir (zeroSet T e) i)
  have hui : (T 0 (E.toBase 1 xu)).1 i = 0 := by
    rw [hxu, ← mem_zeroSet T, hIu, mem_zeroSet T]; exact hei
  have hyi : (T 0 (E.toBase 1 y)).1 i = 0 := by rw [hy, coord_coordVec, rayDir_self]
  have hypos : ∀ l, l ≠ i → (T 0 (E.toBase 1 xu)).1 l = 0 → 0 < (T 0 (E.toBase 1 y)).1 l := by
    intro l hli hl0
    rw [hy, coord_coordVec]
    rw [hxu, ← mem_zeroSet T, hIu] at hl0
    exact rayDir_pos hl0 hli
  have hray := ray_zeroSet hT hR hxuO hxus hui hyi hypos
  have hrayB : ∀ᶠ τ in 𝓝[>] (0 : ℝ), E.toBase 1 (xu + τ • y) ∈ Metric.ball e ε := by
    have hc : Tendsto (fun τ : ℝ => E.toBase 1 (xu + τ • y)) (𝓝 0) (𝓝 u) := by
      have : Continuous fun τ : ℝ => E.toBase 1 (xu + τ • y) := by fun_prop
      simpa [hxu] using this.tendsto 0
    exact (hc.eventually (Metric.isOpen_ball.mem_nhds hkB)).filter_mono nhdsWithin_le_nhds
  obtain ⟨τ₁, ⟨hz₁U, hz₁I, hRz₁I⟩, hz₁B⟩ := (hray.and hrayB).exists
  set z₁ := E.toBase 1 (xu + τ₁ • y) with hz₁
  have hz₁A : z₁ ∈ A := ⟨⟨hz₁B, R.U_subset_C hz₁U⟩, hz₁I⟩
  set p := R z₁ with hp
  have hpS : p ∈ R.faceStratum := hRAS ⟨z₁, hz₁A, rfl⟩
  have hpi : (T 0 p).1 i = 0 := by rw [← mem_zeroSet T, hRz₁I]; exact Finset.mem_singleton_self i
  have hRA : R '' A ⊆ connectedComponentIn R.faceStratum p :=
    hRAconn.subset_connectedComponentIn ⟨z₁, hz₁A, rfl⟩ hRAS
  refine ⟨ε, hεpos, p, hpS, hpi, hBU, hBI, hBRI, fun z hz hzI => hRA ⟨z, ⟨hz, hzI⟩, rfl⟩, ?_⟩
  -- (c) points of `f_i ∩ O ∩ B` are limits of points of `R(A)`
  rintro e' ⟨he'B, he'C⟩ he'i
  have he'U : e' ∈ R.U := hBU ⟨he'B, he'C⟩
  set y' := coordVec T (rayDir (zeroSet T e') i) with hy'
  have hlin : ∀ (t : ℝ) l, (T 0 (e' + t • y')).1 l = (T 0 e').1 l + t * rayDir (zeroSet T e') i l :=
    fun t l => by
      simp only [map_add, map_smul, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, hy']
      rw [coord_coordVec]
  have hcont : Tendsto (fun t : ℝ => e' + t • y') (𝓝 0) (𝓝 e') := by
    have : Continuous fun t : ℝ => e' + t • y' := by fun_prop
    simpa using this.tendsto 0
  have hpath : ∀ᶠ t in 𝓝[>] (0 : ℝ), e' + t • y' ∈ A := by
    filter_upwards [self_mem_nhdsWithin,
      (hcont.eventually (Metric.isOpen_ball.mem_nhds he'B)).filter_mono nhdsWithin_le_nhds]
      with t ht htB
    have htC : e' + t • y' ∈ C := by
      rw [hT]; intro l
      change 0 ≤ (T 0 (e' + t • y')).1 l
      rw [hlin]
      exact add_nonneg (coord_nonneg hT he'C l) (mul_nonneg (le_of_lt ht) (rayDir_nonneg _ _ _))
    refine ⟨⟨htB, htC⟩, ?_⟩
    ext l
    rw [mem_zeroSet, Finset.mem_singleton, hlin]
    constructor
    · intro h0
      by_contra hli
      by_cases hl : l ∈ zeroSet T e'
      · have := rayDir_pos hl hli
        have h1 : (T 0 e').1 l = 0 := (mem_zeroSet T).1 hl
        rw [h1, zero_add] at h0
        exact absurd h0 (mul_pos ht this).ne'
      · rw [rayDir_eq_zero hl, mul_zero, add_zero] at h0
        exact hl ((mem_zeroSet T).2 h0)
    · intro hli; subst hli; rw [he'i, rayDir_self, mul_zero, add_zero]
  have hRpath : Tendsto (fun t : ℝ => R (e' + t • y')) (𝓝[>] 0) (𝓝 (R e')) := by
    have hc := (hRcont e' he'U).tendsto
    refine hc.comp (tendsto_nhdsWithin_iff.2 ⟨hcont.mono_left nhdsWithin_le_nhds, ?_⟩)
    exact hpath.mono fun t ht => hAU ht
  exact mem_closure_of_tendsto hRpath (hpath.mono fun t ht => hRA ⟨_, ht, rfl⟩)

end LocalFace

/-! ### Lemma 2.5.12 (preprint 2.40) and Corollary 2.5.13 (preprint 2.41) -/

/-- A preconnected subset `c` of `F` meeting a subset `G = F ∩ K` (`K` closed) which is
relatively open in `F` lies in `G`. -/
theorem subset_of_relClopen_of_isPreconnected {α : Type*} [TopologicalSpace α] {c F G K : Set α}
    (hc : IsPreconnected c) (hcF : c ⊆ F) (hK : IsClosed K) (hGK : G = F ∩ K)
    (hopen : ∀ e ∈ G, ∃ V ∈ 𝓝 e, F ∩ V ⊆ G) {x : α} (hx : x ∈ c) (hxG : x ∈ G) : c ⊆ G := by
  set u : Set α := {z | ∃ V ∈ 𝓝 z, F ∩ V ⊆ G} with hu
  have huo : IsOpen u := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨V, hV, hVG⟩
    obtain ⟨V', hV'V, hV'o, hzV'⟩ := mem_nhds_iff.1 hV
    exact Filter.mem_of_superset (hV'o.mem_nhds hzV') fun w hw =>
      ⟨V', hV'o.mem_nhds hw, fun t ht => hVG ⟨ht.1, hV'V ht.2⟩⟩
  have hGu : G ⊆ u := fun e he => hopen e he
  have hFu : F ∩ u ⊆ G := fun z ⟨hzF, V, hV, hVG⟩ => hVG ⟨hzF, mem_of_mem_nhds hV⟩
  have hcover : c ⊆ u ∪ Kᶜ := by
    intro z hz
    by_cases hzK : z ∈ K
    · exact Or.inl (hGu (hGK ▸ ⟨hcF hz, hzK⟩))
    · exact Or.inr hzK
  have hdisj : c ∩ (u ∩ Kᶜ) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun z ⟨hz, hzu, hzK⟩ => hzK ?_
    have : z ∈ G := hFu ⟨hcF hz, hzu⟩
    rw [hGK] at this; exact this.2
  rcases isPreconnected_iff_subset_of_disjoint.1 hc u Kᶜ huo hK.isOpen_compl hcover hdisj with h | h
  · exact fun z hz => hFu ⟨hcF hz, h hz⟩
  · exact absurd (by rw [hGK] at hxG; exact hxG.2) (h hx)

/-- The image under `Subtype.val` of a connected component in a subtype. -/
theorem image_val_connectedComponentIn {α : Type*} [TopologicalSpace α] {O : Set α} {S : Set α}
    (hSO : S ⊆ O) (x : O) :
    Subtype.val '' connectedComponentIn (Subtype.val ⁻¹' S : Set O) x =
      connectedComponentIn S (x : α) := by
  apply Subset.antisymm
  · have := continuous_subtype_val.continuousOn.image_connectedComponentIn_subset
      (s := (Subtype.val ⁻¹' S : Set O)) (a := x)
    by_cases hx : (x : α) ∈ S
    · refine (this hx).trans ?_
      rw [Subtype.image_preimage_coe, inter_eq_right.2 hSO]
    · rw [connectedComponentIn_eq_empty (show x ∉ (Subtype.val ⁻¹' S : Set O) from hx),
        image_empty]
      exact empty_subset _
  · by_cases hx : (x : α) ∈ S
    · set c := connectedComponentIn S (x : α)
      have hcS : c ⊆ S := connectedComponentIn_subset _ _
      have hpre : IsPreconnected (Subtype.val ⁻¹' c : Set O) := by
        refine Topology.IsInducing.subtypeVal.isPreconnected_image.1 ?_
        rw [Subtype.image_preimage_coe, inter_eq_right.2 (hcS.trans hSO)]
        exact isPreconnected_connectedComponentIn
      have hsub := hpre.subset_connectedComponentIn (x := x)
        (show (x : α) ∈ c from mem_connectedComponentIn hx) (preimage_mono hcS)
      intro z hz
      exact ⟨⟨z, hSO (hcS hz)⟩, hsub hz, rfl⟩
    · rw [connectedComponentIn_eq_empty hx]; exact empty_subset _

section Lemma240

variable {n : ℕ} {W : ScBanach} {C : Set (E 0)} {R : ScRetraction E C}
  {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)}

/-- A **face of the retract** `O = r(U)`, in `E₀` (Definition 2.5.10 (preprint 2.39) for the M-polyfold `O`, with
`d_O = d_C` by Proposition 2.5.6 (preprint 2.36)): the closure in `O` of a connected component of
`S = {x ∈ O | d_C(x) = 1}`. -/
def ScRetraction.IsRetractFace (R : ScRetraction E C) (G : Set (E 0)) : Prop :=
  ∃ x ∈ R.faceStratum, G = closure (connectedComponentIn R.faceStratum x) ∩ R.retract

lemma faceStratum_degIndexWith (hT : C = T 0 ⁻¹' quadrant n W 0) {z : E 0}
    (hz : z ∈ R.faceStratum) : degIndexWith T z = 1 := by
  rw [← degIndex_eq T hT (R.retract_subset_C hz.1)]; exact hz.2

/-- A connected component of `S` through a point with `λ_i = 0` lies in `f_i`. -/
lemma connectedComponentIn_faceStratum_subset (hT : C = T 0 ⁻¹' quadrant n W 0) {x : E 0}
    {i : Fin n} (hxi : (T 0 x).1 i = 0) :
    connectedComponentIn R.faceStratum x ⊆ coordHyper T i := by
  by_cases hx : x ∈ R.faceStratum
  · exact subset_coordHyper_of_isPreconnected hT isPreconnected_connectedComponentIn
      ((connectedComponentIn_subset _ _).trans fun z hz => R.retract_subset_C hz.1)
      (fun z hz => faceStratum_degIndexWith hT (connectedComponentIn_subset _ _ hz))
      (mem_connectedComponentIn hx) hxi
  · rw [connectedComponentIn_eq_empty hx]; exact empty_subset _

/-- Lemma 4.C (4): a component of `S` in `f_i` whose closure contains `e` is `F̂(e)`. -/
lemma connectedComponentIn_eq_of_mem_closure (hT : C = T 0 ⁻¹' quadrant n W 0)
    {ε : ℝ} {p : E 0} {e : E 0} {i : Fin n}
    (hB : ∀ z ∈ Metric.ball e ε ∩ C, zeroSet T z = {i} →
      R z ∈ connectedComponentIn R.faceStratum p)
    {q : E 0} (hqi : (T 0 q).1 i = 0) (hq : e ∈ closure (connectedComponentIn R.faceStratum q))
    (hε : 0 < ε) :
    connectedComponentIn R.faceStratum q = connectedComponentIn R.faceStratum p := by
  obtain ⟨z, hzq, hz⟩ := Metric.mem_closure_iff.1 hq ε hε
  have hzS : z ∈ R.faceStratum := connectedComponentIn_subset _ _ hzq
  have hzC : z ∈ C := R.retract_subset_C hzS.1
  have hzi : (T 0 z).1 i = 0 := connectedComponentIn_faceStratum_subset hT hqi hzq
  have hzI : zeroSet T z = {i} := zeroSet_eq_singleton (faceStratum_degIndexWith hT hzS) hzi
  have hzB : z ∈ Metric.ball e ε := by rw [Metric.mem_ball, dist_comm]; exact hz
  have hzp := hB z ⟨hzB, hzC⟩ hzI
  rw [R.apply_eq_self_of_mem_retract hzS.1] at hzp
  rw [connectedComponentIn_eq hzq, ← connectedComponentIn_eq hzp]

/-- **Lemma 2.5.12 (preprint 2.40)**, the core: for `x ∈ S` with `λ_i(x) = 0`, the face `closure(F̂) ∩ O` through
the component `F̂` of `S` at `x` is the connected component of `f_i ∩ O` through `x`. -/
theorem closure_connectedComponentIn_faceStratum (hT : C = T 0 ⁻¹' quadrant n W 0)
    (hR : R.IsTameWith T) {x : E 0} (hx : x ∈ R.faceStratum) {i : Fin n} (hxi : (T 0 x).1 i = 0) :
    closure (connectedComponentIn R.faceStratum x) ∩ R.retract =
      connectedComponentIn (coordHyper T i ∩ R.retract) x := by
  set Gh := connectedComponentIn R.faceStratum x with hGh
  set F := coordHyper T i ∩ R.retract with hF
  set G := closure Gh ∩ R.retract with hG
  have hGhi : Gh ⊆ coordHyper T i := connectedComponentIn_faceStratum_subset hT hxi
  have hclGh : closure Gh ⊆ coordHyper T i :=
    (isClosed_coordHyper T i).closure_subset_iff.2 hGhi
  have hGF : G ⊆ F := fun z hz => ⟨hclGh hz.1, hz.2⟩
  have hxG : x ∈ G := ⟨subset_closure (mem_connectedComponentIn hx), hx.1⟩
  have hGhG : Gh ⊆ G := fun z hz =>
    ⟨subset_closure hz, (connectedComponentIn_subset _ _ hz).1⟩
  have hGpre : IsPreconnected G :=
    isPreconnected_connectedComponentIn.subset_closure hGhG inter_subset_left
  refine Subset.antisymm (hGpre.subset_connectedComponentIn hxG hGF) ?_
  refine subset_of_relClopen_of_isPreconnected isPreconnected_connectedComponentIn
    (connectedComponentIn_subset _ _)
    isClosed_closure (by rw [hF, hG]; ext z; constructor
                         · rintro ⟨h1, h2⟩; exact ⟨⟨hclGh h1, h2⟩, h1⟩
                         · rintro ⟨⟨_, h2⟩, h1⟩; exact ⟨h1, h2⟩) ?_
    (mem_connectedComponentIn (hGF hxG)) hxG
  -- `G` is relatively open in `F`
  intro e he
  have hei : (T 0 e).1 i = 0 := hclGh he.1
  obtain ⟨ε, hε, p, hpS, hpi, -, -, -, hB, hcl⟩ := local_face_structure hT hR he.2 hei
  have hGp : Gh = connectedComponentIn R.faceStratum p :=
    connectedComponentIn_eq_of_mem_closure hT hB hxi he.1 hε
  refine ⟨Metric.ball e ε, Metric.ball_mem_nhds e hε, fun z ⟨hzF, hzB⟩ => ⟨?_, hzF.2⟩⟩
  rw [hGp, ← R.apply_eq_self_of_mem_retract hzF.2]
  exact hcl z ⟨hzB, R.retract_subset_C hzF.2⟩ hzF.1

/-- **Lemma 2.5.12 (preprint 2.40)**, the converse half: for `e ∈ f_i ∩ O`, the connected component of `f_i ∩ O`
through `e` is the face `closure(F̂(e)) ∩ O`, `F̂(e)` the component of `S` of Lemma 4.C. -/
theorem connectedComponentIn_coordHyper_eq (hT : C = T 0 ⁻¹' quadrant n W 0) (hR : R.IsTameWith T)
    {e : E 0} (he : e ∈ R.retract) {i : Fin n} (hei : (T 0 e).1 i = 0) :
    ∃ p ∈ R.faceStratum, (T 0 p).1 i = 0 ∧
      connectedComponentIn (coordHyper T i ∩ R.retract) e =
        closure (connectedComponentIn R.faceStratum p) ∩ R.retract := by
  obtain ⟨ε, hε, p, hpS, hpi, -, -, -, -, hcl⟩ := local_face_structure hT hR he hei
  refine ⟨p, hpS, hpi, ?_⟩
  rw [closure_connectedComponentIn_faceStratum hT hR hpS hpi]
  have heH : e ∈ connectedComponentIn (coordHyper T i ∩ R.retract) p := by
    rw [← closure_connectedComponentIn_faceStratum hT hR hpS hpi]
    have := hcl e ⟨Metric.mem_ball_self hε, R.retract_subset_C he⟩ hei
    rw [R.apply_eq_self_of_mem_retract he] at this
    exact ⟨this, he⟩
  exact (connectedComponentIn_eq heH).symm

/-- **Lemma 2.5.12 (preprint 2.40)**: for a tame retract `(O, C, E)` with extended faces `f_i = {λ_i = 0}`, the faces
of `O` are exactly the connected components of the sets `f_i ∩ O`. -/
theorem lemma_2_5_12 (hT : C = T 0 ⁻¹' quadrant n W 0) (hR : R.IsTameWith T) (G : Set (E 0)) :
    R.IsRetractFace G ↔ ∃ i, ∃ e ∈ R.retract, (T 0 e).1 i = 0 ∧
      G = connectedComponentIn (coordHyper T i ∩ R.retract) e := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := Finset.card_eq_one.1
      ((degIndexWith_eq_card_zeroSet T x).symm.trans (faceStratum_degIndexWith hT hx))
    have hxi : (T 0 x).1 i = 0 := by rw [← mem_zeroSet T, hi]; exact Finset.mem_singleton_self i
    exact ⟨i, x, hx.1, hxi, closure_connectedComponentIn_faceStratum hT hR hx hxi⟩
  · rintro ⟨i, e, he, hei, rfl⟩
    obtain ⟨p, hpS, -, hp⟩ := connectedComponentIn_coordHyper_eq hT hR he hei
    exact ⟨p, hpS, hp⟩

/-- **Lemma 2.5.12 (preprint 2.40)**, second statement: the components of `f_i ∩ O` and `f_j ∩ O` through a point
`x ∈ O` (with `i, j ∈ I(x)`) are equal only if `f_i = f_j`. -/
theorem lemma_2_5_12_injective (hT : C = T 0 ⁻¹' quadrant n W 0) (hR : R.IsTameWith T) {x : E 0}
    (hx : x ∈ R.retract) {i j : Fin n} (hxi : (T 0 x).1 i = 0)
    (h : connectedComponentIn (coordHyper T i ∩ R.retract) x =
      connectedComponentIn (coordHyper T j ∩ R.retract) x) : i = j := by
  obtain ⟨p, hpS, hpi, hp⟩ := connectedComponentIn_coordHyper_eq hT hR hx hxi
  have hpmem : p ∈ connectedComponentIn (coordHyper T i ∩ R.retract) x := by
    rw [hp]; exact ⟨subset_closure (mem_connectedComponentIn hpS), hpS.1⟩
  rw [h] at hpmem
  have hpj : (T 0 p).1 j = 0 := (connectedComponentIn_subset _ _ hpmem).1
  have hI := zeroSet_eq_singleton (faceStratum_degIndexWith hT hpS) hpi
  have : j ∈ zeroSet T p := (mem_zeroSet T).2 hpj
  rw [hI, Finset.mem_singleton] at this
  exact this.symm

/-- **Corollary 2.5.13 (preprint 2.41)**, in `E₀`: in a tame retract every point `x ∈ O` lies in exactly `d_C(x)`
faces (and `d_C(x) = d_O(x)` by Proposition 2.5.6 (preprint 2.36)). -/
theorem corollary_2_5_13_retract (hT : C = T 0 ⁻¹' quadrant n W 0) (hR : R.IsTameWith T) {x : E 0}
    (hx : x ∈ R.retract) :
    {G | R.IsRetractFace G ∧ x ∈ G}.encard = (degIndex E C x : ℕ∞) := by
  classical
  set f : Fin n → Set (E 0) := fun i => connectedComponentIn (coordHyper T i ∩ R.retract) x
  have himage : f '' (zeroSet T x : Set (Fin n)) = {G | R.IsRetractFace G ∧ x ∈ G} := by
    ext G
    constructor
    · rintro ⟨i, hi, rfl⟩
      have hxi : (T 0 x).1 i = 0 := (mem_zeroSet T).1 hi
      exact ⟨(lemma_2_5_12 hT hR _).2 ⟨i, x, hx, hxi, rfl⟩, mem_connectedComponentIn ⟨hxi, hx⟩⟩
    · rintro ⟨hG, hxG⟩
      obtain ⟨i, e, he, hei, rfl⟩ := (lemma_2_5_12 hT hR G).1 hG
      have hxi : (T 0 x).1 i = 0 := (connectedComponentIn_subset _ _ hxG).1
      exact ⟨i, (mem_zeroSet T).2 hxi, (connectedComponentIn_eq hxG).symm⟩
  have hinj : InjOn f (zeroSet T x : Set (Fin n)) := fun i hi j hj hij =>
    lemma_2_5_12_injective hT hR hx ((mem_zeroSet T).1 hi) hij
  rw [← himage, hinj.encard_image, Set.encard_coe_eq_coe_finsetCard,
    degIndex_eq T hT (R.retract_subset_C hx), degIndexWith_eq_card_zeroSet]

end Lemma240

/-! ### Faces of the M-polyfold `O` and Corollary 2.5.13 (preprint 2.41) -/

/-- `val '' closure A = closure (val '' A) ∩ O` for `A ⊆ O`. -/
theorem image_val_closure {α : Type*} [TopologicalSpace α] {O : Set α} (A : Set O) :
    Subtype.val '' closure A = closure (Subtype.val '' A) ∩ O := by
  rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image A,
    Subtype.image_preimage_coe, inter_comm]

namespace LocalModel

variable (M : LocalModel) (hne : M.O.Nonempty) {n : ℕ} {W : ScBanach}
  (R : ScRetraction M.E M.C) (hRM : R.retract = M.O)
  {T : ScIso M.E ((ScBanach.const (Fin n → ℝ)).prod W)}

include hRM in
/-- The faces of the M-polyfold `O` (Definition 2.5.10 (preprint 2.39)) are the faces of the retract in `E₀`
(`ScRetraction.IsRetractFace`), for a tame retraction `r` onto `O`. -/
theorem isFace_toMPolyfold_iff (hT : M.C = T 0 ⁻¹' quadrant n W 0) (hR : R.IsTameWith T)
    (F : Set M.O) :
    (M.toMPolyfold hne).IsFace F ↔ R.IsRetractFace (Subtype.val '' F) := by
  have hd := M.degIndex_toMPolyfold_of_isTameWith hne R hRM hT hR
  have hSO : R.faceStratum ⊆ M.O := fun z hz => by rw [← hRM]; exact hz.1
  have hset : {y : M.O | (M.toMPolyfold hne).degIndex y = 1} =
      (Subtype.val ⁻¹' R.faceStratum : Set M.O) := by
    ext y
    simp only [mem_ofPred_eq, mem_preimage, ScRetraction.faceStratum, hd]
    exact ⟨fun h => ⟨by rw [hRM]; exact y.2, h⟩, fun h => h.2⟩
  constructor
  · rintro ⟨x, hx1, rfl⟩
    have hxS : (x : M.E 0) ∈ R.faceStratum := by
      rw [← mem_preimage, ← hset]; exact hx1
    refine ⟨x, hxS, ?_⟩
    rw [hset, image_val_closure, image_val_connectedComponentIn hSO, hRM]
  · rintro ⟨x, hxS, hG⟩
    refine ⟨⟨x, hSO hxS⟩, by rw [hd]; exact hxS.2, ?_⟩
    apply Set.image_injective.2 Subtype.val_injective
    rw [hG, hset, image_val_closure, image_val_connectedComponentIn hSO, hRM]

include hRM in
/-- **Corollary 2.5.13 (preprint 2.41)**: a tame sc-smooth retract `O` is face-structured: every `x ∈ O` lies in
exactly `d_O(x)` faces of the M-polyfold `O`. -/
theorem isFaceStructured_toMPolyfold (hT : M.C = T 0 ⁻¹' quadrant n W 0) (hR : R.IsTameWith T) :
    (M.toMPolyfold hne).IsFaceStructured := by
  intro x
  have hd := M.degIndex_toMPolyfold_of_isTameWith hne R hRM hT hR
  have hinj : InjOn (fun F : Set M.O => Subtype.val '' F)
      {F | (M.toMPolyfold hne).IsFace F ∧ x ∈ F} :=
    (Set.image_injective.2 Subtype.val_injective).injOn
  have himage : (fun F : Set M.O => Subtype.val '' F) ''
      {F | (M.toMPolyfold hne).IsFace F ∧ x ∈ F} =
        {G | R.IsRetractFace G ∧ (x : M.E 0) ∈ G} := by
    ext G
    constructor
    · rintro ⟨F, ⟨hF, hxF⟩, rfl⟩
      exact ⟨(M.isFace_toMPolyfold_iff hne R hRM hT hR F).1 hF, ⟨x, hxF, rfl⟩⟩
    · rintro ⟨hG, hxG⟩
      have hGO : G ⊆ M.O := by
        obtain ⟨_, _, rfl⟩ := hG; rw [← hRM]; exact inter_subset_right
      have himg : Subtype.val '' (Subtype.val ⁻¹' G : Set M.O) = G := by
        rw [Subtype.image_preimage_coe, inter_eq_right.2 hGO]
      refine ⟨Subtype.val ⁻¹' G, ⟨?_, hxG⟩, himg⟩
      rw [M.isFace_toMPolyfold_iff hne R hRM hT hR, himg]
      exact hG
  rw [← hinj.encard_image, himage, hd]
  exact corollary_2_5_13_retract hT hR (by rw [hRM]; exact x.2)

end LocalModel

/-- **Corollary 2.5.13 (preprint 2.41)**: if `(O, C, E)` is a tame sc-smooth retract, then every point `x ∈ O` lies
in precisely `d_O(x)` faces of `O`. -/
theorem corollary_2_5_13 (M : LocalModel) (hne : M.O.Nonempty)
    (htame : IsTameRetract M.E M.C M.O) : (M.toMPolyfold hne).IsFaceStructured := by
  obtain ⟨R, hR, hRt⟩ := htame
  obtain ⟨n, W, T, hT⟩ := M.isPartialQuadrant
  exact M.isFaceStructured_toMPolyfold hne R hR hT (hRt n W T hT)

/-! ### Proposition 2.5.14 (preprint 2.42) -/

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

/-- The charts of an atlas equivalent to the structure's are charts of the structure. -/
lemma isChart_of_mem_equiv {A : MAtlas X} (hA : A.Equiv P.atlas) {φ : MChart X}
    (hφ : φ ∈ A.charts) : P.IsChart φ :=
  (isChart_congr (P := ⟨A⟩) (Q := P) hA φ).1 ((⟨A⟩ : MPolyfold X).isChart_of_mem hφ)

/-- A tame M-polyfold has, around every point, a chart of the structure modelled on a tame
retract. -/
lemma IsTame.exists_chart (hP : P.IsTame) (x : X) :
    ∃ φ : MChart X, P.IsChart φ ∧ x ∈ φ.source ∧ IsTameRetract φ.model.E φ.model.C φ.model.O := by
  obtain ⟨A, hA, htame⟩ := hP
  obtain ⟨φ, hφ, hx⟩ := A.cover x
  exact ⟨φ, P.isChart_of_mem_equiv hA hφ, hx, htame φ hφ⟩

/-- **Proposition 2.5.14 (preprint 2.42)**, the global statement: in a tame M-polyfold, a point `x` lies in at most
`d_X(x)` faces of `X`.

*Proof.* In a tame chart `φ : V → O` around `x`, with `o = φ(x)`: for each `i ∈ I(o)` Lemma 4.C
gives the component `F̂_i` of `S` such that every point `z` of `O` near `o` with `I(z) = {i}` lies
in `F̂_i`.  A face `F = closure(G)` through `x` has points `y ∈ G` near `x`; `d_C(φ y) = d_X(y) = 1`
and `I(φ y) ⊆ I(o)`, so `I(φ y) = {i}` for some `i ∈ I(o)` and `φ⁻¹(F̂_i)` meets `G`; being
connected in `{d_X = 1}`, it lies in `G`.  Distinct faces give distinct `i`. -/
theorem faces_encard_le (hP : P.IsTame) (x : X) :
    {F | P.IsFace F ∧ x ∈ F}.encard ≤ (P.degIndex x : ℕ∞) := by
  classical
  obtain ⟨φ, hφ, hx, htame⟩ := IsTame.exists_chart P hP x
  obtain ⟨R, hRO, hRt⟩ := htame
  obtain ⟨n, W, T, hT⟩ := φ.model.isPartialQuadrant
  have hR := hRt n W T hT
  have hdeg : ∀ y ∈ φ.source, P.degIndex y = degIndexWith T (φ y) := fun y hy => by
    rw [P.degIndex_eq_chartDegIndex_of_isTameWith hφ R hRO hT hR hy, chartDegIndex,
      degIndex_eq T hT (φ.apply_mem_C hy)]
  set o := φ x with ho
  have hoO : o ∈ R.retract := by rw [hRO]; exact φ.mapsTo_model x hx
  -- the components `F̂_i` of Lemma 4.C at `o`
  have key : ∀ i : Fin n, (T 0 o).1 i = 0 → ∃ p ∈ R.faceStratum, ∀ᶠ z in 𝓝 o, z ∈ φ.model.C →
      zeroSet T z = {i} → R z ∈ connectedComponentIn R.faceStratum p := by
    intro i hi
    obtain ⟨ε, hε, p, hpS, -, -, -, -, hB, -⟩ := local_face_structure hT hR hoO hi
    exact ⟨p, hpS, Filter.mem_of_superset (Metric.ball_mem_nhds o hε) fun z hz hzC hzI =>
      hB z ⟨hz, hzC⟩ hzI⟩
  choose! p hpS hp using key
  have hev : ∀ᶠ z in 𝓝 o, zeroSet T z ⊆ zeroSet T o ∧ ∀ i ∈ zeroSet T o, z ∈ φ.model.C →
      zeroSet T z = {i} → R z ∈ connectedComponentIn R.faceStratum (p i) := by
    refine (eventually_zeroSet_subset T o).and ?_
    exact (Filter.eventually_all_finset _).2 fun i hi => hp i ((mem_zeroSet T).1 hi)
  have hφc : ContinuousAt φ x := φ.continuousOn_toFun.continuousAt (φ.isOpen_source.mem_nhds hx)
  have hevx : ∀ᶠ y in 𝓝 x, y ∈ φ.source ∧ (zeroSet T (φ y) ⊆ zeroSet T o ∧
      ∀ i ∈ zeroSet T o, φ y ∈ φ.model.C → zeroSet T (φ y) = {i} →
        R (φ y) ∈ connectedComponentIn R.faceStratum (p i)) :=
    (show ∀ᶠ y in 𝓝 x, y ∈ φ.source from φ.isOpen_source.mem_nhds hx).and (hφc.eventually hev)
  -- the preconnected sets `φ⁻¹(F̂_i)` lie in `{d_X = 1}`
  have hK : ∀ i, IsPreconnected (φ.symm '' connectedComponentIn R.faceStratum (p i)) ∧
      φ.symm '' connectedComponentIn R.faceStratum (p i) ⊆ {y | P.degIndex y = 1} := by
    intro i
    have hsub : connectedComponentIn R.faceStratum (p i) ⊆ φ.model.O := fun z hz => by
      rw [← hRO]; exact (connectedComponentIn_subset _ _ hz).1
    refine ⟨isPreconnected_connectedComponentIn.image _ (φ.continuousOn_invFun.mono hsub), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hzS := connectedComponentIn_subset _ _ hz
    have hy := φ.symm_mapsTo (hsub hz)
    change P.degIndex (φ.symm z) = 1
    rw [hdeg _ hy, φ.apply_symm_apply (hsub hz)]
    exact faceStratum_degIndexWith hT hzS
  -- every face through `x` contains one of them
  have hex : ∀ F ∈ {F | P.IsFace F ∧ x ∈ F}, ∃ i ∈ zeroSet T o, ∃ y₀, P.degIndex y₀ = 1 ∧
      F = closure (connectedComponentIn {y | P.degIndex y = 1} y₀) ∧
      φ.symm '' connectedComponentIn R.faceStratum (p i) ⊆
        connectedComponentIn {y | P.degIndex y = 1} y₀ := by
    rintro F ⟨⟨y₀, hy₀, rfl⟩, hxF⟩
    obtain ⟨y, hyN, hyG⟩ := mem_closure_iff_nhds.1 hxF _ hevx
    obtain ⟨hyV, hysub, hyB⟩ := hyN
    have hy1 := connectedComponentIn_subset {y | P.degIndex y = 1} y₀ hyG
    change P.degIndex y = 1 at hy1
    have hyC : φ y ∈ φ.model.C := φ.apply_mem_C hyV
    obtain ⟨i, hi⟩ := Finset.card_eq_one.1
      ((degIndexWith_eq_card_zeroSet T _).symm.trans ((hdeg y hyV).symm.trans hy1))
    have hio : i ∈ zeroSet T o := hysub (by rw [hi]; exact Finset.mem_singleton_self i)
    have hRy := hyB i hio hyC hi
    have hφyO : φ y ∈ R.retract := by rw [hRO]; exact φ.mapsTo_model y hyV
    rw [R.apply_eq_self_of_mem_retract hφyO] at hRy
    have hyK : y ∈ φ.symm '' connectedComponentIn R.faceStratum (p i) :=
      ⟨φ y, hRy, φ.symm_apply_apply hyV⟩
    refine ⟨i, hio, y₀, hy₀, rfl, ?_⟩
    rw [connectedComponentIn_eq hyG]
    exact (hK i).1.subset_connectedComponentIn hyK (hK i).2
  rcases Set.eq_empty_or_nonempty {F | P.IsFace F ∧ x ∈ F} with hempty | ⟨F₀, hF₀⟩
  · rw [hempty, Set.encard_empty]; exact bot_le
  have : Nonempty (Fin n) := ⟨(hex F₀ hF₀).choose⟩
  choose! g hg y₀ hy₀ hFy₀ hKy₀ using hex
  have hinj : InjOn g {F | P.IsFace F ∧ x ∈ F} := by
    intro F hF F' hF' hFF'
    have hi : (T 0 o).1 (g F) = 0 := (mem_zeroSet T).1 (hg F hF)
    have hpmem : φ.symm (p (g F)) ∈ φ.symm '' connectedComponentIn R.faceStratum (p (g F)) :=
      ⟨p (g F), mem_connectedComponentIn (hpS (g F) hi), rfl⟩
    have h1 := hKy₀ F hF hpmem
    have h2 := hKy₀ F' hF' (hFF' ▸ hpmem)
    rw [hFy₀ F hF, hFy₀ F' hF', connectedComponentIn_eq h1, connectedComponentIn_eq h2, hFF']
  calc {F | P.IsFace F ∧ x ∈ F}.encard ≤ (zeroSet T o : Set (Fin n)).encard :=
        Set.encard_le_encard_of_injOn (fun F hF => hg F hF) hinj
    _ = (P.degIndex x : ℕ∞) := by
        rw [Set.encard_coe_eq_coe_finsetCard, hdeg x hx, degIndexWith_eq_card_zeroSet]

/-- **Proposition 2.5.14 (preprint 2.42)**: let `X` be a tame M-polyfold.  Every `x ∈ X` has an open neighbourhood
`V`, the domain of a tame chart `φ : V → O`, such that `d_X(y) = d_O(φ(y)) = d_C(φ(y))` for all
`y ∈ V` and every point of `O ≅ V` lies in exactly `d_O` faces of `O` (`O` is face-structured);
globally, `x` lies in at most `d_X(x)` faces of `X`.  The neighbourhood `V` is represented by the
M-polyfold `O` it is sc-diffeomorphic to through `φ`. -/
theorem _root_.Polyfold.proposition_2_5_14 (hP : P.IsTame) (x : X) :
    (∃ φ : MChart X, P.IsChart φ ∧ x ∈ φ.source ∧
      (∀ y ∈ φ.source, P.degIndex y = Polyfold.degIndex φ.model.E φ.model.C (φ y)) ∧
      (∀ y (hy : y ∈ φ.source),
        (φ.model.toMPolyfold ⟨_, φ.mapsTo_model y hy⟩).degIndex ⟨φ y, φ.mapsTo_model y hy⟩ =
          P.degIndex y) ∧
      ∀ hne : φ.model.O.Nonempty, (φ.model.toMPolyfold hne).IsFaceStructured) ∧
    {F | P.IsFace F ∧ x ∈ F}.encard ≤ (P.degIndex x : ℕ∞) := by
  refine ⟨?_, P.faces_encard_le hP x⟩
  obtain ⟨φ, hφ, hx, htame⟩ := IsTame.exists_chart P hP x
  obtain ⟨R, hRO, hRt⟩ := htame
  obtain ⟨n, W, T, hT⟩ := φ.model.isPartialQuadrant
  have hR := hRt n W T hT
  have hdX : ∀ y ∈ φ.source, P.degIndex y = Polyfold.degIndex φ.model.E φ.model.C (φ y) :=
    fun y hy => P.degIndex_eq_chartDegIndex_of_isTameWith hφ R hRO hT hR hy
  refine ⟨φ, hφ, hx, hdX, fun y hy => ?_, fun hne =>
    φ.model.isFaceStructured_toMPolyfold hne R hRO hT hR⟩
  exact (φ.model.degIndex_toMPolyfold_of_isTameWith _ R hRO hT hR _).trans (hdX y hy).symm

end MPolyfold

/-! ### Proposition 2.5.15 (preprint 2.43): the retraction onto a face -/

section Prop243

variable {n : ℕ} {W : ScBanach} {C : Set (E 0)} {R : ScRetraction E C}
  {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)}

/-- `a ↦ a` with the `i`-th coordinate set to `0`, on `ℝⁿ`. -/
def killCoordL (n : ℕ) (i : Fin n) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun l => if l = i then 0 else ContinuousLinearMap.proj l

@[simp] lemma killCoordL_apply (i : Fin n) (a : Fin n → ℝ) (l : Fin n) :
    killCoordL n i a l = if l = i then 0 else a l := by
  unfold killCoordL; split_ifs <;> simp [*]

/-- The sc-operator `(a, w) ↦ ((a_l)_{l ≠ i}, 0_i, w)` of `ℝⁿ ⊕ W`. -/
def killCoordModel (n : ℕ) (W : ScBanach) (i : Fin n) :
    ScOperator ((ScBanach.const (Fin n → ℝ)).prod W) ((ScBanach.const (Fin n → ℝ)).prod W) where
  lvl m := (killCoordL n i).prodMap (ContinuousLinearMap.id ℝ (W m))
  incl_comm _ _ := rfl

/-- The sc-projection `P_i = T⁻¹ ∘ (a_i ↦ 0) ∘ T` of `E` onto the extended face `f_i` (the text's
`(b, v) ↦ (0, b₂, …, b_k, v)` in the proof of Proposition 2.5.15 (preprint 2.43)). -/
def killCoord (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (i : Fin n) : ScOperator E E :=
  T.symm.toScOperator.comp ((killCoordModel n W i).comp T.toScOperator)

lemma killCoord_apply (i : Fin n) (z : E 0) :
    killCoord T i 0 z = (T 0).symm (killCoordL n i (T 0 z).1, (T 0 z).2) := rfl

lemma killCoord_coord (i : Fin n) (z : E 0) (l : Fin n) :
    (T 0 (killCoord T i 0 z)).1 l = if l = i then 0 else (T 0 z).1 l := by
  rw [killCoord_apply, ContinuousLinearEquiv.apply_symm_apply]
  exact killCoordL_apply i _ l

lemma killCoord_eq_self {i : Fin n} {z : E 0} (hz : (T 0 z).1 i = 0) : killCoord T i 0 z = z := by
  apply (T 0).injective
  rw [killCoord_apply, ContinuousLinearEquiv.apply_symm_apply]
  refine Prod.ext (funext fun l => ?_) rfl
  change killCoordL n i (T 0 z).1 l = (T 0 z).1 l
  rw [killCoordL_apply]
  split_ifs with h
  · subst h; exact hz.symm
  · rfl

lemma killCoord_mem (hT : C = T 0 ⁻¹' quadrant n W 0) (i : Fin n) {z : E 0} (hz : z ∈ C) :
    killCoord T i 0 z ∈ C := by
  rw [hT]; intro l
  change 0 ≤ (T 0 (killCoord T i 0 z)).1 l
  rw [killCoord_coord]
  split_ifs
  · exact le_rfl
  · exact coord_nonneg hT hz l

lemma killCoord_coord_self (i : Fin n) (z : E 0) : (T 0 (killCoord T i 0 z)).1 i = 0 := by
  rw [killCoord_coord, if_pos rfl]

/-- **Proposition 2.5.15 (preprint 2.43)**, the retraction: let `r : U → U` be a tame retraction onto `O` and `F` a
face of `O`, contained in the extended face `f_i`.  There are an open neighbourhood `U*` of `F`
in `U` (relatively open in `C`) and an sc-smooth retraction `s : U* → U*` onto `s(U*) = F`, namely
`s = r ∘ P_i` with `P_i` the sc-projection onto `f_i`.  So `(F, C, E)` is an sc-smooth retract.

The text's "we find an open neighbourhood `U_{(a,w)}` … such that `r(0, b₂, …, b_k, v)` has the
first coordinate vanishing and belongs to `F`" is Lemma 4.C (face preservation, which rests on
Lemma 4.B and hence on tameness (2) through Proposition 2.5.3 (preprint 2.35)); the neighbourhoods are taken as
preimages under `P_i` of balls, since `P_i` need not be norm-decreasing for the norm of `E₀`. -/
theorem proposition_2_5_15 (hT : C = T 0 ⁻¹' quadrant n W 0) (hR : R.IsTameWith T) {F : Set (E 0)}
    (hF : R.IsRetractFace F) :
    ∃ i : Fin n, F ⊆ coordHyper T i ∧ ∃ S : ScRetraction E C, F ⊆ S.U ∧ S.U ⊆ R.U ∧
      S.retract = F ∧ EqOn S (R ∘ killCoord T i 0) S.U := by
  classical
  obtain ⟨x, hxS, rfl⟩ := hF
  obtain ⟨i, hi⟩ := Finset.card_eq_one.1
    ((degIndexWith_eq_card_zeroSet T x).symm.trans (faceStratum_degIndexWith hT hxS))
  have hxi : (T 0 x).1 i = 0 := by rw [← mem_zeroSet T, hi]; exact Finset.mem_singleton_self i
  set G := closure (connectedComponentIn R.faceStratum x) ∩ R.retract with hG
  have hGi : G ⊆ coordHyper T i := fun z hz =>
    (isClosed_coordHyper T i).closure_subset_iff.2
      (connectedComponentIn_faceStratum_subset hT hxi) hz.1
  refine ⟨i, hGi, ?_⟩
  set P := killCoord T i 0 with hP
  have hPc : Continuous P := (killCoord T i 0).continuous
  -- Lemma 4.C at every point of the face
  have key : ∀ e ∈ G, ∃ ε > 0, Metric.ball e ε ∩ C ⊆ R.U ∧
      ∀ z ∈ Metric.ball e ε ∩ C, (T 0 z).1 i = 0 → R z ∈ G := by
    intro e he
    obtain ⟨ε, hε, p, hpS, hpi, hBU, -, -, hB, hcl⟩ := local_face_structure hT hR he.2 (hGi he)
    have hGp : connectedComponentIn R.faceStratum x = connectedComponentIn R.faceStratum p :=
      connectedComponentIn_eq_of_mem_closure hT hB hxi he.1 hε
    refine ⟨ε, hε, hBU, fun z hz hzi => ⟨?_, R.apply_mem_retract (hBU hz)⟩⟩
    rw [hGp]; exact hcl z hz hzi
  choose! ε hε hεU hεG using key
  set W₀ : Set (E 0) := ⋃ e ∈ G, Metric.ball e (ε e) ∩ P ⁻¹' Metric.ball e (ε e) with hW₀
  have hW₀o : IsOpen W₀ := isOpen_biUnion fun e _ =>
    Metric.isOpen_ball.inter (Metric.isOpen_ball.preimage hPc)
  set U' := W₀ ∩ C with hU'
  have hPmem : ∀ z ∈ U', ∃ e ∈ G, P z ∈ Metric.ball e (ε e) ∩ C := by
    rintro z ⟨hzW, hzC⟩
    obtain ⟨e, he, hz⟩ := mem_iUnion₂.1 hzW
    exact ⟨e, he, hz.2, killCoord_mem hT i hzC⟩
  have hPU : MapsTo P U' R.U := fun z hz => by
    obtain ⟨e, he, hPz⟩ := hPmem z hz
    exact hεU e he hPz
  have hsG : ∀ z ∈ U', R (P z) ∈ G := fun z hz => by
    obtain ⟨e, he, hPz⟩ := hPmem z hz
    exact hεG e he _ hPz (killCoord_coord_self i z)
  have hGU' : G ⊆ U' := by
    intro e he
    refine ⟨mem_iUnion₂.2 ⟨e, he, Metric.mem_ball_self (hε e he), ?_⟩,
      R.retract_subset_C he.2⟩
    rw [mem_preimage, hP, killCoord_eq_self (hGi he)]
    exact Metric.mem_ball_self (hε e he)
  have hfix : ∀ z ∈ G, R (P z) = z := fun z hz => by
    rw [hP, killCoord_eq_self (hGi hz), R.apply_eq_self_of_mem_retract hz.2]
  have hU'rel : IsRelOpenInQuadrant E C U' := ⟨R.relOpen.isPartialQuadrant, W₀, hW₀o, rfl⟩
  let S : ScRetraction E C :=
    { U := U'
      toFun := R ∘ P
      relOpen := hU'rel
      mapsTo := fun z hz => hGU' (hsG z hz)
      isScSmooth := IsScSmooth.comp hU'rel.isScDomain R.isScDomain R.isScSmooth
        ((killCoord T i).isScSmooth hU'rel.isScDomain) hPU
      idem := fun z hz => hfix _ (hsG z hz) }
  refine ⟨S, hGU', fun z hz => hPU hz |> fun h => ?_, ?_, fun _ _ => rfl⟩
  · -- `U' ⊆ U`: points of `U'` are in a ball `B_e ⊆ U`
    obtain ⟨e, he, hz'⟩ := mem_iUnion₂.1 hz.1
    exact hεU e he ⟨hz'.1, hz.2⟩
  · apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩; exact hsG z hz
    · intro z hz; exact ⟨z, hGU' hz, hfix z hz⟩

end Prop243

namespace LocalModel

variable (M : LocalModel) (hne : M.O.Nonempty) {n : ℕ} {W : ScBanach}
  (R : ScRetraction M.E M.C) (hRM : R.retract = M.O)
  {T : ScIso M.E ((ScBanach.const (Fin n → ℝ)).prod W)}

lemma selfChart_symm_apply {z : M.E 0} (hz : z ∈ M.O) : (M.selfChart hne).symm z = ⟨z, hz⟩ :=
  (M.selfChart hne).symm_apply_apply (x := (⟨z, hz⟩ : M.O)) (mem_univ _)

include hRM in
/-- **Proposition 2.5.15 (preprint 2.43)**, second statement: a face `F` of a tame retract `O` is a sub-M-polyfold of
the M-polyfold `O` (Definition 2.3.18 (preprint 2.20)), with the retraction `s = r ∘ P_i` restricted to
`V = O ∩ U*`. -/
theorem isSubMPolyfold_of_isFace (hT : M.C = T 0 ⁻¹' quadrant n W 0) (hR : R.IsTameWith T)
    {F : Set M.O} (hF : (M.toMPolyfold hne).IsFace F) : (M.toMPolyfold hne).IsSubMPolyfold F := by
  classical
  have hG := (M.isFace_toMPolyfold_iff hne R hRM hT hR F).1 hF
  obtain ⟨i, -, S, hGS, hSU, hSret, -⟩ := proposition_2_5_15 hT hR hG
  obtain ⟨W₀, hW₀, hSW⟩ := S.relOpen.relOpen
  have hOC : M.O ⊆ M.C := M.O_subset_C
  set V : Set M.O := Subtype.val ⁻¹' S.U with hV
  have hVo : IsOpen V := by
    have : V = Subtype.val ⁻¹' W₀ := by
      ext y; rw [hV, mem_preimage, mem_preimage, hSW]
      exact ⟨fun h => h.1, fun h => ⟨h, hOC y.2⟩⟩
    rw [this]; exact hW₀.preimage continuous_subtype_val
  have hSO : ∀ y ∈ V, S y ∈ M.O := fun y hy => by
    have : S y ∈ S.retract := S.apply_mem_retract hy
    rw [hSret] at this
    obtain ⟨z, _, hz⟩ := this
    rw [← hz]; exact z.2
  let r : M.O → M.O := fun y => if h : S y ∈ M.O then ⟨S y, h⟩ else y
  have hr : ∀ y ∈ V, (r y : M.E 0) = S y := fun y hy => by
    simp only [r, dif_pos (hSO y hy)]
  have hFG : ∀ y : M.O, y ∈ F ↔ (y : M.E 0) ∈ Subtype.val '' F := fun y =>
    ⟨fun h => ⟨y, h, rfl⟩, fun ⟨z, hz, hzy⟩ => Subtype.val_injective hzy ▸ hz⟩
  intro a haF
  have haV : a ∈ V := hGS ⟨a, haF, rfl⟩
  refine ⟨V, hVo, haV, r, fun y hy => ?_, ?_, fun y hy => ?_, ?_⟩
  · change (r y : M.E 0) ∈ S.U
    rw [hr y hy]; exact S.mapsTo hy
  · -- sc-smoothness, in the chart `id` of `O`
    have hcont : ContinuousOn r V := by
      rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
      refine (S.isSc1.isSc0.continuousOn_base.comp continuous_subtype_val.continuousOn
        fun y hy => hy).congr fun y hy => hr y hy
    refine MPolyfold.IsScSmoothOn.of_exists_charts hVo hcont fun y hy => ?_
    refine ⟨M.selfChart hne, M.selfChart hne, V,
      (M.toMPolyfold hne).isChart_of_mem (mem_singleton _),
      (M.toMPolyfold hne).isChart_of_mem (mem_singleton _), hVo, hy,
      fun z hz => ⟨hz, mem_univ _⟩, fun _ _ => mem_univ _, ?_⟩
    have himV : (M.selfChart hne) '' V = R.retract ∩ W₀ := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        refine ⟨by rw [hRM]; exact w.2, ?_⟩
        have : (w : M.E 0) ∈ S.U := hw
        rw [hSW] at this; exact this.1
      · rintro ⟨hzO, hzW⟩
        rw [hRM] at hzO
        exact ⟨⟨z, hzO⟩, show z ∈ S.U by rw [hSW]; exact ⟨hzW, hOC hzO⟩, rfl⟩
    rw [himV]
    have hret : IsScRetract M.E M.C (R.retract ∩ W₀) := ⟨R.restrict hW₀, R.restrict_retract hW₀⟩
    have heq : ∀ z : M.E 0, z ∈ R.retract ∩ W₀ →
        ((r ((M.selfChart hne).symm z) : M.O) : M.E 0) = S z := by
      intro z hz
      have hzO : z ∈ M.O := by rw [← hRM]; exact hz.1
      have hzV : (⟨z, hzO⟩ : M.O) ∈ V := show z ∈ S.U by rw [hSW]; exact ⟨hz.2, hOC hzO⟩
      rw [M.selfChart_symm_apply hne hzO]
      exact hr _ hzV
    refine (isScSmoothRetractMap_iff_exists hret).2
      ⟨fun z hz => ?_, R.restrict hW₀, R.restrict_retract hW₀, ?_⟩
    · change ((r ((M.selfChart hne).symm z) : M.O) : M.E 0) ∈ M.O
      rw [heq z hz]
      have hzO : z ∈ M.O := by rw [← hRM]; exact hz.1
      exact hSO ⟨z, hzO⟩ (show z ∈ S.U by rw [hSW]; exact ⟨hz.2, hOC hzO⟩)
    · have hmaps : MapsTo (R.restrict hW₀) (R.restrict hW₀).U S.U := fun w hw => by
        have := (R.restrict hW₀).apply_mem_retract hw
        rw [R.restrict_retract hW₀] at this
        rw [hSW]; exact ⟨this.2, R.retract_subset_C this.1⟩
      have h1 : IsScSmooth (R.restrict hW₀).U (S ∘ R.restrict hW₀) :=
        IsScSmooth.comp (R.restrict hW₀).isScDomain S.isScDomain S.isScSmooth
          (R.restrict hW₀).isScSmooth hmaps
      refine h1.congr (R.restrict hW₀).isScDomain fun w hw => ?_
      have := (R.restrict hW₀).apply_mem_retract hw
      rw [R.restrict_retract hW₀] at this
      exact (heq _ this).symm
  · apply Subtype.ext
    have hry : (r y : M.E 0) ∈ S.U := by rw [hr y hy]; exact S.mapsTo hy
    rw [hr _ hry, hr y hy, S.idem _ hy]
  · ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(hFG _).2 ?_, ?_⟩
      · rw [hr z hz, ← hSret]; exact S.apply_mem_retract hz
      · change (r z : M.E 0) ∈ S.U
        rw [hr z hz]; exact S.mapsTo hz
    · rintro ⟨hyF, hyV⟩
      refine ⟨y, hyV, Subtype.ext ?_⟩
      rw [hr y hyV]
      have : (y : M.E 0) ∈ S.retract := by rw [hSret]; exact (hFG y).1 hyF
      exact S.apply_eq_self_of_mem_retract this

end LocalModel

/-! ### Theorem 2.5.17 (preprint 2.45): the interior of a face -/

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

/-- **Theorem 2.5.17 (preprint 2.45)**, the interior of a face: in a tame M-polyfold, a face `F = closure(G)`, `G` a
connected component of `{d_X = 1}`, satisfies `F ∩ {d_X = 1} = G`; the text's "interior of a face"
is this set.

*Proof.* At `y ∈ F` with `d_X(y) = 1`, in a tame chart `φ` with `I(φ y) = {i}`, all points of
`{d_X = 1}` near `y` lie in `φ⁻¹(F̂)` for the single component `F̂` of Lemma 4.C, a connected
subset of `{d_X = 1}` containing `y` and meeting `G`. -/
theorem theorem_2_5_17_interior (hP : P.IsTame) (y₀ : X) :
    closure (connectedComponentIn {y | P.degIndex y = 1} y₀) ∩ {y | P.degIndex y = 1} =
      connectedComponentIn {y | P.degIndex y = 1} y₀ := by
  classical
  set G := connectedComponentIn {y | P.degIndex y = 1} y₀ with hG
  refine Subset.antisymm ?_ fun z hz => ⟨subset_closure hz, connectedComponentIn_subset _ _ hz⟩
  rintro y ⟨hyF, hy1⟩
  change P.degIndex y = 1 at hy1
  obtain ⟨φ, hφ, hyV, htame⟩ := IsTame.exists_chart P hP y
  obtain ⟨R, hRO, hRt⟩ := htame
  obtain ⟨n, W, T, hT⟩ := φ.model.isPartialQuadrant
  have hR := hRt n W T hT
  have hdeg : ∀ z ∈ φ.source, P.degIndex z = degIndexWith T (φ z) := fun z hz => by
    rw [P.degIndex_eq_chartDegIndex_of_isTameWith hφ R hRO hT hR hz, chartDegIndex,
      degIndex_eq T hT (φ.apply_mem_C hz)]
  set o := φ y with ho
  have hoO : o ∈ R.retract := by rw [hRO]; exact φ.mapsTo_model y hyV
  obtain ⟨i, hi⟩ := Finset.card_eq_one.1
    ((degIndexWith_eq_card_zeroSet T o).symm.trans ((hdeg y hyV).symm.trans hy1))
  have hoi : (T 0 o).1 i = 0 := by rw [← mem_zeroSet T, hi]; exact Finset.mem_singleton_self i
  obtain ⟨ε, hε, p, -, -, -, hBI, -, hB, -⟩ := local_face_structure hT hR hoO hoi
  -- points of `S` near `o` lie in `F̂ = cc S p`
  have hnear : ∀ z ∈ Metric.ball o ε ∩ R.retract, degIndexWith T z = 1 →
      z ∈ connectedComponentIn R.faceStratum p := by
    rintro z ⟨hzB, hzO⟩ hz1
    have hzC := R.retract_subset_C hzO
    have hzI : zeroSet T z = {i} := by
      refine Finset.eq_of_subset_of_card_le (hi ▸ hBI z ⟨hzB, hzC⟩) ?_
      rw [← degIndexWith_eq_card_zeroSet, hz1, Finset.card_singleton]
    have := hB z ⟨hzB, hzC⟩ hzI
    rwa [R.apply_eq_self_of_mem_retract hzO] at this
  have hoK : o ∈ connectedComponentIn R.faceStratum p :=
    hnear o ⟨Metric.mem_ball_self hε, hoO⟩ ((hdeg y hyV).symm.trans hy1)
  -- `K = φ⁻¹(F̂)` is preconnected in `{d_X = 1}`
  have hsub : connectedComponentIn R.faceStratum p ⊆ φ.model.O := fun z hz => by
    rw [← hRO]; exact (connectedComponentIn_subset _ _ hz).1
  have hKpre : IsPreconnected (φ.symm '' connectedComponentIn R.faceStratum p) :=
    isPreconnected_connectedComponentIn.image _ (φ.continuousOn_invFun.mono hsub)
  have hKd : φ.symm '' connectedComponentIn R.faceStratum p ⊆ {y | P.degIndex y = 1} := by
    rintro _ ⟨z, hz, rfl⟩
    have hzS := connectedComponentIn_subset _ _ hz
    change P.degIndex (φ.symm z) = 1
    rw [hdeg _ (φ.symm_mapsTo (hsub hz)), φ.apply_symm_apply (hsub hz)]
    exact faceStratum_degIndexWith hT hzS
  have hyK : y ∈ φ.symm '' connectedComponentIn R.faceStratum p :=
    ⟨o, hoK, φ.symm_apply_apply hyV⟩
  -- a point of `G` near `y`
  have hφc : ContinuousAt φ y := φ.continuousOn_toFun.continuousAt (φ.isOpen_source.mem_nhds hyV)
  obtain ⟨y', ⟨hy'V, hy'B⟩, hy'G⟩ := mem_closure_iff_nhds.1 hyF _
    ((show ∀ᶠ z in 𝓝 y, z ∈ φ.source from φ.isOpen_source.mem_nhds hyV).and
      (hφc.eventually (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε))))
  have hy'1 := connectedComponentIn_subset {y | P.degIndex y = 1} y₀ hy'G
  change P.degIndex y' = 1 at hy'1
  have hy'O : φ y' ∈ R.retract := by rw [hRO]; exact φ.mapsTo_model y' hy'V
  have hy'K : y' ∈ φ.symm '' connectedComponentIn R.faceStratum p :=
    ⟨φ y', hnear _ ⟨hy'B, hy'O⟩ ((hdeg y' hy'V).symm.trans hy'1), φ.symm_apply_apply hy'V⟩
  have hKG : φ.symm '' connectedComponentIn R.faceStratum p ⊆ G := by
    rw [hG, connectedComponentIn_eq hy'G]
    exact hKpre.subset_connectedComponentIn hy'K hKd
  exact hKG hyK

end MPolyfold

end Polyfold
