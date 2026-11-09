import Polyfold.Chapter6.SectionOrientation
import Polyfold.Chapter6.PushTransfer

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.5, p. 229:
**Theorem 6.6.18 (preprint 6.41)** *(book 2017: Theorem 6.3; see `BookConcordance.md`)*.

# The natural orientation of the solution set

## The text, paraphrased

(Theorem 6.6.18 (preprint 6.41)) Let `P : Y → X` be a strong bundle over a tame M-polyfold, `f` a proper
sc-Fredholm section such that `(f, x)` is in general position to `∂X` at every zero `x`, and `o_f`
an orientation of `f` (Definition 6.6.16 (preprint 6.40)).  Then the solution set `S = f⁻¹(0)` is a smooth compact
manifold with boundary with corners with a natural orientation.  (Proof) That `S` is a compact
manifold with boundary with corners is known from the transversality discussion.  At `x ∈ S`,
`ker f'(x) = T_xS`, and since `f'(x)` is onto, `T_xS` is oriented by `o_f(x)`.  Since `o_f` has
the local continuation property, the differential-geometric local prolongation of the orientation
of `S` is the Fredholm one.  If `f` is not generic, a small perturbation `s` supported near the
zero set gives `S_{f+s}` a natural orientation coming from `o_f`, since `det((f + s)'(x))` is
oriented from `DET(f, x)`.

## What is formalized

* **The first assertion**: `theorem_6_6_18_solutionSet`, the conclusions
  `SolutionSetInGeneralPosition` of Theorem 5.3.10 (preprint 5.18) (`S` compact, a smooth submanifold in general
  position, with the induced structure of a tame manifold with boundary with corners and
  `d_S = d_X`), from Chapters 4 and 5;
  `MPolyfold.IsGeneralPositionAt.isGoodPositionAt` (Lemma 4.2.8 (preprint 4.19): general position implies good
  position in a tame M-polyfold).
* **`T_xS = ker f'(x)`**: `tangentSpace_solutionSet_eq_linKer` (from Theorem 3.6.8 (preprint 3.54),
  `exists_tangentSpace_eq_linKer`).
* **The tangent orientation**: in a chart point `p` at a zero `x`, `ChartPoint.linZero`, the
  operator `f'(x) : T_zO → K_z`, with `linZero_mem_linSet` (`f'(x) ∈ Lin(f, x)`),
  `linZero_surjective` and `map_ker_linZero` (its kernel is `ker Lin(z) ⊆ E₀`);
  `ChartPoint.tangentOr`: `Or_x^f ≃` the orientations of `λ(ker f'(x))`, `o ↦ o(f'(x))` followed
  by `det f'(x) = λ(ker f'(x)) ⊗ λ(coker f'(x))* ≅ λ(ker f'(x))` (`detEquivOfSurjective`);
  `tangentOrAt`, the same in the chart point `chartPtOf c hc`.
* **Naturality**: `exists_tangentFamily`, `tangentFamily`, `tangentFamily_L` (Lemma 6.6.5 (preprint 6.30): along an
  sc-smooth path of zeros the kernels `ker f'(γ_q)` form a `SubspaceFamily`); `cont_tangentOr`
  (for a continuous orientation, continuation in `λ(Λ)` carries the tangent orientation at `δ(0)`
  to the one at `δ(1)`); `isLineOrientation_tangentOr` (along a path of zeros in `V` the tangent
  orientations form an orientation of the line bundle `λ(Λ)`);
  `isLineOrientation_tangentOr_of_isSectionOrientation`; **Theorem 6.6.18 (preprint 6.41)**: `theorem_6_6_18_hyp`.
* Tools: the stabilization by `ℝ⁰` of an onto operator (`stabJ_surjective_zero`,
  `stabSign_of_surjective`, `stabIota_trans_zero`, `stabRayEquiv_zero`), `kerEquivOfMap`,
  `surjRay`, `stabRayEquiv_eq_surjRay`, `ChartPoint.stabRayEquiv_eq_tangentOr`;
  `SubspaceFamily.congrL`, `SubspaceFamily.cont_map` (`PushTransfer.lean`; here for `v ↦ (v, 0)`),
  `ray_map_maxPowEquiv_ofEq_self`, `pullbackSlice_fiberZero`, `iccZero`, `iccOne`;
  `IsStabKernels.orRay_eq_tangentOr` (for `k = 0`, the orientation read in `λ(Λ')` at a zero
  where the stabilized operator is `f'(x)` is the tangent orientation), `isStabKernels_zero` (the
  push-forward datum `S = 0`, `k = 0` along a path of zeros), `orRay_zero`, and
  `equiv_trans_trans_symm_apply`.

## Reading

`T_xS = ker f'(x)` is read in a chart `c` as `ker Lin(z) ⊆ E₀` at the level-`1` point `z` over
`φ(x)` (`StrongBundleChart.linKer`); that it is the tangent space of the retract `φ(G ∩ S)` is
`tangentSpace_solutionSet_eq_linKer`.  "`T_xS` is oriented by `o_f(x)`" is read as `tangentOr`:
`f'(x)` (the linearization of `f + s` with `s = 0`, `a = 0`) lies in `Lin(f, x)`, `o_f(x)` gives a
ray of `det f'(x)`, and as `f'(x)` is onto, `det f'(x) ≅ λ(ker f'(x))`.

"The local prolongation of the orientation of `S` is the Fredholm one" is read as: along every
sc-smooth path `γ` of zeros in an orientable neighbourhood `V ⊆ U` (Definition 6.6.12 (preprint 6.36)), in its chart
`c`, the kernels `ker f'(γ_q)` form a continuous family of subspaces `Λ` (Lemma 6.6.5 (preprint 6.30)), and the
tangent orientations form an orientation of its line bundle `λ(Λ)` (`IsLineOrientation`): the
continuous prolongation in `λ(Λ)` of the tangent orientation at `γ(0)` is the tangent orientation
at every `γ(t)`.  The Fredholm side is the push-forward of pp. 222–224 for the datum `S = 0`,
`k = 0`: along a path of zeros with `f'` onto the constant zero section is admissible, the
kernels are `(v, 0)`, `v ∈ ker f'(γ_q)`, and the push-forward is continuation in `λ(Λ)` between
the tangent orientations; a continuous orientation is invariant under it (Definition 6.6.12 (preprint 6.36)).  For an
intermediate point `γ(t)` we use the path `s ↦ γ(t · κ(s))`, `κ = Real.smoothTransition`, which is
sc-smooth and stays in `γ([0, t])` for all `s ∈ ℝ` (the push-forward datum asks for zeros near
`[0, 1]`).  The hypothesis `IsContinuousOrientation` of `isLineOrientation_tangentOr` is
satisfiable: over an orientable neighbourhood there are two continuous orientations
(`exists_two_isContinuousOrientation`); the hypothesis `IsSectionOrientation` of `theorem_6_6_18_hyp`
(Definition 6.6.16 (preprint 6.40)) is satisfiable exactly when `f` is orientable (`exists_isSectionOrientation_iff`,
`OrientationFunctor.lean`).

"Proper" is `StrongBundle.IsProper`; only the compactness of `S` is used.  "In general position to
`∂X`" is `IsGeneralPositionGerm` (Definition 5.3.9 (preprint 5.17)); it gives `f'(x)` onto and the good position of
the germ.  The section has tame germ data (`IsScFredholmSectionTame`), the standing hypothesis of
Chapter 5.  "Natural orientation" is formalized as the tangent orientations `tangentOr` together
with their continuity along paths of zeros in orientable neighbourhoods; the orientation of `S` as
an abstract manifold (of its tangent bundle in the charts of `subPolyfold`), the compatibility of
the tangent orientations read in two charts at the same point, and the last paragraph of the proof
(the perturbation `s` when `f` is not generic, and the orientation of `S_{f+s}` from `o_f`) are not
formalized.
-/

open Module TensorProduct Bundle Topology Set

noncomputable section

namespace Polyfold

universe u v

section ZeroStab

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {T : E →L[ℝ] F} {φ : (Fin 0 → ℝ) →L[ℝ] F}

/-- For `n = 0`, `j : ker T → ker(T ⊕ φ)` is onto. -/
theorem stabJ_surjective_zero : Function.Surjective (stabJ T φ) := by
  intro x
  have hx : x ∈ LinearMap.ker (stabPi T φ) := by
    rw [LinearMap.mem_ker]
    exact Subsingleton.elim _ _
  rw [← range_stabJ] at hx
  exact hx

/-- The sign `α(T)` of a surjective operator is `1`. -/
theorem stabSign_of_surjective (hT : Function.Surjective T) : stabSign T = 1 := by
  rw [stabSign, finrank_coker_of_surjective hT, pow_zero]

/-- **The stabilization by `ℝ⁰` of a surjective operator is `det(T) ≅ λ(ker T)`** at the level of
linear isomorphisms: for `T` onto, `φ : ℝ⁰ → F` and identifications `ι : ker(T ⊕ φ) ≅ L`,
`ι' : ker T ≅ L` with `ι ∘ j = ι'`, `λ(ι) ∘ (det(T ⊕ φ) ≅ λ(ker(T ⊕ φ))) ∘ ι_φ` is
`λ(ι') ∘ (det(T) ≅ λ(ker T))`. -/
theorem stabIota_trans_zero (hT : T.IsFredholm) (hTs : Function.Surjective T)
    (hφ : Function.Surjective (T.coprod φ)) {W : Type*} [AddCommGroup W] [Module ℝ W]
    {L : Submodule ℝ W} [FiniteDimensional ℝ L]
    (ι : LinearMap.ker ((T.coprod φ : E × (Fin 0 → ℝ) →L[ℝ] F) : E × (Fin 0 → ℝ) →ₗ[ℝ] F)
      ≃ₗ[ℝ] L) (ι' : LinearMap.ker (T : E →ₗ[ℝ] F) ≃ₗ[ℝ] L)
    (h : ∀ v, ι (stabJ T φ v) = ι' v) :
    (LinearEquiv.ofBijective (stabIota hT hφ) (stabIota_bijective hT hφ)).trans
      ((detEquivOfSurjective hφ).trans (maxPowEquiv ι)) =
      (detEquivOfSurjective hTs).trans (maxPowEquiv ι') := by
  have := hT.finite_ker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := hT.finite_coker
  have := finiteDimensional_ker_coprod (T := T) (φ := φ)
  have := finiteDimensional_coker_coprod hφ
  have a : Basis (Fin (finrank ℝ (LinearMap.ker (T : E →ₗ[ℝ] F)))) ℝ
    (LinearMap.ker (T : E →ₗ[ℝ] F)) := Module.finBasis ℝ _
  have hm : 0 = finrank ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) :=
    (finrank_coker_of_surjective hTs).symm
  have cbar : Fin 0 → Fin 0 → ℝ := Fin.elim0
  have bbar : Fin 0 → LinearMap.ker ((T.coprod φ : E × (Fin 0 → ℝ) →L[ℝ] F) :
    E × (Fin 0 → ℝ) →ₗ[ℝ] F) := Fin.elim0
  have hd : LinearIndependent ℝ (stabClass T φ ∘ cbar) := linearIndependent_empty_type
  have hJ : LinearMap.ker (stabJ T φ) = ⊥ := LinearMap.ker_eq_bot.2 stabJ_injective
  have happ : Fin.append (stabJ T φ ∘ a) bbar = (stabJ T φ ∘ a) ∘ Fin.cast (add_zero _) :=
    Fin.append_right_nil _ _ rfl
  have hb : LinearIndependent ℝ (Fin.append (stabJ T φ ∘ a) bbar) := by
    rw [happ]
    exact (a.linearIndependent.map' _ hJ).comp _ (Fin.cast_injective _)
  have hkl : finrank ℝ (LinearMap.ker (T : E →ₗ[ℝ] F)) + 0 =
      finrank ℝ (LinearMap.ker ((T.coprod φ : E × (Fin 0 → ℝ) →L[ℝ] F) :
        E × (Fin 0 → ℝ) →ₗ[ℝ] F)) :=
    (LinearEquiv.ofBijective (stabJ T φ) ⟨stabJ_injective, stabJ_surjective_zero⟩).finrank_eq
  have h615 := proposition_6_4_15 hT hφ a cbar hd hm bbar hb hkl rfl
  have hone : stabOne hφ (emptyWedge _ (finrank_coker_of_surjective hφ)) = 1 :=
    dualVec_self finrank_maxPow (emptyWedge_ne_zero _ (finrank_coker_of_surjective hφ))
  have hcb : stabClass T φ ∘ cbar = Fin.elim0 := funext fun i => i.elim0
  have hone' : dualVec (wedge (stabClass T φ ∘ cbar) hm)
      (emptyWedge _ (finrank_coker_of_surjective hTs)) = 1 := by
    rw [emptyWedge]
    simp only [hcb]
    exact dualVec_self finrank_maxPow (emptyWedge_ne_zero _ (finrank_coker_of_surjective hTs))
  have ha : finrank ℝ (LinearMap.ker (T : E →ₗ[ℝ] F)) =
      finrank ℝ (LinearMap.ker (T : E →ₗ[ℝ] F)) := rfl
  have hx₀R : detEquivOfSurjective hTs (wedge a ha ⊗ₜ dualVec (wedge (stabClass T φ ∘ cbar) hm))
      = wedge a ha := by
    rw [detEquivOfSurjective_tmul, hone', one_smul]
  have hx₀ : wedge a ha ⊗ₜ dualVec (wedge (stabClass T φ ∘ cbar) hm) ≠ (0 : fredholmDet T) := by
    intro h0
    have h1 := hx₀R
    rw [h0, LinearEquiv.map_zero] at h1
    exact wedge_basis_ne_zero' a _ h1.symm
  have hdet' : (Pi.basisFun ℝ (Fin 0)).det
      (Fin.append cbar (fun i => ((bbar i : E × (Fin 0 → ℝ)).2)) ∘ Fin.cast rfl) = 1 := by
    rw [Basis.det_apply]
    exact Matrix.det_isEmpty
  have h615' : stabIota hT hφ (wedge a ha ⊗ₜ dualVec (wedge (stabClass T φ ∘ cbar) hm)) =
      wedge (Fin.append (stabJ T φ ∘ a) bbar) hkl ⊗ₜ stabOne hφ := by
    rw [h615, hdet', inv_one, one_smul]
  have e1 : detEquivOfSurjective hφ
      (stabIota hT hφ (wedge a ha ⊗ₜ dualVec (wedge (stabClass T φ ∘ cbar) hm))) =
      wedge (Fin.append (stabJ T φ ∘ a) bbar) hkl := by
    rw [h615', detEquivOfSurjective_tmul, hone, one_smul]
  apply LinearEquiv.toLinearMap_injective
  refine linearMap_ext_of_ne_zero (finrank_fredholmDet hT) hx₀ ?_
  change maxPowEquiv ι (detEquivOfSurjective hφ (stabIota hT hφ
      (wedge a ha ⊗ₜ dualVec (wedge (stabClass T φ ∘ cbar) hm)))) =
    maxPowEquiv ι' (detEquivOfSurjective hTs
      (wedge a ha ⊗ₜ dualVec (wedge (stabClass T φ ∘ cbar) hm)))
  rw [e1, hx₀R, maxPowEquiv_wedge, maxPowEquiv_wedge]
  have hfun : ⇑ι ∘ Fin.append (⇑(stabJ T φ) ∘ ⇑a) bbar =
      (⇑ι' ∘ ⇑a) ∘ Fin.cast (add_zero _) := by
    rw [happ]
    exact funext fun i => h _
  exact (congrArg (fun v => wedge v (hkl.trans ι.finrank_eq)) hfun).trans
    (wedge_cast (⇑ι' ∘ ⇑a) (ha.trans ι'.finrank_eq) (add_zero _))

/-- **The stabilization by `ℝ⁰` of a surjective operator is `det(T) ≅ λ(ker T)`**: for `T` onto,
`φ : ℝ⁰ → F` and identifications `ι : ker(T ⊕ φ) ≅ L`, `ι' : ker T ≅ L` with `ι ∘ j = ι'`, the
sign-normalized `Φ_E` of `stabRayEquiv` (here `α(T) = 1`) is `λ(ι') ∘ (det(T) ≅ λ(ker T))` on
rays. -/
theorem stabRayEquiv_zero (hT : T.IsFredholm) (hTs : Function.Surjective T)
    (hφ : Function.Surjective (T.coprod φ)) {W : Type*} [AddCommGroup W] [Module ℝ W]
    {L : Submodule ℝ W} [FiniteDimensional ℝ L]
    (ι : LinearMap.ker ((T.coprod φ : E × (Fin 0 → ℝ) →L[ℝ] F) : E × (Fin 0 → ℝ) →ₗ[ℝ] F)
      ≃ₗ[ℝ] L) (ι' : LinearMap.ker (T : E →ₗ[ℝ] F) ≃ₗ[ℝ] L)
    (h : ∀ v, ι (stabJ T φ v) = ι' v) (r : Module.Ray ℝ (fredholmDet T)) :
    stabRayEquiv hT hφ ι (stabSign T • r) =
      Module.Ray.map (maxPowEquiv ι') (Module.Ray.map (detEquivOfSurjective hTs) r) := by
  have hs : stabSign T • r = r := by
    rw [stabSign_of_surjective hTs, one_smul]
  rw [hs, ray_map_map, ← stabIota_trans_zero hT hTs hφ ι ι' h, ← ray_map_map, ← ray_map_map]
  rfl

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **`ker T ≅ N`** for a subspace `N = j(ker T)` of `V`, `j : E → V` injective. -/
def kerEquivOfMap (T : E →L[ℝ] F) (j : E →L[ℝ] V) (hj : Function.Injective j)
    {N : Submodule ℝ V} (hN : (LinearMap.ker (T : E →ₗ[ℝ] F)).map (j : E →ₗ[ℝ] V) = N) :
    LinearMap.ker (T : E →ₗ[ℝ] F) ≃ₗ[ℝ] N :=
  (Submodule.equivMapOfInjective (j : E →ₗ[ℝ] V) hj _).trans (LinearEquiv.ofEq _ _ hN)

/-- `kerEquivOfMap` is `v ↦ j v`. -/
theorem coe_kerEquivOfMap (T : E →L[ℝ] F) (j : E →L[ℝ] V) (hj : Function.Injective j)
    {N : Submodule ℝ V} (hN : (LinearMap.ker (T : E →ₗ[ℝ] F)).map (j : E →ₗ[ℝ] V) = N)
    (v : LinearMap.ker (T : E →ₗ[ℝ] F)) : (kerEquivOfMap T j hj hN v : V) = j v :=
  rfl

/-- **The rays of `det(T)` and of `λ(N)`** for a surjective `T` and `N = j(ker T)`:
`det(T) ≅ λ(ker T)` (`detEquivOfSurjective`, the cokernel being `{0}`), then `λ(ker T ≅ N)`. -/
def surjRay {T : E →L[ℝ] F} (hTs : Function.Surjective T) (j : E →L[ℝ] V)
    (hj : Function.Injective j) {N : Submodule ℝ V}
    (hN : (LinearMap.ker (T : E →ₗ[ℝ] F)).map (j : E →ₗ[ℝ] V) = N) :
    Module.Ray ℝ (fredholmDet T) ≃ Module.Ray ℝ (maxPow N) :=
  (Module.Ray.map (detEquivOfSurjective hTs)).trans
    (Module.Ray.map (maxPowEquiv (kerEquivOfMap T j hj hN)))

/-- **`Φ_E` of a stabilization by `ℝ⁰` is `surjRay`**: for `T` onto, `L = (j × 1)(ker(T ⊕ φ))`,
`N = j(ker T)` and `e : N ≅ L`, `v ↦ (v, 0)`, the ray `Φ_E(α(T) r)` of `λ(L)` is `λ(e)` of
`surjRay r` (`stabRayEquiv_zero`). -/
theorem stabRayEquiv_eq_surjRay (hT : T.IsFredholm) (hTs : Function.Surjective T)
    (hφ : Function.Surjective (T.coprod φ)) (j : E →L[ℝ] V) (hj : Function.Injective j)
    {L : Submodule ℝ (V × (Fin 0 → ℝ))} [FiniteDimensional ℝ L]
    (hL : L = (LinearMap.ker ((T.coprod φ : E × (Fin 0 → ℝ) →L[ℝ] F) :
      E × (Fin 0 → ℝ) →ₗ[ℝ] F)).map ((j.prodMap (ContinuousLinearMap.id ℝ (Fin 0 → ℝ)) :
        E × (Fin 0 → ℝ) →L[ℝ] V × (Fin 0 → ℝ)) : E × (Fin 0 → ℝ) →ₗ[ℝ] V × (Fin 0 → ℝ)))
    {N : Submodule ℝ V} (hN : (LinearMap.ker (T : E →ₗ[ℝ] F)).map (j : E →ₗ[ℝ] V) = N)
    (e : N ≃ₗ[ℝ] L) (he : ∀ v, (e v : V × (Fin 0 → ℝ)) = ((v : V), 0))
    (r : Module.Ray ℝ (fredholmDet T)) :
    stabRayEquiv hT hφ (kerEquivMap j hj hL) (stabSign T • r) =
      Module.Ray.map (maxPowEquiv e) (surjRay hTs j hj hN r) := by
  rw [stabRayEquiv_zero hT hTs hφ (kerEquivMap j hj hL) ((kerEquivOfMap T j hj hN).trans e)
    (fun v => ?_)]
  · rw [surjRay, Equiv.trans_apply, ray_map_map (maxPowEquiv _) (maxPowEquiv e),
      ← maxPowEquiv_trans]
  · apply Subtype.ext
    rw [coe_kerEquivMap, LinearEquiv.trans_apply, he, coe_kerEquivOfMap, coe_stabJ]

end ZeroStab

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

/-- **General position implies good position** (Definitions 4.2.10 and 4.2.5 (preprint 4.21 and 4.16)) for a smooth
finite-dimensional submanifold of a tame M-polyfold: in a tame chart centred at `a`, an
sc-complement of `T_aA` inside `T_a^R X` is a good complement (Lemma 4.2.8 (preprint 4.19) through
`IsGeneralPositionRetractAt.isGoodPositionRetractAt`). -/
theorem IsGeneralPositionAt.isGoodPositionAt (hX : PX.IsTame) {A : Set X}
    (hA : PX.IsSmoothSubmanifold A) {a : X} (h : PX.IsGeneralPositionAt A a) :
    PX.IsGoodPositionAt A a := by
  have haA : a ∈ A := h.1
  obtain ⟨ψ, hψ, haψ, hψ0, htame⟩ := hX.exists_centredChart (hA.subset_smoothSet haA)
  obtain ⟨R, hR, hRt⟩ := htame
  obtain ⟨n, Wq, T, hT⟩ := ψ.model.isPartialQuadrant
  have hz : ψ.model.E.toBase 1 0 = ψ a := by rw [map_zero, hψ0]
  have hgp := h.isGeneralPositionChart (hA.data haA) hψ T hT (hA.mem_data_V haA) haψ hz
  have h01 : (0 : ψ.model.E 1) ∈ ψ.model.E.lvlSet R.retract 1 := by
    rw [ScBanach.mem_lvlSet, hR, hz]; exact ψ.mapsTo_model a haψ
  have hs0 : (0 : ψ.model.E 1) ∈ ψ.model.E.smoothLvl 1 := by
    change ψ.model.E.toBase 1 0 ∈ (ψ.model.E.smooth : Set (ψ.model.E 0))
    rw [map_zero]; exact ψ.model.E.smooth.zero_mem
  refine ⟨haA, hA.data haA, ψ, n, Wq, T, 0, hA.mem_data_V haA, hψ, haψ, hT, hz, ?_⟩
  unfold SubmanifoldData.IsGeneralPositionChart at hgp
  unfold SubmanifoldData.IsGoodPositionChart
  rw [← hR] at hgp ⊢
  exact hgp.isGoodPositionRetractAt T (hRt n Wq T hT) h01 hs0

end MPolyfold

section Solution

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- **Theorem 6.6.18 (preprint 6.41), first assertion** ("we already know from the transversality discussion"): for
a proper sc-Fredholm section `f` with tame germ data over a tame M-polyfold, in general position
(Definition 5.3.9 (preprint 5.17)) at every zero, the solution set `S = f⁻¹(0)` is compact, a smooth
finite-dimensional submanifold (Definition 4.2.1 (preprint 4.13)) in general position (Definition 4.2.10 (preprint 4.21)) whose
induced structure is that of a tame manifold with boundary with corners (Definition 4.1.1 (preprint 4.1))
(`SolutionSetInGeneralPosition`).  *Proof*: Definition 4.2.1 (preprint 4.13) (`isSmoothSubmanifold_solutionSet_inter`)
for the submanifold, `exists_isOpen_isGeneralPositionGerm` for the general position of `S`,
Lemma 4.2.8 (preprint 4.19) for good position (`IsGeneralPositionAt.isGoodPositionAt`), Theorems 4.2.7 and 4.2.11 (preprint 4.18 and 4.22) for
the corner structure, tameness and the degeneracy index. -/
theorem theorem_6_6_18_solutionSet (hX : PX.IsTame) (hf : B.IsScFredholmSectionTame f)
    (hP : B.IsProper f) (hgp : ∀ x, IsZeroAt P f x → B.IsGeneralPositionGerm f x) :
    B.SolutionSetInGeneralPosition f := by
  have hS : IsCompact (solutionSet P f) := hP.1
  have htr : B.IsTransversal f := fun x hx => (hgp x hx).isLinSurjAt
  have hSm : PX.IsSmoothSubmanifold (solutionSet P f) := by
    have := StrongBundle.isSmoothSubmanifold_solutionSet_inter hf.isScSmooth.1 isOpen_univ
      fun y _ hy0 => (hgp y hy0).isGoodPositionGermTame hf hy0
    rwa [inter_univ] at this
  have hgpS : ∀ y ∈ solutionSet P f, PX.IsGeneralPositionAt (solutionSet P f) y := by
    intro y hy
    obtain ⟨W, hWo, hyW, hWA, hW⟩ := exists_isOpen_isGeneralPositionGerm hX hf hy (hgp y hy)
    refine MPolyfold.IsGeneralPositionAt.congr_nhds hWA hSm hWo hyW ?_ (hW y hyW hy).2.2
    ext w
    simp only [mem_inter_iff]
    tauto
  have hgoodS : ∀ y ∈ solutionSet P f, PX.IsGoodPositionAt (solutionSet P f) y := fun y hy =>
    (hgpS y hy).isGoodPositionAt hX hSm
  have := PX.paracompactSpace_subtype (solutionSet P f)
  obtain ⟨hcs, htameS⟩ := MPolyfold.theorem_4_2_7 hX hSm hgoodS
  refine ⟨htr, hgp, hS, hSm, hgpS, hcs, htameS, fun a => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, Ua, -, haU, -, -, -, hdeg, -, -⟩ :=
    MPolyfold.theorem_4_2_11_preprint hX hSm (hgpS a a.2)
  exact hdeg a haU

/-- **`T_yS = ker f'(y)`** (the proof of Theorem 6.6.18 (preprint 6.41), from Theorem 3.6.8 (preprint 3.54)): at a zero `y` with
`(f, y)` in general position there is an open `W ∋ y` such that, in every chart `c` at `y` and for
every open `G ⊆ W ∩ dom φ` containing `y` with `φ(G ∩ S)` a retract (`S = f⁻¹(0)`), the tangent
space of `φ(G ∩ S)` at the level-`1` point `z` over `φ(y)` is the kernel of `Lin(z) = f'(y)`
(`exists_tangentSpace_eq_linKer`). -/
theorem tangentSpace_solutionSet_eq_linKer (hft : B.IsScFredholmSectionTame f) {y : X}
    (hgp : B.IsGeneralPositionGerm f y) (hy0 : IsZeroAt P f y) :
    ∃ W : Set X, IsOpen W ∧ y ∈ W ∧ ∀ c : StrongBundleChart PX P, B.IsChart c →
      y ∈ c.φ.source → ∀ G : Set X, IsOpen G → G ⊆ c.φ.source → G ⊆ W → y ∈ G →
        IsScRetract c.φ.model.E c.φ.model.C (c.φ '' (G ∩ solutionSet P f)) →
        ∀ z : c.φ.model.E 1, c.φ.model.E.toBase 1 z = c.φ y →
          tangentSpace c.φ.model.E c.φ.model.C (c.φ '' (G ∩ solutionSet P f)) z =
            c.linKer f z := by
  obtain ⟨V, hVo, hyV, -, hV⟩ :=
    exists_tangentSpace_eq_linKer hft (hgp.isGoodPositionGermTame hft hy0) hy0
  refine ⟨V, hVo, hyV, fun c hc hyc G hG hGc hGV hyG hQ z hz => ?_⟩
  have hGS : G ∩ (solutionSet P f ∩ V) = G ∩ solutionSet P f := by
    ext w
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hGV h.1⟩⟩
  rw [← hGS] at hQ ⊢
  exact hV y hyV hy0 c hc hyc G hG hGc hyG hQ z hz

end Solution

section Tangent

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

namespace ChartPoint

variable {x : X} (p : ChartPoint B x)

/-- **`f'(x) : T_zO → K_z`** at a zero `x` of `f`, read in the chart point `p`:
`Lin(z) = D(f̂ ∘ r)(z)|_{T_zO}`, with values in `K_z` (`scDeriv_mem_K`). -/
def linZero (hf : B.IsScFredholmSection f) (hx : IsZeroAt P f x) : ↥p.T →L[ℝ] ↥p.K :=
  (linAt p.c.U p.c.R (p.c.principal f) p.z).codRestrict p.K
    fun v => p.scDeriv_mem_K hf.isScSmooth hx v

/-- `linZero` is `Lin(z)` on `T_zO`. -/
theorem coe_linZero (hf : B.IsScFredholmSection f) (hx : IsZeroAt P f x) (v : ↥p.T) :
    (p.linZero hf hx v : p.c.F 0) = linAt p.c.U p.c.R (p.c.principal f) p.z v :=
  rfl

/-- `f'(x) ∈ Lin(f, x)` at a zero (with the sc⁺-section `s = 0` of Definition 6.2.1 (preprint 6.1)). -/
theorem linZero_mem_linSet (hf : B.IsScFredholmSection f) (hx : IsZeroAt P f x) :
    p.linZero hf hx ∈ p.linSet f := by
  have h0 := sectionAdd_fiberZero hf.isScSmooth.1
  refine ⟨fiberZero P, StrongBundle.isScPlusSection_fiberZero, by rw [h0]; exact hx, 0,
    p.isScPlusOp_zero (hf.mem_smoothSet_of_isZeroAt hx), fun v => ?_⟩
  rw [h0, coe_linZero, zero_apply, Submodule.coe_zero, add_zero]

/-- **`f'(x)` is onto** when `f'(x)` is onto in some chart (`IsLinSurjAt`, chart independence
`IsLinSurjAt.linAt_surjective`). -/
theorem linZero_surjective (hf : B.IsScFredholmSection f) (hx : IsZeroAt P f x)
    (hL : B.IsLinSurjAt f x) : Function.Surjective (p.linZero hf hx) := by
  rintro ⟨k, hk⟩
  have hkK : (p.c.φ x, k) ∈ p.c.K := by
    have := (mem_rangeS_ρCLM_iff p.c.isRetraction p.mem_O p.mem_U).1 hk
    rwa [p.toBase_z] at this
  obtain ⟨v, hv⟩ := hL.linAt_surjective hf.isScSmooth hx p.isChart p.mem_source p.toBase_z k hkK
  exact ⟨v, Subtype.ext hv⟩

/-- **`ker f'(x)` as a subspace of `E₀`**: the image of `ker linZero` in `E₀` is `c.linKer f z`
(the kernel of `Lin(z)`, Theorem 3.6.8 (preprint 3.54) (4): `T_xS = ker f'(x)`). -/
theorem map_ker_linZero (hf : B.IsScFredholmSection f) (hx : IsZeroAt P f x) :
    (LinearMap.ker ((p.linZero hf hx : ↥p.T →L[ℝ] ↥p.K) : ↥p.T →ₗ[ℝ] ↥p.K)).map
      (p.T.subtypeL : ↥p.T →ₗ[ℝ] p.c.φ.model.E 0) = p.c.linKer f p.z := by
  have hker : LinearMap.ker ((p.linZero hf hx : ↥p.T →L[ℝ] ↥p.K) : ↥p.T →ₗ[ℝ] ↥p.K) =
      LinearMap.ker (linAt p.c.U p.c.R (p.c.principal f) p.z :
        ↥(rangeS (scDeriv p.c.U (StrongRetr.r p.c.R) p.z)) →ₗ[ℝ] p.c.F 0) := by
    ext v
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    rw [← Subtype.coe_inj]
    rfl
  rw [hker]
  rfl

/-- **The tangent orientation** (Theorem 6.6.18 (preprint 6.41)): for a zero `x` with `f'(x)` onto, the orientation
`o` of `DET(f, x)` gives the ray `o(f'(x)) ∈ Ray(det f'(x))`, read in `λ(ker f'(x))`
(`det f'(x) = λ(ker f'(x)) ⊗ λ*({0}) ≅ λ(ker f'(x))`, `surjRay`) with `ker f'(x) ⊆ E₀` the kernel
`c.linKer f z` of `Lin(z)`: an orientation of `T_xS = ker f'(x)`. -/
def tangentOr (hf : B.IsScFredholmSection f) (hx : IsZeroAt P f x) (hL : B.IsLinSurjAt f x) :
    p.Or f hf ≃ Module.Ray ℝ (maxPow (p.c.linKer f p.z)) :=
  (p.orEquivRay hf (p.linZero_mem_linSet hf hx)).trans
    (surjRay (p.linZero_surjective hf hx hL) p.T.subtypeL Subtype.val_injective
      (p.map_ker_linZero hf hx))

end ChartPoint

end Tangent

/-! ### Part (3): families of subspaces -/

namespace SubspaceFamily

variable {Q : Type*} [TopologicalSpace Q] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The family `Λ` with its members rewritten to `L'`, for `Λ_q = L'_q` (the other data unchanged):
`(Λ.congrL L' h).L` is `L'` by definition. -/
def congrL (Λ : SubspaceFamily Q W) (L' : Q → Submodule ℝ W) (h : ∀ q, Λ.L q = L' q) :
    SubspaceFamily Q W where
  L := L'
  n := Λ.n
  finiteDimensional q := by
    rw [← h q]
    exact Λ.finiteDimensional q
  finrank_eq q := by
    rw [← h q]
    exact Λ.finrank_eq q
  exists_frame q₀ := by
    obtain ⟨U, hU, hq₀, e, he, h'⟩ := Λ.exists_frame q₀
    exact ⟨U, hU, hq₀, e, he, fun q hq => ⟨fun i => h q ▸ (h' q hq).1 i, (h' q hq).2⟩⟩

end SubspaceFamily

/-- `λ` of the identity of a subspace, written as `LinearEquiv.ofEq`, fixes every ray. -/
theorem ray_map_maxPowEquiv_ofEq_self {M : Type*} [AddCommGroup M] [Module ℝ M]
    (L : Submodule ℝ M) (h : L = L) (r : Module.Ray ℝ (maxPow L)) :
    Module.Ray.map (maxPowEquiv (LinearEquiv.ofEq L L h)) r = r := by
  have h1 : LinearEquiv.ofEq L L h = LinearEquiv.refl ℝ L := LinearEquiv.ext fun _ => rfl
  rw [h1, maxPowEquiv_refl, Module.Ray.map_refl]
  rfl

section PullbackZero

variable {X : Type u} {Y : Type v} {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})]

/-- The slices of the zero section of the pulled-back bundle are the zero section. -/
theorem pullbackSlice_fiberZero {n : ℕ} (t : Fin n → ℝ) :
    pullbackSlice (fiberZero (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))) t =
      fiberZero P :=
  rfl

end PullbackZero

/-- The end point `0` of `[0, 1] ⊆ ℝ¹`. -/
abbrev iccZero : Icc (0 : Fin 1 → ℝ) 1 := ⟨pt1 0, pt1_mem_Icc (left_mem_Icc.2 zero_le_one)⟩

/-- The end point `1` of `[0, 1] ⊆ ℝ¹`. -/
abbrev iccOne : Icc (0 : Fin 1 → ℝ) 1 := ⟨pt1 1, pt1_mem_Icc (right_mem_Icc.2 zero_le_one)⟩

section Tangent3

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

namespace ChartPoint

variable {x : X} (p : ChartPoint B x)

/-- **Through a stabilization by `ℝ⁰` the orientation is read as the tangent orientation**: for
`T = f'(x)` (any operator equal to `linZero`), `φ : ℝ⁰ → K_z`, `L = {(v, 0) | v ∈ ker T}` and
`e : ker f'(x) ≅ L`, `v ↦ (v, 0)`, the ray `Φ_E(α(T) o(T))` of `λ(L)` (`stabRayEquiv`) is
`λ(e)` of the tangent orientation. -/
theorem stabRayEquiv_eq_tangentOr (hf : B.IsScFredholmSection f) (hx : IsZeroAt P f x)
    (hL : B.IsLinSurjAt f x) {T : ↥p.T →L[ℝ] ↥p.K} (hT : T = p.linZero hf hx)
    (hTm : T ∈ p.linSet f) {φ : (Fin 0 → ℝ) →L[ℝ] ↥p.K} (hφ : Function.Surjective (T.coprod φ))
    {L : Submodule ℝ (p.c.φ.model.E 0 × (Fin 0 → ℝ))} [FiniteDimensional ℝ L]
    (hLeq : L = (LinearMap.ker ((T.coprod φ : _ →L[ℝ] ↥p.K) :
        ↥p.T × (Fin 0 → ℝ) →ₗ[ℝ] ↥p.K)).map
      (((p.T.subtypeL.prodMap (ContinuousLinearMap.id ℝ (Fin 0 → ℝ))) :
        ↥p.T × (Fin 0 → ℝ) →L[ℝ] p.c.φ.model.E 0 × (Fin 0 → ℝ)) :
          ↥p.T × (Fin 0 → ℝ) →ₗ[ℝ] p.c.φ.model.E 0 × (Fin 0 → ℝ)))
    (e : p.c.linKer f p.z ≃ₗ[ℝ] L)
    (he : ∀ v, (e v : p.c.φ.model.E 0 × (Fin 0 → ℝ)) = ((v : p.c.φ.model.E 0), 0))
    (o : p.Or f hf) :
    stabRayEquiv (p.isFredholm_of_mem_linSet hf _ hTm) hφ
        (kerEquivMap p.T.subtypeL Subtype.val_injective hLeq)
        (stabSign T • p.orEquivRay hf hTm o) =
      Module.Ray.map (maxPowEquiv e) (p.tangentOr hf hx hL o) := by
  subst hT
  exact stabRayEquiv_eq_surjRay _ (p.linZero_surjective hf hx hL) hφ p.T.subtypeL
    Subtype.val_injective hLeq (p.map_ker_linZero hf hx) e he (p.orEquivRay hf hTm o)

end ChartPoint

/-! ### Orientations read along stabilized kernels with `k = 0` -/

/-- Unfolding `e = A ⬝ (C ⬝ D⁻¹)`: `e(x) = y` gives `C(A(x)) = D(y)`. -/
theorem equiv_trans_trans_symm_apply {α β γ δ : Sort*} {A : α ≃ β} {C : β ≃ γ} {D : δ ≃ γ}
    {x : α} {y : δ} (h : (A.trans (C.trans D.symm)) x = y) : C (A x) = D y := by
  rw [← h, Equiv.trans_apply, Equiv.trans_apply, Equiv.apply_symm_apply]

/-- **The orientation read in `λ(Λ')` is the tangent orientation when `k = 0`**: for stabilized
kernels with no sections `sᵢ` at a zero `x = y_q` of `f` with `f'(x)` onto, if `(f + S_q)'(x)` is
`f'(x)` then `orRay_q` is `λ(e)` of `tangentOr`, for `e : ker f'(x) ≅ Λ'_q`, `v ↦ (v, 0)`. -/
theorem IsStabKernels.orRay_eq_tangentOr {Q : Type*} [TopologicalSpace Q]
    [SimplyConnectedSpace Q] [LocallyPathConnectedSpace Q]
    (hf : B.IsScFredholmSection f) {c : StrongBundleChart PX P} {hc : B.IsChart c} {y : Q → X}
    {hy : ∀ q, y q ∈ c.φ.source} {S : Q → X → Y} {s : Fin 0 → Q → X → Y}
    {Λ' : SubspaceFamily Q (c.φ.model.E 0 × (Fin 0 → ℝ))}
    (hΛS : IsStabKernels f c hc y hy S s Λ') (q : Q) {x : X} (hq : y q = x)
    (hx : x ∈ PX.smoothSet) (z₀ : c.φ.model.E 1) (hz₀ : c.φ.model.E.toBase 1 z₀ = c.φ x)
    (h0 : IsZeroAt P f x) (hL : B.IsLinSurjAt f x)
    (hTe : (chartPt c hc (hq ▸ hy q) z₀ hz₀).stabT hf (hΛS.isScPlusSection q)
        (hq ▸ hΛS.zero q) = (chartPt c hc (hq ▸ hy q) z₀ hz₀).linZero hf h0)
    (e : c.linKer f z₀ ≃ₗ[ℝ] Λ'.L q)
    (he : ∀ v, (e v : c.φ.model.E 0 × (Fin 0 → ℝ)) = ((v : c.φ.model.E 0), 0))
    (o : (chartPt c hc (hq ▸ hy q) z₀ hz₀).Or f hf) :
    hΛS.orRay hf q hq hx z₀ hz₀ o =
      Module.Ray.map (maxPowEquiv e) ((chartPt c hc (hq ▸ hy q) z₀ hz₀).tangentOr hf h0 hL o) := by
  have h0' : IsZeroAt P (sectionAdd P f (S q)) x := hq ▸ hΛS.zero q
  have hTm := (chartPt c hc (hq ▸ hy q) z₀ hz₀).stabT_mem_linSet hf (hΛS.isScPlusSection q) h0' hx
  have hsq := hΛS.spec q hq (hq ▸ hy q) z₀ hz₀
    ((chartPt c hc (hq ▸ hy q) z₀ hz₀).stabT hf (hΛS.isScPlusSection q) h0') (fun _ => rfl)
    ((chartPt c hc (hq ▸ hy q) z₀ hz₀).stabPhi (fun i => s i q) (fun i => hΛS.isSection i q))
    (fun μ => ChartPoint.coe_stabPhi _ _ _ μ)
  -- `orRay` unfolded, as bijections
  have h1 : hΛS.orRay hf q hq hx z₀ hz₀ =
      ((ChartPoint.orEquivRay _ hf hTm).trans (MulAction.toPerm (stabSign
        ((chartPt c hc (hq ▸ hy q) z₀ hz₀).stabT hf (hΛS.isScPlusSection q) h0')))).trans
      (stabRayEquiv (ChartPoint.isFredholm_of_mem_linSet _ hf _ hTm) hsq.1
        (kerEquivMap (chartPt c hc (hq ▸ hy q) z₀ hz₀).T.subtypeL Subtype.val_injective
          hsq.2)) := rfl
  refine (DFunLike.congr_fun h1 o).trans ?_
  refine (Equiv.trans_apply _ _ o).trans ?_
  refine (congrArg _ (Equiv.trans_apply _ _ o)).trans ?_
  refine (congrArg _ (MulAction.toPerm_apply _ _)).trans ?_
  have h2 := (chartPt c hc (hq ▸ hy q) z₀ hz₀).stabRayEquiv_eq_tangentOr hf h0 hL hTe hTm hsq.1
    hsq.2 e he o
  exact h2

/-! ### The tangent family along a path of zeros -/

/-- **The kernels along a path of zeros form a continuous family** (Lemma 6.6.5 (preprint 6.30)): for an sc-smooth
path `γ` with `γ([0, 1])` in the domain of `c`, through zeros of `f` in general position, the
kernels `ker f'(γ_q) = ker Lin(z_q) ⊆ E₀` at the level-`1` lifts `z_q` of `φ(γ_q)` form a
`SubspaceFamily` over `[0, 1]`. -/
theorem exists_tangentFamily (hft : B.IsScFredholmSectionTame f) {c : StrongBundleChart PX P}
    (hc : B.IsChart c) {γ : (Fin 1 → ℝ) → X} (hγs : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγc : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ c.φ.source)
    (hγ0 : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, IsZeroAt P f (γ q))
    (hγgp : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, B.IsGeneralPositionGerm f (γ q)) :
    ∃ Λ : SubspaceFamily (Icc (0 : Fin 1 → ℝ) 1) (c.φ.model.E 0), ∀ q, Λ.L q = c.linKer f
      (chartPtOf c hc (hγc q q.2)
        (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt (hγ0 q q.2))).z := by
  obtain ⟨z, hzc, hzy⟩ := exists_continuousOn_lift_chart hγs c.isChart
  have hγcont : Continuous γ := continuousOn_univ.1 hγs.continuousOn
  have : Nonempty (Icc (0 : Fin 1 → ℝ) 1) := ⟨⟨0, left_mem_Icc.2 zero_le_one⟩⟩
  have : PreconnectedSpace (Icc (0 : Fin 1 → ℝ) 1) :=
    isPreconnected_iff_preconnectedSpace.1 (convex_Icc 0 1).isPreconnected
  have hzQ : Continuous fun q : Icc (0 : Fin 1 → ℝ) 1 => z q :=
    hzc.comp_continuous continuous_subtype_val fun q => hγc q q.2
  obtain ⟨Λ, hΛ⟩ := exists_subspaceFamily_linKer hft hc (fun q : Icc (0 : Fin 1 → ℝ) 1 => γ q)
    (hγcont.comp continuous_subtype_val) (fun q => hγc q q.2) (fun q => hγ0 q q.2)
    (fun q => (hγgp q q.2).isGoodPositionGermTame hft (hγ0 q q.2)) (fun q => z q) hzQ
    (fun q => hzy q (hγc q q.2))
  refine ⟨Λ, fun q => (hΛ q).trans (congrArg (c.linKer f) ?_)⟩
  exact c.φ.model.E.toBase_injective 1 ((hzy q (hγc q q.2)).trans
    (chartPtOf c hc (hγc q q.2)
      (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt (hγ0 q q.2))).toBase_z.symm)

/-- **The tangent family along a path of zeros**: the continuous family `q ↦ ker f'(γ_q)` of
`exists_tangentFamily`, with `L_q` the kernel `ker Lin(z_q)` at the chart point
`chartPtOf c hc (γ_q)` (`tangentFamily_L`), over `[0, 1]`. -/
def tangentFamily (hft : B.IsScFredholmSectionTame f) {c : StrongBundleChart PX P}
    (hc : B.IsChart c) {γ : (Fin 1 → ℝ) → X} (hγs : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγc : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ c.φ.source)
    (hγ0 : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, IsZeroAt P f (γ q))
    (hγgp : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, B.IsGeneralPositionGerm f (γ q)) :
    SubspaceFamily (Icc (0 : Fin 1 → ℝ) 1) (c.φ.model.E 0) :=
  (exists_tangentFamily hft hc hγs hγc hγ0 hγgp).choose.congrL _
    (exists_tangentFamily hft hc hγs hγc hγ0 hγgp).choose_spec

/-- The subspace of `tangentFamily` at `q` is `ker f'(γ_q) = ker Lin(z_q)`. -/
theorem tangentFamily_L (hft : B.IsScFredholmSectionTame f) {c : StrongBundleChart PX P}
    (hc : B.IsChart c) {γ : (Fin 1 → ℝ) → X} (hγs : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγc : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ c.φ.source)
    (hγ0 : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, IsZeroAt P f (γ q))
    (hγgp : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, B.IsGeneralPositionGerm f (γ q))
    (q : Icc (0 : Fin 1 → ℝ) 1) :
    (tangentFamily hft hc hγs hγc hγ0 hγgp).L q = c.linKer f
      (chartPtOf c hc (hγc q q.2)
        (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt (hγ0 q q.2))).z :=
  rfl

/-! ### The push-forward datum of a path of zeros -/

section ZeroDatum

variable [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]

omit [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))] in
/-- **The stabilized kernels of a path of zeros with `S = 0` and `k = 0`**: along a path `δ` of
zeros of `f` in the domain of `c` with `f'(δ_q)` onto, the sections `S_q = 0` and no `sᵢ` give the
operators `T_q = f'(δ_q)`, `T_q ⊕ 0` is onto, and the kernels are `Λ'_q = {(v, 0) | v ∈ Λ_q}` for
a family `Λ` of the kernels `ker Lin(z_q)`. -/
theorem isStabKernels_zero (hf : B.IsScFredholmSection f) {c : StrongBundleChart PX P}
    (hc : B.IsChart c) {δ : (Fin 1 → ℝ) → X}
    (hδ : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, δ q ∈ c.φ.source)
    (hδ0 : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, IsZeroAt P f (δ q))
    (hδL : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, B.IsLinSurjAt f (δ q))
    (z : Icc (0 : Fin 1 → ℝ) 1 → c.φ.model.E 1)
    (hz : ∀ q, c.φ.model.E.toBase 1 (z q) = c.φ (δ q))
    (Λ : SubspaceFamily (Icc (0 : Fin 1 → ℝ) 1) (c.φ.model.E 0))
    (hΛ : ∀ q, Λ.L q = c.linKer f (z q))
    (Λ' : SubspaceFamily (Icc (0 : Fin 1 → ℝ) 1) (c.φ.model.E 0 × (Fin 0 → ℝ)))
    (hΛ' : ∀ q, Λ'.L q = (Λ.L q).map (ContinuousLinearMap.inl ℝ (c.φ.model.E 0) (Fin 0 → ℝ) :
      c.φ.model.E 0 →ₗ[ℝ] c.φ.model.E 0 × (Fin 0 → ℝ))) :
    IsStabKernels f c hc (fun q : Icc (0 : Fin 1 → ℝ) 1 => δ q) (fun q => hδ q q.2)
      (fun q => pullbackSlice (fiberZero (pullbackProj P (Prod.snd : (Fin 1 → ℝ) × X → X))) q)
      (fun (i : Fin 0) q =>
        pullbackSlice (Fin.elim0 i : (Fin 1 → ℝ) × X → pullbackSpace P Prod.snd) q) Λ' where
  isScPlusSection _ := StrongBundle.isScPlusSection_fiberZero
  zero q := by
    rw [pullbackSlice_fiberZero, sectionAdd_fiberZero hf.isScSmooth.1]
    exact hδ0 q q.2
  isSection i _ := i.elim0
  exists_lift q := ⟨z q, hz q⟩
  spec q x hq hxc z' hz' T hT φ hφ := by
    subst hq
    obtain rfl : z' = z q := c.φ.model.E.toBase_injective 1 (hz'.trans (hz q).symm)
    have hT' : ∀ v, (T v : c.F 0) = linAt c.U c.R (c.principal f) (z q) v := fun v => by
      rw [hT v, pullbackSlice_fiberZero, sectionAdd_fiberZero hf.isScSmooth.1]
    have hTe : T = (chartPt c hc hxc (z q) hz').linZero hf (hδ0 q q.2) :=
      ContinuousLinearMap.ext fun v => Subtype.ext (hT' v)
    have hTs : Function.Surjective T := by
      rw [hTe]
      exact (chartPt c hc hxc (z q) hz').linZero_surjective hf (hδ0 q q.2) (hδL q q.2)
    have hφ0 : ∀ μ, φ μ = 0 := fun μ => by rw [Subsingleton.elim μ 0, map_zero]
    refine ⟨fun w => ?_, ?_⟩
    · obtain ⟨v, hv⟩ := hTs w
      exact ⟨(v, 0), by rw [ContinuousLinearMap.coprod_apply, map_zero, add_zero, hv]⟩
    · rw [hΛ', hΛ q]
      ext ⟨w, μ⟩
      simp only [Submodule.mem_map, LinearMap.mem_ker, StrongBundleChart.linKer]
      constructor
      · rintro ⟨v, ⟨u, hu, rfl⟩, hvw⟩
        refine ⟨(u, 0), ?_, ?_⟩
        · change T u + φ 0 = 0
          rw [map_zero, add_zero]
          exact Subtype.ext ((hT' u).trans hu)
        · rw [← hvw]
          rfl
      · rintro ⟨⟨u, μ'⟩, hker, hw⟩
        refine ⟨(u : c.φ.model.E 0), ⟨u, ?_, rfl⟩, ?_⟩
        · change T u + φ μ' = 0 at hker
          rw [hφ0, add_zero] at hker
          exact (hT' u).symm.trans (congrArg Subtype.val hker)
        · rw [← hw]
          exact Prod.ext rfl (Subsingleton.elim _ _)

omit [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))] in
/-- **Along the zero datum the orientation read in `λ(Λ')` is the tangent orientation**: at `q`
with `δ_q = x`, `orRay` of `isStabKernels_zero` is `λ(e)` of `tangentOr`, for
`e : ker f'(x) ≅ Λ'_q`, `v ↦ (v, 0)`. -/
theorem orRay_zero (hf : B.IsScFredholmSection f) {c : StrongBundleChart PX P}
    {hc : B.IsChart c} {δ : (Fin 1 → ℝ) → X}
    {hy : ∀ q : Icc (0 : Fin 1 → ℝ) 1, δ q ∈ c.φ.source}
    {Λ' : SubspaceFamily (Icc (0 : Fin 1 → ℝ) 1) (c.φ.model.E 0 × (Fin 0 → ℝ))}
    (hΛS : IsStabKernels f c hc (fun q : Icc (0 : Fin 1 → ℝ) 1 => δ q) hy
      (fun q => pullbackSlice (fiberZero (pullbackProj P (Prod.snd : (Fin 1 → ℝ) × X → X))) q)
      (fun (i : Fin 0) q =>
        pullbackSlice (Fin.elim0 i : (Fin 1 → ℝ) × X → pullbackSpace P Prod.snd) q) Λ')
    (q : Icc (0 : Fin 1 → ℝ) 1) {x : X} (hq : δ q = x) (hx : x ∈ PX.smoothSet)
    (z₀ : c.φ.model.E 1) (hz₀ : c.φ.model.E.toBase 1 z₀ = c.φ x) (h0 : IsZeroAt P f x)
    (hL : B.IsLinSurjAt f x) (e : c.linKer f z₀ ≃ₗ[ℝ] Λ'.L q)
    (he : ∀ v, (e v : c.φ.model.E 0 × (Fin 0 → ℝ)) = ((v : c.φ.model.E 0), 0))
    (o : (chartPt c hc (hq ▸ hy q) z₀ hz₀).Or f hf) :
    hΛS.orRay hf q hq hx z₀ hz₀ o =
      Module.Ray.map (maxPowEquiv e) ((chartPt c hc (hq ▸ hy q) z₀ hz₀).tangentOr hf h0 hL o) :=
  hΛS.orRay_eq_tangentOr hf q hq hx z₀ hz₀ h0 hL
    (ContinuousLinearMap.ext fun v => Subtype.ext (by
      rw [ChartPoint.coe_stabT, ChartPoint.coe_linZero, pullbackSlice_fiberZero,
        sectionAdd_fiberZero hf.isScSmooth.1])) e he o

variable (f) in
/-- **The tangent orientation at a zero `y` in the chart `c`**, read in the chart point
`chartPtOf c hc hy hys` (the level-`1` lift of `φ(y)`): `tangentOr`. -/
abbrev tangentOrAt (hf : B.IsScFredholmSection f) (c : StrongBundleChart PX P) (hc : B.IsChart c)
    {y : X} (hy : y ∈ c.φ.source) (hys : y ∈ PX.smoothSet) (hy0 : IsZeroAt P f y)
    (hyL : B.IsLinSurjAt f y) :
    (chartPtOf c hc hy hys).Or f hf ≃
      Module.Ray ℝ (maxPow (c.linKer f (chartPtOf c hc hy hys).z)) :=
  (chartPtOf c hc hy hys).tangentOr hf hy0 hyL

/-- **The tangent orientations of a continuous orientation are continued into each other along a
path of zeros** (the core of Theorem 6.6.18 (preprint 6.41)): for a continuous orientation `o` over `V ⊆ U`
(Definition 6.6.12 (preprint 6.36)) and an sc-smooth path `δ` with values in `V`, through zeros of `f` with `f'`
onto, and a family `Λ` of the kernels `ker f'(δ_q) ⊆ E₀` over `[0, 1]`, continuing the tangent
orientation at `δ(0)` in `λ(Λ)` gives the tangent orientation at `δ(1)`.  *Proof*: `S = 0`, `k = 0`
and the kernels `(v, 0)` form a push-forward datum (`isStabKernels_zero`); `o` is invariant under
the push-forward (Definition 6.6.12 (preprint 6.36)), which is continuation between the orientations read in `λ(Λ')`
(`push_eq_orRay`); these are the tangent orientations (`orRay_zero`), and continuation commutes
with `v ↦ (v, 0)` (`SubspaceFamily.cont_map`). -/
theorem cont_tangentOr (hf : B.IsScFredholmSection f) {c : StrongBundleChart PX P}
    {hc : B.IsChart c} {U V : Set X} {hUc : U ⊆ c.φ.source} {hVU : V ⊆ U}
    {o : ∀ y (hy : y ∈ V) (hys : y ∈ PX.smoothSet), (chartPtOf c hc (hUc (hVU hy)) hys).Or f hf}
    (ho : IsContinuousOrientation f hf c hc hUc hVU o) {δ : (Fin 1 → ℝ) → X}
    (hδs : (rnPolyfold 1).IsScSmoothMap PX δ) (hδV : ∀ q, δ q ∈ V)
    (hδ0 : ∀ q, IsZeroAt P f (δ q)) (hδL : ∀ q, B.IsLinSurjAt f (δ q))
    (Λ : SubspaceFamily (Icc (0 : Fin 1 → ℝ) 1) (c.φ.model.E 0))
    (hΛ : ∀ q : Icc (0 : Fin 1 → ℝ) 1, Λ.L q = c.linKer f
      (chartPtOf c hc (hUc (hVU (hδV q))) (hf.mem_smoothSet_of_isZeroAt (hδ0 q))).z) :
    (Λ.congrL (fun q => c.linKer f
        (chartPtOf c hc (hUc (hVU (hδV q))) (hf.mem_smoothSet_of_isZeroAt (hδ0 q))).z) hΛ).cont
        iccZero iccOne
        (tangentOrAt f hf c hc (hUc (hVU (hδV (pt1 0))))
            (hf.mem_smoothSet_of_isZeroAt (hδ0 (pt1 0))) (hδ0 (pt1 0)) (hδL (pt1 0))
            (o (δ (pt1 0)) (hδV (pt1 0)) (hf.mem_smoothSet_of_isZeroAt (hδ0 (pt1 0))))) =
      tangentOrAt f hf c hc (hUc (hVU (hδV (pt1 1))))
          (hf.mem_smoothSet_of_isZeroAt (hδ0 (pt1 1))) (hδ0 (pt1 1)) (hδL (pt1 1))
          (o (δ (pt1 1)) (hδV (pt1 1)) (hf.mem_smoothSet_of_isZeroAt (hδ0 (pt1 1)))) := by
  have hs : ∀ q, δ q ∈ PX.smoothSet := fun q => hf.mem_smoothSet_of_isZeroAt (hδ0 q)
  set Λ₁ := Λ.congrL (fun q => c.linKer f
    (chartPtOf c hc (hUc (hVU (hδV q))) (hf.mem_smoothSet_of_isZeroAt (hδ0 q))).z) hΛ
    with hΛ₁def
  -- the kernels `(v, 0)`
  set J : Icc (0 : Fin 1 → ℝ) 1 → c.φ.model.E 0 →L[ℝ] c.φ.model.E 0 × (Fin 0 → ℝ) :=
    fun _ => ContinuousLinearMap.inl ℝ (c.φ.model.E 0) (Fin 0 → ℝ) with hJdef
  have hJ : Continuous fun p : Icc (0 : Fin 1 → ℝ) 1 × c.φ.model.E 0 => J p.1 p.2 :=
    (ContinuousLinearMap.inl ℝ (c.φ.model.E 0) (Fin 0 → ℝ)).continuous.comp continuous_snd
  have hinl : Function.Injective (ContinuousLinearMap.inl ℝ (c.φ.model.E 0) (Fin 0 → ℝ)) :=
    fun v w h => congrArg Prod.fst h
  obtain ⟨Λ', hΛ'⟩ := Λ₁.exists_map J hJ fun q => hinl.injOn
  have hΛS := isStabKernels_zero hf hc (fun q _ => hUc (hVU (hδV q))) (fun q _ => hδ0 q)
    (fun q _ => hδL q) (fun q => (chartPtOf c hc (hUc (hVU (hδV q))) (hs q)).z)
    (fun q => (chartPtOf c hc (hUc (hVU (hδV q))) (hs q)).toBase_z) Λ₁ (fun q => rfl) Λ' hΛ'
  -- the push-forward datum from `δ(0)` to `δ(1)`
  have hpush : IsPush f hf c hc δ (fun q _ => hUc (hVU (hδV q))) rfl rfl
      (hUc (hVU (hδV (pt1 0)))) (hUc (hVU (hδV (pt1 1)))) (hs (pt1 0)) (hs (pt1 1))
      (hΛS.push hf iccZero iccOne rfl rfl (hs (pt1 0)) (hs (pt1 1))
        (exists_lift_of_smooth c (hUc (hVU (hδV (pt1 0)))) (hs (pt1 0))).choose
        (exists_lift_of_smooth c (hUc (hVU (hδV (pt1 0)))) (hs (pt1 0))).choose_spec
        (exists_lift_of_smooth c (hUc (hVU (hδV (pt1 1)))) (hs (pt1 1))).choose
        (exists_lift_of_smooth c (hUc (hVU (hδV (pt1 1)))) (hs (pt1 1))).choose_spec) := by
    refine ⟨fiberZero _, StrongBundle.isScPlusSection_fiberZero,
      Filter.Eventually.of_forall fun q => ?_, 0, Fin.elim0, fun i => i.elim0, Λ', hΛS, rfl⟩
    have hL' : IsSection (pullbackProj P Prod.snd) (paramLift (n := 1) f hf.isScSmooth.1) :=
      isSection_pullbackLift _
    rw [sectionAdd_fiberZero hL']
    exact (isZeroAt_pullback_iff_pullbackSlice hL' q (δ q)).2 (hδ0 q)
  have hoe := ho δ hδs (fun q _ => hVU (hδV q)) (hδV (pt1 0)) (hδV (pt1 1)) (hs (pt1 0))
    (hs (pt1 1)) rfl rfl _ hpush
  rw [hΛS.push_eq_orRay] at hoe
  have h2 := equiv_trans_trans_symm_apply hoe
  rw [SubspaceFamily.contEquiv_apply] at h2
  -- the identifications `e_q : Λ_q ≅ Λ'_q`, `v ↦ (v, 0)`
  let e : ∀ q, Λ₁.L q ≃ₗ[ℝ] Λ'.L q := fun q =>
    (Submodule.equivMapOfInjective _ hinl (Λ₁.L q)).trans (LinearEquiv.ofEq _ _ (hΛ' q).symm)
  have he : ∀ q (v : Λ₁.L q), (e q v : c.φ.model.E 0 × (Fin 0 → ℝ)) = J q v := fun _ _ => rfl
  have h0e := orRay_zero hf hΛS iccZero rfl (hs (pt1 0))
    (exists_lift_of_smooth c (hUc (hVU (hδV (pt1 0)))) (hs (pt1 0))).choose
    (exists_lift_of_smooth c (hUc (hVU (hδV (pt1 0)))) (hs (pt1 0))).choose_spec
    (hδ0 (pt1 0)) (hδL (pt1 0)) (e iccZero) (fun _ => rfl)
    (o (δ (pt1 0)) (hδV (pt1 0)) (hs (pt1 0)))
  have h1e := orRay_zero hf hΛS iccOne rfl (hs (pt1 1))
    (exists_lift_of_smooth c (hUc (hVU (hδV (pt1 1)))) (hs (pt1 1))).choose
    (exists_lift_of_smooth c (hUc (hVU (hδV (pt1 1)))) (hs (pt1 1))).choose_spec
    (hδ0 (pt1 1)) (hδL (pt1 1)) (e iccOne) (fun _ => rfl)
    (o (δ (pt1 1)) (hδV (pt1 1)) (hs (pt1 1)))
  have key := (Λ₁.cont_map J hJ Λ' e he iccZero iccOne _).symm.trans <|
    (congrArg (Λ'.cont iccZero iccOne) h0e.symm).trans <| h2.trans h1e
  exact (Module.Ray.map (maxPowEquiv (e iccOne))).injective key

/-- **Theorem 6.6.18 (preprint 6.41), naturality of the tangent orientations along a path of zeros**: for a
continuous orientation `o` over `V ⊆ U` (Definition 6.6.12 (preprint 6.36)) and an sc-smooth path `γ` with
`γ([0, 1]) ⊆ V`, through zeros of `f` in general position, the tangent orientations
`q ↦ tangentOr(o_{γ_q})` of `λ(ker f'(γ_q))` form an orientation of the line bundle `λ(Λ)` of the
tangent family `Λ_q = ker f'(γ_q) = T_{γ_q}S` (`tangentFamily`): they vary continuously.
*Proof*: for `t ∈ [0, 1]` the path `δ(s) = γ(t · κ(s))`, `κ = Real.smoothTransition`, is sc-smooth
with values in `γ([0, t]) ⊆ V` for all `s ∈ ℝ`; `cont_tangentOr` along `δ` and `cont_comp`
(continuation in the pulled-back family) show that the orientation of `λ(Λ)` through the tangent
orientation at `γ(0)` has the tangent orientation at `γ(t)`. -/
theorem isLineOrientation_tangentOr (hft : B.IsScFredholmSectionTame f)
    {c : StrongBundleChart PX P} {hc : B.IsChart c} {U V : Set X} {hUc : U ⊆ c.φ.source}
    {hVU : V ⊆ U}
    {o : ∀ y (hy : y ∈ V) (hys : y ∈ PX.smoothSet),
      (chartPtOf c hc (hUc (hVU hy)) hys).Or f hft.toIsScFredholmSection}
    (ho : IsContinuousOrientation f hft.toIsScFredholmSection c hc hUc hVU o)
    {γ : (Fin 1 → ℝ) → X} (hγs : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγV : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ V)
    (hγ0 : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, IsZeroAt P f (γ q))
    (hγgp : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, B.IsGeneralPositionGerm f (γ q)) :
    IsLineOrientation (tangentFamily hft hc hγs (fun q hq => hUc (hVU (hγV q hq))) hγ0 hγgp).det
      fun q => tangentOrAt f hft.toIsScFredholmSection c hc (hUc (hVU (hγV q q.2)))
        (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt (hγ0 q q.2)) (hγ0 q q.2)
        (hγgp q q.2).isLinSurjAt
        (o (γ q) (hγV q q.2)
          (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt (hγ0 q q.2))) := by
  have hf := hft.toIsScFredholmSection
  set Λ := tangentFamily hft hc hγs (fun q hq => hUc (hVU (hγV q hq))) hγ0 hγgp with hΛdef
  set τ : ∀ q, Module.Ray ℝ (Λ.det q) := fun q => tangentOrAt f hf c hc (hUc (hVU (hγV q q.2)))
    (hf.mem_smoothSet_of_isZeroAt (hγ0 q q.2)) (hγ0 q q.2) (hγgp q q.2).isLinSurjAt
    (o (γ q) (hγV q q.2) (hf.mem_smoothSet_of_isZeroAt (hγ0 q q.2))) with hτdef
  obtain ⟨O, hO⟩ := exists_lineOrientation_apply_eq (L := Λ.det) iccZero (τ iccZero)
  suffices h : ∀ t, O t = τ t by
    have hτO : τ = O.1 := funext fun t => (h t).symm
    change IsLineOrientation Λ.det τ
    rw [hτO]
    exact O.2
  intro t
  -- the reparametrization `κ_t(s) = t · κ(s)` of `[0, 1]` onto `[0, t]`
  have hκ : ∀ s : ℝ, pt1 (t.1 0 * Real.smoothTransition s) ∈ Icc (0 : Fin 1 → ℝ) 1 := fun s =>
    pt1_mem_Icc ⟨mul_nonneg (t.2.1 0) (Real.smoothTransition.nonneg s),
      mul_le_one₀ (t.2.2 0) (Real.smoothTransition.nonneg s) (Real.smoothTransition.le_one s)⟩
  let g : C(Icc (0 : Fin 1 → ℝ) 1, Icc (0 : Fin 1 → ℝ) 1) :=
    ⟨fun q => ⟨pt1 (t.1 0 * Real.smoothTransition (q.1 0)), hκ _⟩,
      (continuous_pi fun _ => continuous_const.mul (Real.smoothTransition.continuous.comp
        ((continuous_apply 0).comp continuous_subtype_val))).subtype_mk _⟩
  have hg0 : g iccZero = iccZero := Subtype.ext (by
    change pt1 (t.1 0 * Real.smoothTransition (pt1 0 0)) = pt1 0
    rw [pt1_apply, Real.smoothTransition.zero, mul_zero])
  have hg1 : g iccOne = t := Subtype.ext (by
    change pt1 (t.1 0 * Real.smoothTransition (pt1 1 0)) = t.1
    rw [pt1_apply, Real.smoothTransition.one, mul_one, pt1_apply_zero])
  have hδs : (rnPolyfold 1).IsScSmoothMap PX
      fun s => γ (pt1 (t.1 0 * Real.smoothTransition (s 0))) :=
    isScSmoothMap_reparam (κ := fun s => t.1 0 * Real.smoothTransition s) hγs
      (contDiff_const.mul Real.smoothTransition.contDiff)
  have hcore := cont_tangentOr hf ho hδs (fun q => hγV _ (hκ _)) (fun q => hγ0 _ (hκ _))
    (fun q => (hγgp _ (hκ _)).isLinSurjAt) (Λ.comp g) (fun q => rfl)
  have hO0 : O (g iccZero) = τ (g iccZero) := by
    rw [hg0]
    exact hO
  have h1 : O (g iccOne) = τ (g iccOne) :=
    (Λ.cont_eq O _ _).symm.trans <| (congrArg (Λ.cont (g iccZero) (g iccOne)) hO0).trans <|
      (Λ.cont_comp g _ _ _).symm.trans hcore
  rw [hg1] at h1
  exact h1

/-- **The natural orientation of `S` along paths, for an orientation of `f`**: for an orientation
`o` of `f` (Definition 6.6.16 (preprint 6.40)), an orientable neighbourhood `V ⊆ U` of a smooth point `x₀` in the
chart `c` (Definition 6.6.12 (preprint 6.36)) and an sc-smooth path `γ` with `γ([0, 1]) ⊆ V` through zeros of `f` in
general position, the tangent orientations of `T_{γ_q}S = ker f'(γ_q)` by `o_{γ_q}` (read in `c`
by `restrictOr`) form an orientation of the line bundle `λ(Λ)` of the tangent family
(`isLineOrientation_tangentOr`, `o` being a continuous orientation over `V`). -/
theorem isLineOrientation_tangentOr_of_isSectionOrientation (hft : B.IsScFredholmSectionTame f)
    {o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hft.toIsScFredholmSection y hy}
    (ho : IsSectionOrientation f hft.toIsScFredholmSection o) {x₀ : X} (hx₀ : x₀ ∈ PX.smoothSet)
    {c : StrongBundleChart PX P} {hc : B.IsChart c} {U V : Set X}
    (hN : IsOrientableNbhd f hft.toIsScFredholmSection c hc U V x₀)
    {γ : (Fin 1 → ℝ) → X} (hγs : (rnPolyfold 1).IsScSmoothMap PX γ)
    (hγV : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ V)
    (hγ0 : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, IsZeroAt P f (γ q))
    (hγgp : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, B.IsGeneralPositionGerm f (γ q)) :
    IsLineOrientation (tangentFamily hft hc hγs
        (fun q hq => hN.hasLocalPropagation.subset (hN.subset (hγV q hq))) hγ0 hγgp).det
      fun q => tangentOrAt f hft.toIsScFredholmSection c hc
        (hN.hasLocalPropagation.subset (hN.subset (hγV q q.2)))
        (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt (hγ0 q q.2)) (hγ0 q q.2)
        (hγgp q q.2).isLinSurjAt
        (restrictOr o hN (γ q) (hγV q q.2)
          (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt (hγ0 q q.2))) :=
  isLineOrientation_tangentOr hft (ho x₀ hx₀ c hc U V hN) hγs hγV hγ0 hγgp

/-- **Theorem 6.6.18 (preprint 6.41)**: let `P : Y → X` be a strong bundle over a tame M-polyfold, `f` a proper
sc-Fredholm section (with tame germ data) such that `(f, x)` is in general position at every
zero `x`, and `o` an orientation of `f` (Definition 6.6.16 (preprint 6.40)).  Then (1) `S = f⁻¹(0)` is a compact
manifold with boundary with corners (`SolutionSetInGeneralPosition`, `theorem_6_6_18_solutionSet`),
and (2) the orientations of the tangent spaces `T_xS = ker f'(x)` by `o_x` (`tangentOr`) vary
continuously: along every sc-smooth path `γ` of zeros in an orientable neighbourhood `V ⊆ U` of a
smooth point, in its chart `c`, they form an orientation of the line bundle `λ(Λ)` of the tangent
family `Λ_q = ker f'(γ_q)` (`tangentFamily`, `isLineOrientation_tangentOr`). -/
theorem theorem_6_6_18_hyp (hX : PX.IsTame) (hft : B.IsScFredholmSectionTame f) (hP : B.IsProper f)
    (hgp : ∀ x, IsZeroAt P f x → B.IsGeneralPositionGerm f x)
    {o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hft.toIsScFredholmSection y hy}
    (ho : IsSectionOrientation f hft.toIsScFredholmSection o) :
    B.SolutionSetInGeneralPosition f ∧
      ∀ x₀ ∈ PX.smoothSet, ∀ (c : StrongBundleChart PX P) (hc : B.IsChart c) (U V : Set X)
        (hN : IsOrientableNbhd f hft.toIsScFredholmSection c hc U V x₀)
        (γ : (Fin 1 → ℝ) → X) (hγs : (rnPolyfold 1).IsScSmoothMap PX γ)
        (hγV : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ V)
        (hγ0 : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, IsZeroAt P f (γ q)),
        IsLineOrientation (tangentFamily hft hc hγs
            (fun q hq => hN.hasLocalPropagation.subset (hN.subset (hγV q hq))) hγ0
            (fun q hq => hgp (γ q) (hγ0 q hq))).det
          fun q => tangentOrAt f hft.toIsScFredholmSection c hc
            (hN.hasLocalPropagation.subset (hN.subset (hγV q q.2)))
            (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt (hγ0 q q.2)) (hγ0 q q.2)
            (hgp (γ q) (hγ0 q q.2)).isLinSurjAt
            (restrictOr o hN (γ q) (hγV q q.2)
              (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt (hγ0 q q.2))) :=
  ⟨theorem_6_6_18_solutionSet hX hft hP hgp, fun _ hx₀ _ _ _ _ hN γ hγs hγV hγ0 =>
    isLineOrientation_tangentOr_of_isSectionOrientation hft ho hx₀ hN hγs hγV hγ0
      fun q hq => hgp (γ q) (hγ0 q hq)⟩

end ZeroDatum

end Tangent3

end Polyfold
