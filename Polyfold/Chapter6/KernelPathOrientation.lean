import Polyfold.Chapter6.CobordismOrientationEnds2021b

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, pp. 273–276
(Definition 6.6.16, Theorem 6.6.18, Remark 6.6.19): an orientation of `DET` over a set of
Fredholm operators, read on the kernels of a continuous family of surjective operators.

# The orientation of the kernels along a family of surjective operators

For a continuous orientation `o` of `DET` over a set `C` of Fredholm operators and a continuous
family `T_q ∈ C` of surjective operators over a connected `Q`, the orientations of `ker T_q`
given by `o(T_q)` (`det T_q ≅ λ(ker T_q)`) are carried to each other by every jointly continuous
family of maps `J_q` that sends `ker T_{q₀}` isomorphically to `ker T_q` and is the identity at
`q₀`.

* `ray_detEquivOfSurjective_of_family`: the statement in `λ(ker T_q)`.
* `surjRay_of_family`: the statement for the kernels read in a space `V` through an injective
  `j` (`surjRay`).
* `surjRay_comp_shear`, `shearKerEquiv`, `shearMapEquiv`, `surjRay_shearMapEquiv`: the case
  `T_τ = T (1 + τ N)` with `N² = 0`, `τ ∈ [0, 1]`: the orientation of
  `ker (T (1 + N)) = (1 − N) ker T` given by `o` is the image under `1 − N` of the orientation
  of `ker T` given by `o`.
-/

open Set Filter Topology Module

noncomputable section

namespace Polyfold

section Family

variable {Q : Type*} [TopologicalSpace Q]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

set_option maxHeartbeats 800000 in
-- the stabilization isomorphisms of the family are unfolded at every use
/-- **The orientations of the kernels of a family of surjective operators** given by an
orientation `o` of `DET` over `C ∋ T_q`: if `κ_q : ker T_{q₀} ≅ ker T_q` is the restriction of a
jointly continuous family `J_q` of maps of `E`, with `κ_{q₀}` the identity, then the orientation
of `ker T_q` given by `o(T_q)` is `λ(κ_q)` of the one of `ker T_{q₀}` given by `o(T_{q₀})`. -/
theorem ray_detEquivOfSurjective_of_family [PreconnectedSpace Q] {C : Set (E →L[ℝ] F)}
    {hC : ∀ T ∈ C, T.IsFredholm} (o : LineOrientation (DetOn C hC)) (T : Q → E →L[ℝ] F)
    (hTc : Continuous T) (hTC : ∀ q, T q ∈ C) (hTs : ∀ q, Function.Surjective (T q))
    (J : Q → E →L[ℝ] E) (hJ : Continuous fun p : Q × E => J p.1 p.2) (q₀ : Q)
    (κ : ∀ q, LinearMap.ker (T q₀ : E →ₗ[ℝ] F) ≃ₗ[ℝ] LinearMap.ker (T q : E →ₗ[ℝ] F))
    (hκ : ∀ q v, (κ q v : E) = J q v) (hκ₀ : ∀ v, (κ q₀ v : E) = v) (q : Q) :
    Module.Ray.map (detEquivOfSurjective (hTs q)) (o ⟨T q, hTC q⟩) =
      Module.Ray.map (maxPowEquiv (κ q))
        (Module.Ray.map (detEquivOfSurjective (hTs q₀)) (o ⟨T q₀, hTC q₀⟩)) := by
  have : Nonempty Q := ⟨q₀⟩
  set φ : Q → (Fin 0 → ℝ) →L[ℝ] F := fun _ => 0 with hφdef
  have hφc : Continuous φ := continuous_const
  have hφ : ∀ q, Function.Surjective ((T q).coprod (φ q)) := fun q w => by
    obtain ⟨v, hv⟩ := hTs q w
    exact ⟨(v, 0), by rw [ContinuousLinearMap.coprod_apply, map_zero, add_zero, hv]⟩
  have hTF : ∀ q, (T q).IsFredholm := fun q => hC _ (hTC q)
  obtain ⟨Λ, hΛ⟩ := exists_subspaceFamily_ker (fun q => (T q).coprod (φ q))
    (continuous_coprod hTc hφc) (fun q => isFredholm_coprod_of_surjective (hTF q) (hφ q)) hφ
  -- the orientation of `λ(Λ)` received from `o`
  let o₁ : LineOrientation Λ.det :=
    ⟨_, isLineOrientation_stabRay o T hTc hTC φ hφc hφ Λ hΛ⟩
  -- `ker T_q ≅ ker(T_q ⊕ 0) = Λ_q`
  let σ : ∀ q, LinearMap.ker (T q : E →ₗ[ℝ] F) ≃ₗ[ℝ] Λ.L q := fun q =>
    (LinearEquiv.ofBijective (stabJ (T q) (φ q))
      ⟨stabJ_injective, stabJ_surjective_zero⟩).trans (LinearEquiv.ofEq _ _ (hΛ q).symm)
  have hσ : ∀ q v, ((σ q v : Λ.L q) : E × (Fin 0 → ℝ)) = ((v : E), 0) := fun q v => rfl
  have ho₁ : ∀ q, o₁ q = Module.Ray.map (maxPowEquiv (σ q))
      (Module.Ray.map (detEquivOfSurjective (hTs q)) (o ⟨T q, hTC q⟩)) := fun q => by
    have h := stabRayEquiv_zero (hTF q) (hTs q) (hφ q) (LinearEquiv.ofEq _ _ (hΛ q).symm) (σ q)
      (fun v => rfl) (o ⟨T q, hTC q⟩)
    have hs : stabSign (T q) • (o ⟨T q, hTC q⟩ : Module.Ray ℝ (fredholmDet (T q))) =
        o ⟨T q, hTC q⟩ := stabSign_smul_of_surjective (hTs q) _
    have h' := (congrArg (stabRayEquiv (hTF q) (hφ q) (LinearEquiv.ofEq _ _ (hΛ q).symm))
      hs).symm.trans h
    change stabSign (T q) • stabRayEquiv (hTF q) (hφ q) (LinearEquiv.ofEq _ _ (hΛ q).symm)
      (o ⟨T q, hTC q⟩) = _
    rw [stabSign_of_surjective (hTs q), one_smul]
    exact h'
  -- the orientation carried from `q₀` by `J`
  let g : C(Q, Q) := ContinuousMap.const Q q₀
  let J' : Q → E × (Fin 0 → ℝ) →L[ℝ] E × (Fin 0 → ℝ) := fun q =>
    (J q).prodMap (ContinuousLinearMap.id ℝ (Fin 0 → ℝ))
  have hJ' : Continuous fun p : Q × (E × (Fin 0 → ℝ)) => J' p.1 p.2 := by
    have h1 : Continuous fun p : Q × (E × (Fin 0 → ℝ)) => J p.1 p.2.1 :=
      hJ.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
    exact h1.prodMk (continuous_snd.comp continuous_snd)
  let e : ∀ q, (Λ.comp g).L q ≃ₗ[ℝ] Λ.L q := fun q => ((σ q₀).symm.trans (κ q)).trans (σ q)
  have he : ∀ q (v : (Λ.comp g).L q), ((e q v : Λ.L q) : E × (Fin 0 → ℝ)) = J' q v := by
    intro q v
    obtain ⟨w, rfl⟩ := (σ q₀).surjective v
    change ((σ q (κ q ((σ q₀).symm (σ q₀ w))) : Λ.L q) : E × (Fin 0 → ℝ)) = J' q (σ q₀ w)
    rw [LinearEquiv.symm_apply_apply, hσ, hκ, hσ]
    exact Prod.ext rfl (Subsingleton.elim _ _)
  let o₂ : LineOrientation Λ.det :=
    ⟨_, (Λ.comp g).isLineOrientation_map J' hJ' Λ e he (o₁.comp g)⟩
  have he₀ : e q₀ = LinearEquiv.refl ℝ (Λ.L q₀) := by
    refine LinearEquiv.ext fun v => Subtype.ext ?_
    obtain ⟨w, rfl⟩ := (σ q₀).surjective v
    change ((σ q₀ (κ q₀ ((σ q₀).symm (σ q₀ w))) : Λ.L q₀) : E × (Fin 0 → ℝ)) = (σ q₀ w : Λ.L q₀)
    rw [LinearEquiv.symm_apply_apply, hσ, hκ₀, hσ]
  have h12 : o₁ = o₂ := by
    refine LineOrientation.eq_of_apply_eq q₀ ?_
    have hr : ∀ ε : Λ.L q₀ ≃ₗ[ℝ] Λ.L q₀, ε = LinearEquiv.refl ℝ _ →
        ∀ r : Module.Ray ℝ (maxPow (Λ.L q₀)), Module.Ray.map (maxPowEquiv ε) r = r := by
      intro ε hε r
      subst hε
      rw [maxPowEquiv_refl, Module.Ray.map_refl]
      rfl
    exact (hr (e q₀) he₀ (o₁ q₀)).symm
  have hq : o₁ q = Module.Ray.map (maxPowEquiv (e q)) (o₁ q₀) :=
    congrArg (fun o' : LineOrientation Λ.det => o' q) h12
  have hq2 : Module.Ray.map (maxPowEquiv (σ q))
        (Module.Ray.map (detEquivOfSurjective (hTs q)) (o ⟨T q, hTC q⟩)) =
      Module.Ray.map (maxPowEquiv (e q)) (Module.Ray.map (maxPowEquiv (σ q₀))
        (Module.Ray.map (detEquivOfSurjective (hTs q₀)) (o ⟨T q₀, hTC q₀⟩))) :=
    (ho₁ q).symm.trans (hq.trans (congrArg (Module.Ray.map (maxPowEquiv (e q))) (ho₁ q₀)))
  have hq3 := hq2.trans ((ray_map_map (maxPowEquiv (σ q₀)) (maxPowEquiv (e q)) _).trans
    (congrArg (fun L => Module.Ray.map L
      (Module.Ray.map (detEquivOfSurjective (hTs q₀)) (o ⟨T q₀, hTC q₀⟩)))
      (maxPowEquiv_trans (σ q₀) (e q)).symm))
  have hcomp : (σ q₀).trans (e q) = (κ q).trans (σ q) := by
    refine LinearEquiv.ext fun v => ?_
    change σ q (κ q ((σ q₀).symm (σ q₀ v))) = σ q (κ q v)
    rw [LinearEquiv.symm_apply_apply]
  have hq' := hq3.trans ((congrArg (fun L => Module.Ray.map (maxPowEquiv L)
    (Module.Ray.map (detEquivOfSurjective (hTs q₀)) (o ⟨T q₀, hTC q₀⟩))) hcomp).trans
    ((congrArg (fun L => Module.Ray.map L
      (Module.Ray.map (detEquivOfSurjective (hTs q₀)) (o ⟨T q₀, hTC q₀⟩)))
      (maxPowEquiv_trans (κ q) (σ q))).trans
      (ray_map_map (maxPowEquiv (κ q)) (maxPowEquiv (σ q)) _).symm))
  exact (Module.Ray.map (maxPowEquiv (σ q))).injective hq'

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **The same for the kernels read in `V`** through an injective `j` (`surjRay`): with
`N_q = j(ker T_q)` and `e : N_{q₀} ≅ N_q`, `e(j v) = j(J_q v)`. -/
theorem surjRay_of_family [PreconnectedSpace Q] {C : Set (E →L[ℝ] F)}
    {hC : ∀ T ∈ C, T.IsFredholm} (o : LineOrientation (DetOn C hC)) (T : Q → E →L[ℝ] F)
    (hTc : Continuous T) (hTC : ∀ q, T q ∈ C) (hTs : ∀ q, Function.Surjective (T q))
    (J : Q → E →L[ℝ] E) (hJ : Continuous fun p : Q × E => J p.1 p.2) (q₀ : Q)
    (κ : ∀ q, LinearMap.ker (T q₀ : E →ₗ[ℝ] F) ≃ₗ[ℝ] LinearMap.ker (T q : E →ₗ[ℝ] F))
    (hκ : ∀ q v, (κ q v : E) = J q v) (hκ₀ : ∀ v, (κ q₀ v : E) = v) (q : Q)
    (j : E →L[ℝ] V) (hj : Function.Injective j) {N₀ N : Submodule ℝ V}
    (hN₀ : (LinearMap.ker (T q₀ : E →ₗ[ℝ] F)).map (j : E →ₗ[ℝ] V) = N₀)
    (hN : (LinearMap.ker (T q : E →ₗ[ℝ] F)).map (j : E →ₗ[ℝ] V) = N)
    (e : N₀ ≃ₗ[ℝ] N)
    (he : ∀ v : LinearMap.ker (T q₀ : E →ₗ[ℝ] F),
      (e (kerEquivOfMap (T q₀) j hj hN₀ v) : V) = j (J q v)) :
    surjRay (hTs q) j hj hN (o ⟨T q, hTC q⟩) =
      Module.Ray.map (maxPowEquiv e) (surjRay (hTs q₀) j hj hN₀ (o ⟨T q₀, hTC q₀⟩)) := by
  have h := ray_detEquivOfSurjective_of_family o T hTc hTC hTs J hJ q₀ κ hκ hκ₀ q
  have hcomp : (κ q).trans (kerEquivOfMap (T q) j hj hN) =
      (kerEquivOfMap (T q₀) j hj hN₀).trans e := by
    refine LinearEquiv.ext fun v => Subtype.ext ?_
    change (kerEquivOfMap (T q) j hj hN (κ q v) : V) = (e (kerEquivOfMap (T q₀) j hj hN₀ v) : V)
    rw [coe_kerEquivOfMap, hκ, he]
  change Module.Ray.map (maxPowEquiv (kerEquivOfMap (T q) j hj hN))
      (Module.Ray.map (detEquivOfSurjective (hTs q)) (o ⟨T q, hTC q⟩)) =
    Module.Ray.map (maxPowEquiv e) (Module.Ray.map (maxPowEquiv (kerEquivOfMap (T q₀) j hj hN₀))
      (Module.Ray.map (detEquivOfSurjective (hTs q₀)) (o ⟨T q₀, hTC q₀⟩)))
  rw [h, ray_map_map (maxPowEquiv (κ q)), ← maxPowEquiv_trans, hcomp, maxPowEquiv_trans,
    ← ray_map_map]

/-- **The orientation of the kernel after a shear** (the kernels of `F'(t, x)` and of
`(F_t'(x))^` in Remark 6.6.19): let `T₀, T₁ = T₀ (1 + N)` be surjective members of a convex set
`C` of Fredholm operators, with `N² = 0`.  Then `ker T₁ = (1 − N) ker T₀`, and for an
orientation `o` of `DET` over `C` the orientation of `ker T₁` given by `o(T₁)` is the image
under `1 − N` of the orientation of `ker T₀` given by `o(T₀)` (the path `T₀ (1 + τ N)`,
`τ ∈ [0, 1]`, consists of surjective members of `C`). -/
theorem surjRay_comp_shear {C : Set (E →L[ℝ] F)} (hconv : Convex ℝ C)
    {hC : ∀ T ∈ C, T.IsFredholm} (o : LineOrientation (DetOn C hC)) {T₀ T₁ : E →L[ℝ] F}
    (h₀ : T₀ ∈ C) (h₁ : T₁ ∈ C) (hs₀ : Function.Surjective T₀) (hs₁ : Function.Surjective T₁)
    (N : E →L[ℝ] E) (hNN : ∀ w, N (N w) = 0) (hT : ∀ w, T₁ w = T₀ (w + N w))
    (j : E →L[ℝ] V) (hj : Function.Injective j) {N₀ N₁ : Submodule ℝ V}
    (hN₀ : (LinearMap.ker (T₀ : E →ₗ[ℝ] F)).map (j : E →ₗ[ℝ] V) = N₀)
    (hN₁ : (LinearMap.ker (T₁ : E →ₗ[ℝ] F)).map (j : E →ₗ[ℝ] V) = N₁)
    (e : N₀ ≃ₗ[ℝ] N₁)
    (he : ∀ v : LinearMap.ker (T₀ : E →ₗ[ℝ] F),
      (e (kerEquivOfMap T₀ j hj hN₀ v) : V) = j ((v : E) - N v)) :
    surjRay hs₁ j hj hN₁ (o ⟨T₁, h₁⟩) =
      Module.Ray.map (maxPowEquiv e) (surjRay hs₀ j hj hN₀ (o ⟨T₀, h₀⟩)) := by
  let T : unitInterval → E →L[ℝ] F := fun q =>
    T₀ ∘L (ContinuousLinearMap.id ℝ E + (q : ℝ) • N)
  have hTapp : ∀ q w, T q w = T₀ (w + (q : ℝ) • N w) := fun q w => rfl
  have hTc : Continuous T :=
    continuous_const.clm_comp (continuous_const.add (continuous_subtype_val.smul continuous_const))
  have hTC : ∀ q, T q ∈ C := fun q => by
    have h := hconv h₀ h₁ (sub_nonneg.2 q.2.2) q.2.1 (sub_add_cancel 1 (q : ℝ))
    have heq : (1 - (q : ℝ)) • T₀ + (q : ℝ) • T₁ = T q := by
      refine ContinuousLinearMap.ext fun w => ?_
      change (1 - (q : ℝ)) • T₀ w + (q : ℝ) • T₁ w = T₀ (w + (q : ℝ) • N w)
      rw [hT, map_add, map_add, map_smul]
      module
    rwa [heq] at h
  have hTs : ∀ q, Function.Surjective (T q) := fun q y => by
    obtain ⟨v, hv⟩ := hs₀ y
    refine ⟨v - (q : ℝ) • N v, ?_⟩
    rw [hTapp, map_sub, map_smul, hNN, smul_zero, sub_zero, sub_add_cancel, hv]
  let J : unitInterval → E →L[ℝ] E := fun q => ContinuousLinearMap.id ℝ E - (q : ℝ) • N
  have hJ : Continuous fun p : unitInterval × E => J p.1 p.2 := by
    change Continuous fun p : unitInterval × E => p.2 - (p.1 : ℝ) • N p.2
    exact continuous_snd.sub ((continuous_subtype_val.comp continuous_fst).smul
      (N.continuous.comp continuous_snd))
  have hT0 : T 0 = T₀ := by
    refine ContinuousLinearMap.ext fun w => ?_
    rw [hTapp, Set.Icc.coe_zero, zero_smul, add_zero]
  have hT1 : T 1 = T₁ := by
    refine ContinuousLinearMap.ext fun w => ?_
    rw [hTapp, Set.Icc.coe_one, one_smul, hT]
  have hmem0 : ∀ v : LinearMap.ker (T 0 : E →ₗ[ℝ] F), T₀ (v : E) = 0 := fun v => by
    exact (DFunLike.congr_fun hT0 (v : E)).symm.trans (LinearMap.mem_ker.1 v.2)
  let κ : ∀ q, LinearMap.ker (T 0 : E →ₗ[ℝ] F) ≃ₗ[ℝ] LinearMap.ker (T q : E →ₗ[ℝ] F) := fun q =>
    { toFun := fun v => ⟨(v : E) - (q : ℝ) • N v, by
        rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hTapp, map_sub, map_smul, hNN,
          smul_zero, sub_zero, sub_add_cancel]
        exact hmem0 v⟩
      map_add' := fun v w => Subtype.ext (by
        change ((v : E) + (w : E)) - (q : ℝ) • N ((v : E) + (w : E)) =
          ((v : E) - (q : ℝ) • N v) + ((w : E) - (q : ℝ) • N w)
        rw [map_add]; module)
      map_smul' := fun c v => Subtype.ext (by
        change c • (v : E) - (q : ℝ) • N (c • (v : E)) = c • ((v : E) - (q : ℝ) • N v)
        rw [map_smul]; module)
      invFun := fun w => ⟨(w : E) + (q : ℝ) • N w, by
        rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hT0]
        exact LinearMap.mem_ker.1 w.2⟩
      left_inv := fun v => Subtype.ext (by
        change ((v : E) - (q : ℝ) • N v) + (q : ℝ) • N ((v : E) - (q : ℝ) • N v) = (v : E)
        rw [map_sub, map_smul, hNN, smul_zero, sub_zero, sub_add_cancel])
      right_inv := fun w => Subtype.ext (by
        change ((w : E) + (q : ℝ) • N w) - (q : ℝ) • N ((w : E) + (q : ℝ) • N w) = (w : E)
        rw [map_add, map_smul, hNN, smul_zero, add_zero, add_sub_cancel_right]) }
  have hκ : ∀ q v, (κ q v : E) = J q v := fun q v => rfl
  have hκ₀ : ∀ v, (κ 0 v : E) = v := fun v => by
    change (v : E) - ((0 : unitInterval) : ℝ) • N v = v
    rw [Set.Icc.coe_zero, zero_smul, sub_zero]
  have aux : ∀ (A₀ A₁ : E →L[ℝ] F) (hA₀ : T 0 = A₀) (hA₁ : T 1 = A₁) (h₀ : A₀ ∈ C)
      (h₁ : A₁ ∈ C) (hs₀ : Function.Surjective A₀) (hs₁ : Function.Surjective A₁)
      (hN₀ : (LinearMap.ker (A₀ : E →ₗ[ℝ] F)).map (j : E →ₗ[ℝ] V) = N₀)
      (hN₁ : (LinearMap.ker (A₁ : E →ₗ[ℝ] F)).map (j : E →ₗ[ℝ] V) = N₁)
      (_ : ∀ v : LinearMap.ker (A₀ : E →ₗ[ℝ] F),
        (e (kerEquivOfMap A₀ j hj hN₀ v) : V) = j ((v : E) - N v)),
      surjRay hs₁ j hj hN₁ (o ⟨A₁, h₁⟩) =
        Module.Ray.map (maxPowEquiv e) (surjRay hs₀ j hj hN₀ (o ⟨A₀, h₀⟩)) := by
    intro A₀ A₁ hA₀ hA₁
    subst hA₀ hA₁
    intro h₀ h₁ hs₀ hs₁ hN₀ hN₁ he'
    refine surjRay_of_family o T hTc hTC hTs J hJ 0 κ hκ hκ₀ 1 j hj hN₀ hN₁ e fun v => ?_
    rw [he' v]
    change j ((v : E) - N v) = j ((v : E) - ((1 : unitInterval) : ℝ) • N v)
    rw [Set.Icc.coe_one, one_smul]
  exact aux T₀ T₁ hT0 hT1 h₀ h₁ hs₀ hs₁ hN₀ hN₁ he

/-- **`ker T₀ ≅ ker T₁`, `v ↦ v − N v`**, for `T₁ = T₀ (1 + N)` and `N² = 0`. -/
def shearKerEquiv {T₀ T₁ : E →L[ℝ] F} (N : E →L[ℝ] E) (hNN : ∀ w, N (N w) = 0)
    (hT : ∀ w, T₁ w = T₀ (w + N w)) :
    LinearMap.ker (T₀ : E →ₗ[ℝ] F) ≃ₗ[ℝ] LinearMap.ker (T₁ : E →ₗ[ℝ] F) where
  toFun v := ⟨(v : E) - N v, by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hT, map_sub, hNN, sub_zero,
      sub_add_cancel]
    exact LinearMap.mem_ker.1 v.2⟩
  map_add' v w := Subtype.ext (by
    change ((v : E) + (w : E)) - N ((v : E) + (w : E)) = ((v : E) - N v) + ((w : E) - N w)
    rw [map_add]; abel)
  map_smul' c v := Subtype.ext (by
    change c • (v : E) - N (c • (v : E)) = c • ((v : E) - N v)
    rw [map_smul, smul_sub])
  invFun w := ⟨(w : E) + N w, by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ← hT]
    exact LinearMap.mem_ker.1 w.2⟩
  left_inv v := Subtype.ext (by
    change ((v : E) - N v) + N ((v : E) - N v) = (v : E)
    rw [map_sub, hNN, sub_zero, sub_add_cancel])
  right_inv w := Subtype.ext (by
    change ((w : E) + N w) - N ((w : E) + N w) = (w : E)
    rw [map_add, hNN, add_zero, add_sub_cancel_right])

omit [CompleteSpace E] [CompleteSpace F] in
/-- `shearKerEquiv` is `v ↦ v − N v`. -/
theorem coe_shearKerEquiv {T₀ T₁ : E →L[ℝ] F} (N : E →L[ℝ] E) (hNN : ∀ w, N (N w) = 0)
    (hT : ∀ w, T₁ w = T₀ (w + N w)) (v : LinearMap.ker (T₀ : E →ₗ[ℝ] F)) :
    (shearKerEquiv N hNN hT v : E) = (v : E) - N v := rfl

/-- **`j(ker T₀) ≅ j(ker T₁)`**, `j v ↦ j(v − N v)`: `shearKerEquiv` for the kernels read in `V`. -/
def shearMapEquiv {T₀ T₁ : E →L[ℝ] F} (N : E →L[ℝ] E) (hNN : ∀ w, N (N w) = 0)
    (hT : ∀ w, T₁ w = T₀ (w + N w)) (j : E →L[ℝ] V) (hj : Function.Injective j)
    {N₀ N₁ : Submodule ℝ V}
    (hN₀ : (LinearMap.ker (T₀ : E →ₗ[ℝ] F)).map (j : E →ₗ[ℝ] V) = N₀)
    (hN₁ : (LinearMap.ker (T₁ : E →ₗ[ℝ] F)).map (j : E →ₗ[ℝ] V) = N₁) : N₀ ≃ₗ[ℝ] N₁ :=
  ((kerEquivOfMap T₀ j hj hN₀).symm.trans (shearKerEquiv N hNN hT)).trans
    (kerEquivOfMap T₁ j hj hN₁)

omit [CompleteSpace E] [CompleteSpace F] in
/-- `shearMapEquiv (j v) = j (v − N v)`. -/
theorem coe_shearMapEquiv {T₀ T₁ : E →L[ℝ] F} (N : E →L[ℝ] E) (hNN : ∀ w, N (N w) = 0)
    (hT : ∀ w, T₁ w = T₀ (w + N w)) (j : E →L[ℝ] V) (hj : Function.Injective j)
    {N₀ N₁ : Submodule ℝ V}
    (hN₀ : (LinearMap.ker (T₀ : E →ₗ[ℝ] F)).map (j : E →ₗ[ℝ] V) = N₀)
    (hN₁ : (LinearMap.ker (T₁ : E →ₗ[ℝ] F)).map (j : E →ₗ[ℝ] V) = N₁)
    (v : LinearMap.ker (T₀ : E →ₗ[ℝ] F)) :
    (shearMapEquiv N hNN hT j hj hN₀ hN₁ (kerEquivOfMap T₀ j hj hN₀ v) : V) =
      j ((v : E) - N v) := by
  change (kerEquivOfMap T₁ j hj hN₁ (shearKerEquiv N hNN hT
    ((kerEquivOfMap T₀ j hj hN₀).symm (kerEquivOfMap T₀ j hj hN₀ v))) : V) = _
  rw [LinearEquiv.symm_apply_apply, coe_kerEquivOfMap]
  rfl

/-- `surjRay_comp_shear` with the isomorphism `shearMapEquiv`. -/
theorem surjRay_shearMapEquiv {C : Set (E →L[ℝ] F)} (hconv : Convex ℝ C)
    {hC : ∀ T ∈ C, T.IsFredholm} (o : LineOrientation (DetOn C hC)) {T₀ T₁ : E →L[ℝ] F}
    (h₀ : T₀ ∈ C) (h₁ : T₁ ∈ C) (hs₀ : Function.Surjective T₀) (hs₁ : Function.Surjective T₁)
    (N : E →L[ℝ] E) (hNN : ∀ w, N (N w) = 0) (hT : ∀ w, T₁ w = T₀ (w + N w))
    (j : E →L[ℝ] V) (hj : Function.Injective j) {N₀ N₁ : Submodule ℝ V}
    (hN₀ : (LinearMap.ker (T₀ : E →ₗ[ℝ] F)).map (j : E →ₗ[ℝ] V) = N₀)
    (hN₁ : (LinearMap.ker (T₁ : E →ₗ[ℝ] F)).map (j : E →ₗ[ℝ] V) = N₁) :
    surjRay hs₁ j hj hN₁ (o ⟨T₁, h₁⟩) =
      Module.Ray.map (maxPowEquiv (shearMapEquiv N hNN hT j hj hN₀ hN₁))
        (surjRay hs₀ j hj hN₀ (o ⟨T₀, h₀⟩)) :=
  surjRay_comp_shear hconv o h₀ h₁ hs₀ hs₁ N hNN hT j hj hN₀ hN₁ _
    (coe_shearMapEquiv N hNN hT j hj hN₀ hN₁)

end Family

end Polyfold
