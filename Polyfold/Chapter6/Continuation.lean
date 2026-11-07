import Polyfold.Chapter6.SubspaceBundle
import Polyfold.Chapter6.Stabilization

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.5,
pp. 222–224: the linear algebra of the **push-forward of orientations** `o₁ = φ_* o₀` along a
path, from Lemma 6.31 to the paragraph after it *(book 2017: Lemma 6.14 and after; see
`BookConcordance.md`)*.

# Continuation of orientations and the push-forward along a stabilized family

## The text, paraphrased

Along the path the kernels `L_t = ker F_t'(φ(t), 0)` form a vector bundle over `[0, 1]`, and "an
orientation of the lines `λ(L_t)` determines by continuation an orientation of all the other
lines".  For every `t` the exact sequence `E_t` (96),
`0 → ker T_t → L_t → ℝᵏ → coker T_t → 0` with `T_t = (f − s(·, t))'(φ(t))`, gives the natural
isomorphism `Φ_{E_t} : det(T_t) → λ(L_t) ⊗ λ*(ℝᵏ)`.  An orientation of `det(T_0)` is carried by
`Φ_{E_0}` to `λ(L_0) ⊗ λ*(ℝᵏ)`, continued to `λ(L_1) ⊗ λ*(ℝᵏ)` and carried back by `Φ_{E_1}⁻¹`
to `det(T_1)`.

## What is formalized

* `SubspaceFamily.cont Λ q₀ q₁`: over a simply connected, locally path-connected base `Q`, the
  continuation of a ray of `λ(L_{q₀})` to `λ(L_{q₁})` (the value at `q₁` of the orientation through
  it); `cont_eq`, `cont_self`, `cont_trans`, `contEquiv`, `cont_comp`
  (pull-back along a map of bases) and `cont_eq_transport` (continuation along a path).
* `detEquivOfSurjective`: `det(T) ≅ λ(ker T)` for a surjective `T` (the factor `λ*({0})`).
* `stabRayEquiv hT hφ ι`: the rays of `det(T)` and of `λ(L)`, for a stabilization `T_φ = T ⊕ φ`
  onto and an identification `ι : ker T_φ ≅ L` (Lemma 6.31 is Lemma 6.14, `stabSeq`; the map is
  `Φ_{E}` followed by `λ*(ℝᵏ) ≅ λ*({0})`, i.e. `stabIota`, Definition 6.16 / formula (94)).
* `propagate`: the push-forward `Ray(det T₀) ≃ Ray(det T₁)` along a family `Λ` with stabilized end
  points; `propagate_trans`, `propagate_self`, `propagate_comp`.

## Reading

The text's continuation is along `[0, 1]`; here it is over any simply connected, locally
path-connected base, so that one statement covers the paths of Theorem 6.35 and the squares of
Lemmas 6.33–6.34.  The text writes the target as `λ(L_t) ⊗ λ*(ℝᵏ)`; `stabIota` contains the fixed
identification `λ*(ℝᵏ) ≅ λ*({0})` of formula (94) (`(e₁ ∧ … ∧ e_k)* ↦ 1*`), so the line used is
`det(T ⊕ φ) ≅ λ(ker(T ⊕ φ))`; the same identification at both ends cancels in `φ_*`.
-/

open Module TensorProduct Bundle Topology Set

noncomputable section

namespace Polyfold

/-! ### Continuation over a simply connected base -/

namespace SubspaceFamily

variable {Q : Type*} [TopologicalSpace Q] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  (Λ : SubspaceFamily Q W)

section

variable [SimplyConnectedSpace Q] [LocallyPathConnectedSpace Q]

/-- **Continuation of orientations**: the value at `q₁` of the orientation of `λ(L)` through the
ray `r` of `λ(L_{q₀})`. -/
def cont (q₀ q₁ : Q) (r : Module.Ray ℝ (Λ.det q₀)) : Module.Ray ℝ (Λ.det q₁) :=
  (exists_lineOrientation_apply_eq (L := Λ.det) q₀ r).choose q₁

/-- The continuation is the value of **any** orientation through the ray. -/
theorem cont_eq (o : LineOrientation Λ.det) (q₀ q₁ : Q) :
    Λ.cont q₀ q₁ (o q₀) = o q₁ := by
  have h := LineOrientation.eq_of_apply_eq q₀
    (exists_lineOrientation_apply_eq (L := Λ.det) q₀ (o q₀)).choose_spec
  exact congrArg (fun o : LineOrientation Λ.det => o q₁) h

/-- Continuing from a point to itself does nothing. -/
theorem cont_self (q : Q) (r : Module.Ray ℝ (Λ.det q)) : Λ.cont q q r = r :=
  (exists_lineOrientation_apply_eq (L := Λ.det) q r).choose_spec

/-- Continuation is transitive: continuing through `q₁` is continuing directly. -/
theorem cont_trans (q₀ q₁ q₂ : Q) (r : Module.Ray ℝ (Λ.det q₀)) :
    Λ.cont q₁ q₂ (Λ.cont q₀ q₁ r) = Λ.cont q₀ q₂ r := by
  obtain ⟨o, rfl⟩ := exists_lineOrientation_apply_eq (L := Λ.det) q₀ r
  rw [Λ.cont_eq o q₀ q₁, Λ.cont_eq o q₁ q₂, Λ.cont_eq o q₀ q₂]

/-- The continuation as a bijection of the two rays at `q₀` with the two at `q₁`. -/
def contEquiv (q₀ q₁ : Q) : Module.Ray ℝ (Λ.det q₀) ≃ Module.Ray ℝ (Λ.det q₁) where
  toFun := Λ.cont q₀ q₁
  invFun := Λ.cont q₁ q₀
  left_inv r := by rw [cont_trans, cont_self]
  right_inv r := by rw [cont_trans, cont_self]

/-- `contEquiv` is the continuation. -/
@[simp] theorem contEquiv_apply (q₀ q₁ : Q) (r : Module.Ray ℝ (Λ.det q₀)) :
    Λ.contEquiv q₀ q₁ r = Λ.cont q₀ q₁ r := rfl

/-- **Continuation and pull-back**: continuing in the pulled-back family `Λ ∘ g` is continuing
in `Λ` between the images. -/
theorem cont_comp {Q' : Type*} [TopologicalSpace Q'] [SimplyConnectedSpace Q']
    [LocallyPathConnectedSpace Q'] (g : C(Q', Q)) (q₀ q₁ : Q')
    (r : Module.Ray ℝ (Λ.det (g q₀))) :
    (Λ.comp g).cont q₀ q₁ r = Λ.cont (g q₀) (g q₁) r := by
  obtain ⟨o, rfl⟩ := exists_lineOrientation_apply_eq (L := Λ.det) (g q₀) r
  exact ((Λ.comp g).cont_eq (o.comp g) q₀ q₁).trans (Λ.cont_eq o (g q₀) (g q₁)).symm

open unitInterval in
/-- **Continuation along a path** (`SubspaceFamily.transport`) is continuation between its end
points. -/
theorem cont_eq_transport (γ : C(I, Q)) (r : Module.Ray ℝ (Λ.det (γ 0))) :
    (Λ.comp γ).transport r = Λ.cont (γ 0) (γ 1) r := by
  obtain ⟨o, rfl⟩ := exists_lineOrientation_apply_eq (L := Λ.det) (γ 0) r
  exact (Λ.transport_comp o γ).trans (Λ.cont_eq o (γ 0) (γ 1)).symm

end

end SubspaceFamily

/-! ### The stabilized end points -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- The cokernel of a surjective operator is `{0}`. -/
theorem subsingleton_coker_of_surjective {T : E →L[ℝ] F} (hT : Function.Surjective T) :
    Subsingleton (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) :=
  Submodule.Quotient.subsingleton_iff.2 (LinearMap.range_eq_top.2 hT)

omit [CompleteSpace E] [CompleteSpace F] in
/-- The cokernel of a surjective operator is zero-dimensional. -/
theorem finrank_coker_of_surjective {T : E →L[ℝ] F} (hT : Function.Surjective T) :
    finrank ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) = 0 :=
  have := subsingleton_coker_of_surjective hT
  finrank_zero_of_subsingleton

/-- The empty wedge `1 ∈ λ(M)` of a zero-dimensional space `M`. -/
def emptyWedge (M : Type*) [AddCommGroup M] [Module ℝ M] (h : finrank ℝ M = 0) : maxPow M :=
  wedge (Fin.elim0 : Fin 0 → M) h.symm

/-- The empty wedge of a zero-dimensional, finite-dimensional space is not zero. -/
theorem emptyWedge_ne_zero (M : Type*) [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]
    (h : finrank ℝ M = 0) : emptyWedge M h ≠ 0 :=
  (wedge_ne_zero_iff _).2 linearIndependent_empty_type

omit [CompleteSpace E] [CompleteSpace F] in
/-- Evaluation on the empty wedge, `λ*(coker T) → ℝ`, is bijective for a surjective `T`. -/
theorem evalEmptyWedge_bijective {T : E →L[ℝ] F} (hT : Function.Surjective T) :
    Function.Bijective fun ξ : maxPowDual (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) =>
      ξ (emptyWedge _ (finrank_coker_of_surjective hT)) := by
  have := subsingleton_coker_of_surjective hT
  have hne := emptyWedge_ne_zero _ (finrank_coker_of_surjective hT)
  refine ⟨fun ξ ξ' h => dual_ext_of_ne_zero finrank_maxPow hne h, fun c =>
    ⟨c • dualVec (emptyWedge _ (finrank_coker_of_surjective hT)), ?_⟩⟩
  dsimp only
  rw [LinearMap.smul_apply, dualVec_self finrank_maxPow hne, smul_eq_mul, mul_one]

/-- **`det(T) ≅ λ(ker T)` for a surjective `T`**: the cokernel is `{0}`, and `λ*({0}) ≅ ℝ` by
evaluation on the empty wedge `1`. -/
def detEquivOfSurjective {T : E →L[ℝ] F} (hT : Function.Surjective T) :
    fredholmDet T ≃ₗ[ℝ] maxPow (LinearMap.ker (T : E →ₗ[ℝ] F)) :=
  (TensorProduct.congr (LinearEquiv.refl ℝ _)
    (LinearEquiv.ofBijective
      ((Module.Dual.eval ℝ _ (emptyWedge _ (finrank_coker_of_surjective hT))) :
        maxPowDual (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) →ₗ[ℝ] ℝ)
      (evalEmptyWedge_bijective hT))).trans (TensorProduct.rid ℝ _)

omit [CompleteSpace E] [CompleteSpace F] in
/-- `det(T) ≅ λ(ker T)` on a pure tensor: `w ⊗ ξ ↦ ξ(1) w`. -/
theorem detEquivOfSurjective_tmul {T : E →L[ℝ] F} (hT : Function.Surjective T)
    (w : maxPow (LinearMap.ker (T : E →ₗ[ℝ] F)))
    (ξ : maxPowDual (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F))) :
    detEquivOfSurjective hT (w ⊗ₜ ξ) = ξ (emptyWedge _ (finrank_coker_of_surjective hT)) • w := by
  rw [detEquivOfSurjective, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    TensorProduct.rid_tmul]
  rfl

variable {k : ℕ} {T : E →L[ℝ] F} {φ : (Fin k → ℝ) →L[ℝ] F}

/-- **The rays of `det(T)` and of `λ(L)`** for a stabilization `T ⊕ φ` onto and an identification
`ι : ker(T ⊕ φ) ≅ L`: `ι_φ` (`stabIota`, `Φ_E` of Lemma 6.14 with formula (94)), then
`det(T ⊕ φ) ≅ λ(ker(T ⊕ φ))`, then `λ(ι)`. -/
def stabRayEquiv (hT : T.IsFredholm) (hφ : Function.Surjective (T.coprod φ))
    {W : Type*} [AddCommGroup W] [Module ℝ W] {L : Submodule ℝ W} [FiniteDimensional ℝ L]
    (ι : LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) : E × (Fin k → ℝ) →ₗ[ℝ] F)
      ≃ₗ[ℝ] L) :
    Module.Ray ℝ (fredholmDet T) ≃ Module.Ray ℝ (maxPow L) :=
  ((Module.Ray.map (LinearEquiv.ofBijective (stabIota hT hφ) (stabIota_bijective hT hφ))).trans
    (Module.Ray.map (detEquivOfSurjective hφ))).trans (Module.Ray.map (maxPowEquiv ι))

/-! ### The push-forward along a stabilized family -/

section Propagate

variable {Q : Type*} [TopologicalSpace Q] [SimplyConnectedSpace Q] [LocallyPathConnectedSpace Q]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (Λ : SubspaceFamily Q W)
  {E₁ F₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [CompleteSpace F₁]
  {k₁ : ℕ} {T₁ : E₁ →L[ℝ] F₁} {φ₁ : (Fin k₁ → ℝ) →L[ℝ] F₁}

/-- **The push-forward `φ_*`** (p. 224) along a family `Λ` of kernels with stabilized end points:
`Ray(det T₀) → Ray(λ(L_{q₀})) → Ray(λ(L_{q₁})) → Ray(det T₁)` by `Φ_{E_0}`, continuation and
`Φ_{E_1}⁻¹`. -/
def propagate (q₀ q₁ : Q) (hT : T.IsFredholm) (hφ : Function.Surjective (T.coprod φ))
    (ι : LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) : E × (Fin k → ℝ) →ₗ[ℝ] F)
      ≃ₗ[ℝ] Λ.L q₀)
    (hT₁ : T₁.IsFredholm) (hφ₁ : Function.Surjective (T₁.coprod φ₁))
    (ι₁ : LinearMap.ker ((T₁.coprod φ₁ : E₁ × (Fin k₁ → ℝ) →L[ℝ] F₁) :
      E₁ × (Fin k₁ → ℝ) →ₗ[ℝ] F₁) ≃ₗ[ℝ] Λ.L q₁) :
    Module.Ray ℝ (fredholmDet T) ≃ Module.Ray ℝ (fredholmDet T₁) :=
  ((stabRayEquiv hT hφ ι).trans (Λ.contEquiv q₀ q₁)).trans (stabRayEquiv hT₁ hφ₁ ι₁).symm

omit [CompleteSpace E] [CompleteSpace F] in
/-- The push-forward along a constant family is the identity. -/
theorem propagate_self (q : Q) (hT : T.IsFredholm) (hφ : Function.Surjective (T.coprod φ))
    (ι : LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) : E × (Fin k → ℝ) →ₗ[ℝ] F)
      ≃ₗ[ℝ] Λ.L q) (r : Module.Ray ℝ (fredholmDet T)) :
    propagate Λ q q hT hφ ι hT hφ ι r = r := by
  exact (congrArg (stabRayEquiv hT hφ ι).symm (Λ.cont_self q (stabRayEquiv hT hφ ι r))).trans
    ((stabRayEquiv hT hφ ι).symm_apply_apply r)

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace E₁] [CompleteSpace F₁] in
/-- **The push-forward is compatible with concatenation**: through an intermediate point with
any stabilized data there. -/
theorem propagate_trans {E₂ F₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    [CompleteSpace E₂] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [CompleteSpace F₂]
    {k₂ : ℕ} {T₂ : E₂ →L[ℝ] F₂} {φ₂ : (Fin k₂ → ℝ) →L[ℝ] F₂} (q₀ q₁ q₂ : Q)
    (hT : T.IsFredholm) (hφ : Function.Surjective (T.coprod φ))
    (ι : LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) : E × (Fin k → ℝ) →ₗ[ℝ] F)
      ≃ₗ[ℝ] Λ.L q₀)
    (hT₁ : T₁.IsFredholm) (hφ₁ : Function.Surjective (T₁.coprod φ₁))
    (ι₁ : LinearMap.ker ((T₁.coprod φ₁ : E₁ × (Fin k₁ → ℝ) →L[ℝ] F₁) :
      E₁ × (Fin k₁ → ℝ) →ₗ[ℝ] F₁) ≃ₗ[ℝ] Λ.L q₁)
    (hT₂ : T₂.IsFredholm) (hφ₂ : Function.Surjective (T₂.coprod φ₂))
    (ι₂ : LinearMap.ker ((T₂.coprod φ₂ : E₂ × (Fin k₂ → ℝ) →L[ℝ] F₂) :
      E₂ × (Fin k₂ → ℝ) →ₗ[ℝ] F₂) ≃ₗ[ℝ] Λ.L q₂) (r : Module.Ray ℝ (fredholmDet T)) :
    propagate Λ q₁ q₂ hT₁ hφ₁ ι₁ hT₂ hφ₂ ι₂ (propagate Λ q₀ q₁ hT hφ ι hT₁ hφ₁ ι₁ r) =
      propagate Λ q₀ q₂ hT hφ ι hT₂ hφ₂ ι₂ r := by
  exact (congrArg (fun x : Module.Ray ℝ (Λ.det q₁) => (stabRayEquiv hT₂ hφ₂ ι₂).symm
      (Λ.cont q₁ q₂ x)) ((stabRayEquiv hT₁ hφ₁ ι₁).apply_symm_apply _)).trans
    (congrArg (stabRayEquiv hT₂ hφ₂ ι₂).symm (Λ.cont_trans q₀ q₁ q₂ (stabRayEquiv hT hφ ι r)))

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace E₁] [CompleteSpace F₁] in
/-- **The push-forward and pull-back of the family**: along `Λ ∘ g` it is the push-forward
along `Λ` between the images. -/
theorem propagate_comp {Q' : Type*} [TopologicalSpace Q'] [SimplyConnectedSpace Q']
    [LocallyPathConnectedSpace Q'] (g : C(Q', Q)) (q₀ q₁ : Q')
    (hT : T.IsFredholm) (hφ : Function.Surjective (T.coprod φ))
    (ι : LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) : E × (Fin k → ℝ) →ₗ[ℝ] F)
      ≃ₗ[ℝ] Λ.L (g q₀))
    (hT₁ : T₁.IsFredholm) (hφ₁ : Function.Surjective (T₁.coprod φ₁))
    (ι₁ : LinearMap.ker ((T₁.coprod φ₁ : E₁ × (Fin k₁ → ℝ) →L[ℝ] F₁) :
      E₁ × (Fin k₁ → ℝ) →ₗ[ℝ] F₁) ≃ₗ[ℝ] Λ.L (g q₁)) (r : Module.Ray ℝ (fredholmDet T)) :
    propagate (Λ.comp g) q₀ q₁ hT hφ ι hT₁ hφ₁ ι₁ r =
      propagate Λ (g q₀) (g q₁) hT hφ ι hT₁ hφ₁ ι₁ r := by
  exact congrArg (stabRayEquiv hT₁ hφ₁ ι₁).symm (Λ.cont_comp g q₀ q₁ (stabRayEquiv hT hφ ι r))

end Propagate

end Polyfold
