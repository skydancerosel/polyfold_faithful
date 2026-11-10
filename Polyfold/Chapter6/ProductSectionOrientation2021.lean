import Polyfold.Chapter6.OrientationConvention2021
import Polyfold.Chapter6.PushTransfer
import Polyfold.Chapter6.PerturbedOrientation

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, p. 276:
**Remark 6.6.19** (preprint Remark 6.42, p. 230) beyond a point: the compatibility of the
orientation `h ↦ h̃ = e ∧ h` of `f̂(x, t) = f(x) + s(x, t)` with the choices made in the
construction of the orientation (the stabilizations of Lemma 6.4.14 and the push-forwards of
§6.6).

# The product orientation and the stabilization isomorphism

## The text, paraphrased

(2021, Remark 6.6.19) For an oriented sc-Fredholm section `(f, o)` of `P : Y → X` and an
sc⁺-section `s` of `Y → X × [0, 1]`, `f̂(x, t) = f(x) + s(x, t)` has a natural orientation: for
`L ∈ Lin(f, x)` oriented by `h = (a₁ ∧ … ∧ aₙ) ⊗ (b₁ ∧ … ∧ b_l)*`, `L̃(a, b) = La` is oriented by
`h̃ = (e ∧ a₁ ∧ … ∧ aₙ) ⊗ (b₁ ∧ … ∧ b_l)*`.  "This convention is compatible with the choices which
have to be made during the construction."

## What is formalized here

* `wedgeExtLeft`: `λ(K) → λ(K')`, `w ↦ ℓ₁ ∧ … ∧ ℓ_d ∧ M(w)` (the new vectors **first**, as in the
  2021 convention), and its relation to `wedgeExt` (`AddSections.lean`).
* The stabilization of the extended operator `L̃ = L ⊕ 0 : E × ℝ → F` by the same
  `φ : ℝᵏ → F`: `ker(L̃ ⊕ φ) = ker(L ⊕ φ) × ℝ` (`extStabJ`, `extStabE`, `extStabEquiv`,
  `finrank_extStabKer`, `surjective_coprod_extOp`).
* **The stabilization isomorphism commutes with `h ↦ e ∧ h`**
  (`detEquiv_stabIota_extDetFirst`, `stabRayEquiv_extDetFirst`): reading `e ∧ h` in
  `λ(ker(L̃ ⊕ φ))` through `ι_φ` (Lemma 6.4.14, Proposition 6.4.15) is `e ∧ (reading of `h` in
  `λ(ker(L ⊕ φ)))`, **with no sign**.  This is the computation behind the sentence quoted above:
  the push-forward of §6.6 reads an orientation in `λ(ker(L ⊕ φ))` (`stabRayEquiv`, `orRay`),
  continues it along the stabilized kernels and reads it back, and `e ∧ ·` is compatible with
  each of the three steps.

## Reading

As in `ProductOrientation.lean`: `X × [0, 1]` is read as `ℝ¹ × X` (decision D2), the extra
factor is placed second in `E × ℝ¹`, and `e = (0, 1)`.
-/

open Module TensorProduct Bundle Topology Set Filter

noncomputable section

namespace Polyfold

universe u v

/-! ### `w ↦ ℓ₁ ∧ … ∧ ℓ_d ∧ M(w)` -/

section WedgeExtLeft

variable {K K' : Type*} [AddCommGroup K] [Module ℝ K] [AddCommGroup K'] [Module ℝ K']

/-- **`λ(K) → λ(K')`, `w ↦ ℓ₁ ∧ … ∧ ℓ_d ∧ M(w)`** (the new vectors first), for
`d + dim K = dim K'`. -/
def wedgeExtLeft (M : K →ₗ[ℝ] K') {d : ℕ} (ℓ : Fin d → K')
    (h : d + finrank ℝ K = finrank ℝ K') : maxPow K →ₗ[ℝ] maxPow K' :=
  (LinearEquiv.ofEq _ _ (by rw [h])).toLinearMap ∘ₗ
    exteriorPower.alternatingMapLinearEquiv
      ((appendRightMap (exteriorPower.ιMulti ℝ (d + finrank ℝ K)) ℓ).compLinearMap M)

/-- `wedgeExtLeft` on a wedge: `ℓ₁ ∧ … ∧ ℓ_d ∧ M(b₁) ∧ … ∧ M(bₙ)`. -/
theorem wedgeExtLeft_wedge (M : K →ₗ[ℝ] K') {d : ℕ} (ℓ : Fin d → K')
    (h : d + finrank ℝ K = finrank ℝ K') {n : ℕ} (b : Fin n → K) (hb : n = finrank ℝ K) :
    wedgeExtLeft M ℓ h (wedge b hb) = wedge (Fin.append ℓ (M ∘ b)) (by omega) := by
  subst hb
  apply Subtype.ext
  rw [wedge_eq_ιMulti]
  simp only [wedgeExtLeft, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, LinearEquiv.coe_ofEq_apply,
    AlternatingMap.compLinearMap_apply, coe_wedge]
  rfl

/-- **`M(w) ∧ e = (−1)^{dim K} e ∧ M(w)`**: `wedgeExt` with one vector is `(−1)^{dim K}` times
`wedgeExtLeft` (`wedge_snoc_eq_smul_wedge_cons`). -/
theorem wedgeExt_single_eq_smul_wedgeExtLeft [FiniteDimensional ℝ K] (M : K →ₗ[ℝ] K') (e : K')
    (h : finrank ℝ K + 1 = finrank ℝ K') (h' : 1 + finrank ℝ K = finrank ℝ K') :
    wedgeExt M ![e] h = (-1 : ℝ) ^ finrank ℝ K • wedgeExtLeft M ![e] h' := by
  apply maxPow_linearMap_ext (Module.finBasis ℝ K) rfl
  rw [LinearMap.smul_apply, wedgeExt_wedge, wedgeExtLeft_wedge, Fin.append_right_eq_snoc,
    Fin.append_left_eq_cons]
  rw [wedge_snoc_eq_smul_wedge_cons _ _ h]
  congr 1
  exact (wedge_cast _ _ _).symm

/-- A family `e, u₁, …, uₙ` is linearly independent when `u` is, `p(u) = 0` and `p(e) = e₁`
(`linearIndependent_fin_append_of_single` with the single vector first). -/
theorem linearIndependent_single_append (p : K →ₗ[ℝ] Fin 1 → ℝ) {n : ℕ} {u : Fin n → K}
    (hu : LinearIndependent ℝ u) (hpu : ∀ i, p (u i) = 0) {e : K} (he : p e = Pi.single 0 1) :
    LinearIndependent ℝ (Fin.append ![e] u) := by
  have h := linearIndependent_fin_append_of_single p hu hpu (ℓ := ![e])
    (fun j => by fin_cases j; exact he)
  rw [Fin.append_right_eq_snoc, linearIndependent_finSnoc] at h
  rw [Fin.append_left_eq_cons]
  exact (linearIndependent_finCons.2 h).comp _ (Fin.cast_injective _)

end WedgeExtLeft

/-! ### The stabilization of `L̃ = L ⊕ 0` -/

section ExtStab

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {T : E →L[ℝ] F} {k : ℕ}
  {φ : (Fin k → ℝ) →L[ℝ] F}

omit [CompleteSpace E] [CompleteSpace F] in
/-- **`ker(L ⊕ φ) → ker(L̃ ⊕ φ)`, `(v, λ) ↦ ((v, 0), λ)`.** -/
def extStabJ (T : E →L[ℝ] F) (φ : (Fin k → ℝ) →L[ℝ] F) :
    LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) : E × (Fin k → ℝ) →ₗ[ℝ] F) →ₗ[ℝ]
      LinearMap.ker (((extOp T).coprod φ : (E × (Fin 1 → ℝ)) × (Fin k → ℝ) →L[ℝ] F) :
        (E × (Fin 1 → ℝ)) × (Fin k → ℝ) →ₗ[ℝ] F) :=
  LinearMap.codRestrict _
    ((LinearMap.inl ℝ E (Fin 1 → ℝ)).prodMap (LinearMap.id : (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ)) ∘ₗ
      (LinearMap.ker _).subtype)
    (fun x => by
      refine mem_ker_coprod.2 ?_
      have := mem_ker_coprod.1 x.2
      simpa using this)

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem coe_extStabJ
    (x : LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) : E × (Fin k → ℝ) →ₗ[ℝ] F)) :
    (extStabJ T φ x : (E × (Fin 1 → ℝ)) × (Fin k → ℝ)) =
      (((x : E × (Fin k → ℝ)).1, 0), (x : E × (Fin k → ℝ)).2) := rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- `extStabJ` is injective. -/
theorem extStabJ_injective : Function.Injective (extStabJ T φ) := fun x y h => by
  apply Subtype.ext
  have h' := congrArg Subtype.val h
  rw [coe_extStabJ, coe_extStabJ, Prod.mk.injEq, Prod.mk.injEq] at h'
  exact Prod.ext h'.1.1 h'.2

omit [CompleteSpace E] [CompleteSpace F] in
/-- **`ê = ((0, 1), 0) ∈ ker(L̃ ⊕ φ)`.** -/
def extStabE (T : E →L[ℝ] F) (φ : (Fin k → ℝ) →L[ℝ] F) :
    LinearMap.ker (((extOp T).coprod φ : (E × (Fin 1 → ℝ)) × (Fin k → ℝ) →L[ℝ] F) :
      (E × (Fin 1 → ℝ)) × (Fin k → ℝ) →ₗ[ℝ] F) :=
  ⟨((0, fun _ => 1), 0), mem_ker_coprod.2 (by simp)⟩

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem coe_extStabE :
    (extStabE T φ : (E × (Fin 1 → ℝ)) × (Fin k → ℝ)) = ((0, fun _ => 1), 0) := rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- The `ℝ¹`-coordinate on `ker(L̃ ⊕ φ)`. -/
def extStabPi (T : E →L[ℝ] F) (φ : (Fin k → ℝ) →L[ℝ] F) :
    LinearMap.ker (((extOp T).coprod φ : (E × (Fin 1 → ℝ)) × (Fin k → ℝ) →L[ℝ] F) :
      (E × (Fin 1 → ℝ)) × (Fin k → ℝ) →ₗ[ℝ] F) →ₗ[ℝ] (Fin 1 → ℝ) :=
  LinearMap.snd ℝ E (Fin 1 → ℝ) ∘ₗ LinearMap.fst ℝ (E × (Fin 1 → ℝ)) (Fin k → ℝ) ∘ₗ
    (LinearMap.ker _).subtype

omit [CompleteSpace E] [CompleteSpace F] in
theorem extStabPi_extStabJ
    (x : LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) : E × (Fin k → ℝ) →ₗ[ℝ] F)) :
    extStabPi T φ (extStabJ T φ x) = 0 := rfl

omit [CompleteSpace E] [CompleteSpace F] in
theorem extStabPi_extStabE : extStabPi T φ (extStabE T φ) = Pi.single 0 1 := by
  funext i
  fin_cases i
  simp [extStabPi]

omit [CompleteSpace E] [CompleteSpace F] in
/-- **`ker(L̃ ⊕ φ) = ker(L ⊕ φ) × ℝ`.** -/
def extStabEquiv (T : E →L[ℝ] F) (φ : (Fin k → ℝ) →L[ℝ] F) :
    ((LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) : E × (Fin k → ℝ) →ₗ[ℝ] F)) ×
        (Fin 1 → ℝ)) ≃ₗ[ℝ]
      LinearMap.ker (((extOp T).coprod φ : (E × (Fin 1 → ℝ)) × (Fin k → ℝ) →L[ℝ] F) :
        (E × (Fin 1 → ℝ)) × (Fin k → ℝ) →ₗ[ℝ] F) where
  toFun w := ⟨(((w.1 : E × (Fin k → ℝ)).1, w.2), (w.1 : E × (Fin k → ℝ)).2),
    mem_ker_coprod.2 (by have := mem_ker_coprod.1 w.1.2; simpa [extOp_apply] using this)⟩
  invFun y := (⟨((y : (E × (Fin 1 → ℝ)) × (Fin k → ℝ)).1.1,
      (y : (E × (Fin 1 → ℝ)) × (Fin k → ℝ)).2),
    mem_ker_coprod.2 (by have := mem_ker_coprod.1 y.2; simpa [extOp_apply] using this)⟩,
    (y : (E × (Fin 1 → ℝ)) × (Fin k → ℝ)).1.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

omit [CompleteSpace E] [CompleteSpace F] in
theorem finiteDimensional_extStabKer (hT : T.IsFredholm) :
    FiniteDimensional ℝ (LinearMap.ker (((extOp T).coprod φ :
      (E × (Fin 1 → ℝ)) × (Fin k → ℝ) →L[ℝ] F) : (E × (Fin 1 → ℝ)) × (Fin k → ℝ) →ₗ[ℝ] F)) := by
  have := hT.finite_ker
  have := finiteDimensional_ker_coprod (T := T) (φ := φ)
  exact LinearEquiv.finiteDimensional (extStabEquiv T φ)

omit [CompleteSpace E] [CompleteSpace F] in
/-- `dim ker(L̃ ⊕ φ) = dim ker(L ⊕ φ) + 1`. -/
theorem finrank_extStabKer (hT : T.IsFredholm) :
    finrank ℝ (LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) :
        E × (Fin k → ℝ) →ₗ[ℝ] F)) + 1 =
      finrank ℝ (LinearMap.ker (((extOp T).coprod φ :
        (E × (Fin 1 → ℝ)) × (Fin k → ℝ) →L[ℝ] F) : (E × (Fin 1 → ℝ)) × (Fin k → ℝ) →ₗ[ℝ] F)) := by
  have := hT.finite_ker
  have := finiteDimensional_ker_coprod (T := T) (φ := φ)
  rw [← LinearEquiv.finrank_eq (extStabEquiv T φ), Module.finrank_prod, Module.finrank_fin_fun]

omit [CompleteSpace E] [CompleteSpace F] in
/-- `L̃ ⊕ φ` is onto when `L ⊕ φ` is. -/
theorem surjective_coprod_extOp (hφ : Function.Surjective (T.coprod φ)) :
    Function.Surjective ((extOp T).coprod φ) := fun y => by
  obtain ⟨⟨v, μ⟩, hv⟩ := hφ y
  exact ⟨((v, 0), μ), by simpa [extOp_apply] using hv⟩

omit [CompleteSpace E] [CompleteSpace F] in
/-- **`λ(ker(L ⊕ φ)) → λ(ker(L̃ ⊕ φ))`, `w ↦ ê ∧ j(w)`** (the 2021 convention, `e` first). -/
def extStabWedge (hT : T.IsFredholm) :
    maxPow (LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) :
        E × (Fin k → ℝ) →ₗ[ℝ] F)) →ₗ[ℝ]
      maxPow (LinearMap.ker (((extOp T).coprod φ :
        (E × (Fin 1 → ℝ)) × (Fin k → ℝ) →L[ℝ] F) : (E × (Fin 1 → ℝ)) × (Fin k → ℝ) →ₗ[ℝ] F)) :=
  haveI := hT.finite_ker
  haveI := finiteDimensional_ker_coprod (T := T) (φ := φ)
  wedgeExtLeft (extStabJ T φ) ![extStabE T φ] (by rw [add_comm]; exact finrank_extStabKer hT)

omit [CompleteSpace E] [CompleteSpace F] in
/-- `extStabWedge` is an isomorphism of lines. -/
theorem extStabWedge_bijective (hT : T.IsFredholm) :
    Function.Bijective (extStabWedge (φ := φ) hT) := by
  have := hT.finite_ker
  have := finiteDimensional_ker_coprod (T := T) (φ := φ)
  have := finiteDimensional_extStabKer (φ := φ) hT
  set b := Module.finBasis ℝ (LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) :
    E × (Fin k → ℝ) →ₗ[ℝ] F))
  refine bijective_of_apply_ne_zero_of_finrank_eq_one finrank_maxPow finrank_maxPow _
    (v := wedge b rfl) ?_
  rw [extStabWedge, wedgeExtLeft_wedge]
  exact (wedge_ne_zero_iff _).2 (linearIndependent_single_append (extStabPi T φ)
    (b.linearIndependent.map' _ (LinearMap.ker_eq_bot.2 extStabJ_injective))
    (fun i => extStabPi_extStabJ _) extStabPi_extStabE)

omit [CompleteSpace E] [CompleteSpace F] in
/-- The cokernel classes of the stabilizing vectors for `L̃` are those for `L`. -/
theorem stabClass_extOp_eq (cbar : Fin (finrank ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F))) →
    Fin k → ℝ) :
    (extCoker T).symm ∘ (stabClass T φ ∘ cbar) = stabClass (extOp T) φ ∘ cbar := by
  funext i
  rfl

set_option maxHeartbeats 1600000 in
/-- **The stabilization isomorphism commutes with `h ↦ e ∧ h` at a generator**
`(a₁ ∧ … ∧ a_p) ⊗ (d̄₁ ∧ … ∧ d̄_m)*`: Proposition 6.4.15 for `L` (data `c̄`, `b̄`) and for `L̃`
(data `c̄`, `j(b̄)`, with the basis `e, (a₁, 0), …, (a_p, 0)` of `ker L̃`); the determinant in
(94) is the same. -/
theorem detEquiv_stabIota_extDetFirst_wedge (hT : T.IsFredholm)
    (hφ : Function.Surjective (T.coprod φ)) {p l : ℕ}
    (a : Basis (Fin p) ℝ (LinearMap.ker (T : E →ₗ[ℝ] F)))
    (cbar : Fin (finrank ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F))) → Fin k → ℝ)
    (hd : LinearIndependent ℝ (stabClass T φ ∘ cbar))
    (bbar : Fin l → LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) :
      E × (Fin k → ℝ) →ₗ[ℝ] F))
    (hb : LinearIndependent ℝ (Fin.append (stabJ T φ ∘ a) bbar))
    (hkl : p + l = finrank ℝ (LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) :
      E × (Fin k → ℝ) →ₗ[ℝ] F)))
    (hn : finrank ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) + l = k) :
    detEquivOfSurjective (surjective_coprod_extOp hφ)
        (stabIota (isFredholm_extOp hT) (surjective_coprod_extOp hφ)
          (extDetFirst hT (wedge a (by rw [Module.finrank_eq_card_basis a, Fintype.card_fin]) ⊗ₜ
            dualVec (wedge (stabClass T φ ∘ cbar) rfl)))) =
      extStabWedge hT (detEquivOfSurjective hφ (stabIota hT hφ
        (wedge a (by rw [Module.finrank_eq_card_basis a, Fintype.card_fin]) ⊗ₜ
          dualVec (wedge (stabClass T φ ∘ cbar) rfl)))) := by
  have := hT.finite_ker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := hT.finite_coker
  have := finiteDimensional_ker_coprod (T := T) (φ := φ)
  have := finiteDimensional_ker_extOp hT
  have := finiteDimensional_extStabKer (φ := φ) hT
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (extOp T : E × (Fin 1 → ℝ) →ₗ[ℝ] F)) :=
    (extCoker T).symm.finiteDimensional
  have hp : p = finrank ℝ (LinearMap.ker (T : E →ₗ[ℝ] F)) := by
    rw [Module.finrank_eq_card_basis a, Fintype.card_fin]
  -- the basis `e, (a₁, 0), …, (a_p, 0)` of `ker L̃`
  have hli : LinearIndependent ℝ (Fin.append ![extE T] (stabJ T 0 ∘ a)) :=
    linearIndependent_single_append (stabPi T 0)
      (a.linearIndependent.map' _ (LinearMap.ker_eq_bot.2 stabJ_injective)) (fun i => by simp)
      (stabPi_extE T)
  have h1p : 1 + p = finrank ℝ (LinearMap.ker (extOp T : E × (Fin 1 → ℝ) →ₗ[ℝ] F)) := by
    rw [← finrank_ker_extOp hT, hp, add_comm]
  let a' : Basis (Fin (1 + p)) ℝ (LinearMap.ker (extOp T : E × (Fin 1 → ℝ) →ₗ[ℝ] F)) :=
    basisOfLinearIndependentOfCardEqFinrank' _ hli (by rw [Fintype.card_fin, h1p])
  have ha' : ⇑a' = Fin.append ![extE T] (stabJ T 0 ∘ a) :=
    coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _
  have hwa' : wedge a' (by rw [Module.finrank_eq_card_basis a', Fintype.card_fin]) =
      wedge (Fin.cons (extE T) (stabJ T 0 ∘ a)) (by rw [hp]; exact finrank_ker_extOp hT) := by
    rw [ha', Fin.append_left_eq_cons]
    exact wedge_cast _ _ _
  -- the cokernel data
  have hcl := stabClass_extOp_eq (T := T) (φ := φ) cbar
  have hd' : LinearIndependent ℝ (stabClass (extOp T) φ ∘ cbar) := by
    rw [← hcl]; exact hd.map' (extCoker T).symm.toLinearMap (extCoker T).symm.ker
  have hm' : finrank ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) =
      finrank ℝ (F ⧸ LinearMap.range (extOp T : E × (Fin 1 → ℝ) →ₗ[ℝ] F)) :=
    (extCoker T).symm.finrank_eq
  -- the completion `j(b̄)` and the wedge identity
  have hJ : stabJ (extOp T) φ ∘ ⇑a' = Fin.append ![extStabE T φ] (extStabJ T φ ∘ (stabJ T φ ∘ a)) := by
    rw [ha', comp_append]
    refine congrArg₂ Fin.append (funext fun i => ?_) (funext fun i => ?_)
    · fin_cases i; rfl
    · rfl
  have hkl' : (1 + p) + l = finrank ℝ (LinearMap.ker (((extOp T).coprod φ :
      (E × (Fin 1 → ℝ)) × (Fin k → ℝ) →L[ℝ] F) : (E × (Fin 1 → ℝ)) × (Fin k → ℝ) →ₗ[ℝ] F)) := by
    rw [← finrank_extStabKer hT, ← hkl]; omega
  have hW : wedge (Fin.append (stabJ (extOp T) φ ∘ a') (extStabJ T φ ∘ bbar)) hkl' =
      extStabWedge hT (wedge (Fin.append (stabJ T φ ∘ a) bbar) hkl) := by
    rw [extStabWedge, wedgeExtLeft_wedge, hJ, comp_append]
    exact (wedge_append_assoc _ _ _ _ _).symm
  have hb' : LinearIndependent ℝ (Fin.append (stabJ (extOp T) φ ∘ a') (extStabJ T φ ∘ bbar)) := by
    rw [← wedge_ne_zero_iff hkl', hW, extStabWedge, wedgeExtLeft_wedge, wedge_ne_zero_iff]
    exact linearIndependent_single_append (extStabPi T φ)
      (hb.map' _ (LinearMap.ker_eq_bot.2 extStabJ_injective)) (fun i => extStabPi_extStabJ _)
      extStabPi_extStabE
  have h615 := proposition_6_4_15 hT hφ a cbar hd rfl bbar hb hkl hn
  have h615' := proposition_6_4_15 (isFredholm_extOp hT) (surjective_coprod_extOp hφ) a' cbar hd' hm' (extStabJ T φ ∘ bbar) hb' hkl' hn
  have hdet : (Pi.basisFun ℝ (Fin k)).det (Fin.append cbar
      (fun i => (((extStabJ T φ ∘ bbar) i : (E × (Fin 1 → ℝ)) × (Fin k → ℝ))).2) ∘ Fin.cast hn.symm) =
      (Pi.basisFun ℝ (Fin k)).det (Fin.append cbar
        (fun i => ((bbar i : E × (Fin k → ℝ))).2) ∘ Fin.cast hn.symm) := rfl
  -- the generator after `h ↦ e ∧ h`
  have hgen : extDetFirst hT (wedge a (by rw [Module.finrank_eq_card_basis a, Fintype.card_fin])
      ⊗ₜ dualVec (wedge (stabClass T φ ∘ cbar) rfl)) =
      wedge a' (by rw [Module.finrank_eq_card_basis a', Fintype.card_fin]) ⊗ₜ
        dualVec (wedge (stabClass (extOp T) φ ∘ cbar) hm') := by
    rw [extDetFirst_wedge_tmul hT a hp hd rfl, hwa']
    exact congrArg₂ (fun x y => x ⊗ₜ[ℝ] dualVec y) rfl (wedge_congr_fun hcl _ _)
  have step1 : detEquivOfSurjective (surjective_coprod_extOp hφ)
      (stabIota (isFredholm_extOp hT) (surjective_coprod_extOp hφ)
        (extDetFirst hT (wedge a (by rw [Module.finrank_eq_card_basis a, Fintype.card_fin]) ⊗ₜ
          dualVec (wedge (stabClass T φ ∘ cbar) rfl)))) =
      ((Pi.basisFun ℝ (Fin k)).det (Fin.append cbar
        (fun i => ((bbar i : E × (Fin k → ℝ))).2) ∘ Fin.cast hn.symm))⁻¹ •
        extStabWedge hT (wedge (Fin.append (stabJ T φ ∘ a) bbar) hkl) := by
    rw [hgen, h615', LinearEquiv.map_smul, detEquivOfSurjective_tmul_stabOne, hdet, hW]
  have step2 : detEquivOfSurjective hφ (stabIota hT hφ
      (wedge a (by rw [Module.finrank_eq_card_basis a, Fintype.card_fin]) ⊗ₜ
        dualVec (wedge (stabClass T φ ∘ cbar) rfl))) =
      ((Pi.basisFun ℝ (Fin k)).det (Fin.append cbar
        (fun i => ((bbar i : E × (Fin k → ℝ))).2) ∘ Fin.cast hn.symm))⁻¹ •
        wedge (Fin.append (stabJ T φ ∘ a) bbar) hkl := by
    rw [h615, LinearEquiv.map_smul, detEquivOfSurjective_tmul_stabOne]
  rw [step1, step2, map_smul]

/-- **The stabilization isomorphism commutes with `h ↦ e ∧ h`** (Remark 6.6.19, "compatible with
the choices"): for `L ⊕ φ` onto, `ι_φ(e ∧ h)` read in `λ(ker(L̃ ⊕ φ))` is `e ∧ ι_φ(h)`. -/
theorem detEquiv_stabIota_extDetFirst (hT : T.IsFredholm)
    (hφ : Function.Surjective (T.coprod φ)) (x : fredholmDet T) :
    detEquivOfSurjective (surjective_coprod_extOp hφ)
        (stabIota (isFredholm_extOp hT) (surjective_coprod_extOp hφ) (extDetFirst hT x)) =
      extStabWedge hT (detEquivOfSurjective hφ (stabIota hT hφ x)) := by
  have := hT.finite_ker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := hT.finite_coker
  have hc := exists_stabClass_linearIndependent hT hφ
  have hbb := exists_stabJ_completion (φ := φ) hT (Module.finBasis ℝ (LinearMap.ker
    (T : E →ₗ[ℝ] F)))
  have hn := stab_card_eq hT hφ rfl hbb.choose_spec.choose_spec.2
  refine LinearMap.congr_fun (f := (detEquivOfSurjective
    (surjective_coprod_extOp hφ)).toLinearMap ∘ₗ
      stabIota (isFredholm_extOp hT) (surjective_coprod_extOp hφ) ∘ₗ
        (extDetFirst hT).toLinearMap)
    (g := extStabWedge hT ∘ₗ (detEquivOfSurjective hφ).toLinearMap ∘ₗ stabIota hT hφ) ?_ x
  exact tensor_line_ext finrank_maxPow finrank_maxPowDual (wedge_basis_ne_zero' _ _)
    (dualVec_ne_zero finrank_maxPow ((wedge_ne_zero_iff _).2 hc.choose_spec))
    (detEquiv_stabIota_extDetFirst_wedge hT hφ _ hc.choose hc.choose_spec _
      hbb.choose_spec.choose_spec.1 hbb.choose_spec.choose_spec.2 hn)

set_option maxHeartbeats 1600000 in
/-- **The ray version**: for identifications `ι : ker(L ⊕ φ) ≅ L₀`, `ι' : ker(L̃ ⊕ φ) ≅ L₀'` and
`Ψ : λ(L₀) ≅ λ(L₀')` with `Ψ ∘ λ(ι) = λ(ι') ∘ (ê ∧ j(·))`, the ray of `e ∧ h` read in
`λ(L₀')` by `Φ_{E×ℝ}` (`stabRayEquiv`) is `Ψ` of the ray of `h` read in `λ(L₀)` by `Φ_E`. -/
theorem stabRayEquiv_extDetFirst (hT : T.IsFredholm) (hφ : Function.Surjective (T.coprod φ))
    {W W' : Type*} [AddCommGroup W] [Module ℝ W] [AddCommGroup W'] [Module ℝ W']
    {L₀ : Submodule ℝ W} {L₀' : Submodule ℝ W'} [FiniteDimensional ℝ L₀]
    [FiniteDimensional ℝ L₀']
    (ι : LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) : E × (Fin k → ℝ) →ₗ[ℝ] F)
      ≃ₗ[ℝ] L₀)
    (ι' : LinearMap.ker (((extOp T).coprod φ : (E × (Fin 1 → ℝ)) × (Fin k → ℝ) →L[ℝ] F) :
      (E × (Fin 1 → ℝ)) × (Fin k → ℝ) →ₗ[ℝ] F) ≃ₗ[ℝ] L₀')
    (Ψ : maxPow L₀ ≃ₗ[ℝ] maxPow L₀')
    (hΨ : ∀ w, Ψ (maxPowEquiv ι w) = maxPowEquiv ι' (extStabWedge hT w))
    (r : Module.Ray ℝ (fredholmDet T)) :
    stabRayEquiv (isFredholm_extOp hT) (surjective_coprod_extOp hφ) ι'
        (Module.Ray.map (extDetFirst hT) r) =
      Module.Ray.map Ψ (stabRayEquiv hT hφ ι r) := by
  induction r using Module.Ray.ind with | h v hv => ?_
  have hv' : extDetFirst hT v ≠ 0 := (extDetFirst hT).map_ne_zero_iff.2 hv
  obtain ⟨h1, e1⟩ := stabRayEquiv_ray (isFredholm_extOp hT) (surjective_coprod_extOp hφ) ι' _ hv'
  obtain ⟨h2, e2⟩ := stabRayEquiv_ray hT hφ ι v hv
  refine (congrArg (stabRayEquiv (isFredholm_extOp hT) (surjective_coprod_extOp hφ) ι')
    (Module.Ray.map_apply _ _ _)).trans ?_
  refine e1.trans (Eq.trans ?_ (congrArg (Module.Ray.map Ψ) e2).symm)
  refine Eq.trans ?_ (Module.Ray.map_apply Ψ _ h2).symm
  exact rayOfNeZero_eq_of_eq h1 (Ψ.map_ne_zero_iff.2 h2)
    ((congrArg (maxPowEquiv ι') (detEquiv_stabIota_extDetFirst hT hφ v)).trans (hΨ _).symm)

end ExtStab

/-! ### The product chart point: `L̂ = Γ⁻¹ (L ⊕ 0) A` and its stabilization -/

section ProdPoint

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [ParacompactSpace ((Fin 1 → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))]

namespace ChartPoint

variable {x : X} (p : ChartPoint B x) (t : Fin 1 → ℝ)
  (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))

/-- **The stabilization `φ̂ = Γ⁻¹ ∘ φ : ℝᵏ → Ŷ_{(t, x)}`** of the product chart point. -/
abbrev prodStab {k : ℕ} (φ : (Fin k → ℝ) →L[ℝ] ↥p.K) :
    (Fin k → ℝ) →L[ℝ] ↥(p.prodPt t q₀).K :=
  ((p.prodK t q₀).symm : ↥p.K →L[ℝ] ↥(p.prodPt t q₀).K) ∘L φ

theorem prodStab_conj {k : ℕ} (φ : (Fin k → ℝ) →L[ℝ] ↥p.K) (μ : Fin k → ℝ) :
    φ μ = p.prodK t q₀ (p.prodStab t q₀ φ μ) :=
  ((p.prodK t q₀).apply_symm_apply _).symm

/-- `L̂ ⊕ φ̂` is onto when `L ⊕ φ` is. -/
theorem surjective_coprod_prodLin {k : ℕ} {L : ↥p.T →L[ℝ] ↥p.K} {φ : (Fin k → ℝ) →L[ℝ] ↥p.K}
    (hφ : Function.Surjective (L.coprod φ)) :
    Function.Surjective ((p.prodLin t q₀ L).coprod (p.prodStab t q₀ φ)) := by
  intro y
  obtain ⟨w, hw⟩ := surjective_coprod_extOp hφ (p.prodK t q₀ y)
  refine ⟨((p.prodT t q₀).symm w.1, w.2), (p.prodK t q₀).injective ?_⟩
  rw [← coprod_conj (p.prodT t q₀) (p.prodK t q₀) (p.prodLin_conj t q₀ L)
    (p.prodStab_conj t q₀ φ)]
  simpa using hw

end ChartPoint

end ProdPoint

end Polyfold
