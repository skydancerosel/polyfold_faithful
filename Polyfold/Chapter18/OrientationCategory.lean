import Polyfold.Chapter18.LinearizationSetLocalExamples
import Polyfold.Chapter17.GrassmannianFunctor
import Polyfold.Chapter15.OrientedLinearizations
import Polyfold.Chapter6.ChartTransfer
import Polyfold.Chapter18.OrientationsExamples

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 18,
§18.5, p. 856: **the category `Ĝr_F(C) → C_∞`** of oriented sc-Fredholm operators, before
Definition 18.5.1.  Numbers and pages are the 2021 text's.

# The category `Ĝr_F(C)`

## The text, paraphrased

(p. 856) For a smooth object `α` of `C`, `Ĝr_F(α)` is the set of finite formal sums
`L = ∑ σ_L̂ · L̂` with non-negative rational weights of oriented sc-Fredholm operators
`L̂ = (L, o)`, `L : T_αC → E_α`, `E_α = P⁻¹(α)`.  The pairs `(α, L)` are the objects of a category
`Ĝr_F(C)` fibred over `C_∞` by `π̂(α, L) = α`.  Its morphisms are the pairs `(φ, L)` with `φ` a
smooth morphism and `s(φ) = π̂(α, L)`, with `s(φ, L) = (s(φ), L)` and
`t(φ, L) = (t(φ), φ_* L)`, where `φ_*(∑ σ_L̂ · L̂) = ∑ σ_L̂ · φ_* L̂`, `φ_*(L, o) = (φ_* L, φ_* o)`
and `φ_* L = μ(φ) ∘ L ∘ Tφ⁻¹`.

## What is formalized

* Linear algebra: `linConjKerEquiv`, `linConjCokerEquiv`, **`linConjDet`** (the isomorphism
  `det(S) ≅ det(S')` of a conjugation `S' ∘ A = Γ ∘ S` by linear isomorphisms, the linear form of
  Part III's `conjDet`), with `linConjDet_trans`, `linConjDet_congr`, `linConjDet_eq_refl`,
  `linConjDet_trans_linDetEquivOfEq` and `linConjDet_eq_refl_of_bijective`; `DetRay L` (the
  orientations of `det(L)`), `DetRay.cast`, `DetRay.conj` (`A_* o`); the conjugation
  `linConjOp A Γ L = Γ ∘ L ∘ A⁻¹` on operators of finite index (`linConjFred`) and on pairs
  `(L, o)` (`linConjRay`), with the laws `linConjRay_refl`, `linConjRay_trans`,
  `linConjRay_congr` and `linConjRay_eq_self_of_bijective`; `sigma_ray_ext`,
  `exists_two_sigma_ray`, `sigma_ray_eq_or_neg` (the two rays of a line).
* `FredOp V S α` (sc-Fredholm operators `T_αC → E_α`), **`OrFredOp V S α`** (oriented ones:
  `(L, o)` with `o` a ray of `det(L)`), **`GrFHat V S α`** (`Ĝr_F(α)`, formal sums with weights in
  `ℚ≥0`), `GrF V S α` (the same without orientations).
* `fredPush` (`φ_* L = μ(φ) ∘ L ∘ Tφ⁻¹`, `fredPush_val`), **`orFredPush`**
  (`φ_*(L, o) = (φ_* L, φ_* o)`), **`grFHatPush`** (`φ_*` on formal sums, `grFHatPush_single`),
  with the functor laws `orFredPush_unit`, `orFredPush_comp`, `grFHatPush_unit`,
  `grFHatPush_comp` (and `grFPush_unit`, `grFPush_comp` without orientations);
  `orFredPush_eq_self_of_bijective` (a morphism `φ : α → α` with `φ_* L = L`, `L` bijective, fixes
  both orientations of `L`); `exists_two_orFredOp` (over every `L` exactly two oriented operators);
  `grFForget` and `grFForget_grFHatPush` (forgetting orientations commutes with `φ_*`).
* **`grFHatFunctor hU : C_∞ ⥤ Type`** (`grFHatMap`, `grFHatMap_id`, `grFHatMap_comp`) and
  **`GrFHatCat hU := (grFHatFunctor hU).Elements`** (`Ĝr_F(C)`) with
  **`grFHatProj hU = CategoryOfElements.π`** (`π̂`); the unoriented `grFFunctor hU`, the forgetful
  transformation `grFForgetNat hU` (`grFForgetC_naturality`) and the functor
  `grFForgetFunctor hU` over `C_∞` (`grFForgetFunctor_comp_π`).
* The morphisms as printed: `GrFMor` (pairs `(φ, L)` with `s(φ) = π̂(α, L)`), `GrFMor.src`,
  `GrFMor.tgt` (`(s φ, L)` and `(t φ, φ_* L)`, `GrFMor.tgt_snd`), `GrFMor.toHom` (a morphism of
  `Ĝr_F(C)`), `GrFMor.proj_src_tgt`, and `GrFMor.ofHom`, `GrFMor.ofHom_src_tgt` (every morphism of
  `Ĝr_F(C)` is a printed pair).

## Relation to the orientation category `O_f` of Definition 18.5.1

As we read Definitions 18.5.1–18.5.4 they do not use `Ĝr_F(C)`: `O_f` is built from
`DET(f, α) → Lin(f, α)` (`Orientations.lean`).  The two meet in the fibres:

* `linFredOp`: every member of `Lin(f, α)` (Definition 18.1.4, `linSetLoc`) is an sc-Fredholm
  operator `T_αC → E_α` (`exists_index_linSetLoc`); `fredPush_linFredOp`: `φ_*` on `Ĝr_F` restricts
  to the `φ_*` of Definition 18.1.4 on `Lin(f, α)`.
* `linOrLift ω L = (L, ω_L)` for a choice `ω` of a ray of `det(L)` for every `L ∈ Lin(f, α)`,
  `linCanonLift ω` on formal sums of members of `Lin(f, α)`, `grFForget_linCanonLift` (forgetting
  gives back the formal sum of members of `Lin(f, α)`), and `linOrLift_or_neg`: an oriented
  operator over `L ∈ Lin(f, α)` is `(L, ω_L)` or `(L, −ω_L)` (the two-point fibre of
  `DET(f, α) → Lin(f, α)`, read in `Ĝr_F(α)`).
* `orFredPush_linOrLift`: if `φ_*` carries `ω_L` to `ω'_{φ_* L}`, then `φ_*` carries
  `linOrLift ω L` to `linOrLift ω' (φ_* L)` (the law `o_{t(φ)} = φ_* o_{s(φ)}` of an orientation,
  read in `Ĝr_F`).

The chart-level orientations of `Orientations.lean` (rays of the determinant of the linearization
in the reference chart) are not identified here with rays of `linDet` of the members of
`Lin(f, α)`; that identification is a chart computation not carried out in this file.

## Witness

`reflection_grFHat` on the reflection bundle `ℤ/2 ⋉ (ℝ × ℝ) → ℤ/2 ⋉ ℝ` with `f(x) = (x, x)`, at the
smooth object `0` (`smoothZero`) whose isotropy `g = (−1, 0)` (`smoothNeg`) acts on `E_0` by
`v ↦ −v`: `f'(0) ∈ Lin(f, 0)` is an sc-Fredholm operator with exactly two orientations `q₁ ≠ q₂`,
which give two different objects `(0, 1 · q₁) ≠ (0, 1 · q₂)` of `Ĝr_F(C)` over `0`; `g_*` maps the
fibre over `f'(0)` to itself (`g_* f'(0) = f'(0)`, `linPush_linearization`), and the printed pair
`(g, 1 · q)` has source `(0, 1 · q)` and target `(0, 1 · g_* q)`.  Which of the two orientations
`g_* q` is depends on the sign of `g` on `det(f'(0))`; the witness does not compute it (the
general statement for bijective `L` is `orFredPush_eq_self_of_bijective`).

## Readings

* **"sc-Fredholm operator `L : T_αC → E_α`".**  We read it, as the next paragraph of the text
  reads `Lin(f, α)` ("viewing the operators as classical linear Fredholm operators … on level 0"),
  as a linear map `T_αC → μ(α)` with finite-dimensional kernel and cokernel (`HasFiniteIndex`),
  `T_αC` the tangent space of §17.2 and `μ(α) = E_α`.  The members of `Lin(f, α)` are such
  operators (`linFredOp`).
* **Orientations.**  An orientation of `L` is a ray of `det(L) = λ(ker L) ⊗ λ*(coker L)`
  (Definitions 6.4.1, 6.4.2, `linDet`, `DetRay`); `φ_* o` is the image of `o` under the isomorphism
  `det(L) ≅ det(φ_* L)` of the conjugation by `Tφ` and `μ(φ)` (`linConjDet`).
* **Formal sums** are `Finsupp`s with values in `ℚ≥0` (finitely many non-zero weights, these
  positive), as for `Ĝr_F(x)` in Part III (`ChartPoint.GrFHat`).
* **The category.**  `C_∞` is the full subgroupoid `regSubInf` of the smooth objects (Mathlib's
  groupoid on `regSubInf.Ob`); `T_αC` is defined for smooth objects under the standing reading
  `F(α) ≠ ∅` (`HasUniformizers`, `tangentObj_smoothObjVal`).  `Ĝr_F(C)` is Mathlib's category of
  elements of `α ↦ Ĝr_F(α)`, `φ ↦ φ_*`: objects `(α, L)`, morphisms `φ : α → α'` with
  `φ_* L = L'`, which are the printed pairs `(φ, L)` (`GrFMor`).
-/

set_option maxSynthPendingDepth 3

open Set Function Module TensorProduct CategoryTheory

noncomputable section

namespace Polyfold

universe u

/-! ### The determinant isomorphism of a conjugation, for linear maps -/

section LinConj

variable {E F E' F' E'' F'' : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [AddCommGroup E'] [Module ℝ E'] [AddCommGroup F'] [Module ℝ F'] [AddCommGroup E'']
  [Module ℝ E''] [AddCommGroup F''] [Module ℝ F'']

variable (A : E ≃ₗ[ℝ] E') (Γ : F ≃ₗ[ℝ] F') {S : E →ₗ[ℝ] F} {S' : E' →ₗ[ℝ] F'}

/-- `ker S ≅ ker S'`, `v ↦ A v`, for `S' ∘ A = Γ ∘ S`. -/
def linConjKerEquiv (h : ∀ v, S' (A v) = Γ (S v)) :
    LinearMap.ker S ≃ₗ[ℝ] LinearMap.ker S' where
  toFun v := ⟨A v, by
    have hv : S v = 0 := v.2
    change S' (A v) = 0
    rw [h, hv, map_zero]⟩
  map_add' v w := Subtype.ext (map_add A (v : E) w)
  map_smul' t v := Subtype.ext (map_smul A t (v : E))
  invFun w := ⟨A.symm w, by
    have hw : S' w = 0 := w.2
    change S (A.symm w) = 0
    apply Γ.injective
    rw [← h, LinearEquiv.apply_symm_apply, hw, map_zero]⟩
  left_inv v := Subtype.ext (A.symm_apply_apply (v : E))
  right_inv w := Subtype.ext (A.apply_symm_apply (w : E'))

@[simp] theorem coe_linConjKerEquiv_apply (h : ∀ v, S' (A v) = Γ (S v))
    (v : LinearMap.ker S) : (linConjKerEquiv A Γ h v : E') = A v := rfl

/-- `Γ(R(S)) = R(S')` for `S' ∘ A = Γ ∘ S`. -/
theorem map_range_eq_of_linConj (h : ∀ v, S' (A v) = Γ (S v)) :
    (LinearMap.range S).map (Γ : F →ₗ[ℝ] F') = LinearMap.range S' := by
  ext y
  constructor
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨A v, h v⟩
  · rintro ⟨w, rfl⟩
    refine ⟨S (A.symm w), ⟨A.symm w, rfl⟩, ?_⟩
    change Γ (S (A.symm w)) = S' w
    rw [← h, LinearEquiv.apply_symm_apply]

/-- `F / R(S) ≅ F' / R(S')`, `[y] ↦ [Γ y]`. -/
def linConjCokerEquiv (h : ∀ v, S' (A v) = Γ (S v)) :
    (F ⧸ LinearMap.range S) ≃ₗ[ℝ] (F' ⧸ LinearMap.range S') :=
  Submodule.Quotient.equiv _ _ Γ (map_range_eq_of_linConj A Γ h)

@[simp] theorem linConjCokerEquiv_mk (h : ∀ v, S' (A v) = Γ (S v)) (y : F) :
    linConjCokerEquiv A Γ h (Submodule.Quotient.mk y) = Submodule.Quotient.mk (Γ y) := rfl

/-- **The determinant isomorphism of a conjugation** `S' ∘ A = Γ ∘ S` by linear isomorphisms:
`det(S) = λ(ker S) ⊗ λ*(coker S) ≅ det(S')`, the kernels by `A`, the cokernels by `Γ` (the linear
form of `conjDet`). -/
def linConjDet (h : ∀ v, S' (A v) = Γ (S v)) : linDet S ≃ₗ[ℝ] linDet S' :=
  TensorProduct.congr (maxPowEquiv (linConjKerEquiv A Γ h))
    (maxPowDualEquiv (linConjCokerEquiv A Γ h).symm)

/-- **The determinant isomorphisms of conjugations compose.** -/
theorem linConjDet_trans (A' : E' ≃ₗ[ℝ] E'') (Γ' : F' ≃ₗ[ℝ] F'') {S'' : E'' →ₗ[ℝ] F''}
    (h : ∀ v, S' (A v) = Γ (S v)) (h' : ∀ v, S'' (A' v) = Γ' (S' v))
    (h'' : ∀ v, S'' ((A.trans A') v) = (Γ.trans Γ') (S v)) :
    (linConjDet A Γ h).trans (linConjDet A' Γ' h') = linConjDet (A.trans A') (Γ.trans Γ') h'' := by
  rw [linConjDet, linConjDet, linConjDet, ← TensorProduct.congr_trans, ← maxPowEquiv_trans,
    ← maxPowDualEquiv_trans]
  congr 2
  refine LinearEquiv.ext fun y => ?_
  obtain ⟨x, rfl⟩ := (linConjCokerEquiv (A.trans A') (Γ.trans Γ') h'').surjective y
  have hx : linConjCokerEquiv (A.trans A') (Γ.trans Γ') h'' x =
      linConjCokerEquiv A' Γ' h' (linConjCokerEquiv A Γ h x) := by
    induction x using Submodule.Quotient.induction_on with
    | H y => rfl
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.trans_apply, hx, LinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply]

/-- **`linConjDet` depends only on the maps `A`, `Γ`.** -/
theorem linConjDet_congr {A₁ A₂ : E ≃ₗ[ℝ] E'} {Γ₁ Γ₂ : F ≃ₗ[ℝ] F'} (hA : ∀ v, A₁ v = A₂ v)
    (hΓ : ∀ y, Γ₁ y = Γ₂ y) (h₁ : ∀ v, S' (A₁ v) = Γ₁ (S v))
    (h₂ : ∀ v, S' (A₂ v) = Γ₂ (S v)) : linConjDet A₁ Γ₁ h₁ = linConjDet A₂ Γ₂ h₂ := by
  obtain rfl : A₁ = A₂ := LinearEquiv.ext hA
  obtain rfl : Γ₁ = Γ₂ := LinearEquiv.ext hΓ
  rfl

/-- **The conjugation by isomorphisms which are the identity** is the identity of `det(S)`. -/
theorem linConjDet_eq_refl (A : E ≃ₗ[ℝ] E) (Γ : F ≃ₗ[ℝ] F) (hA : ∀ v, A v = v)
    (hΓ : ∀ y, Γ y = y) (h : ∀ v, S (A v) = Γ (S v)) :
    linConjDet A Γ h = LinearEquiv.refl ℝ _ := by
  obtain rfl : A = LinearEquiv.refl ℝ E := LinearEquiv.ext hA
  obtain rfl : Γ = LinearEquiv.refl ℝ F := LinearEquiv.ext hΓ
  have h1 : linConjKerEquiv (LinearEquiv.refl ℝ E) (LinearEquiv.refl ℝ F) h =
      LinearEquiv.refl ℝ _ := LinearEquiv.ext fun v => Subtype.ext rfl
  have h2 : (linConjCokerEquiv (LinearEquiv.refl ℝ E) (LinearEquiv.refl ℝ F) h).symm =
      LinearEquiv.refl ℝ _ := by
    refine LinearEquiv.ext fun y => ?_
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      apply (linConjCokerEquiv (LinearEquiv.refl ℝ E) (LinearEquiv.refl ℝ F) h).injective
      rw [LinearEquiv.apply_symm_apply]
      rfl
  rw [linConjDet, h1, h2, maxPowEquiv_refl, maxPowDualEquiv_refl, TensorProduct.congr_refl_refl]

/-- `linConjDet` followed by the identification `det(S') = det(S'')` for `S' = S''`. -/
theorem linConjDet_trans_linDetEquivOfEq {S'' : E' →ₗ[ℝ] F'} (h : ∀ v, S' (A v) = Γ (S v))
    (hS : S' = S'') (h' : ∀ v, S'' (A v) = Γ (S v)) :
    (linConjDet A Γ h).trans (linDetEquivOfEq hS) = linConjDet A Γ h' := by
  subst hS
  rw [linDetEquivOfEq_self, LinearEquiv.trans_refl]

/-- **The determinant isomorphism of a self-conjugation of an isomorphism is the identity**:
for a bijective `S` with `S ∘ A = Γ ∘ S`, `det(S) = λ(0) ⊗ λ*(0)`. -/
theorem linConjDet_eq_refl_of_bijective (A : E ≃ₗ[ℝ] E) (Γ : F ≃ₗ[ℝ] F) (hS : Bijective S)
    (h : ∀ v, S (A v) = Γ (S v)) : linConjDet A Γ h = LinearEquiv.refl ℝ _ := by
  have hker : Subsingleton (LinearMap.ker S) := by
    refine ⟨fun a b => Subtype.ext ?_⟩
    have ha : S a = 0 := a.2
    have hb : S b = 0 := b.2
    exact hS.1 (ha.trans hb.symm)
  have hcok : Subsingleton (F ⧸ LinearMap.range S) :=
    Submodule.Quotient.subsingleton_iff.2 (LinearMap.range_eq_top.2 hS.2)
  have h1 : linConjKerEquiv A Γ h = LinearEquiv.refl ℝ _ :=
    LinearEquiv.ext fun _ => Subsingleton.elim _ _
  have h2 : (linConjCokerEquiv A Γ h).symm = LinearEquiv.refl ℝ _ :=
    LinearEquiv.ext fun _ => Subsingleton.elim _ _
  rw [linConjDet, h1, h2, maxPowEquiv_refl, maxPowDualEquiv_refl, TensorProduct.congr_refl_refl]

/-- `Ray.map` of the identification `det(L) = det(L)` is the identity. -/
theorem ray_map_linDetEquivOfEq_rfl (L : E →ₗ[ℝ] F) (h : L = L) (o : Module.Ray ℝ (linDet L)) :
    Module.Ray.map (linDetEquivOfEq h) o = o := by
  rw [linDetEquivOfEq_self, Module.Ray.map_refl]
  rfl

/-- **The orientations of `det(L)`**: the rays of `det(L) = λ(ker L) ⊗ λ*(coker L)`
(Definition 6.4.2), as a type of its own (`Module.Ray ℝ (linDet L)`). -/
def DetRay (L : E →ₗ[ℝ] F) : Type _ := Module.Ray ℝ (linDet L)

/-- `−o`, the opposite orientation. -/
instance (L : E →ₗ[ℝ] F) : Neg (DetRay L) := inferInstanceAs (Neg (Module.Ray ℝ (linDet L)))

/-- The orientations of `det(L)` and `det(L')` for `L = L'` correspond (`linDetEquivOfEq`). -/
def DetRay.cast {L L' : E →ₗ[ℝ] F} (h : L = L') (o : DetRay L) : DetRay L' :=
  Module.Ray.map (linDetEquivOfEq h) o

/-- **`A_* o`**: the image of an orientation of `det(S)` under the determinant isomorphism
`linConjDet` of a conjugation `S' ∘ A = Γ ∘ S`. -/
def DetRay.conj (A : E ≃ₗ[ℝ] E') (Γ : F ≃ₗ[ℝ] F') {S : E →ₗ[ℝ] F} {S' : E' →ₗ[ℝ] F'}
    (h : ∀ v, S' (A v) = Γ (S v)) (o : DetRay S) : DetRay S' :=
  Module.Ray.map (linConjDet A Γ h) o

theorem DetRay.cast_rfl (L : E →ₗ[ℝ] F) (h : L = L) (o : DetRay L) : DetRay.cast h o = o :=
  ray_map_linDetEquivOfEq_rfl L h o

/-- Orientations which correspond under `det(L) = det(L')` are heterogeneously equal. -/
theorem DetRay.heq_of_cast {L L' : E →ₗ[ℝ] F} (h : L = L') {o : DetRay L} {o' : DetRay L'}
    (ho : DetRay.cast h o = o') : HEq o o' := by
  subst h
  exact heq_of_eq ((DetRay.cast_rfl L rfl o).symm.trans ho)

/-- Pairs `(L, o)`, `o` an orientation of `det(L)`, are equal when the operators are and the
orientations correspond under `det(L) = det(L')`. -/
theorem sigma_ray_ext {P : (E →ₗ[ℝ] F) → Prop}
    {x y : Σ L : {L : E →ₗ[ℝ] F // P L}, DetRay L.1} (h : x.1.1 = y.1.1)
    (ho : DetRay.cast h x.2 = y.2) : x = y :=
  Sigma.ext (Subtype.ext h) (DetRay.heq_of_cast h ho)

/-- **Over an operator with finite index there are exactly two oriented ones**. -/
theorem exists_two_sigma_ray {P : (E →ₗ[ℝ] F) → Prop} (hP : ∀ L, P L → HasFiniteIndex L)
    (L : {L : E →ₗ[ℝ] F // P L}) :
    ∃ q₁ q₂ : Σ L : {L : E →ₗ[ℝ] F // P L}, DetRay L.1, q₁.1 = L ∧ q₂.1 = L ∧
      q₁ ≠ q₂ ∧ ∀ q : Σ L : {L : E →ₗ[ℝ] F // P L}, DetRay L.1,
        q.1 = L → q = q₁ ∨ q = q₂ := by
  obtain ⟨L, hL⟩ := L
  have := (hP L hL).finite_ker
  have := (hP L hL).finite_coker
  obtain ⟨r₁, r₂, hne, hr⟩ := ChartPoint.exists_two_rays_of_finrank_eq_one (finrank_linDet L)
  refine ⟨⟨⟨L, hL⟩, r₁⟩, ⟨⟨L, hL⟩, r₂⟩, rfl, rfl,
    fun h => hne (eq_of_heq (Sigma.mk.inj_iff.1 h).2), ?_⟩
  rintro ⟨⟨L', hL'⟩, r⟩ hLL
  obtain rfl : L' = L := congrArg Subtype.val hLL
  rcases hr r with h | h
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inr rfl

/-- **The two-point fibre**: a pair `(L, r)` over `L` is `(L, o)` or `(L, −o)`. -/
theorem sigma_ray_eq_or_neg {P : (E →ₗ[ℝ] F) → Prop} (hP : ∀ L, P L → HasFiniteIndex L)
    (L : {L : E →ₗ[ℝ] F // P L}) (o : DetRay L.1)
    (q : Σ L : {L : E →ₗ[ℝ] F // P L}, DetRay L.1) (hq : q.1 = L) :
    q = ⟨L, o⟩ ∨ q = ⟨L, -o⟩ := by
  obtain ⟨⟨L', hL'⟩, r⟩ := q
  obtain rfl : L' = L.1 := congrArg Subtype.val hq
  have := (hP _ hL').finite_ker
  have := (hP _ hL').finite_coker
  have h1 := finrank_linDet L.1
  induction o using Module.Ray.ind with
  | h v hv =>
    rcases ray_eq_or_eq_neg_of_finrank_eq_one h1 hv r with h | h
    · left; subst h; rfl
    · right; subst h; rfl

/-- The unit law for rays: the conjugation by isomorphisms which are the identity, followed by
`det(S') = det(S)`, fixes every ray. -/
theorem ray_map_linConjDet_unit (A : E ≃ₗ[ℝ] E) (Γ : F ≃ₗ[ℝ] F) (hA : ∀ v, A v = v)
    (hΓ : ∀ y, Γ y = y) {S S' : E →ₗ[ℝ] F} (h : ∀ v, S' (A v) = Γ (S v)) (hS : S' = S)
    (r : Module.Ray ℝ (linDet S)) :
    Module.Ray.map (linDetEquivOfEq hS) (Module.Ray.map (linConjDet A Γ h) r) = r := by
  have h' : ∀ v, S (A v) = Γ (S v) := fun v => by rw [hA, hΓ]
  rw [ray_map_map, linConjDet_trans_linDetEquivOfEq _ _ _ hS h', linConjDet_eq_refl _ _ hA hΓ h',
    Module.Ray.map_refl]
  rfl

/-- The composition law for rays: the conjugation by `(A₃, Γ₃) = (A₂ ∘ A₁, Γ₂ ∘ Γ₁)` followed by
`det(S₃) = det(S'')` is the composite of the two conjugations. -/
theorem ray_map_linConjDet_comp (A₁ : E ≃ₗ[ℝ] E') (Γ₁ : F ≃ₗ[ℝ] F') (A₂ : E' ≃ₗ[ℝ] E'')
    (Γ₂ : F' ≃ₗ[ℝ] F'') (A₃ : E ≃ₗ[ℝ] E'') (Γ₃ : F ≃ₗ[ℝ] F'')
    (hA : ∀ v, A₃ v = A₂ (A₁ v)) (hΓ : ∀ y, Γ₃ y = Γ₂ (Γ₁ y))
    {S₁ : E →ₗ[ℝ] F} {S₂ : E' →ₗ[ℝ] F'} {S₃ S'' : E'' →ₗ[ℝ] F''}
    (h₁ : ∀ v, S₂ (A₁ v) = Γ₁ (S₁ v)) (h₂ : ∀ v, S'' (A₂ v) = Γ₂ (S₂ v))
    (h₃ : ∀ v, S₃ (A₃ v) = Γ₃ (S₁ v)) (hS : S₃ = S'') (r : Module.Ray ℝ (linDet S₁)) :
    Module.Ray.map (linDetEquivOfEq hS) (Module.Ray.map (linConjDet A₃ Γ₃ h₃) r) =
      Module.Ray.map (linConjDet A₂ Γ₂ h₂) (Module.Ray.map (linConjDet A₁ Γ₁ h₁) r) := by
  have h₁₂ : ∀ v, S'' ((A₁.trans A₂) v) = (Γ₁.trans Γ₂) (S₁ v) := fun v => by
    rw [LinearEquiv.trans_apply, h₂, h₁, LinearEquiv.trans_apply]
  have h₃' : ∀ v, S'' (A₃ v) = Γ₃ (S₁ v) := fun v => by rw [← hS]; exact h₃ v
  rw [ray_map_map, ray_map_map, linConjDet_trans A₁ Γ₁ A₂ Γ₂ h₁ h₂ h₁₂,
    linConjDet_trans_linDetEquivOfEq A₃ Γ₃ h₃ hS h₃',
    linConjDet_congr
      (fun v => (hA v).trans (LinearEquiv.trans_apply (e₁₂ := A₁) (e₂₃ := A₂) v).symm)
      (fun y => (hΓ y).trans (LinearEquiv.trans_apply (e₁₂ := Γ₁) (e₂₃ := Γ₂) y).symm) h₃' h₁₂]

/-- For a bijective `S` with `S' = S`, the self-conjugation followed by `det(S') = det(S)` fixes
every ray. -/
theorem ray_map_linConjDet_of_bijective (A : E ≃ₗ[ℝ] E) (Γ : F ≃ₗ[ℝ] F) {S S' : E →ₗ[ℝ] F}
    (h : ∀ v, S' (A v) = Γ (S v)) (hS : S' = S) (hb : Bijective S)
    (r : Module.Ray ℝ (linDet S)) :
    Module.Ray.map (linDetEquivOfEq hS) (Module.Ray.map (linConjDet A Γ h) r) = r := by
  have h' : ∀ v, S (A v) = Γ (S v) := fun v => by have := h v; rw [hS] at this; exact this
  rw [ray_map_map, linConjDet_trans_linDetEquivOfEq _ _ _ hS h',
    linConjDet_eq_refl_of_bijective _ _ hb h', Module.Ray.map_refl]
  rfl

/-! ### Conjugation of oriented operators with finite index -/

/-- `L ↦ Γ ∘ L ∘ A⁻¹`. -/
def linConjOp (A : E ≃ₗ[ℝ] E') (Γ : F ≃ₗ[ℝ] F') (L : E →ₗ[ℝ] F) : E' →ₗ[ℝ] F' :=
  (Γ : F →ₗ[ℝ] F') ∘ₗ L ∘ₗ (A.symm : E' →ₗ[ℝ] E)

theorem linConjOp_apply (A : E ≃ₗ[ℝ] E') (Γ : F ≃ₗ[ℝ] F') (L : E →ₗ[ℝ] F) (v : E) :
    linConjOp A Γ L (A v) = Γ (L v) := by
  simp [linConjOp]

/-- `L ↦ Γ ∘ L ∘ A⁻¹` on operators with finite index. -/
def linConjFred (A : E ≃ₗ[ℝ] E') (Γ : F ≃ₗ[ℝ] F') (L : {L : E →ₗ[ℝ] F // HasFiniteIndex L}) :
    {L : E' →ₗ[ℝ] F' // HasFiniteIndex L} :=
  ⟨linConjOp A Γ L.1, (hasFiniteIndex_conj A.symm Γ L.2).1⟩

/-- **`(L, o) ↦ (Γ ∘ L ∘ A⁻¹, A_* o)`**, `A_* o` the image of `o` under `linConjDet`. -/
def linConjRay (A : E ≃ₗ[ℝ] E') (Γ : F ≃ₗ[ℝ] F')
    (x : Σ L : {L : E →ₗ[ℝ] F // HasFiniteIndex L}, DetRay L.1) :
    Σ L : {L : E' →ₗ[ℝ] F' // HasFiniteIndex L}, DetRay L.1 :=
  ⟨linConjFred A Γ x.1, DetRay.conj A Γ (linConjOp_apply A Γ x.1.1) x.2⟩

theorem linConjFred_refl (L : {L : E →ₗ[ℝ] F // HasFiniteIndex L}) :
    linConjFred (LinearEquiv.refl ℝ E) (LinearEquiv.refl ℝ F) L = L :=
  Subtype.ext (LinearMap.ext fun _ => rfl)

theorem linConjFred_trans (A₁ : E ≃ₗ[ℝ] E') (Γ₁ : F ≃ₗ[ℝ] F') (A₂ : E' ≃ₗ[ℝ] E'')
    (Γ₂ : F' ≃ₗ[ℝ] F'') (L : {L : E →ₗ[ℝ] F // HasFiniteIndex L}) :
    linConjFred (A₁.trans A₂) (Γ₁.trans Γ₂) L = linConjFred A₂ Γ₂ (linConjFred A₁ Γ₁ L) :=
  Subtype.ext (LinearMap.ext fun _ => rfl)

theorem linConjRay_congr {A A' : E ≃ₗ[ℝ] E'} {Γ Γ' : F ≃ₗ[ℝ] F'} (hA : A = A') (hΓ : Γ = Γ')
    (x : Σ L : {L : E →ₗ[ℝ] F // HasFiniteIndex L}, DetRay L.1) :
    linConjRay A Γ x = linConjRay A' Γ' x := by
  subst hA hΓ
  rfl

theorem linConjFred_congr {A A' : E ≃ₗ[ℝ] E'} {Γ Γ' : F ≃ₗ[ℝ] F'} (hA : A = A') (hΓ : Γ = Γ')
    (L : {L : E →ₗ[ℝ] F // HasFiniteIndex L}) : linConjFred A Γ L = linConjFred A' Γ' L := by
  subst hA hΓ
  rfl

/-- `(id, id)_* = Id`. -/
theorem linConjRay_refl
    (x : Σ L : {L : E →ₗ[ℝ] F // HasFiniteIndex L}, DetRay L.1) :
    linConjRay (LinearEquiv.refl ℝ E) (LinearEquiv.refl ℝ F) x = x :=
  sigma_ray_ext (congrArg Subtype.val (linConjFred_refl x.1))
    (ray_map_linConjDet_unit _ _ (fun _ => rfl) (fun _ => rfl) _ _ x.2)

/-- `(A₂ A₁, Γ₂ Γ₁)_* = (A₂, Γ₂)_* (A₁, Γ₁)_*`. -/
theorem linConjRay_trans (A₁ : E ≃ₗ[ℝ] E') (Γ₁ : F ≃ₗ[ℝ] F') (A₂ : E' ≃ₗ[ℝ] E'')
    (Γ₂ : F' ≃ₗ[ℝ] F'')
    (x : Σ L : {L : E →ₗ[ℝ] F // HasFiniteIndex L}, DetRay L.1) :
    linConjRay (A₁.trans A₂) (Γ₁.trans Γ₂) x = linConjRay A₂ Γ₂ (linConjRay A₁ Γ₁ x) :=
  sigma_ray_ext (congrArg Subtype.val (linConjFred_trans A₁ Γ₁ A₂ Γ₂ x.1))
    (ray_map_linConjDet_comp A₁ Γ₁ A₂ Γ₂ _ _ (fun _ => rfl) (fun _ => rfl) _ _ _ _ x.2)

/-- A self-conjugation fixing an isomorphism `L` fixes its orientations. -/
theorem linConjRay_eq_self_of_bijective (A : E ≃ₗ[ℝ] E) (Γ : F ≃ₗ[ℝ] F)
    (x : Σ L : {L : E →ₗ[ℝ] F // HasFiniteIndex L}, DetRay L.1)
    (hL : linConjOp A Γ x.1.1 = x.1.1) (hb : Bijective x.1.1) : linConjRay A Γ x = x :=
  sigma_ray_ext hL (ray_map_linConjDet_of_bijective _ _ _ hL hb x.2)

end LinConj

/-! ### Oriented sc-Fredholm operators `T_αC → E_α` and `Ĝr_F(α)` -/

namespace GCT.VectorBundle

open GroupoidalCategory GroupoidalCategory.BanachFunctor PolyfoldConstruction
  StrongPolyfoldBundleConstruction

variable {C : GCT.{u}} (V : C.VectorBundle) (S : C.PolyfoldConstruction)

/-- **An sc-Fredholm operator `L : T_αC → E_α`** (2021 p. 856), read on level `0`: a linear map
`T_αC → μ(α)` with finite-dimensional kernel and cokernel. -/
abbrev FredOp (α : C.Obj) [Fact (S.TangentObj α)] : Type (u + 1) :=
  {L : S.TangentSpaceAt α →ₗ[ℝ] V.V α // HasFiniteIndex L}

/-- **An oriented sc-Fredholm operator `L̂ = (L, o)`** (2021 p. 856): `o` a ray of `det(L)`. -/
abbrev OrFredOp (α : C.Obj) [Fact (S.TangentObj α)] : Type (u + 1) :=
  Σ L : V.FredOp S α, DetRay L.1

/-- **`Ĝr_F(α)`** (2021 p. 856): finite formal sums `∑ σ_L̂ · L̂` of oriented sc-Fredholm
operators with non-negative rational weights. -/
abbrev GrFHat (α : C.Obj) [Fact (S.TangentObj α)] : Type (u + 1) := V.OrFredOp S α →₀ ℚ≥0

/-- The formal sums of sc-Fredholm operators without orientations. -/
abbrev GrF (α : C.Obj) [Fact (S.TangentObj α)] : Type (u + 1) := V.FredOp S α →₀ ℚ≥0

variable {V S}

/-- Two oriented operators are equal when the operators are and the orientations correspond
under the identification `det(L) = det(L')`. -/
theorem OrFredOp.ext' {α : C.Obj} [Fact (S.TangentObj α)] {x y : V.OrFredOp S α}
    (h : x.1.1 = y.1.1) (ho : DetRay.cast h x.2 = y.2) : x = y :=
  sigma_ray_ext h ho

/-- **Over every sc-Fredholm operator there are exactly two oriented ones** (`det(L)` is a
line). -/
theorem exists_two_orFredOp {α : C.Obj} [Fact (S.TangentObj α)] (L : V.FredOp S α) :
    ∃ q₁ q₂ : V.OrFredOp S α, q₁.1 = L ∧ q₂.1 = L ∧ q₁ ≠ q₂ ∧
      ∀ q : V.OrFredOp S α, q.1 = L → q = q₁ ∨ q = q₂ :=
  exists_two_sigma_ray (fun _ h => h) L

/-! ### `φ_*` on oriented operators and on `Ĝr_F(α)` -/

section Push

variable {α α' α'' : C.Obj} [Fact (S.TangentObj α)] [Fact (S.TangentObj α')]
  [Fact (S.TangentObj α'')]

/-- `φ_* L ∘ Tφ = μ(φ) ∘ L`. -/
theorem linPush_tangentMorCLE (φ : C.Mor) (hs : C.toGroupoidStr.src φ = α)
    (ht : C.toGroupoidStr.tgt φ = α') (L : S.TangentSpaceAt α →ₗ[ℝ] V.V α)
    (v : S.TangentSpaceAt α) :
    linPush (V := V) (S := S) φ hs ht L ((S.tangentMorCLE φ hs ht).toLinearEquiv v) =
      (V.morFiber φ hs ht).toLinearEquiv (L v) := by
  change V.morFiber φ hs ht (L ((S.tangentMorCLE φ hs ht).symm (S.tangentMorCLE φ hs ht v))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rfl

/-- **`φ_* L = μ(φ) ∘ L ∘ Tφ⁻¹`** on sc-Fredholm operators (2021 p. 856). -/
def fredPush (φ : C.Mor) (hs : C.toGroupoidStr.src φ = α) (ht : C.toGroupoidStr.tgt φ = α')
    (L : V.FredOp S α) : V.FredOp S α' :=
  linConjFred (S.tangentMorCLE φ hs ht).toLinearEquiv (V.morFiber φ hs ht).toLinearEquiv L

/-- `fredPush` is the `φ_*` of `linPush` (2021 p. 845). -/
theorem fredPush_val (φ : C.Mor) (hs : C.toGroupoidStr.src φ = α)
    (ht : C.toGroupoidStr.tgt φ = α') (L : V.FredOp S α) :
    (fredPush φ hs ht L).1 = linPush φ hs ht L.1 := rfl

/-- **`φ_*(L, o) = (φ_* L, φ_* o)`** (2021 p. 856), `φ_* o` the image of `o` under
`det(L) ≅ det(φ_* L)` (the conjugation by `Tφ` and `μ(φ)`, `linConjDet`). -/
def orFredPush (φ : C.Mor) (hs : C.toGroupoidStr.src φ = α) (ht : C.toGroupoidStr.tgt φ = α')
    (x : V.OrFredOp S α) : V.OrFredOp S α' :=
  linConjRay (S.tangentMorCLE φ hs ht).toLinearEquiv (V.morFiber φ hs ht).toLinearEquiv x

theorem orFredPush_fst (φ : C.Mor) (hs : C.toGroupoidStr.src φ = α)
    (ht : C.toGroupoidStr.tgt φ = α') (x : V.OrFredOp S α) :
    (orFredPush φ hs ht x).1 = fredPush φ hs ht x.1 := rfl

theorem tangentMorCLE_unit_toLinearEquiv :
    (S.tangentMorCLE (C.toGroupoidStr.unit α) (C.toGroupoidStr.src_unit α)
      (C.toGroupoidStr.tgt_unit α)).toLinearEquiv = LinearEquiv.refl ℝ _ := by
  rw [(proposition_17_2_5 (S := S)).2.1 α]
  rfl

theorem morFiber_unit_toLinearEquiv :
    (V.morFiber (C.toGroupoidStr.unit α) (C.toGroupoidStr.src_unit α)
      (C.toGroupoidStr.tgt_unit α)).toLinearEquiv = LinearEquiv.refl ℝ _ := by
  rw [morFiber_unit]
  rfl

theorem tangentMorCLE_comp_toLinearEquiv (φ ψ : C.Mor) (hs : C.toGroupoidStr.src φ = α)
    (ht : C.toGroupoidStr.tgt φ = α') (hs' : C.toGroupoidStr.src ψ = α')
    (ht' : C.toGroupoidStr.tgt ψ = α'') :
    (S.tangentMorCLE (C.toGroupoidStr.comp ψ φ)
      ((C.toGroupoidStr.src_comp ψ φ (hs'.trans ht.symm)).trans hs)
      ((C.toGroupoidStr.tgt_comp ψ φ (hs'.trans ht.symm)).trans ht')).toLinearEquiv =
      (S.tangentMorCLE φ hs ht).toLinearEquiv.trans (S.tangentMorCLE ψ hs' ht').toLinearEquiv := by
  rw [(proposition_17_2_5 (S := S)).2.2 α α' α'' φ ψ hs ht hs' ht']
  rfl

theorem morFiber_comp_toLinearEquiv (φ ψ : C.Mor) (hs : C.toGroupoidStr.src φ = α)
    (ht : C.toGroupoidStr.tgt φ = α') (hs' : C.toGroupoidStr.src ψ = α')
    (ht' : C.toGroupoidStr.tgt ψ = α'') :
    (V.morFiber (C.toGroupoidStr.comp ψ φ)
      ((C.toGroupoidStr.src_comp ψ φ (hs'.trans ht.symm)).trans hs)
      ((C.toGroupoidStr.tgt_comp ψ φ (hs'.trans ht.symm)).trans ht')).toLinearEquiv =
      (V.morFiber φ hs ht).toLinearEquiv.trans (V.morFiber ψ hs' ht').toLinearEquiv := by
  rw [morFiber_comp φ ψ hs ht hs' ht']
  rfl

/-- **`(1_α)_* = Id`** on oriented operators. -/
theorem orFredPush_unit (x : V.OrFredOp S α) :
    orFredPush (C.toGroupoidStr.unit α) (C.toGroupoidStr.src_unit α)
      (C.toGroupoidStr.tgt_unit α) x = x :=
  (linConjRay_congr tangentMorCLE_unit_toLinearEquiv morFiber_unit_toLinearEquiv x).trans
    (linConjRay_refl x)

/-- **`(ψ φ)_* = ψ_* φ_*`** on oriented operators. -/
theorem orFredPush_comp (φ ψ : C.Mor) (hs : C.toGroupoidStr.src φ = α)
    (ht : C.toGroupoidStr.tgt φ = α') (hs' : C.toGroupoidStr.src ψ = α')
    (ht' : C.toGroupoidStr.tgt ψ = α'') (x : V.OrFredOp S α) :
    orFredPush (C.toGroupoidStr.comp ψ φ)
        ((C.toGroupoidStr.src_comp ψ φ (hs'.trans ht.symm)).trans hs)
        ((C.toGroupoidStr.tgt_comp ψ φ (hs'.trans ht.symm)).trans ht') x =
      orFredPush ψ hs' ht' (orFredPush φ hs ht x) :=
  (linConjRay_congr (tangentMorCLE_comp_toLinearEquiv φ ψ hs ht hs' ht')
    (morFiber_comp_toLinearEquiv φ ψ hs ht hs' ht') x).trans (linConjRay_trans _ _ _ _ x)

/-- **`φ_*` fixes the orientations of an isomorphism `L` with `φ_* L = L`**: for a bijective
`L` the determinant isomorphism of the conjugation is the identity of `det(L) = λ(0) ⊗ λ*(0)`. -/
theorem orFredPush_eq_self_of_bijective (φ : C.Mor) (hs : C.toGroupoidStr.src φ = α)
    (ht : C.toGroupoidStr.tgt φ = α) (x : V.OrFredOp S α) (hL : linPush φ hs ht x.1.1 = x.1.1)
    (hb : Bijective x.1.1) : orFredPush φ hs ht x = x :=
  linConjRay_eq_self_of_bijective _ _ x hL hb

/-- **`φ_*` on `Ĝr_F`** (2021 p. 856): `φ_*(∑ σ_L̂ · L̂) = ∑ σ_L̂ · φ_* L̂`. -/
def grFHatPush (φ : C.Mor) (hs : C.toGroupoidStr.src φ = α) (ht : C.toGroupoidStr.tgt φ = α')
    (w : V.GrFHat S α) : V.GrFHat S α' :=
  Finsupp.mapDomain (orFredPush φ hs ht) w

theorem grFHatPush_single (φ : C.Mor) (hs : C.toGroupoidStr.src φ = α)
    (ht : C.toGroupoidStr.tgt φ = α') (x : V.OrFredOp S α) (c : ℚ≥0) :
    grFHatPush φ hs ht (Finsupp.single x c) = Finsupp.single (orFredPush φ hs ht x) c :=
  Finsupp.mapDomain_single

theorem grFHatPush_congr {φ φ' : C.Mor} (h : φ = φ') (hs : C.toGroupoidStr.src φ = α)
    (ht : C.toGroupoidStr.tgt φ = α') (hs' : C.toGroupoidStr.src φ' = α)
    (ht' : C.toGroupoidStr.tgt φ' = α') (w : V.GrFHat S α) :
    grFHatPush φ hs ht w = grFHatPush φ' hs' ht' w := by
  subst h
  rfl

/-- `(1_α)_* = Id` on `Ĝr_F(α)`. -/
theorem grFHatPush_unit (w : V.GrFHat S α) :
    grFHatPush (C.toGroupoidStr.unit α) (C.toGroupoidStr.src_unit α)
      (C.toGroupoidStr.tgt_unit α) w = w := by
  rw [grFHatPush]
  conv_rhs => rw [← Finsupp.mapDomain_id (v := w)]
  exact Finsupp.mapDomain_congr fun x _ => orFredPush_unit x

/-- `(ψ φ)_* = ψ_* φ_*` on `Ĝr_F`. -/
theorem grFHatPush_comp (φ ψ : C.Mor) (hs : C.toGroupoidStr.src φ = α)
    (ht : C.toGroupoidStr.tgt φ = α') (hs' : C.toGroupoidStr.src ψ = α')
    (ht' : C.toGroupoidStr.tgt ψ = α'') (w : V.GrFHat S α) :
    grFHatPush (C.toGroupoidStr.comp ψ φ)
        ((C.toGroupoidStr.src_comp ψ φ (hs'.trans ht.symm)).trans hs)
        ((C.toGroupoidStr.tgt_comp ψ φ (hs'.trans ht.symm)).trans ht') w =
      grFHatPush ψ hs' ht' (grFHatPush φ hs ht w) := by
  rw [grFHatPush, grFHatPush, grFHatPush, ← Finsupp.mapDomain_comp]
  exact Finsupp.mapDomain_congr fun x _ => orFredPush_comp φ ψ hs ht hs' ht' x

/-- `φ_*` on formal sums of sc-Fredholm operators. -/
def grFPush (φ : C.Mor) (hs : C.toGroupoidStr.src φ = α) (ht : C.toGroupoidStr.tgt φ = α')
    (w : V.GrF S α) : V.GrF S α' :=
  Finsupp.mapDomain (fredPush φ hs ht) w

theorem grFPush_congr {φ φ' : C.Mor} (h : φ = φ') (hs : C.toGroupoidStr.src φ = α)
    (ht : C.toGroupoidStr.tgt φ = α') (hs' : C.toGroupoidStr.src φ' = α)
    (ht' : C.toGroupoidStr.tgt φ' = α') (w : V.GrF S α) :
    grFPush φ hs ht w = grFPush φ' hs' ht' w := by
  subst h
  rfl

theorem grFPush_unit (w : V.GrF S α) :
    grFPush (C.toGroupoidStr.unit α) (C.toGroupoidStr.src_unit α)
      (C.toGroupoidStr.tgt_unit α) w = w := by
  rw [grFPush]
  conv_rhs => rw [← Finsupp.mapDomain_id (v := w)]
  exact Finsupp.mapDomain_congr fun L _ =>
    (linConjFred_congr tangentMorCLE_unit_toLinearEquiv morFiber_unit_toLinearEquiv L).trans
      (linConjFred_refl L)

theorem grFPush_comp (φ ψ : C.Mor) (hs : C.toGroupoidStr.src φ = α)
    (ht : C.toGroupoidStr.tgt φ = α') (hs' : C.toGroupoidStr.src ψ = α')
    (ht' : C.toGroupoidStr.tgt ψ = α'') (w : V.GrF S α) :
    grFPush (C.toGroupoidStr.comp ψ φ)
        ((C.toGroupoidStr.src_comp ψ φ (hs'.trans ht.symm)).trans hs)
        ((C.toGroupoidStr.tgt_comp ψ φ (hs'.trans ht.symm)).trans ht') w =
      grFPush ψ hs' ht' (grFPush φ hs ht w) := by
  rw [grFPush, grFPush, grFPush, ← Finsupp.mapDomain_comp]
  exact Finsupp.mapDomain_congr fun L _ =>
    (linConjFred_congr (tangentMorCLE_comp_toLinearEquiv φ ψ hs ht hs' ht')
      (morFiber_comp_toLinearEquiv φ ψ hs ht hs' ht') L).trans (linConjFred_trans _ _ _ _ L)

variable (V S) in
/-- **Forgetting the orientations**: `∑ σ · (L, o) ↦ ∑ σ · L`. -/
def grFForget (α : C.Obj) [Fact (S.TangentObj α)] (w : V.GrFHat S α) : V.GrF S α :=
  Finsupp.mapDomain Sigma.fst w

/-- Forgetting the orientations commutes with `φ_*`. -/
theorem grFForget_grFHatPush (φ : C.Mor) (hs : C.toGroupoidStr.src φ = α)
    (ht : C.toGroupoidStr.tgt φ = α') (w : V.GrFHat S α) :
    V.grFForget S α' (grFHatPush φ hs ht w) = grFPush φ hs ht (V.grFForget S α w) := by
  rw [grFForget, grFHatPush, grFPush, grFForget, ← Finsupp.mapDomain_comp,
    ← Finsupp.mapDomain_comp]
  rfl

end Push

/-! ### The category `Ĝr_F(C) → C_∞` -/

section Category

variable (hU : S.HasUniformizers)

variable (V) in
/-- `Ĝr_F(α)` for an object `α` of `C_∞`. -/
abbrev GrFHatC (α : S.regSubInf.Ob) : Type (u + 1) :=
  letI : Fact (S.TangentObj (smoothObjVal α)) := ⟨tangentObj_smoothObjVal hU α⟩
  V.GrFHat S (smoothObjVal α)

variable (V) in
/-- The formal sums of sc-Fredholm operators at an object of `C_∞`. -/
abbrev GrFC (α : S.regSubInf.Ob) : Type (u + 1) :=
  letI : Fact (S.TangentObj (smoothObjVal α)) := ⟨tangentObj_smoothObjVal hU α⟩
  V.GrF S (smoothObjVal α)

/-- `φ_*` on `Ĝr_F`, for a morphism `φ` of `C_∞`. -/
def grFHatMap {α β : S.regSubInf.Ob} (f : α ⟶ β) (w : V.GrFHatC hU α) : V.GrFHatC hU β :=
  letI : Fact (S.TangentObj (smoothObjVal α)) := ⟨tangentObj_smoothObjVal hU α⟩
  letI : Fact (S.TangentObj (smoothObjVal β)) := ⟨tangentObj_smoothObjVal hU β⟩
  grFHatPush (smoothMorVal f) (src_smoothMorVal f) (tgt_smoothMorVal f) w

/-- `φ_*` on unoriented formal sums, for a morphism `φ` of `C_∞`. -/
def grFMap {α β : S.regSubInf.Ob} (f : α ⟶ β) (w : V.GrFC hU α) : V.GrFC hU β :=
  letI : Fact (S.TangentObj (smoothObjVal α)) := ⟨tangentObj_smoothObjVal hU α⟩
  letI : Fact (S.TangentObj (smoothObjVal β)) := ⟨tangentObj_smoothObjVal hU β⟩
  grFPush (smoothMorVal f) (src_smoothMorVal f) (tgt_smoothMorVal f) w

theorem grFHatMap_id (α : S.regSubInf.Ob) : grFHatMap (V := V) hU (𝟙 α) = id := by
  let : Fact (S.TangentObj (smoothObjVal α)) := ⟨tangentObj_smoothObjVal hU α⟩
  exact funext fun w => grFHatPush_unit w

theorem grFHatMap_comp {α β γ : S.regSubInf.Ob} (f : α ⟶ β) (g : β ⟶ γ) :
    grFHatMap (V := V) hU (f ≫ g) = grFHatMap hU g ∘ grFHatMap hU f := by
  let : Fact (S.TangentObj (smoothObjVal α)) := ⟨tangentObj_smoothObjVal hU α⟩
  let : Fact (S.TangentObj (smoothObjVal β)) := ⟨tangentObj_smoothObjVal hU β⟩
  let : Fact (S.TangentObj (smoothObjVal γ)) := ⟨tangentObj_smoothObjVal hU γ⟩
  funext w
  exact (grFHatPush_congr (smoothMorVal_comp f g) _ _ _ _ w).trans
    (grFHatPush_comp _ _ (src_smoothMorVal f) (tgt_smoothMorVal f) (src_smoothMorVal g)
      (tgt_smoothMorVal g) w)

theorem grFMap_id (α : S.regSubInf.Ob) : grFMap (V := V) hU (𝟙 α) = id := by
  let : Fact (S.TangentObj (smoothObjVal α)) := ⟨tangentObj_smoothObjVal hU α⟩
  exact funext fun w => grFPush_unit w

theorem grFMap_comp {α β γ : S.regSubInf.Ob} (f : α ⟶ β) (g : β ⟶ γ) :
    grFMap (V := V) hU (f ≫ g) = grFMap hU g ∘ grFMap hU f := by
  let : Fact (S.TangentObj (smoothObjVal α)) := ⟨tangentObj_smoothObjVal hU α⟩
  let : Fact (S.TangentObj (smoothObjVal β)) := ⟨tangentObj_smoothObjVal hU β⟩
  let : Fact (S.TangentObj (smoothObjVal γ)) := ⟨tangentObj_smoothObjVal hU γ⟩
  funext w
  exact (grFPush_congr (smoothMorVal_comp f g) _ _ _ _ w).trans
    (grFPush_comp _ _ (src_smoothMorVal f) (tgt_smoothMorVal f) (src_smoothMorVal g)
      (tgt_smoothMorVal g) w)

variable (V S) in
/-- **The functor `α ↦ Ĝr_F(α)`, `φ ↦ φ_*`** on `C_∞` (2021 p. 856). -/
def grFHatFunctor : S.regSubInf.Ob ⥤ Type (u + 1) where
  obj α := V.GrFHatC hU α
  map f := ↾(grFHatMap hU f)
  map_id α := by
    rw [grFHatMap_id]
    rfl
  map_comp f g := by
    rw [grFHatMap_comp]
    rfl

variable (V S) in
/-- The functor of formal sums of sc-Fredholm operators (no orientations) on `C_∞`. -/
def grFFunctor : S.regSubInf.Ob ⥤ Type (u + 1) where
  obj α := V.GrFC hU α
  map f := ↾(grFMap hU f)
  map_id α := by
    rw [grFMap_id]
    rfl
  map_comp f g := by
    rw [grFMap_comp]
    rfl

theorem grFHatFunctor_map_apply {α β : S.regSubInf.Ob} (f : α ⟶ β)
    (w : (V.grFHatFunctor S hU).obj α) :
    (V.grFHatFunctor S hU).map f w = grFHatMap hU f w :=
  rfl

variable (V S) in
/-- **The category `Ĝr_F(C)`** (2021 p. 856): objects `(α, L)`, `α` smooth and `L ∈ Ĝr_F(α)`;
morphisms `φ : α → α'` of `C_∞` with `φ_* L = L'` (Mathlib's category of elements). -/
abbrev GrFHatCat : Type (u + 1) := (V.grFHatFunctor S hU).Elements

variable (V S) in
/-- **`π̂ : Ĝr_F(C) → C_∞`, `(α, L) ↦ α`** (2021 p. 856). -/
abbrev grFHatProj : V.GrFHatCat S hU ⥤ S.regSubInf.Ob :=
  CategoryOfElements.π (V.grFHatFunctor S hU)

/-- Forgetting the orientations at an object of `C_∞`. -/
def grFForgetC (α : S.regSubInf.Ob) (w : V.GrFHatC hU α) : V.GrFC hU α :=
  letI : Fact (S.TangentObj (smoothObjVal α)) := ⟨tangentObj_smoothObjVal hU α⟩
  V.grFForget S (smoothObjVal α) w

/-- Forgetting the orientations commutes with `φ_*`. -/
theorem grFForgetC_naturality {α β : S.regSubInf.Ob} (f : α ⟶ β) (w : V.GrFHatC hU α) :
    grFForgetC hU β (grFHatMap hU f w) = grFMap hU f (grFForgetC hU α w) := by
  let : Fact (S.TangentObj (smoothObjVal α)) := ⟨tangentObj_smoothObjVal hU α⟩
  let : Fact (S.TangentObj (smoothObjVal β)) := ⟨tangentObj_smoothObjVal hU β⟩
  exact grFForget_grFHatPush _ _ _ w

variable (V S) in
/-- **Forgetting the orientations** as a natural transformation. -/
def grFForgetNat : V.grFHatFunctor S hU ⟶ V.grFFunctor S hU where
  app α := ↾(grFForgetC hU α)
  naturality α β f := by
    have h : (fun w : V.GrFHatC hU α => grFForgetC hU β (grFHatMap hU f w)) =
        fun w => grFMap hU f (grFForgetC hU α w) :=
      funext (grFForgetC_naturality hU f)
    change ↾(fun w : V.GrFHatC hU α => grFForgetC hU β (grFHatMap hU f w)) = _
    rw [h]
    rfl

variable (V S) in
/-- The forgetful functor `Ĝr_F(C) → Gr_F(C)`. -/
abbrev grFForgetFunctor : V.GrFHatCat S hU ⥤ (V.grFFunctor S hU).Elements :=
  CategoryOfElements.map (V.grFForgetNat S hU)

/-- The forgetful functor lies over `C_∞`. -/
theorem grFForgetFunctor_comp_π :
    V.grFForgetFunctor S hU ⋙ CategoryOfElements.π (V.grFFunctor S hU) = V.grFHatProj S hU :=
  CategoryOfElements.map_π _

variable (V S) in
/-- **A morphism `(φ, L)` of `Ĝr_F(C)` as printed** (2021 p. 856): a smooth morphism `φ` and
`L ∈ Ĝr_F(s φ)`, i.e. `s(φ) = π̂(α, L)`. -/
structure GrFMor where
  /-- `s(φ)`. -/
  dom : S.regSubInf.Ob
  /-- `t(φ)`. -/
  cod : S.regSubInf.Ob
  /-- The smooth morphism `φ`. -/
  mor : dom ⟶ cod
  /-- `L ∈ Ĝr_F(s φ)`. -/
  el : (V.grFHatFunctor S hU).obj dom

/-- **`s(φ, L) = (s(φ), L)`**. -/
def GrFMor.src (m : V.GrFMor S hU) : V.GrFHatCat S hU := ⟨m.dom, m.el⟩

/-- **`t(φ, L) = (t(φ), φ_* L)`**. -/
def GrFMor.tgt (m : V.GrFMor S hU) : V.GrFHatCat S hU :=
  ⟨m.cod, (V.grFHatFunctor S hU).map m.mor m.el⟩

/-- `t(φ, L)` carries `φ_* L`. -/
theorem GrFMor.tgt_snd (m : V.GrFMor S hU) :
    m.tgt.2 = grFHatMap hU m.mor m.el := rfl

/-- `(φ, L) : (s(φ), L) → (t(φ), φ_* L)` is a morphism of `Ĝr_F(C)`. -/
def GrFMor.toHom (m : V.GrFMor S hU) : m.src ⟶ m.tgt := ⟨m.mor, rfl⟩

/-- The pair `(φ, L)` of a morphism `φ : (α, L) → (α', L')` of `Ĝr_F(C)`. -/
def GrFMor.ofHom {x y : V.GrFHatCat S hU} (h : x ⟶ y) : V.GrFMor S hU := ⟨x.1, y.1, h.1, x.2⟩

/-- **Every morphism of `Ĝr_F(C)` is a printed pair `(φ, L)`**: its source and target are
`(s φ, L)` and `(t φ, φ_* L)`. -/
theorem GrFMor.ofHom_src_tgt {x y : V.GrFHatCat S hU} (h : x ⟶ y) :
    (GrFMor.ofHom hU h).src = x ∧ (GrFMor.ofHom hU h).tgt = y ∧
      (GrFMor.ofHom hU h).mor = h.1 := by
  obtain ⟨α, w⟩ := x
  obtain ⟨β, w'⟩ := y
  obtain ⟨f, hf⟩ := h
  refine ⟨rfl, ?_, rfl⟩
  change (⟨β, (V.grFHatFunctor S hU).map f w⟩ : V.GrFHatCat S hU) = ⟨β, w'⟩
  rw [hf]

/-- `π̂` of `s(φ, L)` and `t(φ, L)` are `s(φ)`, `t(φ)`. -/
theorem GrFMor.proj_src_tgt (m : V.GrFMor S hU) :
    (V.grFHatProj S hU).obj m.src = m.dom ∧
      (V.grFHatProj S hU).obj m.tgt = m.cod ∧
      (V.grFHatProj S hU).map m.toHom = m.mor :=
  ⟨rfl, rfl, rfl⟩

end Category

/-! ### Relation to `DET(f, α) → Lin(f, α)` -/

section Lin

namespace StrongPolyfoldBundleConstruction

variable (Q : V.StrongPolyfoldBundleConstruction S) {f : V.SectionFunctor}
  (hF : Q.IsScFredholmSectionFunctor f)

/-- **A member of `Lin(f, α)` is an sc-Fredholm operator `T_αC → E_α`** (Definition 18.1.4,
`exists_index_linSetLoc`). -/
def linFredOp {α : C.Obj} [Fact (S.TangentObj α)]
    (L : Q.linSetLoc f hF.isScSmoothSectionFunctor α) : V.FredOp S α :=
  ⟨L.1, ((Q.exists_index_linSetLoc hF α).choose_spec L.1 L.2).1⟩

theorem linFredOp_val {α : C.Obj} [Fact (S.TangentObj α)]
    (L : Q.linSetLoc f hF.isScSmoothSectionFunctor α) : (Q.linFredOp hF L).1 = L.1 := rfl

/-- **`φ_*` on sc-Fredholm operators restricts to the `φ_*` of `Lin(f, α)`** (Definition 18.1.4,
`linPush_mem_linSetLoc`). -/
theorem fredPush_linFredOp {α α' : C.Obj} [Fact (S.TangentObj α)] [Fact (S.TangentObj α')]
    (φ : C.Mor) (hs : C.toGroupoidStr.src φ = α) (ht : C.toGroupoidStr.tgt φ = α')
    (hne' : (Q.F α').Nonempty) (L : Q.linSetLoc f hF.isScSmoothSectionFunctor α) :
    fredPush φ hs ht (Q.linFredOp hF L) =
      Q.linFredOp hF ⟨linPush φ hs ht L.1, Q.linPush_mem_linSetLoc _ φ hs ht hne' L.2⟩ :=
  Subtype.ext rfl

/-- **The oriented operator `(L, ω_L)`** for a choice `ω` of an orientation of `det(L)` for every
`L ∈ Lin(f, α)` (the fibres of `DET(f, α) → Lin(f, α)`). -/
def linOrLift {α : C.Obj} [Fact (S.TangentObj α)]
    (ω : ∀ L : Q.linSetLoc f hF.isScSmoothSectionFunctor α, DetRay L.1)
    (L : Q.linSetLoc f hF.isScSmoothSectionFunctor α) : V.OrFredOp S α :=
  ⟨Q.linFredOp hF L, ω L⟩

/-- **The oriented lift `∑ σ_L · L ↦ ∑ σ_L · (L, ω_L)`** of a formal sum of members of
`Lin(f, α)` into `Ĝr_F(α)`. -/
def linCanonLift {α : C.Obj} [Fact (S.TangentObj α)]
    (ω : ∀ L : Q.linSetLoc f hF.isScSmoothSectionFunctor α, DetRay L.1)
    (w : Q.linSetLoc f hF.isScSmoothSectionFunctor α →₀ ℚ≥0) : V.GrFHat S α :=
  Finsupp.mapDomain (Q.linOrLift hF ω) w

/-- Forgetting the orientations of the lift gives back the formal sum of members of `Lin(f, α)`. -/
theorem grFForget_linCanonLift {α : C.Obj} [Fact (S.TangentObj α)]
    (ω : ∀ L : Q.linSetLoc f hF.isScSmoothSectionFunctor α, DetRay L.1)
    (w : Q.linSetLoc f hF.isScSmoothSectionFunctor α →₀ ℚ≥0) :
    V.grFForget S α (Q.linCanonLift hF ω w) = Finsupp.mapDomain (Q.linFredOp hF) w := by
  rw [grFForget, linCanonLift, ← Finsupp.mapDomain_comp]
  rfl

/-- **The two-point fibre**: an oriented operator over `L ∈ Lin(f, α)` is `(L, ω_L)` or
`(L, −ω_L)`. -/
theorem linOrLift_or_neg {α : C.Obj} [Fact (S.TangentObj α)]
    (ω : ∀ L : Q.linSetLoc f hF.isScSmoothSectionFunctor α, DetRay L.1)
    (L : Q.linSetLoc f hF.isScSmoothSectionFunctor α) (q : V.OrFredOp S α)
    (hq : q.1 = Q.linFredOp hF L) :
    q = Q.linOrLift hF ω L ∨ q = ⟨Q.linFredOp hF L, -ω L⟩ :=
  sigma_ray_eq_or_neg (fun _ h => h) (Q.linFredOp hF L) (ω L) q hq

/-- **`φ_*` carries the lift of `ω` to the lift of `ω'`** when `ω'` is the image of `ω` under
`φ_*` on the fibres of `DET` (the law `o_{t(φ)} = φ_* o_{s(φ)}` of an orientation, read in
`Ĝr_F`). -/
theorem orFredPush_linOrLift {α α' : C.Obj} [Fact (S.TangentObj α)] [Fact (S.TangentObj α')]
    (φ : C.Mor) (hs : C.toGroupoidStr.src φ = α) (ht : C.toGroupoidStr.tgt φ = α')
    (hne' : (Q.F α').Nonempty)
    (ω : ∀ L : Q.linSetLoc f hF.isScSmoothSectionFunctor α, DetRay L.1)
    (ω' : ∀ L : Q.linSetLoc f hF.isScSmoothSectionFunctor α', DetRay L.1)
    (L : Q.linSetLoc f hF.isScSmoothSectionFunctor α)
    (hω : DetRay.cast
          (show (fredPush φ hs ht (Q.linFredOp hF L)).1 = linPush φ hs ht L.1 from rfl)
        (orFredPush φ hs ht (Q.linOrLift hF ω L)).2 =
      ω' ⟨linPush φ hs ht L.1, Q.linPush_mem_linSetLoc _ φ hs ht hne' L.2⟩) :
    orFredPush φ hs ht (Q.linOrLift hF ω L) =
      Q.linOrLift hF ω' ⟨linPush φ hs ht L.1, Q.linPush_mem_linSetLoc _ φ hs ht hne' L.2⟩ :=
  OrFredOp.ext' (x := orFredPush φ hs ht (Q.linOrLift hF ω L))
    (y := Q.linOrLift hF ω' ⟨linPush φ hs ht L.1, Q.linPush_mem_linSetLoc _ φ hs ht hne' L.2⟩)
    rfl hω

end StrongPolyfoldBundleConstruction

end Lin

end GCT.VectorBundle

/-! ### Witness: the reflection bundle -/

namespace GCT.VectorBundle.ReflectionBundle

open GroupoidalCategory GroupoidalCategory.BanachFunctor StrongPolyfoldBundleConstruction
  PolyfoldConstruction

/-- The smooth object `0` of `ℤ/2 ⋉ ℝ` as an object of `C_∞`. -/
def smoothZero : reflectionConstruction.regSubInf.Ob :=
  (⟨0, reflection_isSmoothObj 0⟩ : reflectionConstruction.regSetInf)

/-- The isotropy `g = (−1, 0)` of `0` as a morphism of `C_∞`. -/
def smoothNeg : smoothZero ⟶ smoothZero :=
  ⟨⟨((-1 : ℤˣ), (0 : Fin 1 → ℝ)), reflection_isSmoothObj 0,
    show reflectionConstruction.IsSmoothObj ((-1 : ℤˣ) • (0 : Fin 1 → ℝ)) by
      rw [smul_zero]; exact reflection_isSmoothObj 0⟩,
    rfl, Subtype.ext (smul_zero _)⟩

/-- **Witness for `Ĝr_F(C)`** on the reflection bundle with `f(x) = (x, x)`, at the smooth object
`0` whose isotropy `g = (−1, 0)` acts on `E_0` by `v ↦ −v`: the linearization `f'(0) ∈ Lin(f, 0)`
is an sc-Fredholm operator with exactly two orientations `q₁ ≠ q₂`; they give two different
objects `(0, 1 · q₁)`, `(0, 1 · q₂)` of `Ĝr_F(C)` over `0`; `g_*` maps the fibre over `f'(0)`
to itself, and `(g, 1 · q)` is a morphism of `Ĝr_F(C)` from `(0, 1 · q)` to `(0, 1 · g_* q)`. -/
theorem reflection_grFHat :
    ∃ q₁ q₂ : reflV.OrFredOp reflectionConstruction 0,
      q₁.1.1 = reflQ.linearization reflDiag
          isScFredholmSectionFunctor_reflDiag.isScSmoothSectionFunctor 0 reflDiag_toFun_zero
          ⟨reflUnif, rfl⟩ ∧
      q₂.1 = q₁.1 ∧ q₁ ≠ q₂ ∧
      (Finsupp.single q₁ (1 : ℚ≥0) ≠ Finsupp.single q₂ 1) ∧
      (∀ q : reflV.OrFredOp reflectionConstruction 0, q.1 = q₁.1 → q = q₁ ∨ q = q₂) ∧
      (∀ q : reflV.OrFredOp reflectionConstruction 0, q.1 = q₁.1 →
        (orFredPush (V := reflV) (S := reflectionConstruction)
            (α := (0 : Fin 1 → ℝ)) (α' := (0 : Fin 1 → ℝ)) ((-1 : ℤˣ), (0 : Fin 1 → ℝ)) rfl
            (smul_zero _) q).1 = q₁.1) ∧
      (∀ v : Fin 1 → ℝ, v ≠ 0 → reflV.map ((-1 : ℤˣ), (0 : Fin 1 → ℝ)) v ≠ v) ∧
      ∀ q : reflV.OrFredOp reflectionConstruction 0,
        let m : reflV.GrFMor reflectionConstruction reflectionConstruction_hasUniformizers :=
          ⟨smoothZero, smoothZero, smoothNeg, Finsupp.single q 1⟩
        m.src.2 = Finsupp.single q 1 ∧
          m.tgt.2 = Finsupp.single
            (orFredPush (V := reflV) (S := reflectionConstruction)
            (α := (0 : Fin 1 → ℝ)) (α' := (0 : Fin 1 → ℝ)) ((-1 : ℤˣ), (0 : Fin 1 → ℝ)) rfl
            (smul_zero _) q) 1 := by
  have hL := definition_18_1_4_local_reflDiag.1
  have hi := definition_18_1_4_local_reflDiag.2.2.1.choose_spec
  have hex := exists_two_orFredOp (V := reflV) (S := reflectionConstruction) (α := 0)
    ⟨_, (hi _ hL).1⟩
  have h := hex.choose_spec.choose_spec
  have hL₁ : hex.choose.1.1 = (reflQ.linearization reflDiag
      isScFredholmSectionFunctor_reflDiag.isScSmoothSectionFunctor 0 reflDiag_toFun_zero
      ⟨reflUnif, rfl⟩) := congrArg Subtype.val h.1
  refine ⟨hex.choose, hex.choose_spec.choose, hL₁, h.2.1.trans h.1.symm, h.2.2.1,
    fun h' => h.2.2.1 (Finsupp.single_left_injective one_ne_zero h'),
    fun q hq => h.2.2.2 q (hq.trans h.1), fun q hq => Subtype.ext ?_,
    fun _ hv => reflV_map_ne 0 hv, fun q => ⟨rfl, grFHatPush_single (V := reflV)
      (S := reflectionConstruction) (α := (0 : Fin 1 → ℝ)) (α' := (0 : Fin 1 → ℝ))
      ((-1 : ℤˣ), (0 : Fin 1 → ℝ)) rfl (smul_zero _) q 1⟩⟩
  have hq₀ : q.1.1 = (reflQ.linearization reflDiag
      isScFredholmSectionFunctor_reflDiag.isScSmoothSectionFunctor 0 reflDiag_toFun_zero
      ⟨reflUnif, rfl⟩) := (congrArg Subtype.val hq).trans hL₁
  exact (congrArg (linPush (V := reflV) (S := reflectionConstruction) (α := (0 : Fin 1 → ℝ))
      (α' := (0 : Fin 1 → ℝ)) ((-1 : ℤˣ), (0 : Fin 1 → ℝ)) rfl (smul_zero _)) hq₀).trans
    ((reflQ.linPush_linearization (α := (0 : Fin 1 → ℝ)) (α' := (0 : Fin 1 → ℝ))
      isScFredholmSectionFunctor_reflDiag.isScSmoothSectionFunctor
      ((-1 : ℤˣ), (0 : Fin 1 → ℝ)) rfl (smul_zero _) reflDiag_toFun_zero
      ⟨reflUnif, rfl⟩ ⟨reflUnif, rfl⟩).trans hL₁.symm)

end GCT.VectorBundle.ReflectionBundle

end Polyfold
