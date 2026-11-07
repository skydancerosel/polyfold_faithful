import Polyfold.Chapter6.FredholmDet
import Mathlib.Analysis.LocallyConvex.HahnBanach

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.3, p. 214:
**Definition 6.16**, the isomorphism `det(T) ⊗ det(S) → det(T ⊕ S)` *(book 2017: Definition 6.7;
see `BookConcordance.md`)*.

# The determinant of a direct sum

## The text, paraphrased

For Fredholm operators `T : E → F` and `S : E' → F'`, `T ⊕ S : E ⊕ E' → F ⊕ F'` is Fredholm, and
`det(T) ⊗ det(S) → det(T ⊕ S)` maps `((a₁ ∧ … ∧ aₙ) ⊗ (d₁ ∧ … ∧ d_l)*) ⊗
((a'₁ ∧ … ∧ a'ₙ') ⊗ (d'₁ ∧ … ∧ d'_l')*)` to `(a₁ ∧ … ∧ aₙ ∧ a'₁ ∧ … ∧ a'ₙ') ⊗
(d₁ ∧ … ∧ d_l ∧ d'₁ ∧ … ∧ d'_l')*`.

## What is formalized

* `Polyfold.kerInl`, `kerInr`, `cokerInl`, `cokerInr`: `a ↦ (a, 0)`, `a' ↦ (0, a')` on kernels and
  the same on cokernels; `kerProdEquiv`, `cokerProdEquiv`: together they give
  `ker T × ker S ≅ ker(T ⊕ S)` and `coker T × coker S ≅ coker(T ⊕ S)`; `finrank_ker_prodMap`,
  `finrank_coker_prodMap`, `isFredholm_prodMap`.
* `Polyfold.directSumDet` (**Definition 6.16**), defined by the formula for one choice of bases;
  `directSumVec_eq_smul`: how `(a ∧ a') ⊗ (d ∧ d')*` changes with the bases;
  `definition_6_16`: the formula holds for all bases; `directSumDet_bijective`.

## Reading

Definition 6.16 is a definition by a formula in bases; "natural" is read as: the map defined by one
choice satisfies the formula for every choice (as in Lemma 6.5).  Bases are indexed by
`Fin (dim …)`, the vectors `(a, 0)`, `(0, a')`, `(d, 0)`, `(0, d')` are read through `kerInl` etc.
-/

open Module TensorProduct

noncomputable section

namespace Polyfold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

section Lines

/-- `(c v)* = c⁻¹ v*` for `c ≠ 0` and every vector `v` (both sides vanish when `v = 0` or the space
is not a line). -/
theorem dualVec_smul_of_ne_zero {L : Type*} [AddCommGroup L] [Module ℝ L] (v : L) {c : ℝ}
    (hc : c ≠ 0) : dualVec (c • v) = c⁻¹ • dualVec v := by
  by_cases h : v ≠ 0 ∧ finrank ℝ L = 1
  · exact dualVec_smul h.2 h.1 hc
  · have h' : ¬ (c • v ≠ 0 ∧ finrank ℝ L = 1) := by
      rwa [Ne, smul_eq_zero, or_iff_right hc]
    rw [dualVec, dif_neg h', dualVec, dif_neg h, smul_zero]

/-- **Change of bases in `λ(K) ⊗ λ*(C)`**: `(a₁ ∧ … ∧ aₙ) ⊗ (d₁ ∧ … ∧ d_l)* =
(det_{a₀} a / det_{d₀} d) · (a₀ ∧ …) ⊗ (d₀ ∧ …)*` for bases `a`, `a₀` of `K` and `d`, `d₀` of
`C`. -/
theorem wedge_tmul_dualVec_eq_smul {K C : Type*} [AddCommGroup K] [Module ℝ K]
    [FiniteDimensional ℝ K] [AddCommGroup C] [Module ℝ C] [FiniteDimensional ℝ C]
    (a a₀ : Basis (Fin (finrank ℝ K)) ℝ K) (d d₀ : Basis (Fin (finrank ℝ C)) ℝ C) :
    wedge a rfl ⊗ₜ[ℝ] dualVec (wedge d rfl) =
      (a₀.det a * (d₀.det d)⁻¹) • (wedge a₀ rfl ⊗ₜ[ℝ] dualVec (wedge d₀ rfl)) := by
  rw [wedge_eq_det_smul a₀ a, wedge_eq_det_smul d₀ d,
    dualVec_smul_of_ne_zero _ (d₀.isUnit_det d).ne_zero, TensorProduct.smul_tmul_smul]

/-- If `f + g : U × V → W` is onto, the images under `f` and `g` of bases of `U` and `V` together
span `W`. -/
theorem top_le_span_append_of_surjective {U V W : Type*} [AddCommGroup U] [Module ℝ U]
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W] {p q : ℕ} (f : U →ₗ[ℝ] W)
    (g : V →ₗ[ℝ] W) (hfg : Function.Surjective (f.coprod g)) (u : Basis (Fin p) ℝ U)
    (v : Basis (Fin q) ℝ V) :
    ⊤ ≤ Submodule.span ℝ (Set.range (Fin.append (f ∘ u) (g ∘ v))) := by
  rw [span_range_append, Set.range_comp, Set.range_comp, Submodule.span_image,
    Submodule.span_image, u.span_eq, v.span_eq, Submodule.map_top, Submodule.map_top,
    ← LinearMap.range_coprod, LinearMap.range_eq_top.2 hfg]

/-- A linear map between lines that does not vanish at some nonzero vector is bijective. -/
theorem bijective_of_finrank_eq_one {L M : Type*} [AddCommGroup L] [Module ℝ L]
    [AddCommGroup M] [Module ℝ M] (hL : finrank ℝ L = 1) (hM : finrank ℝ M = 1)
    (f : L →ₗ[ℝ] M) {v : L} (hv : v ≠ 0) (hfv : f v ≠ 0) : Function.Bijective f := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨t, rfl⟩ := exists_smul_eq_of_finrank_eq_one hL hv x
    rw [map_smul] at hx
    rw [(smul_eq_zero.1 hx).resolve_right hfv, zero_smul]
  · intro y
    obtain ⟨t, rfl⟩ := exists_smul_eq_of_finrank_eq_one hM hfv y
    exact ⟨t • v, map_smul f t v⟩

end Lines

section DirectSum

variable {E' F' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F']
  (T : E →L[ℝ] F) (S : E' →L[ℝ] F')

/-- `ker T → ker(T ⊕ S)`, `a ↦ (a, 0)`. -/
def kerInl : LinearMap.ker (T : E →ₗ[ℝ] F) →ₗ[ℝ]
    LinearMap.ker ((T.prodMap S : E × E' →L[ℝ] F × F') : E × E' →ₗ[ℝ] F × F') :=
  LinearMap.codRestrict _ (LinearMap.inl ℝ E E' ∘ₗ (LinearMap.ker (T : E →ₗ[ℝ] F)).subtype)
    (fun x => by simp)

/-- `ker S → ker(T ⊕ S)`, `a' ↦ (0, a')`. -/
def kerInr : LinearMap.ker (S : E' →ₗ[ℝ] F') →ₗ[ℝ]
    LinearMap.ker ((T.prodMap S : E × E' →L[ℝ] F × F') : E × E' →ₗ[ℝ] F × F') :=
  LinearMap.codRestrict _ (LinearMap.inr ℝ E E' ∘ₗ (LinearMap.ker (S : E' →ₗ[ℝ] F')).subtype)
    (fun x => by simp)

/-- `coker T → coker(T ⊕ S)`, `d + R(T) ↦ (d, 0) + R(T ⊕ S)`. -/
def cokerInl : (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) →ₗ[ℝ]
    (F × F') ⧸ LinearMap.range ((T.prodMap S : E × E' →L[ℝ] F × F') : E × E' →ₗ[ℝ] F × F') :=
  (LinearMap.range (T : E →ₗ[ℝ] F)).mapQ _ (LinearMap.inl ℝ F F') (by
    rintro _ ⟨e, rfl⟩
    exact ⟨(e, 0), by simp⟩)

/-- `coker S → coker(T ⊕ S)`, `d' + R(S) ↦ (0, d') + R(T ⊕ S)`. -/
def cokerInr : (F' ⧸ LinearMap.range (S : E' →ₗ[ℝ] F')) →ₗ[ℝ]
    (F × F') ⧸ LinearMap.range ((T.prodMap S : E × E' →L[ℝ] F × F') : E × E' →ₗ[ℝ] F × F') :=
  (LinearMap.range (S : E' →ₗ[ℝ] F')).mapQ _ (LinearMap.inr ℝ F F') (by
    rintro _ ⟨e, rfl⟩
    exact ⟨(0, e), by simp⟩)

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace E'] [CompleteSpace F'] in
/-- `kerInl T S a = (a, 0)`. -/
@[simp] theorem coe_kerInl_apply (x : LinearMap.ker (T : E →ₗ[ℝ] F)) :
    ((kerInl T S x : LinearMap.ker ((T.prodMap S : E × E' →L[ℝ] F × F') : E × E' →ₗ[ℝ] F × F')) :
      E × E') = ((x : E), 0) := rfl

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace E'] [CompleteSpace F'] in
/-- `kerInr T S a' = (0, a')`. -/
@[simp] theorem coe_kerInr_apply (y : LinearMap.ker (S : E' →ₗ[ℝ] F')) :
    ((kerInr T S y : LinearMap.ker ((T.prodMap S : E × E' →L[ℝ] F × F') : E × E' →ₗ[ℝ] F × F')) :
      E × E') = (0, (y : E')) := rfl

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace E'] [CompleteSpace F'] in
/-- `cokerInl T S [d] = [(d, 0)]`. -/
@[simp] theorem cokerInl_mk (f : F) :
    cokerInl T S (Submodule.Quotient.mk f) = Submodule.Quotient.mk (f, 0) := rfl

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace E'] [CompleteSpace F'] in
/-- `cokerInr T S [d'] = [(0, d')]`. -/
@[simp] theorem cokerInr_mk (f' : F') :
    cokerInr T S (Submodule.Quotient.mk f') = Submodule.Quotient.mk (0, f') := rfl

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace E'] [CompleteSpace F'] in
/-- `ker T × ker S → ker(T ⊕ S)`, `(a, a') ↦ (a, 0) + (0, a')`, is bijective. -/
theorem bijective_coprod_kerInl_kerInr :
    Function.Bijective (LinearMap.coprod (kerInl T S) (kerInr T S)) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨x, y⟩ h
    have h1 := Subtype.ext_iff.1 h
    simp only [LinearMap.coprod_apply, Submodule.coe_add, coe_kerInl_apply, coe_kerInr_apply,
      Prod.mk_add_mk, add_zero, zero_add, Submodule.coe_zero, Prod.mk_eq_zero] at h1
    ext
    · simp [h1.1]
    · simp [h1.2]
  · rintro ⟨⟨x, y⟩, hxy⟩
    have hx : T x = 0 ∧ S y = 0 := by simpa using hxy
    refine ⟨(⟨x, hx.1⟩, ⟨y, hx.2⟩), ?_⟩
    apply Subtype.ext
    rw [LinearMap.coprod_apply, Submodule.coe_add, coe_kerInl_apply, coe_kerInr_apply]
    simp

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace E'] [CompleteSpace F'] in
/-- `coker T × coker S → coker(T ⊕ S)`, `([d], [d']) ↦ [(d, 0)] + [(0, d')]`, is bijective. -/
theorem bijective_coprod_cokerInl_cokerInr :
    Function.Bijective (LinearMap.coprod (cokerInl T S) (cokerInr T S)) := by
  have hmk : ∀ (f : F) (f' : F'), LinearMap.coprod (cokerInl T S) (cokerInr T S)
      (Submodule.Quotient.mk f, Submodule.Quotient.mk f') = Submodule.Quotient.mk (f, f') := by
    intro f f'
    rw [LinearMap.coprod_apply, cokerInl_mk, cokerInr_mk, ← Submodule.Quotient.mk_add,
      Prod.mk_add_mk, add_zero, zero_add]
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨x, y⟩ h
    induction x using Submodule.Quotient.induction_on with | H f => ?_
    induction y using Submodule.Quotient.induction_on with | H f' => ?_
    rw [hmk, Submodule.Quotient.mk_eq_zero] at h
    obtain ⟨⟨e, e'⟩, he⟩ := h
    have he' : T e = f ∧ S e' = f' := by simpa using he
    refine Prod.ext ?_ ?_
    · exact (Submodule.Quotient.mk_eq_zero _).2 ⟨e, he'.1⟩
    · exact (Submodule.Quotient.mk_eq_zero _).2 ⟨e', he'.2⟩
  · intro z
    induction z using Submodule.Quotient.induction_on with | H p => ?_
    exact ⟨(Submodule.Quotient.mk p.1, Submodule.Quotient.mk p.2), hmk _ _⟩

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace E'] [CompleteSpace F'] in
/-- `ker T × ker S ≅ ker(T ⊕ S)`. -/
def kerProdEquiv : (LinearMap.ker (T : E →ₗ[ℝ] F) × LinearMap.ker (S : E' →ₗ[ℝ] F')) ≃ₗ[ℝ]
    LinearMap.ker ((T.prodMap S : E × E' →L[ℝ] F × F') : E × E' →ₗ[ℝ] F × F') :=
  LinearEquiv.ofBijective _ (bijective_coprod_kerInl_kerInr T S)

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace E'] [CompleteSpace F'] in
/-- `coker T × coker S ≅ coker(T ⊕ S)`. -/
def cokerProdEquiv :
    ((F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) × (F' ⧸ LinearMap.range (S : E' →ₗ[ℝ] F'))) ≃ₗ[ℝ]
      (F × F') ⧸ LinearMap.range
        ((T.prodMap S : E × E' →L[ℝ] F × F') : E × E' →ₗ[ℝ] F × F') :=
  LinearEquiv.ofBijective _ (bijective_coprod_cokerInl_cokerInr T S)

set_option linter.unusedSectionVars false in
/-- `dim ker(T ⊕ S) = dim ker T + dim ker S`. -/
theorem finrank_ker_prodMap (hT : T.IsFredholm) (hS : S.IsFredholm) :
    finrank ℝ (LinearMap.ker (T : E →ₗ[ℝ] F)) + finrank ℝ (LinearMap.ker (S : E' →ₗ[ℝ] F')) =
      finrank ℝ (LinearMap.ker ((T.prodMap S : E × E' →L[ℝ] F × F') : E × E' →ₗ[ℝ] F × F')) := by
  have := hT.finite_ker
  have := hS.finite_ker
  rw [← Module.finrank_prod, (kerProdEquiv T S).finrank_eq]

set_option linter.unusedSectionVars false in
/-- `dim coker(T ⊕ S) = dim coker T + dim coker S`. -/
theorem finrank_coker_prodMap (hT : T.IsFredholm) (hS : S.IsFredholm) :
    finrank ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) +
        finrank ℝ (F' ⧸ LinearMap.range (S : E' →ₗ[ℝ] F')) =
      finrank ℝ ((F × F') ⧸ LinearMap.range
        ((T.prodMap S : E × E' →L[ℝ] F × F') : E × E' →ₗ[ℝ] F × F')) := by
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := hT.finite_coker
  have : FiniteDimensional ℝ (F' ⧸ LinearMap.range (S : E' →ₗ[ℝ] F')) := hS.finite_coker
  rw [← Module.finrank_prod, (cokerProdEquiv T S).finrank_eq]

set_option linter.unusedSectionVars false in
/-- `T ⊕ S` is Fredholm. -/
theorem isFredholm_prodMap (hT : T.IsFredholm) (hS : S.IsFredholm) :
    (T.prodMap S).IsFredholm := by
  have := hT.finite_ker
  have := hS.finite_ker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := hT.finite_coker
  have : FiniteDimensional ℝ (F' ⧸ LinearMap.range (S : E' →ₗ[ℝ] F')) := hS.finite_coker
  have hker : FiniteDimensional ℝ
      (LinearMap.ker ((T.prodMap S : E × E' →L[ℝ] F × F') : E × E' →ₗ[ℝ] F × F')) :=
    (kerProdEquiv T S).finiteDimensional
  have hcoker : FiniteDimensional ℝ ((F × F') ⧸ LinearMap.range
      ((T.prodMap S : E × E' →L[ℝ] F × F') : E × E' →ₗ[ℝ] F × F')) :=
    (cokerProdEquiv T S).finiteDimensional
  have hrange : ((T.prodMap S).range : Set (F × F')) =
      (T.range : Set F) ×ˢ (S.range : Set F') := by
    ext ⟨f, f'⟩
    simp only [SetLike.mem_coe, Set.mem_prod]
    exact ⟨fun ⟨⟨e, e'⟩, h⟩ => ⟨⟨e, congrArg Prod.fst h⟩, ⟨e', congrArg Prod.snd h⟩⟩,
      fun ⟨⟨e, he⟩, ⟨e', he'⟩⟩ => ⟨(e, e'), Prod.ext he he'⟩⟩
  exact
    { isStrictMap := (LinearMap.isStrictMap_prodMap_iff (fₗ := (T : E →ₗ[ℝ] F))
        (gₗ := (S : E' →ₗ[ℝ] F'))).2 ⟨hT.isStrictMap, hS.isStrictMap⟩
      isClosed_range := hrange ▸ hT.isClosed_range.prod hS.isClosed_range
      finite_ker := hker
      finite_coker := hcoker
      closedComplemented_ker := Submodule.ClosedComplemented.of_finiteDimensional _ }

variable {T S}

/-- The vector `(a ∧ a') ⊗ (d ∧ d')*` of `det(T ⊕ S)` for bases `a`, `d`, `a'`, `d'` of
`ker T`, `coker T`, `ker S`, `coker S`. -/
def directSumVec (hT : T.IsFredholm) (hS : S.IsFredholm)
    (a : Basis (Fin (finrank ℝ (LinearMap.ker (T : E →ₗ[ℝ] F)))) ℝ (LinearMap.ker (T : E →ₗ[ℝ] F)))
    (d : Basis (Fin (finrank ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)))) ℝ
      (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)))
    (a' : Basis (Fin (finrank ℝ (LinearMap.ker (S : E' →ₗ[ℝ] F')))) ℝ
      (LinearMap.ker (S : E' →ₗ[ℝ] F')))
    (d' : Basis (Fin (finrank ℝ (F' ⧸ LinearMap.range (S : E' →ₗ[ℝ] F')))) ℝ
      (F' ⧸ LinearMap.range (S : E' →ₗ[ℝ] F'))) :
    fredholmDet (T.prodMap S) :=
  wedge (Fin.append (kerInl T S ∘ a) (kerInr T S ∘ a')) (finrank_ker_prodMap T S hT hS) ⊗ₜ
    dualVec (wedge (Fin.append (cokerInl T S ∘ d) (cokerInr T S ∘ d'))
      (finrank_coker_prodMap T S hT hS))

/-- **Definition 6.16**: the isomorphism `det(T) ⊗ det(S) → det(T ⊕ S)`, defined by the formula of
the text for the standard bases (`Module.finBasis`): `h ⊗ h' ↦ h₀*(h) h₀'*(h') g₀`, where
`h₀ = a ⊗ d*`, `h₀' = a' ⊗ d'*` and `g₀ = (a ∧ a') ⊗ (d ∧ d')*` for those bases. -/
def directSumDet (hT : T.IsFredholm) (hS : S.IsFredholm) :
    fredholmDet T ⊗[ℝ] fredholmDet S →ₗ[ℝ] fredholmDet (T.prodMap S) :=
  haveI := hT.finite_ker
  haveI : FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := hT.finite_coker
  haveI := hS.finite_ker
  haveI : FiniteDimensional ℝ (F' ⧸ LinearMap.range (S : E' →ₗ[ℝ] F')) := hS.finite_coker
  TensorProduct.lift <|
    ((LinearMap.mul ℝ ℝ).compl₁₂
        (dualVec (wedge (Module.finBasis ℝ _) rfl ⊗ₜ dualVec (wedge (Module.finBasis ℝ _) rfl) :
          fredholmDet T))
        (dualVec (wedge (Module.finBasis ℝ _) rfl ⊗ₜ dualVec (wedge (Module.finBasis ℝ _) rfl) :
          fredholmDet S))).compr₂
      (LinearMap.toSpanSingleton ℝ _
        (directSumVec hT hS (Module.finBasis ℝ _) (Module.finBasis ℝ _) (Module.finBasis ℝ _)
          (Module.finBasis ℝ _)))

/-- **Change of bases in `(a ∧ a') ⊗ (d ∧ d')*`**: for other bases `a₀`, `d₀`, `a₀'`, `d₀'`, the
vector `(a ∧ a') ⊗ (d ∧ d')*` is `det_{a₀} a · det_{a₀'} a' / (det_{d₀} d · det_{d₀'} d')` times
`(a₀ ∧ a₀') ⊗ (d₀ ∧ d₀')*`. -/
theorem directSumVec_eq_smul (hT : T.IsFredholm) (hS : S.IsFredholm)
    (a a₀ : Basis (Fin (finrank ℝ (LinearMap.ker (T : E →ₗ[ℝ] F)))) ℝ
      (LinearMap.ker (T : E →ₗ[ℝ] F)))
    (d d₀ : Basis (Fin (finrank ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)))) ℝ
      (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)))
    (a' a₀' : Basis (Fin (finrank ℝ (LinearMap.ker (S : E' →ₗ[ℝ] F')))) ℝ
      (LinearMap.ker (S : E' →ₗ[ℝ] F')))
    (d' d₀' : Basis (Fin (finrank ℝ (F' ⧸ LinearMap.range (S : E' →ₗ[ℝ] F')))) ℝ
      (F' ⧸ LinearMap.range (S : E' →ₗ[ℝ] F'))) :
    directSumVec hT hS a d a' d' =
      ((a₀.det a * a₀'.det a') * (d₀.det d * d₀'.det d')⁻¹) • directSumVec hT hS a₀ d₀ a₀' d₀' := by
  rw [directSumVec, directSumVec, wedge_append_basis_left (kerInl T S) a₀ a,
    wedge_append_basis_right (kerInr T S) _ a₀' a', wedge_append_basis_left (cokerInl T S) d₀ d,
    wedge_append_basis_right (cokerInr T S) _ d₀' d', smul_smul, smul_smul,
    dualVec_smul_of_ne_zero _ (mul_ne_zero (d₀.isUnit_det d).ne_zero (d₀'.isUnit_det d').ne_zero),
    TensorProduct.smul_tmul_smul]

/-- `(a ∧ a') ⊗ (d ∧ d')* ≠ 0`. -/
theorem directSumVec_ne_zero (hT : T.IsFredholm) (hS : S.IsFredholm)
    (a : Basis (Fin (finrank ℝ (LinearMap.ker (T : E →ₗ[ℝ] F)))) ℝ (LinearMap.ker (T : E →ₗ[ℝ] F)))
    (d : Basis (Fin (finrank ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)))) ℝ
      (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)))
    (a' : Basis (Fin (finrank ℝ (LinearMap.ker (S : E' →ₗ[ℝ] F')))) ℝ
      (LinearMap.ker (S : E' →ₗ[ℝ] F')))
    (d' : Basis (Fin (finrank ℝ (F' ⧸ LinearMap.range (S : E' →ₗ[ℝ] F')))) ℝ
      (F' ⧸ LinearMap.range (S : E' →ₗ[ℝ] F'))) :
    directSumVec hT hS a d a' d' ≠ 0 := by
  have := hT.finite_ker
  have := hS.finite_ker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := hT.finite_coker
  have : FiniteDimensional ℝ (F' ⧸ LinearMap.range (S : E' →ₗ[ℝ] F')) := hS.finite_coker
  have : FiniteDimensional ℝ
      (LinearMap.ker ((T.prodMap S : E × E' →L[ℝ] F × F') : E × E' →ₗ[ℝ] F × F')) :=
    (kerProdEquiv T S).finiteDimensional
  have : FiniteDimensional ℝ ((F × F') ⧸ LinearMap.range
      ((T.prodMap S : E × E' →L[ℝ] F × F') : E × E' →ₗ[ℝ] F × F')) :=
    (cokerProdEquiv T S).finiteDimensional
  exact tmul_ne_zero_of_ne_zero
    (wedge_ne_zero_of_span_eq_top _
      (top_le_span_append_of_surjective _ _ (bijective_coprod_kerInl_kerInr T S).2 a a'))
    (dualVec_ne_zero finrank_maxPow (wedge_ne_zero_of_span_eq_top _
      (top_le_span_append_of_surjective _ _ (bijective_coprod_cokerInl_cokerInr T S).2 d d')))

/-- **Definition 6.16, the formula for all bases**: `h ⊗ h' ↦ (a ∧ a') ⊗ (d ∧ d')*` for
`h = a ⊗ d*` and `h' = a' ⊗ d'*`. -/
theorem definition_6_16 (hT : T.IsFredholm) (hS : S.IsFredholm)
    (a : Basis (Fin (finrank ℝ (LinearMap.ker (T : E →ₗ[ℝ] F)))) ℝ (LinearMap.ker (T : E →ₗ[ℝ] F)))
    (d : Basis (Fin (finrank ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)))) ℝ
      (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)))
    (a' : Basis (Fin (finrank ℝ (LinearMap.ker (S : E' →ₗ[ℝ] F')))) ℝ
      (LinearMap.ker (S : E' →ₗ[ℝ] F')))
    (d' : Basis (Fin (finrank ℝ (F' ⧸ LinearMap.range (S : E' →ₗ[ℝ] F')))) ℝ
      (F' ⧸ LinearMap.range (S : E' →ₗ[ℝ] F'))) :
    directSumDet hT hS ((wedge a rfl ⊗ₜ dualVec (wedge d rfl)) ⊗ₜ
        (wedge a' rfl ⊗ₜ dualVec (wedge d' rfl))) =
      directSumVec hT hS a d a' d' := by
  have := hT.finite_ker
  have := hS.finite_ker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := hT.finite_coker
  have : FiniteDimensional ℝ (F' ⧸ LinearMap.range (S : E' →ₗ[ℝ] F')) := hS.finite_coker
  let fa := Module.finBasis ℝ (LinearMap.ker (T : E →ₗ[ℝ] F))
  let fd := Module.finBasis ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F))
  let fa' := Module.finBasis ℝ (LinearMap.ker (S : E' →ₗ[ℝ] F'))
  let fd' := Module.finBasis ℝ (F' ⧸ LinearMap.range (S : E' →ₗ[ℝ] F'))
  have h0 : wedge fa rfl ⊗ₜ[ℝ] dualVec (wedge fd rfl) ≠ 0 :=
    tmul_ne_zero_of_ne_zero (wedge_basis_ne_zero fa)
      (dualVec_ne_zero finrank_maxPow (wedge_basis_ne_zero fd))
  have h0' : wedge fa' rfl ⊗ₜ[ℝ] dualVec (wedge fd' rfl) ≠ 0 :=
    tmul_ne_zero_of_ne_zero (wedge_basis_ne_zero fa')
      (dualVec_ne_zero finrank_maxPow (wedge_basis_ne_zero fd'))
  have hdet0 : directSumDet hT hS ((wedge fa rfl ⊗ₜ[ℝ] dualVec (wedge fd rfl)) ⊗ₜ[ℝ]
      (wedge fa' rfl ⊗ₜ[ℝ] dualVec (wedge fd' rfl))) = directSumVec hT hS fa fd fa' fd' := by
    simp only [directSumDet, TensorProduct.lift.tmul, LinearMap.compr₂_apply,
      LinearMap.compl₁₂_apply, LinearMap.mul_apply', LinearMap.toSpanSingleton_apply]
    rw [dualVec_self (finrank_fredholmDet hT) h0, dualVec_self (finrank_fredholmDet hS) h0',
      one_mul, one_smul]
  rw [wedge_tmul_dualVec_eq_smul a fa d fd, wedge_tmul_dualVec_eq_smul a' fa' d' fd',
    TensorProduct.smul_tmul_smul, map_smul, hdet0,
    directSumVec_eq_smul hT hS a fa d fd a' fa' d' fd', mul_inv]
  congr 1
  ring

/-- The map of Definition 6.16 is an isomorphism. -/
theorem directSumDet_bijective (hT : T.IsFredholm) (hS : S.IsFredholm) :
    Function.Bijective (directSumDet hT hS) := by
  have := hT.finite_ker
  have := hS.finite_ker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := hT.finite_coker
  have : FiniteDimensional ℝ (F' ⧸ LinearMap.range (S : E' →ₗ[ℝ] F')) := hS.finite_coker
  let fa := Module.finBasis ℝ (LinearMap.ker (T : E →ₗ[ℝ] F))
  let fd := Module.finBasis ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F))
  let fa' := Module.finBasis ℝ (LinearMap.ker (S : E' →ₗ[ℝ] F'))
  let fd' := Module.finBasis ℝ (F' ⧸ LinearMap.range (S : E' →ₗ[ℝ] F'))
  have h0 : wedge fa rfl ⊗ₜ[ℝ] dualVec (wedge fd rfl) ≠ 0 :=
    tmul_ne_zero_of_ne_zero (wedge_basis_ne_zero fa)
      (dualVec_ne_zero finrank_maxPow (wedge_basis_ne_zero fd))
  have h0' : wedge fa' rfl ⊗ₜ[ℝ] dualVec (wedge fd' rfl) ≠ 0 :=
    tmul_ne_zero_of_ne_zero (wedge_basis_ne_zero fa')
      (dualVec_ne_zero finrank_maxPow (wedge_basis_ne_zero fd'))
  have h1 : finrank ℝ (fredholmDet T ⊗[ℝ] fredholmDet S) = 1 := by
    rw [Module.finrank_tensorProduct, finrank_fredholmDet hT, finrank_fredholmDet hS]
  refine bijective_of_finrank_eq_one h1 (finrank_fredholmDet (isFredholm_prodMap T S hT hS)) _
    (tmul_ne_zero_of_ne_zero h0 h0') ?_
  rw [definition_6_16 hT hS fa fd fa' fd']
  exact directSumVec_ne_zero hT hS fa fd fa' fd'

end DirectSum

end Polyfold
