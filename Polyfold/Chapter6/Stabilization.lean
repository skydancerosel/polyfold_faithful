import Polyfold.Chapter6.FredholmDet
import Polyfold.Chapter1.FredholmPerturbation

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.3,
pp. 211–213: the stabilization `T_φ`, **Lemma 6.14** (its exact sequence), formula (94) and
**Proposition 6.15** (the isomorphism `ι_φ : det(T) → det(T_φ)`) *(book 2017: Lemma 6.6,
Proposition 6.7; see `BookConcordance.md`)*.  Definition 6.16 is in `DirectSumDet.lean`.

# Stabilization

## The text, paraphrased

Let `T : E → F` be Fredholm and `φ : ℝⁿ → F` linear with `T_φ : E ⊕ ℝⁿ → F`,
`T_φ(e, r) = T e + φ r`, surjective.  (Lemma 6.14) The sequence
`0 → ker T →j ker T_φ →π ℝⁿ →[φ] F / R(T) → 0`, `j(e) = (e, 0)`, `π(e, r) = r`,
`[φ](r) = φ(r) + R(T)`, is exact; it gives `Φ_E : det(T) → λ(ker T_φ) ⊗ λ*(ℝⁿ)`.  With
`ψ : λ*(ℝⁿ) → λ*({0}) = ℝ*`, `(e₁ ∧ … ∧ eₙ)* ↦ 1*`, one has (94)
`ψ((c₁ ∧ … ∧ cₙ)*) = det[c₁, …, cₙ]⁻¹ 1*`, and `ι_φ = (1 ⊗ ψ) ∘ Φ_E : det(T) → det(T_φ)`.
(Proposition 6.15) For a basis `a` of `ker T`, `c̄₁, …, c̄_m ∈ ℝⁿ` with `φ(c̄ᵢ) + R(T)` a basis of
`F / R(T)`, and `b̄ᵢ = (bᵢ, rᵢ)` completing `(a, 0)` to a basis of `ker T_φ`,
`ι_φ(h) = det(c̄₁, …, c̄_m, r₁, …, r_l)⁻¹ ((a₁, 0) ∧ … ∧ (a_k, 0) ∧ b̄₁ ∧ … ∧ b̄_l) ⊗ 1*`.

## What is formalized

* `Polyfold.stabSeq hφ`: the sequence of Lemma 6.14 as a `FourTermExact`, with
  **Lemma 6.14** (`lemma_6_14`) its exactness; `exists_surjective_coprod`: for `T` Fredholm a
  stabilizing `φ` exists.
* `Polyfold.stabPsi` (`ψ`) and `stabPsi_dualVec` (**(94)**).
* `Polyfold.stabIota` (`ι_φ`), an isomorphism `det(T) ≅ det(T_φ)`, and **Proposition 6.15**
  (`proposition_6_15`).

## Reading

`ℝⁿ` is `Fin n → ℝ` with the standard basis `Pi.basisFun`; `det[c₁, …, cₙ]` is the determinant
of the matrix with columns `cⱼ`, `(Pi.basisFun ℝ (Fin n)).det c`.  `λ*({0})`: as `T_φ` is onto,
`F / R(T_φ) = 0` and `λ*(F / R(T_φ))` is the dual of `⋀⁰`, with `1*` the dual of the empty wedge.
In Proposition 6.15 the identity `m + l = n` is a hypothesis of the statement (it is needed to form
`det(c̄, r)`); `stab_card_eq` shows it always holds.
-/

open Module TensorProduct

noncomputable section

namespace Polyfold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-! ### Helper lemmas on wedges and complements -/

section Helpers

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

/-- The wedge depends only on the family (not on the proof of `k = dim M`). -/
private theorem wedge_congr {k : ℕ} {v w : Fin k → M} (h : v = w) (hv : k = finrank ℝ M)
    (hw : k = finrank ℝ M) : wedge v hv = wedge w hw := by
  subst h
  rfl

/-- **Change of basis** for a basis indexed by `Fin k`, `k = dim M`:
`w₁ ∧ … ∧ w_k = det_b(w) · b₁ ∧ … ∧ b_k`. -/
private theorem wedge_eq_det_smul_of_eq [FiniteDimensional ℝ M] {k : ℕ} (hk : k = finrank ℝ M)
    (b : Basis (Fin k) ℝ M) (w : Fin k → M) : wedge w hk = b.det w • wedge b hk := by
  subst hk
  exact wedge_eq_det_smul b w

/-- A linearly independent `Fin.append u v` gives a linearly independent `Sum.elim u v`. -/
private theorem linearIndependent_sumElim_of_append {p q : ℕ} {u : Fin p → M} {v : Fin q → M}
    (h : LinearIndependent ℝ (Fin.append u v)) : LinearIndependent ℝ (Sum.elim u v) := by
  have hs : Fin.append u v ∘ finSumFinEquiv = Sum.elim u v := by
    funext x
    rcases x with i | j <;> simp
  rw [← hs]
  exact h.comp _ finSumFinEquiv.injective

/-- If `Fin.append u v` is a linearly independent family of `dim M` vectors, the spans of `u` and
of `v` are complements. -/
private theorem isCompl_span_of_linearIndependent_append [FiniteDimensional ℝ M] {p q : ℕ}
    {u : Fin p → M} {v : Fin q → M} (h : LinearIndependent ℝ (Fin.append u v))
    (hpq : p + q = finrank ℝ M) :
    IsCompl (Submodule.span ℝ (Set.range u)) (Submodule.span ℝ (Set.range v)) := by
  have h' := linearIndependent_sumElim_of_append h
  obtain ⟨-, -, hdisj⟩ := linearIndependent_sum.1 h'
  refine ⟨by simpa using hdisj, ?_⟩
  rw [codisjoint_iff, ← Submodule.span_union, ← Set.Sum.elim_range]
  have := (basisOfLinearIndependentOfCardEqFinrank' _ h' (by simp [hpq])).span_eq
  rwa [coe_basisOfLinearIndependentOfCardEqFinrank'] at this

end Helpers

/-! ### Lemma 6.14 -/

section Stab

variable {T : E →L[ℝ] F} {n : ℕ} {φ : (Fin n → ℝ) →L[ℝ] F}

/-- `j : ker T → ker T_φ`, `e ↦ (e, 0)`. -/
def stabJ (T : E →L[ℝ] F) (φ : (Fin n → ℝ) →L[ℝ] F) :
    LinearMap.ker (T : E →ₗ[ℝ] F) →ₗ[ℝ] LinearMap.ker ((T.coprod φ : E × (Fin n → ℝ) →L[ℝ] F) :
      E × (Fin n → ℝ) →ₗ[ℝ] F) :=
  LinearMap.codRestrict _ (LinearMap.inl ℝ E (Fin n → ℝ) ∘ₗ (LinearMap.ker (T : E →ₗ[ℝ] F)).subtype)
    (fun x => by simp)

/-- `π : ker T_φ → ℝⁿ`, `(e, r) ↦ r`. -/
def stabPi (T : E →L[ℝ] F) (φ : (Fin n → ℝ) →L[ℝ] F) :
    LinearMap.ker ((T.coprod φ : E × (Fin n → ℝ) →L[ℝ] F) : E × (Fin n → ℝ) →ₗ[ℝ] F) →ₗ[ℝ]
      (Fin n → ℝ) :=
  LinearMap.snd ℝ E (Fin n → ℝ) ∘ₗ (LinearMap.ker _).subtype

/-- `[φ] : ℝⁿ → F / R(T)`, `r ↦ φ(r) + R(T)`. -/
def stabClass (T : E →L[ℝ] F) (φ : (Fin n → ℝ) →L[ℝ] F) :
    (Fin n → ℝ) →ₗ[ℝ] F ⧸ LinearMap.range (T : E →ₗ[ℝ] F) :=
  (LinearMap.range (T : E →ₗ[ℝ] F)).mkQ ∘ₗ (φ : (Fin n → ℝ) →ₗ[ℝ] F)

omit [CompleteSpace E] [CompleteSpace F] in
/-- `j(e) = (e, 0)`. -/
@[simp] theorem coe_stabJ (x : LinearMap.ker (T : E →ₗ[ℝ] F)) :
    (stabJ T φ x : E × (Fin n → ℝ)) = ((x : E), 0) := rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- `π(e, r) = r`. -/
@[simp] theorem stabPi_apply
    (x : LinearMap.ker ((T.coprod φ : E × (Fin n → ℝ) →L[ℝ] F) : E × (Fin n → ℝ) →ₗ[ℝ] F)) :
    stabPi T φ x = (x : E × (Fin n → ℝ)).2 := rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- `[φ](r) = φ(r) + R(T)`. -/
@[simp] theorem stabClass_apply (r : Fin n → ℝ) :
    stabClass T φ r = Submodule.Quotient.mk (φ r) := rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- `(e, r) ∈ ker T_φ` if and only if `T e + φ r = 0`. -/
theorem mem_ker_coprod {x : E × (Fin n → ℝ)} :
    x ∈ LinearMap.ker ((T.coprod φ : E × (Fin n → ℝ) →L[ℝ] F) : E × (Fin n → ℝ) →ₗ[ℝ] F) ↔
      T x.1 + φ x.2 = 0 := by
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coprod_apply]

omit [CompleteSpace E] [CompleteSpace F] in
/-- `j` is injective. -/
theorem stabJ_injective : Function.Injective (stabJ T φ) := by
  intro x y h
  apply Subtype.ext
  have := congrArg (Prod.fst ∘ Subtype.val) h
  simpa using this

omit [CompleteSpace E] [CompleteSpace F] in
/-- `im j = ker π`. -/
theorem range_stabJ : LinearMap.range (stabJ T φ) = LinearMap.ker (stabPi T φ) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    simp
  · intro hx
    have h2 : (x : E × (Fin n → ℝ)).2 = 0 := by simpa using hx
    have h1 : T (x : E × (Fin n → ℝ)).1 = 0 := by
      have := mem_ker_coprod.1 x.2
      rwa [h2, map_zero, add_zero] at this
    refine ⟨⟨(x : E × (Fin n → ℝ)).1, h1⟩, Subtype.ext ?_⟩
    rw [coe_stabJ]
    exact Prod.ext rfl h2.symm

omit [CompleteSpace E] [CompleteSpace F] in
/-- `im π = ker [φ]`. -/
theorem range_stabPi : LinearMap.range (stabPi T φ) = LinearMap.ker (stabClass T φ) := by
  ext r
  rw [LinearMap.mem_ker, stabClass_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨-(x : E × (Fin n → ℝ)).1, ?_⟩
    have := mem_ker_coprod.1 x.2
    simp only [ContinuousLinearMap.coe_coe, map_neg, stabPi_apply]
    exact neg_eq_of_add_eq_zero_right this
  · rintro ⟨e, he⟩
    refine ⟨⟨(-e, r), mem_ker_coprod.2 ?_⟩, rfl⟩
    simp only [map_neg]
    rw [← he]
    simp

omit [CompleteSpace E] [CompleteSpace F] in
/-- `[φ]` is onto if `T_φ` is. -/
theorem stabClass_surjective (hφ : Function.Surjective (T.coprod φ)) :
    Function.Surjective (stabClass T φ) := by
  intro q
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨x, rfl⟩ := hφ f
  refine ⟨x.2, ?_⟩
  rw [stabClass_apply, ContinuousLinearMap.coprod_apply, Submodule.Quotient.eq]
  refine ⟨-x.1, ?_⟩
  simp

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Lemma 6.14**: if `T_φ` is onto, the sequence
`0 → ker T →j ker T_φ →π ℝⁿ →[φ] F / R(T) → 0` is exact. -/
theorem lemma_6_14 (hφ : Function.Surjective (T.coprod φ)) :
    Function.Injective (stabJ T φ) ∧
      LinearMap.range (stabJ T φ) = LinearMap.ker (stabPi T φ) ∧
      LinearMap.range (stabPi T φ) = LinearMap.ker (stabClass T φ) ∧
      Function.Surjective (stabClass T φ) :=
  ⟨stabJ_injective, range_stabJ, range_stabPi, stabClass_surjective hφ⟩

/-- The exact sequence of Lemma 6.14. -/
def stabSeq (hφ : Function.Surjective (T.coprod φ)) :
    FourTermExact (LinearMap.ker (T : E →ₗ[ℝ] F))
      (LinearMap.ker ((T.coprod φ : E × (Fin n → ℝ) →L[ℝ] F) : E × (Fin n → ℝ) →ₗ[ℝ] F))
      (Fin n → ℝ) (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) where
  α := stabJ T φ
  β := stabPi T φ
  γ := stabClass T φ
  injective_α := (lemma_6_14 hφ).1
  range_α := (lemma_6_14 hφ).2.1
  range_β := (lemma_6_14 hφ).2.2.1
  surjective_γ := (lemma_6_14 hφ).2.2.2

omit [CompleteSpace E] [CompleteSpace F] in
/-- Stabilizations exist: for `T` Fredholm there are `n` and `φ : ℝⁿ → F` with `T_φ` onto (take
`n = dim coker T` and `φ` onto a complement of `R(T)`). -/
theorem exists_surjective_coprod (hT : T.IsFredholm) :
    ∃ (n : ℕ) (φ : (Fin n → ℝ) →L[ℝ] F), Function.Surjective (T.coprod φ) := by
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (LinearMap.range (T : E →ₗ[ℝ] F))
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := hT.finite_coker
  have : FiniteDimensional ℝ q := (Submodule.quotientEquivOfIsCompl _ _ hq).finiteDimensional
  let b := Module.finBasis ℝ q
  refine ⟨finrank ℝ q,
    LinearMap.toContinuousLinearMap (q.subtype ∘ₗ b.equivFun.symm.toLinearMap), ?_⟩
  intro y
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 (hq.sup_eq_top ▸ Submodule.mem_top (x := y))
  obtain ⟨e, rfl⟩ := hu
  refine ⟨(e, b.equivFun ⟨v, hv⟩), ?_⟩
  simp

omit [CompleteSpace E] [CompleteSpace F] in
/-- `F / R(T_φ) = 0` for `T_φ` onto. -/
theorem subsingleton_coker_coprod (hφ : Function.Surjective (T.coprod φ)) :
    Subsingleton (F ⧸ LinearMap.range
      ((T.coprod φ : E × (Fin n → ℝ) →L[ℝ] F) : E × (Fin n → ℝ) →ₗ[ℝ] F)) :=
  Submodule.Quotient.subsingleton_iff.2 (LinearMap.range_eq_top.2 hφ)

omit [CompleteSpace E] [CompleteSpace F] in
/-- `F / R(T_φ)` is finite-dimensional for `T_φ` onto. -/
theorem finiteDimensional_coker_coprod (hφ : Function.Surjective (T.coprod φ)) :
    FiniteDimensional ℝ (F ⧸ LinearMap.range
      ((T.coprod φ : E × (Fin n → ℝ) →L[ℝ] F) : E × (Fin n → ℝ) →ₗ[ℝ] F)) :=
  have := subsingleton_coker_coprod hφ
  inferInstance

omit [CompleteSpace E] [CompleteSpace F] in
/-- `F / R(T_φ) = 0` for `T_φ` onto. -/
theorem finrank_coker_coprod (hφ : Function.Surjective (T.coprod φ)) :
    finrank ℝ (F ⧸ LinearMap.range
      ((T.coprod φ : E × (Fin n → ℝ) →L[ℝ] F) : E × (Fin n → ℝ) →ₗ[ℝ] F)) = 0 :=
  have := subsingleton_coker_coprod hφ
  finrank_zero_of_subsingleton

/-! ### Formula (94) and Proposition 6.15 -/

/-- The wedge `e₁ ∧ … ∧ eₙ` of the standard basis of `ℝⁿ`. -/
def stdWedge (n : ℕ) : maxPow (Fin n → ℝ) :=
  wedge (Pi.basisFun ℝ (Fin n)) (by simp)

/-- `1* ∈ λ*(F / R(T_φ))`: the dual of the empty wedge. -/
def stabOne (hφ : Function.Surjective (T.coprod φ)) :
    maxPowDual (F ⧸ LinearMap.range
      ((T.coprod φ : E × (Fin n → ℝ) →L[ℝ] F) : E × (Fin n → ℝ) →ₗ[ℝ] F)) :=
  dualVec (wedge (Fin.elim0 : Fin 0 → _) (finrank_coker_coprod hφ).symm)

/-- **`ψ : λ*(ℝⁿ) → λ*({0})`**, `(e₁ ∧ … ∧ eₙ)* ↦ 1*`. -/
def stabPsi (hφ : Function.Surjective (T.coprod φ)) :
    maxPowDual (Fin n → ℝ) →ₗ[ℝ] maxPowDual (F ⧸ LinearMap.range
      ((T.coprod φ : E × (Fin n → ℝ) →L[ℝ] F) : E × (Fin n → ℝ) →ₗ[ℝ] F)) :=
  LinearMap.smulRight (dualVec (dualVec (stdWedge n))) (stabOne hφ)

/-- The wedge of the standard basis is not zero. -/
theorem stdWedge_ne_zero (n : ℕ) : stdWedge n ≠ 0 :=
  wedge_basis_ne_zero' _ _

omit [CompleteSpace E] [CompleteSpace F] in
/-- `1* ≠ 0`. -/
theorem stabOne_ne_zero (hφ : Function.Surjective (T.coprod φ)) : stabOne hφ ≠ 0 := by
  have := finiteDimensional_coker_coprod hφ
  exact dualVec_ne_zero finrank_maxPow ((wedge_ne_zero_iff _).2 linearIndependent_empty_type)

omit [CompleteSpace E] [CompleteSpace F] in
/-- `ψ((e₁ ∧ … ∧ eₙ)*) = 1*`. -/
theorem stabPsi_dualVec_stdWedge (hφ : Function.Surjective (T.coprod φ)) :
    stabPsi hφ (dualVec (stdWedge n)) = stabOne hφ := by
  rw [stabPsi, LinearMap.smulRight_apply,
    dualVec_self finrank_maxPowDual (dualVec_ne_zero finrank_maxPow (stdWedge_ne_zero n)),
    one_smul]

omit [CompleteSpace E] [CompleteSpace F] in
/-- **(94)**: `ψ((c₁ ∧ … ∧ cₙ)*) = det[c₁, …, cₙ]⁻¹ 1*` for a basis `c` of `ℝⁿ`. -/
theorem stabPsi_dualVec (hφ : Function.Surjective (T.coprod φ)) {c : Fin n → Fin n → ℝ}
    (hc : LinearIndependent ℝ c) :
    stabPsi hφ (dualVec (wedge c (by simp))) = ((Pi.basisFun ℝ (Fin n)).det c)⁻¹ • stabOne hφ := by
  have hN : n = finrank ℝ (Fin n → ℝ) := by simp
  have hw : wedge c hN = (Pi.basisFun ℝ (Fin n)).det c • stdWedge n :=
    wedge_eq_det_smul_of_eq hN _ c
  have hdet : (Pi.basisFun ℝ (Fin n)).det c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hw
    exact (wedge_ne_zero_iff hN).2 hc hw
  rw [hw, dualVec_smul finrank_maxPow (stdWedge_ne_zero n) hdet, map_smul,
    stabPsi_dualVec_stdWedge]

omit [CompleteSpace E] [CompleteSpace F] in
/-- `ψ` is an isomorphism (a nonzero map of lines). -/
theorem stabPsi_bijective (hφ : Function.Surjective (T.coprod φ)) :
    Function.Bijective (stabPsi hφ) := by
  have := finiteDimensional_coker_coprod hφ
  have hinj : Function.Injective (stabPsi hφ) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨t, rfl⟩ := exists_smul_eq_of_finrank_eq_one finrank_maxPowDual
      (dualVec_ne_zero finrank_maxPow (stdWedge_ne_zero n)) x
    rw [map_smul, stabPsi_dualVec_stdWedge, smul_eq_zero] at hx
    rcases hx with rfl | h
    · exact zero_smul _ _
    · exact absurd h (stabOne_ne_zero hφ)
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [finrank_maxPowDual, finrank_maxPowDual])).1 hinj⟩

omit [CompleteSpace E] [CompleteSpace F] in
/-- `ker T_φ` is finite-dimensional when `ker T` is: `π` has kernel `j(ker T)` and values in
`ℝⁿ`. -/
theorem finiteDimensional_ker_coprod [FiniteDimensional ℝ (LinearMap.ker (T : E →ₗ[ℝ] F))] :
    FiniteDimensional ℝ (LinearMap.ker ((T.coprod φ : E × (Fin n → ℝ) →L[ℝ] F) :
      E × (Fin n → ℝ) →ₗ[ℝ] F)) := by
  refine Module.finite_def.2 (Submodule.fg_of_fg_map_of_fg_inf_ker (stabPi T φ) ?_ ?_)
  · rw [Submodule.map_top]
    exact (Submodule.fg_iff_finiteDimensional _).2 inferInstance
  · rw [top_inf_eq, ← range_stabJ]
    exact (Submodule.fg_iff_finiteDimensional _).2 inferInstance

/-- **`ι_φ : det(T) → det(T_φ)`**: `Φ_E` of the sequence of Lemma 6.14 followed by `1 ⊗ ψ`. -/
def stabIota (hT : T.IsFredholm) (hφ : Function.Surjective (T.coprod φ)) :
    fredholmDet T →ₗ[ℝ] fredholmDet (T.coprod φ) :=
  haveI := hT.finite_ker
  haveI : FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := hT.finite_coker
  haveI : FiniteDimensional ℝ (LinearMap.ker ((T.coprod φ : E × (Fin n → ℝ) →L[ℝ] F) :
      E × (Fin n → ℝ) →ₗ[ℝ] F)) := finiteDimensional_ker_coprod
  LinearMap.lTensor _ (stabPsi hφ) ∘ₗ (stabSeq hφ).phi

omit [CompleteSpace E] [CompleteSpace F] in
/-- `ι_φ = (1 ⊗ ψ) ∘ Φ_E`. -/
theorem stabIota_apply [FiniteDimensional ℝ (LinearMap.ker (T : E →ₗ[ℝ] F))]
    [FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F))]
    [FiniteDimensional ℝ (LinearMap.ker ((T.coprod φ : E × (Fin n → ℝ) →L[ℝ] F) :
      E × (Fin n → ℝ) →ₗ[ℝ] F))]
    (hT : T.IsFredholm) (hφ : Function.Surjective (T.coprod φ)) (x : fredholmDet T) :
    stabIota hT hφ x = LinearMap.lTensor _ (stabPsi hφ) ((stabSeq hφ).phi x) := rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- `ι_φ` is an isomorphism. -/
theorem stabIota_bijective (hT : T.IsFredholm) (hφ : Function.Surjective (T.coprod φ)) :
    Function.Bijective (stabIota hT hφ) := by
  have := hT.finite_ker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := hT.finite_coker
  have := finiteDimensional_ker_coprod (T := T) (φ := φ)
  exact (LinearEquiv.lTensor _ (LinearEquiv.ofBijective _ (stabPsi_bijective hφ))).bijective.comp
    (stabSeq hφ).phi_bijective

omit [CompleteSpace E] [CompleteSpace F] in
/-- The dimension count behind Proposition 6.15: `m + l = n`, where `m = dim coker T`,
`k = dim ker T` and `k + l = dim ker T_φ`. -/
theorem stab_card_eq (hT : T.IsFredholm) (hφ : Function.Surjective (T.coprod φ)) {m l : ℕ}
    (hm : m = finrank ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)))
    (hl : finrank ℝ (LinearMap.ker (T : E →ₗ[ℝ] F)) + l =
      finrank ℝ (LinearMap.ker ((T.coprod φ : E × (Fin n → ℝ) →L[ℝ] F) :
        E × (Fin n → ℝ) →ₗ[ℝ] F))) :
    m + l = n := by
  have := hT.finite_ker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := hT.finite_coker
  have := finiteDimensional_ker_coprod (T := T) (φ := φ)
  have h1 := LinearMap.finrank_range_add_finrank_ker (stabPi T φ)
  have h2 := LinearMap.finrank_range_add_finrank_ker (stabClass T φ)
  rw [← range_stabJ, LinearMap.finrank_range_of_inj stabJ_injective] at h1
  rw [LinearMap.range_eq_top.2 (stabClass_surjective hφ), finrank_top, ← range_stabPi,
    Module.finrank_fin_fun] at h2
  omega

omit [CompleteSpace E] [CompleteSpace F] in
/-- `R(π) = ker [φ]` and the span of `c̄₁, …, c̄_m` are complements in `ℝⁿ` when the classes
`[φ](c̄ᵢ)` form a basis of `F / R(T)`. -/
theorem isCompl_range_stabPi_span [FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F))]
    {m : ℕ} {cbar : Fin m → Fin n → ℝ} (hd : LinearIndependent ℝ (stabClass T φ ∘ cbar))
    (hm : m = finrank ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F))) :
    IsCompl (LinearMap.range (stabPi T φ)) (Submodule.span ℝ (Set.range cbar)) := by
  rw [range_stabPi]
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨t, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hx'
    rw [LinearMap.mem_ker, map_sum] at hx
    simp only [map_smul] at hx
    have ht := Fintype.linearIndependent_iff.1 hd t hx
    simp [ht]
  · rw [codisjoint_iff, eq_top_iff]
    intro y _
    obtain ⟨d, hd'⟩ : ∃ d : Basis (Fin m) ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)),
        ⇑d = stabClass T φ ∘ cbar :=
      ⟨_, coe_basisOfLinearIndependentOfCardEqFinrank' _ hd (by simp [hm])⟩
    have hsum := d.sum_repr (stabClass T φ y)
    refine Submodule.mem_sup.2 ⟨y - ∑ i, d.repr (stabClass T φ y) i • cbar i, ?_,
      ∑ i, d.repr (stabClass T φ y) i • cbar i,
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩),
      sub_add_cancel _ _⟩
    rw [LinearMap.mem_ker, map_sub, map_sum]
    have hdi : ∀ i, stabClass T φ (cbar i) = d i := fun i => (congrFun hd' i).symm
    simp only [map_smul, hdi]
    rw [hsum, sub_self]

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Proposition 6.15**: for a basis `a₁, …, a_k` of `ker T`, vectors `c̄₁, …, c̄_m ∈ ℝⁿ` whose
classes `d̄ᵢ = φ(c̄ᵢ) + R(T)` form a basis of `F / R(T)`, and `b̄₁ = (b₁, r₁), …, b̄_l = (b_l, r_l)`
completing `(a₁, 0), …, (a_k, 0)` to a basis of `ker T_φ`,
`ι_φ((a₁ ∧ … ∧ a_k) ⊗ (d̄₁ ∧ … ∧ d̄_m)*) =
  det(c̄₁, …, c̄_m, r₁, …, r_l)⁻¹ ((a₁, 0) ∧ … ∧ (a_k, 0) ∧ b̄₁ ∧ … ∧ b̄_l) ⊗ 1*`. -/
theorem proposition_6_15 (hT : T.IsFredholm) (hφ : Function.Surjective (T.coprod φ))
    {k m l : ℕ} (a : Basis (Fin k) ℝ (LinearMap.ker (T : E →ₗ[ℝ] F))) (cbar : Fin m → Fin n → ℝ)
    (hd : LinearIndependent ℝ (stabClass T φ ∘ cbar))
    (hm : m = finrank ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)))
    (bbar : Fin l → LinearMap.ker ((T.coprod φ : E × (Fin n → ℝ) →L[ℝ] F) :
      E × (Fin n → ℝ) →ₗ[ℝ] F))
    (hb : LinearIndependent ℝ (Fin.append (stabJ T φ ∘ a) bbar))
    (hkl : k + l = finrank ℝ (LinearMap.ker ((T.coprod φ : E × (Fin n → ℝ) →L[ℝ] F) :
      E × (Fin n → ℝ) →ₗ[ℝ] F)))
    (hn : m + l = n) :
    stabIota hT hφ (wedge a (by rw [Module.finrank_eq_card_basis a, Fintype.card_fin]) ⊗ₜ
        dualVec (wedge (stabClass T φ ∘ cbar) hm)) =
      ((Pi.basisFun ℝ (Fin n)).det
          (Fin.append cbar (fun i => ((bbar i : E × (Fin n → ℝ)).2)) ∘ Fin.cast hn.symm))⁻¹ •
        (wedge (Fin.append (stabJ T φ ∘ a) bbar) hkl ⊗ₜ stabOne hφ) := by
  have := hT.finite_ker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := hT.finite_coker
  have := finiteDimensional_ker_coprod (T := T) (φ := φ)
  -- the complements `Z = span(b̄)` of `j(ker T)` and `V = span(c̄)` of `π(ker T_φ)`
  have hbb : LinearIndependent ℝ bbar := by
    have := (linearIndependent_sum.1 (linearIndependent_sumElim_of_append hb)).2.1
    simpa using this
  have hZ : IsCompl (LinearMap.range (stabJ T φ)) (Submodule.span ℝ (Set.range bbar)) := by
    have h := isCompl_span_of_linearIndependent_append hb hkl
    rwa [Set.range_comp, Submodule.span_image, a.span_eq, Submodule.map_top] at h
  have hV := isCompl_range_stabPi_span hd hm
  obtain ⟨d, hd'⟩ : ∃ d : Basis (Fin m) ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)),
      ⇑d = stabClass T φ ∘ cbar :=
    ⟨_, coe_basisOfLinearIndependentOfCardEqFinrank' _ hd (by simp [hm])⟩
  let χ : (stabSeq hφ).Choice :=
    { n := k, l := m, j := l, Z := Submodule.span ℝ (Set.range bbar), isCompl_Z := hZ,
      V := Submodule.span ℝ (Set.range cbar), isCompl_V := hV, a := a, d := d,
      b' := Basis.span hbb, c := cbar, c_mem := fun i => Submodule.subset_span ⟨i, rfl⟩,
      γ_c := fun i => (congrFun hd' i).symm }
  have h65 := (stabSeq hφ).lemma_6_5 χ
  have hsrc : χ.source = wedge a (by rw [Module.finrank_eq_card_basis a, Fintype.card_fin]) ⊗ₜ
      dualVec (wedge (stabClass T φ ∘ cbar) hm) :=
    congrArg (wedge a _ ⊗ₜ[ℝ] ·) (congrArg dualVec
      (wedge_congr hd' _ _))
  have hb' : (χ.Z.subtype ∘ χ.b' : Fin l → _) = bbar :=
    funext fun i => congrArg Subtype.val (Basis.span_apply hbb i)
  have hwB : χ.wedgeB = wedge (Fin.append (stabJ T φ ∘ a) bbar) hkl :=
    wedge_congr (congrArg (Fin.append (stabJ T φ ∘ a)) hb') _ _
  set r : Fin l → Fin n → ℝ := fun i => ((bbar i : E × (Fin n → ℝ)).2)
  have hwC : χ.wedgeC = wedge (Fin.append cbar r) χ.hC :=
    wedge_congr (congrArg (Fin.append cbar) (by rw [hb']; rfl)) _ _
  have hcast : wedge (Fin.append cbar r ∘ Fin.cast hn.symm) (by simp) =
      wedge (Fin.append cbar r) χ.hC := wedge_cast _ χ.hC hn.symm
  have hc : LinearIndependent ℝ (Fin.append cbar r ∘ Fin.cast hn.symm) := by
    rw [← wedge_ne_zero_iff (by simp), hcast, ← hwC]
    exact χ.wedgeC_ne_zero
  -- `ι_φ(h) = (1 ⊗ ψ)(Φ_E(h))`, `Φ_E(h)` by Lemma 6.5 for the choice `χ`, then (94)
  have step1 : stabIota hT hφ χ.source = LinearMap.lTensor _ (stabPsi hφ) χ.value :=
    (stabIota_apply hT hφ χ.source).trans (congrArg (LinearMap.lTensor _ (stabPsi hφ)) h65)
  have step2 : LinearMap.lTensor _ (stabPsi hφ) χ.value =
      wedge (Fin.append (stabJ T φ ∘ a) bbar) hkl ⊗ₜ
        stabPsi hφ (dualVec (wedge (Fin.append cbar r ∘ Fin.cast hn.symm) (by simp))) :=
    (LinearMap.lTensor_tmul _ (stabPsi hφ) χ.wedgeB (dualVec χ.wedgeC)).trans
      (congrArg₂ (fun x y => x ⊗ₜ[ℝ] stabPsi hφ (dualVec y)) hwB (hwC.trans hcast.symm))
  refine (congrArg (stabIota hT hφ) hsrc.symm).trans ?_
  exact step1.trans (step2.trans
    ((congrArg (wedge (Fin.append (stabJ T φ ∘ a) bbar) hkl ⊗ₜ[ℝ] ·) (stabPsi_dualVec hφ hc)).trans
      (TensorProduct.tmul_smul _ _ _)))

end Stab


end Polyfold
