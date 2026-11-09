import Polyfold.Chapter6.GoodProjections

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.3,
pp. 208–211, and Appendix 6.7.2, pp. 235–237: the exact sequence `E(T,P)` and **Proposition 6.4.10 (preprint 6.11)**, the
isomorphism `γ^P_T : det(T) → det(P T)`, **Proposition 6.4.11 (preprint 6.12)** (`γ^P_{QT} ∘ γ^Q_T = γ^P_T` for
`P ≤ Q`) and **Corollary 6.4.12 (preprint 6.13)** *(book 2017: Proposition 6.4, Proposition 6.5, Corollary 6.1; see
`BookConcordance.md`)*.

# The isomorphisms `γ^P_T`

## The text, paraphrased

For `P ∈ Π_T` the sequence
`E(T,P) : 0 → ker T →j ker(P T) →Φ F / R(P) →π coker T → 0`, with `j` the inclusion,
`Φ(x) = T x + R(P)` and `π(f + R(P)) = (I − P) f + R(T)`, is exact (Proposition 6.4.10 (preprint 6.11)).  Since
`R(P) = R(P T)`, its isomorphism `Φ_{E(T,P)}` is an isomorphism `γ^P_T : det(T) → det(P T)`.  For
`P ≤ Q` in `Π_T`, `Q T` is Fredholm, `P ∈ Π_{QT}`, and `γ^P_{QT} ∘ γ^Q_T = γ^P_T`
(Proposition 6.4.11 (preprint 6.12), proof in §6.7.2).  Hence (Corollary 6.4.12 (preprint 6.13)) for `P ≤ S` and `P ≤ R` in `Π_T` the
map `det(S T) → det(R T)`, `h ↦ (γ^P_{RT})⁻¹ ∘ γ^P_{ST}(h)`, does not depend on `P` and equals
`γ^R_T ∘ (γ^S_T)⁻¹`.

## What is formalized

* `Polyfold.projSeqJ`, `projSeqPhi`, `projSeqPi`: the maps `j`, `Φ`, `π`; **Proposition 6.4.10 (preprint 6.11)**
  (`proposition_6_4_10`): `E(T,P)` is exact; `Polyfold.projSeq`: `E(T,P)` as a `FourTermExact`.
* `Polyfold.gammaProj hT hP` (`γ^P_T : det(T) ≅ det(P T)`): `Φ_{E(T,P)}` followed by the
  identification `F / R(P) = F / R(P T)`; `gammaProj_tmul`: its value on wedges, formula (91);
  `gammaProj_wedge_tmul`: the same for the choice given by families of vectors `a`, `b`, `c`, `d`.
* **Proposition 6.4.11 (preprint 6.12)** (`proposition_6_4_11`): `Q T` is Fredholm, `P ∈ Π_{QT}`, and
  `γ^P_{QT} ∘ γ^Q_T = γ^P_T`, up to the identification `det(P (Q T)) = det(P T)` (the operators
  `P ∘ (Q ∘ T)` and `P ∘ T` are equal, the types of their kernels are not).
* **Corollary 6.4.12 (preprint 6.13)** (`corollary_6_4_12`): `(γ^P_{RT})⁻¹ ∘ γ^P_{ST} = γ^R_T ∘ (γ^S_T)⁻¹`, again up to
  the identification `det(P (S T)) = det(P (R T))`; the right side does not involve `P`.

## Reading

`γ^P_T` is read with the identification of `λ*(F / R(P))` with `λ*(F / R(P T))` by the identity
of `F`, which is what "recalling `R(P) = R(P T)`" means.

In the proof of Proposition 6.4.11 (preprint 6.12) (§6.7.2) the step "the classes of `d₁, …, d_l, T b₁, …` span
`ker Q̃`" is proved directly in `F` (`mem_span_append_of_ker`: if `Q g = 0`, then `g` is a
combination of the `dᵢ` plus `T x` with `x ∈ ker(Q T)`); the classes `[T b̃]` and `[Q T b̃]` in
`F / R(P)` then differ by elements of the span of `[d]`, `[T b]`, which does not change the wedge
(`wedge_append_add_right`).
-/

open Module TensorProduct

noncomputable section

namespace Polyfold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

section Sequence

variable (T : E →L[ℝ] F) (P : F →L[ℝ] F)

set_option linter.unusedSectionVars false in
/-- `ker T ⊆ ker(P T)`. -/
theorem ker_le_ker_comp :
    LinearMap.ker (T : E →ₗ[ℝ] F) ≤ LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F) := by
  intro x hx
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx ⊢
  simp [hx]

/-- `j : ker T → ker(P T)`, the inclusion. -/
def projSeqJ : LinearMap.ker (T : E →ₗ[ℝ] F) →ₗ[ℝ]
    LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F) :=
  Submodule.inclusion (ker_le_ker_comp T P)

/-- `Φ : ker(P T) → F / R(P)`, `x ↦ T x + R(P)`. -/
def projSeqPhi : LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F) →ₗ[ℝ]
    F ⧸ LinearMap.range (P : F →ₗ[ℝ] F) :=
  (LinearMap.range (P : F →ₗ[ℝ] F)).mkQ ∘ₗ (T : E →ₗ[ℝ] F) ∘ₗ
    (LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)).subtype

variable {T P}

/-- `π : F / R(P) → coker T`, `f + R(P) ↦ (I − P) f + R(T)` (well defined since `P` is a
projection). -/
def projSeqPi (hP : P ∘L P = P) : F ⧸ LinearMap.range (P : F →ₗ[ℝ] F) →ₗ[ℝ]
    F ⧸ LinearMap.range (T : E →ₗ[ℝ] F) :=
  (LinearMap.range (P : F →ₗ[ℝ] F)).liftQ
    ((LinearMap.range (T : E →ₗ[ℝ] F)).mkQ ∘ₗ (LinearMap.id - (P : F →ₗ[ℝ] F))) (by
      rintro _ ⟨f, rfl⟩
      have : P (P f) = P f := by
        simpa using congrArg (fun A : F →L[ℝ] F => A f) hP
      simp [this])

set_option linter.unusedSectionVars false in
@[simp] theorem projSeqPi_mk (hP : P ∘L P = P) (f : F) :
    projSeqPi (T := T) hP (Submodule.Quotient.mk f) = Submodule.Quotient.mk (f - P f) := rfl

/-- **Proposition 6.4.10 (preprint 6.11)**: the sequence `E(T,P) : 0 → ker T → ker(P T) → F / R(P) → coker T → 0` is
exact. -/
theorem proposition_6_4_10 (hP : IsGoodLeftProj T P) :
    Function.Injective (projSeqJ T P) ∧
      LinearMap.range (projSeqJ T P) = LinearMap.ker (projSeqPhi T P) ∧
      LinearMap.range (projSeqPhi T P) = LinearMap.ker (projSeqPi (T := T) hP.isProj) ∧
      Function.Surjective (projSeqPi (T := T) hP.isProj) := by
  have hPP : ∀ f, P (P f) = P f := fun f => by
    simpa using congrArg (fun A : F →L[ℝ] F => A f) hP.isProj
  refine ⟨Submodule.inclusion_injective _, ?_, ?_, ?_⟩
  · -- exactness at `ker(P T)`
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      have hy : T (y : E) = 0 := y.2
      rw [LinearMap.mem_ker]
      change Submodule.Quotient.mk (T (y : E)) = 0
      rw [hy, Submodule.Quotient.mk_zero]
    · intro hx
      rw [LinearMap.mem_ker] at hx
      change Submodule.Quotient.mk (T (x : E)) = 0 at hx
      rw [Submodule.Quotient.mk_eq_zero] at hx
      obtain ⟨f, hf⟩ := hx
      have hf' : P f = T (x : E) := hf
      have hPT : P (T (x : E)) = 0 := by simpa using x.2
      have h0 : T (x : E) = 0 := by
        have h2 : P (T (x : E)) = T (x : E) := by
          rw [← hf']
          exact hPP f
        rw [← h2, hPT]
      exact ⟨⟨x, h0⟩, rfl⟩
  · -- exactness at `F / R(P)`
    ext y
    induction y using Submodule.Quotient.induction_on with
    | H y =>
    constructor
    · rintro ⟨x, hx⟩
      have hPT : P (T (x : E)) = 0 := by simpa using x.2
      rw [← hx, LinearMap.mem_ker]
      change projSeqPi _ (Submodule.Quotient.mk (T (x : E))) = 0
      rw [projSeqPi_mk, hPT, sub_zero, Submodule.Quotient.mk_eq_zero]
      exact ⟨x, rfl⟩
    · intro hy
      rw [LinearMap.mem_ker, projSeqPi_mk, Submodule.Quotient.mk_eq_zero] at hy
      obtain ⟨x, hx⟩ := hy
      have hx' : T x = y - P y := hx
      have hPx : P (T x) = 0 := by rw [hx', map_sub, hPP, sub_self]
      refine ⟨⟨x, by simpa using hPx⟩, ?_⟩
      simp only [projSeqPhi, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
        ContinuousLinearMap.coe_coe, Submodule.mkQ_apply]
      rw [hx', Submodule.Quotient.eq]
      simp
  · -- surjectivity of `π`
    intro z
    induction z using Submodule.Quotient.induction_on with
    | H f =>
    have hPf : P f ∈ LinearMap.range ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F) := by
      rw [hP.range_comp]
      exact ⟨f, rfl⟩
    obtain ⟨x, hx⟩ := hPf
    have hx' : P (T x) = P f := hx
    refine ⟨Submodule.Quotient.mk (f - T x), ?_⟩
    rw [projSeqPi_mk, Submodule.Quotient.eq]
    refine ⟨-x, ?_⟩
    simp only [ContinuousLinearMap.coe_coe, map_neg, map_sub, hx']
    abel

/-- The exact sequence `E(T,P)`. -/
def projSeq (hP : IsGoodLeftProj T P) :
    FourTermExact (LinearMap.ker (T : E →ₗ[ℝ] F))
      (LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F))
      (F ⧸ LinearMap.range (P : F →ₗ[ℝ] F)) (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) where
  α := projSeqJ T P
  β := projSeqPhi T P
  γ := projSeqPi hP.isProj
  injective_α := (proposition_6_4_10 hP).1
  range_α := (proposition_6_4_10 hP).2.1
  range_β := (proposition_6_4_10 hP).2.2.1
  surjective_γ := (proposition_6_4_10 hP).2.2.2

end Sequence

/-! ### `γ^P_T` -/

variable {T : E →L[ℝ] F} {P : F →L[ℝ] F}

/-- `F / R(P) ≅ F / R(P T)` (the identity of `F`, since `R(P T) = R(P)`). -/
def cokerCompEquiv (hP : IsGoodLeftProj T P) :
    (F ⧸ LinearMap.range ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)) ≃ₗ[ℝ]
      F ⧸ LinearMap.range (P : F →ₗ[ℝ] F) :=
  Submodule.quotEquivOfEq _ _ hP.range_comp

/-- **`γ^P_T : det(T) → det(P T)`**: `Φ_{E(T,P)} : λ(ker T) ⊗ λ*(coker T) → λ(ker P T) ⊗ λ*(F/R(P))`
followed by `λ*(F / R(P)) = λ*(F / R(P T))`. -/
def gammaProj (hT : T.IsFredholm) (hP : IsGoodLeftProj T P) :
    fredholmDet T ≃ₗ[ℝ] fredholmDet (P ∘L T) :=
  haveI := hT.finite_ker
  haveI : FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := hT.finite_coker
  haveI := hP.finite_coker
  haveI := (hP.isFredholm_comp hT).finite_ker
  (projSeq hP).phiEquiv ≪≫ₗ
    TensorProduct.congr (LinearEquiv.refl ℝ _) (maxPowDualEquiv (cokerCompEquiv hP))

/-- **`γ^P_T` on wedges** (formula (91) for `E(T,P)`): for every choice `χ` of the text's data for
`E(T,P)`, `γ^P_T((a₁ ∧ … ∧ aₙ) ⊗ (d₁ ∧ … ∧ d_l)*)` is
`(a₁ ∧ … ∧ aₙ ∧ b'₁ ∧ … ∧ b'_{m−n}) ⊗ (c₁ ∧ … ∧ c_l ∧ Φ(b'₁) ∧ … ∧ Φ(b'_{m−n}))*`, the second
wedge read in `F / R(P T)`. -/
theorem gammaProj_tmul (hT : T.IsFredholm) (hP : IsGoodLeftProj T P) :
    haveI := hT.finite_ker
    haveI : FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := hT.finite_coker
    haveI := hP.finite_coker
    haveI := (hP.isFredholm_comp hT).finite_ker
    ∀ χ : (projSeq hP).Choice,
      gammaProj hT hP χ.source =
        χ.wedgeB ⊗ₜ maxPowDualEquiv (cokerCompEquiv hP) (dualVec χ.wedgeC) := by
  intro χ
  rw [gammaProj, LinearEquiv.trans_apply, FourTermExact.coe_phiEquiv, FourTermExact.lemma_6_3_3,
    FourTermExact.Choice.value, TensorProduct.congr_tmul, LinearEquiv.refl_apply]

/-- **`γ^P_T` on families of vectors** (formula (91) for `E(T,P)`, in the form used in §6.7.2):
for linearly independent `a`, `d` of lengths `dim ker T`, `dim coker T`, vectors `b` completing `a`
to a basis of `ker(P T)` and `c` with `π(c) = d`,
`γ^P_T((a₁ ∧ … ∧ aₙ) ⊗ (d₁ ∧ … ∧ d_l)*) = (a ∧ b) ⊗ (c ∧ Φ(b))*`, the second wedge read in
`F / R(P T)`. -/
theorem gammaProj_wedge_tmul (hT : T.IsFredholm) (hP : IsGoodLeftProj T P) {n l j : ℕ}
    {a : Fin n → LinearMap.ker (T : E →ₗ[ℝ] F)} (ha : LinearIndependent ℝ a)
    (hn : n = finrank ℝ (LinearMap.ker (T : E →ₗ[ℝ] F)))
    {d : Fin l → F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)} (hd : LinearIndependent ℝ d)
    (hl : l = finrank ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)))
    {b : Fin j → LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)}
    (hb : LinearIndependent ℝ (Fin.append (projSeqJ T P ∘ a) b))
    (hj : n + j = finrank ℝ (LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)))
    {c : Fin l → F ⧸ LinearMap.range (P : F →ₗ[ℝ] F)}
    (hc : ∀ i, projSeqPi (T := T) hP.isProj (c i) = d i)
    (hC : l + j = finrank ℝ (F ⧸ LinearMap.range ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F))) :
    gammaProj hT hP (wedge a hn ⊗ₜ dualVec (wedge d hl)) =
      wedge (Fin.append (projSeqJ T P ∘ a) b) hj ⊗ₜ
        dualVec (wedge ((cokerCompEquiv hP).symm ∘ Fin.append c (projSeqPhi T P ∘ b)) hC) := by
  have := hT.finite_ker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := hT.finite_coker
  have := hP.finite_coker
  have := (hP.isFredholm_comp hT).finite_ker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)) :=
    (hP.isFredholm_comp hT).finite_coker
  have hC' : l + j = finrank ℝ (F ⧸ LinearMap.range (P : F →ₗ[ℝ] F)) :=
    hC.trans (cokerCompEquiv hP).finrank_eq
  have hli := (projSeq hP).linearIndependent_append_lift ha hn hd hl hb hj hc hC'
  rw [gammaProj, LinearEquiv.trans_apply, FourTermExact.coe_phiEquiv,
    (projSeq hP).phi_wedge_tmul ha hn hd hl hb hj hc hC', TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, maxPowDualEquiv_dualVec_symm _ hli]
  rfl

/-! ### Proposition 6.4.11 (preprint 6.12) and Corollary 6.4.12 (preprint 6.13) -/

set_option linter.unusedSectionVars false in
/-- `P ∘ (Q ∘ T) = P ∘ T` for `P ≤ Q`. -/
theorem comp_comp_eq_of_projLE {Q : F →L[ℝ] F} (hPQ : ProjLE P Q) :
    P ∘L (Q ∘L T) = P ∘L T := by
  rw [← ContinuousLinearMap.comp_assoc, ← hPQ.1]

/-- For `P ≤ Q` in `Π_T`, `P ∈ Π_{QT}`. -/
theorem IsGoodLeftProj.of_projLE {Q : F →L[ℝ] F} (hP : IsGoodLeftProj T P)
    (hPQ : ProjLE P Q) : IsGoodLeftProj (Q ∘L T) P where
  isProj := hP.isProj
  finite_coker := hP.finite_coker
  range_comp := by rw [comp_comp_eq_of_projLE hPQ]; exact hP.range_comp

/-- **The step "`ker Q̃` is spanned by `[d]`, `[T b]`" of §6.7.2**, in `F`: if `[d₁], …, [d_l]` is
a basis of `coker T` with `Q dᵢ = 0` and `a, b` is a basis of `ker(Q T)` (`a` in `ker T`), every
`g ∈ ker Q` is a combination of the `dᵢ` and the `T bⱼ`. -/
theorem mem_span_append_of_ker {Q : F →L[ℝ] F} (hT : T.IsFredholm) (hQ : IsGoodLeftProj T Q)
    {n l m : ℕ} {a : Fin n → LinearMap.ker (T : E →ₗ[ℝ] F)}
    (d0 : Basis (Fin l) ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F))) {dt : Fin l → F}
    (hdt : ∀ i, Submodule.Quotient.mk (dt i) = d0 i) (hQdt : ∀ i, Q (dt i) = 0)
    {b : Fin m → LinearMap.ker ((Q ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)}
    (hb : LinearIndependent ℝ (Fin.append (projSeqJ T Q ∘ a) b))
    (hm : n + m = finrank ℝ (LinearMap.ker ((Q ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)))
    {g : F} (hg : Q g = 0) :
    g ∈ Submodule.span ℝ (Set.range (Fin.append dt (fun i => T (b i : E)))) := by
  have := (hQ.isFredholm_comp hT).finite_ker
  have hg0 : (Submodule.Quotient.mk g : F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) ∈
      Submodule.span ℝ (Set.range d0) := d0.span_eq ▸ Submodule.mem_top
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hg0
  have hmem : g - ∑ i, r i • dt i ∈ LinearMap.range (T : E →ₗ[ℝ] F) := by
    rw [← Submodule.Quotient.mk_eq_zero]
    have : (LinearMap.range (T : E →ₗ[ℝ] F)).mkQ (g - ∑ i, r i • dt i) = 0 := by
      rw [map_sub, map_sum]
      simp only [map_smul, Submodule.mkQ_apply, hdt]
      rw [hr, sub_self]
    exact this
  obtain ⟨x, hx⟩ := hmem
  have hx' : T x = g - ∑ i, r i • dt i := hx
  have hxQ : Q (T x) = 0 := by
    rw [hx', map_sub, hg, map_sum]
    simp [hQdt]
  let xk : LinearMap.ker ((Q ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F) := ⟨x, by simpa using hxQ⟩
  have hxspan : xk ∈ Submodule.span ℝ (Set.range (Fin.append (projSeqJ T Q ∘ a) b)) :=
    (hb.span_eq_top_of_card_eq_finrank' (by simp [hm])) ▸ Submodule.mem_top
  have hle : Submodule.span ℝ (Set.range (Fin.append (projSeqJ T Q ∘ a) b)) ≤
      (Submodule.span ℝ (Set.range (fun i => T (b i : E)))).comap
        ((T : E →ₗ[ℝ] F) ∘ₗ (LinearMap.ker ((Q ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)).subtype) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    induction i using Fin.addCases with
    | left i =>
      have hTa : T ((a i : LinearMap.ker (T : E →ₗ[ℝ] F)) : E) = 0 := (a i).2
      simp only [Fin.append_left, Function.comp_apply, SetLike.mem_coe,
        Submodule.mem_comap, LinearMap.comp_apply, Submodule.coe_subtype]
      change T ((a i : LinearMap.ker (T : E →ₗ[ℝ] F)) : E) ∈ _
      rw [hTa]
      exact zero_mem _
    | right i =>
      simp only [Fin.append_right, SetLike.mem_coe, Submodule.mem_comap,
        LinearMap.comp_apply, Submodule.coe_subtype, ContinuousLinearMap.coe_coe]
      exact Submodule.subset_span ⟨i, rfl⟩
  have hTx : T x ∈ Submodule.span ℝ (Set.range (fun i => T (b i : E))) := hle hxspan
  rw [span_range_append]
  have : g = ∑ i, r i • dt i + T x := by rw [hx']; abel
  rw [this]
  exact Submodule.add_mem_sup
    (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)) hTx

/-- **Proposition 6.4.11 (preprint 6.12)**: if `T` is Fredholm and `P ≤ Q` in `Π_T`, then `Q T` is Fredholm,
`P ∈ Π_{QT}`, and `γ^P_{QT} ∘ γ^Q_T = γ^P_T` (up to `det(P (Q T)) = det(P T)`). -/
theorem proposition_6_4_11 {Q : F →L[ℝ] F} (hT : T.IsFredholm) (hP : IsGoodLeftProj T P)
    (hQ : IsGoodLeftProj T Q) (hPQ : ProjLE P Q) :
    (Q ∘L T).IsFredholm ∧ IsGoodLeftProj (Q ∘L T) P ∧
      ∀ h : fredholmDet T,
        linDetEquivOfEq (congrArg (fun A : E →L[ℝ] F => (A : E →ₗ[ℝ] F))
            (comp_comp_eq_of_projLE (T := T) hPQ))
          (gammaProj (hQ.isFredholm_comp hT) (hP.of_projLE hPQ) (gammaProj hT hQ h)) =
        gammaProj hT hP h := by
  have hQT := hQ.isFredholm_comp hT
  have hP' := hP.of_projLE hPQ
  refine ⟨hQT, hP', fun h => ?_⟩
  have iT := hT.finite_ker
  have iTc : FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := hT.finite_coker
  have hn0 : ∃ n, n = finrank ℝ (LinearMap.ker (T : E →ₗ[ℝ] F)) := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ := hn0
  have hl0 : ∃ l, l = finrank ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := ⟨_, rfl⟩
  obtain ⟨l, hl⟩ := hl0
  have a : Basis (Fin n) ℝ (LinearMap.ker (T : E →ₗ[ℝ] F)) :=
    (Module.finBasis ℝ (LinearMap.ker (T : E →ₗ[ℝ] F))).reindex (finCongr hn.symm)
  have d0 : Basis (Fin l) ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) :=
    (Module.finBasis ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F))).reindex (finCongr hl.symm)
  have := hP.finite_coker
  have := hQ.finite_coker
  have := hQT.finite_ker
  have := (hP.isFredholm_comp hT).finite_ker
  have := (hP'.isFredholm_comp hQT).finite_ker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range ((Q ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)) :=
    hQT.finite_coker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)) :=
    (hP.isFredholm_comp hT).finite_coker
  -- `P Q = P` and `Q² = Q`
  have hPQf : ∀ f, P (Q f) = P f := fun f => by
    have := congrArg (fun A : F →L[ℝ] F => A f) hPQ.1
    simpa using this.symm
  have hQQ : ∀ f, Q (Q f) = Q f := fun f => by
    simpa using congrArg (fun A : F →L[ℝ] F => A f) hQ.isProj
  -- the basis `a` of `ker T` and the basis `[d]` of `coker T` with `d ∈ R(I − Q) = ker Q`
  have hrep : ∀ i, ∃ f : F, Submodule.Quotient.mk f = d0 i ∧ Q f = 0 := by
    intro i
    obtain ⟨f, hf⟩ := Submodule.Quotient.mk_surjective _ (d0 i)
    have : Q f ∈ LinearMap.range ((Q ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F) := by
      rw [hQ.range_comp]
      exact ⟨f, rfl⟩
    obtain ⟨x, hx⟩ := this
    have hx' : Q (T x) = Q f := hx
    refine ⟨f - T x, ?_, ?_⟩
    · rw [← hf, Submodule.Quotient.eq]
      exact ⟨-x, by simp⟩
    · rw [map_sub, hx', sub_self]
  choose dt hdt hQdt using hrep
  have hPdt : ∀ i, P (dt i) = 0 := fun i => by rw [← hPQf, hQdt, map_zero]
  -- `b` completing `a` to a basis of `ker(Q T)`, `b̃` completing `(a, b)` to one of `ker(P Q T)`
  have hex1 :=
    exists_linearIndependent_append (projSeqJ T Q) (proposition_6_4_10 hQ).1 a.linearIndependent hn
  choose m b hb hm using hex1
  let a2 := Fin.append (projSeqJ T Q ∘ ⇑a) b
  have hex2 := exists_linearIndependent_append (projSeqJ (Q ∘L T) P) (proposition_6_4_10 hP').1 hb hm
  choose k bt hbt hk using hex2
  have hQTb : ∀ i, Q (T (b i : E)) = 0 := fun i => by simpa using (b i).2
  have hPTb : ∀ i, P (T (b i : E)) = 0 := fun i => by rw [← hPQf, hQTb, map_zero]
  -- `γ^Q_T(h₀) = (a ∧ b) ⊗ ([d]_Q ∧ [T b]_Q)*`
  have hC1 : l + m = finrank ℝ (F ⧸ LinearMap.range (Q : F →ₗ[ℝ] F)) :=
    (projSeq hQ).finrank_eq_of_families hn hl hm
  have hC1' : l + m = finrank ℝ (F ⧸ LinearMap.range ((Q ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)) :=
    hC1.trans (cokerCompEquiv hQ).finrank_eq.symm
  let c1 : Fin l → F ⧸ LinearMap.range (Q : F →ₗ[ℝ] F) := fun i => Submodule.Quotient.mk (dt i)
  have hc1 : ∀ i, projSeqPi (T := T) hQ.isProj (c1 i) = d0 i := by
    intro i
    simp only [c1, projSeqPi_mk, hQdt, sub_zero, hdt]
  have step1 := gammaProj_wedge_tmul hT hQ a.linearIndependent hn d0.linearIndependent hl hb hm
    hc1 hC1'
  let d2 := (cokerCompEquiv hQ).symm ∘ Fin.append c1 (projSeqPhi T Q ∘ b)
  have hd2li : LinearIndependent ℝ d2 :=
    ((projSeq hQ).linearIndependent_append_lift a.linearIndependent hn d0.linearIndependent hl
      hb hm hc1 hC1).map' _ (cokerCompEquiv hQ).symm.ker
  -- `γ^P_{QT}(γ^Q_T h₀) = (a ∧ b ∧ b̃) ⊗ ([d]_P ∧ [T b]_P ∧ [Q T b̃]_P)*`
  let c2 : Fin (l + m) → F ⧸ LinearMap.range (P : F →ₗ[ℝ] F) :=
    fun i => Submodule.Quotient.mk (Fin.append dt (fun i => T (b i : E)) i)
  have hc2 : ∀ i, projSeqPi (T := Q ∘L T) hP'.isProj (c2 i) = d2 i := by
    intro i
    induction i using Fin.addCases with
    | left i =>
      simp only [c2, d2, Function.comp_apply, Fin.append_left, projSeqPi_mk, hPdt, sub_zero, c1]
      rfl
    | right i =>
      simp only [c2, d2, Function.comp_apply, Fin.append_right, projSeqPi_mk, hPTb, sub_zero]
      rfl
  have hC2 : l + m + k = finrank ℝ (F ⧸ LinearMap.range (P : F →ₗ[ℝ] F)) :=
    (projSeq hP').finrank_eq_of_families hm hC1' hk
  have hC2' : l + m + k =
      finrank ℝ (F ⧸ LinearMap.range ((P ∘L (Q ∘L T) : E →L[ℝ] F) : E →ₗ[ℝ] F)) :=
    hC2.trans (cokerCompEquiv hP').finrank_eq.symm
  have step2 := gammaProj_wedge_tmul hQT hP' hb hm hd2li hC1' hbt hk hc2 hC2'
  let w2 := Fin.append c2 (projSeqPhi (Q ∘L T) P ∘ bt)
  have hw2li : LinearIndependent ℝ ((cokerCompEquiv hP').symm ∘ w2) :=
    ((projSeq hP').linearIndependent_append_lift hb hm hd2li hC1' hbt hk hc2 hC2).map' _
      (cokerCompEquiv hP').symm.ker
  -- `γ^P_T(h₀) = (a ∧ b ∧ b̃) ⊗ ([d]_P ∧ [T b]_P ∧ [T b̃]_P)*`
  let e := congrArg (fun A : E →L[ℝ] F => (A : E →ₗ[ℝ] F)) (comp_comp_eq_of_projLE (T := T) hPQ)
  let eK := LinearEquiv.ofEq (LinearMap.ker ((P ∘L (Q ∘L T) : E →L[ℝ] F) : E →ₗ[ℝ] F))
    (LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)) (by rw [e])
  let b3 := eK ∘ Fin.append (projSeqJ (Q ∘L T) P ∘ b) bt
  have hF : Fin.append (projSeqJ T P ∘ ⇑a) b3 =
      (eK ∘ Fin.append (projSeqJ (Q ∘L T) P ∘ a2) bt) ∘ Fin.cast (Nat.add_assoc n m k).symm := by
    funext i
    induction i using Fin.addCases with
    | left i =>
      rw [Fin.append_left]
      simp only [Function.comp_apply]
      rw [show Fin.cast (Nat.add_assoc n m k).symm (Fin.castAdd (m + k) i) =
        Fin.castAdd k (Fin.castAdd m i) from Fin.ext rfl, Fin.append_left]
      simp only [Function.comp_apply, a2, Fin.append_left]
      rfl
    | right i =>
      induction i using Fin.addCases with
      | left i =>
        rw [Fin.append_right]
        simp only [b3, Function.comp_apply]
        rw [Fin.append_left, show Fin.cast (Nat.add_assoc n m k).symm
          (Fin.natAdd n (Fin.castAdd k i)) = Fin.castAdd k (Fin.natAdd n i) from Fin.ext rfl,
          Fin.append_left]
        simp only [Function.comp_apply, a2, Fin.append_right]
      | right i =>
        rw [Fin.append_right]
        simp only [b3, Function.comp_apply]
        rw [Fin.append_right, show Fin.cast (Nat.add_assoc n m k).symm
          (Fin.natAdd n (Fin.natAdd m i)) = Fin.natAdd (n + m) i from
          Fin.ext (Nat.add_assoc n m i).symm, Fin.append_right]
  have hj3 : n + (m + k) = finrank ℝ (LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)) := by
    have := hk.trans eK.finrank_eq
    omega
  have hb3 : LinearIndependent ℝ (Fin.append (projSeqJ T P ∘ ⇑a) b3) := by
    have h1 : LinearIndependent ℝ (⇑eK ∘ Fin.append (projSeqJ (Q ∘L T) P ∘ a2) bt) := by
      have := hbt.map' eK.toLinearMap eK.ker
      simpa only [LinearEquiv.coe_toLinearMap] using this
    rw [hF]
    exact h1.comp (Fin.cast (Nat.add_assoc n m k).symm) (Fin.cast_injective _)
  let c3 : Fin l → F ⧸ LinearMap.range (P : F →ₗ[ℝ] F) := fun i => Submodule.Quotient.mk (dt i)
  have hc3 : ∀ i, projSeqPi (T := T) hP.isProj (c3 i) = d0 i := by
    intro i
    simp only [c3, projSeqPi_mk, hPdt, sub_zero, hdt]
  have hC3P : l + (m + k) = finrank ℝ (F ⧸ LinearMap.range (P : F →ₗ[ℝ] F)) :=
    (projSeq hP).finrank_eq_of_families hn hl hj3
  have hC3 : l + (m + k) = finrank ℝ (F ⧸ LinearMap.range ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)) :=
    hC3P.trans (cokerCompEquiv hP).finrank_eq.symm
  have step4 := gammaProj_wedge_tmul hT hP a.linearIndependent hn d0.linearIndependent hl hb3
    hj3 hc3 hC3
  -- `[T b̃]_P − [Q T b̃]_P = [(I − Q) T b̃]_P` lies in the span of `[d]_P`, `[T b]_P`
  have hkey : ∀ g : F, Q g = 0 →
      (Submodule.Quotient.mk g : F ⧸ LinearMap.range (P : F →ₗ[ℝ] F)) ∈
        Submodule.span ℝ (Set.range c2) := by
    intro g hg
    have hg' := mem_span_append_of_ker hT hQ d0 hdt hQdt hb hm hg
    have := Submodule.mem_map_of_mem (f := (LinearMap.range (P : F →ₗ[ℝ] F)).mkQ) hg'
    rw [← Submodule.span_image, ← Set.range_comp] at this
    exact this
  -- the `C`-wedges agree in `λ(F / R(P))`
  have hw : wedge (Fin.append c3 (projSeqPhi T P ∘ b3)) hC3P = wedge w2 hC2 := by
    have hw3 : projSeqPhi T P ∘ b3 = Fin.append
        (fun i => (Submodule.Quotient.mk (T (b i : E)) : F ⧸ LinearMap.range (P : F →ₗ[ℝ] F)))
        (fun i => Submodule.Quotient.mk (T (bt i : E))) := by
      funext i
      induction i using Fin.addCases with
      | left i =>
        simp only [b3, Function.comp_apply, Fin.append_left]
        rfl
      | right i =>
        simp only [b3, Function.comp_apply, Fin.append_right]
        rfl
    rw [hw3, wedge_append_assoc _ _ _ _ hC2]
    have hc23 : Fin.append c3
        (fun i => (Submodule.Quotient.mk (T (b i : E)) : F ⧸ LinearMap.range (P : F →ₗ[ℝ] F))) =
        c2 := by
      funext i
      induction i using Fin.addCases with
      | left i => simp [c2, c3]
      | right i => simp [c2]
    have hsplit : (fun i => (Submodule.Quotient.mk (T (bt i : E)) :
        F ⧸ LinearMap.range (P : F →ₗ[ℝ] F))) = projSeqPhi (Q ∘L T) P ∘ bt +
          fun i => Submodule.Quotient.mk (T (bt i : E) - Q (T (bt i : E))) := by
      funext i
      simp only [Pi.add_apply, Function.comp_apply]
      change _ = Submodule.Quotient.mk (Q (T (bt i : E))) + _
      rw [← Submodule.Quotient.mk_add, add_sub_cancel]
    rw [hc23, hsplit, wedge_append_add_right]
    intro i
    exact hkey _ (by rw [map_sub, hQQ, sub_self])
  -- reduce to the nonzero vector `h₀ = (a₁ ∧ … ∧ aₙ) ⊗ ([d₁] ∧ … ∧ [d_l])*`
  let h0 : fredholmDet T := wedge (⇑a) hn ⊗ₜ dualVec (wedge (⇑d0) hl)
  have h0ne : h0 ≠ 0 := tmul_ne_zero_of_ne_zero (wedge_basis_ne_zero' a hn)
    (dualVec_ne_zero finrank_maxPow (wedge_basis_ne_zero' d0 hl))
  suffices H : linDetEquivOfEq e (gammaProj hQT hP' (gammaProj hT hQ h0)) = gammaProj hT hP h0 by
    have key : (linDetEquivOfEq e).toLinearMap ∘ₗ (gammaProj hQT hP').toLinearMap ∘ₗ
        (gammaProj hT hQ).toLinearMap = (gammaProj hT hP).toLinearMap := by
      refine linearMap_ext_of_ne_zero (finrank_fredholmDet hT) h0ne ?_
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      exact H
    have := LinearMap.congr_fun key h
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at this
    exact this
  refine (congrArg (fun x => linDetEquivOfEq e (gammaProj hQT hP' x)) step1).trans ?_
  refine (congrArg (fun x => linDetEquivOfEq e x) step2).trans ?_
  refine (linDetEquivOfEq_tmul e _ _ _ hw2li _).trans (Eq.trans ?_ step4.symm)
  refine congrArg₂ (fun x y => x ⊗ₜ[ℝ] y) ?_ (congrArg dualVec ?_)
  · rw [hF]
    exact (wedge_cast (⇑eK ∘ Fin.append (projSeqJ (Q ∘L T) P ∘ a2) bt) _ _).symm
  · have hqe : ⇑(Submodule.quotEquivOfEq
        (LinearMap.range ((P ∘L (Q ∘L T) : E →L[ℝ] F) : E →ₗ[ℝ] F))
        (LinearMap.range ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)) (by rw [e])) ∘
        ⇑(cokerCompEquiv hP').symm ∘ w2 = ⇑(cokerCompEquiv hP).symm ∘ w2 := by
      funext i
      obtain ⟨f, hf⟩ := Submodule.Quotient.mk_surjective _ (w2 i)
      simp only [Function.comp_apply, ← hf]
      rfl
    rw [hqe]
    have := congrArg (maxPowEquiv (cokerCompEquiv hP).symm) hw
    rw [maxPowEquiv_wedge, maxPowEquiv_wedge] at this
    exact this.symm

/-- `P ∘ (S ∘ T) = P ∘ (R ∘ T)` for `P ≤ S` and `P ≤ R`. -/
theorem comp_comp_eq_comp_comp {R S : F →L[ℝ] F} (hPS : ProjLE P S) (hPR : ProjLE P R) :
    P ∘L (S ∘L T) = P ∘L (R ∘L T) := by
  rw [comp_comp_eq_of_projLE hPS, comp_comp_eq_of_projLE hPR]

/-- **Corollary 6.4.12 (preprint 6.13)**: for `P ≤ S` and `P ≤ R` in `Π_T`, the map
`det(S T) → det(R T)`, `h ↦ (γ^P_{RT})⁻¹ ∘ γ^P_{ST}(h)` (through `det(P (S T)) = det(P (R T))`),
equals `γ^R_T ∘ (γ^S_T)⁻¹`; in particular it does not depend on `P`. -/
theorem corollary_6_4_12 {R S : F →L[ℝ] F} (hT : T.IsFredholm) (hP : IsGoodLeftProj T P)
    (hR : IsGoodLeftProj T R) (hS : IsGoodLeftProj T S) (hPS : ProjLE P S) (hPR : ProjLE P R)
    (h : fredholmDet (S ∘L T)) :
    (gammaProj (hR.isFredholm_comp hT) (hP.of_projLE hPR)).symm
        (linDetEquivOfEq (congrArg (fun A : E →L[ℝ] F => (A : E →ₗ[ℝ] F))
            (comp_comp_eq_comp_comp (T := T) hPS hPR))
          (gammaProj (hS.isFredholm_comp hT) (hP.of_projLE hPS) h)) =
      gammaProj hT hR ((gammaProj hT hS).symm h) := by
  have h12S := (proposition_6_4_11 hT hP hS hPS).2.2
  have h12R := (proposition_6_4_11 hT hP hR hPR).2.2
  refine (LinearEquiv.symm_apply_eq _).2 ?_
  apply (linDetEquivOfEq (congrArg (fun A : E →L[ℝ] F => (A : E →ₗ[ℝ] F))
    (comp_comp_eq_of_projLE (T := T) hPR))).injective
  refine (linDetEquivOfEq_trans _ _ _).trans ?_
  refine Eq.trans ?_ (h12R _).symm
  refine Eq.trans ?_ (h12S ((gammaProj hT hS).symm h))
  exact congrArg (fun x => linDetEquivOfEq (congrArg (fun A : E →L[ℝ] F => (A : E →ₗ[ℝ] F))
    (comp_comp_eq_of_projLE (T := T) hPS)) (gammaProj (hS.isFredholm_comp hT) (hP.of_projLE hPS) x))
    (LinearEquiv.apply_symm_apply _ h).symm

end Polyfold
