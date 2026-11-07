import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_63

/-! Round trip for V6_63 (§6.7.1, the proof of Lemma 6.5).

A is `FourTermExact.Choice.exists_smul_source_value`: for two choices `χ, χ'` of the data of (91)
there is `r ≠ 0` with `source χ' = r • source χ` and `value χ' = r • value χ`.  B is the blind
author's three computations of §6.7.1 for explicit families.

* `A ⇒ B`: (1), (3) and the source half of (2) are direct wedge algebra (`wedge_comp_basis`,
  `wedge_append_basis_right` through `Pi.basisFun`, `wedge_append_add_left/right`, projection onto
  `Z₂` along `α(A)`); the value half of (2) and its "iff" use A for the choices
  `(Z, V, a, d, b', c)` and `(Z, V, a', d', b', c')` (the factor `r` is identified with
  `det τ / det ε` from the source side).
* `B ⇒ A`: the text's chain χ → (Z', V', a, d, b₂, c₂) → (Z', V', a', d', b₂, c') → χ' with B (3)
  (which supplies `b₂`), B (2) (`τ`, `ε` the matrices of `a'`, `d'` in `a`, `d`) and B (1) (`σ` the
  matrix of `b'` in `b₂`); `r = det τ / det ε`.
-/

namespace RoundTrip.V6_63
open Polyfold Module TensorProduct

set_option linter.unusedSimpArgs false

/-- The project's statement, universes instantiated at `0`. -/
def A : Prop := type_of% @Polyfold.FourTermExact.Choice.exists_smul_source_value.{0, 0, 0, 0}

theorem A_holds : A := @Polyfold.FourTermExact.Choice.exists_smul_source_value.{0, 0, 0, 0}

section Aux

variable {E : Type} [AddCommGroup E] [Module ℝ E]

/-- The wedge of the rows of `σ` times a family: `det σ` times the wedge of the family. -/
theorem wedge_matrix {p : ℕ} (u : Fin p → E) (σ : Matrix (Fin p) (Fin p) ℝ)
    (hk : p = finrank ℝ E) :
    wedge (fun i => ∑ k, σ i k • u k) hk = σ.det • wedge u hk := by
  have h1 : (fun i => ∑ k, σ i k • u k) = ⇑(Fintype.linearCombination ℝ u) ∘ fun i => σ i := by
    funext i
    simp [Fintype.linearCombination_apply]
  have h2 : u = ⇑(Fintype.linearCombination ℝ u) ∘ ⇑(Pi.basisFun ℝ (Fin p)) := by
    funext i
    simp [Fintype.linearCombination_apply]
  rw [h1, wedge_comp_basis _ (Pi.basisFun ℝ (Fin p)) _ hk, ← h2, Pi.basisFun_det_apply]
  rfl

/-- The same in the right block of an append. -/
theorem wedge_append_matrix_right {p q : ℕ} (u : Fin p → E) (w : Fin q → E)
    (σ : Matrix (Fin q) (Fin q) ℝ) (hk : p + q = finrank ℝ E) :
    wedge (Fin.append u (fun i => ∑ k, σ i k • w k)) hk = σ.det • wedge (Fin.append u w) hk := by
  have h1 : (fun i => ∑ k, σ i k • w k) = ⇑(Fintype.linearCombination ℝ w) ∘ fun i => σ i := by
    funext i
    simp [Fintype.linearCombination_apply]
  have h2 : w = ⇑(Fintype.linearCombination ℝ w) ∘ ⇑(Pi.basisFun ℝ (Fin q)) := by
    funext i
    simp [Fintype.linearCombination_apply]
  rw [h1, wedge_append_basis_right _ u (Pi.basisFun ℝ (Fin q)) _ hk, ← h2,
    Pi.basisFun_det_apply]
  rfl

theorem smul_div_eq_self_iff {M : Type*} [AddCommGroup M] [Module ℝ M] {x : M} (hx : x ≠ 0)
    {s t : ℝ} (ht : t ≠ 0) : (s / t) • x = x ↔ s = t := by
  constructor
  · intro h
    have h0 : (s / t - 1) • x = 0 := by rw [sub_smul, h, one_smul, sub_self]
    have := (smul_eq_zero.1 h0).resolve_right hx
    rwa [sub_eq_zero, div_eq_one_iff_eq ht] at this
  · rintro rfl
    rw [div_self ht, one_smul]

end Aux

/-- `A ⇒ B`: (1), (3) and the source half of (2) are direct wedge algebra; the value half of (2)
is A applied to the two choices `(Z, V, a, d, b', c)` and `(Z, V, a', d', b', c')`. -/
theorem A_to_B : A → B := by
  intro hA A B C D _ _ _ _ _ _ _ _ _ _ _ _ α β γ hα hαβ hβγ hγ Z V hZ hV n l j a d b' c ha hn hd
    hl _ hbLI hspan hcV hγc hB hC
  let S : FourTermExact A B C D := ⟨α, β, γ, hα, hαβ, hβγ, hγ⟩
  have hwd0 : wedge d hl ≠ 0 := (wedge_ne_zero_iff hl).2 hd
  have hwa0 : wedge a hn ≠ 0 := (wedge_ne_zero_iff hn).2 ha
  -- the basis of `Z` and the choice `χ`
  let aB := basisOfLinearIndependentOfCardEqFinrank' a ha (by simp [hn])
  let dB := basisOfLinearIndependentOfCardEqFinrank' d hd (by simp [hl])
  let bB : Basis (Fin j) ℝ Z := (Basis.span hbLI).map (LinearEquiv.ofEq _ _ hspan)
  have hbB : Z.subtype ∘ ⇑bB = b' := by
    funext i
    simp [bB, Basis.span_apply]
  let χ : S.Choice := ⟨n, l, j, Z, hZ, V, hV, aB, dB, bB, c, hcV, fun i => by
    simp only [dB, coe_basisOfLinearIndependentOfCardEqFinrank']; exact hγc i⟩
  have hχs : χ.source = wedge a hn ⊗ₜ[ℝ] dualVec (wedge d hl) := by
    show wedge ⇑aB _ ⊗ₜ[ℝ] dualVec (wedge ⇑dB _) = _
    simp only [aB, dB, coe_basisOfLinearIndependentOfCardEqFinrank']
  have hχv : χ.value = wedge (Fin.append (α ∘ a) b') hB ⊗ₜ[ℝ]
      dualVec (wedge (Fin.append c (β ∘ b')) hC) := by
    show wedge (Fin.append (α ∘ ⇑aB) (Z.subtype ∘ ⇑bB)) _ ⊗ₜ[ℝ]
      dualVec (wedge (Fin.append c (β ∘ Z.subtype ∘ ⇑bB)) _) = _
    rw [hbB]
    simp only [aB, coe_basisOfLinearIndependentOfCardEqFinrank']
  have hwC0 : wedge (Fin.append c (β ∘ b')) hC ≠ 0 := by
    intro h0
    apply χ.value_ne_zero
    rw [hχv, h0, dualVec]
    simp
  refine ⟨?_, ?_, ?_⟩
  · -- (1) a change of the basis of `Z` by `σ`
    intro σ b''
    have h1 : wedge (Fin.append (α ∘ a) b'') hB = σ.det • wedge (Fin.append (α ∘ a) b') hB :=
      wedge_append_matrix_right _ b' σ hB
    have hβb : β ∘ b'' = fun i => ∑ k, σ i k • (β ∘ b') k := by
      funext i
      simp [b'', map_sum, map_smul]
    have h2 : wedge (Fin.append c (β ∘ b'')) hC = σ.det • wedge (Fin.append c (β ∘ b')) hC := by
      rw [hβb]
      exact wedge_append_matrix_right _ _ σ hC
    refine ⟨h1, h2, fun hσ => ?_⟩
    rw [h1, h2, dualVec_smul finrank_maxPow hwC0 hσ, TensorProduct.tmul_smul,
      ← TensorProduct.smul_tmul', smul_smul, inv_mul_cancel₀ hσ, one_smul]
  · -- (2) a change of the bases of `A` and `D`
    intro τ ε hτ hε c' hc'V hγc' a' d'
    have hwa : wedge a' hn = τ.det • wedge a hn := wedge_matrix a τ hn
    have hwd : wedge d' hl = ε.det • wedge d hl := wedge_matrix d ε hl
    have hsrc : wedge a' hn ⊗ₜ[ℝ] dualVec (wedge d' hl) =
        (τ.det / ε.det) • (wedge a hn ⊗ₜ[ℝ] dualVec (wedge d hl)) := by
      rw [hwa, hwd, dualVec_smul finrank_maxPow hwd0 hε, TensorProduct.tmul_smul,
        ← TensorProduct.smul_tmul', smul_smul]
      congr 1
      ring
    have ha' : LinearIndependent ℝ a' := (wedge_ne_zero_iff hn).1 (by
      rw [hwa]; exact smul_ne_zero hτ hwa0)
    have hd' : LinearIndependent ℝ d' := (wedge_ne_zero_iff hl).1 (by
      rw [hwd]; exact smul_ne_zero hε hwd0)
    let aB' := basisOfLinearIndependentOfCardEqFinrank' a' ha' (by simp [hn])
    let dB' := basisOfLinearIndependentOfCardEqFinrank' d' hd' (by simp [hl])
    let χ' : S.Choice := ⟨n, l, j, Z, hZ, V, hV, aB', dB', bB, c', hc'V, fun i => by
      simp only [dB', coe_basisOfLinearIndependentOfCardEqFinrank']; exact hγc' i⟩
    have hχ's : χ'.source = wedge a' hn ⊗ₜ[ℝ] dualVec (wedge d' hl) := by
      show wedge ⇑aB' _ ⊗ₜ[ℝ] dualVec (wedge ⇑dB' _) = _
      simp only [aB', dB', coe_basisOfLinearIndependentOfCardEqFinrank']
    have hχ'v : χ'.value = wedge (Fin.append (α ∘ a') b') hB ⊗ₜ[ℝ]
        dualVec (wedge (Fin.append c' (β ∘ b')) hC) := by
      show wedge (Fin.append (α ∘ ⇑aB') (Z.subtype ∘ ⇑bB)) _ ⊗ₜ[ℝ]
        dualVec (wedge (Fin.append c' (β ∘ Z.subtype ∘ ⇑bB)) _) = _
      rw [hbB]
      simp only [aB', coe_basisOfLinearIndependentOfCardEqFinrank']
    obtain ⟨r, -, hrs, hrv⟩ := hA χ χ'
    have hr : r = τ.det / ε.det := by
      have h0 := χ.source_ne_zero
      apply smul_left_injective ℝ (M := maxPow A ⊗[ℝ] maxPowDual D) h0
      show r • χ.source = (τ.det / ε.det) • χ.source
      rw [← hrs, hχ's, hsrc, hχs]
    have hval : wedge (Fin.append (α ∘ a') b') hB ⊗ₜ[ℝ]
        dualVec (wedge (Fin.append c' (β ∘ b')) hC) =
        (τ.det / ε.det) • (wedge (Fin.append (α ∘ a) b') hB ⊗ₜ[ℝ]
          dualVec (wedge (Fin.append c (β ∘ b')) hC)) := by
      rw [← hχ'v, hrv, hr, hχv]
    refine ⟨hsrc, hval, ?_, ?_⟩
    · rw [hsrc]
      exact smul_div_eq_self_iff (M := maxPow A ⊗[ℝ] maxPowDual D) (hχs ▸ χ.source_ne_zero) hε
    · rw [hval]
      exact smul_div_eq_self_iff (M := maxPow B ⊗[ℝ] maxPowDual C) (hχv ▸ χ.value_ne_zero) hε
  · -- (3) two choices of complements
    intro Z₂ V₂ hZ₂ hV₂
    have hfZ : finrank ℝ Z = j := by
      rw [← hspan, finrank_span_eq_card hbLI, Fintype.card_fin]
    have hfZ₂ : finrank ℝ Z₂ = j := by
      have h1 := Submodule.finrank_add_eq_of_isCompl hZ
      have h2 := Submodule.finrank_add_eq_of_isCompl hZ₂
      omega
    refine ⟨?_, ?_, ?_⟩
    · let p := Submodule.projectionOnto Z₂ (LinearMap.range α) hZ₂.symm
      have hp : ∀ x : B, x - (p x : B) ∈ LinearMap.range α := fun x =>
        (Submodule.projectionOnto_apply_eq_zero_iff hZ₂.symm).1 (by
          rw [map_sub, Submodule.projectionOnto_apply_left, sub_self])
      have hLI : LinearIndependent ℝ (fun i => (p (b' i) : B)) := by
        have := hbLI.map (f := Z₂.subtype ∘ₗ p) (by
          rw [hspan, LinearMap.ker_comp, Submodule.ker_subtype, Submodule.comap_bot,
            Submodule.ker_projectionOnto]
          exact hZ.symm.disjoint)
        exact this
      refine ⟨fun i => (p (b' i) : B), fun i => (p (b' i)).2, fun i => ?_, hLI, ?_⟩
      · rw [← neg_sub]
        exact neg_mem (hp _)
      · apply Submodule.eq_of_le_of_finrank_eq
        · rw [Submodule.span_le]
          rintro _ ⟨i, rfl⟩
          exact (p (b' i)).2
        · rw [finrank_span_eq_card hLI, Fintype.card_fin, hfZ₂]
    · intro c₂ _ hγc₂ i
      rw [hβγ, LinearMap.mem_ker, map_sub, hγc₂, hγc, sub_self]
    · intro b₂ c₂ hb₂ hc₂
      have hspanA : Submodule.span ℝ (Set.range (α ∘ a)) = LinearMap.range α := by
        rw [Set.range_comp, Submodule.span_image,
          ha.span_eq_top_of_card_eq_finrank' (by simp [hn]), Submodule.map_top]
      have hspanB : Submodule.span ℝ (Set.range (β ∘ b')) = LinearMap.range β := by
        rw [Set.range_comp, Submodule.span_image, hspan, ← Submodule.range_subtype Z,
          ← LinearMap.range_comp]
        exact S.range_β_restrict hZ
      have hβ2 : β ∘ b₂ = β ∘ b' := by
        funext i
        have h := hb₂ i
        rw [hαβ, LinearMap.mem_ker, map_sub, sub_eq_zero] at h
        exact h
      constructor
      · have := wedge_append_add_right (α ∘ a) b' (fun i => b₂ i - b' i)
          (fun i => hspanA ▸ hb₂ i) hB
        rwa [show (b' + fun i => b₂ i - b' i) = b₂ from funext fun i => by simp] at this
      · rw [hβ2]
        have := wedge_append_add_left c (fun i => c₂ i - c i) (β ∘ b')
          (fun i => hspanB ▸ hc₂ i) hC
        rwa [show (c + fun i => c₂ i - c i) = c₂ from funext fun i => by simp] at this

/-- `B ⇒ A`: the proof of the text, with B's three steps: change the complements (B (3), which
also supplies the new basis `b₂` of `Z'`), then the bases of `A` and `D` (B (2), with
`c' = χ'.c`), then the basis of `Z'` (B (1)). -/
theorem B_to_A : B → A := by
  intro hB A B C D _ _ _ _ _ _ _ _ S χ _ _ _ _ χ'
  have hn : χ'.n = χ.n := by rw [χ.n_eq, χ'.n_eq]
  have hl : χ'.l = χ.l := by rw [χ.l_eq, χ'.l_eq]
  have hj : χ'.j = χ.j := by have := χ.hB; have := χ'.hB; omega
  have hBk := χ.hB
  have hCk := χ.hC
  have hn0 := χ.n_eq
  have hl0 := χ.l_eq
  obtain ⟨n, l, j, Z, hZ, V, hV, a, d, b, c, hc, hγc⟩ := χ
  obtain ⟨n', l', j', Z', hZ', V', hV', a', d', b', c', hc', hγc'⟩ := χ'
  dsimp only at hn hl hj hBk hCk hn0 hl0
  subst hn hl hj
  simp only [FourTermExact.Choice.source, FourTermExact.Choice.value, FourTermExact.Choice.wedgeB,
    FourTermExact.Choice.wedgeC]
  have hspanb : Submodule.span ℝ (Set.range (Z.subtype ∘ ⇑b)) = Z := by
    rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  -- B for the first choice: change of complements
  have hB1 := hB S.α S.β S.γ S.injective_α S.range_α S.range_β S.surjective_γ Z V hZ hV
    (⇑a) (⇑d) (Z.subtype ∘ ⇑b) c a.linearIndependent hn0 d.linearIndependent hl0
    (fun i => (b i).2) (b.linearIndependent.map' _ Z.ker_subtype) hspanb hc hγc hBk hCk
  obtain ⟨⟨b₂, hb₂Z, hb₂α, hb₂LI, hb₂span⟩, h3c, h3w⟩ := hB1.2.2 Z' V' hZ' hV'
  choose v hv using fun i => (S.bijective_γ_restrict hV').2 (d i)
  let c₂ := fun i => (v i : C)
  have hγc₂ : ∀ i, S.γ (c₂ i) = d i := hv
  have hw := h3w b₂ c₂ hb₂α (h3c c₂ (fun i => (v i).2) hγc₂)
  -- B for `(Z', V', a, d, b₂, c₂)`: change of the bases of `A` and `D`
  have hB2 := hB S.α S.β S.γ S.injective_α S.range_α S.range_β S.surjective_γ Z' V' hZ' hV'
    (⇑a) (⇑d) b₂ c₂ a.linearIndependent hn0 d.linearIndependent hl0
    hb₂Z hb₂LI hb₂span (fun i => (v i).2) hγc₂ hBk hCk
  let τ : Matrix _ _ ℝ := fun i k => a.repr (a' i) k
  let ε : Matrix _ _ ℝ := fun i k => d.repr (d' i) k
  have hτ : τ.det ≠ 0 := by
    rw [show τ = Matrix.transpose (a.toMatrix ⇑a') from rfl, Matrix.det_transpose, ← Basis.det_apply]
    exact (a.isUnit_det a').ne_zero
  have hε : ε.det ≠ 0 := by
    rw [show ε = Matrix.transpose (d.toMatrix ⇑d') from rfl, Matrix.det_transpose, ← Basis.det_apply]
    exact (d.isUnit_det d').ne_zero
  have ea : (fun i => ∑ k, τ i k • a k) = ⇑a' := funext fun i => a.sum_repr (a' i)
  have ed : (fun i => ∑ k, ε i k • d k) = ⇑d' := funext fun i => d.sum_repr (d' i)
  have hγc'' : ∀ i, S.γ (c' i) = ∑ k, ε i k • d k := fun i => by
    rw [hγc' i]; exact (d.sum_repr (d' i)).symm
  obtain ⟨src2, val2, -, -⟩ := hB2.2.1 τ ε hτ hε c' hc' hγc''
  -- B for `(Z', V', a', d', b₂, c')`: change of the basis of `Z'`
  have hB3 := hB S.α S.β S.γ S.injective_α S.range_α S.range_β S.surjective_γ Z' V' hZ' hV'
    (⇑a') (⇑d') b₂ c' a'.linearIndependent hn0 d'.linearIndependent hl0
    hb₂Z hb₂LI hb₂span hc' hγc' hBk hCk
  let bZ : Basis _ ℝ Z' := (Basis.span hb₂LI).map (LinearEquiv.ofEq _ _ hb₂span)
  have hbZ : ∀ k, (bZ k : B) = b₂ k := fun k => by simp [bZ, Basis.span_apply]
  let σ : Matrix _ _ ℝ := fun i k => bZ.repr (b' i) k
  have hσ : σ.det ≠ 0 := by
    rw [show σ = Matrix.transpose (bZ.toMatrix ⇑b') from rfl, Matrix.det_transpose, ← Basis.det_apply]
    exact (bZ.isUnit_det b').ne_zero
  have eb : (fun i => ∑ k, σ i k • b₂ k) = Z'.subtype ∘ ⇑b' := by
    funext i
    simp only [← hbZ, Function.comp_apply, Submodule.subtype_apply]
    have h := congrArg (fun x : Z' => (x : B)) (bZ.sum_repr (b' i))
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using h
  have e1 := (hB3.1 σ).2.2 hσ
  rw [ea, ed] at src2
  rw [ea, hw.1, hw.2] at val2
  refine ⟨τ.det / ε.det, div_ne_zero hτ hε, src2, ?_⟩
  simp only [eb] at e1
  exact e1.trans val2

#rt_check RoundTrip.V6_63.A_to_B [Polyfold.FourTermExact.Choice.exists_smul_source_value]
#rt_check RoundTrip.V6_63.B_to_A [Polyfold.FourTermExact.Choice.exists_smul_source_value]
#rt_overlap RoundTrip.V6_63.B_to_A [Polyfold.FourTermExact.Choice.exists_smul_source_value]

end RoundTrip.V6_63
