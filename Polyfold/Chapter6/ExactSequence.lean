import Polyfold.Chapter6.DetLine
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.2,
pp. 205–207, and Appendix 6.7.1, pp. 234–235: the isomorphism `Φ_E` of a four-term exact
sequence, **Lemma 6.5** (it does not depend on the choices) and **Proposition 6.6** (the
isomorphism `Ψ_E`) *(book 2017: Lemma 6.1, Proposition 6.3; see `BookConcordance.md`)*.

# The isomorphism of a four-term exact sequence

## The text, paraphrased

For an exact sequence `E : 0 → A →α B →β C →γ D → 0` of finite-dimensional spaces, write
`B = α(A) ⊕ Z` and `C = β(B) ⊕ V`; then `α : A → α(A)`, `β : Z → β(B)` and `γ : V → D` are
isomorphisms.  With `n = dim A`, `m = dim B`, `l = dim D`, a basis `a₁, …, aₙ` of `A`, a basis
`d₁, …, d_l` of `D`, the basis `c₁, …, c_l` of `V` with `γ(cᵢ) = dᵢ`, a basis `b'₁, …, b'_{m−n}` of
`Z` and `c'ᵢ = β(b'ᵢ)`, the isomorphism `Φ_E : λ(A) ⊗ λ*(D) → λ(B) ⊗ λ*(C)` is (91)

  `Φ_E((a₁ ∧ … ∧ aₙ) ⊗ (d₁ ∧ … ∧ d_l)*) =
     (α(a₁) ∧ … ∧ α(aₙ) ∧ b'₁ ∧ … ∧ b'_{m−n}) ⊗ (c₁ ∧ … ∧ c_l ∧ c'₁ ∧ … ∧ c'_{m−n})*`,

with the two conventions that the `b'` are listed after the `α(a)` and the `c'` after the `c`.
(Lemma 6.5) With these conventions `Φ_E` does not depend on the choices (proof in §6.7.1).
`Ψ_E : λ(C) ⊗ λ(A) ⊗ λ*(D) → λ(B)` maps `c ⊗ a ⊗ d*` to `ῑ(c ⊗ Φ_E(a ⊗ d*))`, where
`ῑ : λ(C) ⊗ λ(B) ⊗ λ*(C) → λ(B)` is `v ⊗ b ⊗ v* ↦ b`.  (Proposition 6.6) With the notation of
(91), `Ψ_E((c₁ ∧ … ∧ c_l ∧ c'₁ ∧ … ∧ c'_{m−n}) ⊗ a ⊗ d*) = α(a₁) ∧ … ∧ α(aₙ) ∧ b'₁ ∧ … ∧ b'_{m−n}`.

## What is formalized

* `Polyfold.FourTermExact A B C D`: the maps `α, β, γ` with `α` injective, `im α = ker β`,
  `im β = ker γ`, `γ` surjective.
* `Polyfold.FourTermExact.Choice`: the choices of the text (complements `Z`, `V`, bases `a`, `d`,
  `b'` and the `γ`-preimages `c ∈ V` of the `d`), and `Choice.value`, the right-hand side of (91).
* `Polyfold.FourTermExact.phi` (`Φ_E`): defined by (91) for one choice (the canonical one,
  `canonicalChoice`) on the line `λ(A) ⊗ λ*(D)`.
* **Lemma 6.5** (`lemma_6_5`): formula (91) holds **for every choice**.  `phi_ne_zero`,
  `phiEquiv`: `Φ_E` is an isomorphism of lines.
* `Polyfold.contractDual` (`ῑ`, `v ⊗ b ⊗ φ ↦ φ(v) b`, so `v ⊗ b ⊗ v* ↦ b`),
  `Polyfold.FourTermExact.psi` (`Ψ_E`) and **Proposition 6.6** (`proposition_6_6`).

## Reading

The text's "the definition does not depend on the choices" is stated as: the linear map
`Φ_E`, defined from one choice, satisfies (91) for all choices.  This is the strongest form and the
one used later (every computation of `γ^P_T` in §6.3 and §6.7.2 uses (91) with its own choices).
The proof in §6.7.1 is followed (`Choice.exists_smul_source_value`): a change of the basis `b'`
of `Z` by `σ` multiplies both wedges by `det σ`; a change of the bases of `A` and `D` multiplies by
`det τ / det ε` on both sides; a change of complements adds to the `b'` vectors of `α(A)` and to
the `c` vectors of `β(B)`, which does not change the wedges (Findings, Chapter 6: the step
"independent of the choices of the basis if and only if `det(τ) = det(ε)`" reads as homogeneity).
-/

open Module TensorProduct

noncomputable section

namespace Polyfold

/-- In a tensor product of real vector spaces, `x ⊗ y ≠ 0` for `x ≠ 0` and `y ≠ 0`. -/
theorem tmul_ne_zero_of_ne_zero {M N : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N]
    [Module ℝ N] {x : M} {y : N} (hx : x ≠ 0) (hy : y ≠ 0) : x ⊗ₜ[ℝ] y ≠ 0 := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℝ M, φ x ≠ 0 := by
    by_contra h
    push Not at h
    exact hx ((Module.forall_dual_apply_eq_zero_iff ℝ x).1 h)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Module.Dual ℝ N, ψ y ≠ 0 := by
    by_contra h
    push Not at h
    exact hy ((Module.forall_dual_apply_eq_zero_iff ℝ y).1 h)
  intro h
  have := congrArg (TensorProduct.lift ((LinearMap.mul ℝ ℝ).compl₁₂ φ ψ)) h
  rw [TensorProduct.lift.tmul, map_zero] at this
  exact mul_ne_zero hφ hψ this

variable {A B C D : Type*} [AddCommGroup A] [Module ℝ A] [AddCommGroup B] [Module ℝ B]
  [AddCommGroup C] [Module ℝ C] [AddCommGroup D] [Module ℝ D]

/-- The image `α(a)` of a basis `a` of `A` under an injective map `α : A → B` extends to a basis
`α(a), b` of `B` (by a basis of a complement of `α(A)`). -/
theorem exists_linearIndependent_append [FiniteDimensional ℝ A] [FiniteDimensional ℝ B]
    (α : A →ₗ[ℝ] B) (hα : Function.Injective α) {n : ℕ} {a : Fin n → A}
    (ha : LinearIndependent ℝ a) (hn : n = finrank ℝ A) :
    ∃ (j : ℕ) (b : Fin j → B), LinearIndependent ℝ (Fin.append (α ∘ a) b) ∧
      n + j = finrank ℝ B := by
  obtain ⟨Z, hZ⟩ := Submodule.exists_isCompl (LinearMap.range α)
  have hj : n + finrank ℝ Z = finrank ℝ B := by
    rw [← Submodule.finrank_add_eq_of_isCompl hZ, LinearMap.finrank_range_of_inj hα, hn]
  refine ⟨finrank ℝ Z, Z.subtype ∘ Module.finBasis ℝ Z, ?_, hj⟩
  apply linearIndependent_of_top_le_span_of_card_eq_finrank _ (by simp [hj])
  rw [span_range_append, Set.range_comp, Submodule.span_image,
    ha.span_eq_top_of_card_eq_finrank' (by simp [hn]), Submodule.map_top, Set.range_comp,
    Submodule.span_image, (Module.finBasis ℝ Z).span_eq, Submodule.map_top,
    Submodule.range_subtype]
  exact hZ.sup_eq_top.ge

/-- A **four-term exact sequence** `0 → A →α B →β C →γ D → 0`. -/
structure FourTermExact (A B C D : Type*) [AddCommGroup A] [Module ℝ A] [AddCommGroup B]
    [Module ℝ B] [AddCommGroup C] [Module ℝ C] [AddCommGroup D] [Module ℝ D] where
  /-- The map `A → B`. -/
  α : A →ₗ[ℝ] B
  /-- The map `B → C`. -/
  β : B →ₗ[ℝ] C
  /-- The map `C → D`. -/
  γ : C →ₗ[ℝ] D
  injective_α : Function.Injective α
  range_α : LinearMap.range α = LinearMap.ker β
  range_β : LinearMap.range β = LinearMap.ker γ
  surjective_γ : Function.Surjective γ

namespace FourTermExact

variable (S : FourTermExact A B C D)

/-- `β` restricted to a complement `Z` of `α(A)` is injective. -/
theorem injective_β_restrict {Z : Submodule ℝ B} (hZ : IsCompl (LinearMap.range S.α) Z) :
    Function.Injective (S.β ∘ₗ Z.subtype) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  have hzk : (z : B) ∈ LinearMap.ker S.β := hz
  rw [← S.range_α] at hzk
  have := hZ.disjoint.le_bot ⟨hzk, z.2⟩
  exact Subtype.ext this

/-- `β(Z) = β(B)` for a complement `Z` of `α(A)`. -/
theorem range_β_restrict {Z : Submodule ℝ B} (hZ : IsCompl (LinearMap.range S.α) Z) :
    LinearMap.range (S.β ∘ₗ Z.subtype) = LinearMap.range S.β := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    exact ⟨z, rfl⟩
  · rintro _ ⟨b, rfl⟩
    obtain ⟨x, hx, z, hz, rfl⟩ := Submodule.mem_sup.1 (hZ.sup_eq_top ▸ Submodule.mem_top (x := b))
    have : S.β x = 0 := by
      rw [← LinearMap.mem_ker, ← S.range_α]
      exact hx
    exact ⟨⟨z, hz⟩, by simp [this]⟩

/-- `γ` restricted to a complement `V` of `β(B)` is bijective onto `D`. -/
theorem bijective_γ_restrict {V : Submodule ℝ C} (hV : IsCompl (LinearMap.range S.β) V) :
    Function.Bijective (S.γ ∘ₗ V.subtype) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hvk : (v : C) ∈ LinearMap.ker S.γ := hv
    rw [← S.range_β] at hvk
    exact Subtype.ext (hV.disjoint.le_bot ⟨hvk, v.2⟩)
  · intro d
    obtain ⟨c, rfl⟩ := S.surjective_γ d
    obtain ⟨x, hx, v, hv, rfl⟩ := Submodule.mem_sup.1 (hV.sup_eq_top ▸ Submodule.mem_top (x := c))
    have : S.γ x = 0 := by
      rw [← LinearMap.mem_ker, ← S.range_β]
      exact hx
    exact ⟨⟨v, hv⟩, by simp [this]⟩

/-- **The choices of (91)**: complements `Z` of `α(A)` in `B` and `V` of `β(B)` in `C`, bases
`a` of `A`, `d` of `D`, `b'` of `Z`, and the vectors `c ∈ V` with `γ(c) = d`. -/
structure Choice (S : FourTermExact A B C D) where
  /-- The number of vectors in the basis of `A`. -/
  n : ℕ
  /-- The number of vectors in the basis of `D`. -/
  l : ℕ
  /-- The number of vectors in the basis of `Z` (`m − n` in the text). -/
  j : ℕ
  /-- A complement of `α(A)` in `B`. -/
  Z : Submodule ℝ B
  isCompl_Z : IsCompl (LinearMap.range S.α) Z
  /-- A complement of `β(B)` in `C`. -/
  V : Submodule ℝ C
  isCompl_V : IsCompl (LinearMap.range S.β) V
  /-- A basis `a₁, …, aₙ` of `A`. -/
  a : Basis (Fin n) ℝ A
  /-- A basis `d₁, …, d_l` of `D`. -/
  d : Basis (Fin l) ℝ D
  /-- A basis `b'₁, …, b'_{m−n}` of `Z`. -/
  b' : Basis (Fin j) ℝ Z
  /-- The basis `c₁, …, c_l` of `V` with `γ(cᵢ) = dᵢ`. -/
  c : Fin l → C
  c_mem : ∀ i, c i ∈ V
  γ_c : ∀ i, S.γ (c i) = d i

namespace Choice

variable {S} (χ : S.Choice)

theorem n_eq [FiniteDimensional ℝ A] : χ.n = finrank ℝ A := by
  rw [finrank_eq_card_basis χ.a, Fintype.card_fin]

theorem l_eq [FiniteDimensional ℝ D] : χ.l = finrank ℝ D := by
  rw [finrank_eq_card_basis χ.d, Fintype.card_fin]

/-- `n + (m − n) = m`. -/
theorem hB [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] : χ.n + χ.j = finrank ℝ B := by
  rw [← Submodule.finrank_add_eq_of_isCompl χ.isCompl_Z, LinearMap.finrank_range_of_inj
    S.injective_α, χ.n_eq, finrank_eq_card_basis χ.b', Fintype.card_fin]

/-- `l + (m − n) = dim C`. -/
theorem hC [FiniteDimensional ℝ C] [FiniteDimensional ℝ D] : χ.l + χ.j = finrank ℝ C := by
  rw [← Submodule.finrank_add_eq_of_isCompl χ.isCompl_V, add_comm, χ.l_eq,
    ← LinearEquiv.finrank_eq (LinearEquiv.ofBijective _ (S.bijective_γ_restrict χ.isCompl_V)),
    ← S.range_β_restrict χ.isCompl_Z, LinearMap.finrank_range_of_inj
    (S.injective_β_restrict χ.isCompl_Z), finrank_eq_card_basis χ.b', Fintype.card_fin]

variable [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] [FiniteDimensional ℝ C]
  [FiniteDimensional ℝ D]

/-- The `B`-side of (91): `α(a₁) ∧ … ∧ α(aₙ) ∧ b'₁ ∧ … ∧ b'_{m−n}` (the `b'` after the `α(a)`). -/
def wedgeB : maxPow B :=
  wedge (Fin.append (S.α ∘ χ.a) (χ.Z.subtype ∘ χ.b')) χ.hB

/-- The `C`-side of (91): `c₁ ∧ … ∧ c_l ∧ c'₁ ∧ … ∧ c'_{m−n}`, `c'ᵢ = β(b'ᵢ)` (the `c'` after
the `c`). -/
def wedgeC : maxPow C :=
  wedge (Fin.append χ.c (S.β ∘ χ.Z.subtype ∘ χ.b')) χ.hC

/-- The vector `(a₁ ∧ … ∧ aₙ) ⊗ (d₁ ∧ … ∧ d_l)*` of `λ(A) ⊗ λ*(D)`. -/
def source : maxPow A ⊗[ℝ] maxPowDual D :=
  wedge χ.a χ.n_eq ⊗ₜ dualVec (wedge χ.d χ.l_eq)

/-- The right-hand side of (91). -/
def value : maxPow B ⊗[ℝ] maxPowDual C :=
  χ.wedgeB ⊗ₜ dualVec χ.wedgeC

set_option linter.unusedSectionVars false in
/-- `α(a₁), …, α(aₙ), b'₁, …, b'_{m−n}` is a basis of `B`: its wedge is not zero. -/
theorem wedgeB_ne_zero : χ.wedgeB ≠ 0 := by
  apply wedge_ne_zero_of_span_eq_top
  rw [span_range_append, Set.range_comp, Submodule.span_image, χ.a.span_eq, Submodule.map_top,
    Set.range_comp, Submodule.span_image, χ.b'.span_eq, Submodule.map_top, Submodule.range_subtype]
  exact χ.isCompl_Z.sup_eq_top.ge

omit [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] [FiniteDimensional ℝ C]
  [FiniteDimensional ℝ D] in
/-- The `β(b')` span `β(B) = ker γ`. -/
theorem span_β_b' :
    Submodule.span ℝ (Set.range (S.β ∘ χ.Z.subtype ∘ χ.b')) = LinearMap.ker S.γ := by
  have : (S.β ∘ χ.Z.subtype ∘ χ.b') = ⇑(S.β ∘ₗ χ.Z.subtype) ∘ ⇑χ.b' := rfl
  rw [this, Set.range_comp, Submodule.span_image, χ.b'.span_eq, Submodule.map_top,
    S.range_β_restrict χ.isCompl_Z, S.range_β]

set_option linter.unusedSectionVars false in
/-- `c₁, …, c_l, β(b'₁), …, β(b'_{m−n})` is a basis of `C`: its wedge is not zero. -/
theorem wedgeC_ne_zero : χ.wedgeC ≠ 0 := by
  apply wedge_ne_zero_of_span_eq_top
  rw [span_range_append, χ.span_β_b']
  intro x _
  set y : C := ∑ i, χ.d.repr (S.γ x) i • χ.c i
  have hy : y ∈ Submodule.span ℝ (Set.range χ.c) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hxy : x - y ∈ LinearMap.ker S.γ := by
    rw [LinearMap.mem_ker, map_sub, map_sum]
    simp only [map_smul, χ.γ_c]
    rw [χ.d.sum_repr, sub_self]
  exact Submodule.mem_sup.2 ⟨y, hy, x - y, hxy, by abel⟩

set_option linter.unusedSectionVars false in
/-- The source vector of a choice is not zero. -/
theorem source_ne_zero : χ.source ≠ 0 :=
  tmul_ne_zero_of_ne_zero (wedge_basis_ne_zero' χ.a χ.n_eq)
    (dualVec_ne_zero finrank_maxPow (wedge_basis_ne_zero' χ.d χ.l_eq))

/-- The value of a choice is not zero. -/
theorem value_ne_zero : χ.value ≠ 0 :=
  tmul_ne_zero_of_ne_zero χ.wedgeB_ne_zero (dualVec_ne_zero finrank_maxPow χ.wedgeC_ne_zero)

omit [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] [FiniteDimensional ℝ C]
  [FiniteDimensional ℝ D] in
/-- `c = s ∘ d` for the section `s = (γ|_V)⁻¹ : D → V ⊆ C`. -/
theorem c_eq_section (i : Fin χ.l) :
    χ.c i = (χ.V.subtype ∘ₗ (LinearEquiv.ofBijective _
      (S.bijective_γ_restrict χ.isCompl_V)).symm.toLinearMap) (χ.d i) := by
  have : (LinearEquiv.ofBijective _ (S.bijective_γ_restrict χ.isCompl_V)).symm (χ.d i) =
      ⟨χ.c i, χ.c_mem i⟩ := by
    rw [LinearEquiv.symm_apply_eq]
    exact (χ.γ_c i).symm
  simp [this]

/-- **The heart of Lemma 6.5** (Appendix 6.7.1): for two choices `χ`, `χ'` there is `r ≠ 0`
with `source χ' = r • source χ` and `value χ' = r • value χ`; here `r = det τ / det ε` for the
changes of bases `τ` of `A` and `ε` of `D`, and the change of complements and of `b'` multiplies
both wedges of the value by the same `det σ`. -/
theorem exists_smul_source_value (χ' : S.Choice) :
    ∃ r : ℝ, r ≠ 0 ∧ χ'.source = r • χ.source ∧ χ'.value = r • χ.value := by
  have hn : χ'.n = χ.n := by rw [χ.n_eq, χ'.n_eq]
  have hl : χ'.l = χ.l := by rw [χ.l_eq, χ'.l_eq]
  have hj : χ'.j = χ.j := by have := χ.hB; have := χ'.hB; omega
  have hB' := χ'.wedgeB_ne_zero
  have hwC := χ.wedgeC_ne_zero
  have hsec := χ.c_eq_section
  have hspan := χ.span_β_b'
  have hBk := χ.hB
  have hBk' := χ'.hB
  have hCk := χ.hC
  have hCk' := χ'.hC
  obtain ⟨n, l, j, Z, hZ, V, hV, a, d, b, c, hc, hγc⟩ := χ
  obtain ⟨n', l', j', Z', hZ', V', hV', a', d', b', c', hc', hγc'⟩ := χ'
  dsimp only at hn hl hj hBk hBk' hCk hCk'
  subst hn hl hj
  simp only [Choice.source, Choice.value, Choice.wedgeB, Choice.wedgeC] at hB' hwC hsec hspan ⊢
  set τ := a.det a'
  set ε := d.det d'
  have hτ : τ ≠ 0 := (a.isUnit_det a').ne_zero
  have hε : ε ≠ 0 := (d.isUnit_det d').ne_zero
  -- the projection `p : B → Z` along `α(A)` and the vectors `p(b')`
  set pZ := Z.projectionOnto (LinearMap.range S.α) hZ.symm
  have hpZ : ∀ x : B, x - (pZ x : B) ∈ LinearMap.range S.α := fun x =>
    (Submodule.projectionOnto_apply_eq_zero_iff hZ.symm).1 (by
      rw [map_sub, Submodule.projectionOnto_apply_left, sub_self])
  set bz := fun i => pZ (Z'.subtype (b' i)) with hbz
  set σ := b.det bz
  have hspanA : Submodule.span ℝ (Set.range (S.α ∘ a')) = LinearMap.range S.α := by
    rw [Set.range_comp, Submodule.span_image, a'.span_eq, Submodule.map_top]
  -- the `B`-side: `wedgeB χ' = det σ · det τ · wedgeB χ`
  have hBeq : wedge (Fin.append (S.α ∘ a') (Z'.subtype ∘ b')) hBk' =
      σ • τ • wedge (Fin.append (S.α ∘ a) (Z.subtype ∘ b)) hBk := by
    have e1 : Z'.subtype ∘ b' = Z.subtype ∘ bz + fun i => Z'.subtype (b' i) - Z.subtype (bz i) := by
      funext i
      simp
    rw [e1, wedge_append_add_right _ _ _ (fun i => hspanA ▸ hpZ _),
      wedge_append_basis_right Z.subtype _ b bz, wedge_append_basis_left S.α a a']
  have hσ : σ ≠ 0 := by
    intro h0
    rw [hBeq, h0, zero_smul] at hB'
    exact hB' rfl
  -- the `C`-side: `wedgeC χ' = det σ · det ε · wedgeC χ`
  set e := LinearEquiv.ofBijective _ (S.bijective_γ_restrict hV)
  set sec : D →ₗ[ℝ] C := V.subtype ∘ₗ e.symm.toLinearMap
  have hγsec : ∀ x, S.γ (sec x) = x := fun x => e.apply_symm_apply x
  have hCeq : wedge (Fin.append c' (S.β ∘ Z'.subtype ∘ b')) hCk' =
      σ • ε • wedge (Fin.append c (S.β ∘ Z.subtype ∘ b)) hCk := by
    have e2 : ⇑S.β ∘ ⇑Z'.subtype ∘ ⇑b' = ⇑(S.β ∘ₗ Z.subtype) ∘ bz := by
      funext i
      have h1 : (b' i : B) - (pZ (b' i) : B) ∈ LinearMap.ker S.β := S.range_α ▸ hpZ _
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h1
      simpa [hbz] using h1
    have e3 : c' = ⇑sec ∘ ⇑d' + fun i => c' i - sec (d' i) := by
      funext i
      simp
    have hy : ∀ i, c' i - sec (d' i) ∈
        Submodule.span ℝ (Set.range (⇑(S.β ∘ₗ Z.subtype) ∘ ⇑b)) := by
      intro i
      change _ ∈ Submodule.span ℝ (Set.range (S.β ∘ Z.subtype ∘ b))
      rw [hspan, LinearMap.mem_ker, map_sub, hγsec, hγc', sub_self]
    have e4 : ⇑sec ∘ ⇑d = c := funext fun i => (hsec i).symm
    rw [e2, wedge_append_basis_right (S.β ∘ₗ Z.subtype) c' b bz, e3,
      wedge_append_add_left _ _ _ hy, wedge_append_basis_left sec d d', e4]
    rfl
  refine ⟨τ * ε⁻¹, mul_ne_zero hτ (inv_ne_zero hε), ?_, ?_⟩
  · rw [wedge_eq_det_smul' a a', wedge_eq_det_smul' d d',
      dualVec_smul finrank_maxPow (wedge_basis_ne_zero' d _) hε, ← TensorProduct.smul_tmul',
      TensorProduct.tmul_smul, smul_smul]
  · rw [hBeq, hCeq, smul_smul, smul_smul,
      dualVec_smul finrank_maxPow hwC (mul_ne_zero hσ hε), ← TensorProduct.smul_tmul',
      TensorProduct.tmul_smul, smul_smul]
    congr 1
    field_simp

end Choice

variable [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] [FiniteDimensional ℝ C]
  [FiniteDimensional ℝ D]

/-- The canonical choice: `Module.finBasis` for the bases, complements given by
`Submodule.exists_isCompl`, and `c = (γ|_V)⁻¹(d)`. -/
def canonicalChoice : S.Choice :=
  let Z := (Submodule.exists_isCompl (LinearMap.range S.α)).choose
  let hZ := (Submodule.exists_isCompl (LinearMap.range S.α)).choose_spec
  let V := (Submodule.exists_isCompl (LinearMap.range S.β)).choose
  let hV := (Submodule.exists_isCompl (LinearMap.range S.β)).choose_spec
  let e := LinearEquiv.ofBijective _ (S.bijective_γ_restrict hV)
  { n := finrank ℝ A, l := finrank ℝ D, j := finrank ℝ Z, Z := Z, isCompl_Z := hZ, V := V,
    isCompl_V := hV, a := Module.finBasis ℝ A, d := Module.finBasis ℝ D,
    b' := Module.finBasis ℝ Z, c := fun i => (e.symm (Module.finBasis ℝ D i) : C),
    c_mem := fun i => (e.symm (Module.finBasis ℝ D i)).2,
    γ_c := fun i => e.apply_symm_apply (Module.finBasis ℝ D i) }

/-- `λ(A) ⊗ λ*(D)` is a line. -/
theorem finrank_source : finrank ℝ (maxPow A ⊗[ℝ] maxPowDual D) = 1 := by
  rw [Module.finrank_tensorProduct, finrank_maxPow, finrank_maxPowDual]

/-- `λ(B) ⊗ λ*(C)` is a line. -/
theorem finrank_target : finrank ℝ (maxPow B ⊗[ℝ] maxPowDual C) = 1 := by
  rw [Module.finrank_tensorProduct, finrank_maxPow, finrank_maxPowDual]

include S in
/-- `dim A + dim C = dim B + dim D` for a four-term exact sequence. -/
theorem finrank_add : finrank ℝ A + finrank ℝ C = finrank ℝ B + finrank ℝ D := by
  have h1 := S.canonicalChoice.hB
  have h2 := S.canonicalChoice.hC
  have h3 := S.canonicalChoice.n_eq
  have h4 := S.canonicalChoice.l_eq
  omega

include S in
/-- `l + j = dim C` when `n = dim A`, `l = dim D` and `n + j = dim B`. -/
theorem finrank_eq_of_families {n l j : ℕ} (hn : n = finrank ℝ A) (hl : l = finrank ℝ D)
    (hj : n + j = finrank ℝ B) : l + j = finrank ℝ C := by
  have := S.finrank_add
  omega

/-- **`Φ_E : λ(A) ⊗ λ*(D) → λ(B) ⊗ λ*(C)`**, defined by (91) for the canonical choice: the
linear map of the line `λ(A) ⊗ λ*(D)` sending the source vector of that choice to its value. -/
def phi : maxPow A ⊗[ℝ] maxPowDual D →ₗ[ℝ] maxPow B ⊗[ℝ] maxPowDual C :=
  LinearMap.smulRight (dualVec S.canonicalChoice.source) S.canonicalChoice.value

/-- **Lemma 6.5**: with the two conventions of (91), **the definition of `Φ_E` does not depend on
the choices**: for every choice of complements `Z`, `V` and of bases `a`, `d`, `b'` (and `c ∈ V`
with `γ(c) = d`),
`Φ_E((a₁ ∧ … ∧ aₙ) ⊗ (d₁ ∧ … ∧ d_l)*) =
  (α(a₁) ∧ … ∧ α(aₙ) ∧ b'₁ ∧ … ∧ b'_{m−n}) ⊗ (c₁ ∧ … ∧ c_l ∧ β(b'₁) ∧ … ∧ β(b'_{m−n}))*`. -/
theorem lemma_6_5 (χ : S.Choice) : S.phi χ.source = χ.value := by
  obtain ⟨r, -, hs, hv⟩ := S.canonicalChoice.exists_smul_source_value χ
  rw [phi, LinearMap.smulRight_apply, hs, hv, map_smul,
    dualVec_self FourTermExact.finrank_source S.canonicalChoice.source_ne_zero, smul_eq_mul,
    mul_one]

/-- `Φ_E` is not zero. -/
theorem phi_ne_zero : S.phi ≠ 0 := by
  intro h
  have := S.lemma_6_5 S.canonicalChoice
  rw [h, LinearMap.zero_apply] at this
  exact S.canonicalChoice.value_ne_zero this.symm

/-- `Φ_E` is bijective (a nonzero map of lines). -/
theorem phi_bijective : Function.Bijective S.phi := by
  have h0 := S.canonicalChoice.source_ne_zero
  have v0 := S.canonicalChoice.value_ne_zero
  have hphi : ∀ t : ℝ, S.phi (t • S.canonicalChoice.source) = t • S.canonicalChoice.value := by
    intro t
    rw [phi, LinearMap.smulRight_apply, map_smul, dualVec_self FourTermExact.finrank_source h0,
      smul_eq_mul, mul_one]
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨t, rfl⟩ := exists_smul_eq_of_finrank_eq_one FourTermExact.finrank_source h0 x
    rw [hphi] at hx
    rw [(smul_eq_zero.1 hx).resolve_right v0, zero_smul]
  · intro y
    obtain ⟨t, rfl⟩ := exists_smul_eq_of_finrank_eq_one FourTermExact.finrank_target v0 y
    exact ⟨_, hphi t⟩

/-- **`Φ_E` as an isomorphism of lines.** -/
def phiEquiv : (maxPow A ⊗[ℝ] maxPowDual D) ≃ₗ[ℝ] (maxPow B ⊗[ℝ] maxPowDual C) :=
  LinearEquiv.ofBijective S.phi S.phi_bijective

@[simp] theorem coe_phiEquiv : ⇑S.phiEquiv = ⇑S.phi := rfl

/-! ### Choices given by families of vectors -/

omit [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] [FiniteDimensional ℝ C] in
/-- If `γ ∘ c` is a basis of `D`, the span of `c` is a complement of `β(B)`. -/
theorem isCompl_span_of_lift {l : ℕ} {d : Fin l → D} (hd : LinearIndependent ℝ d)
    (hl : l = finrank ℝ D) {c : Fin l → C} (hc : ∀ i, S.γ (c i) = d i) :
    IsCompl (LinearMap.range S.β) (Submodule.span ℝ (Set.range c)) := by
  have hdspan := hd.span_eq_top_of_card_eq_finrank' (by simp [hl])
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hxc
    obtain ⟨r, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hxc
    rw [S.range_β, LinearMap.mem_ker, map_sum] at hx
    simp only [map_smul, hc] at hx
    have := Fintype.linearIndependent_iff.1 hd r hx
    simp [this]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hγx : S.γ x ∈ Submodule.span ℝ (Set.range d) := hdspan ▸ Submodule.mem_top
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hγx
    set y : C := ∑ i, r i • c i
    have hy : y ∈ Submodule.span ℝ (Set.range c) :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hxy : x - y ∈ LinearMap.range S.β := by
      rw [S.range_β, LinearMap.mem_ker, map_sub, map_sum]
      simp only [map_smul, hc]
      rw [hr, sub_self]
    exact Submodule.mem_sup.2 ⟨x - y, hxy, y, hy, by abel⟩

/-- **A choice given by families of vectors**: `Z = span b` and `V = span c`, for linearly
independent `a`, `d` of lengths `dim A`, `dim D`, vectors `b` completing `α(a)` to a basis of `B`,
and `c` with `γ ∘ c = d` (the form in which the text makes its choices in §6.3 and §6.7.2). -/
def Choice.ofFamilies {n l j : ℕ} {a : Fin n → A} (ha : LinearIndependent ℝ a)
    (hn : n = finrank ℝ A) {d : Fin l → D} (hd : LinearIndependent ℝ d) (hl : l = finrank ℝ D)
    {b : Fin j → B} (hb : LinearIndependent ℝ (Fin.append (S.α ∘ a) b))
    (hj : n + j = finrank ℝ B) {c : Fin l → C} (hc : ∀ i, S.γ (c i) = d i) : S.Choice where
  n := n
  l := l
  j := j
  Z := Submodule.span ℝ (Set.range b)
  isCompl_Z := by
    have := isCompl_span_of_append hb hj
    rwa [Set.range_comp, Submodule.span_image, ha.span_eq_top_of_card_eq_finrank' (by simp [hn]),
      Submodule.map_top] at this
  V := Submodule.span ℝ (Set.range c)
  isCompl_V := S.isCompl_span_of_lift hd hl hc
  a := basisOfLinearIndependentOfCardEqFinrank' a ha (by simp [hn])
  d := basisOfLinearIndependentOfCardEqFinrank' d hd (by simp [hl])
  b' := Basis.span (linearIndependent_of_append_right hb)
  c := c
  c_mem i := Submodule.subset_span ⟨i, rfl⟩
  γ_c i := by simp [hc]

section OfFamilies

variable {S} {n l j : ℕ} {a : Fin n → A} (ha : LinearIndependent ℝ a) (hn : n = finrank ℝ A)
  {d : Fin l → D} (hd : LinearIndependent ℝ d) (hl : l = finrank ℝ D) {b : Fin j → B}
  (hb : LinearIndependent ℝ (Fin.append (S.α ∘ a) b)) (hj : n + j = finrank ℝ B) {c : Fin l → C}
  (hc : ∀ i, S.γ (c i) = d i)

omit [FiniteDimensional ℝ C] in
/-- The source vector of `Choice.ofFamilies` is `(a₁ ∧ … ∧ aₙ) ⊗ (d₁ ∧ … ∧ d_l)*`. -/
theorem Choice.ofFamilies_source :
    (Choice.ofFamilies S ha hn hd hl hb hj hc).source = wedge a hn ⊗ₜ dualVec (wedge d hl) := by
  change wedge (⇑(basisOfLinearIndependentOfCardEqFinrank' a ha (by simp [hn]))) hn ⊗ₜ
    dualVec (wedge (⇑(basisOfLinearIndependentOfCardEqFinrank' d hd (by simp [hl]))) hl) = _
  rw [coe_basisOfLinearIndependentOfCardEqFinrank', coe_basisOfLinearIndependentOfCardEqFinrank']

omit [FiniteDimensional ℝ C] in
/-- The `B`-wedge of `Choice.ofFamilies` is `α(a) ∧ b`. -/
theorem Choice.ofFamilies_wedgeB :
    (Choice.ofFamilies S ha hn hd hl hb hj hc).wedgeB = wedge (Fin.append (S.α ∘ a) b) hj := by
  have : (Submodule.span ℝ (Set.range b)).subtype ∘
      ⇑(Basis.span (linearIndependent_of_append_right hb)) = b := by
    funext i
    simp [Basis.span_apply]
  change wedge (Fin.append (S.α ∘ ⇑(basisOfLinearIndependentOfCardEqFinrank' a ha (by simp [hn])))
    ((Submodule.span ℝ (Set.range b)).subtype ∘
      ⇑(Basis.span (linearIndependent_of_append_right hb)))) hj = _
  rw [coe_basisOfLinearIndependentOfCardEqFinrank', this]

/-- The `C`-wedge of `Choice.ofFamilies` is `c ∧ β(b)`. -/
theorem Choice.ofFamilies_wedgeC (hC : l + j = finrank ℝ C) :
    (Choice.ofFamilies S ha hn hd hl hb hj hc).wedgeC = wedge (Fin.append c (S.β ∘ b)) hC := by
  have : (Submodule.span ℝ (Set.range b)).subtype ∘
      ⇑(Basis.span (linearIndependent_of_append_right hb)) = b := by
    funext i
    simp [Basis.span_apply]
  change wedge (Fin.append c (S.β ∘ (Submodule.span ℝ (Set.range b)).subtype ∘
    ⇑(Basis.span (linearIndependent_of_append_right hb)))) hC = _
  rw [this]

include ha hd hb hc in
/-- **Formula (91) for families of vectors**: `Φ_E((a₁ ∧ … ∧ aₙ) ⊗ (d₁ ∧ … ∧ d_l)*) =
(α(a) ∧ b) ⊗ (c ∧ β(b))*` for linearly independent `a`, `d` of lengths `dim A`, `dim D`, vectors `b`
completing `α(a)` to a basis of `B`, and `γ ∘ c = d`. -/
theorem phi_wedge_tmul (hC : l + j = finrank ℝ C) :
    S.phi (wedge a hn ⊗ₜ dualVec (wedge d hl)) =
      wedge (Fin.append (S.α ∘ a) b) hj ⊗ₜ dualVec (wedge (Fin.append c (S.β ∘ b)) hC) := by
  rw [← Choice.ofFamilies_source ha hn hd hl hb hj hc, lemma_6_5, Choice.value,
    Choice.ofFamilies_wedgeB, Choice.ofFamilies_wedgeC _ _ _ _ _ _ _ hC]

include ha hn hd hl hb hj hc in
/-- In the situation of `phi_wedge_tmul`, `c, β(b)` is a basis of `C`. -/
theorem linearIndependent_append_lift (hC : l + j = finrank ℝ C) :
    LinearIndependent ℝ (Fin.append c (S.β ∘ b)) := by
  rw [← wedge_ne_zero_iff hC, ← Choice.ofFamilies_wedgeC ha hn hd hl hb hj hc hC]
  exact Choice.wedgeC_ne_zero _

end OfFamilies

end FourTermExact

/-! ### Proposition 6.6: `Ψ_E` -/

variable (B C) in
/-- `ῑ : λ(C) ⊗ λ(B) ⊗ λ*(C) → λ(B)`, `v ⊗ b ⊗ φ ↦ φ(v) b`; in particular `v ⊗ b ⊗ v* ↦ b`. -/
def contractDual : maxPow C ⊗[ℝ] (maxPow B ⊗[ℝ] maxPowDual C) →ₗ[ℝ] maxPow B :=
  TensorProduct.lift
    (TensorProduct.uncurry (RingHom.id ℝ) _ _ _ ∘ₗ LinearMap.smulRightₗ ∘ₗ LinearMap.applyₗ)

@[simp] theorem contractDual_tmul (v : maxPow C) (b : maxPow B) (φ : maxPowDual C) :
    contractDual B C (v ⊗ₜ (b ⊗ₜ φ)) = φ v • b := rfl

/-- `ῑ(v ⊗ b ⊗ v*) = b` for `v ≠ 0`. -/
theorem contractDual_tmul_dualVec [FiniteDimensional ℝ C] {v : maxPow C} (hv : v ≠ 0)
    (b : maxPow B) : contractDual B C (v ⊗ₜ (b ⊗ₜ dualVec v)) = b := by
  rw [contractDual_tmul, dualVec_self finrank_maxPow hv, one_smul]

namespace FourTermExact

variable (S : FourTermExact A B C D) [FiniteDimensional ℝ A] [FiniteDimensional ℝ B]
  [FiniteDimensional ℝ C] [FiniteDimensional ℝ D]

/-- **`Ψ_E : λ(C) ⊗ λ(A) ⊗ λ*(D) → λ(B)`** (92): `c ⊗ a ⊗ d* ↦ ῑ(c ⊗ Φ_E(a ⊗ d*))`. -/
def psi : maxPow C ⊗[ℝ] (maxPow A ⊗[ℝ] maxPowDual D) →ₗ[ℝ] maxPow B :=
  contractDual B C ∘ₗ LinearMap.lTensor _ S.phi

/-- **Proposition 6.6**: in the notation of (91),
`Ψ_E((c₁ ∧ … ∧ c_l ∧ c'₁ ∧ … ∧ c'_{m−n}) ⊗ a ⊗ d*) = α(a₁) ∧ … ∧ α(aₙ) ∧ b'₁ ∧ … ∧ b'_{m−n}`,
for every choice. -/
theorem proposition_6_6 (χ : S.Choice) : S.psi (χ.wedgeC ⊗ₜ χ.source) = χ.wedgeB := by
  rw [psi, LinearMap.comp_apply, LinearMap.lTensor_tmul, S.lemma_6_5 χ, Choice.value,
    contractDual_tmul_dualVec χ.wedgeC_ne_zero]

end FourTermExact

end Polyfold
