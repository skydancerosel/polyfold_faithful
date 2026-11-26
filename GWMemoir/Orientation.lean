import Polyfold.Chapter6.DetBundle
import Polyfold.Chapter6.DetConventions
import Polyfold.Chapter3.SolutionLinearization
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
Hofer–Wysocki–Zehnder, *Applications of Polyfold Theory I: The Polyfolds of Gromov–Witten Theory*
(Memoirs AMS 248, 2017), Appendix 5.10.1–5.10.2, pp. 172–181: **Definitions 5.8–5.10**,
**Lemmas 5.11–5.15** and **Theorem 5.16**, in the memoir's form (Hilbert spaces, orthogonal
projections), proved from the book's §§6.3–6.5 (2021, pp. 241–252).

# Determinants and the line bundle `DET(E, F)` for Hilbert spaces

## What is formalized

* `memoirDet T = λ(ker T) ⊗ λ(coker(T)*)` (**Definition 5.8**) and
  `memoir_definition_5_8_equiv : memoirDet T ≅ det(T)` (the book's `λ(ker T) ⊗ λ*(coker T)`,
  Definition 6.4.1), by `id ⊗ ι` with `ι` of Definition 6.3.1.
* `memoirPhi S : λ(A) ⊗ λ(D*) ≅ λ(B) ⊗ λ(C*)` (**Definition 5.9**), the book's `Φ_E` of (6.4)
  read through `ι` on both sides; `memoir_definition_5_9`: it is given by the memoir's formula
  `(a) ⊗ (d*) ↦ (α(a) ∧ b) ⊗ (d* ∘ γ ∧ c*)` for **every** choice of `a`, `d*`, `b`, `c*` with
  `det(c*ᵢ(β bⱼ)) = 1`.
* `memoirPsi S : λ(C) ⊗ λ(A) ⊗ λ(D*) → λ(B)` (**Definition 5.10**), defined as the memoir's
  alternative form (pairing after `Id ⊗ Φ`, `memoirPsi_eq_pairing`); `memoir_definition_5_10`: the
  memoir's formula `(c ∧ β(b)) ⊗ (a) ⊗ (d*) ↦ α(a) ∧ b` for every choice with
  `det(d*ᵢ(γ cⱼ)) = 1` and `det(c*ᵢ(β bⱼ)) = 1`.
* **Lemma 5.11** (`memoir_lemma_5_11`): `Φ_E` and `Ψ_E` are isomorphisms; independence of the
  choices is the content of the two formulas above (the maps are defined without choices).
* `memoirPi T` (p. 176): the orthogonal good left-projections, a subset of the book's `Π_T`
  (Definition 6.4.3); `exists_mem_memoirPi`: it is not empty for `T` Fredholm.
* **Lemma 5.12** (`memoir_lemma_5_12`), as printed: the orthogonal projection onto
  `R(P) ∩ R(P')` is a common lower bound in `Π_T`.  With bounded projections (the book's
  Lemma 6.4.9) a projection onto `R(P) ∩ R(P')` below both need not exist
  (`Polyfold.lemma_6_10_text_reading_preprint`); orthogonality is what makes the memoir's `Q` work.
* **Lemma 5.13** (`memoir_lemma_5_13`): the book's Proposition 6.4.10 with the memoir's maps.
* `memoirGammaProj` (`γ^P_T`, p. 177, made from Definition 5.9) and `memoirGammaProj_eq`: it is
  the book's `γ^P_T` under `id ⊗ ι` (naturality of `ι`, Proposition 6.3.2); **Lemma 5.14**
  (`memoir_lemma_5_14`) from Proposition 6.4.11.
* **Lemma 5.15** (`memoir_lemma_5_15`): the charts `L_{T₀,P,ε}` with `P` orthogonal and
  `X = ker(P T₀)^⊥`, which are charts of the book's atlas; **Theorem 5.16**
  (`memoir_theorem_5_16`): `DET(E, F)` is a topological line bundle and the memoir's charts are a
  basis of its topology, so the memoir's structure is the book's (whose atlas allows every
  bounded `P ∈ Π_T`).
* **Lemma 5.37**, abstract part (`memoir_lemma_5_37`): compact perturbations of a Fredholm
  operator form a convex, contractible set of Fredholm operators over which `DET` has exactly two
  orientations.

## Readings

* In Definitions 5.9 and 5.10, "`b₁, …, b_{m−n}` linearly independent and not in the image of
  `α`" is read as: `α(a₁), …, α(aₙ), b₁, …, b_{m−n}` is a basis of `B` (the memoir uses that the
  `β(bᵢ)` are linearly independent; vectors that are each outside `α(A)` need not have this
  property, e.g. `b₂ = b₁ + α(a₁)`).
* The two descriptions of the determinant (`λ(coker(T)*)` in the memoir, `λ*(coker T)` in the
  book) are identified by `ι`; the line bundle is stated on the book's fibres, and
  `memoirGammaProj_eq` shows that the memoir's `γ^P_T` is the book's under this identification.
-/

open Module TensorProduct Polyfold Bundle Topology Set

noncomputable section

namespace GWMemoir

/-! ### Definition 5.8 -/

section Det

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **Memoir Definition 5.8, p. 173**: `det(T) = λ(ker T) ⊗ λ(coker(T)*)`. -/
abbrev memoirDet (T : E →L[ℝ] F) : Type _ := altFredholmDet T

/-- **Memoir Definition 5.8 and the book's Definition 6.4.1 (2021, p. 246)**: the memoir's
`λ(ker T) ⊗ λ(coker(T)*)` and the book's `λ(ker T) ⊗ λ*(coker T)` are identified by `id ⊗ ι`
(Definition 6.3.1; the memoir's `γ : Λ^max(E*) → (Λ^max E)*` of p. 173). -/
def memoir_definition_5_8_equiv {T : E →L[ℝ] F} (hT : T.IsFredholm) :
    memoirDet T ≃ₗ[ℝ] fredholmDet T :=
  altFredholmDetEquiv hT

/-- The memoir's `det(T)` is a line for `T` Fredholm. -/
theorem finrank_memoirDet {T : E →L[ℝ] F} (hT : T.IsFredholm) : finrank ℝ (memoirDet T) = 1 :=
  finrank_altFredholmDet hT

/-- `det(T) = det(T')` for `T = T'` (memoir's form). -/
def memoirDetCongr {T T' : E →L[ℝ] F} (h : T = T') : memoirDet T ≃ₗ[ℝ] memoirDet T' :=
  h ▸ LinearEquiv.refl ℝ _

theorem altFredholmDetEquiv_memoirDetCongr {T T' : E →L[ℝ] F} (h : T = T') (hT : T.IsFredholm)
    (hT' : T'.IsFredholm) (x : memoirDet T) :
    altFredholmDetEquiv hT' (memoirDetCongr h x) =
      linDetEquivOfEq (congrArg (fun A : E →L[ℝ] F => (A : E →ₗ[ℝ] F)) h)
        (altFredholmDetEquiv hT x) := by
  subst h
  rw [linDetEquivOfEq_self]
  rfl

end Det

/-! ### Definitions 5.9, 5.10 and Lemma 5.11 -/

section Exact

variable {A B C D : Type*} [AddCommGroup A] [Module ℝ A] [AddCommGroup B] [Module ℝ B]
  [AddCommGroup C] [Module ℝ C] [AddCommGroup D] [Module ℝ D]

/-- A block-triangular determinant: for `e = e₁ ++ e₂` and `v = v₁ ++ v₂` with `e₁ᵢ(v₂ⱼ) = 0`,
`det(eᵢ(vⱼ)) = det(e₁ᵢ(v₁ⱼ)) · det(e₂ᵢ(v₂ⱼ))`. -/
theorem det_append_of_zero {p q : ℕ} (e₁ : Fin p → Module.Dual ℝ C) (e₂ : Fin q → Module.Dual ℝ C)
    (v₁ : Fin p → C) (v₂ : Fin q → C) (h : ∀ i k, e₁ i (v₂ k) = 0) :
    (Matrix.of fun i k => Fin.append e₁ e₂ i (Fin.append v₁ v₂ k)).det =
      (Matrix.of fun i k => e₁ i (v₁ k)).det * (Matrix.of fun i k => e₂ i (v₂ k)).det := by
  have hM : (Matrix.of fun i k => Fin.append e₁ e₂ i (Fin.append v₁ v₂ k)) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (Matrix.of fun i k => e₁ i (v₁ k)) 0
          (Matrix.of fun i k => e₂ i (v₁ k)) (Matrix.of fun i k => e₂ i (v₂ k))) := by
    ext i k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      refine Fin.addCases (fun k => ?_) (fun k => ?_) k <;>
      simp [Matrix.reindex_apply, h]
  rw [hM, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₁₂]

/-- A functional on a line is its value on a nonzero vector times the dual vector. -/
theorem eq_smul_dualVec {L : Type*} [AddCommGroup L] [Module ℝ L] (h1 : finrank ℝ L = 1)
    {v : L} (hv : v ≠ 0) (φ : Module.Dual ℝ L) : φ = φ v • dualVec v := by
  refine dual_ext_of_ne_zero h1 hv ?_
  rw [LinearMap.smul_apply, dualVec_self h1 hv, smul_eq_mul, mul_one]

variable (S : FourTermExact A B C D) [FiniteDimensional ℝ A] [FiniteDimensional ℝ B]
  [FiniteDimensional ℝ C] [FiniteDimensional ℝ D]

/-- `id ⊗ ι : λ(X) ⊗ λ(Y*) ≅ λ(X) ⊗ λ*(Y)`. -/
abbrev iotaTensor (X Y : Type*) [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
    [FiniteDimensional ℝ Y] :
    maxPow X ⊗[ℝ] maxPow (Module.Dual ℝ Y) ≃ₗ[ℝ] maxPow X ⊗[ℝ] maxPowDual Y :=
  TensorProduct.congr (LinearEquiv.refl ℝ _) (iotaDualEquiv Y)

/-- **Memoir Definition 5.9, p. 173**: `Φ_E : λ(A) ⊗ λ(D*) → λ(B) ⊗ λ(C*)`, the book's `Φ_E`
of (6.4) (Lemma 6.3.3, 2021 p. 242) read through `ι` on both sides. -/
def memoirPhi : (maxPow A ⊗[ℝ] maxPow (Module.Dual ℝ D)) ≃ₗ[ℝ]
    (maxPow B ⊗[ℝ] maxPow (Module.Dual ℝ C)) :=
  iotaTensor A D ≪≫ₗ S.phiEquiv ≪≫ₗ (iotaTensor B C).symm

theorem iotaTensor_memoirPhi (x : maxPow A ⊗[ℝ] maxPow (Module.Dual ℝ D)) :
    iotaTensor B C (memoirPhi S x) = S.phi (iotaTensor A D x) := by
  simp [memoirPhi]

/-- **Memoir Definition 5.9 and Lemma 5.11 for `Φ_E`, p. 173–175**: for a basis `a` of `A`, a
basis `d*` of `D*`, vectors `b` completing `α(a)` to a basis of `B`, and `c* ∈ C*` with
`det(c*ᵢ(β(bⱼ))) = 1`,
`Φ_E((a₁ ∧ … ∧ aₙ) ⊗ (d*₁ ∧ … ∧ d*_l)) =
  (α(a₁) ∧ … ∧ α(aₙ) ∧ b₁ ∧ … ∧ b_{m−n}) ⊗ (d*₁ ∘ γ ∧ … ∧ d*_l ∘ γ ∧ c*₁ ∧ … ∧ c*_{m−n})`.
Since `Φ_E` is defined without choices, the right side does not depend on them. -/
theorem memoir_definition_5_9 {n l j : ℕ} {a : Fin n → A} (ha : LinearIndependent ℝ a)
    (hn : n = finrank ℝ A) {ds : Fin l → Module.Dual ℝ D}
    (hl : l = finrank ℝ (Module.Dual ℝ D)) {b : Fin j → B}
    (hb : LinearIndependent ℝ (Fin.append (S.α ∘ a) b)) (hj : n + j = finrank ℝ B)
    (cs : Fin j → Module.Dual ℝ C) (hcs : (Matrix.of fun i k => cs i (S.β (b k))).det = 1)
    (hC : l + j = finrank ℝ (Module.Dual ℝ C)) :
    memoirPhi S (wedge a hn ⊗ₜ wedge ds hl) =
      wedge (Fin.append (S.α ∘ a) b) hj ⊗ₜ
        wedge (Fin.append (fun i => ds i ∘ₗ S.γ) cs) hC := by
  have hlD : l = finrank ℝ D := hl.trans Subspace.dual_finrank_eq
  have hjC : l + j = finrank ℝ C := hC.trans Subspace.dual_finrank_eq
  -- a basis `d` of `D`, lifts `c` with `γ(cᵢ) = dᵢ`, and `r = det(d*ᵢ(dⱼ))`
  set d : Fin l → D := ⇑((Module.finBasis ℝ D).reindex (finCongr hlD.symm)) with hd
  have hdli : LinearIndependent ℝ d := Basis.linearIndependent _
  choose c hc using fun i => S.surjective_γ (d i)
  set r := (Matrix.of fun i k => ds i (d k)).det
  have hwd : wedge d hlD ≠ 0 := wedge_basis_ne_zero' _ hlD
  have hli := S.linearIndependent_append_lift ha hn hdli hlD hb hj hc hjC
  have hwc : wedge (Fin.append c (S.β ∘ b)) hjC ≠ 0 := (wedge_ne_zero_iff hjC).2 hli
  have hD : iotaDual D (wedge ds hl) = r • dualVec (wedge d hlD) := by
    rw [eq_smul_dualVec finrank_maxPow hwd (iotaDual D (wedge ds hl)), iotaDual_wedge_wedge]
  have hCι : iotaDual C (wedge (Fin.append (fun i => ds i ∘ₗ S.γ) cs) hC) =
      r • dualVec (wedge (Fin.append c (S.β ∘ b)) hjC) := by
    rw [eq_smul_dualVec finrank_maxPow hwc (iotaDual C _), iotaDual_wedge_wedge,
      det_append_of_zero]
    · congr 1
      simp only [Function.comp_apply, hcs, mul_one, LinearMap.comp_apply, hc, r]
    · intro i k
      simp only [Function.comp_apply, LinearMap.comp_apply]
      have : S.γ (S.β (b k)) = 0 := by
        rw [← LinearMap.mem_ker, ← S.range_β]; exact ⟨_, rfl⟩
      rw [this, map_zero]
  apply (iotaTensor B C).injective
  rw [iotaTensor_memoirPhi]
  simp only [iotaTensor, TensorProduct.congr_tmul, LinearEquiv.refl_apply, iotaDualEquiv_apply]
  rw [hD, hCι, TensorProduct.tmul_smul, map_smul, S.phi_wedge_tmul ha hn hdli hlD hb hj hc hjC,
    TensorProduct.tmul_smul]

/-- The pairing `λ(C) ⊗ λ(B) ⊗ λ(C*) → λ(B)`, `(c) ⊗ (b) ⊗ (c*) ↦ det(c*ⱼ(cᵢ)) · (b)`
(memoir, p. 174). -/
def memoirPairing (B C : Type*) [AddCommGroup B] [Module ℝ B] [AddCommGroup C] [Module ℝ C]
    [FiniteDimensional ℝ C] :
    maxPow C ⊗[ℝ] (maxPow B ⊗[ℝ] maxPow (Module.Dual ℝ C)) →ₗ[ℝ] maxPow B :=
  contractDual B C ∘ₗ LinearMap.lTensor _ (iotaTensor B C).toLinearMap

/-- **Memoir Definition 5.10, p. 174**: `Ψ_E : λ(C) ⊗ λ(A) ⊗ λ(D*) → λ(B)`, in the memoir's
alternative form: `Id ⊗ Φ_E` followed by the pairing. -/
def memoirPsi : maxPow C ⊗[ℝ] (maxPow A ⊗[ℝ] maxPow (Module.Dual ℝ D)) →ₗ[ℝ] maxPow B :=
  memoirPairing B C ∘ₗ LinearMap.lTensor _ (memoirPhi S).toLinearMap

/-- `Ψ_E` is the book's `Ψ_E` (Proposition 6.3.5, 2021 p. 243) read through `ι` on `λ(D*)`. -/
theorem memoirPsi_eq_psi :
    memoirPsi S = S.psi ∘ₗ LinearMap.lTensor _ (iotaTensor A D).toLinearMap := by
  apply TensorProduct.ext'
  intro v x
  simp only [memoirPsi, memoirPairing, FourTermExact.psi, LinearMap.comp_apply,
    LinearMap.lTensor_tmul, LinearEquiv.coe_coe]
  rw [iotaTensor_memoirPhi]

/-- **Memoir Definition 5.10, the formula (5.73), p. 174**: for a basis `a` of `A`, a basis `d*`
of `D*`, `c* ∈ C*` and vectors `b` completing `α(a)` to a basis of `B` with
`det(c*ᵢ(β(bⱼ))) = 1`, and `c₁, …, c_l ∈ C` with `det(d*ᵢ(γ(cⱼ))) = 1`,
`Ψ_E((c₁ ∧ … ∧ c_l ∧ β(b₁) ∧ … ∧ β(b_{m−n})) ⊗ (a₁ ∧ … ∧ aₙ) ⊗ (d*₁ ∧ … ∧ d*_l)) =
  α(a₁) ∧ … ∧ α(aₙ) ∧ b₁ ∧ … ∧ b_{m−n}`. -/
theorem memoir_definition_5_10 {n l j : ℕ} {a : Fin n → A} (ha : LinearIndependent ℝ a)
    (hn : n = finrank ℝ A) {ds : Fin l → Module.Dual ℝ D}
    (hl : l = finrank ℝ (Module.Dual ℝ D)) {b : Fin j → B}
    (hb : LinearIndependent ℝ (Fin.append (S.α ∘ a) b)) (hj : n + j = finrank ℝ B)
    (cs : Fin j → Module.Dual ℝ C) (hcs : (Matrix.of fun i k => cs i (S.β (b k))).det = 1)
    (c : Fin l → C) (hc : (Matrix.of fun i k => ds i (S.γ (c k))).det = 1)
    (hC : l + j = finrank ℝ C) :
    memoirPsi S (wedge (Fin.append c (S.β ∘ b)) hC ⊗ₜ (wedge a hn ⊗ₜ wedge ds hl)) =
      wedge (Fin.append (S.α ∘ a) b) hj := by
  have hC' : l + j = finrank ℝ (Module.Dual ℝ C) := hC.trans Subspace.dual_finrank_eq.symm
  simp only [memoirPsi, memoirPairing, LinearMap.comp_apply, LinearMap.lTensor_tmul,
    LinearEquiv.coe_coe, memoir_definition_5_9 S ha hn hl hb hj cs hcs hC', iotaTensor,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply, iotaDualEquiv_apply, contractDual_tmul]
  rw [iotaDual_wedge_wedge, det_append_of_zero]
  · simp only [Function.comp_apply, LinearMap.comp_apply, hc, hcs, mul_one, one_smul]
  · intro i k
    simp only [Function.comp_apply, LinearMap.comp_apply]
    have : S.γ (S.β (b k)) = 0 := by
      rw [← LinearMap.mem_ker, ← S.range_β]; exact ⟨_, rfl⟩
    rw [this, map_zero]

/-- **Memoir Lemma 5.11, p. 175**: `Φ_E` and `Ψ_E` are isomorphisms (their independence of the
choices is `memoir_definition_5_9` and `memoir_definition_5_10`). -/
theorem memoir_lemma_5_11 :
    Function.Bijective (memoirPhi S) ∧ Function.Bijective (memoirPsi S) := by
  refine ⟨(memoirPhi S).bijective, ?_⟩
  have h1 : finrank ℝ (maxPow C ⊗[ℝ] (maxPow A ⊗[ℝ] maxPow (Module.Dual ℝ D))) = 1 := by
    simp [Module.finrank_tensorProduct, finrank_maxPow]
  have hne : memoirPsi S ≠ 0 := by
    intro h0
    set χ := S.canonicalChoice
    have hx := S.proposition_6_3_5 χ
    have : memoirPsi S (χ.wedgeC ⊗ₜ (iotaTensor A D).symm χ.source) = χ.wedgeB := by
      rw [memoirPsi_eq_psi, LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply, hx]
    rw [h0, LinearMap.zero_apply] at this
    exact χ.wedgeB_ne_zero this.symm
  have hinj := injective_of_finrank_eq_one h1 hne
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (h1.trans finrank_maxPow.symm)).1 hinj⟩

end Exact

/-! ### The `γ` of a sequence `(P)`: naturality of `ι` -/

section Naturality

variable {X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]

/-- `ι` is natural (Proposition 6.3.2, 2021 p. 242), in the form `ι ∘ λ(Φ*) = λ*(Φ) ∘ ι`. -/
theorem iotaDual_maxPowEquiv_dualMap (Φ : X ≃ₗ[ℝ] Y) (ω : maxPow (Module.Dual ℝ Y)) :
    iotaDual X (maxPowEquiv Φ.dualMap ω) = maxPowDualEquiv Φ (iotaDual Y ω) := by
  have h := LinearMap.congr_fun (proposition_6_3_2 Φ) ω
  simp only [LinearMap.comp_apply] at h
  rw [← coe_maxPowDualEquiv] at h
  exact h.symm

end Naturality

/-! ### Orthogonal good projections: Lemmas 5.12–5.14 -/

section Hilbert

variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- **Memoir p. 176**: `Π_T`, the orthogonal projections `P : F → F` with (1) `dim(F/R(P)) < ∞`
and (2) `R(P ∘ T) = R(P)`: the book's good left-projections (Definition 6.4.3, 2021 p. 247)
which are orthogonal. -/
def memoirPi (T : E →L[ℝ] F) : Set (F →L[ℝ] F) := {P | IsStarProjection P ∧ IsGoodLeftProj T P}

omit [CompleteSpace E] in
theorem memoirPi_subset_goodLeftProjs (T : E →L[ℝ] F) : memoirPi T ⊆ goodLeftProjs T :=
  fun _ h => h.2

/-- For an orthogonal projection, `x − P x ⊥ R(P)`. -/
theorem sub_apply_mem_orthogonal {P : F →L[ℝ] F} (hP : IsStarProjection P) (x : F) :
    x - P x ∈ (LinearMap.range (P : F →ₗ[ℝ] F))ᗮ := by
  obtain ⟨_, hPe⟩ := isStarProjection_iff_eq_starProjection_range.1 hP
  have := Submodule.sub_starProjection_mem_orthogonal (K := P.range) x
  rw [← hPe] at this
  exact this

omit [CompleteSpace E] in
/-- `Π_T` is not empty for `T` Fredholm: the orthogonal projection onto `R(T)`. -/
theorem exists_mem_memoirPi {T : E →L[ℝ] F} (hT : T.IsFredholm) : ∃ P, P ∈ memoirPi T := by
  set H := LinearMap.range (T : E →ₗ[ℝ] F)
  have : CompleteSpace H := hT.isClosed_range.completeSpace_coe
  have hPP : H.starProjection ∘L H.starProjection = H.starProjection :=
    H.isIdempotentElem_starProjection
  have hr : LinearMap.range (H.starProjection : F →ₗ[ℝ] F) = H := H.range_starProjection
  refine ⟨H.starProjection, isStarProjection_starProjection, hPP, ?_, ?_⟩
  · rw [hr]; exact hT.finite_coker
  · rw [hr]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact H.starProjection_apply_mem _
    · rintro ⟨x, rfl⟩
      exact ⟨x, Submodule.starProjection_eq_self_iff.2 ⟨x, rfl⟩⟩

omit [CompleteSpace E] in
/-- **Memoir Lemma 5.12, p. 176**: for `P, P' ∈ Π_T` the orthogonal projection `Q` onto
`R(P) ∩ R(P')` lies in `Π_T` and `Q ≤ P`, `Q ≤ P'`.  As printed, with the memoir's `Q`.  For bounded
projections on Banach spaces (the book's Lemma 6.4.9) a projection onto `R(P) ∩ R(P')` below both
need not exist (`Polyfold.lemma_6_10_text_reading_preprint`); some common lower bound does
(`Polyfold.lemma_6_10_preprint`). -/
theorem memoir_lemma_5_12 {T : E →L[ℝ] F} {P P' : F →L[ℝ] F} (hP : P ∈ memoirPi T)
    (hP' : P' ∈ memoirPi T) :
    ∃ Q ∈ memoirPi T, ProjLE Q P ∧ ProjLE Q P' ∧
      LinearMap.range (Q : F →ₗ[ℝ] F) =
        LinearMap.range (P : F →ₗ[ℝ] F) ⊓ LinearMap.range (P' : F →ₗ[ℝ] F) := by
  set H := LinearMap.range (P : F →ₗ[ℝ] F) ⊓ LinearMap.range (P' : F →ₗ[ℝ] F) with hH
  have : CompleteSpace H :=
    (hP.2.isClosed_range.inter hP'.2.isClosed_range).completeSpace_coe
  have hr : LinearMap.range (H.starProjection : F →ₗ[ℝ] F) = H := H.range_starProjection
  have hle : ∀ {R : F →L[ℝ] F}, R ∈ memoirPi T →
      H ≤ LinearMap.range (R : F →ₗ[ℝ] F) → ProjLE H.starProjection R := by
    intro R hR hHR
    constructor
    · ext x
      have h0 : H.starProjection (x - R x) = 0 := by
        rw [Submodule.starProjection_apply_eq_zero_iff]
        exact Submodule.orthogonal_le hHR (sub_apply_mem_orthogonal hR.1 x)
      rw [map_sub, sub_eq_zero] at h0
      exact h0
    · ext x
      exact (proj_apply_eq_self_of_mem_range hR.2.isProj
        (hHR (H.starProjection_apply_mem x))).symm
  have hQP := hle hP inf_le_left
  have hQP' := hle hP' inf_le_right
  refine ⟨H.starProjection, ⟨isStarProjection_starProjection,
    H.isIdempotentElem_starProjection, ?_, ?_⟩, hQP, hQP', hr⟩
  · rw [hr]; exact hP.2.finiteDimensional_quotient_inf hP'.2
  · exact range_comp_eq_of_comp_eq hP.2 hQP.1.symm

/-- **Memoir Lemma 5.13, p. 177**: for `P ∈ Π_T` the sequence
`0 → ker T →j ker(P T) →Φ F/R(P) →π coker T → 0`, `Φ(x) = T x + R(P)`,
`π(y + R(P)) = (I − P) y + R(T)`, is exact (the book's Proposition 6.4.10, 2021 p. 248). -/
theorem memoir_lemma_5_13 {T : E →L[ℝ] F} {P : F →L[ℝ] F} (hP : P ∈ memoirPi T) :
    Function.Injective (projSeqJ T P) ∧
      LinearMap.range (projSeqJ T P) = LinearMap.ker (projSeqPhi T P) ∧
      LinearMap.range (projSeqPhi T P) = LinearMap.ker (projSeqPi (T := T) hP.2.isProj) ∧
      Function.Surjective (projSeqPi (T := T) hP.2.isProj) ∧
      (∀ y : F, projSeqPi (T := T) hP.2.isProj (Submodule.Quotient.mk y) =
        Submodule.Quotient.mk (y - P y)) :=
  ⟨(proposition_6_4_10 hP.2).1, (proposition_6_4_10 hP.2).2.1, (proposition_6_4_10 hP.2).2.2.1,
    (proposition_6_4_10 hP.2).2.2.2, fun _ => rfl⟩

/-- Memoir p. 177: for `P ≤ Q` in `Π_T`, `P ∈ Π_{QT}`. -/
theorem memoirPi_comp_of_projLE {T : E →L[ℝ] F} {P Q : F →L[ℝ] F} (hP : P ∈ memoirPi T)
    (hPQ : ProjLE P Q) : P ∈ memoirPi (Q ∘L T) :=
  ⟨hP.1, hP.2.of_projLE hPQ⟩

/-- **Memoir p. 177, `γ^P_T : det(T) → det(P T)`**: the isomorphism `Φ_(P)` of Definition 5.9 for
the exact sequence `(P)`, followed by `λ` of the identification `F/R(P) = F/R(P T)`. -/
def memoirGammaProj {T : E →L[ℝ] F} {P : F →L[ℝ] F} (hT : T.IsFredholm)
    (hP : IsGoodLeftProj T P) : memoirDet T ≃ₗ[ℝ] memoirDet (P ∘L T) :=
  haveI := hT.finite_ker
  haveI : FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := hT.finite_coker
  haveI := hP.finite_coker
  haveI := (hP.isFredholm_comp hT).finite_ker
  memoirPhi (projSeq hP) ≪≫ₗ
    TensorProduct.congr (LinearEquiv.refl ℝ _) (maxPowEquiv (cokerCompEquiv hP).dualMap)

/-- **The memoir's `γ^P_T` is the book's** (2021 p. 248, after Proposition 6.4.10) under the
identification `id ⊗ ι` of Definition 5.8 on both sides. -/
theorem memoirGammaProj_eq {T : E →L[ℝ] F} {P : F →L[ℝ] F} (hT : T.IsFredholm)
    (hP : IsGoodLeftProj T P) (x : memoirDet T) :
    altFredholmDetEquiv (hP.isFredholm_comp hT) (memoirGammaProj hT hP x) =
      gammaProj hT hP (altFredholmDetEquiv hT x) := by
  have := hT.finite_ker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := hT.finite_coker
  have := hP.finite_coker
  have := (hP.isFredholm_comp hT).finite_ker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)) :=
    (hP.isFredholm_comp hT).finite_coker
  have key : ∀ y, altFredholmDetEquiv (hP.isFredholm_comp hT)
      (TensorProduct.congr (LinearEquiv.refl ℝ _) (maxPowEquiv (cokerCompEquiv hP).dualMap) y) =
      TensorProduct.congr (LinearEquiv.refl ℝ _) (maxPowDualEquiv (cokerCompEquiv hP))
        (iotaTensor _ _ y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp only [LinearEquiv.map_zero]
    | tmul u ω =>
      simp only [altFredholmDetEquiv, altLinDetEquiv_tmul, TensorProduct.congr_tmul,
        LinearEquiv.refl_apply, iotaDualEquiv_apply]
      exact congrArg (u ⊗ₜ ·) (iotaDual_maxPowEquiv_dualMap _ ω)
    | add y z hy hz => simp only [LinearEquiv.map_add, hy, hz]
  exact (key _).trans (congrArg _ (iotaTensor_memoirPhi _ x))

/-- **Memoir Lemma 5.14, p. 177**: for `P ≤ Q` in `Π_T`, `γ^P_{QT} ∘ γ^Q_T = γ^P_T` (up to
`det(P (Q T)) = det(P T)`), from the book's Proposition 6.4.11 (2021 p. 249). -/
theorem memoir_lemma_5_14 {T : E →L[ℝ] F} {P Q : F →L[ℝ] F} (hT : T.IsFredholm)
    (hP : P ∈ memoirPi T) (hQ : Q ∈ memoirPi T) (hPQ : ProjLE P Q) (h : memoirDet T) :
    memoirDetCongr (comp_comp_eq_of_projLE (T := T) hPQ)
        (memoirGammaProj (hQ.2.isFredholm_comp hT) (hP.2.of_projLE hPQ)
          (memoirGammaProj hT hQ.2 h)) =
      memoirGammaProj hT hP.2 h := by
  have hQT := hQ.2.isFredholm_comp hT
  apply (altFredholmDetEquiv (hP.2.isFredholm_comp hT)).injective
  have e1 := altFredholmDetEquiv_memoirDetCongr (comp_comp_eq_of_projLE (T := T) hPQ)
    ((hP.2.of_projLE hPQ).isFredholm_comp hQT) (hP.2.isFredholm_comp hT)
    (memoirGammaProj hQT (hP.2.of_projLE hPQ) (memoirGammaProj hT hQ.2 h))
  have e2 := memoirGammaProj_eq hQT (hP.2.of_projLE hPQ) (memoirGammaProj hT hQ.2 h)
  have e3 := memoirGammaProj_eq hT hQ.2 h
  have e4 := memoirGammaProj_eq hT hP.2 h
  have e5 := (proposition_6_4_11 hT hP.2 hQ.2 hPQ).2.2
  refine e1.trans ((congrArg _ e2).trans ?_)
  refine (congrArg (fun y => linDetEquivOfEq (congrArg (fun A : E →L[ℝ] F => (A : E →ₗ[ℝ] F))
    (comp_comp_eq_of_projLE (T := T) hPQ)) (gammaProj hQT (hP.2.of_projLE hPQ) y)) e3).trans ?_
  exact (e5 _).trans e4.symm

/-! ### Lemma 5.15 and Theorem 5.16: the line bundle `DET(E, F)` -/

/-- Operators near a Fredholm operator are Fredholm (the memoir's Lemma 5.15 (i)), from a
quasi-inverse (`Polyfold.isFredholm_add_of_norm_lt`). -/
theorem exists_isFredholm_of_lt {T₀ : E →L[ℝ] F} (hT₀ : T₀.IsFredholm) :
    ∃ δ > 0, ∀ T : E →L[ℝ] F, ‖T - T₀‖ < δ → T.IsFredholm := by
  obtain ⟨v, hv⟩ := hT₀.exists_isQuasiInverse
  refine ⟨1 / (‖v‖ + 1), by positivity, fun T hT => ?_⟩
  have h2 : ‖T - T₀‖ * (‖v‖ + 1) < 1 := (lt_div_iff₀ (by positivity)).1 hT
  have h := isFredholm_add_of_norm_lt hv (s := T - T₀)
    (by nlinarith [norm_nonneg v, norm_nonneg (T - T₀)])
  simpa using h

/-- **Memoir Lemma 5.15, p. 180**: for `T₀` Fredholm and `P ∈ Π_{T₀}` there are `ε > 0` and the
chart `L_{T₀,P,ε}` built, as in the memoir, with the orthogonal complement `X = ker(P T₀)^⊥`, such
that (i) every `T` with `‖T − T₀‖ < ε` is Fredholm, (ii) `P ∈ Π_T`, and (iii)–(iv) the map
`(T, h) ↦ (T, γ^P_T(h))`, read in the frame of `L_{T₀,P,ε}`, is a trivialization of the line bundle
`DET(E, F)` (the book's Lemma 6.5.1 and Propositions 6.5.4, 6.5.8, 2021 pp. 250–252). -/
theorem memoir_lemma_5_15 {T₀ : E →L[ℝ] F} (hT₀ : T₀.IsFredholm) {P : F →L[ℝ] F}
    (hP : P ∈ memoirPi T₀) :
    ∃ ε > 0, ∃ c : LocalDetChart E F, c.T = T₀ ∧ c.P = P ∧
      c.Y = (LinearMap.ker ((P ∘L T₀ : E →L[ℝ] F) : E →ₗ[ℝ] F))ᗮ ∧ ε ≤ c.ε ∧
      (∀ T : E →L[ℝ] F, ‖T - T₀‖ < ε → T.IsFredholm ∧ P ∈ memoirPi T) ∧
      ∃ e : Trivialization ℝ (π ℝ (DetFiber (E := E) (F := F))),
        MemTrivializationAtlas e ∧ e.baseSet = c.baseSet ∧ ∀ x, e x = c.pretriv x := by
  set K := LinearMap.ker ((P ∘L T₀ : E →L[ℝ] F) : E →ₗ[ℝ] F)
  have := (hP.2.isFredholm_comp hT₀).finite_ker
  have hY : K.IsTopCompl Kᗮ := K.isTopCompl_orthogonal
  obtain ⟨ε, hε, h⟩ := lemma_6_5_1 hP.2 hY
  let c : LocalDetChart E F :=
    ⟨T₀, hT₀, P, hP.2, Kᗮ, hY, ε, hε, fun S hS => (h S hS).1, fun S hS => (h S hS).2⟩
  obtain ⟨δ, hδ, hF⟩ := exists_isFredholm_of_lt hT₀
  obtain ⟨e, he, hb, hx⟩ := (proposition_6_5_8 (E := E) (F := F)).2 c
  exact ⟨min ε δ, lt_min hε hδ, c, rfl, rfl, rfl, min_le_left _ _, fun T hT =>
    ⟨hF T (lt_of_lt_of_le hT (min_le_right _ _)), hP.1,
      (h T (lt_of_lt_of_le hT (min_le_left _ _))).1⟩, e, he, hb, hx⟩

variable (E F) in
/-- The memoir's charts: subsets `B` of `DET(E, F)` over the ball of a chart `L_{T,P,ε}` with `P`
orthogonal and `X = ker(P T)^⊥` whose image in `ball × ℝ` is open. -/
def memoirDetBasis : Set (Set (TotalSpace ℝ (DetFiber (E := E) (F := F)))) :=
  {B | ∃ c : LocalDetChart E F, IsStarProjection c.P ∧
    c.Y = (LinearMap.ker ((c.P ∘L c.T : E →L[ℝ] F) : E →ₗ[ℝ] F))ᗮ ∧
    B ⊆ c.pretriv.source ∧ IsOpen (c.pretriv '' B)}

/-- **Memoir Theorem 5.16, p. 181**: `DET(E, F)` is a topological line bundle over `Fred(E, F)`,
and the memoir's charts (orthogonal `P`, orthogonal complements) form a basis of its topology, so
the structure made from them is the book's (Propositions 6.5.7, 6.5.8, Lemma 6.5.9, 2021
pp. 251–252), whose charts allow every bounded `P ∈ Π_T`. -/
theorem memoir_theorem_5_16 :
    VectorBundle ℝ ℝ (DetFiber (E := E) (F := F)) ∧
      TopologicalSpace.IsTopologicalBasis (memoirDetBasis E F) ∧
      (inferInstance : TopologicalSpace (TotalSpace ℝ (DetFiber (E := E) (F := F)))) =
        TopologicalSpace.generateFrom (memoirDetBasis E F) := by
  have hb : TopologicalSpace.IsTopologicalBasis (memoirDetBasis E F) := by
    refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro B ⟨c, -, -, hBs, hBo⟩
      let e := (detPrebundle E F).trivializationOfMemPretrivializationAtlas ⟨c, rfl⟩
      have hB : B = e.source ∩ e ⁻¹' (c.pretriv '' B) := by
        ext x
        refine ⟨fun hx => ⟨hBs hx, x, hx, rfl⟩, ?_⟩
        rintro ⟨hx, y, hy, hyx⟩
        exact (e.toOpenPartialHomeomorph.injOn (hBs hy) hx hyx) ▸ hy
      rw [hB]
      exact e.continuousOn.isOpen_inter_preimage e.open_source hBo
    · intro x O hx hO
      obtain ⟨P, hP⟩ := exists_mem_memoirPi x.proj.2
      obtain ⟨ε, -, c, hcT, hcP, hcY, -, -, -⟩ := memoir_lemma_5_15 x.proj.2 hP
      let e := (detPrebundle E F).trivializationOfMemPretrivializationAtlas ⟨c, rfl⟩
      have hxc : x.proj ∈ c.baseSet := by
        change ‖x.proj.1 - c.T‖ < c.ε
        rw [hcT, sub_self, norm_zero]
        exact c.ε_pos
      refine ⟨O ∩ c.pretriv.source, ⟨c, hcP ▸ hP.1, by rw [hcP, hcT]; exact hcY,
        inter_subset_right, ?_⟩, ⟨hx, hxc⟩, inter_subset_left⟩
      exact e.toOpenPartialHomeomorph.isOpen_image_of_subset_source (hO.inter e.open_source)
        inter_subset_right
  exact ⟨inferInstance, hb, hb.eq_generateFrom⟩

end Hilbert

/-! ### Lemma 5.37 in abstract form (fixed `J`, `j`) -/

section Compact

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The operators `L₀ + A` with `A` compact. -/
def compactPerturbations (L₀ : E →L[ℝ] F) : Set (E →L[ℝ] F) :=
  {L | IsCompactOperator (L - L₀)}

/-- **Memoir Lemma 5.37, p. 188, abstract part (for fixed `u`, `J`, `j`)**: the operators
`L₀ + A`, `A` compact, around a Fredholm `L₀` (the form (5.78) with fixed `∇`, `J`, `j`) form a
convex, hence contractible, set of Fredholm operators (`Polyfold.isFredholm_add_isCompactOperator`,
Proposition 1.1.11 of the book), and `DET` over it is a line bundle with exactly two orientations
(Proposition 6.6.1).  The variation of `J` and `j` (contractible spaces of almost complex
structures, Remark 5.38) is not part of this statement. -/
theorem memoir_lemma_5_37 {L₀ : E →L[ℝ] F} (hL₀ : L₀.IsFredholm) :
    Convex ℝ (compactPerturbations L₀) ∧
      (∀ L ∈ compactPerturbations L₀, L.IsFredholm) ∧
      ContractibleSpace (compactPerturbations L₀) ∧
      ∃ hC : ∀ L ∈ compactPerturbations L₀, L.IsFredholm,
        VectorBundle ℝ ℝ (DetOn (compactPerturbations L₀) hC) ∧
        ∃ o₁ o₂ : LineOrientation (DetOn (compactPerturbations L₀) hC), o₁ ≠ o₂ ∧
          ∀ o : LineOrientation (DetOn (compactPerturbations L₀) hC), o = o₁ ∨ o = o₂ := by
  have hconv : Convex ℝ (compactPerturbations L₀) := by
    intro L₁ h₁ L₂ h₂ a b ha hb hab
    have : a • L₁ + b • L₂ - L₀ = a • (L₁ - L₀) + b • (L₂ - L₀) := by
      have h0 : L₀ = a • L₀ + b • L₀ := by rw [← add_smul, hab, one_smul]
      conv_lhs => rw [h0]
      rw [smul_sub, smul_sub]; abel
    change IsCompactOperator (a • L₁ + b • L₂ - L₀)
    rw [this]
    exact (h₁.smul a).add (h₂.smul b)
  have hne : L₀ ∈ compactPerturbations L₀ := by
    change IsCompactOperator (L₀ - L₀)
    rw [sub_self]; exact isCompactOperator_zero
  have hF : ∀ L ∈ compactPerturbations L₀, L.IsFredholm := fun L hL => by
    have := isFredholm_add_isCompactOperator hL₀ hL
    rwa [add_sub_cancel] at this
  exact ⟨hconv, hF, hconv.contractibleSpace ⟨L₀, hne⟩, hF,
    proposition_6_6_1 hconv ⟨L₀, hne⟩ hF⟩

end Compact

end GWMemoir
