import Polyfold
/-! Blind formalization of V6_18 (the text's §6.3, Proposition 6.15, p. 213).

Text: with (94), `ι_φ` is given as follows: for a basis `a` of `ker T`,
`d̄_i = φ(c̄_i) + R(T)` a basis of `F/R(T)` and `b̄_j = (b_j, r_j)` completing `(a_i, 0)` to a basis
of `ker T_φ`, the `r_j` and `c̄_i` form a basis of `ℝⁿ`, and
`ι_φ(h) = det(c̄_1, …, c̄_m, r_1, …, r_l)⁻¹ ((a_1, 0) ∧ … ∧ (a_k, 0) ∧ b̄_1 ∧ … ∧ b̄_l) ⊗ 1*`.

Choices:
- Setting as in the blind V6_16 (copied): real Banach spaces `E F : Type`, `T : E →L[ℝ] F`
  Fredholm in the classical sense (`IsFredholmOp`), `ℝⁿ = Fin n → ℝ`, `φ : ℝⁿ →L[ℝ] F` (every
  linear map on `ℝⁿ` is continuous), `T_φ = T.coprod φ` on `E × ℝⁿ`, assumed onto (as in
  Lemma 6.14, which `ι_φ` uses); the maps `jS` (`e ↦ (e, 0)`), `piS` (`(e, r) ↦ r`), `clsPhi`
  (`r ↦ φ(r) + R(T)`) of the sequence of Lemma 6.14 written out.
- Determinant lines: the project's `maxPow`, `maxPowDual`, `wedge`, `dualVec`, `fredholmDet`
  (checked with `#print`; `det(T) = λ(ker T) ⊗ λ*(F/R(T))`).
- `ι_φ` is (as defined in the text before Proposition 6.15) `Φ_E` of the sequence of Lemma 6.14,
  `λ(ker T) ⊗ λ*(F/R(T)) → λ(ker T_φ) ⊗ λ*(ℝⁿ)`, followed by `1 ⊗ ψ` with
  `ψ : λ*(ℝⁿ) → λ*(F/R(T_φ)) = λ*({0})` of (94).  `Φ_E` is characterized by (91) for every
  choice (`IsPhiE`, general four-term version: `b'` after `α(a)`, `c'= β(b')` after `c`) and `ψ`
  by `ψ((e₁ ∧ … ∧ eₙ)*) = 1*` (`IsPsi`, as in V6_17); both are quantified universally among the
  maps with these properties (they exist and are unique).  `1* = dualVec` of the empty wedge.
- `h = (a_1 ∧ … ∧ a_k) ⊗ (d̄_1 ∧ … ∧ d̄_m)*` (implicit in the statement); `k = dim ker T`,
  `m = dim F/R(T)`, `l` the number of `b̄`'s (`k + l = dim ker T_φ`).  "`d̄` a basis of `F/R(T)`":
  `[φ] ∘ c̄` linearly independent with `m = dim F/R(T)`; "`b̄` completing `(a_i, 0)` to a basis":
  `(j a, b̄)` linearly independent with `k + l = dim ker T_φ`; `r_j = π(b̄_j)`.
- "The `r_j` and `c̄_i` form a basis of `ℝⁿ`": `(c̄, r)` linearly independent and `m + l = n`.  The
  determinant is that of the `n × n` matrix with columns `c̄_1, …, c̄_m, r_1, …, r_l` (indexed
  through `m + l = n`; the formula is stated for every proof of `m + l = n`, which the first
  conjunct provides).
- `1*` and `ψ` need `dim F/R(T_φ) = 0` to be typed (`wedge` of the empty family); the small
  auxiliary theorem `finrank_coker_Tphi` proves it from the surjectivity of `T_φ` (no junk).
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V6_18
open Polyfold

section Fredholm
variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

/-- A bounded operator is Fredholm: finite-dimensional kernel, closed range, finite-dimensional
cokernel. -/
def IsFredholmOp (L : X →L[ℝ] Y) : Prop :=
  FiniteDimensional ℝ (LinearMap.ker (L : X →ₗ[ℝ] Y)) ∧
    IsClosed (LinearMap.range (L : X →ₗ[ℝ] Y) : Set Y) ∧
    FiniteDimensional ℝ (Y ⧸ LinearMap.range (L : X →ₗ[ℝ] Y))

end Fredholm

section Phi
variable {A B C D : Type} [AddCommGroup A] [Module ℝ A] [AddCommGroup B] [Module ℝ B]
  [AddCommGroup C] [Module ℝ C] [AddCommGroup D] [Module ℝ D]

/-- `g = Φ_E : λ(A) ⊗ λ*(D) → λ(B) ⊗ λ*(C)` of (91) for `0 → A →α B →β C →γ D → 0`: for every
choice (`a` a basis of `A`, `d` of `D`, `b'` completing `α(a)` to a basis of `B`, `c` with
`γ(c) = d`), `g((a₁ ∧ … ∧ aₙ) ⊗ (d₁ ∧ … ∧ d_l)*) = (α a ∧ b') ⊗ (c ∧ β b')*`. -/
def IsPhiE (α : A →ₗ[ℝ] B) (β : B →ₗ[ℝ] C) (γ : C →ₗ[ℝ] D)
    (g : TensorProduct ℝ (maxPow A) (maxPowDual D) →ₗ[ℝ]
      TensorProduct ℝ (maxPow B) (maxPowDual C)) : Prop :=
  ∀ (n l j : ℕ) (a : Fin n → A) (d : Fin l → D) (b' : Fin j → B) (c : Fin l → C)
    (hA : n = Module.finrank ℝ A) (hD : l = Module.finrank ℝ D)
    (hB : n + j = Module.finrank ℝ B) (hC : l + j = Module.finrank ℝ C),
    LinearIndependent ℝ a → LinearIndependent ℝ d →
    LinearIndependent ℝ (Fin.append (α ∘ a) b') → (∀ i, γ (c i) = d i) →
    g (wedge a hA ⊗ₜ[ℝ] dualVec (wedge d hD)) =
      wedge (Fin.append (α ∘ a) b') hB ⊗ₜ[ℝ] dualVec (wedge (Fin.append c (β ∘ b')) hC)

end Phi

/-- `e₁ ∧ … ∧ eₙ ∈ λ(ℝⁿ)` for the standard basis. -/
noncomputable def stdW (n : ℕ) : maxPow (Fin n → ℝ) :=
  wedge (Pi.basisFun ℝ (Fin n)) (Module.finrank_fin_fun ℝ).symm

/-- `1* ∈ λ*({0})`: the dual of the empty wedge `1 ∈ λ({0})`. -/
noncomputable def oneStar (Z : Type) [AddCommGroup Z] [Module ℝ Z]
    (h0 : 0 = Module.finrank ℝ Z) : maxPowDual Z :=
  dualVec (wedge (![] : Fin 0 → Z) h0)

/-- (94): `ψ((e₁ ∧ … ∧ eₙ)*) = 1*`. -/
def IsPsi {n : ℕ} {Z : Type} [AddCommGroup Z] [Module ℝ Z] (h0 : 0 = Module.finrank ℝ Z)
    (ψ : maxPowDual (Fin n → ℝ) →ₗ[ℝ] maxPowDual Z) : Prop :=
  ψ (dualVec (stdW n)) = oneStar Z h0

section Stab
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {n : ℕ}

/-- The stabilization `T_φ : E ⊕ ℝⁿ → F`, `(e, r) ↦ Te + φ(r)`. -/
def Tphi (T : E →L[ℝ] F) (φ : (Fin n → ℝ) →L[ℝ] F) : E × (Fin n → ℝ) →L[ℝ] F :=
  T.coprod φ

/-- `j : ker T → ker T_φ`, `e ↦ (e, 0)`. -/
def jS (T : E →L[ℝ] F) (φ : (Fin n → ℝ) →L[ℝ] F) :
    LinearMap.ker (T : E →ₗ[ℝ] F) →ₗ[ℝ]
      LinearMap.ker ((Tphi T φ : E × (Fin n → ℝ) →L[ℝ] F) : E × (Fin n → ℝ) →ₗ[ℝ] F) :=
  LinearMap.codRestrict _
    ((LinearMap.inl ℝ E (Fin n → ℝ)) ∘ₗ (LinearMap.ker (T : E →ₗ[ℝ] F)).subtype)
    (fun x => by simp [Tphi])

/-- `π : ker T_φ → ℝⁿ`, `(e, r) ↦ r`. -/
def piS (T : E →L[ℝ] F) (φ : (Fin n → ℝ) →L[ℝ] F) :
    LinearMap.ker ((Tphi T φ : E × (Fin n → ℝ) →L[ℝ] F) : E × (Fin n → ℝ) →ₗ[ℝ] F) →ₗ[ℝ]
      (Fin n → ℝ) :=
  (LinearMap.snd ℝ E (Fin n → ℝ)) ∘ₗ (LinearMap.ker _).subtype

/-- `[φ] : ℝⁿ → F/R(T)`, `r ↦ φ(r) + R(T)`. -/
def clsPhi (T : E →L[ℝ] F) (φ : (Fin n → ℝ) →L[ℝ] F) :
    (Fin n → ℝ) →ₗ[ℝ] F ⧸ LinearMap.range (T : E →ₗ[ℝ] F) :=
  (LinearMap.range (T : E →ₗ[ℝ] F)).mkQ ∘ₗ (φ : (Fin n → ℝ) →ₗ[ℝ] F)

/-- `F/R(T_φ) = {0}` when `T_φ` is onto, so `dim F/R(T_φ) = 0`. -/
theorem finrank_coker_Tphi {T : E →L[ℝ] F} {φ : (Fin n → ℝ) →L[ℝ] F}
    (hs : Function.Surjective (Tphi T φ)) :
    0 = Module.finrank ℝ
      (F ⧸ LinearMap.range ((Tphi T φ : E × (Fin n → ℝ) →L[ℝ] F) : E × (Fin n → ℝ) →ₗ[ℝ] F)) := by
  have : Subsingleton
      (F ⧸ LinearMap.range ((Tphi T φ : E × (Fin n → ℝ) →L[ℝ] F) :
        E × (Fin n → ℝ) →ₗ[ℝ] F)) :=
    Submodule.Quotient.subsingleton_iff.mpr (LinearMap.range_eq_top.mpr hs)
  exact Module.finrank_zero_of_subsingleton.symm

end Stab

/-- Proposition 6.15: for `ι_φ = (1 ⊗ ψ) ∘ Φ_E` (sequence of Lemma 6.14, `ψ` of (94)), a basis `a`
of `ker T`, `c̄` with `φ(c̄) + R(T)` a basis of `F/R(T)` and `b̄ = (b, r)` completing `(a, 0)` to a
basis of `ker T_φ`: `(c̄, r)` is a basis of `ℝⁿ`, and
`ι_φ((a ∧) ⊗ (d̄ ∧)*) = det(c̄, r)⁻¹ ((a, 0) ∧ b̄) ⊗ 1*`. -/
def B : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (n : ℕ) (T : E →L[ℝ] F)
    (φ : (Fin n → ℝ) →L[ℝ] F),
    IsFredholmOp T → ∀ hs : Function.Surjective (Tphi T φ),
    ∀ g : fredholmDet T →ₗ[ℝ]
        TensorProduct ℝ
          (maxPow (LinearMap.ker
            ((Tphi T φ : E × (Fin n → ℝ) →L[ℝ] F) : E × (Fin n → ℝ) →ₗ[ℝ] F)))
          (maxPowDual (Fin n → ℝ)),
      IsPhiE (jS T φ) (piS T φ) (clsPhi T φ) g →
    ∀ ψ : maxPowDual (Fin n → ℝ) →ₗ[ℝ]
        maxPowDual (F ⧸ LinearMap.range
          ((Tphi T φ : E × (Fin n → ℝ) →L[ℝ] F) : E × (Fin n → ℝ) →ₗ[ℝ] F)),
      IsPsi (finrank_coker_Tphi hs) ψ →
    ∀ (k m l : ℕ) (a : Fin k → LinearMap.ker (T : E →ₗ[ℝ] F)) (cbar : Fin m → (Fin n → ℝ))
      (bbar : Fin l → LinearMap.ker
        ((Tphi T φ : E × (Fin n → ℝ) →L[ℝ] F) : E × (Fin n → ℝ) →ₗ[ℝ] F))
      (hk : k = Module.finrank ℝ (LinearMap.ker (T : E →ₗ[ℝ] F)))
      (hm : m = Module.finrank ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)))
      (hkl : k + l = Module.finrank ℝ (LinearMap.ker
        ((Tphi T φ : E × (Fin n → ℝ) →L[ℝ] F) : E × (Fin n → ℝ) →ₗ[ℝ] F))),
      LinearIndependent ℝ a → LinearIndependent ℝ (clsPhi T φ ∘ cbar) →
      LinearIndependent ℝ (Fin.append (jS T φ ∘ a) bbar) →
        -- the `r_j = π(b̄_j)` and the `c̄_i` form a basis of `ℝⁿ`
        (LinearIndependent ℝ (Fin.append cbar (piS T φ ∘ bbar)) ∧ m + l = n) ∧
        -- the formula for `ι_φ(h)`
        ∀ hn : m + l = n,
          (TensorProduct.map LinearMap.id ψ ∘ₗ g)
              (wedge a hk ⊗ₜ[ℝ] dualVec (wedge (clsPhi T φ ∘ cbar) hm)) =
            (Matrix.det (Matrix.of fun i j =>
                Fin.append cbar (piS T φ ∘ bbar) (Fin.cast hn.symm j) i))⁻¹ •
              (wedge (Fin.append (jS T φ ∘ a) bbar) hkl ⊗ₜ[ℝ]
                oneStar _ (finrank_coker_Tphi hs))

end RoundTrip.V6_18
