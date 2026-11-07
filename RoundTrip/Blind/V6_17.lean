import Polyfold
/-! Blind formalization of V6_17 (the text's §6.3, formula (94), p. 212).

Text: `ψ((e₁ ∧ … ∧ eₙ)*) = 1*` for the standard basis; then
`ψ((c₁ ∧ … ∧ cₙ)*) = det([c₁, …, cₙ])⁻¹ 1*` for every basis `c` of `ℝⁿ`.

Choices:
- Setting: `ℝⁿ = Fin n → ℝ`, `e` its standard basis (`Pi.basisFun`).  `{0}` is any real vector
  space `Z : Type` with `[Subsingleton Z]` (in the text it is `F/R(T_φ) = {0}`, see V6_18).
- Determinant lines: the project's `maxPow` (`λ(V) = ⋀^{dim V} V`), `maxPowDual`
  (`λ*(V) = λ(V)*`), `wedge` (`v₁ ∧ … ∧ v_k`, `k = dim V`) and `dualVec` (`v*` with `v*(v) = 1`
  in a line), checked with `#print`.  `1 ∈ λ({0}) = ⋀⁰{0} = ℝ` is the wedge of the empty
  family (the unit of the exterior algebra), `1* = dualVec 1` (`oneStar`).
- `ψ : λ*(ℝⁿ) → λ*({0})` is the linear map defined by `ψ((e₁ ∧ … ∧ eₙ)*) = 1*` (`IsPsi`).  The
  text calls it an isomorphism; `B` says (a) a linear isomorphism with this property exists and
  (b) every linear map with this property satisfies the second formula.
- "a basis `c` of `ℝⁿ`": `n` linearly independent vectors `c : Fin n → ℝⁿ`; `[c₁, …, cₙ]` is the
  matrix with columns `cⱼ` (entry `(i, j)` is `cⱼ i`).
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V6_17
open Polyfold

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

/-- Formula (94): the isomorphism `ψ : λ*(ℝⁿ) → λ*({0})` with `ψ((e₁ ∧ … ∧ eₙ)*) = 1*` exists,
and it maps `(c₁ ∧ … ∧ cₙ)*` to `det([c₁, …, cₙ])⁻¹ 1*` for every basis `c` of `ℝⁿ`. -/
def B : Prop :=
  ∀ (n : ℕ) (Z : Type) [AddCommGroup Z] [Module ℝ Z] [Subsingleton Z],
    (∃ ψ : maxPowDual (Fin n → ℝ) ≃ₗ[ℝ] maxPowDual Z,
      IsPsi (Module.finrank_zero_of_subsingleton (R := ℝ) (M := Z)).symm ψ.toLinearMap) ∧
    ∀ ψ : maxPowDual (Fin n → ℝ) →ₗ[ℝ] maxPowDual Z,
      IsPsi (Module.finrank_zero_of_subsingleton (R := ℝ) (M := Z)).symm ψ →
      ∀ c : Fin n → (Fin n → ℝ), LinearIndependent ℝ c →
        ψ (dualVec (wedge c (Module.finrank_fin_fun ℝ).symm)) =
          (Matrix.det (Matrix.of fun i j => c j i))⁻¹ •
            oneStar Z (Module.finrank_zero_of_subsingleton (R := ℝ) (M := Z)).symm

end RoundTrip.V6_17
