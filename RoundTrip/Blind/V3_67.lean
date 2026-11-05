import Polyfold
/-! Blind formalization of V3_67 (the text's §3.8.5, Lemma 3.82, p. 144). Choices:
- Setting: the standing assumptions of §3.8.5 (Theorem 3.78), as in my blind files V3_65/V3_66,
  plain Mathlib, no universe choices: `ℝⁿ = Fin n → ℝ`, `ℝᴺ = Fin N → ℝ` (sup norms),
  `C = [0, ∞)^q ⊕ ℝ^{n−q}` (`quadC n q`, `q ≤ n`), `U` a relatively open neighbourhood of `0` in
  `C`, `f(0) = 0`, `Df(0) = L` (within `U`) onto, `K = ker L` in good position with good complement
  `Y` and good-position constant `ε` (as in V3_65; `B` holds for every such `ε`).
- "`f` of class `C^j`, `j ≥ 1`": `j : ℕ`, `1 ≤ j`, `ContDiffOn ℝ j f U`.
- `B(k, y) = y − (D₂f(0))⁻¹ f(k + y)` (`Bmap`, `K × Y → Y`, as in V3_65); `D₁B`, `D₂B` are the
  partial derivatives of `B` (the derivative within its domain `{(k, y) | k + y ∈ U}` composed with
  the inclusions `K → K × Y`, `Y → K × Y`).
- `τ` is the map of Lemmas 3.80/3.81: for some `a > 0`, `τ : K → Y` with, on `D_a = B_K(a) ∩ C`,
  `k + X_k ⊆ U`, `τ(k) ∈ X_k = B̄_Y(ε|k|)`, `B(k, τ(k)) = τ(k)`, and `τ(k)` the only fixed point of
  `B(k, ·)` in `X_k` (this pins `τ` down on `D_a`).
- "`τ` is of class `C^j` on a possibly smaller neighbourhood of `0`": a relatively open
  neighbourhood `V` of `0` in `K ∩ C` with `V ⊆ D_a` and `ContDiffOn ℝ j τ V`.
- "`Dτ(k) = (1 − D₂B(k, τ(k)))⁻¹ D₁B(k, τ(k))`" for `k ∈ V`: `1 − D₂B(k, τ(k)) : Y → Y` is a
  continuous linear automorphism `Φ` of `Y`, and the derivative of `τ` within `V` at `k` is
  `Φ⁻¹ ∘ D₁B(k, τ(k))`.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_67
open Polyfold

/-- The partial quadrant `C = [0, ∞)^q ⊕ ℝ^{n−q} ⊆ ℝⁿ`. -/
def quadC (n q : ℕ) : Set (Fin n → ℝ) := {x | ∀ i : Fin n, (i : ℕ) < q → 0 ≤ x i}

/-- The kernel of a continuous linear map, as a subspace. -/
def kerCLM {n N : ℕ} (L : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ)) : Submodule ℝ (Fin n → ℝ) :=
  LinearMap.ker (L : (Fin n → ℝ) →ₗ[ℝ] (Fin N → ℝ))

/-- `(L|_Y)⁻¹ z`: the element of `Y` mapped to `z` by `L` (junk `0` if there is none). -/
noncomputable def invY {n N : ℕ} (L : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ))
    (Y : Submodule ℝ (Fin n → ℝ)) (z : Fin N → ℝ) : Y := by
  classical
  exact if h : ∃ y : Y, L y = z then h.choose else 0

/-- The map `B(k, y) = y − (D₂f(0))⁻¹ f(k + y)`, `K × Y → Y`, with `D₂f(0) = L|_Y`. -/
noncomputable def Bmap {n N : ℕ} (f : (Fin n → ℝ) → (Fin N → ℝ))
    (L : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ)) (Y : Submodule ℝ (Fin n → ℝ))
    (p : kerCLM L × Y) : Y :=
  p.2 - invY L Y (f ((p.1 : Fin n → ℝ) + (p.2 : Fin n → ℝ)))

/-- The domain `{(k, y) ∈ K × Y | k + y ∈ U}` of `B`. -/
def domB {n N : ℕ} (L : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ)) (Y : Submodule ℝ (Fin n → ℝ))
    (U : Set (Fin n → ℝ)) : Set (kerCLM L × Y) :=
  {p | (p.1 : Fin n → ℝ) + (p.2 : Fin n → ℝ) ∈ U}

/-- `DB(p)`: the derivative of `B` at `p` within its domain. -/
noncomputable def DB {n N : ℕ} (f : (Fin n → ℝ) → (Fin N → ℝ))
    (L : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ)) (Y : Submodule ℝ (Fin n → ℝ)) (U : Set (Fin n → ℝ))
    (p : kerCLM L × Y) : kerCLM L × Y →L[ℝ] Y :=
  fderivWithin ℝ (Bmap f L Y) (domB L Y U) p

/-- The partial derivative `D₁B(p) : K → Y`. -/
noncomputable def D1B {n N : ℕ} (f : (Fin n → ℝ) → (Fin N → ℝ))
    (L : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ)) (Y : Submodule ℝ (Fin n → ℝ)) (U : Set (Fin n → ℝ))
    (p : kerCLM L × Y) : kerCLM L →L[ℝ] Y :=
  (DB f L Y U p).comp (ContinuousLinearMap.inl ℝ (kerCLM L) Y)

/-- The partial derivative `D₂B(p) : Y → Y`. -/
noncomputable def D2B {n N : ℕ} (f : (Fin n → ℝ) → (Fin N → ℝ))
    (L : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ)) (Y : Submodule ℝ (Fin n → ℝ)) (U : Set (Fin n → ℝ))
    (p : kerCLM L × Y) : Y →L[ℝ] Y :=
  (DB f L Y U p).comp (ContinuousLinearMap.inr ℝ (kerCLM L) Y)

/-- Lemma 3.82: if `f` is `C^j`, `j ≥ 1`, the fixed-point map `τ` of Lemma 3.80 is `C^j` on a
relatively open neighbourhood `V` of `0` in `K ∩ C`, with
`Dτ(k) = (1 − D₂B(k, τ(k)))⁻¹ D₁B(k, τ(k))`. -/
def B : Prop :=
  ∀ (n q N j : ℕ) (U : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → (Fin N → ℝ))
    (L : (Fin n → ℝ) →L[ℝ] (Fin N → ℝ)) (Y : Submodule ℝ (Fin n → ℝ)) (ε : ℝ),
    q ≤ n → 1 ≤ j →
    (∃ O : Set (Fin n → ℝ), IsOpen O ∧ U = O ∩ quadC n q) → 0 ∈ U →
    ContDiffOn ℝ j f U → f 0 = 0 →
    HasFDerivWithinAt f L U 0 → Function.Surjective L →
    (interior (Subtype.val ⁻¹' quadC n q : Set (kerCLM L))).Nonempty →
    IsCompl (kerCLM L) Y → 0 < ε →
    (∀ v ∈ kerCLM L, ∀ y ∈ Y, ‖y‖ ≤ ε * ‖v‖ → (v ∈ quadC n q ↔ v + y ∈ quadC n q)) →
    ∃ a : ℝ, 0 < a ∧ ∃ τ : kerCLM L → Y,
      -- `τ` is the fixed-point map of Lemma 3.80 on `B_K(a) ∩ C`
      (∀ k : kerCLM L, (k : Fin n → ℝ) ∈ quadC n q → ‖k‖ < a →
        (∀ y : Y, ‖y‖ ≤ ε * ‖k‖ → (k : Fin n → ℝ) + (y : Fin n → ℝ) ∈ U) ∧
        ‖τ k‖ ≤ ε * ‖k‖ ∧ Bmap f L Y (k, τ k) = τ k ∧
        (∀ y : Y, ‖y‖ ≤ ε * ‖k‖ → Bmap f L Y (k, y) = y → y = τ k)) ∧
      -- Lemma 3.82
      ∃ V : Set (kerCLM L),
        (∃ O : Set (kerCLM L), IsOpen O ∧ V = O ∩ (Subtype.val ⁻¹' quadC n q)) ∧
        (0 : kerCLM L) ∈ V ∧
        (∀ k ∈ V, (k : Fin n → ℝ) ∈ quadC n q ∧ ‖k‖ < a) ∧
        ContDiffOn ℝ j τ V ∧
        ∀ k ∈ V, ∃ Φ : Y ≃L[ℝ] Y,
          (Φ : Y →L[ℝ] Y) = ContinuousLinearMap.id ℝ Y - D2B f L Y U (k, τ k) ∧
          fderivWithin ℝ τ V k = (Φ.symm : Y →L[ℝ] Y).comp (D1B f L Y U (k, τ k))

end RoundTrip.V3_67
