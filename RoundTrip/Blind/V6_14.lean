import Polyfold
/-! Blind formalization of V6_14 (the text's §6.3, Proposition 6.12, p. 211; proof §6.7.2,
pp. 235–237).

Text: for a Fredholm `T` and `Q, P ∈ Π_T` with `P ≤ Q`, `QT` is Fredholm, `P ∈ Π_{QT}`, and
`γ^P_{QT} ∘ γ^Q_T = γ^P_T`.

Choices:
- Setting and prelude as in the blind V6_13 (copied): real Banach spaces `E F : Type`,
  `T : E →L[ℝ] F` Fredholm in the classical sense (`IsFredholmOp`), `IsGLP` and the order
  `PLe P Q := P = P ∘L Q ∧ P = Q ∘L P` written out, and `IsGamma T P g`: `g : det(T) → det(PT)` is
  `γ^P_T`, i.e. `Φ_{E(T,P)}` of (91) for every choice (see the header of V6_13; determinant lines
  via the project's `maxPow`, `maxPowDual`, `wedge`, `dualVec`, `fredholmDet`, checked with
  `#print`).
- The maps `γ^Q_T`, `γ^P_{QT}`, `γ^P_T` are quantified universally among the linear maps with
  the defining property (91); by V6_13 such maps exist, and they are unique.
- Types: `γ^P_{QT}` lands in `det(P ∘ (Q ∘ T))`, `γ^P_T` in `det(P ∘ T)`.  These operators are
  equal (`PQ = P`) but not syntactically, so the composite is followed by the canonical
  identification `det(P(QT)) ≅ det(PT)` of equal operators, the project's `linDetEquivOfEq`
  (checked with `#print`: `λ` of the equality `ker = ker` tensor `λ*` of `F/R = F/R`).
- `P ∈ Π_{QT}` is `IsGLP (Q ∘L T) P`.
- Nothing in the statement looks false to me.  (A numerical check outside Lean, on random
  finite-dimensional `T`, `P ≤ Q` with `ker QT ⊋ ker T` in most cases, computing `γ` by (91)
  with random choices, found `γ` independent of the choices and the composition law exact with
  these order conventions.)
-/
namespace RoundTrip.V6_14
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

section Proj
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- Definition 6.9: `P` is a good left-projection for `T`: a bounded projection of `F` with
(1) `dim F/R(P) < ∞` and (2) `R(P ∘ T) = R(P)`. -/
def IsGLP (T : E →L[ℝ] F) (P : F →L[ℝ] F) : Prop :=
  P ∘L P = P ∧ FiniteDimensional ℝ (F ⧸ LinearMap.range (P : F →ₗ[ℝ] F)) ∧
    LinearMap.range ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F) = LinearMap.range (P : F →ₗ[ℝ] F)

/-- The order `P ≤ Q` iff `P = PQ = QP`. -/
def PLe (P Q : F →L[ℝ] F) : Prop := P = P ∘L Q ∧ P = Q ∘L P

/-- `j^P_T : ker T → ker(PT)`, the inclusion. -/
def jMap (T : E →L[ℝ] F) (P : F →L[ℝ] F) :
    LinearMap.ker (T : E →ₗ[ℝ] F) →ₗ[ℝ] LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F) :=
  Submodule.inclusion (fun x hx => by
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx ⊢
    simp [hx])

/-- `g : det(T) → det(PT)` is `Φ_{E(T,P)}` of (91) (followed by `λ*(F/R(P)) = λ*(F/R(PT))`):
for every choice `a`, `d`, `b'`, `c_i = f_i + R(P)` of (91) for `E(T, P)`,
`g((a₁ ∧ … ∧ aₙ) ⊗ (d₁ ∧ … ∧ d_l)*) = (j a ∧ b') ⊗ (c ∧ Φ(b'))*`. -/
def IsGamma (T : E →L[ℝ] F) (P : F →L[ℝ] F)
    (g : fredholmDet T →ₗ[ℝ] fredholmDet (P ∘L T)) : Prop :=
  ∀ (n l j : ℕ) (a : Fin n → LinearMap.ker (T : E →ₗ[ℝ] F))
    (d : Fin l → F ⧸ LinearMap.range (T : E →ₗ[ℝ] F))
    (b' : Fin j → LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)) (f : Fin l → F)
    (hA : n = Module.finrank ℝ (LinearMap.ker (T : E →ₗ[ℝ] F)))
    (hD : l = Module.finrank ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)))
    (hB : n + j = Module.finrank ℝ (LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)))
    (hC : l + j = Module.finrank ℝ (F ⧸ LinearMap.range ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F))),
    LinearIndependent ℝ a → LinearIndependent ℝ d →
    LinearIndependent ℝ (Fin.append (jMap T P ∘ a) b') →
    (∀ i, (LinearMap.range (T : E →ₗ[ℝ] F)).mkQ (f i - P (f i)) = d i) →
    g (wedge a hA ⊗ₜ[ℝ] dualVec (wedge d hD)) =
      wedge (Fin.append (jMap T P ∘ a) b') hB ⊗ₜ[ℝ]
        dualVec (wedge (Fin.append
          (fun i => (LinearMap.range ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)).mkQ (f i))
          (fun k => (LinearMap.range ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)).mkQ
            (T (b' k : E)))) hC)

end Proj

/-- Proposition 6.12: for a Fredholm `T` and `P ≤ Q` in `Π_T`, `QT` is Fredholm, `P ∈ Π_{QT}`,
and `γ^P_{QT} ∘ γ^Q_T = γ^P_T` (up to `det(P(QT)) = det(PT)`). -/
def B : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (T : E →L[ℝ] F),
    IsFredholmOp T → ∀ Q P : F →L[ℝ] F, IsGLP T Q → IsGLP T P → ∀ hle : PLe P Q,
      IsFredholmOp (Q ∘L T) ∧ IsGLP (Q ∘L T) P ∧
      ∀ (γQT : fredholmDet T →ₗ[ℝ] fredholmDet (Q ∘L T))
        (γPQT : fredholmDet (Q ∘L T) →ₗ[ℝ] fredholmDet (P ∘L (Q ∘L T)))
        (γPT : fredholmDet T →ₗ[ℝ] fredholmDet (P ∘L T)),
        IsGamma T Q γQT → IsGamma (Q ∘L T) P γPQT → IsGamma T P γPT →
          (linDetEquivOfEq
              (show ((P ∘L (Q ∘L T) : E →L[ℝ] F) : E →ₗ[ℝ] F) = ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)
                by rw [← ContinuousLinearMap.comp_assoc, ← hle.1])).toLinearMap ∘ₗ
            γPQT ∘ₗ γQT = γPT

end RoundTrip.V6_14
