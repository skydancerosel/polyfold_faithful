import Polyfold
/-! Blind formalization of V6_15 (the text's §6.3, Corollary 6.13, p. 211).

Text: for `P, R, S ∈ Π_T` with `P ≤ R` and `P ≤ S`, the map
`h ↦ (γ^P_{RT})⁻¹ ∘ γ^P_{ST}(h)`, `det(ST) → det(RT)`, does not depend on `P`, and it equals
`γ^R_T ∘ (γ^S_T)⁻¹`.

Choices:
- Setting and prelude as in the blind V6_13/V6_14 (copied): real Banach spaces `E F : Type`,
  `T : E →L[ℝ] F` Fredholm in the classical sense (`IsFredholmOp`), `IsGLP`, the order `PLe`,
  and `IsGamma T P g` (`g` is `γ^P_T = Φ_{E(T,P)}`, characterized by (91) for every choice; see
  the header of V6_13; determinant lines via the project's `maxPow`, `maxPowDual`, `wedge`,
  `dualVec`, `fredholmDet`, checked with `#print`).
- The `γ`'s are quantified universally among the maps with the defining property; those that are
  inverted (`γ^P_{RT}`, `γ^S_T`) are taken as linear equivalences (V6_13 says they are
  isomorphisms; they exist and are unique).  `γ^P_{ST}` and `γ^P_{RT}` presuppose
  `P ∈ Π_{ST}`, `P ∈ Π_{RT}` (Proposition 6.12); `IsGamma` itself needs no such hypothesis.
- `γ^P_{ST}` lands in `det(P(ST))` and `(γ^P_{RT})⁻¹` starts from `det(P(RT))`; both operators
  equal `PT` (`PS = P = PR`) but not syntactically, so the canonical identification of the
  determinants of equal operators, the project's `linDetEquivOfEq` (checked with `#print`), is
  inserted between them (`corMap`).
- "Does not depend on `P`": for two such `P₁`, `P₂` (each `≤ R` and `≤ S`) the two maps agree.
  `B` is the conjunction of this and the formula (the first follows from the second).
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V6_15
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

section Cor
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The map `h ↦ (γ^P_{RT})⁻¹(γ^P_{ST}(h))`, `det(ST) → det(RT)`, with the identification
`det(P(ST)) = det(P(RT))` of equal operators in between. -/
noncomputable def corMap (T : E →L[ℝ] F) {P R S : F →L[ℝ] F} (hR : PLe P R) (hS : PLe P S)
    (γPRT : fredholmDet (R ∘L T) ≃ₗ[ℝ] fredholmDet (P ∘L (R ∘L T)))
    (γPST : fredholmDet (S ∘L T) →ₗ[ℝ] fredholmDet (P ∘L (S ∘L T))) :
    fredholmDet (S ∘L T) →ₗ[ℝ] fredholmDet (R ∘L T) :=
  γPRT.symm.toLinearMap ∘ₗ
    (linDetEquivOfEq
      (show ((P ∘L (S ∘L T) : E →L[ℝ] F) : E →ₗ[ℝ] F) =
          ((P ∘L (R ∘L T) : E →L[ℝ] F) : E →ₗ[ℝ] F) by
        rw [← ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc, ← hS.1,
          ← hR.1])).toLinearMap ∘ₗ γPST

end Cor

/-- Corollary 6.13: for `P ≤ R`, `P ≤ S` in `Π_T`, `(γ^P_{RT})⁻¹ ∘ γ^P_{ST} : det(ST) → det(RT)`
does not depend on `P` and equals `γ^R_T ∘ (γ^S_T)⁻¹`. -/
def B : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (T : E →L[ℝ] F),
    IsFredholmOp T →
      -- the map does not depend on `P`
      (∀ P₁ P₂ R S : F →L[ℝ] F, IsGLP T P₁ → IsGLP T P₂ → IsGLP T R → IsGLP T S →
        ∀ (hR₁ : PLe P₁ R) (hS₁ : PLe P₁ S) (hR₂ : PLe P₂ R) (hS₂ : PLe P₂ S)
          (γ₁PRT : fredholmDet (R ∘L T) ≃ₗ[ℝ] fredholmDet (P₁ ∘L (R ∘L T)))
          (γ₁PST : fredholmDet (S ∘L T) →ₗ[ℝ] fredholmDet (P₁ ∘L (S ∘L T)))
          (γ₂PRT : fredholmDet (R ∘L T) ≃ₗ[ℝ] fredholmDet (P₂ ∘L (R ∘L T)))
          (γ₂PST : fredholmDet (S ∘L T) →ₗ[ℝ] fredholmDet (P₂ ∘L (S ∘L T))),
          IsGamma (R ∘L T) P₁ γ₁PRT.toLinearMap → IsGamma (S ∘L T) P₁ γ₁PST →
          IsGamma (R ∘L T) P₂ γ₂PRT.toLinearMap → IsGamma (S ∘L T) P₂ γ₂PST →
            corMap T hR₁ hS₁ γ₁PRT γ₁PST = corMap T hR₂ hS₂ γ₂PRT γ₂PST) ∧
      -- and it equals `γ^R_T ∘ (γ^S_T)⁻¹`
      (∀ P R S : F →L[ℝ] F, IsGLP T P → IsGLP T R → IsGLP T S →
        ∀ (hR : PLe P R) (hS : PLe P S)
          (γPRT : fredholmDet (R ∘L T) ≃ₗ[ℝ] fredholmDet (P ∘L (R ∘L T)))
          (γPST : fredholmDet (S ∘L T) →ₗ[ℝ] fredholmDet (P ∘L (S ∘L T)))
          (γRT : fredholmDet T →ₗ[ℝ] fredholmDet (R ∘L T))
          (γST : fredholmDet T ≃ₗ[ℝ] fredholmDet (S ∘L T)),
          IsGamma (R ∘L T) P γPRT.toLinearMap → IsGamma (S ∘L T) P γPST →
          IsGamma T R γRT → IsGamma T S γST.toLinearMap →
            corMap T hR hS γPRT γPST = γRT ∘ₗ γST.symm.toLinearMap)

end RoundTrip.V6_15
