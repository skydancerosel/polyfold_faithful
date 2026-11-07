import Polyfold
/-! Blind formalization of V6_13 (the text's §6.3, p. 210).

Text: from `E(T, P)`, "recalling `R(P) = R(PT)`", `Φ_{E(T,P)}` is an isomorphism
`det(T) → det(PT)`, renamed `γ^P_T`.

Choices:
- Setting and prelude as in the blind V6_10/V6_12: real Banach spaces `E F : Type`,
  `T : E →L[ℝ] F` Fredholm in the classical sense (`IsFredholmOp`), `IsGLP` written out, and the
  inclusion `jMap : ker T → ker(PT)` of V6_12.
- Determinant lines: the project's `maxPow` (`λ(V) = ⋀^{dim V} V`), `maxPowDual`
  (`λ*(V) = λ(V)*`), `wedge` (`v₁ ∧ … ∧ v_k`, `k = dim V`), `dualVec` (`v*` with `v*(v) = 1` in a
  line) and `fredholmDet` (`det(T) = λ(ker T) ⊗ λ*(F ⧸ R(T))`), all checked with `#print`.
- `Φ_E` (formula (91), well defined by Lemma 6.5) is characterized by its values: `IsGamma T P g`
  says that for EVERY choice of (91) for `E(T, P)` the map `g` sends
  `(a₁ ∧ … ∧ aₙ) ⊗ (d₁ ∧ … ∧ d_l)*` to `(j a₁ ∧ … ∧ j aₙ ∧ b'₁ ∧ … ∧ b'ⱼ) ⊗ (c₁ ∧ … ∧ c_l ∧
  c'₁ ∧ … ∧ c'ⱼ)*`, `c'_k = Φ(b'_k)` (the order conventions of (91): `b'` after `j(a)`, `c'` after
  `c`).  A choice: `a` a basis of `ker T`; `d` a basis of `coker T`; `b'` completing `j(a)` to a
  basis of `ker(PT)` (i.e. `Z = span b'` with basis `b'`); `c_i ∈ F/R(P)` with `π(c_i) = d_i`.
  Every `c_i` is written `f_i + R(P)` with `f_i ∈ F`, and `π(c_i) = d_i` reads
  `(f_i − P f_i) + R(T) = d_i`.  The text takes `c_i` in a complement `V` of `Φ(ker PT)`; any
  family with `π(c) = d` spans such a complement, so nothing is lost.
- "Recalling `R(P) = R(PT)`": the cosets `c_i = f_i + R(P)` and `c'_k = T b'_k + R(P)` are read as
  the same cosets `f_i + R(PT)`, `T b'_k + R(PT)` of `F ⧸ R(PT)`, so the value lies in
  `det(PT) = λ(ker PT) ⊗ λ*(F/R(PT))`.  This is `Φ_{E(T,P)}` followed by the identification
  `λ*(F/R(P)) = λ*(F/R(PT))` induced by the identity of `F`.
- `B`: for Fredholm `T` and `P ∈ Π_T` there is a linear isomorphism `det(T) ≃ det(PT)` with this
  property (it is then unique: `det(T)` is a line spanned by the source vector of any choice).
  The project's `gammaProj`, `projSeq`, `FourTermExact.phi` are not used.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V6_13
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

/-- §6.3, p. 210: for a Fredholm `T` and `P ∈ Π_T`, `Φ_{E(T,P)}` is an isomorphism
`γ^P_T : det(T) → det(PT)`. -/
def B : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (T : E →L[ℝ] F),
    IsFredholmOp T → ∀ P : F →L[ℝ] F, IsGLP T P →
      ∃ γ : fredholmDet T ≃ₗ[ℝ] fredholmDet (P ∘L T), IsGamma T P γ.toLinearMap

end RoundTrip.V6_13
