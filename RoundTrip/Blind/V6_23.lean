import Polyfold
/-! Blind formalization of V6_23 (the text's §6.4, Lemma 6.21, p. 216). Choices:
- Hypotheses: `(T, P, ε)` and `(T, Q, ε)` both admissible (so `DET(T, P, ε)` and `DET(T, Q, ε)`
  are defined, with the same `ε`), and `Q ≤ P` (the project's `ProjLE Q P`, checked with
  `#print`: `Q = QP` and `Q = PQ`, so `R(Q) ⊆ R(P)`; the vocabulary's reading of the text's
  order, and the only one under which `γ^Q_{PS}` is defined: `R(QPS) = R(QS) = R(Q)`).
- `γ^Q_{PS} : det(PS) → det(QPS)` needs `PS` Fredholm and `Q ∈ Π_{PS}`, and `det(QPS) = det(QS)`
  uses `QP = Q`; the text presupposes these.  B asserts them (`∃ hF hQ hQP`, proofs only) and then
  that `(S, h) ↦ (S, γ^Q_{PS}(h))` is a homeomorphism `DET(T, P, ε) → DET(T, Q, ε)` for the
  natural topologies.  It covers the identity of the ball and is a linear isomorphism on every
  fibre by construction, so this is "topological line bundle isomorphism".
- The proof sketch (extending kernel frames) is not part of the claim.
- Setting: real Banach spaces `E F : Type` (universe 0); `L(E, F)` with the operator norm; the
  ball `{‖S − T‖ < ε}` is `Metric.ball T ε` with the subspace topology.  Fredholm is Mathlib's
  `ContinuousLinearMap.IsFredholm` (for Banach spaces the text's notion).
- `DET(T, P, ε)` is "defined" for the admissible triples `IsDetChart T P ε`: `T` Fredholm,
  `P ∈ Π_T`, `ε > 0`, and for some topological complement `Y` of `ker(PT)` (Mathlib's
  `Submodule.IsTopCompl`) the conclusions of Lemma 6.17 hold on the ball (`P ∈ Π_S`, and
  `y ↦ PSy` is a topological isomorphism `Y ≅ R(P)`).  Every such `ε` is allowed, not only the
  one produced by the proof of Lemma 6.17.  (These conditions imply that every `S` of the ball is
  Fredholm; I do not add this as a hypothesis.)
- "In a natural way" (Lemma 6.19 applied to the trivial kernel bundle of Lemma 6.18 and the
  constant cokernel bundle `F/R(PS) = F/R(P)`): I define the natural topology of
  `DET(T, P, ε) = ⋃ {S} × det(PS)` myself, as the final topology of all frame maps
  `U × ℝ → DET(T, P, ε)`, `(S, t) ↦ (S, t (σ₁(S) ∧ … ∧ σₙ(S)) ⊗ ([f₁(S)] ∧ … ∧ [f_l(S)])*)`,
  for `U` open in the ball, `σᵢ : U → E` continuous with `σ(S)` a basis of `ker(PS)` (a continuous
  local frame of the kernel bundle, whose topology is that of `⋃ {S} × ker(PS) ⊆ L(E,F) × E`),
  and `fⱼ : U → F` continuous with classes a basis of `F/R(PS)`.  These are the trivializations
  induced, as in Lemma 6.19, by local trivializations of the two bundles.  (A set is open iff its
  preimage under every frame map is open.)
- Project definitions used (checked with `#print`): `fredholmDet T = λ(ker T) ⊗ λ*(F ⧸ R(T))`,
  `maxPow` (`λ`, top exterior power), `maxPowDual` (`λ*`), `wedge` (`v₁ ∧ … ∧ vₖ`), `dualVec`
  (`v ↦ v*`, `v*(v) = 1`), `IsGoodLeftProj` (`Π_T`: `P² = P`, `dim F/R(P) < ∞`,
  `R(PT) = R(P)`).
- `γ^P_T : det(T) → det(PT)` is the project's `gammaProj` (only its type was checked; its
  docstring: `Φ_{E(T,P)}` of the exact sequence `E(T,P)` followed by `λ*(F/R(P)) = λ*(F/R(PT))`).
  I did not re-derive this map; I take it to be the text's `γ^P_T`.
- Nothing looks false to me.
-/
namespace RoundTrip.V6_23
open Polyfold Bundle

noncomputable section

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- `ker(PS)`. -/
abbrev kerPS (P : F →L[ℝ] F) (S : E →L[ℝ] F) : Submodule ℝ E :=
  LinearMap.ker ((P.comp S : E →L[ℝ] F) : E →ₗ[ℝ] F)

/-- `coker(PS) = F ⧸ R(PS)`. -/
abbrev cokPS (P : F →L[ℝ] F) (S : E →L[ℝ] F) : Type :=
  F ⧸ LinearMap.range ((P.comp S : E →L[ℝ] F) : E →ₗ[ℝ] F)

/-- `(T, P, ε)` is admissible, i.e. `DET(T, P, ε)` is defined: `T` Fredholm, `P ∈ Π_T`, `ε > 0`,
and the conclusions of Lemma 6.17 hold on the ball `‖S − T‖ < ε` for some topological complement
`Y` of `ker(PT)`: `P ∈ Π_S`, and `y ↦ PSy` is a topological isomorphism `Y ≅ R(P)`. -/
def IsDetChart (T : E →L[ℝ] F) (P : F →L[ℝ] F) (ε : ℝ) : Prop :=
  T.IsFredholm ∧ IsGoodLeftProj T P ∧ 0 < ε ∧
  (∀ S : E →L[ℝ] F, ‖S - T‖ < ε → IsGoodLeftProj S P) ∧
  ∃ Y : Submodule ℝ E, Submodule.IsTopCompl (kerPS P T) Y ∧
    ∀ S : E →L[ℝ] F, ‖S - T‖ < ε →
      ∃ e : Y ≃L[ℝ] LinearMap.range (P : F →ₗ[ℝ] F), ∀ y : Y, (e y : F) = P (S y)

/-- The fibre `det(PS)` of `DET(T, P, ε) = ⋃_{‖S−T‖<ε} {S} × det(PS)`. -/
abbrev LD (T : E →L[ℝ] F) (P : F →L[ℝ] F) (ε : ℝ) (S : Metric.ball T ε) : Type :=
  fredholmDet (P.comp (S : E →L[ℝ] F))

/-- A continuous local frame of the kernel bundle `⋃ {S} × ker(PS)` over `U ⊆ L(E, F)`:
continuous `σ₁, …, σₙ : U → E` forming a basis of `ker(PS)` at every `S ∈ U`. -/
structure KerFrame (P : F →L[ℝ] F) (U : Set (E →L[ℝ] F)) where
  n : ℕ
  σ : U → Fin n → E
  cont : Continuous σ
  mem : ∀ (S : U) (i : Fin n), σ S i ∈ kerPS P (S : E →L[ℝ] F)
  li : ∀ S : U, LinearIndependent ℝ (σ S)
  card : ∀ S : U, n = Module.finrank ℝ (kerPS P (S : E →L[ℝ] F))

/-- `σ₁(S) ∧ … ∧ σₙ(S) ∈ λ(ker(PS))`. -/
def KerFrame.wedgeAt {P : F →L[ℝ] F} {U : Set (E →L[ℝ] F)} (k : KerFrame P U) (S : U) :
    ↥(maxPow (kerPS P (S : E →L[ℝ] F))) :=
  wedge (fun i => (⟨k.σ S i, k.mem S i⟩ : kerPS P (S : E →L[ℝ] F))) (k.card S)

/-- A continuous local frame of the cokernel bundle `⋃ {S} × coker(PS)` over `U`: continuous
`f₁, …, f_l : U → F` whose classes form a basis of `F ⧸ R(PS)` at every `S ∈ U`. -/
structure CokFrame (P : F →L[ℝ] F) (U : Set (E →L[ℝ] F)) where
  l : ℕ
  f : U → Fin l → F
  cont : Continuous f
  li : ∀ S : U, LinearIndependent ℝ
    (fun j => (Submodule.Quotient.mk (f S j) : cokPS P (S : E →L[ℝ] F)))
  card : ∀ S : U, l = Module.finrank ℝ (cokPS P (S : E →L[ℝ] F))

/-- `([f₁(S)] ∧ … ∧ [f_l(S)])* ∈ λ*(coker(PS))`. -/
def CokFrame.dualAt {P : F →L[ℝ] F} {U : Set (E →L[ℝ] F)} (c : CokFrame P U) (S : U) :
    maxPowDual (cokPS P (S : E →L[ℝ] F)) :=
  dualVec (wedge (fun j => (Submodule.Quotient.mk (c.f S j) : cokPS P (S : E →L[ℝ] F))) (c.card S))

/-- Open subsets `U` of the ball `‖S − T‖ < ε` (as subsets of `L(E, F)`). -/
def OpenSub (T : E →L[ℝ] F) (ε : ℝ) : Type :=
  {U : Set (E →L[ℝ] F) // IsOpen U ∧ U ⊆ Metric.ball T ε}

/-- The frame map `U × ℝ → ⋃ {S} × Fib(S)`, `(S, t) ↦ (S, t s(S))` of a section `s` over `U`. -/
def frameMap {T : E →L[ℝ] F} {ε : ℝ} {Fib : Metric.ball T ε → Type}
    [∀ S, AddCommGroup (Fib S)] [∀ S, Module ℝ (Fib S)]
    (U : OpenSub T ε) (s : ∀ S : U.1, Fib ⟨S.1, U.2.2 S.2⟩) : U.1 × ℝ → TotalSpace ℝ Fib :=
  fun p => ⟨⟨p.1.1, U.2.2 p.1.2⟩, p.2 • s p.1⟩

/-- The natural topology of `DET(T, P, ε)` (Lemma 6.19 / Proposition 6.20): the final topology of
the frame maps `(S, t) ↦ (S, t (σ₁(S) ∧ … ∧ σₙ(S)) ⊗ ([f₁(S)] ∧ … ∧ [f_l(S)])*)` of all pairs of
continuous local frames `σ` of `ker(PS)` and `f` of `coker(PS)` over a common open `U`. -/
@[instance_reducible] def natTopD (T : E →L[ℝ] F) (P : F →L[ℝ] F) (ε : ℝ) :
    TopologicalSpace (TotalSpace ℝ (LD T P ε)) :=
  ⨆ i : (Σ U : OpenSub T ε, KerFrame P U.1 × CokFrame P U.1),
    TopologicalSpace.coinduced (frameMap (Fib := LD T P ε) i.1
      (fun S => i.2.1.wedgeAt S ⊗ₜ[ℝ] i.2.2.dualAt S)) inferInstance

/-- `det(A) = det(B)` for `A = B`. -/
def detCast {A B : E →L[ℝ] F} (h : A = B) : fredholmDet A ≃ₗ[ℝ] fredholmDet B :=
  Eq.rec (motive := fun X _ => fredholmDet A ≃ₗ[ℝ] fredholmDet X) (LinearEquiv.refl ℝ _) h

/-- The map `(S, h) ↦ (S, γ^Q_{PS}(h))`, `DET(T, P, ε) → DET(T, Q, ε)`, where
`γ^Q_{PS} : det(PS) → det(QPS) = det(QS)`. -/
def gammaQP {T : E →L[ℝ] F} {P Q : F →L[ℝ] F} {ε : ℝ}
    (hF : ∀ S : Metric.ball T ε, (P.comp (S : E →L[ℝ] F)).IsFredholm)
    (hQ : ∀ S : Metric.ball T ε, IsGoodLeftProj (P.comp (S : E →L[ℝ] F)) Q)
    (hQP : ∀ S : Metric.ball T ε, Q.comp (P.comp (S : E →L[ℝ] F)) = Q.comp (S : E →L[ℝ] F)) :
    TotalSpace ℝ (LD T P ε) → TotalSpace ℝ (LD T Q ε) :=
  fun p => ⟨p.proj, detCast (hQP p.proj) (gammaProj (hF p.proj) (hQ p.proj) p.2)⟩

/-- Lemma 6.21: for `Q ≤ P` in `Π_T`, `(S, h) ↦ (S, γ^Q_{PS}(h))` is an isomorphism of
topological line bundles `DET(T, P, ε) → DET(T, Q, ε)`. -/
def B : Prop :=
  ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (T : E →L[ℝ] F) (P Q : F →L[ℝ] F) (ε : ℝ),
    IsDetChart T P ε → IsDetChart T Q ε → ProjLE Q P →
    ∃ (hF : ∀ S : Metric.ball T ε, (P.comp (S : E →L[ℝ] F)).IsFredholm)
      (hQ : ∀ S : Metric.ball T ε, IsGoodLeftProj (P.comp (S : E →L[ℝ] F)) Q)
      (hQP : ∀ S : Metric.ball T ε,
        Q.comp (P.comp (S : E →L[ℝ] F)) = Q.comp (S : E →L[ℝ] F)),
      @IsHomeomorph _ _ (natTopD T P ε) (natTopD T Q ε) (gammaQP hF hQ hQP)

end

end RoundTrip.V6_23
