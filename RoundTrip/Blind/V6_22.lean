import Polyfold
/-! Blind formalization of V6_22 (the text's §6.4, Lemma 6.19 and Proposition 6.20, p. 216). Choices:
- Claim (Lemma 6.19 "in the case used" and Proposition 6.20): for every admissible `(T, P, ε)`,
  the bundles `⋃ {S} × λ(ker(PS))`, `⋃ {S} × λ*(coker(PS))` (Lemma 6.19 for `λ` of the kernel
  bundle and `λ*` of the cokernel bundle) and `DET(T, P, ε) = ⋃ {S} × det(PS)` (their tensor
  product, Proposition 6.20), each with its natural topology (final topology of its natural
  frames: wedges of kernel frames, duals of wedges of cokernel frames, and their tensor
  products), are topological line bundles.  The general Lemma 6.19 (arbitrary finite-dimensional
  bundles, also `E ⊕ F`) is not claimed; only the case used.
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
- "topological line bundle": `IsLineBundle` below (every base point lies in the base set of a
  Mathlib `Trivialization` with fibre `ℝ` that is fibrewise linear for the given linear
  structure of the fibres).  No topology on the individual fibres is involved.
- Nothing looks false to me.
-/
namespace RoundTrip.V6_22
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

/-- The fibre `λ(ker(PS))` of the bundle `λ(⋃ {S} × ker(PS))` over the ball. -/
abbrev LK (T : E →L[ℝ] F) (P : F →L[ℝ] F) (ε : ℝ) (S : Metric.ball T ε) : Type :=
  ↥(maxPow (kerPS P (S : E →L[ℝ] F)))

/-- The fibre `λ*(coker(PS))` of the bundle `λ*(⋃ {S} × coker(PS))` over the ball. -/
abbrev LC (T : E →L[ℝ] F) (P : F →L[ℝ] F) (ε : ℝ) (S : Metric.ball T ε) : Type :=
  maxPowDual (cokPS P (S : E →L[ℝ] F))

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

/-- The natural topology of `λ(ker(PS))` over the ball (Lemma 6.19 for the kernel bundle of
Lemma 6.18): the final topology of the frame maps `(S, t) ↦ (S, t σ₁(S) ∧ … ∧ σₙ(S))` of all
continuous local frames `σ` of `ker(PS)`. -/
@[instance_reducible] def natTopK (T : E →L[ℝ] F) (P : F →L[ℝ] F) (ε : ℝ) :
    TopologicalSpace (TotalSpace ℝ (LK T P ε)) :=
  ⨆ i : (Σ U : OpenSub T ε, KerFrame P U.1),
    TopologicalSpace.coinduced (frameMap (Fib := LK T P ε) i.1 (fun S => i.2.wedgeAt S))
      inferInstance

/-- The natural topology of `λ*(coker(PS))` over the ball: the final topology of the frame maps
`(S, t) ↦ (S, t ([f₁(S)] ∧ … ∧ [f_l(S)])*)` of all continuous local frames `f`. -/
@[instance_reducible] def natTopC (T : E →L[ℝ] F) (P : F →L[ℝ] F) (ε : ℝ) :
    TopologicalSpace (TotalSpace ℝ (LC T P ε)) :=
  ⨆ i : (Σ U : OpenSub T ε, CokFrame P U.1),
    TopologicalSpace.coinduced (frameMap (Fib := LC T P ε) i.1 (fun S => i.2.dualAt S))
      inferInstance

/-- The natural topology of `DET(T, P, ε)` (Lemma 6.19 / Proposition 6.20): the final topology of
the frame maps `(S, t) ↦ (S, t (σ₁(S) ∧ … ∧ σₙ(S)) ⊗ ([f₁(S)] ∧ … ∧ [f_l(S)])*)` of all pairs of
continuous local frames `σ` of `ker(PS)` and `f` of `coker(PS)` over a common open `U`. -/
@[instance_reducible] def natTopD (T : E →L[ℝ] F) (P : F →L[ℝ] F) (ε : ℝ) :
    TopologicalSpace (TotalSpace ℝ (LD T P ε)) :=
  ⨆ i : (Σ U : OpenSub T ε, KerFrame P U.1 × CokFrame P U.1),
    TopologicalSpace.coinduced (frameMap (Fib := LD T P ε) i.1
      (fun S => i.2.1.wedgeAt S ⊗ₜ[ℝ] i.2.2.dualAt S)) inferInstance

/-- A topology on `⋃ₓ {x} × Fib(x)` (fibres with their given linear structure) makes it a
topological line bundle: every point of the base lies in the base set of a fibrewise linear local
trivialization with fibre `ℝ`. -/
def IsLineBundle {X : Type} [TopologicalSpace X] (Fib : X → Type) [∀ x, AddCommGroup (Fib x)]
    [∀ x, Module ℝ (Fib x)] (τ : TopologicalSpace (TotalSpace ℝ Fib)) : Prop :=
  letI := τ
  ∀ x : X, ∃ e : Trivialization ℝ (TotalSpace.proj : TotalSpace ℝ Fib → X),
    x ∈ e.baseSet ∧ e.IsLinear ℝ

/-- Lemma 6.19 (case used) and Proposition 6.20: `λ(ker(PS))`, `λ*(coker(PS))` and
`DET(T, P, ε)` are, with their natural topologies, topological line bundles over the ball. -/
def B : Prop :=
  ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (T : E →L[ℝ] F) (P : F →L[ℝ] F) (ε : ℝ), IsDetChart T P ε →
    IsLineBundle (LK T P ε) (natTopK T P ε) ∧ IsLineBundle (LC T P ε) (natTopC T P ε) ∧
    IsLineBundle (LD T P ε) (natTopD T P ε)

end

end RoundTrip.V6_22
