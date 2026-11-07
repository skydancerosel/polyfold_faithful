import Polyfold
/-! Blind formalization of V6_40 (the text's §6.3, formula (94), p. 212, as it is used on
pp. 223–226).

Text: the orientations carried by `Φ_{E_t}` along `t`, and those of the bundles `L̃_τ` along `τ`,
are used as varying continuously with the parameter (Lemmas 6.33, 6.34 and the homotopy argument
before Theorem 6.35).

Choices:
- Reading: the principle the text uses is that the stabilization isomorphism `Φ_E` (of the exact
  sequence `0 → ker T → ker(T ⊕ φ) → ℝᵏ → coker T → 0`, followed by `ψ` of (94),
  `ψ((e₁ ∧ … ∧ e_k)*) = 1*`) is continuous in the parameter: for a continuous family of Fredholm
  operators `T_q : E → F` and stabilizations `φ_q : ℝᵏ → F` with `T_q ⊕ φ_q` onto, `Φ_{E_q}`
  carries a continuous orientation of `DET` along `q ↦ T_q` to a continuous orientation of the
  line bundle `λ(L)`, `L_q = ker(T_q ⊕ φ_q)`.  B states this for parameters `q ∈ [0, 1]` (both `t`
  and `τ` range over `[0, 1]`); `φ_q` may vary with `q` (along `t` it is `λ ↦ Σ λᵢ sᵢ(φ(t), t)`;
  for `L̃` it contains the added sections).
- Setting: real Banach spaces `E F : Type` (universe 0; `CompleteSpace`, needed for the topology
  of `DET(E, F)`); operators with the norm topology (`Continuous T`, `Continuous φ`); the parameter
  space `J = [0, 1] ⊆ ℝ¹` (`Set.Icc (0 : Fin 1 → ℝ) 1`, as in the other §6.5 items).
- Along `t` the text's operators act on the varying spaces `T_{φ(t)}X → Y_{φ(t)}`; B is the
  fixed-space principle (which is exactly the situation along `τ` at the end points `t = 0, 1`,
  Lemma 6.34, where `T^τ_t : T_{φ(t)}X → Y_{φ(t)}`).
- "continuous orientation of `DET` along `q ↦ T_q`" (`IsContAlong`): locally the ray of a
  continuous non-vanishing section of the pull-back of `DET(E, F)` along `q ↦ T_q`, i.e. of a
  continuous `q ↦ (T_q, σ_q)` into the total space `DET(E, F)` with the project's topology (the
  instance on `TotalSpace ℝ DetFiber`, from `detPrebundle`, Definition 6.22 / Proposition 6.24),
  in the form of the vocabulary's `IsLineOrientation`.
- `Φ_{E_q}` on rays, with `λ(ker(T ⊕ φ)) ⊗ λ*(ℝᵏ)` identified with `λ(L_q)` through `ψ`: the
  project's `stabRayEquiv` (`stabIota` = `Φ_E` of the sequence of Lemma 6.14 followed by `1 ⊗ ψ`,
  then `det(T ⊕ φ) ≅ λ(ker(T ⊕ φ))`, then `ker(T ⊕ φ) = L_q`), trusted from its docstring and
  `#print`.  The family `L` is the project's `SubspaceFamily` (local continuous frames) with
  `Λ_q = ker(T_q ⊕ φ_q)`, its line bundle `λ(L)` with the project's topology; continuity of the
  image orientation is the vocabulary's `IsLineOrientation`.
- I expect B to be FALSE as stated: the item's title and the vocabulary (`stabSign`
  `(−1)^{dim coker T}`, "the sign normalization of the stabilization isomorphism", and
  `StabCounterexample`: `T_q = q/(1 + |q|) · 1` on `ℝ`, `φ = id_{ℝ¹}`) indicate that without that
  sign `Φ_{E_q}` is not continuous where `dim coker T_q` jumps.  I formalize the text literally
  (no sign).
-/
namespace RoundTrip.V6_40
open Polyfold

/-- The parameter interval `[0, 1] ⊆ ℝ¹`. -/
abbrev J : Type := Set.Icc (0 : Fin 1 → ℝ) 1

section
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- `q ↦ o_q` is a continuous orientation of `DET(E, F)` along the path `q ↦ T_q`: near every
`q₀` it is the ray of a non-vanishing `σ_q ∈ det(T_q)` with `q ↦ (T_q, σ_q)` continuous into
`DET(E, F)`. -/
def IsContAlong (T : J → E →L[ℝ] F) (hT : ∀ q, (T q).IsFredholm)
    (o : ∀ q, Module.Ray ℝ (fredholmDet (T q))) : Prop :=
  ∀ q₀ : J, ∃ U ∈ nhds q₀, ∃ σ : ∀ q, fredholmDet (T q),
    ContinuousOn
      (fun q => (⟨⟨T q, hT q⟩, σ q⟩ : Bundle.TotalSpace ℝ (DetFiber (E := E) (F := F)))) U ∧
    ∀ q ∈ U, ∃ h : σ q ≠ 0, o q = rayOfNeZero ℝ (σ q) h

end

/-- `Φ_{E_q}` (with `ψ` of (94)) carries continuous orientations of `DET` along a continuous
family of stabilized Fredholm operators to continuous orientations of `λ(ker(T_q ⊕ φ_q))`. -/
def B : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (k : ℕ)
    (T : J → E →L[ℝ] F) (hT : ∀ q, (T q).IsFredholm) (φ : J → (Fin k → ℝ) →L[ℝ] F)
    (hs : ∀ q, Function.Surjective ((T q).coprod (φ q))),
    Continuous T → Continuous φ →
  ∀ (Λ : SubspaceFamily J (E × (Fin k → ℝ)))
    (hΛ : ∀ q, Λ.L q = LinearMap.ker ((T q).coprod (φ q)).toLinearMap)
    (o : ∀ q, Module.Ray ℝ (fredholmDet (T q))), IsContAlong T hT o →
    IsLineOrientation Λ.det
      (fun q => stabRayEquiv (hT q) (hs q) (LinearEquiv.ofEq _ _ (hΛ q).symm) (o q))

end RoundTrip.V6_40
