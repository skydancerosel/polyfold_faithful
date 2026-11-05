import Polyfold
/-! Blind formalization of V5_59 (the text's §5.4.2, Definition 5.39 and Theorem 5.40, p. 198).

Text: `c₀(Γ)`: the `f : Γ → ℝ` with `{γ | |f(γ)| > ε}` finite for every `ε`, norm
`max_γ |f(γ)|`; coordinate-wise `C^k` homeomorphic embeddings `E → c₀(Γ)`.  Theorem 5.40
(Toruńczyk, cited): a Banach space admits `C^k` partitions of unity iff it has such an embedding
into some `c₀(Γ)`.

Choices:
- This item is a definition plus the STATEMENT of a cited theorem.  B is the conjunction of:
  (1) the project's `cZero Γ` (a submodule of Mathlib's `ℓ^∞(Γ) = lp (fun _ => ℝ) ⊤`) has exactly
      the text's elements: an `F ∈ ℓ^∞` lies in `cZero Γ` iff `{γ | ε < |F(γ)|}` is finite for
      every `ε > 0` (`c0SetB`); and every `f : Γ → ℝ` with that property is (the function of) an
      element of `cZero Γ` (boundedness is automatic);
  (2) its norm is `max_γ |f(γ)|`: `|F(γ)| ≤ ‖F‖` for all `γ`, with equality for some `γ` (for
      `Γ = ∅` there is no `γ`; then `‖F‖ = 0`, the junk value of the empty max);
  (3) the project's `IsCoordinatewiseContDiffEmbedding k h` is the text's notion `IsCoordEmbB`:
      `h : E → c₀(Γ)` a homeomorphism onto its image (injective, continuous, inverse continuous on
      the image, written metrically) all of whose coordinates `e ↦ h(e)(γ)` are `C^k`;
  (4) the project's `AdmitsContDiffPartitionsOfUnity V k` is the text's "`V` admits `C^k`
      partitions of unity" (`AdmitsCkPOUB`: every open cover `(U_i)_{i ∈ ι}`, `ι : Type`, has a
      subordinate family of `C^k` functions `ρ_i ≥ 0`, locally finite supports, `Σ ρ_i = 1`,
      `supp ρ_i ⊆ U_i`), and the project's `TorunczykStatement V k` is the text's statement of
      Theorem 5.40 (`TorunczykB`), for every Banach space `V : Type` (universe 0, as asked; the
      text's `E` is a Banach space) and `k : ℕ∞` (`⊤ = ∞`; `C^k` is `ContDiff ℝ k`).
  `Γ` ranges over `Type` (the project's `TorunczykStatement` takes `Γ` in the universe of `V`).
- The truth of Theorem 5.40 (cited, [9] Theorem 30) is NOT in B; `BTheorem` below (not the item)
  records it.
- Nothing looks false to me.
-/
namespace RoundTrip.V5_59
open Polyfold

/-- `c₀(Γ)` as a set of functions: `{γ | |f(γ)| > ε}` is finite for every `ε > 0`. -/
def c0SetB (Γ : Type) : Set (Γ → ℝ) :=
  {f | ∀ ε : ℝ, 0 < ε → {γ | ε < |f γ|}.Finite}

/-- **Definition 5.39**: `h : V → c₀(Γ)` is a coordinate-wise `C^k` homeomorphic embedding. -/
def IsCoordEmbB {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Γ : Type} (k : ℕ∞)
    (h : V → cZero Γ) : Prop :=
  Function.Injective h ∧ Continuous h ∧
  (∀ e : V, ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ ∀ e' : V, dist (h e') (h e) < δ → dist e' e < ε) ∧
  ∀ γ : Γ, ContDiff ℝ (k : WithTop ℕ∞) (fun e => (h e : lp (fun _ : Γ => ℝ) ⊤) γ)

/-- `V` admits `C^k` partitions of unity. -/
def AdmitsCkPOUB (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (k : ℕ∞) : Prop :=
  ∀ (ι : Type) (U : ι → Set V), (∀ i, IsOpen (U i)) → (⋃ i, U i) = Set.univ →
    ∃ ρ : ι → V → ℝ, (∀ i, ContDiff ℝ (k : WithTop ℕ∞) (ρ i)) ∧ (∀ i x, 0 ≤ ρ i x) ∧
      LocallyFinite (fun i => tsupport (ρ i)) ∧ (∀ x, ∑ᶠ i, ρ i x = 1) ∧
      ∀ i, tsupport (ρ i) ⊆ U i

/-- **Theorem 5.40** (statement): `V` admits `C^k` partitions of unity iff there is a
coordinate-wise `C^k` homeomorphic embedding of `V` into some `c₀(Γ)`. -/
def TorunczykB (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (k : ℕ∞) : Prop :=
  AdmitsCkPOUB V k ↔ ∃ (Γ : Type) (h : V → cZero Γ), IsCoordEmbB k h

/-- Definition 5.39 and the statement of Theorem 5.40: the project's `c₀(Γ)` (elements and norm),
coordinate-wise `C^k` embeddings, `C^k` partitions of unity and Toruńczyk statement are the
text's. -/
def B : Prop :=
  -- (1) the elements of `c₀(Γ)`
  (∀ (Γ : Type) (F : lp (fun _ : Γ => ℝ) ⊤), F ∈ cZero Γ ↔ (fun γ => F γ) ∈ c0SetB Γ) ∧
  (∀ (Γ : Type) (f : Γ → ℝ), f ∈ c0SetB Γ →
    ∃ F : lp (fun _ : Γ => ℝ) ⊤, F ∈ cZero Γ ∧ ∀ γ, F γ = f γ) ∧
  -- (2) the norm `max_γ |f(γ)|`
  (∀ (Γ : Type) (F : cZero Γ),
    (∀ γ, |(F : lp (fun _ : Γ => ℝ) ⊤) γ| ≤ ‖F‖) ∧
    ((∃ γ, |(F : lp (fun _ : Γ => ℝ) ⊤) γ| = ‖F‖) ∨ (IsEmpty Γ ∧ ‖F‖ = 0))) ∧
  -- (3) coordinate-wise `C^k` homeomorphic embeddings
  (∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (Γ : Type) (k : ℕ∞)
      (h : V → cZero Γ), IsCoordinatewiseContDiffEmbedding k h ↔ IsCoordEmbB k h) ∧
  -- (4) `C^k` partitions of unity, and the statement of Theorem 5.40
  (∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (k : ℕ∞),
      (AdmitsContDiffPartitionsOfUnity V k ↔ AdmitsCkPOUB V k) ∧
      (TorunczykStatement V k ↔ TorunczykB V k))

/-- Not the item: Theorem 5.40 itself (cited), for every Banach space. -/
def BTheorem : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (k : ℕ∞),
    TorunczykB V k

end RoundTrip.V5_59
