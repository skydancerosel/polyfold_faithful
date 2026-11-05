import Polyfold
/-! Blind formalization of V5_63 (the text's §5.4.2, Corollary 5.44, p. 199).

Text: if `E₀` is a Hilbert space, `(O, C, E)` has the sc-smooth approximation property (proof: "a
Hilbert space is reflexive and hence a WCG-space … from Theorem 5.43 … in view of Theorem 5.37").

Choices:
- For every local model `M = (O, C, E)` (the project's `LocalModel`; levels of `E` in `Type`).
- "`E₀` is a Hilbert space": as in `RoundTrip/Blind/V5_53.lean`, `E₀` (complete, built into
  `ScBanach`) has its GIVEN norm induced by an inner product (`IsHilbertNormB`: a symmetric
  continuous bilinear `b` with `b(x, x) = ‖x‖²`).  Not read as "admits an equivalent Hilbert norm"
  (weaker hypothesis).
- "the sc-smooth approximation property": the project's `HasApproxProperty` (Definition 5.36,
  checked with `#print`; see `RoundTrip/Blind/V5_54.lean`).
- The proof's ingredients ("a Hilbert space is reflexive and hence WCG", the cited Theorem 5.43
  of Godefroy–Troyanski–Whitfield–Zizler) are justification, not part of the claim; in
  particular the cited Theorem 5.43 is NOT a hypothesis of B (the text uses it as a known
  theorem).  `BCited` below (not the item) is the claim with the statement of Theorem 5.43 (the
  project's `GodefroyTroyanskiWhitfieldZizlerStatement`, checked: WCG with a `C^k`-bump function
  implies `C^k` partitions of unity) assumed for every Banach space and every `k`.
- Nothing looks false to me.
-/
namespace RoundTrip.V5_63
open Polyfold

/-- The norm of `V` comes from an inner product: `‖x‖² = b(x, x)` for a symmetric continuous
bilinear form `b`. -/
def IsHilbertNormB (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] : Prop :=
  ∃ b : V →L[ℝ] V →L[ℝ] ℝ, (∀ x y, b x y = b y x) ∧ ∀ x, b x x = ‖x‖ ^ 2

/-- Corollary 5.44: a local model on an sc-Banach space with Hilbert `E₀` has the sc-smooth
approximation property. -/
def B : Prop :=
  ∀ M : LocalModel, IsHilbertNormB (M.E.lvl 0) → M.HasApproxProperty

/-- Not the item: the same, given the cited Theorem 5.43 for all Banach spaces. -/
def BCited : Prop :=
  (∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (k : ℕ∞),
      GodefroyTroyanskiWhitfieldZizlerStatement V k) →
    ∀ M : LocalModel, IsHilbertNormB (M.E.lvl 0) → M.HasApproxProperty

end RoundTrip.V5_63
