import Polyfold
/-! Blind formalization of V16_21 (the text's Part II, §16.2, Theorem 16.2.6, p. 721 of the
Springer 2021 book; 2017: Theorem 16.2).

Text: `(Ω*_sc(Z, c), d)` is a de Rham complex, and sc-smooth maps of polyfolds pull it back.

Choices:
- Setting: `Z W : Type` (universe `0`), polyfolds `c, d` (`PolyfoldClass`).
- `Ωᵏ_sc(Z, c)`: the project's `c.ScForm k` (Definition 16.2.5: classes `[(ω, (X, α))]`,
  `ω ∈ Ωᵏ_{ep,∞}(X)`); the class of a representative is `ScForm.mk p hp ω`.
- `d`: the project's `ScForm.d` (linear).  I pin it to the text's definition
  `d[(ω, (X, α))] = [(dω, (X, α))]` (2021 p. 720), with `dω` the project's
  `EP.epFormsInftyD` on `Ω*_{ep,∞}(X)`; this also contains that `d` is well defined.
- "de Rham complex": `d ∘ d = 0` on every degree (`d` linear is in its type).  The text's complex
  may also carry the wedge product (graded Leibniz rule); the project has no wedge product on
  `Ω*_sc(Z, c)`, and I do not formalize it.
- sc-smooth maps `f̂ = [(f, 𝔣)] : (Z, c) → (W, d)`: the project's `ScMap c d`; the pull-back
  `f̂^*`: the project's `ScMap.pullback`, which I pin to the text's formula
  `f̂^*[(τ, (Y, β))] = [(𝔣^*τ, (X, α))]` for EVERY representative `(f, 𝔣) : (X, α) → (Y, β)` of
  `f̂` (so the formula is independent of the representatives), with `𝔣^*` the pull-back by a
  generalized map (Definition 11.2.7, the project's `EPLoc.formsPullback`).
- "pull it back" = `f̂^*` is a cochain map: `d ∘ f̂^* = f̂^* ∘ d`.  Functoriality of `f̂ ↦ f̂^*`
  is not added (the statement does not say it).
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V16_21
open Polyfold

/-- Theorem 16.2.6: `d` is well defined with `d ∘ d = 0`, and the pull-back by an sc-smooth map
is well defined by the representative formula and commutes with `d`. -/
def B : Prop :=
  -- `d` on representatives
  (∀ (Z : Type) [TopologicalSpace Z] (c : PolyfoldClass Z) (k : ℕ)
      (p : PolyfoldStructure Z) (hp : ⟦p⟧ = c) (ω : p.X.epFormsInfty k),
      PolyfoldClass.ScForm.d (PolyfoldClass.ScForm.mk p hp ω) =
        PolyfoldClass.ScForm.mk p hp (p.X.epFormsInftyD k ω)) ∧
  -- `d ∘ d = 0`
  (∀ (Z : Type) [TopologicalSpace Z] (c : PolyfoldClass Z) (k : ℕ) (ω : c.ScForm k),
      PolyfoldClass.ScForm.d (PolyfoldClass.ScForm.d ω) = 0) ∧
  -- the pull-back on representatives
  (∀ (Z W : Type) [TopologicalSpace Z] [TopologicalSpace W]
      (c : PolyfoldClass Z) (d : PolyfoldClass W) (F : c.ScMap d)
      (p : PolyfoldStructure Z) (hp : ⟦p⟧ = c) (q : PolyfoldStructure W) (hq : ⟦q⟧ = d)
      (φ : PSHom p q), PolyfoldClass.ScMap.mk p hp q hq φ = F →
      ∀ (k : ℕ) (τ : q.X.epFormsInfty k),
        F.pullback k (PolyfoldClass.ScForm.mk q hq τ) =
          PolyfoldClass.ScForm.mk p hp (EPLocalization.EPLoc.formsPullback φ.gen k τ)) ∧
  -- the pull-back commutes with `d`
  (∀ (Z W : Type) [TopologicalSpace Z] [TopologicalSpace W]
      (c : PolyfoldClass Z) (d : PolyfoldClass W) (F : c.ScMap d) (k : ℕ) (τ : d.ScForm k),
      PolyfoldClass.ScForm.d (F.pullback k τ) = F.pullback (k + 1) (PolyfoldClass.ScForm.d τ))

end RoundTrip.V16_21
