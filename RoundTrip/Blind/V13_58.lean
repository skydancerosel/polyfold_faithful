import Polyfold
/-! Blind formalization of V13_58 (the Springer 2021 book, Part II, §13.5, Theorem 13.5.7,
p. 635; 2017: Theorem 13.10).

Text: `|X|` paracompact, `X` with sc-smooth partitions of unity, `Λ` structurable: there is a
locally finite family of commensurable structured `[Λ_j, 𝒰, S_j, τ]`, each `Λ_j` atomic, with
`[Λ, 𝒰, S, τ] = ⊕^c_j [Λ_j, 𝒰, S_j, τ]`.

Choices:
- Setting: universe 0; the strong bundle over the ep-groupoid is `A : SEP.{0}`.
- Hypotheses: `A.X.HasParacompactOrbitSpace` (`|X|` paracompact); "`X` with sc-smooth
  partitions of unity": the ep-groupoid notion `A.X.HasScPartitionsOfUnity` (Definition 7.5.5,
  `#print`ed: every saturated open cover has a subordinate sc-smooth, invariant, locally finite
  partition of unity).  I read "`X`" as the ep-groupoid; the alternative is the object
  M-polyfold's `MPolyfold.AdmitsScPartitionsOfUnity` (every open cover).
- "`Λ` structurable": the project's `IsStructurable` (an sc⁺-multisection functor with a
  structure, Definition 13.3.6).
- The common data `(𝒰, I_x, τ)` shared by commensurable structured multisections (Definition
  13.4.5 (1)): the project's `CommData A`; a structure `[Λ, 𝒰, S, τ]` of `Λ` with that data: a
  term `o : c.Over Λ` (the sections `S` with the counting formula on every `U(x)`), its class
  `o.toStructured`.  The family `[Λ_j, 𝒰, S_j, τ]`: `oj j : c.Over (Λj j)` for the same `c`, so
  the members are pairwise commensurable and commensurable with `[Λ, 𝒰, S, τ]`.
- "locally finite": `IsLocallyFiniteFamily` (Definition 13.2.12, `#print`ed: every `x` has a
  saturated open neighbourhood over which only finitely many `Λ_j` charge a nonzero point).
- "each `Λ_j` atomic": `SBLocalization.IsAtomic` (Definition 13.5.1).
- `⊕^c`: the project's `CommData.lfSum` (the functor of the sections `∑_j s^{j,x}_i`, Definition
  13.4.5 (2)) and `CommData.Over.lfSum` (its structure); the equation
  `[Λ, 𝒰, S, τ] = ⊕^c_j [Λ_j, 𝒰, S_j, τ]` is the equality of the classes, and I add the equality
  `⊕^c_j Λ_j = Λ` of the underlying functors.  The index type `J : Type`.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V13_58
open Polyfold Polyfold.SBLocalization

/-- Theorem 13.5.7: a structurable sc⁺-multisection is a locally finite commensurable sum of
atomic ones. -/
def B : Prop :=
  ∀ A : SEP.{0}, A.X.HasParacompactOrbitSpace → A.X.HasScPartitionsOfUnity →
    ∀ Λ : A.W → ℚ≥0, IsStructurable A Λ →
      ∃ (c : CommData A) (o : c.Over Λ) (J : Type) (Λj : J → A.W → ℚ≥0)
        (oj : ∀ j, c.Over (Λj j)) (hlf : IsLocallyFiniteFamily Λj),
        (∀ j, SBLocalization.IsAtomic A (Λj j)) ∧
        CommData.lfSum oj hlf = Λ ∧
        (CommData.Over.lfSum oj hlf).toStructured = o.toStructured

end RoundTrip.V13_58
