import Polyfold
/-! Blind formalization of V14_37 (the Springer 2021 book, Part II, §14.5, Proposition 14.5.4,
pp. 673–677; 2017: Proposition 14.8).

Text: fix `a ∈ A`.  There are sections `s̃ᵃ_{b,j}` on every `V̂_b`, sc⁺ and `G_b`-equivariant, with
(1) `s̃ᵃ_{a,i} = β_a ŝᵃᵢ`; (2) compact support in `V̂_a`; (3) `s̃ᵃ_{b,j} = β_a s⁰ᵇⱼ` on `V̂_b ∩ ∂X`;
(4) compatibility with `τ̂_{b,b'}`.  They are defined by transport `μ(φ, β_a ŝᵃᵢ)` along `φ` from
`V̂_a`, and are `0` where no such `φ` exists.

Choices:
- Setting: universe 0, `SEP.{0}`, with the standing hypotheses of Theorem 14.1.9 (`X` tame,
  paracompact orbit space, sc-smooth partitions of unity), and every choice of the running
  construction of §§14.2–14.4 as in my `V14_33.lean`: a structured tuple `T` over `∂X`, (P5),
  the extension `E` of the correspondences, (P6), the data `C` of Proposition 14.3.8; the setting of
  §14.4 is `S = C.toZData` (`A`, `Ũ(a)`, `V̂_a`, `I_a`, `τ̂_{b,b'}`), `s⁰ᵇⱼ = C.toZSections.s b j`.
- The local extensions `ŝᵃ` (Proposition 14.4.14): ANY family satisfying the conclusion of
  Proposition 14.4.14 at every `a ∈ A` (`IsLocalExtension`, copied from `V14_33.lean`).
- The cut-offs `β_a` (Lemma 14.5.1, not quoted in my statement file): the project's
  `ZConcrete.BetaSpec` (`#print`ed: `β_a` sc-smooth functors `X → ℝ`, `tsupport β_a` inside the
  saturation of `V̂_a`, locally finite, `∑_a β_a = 1` on `∂X`).  I trust this reading of the lemma.
- `β_a ŝᵃᵢ` is the fibrewise product `Polyfold.sectionSmul A.P (β a) (ŝᵃᵢ)`; `0` is the zero of the
  fibre (`fiberZero`); `μ(φ, ·)` is `fibAct φ`.
- (2) "compact support in `V̂_a`": `s̃ᵃ_{b,j}` lives on `V̂_b`, so I read this for `b = a`.  A
  literally compact support is impossible in infinite dimensions for a section that is not
  identically zero (a compact set has empty interior there), so I read "support" as the closure
  in `X` of `{y ∈ V̂_a | s̃ᵃ_{a,i}(y) ≠ 0}` and require it to lie in `V̂_a` (support is a closed set
  inside `V̂_a`); "compact" is not formalized.  This is my most doubtful clause.
- (4): for `b, b' ∈ A`, `φ` with `s(φ) ∈ V̂_b`, `t(φ) ∈ V̂_{b'}`, and every pair `(j, j')` of the
  correspondence `τ̂_{b,b'}(φ)` (`IndexCorr.Pairs`): `s̃ᵃ_{b',j'}(t(φ)) = μ(φ, s̃ᵃ_{b,j}(s(φ)))`
  (Definition 13.3.4 (3) for `τ̂`).
- "defined by transport": (5) for `φ` from `V̂_a` to `V̂_b` and a pair `(i, j)` of `τ̂_{a,b}(φ)`,
  `s̃ᵃ_{b,j}(t(φ)) = μ(φ, β_a(s φ) ŝᵃᵢ(s φ))` (this also follows from (1) and (4)); and (6)
  `s̃ᵃ_{b,j}(y) = 0` for `y ∈ V̂_b` that is the target of no morphism with source in `V̂_a`.
- I `#print`ed the project's `proposition_14_5_4_statement` (a vocabulary definition) while
  looking at the transport vocabulary, before writing this file; see the report.
- Nothing else looks doubtful to me.
-/
namespace RoundTrip.V14_37
open Polyfold Polyfold.SBLocalization

/-- The conclusion of Proposition 14.4.14 at `a` (copied from `V14_33.lean`). -/
def IsLocalExtension {A : SEP.{0}} {T : BoundaryStructuredTuple A} {P : P5Nbhds T}
    {E : CorrExtension T P} {Q : P.P6Nbhds} (C : ZConcrete E Q) (a : A.Obj)
    (sh : C.toZData.I a → A.Obj → A.W) : Prop :=
  (∀ i, IsScPlusSectionOn A (sh i) (C.toZData.V a)) ∧
  (∀ (g : A.X.Isotropy a) (i : C.toZData.I a), ∀ y ∈ C.toZData.V a,
    sh (g • i) ((C.toZData.nbhd a).rep.Φ g y) = fibAct ((C.toZData.nbhd a).rep.Γ g y) (sh i y)) ∧
  (∀ i, ∀ y ∈ C.toZData.V a ∩ A.X.PObj.boundary, sh i y = C.toZSections.s a i y) ∧
  (∀ z ∈ C.toZData.V a, ∀ i i' : C.toZData.I a, C.toZData.ZRel a z i i' → sh i z = sh i' z)

/-- The conclusion of Proposition 14.5.4 for `a`, the cut-offs `β`, the local extensions `sh`
and the sections `st b j = s̃ᵃ_{b,j}`. -/
def IsTransport {A : SEP.{0}} {T : BoundaryStructuredTuple A} {P : P5Nbhds T}
    {E : CorrExtension T P} {Q : P.P6Nbhds} (C : ZConcrete E Q) (β : A.Obj → A.Obj → ℝ)
    (sh : (a : A.Obj) → C.toZData.I a → A.Obj → A.W) (a : A.Obj)
    (st : (b : A.Obj) → C.toZData.I b → A.Obj → A.W) : Prop :=
  -- sc⁺ on every `V̂_b`
  (∀ b ∈ C.toZData.A, ∀ j, IsScPlusSectionOn A (st b j) (C.toZData.V b)) ∧
  -- `G_b`-equivariant on `V̂_b`
  (∀ b ∈ C.toZData.A, ∀ (g : A.X.Isotropy b) (j : C.toZData.I b), ∀ y ∈ C.toZData.V b,
    st b (g • j) ((C.toZData.nbhd b).rep.Φ g y) =
      fibAct ((C.toZData.nbhd b).rep.Γ g y) (st b j y)) ∧
  -- (1) `s̃ᵃ_{a,i} = β_a ŝᵃᵢ` on `V̂_a`
  (∀ i, ∀ y ∈ C.toZData.V a, st a i y = sectionSmul A.P (β a) (sh a i) y) ∧
  -- (2) the support of `s̃ᵃ_{a,i}` lies in `V̂_a`
  (∀ i, closure {y | y ∈ C.toZData.V a ∧ st a i y ≠ fiberZero A.P y} ⊆ C.toZData.V a) ∧
  -- (3) `s̃ᵃ_{b,j} = β_a s⁰ᵇⱼ` on `V̂_b ∩ ∂X`
  (∀ b ∈ C.toZData.A, ∀ j, ∀ y ∈ C.toZData.V b ∩ A.X.PObj.boundary,
    st b j y = sectionSmul A.P (β a) (C.toZSections.s b j) y) ∧
  -- (4) compatibility with `τ̂_{b,b'}`
  (∀ b ∈ C.toZData.A, ∀ b' ∈ C.toZData.A,
    ∀ φ ∈ A.X.morBetween (C.toZData.V b) (C.toZData.V b'), ∀ j j',
      (C.toZData.τ b b' φ).Pairs j j' → st b' j' (A.X.tgt φ) = fibAct φ (st b j (A.X.src φ))) ∧
  -- (5) transport along `φ` from `V̂_a`
  (∀ b ∈ C.toZData.A, ∀ φ ∈ A.X.morBetween (C.toZData.V a) (C.toZData.V b), ∀ i j,
    (C.toZData.τ a b φ).Pairs i j →
      st b j (A.X.tgt φ) = fibAct φ (sectionSmul A.P (β a) (sh a i) (A.X.src φ))) ∧
  -- (6) `0` where no morphism from `V̂_a` arrives
  (∀ b ∈ C.toZData.A, ∀ j, ∀ y ∈ C.toZData.V b,
    (¬ ∃ φ : A.Mor, A.X.src φ ∈ C.toZData.V a ∧ A.X.tgt φ = y) → st b j y = fiberZero A.P y)

/-- Proposition 14.5.4: for every `a ∈ A` the transported sections `s̃ᵃ_{b,j}` exist. -/
def B : Prop :=
  ∀ (A : SEP.{0}), A.X.IsTame → A.X.HasParacompactOrbitSpace →
    A.X.PObj.AdmitsScPartitionsOfUnity →
    ∀ (T : BoundaryStructuredTuple A) (P : P5Nbhds T) (E : CorrExtension T P) (Q : P.P6Nbhds)
      (C : ZConcrete E Q) (β : A.Obj → A.Obj → ℝ), C.BetaSpec β →
    ∀ sh : (a : A.Obj) → C.toZData.I a → A.Obj → A.W,
      (∀ a ∈ C.toZData.A, IsLocalExtension C a (sh a)) →
      ∀ a ∈ C.toZData.A, ∃ st : (b : A.Obj) → C.toZData.I b → A.Obj → A.W,
        IsTransport C β sh a st

end RoundTrip.V14_37
