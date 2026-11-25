import Polyfold
/-! Blind formalization of V14_48 (the Springer 2021 book, Part II, §14.5, Lemma 14.5.2 and
Remark 14.5.3, p. 672; 2017: Lemma 14.11, Remark 14.7).

Text: the structured `Λ_a = (β_a|∂X) ⊙ Λ`, with sections `β_a s⁰ˣᵢ` and the same `(𝒰⁰, I, τ⁰)`,
form a commensurable locally finite family over `∂X` whose sum is `Λ̃`; `Λ_a` is determined by
`(β_a s⁰ᵃᵢ)` on `V_a`.

Choices:
- Setting: universe 0, `SEP.{0}`, with the standing hypotheses of Theorem 14.1.9 (`X` tame,
  paracompact orbit space, sc-smooth partitions of unity) and every choice of the running
  construction as in my `V14_33.lean`: `Λ̃ = [T]` for a structured tuple `T = (Λ, 𝒰⁰, S⁰, τ⁰)`
  over `∂X` (`BoundaryStructuredTuple`), (P5), the extension `E`, (P6), and the data `C` of
  Proposition 14.3.8 (`A = C.Aset ⊆ ∂X`, `V̂_a`); `V_a = V̂_a ∩ ∂X`.  The cut-offs `β_a` are those
  of Lemma 14.5.1, read as the project's `ZConcrete.BetaSpec` (`#print`ed: sc-smooth functors,
  `tsupport β_a` in the saturation of `V̂_a`, locally finite, `∑_a β_a = 1` on `∂X`).
- `Λ_a = (β_a|∂X) ⊙ Λ`: the project's `multisectionSmulFun (β a) T.Λ` (`#print`ed:
  `(β ⊙ Λ)(w) = (β(P w)·Λ)(w)`, with `(0·Λ)(w) = 1` iff `w = 0`); only its values over `∂X` matter.
- "structured, with sections `β_a s⁰ˣᵢ` and the same `(𝒰⁰, I, τ⁰)`": sections over the common
  data `c = BoundaryCommData.ofTuple T` (`#print`ed: `T`'s good system, index sets, `τ⁰`) for the
  functor `Λ_a`, i.e. a term of the project's `c.Over Λ_a` (Definition 14.1.7 data: face-sc⁺,
  equivariant, compatible with `τ⁰`, counting formula on every `U⁰(x)`), whose sections are
  `β_a·s⁰ˣᵢ` on `U⁰(x)` (fibrewise product `sectionSmul`).  "Commensurable" = over the same `c`.
- "locally finite over `∂X`": the project's `BoundaryCommData.IsLocallyFiniteBoundaryFamily`
  (Definition 13.2.12 read over `∂X`).  "whose sum is `Λ̃`": the commensurable sum
  (`BoundaryCommData.lfSum`, sections `∑_a β_a s⁰ˣᵢ`) agrees with `Λ` over `∂X`, and its structured
  class (`Over.toStructured` of `Over.lfSum`) is the class `[T]` (quotient by the project's
  `BoundaryStructuredTuple.setoid`, Definition 14.1.7's equivalence).
- Remark 14.5.3, "`Λ_a` is determined by `(β_a s⁰ᵃᵢ)` on `V_a`", read as formulas: for `w` over
  `∂X` and a morphism `φ : z → P(w)` with `z ∈ V_a`,
  `Λ_a(w) = |I_a|⁻¹·#{i | μ(φ, β_a(z)s⁰ᵃᵢ(z)) = w}`; if `P(w) ∈ ∂X` is the target of no morphism
  from `V_a`, then `Λ_a(w) = 1` for `w = 0` and `0` otherwise.  Here `s⁰ᵃᵢ = C.toZSections.s a i`,
  `I_a = C.toZData.I a` (the tuple's sections and index set at `a`).
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V14_48
open Polyfold Polyfold.SBLocalization

/-- `Λ_a = (β_a|∂X) ⊙ Λ`. -/
noncomputable def Λa {A : SEP.{0}} (T : BoundaryStructuredTuple A) (β : A.Obj → A.Obj → ℝ)
    (a : A.Obj) : A.W → ℚ≥0 :=
  multisectionSmulFun (β a) T.Λ

open Classical in
/-- Lemma 14.5.2 and Remark 14.5.3. -/
def B : Prop :=
  ∀ (A : SEP.{0}), A.X.IsTame → A.X.HasParacompactOrbitSpace →
    A.X.PObj.AdmitsScPartitionsOfUnity →
    ∀ (T : BoundaryStructuredTuple A) (P : P5Nbhds T) (E : CorrExtension T P) (Q : P.P6Nbhds)
      (C : ZConcrete E Q) (β : A.Obj → A.Obj → ℝ), C.BetaSpec β →
    -- Lemma 14.5.2: structured over the common data, locally finite, with sum `Λ̃`
    (∃ o : (a : C.Aset) → (BoundaryCommData.ofTuple T).Over (Λa T β a),
      (∀ (a : C.Aset) (x : A.X.PObj.boundary) (i : (BoundaryCommData.ofTuple T).I x),
        ∀ y ∈ T.dec.𝒰.U x, (o a).s x i y = sectionSmul A.P (β a) ((T.dec.S x).s i) y) ∧
      ∃ hlf : BoundaryCommData.IsLocallyFiniteBoundaryFamily (fun a : C.Aset => Λa T β a),
        (∀ w : A.W, A.P w ∈ A.X.PObj.boundary → BoundaryCommData.lfSum o hlf w = T.Λ w) ∧
        (BoundaryCommData.Over.lfSum o hlf).toStructured =
          Quotient.mk (BoundaryStructuredTuple.setoid A) T) ∧
    -- Remark 14.5.3: `Λ_a` is determined by `β_a s⁰ᵃᵢ` on `V_a`
    (∀ a ∈ C.Aset, ∀ w : A.W, A.P w ∈ A.X.PObj.boundary →
      (∀ φ : A.Mor, A.X.src φ ∈ C.toZData.V a ∩ A.X.PObj.boundary → A.X.tgt φ = A.P w →
        Λa T β a w = ((Fintype.card (C.toZData.I a) : ℚ≥0))⁻¹ *
          (({i | fibAct φ (sectionSmul A.P (β a) (C.toZSections.s a i) (A.X.src φ)) = w} :
            Finset (C.toZData.I a)).card : ℚ≥0)) ∧
      ((¬ ∃ φ : A.Mor, A.X.src φ ∈ C.toZData.V a ∩ A.X.PObj.boundary ∧ A.X.tgt φ = A.P w) →
        Λa T β a w = if w = fiberZero A.P (A.P w) then 1 else 0))

end RoundTrip.V14_48
