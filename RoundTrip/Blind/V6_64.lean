import Polyfold
/-! Blind formalization of V6_64 (the text's §6.7.2, the proof of Proposition 6.12,
pp. 235–237).

Text: with `dᵢ ∈ R(I − Q)`, bases `a, b` of `ker(QT)` and `a, b, b̃` of `ker(PT)`, the text computes
`γ^P_{QT}(γ^Q_T(h)) = α^P ⊗ (β^P)*`, splits `F/R(P) = ker Q̃ ⊕ ker(I − Q̃)`, replaces `[QT(b̃ᵢ)]`
by `[T(b̃ᵢ)]` in the wedge, and finds the same vector for `γ^P_T(h)`.

Choices:
- Setting: real Banach spaces `E F : Type` (universe 0; completeness is needed by the project's
  `gammaProj`), a Fredholm `T : E → F` (`T.IsFredholm`), good left-projections `P, Q ∈ Π_T`
  (`IsGoodLeftProj`, Definition 6.9) with `P ≤ Q` (`ProjLE P Q`: `P = PQ = QP`), as in
  Proposition 6.12.
- `γ^P_T : det(T) → det(PT)`: the project's `gammaProj hT hP` (`Φ_{E(T,P)}` of (91) for the exact
  sequence of Lemma 6.11, then `λ*(F/R(P)) = λ*(F/R(PT))`; checked with `#print`, trusted as
  the text's map of p. 210).  `γ^P_{QT}` is `gammaProj hQT hPQT`; that `QT` is Fredholm and
  `P ∈ Π_{QT}` (the first claims of Proposition 6.12, item V6_14) are universally quantified
  proofs here, as the computation presupposes them.  Its target `det(P(QT))` is identified with
  `det(PT)` by `linDetEquivOfEq` (`P(QT) = PT` since `PQ = P`).
- The data, in the text's form: `a₁, …, aₙ` a basis of `ker T`; `b₁, …, b_k` with `(a, b)` a basis
  of `ker(QT)`; `b̃₁, …, b̃_m` with `(a, b, b̃)` a basis of `ker(PT)` (linear independence in `E`,
  membership, and the dimension counts); `d₁, …, d_l ∈ R(I − Q)` whose classes form a basis of
  `coker T = F/R(T)`; `h = (a₁ ∧ … ∧ aₙ) ⊗ ([d₁] ∧ … ∧ [d_l])* ∈ det(T)`.
- `α^P ⊗ (β^P)*` is not displayed in the item; I computed it from (91) with the text's order
  conventions (`α(a)` then `b'`; `c` then `c' = β(b')`) and the evident choices (`[dᵢ]_Q`, then
  `[dᵢ]_P`, `[Tbᵢ]_P` lifting the `D`-bases, as the hypothesis `dᵢ ∈ R(I − Q)` is made for):
  `α^P = a₁ ∧ … ∧ aₙ ∧ b₁ ∧ … ∧ b_k ∧ b̃₁ ∧ … ∧ b̃_m ∈ λ(ker PT)` and
  `β^P = [d₁] ∧ … ∧ [d_l] ∧ [Tb₁] ∧ … ∧ [Tb_k] ∧ [QTb̃₁] ∧ … ∧ [QTb̃_m] ∈ λ(F/R(PT))`; it contains
  `[QT(b̃ᵢ)]`, consistent with the replacement step.  The vector found for `γ^P_T(h)` has
  `[Tb̃ᵢ]` in place of `[QTb̃ᵢ]` (formula (91) for `E(T, P)` with `b' = (b, b̃)`).
- B is the conjunction: (1) `γ^P_{QT}(γ^Q_T(h)) = α^P ⊗ (β^P)*`; (2) the split: `Q̃`, the map
  induced by `Q` on `F/R(P)`, gives `F/R(P) = ker Q̃ ⊕ ker(I − Q̃)`, with
  `ker Q̃ = {[f] | Qf ∈ R(P)}`, `ker(I − Q̃) = {[f] | (I − Q)f ∈ R(P)}` (images of the
  preimages, so that `Q̃` need not be constructed); (3) the replacement leaves the wedge
  unchanged; (4) `γ^P_T(h)` is the vector with `[Tb̃ᵢ]`.  Together they give
  `γ^P_{QT} ∘ γ^Q_T = γ^P_T` on `h`.
- Nothing looks false to me.
-/
namespace RoundTrip.V6_64
open Polyfold

/-- The proof of Proposition 6.12: the explicit vectors `γ^P_{QT}(γ^Q_T(h))` and `γ^P_T(h)`, the
split of `F/R(P)` and the replacement of `[QT btᵢ]` by `[T btᵢ]`. -/
def B : Prop :=
  ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (T : E →L[ℝ] F) (hT : T.IsFredholm) (P Q : F →L[ℝ] F)
    (hP : IsGoodLeftProj T P) (hQ : IsGoodLeftProj T Q) (hPQ : ProjLE P Q)
    (hQT : (Q.comp T).IsFredholm) (hPQT : IsGoodLeftProj (Q.comp T) P)
    {n k m l : ℕ} (a : Fin n → E) (b : Fin k → E) (bt : Fin m → E) (d : Fin l → F)
    -- `a` a basis of `ker T`
    (haT : ∀ i, a i ∈ LinearMap.ker (T : E →ₗ[ℝ] F)),
    LinearIndependent ℝ a → ∀ hn : n = Module.finrank ℝ (LinearMap.ker (T : E →ₗ[ℝ] F)),
    -- `(a, b)` a basis of `ker(QT)`
    (∀ i, Fin.append a b i ∈ LinearMap.ker ((Q.comp T : E →L[ℝ] F) : E →ₗ[ℝ] F)) →
    LinearIndependent ℝ (Fin.append a b) →
    n + k = Module.finrank ℝ (LinearMap.ker ((Q.comp T : E →L[ℝ] F) : E →ₗ[ℝ] F)) →
    -- `(a, b, bt)` a basis of `ker(PT)`
    ∀ (habP : ∀ i, Fin.append (Fin.append a b) bt i ∈
        LinearMap.ker ((P.comp T : E →L[ℝ] F) : E →ₗ[ℝ] F)),
    LinearIndependent ℝ (Fin.append (Fin.append a b) bt) →
    ∀ hnkm : n + k + m = Module.finrank ℝ (LinearMap.ker ((P.comp T : E →L[ℝ] F) : E →ₗ[ℝ] F)),
    -- `dᵢ ∈ R(I − Q)` with classes a basis of `coker T`
    (∀ i, d i ∈ LinearMap.range (((1 : F →L[ℝ] F) - Q : F →L[ℝ] F) : F →ₗ[ℝ] F)) →
    LinearIndependent ℝ
      (fun i => Submodule.Quotient.mk (p := LinearMap.range (T : E →ₗ[ℝ] F)) (d i)) →
    ∀ (hl : l = Module.finrank ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)))
      (hlkm : l + k + m =
        Module.finrank ℝ (F ⧸ LinearMap.range ((P.comp T : E →L[ℝ] F) : E →ₗ[ℝ] F))),
    let h : fredholmDet T :=
      wedge (fun i => (⟨a i, haT i⟩ : LinearMap.ker (T : E →ₗ[ℝ] F))) hn ⊗ₜ[ℝ]
        dualVec (wedge (fun i => Submodule.Quotient.mk (p := LinearMap.range (T : E →ₗ[ℝ] F))
          (d i)) hl)
    let mkP : F → F ⧸ LinearMap.range ((P.comp T : E →L[ℝ] F) : E →ₗ[ℝ] F) :=
      fun y => Submodule.Quotient.mk y
    let αP : maxPow (LinearMap.ker ((P.comp T : E →L[ℝ] F) : E →ₗ[ℝ] F)) :=
      wedge (fun i => (⟨Fin.append (Fin.append a b) bt i, habP i⟩ :
        LinearMap.ker ((P.comp T : E →L[ℝ] F) : E →ₗ[ℝ] F))) hnkm
    -- `β^P = [d] ∧ [T b] ∧ [QT bt]` and the replaced wedge `[d] ∧ [T b] ∧ [T bt]`
    let βP := wedge (Fin.append (Fin.append (fun i => mkP (d i)) (fun i => mkP (T (b i))))
      (fun i => mkP (Q (T (bt i))))) hlkm
    let βP' := wedge (Fin.append (Fin.append (fun i => mkP (d i)) (fun i => mkP (T (b i))))
      (fun i => mkP (T (bt i)))) hlkm
    -- (1) `γ^P_{QT}(γ^Q_T(h)) = α^P ⊗ (β^P)*`, read in `det(PT)`
    linDetEquivOfEq (congrArg (fun S : E →L[ℝ] F => (S : E →ₗ[ℝ] F))
        (by rw [← ContinuousLinearMap.comp_assoc, ← hPQ.1]))
      (gammaProj hQT hPQT (gammaProj hT hQ h)) = αP ⊗ₜ[ℝ] dualVec βP ∧
    -- (2) `F/R(P) = ker Q̃ ⊕ ker(I − Q̃)`
    IsCompl
      ((Submodule.comap (Q : F →ₗ[ℝ] F) (LinearMap.range (P : F →ₗ[ℝ] F))).map
        (LinearMap.range (P : F →ₗ[ℝ] F)).mkQ)
      ((Submodule.comap (((1 : F →L[ℝ] F) - Q : F →L[ℝ] F) : F →ₗ[ℝ] F)
          (LinearMap.range (P : F →ₗ[ℝ] F))).map
        (LinearMap.range (P : F →ₗ[ℝ] F)).mkQ) ∧
    -- (3) replacing `[QT btᵢ]` by `[T btᵢ]` leaves the wedge unchanged
    βP = βP' ∧
    -- (4) `γ^P_T(h)` is the same vector
    gammaProj hT hP h = αP ⊗ₜ[ℝ] dualVec βP'

end RoundTrip.V6_64
