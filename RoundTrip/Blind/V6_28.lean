import Polyfold
/-! Blind formalization of V6_28 (the text's §6.4, Lemma 6.25, p. 218).

Text: `γ_{(T',P',ε')} ∘ γ_{(T,P,ε)}⁻¹` is a topological isomorphism of line bundles: for `Q ≤ P`,
`Q ≤ P'` it is `(S, h) ↦ (S, (γ^Q_{P'S})⁻¹ ∘ γ^Q_{PS}(h))` by Corollary 6.13, continuous by
Lemma 6.21.

Choices:
- Setting: real Banach spaces `E F : Type` (universe 0; `CompleteSpace`, needed by the project's
  `γ^P_T`).  B quantifies over two local determinant bundles `DET(T, P, ε)`, `DET(T', P', ε')`,
  given as the project's `LocalDetChart E F` (checked with `#print`: a Fredholm `T`, `P ∈ Π_T`, a
  topological complement `Y` of `ker(P T)` and `ε > 0` with the conclusions of Lemma 6.17 for
  `‖S − T‖ < ε`, among them `P ∈ Π_S`), and over the operators `S` of the intersection of the two
  balls (`LocalDetChart.baseSet`, a set of Fredholm operators `FredholmOp E F`).
- `γ^P_S : det(S) → det(P S)`: the project's `gammaProj` (Definition of `γ^P_T` via the exact
  sequence `E(T, P)`, `Φ_{E(T,P)}` followed by `λ*(F/R(P)) = λ*(F/R(PS))`; docstring checked).
  `γ_{(T,P,ε)}(S, h) = (S, γ^P_S h)`, so on the fibre over `S` the transition map
  `γ_{(T',P',ε')} ∘ γ_{(T,P,ε)}⁻¹` is `k ↦ γ^{P'}_S((γ^P_S)⁻¹ k)`, `det(P S) → det(P' S)`.
- The formula (Corollary 6.13): for every `S` in both balls and every projection `Q` with
  `Q ≤ P` and `Q ≤ P'` (`ProjLE`: `Q = QP = PQ`) which is a good left-projection for `P S` and for
  `P' S` (the text's implicit requirement that `γ^Q_{PS}`, `γ^Q_{P'S}` be defined; given `Q ≤ P`,
  `Q ∈ Π_{PS}` is equivalent to `Q ∈ Π_S`), and `P S`, `P' S` Fredholm (they are; the hypotheses
  only name the proofs `gammaProj` needs): `γ^{P'}_S((γ^P_S)⁻¹ h) = (γ^Q_{P'S})⁻¹(γ^Q_{PS} h)` for
  `h ∈ det(P S)`.  The two middle lines `det(Q(PS))` and `det(Q(P'S))` are lines of the same
  operator `QPS = QS = QP'S`; they are identified by `linDetEquivOfEq` (identity on kernels and
  cokernels), which the text leaves implicit.
- "topological isomorphism of line bundles": the topology of `DET(T, P, ε) = ⋃ {S} × det(P S)` is
  that of Lemma 6.21, given by the frame `ω(S)` of `det(P S)`, `ball × ℝ ≅ DET(T, P, ε)`,
  `(S, t) ↦ (S, t ω(S))`.  Composed with `γ_{(T,P,ε)}` these are the project's
  `LocalDetChart.coord` (`h ↦ ω(S)*(γ^P_S h)`) and `coordInv` (`t ↦ (γ^P_S)⁻¹(t ω(S))`),
  checked with `#print`.  So in the frames the transition map is
  `(S, t) ↦ (S, coord'_S(coordInv_S t))` on `(ball ∩ ball') × ℝ`, and B says it is a homeomorphism
  of `(ball ∩ ball') × ℝ` (it is linear on the fibres by construction).  Continuity of the inverse
  is included (the text's "isomorphism").
- Nothing looks false to me.
-/
namespace RoundTrip.V6_28
open Polyfold

section
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- `γ^P_S : det(S) ≅ det(P S)` for `S` in the ball of the chart `c` (where `P ∈ Π_S`). -/
noncomputable def gam (c : LocalDetChart E F) (S : FredholmOp E F) (hS : S ∈ c.baseSet) :
    fredholmDet (S : E →L[ℝ] F) ≃ₗ[ℝ] fredholmDet (c.P ∘L (S : E →L[ℝ] F)) :=
  gammaProj S.2 (c.isGoodLeftProj_of_lt S hS)

omit [CompleteSpace E] [CompleteSpace F] in
/-- `Q ≤ P` and `Q ≤ P'` give `Q P S = Q P' S` (both are `Q S`). -/
theorem comp_eq (Q P P' : F →L[ℝ] F) (S : E →L[ℝ] F) (h : ProjLE Q P) (h' : ProjLE Q P') :
    ((Q ∘L (P ∘L S) : E →L[ℝ] F) : E →ₗ[ℝ] F) = ((Q ∘L (P' ∘L S) : E →L[ℝ] F) : E →ₗ[ℝ] F) := by
  rw [← ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc, ← h.1, ← h'.1]

/-- The formula of Corollary 6.13 for the transition map on the fibre over `S`. -/
def Formula : Prop :=
  ∀ (c c' : LocalDetChart E F) (S : FredholmOp E F) (hS : S ∈ c.baseSet) (hS' : S ∈ c'.baseSet)
    (Q : F →L[ℝ] F) (hQ : ProjLE Q c.P) (hQ' : ProjLE Q c'.P)
    (hPS : (c.P ∘L (S : E →L[ℝ] F)).IsFredholm) (hP'S : (c'.P ∘L (S : E →L[ℝ] F)).IsFredholm)
    (hQS : IsGoodLeftProj (c.P ∘L (S : E →L[ℝ] F)) Q)
    (hQS' : IsGoodLeftProj (c'.P ∘L (S : E →L[ℝ] F)) Q)
    (h : fredholmDet (c.P ∘L (S : E →L[ℝ] F))),
    gam c' S hS' ((gam c S hS).symm h) =
      (gammaProj hP'S hQS').symm
        (linDetEquivOfEq (comp_eq Q c.P c'.P (S : E →L[ℝ] F) hQ hQ') (gammaProj hPS hQS h))

/-- The transition map, read in the frames of Lemma 6.21, is a homeomorphism of
`(ball ∩ ball') × ℝ`. -/
def TopIso : Prop :=
  ∀ c c' : LocalDetChart E F,
    ∃ Φ : (↥(c.baseSet ∩ c'.baseSet) × ℝ) ≃ₜ (↥(c.baseSet ∩ c'.baseSet) × ℝ),
      ∀ (S : ↥(c.baseSet ∩ c'.baseSet)) (t : ℝ),
        Φ (S, t) = (S, c'.coord (S : FredholmOp E F) (c.coordInv (S : FredholmOp E F) t))

end

/-- Lemma 6.25: the transition maps of the local determinant bundles are topological
isomorphisms of line bundles, given on the fibres by the formula of Corollary 6.13. -/
def B : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F],
    Formula (E := E) (F := F) ∧ TopIso (E := E) (F := F)

end RoundTrip.V6_28
