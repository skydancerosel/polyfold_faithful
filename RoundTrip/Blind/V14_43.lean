import Polyfold
/-! Blind formalization of V14_43 (the Springer 2021 book, Part II, §14.6, Theorem 14.6.3, p. 682;
2017: Theorem 14.4).

Text: a compatible assignment over a tame face-structured `X` defines a structured `Λ̃` on `W|∂X`
with `Λ|F = Λ_F`.  Hence (Theorem 14.1.9) `Λ` extends to a structurable `Λ'` on `W` with
`N(Λ') ≤ f` and `dom-supp(Λ') ⊆ Ũ`.

Choices:
- Setting: universe 0, a strong bundle over an ep-groupoid `SEP.{0}`.  "Tame face-structured":
  the project's `EpGroupoid.IsTame` and `EpGroupoid.IsEpFaceStructured` (Definition 11.1.3: every
  `z ∈ |X|` lies in exactly `d(z)` faces).  Faces `F` of `X`: the project's `EpGroupoid.IsEpFace`
  (the object sets of the faces of `|X|`).
- Structured sc⁺-multisections `Λ̃_F` on `W|F`: the project's `FaceStructuredMultisection A F`
  (§14.6 p. 680, classes of tuples `(Λ_F, 𝒰_F, S_F, τ_F)` with sections sc⁺ relative to `F`); a
  compatible assignment `F ↦ Λ̃_F` is the project's `IsCompatibleAssignment` (Definition 14.6.2,
  `Λ̃_F|F' = Λ̃_{F'}|F`, `#print`ed).  The functor `Λ_F` of a class is the functor of a
  representative (`faceFun`, via `Quotient.out`); only its values over `F` are used.
- "a structured `Λ̃` on `W|∂X` with `Λ|F = Λ_F`": a class `L` of the project's
  `BoundaryStructuredMultisection` (Definition 14.1.7) whose functor (`forget`) agrees with `Λ_F`
  over every face `F`.
- The second sentence is Theorem 14.1.9 applied to `Λ = L.forget`; its hypotheses beyond the
  first sentence are added for that part only: paracompact orbit space, sc-smooth partitions of
  unity, an auxiliary norm `N` (`EpStrongBundle.IsAuxNorm`), a saturated open `Ũ ⊇ dom-supp(Λ)`,
  and a continuous functor `f : X → [0, ∞)` with `tsupport f ⊆ Ũ` and `N(Λ) < f` on
  `dom-supp(Λ)`.  These hypotheses are not quoted in my statement file; I took them from the
  project's vocabulary definition `theorem_14_1_9_statement` (`#print`ed), whose docstring states
  Theorem 14.1.9, and restated them here.  `N(Λ)(x)` is the project's
  `pointwiseNorm` (sup of `N` over `w` over `x` with `Λ(w) > 0`), `dom-supp` over `∂X` is
  `boundaryDomSupp`, on `X` it is `domSupp` (closures of the points carrying a nonzero `w` with
  `Λ(w) > 0`).  "`Λ` extends": `Λ' = Λ` over `∂X`.  "structurable" on `W`: `IsStructurable`
  (Definition 13.3.6).
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V14_43
open Polyfold Polyfold.SBLocalization

/-- The functor `Λ_F` of a structured sc⁺-multisection on `W|F` (a representative's). -/
noncomputable def faceFun {A : SEP.{0}} {F : Set A.Obj} (L : FaceStructuredMultisection A F) :
    A.W → ℚ≥0 :=
  (Quotient.out L).2.Λ

/-- Theorem 14.6.3. -/
def B : Prop :=
  ∀ (A : SEP.{0}), A.X.IsTame → A.X.IsEpFaceStructured →
    ∀ Λt : (F : Set A.Obj) → A.X.IsEpFace F → FaceStructuredMultisection A F,
      IsCompatibleAssignment Λt →
      ∃ L : BoundaryStructuredMultisection A,
        -- `Λ|F = Λ_F`
        (∀ (F : Set A.Obj) (hF : A.X.IsEpFace F) (w : A.W), A.P w ∈ F →
          L.forget w = faceFun (Λt F hF) w) ∧
        -- the extension by Theorem 14.1.9
        (A.X.HasParacompactOrbitSpace → A.X.PObj.AdmitsScPartitionsOfUnity →
          ∀ (N : A.B.One → ℝ), A.E.IsAuxNorm N →
          ∀ (Ũ : Set A.Obj), IsOpen Ũ → A.X.IsSaturated Ũ → boundaryDomSupp L.forget ⊆ Ũ →
          ∀ (f : A.Obj → ℝ), Continuous f → (∀ x, 0 ≤ f x) →
            (∀ φ : A.Mor, f (A.X.tgt φ) = f (A.X.src φ)) → tsupport f ⊆ Ũ →
            (∀ x ∈ boundaryDomSupp L.forget, pointwiseNorm N L.forget x < f x) →
            ∃ Λ' : A.W → ℚ≥0, IsStructurable A Λ' ∧
              (∀ x, pointwiseNorm N Λ' x ≤ f x) ∧ domSupp Λ' ⊆ Ũ ∧
              ∀ w : A.W, A.P w ∈ A.X.PObj.boundary → Λ' w = L.forget w)

end RoundTrip.V14_43
