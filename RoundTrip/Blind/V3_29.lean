import Polyfold
/-! Blind formalization of V3_29 (the text's §3.3, Lemma 3.32, p. 87). Choices:
- Setting (as in my blind V3_28): the text's `ℝⁿ` is an arbitrary finite-dimensional real normed
  space `P : Type` (needed: the iterated parameter spaces `T^j ℝⁿ = ℝ^{2^j n}` are iterated
  products `P × P`), `C̃ ⊆ P` a partial quadrant (`IsPartialQuadrant (ScBanach.const P)`), `W` an
  arbitrary sc-Banach space, `C̃ ⊕ W` is `ScBanach.paramProd P W` with the set `C̃ × W`.  No
  universe choices arise.  A pair (finite-dimensional space, subset) is bundled as `PQ`
  (defined here) so that it can be iterated.
- "an sc⁰-contraction germ `f` of class sc^k": a germ of neighbourhoods `G`,
  `f = contractionMap B`, `IsSc0ContractionGerm C̃ G B` (Definition 3.28) and `IsSckGerm k G f`.
- "a solution germ `δ` of class sc^j, `j ≤ k`": every representative `(V, δ)` with `IsSolGerm`
  (as in V3_26/V3_30: an sc⁰-germ on `V`, `δ(0) = 0`, `(a, δ a) ∈ G₀`, `f(a, δ a) = 0` on `V₀`)
  that is an sc^j-germ on `V`, and `j ≤ k` (`j = 0` allowed: then `f⁽⁰⁾ = f` works).
- Iterated tangents: `T C̃ = C̃¹ ⊕ ℝⁿ` is `C̃ × P ⊆ P × P` (`PQ.T`), `T^j W` is
  `ScBanach.tangent^[j] W`, and `T^j δ` is defined recursively by
  `Tδ(v, b) = (δ(v), Dδ(v) b) ∈ W₁ × W₀` (`tanMap`, `iterTan`), where `δ(v) ∈ W₁` is the preimage
  under `W₁ → W₀` (`lvlLift`, junk `0` off level 1) and `Dδ(v)` is the derivative of
  `δ : P → W₀` within `C̃` at `v` (`fderivWithin`; for a finite-dimensional parameter space the
  sc-derivative at a level-1 point is this Fréchet derivative; it is unique since `C̃` is convex
  with nonempty interior).  On the levels where `T^j δ` is used (near `0` in `T^j V`) these are the
  text's values.
- "there is an sc⁰-contraction germ `f⁽ʲ⁾` of class sc^{min(k−j, 1)} with solution germ `T^j δ`":
  there are a germ of neighbourhoods `G_j` of `0` in `T^j C̃ ⊕ T^j W`, a map `B_j` with
  `IsSc0ContractionGerm (T^j C̃) G_j B_j`, `f⁽ʲ⁾ = contractionMap B_j` of class
  sc^{min(k−j, 1)} (`IsSckGerm`), and a germ of neighbourhoods `V_j` of `0` in `T^j C̃` on which
  `T^j δ` is a solution germ of `f⁽ʲ⁾` (`IsSolGerm`).  The text says "there is"; the specific
  iterate `f⁽ʲ⁾ = (f⁽ʲ⁻¹⁾)⁽¹⁾` of Lemma 3.31 is not prescribed here (an existence claim).
- Nothing in the statement looks false to me (the class `min(k − j, 1)` matches iterating
  Lemma 3.31: `f⁽ⁱ⁾` has class `min(k − i, j − i + 1)`).
-/
namespace RoundTrip.V3_29
open Polyfold

/-- A finite-dimensional real normed space `P` together with a subset `C ⊆ P`. -/
structure PQ where
  /-- The space. -/
  P : Type
  [ng : NormedAddCommGroup P]
  [ns : NormedSpace ℝ P]
  [fd : FiniteDimensional ℝ P]
  /-- The subset (a partial quadrant). -/
  C : Set P

attribute [instance] PQ.ng PQ.ns PQ.fd

/-- The tangent `T C = C¹ ⊕ P = C × P ⊆ P × P` of a subset of a finite-dimensional space. -/
noncomputable def PQ.T (X : PQ) : PQ where
  P := X.P × X.P
  C := X.C ×ˢ Set.univ

/-- The preimage in `W_m` of `x ∈ W₀` under `W_m → W₀` (junk `0` if `x` is not on level `m`). -/
noncomputable def lvlLift (W : ScBanach) (m : ℕ) (x : W.lvl 0) : W.lvl m := by
  classical
  exact if h : ∃ y : W.lvl m, W.toBase m y = x then h.choose else 0

/-- The tangent `Tδ(v, b) = (δ(v), Dδ(v) b) ∈ W₁ × W₀` of a germ `δ : C → W` on a finite-dimensional
parameter space, `Dδ(v)` the derivative within `C`. -/
noncomputable def tanMap (X : PQ) (W : ScBanach) (δ : X.P → W.lvl 0) :
    X.T.P → W.tangent.lvl 0 :=
  fun p : X.P × X.P => ((lvlLift W 1 (δ p.1), fderivWithin ℝ δ X.C p.1 p.2) : W.lvl 1 × W.lvl 0)

/-- The iterated tangent `T^j δ : T^j C → T^j W`. -/
noncomputable def iterTan : (j : ℕ) → (X : PQ) → (W : ScBanach) → (X.P → W.lvl 0) →
    (PQ.T^[j] X).P → (ScBanach.tangent^[j] W).lvl 0
  | 0, _, _, δ => δ
  | j + 1, X, W, δ => iterTan j X.T W.tangent (tanMap X W δ)

/-- `δ` is a solution germ of `f = w − B(a, w)` on the germ of neighbourhoods `V`: an sc⁰-germ with
`δ(0) = 0`, `(v, δ v)` in the domain of `f` and `f(v, δ v) = 0` for `v ∈ V₀`. -/
def IsSolGerm {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {W : ScBanach} {Ct : Set P}
    (G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ Set.univ))
    (Bm : P × W.lvl 0 → W.lvl 0)
    (V : ScNbhdGerm (ScBanach.const P) Ct) (δ : P → W.lvl 0) : Prop :=
  IsSc0Germ (F := W) V δ ∧ δ 0 = 0 ∧
    ∀ a ∈ V.U 0, ((a, δ a) : P × W.lvl 0) ∈ G.U 0 ∧ contractionMap Bm (a, δ a) = 0

/-- Lemma 3.32: for an sc⁰-contraction germ `f` of class sc^k with solution germ `δ` of class sc^j,
`j ≤ k`, there is an sc⁰-contraction germ `f⁽ʲ⁾` on `T^j C̃ ⊕ T^j W` of class sc^{min(k−j, 1)} with
solution germ `T^j δ`. -/
def B : Prop :=
  ∀ (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (W : ScBanach) (Ct : Set P) (G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ Set.univ))
    (Bm : P × W.lvl 0 → W.lvl 0) (k j : ℕ),
    IsPartialQuadrant (ScBanach.const P) Ct →
    IsSc0ContractionGerm Ct G Bm →
    IsSckGerm k (F := W) G (contractionMap Bm) →
    j ≤ k →
    ∀ (V : ScNbhdGerm (ScBanach.const P) Ct) (δ : P → W.lvl 0),
      IsSolGerm G Bm V δ → IsSckGerm j (F := W) V δ →
      ∃ (Gj : ScNbhdGerm (ScBanach.paramProd (PQ.T^[j] ⟨P, Ct⟩).P (ScBanach.tangent^[j] W))
            ((PQ.T^[j] ⟨P, Ct⟩).C ×ˢ Set.univ))
        (Bj : (PQ.T^[j] ⟨P, Ct⟩).P × (ScBanach.tangent^[j] W).lvl 0 →
          (ScBanach.tangent^[j] W).lvl 0)
        (Vj : ScNbhdGerm (ScBanach.const (PQ.T^[j] ⟨P, Ct⟩).P) (PQ.T^[j] ⟨P, Ct⟩).C),
        IsSc0ContractionGerm (PQ.T^[j] ⟨P, Ct⟩).C Gj Bj ∧
        IsSckGerm (min (k - j) 1) (F := ScBanach.tangent^[j] W) Gj (contractionMap Bj) ∧
        IsSolGerm Gj Bj Vj (iterTan j ⟨P, Ct⟩ W δ)

end RoundTrip.V3_29
