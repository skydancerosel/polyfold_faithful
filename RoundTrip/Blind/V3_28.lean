import Polyfold
/-! Blind formalization of V3_28 (the text's §3.3, Lemma 3.31, pp. 86–87). Choices:
- Setting (as in the blind V3_26/V3_30, but with the text's `ℝⁿ` read as an arbitrary
  finite-dimensional real normed space `P : Type`, needed because `f⁽¹⁾` has the parameter space
  `ℝⁿ ⊕ ℝⁿ`, here `P × P`): `C̃ ⊆ P` a partial quadrant (`IsPartialQuadrant (ScBanach.const P)`),
  `W` an arbitrary sc-Banach space, `C̃ ⊕ W` is `ScBanach.paramProd P W` with the set `C̃ × W`.
  No universe choices arise.
- "`f = w − B(a, w)` an sc⁰-contraction germ": a germ of neighbourhoods `G` (Definition 3.1),
  `f = contractionMap B`, `IsSc0ContractionGerm C̃ G B` (Definition 3.28; item V3_25 checks it
  against the text).  "of class sc^k, `k ≥ 1`": `IsSckGerm k G f`, `1 ≤ k`.
- "with solution germ `δ` of class sc^j": every representative `(V, δ)` of the solution germ
  (`IsSolGerm`, as in V3_26/V3_30: an sc⁰-germ on `V` with `δ(0) = 0`, `(a, δ a) ∈ G₀`,
  `f(a, δ a) = 0` on `V₀`) which is an sc^j-germ on `V` (`IsSckGerm j V δ`).  I add `1 ≤ j`: the
  conclusion's `Tδ` presupposes that `δ` is sc¹ (Theorem 3.30 gives this anyway).
- `DB` and `Dδ`: *any* derivative families of the sc¹-germs `B` (on `G`) and `δ` (on `V`)
  (`IsSc1GermWith`); on the level-1 points where they are used they are unique.
- Level-1 values: `δ(v) ∈ W₁` for `v ∈ V₁` and `B(v, u) ∈ W₁` for `(v, u) ∈ U₁` are the preimages
  under `W₁ → W₀` (`lvlLift`, defined here; junk `0` if there is none, which does not happen on
  the domain below).
- `f⁽¹⁾(v, b, u, w) = (u − B(v, u), w − DB(v, δ(v))(b, w))` on `(C̃ ⊕ ℝⁿ) ⊕ TW`
  (`TW = W¹ ⊕ W`, so `u ∈ W₁`, `w ∈ W₀` on level `0`): the parameter space is
  `ScBanach.paramProd (P × P) W.tangent` with the set `(C̃ × P) × TW`, and
  `f⁽¹⁾ = contractionMap B⁽¹⁾` with `B⁽¹⁾((v, b), (u, w)) = (B(v, u), DB(v, δ(v))(b, w))`.
  Its germ of neighbourhoods `G⁽¹⁾` is not specified by the text; I assert that there is one
  inside the natural domain of the formula (`(v, u) ∈ U_{m+1}` and `v ∈ V_{m+1}` on level `m`).
- "is an sc⁰-contraction germ of class sc^{min(k−1, j)}": `IsSc0ContractionGerm (C̃ × P) G⁽¹⁾ B⁽¹⁾`
  and `IsSckGerm (min (k − 1) j) G⁽¹⁾ f⁽¹⁾`.
- "with solution germ `Tδ`": `Tδ(v, b) = (δ(v), Dδ(v) b) ∈ W₁ × W₀` is a solution germ of `f⁽¹⁾`
  (`IsSolGerm`) on some germ of neighbourhoods of `0` in `C̃ × P` inside `TV = (V_{m+1} × P)_m`.
  (By the uniqueness of Theorem 3.29, being a solution germ means being *the* solution germ.)
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_28
open Polyfold

/-- The preimage in `W_m` of `x ∈ W₀` under `W_m → W₀` (junk `0` if `x` is not on level `m`). -/
noncomputable def lvlLift (W : ScBanach) (m : ℕ) (x : W.lvl 0) : W.lvl m := by
  classical
  exact if h : ∃ y : W.lvl m, W.toBase m y = x then h.choose else 0

/-- `δ` is a solution germ of `f = w − B(a, w)` on the germ of neighbourhoods `V`: an sc⁰-germ with
`δ(0) = 0`, `(v, δ v)` in the domain of `f` and `f(v, δ v) = 0` for `v ∈ V₀`. -/
def IsSolGerm {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {W : ScBanach} {Ct : Set P}
    (G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ Set.univ))
    (Bm : P × W.lvl 0 → W.lvl 0)
    (V : ScNbhdGerm (ScBanach.const P) Ct) (δ : P → W.lvl 0) : Prop :=
  IsSc0Germ (F := W) V δ ∧ δ 0 = 0 ∧
    ∀ a ∈ V.U 0, ((a, δ a) : P × W.lvl 0) ∈ G.U 0 ∧ contractionMap Bm (a, δ a) = 0

/-- The map `B⁽¹⁾((v, b), (u, w)) = (B(v, u), DB(v, δ(v))(b, w))` of Lemma 3.31, so that
`f⁽¹⁾ = contractionMap B⁽¹⁾`, `f⁽¹⁾(v, b, u, w) = (u − B(v, u), w − DB(v, δ(v))(b, w))`. -/
noncomputable def B1 {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {W : ScBanach} (Bm : P × W.lvl 0 → W.lvl 0)
    (DB : (ScBanach.paramProd P W).lvl 1 → (ScBanach.paramProd P W).lvl 0 →L[ℝ] W.lvl 0)
    (δ : P → W.lvl 0) (x : (P × P) × W.tangent.lvl 0) : W.tangent.lvl 0 :=
  ((lvlLift W 1 (Bm (x.1.1, W.toBase 1 x.2.1)),
    DB ((x.1.1, lvlLift W 1 (δ x.1.1)) : P × W.lvl 1) ((x.1.2, x.2.2) : P × W.lvl 0)) :
      W.lvl 1 × W.lvl 0)

/-- The tangent `Tδ(v, b) = (δ(v), Dδ(v) b) ∈ W₁ × W₀` of the solution germ. -/
noncomputable def Tδ {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {W : ScBanach} (δ : P → W.lvl 0) (Dδ : P → P →L[ℝ] W.lvl 0) (p : P × P) :
    W.tangent.lvl 0 :=
  ((lvlLift W 1 (δ p.1), Dδ p.1 p.2) : W.lvl 1 × W.lvl 0)

/-- Lemma 3.31: for an sc⁰-contraction germ `f = w − B(a, w)` of class sc^k (`k ≥ 1`) with solution
germ `δ` of class sc^j, `f⁽¹⁾(v, b, u, w) = (u − B(v, u), w − DB(v, δ(v))(b, w))` is an
sc⁰-contraction germ of class sc^{min(k−1, j)} with solution germ `Tδ`. -/
def B : Prop :=
  ∀ (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (W : ScBanach) (Ct : Set P) (G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ Set.univ))
    (Bm : P × W.lvl 0 → W.lvl 0) (k j : ℕ),
    IsPartialQuadrant (ScBanach.const P) Ct →
    IsSc0ContractionGerm Ct G Bm →
    1 ≤ k → IsSckGerm k (F := W) G (contractionMap Bm) →
    ∀ (V : ScNbhdGerm (ScBanach.const P) Ct) (δ : P → W.lvl 0),
      IsSolGerm G Bm V δ → 1 ≤ j → IsSckGerm j (F := W) V δ →
    ∀ (DB : (ScBanach.paramProd P W).lvl 1 → (ScBanach.paramProd P W).lvl 0 →L[ℝ] W.lvl 0),
      IsSc1GermWith (F := W) G Bm DB →
    ∀ (Dδ : P → P →L[ℝ] W.lvl 0), IsSc1GermWith (F := W) V δ Dδ →
      ∃ G1 : ScNbhdGerm (ScBanach.paramProd (P × P) W.tangent) ((Ct ×ˢ Set.univ) ×ˢ Set.univ),
        (∀ (m : ℕ) (v b : P) (u : W.lvl (m + 1)) (w : W.lvl m),
          (((v, b), (u, w)) : (P × P) × (W.lvl (m + 1) × W.lvl m)) ∈ G1.U m →
            ((v, u) : P × W.lvl (m + 1)) ∈ G.U (m + 1) ∧ v ∈ V.U (m + 1)) ∧
        IsSc0ContractionGerm (Ct ×ˢ Set.univ) G1 (B1 Bm DB δ) ∧
        IsSckGerm (min (k - 1) j) (F := W.tangent) G1 (contractionMap (B1 Bm DB δ)) ∧
        ∃ V1 : ScNbhdGerm (ScBanach.const (P × P)) (Ct ×ˢ Set.univ),
          (∀ m, V1.U m ⊆ V.U (m + 1) ×ˢ Set.univ) ∧ IsSolGerm G1 (B1 Bm DB δ) V1 (Tδ δ Dδ)

end RoundTrip.V3_28
