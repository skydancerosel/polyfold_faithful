import Polyfold
/-! Blind formalization of V3_31 (the text's §3.3, Corollary 3.34, p. 88). `B` is the conjunction
of the main claim and its "in particular".  Choices:
- Setting (as in my blind V3_28/V3_29): the text's `ℝⁿ` is an arbitrary finite-dimensional real
  normed space `P : Type`, `C̃ ⊆ P` a partial quadrant (`IsPartialQuadrant (ScBanach.const P)`),
  `W` an arbitrary sc-Banach space, `C̃ ⊕ W` is `ScBanach.paramProd P W` with the set `C̃ × W`.
  No universe choices arise.
- "the sc⁰-contraction germ `f`": a germ of neighbourhoods `G`, `f = contractionMap B`,
  `IsSc0ContractionGerm C̃ G B` (Definition 3.28).  "`f` is sc-smooth": `IsScSmoothGerm G f`.
- "`δ`" (its solution germ): every representative `(V, δ)` (`IsSolGerm`, as in V3_26/V3_30: an
  sc⁰-germ on `V`, `δ(0) = 0`, `(a, δ a) ∈ G₀`, `f(a, δ a) = 0` on `V₀`).
- "a relatively open `V_{m,k} ∋ 0` in `C̃`": `V_{m,k} = O ∩ C̃` with `O` open in `P`, `0 ∈ V_{m,k}`;
  I also require `V_{m,k} ⊆ V₀` (inside the domain of the representative `δ`, where `δ` means
  something).
- "(1) `δ(V_{m,k}) ⊆ W_m`, (2) `δ : V_{m,k} → W_m` of class `C^k`": there is a map
  `δ_m : P → W_m` with `ι(δ_m(v)) = δ(v)` for `v ∈ V_{m,k}` (`ι : W_m → W₀` the inclusion; so
  (1) holds and `δ_m` is the induced map, unique on `V_{m,k}`) with `ContDiffOn ℝ k δ_m V_{m,k}`
  (`C^k` on the relatively open subset of the quadrant, derivatives within it).
- "In particular `δ` is sc-smooth at the smooth point `0`": read as "the germ `δ` is sc-smooth",
  i.e. `δ` is an sc-smooth germ (`IsScSmoothGerm`) on some germ of neighbourhoods `V' ⊆ V`
  (level by level).
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_31
open Polyfold

/-- `δ` is a solution germ of `f = w − B(a, w)` on the germ of neighbourhoods `V`: an sc⁰-germ with
`δ(0) = 0`, `(v, δ v)` in the domain of `f` and `f(v, δ v) = 0` for `v ∈ V₀`. -/
def IsSolGerm {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {W : ScBanach} {Ct : Set P}
    (G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ Set.univ))
    (Bm : P × W.lvl 0 → W.lvl 0)
    (V : ScNbhdGerm (ScBanach.const P) Ct) (δ : P → W.lvl 0) : Prop :=
  IsSc0Germ (F := W) V δ ∧ δ 0 = 0 ∧
    ∀ a ∈ V.U 0, ((a, δ a) : P × W.lvl 0) ∈ G.U 0 ∧ contractionMap Bm (a, δ a) = 0

/-- Corollary 3.34: if the sc⁰-contraction germ `f` is sc-smooth, then for all `m, k` the solution
germ `δ` maps some relatively open `V_{m,k} ∋ 0` in `C̃` into `W_m`, by a `C^k` map; in particular
`δ` is an sc-smooth germ. -/
def B : Prop :=
  ∀ (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (W : ScBanach) (Ct : Set P) (G : ScNbhdGerm (ScBanach.paramProd P W) (Ct ×ˢ Set.univ))
    (Bm : P × W.lvl 0 → W.lvl 0),
    IsPartialQuadrant (ScBanach.const P) Ct →
    IsSc0ContractionGerm Ct G Bm →
    IsScSmoothGerm (F := W) G (contractionMap Bm) →
    ∀ (V : ScNbhdGerm (ScBanach.const P) Ct) (δ : P → W.lvl 0), IsSolGerm G Bm V δ →
      (∀ m k : ℕ, ∃ Vmk : Set P,
        (∃ O : Set P, IsOpen O ∧ Vmk = O ∩ Ct) ∧ (0 : P) ∈ Vmk ∧ Vmk ⊆ V.U 0 ∧
        ∃ δm : P → W.lvl m, (∀ v ∈ Vmk, W.toBase m (δm v) = δ v) ∧
          ContDiffOn ℝ (k : ℕ) δm Vmk) ∧
      (∃ V' : ScNbhdGerm (ScBanach.const P) Ct,
        (∀ m, V'.U m ⊆ V.U m) ∧ IsScSmoothGerm (F := W) V' δ)

end RoundTrip.V3_31
