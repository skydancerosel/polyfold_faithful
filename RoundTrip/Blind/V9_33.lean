import Polyfold
/-! Blind formalization of V9_33 (the text's Part II, §9.3, Example 9.3.5, p. 425 of the Springer
2021 book; 2017: Example 9.1, p. 313).

Text: four smooth `β^{±±}` with graphs `G^{±±}` define `Θ` in two ways; orienting by `±(1, 0)` at
the origin gives two orientations which coincide at `(0, 0)` but are otherwise different; there
are four possibilities to orient, and the second structure cannot necessarily be oriented to
coincide with the first.

Choices:
- The md does not list the `β^{±±}`; I reconstruct them as the picture requires (and as the
  vocabulary's docstrings for the example describe them): `β⁺⁺ = β` with `β(0) = 0`, `β(s) > 0`
  for `s ≠ 0`; `β⁻⁻ = -β`; `β⁺⁻ = β⁺⁺` on `s ≤ 0`, `β⁻⁻` on `s > 0`; `β⁻⁺ = -β⁺⁻`.  "Four smooth"
  is the hypothesis that all four are `C^∞` (`ContDiff ℝ ∞`; this forces `β` flat at `0`).  B is
  stated for EVERY such `β` (the md gives no specific one).  The first structure is
  `{G⁺⁺, G⁻⁻}` (`G1 true`, `G1 false`), the second `{G⁺⁻, G⁻⁺}` (`G2 true`, `G2 false`); graphs are
  the project's `graph2 β = {r | r 1 = β (r 0)}` (`#print`ed).
- Setting: `ℝ²` (the project's `rnPolyfold 2`) with identity morphisms only, the project's
  `EpGroupoid.trivial`.  `Θ(p) = #{b | p ∈ G1 b}` ("`Θ(x, y) = |{i ∈ {++, --} | (x, y) ∈ Gᵢ}|`").
- (a) "define `Θ` in two ways": `Θ` is a branched ep⁺-subgroupoid (project's
  `IsBranchedEpSubgroupoid`), `Θ(p) = #{b | p ∈ G2 b}` too, and both families, with weights `1`
  and `U = ℝ²`, are local branching structures of `Θ` at the origin (project's
  `LocalBranchingStructure`, sheets indexed by a type equivalent to `Bool`).
- Orientations of the graphs: the project's `graphOrientation hβ ε` (`#print`ed: the positive
  frames of `T_z(graph β)` are those with chart vector a positive multiple of `ε (1, β'(z₀))`),
  `ε = ±1`.  Since `β'(0) = 0`, `+` orients by `(1, 0)` at the origin and `-` by `(-1, 0)`.
  `liftB G hG ε (y) = ∑_{b : y ∈ G b} 1 · T_y(G b, ±)`, the oriented sum of (9.9) with sign
  `ε b` (`true` = `+`).  "Orientation of `Θ`": my `IsOrientationB` (Definition 9.3.2, copied from
  `RoundTrip/Blind/V9_30.lean`).
- (b) `T̂¹`: `G⁺⁺` by `(1, 0)`, `G⁻⁻` by `(-1, 0)`; `T̂²`: `G⁺⁻` by `(1, 0)`, `G⁻⁺` by `(-1, 0)`
  (sign function `id`).  Both are orientations, `T̂¹(0) = T̂²(0)`, and "otherwise different" is
  read as `T̂¹ ≠ T̂²` (some point where they differ).  (They coincide on `s < 0`, so the reading
  "different at every other point" would be false.)
- (c) "four possibilities to orient": for each structure, each of the four sign choices gives an
  orientation of `Θ`, and the four are pairwise different (injectivity in the sign choice).
- (d) "the second structure cannot necessarily be oriented to coincide with the first": some
  orientation of the first structure equals no orientation of the second.
- Nothing looks false to me.
-/
namespace RoundTrip.V9_33
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

open Classical in
/-- `∑_{i : y ∈ Mᵢ} σᵢ T_y(Mᵢ, oᵢ)` (as in `RoundTrip/Blind/V9_30.lean`). -/
noncomputable def orSumB {X : EpGroupoid Obj Mor} {Θ : Obj → ℚ} {x : Obj}
    (B : X.LocalBranchingStructure Θ x) (n : B.ι → ℕ)
    (o : ∀ i, X.PObj.SubmanifoldOrientation (B.M i) (n i)) (y : Obj) :
    X.PObj.OrTangent →₀ ℚ :=
  ∑ i with y ∈ B.M i, Finsupp.single ((o i).tangent y) (B.σ i)

/-- **Definition 9.3.2** (as in `RoundTrip/Blind/V9_30.lean`): `T` is an orientation of `Θ`. -/
structure IsOrientationB (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ)
    (T : Obj → X.PObj.OrTangent →₀ ℚ) : Prop where
  mem : ∀ x ∈ X.PObj.smoothSet,
    (∀ g, 0 ≤ T x g) ∧ ∀ g ∈ (T x).support, X.PObj.IsOrientedAt x g
  functor : ∀ φ : Mor, X.src φ ∈ X.PObj.smoothSet →
    Finsupp.mapDomain (MPolyfold.OrTangent.push (X.tangentMor φ)) (T (X.src φ)) = T (X.tgt φ)
  lifts : ∀ x ∈ X.PObj.smoothSet,
    Finsupp.mapDomain MPolyfold.OrTangent.carrier (T x) = X.tangentValue Θ x
  locRep : ∀ x ∈ EpGroupoid.supp Θ, ∃ (B : X.LocalBranchingStructure Θ x) (n : B.ι → ℕ)
    (o : ∀ i, X.PObj.SubmanifoldOrientation (B.M i) (n i)),
    ∀ y ∈ B.U, y ∈ X.PObj.smoothSet → T y = orSumB B n o y

end

/-- `ℝ²` with identity morphisms only. -/
noncomputable abbrev X2 : EpGroupoid (Fin 2 → ℝ) (Fin 2 → ℝ) := EpGroupoid.trivial (rnPolyfold 2)

/-- The first structure: `G1 true = graph β⁺⁺`, `G1 false = graph β⁻⁻`. -/
def G1 (β : ℝ → ℝ) : Bool → ℝ → ℝ
  | true => β
  | false => fun s => -β s

/-- The second structure: `G2 true = graph β⁺⁻`, `G2 false = graph β⁻⁺`. -/
noncomputable def G2 (β : ℝ → ℝ) : Bool → ℝ → ℝ
  | true => fun s => if s ≤ 0 then β s else -β s
  | false => fun s => if s ≤ 0 then -β s else β s

open Classical in
/-- `Θ(p) = |{b | p ∈ G1 b}|`. -/
noncomputable def ThetaB (β : ℝ → ℝ) (p : Fin 2 → ℝ) : ℚ :=
  ((Finset.univ.filter (fun b : Bool => p ∈ graph2 (G1 β b))).card : ℚ)

/-- The sign `+1` (`true`) or `-1` (`false`). -/
def signB : Bool → ℝ
  | true => 1
  | false => -1

lemma signB_ne_zero (b : Bool) : signB b ≠ 0 := by
  cases b <;> norm_num [signB]

open Classical in
/-- The oriented sum `∑_{b : y ∈ graph(G b)} T_y(graph(G b), signB (ε b) · (1, (G b)'))`. -/
noncomputable def liftB (G : Bool → ℝ → ℝ) (hG : ∀ b, ContDiff ℝ (⊤ : ℕ∞) (G b))
    (ε : Bool → Bool) (y : Fin 2 → ℝ) : (rnPolyfold 2).OrTangent →₀ ℚ :=
  ∑ b with y ∈ graph2 (G b),
    Finsupp.single ((graphOrientation (hG b) (signB (ε b)) (signB_ne_zero _)).tangent y) 1

/-- **Example 9.3.5**: for four smooth `β^{±±}` as above, the two structures `{G⁺⁺, G⁻⁻}`,
`{G⁺⁻, G⁻⁺}` define the same `Θ`; orienting by `±(1, 0)` at the origin gives orientations that
coincide at `0` but differ; each structure can be oriented in four different ways; some
orientation of the first is no orientation of the second. -/
def B : Prop :=
  open Classical in
  ∀ β : ℝ → ℝ, β 0 = 0 → (∀ s, s ≠ 0 → 0 < β s) →
  ∀ (h1 : ∀ b, ContDiff ℝ (⊤ : ℕ∞) (G1 β b)) (h2 : ∀ b, ContDiff ℝ (⊤ : ℕ∞) (G2 β b)),
    -- (a) `Θ` defined in two ways
    (X2.IsBranchedEpSubgroupoid (ThetaB β) ∧
      (∀ p, ThetaB β p = ((Finset.univ.filter (fun b : Bool => p ∈ graph2 (G2 β b))).card : ℚ)) ∧
      (∃ B : X2.LocalBranchingStructure (ThetaB β) 0, B.U = Set.univ ∧
        ∃ e : B.ι ≃ Bool, ∀ i, B.M i = graph2 (G1 β (e i)) ∧ B.σ i = 1) ∧
      (∃ B : X2.LocalBranchingStructure (ThetaB β) 0, B.U = Set.univ ∧
        ∃ e : B.ι ≃ Bool, ∀ i, B.M i = graph2 (G2 β (e i)) ∧ B.σ i = 1)) ∧
    -- (b) the two orientations `T̂¹`, `T̂²`
    (IsOrientationB X2 (ThetaB β) (liftB (G1 β) h1 id) ∧
      IsOrientationB X2 (ThetaB β) (liftB (G2 β) h2 id) ∧
      liftB (G1 β) h1 id 0 = liftB (G2 β) h2 id 0 ∧
      ∃ y, liftB (G1 β) h1 id y ≠ liftB (G2 β) h2 id y) ∧
    -- (c) four possibilities to orient each structure
    ((∀ ε, IsOrientationB X2 (ThetaB β) (liftB (G1 β) h1 ε) ∧
        IsOrientationB X2 (ThetaB β) (liftB (G2 β) h2 ε)) ∧
      Function.Injective (liftB (G1 β) h1) ∧ Function.Injective (liftB (G2 β) h2)) ∧
    -- (d) the second structure cannot always be oriented like the first
    (∃ ε, ∀ ε', liftB (G1 β) h1 ε ≠ liftB (G2 β) h2 ε')

end RoundTrip.V9_33
