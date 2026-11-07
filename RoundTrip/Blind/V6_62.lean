import Polyfold
/-! Blind formalization of V6_62 (the text's §6.5, Remark 6.42, p. 230), at a point.

Text: for an oriented `(f, o)` and an sc⁺-section `s` of `Y → X × [0, 1]`,
`f̂(x, t) = f(x) + s(x, t)` has a natural orientation from `o` and the standard orientation of
`[0, 1]`: for `L = (f − t)'(x)` oriented by `h = (a₁ ∧ … ∧ aₙ) ⊗ (b₁ ∧ … ∧ b_l)*`, the operator
`L̃(a, b) = La` on `T_{(x,t)}(X × [0, 1])` is oriented by
`h̃ = (a₁ ∧ … ∧ aₙ ∧ e) ⊗ (b₁ ∧ … ∧ b_l)*`, `e` the standard orientation of `[0, 1]`, and `L̃`
lies in the linearization space of `f̂` at `(x, t)`.

Choices:
- Setting: `X Y : Type` (universe 0), `PX : MPolyfold X`, `P : Y → X` with the fibrewise linear
  structure as instances, `Bd : StrongBundle PX P`, `f` an sc-Fredholm section (`hf`, Definition
  3.14) which is a section (`hsec : IsSection P f`, needed to lift it).
- `X × [0, 1]`: modelled, as the project does, by the product M-polyfold `ℝ¹ × X`
  (`(rnPolyfold 1).prod PX`, the `ℝ`-factor FIRST) at points `(t, x)` with `t ∈ [0, 1]`; the
  bundle "`Y → X × [0, 1]`" is the pull-back `π*Y` along `π = Prod.snd` (`Bd.pullback hπ`,
  Proposition 2.54; the sc-smoothness `hπ` of `π` and the paracompactness of `ℝ¹ × X` and `π*Y`
  are taken as hypotheses / instance binders, they hold anyway).  `s` is an sc⁺-section `S` of
  `π*Y` (Definition 2.52), `f̂ = f̃ + S` with `f̃(t, x) = f(x)` (`paramLift`, `sectionAdd`).  The
  tangent space at a boundary point `t ∈ {0, 1}` is the full `ℝ × T_xX` (M-polyfold tangent
  spaces are not one-sided), so nothing is lost by working in `ℝ¹ × X`.  That `f̂` is
  sc-Fredholm is a universally quantified hypothesis `hfh` (the text presupposes it to speak of
  its orientation).
- "At a point": B is stated at one smooth `x` and one `t ∈ [0, 1]`, read in a chart point `p` at
  `x` (any chart of the atlas, with the level-`1` lift `z`) and the product chart point
  `p.prodPt t q₀` at `(t, x)` (the project's product chart `(r ↦ r) × φ`, `q₀` a junk point of
  `π*Y` the construction needs; quantified).  The orientation `o_x` of `DET(f, x)` read in `p`
  is an arbitrary `ω ∈ ChartPoint.Or f p hf` (the construction is pointwise; every `o_x` is such an
  `ω`).
- `Lin(f, x)`: the project's `ChartPoint.linSet f p` (Definition 6.1 in the chart; trusted).
  "`L = (f − t)'(x)`" (with `t` here an sc⁺-section through `f(x)`, a letter clash with the time
  `t`): read as an arbitrary `L ∈ Lin(f, x)` (these are the operators `(f − t)'(x)` up to an
  sc⁺-operator, which is again of that form).
- `L̃(a, b) = La` read in the product chart: the project's `p.prodLin t q₀ L`
  (`= Γ⁻¹ (L ⊕ 0) A`, `A = prodT : T_{(t,z)} ≅ T_zO × ℝ¹`, `(σ, v) ↦ (v, σ)`, `Γ = prodK` the
  identity of the fibre).  "`L̃` lies in the linearization space of `f̂`": `L̃ ∈ Lin(f̂, (t, x))`.
- `h ↦ h̃`: the project's `extDet` (checked with `#print`: `TensorProduct.congr` of
  `a₁ ∧ … ∧ aₙ ↦ (a₁, 0) ∧ … ∧ (aₙ, 0) ∧ e`, `e = (0, 1)`, and of `λ*` of `coker L̃ = coker L`;
  WITHOUT the project's sign `(−1)^{dim coker L}` of `extDetN`), then transported to `det(L̃)` in
  the product chart by `conjDet` along `prodT⁻¹`, `prodK⁻¹`.  `e = (0, 1)` with `1 ∈ ℝ¹` is the
  standard orientation `∂_t` of `[0, 1]`.
- "`f̂` has a natural orientation ... `L̃` is oriented by `h̃`": there is an orientation `ô` of
  `DET(f̂, (t, x))` whose value at `L̃` is the ray of `h̃` for EVERY `L ∈ Lin(f, x)` and every `h`
  in the ray `ω(L)` (`Module.Ray.map`), i.e. the rule is consistent.  (Uniqueness is automatic,
  `Lin(f, x) ≠ ∅`; I state existence.)  The Fredholm property of `L` (needed by `extDet`) is a
  universally quantified proof.
- I BELIEVE THE LITERAL CONSISTENCY CLAIM IS FALSE, formalized literally anyway.  The text's
  map `h ↦ h̃` is not continuous in `L`: for `E = F = ℝ`, `L_s = s`, `L̃_s(a, b) = sa`, with the
  chart `P = 0` of `DET` (the text's `γ^0_S`, Definition 6.22), `h_s = 1 ⊗ 1*` has coordinate
  `1/s` and `h̃_s = e ⊗ 1*` coordinate `−1/s` for `s ≠ 0`, while at `s = 0` both `h_0 = 1 ⊗ 1*`
  and `h̃_0 = (1 ∧ e) ⊗ 1*` have coordinate `1`; so the rule reverses the orientation at the
  operators with odd `dim coker L` relative to a continuous one.  `Lin(f, x)` contains such
  paths `L₀ + s·a` (a rank-one sc⁺-operator `a`) as soon as `Lin(f, x)` has an operator with
  non-trivial kernel and cokernel, and the convex set `{L̃}` then carries no orientation with the
  stated values.  A correct form multiplies `h̃` by `(−1)^{dim coker L}` (or restricts to onto `L`).
-/
namespace RoundTrip.V6_62
open Polyfold

/-- Remark 6.42 at a point `(t, x)`: `L̃ ∈ Lin(f̂, (t, x))` for every `L ∈ Lin(f, x)`, and an
orientation of `DET(f̂, (t, x))` whose value at every `L̃` is the ray of `h̃`, `h ∈ ω(L)`. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    [ParacompactSpace ((Fin 1 → ℝ) × X)]
    [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))]
    (Bd : StrongBundle PX P) (hπ : ((rnPolyfold 1).prod PX).IsScSmoothMap PX Prod.snd)
    (f : X → Y) (hf : Bd.IsScFredholmSection f) (hsec : IsSection P f)
    (S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)),
    (Bd.pullback hπ).IsScPlusSection S →
    ∀ (hfh : (Bd.pullback hπ).IsScFredholmSection
        (sectionAdd (pullbackProj P Prod.snd) (paramLift f hsec) S))
      (x : X), x ∈ PX.smoothSet → ∀ (t : Fin 1 → ℝ), t ∈ Set.Icc 0 1 →
    ∀ (p : ChartPoint Bd x) (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))
      (ω : ChartPoint.Or f p hf),
      -- `L̃` lies in the linearization space of `f̂` at `(t, x)`
      (∀ L ∈ ChartPoint.linSet f p, p.prodLin t q₀ L ∈
        ChartPoint.linSet (sectionAdd (pullbackProj P Prod.snd) (paramLift f hsec) S)
          (p.prodPt t q₀)) ∧
      -- the natural orientation: `L̃` oriented by `h̃` for every `L ∈ Lin(f, x)`, `h ∈ ω(L)`
      ∃ ô : ChartPoint.Or (sectionAdd (pullbackProj P Prod.snd) (paramLift f hsec) S)
          (p.prodPt t q₀) hfh,
        ∀ (L : p.T →L[ℝ] p.K) (hL : L ∈ ChartPoint.linSet f p)
          (hL' : p.prodLin t q₀ L ∈
            ChartPoint.linSet (sectionAdd (pullbackProj P Prod.snd) (paramLift f hsec) S)
              (p.prodPt t q₀))
          (hLF : L.IsFredholm),
          ChartPoint.orEquivRay (p.prodPt t q₀) hfh hL' ô =
            Module.Ray.map ((extDet hLF).trans
              (conjDet (p.prodT t q₀).symm (p.prodK t q₀).symm (S := extOp L)
                (S' := p.prodLin t q₀ L) (fun v => by
                  simp [ChartPoint.prodLin, extConjOp])))
              (ChartPoint.orEquivRay p hf hL ω)

end RoundTrip.V6_62
