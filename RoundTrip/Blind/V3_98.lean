import Polyfold
/-! Blind formalization of V3_98 (the text's Proposition 6.2, p. 201, along the solution set; cf.
Theorem 3.54 (1)).  `B` is the conjunction of (a) Proposition 6.2 for points of the solution set
and (b) the title's claim, local constancy of the index along the solution set.  Choices:
- Setting: `X Y : Type` (universe 0; nothing depends on the universe).  `PX : MPolyfold X`,
  `P : Y → X` with the fibrewise linear structure as instances on `P ⁻¹' {x}`, and
  `Bd : StrongBundle PX P` (Definition 2.51); `f` an sc-Fredholm section
  (`StrongBundle.IsScFredholmSection`, Definition 3.14; no tameness assumed).  Doubt: the
  project's docstring of `IsScFredholmSection` says the text states Definition 3.14 for tame
  strong bundles; if Proposition 6.2 presupposes a tame bundle, `B` is stronger than the text.
- "along the solution set": the points whose index is compared are zeros of `f` (`IsZeroAt`;
  they are smooth points since `f` is regularizing).  At a zero the linearization
  `f'(x) : T_xX → Y_x` is intrinsic; it is read in a strong bundle chart `c` around `x` as
  `D(f̂ ∘ r)(z)|_{T_zO} : T_zO → K_z` (`z = φ(x)` lifted to level `1`, `f̂` the principal part).
- `ind(f, x) = i` (`IndexAt`, defined here): in *every* strong bundle chart around `x` this
  operator is sc-Fredholm of index `i` (`ChartLinScFredholm`, as in my V3_68: `T_zO`, `K_z` with
  their induced sc-structures, `IsScFredholm`, `scIndex`).  "`ind(f, x₀) = ind(f, x₁)`" is
  `∃ i, IndexAt x₀ i ∧ IndexAt x₁ i` (it also asserts that the indices exist, which the text
  presupposes).
- (a) "connected by an sc-smooth path": a map `γ : ℝ → X` (`ℝ` as `Fin 1 → ℝ`, the M-polyfold
  `rnPolyfold 1`) which is sc-smooth on an open set containing `[0, 1]`
  (`MPolyfold.IsScSmoothOn`), with `γ(0) = x₀`, `γ(1) = x₁` (`IsScPathBetween`).  This reads an
  sc-smooth path `[0, 1] → X` as one extending sc-smoothly past the end points; after an
  orientation-preserving reparametrization constant near the end points every path on `[0, 1]` is
  of this kind, so nothing is lost.  The path itself need not lie in the solution set.
- (b) "locally constant along the solution set": every zero `x₀` has an open neighbourhood `V` in
  `X` such that `ind(f, y) = ind(f, x₀)` for every zero `y ∈ V`.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_98
open Polyfold

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- In the strong bundle chart `c` around `x`, with `z = φ(x)` (lifted to `z₁ ∈ E₁`), the
linearization `D(f̂ ∘ r)(z)|_{T_zO} : T_zO → K_z` is an sc-Fredholm operator of index `i` between
the sc-subspaces `T_zO = Dr(z)E ⊆ E` and `K_z = {h | (z, h) ∈ K} ⊆ F` (induced sc-structures). -/
def ChartLinScFredholm (c : StrongBundleChart PX P) (f : X → Y) (x : X) (i : ℤ) : Prop :=
  ∃ z₁ : c.φ.model.E.lvl 1, c.φ.model.E.toBase 1 z₁ = c.φ.toPartialEquiv x ∧
  ∃ Kz : Submodule ℝ (c.F.lvl 0),
    (Kz : Set (c.F.lvl 0)) = {h | (c.φ.toPartialEquiv x, h) ∈ c.K} ∧
  ∃ (hT : c.φ.model.E.IsScSubspace (rangeS (scDeriv c.U (StrongRetr.r c.R) z₁)))
    (hK : c.F.IsScSubspace Kz)
    (L₀ : ↥(c.φ.model.E.levelSub (rangeS (scDeriv c.U (StrongRetr.r c.R) z₁)) 0) →L[ℝ]
      ↥(c.F.levelSub Kz 0)),
    (∀ v, (L₀ v : c.F.lvl 0) =
      scDeriv c.U (c.principal f ∘ StrongRetr.r c.R) z₁ (v : c.φ.model.E.lvl 0)) ∧
    ∃ hL : @IsScOperator (c.φ.model.E.ofSubspace hT) (c.F.ofSubspace hK) L₀,
      IsScFredholm hL.toScOperator ∧ scIndex hL.toScOperator = i

/-- `ind(f, x) = i`: in every strong bundle chart of the bundle around `x`, the linearization
`f'(x)` is sc-Fredholm of index `i`. -/
def IndexAt (Bd : StrongBundle PX P) (f : X → Y) (x : X) (i : ℤ) : Prop :=
  ∀ c : StrongBundleChart PX P, Bd.IsChart c → x ∈ c.φ.source → ChartLinScFredholm c f x i

end

/-- `γ : ℝ → X` is an sc-smooth path from `x₀` to `x₁`: sc-smooth on an open neighbourhood of
`[0, 1]`, with `γ(0) = x₀` and `γ(1) = x₁`. -/
def IsScPathBetween {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (PX : MPolyfold X) (γ : (Fin 1 → ℝ) → X) (x₀ x₁ : X) : Prop :=
  ∃ W : Set (Fin 1 → ℝ), IsOpen W ∧ {t | 0 ≤ t 0 ∧ t 0 ≤ 1} ⊆ W ∧
    (rnPolyfold 1).IsScSmoothOn PX γ W ∧ γ (fun _ => 0) = x₀ ∧ γ (fun _ => 1) = x₁

/-- (a) Proposition 6.2 along the solution set: zeros of an sc-Fredholm section joined by an
sc-smooth path have the same Fredholm index; (b) the index is locally constant along the
solution set. -/
def B : Prop :=
  (∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x₀ x₁ : X),
    Bd.IsScFredholmSection f → IsZeroAt P f x₀ → IsZeroAt P f x₁ →
    (∃ γ : (Fin 1 → ℝ) → X, IsScPathBetween PX γ x₀ x₁) →
      ∃ i : ℤ, IndexAt Bd f x₀ i ∧ IndexAt Bd f x₁ i) ∧
  (∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x₀ : X),
    Bd.IsScFredholmSection f → IsZeroAt P f x₀ →
      ∃ V : Set X, IsOpen V ∧ x₀ ∈ V ∧
        ∀ y ∈ V, IsZeroAt P f y → ∃ i : ℤ, IndexAt Bd f x₀ i ∧ IndexAt Bd f y i)

end RoundTrip.V3_98
