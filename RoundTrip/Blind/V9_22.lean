import Polyfold
/-! Blind formalization of V9_22 (the text's Part II, §9.2, Proposition 9.2.8, p. 413, and
Lemmas 9.2.9–9.2.11, pp. 414–417 of the Springer 2021 book; 2017: Proposition 9.3, p. 302, and
Lemmas 9.6–9.8, pp. 302–305).  Text (summary): at a bad point `x`, for a class `Ξ` of indices with
one tangent space `T_xMᵢ` there are `i₁, …, i_p ∈ Ξ`, a partition `Ξ = I¹ ⊔ ⋯ ⊔ I^p` and
sequences of good points `x^e_k → x` with `x^e_k ∈ Mᵢ` iff `i ∈ I^e`.  Lemmas 9.2.9–9.2.11:
`L ∩ C` has interior in `L = T₀M_{i₁}`; the `Mᵢ`, `i ∈ Ξ`, are graphs over a cone around `h₀`;
the map `a ↦ a + Bᵢ(a)` is injective with invertible derivative and its image contains a cone.

Choices:
- B is the conjunction of Proposition 9.2.8 (`Prop98`) and of the three lemmas (`Lemmas`), all
  for the same data: an ep-groupoid `X : EpGroupoid Obj Mor`, `Obj Mor : Type` (universe 0, as in
  the Chapter 7 blind files), a branched ep⁺-subgroupoid `Θ` (project's
  `IsBranchedEpSubgroupoid`), equidimensional read as `∃ n, X.IsNDimensional Θ n` (the standing
  hypothesis of §9.2), a bad point `x` (`x ∈ supp Θ`, not good: see below), ANY local branching
  structure `B` of `Θ` at `x` (project's `LocalBranchingStructure Θ x`; not required to be
  `n`-dimensional), and an index `i₀`; `Ξ = {j | T_xMⱼ = T_xM_{i₀}}` is the class of `i₀` for
  "same tangent space" (`T_xMⱼ` = project's `MPolyfold.submanifoldTangent`, as sets of `TX`).
- Good points: as in `RoundTrip/Blind/V9_21.lean` (`IsGoodAt` = Definition 9.2.2; a point is
  good if it is good for some local branching structure whose domain contains it).
- Proposition 9.2.8: `p : ℕ`, the representatives `i_e = rep e ∈ Ξ`, the partition as a map
  `part : ι → Fin p` (`I^e = {j ∈ Ξ | part j = e}`, values off `Ξ` are junk) with
  `part (rep e) = e` (so `i_e ∈ I^e` and every `I^e` is nonempty; I read `i_e` as a member of
  `I^e`), sequences `seq e : ℕ → Obj` of good points of `supp Θ` with `seq e → x`, and
  "`x^e_k ∈ Mⱼ` iff `j ∈ I^e`" for EVERY index `j` of the structure (so `x^e_k` lies on no `Mⱼ`
  with `j ∉ Ξ`).
- The lemmas live in a chart.  The text normalizes "`x = 0`, `C` the partial quadrant"; I
  quantify over every chart `φ` of the object M-polyfold (project's `IsChart`) with `x` in its
  source, `φ(x) = 0`, and partial quadrant presented as `C = T⁻¹([0,∞)^m ⊕ W)` for some
  sc-isomorphism `T` (as in the project's `IsTangentReducedAt`).  `E` = level 0 of the model
  space.  `L` = the linear span in `E` of the chart image of `T_xM_{i₀}` (project's
  `MPolyfold.chartTangent`; the span is the image itself if that is a subspace); all `Mⱼ`,
  `j ∈ Ξ`, have this `L`.  `Mc j = φ(Mⱼ ∩ dom φ) ⊆ E`.
- Lemma 9.2.9: `int_L(L ∩ C) ≠ ∅` (relative interior in `L`).
- `h₀`, the cone and the projection are not specified by the summary: I quantify over EVERY
  `h₀ ≠ 0` in the relative interior of `L ∩ C` and EVERY continuous linear projection
  `Pr : E → L` (`Pr = id` on `L`); the cone around `h₀` is `K = {t·h | t > 0, h ∈ L,
  ‖h − h₀‖ < r}` for some `r > 0`.  (This is a strengthening if the text uses one particular
  `h₀`, complement or projection.)
- Lemma 9.2.10 ("graphs over a cone"): for `k ∈ K` with `‖k‖ < δ'` there is exactly one
  `e ∈ Mc j` with `‖e‖ < δ` and `Pr e = k`.
- Lemma 9.2.11: `Bᵢ` is not defined in the summary.  I read `a ↦ a + Bᵢ(a)` as `Pr ∘ Γ` for a
  graph parametrization `Γ` of `Mc j` over `L ∩ C` near `0` (as in Part I's Proposition 4.9:
  `Γ(a) = a + δ(a)`), so `Bᵢ(a) = Pr(Γ a) − a`; the claim is: there are `ρ > 0` and `Γ : L → E`,
  `C¹` on `D = {a ∈ L ∩ C | ‖a‖ < ρ}` with `Γ(0) = 0`, derivative the inclusion at `0`,
  `Γ(D) ⊆ Mc j` covering a neighbourhood of `0` in `Mc j`, such that `Pr ∘ Γ` is injective on
  `D`, has bijective derivative (within `D`) at every point of `D`, and its image contains
  `K ∩ {‖k‖ < δ'}`.
- Nothing looks false to me in this reading.
-/
namespace RoundTrip.V9_22
open Polyfold

/-- The text's good point `y` of the local branching structure `B` (Definition 9.2.2). -/
def IsGoodAt {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
    {Θ : Obj → ℚ} {x : Obj} (B : X.LocalBranchingStructure Θ x) (y : Obj) : Prop :=
  y ∈ ⋃ i, B.M i ∧
    ∃ V : Set Obj, IsOpen V ∧ y ∈ V ∧ V ⊆ B.U ∧
      ∀ i j : B.ι, y ∈ B.M i ∩ B.M j → B.M i ∩ V = B.M j ∩ V

/-- `y` is a good point of `Θ`: good for some local branching structure whose domain contains
`y`. -/
def IsGoodPt {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (Θ : Obj → ℚ) (y : Obj) : Prop :=
  ∃ (x : Obj) (B : X.LocalBranchingStructure Θ x), y ∈ B.U ∧ IsGoodAt B y

/-- The class `Ξ` of `i₀`: the indices `j` with `T_xMⱼ = T_xM_{i₀}`. -/
def Xi {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
    {Θ : Obj → ℚ} {x : Obj} (B : X.LocalBranchingStructure Θ x) (i₀ : B.ι) : Set B.ι :=
  {j | X.PObj.submanifoldTangent (B.M j) x = X.PObj.submanifoldTangent (B.M i₀) x}

/-- **Proposition 9.2.8** for the structure `B` at `x` and the class of `i₀`. -/
def Prop98 {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (Θ : Obj → ℚ) {x : Obj} (B : X.LocalBranchingStructure Θ x) (i₀ : B.ι) : Prop :=
  ∃ (p : ℕ) (rep : Fin p → B.ι) (part : B.ι → Fin p) (seq : Fin p → ℕ → Obj),
    (∀ e, rep e ∈ Xi B i₀ ∧ part (rep e) = e) ∧
    (∀ e k, seq e k ∈ EpGroupoid.supp Θ ∧ IsGoodPt X Θ (seq e k)) ∧
    (∀ e k (j : B.ι), seq e k ∈ B.M j ↔ (j ∈ Xi B i₀ ∧ part j = e)) ∧
    (∀ e, Filter.Tendsto (seq e) Filter.atTop (nhds x))

/-- **Lemmas 9.2.9–9.2.11** in a chart `φ` at `x` with `φ(x) = 0`, for the class of `i₀`. -/
def Lemmas {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    {Θ : Obj → ℚ} {x : Obj} (B : X.LocalBranchingStructure Θ x) (i₀ : B.ι)
    {φ : MChart Obj} (hφ : X.PObj.IsChart φ) : Prop :=
  let L : Submodule ℝ (φ.model.E.lvl 0) :=
    Submodule.span ℝ (X.PObj.chartTangent hφ (B.M i₀) x)
  let C : Set (φ.model.E.lvl 0) := φ.model.C
  let Mc : B.ι → Set (φ.model.E.lvl 0) := fun j =>
    φ.toPartialEquiv '' (B.M j ∩ φ.toPartialEquiv.source)
  -- Lemma 9.2.9: `L ∩ C` has nonempty interior in `L`
  (∃ h : L, (h : φ.model.E.lvl 0) ∈ C ∧ ∃ r > (0 : ℝ), ∀ v : L, ‖v - h‖ < r →
      (v : φ.model.E.lvl 0) ∈ C) ∧
  -- Lemmas 9.2.10, 9.2.11, for every interior point `h₀ ≠ 0` and every projection onto `L`
  (∀ h₀ : L, h₀ ≠ 0 →
    (∃ r > (0 : ℝ), ∀ v : L, ‖v - h₀‖ < r → (v : φ.model.E.lvl 0) ∈ C) →
    ∀ Pr : φ.model.E.lvl 0 →L[ℝ] L, (∀ v : L, Pr v = v) →
    ∃ r > (0 : ℝ), ∃ δ > (0 : ℝ), ∃ δ' > (0 : ℝ),
      let K : Set L := {k | ∃ t > (0 : ℝ), ∃ h : L, ‖h - h₀‖ < r ∧ k = t • h}
      ∀ j ∈ Xi B i₀,
        -- Lemma 9.2.10: `Mⱼ` is a graph over the cone `K` near `0`
        (∀ k ∈ K, ‖k‖ < δ' →
          ∃! e : φ.model.E.lvl 0, e ∈ Mc j ∧ ‖e‖ < δ ∧ Pr e = k) ∧
        -- Lemma 9.2.11: `a ↦ a + Bⱼ(a) = Pr (Γ a)` for a graph parametrization `Γ` of `Mⱼ`
        (∃ ρ > (0 : ℝ), ∃ Γ : L → φ.model.E.lvl 0,
          let D : Set L := {a | (a : φ.model.E.lvl 0) ∈ C ∧ ‖a‖ < ρ}
          Γ '' D ⊆ Mc j ∧
          (∃ Wn ∈ nhds (0 : φ.model.E.lvl 0), Mc j ∩ Wn ⊆ Γ '' D) ∧
          ContDiffOn ℝ 1 Γ D ∧ Γ 0 = 0 ∧ HasFDerivWithinAt Γ L.subtypeL D 0 ∧
          Set.InjOn (fun a => Pr (Γ a)) D ∧
          (∀ a ∈ D, Function.Bijective (fderivWithin ℝ (fun a => Pr (Γ a)) D a)) ∧
          (∀ k ∈ K, ‖k‖ < δ' → k ∈ (fun a => Pr (Γ a)) '' D)))

/-- **Proposition 9.2.8 and Lemmas 9.2.9–9.2.11**: at a bad point `x` of an equidimensional `Θ`,
for every local branching structure at `x` and every class `Ξ` of equal tangent spaces, the
partition and the good sequences exist, and in every chart at `x` with `φ(x) = 0` the sheets of
`Ξ` are graphs over cones in `L = T₀Mᵢ`. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ), X.IsBranchedEpSubgroupoid Θ →
    (∃ n : ℕ, X.IsNDimensional Θ n) →
    ∀ x : Obj, x ∈ EpGroupoid.supp Θ → ¬ IsGoodPt X Θ x →
    ∀ (B : X.LocalBranchingStructure Θ x) (i₀ : B.ι),
      Prop98 X Θ B i₀ ∧
      ∀ (φ : MChart Obj) (hφ : X.PObj.IsChart φ), x ∈ φ.toPartialEquiv.source →
        φ.toPartialEquiv x = 0 →
        (∃ (m : ℕ) (W : ScBanach) (T : ScIso φ.model.E ((ScBanach.const (Fin m → ℝ)).prod W)),
          φ.model.C = ⇑(T.lvl 0) ⁻¹' quadrant m W 0) →
        Lemmas X B i₀ hφ

end RoundTrip.V9_22
