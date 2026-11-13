import Polyfold.Chapter3.MainTheorems2021
import Polyfold.Chapter3.LinearizationChartsScG
import Polyfold.Chapter3.GoodComplementClosed

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021): **Theorem 3.6.8** (p. 136)
with the steps of its proof (pp. 136–140), and **Theorem 3.1.22** (p. 100), each in one statement
(preprint: Theorems 3.54, 3.19).  Numbers and pages are the 2021 text's.

# The implicit function theorems in book form

## The text, paraphrased

(Theorem 3.6.8) Let `f` be an sc-Fredholm section of a tame strong bundle, `f(x) = 0` and
`(f, x)` in good position.  There is an open `V ∋ x` such that `S = {y ∈ V | f(y) = 0}` has:
(1) `(f, y)` is in good position at every `y ∈ S`; (2) `S` is a sub-M-polyfold whose induced
structure is equivalent to a smooth manifold with boundary with corners.  (Proof, p. 139) (4) at
every zero `y ∈ V`, `f'(y)` is surjective and `ker f'(y)` is in good position; with
`d = dim ker f'(x)`, `S` has the `d`-dimensional tangent germ property (Definition 3.2.1), and
Theorem 3.2.3 applies.
(Theorem 3.1.22) Let `d_X ≡ 0`, `f` an sc-Fredholm section, `f(x₀) = 0`.  Then `f'(x₀)` is
sc-Fredholm.  If it is surjective, there is an open `U ∋ x₀` such that `S(f, U)` is a smooth
manifold whose dimension is the Fredholm index, and `U` can be taken such that `f'(y)` is
surjective at every `y ∈ S(f, U)` and `ker f'(y) = T_yS(f, U)`.

## What is formalized

All with the 2021 notions of `MainTheorems2021.lean` (`IsScFredholmSectionTame2021`,
`IsGoodPositionGermTame2021`: germ data and good position in a tame chart, the reading of "tame
strong bundle", row V3.103).

* `theorem_3_6_8_book`: Theorem 3.6.8 (1), (2), with, at every zero of `V`, `f'(y)` onto in every
  strong bundle chart with the same index `d` (`IsSurjLinOfIndex`, property (4) of the proof), and
  `S` a sub-M-polyfold whose induced structure is that of a `d`-dimensional manifold with boundary
  with corners.  From `theorem_3_1_26_index`.
* `theorem_3_6_8_tangentGermProperty`: the last step of the proof: an open `U ∋ x₀` and
  `d = ind f'(x₀) = dim ker f'(x₀)` such that `S(f, U)` has the `d`-dimensional tangent germ
  property **as written in 2021 Definition 3.2.1** (`HasTangentGermProperty2021`), and Theorem
  3.2.3 applies: `S(f, U)` is a sub-M-polyfold with tame induced structure of a `d`-dimensional
  manifold with boundary with corners.  The proof is the first half of `theorem_3_1_26_index`.
* `theorem_3_1_22_book`: Theorem 3.1.22 except its last clause: `f'(x₀)` is sc-Fredholm in every
  strong bundle chart around `x₀` (`StrongBundle.linAt_isScFredholm`); if `f'(x₀)` is onto
  (`IsLinSurjAt`), there are `U` and `d` with `f'(y)` onto of index `d = dim ker f'(y)` at every
  zero `y ∈ U`, and `S(f, U)` a sub-M-polyfold with the structure of a `d`-dimensional manifold
  without boundary (`theorem_3_1_22_of_surjective`).

## What is not here

* **"`ker f'(y) = T_yS(f, U)`"** (Theorem 3.1.22, last clause) is stated here in the chart of the
  tangent germ data (`theorem_3_6_8_ker_eq_tangent`, row V3.99). In `T_yX`, with the intrinsic
  linearization `StrongBundle.linIntr` (chart-independent), it is `theorem_3_1_22_book_ker`
  (`GapP1_Theorem3122Ker.lean`, 2026-11-12).
* The graph description of the proof, `ψφ(S) = {v + σ(v) | v ∈ V'}` (row V3.48,
  `theorem_3_6_8_graph`), is a step of the proof stated in the chart at `x₀`; it is not repeated
  here.
-/

open Set Filter Topology Function Module

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

open StrongBundle StrongRetr

/-- **2021 Theorem 3.6.8, p. 136** (preprint: Theorem 3.54), in book form, for the 2021
definitions: for an sc-Fredholm section `f` with germ data in tame charts and a zero `x₀` in good
position, there are an open `V ∋ x₀` and `d` such that (1) every zero `y ∈ V` is in good position,
with (property (4) of the proof) `f'(y)` onto in every strong bundle chart, of index
`d = dim ker f'(y)`; and (2) `S = {y ∈ V | f(y) = 0}` is a sub-M-polyfold whose induced structure
is equivalent to that of a `d`-dimensional manifold with boundary with corners (and is tame).
From `theorem_3_1_26_index` by the dictionary of `MainTheorems2021.lean`. -/
theorem theorem_3_6_8_book (hf : B.IsScFredholmSectionTame2021 f) {x₀ : X}
    (hg : B.IsGoodPositionGermTame2021 f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ (V : Set X) (d : ℕ), IsOpen V ∧ x₀ ∈ V ∧
      (∀ y ∈ V, IsZeroAt P f y → B.IsGoodPositionGermTame2021 f y ∧ B.IsSurjLinOfIndex f y d) ∧
      ∃ hsub : PX.IsSubMPolyfold {y ∈ V | IsZeroAt P f y},
        haveI := PX.paracompactSpace_subtype {y ∈ V | IsZeroAt P f y}
        (MPolyfold.subPolyfold hsub).IsTame ∧
          (MPolyfold.subPolyfold hsub).IsManifoldWithCorners d := by
  obtain ⟨V, d, hVo, hxV, hall, -, hsub, htame, hman⟩ :=
    theorem_3_1_26_index (isScFredholmSectionTame2021_iff.1 hf) hx₀
      (isGoodPositionGermTame2021_iff.1 hg)
  exact ⟨V, d, hVo, hxV, fun y hy hy0 =>
    ⟨isGoodPositionGermTame2021_iff.2 (hall y hy hy0).1, (hall y hy hy0).2⟩, hsub, htame, hman⟩

/-- **The tangent germ property in the proof of 2021 Theorem 3.6.8** (p. 139; preprint p. 115),
in book form: for an sc-Fredholm section with germ data in tame charts and a zero `x₀` in good
position, there are an open `U ∋ x₀` and `d` with `f'(x₀)` onto of index `d = dim ker f'(x₀)` such
that the solution set `S(f, U)` has the `d`-dimensional tangent germ property of 2021
Definition 3.2.1 as written, and (Theorem 3.2.3) is a sub-M-polyfold whose induced structure is
tame and that of a `d`-dimensional manifold with boundary with corners. -/
theorem theorem_3_6_8_tangentGermProperty (hf : B.IsScFredholmSectionTame2021 f) {x₀ : X}
    (hg : B.IsGoodPositionGermTame2021 f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ (U : Set X) (d : ℕ), IsOpen U ∧ x₀ ∈ U ∧ B.IsSurjLinOfIndex f x₀ d ∧
      PX.HasTangentGermProperty2021 {y ∈ U | IsZeroAt P f y} d ∧
      ∃ hsub : PX.IsSubMPolyfold {y ∈ U | IsZeroAt P f y},
        haveI := PX.paracompactSpace_subtype {y ∈ U | IsZeroAt P f y}
        (MPolyfold.subPolyfold hsub).IsTame ∧
          (MPolyfold.subPolyfold hsub).IsManifoldWithCorners d := by
  have hf' := isScFredholmSectionTame2021_iff.1 hf
  have hg' := isGoodPositionGermTame2021_iff.1 hg
  obtain ⟨Vx, hVxo, hxVx, hall⟩ := theorem_3_6_8_one' hf' hg' hx₀
  obtain ⟨d, D, -, hsub, hdim, hind⟩ :=
    theorem_3_6_8_two_index hf'.isScSmooth hg' hx₀ hVxo hxVx hall
  set S' := {y ∈ D.φ.source | IsZeroAt P f y} with hS'
  -- every point of `S(f, U)` has regular data of Definition 3.2.1 (b) for `S(f, U)`, dimension `d`
  have hS'reg : ∀ y ∈ S', ∃ d' : PX.TangentGermChart S' y d, d'.IsRegular := by
    intro y hy
    obtain ⟨dy, Dy, hregy, hsuby, -⟩ := theorem_3_6_8_two hf'.isScSmooth.1
      (hall y (hsub hy.1) hy.2) hy.2 (D.φ.isOpen_source.inter hVxo) ⟨hy.1, hsub hy.1⟩
      fun z hz hz0 => hall z hz.2 hz0
    have hdy : dy = d := hdim y ⟨hy.2, hy.1⟩ dy Dy
    subst hdy
    have himage : Dy.φ '' (S' ∩ Dy.φ.source) =
        (fun v : Dy.N => (v : Dy.φ.model.E 0) + Dy.δ v) '' Dy.V := by
      rw [← Dy.image_eq]
      congr 1
      ext z
      constructor
      · rintro ⟨⟨-, hz0⟩, hzsrc⟩; exact ⟨hz0, hzsrc⟩
      · rintro ⟨hz0, hzsrc⟩; exact ⟨⟨(hsuby hzsrc).1, hz0⟩, hzsrc⟩
    exact ⟨Dy.shrink S' subset_rfl Dy.φ.isOpen_source Dy.mem_source Dy.V_relOpen Dy.zero_mem_V
      subset_rfl himage, Dy.shrink_isRegular S' subset_rfl Dy.φ.isOpen_source Dy.mem_source
      Dy.V_relOpen Dy.zero_mem_V subset_rfl himage hregy.isScSmooth hregy.π_mem⟩
  have hprop : PX.HasTangentGermProperty2021 S' d :=
    (PX.hasTangentGermProperty2021_iff).2
      ⟨fun y hy => hf'.mem_smoothSet_of_isZeroAt hy.2, fun y hy => ⟨(hS'reg y hy).choose⟩⟩
  have hne : S'.Nonempty := ⟨x₀, D.mem_source, hx₀⟩
  obtain ⟨hsubM, htameS, hman, -⟩ := theorem_3_2_3_of_isRegular PX hne hS'reg
  exact ⟨D.φ.source, d, D.φ.isOpen_source, D.mem_source, hind, hprop, hsubM, htameS, hman⟩

/-- **2021 Theorem 3.1.22, p. 100 (implicit function theorem, interior case)** (preprint: Theorem
3.19), in book form except for its last clause, for the 2021 definitions.  Let `d_X ≡ 0`, `f` an
sc-Fredholm section with germ data in tame charts and `f(x₀) = 0`.  Then (a) `f'(x₀)` is
sc-Fredholm: in every strong bundle chart around `x₀`, at the level-`1` point `z` over `φ(x₀)`,
`Lin(z) : T_zO → K_z` is the restriction of an sc-operator to sc-subspaces and an sc-Fredholm
operator; (b) if `f'(x₀)` is surjective (`IsLinSurjAt`), there are an open `U ∋ x₀` and `d` such
that at every zero `y ∈ U` the linearization `f'(y)` is surjective, Fredholm of index
`d = dim ker f'(y)` (in every chart), and `S(f, U)` is a sub-M-polyfold whose induced structure is
that of a `d`-dimensional manifold without boundary — its dimension is the Fredholm index.
"`ker f'(y) = T_yS(f, U)`" is stated in a chart: `theorem_3_6_8_ker_eq_tangent`; in `T_yX` it is
`theorem_3_1_22_book_ker` (`GapP1_Theorem3122Ker.lean`). -/
theorem theorem_3_1_22_book (hX : PX.IsWithoutBoundary) (hf : B.IsScFredholmSectionTame2021 f)
    {x₀ : X} (hx₀ : IsZeroAt P f x₀) :
    (∀ c : StrongBundleChart PX P, B.IsChart c → x₀ ∈ c.φ.source →
      ∀ (z : c.φ.model.E 1) (_ : c.φ.model.E.toBase 1 z = c.φ x₀)
        (hzU : c.φ.model.E.toBase 1 z ∈ c.U),
        ∃ (hD : IsScOperator (scDeriv c.U (c.principal f ∘ r c.R) z))
          (hT : c.φ.model.E.IsScSubspace (rangeS (scDeriv c.U (r c.R) z)))
          (hK : c.F.IsScSubspace (rangeS (ρCLM c.isRetraction hzU)))
          (hTK : ∀ x ∈ rangeS (scDeriv c.U (r c.R) z),
            hD.toScOperator 0 x ∈ rangeS (ρCLM c.isRetraction hzU)),
          (∀ x : (c.φ.model.E.ofSubspace hT) 0,
            ((hD.toScOperator.restrict hT hK hTK 0 x).1 : c.F 0) =
              linAt c.U c.R (c.principal f) z ⟨x.1, x.2⟩) ∧
          IsScFredholm (hD.toScOperator.restrict hT hK hTK)) ∧
    (B.IsLinSurjAt f x₀ →
      ∃ (U : Set X) (d : ℕ), IsOpen U ∧ x₀ ∈ U ∧
        (∀ y ∈ U, IsZeroAt P f y → B.IsSurjLinOfIndex f y d) ∧
        ∃ hsub : PX.IsSubMPolyfold {y ∈ U | IsZeroAt P f y},
          haveI := PX.paracompactSpace_subtype {y ∈ U | IsZeroAt P f y}
          (MPolyfold.subPolyfold hsub).IsManifoldWithCorners d ∧
            (MPolyfold.subPolyfold hsub).IsWithoutBoundary) := by
  have hf' := isScFredholmSectionTame2021_iff.1 hf
  refine ⟨fun c hc hxV z hz hzU => ?_, fun hsurj => ?_⟩
  · obtain ⟨hD, hT, hK, hTK, h1, h2, -⟩ :=
      StrongBundle.linAt_isScFredholm hf'.toIsScFredholmSection hx₀ hc hxV hz hzU
    exact ⟨hD, hT, hK, hTK, h1, h2⟩
  · obtain ⟨U, d, hUo, hxU, hall, -, hsub, -, hman, hbd⟩ :=
      theorem_3_1_22_of_surjective hX hf' hx₀ hsurj
    exact ⟨U, d, hUo, hxU, fun y hy hy0 => (hall y hy hy0).2, hsub, hman, hbd⟩

end Polyfold
