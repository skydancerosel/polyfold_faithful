import Polyfold.Chapter3.TangentGermProjecting

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §3.2: **Theorem 3.2.3**
(p. 106; preprint: Theorem 3.27) with **Definition 3.2.1** (p. 104) as written, parts (1) and (2).

# Theorem 3.2.3 with Definition 3.2.1 as written, including part (2)

## The text, paraphrased

(Definition 3.2.1) `M ⊆ X_∞` has the `n`-dimensional tangent germ property if every `x ∈ M` has
data `(ϕ, N, Y, V, δ)`: a chart `ϕ` with `ϕ(x) = 0`, an `n`-dimensional subspace `N` in good
position with good complement `Y`, and `δ : V → Y` an sc^∞-germ with
`ϕ(M ∩ U) = {v + δ(v) | v ∈ V}`.  (Theorem 3.2.3) Then (1) `M` is a sub-M-polyfold whose induced
structure is tame and equivalent to that of a manifold with boundary with corners, and (2) at
every `x ∈ M` the map `y ↦ π ∘ ϕ(y)` (`π` the projection along `Y` onto `N`) is a chart of `M`.

## What is formalized

* `MPolyfold.TangentGermChart.IsRegular.toTangentGermChart2021`: regular data
  (`TangentGermChart.IsRegular`: `δ` sc-smooth on `V`, `π` maps the chart's model into `C`) give
  data of Definition 3.2.1 as written whose associated data are again regular (`δ` is changed
  off `V` only).
* **`theorem_3_2_3_2021def_isChart`**: Theorem 3.2.3 for `HasTangentGermProperty2021`: (1) as in
  `theorem_3_2_3_2021def`, (2) `y ↦ π ∘ ϕ(y)` is a chart of the induced structure for every datum
  of Definition 3.2.1 whose associated data are regular, and such data exist at every point of
  `M`.

## Reading

Part (2) is stated for the data with the regularity conditions of `TangentGermChart.IsRegular`
(the chart `TangentGermChart.chart` is built from them); every point of `M` has such data
(`HasTangentGermProperty.exists_isRegular`), so (2) is not vacuous.
-/

open Set

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold.TangentGermChart

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {M : Set X} {x : X} {n : ℕ} {d : P.TangentGermChart M x n}

/-- **Regular data give regular data of Definition 3.2.1 as written**: for regular data `d`, the
data of `d.toTangentGermChart2021` are regular again (their `δ` is that of `d` on `V`, and
`π` is unchanged). -/
theorem IsRegular.toTangentGermChart2021 (hreg : d.IsRegular) :
    d.toTangentGermChart2021.toTangentGermChart.IsRegular where
  isScSmooth := hreg.isScSmooth.congr d.V_isRelOpenInQuadrant.isScDomain
    fun _ hv => (d.toTangentGermChart2021.δ'_of_mem hv).symm
  π_mem := hreg.π_mem

end MPolyfold.TangentGermChart

section Thm323

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

/-- **2021 Theorem 3.2.3, p. 106, parts (1) and (2), with Definition 3.2.1 as written**
(`HasTangentGermProperty2021`): a nonempty `M ⊆ X` with the `n`-dimensional tangent germ property
is a sub-M-polyfold whose induced structure is tame and that of an `n`-dimensional manifold with
boundary with corners (1); for every datum `d` of Definition 3.2.1 at `x ∈ M` whose associated
data are regular, `y ↦ π ∘ ϕ(y)` is a chart of `M` around `x` (2); and every point of `M` has
such a datum. -/
theorem theorem_3_2_3_2021def_isChart (P : MPolyfold X) {M : Set X} {n : ℕ} (hne : M.Nonempty)
    (hM : P.HasTangentGermProperty2021 M n) :
    ∃ hsub : P.IsSubMPolyfold M,
      haveI := P.paracompactSpace_subtype M
      (MPolyfold.subPolyfold hsub).IsTame ∧ (MPolyfold.subPolyfold hsub).IsManifoldWithCorners n ∧
      (∀ x (hx : x ∈ M) (d : P.TangentGermChart2021 M x n)
        (hreg : d.toTangentGermChart.IsRegular) (a₀ : M),
        (MPolyfold.subPolyfold hsub).IsChart (d.toTangentGermChart.chart hreg a₀) ∧
          (⟨x, hx⟩ : M) ∈ (d.toTangentGermChart.chart hreg a₀).source) ∧
      ∀ x ∈ M, ∃ d : P.TangentGermChart2021 M x n, d.toTangentGermChart.IsRegular := by
  have hM' := (MPolyfold.hasTangentGermProperty2021_iff P).1 hM
  obtain ⟨hsub, h1, h2, h3⟩ := theorem_3_2_3 P hne hM'
  refine ⟨hsub, h1, h2, fun x hx d hreg a₀ => h3 x hx _ hreg a₀, fun x hx => ?_⟩
  obtain ⟨d, hreg⟩ := hM'.exists_isRegular hx
  exact ⟨d.toTangentGermChart2021, hreg.toTangentGermChart2021⟩

end Thm323

end Polyfold
