import Polyfold.Chapter3.TangentGerm
import Polyfold.Chapter3.GoodPositionSc

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2014 preprint), §3.1 and
§3.2: **Definition 3.2.1** (p. 104, the `n`-dimensional tangent germ property; preprint: Definition
3.25) with the good complement of **Definition 3.1.24** (p. 102; preprint: Definition 3.21), which
is an sc-complement, and **Lemma 3.6.9** (p. 139; preprint: Lemma 3.55).  Numbers and pages are the
2021 text's, the preprint ones in parentheses.

# The book's good complement is closed: Definition 3.2.1 as written

## The text, paraphrased

(Definition 3.1.24, p. 102) `N` is in good position to the partial quadrant `C` if the interior of
`N ∩ C` in `N` is nonempty and `N` possesses an **sc-complement** `P`, `E = N ⊕ P`, with an
`ε > 0` such that for `(n, p) ∈ N × P` with `|p|₀ ≤ ε|n|₀` the statements `n ∈ C` and `n + p ∈ C`
are equivalent; such a `P` is a good complement.  (Definition 3.2.1, p. 104) `M ⊆ X` has the
`n`-dimensional tangent germ property if (a) `M ⊆ X_∞` and (b) every `x ∈ M` has a chart
`ϕ : (U, x) → (O, 0)` onto a tame retract `(O, C, E)`, an `n`-dimensional smooth subspace `N ⊆ E`
in good position to `C` with a good complement `Y`, a relatively open neighbourhood `V` of `0` in
`N ∩ C` and a continuous `δ : V → Y` with (1) `ϕ(M ∩ U) = {v + δ(v) | v ∈ V}` and (2) `δ` an
sc^∞-germ at `0` with `δ(0) = 0`, `Dδ(0) = 0`.

## What is formalized

The project's datum `MPolyfold.TangentGermChart` (`TangentGerm.lean`) carries the **added
hypothesis `isClosed_Y`** ("`Y` closed"; comparison rows V3.22 and V3.49, and the "`Y` closed"
chips of V3.48 and V3.80), used to make the projection `π : E → N` along `Y` continuous.  This
file shows that the hypothesis is implied by the book's notion:

* `MPolyfold.TangentGermChart2021`: **Definition 3.2.1 (b) as written**: good position in the
  sense of Definition 3.1.24 (`IsInGoodPositionSc`), the good complement `Y` an sc-complement
  (`IsScGoodComplement`), `δ` defined on `V` only (`δ_mem_Y : ∀ v ∈ V, δ v ∈ Y`), and the
  sc^∞-germ property in the `k`-dependent reading `IsScInftyGermAt` (the weakest reading; the
  fixed-germ reading `IsScSmoothGerm` and set-sense sc-smoothness imply it,
  `TangentGermChart2021.germ_of_isScSmoothGerm`, `IsScSmooth.isScInftyGermAt`).  No closedness
  and no smoothness of `N` are asked.
* `MPolyfold.TangentGermChart2021.toTangentGermChart`: **the bridge**: the book's datum gives the
  Lean datum.  An sc-complement is closed (`IsScGoodComplement.isClosed`) and `N` is then smooth
  (`IsScGoodComplement.le_smooth`, Proposition 1.1.7); `δ` is extended by `0` off `V`.
* `MPolyfold.TangentGermChart.toTangentGermChart2021`: the converse: the Lean datum is a book
  datum (a closed good complement of a smooth `N` is an sc-complement,
  `IsGoodComplement.isScGoodComplement`).
* `MPolyfold.HasTangentGermProperty2021` (**Definition 3.2.1 as written**) and
  `MPolyfold.hasTangentGermProperty2021_iff`: it is the project's `HasTangentGermProperty`.  So
  the "`Y` closed" of rows V3.22 and V3.49 is not an added hypothesis: both rows read as
  *restated*.
* `Polyfold.lemma_3_6_9_2021`: **Lemma 3.6.9** (`lemma_3_55_relOpen`, row V3.80) with the good
  complement in the book's sense, which supplies the closedness hypothesis `hYc` of
  `lemma_3_55_relOpen`.

## What the text leaves implicit, and the choices made

* **"sc^∞-germ" in (2)** is read with `k`-dependent neighbourhoods (`IsScInftyGermAt`), as in
  `TangentGerm.lean`; the stronger readings imply it.
* **`δ : V → Y`** is a map on `V`; the Lean datum extends it by `0` outside `V`, which changes
  nothing on `V` (`Set.indicator`).
* **Smoothness of `N`** is part of Definition 3.2.1 ("smooth subspace `N`"); it is not a field of
  `TangentGermChart2021` because it follows from the sc-complement (the remark after Definition
  3.1.24, Proposition 1.1.7), and the Lean datum's `smooth` field is derived from it.
-/

open Set Filter Topology Function Module

noncomputable section

namespace Polyfold

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

/-- **2021 Definition 3.2.1 (b), p. 104, as written** (preprint: Definition 3.25 (2)): a chart
`ϕ : (U, x) → (O, 0)` onto a tame retract `(O, C, E)`, an `n`-dimensional subspace `N ⊆ E` in good
position to `C` in the sense of Definition 3.1.24 (`IsInGoodPositionSc`: with an sc-complement),
a good complement `Y` which is an sc-complement (`IsScGoodComplement`), a relatively open
neighbourhood `V` of `0` in `N ∩ C` and a continuous `δ : V → Y` with (1) `ϕ(M ∩ U) =
{v + δ(v) | v ∈ V}` and (2) `δ` an sc^∞-germ at `0` (`IsScInftyGermAt`), `δ(0) = 0`, `Dδ(0) = 0`.
Neither closedness of `Y` nor smoothness of `N` is asked; both follow. -/
structure TangentGermChart2021 (M : Set X) (x : X) (n : ℕ) where
  /-- The chart `ϕ`. -/
  φ : MChart X
  isChart : P.IsChart φ
  mem_source : x ∈ φ.source
  φ_zero : φ x = 0
  tame : IsTameRetract φ.model.E φ.model.C φ.model.O
  /-- The `n`-dimensional subspace `N`. -/
  N : Submodule ℝ (φ.model.E 0)
  finiteDimensional : FiniteDimensional ℝ N
  finrank_eq : finrank ℝ N = n
  goodPosition : IsInGoodPositionSc φ.model.E φ.model.C N
  /-- The good complement `Y`, an sc-complement. -/
  Y : Submodule ℝ (φ.model.E 0)
  goodComplement : IsScGoodComplement φ.model.E φ.model.C N Y
  /-- The relatively open neighbourhood `V` of `0` in `N ∩ C`. -/
  V : Set N
  V_relOpen : ∃ O : Set N, IsOpen O ∧ V = O ∩ Subtype.val ⁻¹' φ.model.C
  zero_mem_V : (0 : N) ∈ V
  /-- The map `δ : V → Y`. -/
  δ : N → φ.model.E 0
  δ_mem_Y : ∀ v ∈ V, δ v ∈ Y
  continuousOn : ContinuousOn δ V
  image_eq : φ '' (M ∩ φ.source) = (fun v : N => (v : φ.model.E 0) + δ v) '' V
  germ : IsScInftyGermAt (Subtype.val ⁻¹' φ.model.C) δ
  δ_zero : δ 0 = 0
  fderivWithin_zero : fderivWithin ℝ δ (Subtype.val ⁻¹' φ.model.C) 0 = 0

/-- **2021 Definition 3.2.1, p. 104, as written**: `M ⊆ X_∞` and every point of `M` has the data
`TangentGermChart2021`. -/
def HasTangentGermProperty2021 (M : Set X) (n : ℕ) : Prop :=
  M ⊆ P.smoothSet ∧ ∀ x ∈ M, Nonempty (P.TangentGermChart2021 M x n)

namespace TangentGermChart2021

variable {P} {M : Set X} {x : X} {n : ℕ} (d : P.TangentGermChart2021 M x n)

instance : FiniteDimensional ℝ d.N := d.finiteDimensional

/-- `N ∩ C` is a partial quadrant in `N` (Proposition 3.1.25). -/
theorem isPartialQuadrant :
    IsPartialQuadrant (ScBanach.const d.N) (Subtype.val ⁻¹' d.φ.model.C) :=
  proposition_3_22 d.φ.model.isPartialQuadrant d.goodPosition.toIsInGoodPosition

/-- The book's good complement is closed (it is an sc-complement). -/
theorem isClosed_Y : IsClosed (d.Y : Set (d.φ.model.E 0)) := d.goodComplement.isClosed

/-- `N` is smooth (the remark after Definition 3.1.24, Proposition 1.1.7). -/
theorem smooth : d.N ≤ d.φ.model.E.smooth := d.goodComplement.le_smooth

lemma V_subset : d.V ⊆ Subtype.val ⁻¹' d.φ.model.C := by
  obtain ⟨O, -, hV⟩ := d.V_relOpen; rw [hV]; exact inter_subset_right

/-- `V` is a neighbourhood of `0` within `N ∩ C`. -/
lemma V_mem_nhdsWithin : d.V ∈ 𝓝[Subtype.val ⁻¹' d.φ.model.C] (0 : d.N) := by
  obtain ⟨O, hO, hV⟩ := d.V_relOpen
  have h0O : (0 : d.N) ∈ O := (hV ▸ d.zero_mem_V : (0 : d.N) ∈ O ∩ _).1
  rw [hV, inter_comm]
  exact inter_mem_nhdsWithin _ (hO.mem_nhds h0O)

/-- The extension of `δ` by `0` off `V` (the Lean datum's `δ` is defined on all of `N`). -/
def δ' : d.N → d.φ.model.E 0 := d.V.indicator d.δ

lemma δ'_of_mem {v : d.N} (hv : v ∈ d.V) : d.δ' v = d.δ v := indicator_of_mem hv _

lemma δ'_eqOn : EqOn d.δ' d.δ d.V := fun _ hv => d.δ'_of_mem hv

/-- **The bridge from the book's datum to the Lean datum** (rows V3.22, V3.49): the closedness
of `Y` and the smoothness of `N` come from the sc-complement. -/
def toTangentGermChart : P.TangentGermChart M x n where
  φ := d.φ
  isChart := d.isChart
  mem_source := d.mem_source
  φ_zero := d.φ_zero
  tame := d.tame
  N := d.N
  finiteDimensional := d.finiteDimensional
  finrank_eq := d.finrank_eq
  smooth := d.smooth
  goodPosition := d.goodPosition.toIsInGoodPosition
  Y := d.Y
  goodComplement := d.goodComplement.toIsGoodComplement
  isClosed_Y := d.isClosed_Y
  V := d.V
  V_relOpen := d.V_relOpen
  zero_mem_V := d.zero_mem_V
  δ := d.δ'
  δ_mem_Y := fun v => by
    by_cases hv : v ∈ d.V
    · rw [d.δ'_of_mem hv]; exact d.δ_mem_Y v hv
    · rw [δ', indicator_of_notMem hv]; exact d.Y.zero_mem
  continuousOn := d.continuousOn.congr d.δ'_eqOn
  image_eq := by
    rw [d.image_eq]
    exact image_congr fun v hv => by rw [d.δ'_of_mem hv]
  germ := by
    intro m k
    obtain ⟨Vk, ⟨Ok, hOk, hVk⟩, h0k, hmem, hC⟩ := d.germ m k
    obtain ⟨OV, hOV, hVeq⟩ := d.V_relOpen
    refine ⟨Vk ∩ d.V, ⟨Ok ∩ OV, hOk.inter hOV, ?_⟩, ⟨h0k, d.zero_mem_V⟩, fun v hv => ?_, ?_⟩
    · rw [hVk, hVeq]; ext v; simp only [mem_inter_iff, mem_preimage]; tauto
    · rw [d.δ'_of_mem hv.2]; exact hmem v hv.1
    · refine (hC.mono inter_subset_left).congr fun v hv => ?_
      change invFun (d.φ.model.E.toBase m) (d.δ' ((ScBanach.const d.N).toBase m v)) =
        invFun (d.φ.model.E.toBase m) (d.δ ((ScBanach.const d.N).toBase m v))
      rw [ScBanach.const_toBase, d.δ'_of_mem hv.2]
  δ_zero := by rw [d.δ'_of_mem d.zero_mem_V, d.δ_zero]
  fderivWithin_zero := by
    have h : d.δ' =ᶠ[𝓝[Subtype.val ⁻¹' d.φ.model.C] (0 : d.N)] d.δ :=
      eventually_of_mem d.V_mem_nhdsWithin fun v hv => d.δ'_of_mem hv
    rw [h.fderivWithin_eq (d.δ'_of_mem d.zero_mem_V), d.fderivWithin_zero]

@[simp] lemma toTangentGermChart_φ : d.toTangentGermChart.φ = d.φ := rfl
@[simp] lemma toTangentGermChart_N : d.toTangentGermChart.N = d.N := rfl
@[simp] lemma toTangentGermChart_Y : d.toTangentGermChart.Y = d.Y := rfl
@[simp] lemma toTangentGermChart_V : d.toTangentGermChart.V = d.V := rfl
lemma toTangentGermChart_δ_of_mem {v : d.N} (hv : v ∈ d.V) :
    d.toTangentGermChart.δ v = d.δ v := d.δ'_of_mem hv

omit [T2Space X] [ParacompactSpace X] in
/-- The `germ` field from the fixed-germ reading of "sc^∞-germ" (an sc-smooth germ on an sc-germ
of neighbourhoods `G` of `0` in `N ∩ C`): the stronger readings of Definition 3.2.1 (2) give the
book's datum. -/
theorem germ_of_isScSmoothGerm {φ : MChart X} {N : Submodule ℝ (φ.model.E 0)}
    [FiniteDimensional ℝ N] (hN : IsInGoodPositionSc φ.model.E φ.model.C N)
    (G : ScNbhdGerm (ScBanach.const N) (Subtype.val ⁻¹' φ.model.C)) {δ : N → φ.model.E 0}
    (h : IsScSmoothGerm G δ) : IsScInftyGermAt (Subtype.val ⁻¹' φ.model.C) δ :=
  h.isScInftyGermAt
    (proposition_3_22 φ.model.isPartialQuadrant hN.toIsInGoodPosition).isQuadrantLike G

end TangentGermChart2021

namespace TangentGermChart

variable {P} {M : Set X} {x : X} {n : ℕ} (d : P.TangentGermChart M x n)

/-- **The Lean datum is a book datum**: the closed good complement `Y` of the smooth `N` is an
sc-complement (`IsGoodComplement.isScGoodComplement`), and `N` is in good position in the sense
of Definition 3.1.24 (`IsInGoodPosition.isInGoodPositionSc`). -/
def toTangentGermChart2021 : P.TangentGermChart2021 M x n where
  φ := d.φ
  isChart := d.isChart
  mem_source := d.mem_source
  φ_zero := d.φ_zero
  tame := d.tame
  N := d.N
  finiteDimensional := d.finiteDimensional
  finrank_eq := d.finrank_eq
  goodPosition := d.goodPosition.isInGoodPositionSc d.φ.model.isPartialQuadrant d.smooth
  Y := d.Y
  goodComplement := d.goodComplement.isScGoodComplement d.isClosed_Y d.smooth
  V := d.V
  V_relOpen := d.V_relOpen
  zero_mem_V := d.zero_mem_V
  δ := d.δ
  δ_mem_Y := fun v _ => d.δ_mem_Y v
  continuousOn := d.continuousOn
  image_eq := d.image_eq
  germ := d.germ
  δ_zero := d.δ_zero
  fderivWithin_zero := d.fderivWithin_zero

end TangentGermChart

/-- **Definition 3.2.1 as written is the project's `HasTangentGermProperty`** (rows V3.22 and
V3.49: "`Y` closed" is implied by the book's sc-complement, so it is not an added hypothesis). -/
theorem hasTangentGermProperty2021_iff {M : Set X} {n : ℕ} :
    P.HasTangentGermProperty2021 M n ↔ P.HasTangentGermProperty M n :=
  ⟨fun ⟨h1, h2⟩ => ⟨h1, fun x hx => ⟨(h2 x hx).some.toTangentGermChart⟩⟩,
    fun ⟨h1, h2⟩ => ⟨h1, fun x hx => ⟨(h2 x hx).some.toTangentGermChart2021⟩⟩⟩

end MPolyfold

/-! ### Lemma 3.6.9 with the book's good complement -/

section Lemma369

variable {E : ScBanach} {n : ℕ} {W' : ScBanach}

/-- **2021 Lemma 3.6.9, p. 139** (preprint: Lemma 3.55; `lemma_3_55_relOpen`, row V3.80), with the
good complement `Y` of `N` in the book's sense (Definition 3.1.24: an sc-complement) in place of
the project's closed good complement: for `σ : V → Y` of class `C¹` on the relatively open
neighbourhood `V` of `0` in `N ∩ C` with `σ(0) = 0`, `Dσ(0) = 0`, and `v ∈ V` close to `0` with
`z = v + σ(v)`: (1) `z ∈ C`; (2), (3) `Y` is a good complement of `N_v = {n + Dσ(v)n | n ∈ N}` with
respect to the partial quadrant `C_z`, and `N_v` is in good position to `C_z`.  The closedness
hypothesis `hYc` of `lemma_3_55_relOpen` is supplied by `IsScGoodComplement.isClosed`. -/
theorem lemma_3_6_9_2021 {C : Set (E 0)} (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W'))
    (hT : C = T 0 ⁻¹' quadrant n W' 0) {N : Submodule ℝ (E 0)} [FiniteDimensional ℝ N]
    (hN : IsInGoodPositionSc E C N) {Y : Submodule ℝ (E 0)} (hY : IsScGoodComplement E C N Y)
    {V : Set N} (hVrel : ∃ O : Set N, IsOpen O ∧ V = O ∩ Subtype.val ⁻¹' C) (h0V : (0 : N) ∈ V)
    (σ : N → E 0) (hσY : ∀ v, σ v ∈ Y) (hσC : ContDiffOn ℝ 1 σ V) (hσ0 : σ 0 = 0)
    (hDσ : fderivWithin ℝ σ V 0 = 0) :
    ∃ ρ > 0, ∀ v ∈ V, ‖v‖ < ρ →
      ((v : E 0) + σ v ∈ C) ∧
      IsGoodComplement E (partialQuadrantAtWith T ((v : E 0) + σ v))
        (graphSpace N (fderivWithin ℝ σ V v)) Y ∧
      IsInGoodPosition E (partialQuadrantAtWith T ((v : E 0) + σ v))
        (graphSpace N (fderivWithin ℝ σ V v)) :=
  lemma_3_55_relOpen T hT hN.toIsInGoodPosition hY.toIsGoodComplement hY.isClosed hVrel h0V σ
    hσY hσC hσ0 hDσ

end Lemma369

end Polyfold
