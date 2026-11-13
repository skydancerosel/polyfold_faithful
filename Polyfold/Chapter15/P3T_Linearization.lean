import Polyfold.Chapter15.P3T_LinearizationModel
import Polyfold.Chapter3.StrongBundleMaximalAtlas
import Polyfold.Chapter11.MultisectionLocalStructure2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 15,
§15.1 (pp. 683–687): **Theorem 15.1.1** (2017: Theorem 15.1), **Remark 15.1.2** (2017: Remark
15.1) and **Definition 15.1.7** (2017: Definition 15.1) for a strong bundle over an ep-groupoid,
read in strong bundle charts.

# The linearization `T(f, Λ)` of `Λ ∘ f`

## The text, paraphrased

(Theorem 15.1.1) For a strong bundle `(P : W → X, μ)` over an ep-groupoid, an sc-Fredholm
section `f` and an sc⁺-multisection `Λ`, the formal sums
`T(f,Λ)(y) = ∑_{i : f(y) = sᵢ(y)} σᵢ · (f − sᵢ)'(y) ∈ GrF(y)`, for a local sc⁺-section structure
`(sᵢ, σᵢ)` of `Λ` near `x`, do not depend on the structure; with `T(f,Λ) = 0` off
`supp(Λ ∘ f)` this defines a section functor of `GrF(X) → X_∞`.  (Remark 15.1.2) (1) follows from
(2).  (Definition 15.1.7) `T(f,Λ)` is the linearization of `Λ ∘ f`.

## What is formalized (namespace `Polyfold.SBLocalization`)

The project has no intrinsic linear structure on `T_xX` and `W_x` beyond chart readings (as for
Part I's `Lin(f, x)`, `linSet`, which is made in a chart), so `T(f,Λ)` is read in a strong bundle
chart `c` of `P`: the operators are `(f̂ − ŝᵢ)'(z) : T_zO → F` at the level-`1` point `z`
(`Linearization15.linSumModel`).

* `IsScPlusSectionOn.isScSmooth_principal_comp_r`: a local sc⁺-section on `O` has an sc-smooth
  principal part `ŝ ∘ r` in every chart of `P` with domain in `O`;
  `IsLocalRepOn.count_eq`: the weighted count of `v` in the chart is `Λ(Φ⁻¹(y, v))`.
* `linSumChart c f s σ z`, the formal sum of Theorem 15.1.1 (2) in the chart `c`.
* **`theorem_15_1_1`**: for an sc-Fredholm section functor `f` and two local section structures
  of `Λ` on open sets `O`, `O'` (Definition 13.2.1, `IsLocalRepOn`), the formal sums agree at
  every level-`1` point of any chart of `P` with domain in `O ∩ O'`.  `linSumChart_eq` is the
  same for any sc-smooth section `f`.  `exists_chart_isLocalRepOn`: for an sc⁺-multisection every
  object lies in such a chart (structure and chart domain), so the two clauses cover `X`.
* **Definition 15.1.7**: `linearizationIn c f Λ z`, the common value (`linearizationIn_eq`), and
  **Remark 15.1.2**: `remark_15_1_2` (`= 0` where `Λ(f(y)) = 0`, i.e. off `supp(Λ ∘ f)`, clause
  (1) of Theorem 15.1.1).

## Continued in `P3T_LinearizationIntrinsic.lean`

The passage to intrinsic operators `T_xX → W_x` and the independence of the chart are in
`P3T_LinearizationIntrinsic.lean` (`theorem_15_1_1_intrinsic`, `linearization`).  The functor
property `T(f,Λ)(t φ) = φ_* T(f,Λ)(s φ)` of the text's "section functor" is not formalized.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongRetr Linearization15

variable {A : SEP.{u}}

/-! ### Local sections read in a chart -/

/-- A local section on `O` read in a chart with domain in `O`: `Φ(s(φ⁻¹ z)) = (z, ŝ(z))`. -/
theorem apply_localSection {c : StrongBundleChart A.X.PObj A.P} {s : A.Obj → A.W}
    {O : Set A.Obj} (hsec : ∀ y ∈ O, A.P (s y) = y) (hsub : c.φ.source ⊆ O)
    {z : c.φ.model.E 0} (hz : z ∈ c.φ.model.O) :
    c (s (c.φ.symm z)) = (z, c.principal s z) := by
  have hzV : c.φ.symm z ∈ c.φ.source := c.φ.symm_mapsTo hz
  refine Prod.ext ?_ rfl
  rw [c.fst_apply (by rw [hsec _ (hsub hzV)]; exact hzV), hsec _ (hsub hzV),
    c.φ.apply_symm_apply hz]

/-- **A local sc⁺-section has an sc-smooth principal part** `ŝ ∘ r` on `U`, in every strong bundle
chart of `P` whose domain lies in the domain `O` of the section. -/
theorem IsScPlusSectionOn.isScSmooth_principal_comp_r {s : A.Obj → A.W} {O : Set A.Obj}
    (hs : IsScPlusSectionOn A s O) {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c)
    (hsub : c.φ.source ⊆ O) : IsScSmooth c.U (c.principal s ∘ r c.R) := by
  obtain ⟨hsec, G, hG, hGsm⟩ := hs
  have h0 : A.X.PObj.IsScSmoothOn A.B.toMPolyfold0 s O :=
    (MPolyfold.IsScSmoothOn.comp A.B.isScSmoothMap_oneVal hGsm (mapsTo_univ _ _)).congr
      fun y hy => hG y hy
  have h := h0.smooth c.φ (c.toMChart A.B.continuous) c.isChart hc.toMChart c.φ.source
    c.φ.isOpen_source (fun x hx => ⟨hsub hx, hx⟩)
    (fun x hx => c.mem_source_of_proj (by rw [hsec x (hsub hx)]; exact hx))
  rw [c.φ.image_source] at h
  have h' : IsScSmoothRetractMap c.φ.model.E c.φ.model.C c.φ.model.O (c.φ.model.E.prod c.F)
      (c.φ.model.C ×ˢ univ) c.K (fun z => (z, c.principal s z)) :=
    h.congr fun z hz => apply_localSection hsec hsub hz
  have h1 := h'.comp_isScSmooth (c.isRetraction.baseRetraction c.relOpen) c.base_retract
  exact (h1.snd c.relOpen.isScDomain).congr c.relOpen.isScDomain fun _ _ => rfl

/-- The principal part of an sc-smooth section composed with `r` is sc-smooth on `U`. -/
theorem isScSmooth_principal_comp_r {f : A.Obj → A.W} (hf : A.B.IsScSmoothSection f)
    {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c) :
    IsScSmooth c.U (c.principal f ∘ r c.R) := by
  have h1 := (hf.isScSmoothRetractMap hc).comp_isScSmooth
    (c.isRetraction.baseRetraction c.relOpen) c.base_retract
  exact (h1.snd c.relOpen.isScDomain).congr c.relOpen.isScDomain fun _ _ => rfl

open Classical in
/-- **The weighted count of a local section structure in a chart**: for a local representation
`(sᵢ, σᵢ)` of `Λ` on `O` and a chart with domain in `O`, the weighted count of `v` at `y ∈ O`
(model) is `Λ(Φ⁻¹(y, v))` if `(y, v) ∈ K` and `0` otherwise. -/
theorem IsLocalRepOn.count_eq {Λ : A.W → ℚ≥0} {O : Set A.Obj} {k : ℕ}
    {s : Fin k → A.Obj → A.W} {σ : Fin k → ℚ≥0} (hs : IsLocalRepOn A Λ O s σ)
    {c : StrongBundleChart A.X.PObj A.P} (hsub : c.φ.source ⊆ O) {y : c.φ.model.E 0}
    (hy : y ∈ c.φ.model.O) (v : c.F 0) :
    (∑ i, if c.principal (s i) y = v then σ i else 0) =
      if (y, v) ∈ c.K then Λ (c.toPartialEquiv.symm (y, v)) else 0 := by
  have hyV : c.φ.symm y ∈ c.φ.source := c.φ.symm_mapsTo hy
  have hsec : ∀ i, ∀ x ∈ O, A.P (s i x) = x := fun i => (hs.2.1 i).1
  have happ : ∀ i, c (s i (c.φ.symm y)) = (y, c.principal (s i) y) := fun i =>
    apply_localSection (hsec i) hsub hy
  have hsrc : ∀ i, s i (c.φ.symm y) ∈ c.toPartialEquiv.source := fun i =>
    c.mem_source_of_proj (by rw [hsec i _ (hsub hyV)]; exact hyV)
  by_cases hK : (y, v) ∈ c.K
  · rw [if_pos hK]
    set w := c.toPartialEquiv.symm (y, v) with hw
    have hPw : A.P w = c.φ.symm y := c.proj_symm hK
    rw [hs.2.2.2 w (by rw [hPw]; exact hsub hyV), hPw]
    refine Finset.sum_congr rfl fun i _ => ite_iff_congr ?_ _ _
    constructor
    · intro e
      apply c.toPartialEquiv.injOn (c.symm_mem_source hK) (hsrc i)
      rw [happ i, c.apply_symm hK, e]
    · intro e
      have := congrArg (fun q => (c q).2) e
      simp only [hw, c.apply_symm hK] at this
      rw [this, happ i]
  · rw [if_neg hK]
    refine Finset.sum_eq_zero fun i _ => if_neg fun e => hK ?_
    rw [← e, ← happ i, ← c.image_source]
    exact ⟨_, hsrc i, rfl⟩

/-! ### Theorem 15.1.1 in a chart -/

/-- **The formal sum of Theorem 15.1.1 (2) in the chart `c`**: at the level-`1` point `z` over
`y`, `∑_{i : ŝᵢ(y) = f̂(y)} σᵢ · (f̂ − ŝᵢ)'(z) ∈ GrF`, the operators `T_zO → F`. -/
def linSumChart (c : StrongBundleChart A.X.PObj A.P) (f : A.Obj → A.W) {k : ℕ}
    (s : Fin k → A.Obj → A.W) (σ : Fin k → ℚ≥0) (z : c.φ.model.E 1) : GrFModel c.U c.R z :=
  linSumModel c.U c.R (c.principal f) (fun i => c.principal (s i)) σ z

/-- **Well-definedness of `T(f,Λ)` in a chart, for any sc-smooth section `f`**: two local
section structures of `Λ` on `O`, `O'` give the same formal sum at every level-`1` point of a
chart of `P` with domain in `O ∩ O'`. -/
theorem linSumChart_eq {f : A.Obj → A.W} (hf : A.B.IsScSmoothSection f) {Λ : A.W → ℚ≥0}
    {O O' : Set A.Obj} {k l : ℕ} {s : Fin k → A.Obj → A.W} {σ : Fin k → ℚ≥0}
    {t : Fin l → A.Obj → A.W} {τ : Fin l → ℚ≥0} (hs : IsLocalRepOn A Λ O s σ)
    (ht : IsLocalRepOn A Λ O' t τ) {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c)
    (hsub : c.φ.source ⊆ O ∩ O') {z : c.φ.model.E 1}
    (hz : c.φ.model.E.toBase 1 z ∈ c.φ.model.O) :
    linSumChart c f s σ z = linSumChart c f t τ z := by
  have hO : r c.R '' c.U = c.φ.model.O := c.r_image
  refine theorem_15_1_1_model c.relOpen c.isRetraction (isScSmooth_principal_comp_r hf hc)
    (fun i => (hs.2.1 i).isScSmooth_principal_comp_r hc fun x hx => (hsub hx).1)
    (fun j => (ht.2.1 j).isScSmooth_principal_comp_r hc fun x hx => (hsub hx).2)
    isOpen_univ (fun y hy _ v => ?_) (by rw [hO]; exact hz) (mem_univ _)
  rw [hO] at hy
  rw [hs.count_eq (fun x hx => (hsub hx).1) hy v, ht.count_eq (fun x hx => (hsub hx).2) hy v]

/-- **Theorem 15.1.1 (2017: Theorem 15.1), pp. 684–687, read in a chart**: for a strong bundle
over an ep-groupoid, an sc-Fredholm section functor `f` and two local sc⁺-section structures
`(sᵢ, σᵢ)` on `O`, `(tⱼ, τⱼ)` on `O'` describing the same `Λ` (Definition 13.2.1), the formal sums
`∑_{i : f(y) = sᵢ(y)} σᵢ · (f − sᵢ)'(y)` and `∑_{j : f(y) = tⱼ(y)} τⱼ · (f − tⱼ)'(y)` agree at every
level-`1` point `y` (in particular every smooth point) of every strong bundle chart of `P` with
domain in `O ∩ O'`.  `Λ` need not be a functor here, and only sc-smoothness of `f` is used
(`linSumChart_eq`). -/
theorem theorem_15_1_1 {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    {Λ : A.W → ℚ≥0} {O O' : Set A.Obj} {k l : ℕ} {s : Fin k → A.Obj → A.W}
    {σ : Fin k → ℚ≥0} {t : Fin l → A.Obj → A.W} {τ : Fin l → ℚ≥0}
    (hs : IsLocalRepOn A Λ O s σ) (ht : IsLocalRepOn A Λ O' t τ)
    {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c) (hsub : c.φ.source ⊆ O ∩ O')
    {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z ∈ c.φ.model.O) :
    linSumChart c f s σ z = linSumChart c f t τ z := by
  obtain ⟨⟨hsm, -⟩, -⟩ := hf
  exact linSumChart_eq hsm hs ht hc hsub hz

/-- **Every object lies in a chart inside the domain of a local section structure**: for an
sc⁺-multisection `Λ` and `x`, there are a local section structure of `Λ` on an open `O ∋ x` and a
strong bundle chart of `P` around `x` with domain in `O` (restrict a chart of the atlas,
`StrongBundle.IsChart.restrict`). -/
theorem exists_chart_isLocalRepOn {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ) (x : A.Obj) :
    ∃ (O : Set A.Obj) (k : ℕ) (s : Fin k → A.Obj → A.W) (σ : Fin k → ℚ≥0)
      (c : StrongBundleChart A.X.PObj A.P), IsOpen O ∧ x ∈ O ∧ IsLocalRepOn A Λ O s σ ∧
        A.B.IsChart c ∧ x ∈ c.φ.source ∧ c.φ.source ⊆ O := by
  obtain ⟨R, k, s, σ, h⟩ := hΛ.2 x
  obtain ⟨c, hc, hxc⟩ := StrongBundle.exists_chart_mem A.B x
  have hso : IsOpen (c.φ.source ∩ R.U) := c.φ.isOpen_source.inter R.isOpen_U
  refine ⟨R.U, k, s, σ, c.restrict inter_subset_left hso, R.isOpen_U, R.mem_U, h,
    (StrongBundle.isChart_of_mem A.B hc).restrict inter_subset_left hso, ⟨hxc, R.mem_U⟩,
    inter_subset_right⟩

/-! ### Definition 15.1.7 and Remark 15.1.2 -/

open Classical in
/-- **Definition 15.1.7 (2017: Definition 15.1), p. 687, read in the chart `c`**: the
linearization `T(f,Λ)` of `Λ ∘ f` at the level-`1` point `z`, the formal sum of any local section
structure of `Λ` on an open set containing the domain of `c` (well defined by Theorem 15.1.1,
`linearizationIn_eq`), and `0` if there is none. -/
def linearizationIn (c : StrongBundleChart A.X.PObj A.P) (f : A.Obj → A.W) (Λ : A.W → ℚ≥0)
    (z : c.φ.model.E 1) : GrFModel c.U c.R z :=
  if h : ∃ (O : Set A.Obj) (k : ℕ) (s : Fin k → A.Obj → A.W) (σ : Fin k → ℚ≥0),
      IsLocalRepOn A Λ O s σ ∧ c.φ.source ⊆ O then
    linSumChart c f h.choose_spec.choose_spec.choose h.choose_spec.choose_spec.choose_spec.choose z
  else 0

/-- **Theorem 15.1.1 (2) for Definition 15.1.7**: in a chart with domain in the domain `O` of a
local section structure `(sᵢ, σᵢ)` of `Λ`, `T(f,Λ)(y) = ∑_{i : f(y) = sᵢ(y)} σᵢ · (f − sᵢ)'(y)` at
every level-`1` point. -/
theorem linearizationIn_eq {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    {Λ : A.W → ℚ≥0} {O : Set A.Obj} {k : ℕ} {s : Fin k → A.Obj → A.W} {σ : Fin k → ℚ≥0}
    (hs : IsLocalRepOn A Λ O s σ) {c : StrongBundleChart A.X.PObj A.P} (hc : A.B.IsChart c)
    (hsub : c.φ.source ⊆ O) {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z ∈ c.φ.model.O) :
    linearizationIn c f Λ z = linSumChart c f s σ z := by
  have h : ∃ (O : Set A.Obj) (k : ℕ) (s : Fin k → A.Obj → A.W) (σ : Fin k → ℚ≥0),
      IsLocalRepOn A Λ O s σ ∧ c.φ.source ⊆ O := ⟨O, k, s, σ, hs, hsub⟩
  rw [linearizationIn, dif_pos h]
  have hspec := h.choose_spec.choose_spec.choose_spec.choose_spec
  exact theorem_15_1_1 hf hspec.1 hs hc (subset_inter hspec.2 hsub) hz

open Classical in
/-- **Remark 15.1.2 (2017: Remark 15.1), p. 684, and Theorem 15.1.1 (1)**: at a point `y` of the
chart with `Λ(f(y)) = 0` (`y ∉ supp(Λ ∘ f)`), `T(f,Λ)(y) = 0`: the formal sum of (2) is empty,
since the weights are positive. -/
theorem remark_15_1_2 {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    {Λ : A.W → ℚ≥0} {c : StrongBundleChart A.X.PObj A.P}
    {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z ∈ c.φ.model.O)
    (h0 : Λ (f (c.φ.symm (c.φ.model.E.toBase 1 z))) = 0) :
    linearizationIn c f Λ z = 0 := by
  rw [linearizationIn]
  split_ifs with h
  · have hspec := h.choose_spec.choose_spec.choose_spec.choose_spec
    set y := c.φ.model.E.toBase 1 z
    have hsec : IsSection A.P f := hf.1.1.1
    have hK : (y, c.principal f y) ∈ c.K := c.principal_mem_K hsec hz
    have hw : c.toPartialEquiv.symm (y, c.principal f y) = f (c.φ.symm y) := by
      rw [← c.apply_section hsec hz]
      exact c.toPartialEquiv.left_inv (c.mem_source_of_proj (by
        rw [hsec]; exact c.φ.symm_mapsTo hz))
    refine remark_15_1_2_model _ _ hspec.1.1 z ?_
    rw [hspec.1.count_eq hspec.2 hz, if_pos hK, hw, h0]
  · rfl

end SBLocalization

end Polyfold
