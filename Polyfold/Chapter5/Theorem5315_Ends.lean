import Polyfold.Chapter5.Theorem5315_GeneralPosition
import Polyfold.Chapter2.ReducedTangentIntrinsic
import Polyfold.Chapter3.TameGermTransfer
import Polyfold.Chapter3.QuadrantInverse

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §5.3,
**Theorem 5.3.15** (p. 223; 2017: Theorem 5.8; preprint: Theorem 5.22), the compactness
statement and conclusion (1) under the printed hypotheses on the ends.  Gap G.48, piece (A).

# Theorem 5.3.15 (1): from the ends to general position on `∂X`

## The text, paraphrased

(Theorem 5.3.15) For a generalized compact homotopy `f` between compact problems `(fᵢ, Pᵢ)` over
M-polyfolds `Xᵢ` without boundary, with every `(fᵢ, x)`, `x ∈ S_{fᵢ}`, in general position, and
`∂X = X₀ ⊔ X₁`: an open `U ⊇ S_f` with `S_{f+s}` compact for `s ∈ Γ^{+,1}_U(P)`, and an arbitrarily
small `s₀` vanishing near `∂X` with (1) `(f + s₀, x)` in general position at every zero, and (2)
`t|S_{f+s₀}` Morse.  The proof (p. 223, bottom) uses the ends only through the general position
of `(f, x)` at the zeros on `∂X`, "in view of the assumption that `(fᵢ, Xᵢ)` are already in
general position".

## What is formalized

* `StrongBundle.IsGeneralPositionAtEnds`: the printed hypotheses on the ends, for the ends
  `Xᵢ = t⁻¹(i)` and end problems `fᵢ = f|Xᵢ` of `IsSubmersiveGenCompactHomotopy`
  (Definition 5.3.13): `Xᵢ` (with the sub-M-polyfold structure) has no boundary, and
  `(fᵢ, a)` is in general position (`IsGeneralPositionGerm` of the pull-back bundle) at every zero.
* `isGeneralPositionGerm_of_restrict`: for a boundaryless sub-M-polyfold `A ⊆ X`, a zero `a ∈ A`
  of `f` at which `(f|A)'(a)` is onto is a point of general position of `f` in `X`.  The proof
  compares, in a tame chart `c` of `X` centred at `a`, the linearization of `f` with that of `f|A`
  in the pull-back chart over the sub-chart of `A` built from `c`
  (`exists_scDeriv_eq_of_isLinSurjAt_restrict`: chain rule through the sub-retract
  `φ(W ∩ A) ⊆ O`), and shows `T_0(φ(W ∩ A)) ⊆ E_0` from `d_A ≡ 0` and the chart independence of
  the reduced tangent space (`mem_minimalSubspaceWith_of_isWithoutBoundary`).  So `Lin_f(0)` is
  onto on `T^R_0O`, and the chart criterion `isGeneralPositionGerm_of_sup_eq` applies.
* `IsSubmersiveGenCompactHomotopy.isGeneralPositionGerm_of_mem_boundary`: with `∂X ⊆ X₀ ∪ X₁`,
  `(f, x)` is in general position at every zero `x ∈ ∂X`.
* **`theorem_5_3_15_generalPosition`**: the compactness statement and conclusion (1) of Theorem
  5.3.15 under the printed hypotheses (`theorem_5_3_15_generalPosition_hyp` without its added
  hypothesis on `∂X`).
* `theorem_5_3_15_generalPosition_witness`: the hypotheses hold for the generalized compact
  homotopy `isSubmersiveGenCompactHomotopy_witness` (empty ends, `∂ℝ = ∅`).

## What the text leaves implicit, and the choices made

* Of the general position of the end problems only the surjectivity of `(fᵢ)'(x)` is used: the
  complement condition in `X` follows from `T_xXᵢ ⊆ T^R_xX`, which holds because `Xᵢ` has no
  boundary.  The degeneracy index of `X` at `x ∈ ∂X` plays no role, and of `∂X = X₀ ⊔ X₁` only
  `∂X ⊆ X₀ ∪ X₁` is used.
* The text also assumes sc-smooth bump functions on the `Xᵢ`; they are not needed for (1).
* Conclusion (2) is not formalized here (the chart step of its proof is
  `Chapter5/Theorem5315_ParametricMorse.lean`).
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u v

open StrongRetr

section SubRetract

variable {E F : ScBanach} {C : Set (E 0)}

/-- For retractions `S`, `R` with `S(U_S) ⊆ R(U_R)`, the derivative `DR(z)` is the identity on
`T_z S(U_S)` (the tangent space of the sub-retract lies in that of the retract). -/
lemma scDeriv_apply_eq_self_of_retract_subset (S R : ScRetraction E C)
    (hSR : S.retract ⊆ R.retract) {z : E 1} (hz : E.toBase 1 z ∈ S.retract) {v : E 0}
    (hv : v ∈ range (scDeriv S.U S z)) : scDeriv R.U R z v = v := by
  obtain ⟨h, rfl⟩ := hv
  have hzU : z ∈ E.lvlSet S.U 1 := S.retract_subset hz
  have hmaps : MapsTo S S.U R.U := fun u hu => R.retract_subset (hSR (S.apply_mem_retract hu))
  have hR1 : IsSc1 R.U R := R.isScSmooth.isSc1
  have hS1 : IsSc1 S.U S := S.isScSmooth.isSc1
  have hchain := scDeriv_comp_apply' S.relOpen R.relOpen hS1 hR1 hmaps hzU h
  have hlev : levelMap S 1 z = z :=
    levelMap_eq_of_toBase_eq (S.apply_eq_self_of_mem_retract hz).symm
  have heq : EqOn (R ∘ S) S S.U := fun u hu =>
    R.apply_eq_self_of_mem_retract (hSR (S.apply_mem_retract hu))
  have hcomp1 : IsSc1 S.U (R ∘ S) := (theorem_1_3_1 S.relOpen R.relOpen hS1 hR1 hmaps).1
  rw [hlev] at hchain
  rw [hchain, scDeriv_eq_of_eqOn_relOpen S.relOpen hcomp1 hS1 subset_rfl subset_rfl heq hzU]

/-- For retractions `S`, `R` with `S(U_S) ⊆ R(U_R)` and maps `g, g'` agreeing on `S(U_S)`:
`D(g' ∘ S)(z) = D(g ∘ R)(z)` on `T_z S(U_S)` (chain rule, `g ∘ R ∘ S = g' ∘ S`). -/
lemma scDeriv_comp_apply_eq_of_retract_subset (S R : ScRetraction E C)
    (hSR : S.retract ⊆ R.retract) {g g' : E 0 → F 0} (hg : IsSc1 R.U (g ∘ R))
    (hgg' : ∀ u ∈ S.retract, g' u = g u) {z : E 1} (hz : E.toBase 1 z ∈ S.retract)
    {v : E 0} (hv : v ∈ range (scDeriv S.U S z)) :
    scDeriv S.U (g' ∘ S) z v = scDeriv R.U (g ∘ R) z v := by
  have hzU : z ∈ E.lvlSet S.U 1 := S.retract_subset hz
  have hmaps : MapsTo S S.U R.U := fun u hu => R.retract_subset (hSR (S.apply_mem_retract hu))
  have hS1 : IsSc1 S.U S := S.isScSmooth.isSc1
  have hcomp1 : IsSc1 S.U ((g ∘ R) ∘ S) := (theorem_1_3_1 S.relOpen R.relOpen hS1 hg hmaps).1
  have heq : EqOn (g' ∘ S) ((g ∘ R) ∘ S) S.U := fun u hu => by
    have hu' := S.apply_mem_retract hu
    simp only [Function.comp_apply, R.apply_eq_self_of_mem_retract (hSR hu')]
    exact hgg' _ hu'
  have hcomp2 : IsSc1 S.U (g' ∘ S) := (hcomp1.isSc1With_scDeriv.congr heq.symm).isSc1
  have hlev : levelMap S 1 z = z :=
    levelMap_eq_of_toBase_eq (S.apply_eq_self_of_mem_retract hz).symm
  rw [scDeriv_eq_of_eqOn_relOpen S.relOpen hcomp2 hcomp1 subset_rfl subset_rfl heq hzU,
    ← scDeriv_comp_apply' S.relOpen R.relOpen hS1 hg hmaps hzU v, hlev,
    S.scDeriv_apply_eq_self_of_mem_range hz hv]

end SubRetract

section SubPullback

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {A : Set X} (hA : PX.IsSubMPolyfold A) [ParacompactSpace A]

/-- The sub-chart `(φ|_{W ∩ A}, W ∩ A, (φ(W ∩ A), C, E))` of `A` built from the base chart of a
strong bundle chart `c` of `P` (2021 Proposition 2.3.19, p. 39). -/
abbrev subChartOf (c : StrongBundleChart PX P) (a : A) : MChart A :=
  MPolyfold.subChart (hA.data a.2) c.isChart a

omit [ParacompactSpace A] in
/-- In the sub-chart, `φ ∘ ι ∘ ψ⁻¹` is the inclusion `φ(W ∩ A) ⊆ O`, hence sc-smooth. -/
lemma isScSmoothRetractMap_subChartOf (c : StrongBundleChart PX P) (a : A) :
    IsScSmoothRetractMap (subChartOf hA c a).model.E (subChartOf hA c a).model.C
      (subChartOf hA c a).model.O c.φ.model.E c.φ.model.C c.φ.model.O
      (c.φ ∘ Subtype.val ∘ (subChartOf hA c a).symm) := by
  set d := hA.data a.2
  have hsub : c.φ '' (d.shrink c.φ ∩ A) ⊆ c.φ.model.O :=
    c.φ.image_subset_model fun _ hx => d.shrink_subset_source c.φ hx.1
  refine ((isScSmoothRetractMap_id (C := c.φ.model.C) (c.φ '' (d.shrink c.φ ∩ A))).mono_target
    hsub).congr fun z hz => ?_
  change z = c.φ ((MPolyfold.subChart d c.isChart a).symm z).1
  rw [MPolyfold.subChart_symm_apply d c.isChart a hz, c.φ.apply_symm_apply (hsub hz)]

/-- The pull-back chart data of `ι*P → A` over the sub-chart of `A` built from `c`. -/
def subPullbackData (c : StrongBundleChart PX P) (a : A) :
    PullbackChartData PX P (MPolyfold.subPolyfold hA) (Subtype.val : A → X) where
  c := c
  ψ := subChartOf hA c a
  isChart := MPolyfold.subPolyfold_isChart hA _ c.isChart a
  mapsTo := fun _ hb => (hA.data a.2).shrink_subset_source c.φ hb
  RZ := (subChartOf hA c a).model.isScRetract.choose
  RZ_retract := (subChartOf hA c a).model.isScRetract.choose_spec
  smooth := isScSmoothRetractMap_subChartOf hA c a

end SubPullback

section SubPullbackLin

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {A : Set X} (hA : PX.IsSubMPolyfold A) [ParacompactSpace A]
  (c : StrongBundleChart PX P) (a : A)

lemma subPullbackData_retract :
    (subPullbackData hA c a).RZ.retract = c.φ '' ((hA.data a.2).shrink c.φ ∩ A) :=
  (subPullbackData hA c a).RZ_retract

lemma subPullbackData_retract_subset : (subPullbackData hA c a).RZ.retract ⊆ c.φ.model.O := by
  rw [subPullbackData_retract]
  exact c.φ.image_subset_model fun _ hx => (hA.data a.2).shrink_subset_source c.φ hx.1

/-- The retraction onto `φ(W ∩ A)` maps its domain into the domain `U` of `c`. -/
lemma subPullbackData_mapsTo :
    MapsTo (subPullbackData hA c a).RZ (subPullbackData hA c a).RZ.U c.U :=
  fun _ hu => mem_U_of_mem_O c.isRetraction (c.r_image ▸
    subPullbackData_retract_subset hA c a ((subPullbackData hA c a).RZ.apply_mem_retract hu))

/-- **The tangent space of a boundaryless sub-M-polyfold lies in the reduced tangent space**
(2021 Definition 2.5.8, p. 57, with Proposition 2.4.10): if `A` has no boundary (`d_A ≡ 0`), then
in the sub-chart of `A` built from a chart `φ` of `X`, every vector of `T_{φ(a)}(φ(W ∩ A))` lies in
`E_{φ(a)} = {v | (Tv)_i = 0 whenever (Tφ(a))_i = 0}` for every presentation `T` of the partial
quadrant of `φ`.  *Proof*: `T^R_aA` does not depend on the chart (`reducedTangentFiber_eq`); in
a chart of `A` realizing `d_A(a) = 0` the point is interior, so `T^R_aA = T_aA`. -/
lemma mem_minimalSubspaceWith_of_isWithoutBoundary
    (hAb : (MPolyfold.subPolyfold hA).IsWithoutBoundary) (ha : a.1 ∈ c.φ.source)
    {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z = c.φ a.1)
    {n : ℕ} {Wq : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant n Wq 0) {v : c.φ.model.E 0}
    (hv : v ∈ range (scDeriv (subPullbackData hA c a).RZ.U (subPullbackData hA c a).RZ z)) :
    v ∈ minimalSubspaceWith T (c.φ a.1) := by
  set PA := MPolyfold.subPolyfold hA
  have hψ : PA.IsChart (subPullbackData hA c a).ψ := (subPullbackData hA c a).isChart
  have haψ : a ∈ (subPullbackData hA c a).ψ.source :=
    (hA.data a.2).mem_shrink c.φ a.2 (hA.mem_data_V a.2) ha
  have hlev : a ∈ PA.levelSet 1 :=
    ⟨(subPullbackData hA c a).ψ, hψ, haψ, ⟨(z : (subPullbackData hA c a).ψ.model.E 1), hz⟩⟩
  set xA : PA.Level 1 := PA.levelMk 1 a hlev
  have haψ' : PA.levelVal 1 xA ∈ (subPullbackData hA c a).ψ.source := haψ
  -- a chart of `A` in which `a` is interior
  obtain ⟨χ, hχ, haχ, hdχ⟩ := PA.exists_isChart_degIndex_eq a
  have haχ' : PA.levelVal 1 xA ∈ χ.source := haχ
  obtain ⟨n', W', Tχ, hTχ⟩ := χ.model.isPartialQuadrant
  have h0 : degIndex χ.model.E χ.model.C (χ a) = 0 := by
    have := hAb a; rw [hdχ] at this; exact this
  have hint : χ a ∈ interior χ.model.C :=
    (degIndex_eq_zero_iff χ.model.isPartialQuadrant (χ.apply_mem_C haχ)).1 h0
  have htop : MPolyfold.reducedTangentFiber hχ haχ' Tχ = ⊤ := by
    change (minimalSubspaceWith Tχ (χ a)).comap _ = ⊤
    rw [minimalSubspaceWith_eq_top_of_mem_interior Tχ hTχ hint, Submodule.comap_top]
  -- `v` as a tangent vector of `A` at `a`
  have hlift : MPolyfold.levelLift (subPullbackData hA c a).ψ 1 (PA.levelVal 1 xA) = z :=
    (subPullbackData hA c a).ψ.model.E.toBase_injective 1
      (by rw [PA.toBase_levelLift hψ haψ' hlev]; exact hz.symm)
  have hzR : z ∈ c.φ.model.E.lvlSet (subPullbackData hA c a).RZ.retract 1 := by
    change c.φ.model.E.toBase 1 z ∈ (subPullbackData hA c a).RZ.retract
    rw [(subPullbackData hA c a).RZ_retract, hz]
    exact (subPullbackData hA c a).ψ.mapsTo_model a haψ
  have hmem : v ∈ MPolyfold.tangentFiberModel hψ haψ' := by
    have h2 : v ∈ tangentSpace (subPullbackData hA c a).ψ.model.E (subPullbackData hA c a).ψ.model.C
        (subPullbackData hA c a).RZ.retract z := by
      rw [tangentSpace_eq_coe_submodule (subPullbackData hA c a).RZ hzR]
      obtain ⟨h, rfl⟩ := hv
      exact ⟨h, rfl⟩
    have h3 := MPolyfold.coe_tangentFiberModel hψ haψ'
    rw [hlift, ← (subPullbackData hA c a).RZ_retract] at h3
    exact (Set.ext_iff.1 h3 v).2 h2
  have hα : MPolyfold.tangentFiberMk hψ haψ' ⟨v, hmem⟩ ∈
      MPolyfold.reducedTangentFiber hψ haψ' T := by
    rw [← MPolyfold.reducedTangentFiber_eq hχ haχ' Tχ hψ haψ' T hTχ hT, htop]
    exact Submodule.mem_top
  have h1 := Submodule.mem_comap.1 hα
  rw [MPolyfold.fiberCoord_eq_coe, MPolyfold.tangentFiberMk, Equiv.apply_symm_apply] at h1
  exact h1

end SubPullbackLin

section RestrictLin

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {f : X → Y} {A : Set X} (hA : PX.IsSubMPolyfold A) [ParacompactSpace A]
  (c : StrongBundleChart PX P) (a : A)

/-- The principal part of the restricted section `f|A` in the pull-back chart over the sub-chart
is the principal part of `f` in `c`, on `φ(W ∩ A)`. -/
lemma principal_restrictSection_subPullback (hf : IsSection P f)
    (q₀ : pullbackSpace P (Subtype.val : A → X)) {w : c.φ.model.E 0}
    (hw : w ∈ (subPullbackData hA c a).RZ.retract) :
    ((subPullbackData hA c a).toChart q₀).principal (restrictSection P A f hf) w =
      c.principal f w := by
  rw [subPullbackData_retract] at hw
  change (c (f ((subChartOf hA c a).symm w).1)).2 = (c (f (c.φ.symm w))).2
  rw [MPolyfold.subChart_symm_apply (hA.data a.2) c.isChart a hw]

/-- The fibre of the pull-back chart over `a` contains the fibre of `c` over `a`. -/
lemma mem_K_subPullback (q₀ : pullbackSpace P (Subtype.val : A → X)) (ha : a.1 ∈ c.φ.source)
    {k : c.F 0} (hk : (c.φ a.1, k) ∈ c.K) :
    (((subPullbackData hA c a).toChart q₀).φ a, k) ∈ ((subPullbackData hA c a).toChart q₀).K := by
  have haψ : a ∈ (subPullbackData hA c a).ψ.source :=
    (hA.data a.2).mem_shrink c.φ a.2 (hA.mem_data_V a.2) ha
  change ((subPullbackData hA c a).ψ a, k) ∈ pullbackRetraction (subPullbackData hA c a).c.R
    (subPullbackData hA c a).RZ (subPullbackData hA c a).g ''
      ((subPullbackData hA c a).RZ.U ×ˢ univ)
  rw [(subPullbackData hA c a).image_eq_Kg]
  refine ⟨?_, ?_⟩
  · rw [(subPullbackData hA c a).RZ_retract]
    exact (subPullbackData hA c a).ψ.mapsTo_model a haψ
  · change (c.φ ((subPullbackData hA c a).ψ.symm ((subPullbackData hA c a).ψ a)).1, k) ∈ c.K
    rw [(subPullbackData hA c a).ψ.symm_apply_apply haψ]
    exact hk

lemma subPullbackData_retract_subset_base :
    (subPullbackData hA c a).RZ.retract ⊆ (c.isRetraction.baseRetraction c.relOpen).retract := by
  rw [c.base_retract]; exact subPullbackData_retract_subset hA c a

variable [T2Space Y] [ParacompactSpace Y] {B : StrongBundle PX P}
  [ParacompactSpace (pullbackSpace P (Subtype.val : A → X))]

/-- **The linearization of `f|A` is the restriction of that of `f`** (2021 Definition 5.3.13 (2)
read with Proposition 2.6.8): if `(f|A)'(a)` is onto (`IsLinSurjAt` in the pull-back bundle
`ι*P → A`), then for every `k` in the fibre of `c` over `a` there is a vector `v` tangent to
the sub-retract `φ(W ∩ A)` at `z` with `D(f̂ ∘ r)(z)v = k`.  *Proof*: by the chart independence
of `IsLinSurjAt` the linearization of `f|A` is onto in the pull-back chart over the sub-chart of
`A` built from `c`; there its principal part is `f̂` on `φ(W ∩ A) ⊆ O`, and the chain rule gives
`D(f̂ ∘ S)(z) = D(f̂ ∘ r)(z)` on `T_z(φ(W ∩ A))`. -/
theorem exists_scDeriv_eq_of_isLinSurjAt_restrict (hf : B.IsScSmoothSection f)
    (hfA : (B.pullback (MPolyfold.subPolyfold_inclusion_isScSmooth hA)).IsScSmoothSection
      (restrictSection P A f hf.1))
    (ha0 : IsZeroAt P f a.1)
    (hsurjA : (B.pullback (MPolyfold.subPolyfold_inclusion_isScSmooth hA)).IsLinSurjAt
      (restrictSection P A f hf.1) a)
    (hc : B.IsChart c) (ha : a.1 ∈ c.φ.source) {z : c.φ.model.E 1}
    (hz : c.φ.model.E.toBase 1 z = c.φ a.1) {k : c.F 0} (hk : (c.φ a.1, k) ∈ c.K) :
    ∃ v : c.φ.model.E 0,
      v ∈ range (scDeriv (subPullbackData hA c a).RZ.U (subPullbackData hA c a).RZ z) ∧
        scDeriv c.U (c.principal f ∘ r c.R) z v = k := by
  have hC' := (subPullbackData hA c a).isChart_toChart B
    (MPolyfold.subPolyfold_inclusion_isScSmooth hA) hc (restrictSection P A f hf.1 a)
  have haψ : a ∈ (subPullbackData hA c a).ψ.source :=
    (hA.data a.2).mem_shrink c.φ a.2 (hA.mem_data_V a.2) ha
  have hy0 : IsZeroAt (pullbackProj P (Subtype.val : A → X)) (restrictSection P A f hf.1) a :=
    (isZeroAt_restrictSection_iff hf.1 a).2 ha0
  obtain ⟨x, hx⟩ := StrongBundle.IsLinSurjAt.linAt_surjective hfA hy0 hsurjA hC' haψ
    (z' := z) hz k (mem_K_subPullback hA c a _ ha hk)
  obtain ⟨h, hh⟩ := x.2
  have hzR : c.φ.model.E.toBase 1 z ∈ (subPullbackData hA c a).RZ.retract := by
    rw [(subPullbackData hA c a).RZ_retract, hz]
    exact (subPullbackData hA c a).ψ.mapsTo_model a haψ
  refine ⟨x.1, ⟨h, hh⟩, ?_⟩
  rw [← hx]
  exact (scDeriv_comp_apply_eq_of_retract_subset (subPullbackData hA c a).RZ
    (c.isRetraction.baseRetraction c.relOpen) (subPullbackData_retract_subset_base hA c a)
    (hf.isSc1_principal_comp_r hc)
    (fun u hu => principal_restrictSection_subPullback hA c a hf.1 _ hu) hzR ⟨h, hh⟩).symm

/-- **General position at a zero on a boundaryless sub-M-polyfold** (the step "in view of the
assumption that `(fᵢ, Xᵢ)` are already in general position" of the proof of 2021 Theorem
5.3.15, p. 223).  Let `f` be an sc-Fredholm section (tame germ data), `A ⊆ X` a sub-M-polyfold
without boundary, `f|A` sc-smooth in the pull-back bundle `ι*P → A`, and `a ∈ A` a zero with
`(f|A)'(a)` onto.  Then `(f, a)` is in general position in `X` (2021 Definition 5.3.9, p. 220).
*Proof*: in a tame chart `c` centred at `a`, `exists_scDeriv_eq_of_isLinSurjAt_restrict` gives,
for every `k` in the fibre, a vector `v ∈ T_0(φ(W ∩ A)) ⊆ T_0O` with `Lin_f(0)v = k`, and
`v ∈ E_0` because `A` has no boundary (`mem_minimalSubspaceWith_of_isWithoutBoundary`); so
`Lin_f(0)` is onto already on `T^R_0O`, hence `ker Lin_f(0) + T^R_0O = T_0O`, and the chart
criterion `isGeneralPositionGerm_of_sup_eq` concludes. -/
theorem isGeneralPositionGerm_of_restrict (hf : B.IsScFredholmSectionTame f)
    (hAb : (MPolyfold.subPolyfold hA).IsWithoutBoundary)
    (hfA : (B.pullback (MPolyfold.subPolyfold_inclusion_isScSmooth hA)).IsScSmoothSection
      (restrictSection P A f hf.isScSmooth.1))
    {a : A} (ha0 : IsZeroAt P f a.1)
    (hsurjA : (B.pullback (MPolyfold.subPolyfold_inclusion_isScSmooth hA)).IsLinSurjAt
      (restrictSection P A f hf.isScSmooth.1) a) :
    B.IsGeneralPositionGerm f a.1 := by
  classical
  have hxs : a.1 ∈ PX.smoothSet := hf.toIsScFredholmSection.mem_smoothSet_of_isZeroAt ha0
  obtain ⟨-, c, hc, hxc, hφ0, -⟩ := hf.germTame a.1 hxs
  obtain ⟨n, Wq, T, hT⟩ := c.φ.model.isPartialQuadrant
  have hz : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) = c.φ a.1 := by rw [map_zero, hφ0]
  set R' := c.isRetraction.baseRetraction c.relOpen with hR'
  -- `Lin_f(0)` is onto on `T^R_0O`
  have hkey : ∀ k, (c.φ a.1, k) ∈ c.K → ∃ w ∈ reducedTangentSpaceWith R' T 0,
      ∃ hw : w ∈ rangeS (scDeriv c.U (r c.R) 0), linAt c.U c.R (c.principal f) 0 ⟨w, hw⟩ = k := by
    intro k hk
    obtain ⟨v, hv, hvk⟩ := exists_scDeriv_eq_of_isLinSurjAt_restrict hA c a hf.isScSmooth hfA ha0
      hsurjA hc.1 hxc hz hk
    have hzR : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) ∈ (subPullbackData hA c a).RZ.retract := by
      rw [(subPullbackData hA c a).RZ_retract, hz]
      exact (subPullbackData hA c a).ψ.mapsTo_model a
        ((hA.data a.2).mem_shrink c.φ a.2 (hA.mem_data_V a.2) hxc)
    have hvr : scDeriv R'.U R' 0 v = v :=
      scDeriv_apply_eq_self_of_retract_subset (subPullbackData hA c a).RZ R'
        (subPullbackData_retract_subset_base hA c a) hzR hv
    have hvmin := mem_minimalSubspaceWith_of_isWithoutBoundary hA c a hAb hxc hz T hT hv
    refine ⟨v, ⟨⟨v, hvr⟩, ?_⟩, ⟨v, hvr⟩, hvk⟩
    rw [hz]; exact hvmin
  -- (i) surjectivity
  have hsurj : ∀ k, (c.φ a.1, k) ∈ c.K → ∃ x, linAt c.U c.R (c.principal f) 0 x = k := by
    intro k hk
    obtain ⟨w, -, hw, hwk⟩ := hkey k hk
    exact ⟨⟨w, hw⟩, hwk⟩
  -- (ii) `ker Lin_f(0) + T^R_0O = T_0O`
  have hzO : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) ∈ r c.R '' c.U := by
    rw [c.r_image, hz]; exact c.φ.mapsTo_model _ hxc
  have hzU : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) ∈ c.U := mem_U_of_mem_O c.isRetraction hzO
  have hsup : c.linKer f 0 ⊔ reducedTangentSpaceWith R' T 0 =
      LinearMap.range (scDeriv R'.U R' 0 : c.φ.model.E 0 →ₗ[ℝ] c.φ.model.E 0) := by
    refine le_antisymm (sup_le (c.linKer_le _ 0) inf_le_left) fun v hv => ?_
    have hv' : v ∈ rangeS (scDeriv c.U (r c.R) 0) := hv
    set k := linAt c.U c.R (c.principal f) 0 ⟨v, hv'⟩ with hkdef
    have hkρ : ρCLM c.isRetraction hzU k = k :=
      rho_scDeriv_comp_r c.relOpen c.isRetraction (hf.isScSmooth.isSc1_principal_comp_r hc.1)
        (fun x hx => c.principal_mem_K hf.isScSmooth.1 (c.r_image ▸ hx)) hzO
        (by rw [hz]; exact (c.isZeroAt_iff hf.isScSmooth.1 hxc).1 ha0) v
    have hkK : (c.φ a.1, k) ∈ c.K := by
      have h1 := c.mem_K_ρ (c.φ.mapsTo_model _ hxc) k
      rw [ρCLM_apply, hz] at hkρ
      rwa [hkρ] at h1
    obtain ⟨w, hwR, hw, hwk⟩ := hkey k hkK
    have hker : v - w ∈ c.linKer f 0 := by
      refine (c.mem_linKer_iff f 0 (v - w)).2 ⟨Submodule.sub_mem _ hv' hw, ?_⟩
      have := map_sub (linAt c.U c.R (c.principal f) 0) ⟨v, hv'⟩ ⟨w, hw⟩
      rw [hwk, ← hkdef, sub_self] at this
      exact this
    have : v = (v - w) + w := by abel
    rw [this]
    exact Submodule.add_mem_sup hker hwR
  exact isGeneralPositionGerm_of_sup_eq hf ha0 hc hxc hφ0 T hT hsurj hsup

end RestrictLin

section Theorem5315

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

variable (B) in
/-- **The hypotheses of 2021 Theorem 5.3.15 (p. 223) on the ends** of a generalized compact
homotopy `(f, t)`: for `i ∈ {0, 1}` the end `Xᵢ = t⁻¹(i)`, a sub-M-polyfold (Definition 5.3.13
(1)), has no boundary, and the end problem `fᵢ = f|Xᵢ` (Definition 5.3.13 (2): the restriction
`restrictSection` in the pull-back bundle `ι*P → Xᵢ`) is in general position at each of its zeros
(Definition 5.3.9, p. 220). -/
def StrongBundle.IsGeneralPositionAtEnds (f : X → Y) (hf : IsSection P f) (t : X → ℝ) : Prop :=
  ∀ i ∈ ({0, 1} : Set ℝ), ∀ hsub : PX.IsSubMPolyfold (t ⁻¹' {i}),
    haveI := PX.paracompactSpace_subtype (t ⁻¹' {i})
    (MPolyfold.subPolyfold hsub).IsWithoutBoundary ∧
      haveI := paracompactSpace_pullbackSpace (f := (Subtype.val : t ⁻¹' {i} → X))
        (MPolyfold.subPolyfold hsub) B
      ∀ a : t ⁻¹' {i},
        IsZeroAt (pullbackProj P (Subtype.val : t ⁻¹' {i} → X))
          (restrictSection P (t ⁻¹' {i}) f hf) a →
        (B.pullback (MPolyfold.subPolyfold_inclusion_isScSmooth hsub)).IsGeneralPositionGerm
          (restrictSection P (t ⁻¹' {i}) f hf) a

/-- **The ends give general position on `∂X`** (the step of the proof of 2021 Theorem 5.3.15,
p. 223, "in view of the assumption that `(fᵢ, Xᵢ)` are already in general position"): for a
generalized compact homotopy (Definition 5.3.13) whose ends are boundaryless and in general
position, and with `∂X ⊆ X₀ ∪ X₁`, the germ `(f, x)` is in general position at every zero
`x ∈ ∂X` (`isGeneralPositionGerm_of_restrict`). -/
theorem StrongBundle.IsSubmersiveGenCompactHomotopy.isGeneralPositionGerm_of_mem_boundary
    {t : X → ℝ} (h : B.IsSubmersiveGenCompactHomotopy f t)
    (hends : B.IsGeneralPositionAtEnds f h.isScFredholm.isScSmooth.1 t)
    (hbd : PX.boundary ⊆ t ⁻¹' {0} ∪ t ⁻¹' {1}) {x : X} (hxb : x ∈ PX.boundary)
    (hx0 : IsZeroAt P f x) : B.IsGeneralPositionGerm f x := by
  have hi : ∃ i ∈ ({0, 1} : Set ℝ), t x = i := by
    rcases hbd hxb with hx | hx
    · exact ⟨0, Or.inl rfl, hx⟩
    · exact ⟨1, Or.inr rfl, hx⟩
  obtain ⟨i, hi, hti⟩ := hi
  obtain ⟨hsub, -, hfA⟩ := h.ends i hi
  have := PX.paracompactSpace_subtype (t ⁻¹' {i})
  have := paracompactSpace_pullbackSpace (f := (Subtype.val : t ⁻¹' {i} → X))
    (MPolyfold.subPolyfold hsub) B
  obtain ⟨hAb, hgp⟩ := hends i hi hsub
  set a : t ⁻¹' {i} := ⟨x, hti⟩
  have ha0 : IsZeroAt (pullbackProj P (Subtype.val : t ⁻¹' {i} → X))
      (restrictSection P (t ⁻¹' {i}) f h.isScFredholm.isScSmooth.1) a :=
    (isZeroAt_restrictSection_iff _ a).2 hx0
  exact isGeneralPositionGerm_of_restrict hsub h.isScFredholm hAb hfA.isScSmooth (a := a) hx0
    (hgp a ha0).isLinSurjAt

/-- **2021 Theorem 5.3.15, p. 223** (2017: Theorem 5.8; preprint: Theorem 5.22), the
compactness statement and conclusion (1), under the printed hypotheses.  Let `X` admit sc-smooth
bump functions, `(f, t)` a generalized compact homotopy (Definition 5.3.13:
`IsSubmersiveGenCompactHomotopy`) whose ends `Xᵢ = t⁻¹(i)` have no boundary and whose end
problems `fᵢ = f|Xᵢ` are in general position at all their zeros (`IsGeneralPositionAtEnds`), with
`∂X = X₀ ∪ X₁`, and `N` an auxiliary norm.  Then there is an open `U ⊇ S_f` such that `S_{f+s}`
is compact for every `s ∈ Γ^{+,1}_U(P)`, and for every `ε > 0` an `s₀ ∈ Γ^{+,1}_U(P)` with
`N(s₀(x)) ≤ ε` for all `x`, vanishing near `∂X`, such that `(f + s₀, x)` is in general position
at every `x ∈ S_{f+s₀}`.  *Proof*: `theorem_5_3_15_generalPosition_hyp` with its hypothesis on
`∂X` from `isGeneralPositionGerm_of_mem_boundary`.  Conclusion (2) (Morse-type critical points
of `t`) is not part of this statement.  The bump functions on the `Xᵢ` that the text also assumes
are not needed. -/
theorem theorem_5_3_15_generalPosition (hbump : PX.AdmitsBumpFunctions) {t : X → ℝ}
    (h : B.IsSubmersiveGenCompactHomotopy f t)
    (hends : B.IsGeneralPositionAtEnds f h.isScFredholm.isScSmooth.1 t)
    (hbd : PX.boundary = t ⁻¹' {0} ∪ t ⁻¹' {1}) {N : B.One → ℝ} (hN : B.IsAuxNorm N) :
    ∃ U : Set X, IsOpen U ∧ solutionSet P f ⊆ U ∧
      (∀ s ∈ B.allowableSections N U, IsCompact (solutionSet P (sectionAdd P f s))) ∧
      ∀ ε > 0, ∃ s₀ ∈ B.allowableSections N U,
        (∀ x (hx : s₀ x ∈ B.oneSet), N (B.oneMk (s₀ x) hx) ≤ ε) ∧
        (∀ᶠ x in 𝓝ˢ PX.boundary, IsZeroAt P s₀ x) ∧
        ∀ x ∈ solutionSet P (sectionAdd P f s₀), B.IsGeneralPositionGerm (sectionAdd P f s₀) x :=
  theorem_5_3_15_generalPosition_hyp h.isTame hbump h.isScFredholm h.isCompact hN
    fun _ hxb hx0 => h.isGeneralPositionGerm_of_mem_boundary hends hbd.le hxb hx0

end Theorem5315

section Witness

open GenCompactHomotopyWitness TrivialBundle

/-- **Satisfiability of the hypotheses of `theorem_5_3_15_generalPosition`**: for the generalized
compact homotopy `isSubmersiveGenCompactHomotopy_witness` (the graph section of `id` on `ℝ`,
`t(x) = 1/2 + arctan(x)/π`) the ends are empty, so `IsGeneralPositionAtEnds` holds, and
`∂ℝ = ∅ = X₀ ∪ X₁`. -/
theorem theorem_5_3_15_generalPosition_witness :
    (bundle 1 1).IsGeneralPositionAtEnds (graphSection (_root_.id : (Fin 1 → ℝ) → (Fin 1 → ℝ)))
        isSubmersiveGenCompactHomotopy_witness.isScFredholm.isScSmooth.1 arctanTime ∧
      (rnPolyfold 1).boundary = arctanTime ⁻¹' {0} ∪ arctanTime ⁻¹' {1} := by
  refine ⟨fun i hi hsub => ⟨fun a => ?_, fun a _ => ?_⟩, ?_⟩
  · exact absurd a.2 (eq_empty_iff_forall_notMem.1 (arctanTime_preimage_eq_empty hi) a.1)
  · exact absurd a.2 (eq_empty_iff_forall_notMem.1 (arctanTime_preimage_eq_empty hi) a.1)
  · rw [arctanTime_preimage_eq_empty (Or.inl rfl), arctanTime_preimage_eq_empty (Or.inr rfl),
      union_empty]
    exact (MPolyfold.isWithoutBoundary_iff _).1 (rnPolyfold_degIndex 1)

end Witness

end Polyfold
