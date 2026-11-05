import Polyfold.Chapter4.Characterization
import Polyfold.Chapter3.GlobalIFTNearbyGraph
import Polyfold.Chapter2.Metrizable

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §4.2,
Definition 4.13, Remark 4.14, Proposition 4.15, Definitions 4.16, 4.17, Theorem 4.18, Lemma 4.19,
Remark 4.20, Definition 4.21 *(book 2017: Definition 4.4, Remark 4.3, Proposition 4.3, Definitions
4.5, 4.6, Theorem 4.2, Lemma 4.6, Remark 4.4, Definition 4.7; see `BookConcordance.md`)*.

# Smooth finite-dimensional submanifolds

## The text, paraphrased

(Definition 4.13) `A ⊆ X` is a smooth finite-dimensional submanifold if every `a ∈ A` has an open
neighbourhood `V ⊆ X` and an sc⁺-retraction `s : V → V` with `s(V) = A ∩ V`.  (Remark 4.14) `s(V)`
consists of smooth points, `T_aA = Ts(a)(T_aX)` is the image of the sc⁺-operator `Ts(a)`, hence
finite-dimensional; near points with `d_X(a) = 0`, and where `T_aA` is in good position to
`C_aX`, `A` is a manifold in the classical sense.  (Proposition 4.15) (1) `A ⊆ X_∞` and `A` inherits
the M-polyfold structure of `X` (Proposition 2.21); (2) `A` is locally closed; (3)
`∂A = {d_A ≥ 1} ⊆ ∂X`; (4) `1₀¹ : A → A¹` is sc-smooth.  (Open question) Is a sub-M-polyfold with
`A = A_∞` and `dim T_aA` finite and locally constant a smooth finite-dimensional submanifold?
(Definition 4.16) For tame `X`, `A` is in good position at `a` if `T_aA` is in good position to the
partial quadrant `C_aX` in `T_aX`.  (Definition 4.17) `A` is tame if its induced M-polyfold
structure is tame.  (Theorem 4.18) If `X` is tame and `A` is in good position at every point, the
induced structure on `A` is that of a smooth manifold with boundary with corners, and `A` is tame.
*Proof*: in a tame chart `ϕ` centred at `a` with `T₀O = N ⊕ Y ⊕ Z` (`Z ⊆ C` the sc-complement of
Proposition 2.35), (Lemma 4.19) `N = Tϕ(a)(T_aA)` is in good position to `C` with good complement
`Y ⊕ Z`; `t = ϕ ∘ s ∘ ϕ⁻¹ ∘ r` is an sc⁺-retraction onto `ϕ(A ∩ V)` with `Dt(0)E = N`, and
Proposition 4.9 gives the sc-diffeomorphism `p : V₁ → V₀ ⊆ N ∩ C`; the charts `p ∘ ϕ` form the
manifold structure ("Proposition 4.2", i.e. Theorem 4.2).  (Remark 4.20) Good position is an open
condition along `A` (Proposition 4.9 and Lemma 3.55).  (Definition 4.21) `A` is in general position
at `a` if `T_aA` has in `T_aX` an sc-complement contained in `T_a^R X`.

## What is formalized

* **Tangent spaces of sub-retracts** (chart level): `tangentSpace_inter_isOpen` (the tangent space
  of a retract is a germ), `tangentSpace_subset_of_subset` (`T_zQ ⊆ T_zO` for `Q ⊆ O`),
  `scDeriv_mem_tangentSpace_of_subset` (`D(F ∘ r)(z)` maps `T_zQ` into `T_{F(z)}Q'`).
* **Definition 4.16 in a chart**: `IsGoodPositionRetractAt` (`T_zQ` in good position to `C_z`
  inside `T_zO`, `IsInGoodPositionIn`), carried by germs of sc-diffeomorphisms
  (`IsGoodPositionRetractAt.transport`, through `proposition_2_30_cone` and
  `IsInGoodPositionIn.transport`).  **Definition 4.21 in a chart**: `IsGeneralPositionRetractAt`
  (an sc-subspace `B ⊆ T_zO ∩ E_z` with `(T_zO)_m = (T_zQ)_m ⊕ B_m` on every level), carried by
  germs of sc-diffeomorphisms at smooth points (`IsGeneralPositionRetractAt.transport`, through
  `proposition_2_30_reduced`).  The chart change for both (`chart_change_of_transport`,
  `isGoodPositionRetractAt_chart_change`, `isGeneralPositionRetractAt_chart_change`).
* `isInGoodPosition_univ`, `partialQuadrantAtWith_eq_univ_of_degIndex_eq_zero`;
  `hasFDerivWithinAt_scDeriv_const`,
  `tangentSpace_eq_range_graph` (the tangent spaces along the graph of Proposition 4.9).
* **Lemma 4.19**: `lemma_4_19` (with the explicit good complement `Y ⊕ (1 − π)E`,
  `isGoodComplement_sup_range`).
* **Definition 4.13**: `MPolyfold.SubmanifoldData`, `MPolyfold.IsSmoothSubmanifold`,
  `isSmoothSubmanifold_iff`, `SubmanifoldData.toSubData`, `IsSmoothSubmanifold.isSubMPolyfold`;
  in a chart: `SubmanifoldData.isScSmoothRetractMap_lift` (the sc⁺ property of `s` read in the
  charts of `X` and `X¹`), `SubmanifoldData.exists_chartRetraction` (**the sc⁺-retraction
  `t = φ ∘ s ∘ φ⁻¹ ∘ r`** of the proof of Theorem 4.18), `SubmanifoldData.isScPlusRetract_image`,
  `SubmanifoldData.apply_mem_smooth`.
* **Remark 4.14**: `SubmanifoldData.remark_4_14` (in a chart: `T_aA = Ts(a)T_aX`, `T_aA ⊆ T_aX`,
  finite-dimensional), `isGoodPositionAt_of_degIndex_eq_zero`,
  `hasCornerStructure_of_degIndex_eq_zero`.
* **Proposition 4.15**: `IsSmoothSubmanifold.proposition_4_15_1` (and `subset_smoothSet`,
  `mem_levelSet_subPolyfold_iff`), `proposition_4_15_2` (Mathlib's `IsLocallyClosed`),
  `proposition_4_15_3`, `proposition_4_15_4`.
* **Definition 4.16**: `SubmanifoldData.IsGoodPositionChart`, `MPolyfold.IsGoodPositionAt`, with
  chart independence `IsGoodPositionAt.isGoodPositionChart`, `isGoodPositionAt_iff_forall`, and the
  explicit chart form `SubmanifoldData.isGoodPositionChart_iff` (`Dt(z)E` in good position to `C_z`
  inside `Dr(z)E`).  **Definition 4.21**: `SubmanifoldData.IsGeneralPositionChart`,
  `MPolyfold.IsGeneralPositionAt`, `IsGeneralPositionAt.isGeneralPositionChart`,
  `isGeneralPositionAt_iff_forall`.  **Definition 4.17**: `MPolyfold.IsTameSubmanifold`.
* **Theorem 4.18**: `MPolyfold.theorem_4_18`, through
  `hasCornerStructure_of_centred_isInGoodPosition`
  (Theorem 4.2 (ii) ⇒ (i) for the induced structure) and `IsGoodPositionAt.isInGoodPosition_of_tame`
  (Lemma 4.19 in a tame centred chart).
* **Remark 4.20**: `MPolyfold.remark_4_20`.

## What the text leaves implicit, and the choices made

* `T_xX` carries no linear structure here (gap G.7), so Definitions 4.16 and 4.21 are stated in a
  chart, as Definition 3.53 is (`LinearizationCharts.lean`), and their independence of the chart, of
  the data of Definition 4.13 and of the presentation of the partial quadrant is proved; the text
  asserts it implicitly.  The chart form of `T_aA` is the tangent space of the retract `φ(W ∩ A)` of
  the induced chart of `A` (Proposition 2.21), equal to `Dt(z)E` for the sc⁺-retraction
  `t = φ ∘ s ∘ φ⁻¹ ∘ r`; "good position to the partial cone `C_aX` in `T_aX`" is good position
  to `C_z` inside `T_zO` (`IsInGoodPositionIn`).  Neither the definitions nor their chart
  independence need tameness; tameness of `X` enters Theorem 4.18 and Remark 4.20 only through
  Lemma 4.19.
* **Proposition 4.15 (2)**: the text's definition of "locally closed" (lines 6463–6466) is garbled
  ("`b` belongs to `A` if `U ∩ A ≠ ∅` for all open neighbourhoods `U` of `b`" uses `U` twice);
  Mathlib's `IsLocallyClosed` is used, through its characterization "every `a ∈ A` has an open `U`
  with `U ∩ cl(A) ⊆ A`".  The text's sequence `a_k → b` is replaced by a filter (no metrizability
  is needed).
* **Proposition 4.15 (1), (4)**: "`A ⊆ X_∞`" and "`1₀¹ : A → A¹` is sc-smooth" are proved in the
  charts of `A` induced by charts of `X`: their models `φ(W ∩ A)` are sc⁺-retracts, the sc⁺
  property of `t = φ ∘ s ∘ φ⁻¹ ∘ r` coming from the condition "`1₀¹ ∘ s : V → X¹` sc-smooth" of
  Definition 4.4 read in the level charts of `X¹`; Proposition 4.8 then applies in each chart
  (`isScSmoothMap_toLevelOne_of_cover`).  The text's "the postulated sc⁺-retraction is the
  identity on the retract `A`" skips this.
* **Theorem 4.18** follows the text's route through Theorem 4.2 ("Proposition 4.2" in the proof):
  the chart of `X` centred at `a` is the re-centred tame chart (`IsTame.exists_centredChart`), the
  projection of Proposition 4.9 is taken along a closed good complement (Findings Chapter 4, items
  20–21, 54), and the compatibility of the charts `p ∘ ϕ`, not argued in the text, is that of
  Theorem 4.2 (`hasCornerStructure_of_centred`, Finding 55).  No hypothesis is added; the
  paracompactness of `A` is an instance argument `[ParacompactSpace A]` (proved for every subset by
  `MPolyfold.paracompactSpace_subtype`), as for `subPolyfold`.
* **Remark 4.20** is stated in the text without "tame"; it is proved for tame `X` (Definition 4.16
  is for tame `X`, and Lemma 4.19 is used).  "The tangent spaces of `A` move only slowly" is the
  `C¹` property of the graph map `σ = (1 − π) ∘ Γ` of Proposition 4.9 with `Dσ(0) = 0`, and Lemma
  3.55 needs a closed good complement, chosen by the normal form (`exists_proj_goodComplement`).
* **Definition 4.21** uses the sc-structure induced on `T_zO` (an sc-subspace of `E` at a smooth
  point); the transport of the sc-complement needs the smoothness of the point, which holds on `A`.
* The **open question** after Proposition 4.15 (lines ≈ 6497–6510) is not formalized.
-/

open Set Filter Topology Function Module

noncomputable section

namespace Polyfold

/-! ### Tangent spaces of sub-retracts -/

section SubRetract

variable {E E' : ScBanach} {C Q : Set (E 0)} {C' : Set (E' 0)}

/-- **The tangent space of a retract is a germ**: for an open `K`, the tangent space of the retract
`Q ∩ K` (Proposition 2.10 (1)) at a point of `K` is that of `Q`. -/
theorem tangentSpace_inter_isOpen (hQ : IsScRetract E C Q) {K : Set (E 0)} (hK : IsOpen K)
    {z : E 1} (hz : E.toBase 1 z ∈ Q ∩ K) :
    tangentSpace E C (Q ∩ K) z = tangentSpace E C Q z := by
  obtain ⟨R, rfl⟩ := hQ
  have hRK := R.restrict_retract hK
  have hz1 : z ∈ E.lvlSet (R.restrict hK).retract 1 := by rw [ScBanach.mem_lvlSet, hRK]; exact hz
  have hzU : z ∈ E.lvlSet (R.restrict hK).U 1 := (R.restrict hK).lvlSet_retract_subset 1 hz1
  rw [← hRK, tangentSpace_eq_range _ hz1, tangentSpace_eq_range R hz.1]
  have : scDeriv (R.restrict hK).U (R.restrict hK) z = scDeriv R.U R z :=
    scDeriv_eq_of_eqOn_relOpen (R.restrict hK).relOpen (R.restrict hK).isSc1 R.isSc1 subset_rfl
      inter_subset_left (fun _ _ => rfl) hzU
  rw [this]

/-- **The tangent space of a sub-retract lies in that of the retract**: for retracts `Q ⊆ O = r(U)`
and `z ∈ Q₁`, `T_zQ ⊆ T_zO` (with a retraction `s` onto `Q`, `s = r ∘ s`, so
`Ds(z) = Dr(z) Ds(z)`). -/
theorem tangentSpace_subset_of_subset (R : ScRetraction E C) (hQ : IsScRetract E C Q)
    (hQR : Q ⊆ R.retract) {z : E 1} (hz : z ∈ E.lvlSet Q 1) :
    tangentSpace E C Q z ⊆ tangentSpace E C R.retract z := by
  obtain ⟨S, rfl⟩ := hQ
  intro v hv
  have hzR : z ∈ E.lvlSet R.retract 1 := hQR hz
  rw [tangentSpace_eq_range S hz] at hv
  rw [tangentSpace_eq_range R hzR]
  obtain ⟨w, rfl⟩ := hv
  have hmaps : MapsTo S S.U R.U := fun y hy => R.retract_subset (hQR (S.apply_mem_retract hy))
  have hzU : z ∈ E.lvlSet S.U 1 := S.lvlSet_retract_subset 1 hz
  have h1 := scDeriv_comp_apply S.relOpen R.relOpen S.isSc1 R.isSc1 hmaps hzU w
  rw [S.levelMap_one_eq_self hz] at h1
  have hRS : EqOn (R ∘ S) S S.U := fun y hy =>
    R.apply_eq_self_of_mem_retract (hQR (S.apply_mem_retract hy))
  have h2 : scDeriv S.U (R ∘ S) z = scDeriv S.U S z :=
    scDeriv_eq_of_eqOn_relOpen S.relOpen
      (theorem_1_21 S.relOpen R.relOpen S.isSc1 R.isSc1 hmaps).1 S.isSc1 subset_rfl subset_rfl
      hRS hzU
  rw [h2] at h1
  exact ⟨scDeriv S.U S z w, h1⟩

/-- **The derivative of a map between retracts maps tangent spaces of sub-retracts**: let
`F ∘ r` be sc-smooth for a retraction `r` onto `O`, and let `Q ⊆ O`, `Q'` be retracts with
`F(Q) ⊆ Q'`.  Then at `z ∈ Q₁` the derivative `D(F ∘ r)(z)` maps `T_zQ` into `T_{F(z)}Q'`
(Proposition 2.6 (3) for `F|_Q`, whose tangent map at `z` is `D(F ∘ r)(z)` on `T_zQ`). -/
theorem scDeriv_mem_tangentSpace_of_subset (R : ScRetraction E C) {F : E 0 → E' 0}
    (hF : IsScSmooth R.U (F ∘ R)) (hQ : IsScRetract E C Q) {Q' : Set (E' 0)}
    (hQ' : IsScRetract E' C' Q') (hQR : Q ⊆ R.retract) (hFQ : MapsTo F Q Q') {z : E 1}
    (hz : z ∈ E.lvlSet Q 1) {v : E 0} (hv : v ∈ tangentSpace E C Q z) :
    scDeriv R.U (F ∘ R) z v ∈ tangentSpace E' C' Q' (levelMap (F ∘ R) 1 z) := by
  obtain ⟨S, rfl⟩ := hQ
  obtain ⟨S', rfl⟩ := hQ'
  have hmaps : MapsTo S S.U R.U := fun y hy => R.retract_subset (hQR (S.apply_mem_retract hy))
  have hzU : z ∈ E.lvlSet S.U 1 := S.lvlSet_retract_subset 1 hz
  have hFS : EqOn ((F ∘ R) ∘ S) (F ∘ S) S.U := fun y hy => by
    simp only [Function.comp_apply, R.apply_eq_self_of_mem_retract (hQR (S.apply_mem_retract hy))]
  have hFSsm : IsScSmooth S.U (F ∘ S) :=
    (IsScSmooth.comp S.isScDomain R.isScDomain hF S.isScSmooth hmaps).congr S.isScDomain hFS
  have hT := proposition_2_6_3 S S' hFSsm hFQ
  have hvS : ((z, v) : E.tangent 0) ∈ S.tangent := by
    have : ((z, v) : E.tangent 0) ∈ retractTangent E C S.retract := hv
    rwa [retractTangent_eq] at this
  have h := hT hvS
  have hlev : levelMap (F ∘ S) 1 z = levelMap (F ∘ R) 1 z := by
    apply levelMap_eq_of_toBase_eq
    rw [hF.isSc1.isSc0.toBase_levelMap
      (R.lvlSet_retract_subset 1 (show z ∈ E.lvlSet R.retract 1 from hQR hz))]
    have h1 := hFS hzU
    simp only [Function.comp_apply, S.apply_eq_self_of_mem_retract hz] at h1 ⊢
    exact h1
  have hDv : scDeriv S.U (F ∘ S) z v = scDeriv R.U (F ∘ R) z v := by
    have h1 := scDeriv_comp_apply' S.relOpen R.relOpen S.isSc1 hF.isSc1 hmaps hzU v
    rw [S.levelMap_one_eq_self hz, (S.mem_tangent_iff_of_mem hz).1 hvS] at h1
    rw [h1]
    exact congrArg (fun L : E 0 →L[ℝ] E' 0 => L v)
      (scDeriv_eq_of_eqOn_relOpen S.relOpen
        (theorem_1_21 S.relOpen R.relOpen S.isSc1 hF.isSc1 hmaps).1 hFSsm.isSc1 subset_rfl
        subset_rfl hFS hzU).symm
  change ((levelMap (F ∘ R) 1 z, scDeriv R.U (F ∘ R) z v) : E'.tangent 0) ∈
    retractTangent E' C' S'.retract
  rw [retractTangent_eq, ← hlev, ← hDv]
  exact h

end SubRetract

/-! ### Good position of a sub-retract (Definition 4.16 in a chart) -/

section GoodPositionRetract

variable {E E' : ScBanach} {C : Set (E 0)} {C' : Set (E' 0)} {n n' : ℕ} {Wq Wq' : ScBanach}

/-- **Definition 4.16 in a chart**: for retracts `Q ⊆ O` (`Q` the image of the submanifold in the
chart, `O` the model of the chart), a presentation `T` of `C` and a level-`1` point `z` of `Q`, the
tangent space `T_zQ` is **in good position to the partial cone `C_zO = T_zO ∩ C_z` inside `T_zO`**
(`IsInGoodPositionIn`, the form of Definition 3.21 inside a subspace used for Definition 3.53).
The tangent spaces are those of Definition 2.17; `N` and `M` are the corresponding subspaces. -/
def IsGoodPositionRetractAt (E : ScBanach) (C O Q : Set (E 0))
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod Wq)) (z : E 1) : Prop :=
  ∃ N M : Submodule ℝ (E 0), (N : Set (E 0)) = tangentSpace E C Q z ∧
    (M : Set (E 0)) = tangentSpace E C O z ∧
    IsInGoodPositionIn E M (partialQuadrantAtWith T (E.toBase 1 z)) N

/-- The condition depends only on the tangent spaces. -/
theorem IsGoodPositionRetractAt.congr {O Q O₂ Q₂ : Set (E 0)}
    {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod Wq)} {z : E 1}
    (hQ : tangentSpace E C Q z = tangentSpace E C Q₂ z)
    (hO : tangentSpace E C O z = tangentSpace E C O₂ z) (h : IsGoodPositionRetractAt E C O Q T z) :
    IsGoodPositionRetractAt E C O₂ Q₂ T z := by
  obtain ⟨N, M, hN, hM, hg⟩ := h
  exact ⟨N, M, hN.trans hQ, hM.trans hO, hg⟩

/-- **Good position of a sub-retract is carried by a germ of sc-diffeomorphisms** (the chart
independence of Definition 4.16): let `F : O → O'` be a germ of sc-diffeomorphisms between the
retracts `O = r(U)`, `O' = r'(U')` with inverse `G` (`F ∘ r`, `G ∘ r'` sc-smooth), and `Q ⊆ O`,
`Q' ⊆ O'` sub-retracts with `F(Q) ⊆ Q'`, `G(Q') ⊆ Q`.  If `T_zQ` is in good position to `C_zO`
inside `T_zO`, then `T_{F(z)}Q'` is in good position to `C'_{F(z)}O'` inside `T_{F(z)}O'`.
*Proof.* `A = D(F ∘ r)(z)` restricts to an isomorphism `T_zO ≅ T_{F(z)}O'` (inverse
`D(G ∘ r')(F(z))`) carrying `C_zO` onto `C'_{F(z)}O'` (Proposition 2.30, `proposition_2_30_cone`)
and `T_zQ` onto `T_{F(z)}Q'` (`scDeriv_mem_tangentSpace_of_subset` in both directions); good
position inside a subspace is transported by such isomorphisms (`IsInGoodPositionIn.transport`,
Lemma 3.45). -/
theorem IsGoodPositionRetractAt.transport {R : ScRetraction E C} {R' : ScRetraction E' C'}
    {F : E 0 → E' 0} {G : E' 0 → E 0} (h : R.IsDiffeoGerm R' F G)
    (hFs : IsScSmooth R.U (F ∘ R)) (hGs : IsScSmooth R'.U (G ∘ R'))
    {Q : Set (E 0)} {Q' : Set (E' 0)} (hQ : IsScRetract E C Q) (hQ' : IsScRetract E' C' Q')
    (hQR : Q ⊆ R.retract) (hQ'R : Q' ⊆ R'.retract) (hFQ : MapsTo F Q Q') (hGQ : MapsTo G Q' Q)
    {z : E 1} (hz : z ∈ E.lvlSet Q 1)
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod Wq)) (hT : C = T 0 ⁻¹' quadrant n Wq 0)
    (T' : ScIso E' ((ScBanach.const (Fin n' → ℝ)).prod Wq'))
    (hT' : C' = T' 0 ⁻¹' quadrant n' Wq' 0)
    (hgp : IsGoodPositionRetractAt E C R.retract Q T z) :
    IsGoodPositionRetractAt E' C' R'.retract Q' T' (levelMap (F ∘ R) 1 z) := by
  obtain ⟨N, M, hN, hM, hgood⟩ := hgp
  have hx : z ∈ E.lvlSet R.retract 1 := hQR hz
  have hy' : levelMap (F ∘ R) 1 z ∈ E'.lvlSet R'.retract 1 := h.image_mem hx
  have hMeq : M = rangeS (scDeriv R.U R z) :=
    SetLike.coe_injective (hM.trans (tangentSpace_eq_coe_submodule R hx))
  subst hMeq
  have himg : levelMap (G ∘ R') 1 (levelMap (F ∘ R) 1 z) = z := h.image_image hx
  have hTA : ∀ v ∈ rangeS (scDeriv R.U R z),
      scDeriv R.U (F ∘ R) z v ∈ rangeS (scDeriv R'.U R' (levelMap (F ∘ R) 1 z)) := by
    intro v hv
    obtain ⟨u, hu⟩ := h.deriv_mem_range hx (v := v) (by obtain ⟨w, hw⟩ := hv; exact ⟨w, hw⟩)
    exact ⟨u, hu⟩
  have hTA' : ∀ w ∈ rangeS (scDeriv R'.U R' (levelMap (F ∘ R) 1 z)),
      scDeriv R'.U (G ∘ R') (levelMap (F ∘ R) 1 z) w ∈ rangeS (scDeriv R.U R z) := by
    intro w hw
    have := h.symm.deriv_mem_range hy' (v := w) (by obtain ⟨u, hu⟩ := hw; exact ⟨u, hu⟩)
    rw [himg] at this
    obtain ⟨u, hu⟩ := this
    exact ⟨u, hu⟩
  have hinv1 : ∀ v ∈ rangeS (scDeriv R.U R z),
      scDeriv R'.U (G ∘ R') (levelMap (F ∘ R) 1 z) (scDeriv R.U (F ∘ R) z v) = v := by
    rintro _ ⟨w, rfl⟩
    rw [h.deriv_inv_deriv hx]
    exact congrArg (fun L : E 0 →L[ℝ] E 0 => L w) (R.scDeriv_comp_self hx)
  have hinv2 : ∀ w ∈ rangeS (scDeriv R'.U R' (levelMap (F ∘ R) 1 z)),
      scDeriv R.U (F ∘ R) z (scDeriv R'.U (G ∘ R') (levelMap (F ∘ R) 1 z) w) = w := by
    rintro _ ⟨u, rfl⟩
    rw [h.deriv_deriv_inv hx]
    exact congrArg (fun L : E' 0 →L[ℝ] E' 0 => L u) (R'.scDeriv_comp_self hy')
  set A := restrictEquiv _ _ _ _ hTA hTA' hinv1 hinv2 with hAdef
  -- the partial cones correspond (Proposition 2.30)
  have hcone := proposition_2_30_cone h hx T hT T' hT'
  simp only [partialConeWith] at hcone
  have hAC : ∀ x : ↥(rangeS (scDeriv R.U R z)),
      (x : E 0) ∈ partialQuadrantAtWith T (E.toBase 1 z) ↔
        (A x : E' 0) ∈ partialQuadrantAtWith T' (E'.toBase 1 (levelMap (F ∘ R) 1 z)) := by
    intro x
    have hxT : (x : E 0) ∈ range (scDeriv R.U R z) := by
      obtain ⟨w, hw⟩ := x.2; exact ⟨w, hw⟩
    rw [hAdef, restrictEquiv_apply]
    constructor
    · intro hxC
      have : scDeriv R.U (F ∘ R) z x ∈ scDeriv R.U (F ∘ R) z ''
          (range (scDeriv R.U R z) ∩ partialQuadrantAtWith T (E.toBase 1 z)) :=
        ⟨x, ⟨hxT, hxC⟩, rfl⟩
      rw [hcone] at this
      exact this.2
    · intro hAxC
      have hAxT : scDeriv R.U (F ∘ R) z x ∈ range (scDeriv R'.U R' (levelMap (F ∘ R) 1 z)) := by
        obtain ⟨w, hw⟩ := hTA x x.2; exact ⟨w, hw⟩
      have : scDeriv R.U (F ∘ R) z x ∈ range (scDeriv R'.U R' (levelMap (F ∘ R) 1 z)) ∩
          partialQuadrantAtWith T' (E'.toBase 1 (levelMap (F ∘ R) 1 z)) := ⟨hAxT, hAxC⟩
      rw [← hcone] at this
      obtain ⟨w, ⟨hwT, hwC⟩, hwx⟩ := this
      have hwT' : w ∈ rangeS (scDeriv R.U R z) := by obtain ⟨u, hu⟩ := hwT; exact ⟨u, hu⟩
      have : w = x := by rw [← hinv1 w hwT', hwx, hinv1 x x.2]
      rw [← this]; exact hwC
  refine ⟨transportSub A N, rangeS (scDeriv R'.U R' (levelMap (F ∘ R) 1 z)), ?_,
    (tangentSpace_eq_coe_submodule R' hy').symm, hgood.transport A hAC⟩
  -- `A(T_zQ) = T_{F(z)}Q'`
  have hzQ' : levelMap (F ∘ R) 1 z ∈ E'.lvlSet Q' 1 := by
    rw [ScBanach.mem_lvlSet, h.toBase_image hx]; exact hFQ hz
  ext w
  constructor
  · intro hw
    obtain ⟨x, hxN, rfl⟩ := (mem_transportSub A).1 hw
    rw [hAdef, restrictEquiv_apply]
    have hxQ : (x : E 0) ∈ tangentSpace E C Q z := by rw [← hN]; exact hxN
    exact scDeriv_mem_tangentSpace_of_subset R hFs hQ hQ' hQR hFQ hz hxQ
  · intro hw
    have hwM : w ∈ rangeS (scDeriv R'.U R' (levelMap (F ∘ R) 1 z)) := by
      have := tangentSpace_subset_of_subset R' hQ' hQ'R hzQ' hw
      rw [tangentSpace_eq_coe_submodule R' hy'] at this; exact this
    have h1 : scDeriv R'.U (G ∘ R') (levelMap (F ∘ R) 1 z) w ∈ tangentSpace E C Q z := by
      have := scDeriv_mem_tangentSpace_of_subset R' hGs hQ' hQ hQ'R hGQ hzQ' hw
      rwa [himg] at this
    rw [SetLike.mem_coe, mem_transportSub]
    refine ⟨⟨_, hTA' w hwM⟩, by rw [← SetLike.mem_coe, hN]; exact h1, ?_⟩
    rw [hAdef, restrictEquiv_apply]
    exact hinv2 w hwM

/-- **Definition 4.21 in a chart**: for retracts `Q ⊆ O`, a presentation `T` of `C` and a level-`1`
point `z` of `Q`, **`T_zQ` has in `T_zO` an sc-complement contained in the reduced tangent space
`T_z^R O = T_zO ∩ E_z`** (Definitions 2.27, 2.38): an sc-subspace `B ⊆ T_zO ∩ E_z` of `E` with
`(T_zO)_m = (T_zQ)_m ⊕ B_m` on every level (the form of the sc-splitting of
`proposition_2_21_3`). -/
def IsGeneralPositionRetractAt (E : ScBanach) (C O Q : Set (E 0))
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod Wq)) (z : E 1) : Prop :=
  ∃ N M B : Submodule ℝ (E 0), (N : Set (E 0)) = tangentSpace E C Q z ∧
    (M : Set (E 0)) = tangentSpace E C O z ∧ B ≤ M ⊓ minimalSubspaceWith T (E.toBase 1 z) ∧
    E.IsScSubspace B ∧ ∀ m, Disjoint (E.levelSub N m) (E.levelSub B m) ∧
      E.levelSub N m ⊔ E.levelSub B m = E.levelSub M m

/-- The condition depends only on the tangent spaces. -/
theorem IsGeneralPositionRetractAt.congr {O Q O₂ Q₂ : Set (E 0)}
    {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod Wq)} {z : E 1}
    (hQ : tangentSpace E C Q z = tangentSpace E C Q₂ z)
    (hO : tangentSpace E C O z = tangentSpace E C O₂ z)
    (h : IsGeneralPositionRetractAt E C O Q T z) : IsGeneralPositionRetractAt E C O₂ Q₂ T z := by
  obtain ⟨N, M, B, hN, hM, hB⟩ := h
  exact ⟨N, M, B, hN.trans hQ, hM.trans hO, hB⟩

/-- **General position of a sub-retract is carried by a germ of sc-diffeomorphisms** (the chart
independence of Definition 4.21), at a smooth point `z`: with `A = D(F ∘ r)(z)`, an sc-operator
since `z` is smooth, inverse to `D(G ∘ r')(F(z))` on `T_zO` and `T_{F(z)}O'`, the image `A(B)` of
an sc-complement `B ⊆ T_z^R O` of `T_zQ` in `T_zO` is an sc-complement of `T_{F(z)}Q' = A(T_zQ)` in
`T_{F(z)}O'`, contained in `T^R_{F(z)}O' = A(T_z^R O)` (Proposition 2.30,
`proposition_2_30_reduced`). -/
theorem IsGeneralPositionRetractAt.transport {R : ScRetraction E C} {R' : ScRetraction E' C'}
    {F : E 0 → E' 0} {G : E' 0 → E 0} (h : R.IsDiffeoGerm R' F G)
    (hFs : IsScSmooth R.U (F ∘ R)) (hGs : IsScSmooth R'.U (G ∘ R'))
    {Q : Set (E 0)} {Q' : Set (E' 0)} (hQ : IsScRetract E C Q) (hQ' : IsScRetract E' C' Q')
    (hQR : Q ⊆ R.retract) (hQ'R : Q' ⊆ R'.retract) (hFQ : MapsTo F Q Q') (hGQ : MapsTo G Q' Q)
    {z : E 1} (hz : z ∈ E.lvlSet Q 1) (hzs : z ∈ E.smoothLvl 1)
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod Wq)) (hT : C = T 0 ⁻¹' quadrant n Wq 0)
    (T' : ScIso E' ((ScBanach.const (Fin n' → ℝ)).prod Wq'))
    (hT' : C' = T' 0 ⁻¹' quadrant n' Wq' 0)
    (hgp : IsGeneralPositionRetractAt E C R.retract Q T z) :
    IsGeneralPositionRetractAt E' C' R'.retract Q' T' (levelMap (F ∘ R) 1 z) := by
  obtain ⟨N, M, B, hN, hM, hBM, hB, hsplit⟩ := hgp
  have hx : z ∈ E.lvlSet R.retract 1 := hQR hz
  set y := levelMap (F ∘ R) 1 z with hydef
  have hy' : y ∈ E'.lvlSet R'.retract 1 := h.image_mem hx
  have hMeq : M = rangeS (scDeriv R.U R z) :=
    SetLike.coe_injective (hM.trans (tangentSpace_eq_coe_submodule R hx))
  subst hMeq
  have himg : levelMap (G ∘ R') 1 y = z := h.image_image hx
  set A₀ := scDeriv R.U (F ∘ R) z with hA₀
  set A₀' := scDeriv R'.U (G ∘ R') y with hA₀'
  have hTA : ∀ v ∈ rangeS (scDeriv R.U R z), A₀ v ∈ rangeS (scDeriv R'.U R' y) := by
    intro v hv
    obtain ⟨u, hu⟩ := h.deriv_mem_range hx (v := v) (by obtain ⟨w, hw⟩ := hv; exact ⟨w, hw⟩)
    exact ⟨u, hu⟩
  have hTA' : ∀ w ∈ rangeS (scDeriv R'.U R' y), A₀' w ∈ rangeS (scDeriv R.U R z) := by
    intro w hw
    have := h.symm.deriv_mem_range hy' (v := w) (by obtain ⟨u, hu⟩ := hw; exact ⟨u, hu⟩)
    rw [himg] at this
    obtain ⟨u, hu⟩ := this
    exact ⟨u, hu⟩
  have hinv1 : ∀ v ∈ rangeS (scDeriv R.U R z), A₀' (A₀ v) = v := by
    rintro _ ⟨w, rfl⟩
    rw [hA₀', hA₀, h.deriv_inv_deriv hx]
    exact congrArg (fun L : E 0 →L[ℝ] E 0 => L w) (R.scDeriv_comp_self hx)
  have hinv2 : ∀ w ∈ rangeS (scDeriv R'.U R' y), A₀ (A₀' w) = w := by
    rintro _ ⟨u, rfl⟩
    rw [hA₀', hA₀, h.deriv_deriv_inv hx]
    exact congrArg (fun L : E' 0 →L[ℝ] E' 0 => L u) (R'.scDeriv_comp_self hy')
  have hNM : N ≤ rangeS (scDeriv R.U R z) := by
    intro v hv
    have hv' : v ∈ tangentSpace E C Q z := by rw [← hN]; exact hv
    have := tangentSpace_subset_of_subset R hQ hQR hz hv'
    rwa [← hM] at this
  have hBle : B ≤ rangeS (scDeriv R.U R z) := fun v hv => (hBM hv).1
  -- `w ∈ A(S) ↔ w ∈ T_yO' ∧ A'w ∈ S` for `S ⊆ T_zO`
  have hmapiff : ∀ S : Submodule ℝ (E 0), S ≤ rangeS (scDeriv R.U R z) → ∀ w : E' 0,
      w ∈ S.map (A₀ : E 0 →ₗ[ℝ] E' 0) ↔ w ∈ rangeS (scDeriv R'.U R' y) ∧ A₀' w ∈ S := by
    intro S hS w
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨hTA v (hS hv), ?_⟩
      change A₀' (A₀ v) ∈ S
      rw [hinv1 v (hS hv)]; exact hv
    · rintro ⟨hw, hw'⟩
      exact ⟨A₀' w, hw', hinv2 w hw⟩
  -- the sc-operators `A`, `A'` (`z`, `y` smooth)
  have hzU : z ∈ E.lvlSet R.U 1 := R.lvlSet_retract_subset 1 hx
  have hyU : y ∈ E'.lvlSet R'.U 1 := R'.lvlSet_retract_subset 1 hy'
  have hys : y ∈ E'.smoothLvl 1 := by
    change E'.toBase 1 y ∈ (E'.smooth : Set (E' 0))
    rw [h.toBase_image hx]
    have := hFs.isSc1.isSc0.mem_smooth hzU hzs
    rwa [Function.comp_apply, R.apply_eq_self_of_mem_retract hx] at this
  have hAop : IsScOperator A₀ := hFs.isSc1.isSc1With_scDeriv.scOperator_deriv hzU hzs
  have hA'op : IsScOperator A₀' := hGs.isSc1.isSc1With_scDeriv.scOperator_deriv hyU hys
  -- level maps: `A'_m w` lies over `A'(w)`, and `A_m (A'_m w) = w` over `T_yO'`
  have hlev : ∀ m (w : E' m), E'.toBase m w ∈ rangeS (scDeriv R'.U R' y) →
      ∃ x : E m, E.toBase m x = A₀' (E'.toBase m w) ∧
        ∀ Am : E m →L[ℝ] E' m, (∀ u, E'.toBase m (Am u) = A₀ (E.toBase m u)) → Am x = w := by
    intro m w hw
    obtain ⟨Am', hAm'⟩ := hA'op m
    refine ⟨Am' w, hAm' w, fun Am hAm => E'.toBase_injective m ?_⟩
    rw [hAm, hAm', hinv2 _ hw]
  refine ⟨N.map (A₀ : E 0 →ₗ[ℝ] E' 0), rangeS (scDeriv R'.U R' y),
    B.map (A₀ : E 0 →ₗ[ℝ] E' 0), ?_, (tangentSpace_eq_coe_submodule R' hy').symm, ?_, ?_, ?_⟩
  · -- `A(T_zQ) = T_yQ'`
    have hzQ' : y ∈ E'.lvlSet Q' 1 := by
      rw [ScBanach.mem_lvlSet, h.toBase_image hx]; exact hFQ hz
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hvQ : v ∈ tangentSpace E C Q z := by rw [← hN]; exact hv
      exact scDeriv_mem_tangentSpace_of_subset R hFs hQ hQ' hQR hFQ hz hvQ
    · intro hw
      have hwM : w ∈ rangeS (scDeriv R'.U R' y) := by
        have := tangentSpace_subset_of_subset R' hQ' hQ'R hzQ' hw
        rw [tangentSpace_eq_coe_submodule R' hy'] at this; exact this
      have h1 : A₀' w ∈ tangentSpace E C Q z := by
        have := scDeriv_mem_tangentSpace_of_subset R' hGs hQ' hQ hQ'R hGQ hzQ' hw
        rwa [himg] at this
      rw [SetLike.mem_coe, hmapiff N hNM]
      exact ⟨hwM, by rw [← SetLike.mem_coe, hN]; exact h1⟩
  · -- `A(B) ⊆ T^R_y O'`
    have hred := proposition_2_30_reduced h hx T hT T' hT'
    have : B.map (A₀ : E 0 →ₗ[ℝ] E' 0) ≤ reducedTangentSpaceWith R' T' y :=
      (Submodule.map_mono hBM).trans hred.le
    exact this
  · -- `A(B)` is an sc-subspace
    refine ⟨?_, fun m w hw => ?_⟩
    · have heq : (B.map (A₀ : E 0 →ₗ[ℝ] E' 0) : Set (E' 0)) =
          {w | scDeriv R'.U R' y w = w} ∩ A₀' ⁻¹' (B : Set (E 0)) := by
        ext w
        rw [SetLike.mem_coe, hmapiff B hBle]
        constructor
        · rintro ⟨⟨u, hu⟩, hw'⟩
          refine ⟨?_, hw'⟩
          change scDeriv R'.U R' y w = w
          rw [← hu]
          exact congrArg (fun L : E' 0 →L[ℝ] E' 0 => L u) (R'.scDeriv_comp_self hy')
        · rintro ⟨hw, hw'⟩
          exact ⟨⟨w, hw⟩, hw'⟩
      rw [heq]
      exact (isClosed_eq (scDeriv R'.U R' y).continuous continuous_id).inter
        (hB.1.preimage A₀'.continuous)
    · rw [SetLike.mem_coe, ScBanach.mem_levelSub, hmapiff B hBle] at hw
      obtain ⟨x, hx0, hxw⟩ := hlev m w hw.1
      obtain ⟨Am, hAm⟩ := hAop m
      have hxB : x ∈ E.levelSub B m := by rw [ScBanach.mem_levelSub, hx0]; exact hw.2
      have hcl := hB.2 m hxB
      have h1 : Am x ∈ closure (Am '' (E.levelSub B m ∩ E.smoothLvl m)) :=
        image_closure_subset_closure_image Am.continuous ⟨x, hcl, rfl⟩
      rw [hxw Am hAm] at h1
      refine closure_mono ?_ h1
      rintro _ ⟨u, ⟨huB, hus⟩, rfl⟩
      refine ⟨?_, mem_smoothLvl_of_isScOperator hAop hus (hAm u)⟩
      rw [SetLike.mem_coe, ScBanach.mem_levelSub, hAm]
      exact Submodule.mem_map_of_mem huB
  · -- the levelwise splitting
    intro m
    obtain ⟨Am, hAm⟩ := hAop m
    have hmapN : ∀ u ∈ E.levelSub N m, Am u ∈ E'.levelSub (N.map (A₀ : E 0 →ₗ[ℝ] E' 0)) m :=
      fun u hu => by rw [ScBanach.mem_levelSub, hAm]; exact Submodule.mem_map_of_mem hu
    have hmapB : ∀ u ∈ E.levelSub B m, Am u ∈ E'.levelSub (B.map (A₀ : E 0 →ₗ[ℝ] E' 0)) m :=
      fun u hu => by rw [ScBanach.mem_levelSub, hAm]; exact Submodule.mem_map_of_mem hu
    refine ⟨?_, le_antisymm (sup_le ?_ ?_) ?_⟩
    · rw [Submodule.disjoint_def]
      intro w hwN hwB
      rw [ScBanach.mem_levelSub, hmapiff N hNM] at hwN
      rw [ScBanach.mem_levelSub, hmapiff B hBle] at hwB
      obtain ⟨x, hx0, hxw⟩ := hlev m w hwN.1
      have hxN : x ∈ E.levelSub N m := by rw [ScBanach.mem_levelSub, hx0]; exact hwN.2
      have hxB : x ∈ E.levelSub B m := by rw [ScBanach.mem_levelSub, hx0]; exact hwB.2
      have hx00 : x = 0 := Submodule.disjoint_def.1 (hsplit m).1 x hxN hxB
      rw [← hxw Am hAm, hx00, map_zero]
    · exact Submodule.comap_mono fun w hw => ((hmapiff N hNM w).1 hw).1
    · exact Submodule.comap_mono fun w hw => ((hmapiff B hBle w).1 hw).1
    · intro w hw
      obtain ⟨x, hx0, hxw⟩ := hlev m w hw
      have hxM : x ∈ E.levelSub (rangeS (scDeriv R.U R z)) m := by
        rw [ScBanach.mem_levelSub, hx0]; exact hTA' _ hw
      rw [← (hsplit m).2] at hxM
      obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 hxM
      rw [← hxw Am hAm, ← huv, map_add]
      exact Submodule.add_mem_sup (hmapN u hu) (hmapB v hv)

end GoodPositionRetract

/-! ### Good position to the whole space -/

section GoodPositionUniv

variable {E : ScBanach}

/-- Every subspace is in good position to the whole space (any algebraic complement is good). -/
theorem isInGoodPosition_univ (N : Submodule ℝ (E 0)) : IsInGoodPosition E univ N := by
  obtain ⟨Y, hY⟩ := Submodule.exists_isCompl N
  refine ⟨⟨0, ?_⟩, Y, hY, 1, one_pos, fun _ _ _ _ _ => by simp⟩
  rw [preimage_univ, interior_univ]; exact mem_univ _

variable {n : ℕ} {Wq : ScBanach}

/-- At a point `e ∈ C` with `d_C(e) = 0` the partial quadrant `C_e` is the whole space. -/
theorem partialQuadrantAtWith_eq_univ_of_degIndex_eq_zero {C : Set (E 0)}
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod Wq)) (hT : C = T 0 ⁻¹' quadrant n Wq 0)
    {e : E 0} (he : e ∈ C) (h0 : degIndex E C e = 0) : partialQuadrantAtWith T e = univ := by
  rw [degIndex_eq T hT he] at h0
  refine eq_univ_of_forall fun v i hi => ?_
  exfalso
  have : (Finset.univ.filter fun j => (T 0 e).1 j = 0).card = 0 := h0
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at this
  exact this (Finset.mem_univ i) hi

end GoodPositionUniv

/-! ### Tangent spaces along the graph of Proposition 4.9 -/

section GraphTangent

variable {E : ScBanach} {C Q : Set (E 0)} {N : Submodule ℝ (E 0)} [FiniteDimensional ℝ N]
  {V : Set N}

/-- On a subset of a finite-dimensional space with the constant sc-structure, the sc-derivative is
the classical derivative within the set. -/
theorem hasFDerivWithinAt_scDeriv_const {Γ : N → E 0}
    (hΓ : IsSc1 (E := ScBanach.const N) (F := E) V Γ) {v : N} (hv : v ∈ V) :
    HasFDerivWithinAt Γ (scDeriv (E := ScBanach.const N) V Γ v) V v := by
  have hv' : (v : (ScBanach.const N) 1) ∈ (ScBanach.const N).lvlSet V 1 := by
    rw [ScBanach.lvlSet_const]; exact hv
  have h1 := hΓ.isSc1With_scDeriv.hasFDerivWithinAt _ hv'
  rw [ScBanach.lvlSet_const] at h1
  have e1 : (Γ ∘ ⇑((ScBanach.const N).toBase 1)) = Γ :=
    funext fun x => congrArg Γ (ScBanach.const_toBase N 1 x)
  have e2 : (scDeriv (E := ScBanach.const N) V Γ v).comp ((ScBanach.const N).toBase 1) =
      scDeriv (E := ScBanach.const N) V Γ v := by
    ext x; exact congrArg _ (ScBanach.const_toBase N 1 x)
  rw [e1, e2] at h1
  exact h1

/-- **The tangent spaces of a retract parametrized by a finite-dimensional quadrant** (the graph
`Γ : V → Q` of Proposition 4.9, with inverse the projection `p`): at `v ∈ V` and the level-`1`
point `y` over `Γ(v)`, `T_yQ = DΓ(v)N` and `p ∘ DΓ(v) = 1` (the tangent maps of the
sc-diffeomorphism `Γ : (V, N ∩ C, N) → (Q, C, E)` and of its inverse, `IsDiffeoGerm`). -/
theorem tangentSpace_eq_range_graph (hQ : IsScRetract E C Q)
    (hV : IsRelOpenInQuadrant (ScBanach.const N) (Subtype.val ⁻¹' C) V) {Γ : N → E 0}
    {p : E 0 →L[ℝ] N}
    (hpmap : IsScSmoothRetractMap E C Q (ScBanach.const N) (Subtype.val ⁻¹' C) V p)
    (hΓmap : IsScSmoothRetractMap (ScBanach.const N) (Subtype.val ⁻¹' C) V E C Q Γ)
    (hΓp : ∀ u ∈ Q, Γ (p u) = u) (hpΓ : ∀ v ∈ V, p (Γ v) = v) {v : N} (hv : v ∈ V) {y : E 1}
    (hy : E.toBase 1 y = Γ v) :
    HasFDerivWithinAt Γ (scDeriv (E := ScBanach.const N) V Γ v) V v ∧
      tangentSpace E C Q y = range (scDeriv (E := ScBanach.const N) V Γ v) ∧
      ∀ n, p (scDeriv (E := ScBanach.const N) V Γ v n) = n := by
  set R₁ := ScRetraction.id hV with hR₁def
  have hR₁ : R₁.retract = V := image_id V
  obtain ⟨R₂, hR₂⟩ := hQ
  have hΓsm : IsScSmooth (E := ScBanach.const N) (F := E) V Γ := hΓmap.comp_isScSmooth R₁ hR₁
  have hfd := hasFDerivWithinAt_scDeriv_const hΓsm.isSc1 hv
  have hdiff : R₁.IsDiffeoGerm R₂ Γ p :=
    IsScSmoothRetractMap.isDiffeoGerm (by rw [hR₁, hR₂]; exact hΓmap)
      (by rw [hR₁, hR₂]; exact hpmap) (by rw [hR₁]; exact hpΓ) (by rw [hR₂]; exact hΓp)
  have hx : (v : (ScBanach.const N) 1) ∈ (ScBanach.const N).lvlSet R₁.retract 1 := by
    rw [hR₁, ScBanach.lvlSet_const]; exact hv
  have hxU : (v : (ScBanach.const N) 1) ∈ (ScBanach.const N).lvlSet V 1 := by
    rw [ScBanach.lvlSet_const]; exact hv
  have hlev : levelMap (Γ ∘ R₁) 1 (v : (ScBanach.const N) 1) = y := by
    apply levelMap_eq_of_toBase_eq
    rw [hy]
    change Γ v = Γ ((ScBanach.const N).toBase 1 v)
    rw [ScBanach.const_toBase]
  have hDid : ∀ w, scDeriv R₁.U R₁ (v : (ScBanach.const N) 1) w = w := fun w => by
    have := IsSc1.scDeriv_eqOn (isSc1With_id (E := ScBanach.const N) V)
      (hV.isScDomain.uniqueDiffWithinAt 1) hxU
    exact congrArg (fun L : N →L[ℝ] N => L w) this
  have hy2 : y ∈ E.lvlSet R₂.retract 1 := by
    rw [ScBanach.mem_lvlSet, hR₂, hy]; exact hΓmap.mapsTo hv
  refine ⟨hfd, ?_, fun n => ?_⟩
  · rw [← hR₂, tangentSpace_eq_range R₂ hy2]
    ext w
    constructor
    · rintro ⟨u, rfl⟩
      have := hdiff.deriv_deriv_inv hx u
      rw [hlev] at this
      exact ⟨_, this⟩
    · rintro ⟨u, rfl⟩
      have := hdiff.deriv_mem_range hx (v := u) ⟨u, hDid u⟩
      rwa [hlev] at this
  · -- `p ∘ Γ = 1` on `V`, differentiated within `V`
    have huniq : UniqueDiffWithinAt ℝ V v := by
      have := hV.isScDomain.uniqueDiffWithinAt 0 v (by rw [ScBanach.lvlSet_const]; exact hv)
      rwa [ScBanach.lvlSet_const] at this
    have h1 : HasFDerivWithinAt (fun x => p (Γ x))
        (p.comp (scDeriv (E := ScBanach.const N) V Γ v)) V v :=
      p.hasFDerivAt.comp_hasFDerivWithinAt v hfd
    have h2 : HasFDerivWithinAt (fun x => p (Γ x)) (ContinuousLinearMap.id ℝ N) V v :=
      (hasFDerivWithinAt_id v V).congr (fun x hx => hpΓ x hx) (hpΓ v hv)
    exact congrArg (fun L : N →L[ℝ] N => L n) (huniq.eq h1 h2)

end GraphTangent

/-! ### Lemma 4.19 -/

section Lemma419

variable {E : ScBanach} {C : Set (E 0)} {n : ℕ} {Wq : ScBanach}

/-- The good complement of Lemma 4.19: if `π` is a bounded idempotent with
`Z = (1 − π)E ⊆ E₀` (the minimal subspace at the corner `0`; Proposition 2.35 for a tame
retraction), and `Y ⊆ πE` is a good complement of `N` inside `πE` (constant `ε`), then `Y ⊕ Z` is a
good complement of `N` in `E`, with the constant `ε/(‖π‖ + 1)` (the text: the norm
`|(y, z)| = |y| + |z|` on `Y ⊕ Z`).  The argument is that of
`IsInGoodPositionIn.isInGoodPosition`, with the complement kept explicit. -/
theorem isGoodComplement_sup_range (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hC : C = T 0 ⁻¹' quadrant n Wq 0) (π : E 0 →L[ℝ] E 0) (hπ : ∀ x, π (π x) = π x)
    (hK : LinearMap.range (ContinuousLinearMap.id ℝ (E 0) - π : E 0 →ₗ[ℝ] E 0) ≤
      minimalSubspaceWith T 0)
    {N Y : Submodule ℝ (E 0)} (hNT : N ≤ rangeS π) (hYT : Y ≤ rangeS π) (hNY : N ⊓ Y = ⊥)
    (hNYT : N ⊔ Y = rangeS π) {ε : ℝ} (hε : 0 < ε)
    (hgood : ∀ x ∈ N, ∀ p ∈ Y, ‖p‖ ≤ ε * ‖x‖ → (x ∈ C ↔ x + p ∈ C)) :
    IsGoodComplement E C N
      (Y ⊔ LinearMap.range (ContinuousLinearMap.id ℝ (E 0) - π : E 0 →ₗ[ℝ] E 0)) := by
  set K : Submodule ℝ (E 0) := LinearMap.range (ContinuousLinearMap.id ℝ (E 0) - π : E 0 →ₗ[ℝ] E 0)
    with hKdef
  have hπT : ∀ x ∈ rangeS π, π x = x := by
    rintro _ ⟨y, rfl⟩
    exact hπ y
  have hπK : ∀ k ∈ K, π k = 0 := by
    rintro _ ⟨y, rfl⟩
    change π (y - π y) = 0
    rw [map_sub, hπ, sub_self]
  have hKcoord : ∀ k ∈ K, ∀ i, (T 0 k).1 i = 0 := fun k hk i =>
    (mem_minimalSubspaceWith T).1 (hK hk) i (by rw [map_zero]; rfl)
  have hmemC : ∀ (x : E 0), ∀ k ∈ K, (x + k ∈ C ↔ x ∈ C) := by
    intro x k hk
    rw [hC, mem_preimage, mem_preimage]
    change (∀ i, 0 ≤ (T 0 (x + k)).1 i) ↔ ∀ i, 0 ≤ (T 0 x).1 i
    refine forall_congr' fun i => ?_
    rw [map_add, Prod.fst_add, Pi.add_apply, hKcoord k hk i, add_zero]
  refine ⟨IsCompl.of_eq ?_ ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro x ⟨hxN, hxPK⟩
    obtain ⟨p, hp, k, hk, rfl⟩ := Submodule.mem_sup.1 hxPK
    have h1 : π (p + k) = p + k := hπT _ (hNT hxN)
    rw [map_add, hπT p (hYT hp), hπK k hk, add_zero] at h1
    have hk0 : k = 0 := by
      have := congrArg (fun z => z - p) h1
      simpa using this.symm
    rw [hk0, add_zero] at hxN ⊢
    have : p ∈ N ⊓ Y := ⟨hxN, hp⟩
    rwa [hNY] at this
  · rw [eq_top_iff]
    intro x _
    rw [← sup_assoc, hNYT]
    exact Submodule.mem_sup.2 ⟨π x, ⟨x, rfl⟩, x - π x, ⟨x, rfl⟩, by abel⟩
  · refine ⟨ε / (‖π‖ + 1), by positivity, ?_⟩
    intro x hx q hq hle
    obtain ⟨p, hp, k, hk, rfl⟩ := Submodule.mem_sup.1 hq
    have hpq : π (p + k) = p := by rw [map_add, hπT p (hYT hp), hπK k hk, add_zero]
    have hpn : ‖p‖ ≤ ε * ‖x‖ := by
      calc ‖p‖ = ‖π (p + k)‖ := by rw [hpq]
        _ ≤ ‖π‖ * ‖p + k‖ := π.le_opNorm _
        _ ≤ ‖π‖ * (ε / (‖π‖ + 1) * ‖x‖) := by gcongr
        _ = ε * ‖x‖ * (‖π‖ / (‖π‖ + 1)) := by ring
        _ ≤ ε * ‖x‖ * 1 := by
          gcongr
          rw [div_le_one (by positivity)]; linarith
        _ = ε * ‖x‖ := mul_one _
    rw [← add_assoc, hmemC (x + p) k hk]
    exact hgood x hx p hp hpn

/-- **Lemma 4.19**: in a tame chart centred at `a` (`ϕ(a) = 0`, so that `C_0 = C`), with
`T₀O = πE` for the projection `π = Dr(0)` and `Z = (1 − π)E` the sc-complement of `T₀O` contained in
`E₀ ⊆ C` (Proposition 2.35), if `N = Tϕ(a)(T_aA)` is in good position to `C₀ = T₀O ∩ C` inside
`T₀O`, then **`N` is in good position to `C` in `E`, and for every good complement `Y` of `N` in
`T₀O` the sum `Y ⊕ Z` is a good complement of `N` in `E`**.  (The good position statement is
`IsInGoodPositionIn.isInGoodPosition` of `GoodPositionGerm.lean`, the transport lemma of
Theorem 3.54; the explicit complement is `isGoodComplement_sup_range`.) -/
theorem lemma_4_19 (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hC : C = T 0 ⁻¹' quadrant n Wq 0) (π : E 0 →L[ℝ] E 0) (hπ : ∀ x, π (π x) = π x)
    (hK : LinearMap.range (ContinuousLinearMap.id ℝ (E 0) - π : E 0 →ₗ[ℝ] E 0) ≤
      minimalSubspaceWith T 0)
    {N : Submodule ℝ (E 0)} (hN : IsInGoodPositionIn E (rangeS π) C N) :
    IsInGoodPosition E C N ∧
      ∀ Y : Submodule ℝ (E 0), Y ≤ rangeS π → N ⊓ Y = ⊥ → N ⊔ Y = rangeS π →
        (∃ ε > 0, ∀ x ∈ N, ∀ p ∈ Y, ‖p‖ ≤ ε * ‖x‖ → (x ∈ C ↔ x + p ∈ C)) →
        IsGoodComplement E C N
          (Y ⊔ LinearMap.range (ContinuousLinearMap.id ℝ (E 0) - π : E 0 →ₗ[ℝ] E 0)) :=
  ⟨hN.isInGoodPosition T hC π hπ hK, fun _ hYT hNY hNYT ⟨_, hε, hgood⟩ =>
    isGoodComplement_sup_range T hC π hπ hK hN.le hYT hNY hNYT hε hgood⟩

end Lemma419

/-! ### Definition 4.13: smooth finite-dimensional submanifolds -/

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

/-- The data of Definition 4.13 at a point: an open `V ⊆ X` and an **sc⁺-retraction** `s : V → V`
(Definition 4.4 on an open subset, `IsScPlusRetractionOn`) with `s(V) = A ∩ V`. -/
structure SubmanifoldData (A : Set X) where
  /-- The open set `V`. -/
  V : Set X
  /-- The sc⁺-retraction `s`. -/
  s : X → X
  isOpen : IsOpen V
  isScPlusRetractionOn : P.IsScPlusRetractionOn s V
  image : s '' V = A ∩ V

/-- **Definition 4.13**: `A ⊆ X` is a **smooth finite-dimensional submanifold** of the M-polyfold
`X` if every `a ∈ A` has an open neighbourhood `V ⊆ X` and an sc⁺-retraction `s : V → V`
(Definition 4.4: `s` sc-smooth, `s ∘ s = s` on `V`, `s(V) ⊆ X₁` and `1₀¹ ∘ s : V → X¹` sc-smooth)
with `s(V) = A ∩ V`. -/
def IsSmoothSubmanifold (A : Set X) : Prop :=
  ∀ a ∈ A, ∃ V : Set X, IsOpen V ∧ a ∈ V ∧ ∃ s : X → X, P.IsScPlusRetractionOn s V ∧ s '' V = A ∩ V

variable {P}

/-- Definition 4.13 with the data as a structure. -/
theorem isSmoothSubmanifold_iff {A : Set X} :
    P.IsSmoothSubmanifold A ↔ ∀ a ∈ A, ∃ d : P.SubmanifoldData A, a ∈ d.V := by
  constructor
  · intro h a ha
    obtain ⟨V, hV, haV, s, hs, himg⟩ := h a ha
    exact ⟨⟨V, s, hV, hs, himg⟩, haV⟩
  · intro h a ha
    obtain ⟨d, had⟩ := h a ha
    exact ⟨d.V, d.isOpen, had, d.s, d.isScPlusRetractionOn, d.image⟩

namespace SubmanifoldData

variable {A : Set X} (d : P.SubmanifoldData A)

/-- An sc⁺-retraction is in particular an sc-smooth retraction: the data of Definition 2.20. -/
def toSubData : P.SubData A where
  V := d.V
  r := d.s
  isOpen := d.isOpen
  mapsTo := d.isScPlusRetractionOn.mapsTo
  isScSmoothOn := d.isScPlusRetractionOn.isScSmoothOn
  idem := d.isScPlusRetractionOn.idem
  image := d.image

@[simp] lemma toSubData_V : d.toSubData.V = d.V := rfl

@[simp] lemma toSubData_r : d.toSubData.r = d.s := rfl

lemma apply_eq_self {x : X} (hx : x ∈ A ∩ d.V) : d.s x = x := d.toSubData.apply_eq_self hx

/-- The points of `A ∩ V` lie on level `1` (`a = s(a) ∈ X₁`). -/
lemma mem_levelSet_one {a : X} (ha : a ∈ A) (haV : a ∈ d.V) : a ∈ P.levelSet 1 := by
  rw [← d.apply_eq_self ⟨ha, haV⟩]
  exact d.isScPlusRetractionOn.mem_levelSet a haV

variable {φ : MChart X} (hφ : P.IsChart φ)
include hφ

/-- **The sc⁺-property of `s` in a chart**: for a chart `φ` of `X` and the open set
`W = V ∩ dom φ ∩ s⁻¹(V ∩ dom φ)` of the proof of Proposition 2.21, the lift
`1₀¹ ∘ (φ ∘ s ∘ φ⁻¹) : φ(W) → E¹` is sc-smooth from `(φ(W), C, E)` to `(O₁, C₁, E¹)` (the
condition "`s : V → V¹` sc-smooth" of Definition 4.4, read in the charts `φ` of `X` and
`(V₁, φ, (O₁, C₁, E¹))` of `X¹`). -/
theorem isScSmoothRetractMap_lift (x₀ : P.Level 1) :
    IsScSmoothRetractMap φ.model.E φ.model.C (φ '' d.toSubData.shrink φ) φ.model.E.shift
      (φ.model.E.lvlSet φ.model.C 1) (φ.model.E.lvlSet φ.model.O 1)
      (φ.model.E.liftOne ∘ (φ ∘ d.s ∘ φ.symm)) := by
  have hW := d.toSubData.isOpen_shrink φ
  have hsub : d.toSubData.shrink φ ⊆ d.V ∩ φ.source := fun x hx => ⟨hx.1.1, hx.1.2⟩
  have hmaps : MapsTo (P.toLevelOne x₀ ∘ d.s) (d.toSubData.shrink φ)
      (levelChart hφ x₀).source := fun x hx => by
    change P.levelVal 1 (P.toLevelOne x₀ (d.s x)) ∈ φ.source
    rw [levelVal_toLevelOne x₀ (d.isScPlusRetractionOn.mem_levelSet x hx.1.1)]
    exact (d.toSubData.mapsTo_shrink φ hx).1.2
  have h := (d.isScPlusRetractionOn.isScSmoothOn_one x₀).smooth φ (levelChart hφ x₀) hφ
    (P.shift_isChart hφ x₀) _ hW hsub hmaps
  refine h.congr ?_
  rintro _ ⟨x, hx, rfl⟩
  simp only [Function.comp_apply, φ.symm_apply_apply (d.toSubData.shrink_subset_source φ hx)]
  exact levelChart_toLevelOne hφ x₀ x₀ (d.isScPlusRetractionOn.mem_levelSet x hx.1.1)

/-- **The chart retraction `t = φ ∘ s ∘ φ⁻¹ ∘ r` of the proof of Theorem 4.18 is an
sc⁺-retraction**: for a chart `φ : V' → O` of `X` and an sc-smooth retraction `r` onto `O`, with
`W` as in `isScSmoothRetractMap_lift` and `φ(W) = O ∩ G` (`G` open), the retraction
`t = (φ ∘ s ∘ φ⁻¹) ∘ r` on `U ∩ r⁻¹(G)` (`ScRetraction.compRetraction` of the restricted `r`) is an
sc⁺-retraction onto `φ(W ∩ A)`, agreeing with `φ ∘ s ∘ φ⁻¹ ∘ r` on its domain. -/
theorem exists_chartRetraction (x₀ : P.Level 1) (R : ScRetraction φ.model.E φ.model.C)
    (hR : R.retract = φ.model.O) :
    ∃ t : ScRetraction φ.model.E φ.model.C, t.retract = φ '' (d.toSubData.shrink φ ∩ A) ∧
      t.IsScPlus ∧ t.U ⊆ R.U ∧ (∀ u ∈ t.U, t u = (φ ∘ d.s ∘ φ.symm) (R u)) ∧
      ∃ G : Set (φ.model.E 0), IsOpen G ∧ t.U = R.U ∩ R ⁻¹' G ∧
        φ '' d.toSubData.shrink φ = φ.model.O ∩ G := by
  obtain ⟨G, hG, hWG⟩ := φ.exists_isOpen_image_eq (d.toSubData.shrink_subset_source φ)
    (d.toSubData.isOpen_shrink φ)
  set Rw := R.restrict hG with hRwdef
  have hRw : Rw.retract = φ '' d.toSubData.shrink φ := by
    rw [R.restrict_retract, hR, hWG]
  have hρ := d.toSubData.rho_isScSmooth φ hφ
  rw [← hRw] at hρ
  have hρρ : ∀ x ∈ Rw.retract, (φ ∘ d.toSubData.r ∘ φ.symm) ((φ ∘ d.toSubData.r ∘ φ.symm) x) =
      (φ ∘ d.toSubData.r ∘ φ.symm) x := by
    rw [hRw]; exact fun x hx => d.toSubData.rho_idem φ hx
  refine ⟨Rw.compRetraction hρ hρρ, ?_, ?_, inter_subset_left, fun u _ => rfl, G, hG, rfl, hWG⟩
  · rw [Rw.compRetraction_retract, hRw, d.toSubData.rho_image φ]
  · have hlift := d.isScSmoothRetractMap_lift hφ x₀
    rw [← hRw] at hlift
    refine ⟨fun u hu => ?_, hlift.comp_isScSmooth Rw rfl⟩
    have hu' : Rw u ∈ φ '' d.toSubData.shrink φ := hRw ▸ Rw.apply_mem_retract hu
    obtain ⟨x, hx, hxu⟩ := hu'
    change φ (d.s (φ.symm (Rw u))) ∈ range _
    rw [← hxu, φ.symm_apply_apply (d.toSubData.shrink_subset_source φ hx)]
    have hsx : d.s x ∈ P.levelSet 1 := d.isScPlusRetractionOn.mem_levelSet x hx.1.1
    exact (P.mem_levelSet_iff hφ (d.toSubData.shrink_subset_source φ
      (d.toSubData.mapsTo_shrink φ hx))).1 hsx

/-- **The model of the chart of `A` induced by `φ` is an sc⁺-retract** (Definition 4.6): the
retract `φ(W ∩ A)` of the sub-M-polyfold chart (`subChart`) is the image of the sc⁺-retraction
`t = φ ∘ s ∘ φ⁻¹ ∘ r`. -/
theorem isScPlusRetract_image (x₀ : P.Level 1) :
    IsScPlusRetract φ.model.E φ.model.C (φ '' (d.toSubData.shrink φ ∩ A)) := by
  obtain ⟨R, hR⟩ := φ.model.isScRetract
  obtain ⟨t, ht, htp, -⟩ := d.exists_chartRetraction hφ x₀ R hR
  exact ⟨t, ht, htp⟩

/-- The image `φ(a)` of a point `a ∈ A ∩ V ∩ dom φ` is a smooth point (it lies in the retract of
the sc⁺-retraction `t`, Lemma 4.7 (i)). -/
theorem apply_mem_smooth {a : X} (ha : a ∈ A) (haV : a ∈ d.V) (haφ : a ∈ φ.source) :
    φ a ∈ φ.model.E.smooth := by
  obtain ⟨R, hR⟩ := φ.model.isScRetract
  obtain ⟨t, ht, htp, -⟩ := d.exists_chartRetraction hφ (P.levelMk 1 a (d.mem_levelSet_one ha haV))
    R hR
  exact lemma_4_7_i htp (ht ▸ ⟨a, ⟨d.toSubData.mem_shrink φ ha haV haφ, ha⟩, rfl⟩)

/-- **Remark 4.14, in a chart**: at `a ∈ A ∩ V ∩ dom φ`, with `z` the level-`1` point over `φ(a)`
and `W` the open set of the sub-M-polyfold chart: (i) `z` is smooth; (ii) **`T_aA = Ts(a)T_aX`**:
the tangent map of `ρ = φ ∘ s ∘ φ⁻¹ : φ(W) → φ(W)` at `z` maps `T_zO` (the chart form of `T_aX`)
onto the tangent space `T_z(φ(W ∩ A))` of the chart model of `A` (Proposition 2.21 (4) for `ρ`, and
`T_z(φ(W)) = T_zO`); (iii) `T_aA ⊆ T_aX`; (iv) **`T_aA` is finite-dimensional**: it is the range of
`Dt(z)` for the sc⁺-retraction `t = ρ ∘ r` (Lemma 4.7 (ii): `Dt(z)` is an sc⁺-operator, hence
compact, and a projection). -/
theorem remark_4_14 {a : X} (ha : a ∈ A) (haV : a ∈ d.V) (haφ : a ∈ φ.source)
    {z : φ.model.E 1} (hz : φ.model.E.toBase 1 z = φ a) :
    z ∈ φ.model.E.smoothLvl 1 ∧
      (fun h => (retractTangentMap φ.model.E φ.model.C (φ '' d.toSubData.shrink φ)
          (φ ∘ d.s ∘ φ.symm) ((z, h) : φ.model.E.tangent 0)).2) ''
          tangentSpace φ.model.E φ.model.C φ.model.O z =
        tangentSpace φ.model.E φ.model.C (φ '' (d.toSubData.shrink φ ∩ A)) z ∧
      tangentSpace φ.model.E φ.model.C (φ '' (d.toSubData.shrink φ ∩ A)) z ⊆
        tangentSpace φ.model.E φ.model.C φ.model.O z ∧
      ∃ N : Submodule ℝ (φ.model.E 0), (N : Set (φ.model.E 0)) =
        tangentSpace φ.model.E φ.model.C (φ '' (d.toSubData.shrink φ ∩ A)) z ∧
        FiniteDimensional ℝ N := by
  have haW : a ∈ d.toSubData.shrink φ := d.toSubData.mem_shrink φ ha haV haφ
  obtain ⟨G, hG, hWG⟩ := φ.exists_isOpen_image_eq (d.toSubData.shrink_subset_source φ)
    (d.toSubData.isOpen_shrink φ)
  obtain ⟨R, hR⟩ := φ.model.isScRetract
  have hRw : (R.restrict hG).retract = φ '' d.toSubData.shrink φ := by
    rw [R.restrict_retract, hR, hWG]
  have hρ := d.toSubData.rho_isScSmooth φ hφ
  rw [← hRw] at hρ
  have hρρ : ∀ x ∈ (R.restrict hG).retract,
      (φ ∘ d.toSubData.r ∘ φ.symm) ((φ ∘ d.toSubData.r ∘ φ.symm) x) =
        (φ ∘ d.toSubData.r ∘ φ.symm) x := by
    rw [hRw]; exact fun x hx => d.toSubData.rho_idem φ hx
  have hzQ : z ∈ φ.model.E.lvlSet ((φ ∘ d.toSubData.r ∘ φ.symm) '' (R.restrict hG).retract) 1 := by
    rw [ScBanach.mem_lvlSet, hRw, d.toSubData.rho_image, hz]; exact ⟨a, ⟨haW, ha⟩, rfl⟩
  have h214 := (proposition_2_21_4 (R.restrict hG) hρ hρρ hzQ).2
  rw [hRw, d.toSubData.rho_image] at h214
  have hzW : φ.model.E.toBase 1 z ∈ φ.model.O ∩ G := by rw [← hWG, hz]; exact ⟨a, haW, rfl⟩
  have hTW : tangentSpace φ.model.E φ.model.C (φ '' d.toSubData.shrink φ) z =
      tangentSpace φ.model.E φ.model.C φ.model.O z := by
    rw [hWG]; exact tangentSpace_inter_isOpen φ.model.isScRetract hG hzW
  obtain ⟨t, ht, htp, -⟩ := d.exists_chartRetraction hφ (P.levelMk 1 a (d.mem_levelSet_one ha haV))
    R hR
  have hzt : φ.model.E.toBase 1 z ∈ t.retract := by rw [ht, hz]; exact ⟨a, ⟨haW, ha⟩, rfl⟩
  have hzA : z ∈ φ.model.E.lvlSet (φ '' (d.toSubData.shrink φ ∩ A)) 1 := by
    rw [ScBanach.mem_lvlSet, hz]; exact ⟨a, ⟨haW, ha⟩, rfl⟩
  refine ⟨lemma_4_7_i htp hzt, ?_, ?_, ?_⟩
  · rw [← hTW]; exact h214
  · have := tangentSpace_subset_of_subset R (d.toSubData.isScRetract_image φ hφ)
      (hR ▸ φ.image_subset_model fun _ hx => d.toSubData.shrink_subset_source φ hx.1) hzA
    rwa [hR] at this
  · refine ⟨_, ?_, lemma_4_7_ii htp hzt⟩
    rw [← ht]
    exact (tangentSpace_eq_coe_submodule t hzt).symm

end SubmanifoldData

/-! ### Proposition 4.15 -/

namespace IsSmoothSubmanifold

variable {A : Set X} (hA : P.IsSmoothSubmanifold A)
include hA

/-- The data of Definition 4.13 at a point of `A`. -/
def data {a : X} (ha : a ∈ A) : P.SubmanifoldData A :=
  ((isSmoothSubmanifold_iff.1 hA) a ha).choose

lemma mem_data_V {a : X} (ha : a ∈ A) : a ∈ (hA.data ha).V :=
  ((isSmoothSubmanifold_iff.1 hA) a ha).choose_spec

/-- A smooth finite-dimensional submanifold is a sub-M-polyfold (Definition 2.20): an
sc⁺-retraction is an sc-smooth retraction. -/
theorem isSubMPolyfold : P.IsSubMPolyfold A := fun _ ha =>
  ⟨(hA.data ha).V, (hA.data ha).isOpen, hA.mem_data_V ha, (hA.data ha).s,
    (hA.data ha).isScPlusRetractionOn.mapsTo, (hA.data ha).isScPlusRetractionOn.isScSmoothOn,
    (hA.data ha).isScPlusRetractionOn.idem, (hA.data ha).image⟩

/-- The points of `A` lie on level `1`. -/
lemma mem_levelSet_one {a : X} (ha : a ∈ A) : a ∈ P.levelSet 1 :=
  (hA.data ha).mem_levelSet_one ha (hA.mem_data_V ha)

/-- **Proposition 4.15 (1)**, first half: **`A ⊆ X_∞`**.  *Proof* (the text's): in a chart `φ`
around `a`, `φ(a)` lies in the retract of the sc⁺-retraction `t = φ ∘ s ∘ φ⁻¹ ∘ r`, which consists
of smooth points (Lemma 4.7 (i)). -/
theorem subset_smoothSet : A ⊆ P.smoothSet := by
  intro a ha
  set d := hA.data ha
  obtain ⟨φ, hφ, haφ⟩ := P.exists_isChart_mem_source a
  obtain ⟨R, hR⟩ := φ.model.isScRetract
  obtain ⟨t, ht, htp, -⟩ :=
    d.exists_chartRetraction hφ (P.levelMk 1 a (hA.mem_levelSet_one ha)) R hR
  have hmem : φ a ∈ t.retract :=
    ht ▸ ⟨a, ⟨d.toSubData.mem_shrink φ ha (hA.mem_data_V ha) haφ, ha⟩, rfl⟩
  exact (mem_smoothSet_iff hφ haφ).2 (lemma_4_7_i htp hmem)

/-- The level sets of the induced M-polyfold structure are the traces of those of `X`. -/
theorem mem_levelSet_subPolyfold_iff [ParacompactSpace A] (a : A) (m : ℕ) :
    a ∈ (subPolyfold hA.isSubMPolyfold).levelSet m ↔ a.1 ∈ P.levelSet m := by
  obtain ⟨φ, hφ, haφ⟩ := P.exists_isChart_mem_source a.1
  set d := (hA.data a.2).toSubData
  have hsrc : a ∈ (subChart d hφ a).source :=
    d.mem_shrink φ a.2 (hA.mem_data_V a.2) haφ
  rw [(subPolyfold hA.isSubMPolyfold).mem_levelSet_iff
    (subPolyfold_isChart hA.isSubMPolyfold d hφ a) hsrc, P.mem_levelSet_iff hφ haφ]
  rfl

/-- **Proposition 4.15 (4)**: **`1₀¹ : A → A¹` is sc-smooth** for the induced M-polyfold structure,
and every point of `A` is smooth for it (`A = A_∞`).  *Proof*: every point of `A` lies in a chart of
the induced structure (`subChart`) whose model `φ(W ∩ A)` is an sc⁺-retract
(`SubmanifoldData.isScPlusRetract_image`), and Proposition 4.8 applies in each such chart
(`isScSmoothMap_toLevelOne_of_cover`).  The text: "the postulated sc⁺-retraction is the identity on
the retract `A`". -/
theorem proposition_4_15_4 [ParacompactSpace A] (x₀ : (subPolyfold hA.isSubMPolyfold).Level 1) :
    (∀ a, a ∈ (subPolyfold hA.isSubMPolyfold).smoothSet) ∧
      (subPolyfold hA.isSubMPolyfold).IsScSmoothMap (subPolyfold hA.isSubMPolyfold).shift
        ((subPolyfold hA.isSubMPolyfold).toLevelOne x₀) :=
  isScSmoothMap_toLevelOne_of_cover x₀ fun a => by
    obtain ⟨φ, hφ, haφ⟩ := P.exists_isChart_mem_source a.1
    set d := hA.data a.2
    exact ⟨subChart d.toSubData hφ a, subPolyfold_isChart hA.isSubMPolyfold d.toSubData hφ a,
      d.toSubData.mem_shrink φ a.2 (hA.mem_data_V a.2) haφ,
      d.isScPlusRetract_image hφ (P.levelMk 1 a.1 (hA.mem_levelSet_one a.2))⟩

/-- **Proposition 4.15 (1)**: `A ⊆ X_∞`, and `A` with the M-polyfold structure induced from `X`
(Proposition 2.21, `subPolyfold`) has all its points smooth; in particular `A` has a tangent space
at every point (Remark 4.14) and the degeneracy index `d_A` is defined on `A`. -/
theorem proposition_4_15_1 [ParacompactSpace A] :
    A ⊆ P.smoothSet ∧ ∀ a, a ∈ (subPolyfold hA.isSubMPolyfold).smoothSet := by
  refine ⟨hA.subset_smoothSet, fun a => ?_⟩
  have h1 : a ∈ (subPolyfold hA.isSubMPolyfold).levelSet 1 :=
    (hA.mem_levelSet_subPolyfold_iff a 1).2 (hA.mem_levelSet_one a.2)
  exact (hA.proposition_4_15_4 ((subPolyfold hA.isSubMPolyfold).levelMk 1 a h1)).1 a

/-- **Proposition 4.15 (2)**: **`A` is locally closed in `X`** (Mathlib's `IsLocallyClosed`: the
intersection of an open and a closed set; the text's definition at preprint lines 6463–6466 is
garbled, see the Findings).  *Proof* (the text's, with a filter in place of the sequence): every
`a ∈ A` has the open neighbourhood `V` of Definition 4.13, and a point `b ∈ V` in the closure of `A`
satisfies `s(b) = lim s(a_k) = lim a_k = b`, so `b ∈ s(V) ⊆ A`. -/
theorem proposition_4_15_2 : IsLocallyClosed A := by
  refine ((isLocallyClosed_tfae A).out 0 3).2 fun a ha => ?_
  set d := hA.data ha
  refine ⟨d.V, hA.mem_data_V ha, d.isOpen, fun b hb => ?_⟩
  obtain ⟨hbV, hbcl⟩ := hb
  have hcont : ContinuousOn d.s d.V := d.isScPlusRetractionOn.isScSmoothOn.continuousOn
  have hb' : b ∈ closure (A ∩ d.V) := by
    have := d.isOpen.inter_closure ⟨hbV, hbcl⟩
    rwa [inter_comm] at this
  have : (𝓝[A ∩ d.V] b).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hb'
  have h1 : Tendsto d.s (𝓝[A ∩ d.V] b) (𝓝 (d.s b)) :=
    (hcont.continuousAt (d.isOpen.mem_nhds hbV)).tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto d.s (𝓝[A ∩ d.V] b) (𝓝 b) := by
    refine Tendsto.congr' ?_ ((tendsto_id (x := 𝓝 b)).mono_left nhdsWithin_le_nhds)
    exact eventually_nhdsWithin_of_forall fun x hx => (d.apply_eq_self hx).symm
  have hsb : d.s b = b := tendsto_nhds_unique h1 h2
  have : b ∈ d.s '' d.V := ⟨b, hbV, hsb⟩
  rw [d.image] at this
  exact this.1

/-- **Proposition 4.15 (3)**: **`∂A = {a ∈ A | d_A(a) ≥ 1} ⊆ ∂X`**, by `d_A(a) ≤ d_X(a)`
(Lemma 2.26 for the sub-M-polyfold `A`; the text's argument in the case `d_X(a) = 0` is the proof
of that lemma). -/
theorem proposition_4_15_3 [ParacompactSpace A] :
    Subtype.val '' (subPolyfold hA.isSubMPolyfold).boundary ⊆ P.boundary := by
  rintro _ ⟨a, ha, rfl⟩
  exact le_trans ha (lemma_2_26 hA.isSubMPolyfold a)

end IsSmoothSubmanifold

/-! ### Definition 4.16: good position, and its chart independence -/

omit [T2Space X] [ParacompactSpace X] in
/-- `φ(H ∩ A) = φ(G ∩ A) ∩ K` when `H ⊆ G ⊆ dom φ` and `φ(H) = O ∩ K`. -/
lemma _root_.Polyfold.MChart.image_inter_eq_inter (ψ : MChart X) {G₀ H B : Set X}
    {K : Set (ψ.model.E 0)} (hG₀ : G₀ ⊆ ψ.source) (hHG : H ⊆ G₀)
    (hK : ψ '' H = ψ.model.O ∩ K) : ψ '' (H ∩ B) = ψ '' (G₀ ∩ B) ∩ K := by
  ext w
  constructor
  · rintro ⟨x, ⟨hxH, hxB⟩, rfl⟩
    have : ψ x ∈ ψ.model.O ∩ K := hK ▸ ⟨x, hxH, rfl⟩
    exact ⟨⟨x, ⟨hHG hxH, hxB⟩, rfl⟩, this.2⟩
  · rintro ⟨⟨x, ⟨hxG, hxB⟩, rfl⟩, hxK⟩
    have : ψ x ∈ ψ '' H := by rw [hK]; exact ⟨ψ.mapsTo_model x (hG₀ hxG), hxK⟩
    obtain ⟨y, hyH, hyx⟩ := this
    have : y = x := ψ.toPartialEquiv.injOn (hG₀ (hHG hyH)) (hG₀ hxG) hyx
    exact ⟨x, ⟨this ▸ hyH, hxB⟩, rfl⟩

/-- **The chart change for a property of sub-retracts** (Definitions 4.16 and 4.21): let `Φ` be a
property of `(E, C, O, Q, T, z)` (retracts `Q ⊆ O`, a presentation `T` of `C`, a level-`1` point
`z`) which depends only on the tangent spaces `T_zQ`, `T_zO` (`hcongr`) and is carried by germs of
sc-diffeomorphisms at smooth points (`htrans`).  Let `φ`, `φ'` be charts of `X`, `G ⊆ dom φ`,
`G' ⊆ dom φ'` open, `A ⊆ X` with `φ(G ∩ A)` and `φ'(G' ∩ A)` retracts, and `a ∈ A ∩ G ∩ G'` with
level-`1` points `z` (smooth), `z'` over `φ(a)`, `φ'(a)`.  If `Φ` holds for `φ(G ∩ A) ⊆ O` at `z`,
it holds for `φ'(G' ∩ A) ⊆ O'` at `z'`, for any presentations `T`, `T'` of the partial quadrants.
*Proof*: the transition `τ = φ' ∘ φ⁻¹` is a germ of sc-diffeomorphisms between the overlap
retracts, carrying `φ(H ∩ A)` onto `φ'(H ∩ A)` for `H = G ∩ G'`, and the tangent spaces at `z` are
those of the open pieces (`tangentSpace_inter_isOpen`). -/
theorem chart_change_of_transport
    (Φ : ∀ E : ScBanach, Set (E 0) → Set (E 0) → Set (E 0) → ∀ (n : ℕ) (Wq : ScBanach),
      ScIso E ((ScBanach.const (Fin n → ℝ)).prod Wq) → E 1 → Prop)
    (hcongr : ∀ (E : ScBanach) (C O Q O₂ Q₂ : Set (E 0)) (n : ℕ) (Wq : ScBanach)
      (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod Wq)) (z : E 1),
      tangentSpace E C Q z = tangentSpace E C Q₂ z → tangentSpace E C O z = tangentSpace E C O₂ z →
      Φ E C O Q n Wq T z → Φ E C O₂ Q₂ n Wq T z)
    (htrans : ∀ (E E' : ScBanach) (C : Set (E 0)) (C' : Set (E' 0)) (R : ScRetraction E C)
      (R' : ScRetraction E' C') (F : E 0 → E' 0) (G : E' 0 → E 0), R.IsDiffeoGerm R' F G →
      IsScSmooth R.U (F ∘ R) → IsScSmooth R'.U (G ∘ R') → ∀ (Q : Set (E 0)) (Q' : Set (E' 0)),
      IsScRetract E C Q → IsScRetract E' C' Q' → Q ⊆ R.retract → Q' ⊆ R'.retract →
      MapsTo F Q Q' → MapsTo G Q' Q → ∀ z : E 1, z ∈ E.lvlSet Q 1 → z ∈ E.smoothLvl 1 →
      ∀ (n : ℕ) (Wq : ScBanach) (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod Wq)),
      C = T 0 ⁻¹' quadrant n Wq 0 → ∀ (n' : ℕ) (Wq' : ScBanach)
      (T' : ScIso E' ((ScBanach.const (Fin n' → ℝ)).prod Wq')), C' = T' 0 ⁻¹' quadrant n' Wq' 0 →
      Φ E C R.retract Q n Wq T z → Φ E' C' R'.retract Q' n' Wq' T' (levelMap (F ∘ R) 1 z))
    {φ φ' : MChart X} (hφ : P.IsChart φ)
    (hφ' : P.IsChart φ') {A G G' : Set X} (hG : IsOpen G) (hG' : IsOpen G')
    (hGφ : G ⊆ φ.source) (hGφ' : G' ⊆ φ'.source)
    (hQ : IsScRetract φ.model.E φ.model.C (φ '' (G ∩ A)))
    (hQ' : IsScRetract φ'.model.E φ'.model.C (φ' '' (G' ∩ A))) {a : X} (haA : a ∈ A)
    (haG : a ∈ G) (haG' : a ∈ G') {z : φ.model.E 1} {z' : φ'.model.E 1}
    (hz : φ.model.E.toBase 1 z = φ a) (hz' : φ'.model.E.toBase 1 z' = φ' a)
    (hzs : z ∈ φ.model.E.smoothLvl 1) {n n' : ℕ} {Wq Wq' : ScBanach}
    (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : φ.model.C = T 0 ⁻¹' quadrant n Wq 0)
    (T' : ScIso φ'.model.E ((ScBanach.const (Fin n' → ℝ)).prod Wq'))
    (hT' : φ'.model.C = T' 0 ⁻¹' quadrant n' Wq' 0)
    (h : Φ φ.model.E φ.model.C φ.model.O (φ '' (G ∩ A)) n Wq T z) :
    Φ φ'.model.E φ'.model.C φ'.model.O (φ' '' (G' ∩ A)) n' Wq' T' z' := by
  classical
  have hbase : φ.Compatible φ' := MPolyfold.IsChart.compatible P hφ hφ'
  obtain ⟨W, hWo, hW⟩ := φ.exists_isOpen_image_eq (s := φ.source ∩ φ'.source)
    inter_subset_left (φ.isOpen_source.inter φ'.isOpen_source)
  obtain ⟨W', hWo', hW'⟩ := φ'.exists_isOpen_image_eq (s := φ'.source ∩ φ.source)
    inter_subset_left (φ'.isOpen_source.inter φ.isOpen_source)
  obtain ⟨R, hR⟩ := φ.model.isScRetract
  obtain ⟨R', hR'⟩ := φ'.model.isScRetract
  set Rw := R.restrict hWo with hRwdef
  set Rw' := R'.restrict hWo' with hRw'def
  have hRw : Rw.retract = φ.overlap φ' := by rw [R.restrict_retract, hR]; exact hW.symm
  have hRw' : Rw'.retract = φ'.overlap φ := by rw [R'.restrict_retract, hR']; exact hW'.symm
  set τ := φ.transition φ' with hτdef
  set τ' := φ'.transition φ with hτ'def
  have hdiff : Rw.IsDiffeoGerm Rw' τ τ' :=
    { isSc1 := (hbase.1.comp_isScSmooth Rw hRw).isSc1
      isSc1_inv := (hbase.2.comp_isScSmooth Rw' hRw').isSc1
      mapsTo := by rw [hRw, hRw']; exact φ.transition_mapsTo φ'
      mapsTo_inv := by rw [hRw, hRw']; exact φ'.transition_mapsTo φ
      left_inv := by
        rw [hRw]; rintro _ ⟨y₁, hy₁, rfl⟩
        rw [hτdef, hτ'def, φ.transition_apply φ' hy₁.1, φ'.transition_apply φ hy₁.2]
      right_inv := by
        rw [hRw']; rintro _ ⟨y₁, hy₁, rfl⟩
        rw [hτdef, hτ'def, φ'.transition_apply φ hy₁.1, φ.transition_apply φ' hy₁.2] }
  have hτs : IsScSmooth Rw.U (τ ∘ Rw) := hbase.1.comp_isScSmooth Rw hRw
  have hτ's : IsScSmooth Rw'.U (τ' ∘ Rw') := hbase.2.comp_isScSmooth Rw' hRw'
  -- the common open piece `H = G ∩ G'`
  have hH : IsOpen (G ∩ G') := hG.inter hG'
  have hHφ : G ∩ G' ⊆ φ.source := fun x hx => hGφ hx.1
  have hHφ' : G ∩ G' ⊆ φ'.source := fun x hx => hGφ' hx.2
  obtain ⟨K, hK, hKeq⟩ := φ.exists_isOpen_image_eq hHφ hH
  obtain ⟨K', hK', hK'eq⟩ := φ'.exists_isOpen_image_eq hHφ' hH
  have hQH : φ '' ((G ∩ G') ∩ A) = φ '' (G ∩ A) ∩ K :=
    φ.image_inter_eq_inter hGφ inter_subset_left hKeq
  have hQ'H : φ' '' ((G ∩ G') ∩ A) = φ' '' (G' ∩ A) ∩ K' :=
    φ'.image_inter_eq_inter hGφ' inter_subset_right hK'eq
  have hQHr : IsScRetract φ.model.E φ.model.C (φ '' ((G ∩ G') ∩ A)) := by
    rw [hQH]; exact proposition_2_10_1 hQ hK
  have hQ'Hr : IsScRetract φ'.model.E φ'.model.C (φ' '' ((G ∩ G') ∩ A)) := by
    rw [hQ'H]; exact proposition_2_10_1 hQ' hK'
  have hQHsub : φ '' ((G ∩ G') ∩ A) ⊆ Rw.retract := by
    rw [hRw]; exact image_mono fun x hx => ⟨hHφ hx.1, hHφ' hx.1⟩
  have hQ'Hsub : φ' '' ((G ∩ G') ∩ A) ⊆ Rw'.retract := by
    rw [hRw']; exact image_mono fun x hx => ⟨hHφ' hx.1, hHφ hx.1⟩
  have hτQ : MapsTo τ (φ '' ((G ∩ G') ∩ A)) (φ' '' ((G ∩ G') ∩ A)) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hτdef, φ.transition_apply φ' (hHφ hx.1)]
    exact ⟨x, hx, rfl⟩
  have hτ'Q : MapsTo τ' (φ' '' ((G ∩ G') ∩ A)) (φ '' ((G ∩ G') ∩ A)) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hτ'def, φ'.transition_apply φ (hHφ' hx.1)]
    exact ⟨x, hx, rfl⟩
  have haH : a ∈ (G ∩ G') ∩ A := ⟨⟨haG, haG'⟩, haA⟩
  have hz1 : z ∈ φ.model.E.lvlSet (φ '' ((G ∩ G') ∩ A)) 1 := by
    rw [ScBanach.mem_lvlSet, hz]; exact ⟨a, haH, rfl⟩
  have hz'1 : φ'.model.E.toBase 1 z' ∈ φ' '' ((G ∩ G') ∩ A) := by rw [hz']; exact ⟨a, haH, rfl⟩
  -- the tangent spaces at `z` of the open pieces
  have hzQ : φ.model.E.toBase 1 z ∈ φ '' (G ∩ A) ∩ K := by rw [← hQH]; exact hz1
  have hzO : φ.model.E.toBase 1 z ∈ R.retract ∩ W := by
    rw [← R.restrict_retract hWo]; exact hQHsub hz1
  have hz'Q : φ'.model.E.toBase 1 z' ∈ φ' '' (G' ∩ A) ∩ K' := by rw [← hQ'H]; exact hz'1
  have hz'O : φ'.model.E.toBase 1 z' ∈ R'.retract ∩ W' := by
    rw [← R'.restrict_retract hWo']; exact hQ'Hsub hz'1
  have h1 : Φ φ.model.E φ.model.C Rw.retract (φ '' ((G ∩ G') ∩ A)) n Wq T z := by
    refine hcongr _ _ _ _ _ _ _ _ _ _ ?_ ?_ h
    · rw [hQH, tangentSpace_inter_isOpen hQ hK hzQ]
    · rw [R.restrict_retract hWo, tangentSpace_inter_isOpen R.isScRetract hWo hzO, hR]
  have h2 := htrans _ _ _ _ Rw Rw' τ τ' hdiff hτs hτ's _ _ hQHr hQ'Hr hQHsub hQ'Hsub hτQ hτ'Q
    z hz1 hzs n Wq T hT n' Wq' T' hT' h1
  have hlev : levelMap (τ ∘ Rw) 1 z = z' := by
    apply levelMap_eq_of_toBase_eq
    have hφa : φ a ∈ R.retract := hR ▸ φ.mapsTo_model a (hGφ haG)
    change φ'.model.E.toBase 1 z' = τ (R (φ.model.E.toBase 1 z))
    rw [hz, R.apply_eq_self_of_mem_retract hφa, hτdef, φ.transition_apply φ' (hGφ haG), hz']
  rw [hlev] at h2
  refine hcongr _ _ _ _ _ _ _ _ _ _ ?_ ?_ h2
  · rw [hQ'H, tangentSpace_inter_isOpen hQ' hK' hz'Q]
  · rw [R'.restrict_retract hWo', tangentSpace_inter_isOpen R'.isScRetract hWo' hz'O, hR']

/-- **The chart change for Definition 4.16** (`chart_change_of_transport` for
`IsGoodPositionRetractAt`, with `IsGoodPositionRetractAt.transport`). -/
theorem isGoodPositionRetractAt_chart_change {φ φ' : MChart X} (hφ : P.IsChart φ)
    (hφ' : P.IsChart φ') {A G G' : Set X} (hG : IsOpen G) (hG' : IsOpen G')
    (hGφ : G ⊆ φ.source) (hGφ' : G' ⊆ φ'.source)
    (hQ : IsScRetract φ.model.E φ.model.C (φ '' (G ∩ A)))
    (hQ' : IsScRetract φ'.model.E φ'.model.C (φ' '' (G' ∩ A))) {a : X} (haA : a ∈ A)
    (haG : a ∈ G) (haG' : a ∈ G') {z : φ.model.E 1} {z' : φ'.model.E 1}
    (hz : φ.model.E.toBase 1 z = φ a) (hz' : φ'.model.E.toBase 1 z' = φ' a)
    (hzs : z ∈ φ.model.E.smoothLvl 1) {n n' : ℕ} {Wq Wq' : ScBanach}
    (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : φ.model.C = T 0 ⁻¹' quadrant n Wq 0)
    (T' : ScIso φ'.model.E ((ScBanach.const (Fin n' → ℝ)).prod Wq'))
    (hT' : φ'.model.C = T' 0 ⁻¹' quadrant n' Wq' 0)
    (h : IsGoodPositionRetractAt φ.model.E φ.model.C φ.model.O (φ '' (G ∩ A)) T z) :
    IsGoodPositionRetractAt φ'.model.E φ'.model.C φ'.model.O (φ' '' (G' ∩ A)) T' z' :=
  chart_change_of_transport (fun E C O Q _ _ T z => IsGoodPositionRetractAt E C O Q T z)
    (fun _ _ _ _ _ _ _ _ _ _ hQ hO h => h.congr hQ hO)
    (fun _ _ _ _ _ _ _ _ h hF hG _ _ hQ hQ' hQR hQ'R hFQ hGQ _ hz _ _ _ T hT _ _ T' hT' hgp =>
      hgp.transport h hF hG hQ hQ' hQR hQ'R hFQ hGQ hz T hT T' hT')
    hφ hφ' hG hG' hGφ hGφ' hQ hQ' haA haG haG' hz hz' hzs T hT T' hT' h

/-- **The chart change for Definition 4.21** (`chart_change_of_transport` for
`IsGeneralPositionRetractAt`, with `IsGeneralPositionRetractAt.transport`). -/
theorem isGeneralPositionRetractAt_chart_change {φ φ' : MChart X} (hφ : P.IsChart φ)
    (hφ' : P.IsChart φ') {A G G' : Set X} (hG : IsOpen G) (hG' : IsOpen G')
    (hGφ : G ⊆ φ.source) (hGφ' : G' ⊆ φ'.source)
    (hQ : IsScRetract φ.model.E φ.model.C (φ '' (G ∩ A)))
    (hQ' : IsScRetract φ'.model.E φ'.model.C (φ' '' (G' ∩ A))) {a : X} (haA : a ∈ A)
    (haG : a ∈ G) (haG' : a ∈ G') {z : φ.model.E 1} {z' : φ'.model.E 1}
    (hz : φ.model.E.toBase 1 z = φ a) (hz' : φ'.model.E.toBase 1 z' = φ' a)
    (hzs : z ∈ φ.model.E.smoothLvl 1) {n n' : ℕ} {Wq Wq' : ScBanach}
    (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : φ.model.C = T 0 ⁻¹' quadrant n Wq 0)
    (T' : ScIso φ'.model.E ((ScBanach.const (Fin n' → ℝ)).prod Wq'))
    (hT' : φ'.model.C = T' 0 ⁻¹' quadrant n' Wq' 0)
    (h : IsGeneralPositionRetractAt φ.model.E φ.model.C φ.model.O (φ '' (G ∩ A)) T z) :
    IsGeneralPositionRetractAt φ'.model.E φ'.model.C φ'.model.O (φ' '' (G' ∩ A)) T' z' :=
  chart_change_of_transport (fun E C O Q _ _ T z => IsGeneralPositionRetractAt E C O Q T z)
    (fun _ _ _ _ _ _ _ _ _ _ hQ hO h => h.congr hQ hO)
    (fun _ _ _ _ _ _ _ _ h hF hG _ _ hQ hQ' hQR hQ'R hFQ hGQ _ hz hzs _ _ T hT _ _ T' hT' hgp =>
      hgp.transport h hF hG hQ hQ' hQR hQ'R hFQ hGQ hz hzs T hT T' hT')
    hφ hφ' hG hG' hGφ hGφ' hQ hQ' haA haG haG' hz hz' hzs T hT T' hT' h

variable (P)

namespace SubmanifoldData

variable {P} {A : Set X}

/-- **Definition 4.16 in a chart**: for the data `d` of Definition 4.13, a chart `φ` of `X`, a
presentation `T` of the partial quadrant `C` and a level-`1` point `z` (over `φ(a)`), the tangent
space `T_zA = T_z(φ(W ∩ A))` (Remark 4.14) is in good position to the partial cone
`C_zO = T_zO ∩ C_z` inside `T_zO` (the chart form of "`T_aA` is in good position to the partial
quadrant `C_aX` in `T_aX`"). -/
def IsGoodPositionChart (d : P.SubmanifoldData A) (φ : MChart X) {n : ℕ} {Wq : ScBanach}
    (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq)) (z : φ.model.E 1) : Prop :=
  IsGoodPositionRetractAt φ.model.E φ.model.C φ.model.O (φ '' (d.toSubData.shrink φ ∩ A)) T z

end SubmanifoldData

/-- **Definition 4.16**: the smooth finite-dimensional submanifold `A` is **in good position at
`a ∈ A`** if `T_aA` is in good position to the partial cone `C_aX` in `T_aX`.  As `T_aX` carries
no linear structure here (gap G.7), the condition is stated in a chart (`IsGoodPositionChart`): for
some data `d` of Definition 4.13 at `a`, some chart `φ` of `X` at `a`, some presentation `T` of the
partial quadrant of `φ` and the level-`1` point `z` over `φ(a)`.  It then holds for all of them
(`IsGoodPositionAt.isGoodPositionChart`). -/
def IsGoodPositionAt (A : Set X) (a : X) : Prop :=
  a ∈ A ∧ ∃ (d : P.SubmanifoldData A) (φ : MChart X) (n : ℕ) (Wq : ScBanach)
    (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq)) (z : φ.model.E 1),
    a ∈ d.V ∧ P.IsChart φ ∧ a ∈ φ.source ∧ φ.model.C = T 0 ⁻¹' quadrant n Wq 0 ∧
    φ.model.E.toBase 1 z = φ a ∧ d.IsGoodPositionChart φ T z

variable {P}

/-- **Definition 4.16 is independent of the choices** (the chart, the data of Definition 4.13, the
presentation of the partial quadrant): if `A` is in good position at `a`, then the chart condition
holds for every data `d'` at `a`, every chart `φ'` at `a`, every presentation `T'` and the
level-`1` point `z'` over `φ'(a)` (`isGoodPositionRetractAt_chart_change`, with `G = W`, `G' = W'`
the open sets of the two sub-M-polyfold charts). -/
theorem IsGoodPositionAt.isGoodPositionChart {A : Set X} {a : X} (h : P.IsGoodPositionAt A a)
    (d' : P.SubmanifoldData A) {φ' : MChart X} (hφ' : P.IsChart φ') {n' : ℕ} {Wq' : ScBanach}
    (T' : ScIso φ'.model.E ((ScBanach.const (Fin n' → ℝ)).prod Wq'))
    (hT' : φ'.model.C = T' 0 ⁻¹' quadrant n' Wq' 0) {z' : φ'.model.E 1} (ha' : a ∈ d'.V)
    (haφ' : a ∈ φ'.source) (hz' : φ'.model.E.toBase 1 z' = φ' a) :
    d'.IsGoodPositionChart φ' T' z' := by
  obtain ⟨haA, d, φ, n, Wq, T, z, ha, hφ, haφ, hT, hz, hgp⟩ := h
  have hzs : z ∈ φ.model.E.smoothLvl 1 := by
    change φ.model.E.toBase 1 z ∈ (φ.model.E.smooth : Set (φ.model.E 0))
    rw [hz]; exact d.apply_mem_smooth hφ haA ha haφ
  exact isGoodPositionRetractAt_chart_change hφ hφ' (d.toSubData.isOpen_shrink φ)
    (d'.toSubData.isOpen_shrink φ') (d.toSubData.shrink_subset_source φ)
    (d'.toSubData.shrink_subset_source φ') (d.toSubData.isScRetract_image φ hφ)
    (d'.toSubData.isScRetract_image φ' hφ') haA (d.toSubData.mem_shrink φ haA ha haφ)
    (d'.toSubData.mem_shrink φ' haA ha' haφ') hz hz' hzs T hT T' hT' hgp

/-- **Definition 4.16, the chart-free form**: `A` is in good position at `a ∈ A` iff the chart
condition holds for all data, charts, presentations and lifts (equivalently, by
`IsGoodPositionAt.isGoodPositionChart`, for one of them). -/
theorem isGoodPositionAt_iff_forall {A : Set X} (hA : P.IsSmoothSubmanifold A) {a : X}
    (haA : a ∈ A) :
    P.IsGoodPositionAt A a ↔ ∀ (d : P.SubmanifoldData A) (φ : MChart X), P.IsChart φ →
      ∀ (n : ℕ) (Wq : ScBanach) (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq)),
        φ.model.C = T 0 ⁻¹' quadrant n Wq 0 → ∀ z : φ.model.E 1, a ∈ d.V → a ∈ φ.source →
          φ.model.E.toBase 1 z = φ a → d.IsGoodPositionChart φ T z := by
  refine ⟨fun h d φ hφ n Wq T hT z ha haφ hz => h.isGoodPositionChart d hφ T hT ha haφ hz,
    fun h => ?_⟩
  obtain ⟨φ, hφ, haφ⟩ := P.exists_isChart_mem_source a
  obtain ⟨n, Wq, T, hT⟩ := φ.model.isPartialQuadrant
  have hs : φ a ∈ φ.model.E.smooth := (mem_smoothSet_iff hφ haφ).1 (hA.subset_smoothSet haA)
  obtain ⟨z, hz, -⟩ := exists_smoothLvl_one_of_mem_smooth hs
  exact ⟨haA, hA.data haA, φ, n, Wq, T, z, hA.mem_data_V haA, hφ, haφ, hT, hz,
    h _ φ hφ n Wq T hT z (hA.mem_data_V haA) haφ hz⟩

/-- **Definition 4.16 in a chart, explicitly** (the form `range D(φ ∘ s ∘ φ⁻¹ ∘ r)(φ(a))`): for
retractions `r` onto the model `O` of `φ` and `t` onto `φ(W ∩ A)` (e.g. the sc⁺-retraction
`t = φ ∘ s ∘ φ⁻¹ ∘ r` of `SubmanifoldData.exists_chartRetraction`), the chart condition says that
`Dt(z)E` is in good position to the partial quadrant `C_z` inside `Dr(z)E`. -/
theorem SubmanifoldData.isGoodPositionChart_iff {A : Set X} (d : P.SubmanifoldData A)
    {φ : MChart X} {n : ℕ} {Wq : ScBanach}
    (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq)) {z : φ.model.E 1}
    (R : ScRetraction φ.model.E φ.model.C) (hR : R.retract = φ.model.O)
    (t : ScRetraction φ.model.E φ.model.C) (ht : t.retract = φ '' (d.toSubData.shrink φ ∩ A))
    (hz : φ.model.E.toBase 1 z ∈ φ '' (d.toSubData.shrink φ ∩ A)) :
    d.IsGoodPositionChart φ T z ↔
      IsInGoodPositionIn φ.model.E (rangeS (scDeriv R.U R z))
        (partialQuadrantAtWith T (φ.model.E.toBase 1 z)) (rangeS (scDeriv t.U t z)) := by
  have hzt : z ∈ φ.model.E.lvlSet t.retract 1 := by rw [ScBanach.mem_lvlSet, ht]; exact hz
  have hzR : z ∈ φ.model.E.lvlSet R.retract 1 := by
    rw [ScBanach.mem_lvlSet, hR]
    exact φ.image_subset_model (fun _ hx => d.toSubData.shrink_subset_source φ hx.1) hz
  have hN : ((rangeS (scDeriv t.U t z) : Submodule ℝ (φ.model.E 0)) : Set (φ.model.E 0)) =
      tangentSpace φ.model.E φ.model.C (φ '' (d.toSubData.shrink φ ∩ A)) z := by
    rw [← ht]; exact (tangentSpace_eq_coe_submodule t hzt).symm
  have hM : ((rangeS (scDeriv R.U R z) : Submodule ℝ (φ.model.E 0)) : Set (φ.model.E 0)) =
      tangentSpace φ.model.E φ.model.C φ.model.O z := by
    rw [← hR]; exact (tangentSpace_eq_coe_submodule R hzR).symm
  constructor
  · rintro ⟨N, M, hN', hM', hg⟩
    rw [SetLike.coe_injective (hN'.trans hN.symm), SetLike.coe_injective (hM'.trans hM.symm)] at hg
    exact hg
  · intro hg
    exact ⟨_, _, hN, hM, hg⟩

/-! ### Definition 4.21: general position, and its chart independence -/

namespace SubmanifoldData

variable {A : Set X}

/-- **Definition 4.21 in a chart**: for the data `d` of Definition 4.13, a chart `φ` of `X`, a
presentation `T` of the partial quadrant and a level-`1` point `z` (over `φ(a)`), the tangent space
`T_zA = T_z(φ(W ∩ A))` has in `T_zO` an sc-complement contained in `T_z^R O = T_zO ∩ E_z`
(`IsGeneralPositionRetractAt`). -/
def IsGeneralPositionChart (d : P.SubmanifoldData A) (φ : MChart X) {n : ℕ} {Wq : ScBanach}
    (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq)) (z : φ.model.E 1) : Prop :=
  IsGeneralPositionRetractAt φ.model.E φ.model.C φ.model.O (φ '' (d.toSubData.shrink φ ∩ A)) T z

end SubmanifoldData

variable (P) in
/-- **Definition 4.21**: the smooth finite-dimensional submanifold `A` is **in general position at
`a ∈ A`** if `T_aA` has in `T_aX` an sc-complement contained in the reduced tangent space `T_a^R X`
(Definition 2.38).  As for Definition 4.16, the condition is stated in a chart
(`IsGeneralPositionChart`), for some data, chart, presentation and lift; it then holds for all of
them (`IsGeneralPositionAt.isGeneralPositionChart`). -/
def IsGeneralPositionAt (A : Set X) (a : X) : Prop :=
  a ∈ A ∧ ∃ (d : P.SubmanifoldData A) (φ : MChart X) (n : ℕ) (Wq : ScBanach)
    (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq)) (z : φ.model.E 1),
    a ∈ d.V ∧ P.IsChart φ ∧ a ∈ φ.source ∧ φ.model.C = T 0 ⁻¹' quadrant n Wq 0 ∧
    φ.model.E.toBase 1 z = φ a ∧ d.IsGeneralPositionChart φ T z

/-- **Definition 4.21 is independent of the choices** (chart, data of Definition 4.13,
presentation): `isGeneralPositionRetractAt_chart_change`, through `T_zO ≅ T_{z'}O'` carrying
`T_z^R O` onto `T_{z'}^R O'` (Proposition 2.30) and the sc-complement onto an sc-complement. -/
theorem IsGeneralPositionAt.isGeneralPositionChart {A : Set X} {a : X}
    (h : P.IsGeneralPositionAt A a) (d' : P.SubmanifoldData A) {φ' : MChart X}
    (hφ' : P.IsChart φ') {n' : ℕ} {Wq' : ScBanach}
    (T' : ScIso φ'.model.E ((ScBanach.const (Fin n' → ℝ)).prod Wq'))
    (hT' : φ'.model.C = T' 0 ⁻¹' quadrant n' Wq' 0) {z' : φ'.model.E 1} (ha' : a ∈ d'.V)
    (haφ' : a ∈ φ'.source) (hz' : φ'.model.E.toBase 1 z' = φ' a) :
    d'.IsGeneralPositionChart φ' T' z' := by
  obtain ⟨haA, d, φ, n, Wq, T, z, ha, hφ, haφ, hT, hz, hgp⟩ := h
  have hzs : z ∈ φ.model.E.smoothLvl 1 := by
    change φ.model.E.toBase 1 z ∈ (φ.model.E.smooth : Set (φ.model.E 0))
    rw [hz]; exact d.apply_mem_smooth hφ haA ha haφ
  exact isGeneralPositionRetractAt_chart_change hφ hφ' (d.toSubData.isOpen_shrink φ)
    (d'.toSubData.isOpen_shrink φ') (d.toSubData.shrink_subset_source φ)
    (d'.toSubData.shrink_subset_source φ') (d.toSubData.isScRetract_image φ hφ)
    (d'.toSubData.isScRetract_image φ' hφ') haA (d.toSubData.mem_shrink φ haA ha haφ)
    (d'.toSubData.mem_shrink φ' haA ha' haφ') hz hz' hzs T hT T' hT' hgp

/-- **Definition 4.21, the chart-free form**: `A` is in general position at `a ∈ A` iff the chart
condition holds for all data, charts, presentations and lifts. -/
theorem isGeneralPositionAt_iff_forall {A : Set X} (hA : P.IsSmoothSubmanifold A) {a : X}
    (haA : a ∈ A) :
    P.IsGeneralPositionAt A a ↔ ∀ (d : P.SubmanifoldData A) (φ : MChart X), P.IsChart φ →
      ∀ (n : ℕ) (Wq : ScBanach) (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq)),
        φ.model.C = T 0 ⁻¹' quadrant n Wq 0 → ∀ z : φ.model.E 1, a ∈ d.V → a ∈ φ.source →
          φ.model.E.toBase 1 z = φ a → d.IsGeneralPositionChart φ T z := by
  refine ⟨fun h d φ hφ n Wq T hT z ha haφ hz => h.isGeneralPositionChart d hφ T hT ha haφ hz,
    fun h => ?_⟩
  obtain ⟨φ, hφ, haφ⟩ := P.exists_isChart_mem_source a
  obtain ⟨n, Wq, T, hT⟩ := φ.model.isPartialQuadrant
  have hs : φ a ∈ φ.model.E.smooth := (mem_smoothSet_iff hφ haφ).1 (hA.subset_smoothSet haA)
  obtain ⟨z, hz, -⟩ := exists_smoothLvl_one_of_mem_smooth hs
  exact ⟨haA, hA.data haA, φ, n, Wq, T, z, hA.mem_data_V haA, hφ, haφ, hT, hz,
    h _ φ hφ n Wq T hT z (hA.mem_data_V haA) haφ hz⟩

/-! ### Definition 4.17 and Theorem 4.18 -/

variable (P) in
/-- **Definition 4.17**: a smooth finite-dimensional submanifold `A ⊆ X` is **tame** if the
M-polyfold `A`, with the structure induced from `X` (Proposition 2.21, `subPolyfold`), is tame
(Definition 2.37).  (The induced structure depends only on `A`, by proof irrelevance.) -/
def IsTameSubmanifold (A : Set X) [ParacompactSpace A] : Prop :=
  ∃ hA : P.IsSmoothSubmanifold A, (subPolyfold hA.isSubMPolyfold).IsTame

/-- **The corner charts of `A`** (the core of the proof of Theorem 4.18, through Theorem 4.2): if
every `a ∈ A` lies in a chart `ψ` of `X` centred at `a` (`ψ(a) = 0`) in which the tangent space
`N = T₀(ψ(W ∩ A))` of the chart model of `A` (for the data of Definition 4.13 at `a`) is in good
position to the partial quadrant `C` of `ψ` in `E`, then the induced M-polyfold structure on `A`
has a corner structure (Definition 4.1).  *Proof*: Proposition 4.15 (4) (`A = A_∞`, `1₀¹ : A → A¹`
sc-smooth), the induced chart `subChart` of `A` centred at `a`, `N` finite-dimensional by Lemma 4.7
for the sc⁺ chart retraction, and Theorem 4.2 (ii) ⇒ (i) (`hasCornerStructure_of_centred`). -/
theorem hasCornerStructure_of_centred_isInGoodPosition {A : Set X}
    (hA : P.IsSmoothSubmanifold A) [ParacompactSpace A]
    (h : ∀ a (ha : a ∈ A), ∃ ψ : MChart X, P.IsChart ψ ∧ a ∈ ψ.source ∧ ψ a = 0 ∧
      ∀ N : Submodule ℝ (ψ.model.E 0), (N : Set (ψ.model.E 0)) =
        tangentSpace ψ.model.E ψ.model.C (ψ '' ((hA.data ha).toSubData.shrink ψ ∩ A)) 0 →
        IsInGoodPosition ψ.model.E ψ.model.C N) :
    (subPolyfold hA.isSubMPolyfold).HasCornerStructure := by
  by_cases hne : Nonempty A
  · obtain ⟨a₀⟩ := hne
    have h1 : a₀ ∈ (subPolyfold hA.isSubMPolyfold).levelSet 1 :=
      (hA.mem_levelSet_subPolyfold_iff a₀ 1).2 (hA.mem_levelSet_one a₀.2)
    set x₀ := (subPolyfold hA.isSubMPolyfold).levelMk 1 a₀ h1
    obtain ⟨hsm, hmap⟩ := hA.proposition_4_15_4 x₀
    refine hasCornerStructure_of_centred x₀ hsm hmap fun a => ?_
    obtain ⟨ψ, hψ, haψ, hψ0, hgood⟩ := h a a.2
    set d := hA.data a.2
    have haW : a.1 ∈ d.toSubData.shrink ψ :=
      d.toSubData.mem_shrink ψ a.2 (hA.mem_data_V a.2) haψ
    refine ⟨subChart d.toSubData hψ a, subPolyfold_isChart hA.isSubMPolyfold d.toSubData hψ a,
      haW, hψ0, ?_⟩
    obtain ⟨R, hR⟩ := ψ.model.isScRetract
    have hz : ψ.model.E.toBase 1 0 = ψ a := by rw [map_zero, hψ0]
    obtain ⟨t, ht, htp, -⟩ :=
      d.exists_chartRetraction hψ (P.levelMk 1 a.1 (hA.mem_levelSet_one a.2)) R hR
    have h0t : (0 : ψ.model.E 1) ∈ ψ.model.E.lvlSet t.retract 1 := by
      rw [ScBanach.mem_lvlSet, ht, hz]; exact ⟨a.1, ⟨haW, a.2⟩, rfl⟩
    have hN : ((LinearMap.range (scDeriv t.U t 0 : ψ.model.E 0 →ₗ[ℝ] ψ.model.E 0) :
        Submodule ℝ (ψ.model.E 0)) : Set (ψ.model.E 0)) =
        tangentSpace ψ.model.E ψ.model.C (ψ '' (d.toSubData.shrink ψ ∩ A)) 0 := by
      rw [← ht]; exact (tangentSpace_eq_coe_submodule t h0t).symm
    exact ⟨_, hN, lemma_4_7_ii htp h0t, hgood _ hN⟩
  · rw [hasCornerStructure_iff]
    intro x
    exact (hne ⟨x⟩).elim

/-- **Good position read in a tame centred chart** (the step of the proof of Theorem 4.18 before
Theorem 4.2): if `A` is in good position at `a` and `ψ` is a chart of `X` with `ψ(a) = 0` modelled
on a tame retract, then `N = T₀(ψ(W ∩ A))` is in good position to the partial quadrant `C` in `E`:
the chart condition in `ψ` (chart independence of Definition 4.16) gives good position to
`C_0 = C` inside `T₀O = Dr(0)E`, and Lemma 4.19 with `π = Dr(0)` (`(1 − Dr(0))E ⊆ E₀` by
Proposition 2.35 for the tame retraction `r`) gives good position in `E`. -/
theorem IsGoodPositionAt.isInGoodPosition_of_tame {A : Set X} {a : X}
    (h : P.IsGoodPositionAt A a) (d : P.SubmanifoldData A) (had : a ∈ d.V) {ψ : MChart X}
    (hψ : P.IsChart ψ) (haψ : a ∈ ψ.source) (hψ0 : ψ a = 0)
    (htame : IsTameRetract ψ.model.E ψ.model.C ψ.model.O) {N : Submodule ℝ (ψ.model.E 0)}
    (hN : (N : Set (ψ.model.E 0)) =
      tangentSpace ψ.model.E ψ.model.C (ψ '' (d.toSubData.shrink ψ ∩ A)) 0) :
    IsInGoodPosition ψ.model.E ψ.model.C N := by
  obtain ⟨R, hR, hRt⟩ := htame
  obtain ⟨n, Wq, T, hT⟩ := ψ.model.isPartialQuadrant
  have hz : ψ.model.E.toBase 1 0 = ψ a := by rw [map_zero, hψ0]
  obtain ⟨N', M, hN', hM, hgood⟩ := h.isGoodPositionChart d hψ T hT had haψ hz
  have hNN' : N' = N := SetLike.coe_injective (hN'.trans hN.symm)
  subst hNN'
  have h01 : (0 : ψ.model.E 1) ∈ ψ.model.E.lvlSet R.retract 1 := by
    rw [ScBanach.mem_lvlSet, hR, hz]; exact ψ.mapsTo_model a haψ
  have hs0 : (0 : ψ.model.E 1) ∈ ψ.model.E.smoothLvl 1 := by
    change ψ.model.E.toBase 1 0 ∈ (ψ.model.E.smooth : Set (ψ.model.E 0))
    rw [map_zero]; exact ψ.model.E.smooth.zero_mem
  have hK := (proposition_2_35 hT (hRt n Wq T hT) h01 hs0).1
  have hMeq : M = rangeS (scDeriv R.U R 0) := by
    refine SetLike.coe_injective (hM.trans ?_)
    rw [← hR]
    exact tangentSpace_eq_coe_submodule R h01
  rw [hMeq, map_zero, partialQuadrantAtWith_zero, ← hT] at hgood
  rw [map_zero] at hK
  have hπ : ∀ v, scDeriv R.U R 0 (scDeriv R.U R 0 v) = scDeriv R.U R 0 v := fun v =>
    congrArg (fun L : ψ.model.E 0 →L[ℝ] ψ.model.E 0 => L v) (R.scDeriv_comp_self h01)
  exact (lemma_4_19 T hT (scDeriv R.U R 0) hπ hK hgood).1

/-- **Theorem 4.18**: let `X` be a tame M-polyfold and `A ⊆ X` a smooth finite-dimensional
submanifold in good position at every point (Definition 4.16).  Then the induced M-polyfold
structure on `A` is equivalent to the structure of a smooth manifold with boundary with corners
(Definition 4.1, `HasCornerStructure`), and `A` is tame (Definition 4.17).
*Proof* (the text's, through Theorem 4.2): every point of `A` is smooth and `1₀¹ : A → A¹` is
sc-smooth (Proposition 4.15 (4)).  At `a ∈ A` take a tame chart `ψ` of `X` centred at `a`
(`MPolyfold.IsTame.exists_centredChart`, the re-centring that the text takes for granted); the
induced chart of `A` (`subChart`) is centred at `a`, modelled on the retract `ψ(W ∩ A)` of the
sc⁺-retraction `t = ψ ∘ s ∘ ψ⁻¹ ∘ r`, whose tangent space `N = T₀(ψ(W ∩ A)) = Dt(0)E` is
finite-dimensional (Lemma 4.7) and, by the good position hypothesis read in the chart `ψ`
(chart independence of Definition 4.16), in good position to `C` inside `T₀O`; by Lemma 4.19
(with `π = Dr(0)` for the tame retraction `r`, Proposition 2.35) `N` is in good position to `C`
in `E`.  Theorem 4.2, (ii) ⇒ (i) (`hasCornerStructure_of_centred`, which applies Propositions 4.8
and 4.9) gives the corner structure (`hasCornerStructure_of_centred_isInGoodPosition`), and a
manifold with corners is tame. -/
theorem theorem_4_18 (hP : P.IsTame) {A : Set X} (hA : P.IsSmoothSubmanifold A)
    [ParacompactSpace A] (hgp : ∀ a ∈ A, P.IsGoodPositionAt A a) :
    (subPolyfold hA.isSubMPolyfold).HasCornerStructure ∧ P.IsTameSubmanifold A := by
  have hcs : (subPolyfold hA.isSubMPolyfold).HasCornerStructure := by
    refine hasCornerStructure_of_centred_isInGoodPosition hA fun a ha => ?_
    obtain ⟨ψ, hψ, haψ, hψ0, htame⟩ := hP.exists_centredChart (hA.subset_smoothSet ha)
    exact ⟨ψ, hψ, haψ, hψ0, fun N hN =>
      (hgp a ha).isInGoodPosition_of_tame (hA.data ha) (hA.mem_data_V ha) hψ haψ hψ0 htame hN⟩
  exact ⟨hcs, hA, hcs.isTame⟩

/-- **Remark 4.14, last sentences: at points with `d_X(a) = 0` the good position is automatic**:
if `d_X(a) = 0` then `C_aX = T_aX`, and every subspace of `T_aX` is in good position to it (any
algebraic complement is a good complement).  In the chart realizing `d_X(a) = 0` the partial
quadrant `C_{φ(a)}` is the whole space. -/
theorem isGoodPositionAt_of_degIndex_eq_zero {A : Set X} (hA : P.IsSmoothSubmanifold A) {a : X}
    (ha : a ∈ A) (h0 : P.degIndex a = 0) : P.IsGoodPositionAt A a := by
  obtain ⟨φ, hφ, haφ, hd⟩ := P.exists_isChart_degIndex_eq a
  obtain ⟨n, Wq, T, hT⟩ := φ.model.isPartialQuadrant
  have hs : φ a ∈ φ.model.E.smooth := (mem_smoothSet_iff hφ haφ).1 (hA.subset_smoothSet ha)
  obtain ⟨z, hz, -⟩ := exists_smoothLvl_one_of_mem_smooth hs
  set d := hA.data ha
  refine ⟨ha, d, φ, n, Wq, T, z, hA.mem_data_V ha, hφ, haφ, hT, hz, ?_⟩
  have hhuniv : partialQuadrantAtWith T (φ.model.E.toBase 1 z) = univ := by
    rw [hz]
    exact partialQuadrantAtWith_eq_univ_of_degIndex_eq_zero T hT (φ.apply_mem_C haφ)
      (hd.symm.trans h0)
  obtain ⟨-, -, hsub, N, hN, -⟩ := d.remark_4_14 hφ ha (hA.mem_data_V ha) haφ hz
  obtain ⟨R, hR⟩ := φ.model.isScRetract
  have hz1 : z ∈ φ.model.E.lvlSet R.retract 1 := by
    rw [ScBanach.mem_lvlSet, hR, hz]; exact φ.mapsTo_model a haφ
  have hM : ((rangeS (scDeriv R.U R z) : Submodule ℝ (φ.model.E 0)) : Set (φ.model.E 0)) =
      tangentSpace φ.model.E φ.model.C φ.model.O z := by
    rw [← hR]; exact (tangentSpace_eq_coe_submodule R hz1).symm
  refine ⟨N, rangeS (scDeriv R.U R z), hN, hM, ?_⟩
  rw [hhuniv]
  refine (isInGoodPosition_univ N).isInGoodPositionIn_of_le fun v hv => ?_
  have hv' : v ∈ tangentSpace φ.model.E φ.model.C φ.model.O z := hsub (hN ▸ hv)
  rw [← hM] at hv'
  exact hv'

/-- **Remark 4.14: near `d_X = 0` a submanifold is a manifold in the classical sense** (no
tameness needed): if `d_X(a) = 0` for every `a ∈ A` then the induced structure on `A` has a corner
structure (Definition 4.1).  *Proof*: in the chart re-centred at `a` from a chart realizing
`d_X(a) = 0`, the partial quadrant `C_{φ(a)}` is the whole space, and every subspace is in good
position to the whole space (`hasCornerStructure_of_centred_isInGoodPosition`). -/
theorem hasCornerStructure_of_degIndex_eq_zero {A : Set X} (hA : P.IsSmoothSubmanifold A)
    [ParacompactSpace A] (h0 : ∀ a ∈ A, P.degIndex a = 0) :
    (subPolyfold hA.isSubMPolyfold).HasCornerStructure := by
  refine hasCornerStructure_of_centred_isInGoodPosition hA fun a ha => ?_
  obtain ⟨φ, hφ, haφ, hd⟩ := P.exists_isChart_degIndex_eq a
  obtain ⟨n, Wq, T, hT⟩ := φ.model.isPartialQuadrant
  have he : φ a ∈ φ.model.E.smooth := (mem_smoothSet_iff hφ haφ).1 (hA.subset_smoothSet ha)
  refine ⟨φ.recentre T hT (φ a) he, φ.recentre_isChart T hT (φ a) he hφ,
    φ.mem_recentre_source T hT (φ a) he haφ rfl, φ.recentre_apply_self T hT (φ a) he rfl,
    fun N _ => ?_⟩
  rw [MChart.recentre_model_C, partialQuadrantAtWith_eq_univ_of_degIndex_eq_zero T hT
    (φ.apply_mem_C haφ) (hd.symm.trans (h0 a ha))]
  exact isInGoodPosition_univ N

/-! ### Remark 4.20: good position is an open condition -/

/-- **Remark 4.20**: in a tame M-polyfold, if the smooth finite-dimensional submanifold `A` is in
good position at `a`, there is an open neighbourhood `U ⊆ X` of `a` such that `A` is in good
position at every `b ∈ U ∩ A`.  *Proof* (the text's: "Proposition 4.9 defines a chart from the sole
knowledge that we are in good position at `0`; since the tangent spaces of `A` move only slowly,
Lemma 3.55 implies that we are in good position at the nearby points as well"): in a tame chart `ψ`
centred at `a`, `N = T₀(ψ(W ∩ A))` is in good position to `C` in `E`
(`IsGoodPositionAt.isInGoodPosition_of_tame`); with the closed good complement `Y = ker π` of the
normal form (`exists_proj_goodComplement`), Proposition 4.9 for the sc⁺-retraction `t` describes
`ψ(W ∩ A)` near `0` as the graph `Γ(v) = v + σ(v)`, `σ = (1 − π) ∘ Γ : V → Y`, `σ` of class `C¹`
with `σ(0) = 0`, `Dσ(0) = 0`; the tangent space at `Γ(v)` is `DΓ(v)N = {n + Dσ(v)n}`
(`tangentSpace_eq_range_graph`), which by Lemma 3.55 (`lemma_3_55_relOpen`) is in good position to
`C_{Γ(v)}` in `E` for `|v|` small, hence to the partial cone inside `T_{Γ(v)}O`
(`IsInGoodPosition.isInGoodPositionIn_of_le`); that is Definition 4.16 at `b = ψ⁻¹(Γ(v))` in the
chart `ψ`.  The neighbourhood is `U = {b ∈ W | ψ(b) ∈ W₁, |π(ψ(b))| < ρ}`. -/
theorem remark_4_20 (hP : P.IsTame) {A : Set X} (hA : P.IsSmoothSubmanifold A) {a : X}
    (h : P.IsGoodPositionAt A a) :
    ∃ U : Set X, IsOpen U ∧ a ∈ U ∧ ∀ b ∈ U ∩ A, P.IsGoodPositionAt A b := by
  classical
  have haA : a ∈ A := h.1
  obtain ⟨ψ, hψ, haψ, hψ0, htame⟩ := hP.exists_centredChart (hA.subset_smoothSet haA)
  set d := hA.data haA with hd
  have had : a ∈ d.V := hA.mem_data_V haA
  have haW : a ∈ d.toSubData.shrink ψ := d.toSubData.mem_shrink ψ haA had haψ
  obtain ⟨n, Wq, T, hT⟩ := ψ.model.isPartialQuadrant
  obtain ⟨R, hR⟩ := ψ.model.isScRetract
  obtain ⟨t, ht, htp, -⟩ :=
    d.exists_chartRetraction hψ (P.levelMk 1 a (hA.mem_levelSet_one haA)) R hR
  have hz : ψ.model.E.toBase 1 0 = ψ a := by rw [map_zero, hψ0]
  have h0t : (0 : ψ.model.E 1) ∈ ψ.model.E.lvlSet t.retract 1 := by
    rw [ScBanach.mem_lvlSet, ht, hz]; exact ⟨a, ⟨haW, haA⟩, rfl⟩
  have h0Q : (0 : ψ.model.E 0) ∈ t.retract := by
    have := h0t; rwa [ScBanach.mem_lvlSet, map_zero] at this
  set N : Submodule ℝ (ψ.model.E 0) :=
    LinearMap.range (scDeriv t.U t 0 : ψ.model.E 0 →ₗ[ℝ] ψ.model.E 0) with hNdef
  have : FiniteDimensional ℝ N := lemma_4_7_ii htp h0t
  have hN : (N : Set (ψ.model.E 0)) = tangentSpace ψ.model.E ψ.model.C t.retract 0 :=
    (tangentSpace_eq_coe_submodule t h0t).symm
  have hgood : IsInGoodPosition ψ.model.E ψ.model.C N :=
    h.isInGoodPosition_of_tame d had hψ haψ hψ0 htame (by rw [hN, ht])
  obtain ⟨π, hπN, -, hY⟩ := exists_proj_goodComplement ψ.model.isPartialQuadrant hgood
  have hπY : ∀ y ∈ LinearMap.ker (π : ψ.model.E 0 →ₗ[ℝ] N), π y = 0 :=
    fun y hy => LinearMap.mem_ker.1 hy
  obtain ⟨W₁, V, Γ, hW₁, h0W₁, hV, h0V, hΓs, hpΓ, -, hΓV, hΓp, hΓ0, hpmap, hΓmap⟩ :=
    proposition_4_9 t htp h0Q hN hgood hY π.isClosed_ker π hπN hπY
  have hQ' : IsScRetract ψ.model.E ψ.model.C (t.retract ∩ W₁) :=
    proposition_2_10_1 t.isScRetract hW₁
  -- the graph map `σ = (1 − π) ∘ Γ : N → Y`
  set σ : N → ψ.model.E 0 := fun v => Γ v - ((π (Γ v) : N) : ψ.model.E 0) with hσdef
  have hσY : ∀ v, σ v ∈ LinearMap.ker (π : ψ.model.E 0 →ₗ[ℝ] N) := fun v => by
    rw [LinearMap.mem_ker]
    change π (Γ v - ((π (Γ v) : N) : ψ.model.E 0)) = 0
    rw [map_sub, hπN, sub_self]
  have hσV : ∀ v ∈ V, (v : ψ.model.E 0) + σ v = Γ v := fun v hv => by
    simp only [hσdef, hpΓ v hv]; abel
  have hΓC : ContDiffOn ℝ 1 Γ V := by
    have := (hΓs 1).contDiffOn_base hV.isScDomain
    rw [ScBanach.lvlSet_const] at this
    have e1 : (Γ ∘ ⇑((ScBanach.const N).toBase 1)) = Γ :=
      funext fun x => congrArg Γ (ScBanach.const_toBase N 1 x)
    rw [e1] at this
    exact_mod_cast this
  have hσC : ContDiffOn ℝ 1 σ V :=
    hΓC.sub ((N.subtypeL.comp π).contDiff.comp_contDiffOn hΓC)
  have huniq : ∀ v ∈ V, UniqueDiffWithinAt ℝ V v := fun v hv => by
    have := hV.isScDomain.uniqueDiffWithinAt 0 v (by rw [ScBanach.lvlSet_const]; exact hv)
    rwa [ScBanach.lvlSet_const] at this
  have hDσ : ∀ v ∈ V, fderivWithin ℝ σ V v = scDeriv (E := ScBanach.const N) V Γ v -
      (N.subtypeL.comp π).comp (scDeriv (E := ScBanach.const N) V Γ v) := fun v hv => by
    have hfd := hasFDerivWithinAt_scDeriv_const hΓs.isSc1 hv
    exact (hfd.sub ((N.subtypeL.comp π).hasFDerivAt.comp_hasFDerivWithinAt v hfd)).fderivWithin
      (huniq v hv)
  have hDσ0 : fderivWithin ℝ σ V 0 = 0 := by
    rw [hDσ 0 h0V]
    obtain ⟨-, hT0, -⟩ := tangentSpace_eq_range_graph hQ' hV hpmap hΓmap hΓp hpΓ h0V
      (y := 0) (by rw [map_zero, hΓ0])
    ext m
    have hmem : scDeriv (E := ScBanach.const N) V Γ 0 m ∈
        tangentSpace ψ.model.E ψ.model.C (t.retract ∩ W₁) 0 := by rw [hT0]; exact ⟨m, rfl⟩
    rw [tangentSpace_inter_isOpen t.isScRetract hW₁ (by rw [map_zero]; exact ⟨h0Q, h0W₁⟩),
      ← hN] at hmem
    have := hπN ⟨_, hmem⟩
    simp only [sub_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      Submodule.coe_subtypeL, Submodule.coe_subtype, zero_apply]
    rw [this, sub_self]
  have hσ0 : σ 0 = 0 := by simp only [hσdef, hΓ0, map_zero, ZeroMemClass.coe_zero, sub_self]
  obtain ⟨ρ, hρ, hρgood⟩ := lemma_3_55_relOpen T hT hgood hY π.isClosed_ker hV.relOpen h0V σ
    hσY hσC hσ0 hDσ0
  -- the neighbourhood `U`
  refine ⟨d.toSubData.shrink ψ ∩ ψ ⁻¹' (W₁ ∩ {u | ‖π u‖ < ρ}), ?_, ⟨haW, ?_⟩, ?_⟩
  · exact (ψ.continuousOn_toFun.mono (d.toSubData.shrink_subset_source ψ)).isOpen_inter_preimage
      (d.toSubData.isOpen_shrink ψ)
      (hW₁.inter (isOpen_lt (continuous_norm.comp π.continuous) continuous_const))
  · rw [mem_preimage, hψ0]
    refine ⟨h0W₁, ?_⟩
    change ‖π 0‖ < ρ
    rw [map_zero, norm_zero]; exact hρ
  · rintro b ⟨⟨hbW, hbW₁, hbρ⟩, hbA⟩
    have hbV : b ∈ d.V := d.toSubData.shrink_subset_V ψ hbW
    have hbψ : b ∈ ψ.source := d.toSubData.shrink_subset_source ψ hbW
    have hbQ : ψ b ∈ t.retract ∩ W₁ := ⟨ht ▸ ⟨b, ⟨hbW, hbA⟩, rfl⟩, hbW₁⟩
    have hbQ' := hbQ
    rw [← hΓV] at hbQ'
    obtain ⟨v, hv, hvb⟩ := hbQ'
    have hπv : π (ψ b) = v := by rw [← hvb, hpΓ v hv]
    have hvρ : ‖v‖ < ρ := by
      have : ‖π (ψ b)‖ < ρ := hbρ
      rwa [hπv] at this
    obtain ⟨-, -, hgp⟩ := hρgood v hv hvρ
    rw [hσV v hv, hvb] at hgp
    obtain ⟨y, hy, -⟩ := exists_smoothLvl_one_of_mem_smooth (d.apply_mem_smooth hψ hbA hbV hbψ)
    obtain ⟨-, hTy, hpD⟩ := tangentSpace_eq_range_graph hQ' hV hpmap hΓmap hΓp hpΓ hv
      (y := y) (by rw [hy, hvb])
    have hgraph : (graphSpace N (fderivWithin ℝ σ V v) : Set (ψ.model.E 0)) =
        tangentSpace ψ.model.E ψ.model.C (ψ '' (d.toSubData.shrink ψ ∩ A)) y := by
      rw [← ht, ← tangentSpace_inter_isOpen t.isScRetract hW₁ (by rw [hy]; exact hbQ), hTy]
      ext w
      rw [SetLike.mem_coe, mem_graphSpace, hDσ v hv]
      constructor
      · rintro ⟨m, rfl⟩
        refine ⟨m, ?_⟩
        simp only [sub_apply, ContinuousLinearMap.coe_comp,
          Function.comp_apply, Submodule.coe_subtypeL, Submodule.coe_subtype, hpD m]
        abel
      · rintro ⟨m, rfl⟩
        refine ⟨m, ?_⟩
        simp only [sub_apply, ContinuousLinearMap.coe_comp,
          Function.comp_apply, Submodule.coe_subtypeL, Submodule.coe_subtype, hpD m]
        abel
    obtain ⟨-, -, hsub, -⟩ := d.remark_4_14 hψ hbA hbV hbψ hy
    have hy1 : y ∈ ψ.model.E.lvlSet R.retract 1 := by
      rw [ScBanach.mem_lvlSet, hR, hy]; exact ψ.mapsTo_model b hbψ
    have hM : ((rangeS (scDeriv R.U R y) : Submodule ℝ (ψ.model.E 0)) : Set (ψ.model.E 0)) =
        tangentSpace ψ.model.E ψ.model.C ψ.model.O y := by
      rw [← hR]; exact (tangentSpace_eq_coe_submodule R hy1).symm
    refine ⟨hbA, d, ψ, n, Wq, T, y, hbV, hψ, hbψ, hT, hy, graphSpace N (fderivWithin ℝ σ V v),
      rangeS (scDeriv R.U R y), hgraph, hM, ?_⟩
    rw [hy]
    refine hgp.isInGoodPositionIn_of_le fun w hw => ?_
    have := hsub (by rw [← hgraph]; exact hw)
    rw [← hM] at this
    exact this

end MPolyfold

end Polyfold
