import Polyfold.Chapter3.FredholmGermLinearization
import Polyfold.Chapter3.GermFillingChart
import Polyfold.Chapter3.GermFillerLinearization
import Polyfold.Chapter3.GermPushforward

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.6,
**Proposition 3.6.5 (preprint 3.52)** (the linearization of an sc-Fredholm section at a zero is Fredholm, of the
index `n − N` of the conjugating basic germ) **in the text's germ reading of Definition 3.1.11 (preprint 3.11)**
(phase 2): the filling `g` and the sc⁺-section `s` are sc-smooth germs on germs of neighbourhoods
`G`, `G_s` whose levels may shrink with the level.

# The linearization of an sc-Fredholm germ, germ reading

## The text, paraphrased

(Proposition 3.6.5 (preprint 3.52)) If `f` is an sc-Fredholm section and `f(x) = 0`, then `Tf(x) : T_xX → Y_x` is
an sc-Fredholm operator.  Proof: in the chart of the sc-Fredholm germ, `D(g − s)(0)` is
sc-Fredholm by Proposition 3.1.10 (preprint 3.10), `Dg(0)` by Proposition 1.1.11 (preprint 1.10) (`Ds(0)` is sc⁺), and
`Tf̃(0) : T₀O → K₀` has the index of `Dg(0)` by Proposition 3.1.5 (preprint 3.5).

## What is formalized

* `Polyfold.IsStrongBundleIso.fiberCLM_comp_deriv_zero_eq_germ`: for an sc¹-germ `k` (derivative
  family `Dk` on a germ `G_k ⊆ U`) with `k(0) = 0` and `(Ψ(u, k(u)))₂ = h(ψ(u))` near `0`,
  `Γ(0) ∘ Dk(0) = Dh(0) ∘ Dψ(0)`.  The old proof's step "`u ↦ (Ψ(u, k(u)))₂` is sc-smooth on `U`"
  is replaced by the germ chain rule (`IsStrongBundleMap.fiber_comp_isSc1GermWith`,
  `fiberCompDeriv_zero_eq`), and the two derivative families are compared on the germ
  `G_k ∩ ψ⁻¹(G_h)`.
* `Polyfold.IsStrongBundleIso.deriv_zero_isFredholm_germ` (index `dim Pn − dim Q` of the given
  conjugation) and `Polyfold.IsConjugateToBasicGerm.scDeriv_isFredholm` (the germ version of
  `IsConjugateToBasicGerm.scDeriv_isFredholm_wholeChart`): `Dk(0)` is Fredholm of index `n − N`.
* `Polyfold.IsSc1GermWith.sub_toBase_shift`: `g − ιs` is an sc¹-germ on `G ∩ G_s` with the family
  `Dg − ι ∘ Ds`, and `Polyfold.IsSc1GermWith.deriv_zero_eq_add_scPlus`: `Dg(0) = Dk(0) + ιDs(0)`
  with `ιDs(0)` the sc-operator underlying the sc⁺-operator `Ds(0)`.
* `Polyfold.proposition_3_6_5_local` (the germ version of `proposition_3_6_5_local_wholeChart`) and
  `Polyfold.proposition_3_6_5_preprint` (the germ version of `proposition_3_6_5_wholeChart`, hypothesis
  `B.IsScFredholmGerm f x₀`): in the chart of Definition 3.1.11 (preprint 3.11), for **every** derivative family
  `Dg` of the filling germ `g` on a germ `G ⊆ U`, `Dg(0)` and `Tf(0) = Dg(0)|_{T₀O} : T₀O → K₀`
  are Fredholm with `ind Tf(0) = ind Dg(0) = n − N`.  `proposition_3_6_5_preprint` exposes the filling
  germ (`IsFillingGerm`), the germ `G`, the family `Dg` with `IsSc1GermWith G g Dg` and the
  statements about `Dg(0)` in place of the old `IsFilledVersion` and `scDeriv c.U g 0`.
  `Polyfold.proposition_3_6_5_local_of_germ`: the old whole-chart statement re-derived from the
  germ one (`G = G_s = ofSet U`).  `Polyfold.StrongBundleChart.zero_data`: `0 ∈ O`, `f̂(0) = 0` and
  `f̂` a section of `K → O` in a chart centred at a zero (the three lines repeated in every
  section-level proof).

## What the text leaves implicit, and the choices made

* **Which `Dg(0)`.**  For a germ, `scDeriv U g 0` is a junk value; the linearization is `Dg(0)`
  for a derivative family `Dg` on some germ `G ⊆ U`.  It does not depend on the choice
  (`IsSc1GermWith.eq_of_uniqueDiffWithinAt` on `G ∩ G'`), and the local statements hold for every
  such family; the section-level statement takes `G` from the filling and `Dg = scDerivGerm G g`.
* **No hypothesis on `G_s` beyond being a germ.**  `g − ιs` lives on `G ∩ G_s ⊆ G ⊆ U`; the
  inclusion `(G_s)₀ ⊆ U` of `IsScPlusGerm` is not used.  Of `s` only its sc¹-germ property into
  `F¹` is used (for `Ds(0)` to be an sc⁺-operator, `IsSc1GermWith.isScOperator_deriv_zero`).
* **The level-`0` Fredholm property only**, with the index, as in `FredholmGermLinearization.lean`;
  the sc form is `FredholmGermLinearizationScG.lean`.
-/

open Set Filter Topology Function Module ContinuousLinearMap

noncomputable section

namespace Polyfold

variable {E F : ScBanach}

/-! ### The derivative of a germ conjugated to a basic germ -/

section Conjugate

variable {C U : Set (E 0)} {Gk : ScNbhdGerm E C} {k : E 0 → F 0} {Dk : E 1 → E 0 →L[ℝ] F 0}
  {Pn Q : Type} [NormedAddCommGroup Pn] [NormedSpace ℝ Pn] [FiniteDimensional ℝ Pn]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q] {W : ScBanach} {Ct : Set Pn}
  {U' : Set ((ScBanach.paramProd Pn W) 0)}
  {Ψ : E 0 × F 0 → (ScBanach.paramProd Pn W) 0 × (ScBanach.paramProd Q W) 0}
  {Ψ' : (ScBanach.paramProd Pn W) 0 × (ScBanach.paramProd Q W) 0 → E 0 × F 0}
  {G : ScNbhdGerm (ScBanach.paramProd Pn W) (Ct ×ˢ univ)} {h : Pn × W 0 → Q × W 0}
  {Bc : Pn × W 0 → W 0}

/-- **`Γ(0) ∘ Dk(0) = Dh(0) ∘ Dψ(0)` for a germ `k`** (the identity behind Proposition 3.6.5 (preprint 3.52), germ
reading, phase 2): if `k` is an sc¹-germ on `G_k` (`(G_k)₀ ⊆ U`) with derivative family `Dk`,
`k(0) = 0`, and `(Ψ(u, k(u)))₂ = h(ψ(u))` for `u ∈ U` near `0`, with `Ψ` a strong bundle
isomorphism covering `ψ`, `ψ(0) = 0`, and `h` a basic germ on `G`, then
`Γ(0) ∘ Dk(0) = Dh(0) ∘ Dψ(0)`.  The left side is the derivative at `0` of the germ
`u ↦ (Ψ(u, k(u)))₂` (germ chain rule, `fiberCompDeriv_zero_eq`), the right side that of `h ∘ ψ`
on `ψ⁻¹(G)`; both are derivative families of the same map on `G_k ∩ ψ⁻¹(G)` near `0`. -/
theorem IsStrongBundleIso.fiberCLM_comp_deriv_zero_eq_germ (hU : IsRelOpenInQuadrant E C U)
    (h0 : (0 : E 0) ∈ U) (hGk : Gk.U 0 ⊆ U) (hk : IsSc1GermWith Gk k Dk) (hk0 : k 0 = 0)
    (hU' : IsRelOpenInQuadrant (ScBanach.paramProd Pn W) (Ct ×ˢ univ) U')
    (hΨ : IsStrongBundleIso U U' Ψ Ψ') (hψ0 : IsStrongBundleMap.base Ψ 0 = 0)
    (hh : IsBasicGerm Ct G h Bc)
    (hev : ∀ᶠ u in 𝓝 (0 : E 0), u ∈ U → (Ψ (u, k u)).2 = h (IsStrongBundleMap.base Ψ u)) :
    (hΨ.toFun.fiberCLM h0).comp (Dk 0) =
      (scDerivGerm (F := ScBanach.paramProd Q W) G h 0).comp
        (scDeriv U (IsStrongBundleMap.base Ψ) 0) := by
  have hC : IsQuadrantLike E C := hU.isPartialQuadrant.isQuadrantLike
  have hC' : IsQuadrantLike (ScBanach.paramProd Pn W) (Ct ×ˢ univ) :=
    hU'.isPartialQuadrant.isQuadrantLike
  have hU'C : U' ⊆ Ct ×ˢ univ := hU'.subset_quadrant
  set ψ := IsStrongBundleMap.base Ψ with hψdef
  have hψsm : IsScSmooth U ψ := hΨ.toFun.base_isScSmooth hU
  have hψU' : MapsTo ψ U U' := fun u hu => hΨ.toFun.base_mem hu
  have hlevψ : levelMap ψ 1 (0 : E 1) = 0 := levelMap_one_zero_of_zero hψ0
  -- the germ `u ↦ (Ψ(u, k(u)))₂` on `G_k` and its derivative at `0`
  have hfib := hΨ.toFun.fiber_comp_isSc1GermWith hU hGk hk
  have hfib0 := fiberCompDeriv_zero_eq hU h0 hΨ.toFun hk0 Dk
  -- the germ `h ∘ ψ` on `ψ⁻¹(G)`, inside the neighbourhood `N₁` of the conjugation identity
  obtain ⟨N₁, hN₁sub, hN₁open, h0N₁⟩ := mem_nhds_iff.1 hev
  have hU₁ : IsRelOpenInQuadrant E C (U ∩ N₁) := hU.inter_isOpen hN₁open
  have h0₁ : (0 : E 0) ∈ U ∩ N₁ := ⟨h0, h0N₁⟩
  set G₀ := ScNbhdGerm.ofSet hU₁.relOpen h0₁ with hG₀
  have hψG₀ : IsSc0Germ (F := ScBanach.paramProd Pn W) G₀ ψ :=
    ((hψsm.of_subset hU₁.isScDomain inter_subset_left).isScSmoothGerm hC hU₁.relOpen h0₁) 0
  have hψC' : MapsTo ψ (G₀.U 0) (Ct ×ˢ univ) := fun u hu => hU'C (hψU' hu.1)
  set G₁ := G₀.preimage G hψG₀ hψ0 hψC' with hG₁
  have hG₁sub : ∀ m, G₁.U m ⊆ (ScNbhdGerm.ofSet hU.relOpen h0).U m := fun m x hx =>
    E.lvlSet_mono inter_subset_left m (G₀.preimage_subset G hψG₀ hψ0 hψC' m hx)
  have hhG : IsSc1GermWith (F := ScBanach.paramProd Q W) G h
      (scDerivGerm (F := ScBanach.paramProd Q W) G h) :=
    (hh.isScSmooth 1).1.isSc1GermWith_scDerivGerm
  have hψG₁ : IsSc1GermWith (F := ScBanach.paramProd Pn W) G₁ ψ (scDeriv U ψ) :=
    (hψsm.isSc1.isSc1GermWith_ofSet hU.relOpen h0).mono hG₁sub
  have hcomp : IsSc1GermWith (F := ScBanach.paramProd Q W) G₁ (h ∘ ψ)
      (fun x => (scDerivGerm (F := ScBanach.paramProd Q W) G h (levelMap ψ 1 x)).comp
        (scDeriv U ψ x)) :=
    hhG.comp (G.relOpenConvex hC' 1) hψG₁ (G₀.preimage_mapsToGerm G hψG₀ hψ0 hψC')
  -- both are derivative families of `u ↦ (Ψ(u, k(u)))₂` on `G₁ ∩ G_k`
  set G₂ := G₁.inter Gk with hG₂
  have h1 : IsSc1GermWith G₂ (fun u => (Ψ (u, k u)).2) (fiberCompDeriv U Ψ k Dk) :=
    hfib.mono (G₁.inter_subset_right Gk)
  have h2 : IsSc1GermWith G₂ (fun u => (Ψ (u, k u)).2)
      (fun x => (scDerivGerm (F := ScBanach.paramProd Q W) G h (levelMap ψ 1 x)).comp
        (scDeriv U ψ x)) :=
    (hcomp.mono (G₁.inter_subset_left Gk)).congr fun u hu => by
      have hu' : u ∈ U ∩ N₁ := G₀.preimage_subset G hψG₀ hψ0 hψC' 0 hu.1
      exact (hN₁sub hu'.2 hu'.1).symm
  have heq := h1.eq_of_uniqueDiffWithinAt h2 (G₂.zero_mem 1)
    (G₂.uniqueDiffWithinAt hC 1 (G₂.zero_mem 1))
  rw [hfib0, hlevψ] at heq
  exact heq

/-- **The derivative at `0` of a germ conjugated to a basic germ is Fredholm of index
`dim Pn − dim Q`** (Propositions 3.1.10 and 3.6.5 (preprint 3.10 and 3.52), germ reading, phase 2): `k` an sc¹-germ on
`G_k ⊆ U` with derivative family `Dk`, `k(0) = 0`, conjugated by `Ψ` to the basic germ `h` on `G`
(`h : O(C̃ ⊕ W, 0) → ℝᴺ ⊕ W`, `C̃ ⊆ Pn`, `ℝᴺ = Q`).  Then `Dk(0) = Γ(0)⁻¹ Dh(0) Dψ(0)` is Fredholm
of index `ind Dh(0) = dim Pn − dim Q`.  The germ version of
`ConjugationData.scDeriv_isFredholm_index_wholeChart` with the data unpacked. -/
theorem IsStrongBundleIso.deriv_zero_isFredholm_germ (hU : IsRelOpenInQuadrant E C U)
    (h0 : (0 : E 0) ∈ U) (hGk : Gk.U 0 ⊆ U) (hk : IsSc1GermWith Gk k Dk) (hk0 : k 0 = 0)
    (hCt : IsPartialQuadrant (ScBanach.const Pn) Ct)
    (hU' : IsRelOpenInQuadrant (ScBanach.paramProd Pn W) (Ct ×ˢ univ) U')
    (hΨ : IsStrongBundleIso U U' Ψ Ψ') (hψ0 : IsStrongBundleMap.base Ψ 0 = 0)
    (hh : IsBasicGerm Ct G h Bc)
    (hev : ∀ᶠ u in 𝓝 (0 : E 0), u ∈ U → (Ψ (u, k u)).2 = h (IsStrongBundleMap.base Ψ u)) :
    IsFredholm (Dk 0) ∧ fredholmIndex (Dk 0) = finrank ℝ Pn - finrank ℝ Q := by
  have h01 : (0 : E 1) ∈ E.lvlSet U 1 := by rw [ScBanach.mem_lvlSet, map_zero]; exact h0
  have h0U' : (0 : (ScBanach.paramProd Pn W) 0) ∈ U' := hψ0 ▸ hΨ.toFun.base_mem h0
  have h01' : (0 : (ScBanach.paramProd Pn W) 1) ∈ (ScBanach.paramProd Pn W).lvlSet U' 1 := by
    rw [ScBanach.mem_lvlSet, map_zero]; exact h0U'
  set ψ := IsStrongBundleMap.base Ψ with hψdef
  set ψ' := IsStrongBundleMap.base Ψ' with hψ'def
  have hψψ' : ∀ u ∈ U, ψ' (ψ u) = u := fun u hu => hΨ.base_base hu
  have hψ'ψ : ∀ u' ∈ U', ψ (ψ' u') = u' := fun u' hu' => hΨ.base_base' hu'
  have hψ'0 : ψ' 0 = 0 := hΨ.base_zero' h0 hψ0
  have hψsm : IsScSmooth U ψ := hΨ.toFun.base_isScSmooth hU
  have hψ'sm : IsScSmooth U' ψ' := hΨ.invFun.base_isScSmooth hU'
  have hψU' : MapsTo ψ U U' := fun u hu => hΨ.toFun.base_mem hu
  have hψ'U : MapsTo ψ' U' U := fun u hu => hΨ.invFun.base_mem hu
  set Dψ := scDeriv U ψ 0 with hDψ
  set Dψ' := scDeriv U' ψ' 0 with hDψ'
  set Dh := scDerivGerm (F := ScBanach.paramProd Q W) G h 0 with hDh
  set Γ := hΨ.toFun.fiberCLM h0 with hΓ
  set Γ' := hΨ.invFun.fiberCLM h0U' with hΓ'
  -- (a) `Dh(0)` is Fredholm of index `n − N`
  obtain ⟨hDhF, hDhind⟩ := proposition_3_1_10_basic_level_zero hCt hh
  -- (b) `Γ(0)Dk(0) = Dh(0)Dψ(0)`
  have hkey : Γ.comp (Dk 0) = Dh.comp Dψ :=
    hΨ.fiberCLM_comp_deriv_zero_eq_germ hU h0 hGk hk hk0 hU' hψ0 hh hev
  -- (c) `Dψ(0)` and `Γ(0)` are isomorphisms
  have hlevψ : levelMap ψ 1 (0 : E 1) = 0 := levelMap_one_zero_of_zero hψ0
  have hlevψ' : levelMap ψ' 1 (0 : (ScBanach.paramProd Pn W) 1) = 0 :=
    levelMap_one_zero_of_zero hψ'0
  have hψψ'D : ∀ x, Dψ' (Dψ x) = x := fun x => by
    have := scDeriv_comp_eq_self hU hU' hψsm.isSc1 hψ'sm.isSc1 hψU' hψψ' h01 x
    rwa [hlevψ] at this
  have hψ'ψD : ∀ x, Dψ (Dψ' x) = x := fun x => by
    have := scDeriv_comp_eq_self hU' hU hψ'sm.isSc1 hψsm.isSc1 hψ'U hψ'ψ h01' x
    rwa [hlevψ'] at this
  set e₁ : E 0 ≃L[ℝ] (ScBanach.paramProd Pn W) 0 :=
    ContinuousLinearEquiv.equivOfInverse Dψ Dψ' hψψ'D hψ'ψD with he₁
  have hΓΓ' : ∀ y, Γ (Γ' y) = y := fun y => by
    simp only [hΓ, hΓ']
    have h1 : Ψ' (0, y) = (ψ' 0, (Ψ' (0, y)).2) := hΨ.invFun.apply_eq h0U' y
    rw [hψ'0] at h1
    have h2 := congrArg Prod.snd (hΨ.right_inv (0, y) ⟨h0U', mem_univ _⟩)
    rw [h1] at h2
    exact h2
  have hΓ'Γ : ∀ y, Γ' (Γ y) = y := fun y => by
    simp only [hΓ, hΓ']
    have h1 : Ψ (0, y) = (ψ 0, (Ψ (0, y)).2) := hΨ.toFun.apply_eq h0 y
    rw [hψ0] at h1
    have h2 := congrArg Prod.snd (hΨ.left_inv (0, y) ⟨h0, mem_univ _⟩)
    rw [h1] at h2
    exact h2
  set e₂ : (ScBanach.paramProd Q W) 0 ≃L[ℝ] F 0 :=
    ContinuousLinearEquiv.equivOfInverse Γ' Γ hΓΓ' hΓ'Γ with he₂
  -- (d) `Dk(0) = Γ(0)⁻¹ Dh(0) Dψ(0)`
  have hDk_eq : Dk 0 = (e₂ : (ScBanach.paramProd Q W) 0 →L[ℝ] F 0).comp
      (Dh.comp (e₁ : E 0 →L[ℝ] (ScBanach.paramProd Pn W) 0)) := by
    ext x
    have := congrArg (fun T : E 0 →L[ℝ] (ScBanach.paramProd Q W) 0 => Γ' (T x)) hkey
    simp only [ContinuousLinearMap.comp_apply] at this
    rw [hΓ'Γ] at this
    exact this
  obtain ⟨hF, hind⟩ := isFredholm_equiv_comp_equiv hDhF e₁ e₂
  rw [← hDk_eq] at hF hind
  exact ⟨hF, by rw [hind, hDhind]⟩

end Conjugate

section ConjugateExists

variable {C U : Set (E 0)} {Gk : ScNbhdGerm E C} {k : E 0 → F 0} {Dk : E 1 → E 0 →L[ℝ] F 0}

/-- **The germ version of `IsConjugateToBasicGerm.scDeriv_isFredholm_wholeChart`** (Proposition 3.6.5 (preprint 3.52), germ
reading, phase 2): for `k` an sc¹-germ on a germ `G_k ⊆ U` with derivative family `Dk`, `k(0) = 0`
and `k` conjugated to a basic germ, `Dk(0)` is Fredholm (level `0`) of index `n − N`.  The old
proof's step "`k` sc-smooth on `U`" is replaced by the germ chain rule
(`IsStrongBundleIso.fiberCLM_comp_deriv_zero_eq_germ`). -/
theorem IsConjugateToBasicGerm.scDeriv_isFredholm (hU : IsRelOpenInQuadrant E C U)
    (h0 : (0 : E 0) ∈ U) (hGk : Gk.U 0 ⊆ U) (hk : IsSc1GermWith Gk k Dk) (hk0 : k 0 = 0)
    (hconj : IsConjugateToBasicGerm U k) :
    IsFredholm (Dk 0) ∧ ∃ n N : ℕ, fredholmIndex (Dk 0) = n - N := by
  obtain ⟨Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, U', Ψ, Ψ', G, h, Bc, hCt, hU', hΨ, hψ0, -, hh,
    hev⟩ := hconj
  obtain ⟨hF, hind⟩ := hΨ.deriv_zero_isFredholm_germ hU h0 hGk hk hk0 hCt hU' hψ0 hh hev
  exact ⟨hF, finrank ℝ Pn, finrank ℝ Q, hind⟩

end ConjugateExists

/-! ### `g − ιs` and `Dg(0) = D(g − ιs)(0) + ιDs(0)` -/

section SubShift

variable {C : Set (E 0)} {G Gs : ScNbhdGerm E C} {g : E 0 → F 0} {s : E 0 → F 1}
  {Dg : E 1 → E 0 →L[ℝ] F 0} {Ds : E 1 → E 0 →L[ℝ] F.shift 0}

/-- **`g − ιs` is an sc¹-germ on `G ∩ G_s`** with the derivative family `Dg − ι ∘ Ds`, for `g` an
sc¹-germ on `G` and `s` an sc¹-germ into `F¹` on `G_s` (the sum rule and the sc-operator
`ι : F¹ → F`; germ reading of Definition 3.1.11 (preprint 3.11), phase 2). -/
theorem IsSc1GermWith.sub_toBase_shift (hg : IsSc1GermWith G g Dg)
    (hs : IsSc1GermWith (F := F.shift) Gs s Ds) :
    IsSc1GermWith (G.inter Gs) (fun u => g u - F.toBase 1 (s u))
      fun x => Dg x - (F.toBase 1).comp (Ds x) :=
  (hg.sub_inter (hs.operator_comp F.shiftIncl)).congr fun _ _ => rfl

/-- **`Dg(0) = D(g − ιs)(0) + ιDs(0)`** with `ιDs(0)` the sc-operator underlying the
sc⁺-operator `Ds(0)` (`IsSc1GermWith.isScOperator_deriv_zero`): the decomposition behind
Proposition 1.1.11 (preprint 1.10) in the proof of Proposition 3.6.5 (preprint 3.52) (germ reading, phase 2). -/
theorem IsSc1GermWith.deriv_zero_eq_add_scPlus (hs : IsSc1GermWith (F := F.shift) Gs s Ds) :
    Dg 0 = (Dg 0 - (F.toBase 1).comp (Ds 0)) +
      ScPlus.toScOperator hs.isScOperator_deriv_zero.toScOperator 0 := by
  ext x
  rw [add_apply, ScPlus.toScOperator_apply,
    IsScOperator.toScOperator_zero, sub_apply,
    ContinuousLinearMap.comp_apply]
  change _ = _ - F.toBase 1 (Ds 0 x) + F.toBase 1 (Ds 0 x)
  abel

end SubShift

/-! ### Proposition 3.6.5 (preprint 3.52), germ reading -/

section Prop352

variable {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

open StrongRetr

/-- **Proposition 3.6.5 (preprint 3.52) in the chart of Definition 3.1.11 (preprint 3.11), germ reading** (phase 2; the germ version
of `proposition_3_6_5_local_wholeChart`): let `g` be a filling germ of the principal part `f̂` of a section at
a zero (`f̂(0) = 0`), with a derivative family `Dg` on a germ `G ⊆ U`, `s` an sc¹-germ into `F¹`
on a germ `G_s` (derivative family `Ds`) with `s(0) = g(0)`, and `g − s` conjugated to a basic
germ.  Then `Dg(0) : E → F` is a Fredholm operator (on level `0`) of index `n − N`, and so is
`Tf(0) = Dg(0)|_{T₀O} : T₀O → K₀` (Propositions 3.1.10, 1.1.11 and 3.1.5 (preprint 3.10, 1.10 and 3.5)). -/
theorem proposition_3_6_5_local (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U) (h0O : (0 : E 0) ∈ r R '' U)
    {fb g : E 0 → F 0} (hfill : IsFillingGerm hU hR h0 fb g) (hfb0 : fb 0 = 0)
    (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ)) {G : ScNbhdGerm E C} (hG : G.U 0 ⊆ U)
    {Dg : E 1 → E 0 →L[ℝ] F 0} (hg : IsSc1GermWith G g Dg) {Gs : ScNbhdGerm E C}
    {s : E 0 → F 1} {Ds : E 1 → E 0 →L[ℝ] F.shift 0} (hs : IsSc1GermWith (F := F.shift) Gs s Ds)
    (hs0 : F.toBase 1 (s 0) = g 0)
    (hconj : IsConjugateToBasicGerm U fun u => g u - F.toBase 1 (s u)) :
    ∃ (h1 : ∀ x, ρCLM hR h0 (Dg 0 (scDeriv U (r R) 0 x)) = Dg 0 (scDeriv U (r R) 0 x))
      (n N : ℕ),
      IsFredholm (Dg 0) ∧ fredholmIndex (Dg 0) = n - N ∧
      IsFredholm (fillerRestrict (scDeriv U (r R) 0) (ρCLM hR h0) (Dg 0) h1) ∧
      fredholmIndex (fillerRestrict (scDeriv U (r R) 0) (ρCLM hR h0) (Dg 0) h1) = n - N := by
  have hg0 : g 0 = 0 := by rw [← hfill.eq_on.self_of_nhds h0O, hfb0]
  have hk := hg.sub_toBase_shift hs
  have hk0 : (fun u => g u - F.toBase 1 (s u)) 0 = 0 := by
    change g 0 - F.toBase 1 (s 0) = 0
    rw [hs0, hg0, sub_self]
  obtain ⟨hDkF, n, N, hDkind⟩ :=
    hconj.scDeriv_isFredholm hU h0 ((G.inter_subset_left Gs 0).trans hG) hk hk0
  -- `Dg(0) = Dk(0) + ιDs(0)`, with `ιDs(0)` compact (an sc⁺-operator)
  set S : ScPlus E F := hs.isScOperator_deriv_zero.toScOperator with hS
  have hDg : Dg 0 = (Dg 0 - (F.toBase 1).comp (Ds 0)) + S.toScOperator 0 :=
    hs.deriv_zero_eq_add_scPlus
  have hcompact : IsCompactOperator (S.toScOperator 0) := S.isCompactOperator 0
  have hDgF : IsFredholm (Dg 0) := by
    rw [hDg]; exact isFredholm_add_isCompactOperator hDkF hcompact
  have hDgind : fredholmIndex (Dg 0) = n - N := by
    rw [hDg, fredholmIndex_add_isCompactOperator hDkF hcompact, hDkind]
  -- Proposition 3.1.5 (preprint 3.5)
  obtain ⟨h1, -, hFiff, hindeq⟩ := hfill.proposition_3_1_5 hU hR h0 hg0 h0O hfK hG hg
  exact ⟨h1, n, N, hDgF, hDgind, hFiff.2 hDgF, by rw [hindeq, hDgind]⟩

/-- **The whole-chart statement `proposition_3_6_5_local_wholeChart` is the special case** `G = G_s = ofSet U`,
`Dg = scDeriv U g`, `Ds = scDeriv U s` of `proposition_3_6_5_local` (germ reading, phase 2):
the old statement re-derived from the germ one (`IsFilledVersion.isFillingGerm`,
`IsSc1.isSc1GermWith_ofSet`). -/
theorem proposition_3_6_5_local_of_germ (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U) (h0O : (0 : E 0) ∈ r R '' U)
    {fb g : E 0 → F 0} (hfill : IsFilledVersion hU hR h0 fb g) (hfb0 : fb 0 = 0)
    (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ)) {s : E 0 → F 1}
    (hs : IsScSmooth (F := F.shift) U s) (hs0 : F.toBase 1 (s 0) = g 0)
    (hconj : IsConjugateToBasicGerm U fun u => g u - F.toBase 1 (s u)) :
    ∃ (h1 : ∀ x, ρCLM hR h0 (scDeriv U g 0 (scDeriv U (r R) 0 x)) =
        scDeriv U g 0 (scDeriv U (r R) 0 x)) (n N : ℕ),
      IsFredholm (scDeriv U g 0) ∧ fredholmIndex (scDeriv U g 0) = n - N ∧
      IsFredholm (fillerRestrict (scDeriv U (r R) 0) (ρCLM hR h0) (scDeriv U g 0) h1) ∧
      fredholmIndex (fillerRestrict (scDeriv U (r R) 0) (ρCLM hR h0) (scDeriv U g 0) h1) =
        n - N :=
  proposition_3_6_5_local hU hR h0 h0O (hfill.isFillingGerm hU hR h0) hfb0 hfK
    (G := ScNbhdGerm.ofSet hU.relOpen h0) (fun _ hu => hu)
    (hfill.isScSmooth.isSc1.isSc1GermWith_ofSet hU.relOpen h0)
    (hs.isSc1.isSc1GermWith_ofSet (F := F.shift) hU.relOpen h0) hs0 hconj

end Prop352

/-! ### Proposition 3.6.5 (preprint 3.52) for sections of strong bundles, germ reading -/

section Bundle

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

open StrongRetr

omit [T2Space Y] [ParacompactSpace Y] in
/-- The chart identities at a zero `x₀` of a section in a chart centred at `x₀`: `0 ∈ O`,
`f̂(0) = 0`, and `f̂` is a section of `K → O`. -/
theorem StrongBundleChart.zero_data (hf : IsSection P f) {c : StrongBundleChart PX P} {x₀ : X}
    (hxV : x₀ ∈ c.φ.source) (hφ0 : c.φ x₀ = 0) (hx₀ : IsZeroAt P f x₀) :
    (0 : c.φ.model.E 0) ∈ r c.R '' c.U ∧ c.principal f 0 = 0 ∧
      ∀ x ∈ r c.R '' c.U, (x, c.principal f x) ∈ c.R '' (c.U ×ˢ univ) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [c.r_image, ← hφ0]; exact c.φ.mapsTo_model x₀ hxV
  · have := (c.isZeroAt_iff hf hxV).1 hx₀
    rwa [hφ0] at this
  · intro x hx
    rw [c.r_image] at hx
    rw [← c.apply_section hf hx]
    change c (f (c.φ.symm x)) ∈ c.K
    rw [← c.image_source]
    exact ⟨_, c.mem_source_of_proj (by rw [hf]; exact c.φ.symm_mapsTo hx), rfl⟩

/-- **Proposition 3.6.5 (preprint 3.52), germ reading** (phase 2; the germ version of `proposition_3_6_5_wholeChart`, with the
hypothesis `B.IsScFredholmGerm f x₀` of Definition 3.1.11 (preprint 3.11) in the text's germ reading): let `f` be a
section of the strong bundle `P : Y → X` with `(f, x₀)` an sc-Fredholm germ and `f(x₀) = 0`.  Then
in the strong bundle chart of Definition 3.1.11 (preprint 3.11) centred at `x₀`, with the filling germ `g` of the
principal part `f̂` on the germ `G ⊆ U` and its derivative family `Dg`, the linearization
`Tf(x₀) = Dg(0)|_{T₀O} : T₀O → K₀` (`fillerRestrict`) is a Fredholm operator of index `n − N`, and
so is `Dg(0) : E → F`.  (Level `0`, in the chart; `Dg(0)` is the same for every derivative family
of `g` on every germ, `IsSc1GermWith.eq_of_uniqueDiffWithinAt`.) -/
theorem proposition_3_6_5_preprint (hf : IsSection P f) {x₀ : X} (hg : B.IsScFredholmGerm f x₀)
    (hx₀ : IsZeroAt P f x₀) :
    ∃ (c : StrongBundleChart PX P) (_ : B.IsChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
      (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0)
      (_ : IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g)
      (G : ScNbhdGerm c.φ.model.E c.φ.model.C) (_ : G.U 0 ⊆ c.U) (_ : IsScSmoothGerm G g)
      (Dg : c.φ.model.E 1 → c.φ.model.E 0 →L[ℝ] c.F 0) (_ : IsSc1GermWith G g Dg)
      (h1 : ∀ x, ρCLM c.isRetraction h0 (Dg 0 (scDeriv c.U (r c.R) 0 x)) =
        Dg 0 (scDeriv c.U (r c.R) 0 x)) (n N : ℕ),
      IsFredholm (Dg 0) ∧ fredholmIndex (Dg 0) = n - N ∧
      IsFredholm (fillerRestrict (scDeriv c.U (r c.R) 0) (ρCLM c.isRetraction h0) (Dg 0) h1) ∧
      fredholmIndex (fillerRestrict (scDeriv c.U (r c.R) 0) (ρCLM c.isRetraction h0) (Dg 0) h1) =
        n - N := by
  obtain ⟨-, c, hc, hxV, hφ0, h0U, g, s, hfill, ⟨Gs, -, hs⟩, hs0, hconj⟩ := hg
  obtain ⟨h0O, hfb0, hfK⟩ := c.zero_data hf hxV hφ0 hx₀
  obtain ⟨G, hGU, hgG, -⟩ := hfill.germ
  have hg1 := (hgG 1).1.isSc1GermWith_scDerivGerm
  have hs1 := (hs 1).1.isSc1GermWith_scDerivGerm
  obtain ⟨h1, n, N, hDgF, hDgind, hTF, hTind⟩ :=
    proposition_3_6_5_local c.relOpen c.isRetraction h0U h0O hfill hfb0 hfK hGU hg1 hs1 hs0
      hconj
  exact ⟨c, hc, hxV, hφ0, h0U, g, hfill, G, hGU, hgG, _, hg1, h1, n, N, hDgF, hDgind, hTF, hTind⟩

end Bundle

end Polyfold
