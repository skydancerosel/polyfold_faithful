import Polyfold.Chapter3.TameGermsG
import Polyfold.Chapter3.FredholmGermLinearizationSc
import Polyfold.Chapter3.FredholmGermIndexG

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.6,
**Proposition 3.6.5 (preprint 3.52) in sc form**, the sc form of **Proposition 3.1.5 (preprint 3.5)**, and the clause
"**`f'(x₀)` is sc-Fredholm**" of **Theorem 3.1.22 (preprint 3.19)**, **in the text's germ reading of Definition 3.1.11 (preprint 3.11)**
(phase 2): the filling `g` and the sc⁺-section `s` are sc-smooth germs.

# The linearization of an sc-Fredholm germ is sc-Fredholm, germ reading

## What is formalized

* `Polyfold.ConjugationData.scDeriv_isRegularizing`,
  `Polyfold.ConjugationData.scDeriv_isScFredholm` (germ versions of
  `ConjugationData.scDeriv_isRegularizing_wholeChart`, `ConjugationData.scDeriv_isScFredholm_wholeChart`): for `k` an
  sc¹-germ on `G_k ⊆ U` (derivative family `Dk`) with `k(0) = 0` conjugated to a basic germ,
  `Dk(0)` is an sc-operator (`IsSc1GermWith.isScOperator_deriv_zero`), regularizing, and
  sc-Fredholm of index `dim Pn − dim Q`.
* `Polyfold.IsFillingGerm.proposition_3_1_5_sc` (the germ version of `IsFillerOf.proposition_3_1_5_sc`):
  for a filling germ `g` with `g(0) = 0` and `Dg(0)` an sc-Fredholm sc-operator,
  `Tf(0) = Dg(0)|_{T₀O} : T₀O → K₀` is sc-Fredholm of index `ind Dg(0)` on every level.
* `Polyfold.proposition_3_6_5_local_sc`, `Polyfold.proposition_3_6_5_sc` (hypothesis
  `B.IsScFredholmGerm f x₀`): `Dg(0)` and `Tf(x₀)` are sc-Fredholm, of index `dim d.Pn − dim d.Q`
  on every level for every conjugation `d`.
* `Polyfold.theorem_3_1_22_linearization_sc_local_germ` and
  `Polyfold.theorem_3_1_22_linearization_sc`: the same, and `Tf(x₀)` onto on every level, at a
  zero where `Tf(x₀)` is onto on level `0` (condition (1) of Definition 3.6.6 (preprint 3.53), germ reading).

## What the text leaves implicit, and the choices made

* As in `FredholmGermLinearizationSc.lean`; the derivatives at `0` are the values `Dg(0)`,
  `Ds(0)`, `Dk(0)` of derivative families of the germs (unique), never a junk `scDeriv`.
* **The hypothesis of Theorem 3.1.22 (preprint 3.19) here is condition (1) of Definition 3.6.6 (preprint 3.53) only** ("`Tf̃(0)` onto",
  in the chart of the germ data), stated inline in `theorem_3_1_22_linearization_sc`: it is
  the `surj` field of the germ good position `IsGoodPositionAtGerm` (`GoodPositionGermG.lean`,
  written at the same time), so `StrongBundle.IsGoodPositionGerm f x₀` implies it; the kernel
  condition (2) is not used for this clause, as in `theorem_3_1_22_linearization_sc_wholeChart`.
-/

open Set Filter Topology Function Module ContinuousLinearMap

noncomputable section

namespace Polyfold

variable {E F : ScBanach}

/-! ### The derivative of a germ conjugated to a basic germ is sc-Fredholm -/

section Conjugate

variable {C U : Set (E 0)} {Gk : ScNbhdGerm E C} {k : E 0 → F 0} {Dk : E 1 → E 0 →L[ℝ] F 0}

/-- **The derivative at `0` of a germ conjugated to a basic germ is regularizing** (germ reading,
phase 2; the germ version of `ConjugationData.scDeriv_isRegularizing_wholeChart`): `Dk(0)e ∈ F_m` implies
`e ∈ E_m`.  From `Γ(0)Dk(0) = Dh(0)Dψ(0)` (`IsStrongBundleIso.fiberCLM_comp_deriv_zero_eq_germ`),
`Γ(0)` preserving the levels, `Dh(0)` regularizing and `Dψ(0)⁻¹ = Dψ'(0)` an sc-operator. -/
theorem ConjugationData.scDeriv_isRegularizing (hU : IsRelOpenInQuadrant E C U)
    (h0 : (0 : E 0) ∈ U) (hGk : Gk.U 0 ⊆ U) (hk : IsSc1GermWith Gk k Dk) (hk0 : k 0 = 0)
    (d : ConjugationData U k) :
    ∀ (m : ℕ) (e : E 0), Dk 0 e ∈ range (F.toBase m) → e ∈ range (E.toBase m) := by
  obtain ⟨Pn, Q, W, Ct, U', Ψ, Ψ', G, h, Bc, hCt, hU', hΨ, hψ0, hG, hh, hev⟩ := d
  have h01 : (0 : E 1) ∈ E.lvlSet U 1 := by rw [ScBanach.mem_lvlSet, map_zero]; exact h0
  have h0U' : (0 : (ScBanach.paramProd Pn W) 0) ∈ U' := hψ0 ▸ hΨ.toFun.base_mem h0
  have h01' : (0 : (ScBanach.paramProd Pn W) 1) ∈ (ScBanach.paramProd Pn W).lvlSet U' 1 := by
    rw [ScBanach.mem_lvlSet, map_zero]; exact h0U'
  set ψ := IsStrongBundleMap.base Ψ with hψdef
  set ψ' := IsStrongBundleMap.base Ψ' with hψ'def
  have hψψ' : ∀ u ∈ U, ψ' (ψ u) = u := fun u hu => hΨ.base_base hu
  have hψsm : IsScSmooth U ψ := hΨ.toFun.base_isScSmooth hU
  have hψ'sm : IsScSmooth U' ψ' := hΨ.invFun.base_isScSmooth hU'
  have hψU' : MapsTo ψ U U' := fun u hu => hΨ.toFun.base_mem hu
  set Dψ := scDeriv U ψ 0 with hDψ
  set Dψ' := scDeriv U' ψ' 0 with hDψ'
  set Γ := hΨ.toFun.fiberCLM h0 with hΓ
  -- (a) `Dh(0)` is sc-Fredholm, hence regularizing
  obtain ⟨hDhop, hDhF, -⟩ := proposition_3_1_10_basic hCt hh
  -- (b) `Γ(0)Dk(0) = Dh(0)Dψ(0)`
  have hkey := hΨ.fiberCLM_comp_deriv_zero_eq_germ hU h0 hGk hk hk0 hU' hψ0 hh hev
  -- (c) `Dψ'(0)Dψ(0) = 1`, and `Dψ'(0)` is an sc-operator
  have hlevψ : levelMap ψ 1 (0 : E 1) = 0 := levelMap_one_zero_of_zero hψ0
  have hψψ'D : ∀ x, Dψ' (Dψ x) = x := fun x => by
    have := scDeriv_comp_eq_self hU hU' hψsm.isSc1 hψ'sm.isSc1 hψU' hψψ' h01 x
    rwa [hlevψ] at this
  have hDψ'op : IsScOperator Dψ' :=
    hψ'sm.isSc1.isSc1With_scDeriv.scOperator_deriv h01'
      (ScBanach.paramProd Pn W).zero_mem_smoothLvl_one
  -- (d) the regularity
  intro m e he
  have hΓe : Γ (Dk 0 e) ∈ range ((ScBanach.paramProd Q W).toBase m) := by
    obtain ⟨y, hy⟩ := he
    have := (hΨ.toFun.preserves_filtration m m (Nat.le_succ m) 0 h0 ⟨0, map_zero _⟩ (Dk 0 e)
      ⟨y, hy⟩).2
    rwa [hΓ, IsStrongBundleMap.fiberCLM_apply]
  have hDhe : hDhop.toScOperator 0 (Dψ e) ∈ range ((ScBanach.paramProd Q W).toBase m) := by
    rw [hDhop.toScOperator_zero]
    have := congrArg (fun T : E 0 →L[ℝ] (ScBanach.paramProd Q W) 0 => T e) hkey
    simp only [ContinuousLinearMap.comp_apply] at this
    rw [← this]; exact hΓe
  obtain ⟨z, hz⟩ := hDhF.isRegularizing m (Dψ e) hDhe
  obtain ⟨Tm, hTm⟩ := hDψ'op m
  exact ⟨Tm z, by rw [hTm, hz, hψψ'D]⟩

/-- **The derivative at `0` of a germ conjugated to a basic germ is sc-Fredholm**, of index
`dim Pn − dim Q` (germ reading, phase 2; the germ version of
`ConjugationData.scDeriv_isScFredholm_wholeChart`): `Dk(0)` is an sc-operator (the derivative of an
sc¹-germ at the smooth point `0`), Fredholm on level `0` of index `n − N`
(`ConjugationData.scDeriv_isFredholm_index`) and regularizing; the criterion
`isScFredholm_of_isRegularizing`. -/
theorem ConjugationData.scDeriv_isScFredholm (hU : IsRelOpenInQuadrant E C U)
    (h0 : (0 : E 0) ∈ U) (hGk : Gk.U 0 ⊆ U) (hk : IsSc1GermWith Gk k Dk) (hk0 : k 0 = 0)
    (d : ConjugationData U k) :
    ∃ hop : IsScOperator (Dk 0), IsScFredholm hop.toScOperator ∧
      scIndex hop.toScOperator = finrank ℝ d.Pn - finrank ℝ d.Q := by
  have hop : IsScOperator (Dk 0) := hk.isScOperator_deriv_zero
  obtain ⟨hF, hind⟩ := d.scDeriv_isFredholm_index hU h0 hGk hk hk0
  refine ⟨hop, isScFredholm_of_isRegularizing ?_ ?_, ?_⟩
  · rw [hop.toScOperator_zero]; exact hF
  · intro m e he
    rw [hop.toScOperator_zero] at he
    exact d.scDeriv_isRegularizing hU h0 hGk hk hk0 m e he
  · rw [scIndex_eq_fredholmIndex, hop.toScOperator_zero, hind]

end Conjugate

/-! ### Proposition 3.1.5 (preprint 3.5) in sc form, germ reading -/

open StrongRetr

namespace IsFillingGerm

variable {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0} {hU : IsRelOpenInQuadrant E C U}
  {hR : IsStrongBundleRetraction U R} {h0 : (0 : E 0) ∈ U} {fb g : E 0 → F 0}
  (hfg : IsFillingGerm hU hR h0 fb g)

include hfg in
/-- **Proposition 3.1.5 (preprint 3.5), sc form, germ reading** (phase 2; the germ version of
`IsFillerOf.proposition_3_1_5_sc`): let `g` be a filling germ of `f` with `g(0) = 0` (`f` a section
of `K → O`, `0 ∈ O`), `Dg` a derivative family of `g` on a germ `G ⊆ U`, and let `Dg(0) : E → F`
be an sc-Fredholm sc-operator.  Then `T₀O = Dr(0)E` and `K₀ = ρ(0)F` are sc-subspaces, `Dg(0)`
maps `T₀O` into `K₀`, and `Tf(0) = Dg(0)|_{T₀O} : T₀O → K₀` is an sc-Fredholm operator, Fredholm
on every level of index `ind Dg(0)`. -/
theorem proposition_3_1_5_sc (hg0 : g 0 = 0) (h0O : (0 : E 0) ∈ r R '' U)
    (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ)) {G : ScNbhdGerm E C} (hG : G.U 0 ⊆ U)
    {Dg : E 1 → E 0 →L[ℝ] F 0} (hg : IsSc1GermWith G g Dg) (hDg : IsScOperator (Dg 0))
    (hDgF : IsScFredholm hDg.toScOperator) :
    ∃ (hT : E.IsScSubspace (rangeS (scDeriv U (r R) 0)))
      (hK : F.IsScSubspace (rangeS (ρCLM hR h0)))
      (hTK : ∀ x ∈ rangeS (scDeriv U (r R) 0), hDg.toScOperator 0 x ∈ rangeS (ρCLM hR h0)),
      IsScFredholm (hDg.toScOperator.restrict hT hK hTK) ∧
      (∀ x : (E.ofSubspace hT) 0, ((hDg.toScOperator.restrict hT hK hTK 0 x).1 : F 0) = Dg 0 x.1) ∧
      ∀ m, ((hDg.toScOperator.restrict hT hK hTK) m).IsFredholm ∧
        fredholmIndex ((hDg.toScOperator.restrict hT hK hTK) m) = fredholmIndex (Dg 0) := by
  obtain ⟨h1, -, hFiff, hindeq⟩ := hfg.proposition_3_1_5 hU hR h0 hg0 h0O hfK hG hg
  have hT := isScSubspace_range_scDeriv_r hU hR h0O
  have hK := isScSubspace_range_ρCLM hR h0 h0O
  have hTK : ∀ x ∈ rangeS (scDeriv U (r R) 0), hDg.toScOperator 0 x ∈ rangeS (ρCLM hR h0) := by
    rintro _ ⟨y, rfl⟩
    rw [hDg.toScOperator_zero]
    exact ⟨_, h1 y⟩
  have hDgF0 : (Dg 0).IsFredholm := by
    have := (hDgF.fredholmIndex_lvl 0).1
    rwa [hDg.toScOperator_zero] at this
  obtain ⟨hF0, hind0⟩ := hDg.toScOperator.isFredholm_restrict_zero hT hK hTK
    (L := fillerRestrict (scDeriv U (r R) 0) (ρCLM hR h0) (Dg 0) h1)
    (fun x => by rw [fillerRestrict_apply, hDg.toScOperator_zero]) (hFiff.2 hDgF0)
  obtain ⟨hsc, hlvl⟩ := hDgF.restrict hF0
  refine ⟨hT, hK, hTK, hsc, fun x => ?_, fun m => ?_⟩
  · change hDg.toScOperator 0 x.1 = _
    rw [hDg.toScOperator_zero]
  · rw [← hindeq, ← hind0]
    exact hlvl m

end IsFillingGerm

/-! ### Proposition 3.6.5 (preprint 3.52) in sc form, germ reading -/

section Prop352

variable {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

/-- **Proposition 3.6.5 (preprint 3.52) in the chart of Definition 3.1.11 (preprint 3.11), sc form, germ reading** (phase 2; the germ
version of `proposition_3_6_5_local_sc_wholeChart`): let `g` be a filling germ of the principal part `f̂` of a
section at a zero (`f̂(0) = 0`), `Dg` a derivative family of `g` on a germ `G ⊆ U`, `s` an sc¹-germ
into `F¹` on `G_s` (derivative family `Ds`) with `s(0) = g(0)`, and `d` conjugation data of
`g − s` to a basic germ.  Then `Dg(0) : E → F` is an **sc-Fredholm operator**, `T₀O = Dr(0)E` and
`K₀ = ρ(0)F` are sc-subspaces, and `Tf(0) = Dg(0)|_{T₀O} : T₀O → K₀` is an **sc-Fredholm
operator**; on every level both are Fredholm of index `n − N = dim d.Pn − dim d.Q`.  The text's
proof: `D(g − s)(0)` is sc-Fredholm (Proposition 3.1.10 (preprint 3.10)), `Dg(0)` by Proposition 1.1.11 (preprint 1.10) (`Ds(0)` is an
sc⁺-operator), `Tf(0)` by Proposition 3.1.5 (preprint 3.5). -/
theorem proposition_3_6_5_local_sc (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U) (h0O : (0 : E 0) ∈ r R '' U)
    {fb g : E 0 → F 0} (hfill : IsFillingGerm hU hR h0 fb g) (hfb0 : fb 0 = 0)
    (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ)) {G : ScNbhdGerm E C} (hG : G.U 0 ⊆ U)
    {Dg : E 1 → E 0 →L[ℝ] F 0} (hg : IsSc1GermWith G g Dg) {Gs : ScNbhdGerm E C}
    {s : E 0 → F 1} {Ds : E 1 → E 0 →L[ℝ] F.shift 0} (hs : IsSc1GermWith (F := F.shift) Gs s Ds)
    (hs0 : F.toBase 1 (s 0) = g 0) (d : ConjugationData U fun u => g u - F.toBase 1 (s u)) :
    ∃ (hDg : IsScOperator (Dg 0)) (hT : E.IsScSubspace (rangeS (scDeriv U (r R) 0)))
      (hK : F.IsScSubspace (rangeS (ρCLM hR h0)))
      (hTK : ∀ x ∈ rangeS (scDeriv U (r R) 0), hDg.toScOperator 0 x ∈ rangeS (ρCLM hR h0)),
      IsScFredholm hDg.toScOperator ∧ IsScFredholm (hDg.toScOperator.restrict hT hK hTK) ∧
      (∀ x : (E.ofSubspace hT) 0, ((hDg.toScOperator.restrict hT hK hTK 0 x).1 : F 0) = Dg 0 x.1) ∧
      ∀ m, (hDg.toScOperator m).IsFredholm ∧
        fredholmIndex (hDg.toScOperator m) = finrank ℝ d.Pn - finrank ℝ d.Q ∧
        ((hDg.toScOperator.restrict hT hK hTK) m).IsFredholm ∧
        fredholmIndex ((hDg.toScOperator.restrict hT hK hTK) m) =
          finrank ℝ d.Pn - finrank ℝ d.Q := by
  have hg0 : g 0 = 0 := by rw [← hfill.eq_on.self_of_nhds h0O, hfb0]
  -- `k = g − s` has an sc-Fredholm derivative at `0`
  have hk := hg.sub_toBase_shift hs
  have hk0 : (fun u => g u - F.toBase 1 (s u)) 0 = 0 := by
    change g 0 - F.toBase 1 (s 0) = 0
    rw [hs0, hg0, sub_self]
  obtain ⟨hDkop, hDkF, hDkind⟩ :=
    d.scDeriv_isScFredholm hU h0 ((G.inter_subset_left Gs 0).trans hG) hk hk0
  -- `Dg(0) = Dk(0) + ιDs(0)`, `Ds(0)` an sc⁺-operator
  set S : ScPlus E F := hs.isScOperator_deriv_zero.toScOperator with hS
  have hDg : Dg 0 = (Dg 0 - (F.toBase 1).comp (Ds 0)) + S.toScOperator 0 :=
    hs.deriv_zero_eq_add_scPlus
  have hDgop : IsScOperator (Dg 0) := hg.isScOperator_deriv_zero
  have heqop : hDgop.toScOperator = hDkop.toScOperator + S.toScOperator := by
    apply ScOperator.ext_base
    ext x
    rw [ScOperator.add_apply, hDgop.toScOperator_zero, hDkop.toScOperator_zero]
    exact congrArg (fun T : E 0 →L[ℝ] F 0 => T x) hDg
  -- Proposition 1.1.11 (preprint 1.10)
  have hDgF : IsScFredholm hDgop.toScOperator := heqop ▸ proposition_1_1_11_preprint hDkF S
  have hDgind : scIndex hDgop.toScOperator = finrank ℝ d.Pn - finrank ℝ d.Q := by
    rw [heqop, proposition_1_1_11_index hDkF S, hDkind]
  -- Proposition 3.1.5 (preprint 3.5)
  obtain ⟨hT, hK, hTK, hTF, happ, hTlvl⟩ :=
    hfill.proposition_3_1_5_sc hg0 h0O hfK hG hg hDgop hDgF
  refine ⟨hDgop, hT, hK, hTK, hDgF, hTF, happ, fun m => ?_⟩
  obtain ⟨hDgFm, hDgindm⟩ := hDgF.fredholmIndex_lvl m
  obtain ⟨hTFm, hTindm⟩ := hTlvl m
  have h0ind : fredholmIndex (Dg 0) = finrank ℝ d.Pn - finrank ℝ d.Q := by
    rw [← hDgop.toScOperator_zero, ← scIndex_eq_fredholmIndex, hDgind]
  exact ⟨hDgFm, hDgindm.trans hDgind, hTFm, hTindm.trans h0ind⟩

/-- **Theorem 3.1.22 (preprint 3.19), "`f'(x₀)` is sc-Fredholm", in the chart, germ reading** (phase 2): under the
hypotheses of `proposition_3_6_5_local_sc`, if moreover `Tf(0) = Dg(0)|_{T₀O} : T₀O → K₀` is
onto on level `0` (condition (1) of Definition 3.6.6 (preprint 3.53): every `y ∈ K₀` is `Dg(0)x` for some
`x ∈ T₀O`), then the sc-Fredholm `Tf(0)` is onto on every level (it is regularizing). -/
theorem theorem_3_1_22_linearization_sc_local_germ (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U) (h0O : (0 : E 0) ∈ r R '' U)
    {fb g : E 0 → F 0} (hfill : IsFillingGerm hU hR h0 fb g) (hfb0 : fb 0 = 0)
    (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ)) {G : ScNbhdGerm E C} (hG : G.U 0 ⊆ U)
    {Dg : E 1 → E 0 →L[ℝ] F 0} (hg : IsSc1GermWith G g Dg) {Gs : ScNbhdGerm E C}
    {s : E 0 → F 1} {Ds : E 1 → E 0 →L[ℝ] F.shift 0} (hs : IsSc1GermWith (F := F.shift) Gs s Ds)
    (hs0 : F.toBase 1 (s 0) = g 0) (d : ConjugationData U fun u => g u - F.toBase 1 (s u))
    (hsurj : ∀ y ∈ rangeS (ρCLM hR h0), ∃ x ∈ rangeS (scDeriv U (r R) 0), Dg 0 x = y) :
    ∃ (hDg : IsScOperator (Dg 0)) (hT : E.IsScSubspace (rangeS (scDeriv U (r R) 0)))
      (hK : F.IsScSubspace (rangeS (ρCLM hR h0)))
      (hTK : ∀ x ∈ rangeS (scDeriv U (r R) 0), hDg.toScOperator 0 x ∈ rangeS (ρCLM hR h0)),
      IsScFredholm hDg.toScOperator ∧ IsScFredholm (hDg.toScOperator.restrict hT hK hTK) ∧
      (∀ x : (E.ofSubspace hT) 0, ((hDg.toScOperator.restrict hT hK hTK 0 x).1 : F 0) = Dg 0 x.1) ∧
      (∀ m, Surjective ((hDg.toScOperator.restrict hT hK hTK) m)) ∧
      ∀ m, fredholmIndex (hDg.toScOperator m) = finrank ℝ d.Pn - finrank ℝ d.Q ∧
        fredholmIndex ((hDg.toScOperator.restrict hT hK hTK) m) =
          finrank ℝ d.Pn - finrank ℝ d.Q := by
  obtain ⟨hDg, hT, hK, hTK, hDgF, hTF, happ, hlvl⟩ :=
    proposition_3_6_5_local_sc hU hR h0 h0O hfill hfb0 hfK hG hg hs hs0 d
  have hsurj0 : Surjective (hDg.toScOperator.restrict hT hK hTK 0) := by
    intro y
    obtain ⟨x, hx, hxy⟩ := hsurj y.1 y.2
    exact ⟨⟨x, hx⟩, Subtype.ext ((happ _).trans hxy)⟩
  exact ⟨hDg, hT, hK, hTK, hDgF, hTF, happ, hTF.isRegularizing.surjective hsurj0,
    fun m => ⟨(hlvl m).2.1, (hlvl m).2.2.2⟩⟩

end Prop352

/-! ### Proposition 3.6.5 (preprint 3.52) and Theorem 3.1.22 (preprint 3.19) for sections of strong bundles, sc form, germ reading -/

section Bundle

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- **Proposition 3.6.5 (preprint 3.52), sc form, germ reading** (phase 2; the germ version of
`proposition_3_6_5_sc_wholeChart`, hypothesis `B.IsScFredholmGerm f x₀`): let `f` be a section with `(f, x₀)`
an sc-Fredholm germ and `f(x₀) = 0`.  In the strong bundle chart of Definition 3.1.11 (preprint 3.11) centred at
`x₀`, with the filling germ `g` of `f̂` (on `G ⊆ U`, derivative family `Dg`) and the sc⁺-germ `s`
(`s(0) = g(0)`) for which `g − s` is conjugated to a basic germ, `Dg(0) : E → F` and
`Tf(x₀) = Dg(0)|_{T₀O} : T₀O → K₀` are **sc-Fredholm operators**, and for **every** conjugation
`d` of `g − s` their level maps all have index `n − N = dim d.Pn − dim d.Q`. -/
theorem proposition_3_6_5_sc (hf : IsSection P f) {x₀ : X} (hg : B.IsScFredholmGerm f x₀)
    (hx₀ : IsZeroAt P f x₀) :
    ∃ (c : StrongBundleChart PX P) (_ : B.IsChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
      (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0) (s : c.φ.model.E 0 → c.F 1)
      (_ : IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g)
      (_ : IsScPlusGerm c.φ.model.C c.U s) (_ : c.F.toBase 1 (s 0) = g 0)
      (_ : Nonempty (ConjugationData c.U fun u => g u - c.F.toBase 1 (s u)))
      (G : ScNbhdGerm c.φ.model.E c.φ.model.C) (_ : G.U 0 ⊆ c.U) (_ : IsScSmoothGerm G g)
      (Dg : c.φ.model.E 1 → c.φ.model.E 0 →L[ℝ] c.F 0) (_ : IsSc1GermWith G g Dg)
      (hDg : IsScOperator (Dg 0))
      (hT : c.φ.model.E.IsScSubspace (rangeS (scDeriv c.U (r c.R) 0)))
      (hK : c.F.IsScSubspace (rangeS (ρCLM c.isRetraction h0)))
      (hTK : ∀ x ∈ rangeS (scDeriv c.U (r c.R) 0),
        hDg.toScOperator 0 x ∈ rangeS (ρCLM c.isRetraction h0)),
      IsScFredholm hDg.toScOperator ∧ IsScFredholm (hDg.toScOperator.restrict hT hK hTK) ∧
      (∀ x : (c.φ.model.E.ofSubspace hT) 0,
        ((hDg.toScOperator.restrict hT hK hTK 0 x).1 : c.F 0) = Dg 0 x.1) ∧
      ∀ d : ConjugationData c.U (fun u => g u - c.F.toBase 1 (s u)), ∀ m,
        fredholmIndex (hDg.toScOperator m) = finrank ℝ d.Pn - finrank ℝ d.Q ∧
        fredholmIndex ((hDg.toScOperator.restrict hT hK hTK) m) =
          finrank ℝ d.Pn - finrank ℝ d.Q := by
  obtain ⟨-, c, hc, hxV, hφ0, h0U, g, s, hfill, hsp, hs0, hconj⟩ := hg
  obtain ⟨Gs, -, hs⟩ := id hsp
  obtain ⟨h0O, hfb0, hfK⟩ := c.zero_data hf hxV hφ0 hx₀
  obtain ⟨G, hGU, hgG, -⟩ := hfill.germ
  have hg1 := (hgG 1).1.isSc1GermWith_scDerivGerm
  have hs1 := (hs 1).1.isSc1GermWith_scDerivGerm
  obtain ⟨d₀⟩ := isConjugateToBasicGerm_iff_nonempty.1 hconj
  obtain ⟨hDg, hT, hK, hTK, hDgF, hTF, happ, -⟩ :=
    proposition_3_6_5_local_sc c.relOpen c.isRetraction h0U h0O hfill hfb0 hfK hGU hg1 hs1
      hs0 d₀
  refine ⟨c, hc, hxV, hφ0, h0U, g, s, hfill, hsp, hs0, ⟨d₀⟩, G, hGU, hgG, _, hg1, hDg, hT, hK,
    hTK, hDgF, hTF, happ, fun d m => ?_⟩
  obtain ⟨hDg', hT', hK', hTK', -, -, -, hlvl⟩ :=
    proposition_3_6_5_local_sc c.relOpen c.isRetraction h0U h0O hfill hfb0 hfK hGU hg1 hs1
      hs0 d
  obtain ⟨-, h1, -, h2⟩ := hlvl m
  exact ⟨h1, h2⟩

/-- **Theorem 3.1.22 (preprint 3.19), the first clause, sc form, germ reading: "`f'(x₀)` is sc-Fredholm"** (phase 2;
the germ version of `theorem_3_1_22_linearization_sc_wholeChart`): for an sc-Fredholm section `f` and a zero
`x₀` such that `(f, x₀)` has the germ data of Definition 3.1.11 (preprint 3.11) (germ reading) in a chart in which
`Tf(x₀) = Dg(0)|_{T₀O} : T₀O → K₀` is onto (condition (1) of Definition 3.6.6 (preprint 3.53), germ reading: the
`surj` field of `IsGoodPositionAtGerm`, so the hypothesis follows from
`StrongBundle.IsGoodPositionGerm f x₀`), `Dg(0)` and `f'(x₀) = Tf(x₀)` are sc-Fredholm
operators, `Tf(x₀)` is onto on every level, and for every conjugation `d` of `g − s` to a basic
germ the level maps of both have index `dim d.Pn − dim d.Q`. -/
theorem theorem_3_1_22_linearization_sc (hf : B.IsScFredholmSection f) {x₀ : X}
    (hx₀ : IsZeroAt P f x₀)
    (hg : x₀ ∈ PX.smoothSet ∧
      ∃ (c : StrongBundleChart PX P) (_ : B.IsChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
        (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0)
        (s : c.φ.model.E 0 → c.F 1),
        IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g ∧
        IsScPlusGerm c.φ.model.C c.U s ∧ c.F.toBase 1 (s 0) = g 0 ∧
        IsConjugateToBasicGerm c.U (fun u => g u - c.F.toBase 1 (s u)) ∧
        ∃ (G : ScNbhdGerm c.φ.model.E c.φ.model.C)
          (Dg : c.φ.model.E 1 → c.φ.model.E 0 →L[ℝ] c.F 0),
          G.U 0 ⊆ c.U ∧ IsSc1GermWith G g Dg ∧
          ∀ y ∈ rangeS (ρCLM c.isRetraction h0),
            ∃ x ∈ rangeS (scDeriv c.U (r c.R) 0), Dg 0 x = y) :
    ∃ (c : StrongBundleChart PX P) (_ : B.IsChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
      (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0) (s : c.φ.model.E 0 → c.F 1)
      (_ : IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g)
      (_ : IsScPlusGerm c.φ.model.C c.U s) (_ : c.F.toBase 1 (s 0) = g 0)
      (_ : Nonempty (ConjugationData c.U fun u => g u - c.F.toBase 1 (s u)))
      (G : ScNbhdGerm c.φ.model.E c.φ.model.C) (_ : G.U 0 ⊆ c.U)
      (Dg : c.φ.model.E 1 → c.φ.model.E 0 →L[ℝ] c.F 0) (_ : IsSc1GermWith G g Dg)
      (hDg : IsScOperator (Dg 0))
      (hT : c.φ.model.E.IsScSubspace (rangeS (scDeriv c.U (r c.R) 0)))
      (hK : c.F.IsScSubspace (rangeS (ρCLM c.isRetraction h0)))
      (hTK : ∀ x ∈ rangeS (scDeriv c.U (r c.R) 0),
        hDg.toScOperator 0 x ∈ rangeS (ρCLM c.isRetraction h0)),
      IsScFredholm hDg.toScOperator ∧ IsScFredholm (hDg.toScOperator.restrict hT hK hTK) ∧
      (∀ x : (c.φ.model.E.ofSubspace hT) 0,
        ((hDg.toScOperator.restrict hT hK hTK 0 x).1 : c.F 0) = Dg 0 x.1) ∧
      (∀ m, Surjective ((hDg.toScOperator.restrict hT hK hTK) m)) ∧
      ∀ d : ConjugationData c.U (fun u => g u - c.F.toBase 1 (s u)), ∀ m,
        fredholmIndex (hDg.toScOperator m) = finrank ℝ d.Pn - finrank ℝ d.Q ∧
        fredholmIndex ((hDg.toScOperator.restrict hT hK hTK) m) =
          finrank ℝ d.Pn - finrank ℝ d.Q := by
  obtain ⟨-, c, hc, hxV, hφ0, h0U, g, s, hfill, hsp, hs0, hconj, G, Dg, hGU, hg, hsurj⟩ := hg
  obtain ⟨Gs, -, hs⟩ := id hsp
  obtain ⟨h0O, hfb0, hfK⟩ := c.zero_data hf.isScSmooth.1 hxV hφ0 hx₀
  have hs1 := (hs 1).1.isSc1GermWith_scDerivGerm
  obtain ⟨d₀⟩ := isConjugateToBasicGerm_iff_nonempty.1 hconj
  obtain ⟨hDg, hT, hK, hTK, hDgF, hTF, happ, hsurjm, -⟩ :=
    theorem_3_1_22_linearization_sc_local_germ c.relOpen c.isRetraction h0U h0O hfill hfb0 hfK hGU
      hg hs1 hs0 d₀ hsurj
  refine ⟨c, hc, hxV, hφ0, h0U, g, s, hfill, hsp, hs0, ⟨d₀⟩, G, hGU, Dg, hg, hDg, hT, hK, hTK,
    hDgF, hTF, happ, hsurjm, fun d m => ?_⟩
  obtain ⟨hDg', hT', hK', hTK', -, -, -, hlvl⟩ :=
    proposition_3_6_5_local_sc c.relOpen c.isRetraction h0U h0O hfill hfb0 hfK hGU hg hs1
      hs0 d
  obtain ⟨-, h1, -, h2⟩ := hlvl m
  exact ⟨h1, h2⟩

end Bundle

end Polyfold
