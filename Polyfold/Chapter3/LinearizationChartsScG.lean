import Polyfold.Chapter3.LinearizationChartsSc
import Polyfold.Chapter3.GlobalIFTIndexG
import Polyfold.Chapter3.FredholmGermLinearizationScG

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.1 and §3.6:
**condition (3) of a filler on every level at a zero**, **the converse of Proposition 3.5 in sc
form**, and **the linearization of an sc-Fredholm section at a zero is sc-Fredholm in every strong
bundle chart** — **in the text's germ reading of Definition 3.11** (phase 2).

# sc-Fredholm linearizations in every chart, germ reading

## The text, paraphrased

See `LinearizationChartsSc.lean`.  (Definition 3.4 (3)) `(1 − ρ(0))Dg(0)|_{ker Dr(0)}` is an
isomorphism onto `ker ρ(0)`; (Proposition 3.5) `Tf(0)` Fredholm iff `Dg(0)` is; (Proposition 3.52,
Theorem 3.19) at a zero, `f'(x)` is sc-Fredholm.  The filling `g` of Definition 3.11 is a germ: it
is sc-smooth on a germ of neighbourhoods of `0` whose levels may shrink, and `Dg(0)` is the value at
`0` of a derivative family of `g` (`IsSc1GermWith`).

## What is formalized

* `Polyfold.IsFillingGerm.mem_range_toBase_of_scDeriv_r_eq_zero`,
  `IsFillingGerm.filler_condition_three_sc`, `IsFillingGerm.proposition_3_5_sc_converse`,
  `IsFillingGerm.proposition_3_5_sc_iff`: the germ forms of the `IsFillerOf` statements of
  `LinearizationChartsSc.lean` (condition (3) on every level at a zero as an sc-isomorphism, and
  the converse of Proposition 3.5 in sc form), for a filling germ `g` with a derivative family `Dg`
  on a germ `G ⊆ U`, with `Dg(0)` in place of `scDeriv U g 0`.
* `Polyfold.StrongBundle.linAt_sc_of_germ`: the transport step of `linAt_isScFredholm_wholeChart` from a
  datum of Definition 3.11 in the germ reading at `y` (filling germ, sc⁺-germ, conjugation).
* `Polyfold.StrongBundle.linAt_isScFredholm`: **`Lin(z)` is sc-Fredholm in every chart** for an
  sc-Fredholm section in the germ reading (`IsScFredholmSection`), with every level map of index
  `dim d.Pn − dim d.Q` for **every** datum of Definition 3.11 in the germ reading at `y`.
* `Polyfold.StrongBundle.linAt_isScFredholm_of_isSurjLinOfIndex`,
  `Polyfold.theorem_3_54_index_locally_constant_sc`: the sc form of the local constancy of the
  index along the solution set (hypotheses `IsScFredholmSectionTame`, `IsGoodPositionGermTame`).

## What the text leaves implicit, and the choices made

* The proofs are those of `LinearizationChartsSc.lean` with Proposition 3.52 and Proposition 3.5
  for germs (`proposition_3_52_local_sc`, `IsFillingGerm.proposition_3_5_sc`,
  `IsFillingGerm.proposition_3_5`, `IsFillingGerm.exists_kerEquiv`,
  `IsFillingGerm.deriv_comp_r_eq_zero`) and the bridge `Tf̃₁(0) = Lin₁(0)` on `T₀O₁` for a filling
  germ (`IsFillingGerm.fillerRestrict_eq_linAt`).  All statements at the chart of the germ datum
  are at its centre `0`, which lies in every germ; the transport to the chart `c` (around `y`,
  not centred) is about `linAt`, the derivative of the whole-chart map `f̂ ∘ r`, and is unchanged
  (`linAt_chart_change_sc`).
* The derivative family of the filling germ in the transport is `scDerivGerm G₁ g₁` on the germ of
  `IsFillingGerm.germ`; `Dg₁(0)` does not depend on this choice (`IsSc1GermWith.deriv_zero_eq`).
-/

open Set Filter Topology Function Module ContinuousLinearMap

noncomputable section

namespace Polyfold

universe u v

variable {E F : ScBanach}

open StrongRetr

/-! ### Condition (3) of the filler on every level, and the converse of Proposition 3.5, germ
reading -/

namespace IsFillingGerm

variable {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0} {hU : IsRelOpenInQuadrant E C U}
  {hR : IsStrongBundleRetraction U R} {h0 : (0 : E 0) ∈ U} {fb g : E 0 → F 0}
  (hfg : IsFillingGerm hU hR h0 fb g)

include hfg in
/-- **Condition (3) of the filler on every level at a zero, germ reading** (phase 2; the germ form
of `IsFillerOf.mem_range_toBase_of_scDeriv_r_eq_zero`; Definition 3.4 (3)): let `g` be a filling
germ of `f` with `g(0) = 0`, `Dg` a derivative family of `g` on a germ `G ⊆ U`, and `Dg(0)`
sc-Fredholm.  If `v ∈ ker Dr(0)` and `(1 − ρ(0))Dg(0)v ∈ F_m`, then `v ∈ E_m`.  Proof as for
fillers: `ρ(0)Dg(0)v = Dg(0)t + c` with `t ∈ T₀O`, `c ∈ K₀` smooth (`Tf(0)` is sc-Fredholm,
`IsFillingGerm.proposition_3_5_sc`); `Dg(0)(v − t) ∈ F_m`, so `v − t ∈ E_m`, and
`t = −Dr(0)(v − t) ∈ E_m`. -/
theorem mem_range_toBase_of_scDeriv_r_eq_zero (hg0 : g 0 = 0)
    (h0O : (0 : E 0) ∈ r R '' U) (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ))
    {G : ScNbhdGerm E C} (hG : G.U 0 ⊆ U) {Dg : E 1 → E 0 →L[ℝ] F 0} (hg : IsSc1GermWith G g Dg)
    (hDg : IsScOperator (Dg 0)) (hDgF : IsScFredholm hDg.toScOperator) {m : ℕ}
    {v : E 0} (hv : scDeriv U (r R) 0 v = 0)
    (hy : Dg 0 v - ρCLM hR h0 (Dg 0 v) ∈ range (F.toBase m)) :
    v ∈ range (E.toBase m) := by
  obtain ⟨hT, hK, hTK, hTF, happ, -⟩ := hfg.proposition_3_5_sc hg0 h0O hfK hG hg hDg hDgF
  have hS0 : (hDg.toScOperator.restrict hT hK hTK 0).IsFredholm := by
    obtain ⟨s⟩ := hTF; exact s.isFredholm 0
  set w := ρCLM hR h0 (Dg 0 v) with hw
  have hwK : w ∈ rangeS (ρCLM hR h0) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ := ScOperator.exists_sub_mem_smooth hS0 (⟨w, hwK⟩ : (F.ofSubspace hK) 0)
  -- `c = w − Dg(0)t` is smooth, `t = e ∈ T₀O`
  have hc : w - Dg 0 e.1 ∈ range (F.toBase m) := by
    obtain ⟨c, hc⟩ := (ScScale.mem_smooth_iff _).1 he m
    have hmem := (ScBanach.ofSubspace_mem_range_toBase_iff hK).1 ⟨c, hc⟩
    convert hmem using 1
    change w - Dg 0 e.1 = w - (hDg.toScOperator.restrict hT hK hTK 0 e).1
    rw [happ]
  have hDgv : Dg 0 (v - e.1) ∈ range (F.toBase m) := by
    have : Dg 0 (v - e.1) = (Dg 0 v - w) + (w - Dg 0 e.1) := by rw [map_sub]; abel
    rw [this]
    exact ScBanach.add_mem_range_toBase hy hc
  have hreg : v - e.1 ∈ range (E.toBase m) :=
    hDgF.isRegularizing m (v - e.1) (by rw [hDg.toScOperator_zero]; exact hDgv)
  have hDr := isScOperator_scDeriv_r hU hR h0
  have he1 : scDeriv U (r R) 0 e.1 = e.1 := by
    have he2 : (e.1 : E 0) ∈ rangeS (scDeriv U (r R) 0) := e.2
    obtain ⟨w', hw'⟩ := he2
    rw [ContinuousLinearMap.coe_coe] at hw'
    rw [← hw']
    exact scDeriv_r_idem hU hR h0O w'
  have h2 : scDeriv U (r R) 0 (v - e.1) = -e.1 := by rw [map_sub, hv, he1, zero_sub]
  have h3 : e.1 ∈ range (E.toBase m) := by
    rw [← ScBanach.neg_mem_range_toBase_iff, ← h2]
    exact hDr.mem_range_toBase hreg
  have : v = (v - e.1) + e.1 := by abel
  rw [this]
  exact ScBanach.add_mem_range_toBase hreg h3

include hfg in
/-- **Condition (3) of the filler on every level at a zero, as an sc-isomorphism, germ reading**
(phase 2; the germ form of `IsFillerOf.filler_condition_three_sc`): let `g` be a filling germ with
`g(0) = 0`, `Dg` a derivative family on a germ `G ⊆ U`, and `Dg(0)` sc-Fredholm.  Then `ker Dr(0)`
and `ker ρ(0)` are sc-subspaces, and `(1 − ρ(0))Dg(0)` restricts to an **sc-isomorphism**
`ker Dr(0) → ker ρ(0)` between the induced sc-Banach spaces. -/
theorem filler_condition_three_sc (hg0 : g 0 = 0)
    (h0O : (0 : E 0) ∈ r R '' U) (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ))
    {G : ScNbhdGerm E C} (hG : G.U 0 ⊆ U) {Dg : E 1 → E 0 →L[ℝ] F 0} (hg : IsSc1GermWith G g Dg)
    (hDg : IsScOperator (Dg 0)) (hDgF : IsScFredholm hDg.toScOperator) :
    ∃ (hN : E.IsScSubspace (LinearMap.ker (scDeriv U (r R) 0 : E 0 →ₗ[ℝ] E 0)))
      (hM : F.IsScSubspace (LinearMap.ker (ρCLM hR h0 : F 0 →ₗ[ℝ] F 0)))
      (Φ : ScIso (E.ofSubspace hN) (F.ofSubspace hM)),
      ∀ v : (E.ofSubspace hN) 0, ((Φ 0 v).1 : F 0) = Dg 0 v.1 - ρCLM hR h0 (Dg 0 v.1) := by
  have hN := isScSubspace_ker_scDeriv_r hU hR h0O
  have hM := isScSubspace_ker_ρCLM hR h0 h0O
  have hρ := isScOperator_ρCLM hR h0
  -- `(1 − ρ(0))Dg(0)` is an sc-operator
  have hC : IsScOperator (Dg 0 - (ρCLM hR h0).comp (Dg 0)) :=
    isScOperator_of_mapsTo fun m x => by
      have h1 := hDg.mem_range_toBase (⟨x, rfl⟩ : E.toBase m x ∈ range (E.toBase m))
      rw [sub_apply, ContinuousLinearMap.comp_apply]
      exact ScBanach.sub_mem_range_toBase h1 (hρ.mem_range_toBase h1)
  have hNM : ∀ x ∈ LinearMap.ker (scDeriv U (r R) 0 : E 0 →ₗ[ℝ] E 0),
      hC.toScOperator 0 x ∈ LinearMap.ker (ρCLM hR h0 : F 0 →ₗ[ℝ] F 0) := by
    intro x _
    rw [hC.toScOperator_zero, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      sub_apply, ContinuousLinearMap.comp_apply, map_sub, ρCLM_idem hR h0 h0O,
      sub_self]
  set Cop := hC.toScOperator.restrict hN hM hNM with hCop
  obtain ⟨Φ, hΦ⟩ := hfg.exists_kerEquiv hU hR h0 hg0 h0O hg
  have hCapp : ∀ x : (E.ofSubspace hN) 0, ((Cop 0 x).1 : F 0) =
      Dg 0 x.1 - ρCLM hR h0 (Dg 0 x.1) := by
    intro x
    change hC.toScOperator 0 x.1 = _
    rw [hC.toScOperator_zero]
    rfl
  have hbij0 : Bijective (Cop 0) := by
    constructor
    · intro x x' hxx'
      have h2 := congrArg Subtype.val hxx'
      rw [hCapp, hCapp] at h2
      have h1 : Φ ⟨x.1, x.2⟩ = Φ ⟨x'.1, x'.2⟩ := Subtype.ext (by rw [hΦ, hΦ]; exact h2)
      exact Subtype.ext (congrArg Subtype.val (Φ.injective h1))
    · intro y
      set v := Φ.symm ⟨y.1, y.2⟩ with hv
      refine ⟨⟨v.1, v.2⟩, Subtype.ext ((hCapp _).trans ?_)⟩
      change Dg 0 v.1 - ρCLM hR h0 (Dg 0 v.1) = y.1
      rw [← hΦ, hv, Φ.apply_symm_apply]
  have hreg : Cop.IsRegularizing := by
    intro m x hx
    rw [ScBanach.ofSubspace_mem_range_toBase_iff] at hx ⊢
    rw [hCapp] at hx
    exact hfg.mem_range_toBase_of_scDeriv_r_eq_zero hg0 h0O hfK hG hg hDg hDgF x.2 hx
  exact ⟨hN, hM, ScIso.ofBijective Cop (hreg.bijective hbij0), hCapp⟩

include hfg in
/-- **The converse of Proposition 3.5, sc form, germ reading** (phase 2; the germ form of
`IsFillerOf.proposition_3_5_sc_converse`): let `g` be a filling germ with `g(0) = 0`, `Dg` a
derivative family on a germ `G ⊆ U`, `Dg(0)` an sc-operator, `Tf(0) = Dg(0)|_{T₀O} : T₀O → K₀`
sc-Fredholm, and condition (3) of Definition 3.4 on every level.  Then `Dg(0)` is sc-Fredholm, and
every level map of `Dg(0)` is Fredholm with the index of `Tf(0)`. -/
theorem proposition_3_5_sc_converse (hg0 : g 0 = 0)
    (h0O : (0 : E 0) ∈ r R '' U) (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ))
    {G : ScNbhdGerm E C} (hG : G.U 0 ⊆ U) {Dg : E 1 → E 0 →L[ℝ] F 0} (hg : IsSc1GermWith G g Dg)
    (hDg : IsScOperator (Dg 0)) (hT : E.IsScSubspace (rangeS (scDeriv U (r R) 0)))
    (hK : F.IsScSubspace (rangeS (ρCLM hR h0)))
    (hTK : ∀ x ∈ rangeS (scDeriv U (r R) 0), hDg.toScOperator 0 x ∈ rangeS (ρCLM hR h0))
    (hTF : IsScFredholm (hDg.toScOperator.restrict hT hK hTK))
    (h3 : ∀ (m : ℕ) (y : F 0), ρCLM hR h0 y = 0 → y ∈ range (F.toBase m) →
      ∃ v ∈ range (E.toBase m), scDeriv U (r R) 0 v = 0 ∧
        Dg 0 v - ρCLM hR h0 (Dg 0 v) = y) :
    IsScFredholm hDg.toScOperator ∧ ∀ m, (hDg.toScOperator m).IsFredholm ∧
      fredholmIndex (hDg.toScOperator m) =
        fredholmIndex (hDg.toScOperator.restrict hT hK hTK 0) := by
  obtain ⟨h1, -, hFiff, hindeq⟩ := hfg.proposition_3_5 hU hR h0 hg0 h0O hfK hG hg
  obtain ⟨Φ, hΦ⟩ := hfg.exists_kerEquiv hU hR h0 hg0 h0O hg
  have hρ := isScOperator_ρCLM hR h0
  have hS0F : (hDg.toScOperator.restrict hT hK hTK 0).IsFredholm := by
    obtain ⟨s⟩ := hTF; exact s.isFredholm 0
  obtain ⟨hiff, hind⟩ := hDg.toScOperator.isFredholm_restrict_zero_iff hT hK hTK
    (L := fillerRestrict (scDeriv U (r R) 0) (ρCLM hR h0) (Dg 0) h1)
    (fun x => by rw [fillerRestrict_apply, hDg.toScOperator_zero])
  have hDgF0 : (Dg 0).IsFredholm := hFiff.1 (hiff.1 hS0F)
  have hreg : hDg.toScOperator.IsRegularizing := by
    intro m e he
    rw [hDg.toScOperator_zero] at he
    set t := scDeriv U (r R) 0 e with ht
    set v := e - t with hv
    have hv0 : scDeriv U (r R) 0 v = 0 := by
      rw [hv, map_sub, ht, scDeriv_r_idem hU hR h0O, sub_self]
    have ht0 : Dg 0 t - ρCLM hR h0 (Dg 0 t) = 0 :=
      hfg.deriv_comp_r_eq_zero hU hR h0 hg0 h0O hfK hG hg e
    have hy : Dg 0 v - ρCLM hR h0 (Dg 0 v) = Dg 0 e - ρCLM hR h0 (Dg 0 e) := by
      have : Dg 0 v - ρCLM hR h0 (Dg 0 v) =
          (Dg 0 e - ρCLM hR h0 (Dg 0 e)) - (Dg 0 t - ρCLM hR h0 (Dg 0 t)) := by
        rw [hv, map_sub, map_sub]; abel
      rw [this, ht0, sub_zero]
    have hρy : ρCLM hR h0 (Dg 0 v - ρCLM hR h0 (Dg 0 v)) = 0 := by
      rw [hy, map_sub, ρCLM_idem hR h0 h0O, sub_self]
    have hym : Dg 0 v - ρCLM hR h0 (Dg 0 v) ∈ range (F.toBase m) := by
      rw [hy]; exact ScBanach.sub_mem_range_toBase he (hρ.mem_range_toBase he)
    obtain ⟨v', hv'm, hv'0, hv'y⟩ := h3 m _ hρy hym
    have hvv' : v' = v := by
      have h4 : Φ ⟨v', hv'0⟩ = Φ ⟨v, hv0⟩ := Subtype.ext (by rw [hΦ, hΦ, hv'y])
      exact congrArg Subtype.val (Φ.injective h4)
    have hvm : v ∈ range (E.toBase m) := hvv' ▸ hv'm
    have htm : Dg 0 t ∈ range (F.toBase m) := by
      have : Dg 0 t = Dg 0 e - Dg 0 v := by rw [hv, map_sub]; abel
      rw [this]
      exact ScBanach.sub_mem_range_toBase he (hDg.mem_range_toBase hvm)
    have htT : t ∈ rangeS (scDeriv U (r R) 0) := ⟨e, rfl⟩
    have htlev := (ScBanach.ofSubspace_mem_range_toBase_iff hT).1
      (hTF.isRegularizing m ⟨t, htT⟩ ((ScBanach.ofSubspace_mem_range_toBase_iff hK).2 (by
        change hDg.toScOperator 0 t ∈ _
        rw [hDg.toScOperator_zero]; exact htm)))
    have he' : e = t + v := by rw [hv]; abel
    rw [he']
    exact ScBanach.add_mem_range_toBase htlev hvm
  have hF0 : (hDg.toScOperator 0).IsFredholm := by rw [hDg.toScOperator_zero]; exact hDgF0
  obtain ⟨hsc, hlvl⟩ := isScFredholm_of_isRegularizing_index hF0 hreg
  refine ⟨hsc, fun m => ⟨(hlvl m).1, ?_⟩⟩
  rw [(hlvl m).2, hDg.toScOperator_zero, ← hindeq, hind hS0F]

include hfg in
/-- **Proposition 3.5, sc form, both directions, germ reading** (phase 2; the germ form of
`IsFillerOf.proposition_3_5_sc_iff`): for a filling germ `g` with `g(0) = 0`, a derivative family
`Dg` on a germ `G ⊆ U` and `Dg(0)` an sc-operator, `Dg(0)` is sc-Fredholm **iff**
`Tf(0) : T₀O → K₀` is sc-Fredholm **and** condition (3) of Definition 3.4 holds on every level. -/
theorem proposition_3_5_sc_iff (hg0 : g 0 = 0)
    (h0O : (0 : E 0) ∈ r R '' U) (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ))
    {G : ScNbhdGerm E C} (hG : G.U 0 ⊆ U) {Dg : E 1 → E 0 →L[ℝ] F 0} (hg : IsSc1GermWith G g Dg)
    (hDg : IsScOperator (Dg 0)) (hT : E.IsScSubspace (rangeS (scDeriv U (r R) 0)))
    (hK : F.IsScSubspace (rangeS (ρCLM hR h0)))
    (hTK : ∀ x ∈ rangeS (scDeriv U (r R) 0), hDg.toScOperator 0 x ∈ rangeS (ρCLM hR h0)) :
    IsScFredholm hDg.toScOperator ↔ IsScFredholm (hDg.toScOperator.restrict hT hK hTK) ∧
      ∀ (m : ℕ) (y : F 0), ρCLM hR h0 y = 0 → y ∈ range (F.toBase m) →
        ∃ v ∈ range (E.toBase m), scDeriv U (r R) 0 v = 0 ∧
          Dg 0 v - ρCLM hR h0 (Dg 0 v) = y := by
  constructor
  · intro hDgF
    obtain ⟨hT', hK', hTK', hsc, -⟩ := hfg.proposition_3_5_sc hg0 h0O hfK hG hg hDg hDgF
    refine ⟨hsc, fun m y hy hym => ?_⟩
    obtain ⟨Φ, hΦ⟩ := hfg.exists_kerEquiv hU hR h0 hg0 h0O hg
    have hyk : y ∈ LinearMap.ker (ρCLM hR h0 : F 0 →ₗ[ℝ] F 0) := hy
    set v := Φ.symm ⟨y, hyk⟩ with hv
    have hvy : Dg 0 v - ρCLM hR h0 (Dg 0 v) = y := by
      rw [← hΦ, hv, Φ.apply_symm_apply]
    exact ⟨v, hfg.mem_range_toBase_of_scDeriv_r_eq_zero hg0 h0O hfK hG hg hDg hDgF v.2
      (hvy ▸ hym), v.2, hvy⟩
  · rintro ⟨hTF, h3⟩
    exact (hfg.proposition_3_5_sc_converse hg0 h0O hfK hG hg hDg hT hK hTK hTF h3).1

end IsFillingGerm

/-! ### `Lin(z)` is sc-Fredholm in every chart, germ reading -/

section Bundle

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- **`Lin(z)` from a germ datum at `y`, germ reading** (phase 2; the germ form of
`StrongBundle.linAt_sc_of_germ_wholeChart`): let `f` be sc-smooth, `y` a zero, `c` a strong bundle chart of
`P` around `y` with the smooth level-`1` point `z` over `φ(y)`, and `D(f̂ ∘ r)(z)` an sc-operator
restricting to `Lin(z) : T_zO → K_z`.  Given a datum of Definition 3.11 at `y` in the germ reading
(a chart `c₁` centred at `y`, a filling germ `g₁`, an sc⁺-germ `s₁` with `s₁(0) = g₁(0)`, a
conjugation `d` of `g₁ − s₁` to a basic germ), the level-`0` map of `Lin(z)` is Fredholm of index
`dim d.Pn − dim d.Q`, and `Lin(z)` is regularizing.  Proof: in `c₁`, `Dg₁(0)` is sc-Fredholm and
`Tf₁(0)` is Fredholm of that index (`proposition_3_52_local_sc`,
`IsFillingGerm.proposition_3_5`,
for the family `scDerivGerm` of `g₁`); `Tf₁(0) = Lin₁(0)` on `T₀O₁`
(`IsFillingGerm.fillerRestrict_eq_linAt`); `Lin₁(0) ∘ a = γ ∘ Lin(z)` with level-preserving `a`,
`a'`, `γ` (`linAt_chart_change_sc`). -/
theorem StrongBundle.linAt_sc_of_germ (hf : B.IsScSmoothSection f) {y : X}
    (hy0 : IsZeroAt P f y) {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (hyV : y ∈ c.φ.source) {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z = c.φ y)
    (hzU : c.φ.model.E.toBase 1 z ∈ c.U) (hzs : z ∈ c.φ.model.E.smoothLvl 1)
    (hD : IsScOperator (scDeriv c.U (c.principal f ∘ r c.R) z))
    (hT : c.φ.model.E.IsScSubspace (rangeS (scDeriv c.U (r c.R) z)))
    (hK : c.F.IsScSubspace (rangeS (ρCLM c.isRetraction hzU)))
    (hTK : ∀ x ∈ rangeS (scDeriv c.U (r c.R) z),
      hD.toScOperator 0 x ∈ rangeS (ρCLM c.isRetraction hzU))
    {c₁ : StrongBundleChart PX P} (hc₁ : B.IsChart c₁) (hyV₁ : y ∈ c₁.φ.source)
    (hφ₁ : c₁.φ y = 0) (h0₁ : (0 : c₁.φ.model.E 0) ∈ c₁.U) {g₁ : c₁.φ.model.E 0 → c₁.F 0}
    {s₁ : c₁.φ.model.E 0 → c₁.F 1}
    (hfill₁ : IsFillingGerm c₁.relOpen c₁.isRetraction h0₁ (c₁.principal f) g₁)
    (hs₁ : IsScPlusGerm c₁.φ.model.C c₁.U s₁) (hs0₁ : c₁.F.toBase 1 (s₁ 0) = g₁ 0)
    (d : ConjugationData c₁.U fun u => g₁ u - c₁.F.toBase 1 (s₁ u)) :
    (hD.toScOperator.restrict hT hK hTK 0).IsFredholm ∧
      fredholmIndex (hD.toScOperator.restrict hT hK hTK 0) = finrank ℝ d.Pn - finrank ℝ d.Q ∧
      (hD.toScOperator.restrict hT hK hTK).IsRegularizing := by
  have hfs : IsSection P f := hf.1
  -- the chart of the germ: `Dg₁(0)` sc-Fredholm, `Tf₁(0)` Fredholm
  obtain ⟨h0O₁, hfb0, hfK₁⟩ := c₁.zero_data hfs hyV₁ hφ₁ hy0
  obtain ⟨G₁, hG₁, hgsm₁, -⟩ := hfill₁.germ
  set Dg₁ := scDerivGerm G₁ g₁ with hDg₁def
  have hg₁ : IsSc1GermWith G₁ g₁ Dg₁ := (hgsm₁ 1).1.isSc1GermWith_scDerivGerm
  obtain ⟨Gs₁, -, hsm₁⟩ := hs₁
  have hs1₁ := (hsm₁ 1).1.isSc1GermWith_scDerivGerm
  obtain ⟨hDg₁, hT₁, hK₁, hTK₁, hDgF₁, hTF₁, happ₁, hlvl₁⟩ :=
    proposition_3_52_local_sc c₁.relOpen c₁.isRetraction h0₁ h0O₁ hfill₁ hfb0 hfK₁ hG₁ hg₁
      hs1₁ hs0₁ d
  have hg0₁ : g₁ 0 = 0 := by rw [← hfill₁.eq_on.self_of_nhds h0O₁, hfb0]
  obtain ⟨h1₁, -, hFiff₁, hindeq₁⟩ :=
    hfill₁.proposition_3_5 c₁.relOpen c₁.isRetraction h0₁ hg0₁ h0O₁ hfK₁ hG₁ hg₁
  have hDg₁F : (Dg₁ 0).IsFredholm := by
    have := (hlvl₁ 0).1; rwa [hDg₁.toScOperator_zero] at this
  have hDg₁ind : fredholmIndex (Dg₁ 0) = finrank ℝ d.Pn - finrank ℝ d.Q := by
    have := (hlvl₁ 0).2.1; rwa [hDg₁.toScOperator_zero] at this
  have hL₁F := hFiff₁.2 hDg₁F
  -- on `T₀O₁`, `Dg₁(0) = D(f̂₁ ∘ r₁)(0)`
  have hL₁app : ∀ w ∈ rangeS (scDeriv c₁.U (r c₁.R) 0),
      Dg₁ 0 w = scDeriv c₁.U (c₁.principal f ∘ r c₁.R) 0 w := fun w hw => by
    have := IsFillingGerm.fillerRestrict_eq_linAt c₁.relOpen c₁.isRetraction h0O₁ hfill₁
      (hf.isSc1_principal_comp_r hc₁) hg₁ h1₁ ⟨w, hw⟩
    rwa [fillerRestrict_apply, linAt_apply] at this
  -- the transport `c → c₁`
  have hz₁ : c₁.φ.model.E.toBase 1 (0 : c₁.φ.model.E 1) = c₁.φ y := by rw [map_zero, hφ₁]
  have hzU₁ : c₁.φ.model.E.toBase 1 (0 : c₁.φ.model.E 1) ∈ c₁.U := by rw [map_zero]; exact h0₁
  obtain ⟨a, a', γ, γ', hTA, hTA', hinv1, hinv2, hΓmem, hΓmem', hΓinv1, hΓinv2, key, hsm, hsm'⟩ :=
    linAt_chart_change_sc c c₁ hfs (StrongBundle.IsChart.transition_isScSmoothRetractMap hc hc₁)
      (hf.isScSmoothRetractMap hc) (hf.isScSmoothRetractMap hc₁) hyV hyV₁ hy0 hz hz₁ hzU hzU₁
  have hρeq := rangeS_ρCLM_congr c₁.isRetraction (map_zero _) hzU₁ h0₁
  rw [hρeq] at hΓmem hΓmem' hΓinv2
  obtain ⟨-, hγ⟩ := hsm hzs
  have ha' := hsm' c₁.φ.model.E.zero_mem_smoothLvl_one
  -- the conjugation on level `0`
  have hmem : ∀ x : ↥(rangeS (scDeriv c.U (r c.R) z)),
      linAt c.U c.R (c.principal f) z x ∈ rangeS (ρCLM c.isRetraction hzU) := fun x => by
    have := hTK x x.2
    rwa [hD.toScOperator_zero] at this
  have : CompleteSpace ↥(rangeS (scDeriv c.U (r c.R) z)) := hT.isClosed.completeSpace_coe
  have : CompleteSpace ↥(rangeS (ρCLM c.isRetraction hzU)) := hK.isClosed.completeSpace_coe
  have : CompleteSpace ↥(rangeS (scDeriv c₁.U (r c₁.R) 0)) := hT₁.isClosed.completeSpace_coe
  have : CompleteSpace ↥(rangeS (ρCLM c₁.isRetraction h0₁)) := hK₁.isClosed.completeSpace_coe
  have hLL : ∀ x, fillerRestrict (scDeriv c₁.U (r c₁.R) 0) (ρCLM c₁.isRetraction h0₁)
      (Dg₁ 0) h1₁ (restrictEquiv _ _ a a' hTA hTA' hinv1 hinv2 x) =
      restrictEquiv _ _ γ γ' hΓmem hΓmem' hΓinv1 hΓinv2
        ((linAt c.U c.R (c.principal f) z).codRestrict _ hmem x) := fun x => by
    apply Subtype.ext
    change Dg₁ 0 (a x) = γ (scDeriv c.U (c.principal f ∘ r c.R) z x)
    rw [hL₁app _ (hTA x x.2)]
    exact key x
  obtain ⟨hFiffc, hindc⟩ := isFredholm_iff_of_conj hLL
  have hLzF := hFiffc.2 hL₁F
  obtain ⟨hF0, hind0⟩ := hD.toScOperator.isFredholm_restrict_zero hT hK hTK
    (L := (linAt c.U c.R (c.principal f) z).codRestrict _ hmem)
    (fun x => by rw [hD.toScOperator_zero]; rfl) hLzF
  refine ⟨hF0, ?_, ?_⟩
  · rw [hind0, ← hindc hLzF, hindeq₁, hDg₁ind]
  · -- the regularity: `Lin(z)x ∈ F_m ⟹ Lin₁(0)(ax) = γ Lin(z)x ∈ F₁_m ⟹ ax ∈ E₁_m ⟹ x ∈ E_m`
    intro m x hx
    have hx' := (ScBanach.ofSubspace_mem_range_toBase_iff hK).1 hx
    apply (ScBanach.ofSubspace_mem_range_toBase_iff hT).2
    have h6 : scDeriv c.U (c.principal f ∘ r c.R) z x.1 ∈ range (c.F.toBase m) := by
      have h5 : ((hD.toScOperator.restrict hT hK hTK 0 x).1 : c.F 0) =
          scDeriv c.U (c.principal f ∘ r c.R) z x.1 := by
        change hD.toScOperator 0 x.1 = _
        rw [hD.toScOperator_zero]
      rwa [h5] at hx'
    have h7 := hγ.mem_range_toBase h6
    rw [← key, ← hL₁app _ (hTA x.1 x.2)] at h7
    have h8 := hDgF₁.isRegularizing m (a x.1) (by rw [hDg₁.toScOperator_zero]; exact h7)
    have h9 := ha'.mem_range_toBase h8
    rwa [hinv1 x.1 x.2] at h9

/-- **The linearization of an sc-Fredholm section at a zero is sc-Fredholm in every chart, germ
reading** (phase 2; the germ form of `StrongBundle.linAt_isScFredholm_wholeChart`; Proposition 3.52 and
Theorem 3.19, "`f'(x)` is sc-Fredholm", chart-intrinsically).  Let `f` be an sc-Fredholm section
in the germ reading (`IsScFredholmSection`), `y` a zero, `c` **any** strong bundle chart of `P`
around `y`, `z` the level-`1` point over `φ(y)`.  Then `D(f̂ ∘ r)(z)` is an sc-operator, `T_zO` and
`K_z` are sc-subspaces, and the restriction `Lin(z) : T_zO → K_z` is an **sc-Fredholm operator**;
every level map is Fredholm with the level-`0` index, which is `dim d.Pn − dim d.Q` for **every**
datum of Definition 3.11 at `y` in the germ reading (chart `c₁` centred at `y`, filling germ `g₁`,
sc⁺-germ `s₁`, conjugation `d` of `g₁ − s₁` to a basic germ). -/
theorem StrongBundle.linAt_isScFredholm (hf : B.IsScFredholmSection f) {y : X}
    (hy0 : IsZeroAt P f y) {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (hyV : y ∈ c.φ.source) {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z = c.φ y)
    (hzU : c.φ.model.E.toBase 1 z ∈ c.U) :
    ∃ (hD : IsScOperator (scDeriv c.U (c.principal f ∘ r c.R) z))
      (hT : c.φ.model.E.IsScSubspace (rangeS (scDeriv c.U (r c.R) z)))
      (hK : c.F.IsScSubspace (rangeS (ρCLM c.isRetraction hzU)))
      (hTK : ∀ x ∈ rangeS (scDeriv c.U (r c.R) z),
        hD.toScOperator 0 x ∈ rangeS (ρCLM c.isRetraction hzU)),
      (∀ x : (c.φ.model.E.ofSubspace hT) 0, ((hD.toScOperator.restrict hT hK hTK 0 x).1 : c.F 0) =
        linAt c.U c.R (c.principal f) z ⟨x.1, x.2⟩) ∧
      IsScFredholm (hD.toScOperator.restrict hT hK hTK) ∧
      ∀ m, ((hD.toScOperator.restrict hT hK hTK) m).IsFredholm ∧
        fredholmIndex ((hD.toScOperator.restrict hT hK hTK) m) =
          fredholmIndex (hD.toScOperator.restrict hT hK hTK 0) ∧
        ∀ (c₁ : StrongBundleChart PX P) (_ : B.IsChart c₁) (_ : y ∈ c₁.φ.source) (_ : c₁.φ y = 0)
          (h0₁ : (0 : c₁.φ.model.E 0) ∈ c₁.U) (g₁ : c₁.φ.model.E 0 → c₁.F 0)
          (s₁ : c₁.φ.model.E 0 → c₁.F 1)
          (_ : IsFillingGerm c₁.relOpen c₁.isRetraction h0₁ (c₁.principal f) g₁)
          (_ : IsScPlusGerm c₁.φ.model.C c₁.U s₁) (_ : c₁.F.toBase 1 (s₁ 0) = g₁ 0)
          (d : ConjugationData c₁.U fun u => g₁ u - c₁.F.toBase 1 (s₁ u)),
          fredholmIndex ((hD.toScOperator.restrict hT hK hTK) m) =
            finrank ℝ d.Pn - finrank ℝ d.Q := by
  have hfs := hf.isScSmooth
  have hys : y ∈ PX.smoothSet := hf.mem_smoothSet_of_isZeroAt hy0
  have hzs : z ∈ c.φ.model.E.smoothLvl 1 := by
    change c.φ.model.E.toBase 1 z ∈ c.φ.model.E.smooth
    rw [hz, ScScale.mem_smooth_iff]
    intro m
    exact (PX.mem_levelSet_iff c.isChart hyV).1 (Set.mem_iInter.1 hys m)
  have hzO : c.φ.model.E.toBase 1 z ∈ r c.R '' c.U := by
    rw [c.r_image, hz]; exact c.φ.mapsTo_model y hyV
  have hfr : IsSc1 c.U (c.principal f ∘ r c.R) := hfs.isSc1_principal_comp_r hc
  have hD : IsScOperator (scDeriv c.U (c.principal f ∘ r c.R) z) :=
    hfr.isSc1With_scDeriv.scOperator_deriv hzU hzs
  have hT := isScSubspace_range_scDeriv_r_at c.relOpen c.isRetraction hzO hzs
  have hK := isScSubspace_range_ρCLM_of_mem_smooth c.isRetraction hzU hzO hzs
  have hTK : ∀ x ∈ rangeS (scDeriv c.U (r c.R) z),
      hD.toScOperator 0 x ∈ rangeS (ρCLM c.isRetraction hzU) := fun x _ => by
    rw [hD.toScOperator_zero]
    exact ⟨_, rho_scDeriv_comp_r c.relOpen c.isRetraction hfr
      (fun x hx => c.principal_mem_K hfs.1 (c.r_image ▸ hx)) hzO
      (by rw [hz]; exact (c.isZeroAt_iff hfs.1 hyV).1 hy0) x⟩
  obtain ⟨-, c₁, hc₁, hyV₁, hφ₁, h0₁, g₁, s₁, hfill₁, hs₁, hs0₁, hconj₁⟩ := hf.germ y hys
  obtain ⟨d₁⟩ := isConjugateToBasicGerm_iff_nonempty.1 hconj₁
  obtain ⟨hF0, -, hreg⟩ := StrongBundle.linAt_sc_of_germ hfs hy0 hc hyV hz hzU hzs hD hT hK
    hTK hc₁ hyV₁ hφ₁ h0₁ hfill₁ hs₁ hs0₁ d₁
  obtain ⟨hsc, hlvl⟩ := isScFredholm_of_isRegularizing_index hF0 hreg
  refine ⟨hD, hT, hK, hTK, fun x => ?_, hsc, fun m => ⟨(hlvl m).1, (hlvl m).2, ?_⟩⟩
  · change hD.toScOperator 0 x.1 = _
    rw [hD.toScOperator_zero]
    rfl
  · intro c₂ hc₂ hyV₂ hφ₂ h0₂ g₂ s₂ hfill₂ hs₂ hs0₂ d
    obtain ⟨-, hind, -⟩ := StrongBundle.linAt_sc_of_germ hfs hy0 hc hyV hz hzU hzs hD hT hK
      hTK hc₂ hyV₂ hφ₂ h0₂ hfill₂ hs₂ hs0₂ d
    rw [(hlvl m).2, hind]

/-- **At a zero where `f'(y)` is onto of index `d`, germ reading** (phase 2; the germ form of
`StrongBundle.linAt_isScFredholm_of_isSurjLinOfIndex_wholeChart`): for an sc-Fredholm section in the germ
reading and a zero with `IsSurjLinOfIndex f y d`, in every chart `Lin(z) : T_zO → K_z` is
sc-Fredholm, **onto on every level** and of index `d` on every level. -/
theorem StrongBundle.linAt_isScFredholm_of_isSurjLinOfIndex
    (hf : B.IsScFredholmSection f) {y : X} (hy0 : IsZeroAt P f y) {d : ℕ}
    (hd : B.IsSurjLinOfIndex f y d) {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (hyV : y ∈ c.φ.source) {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z = c.φ y)
    (hzU : c.φ.model.E.toBase 1 z ∈ c.U) :
    ∃ (hD : IsScOperator (scDeriv c.U (c.principal f ∘ r c.R) z))
      (hT : c.φ.model.E.IsScSubspace (rangeS (scDeriv c.U (r c.R) z)))
      (hK : c.F.IsScSubspace (rangeS (ρCLM c.isRetraction hzU)))
      (hTK : ∀ x ∈ rangeS (scDeriv c.U (r c.R) z),
        hD.toScOperator 0 x ∈ rangeS (ρCLM c.isRetraction hzU)),
      (∀ x : (c.φ.model.E.ofSubspace hT) 0, ((hD.toScOperator.restrict hT hK hTK 0 x).1 : c.F 0) =
        linAt c.U c.R (c.principal f) z ⟨x.1, x.2⟩) ∧
      IsScFredholm (hD.toScOperator.restrict hT hK hTK) ∧
      ∀ m, Surjective ((hD.toScOperator.restrict hT hK hTK) m) ∧
        ((hD.toScOperator.restrict hT hK hTK) m).IsFredholm ∧
        fredholmIndex ((hD.toScOperator.restrict hT hK hTK) m) = d := by
  obtain ⟨hD, hT, hK, hTK, happ, hsc, hlvl⟩ :=
    StrongBundle.linAt_isScFredholm hf hy0 hc hyV hz hzU
  have hmem : ∀ x : ↥(rangeS (scDeriv c.U (r c.R) z)),
      linAt c.U c.R (c.principal f) z x ∈ rangeS (ρCLM c.isRetraction hzU) := fun x => by
    have := hTK x x.2
    rwa [hD.toScOperator_zero] at this
  obtain ⟨hLs, hLF, hLind, -⟩ := hd c hc hyV z hz hzU
    ((linAt c.U c.R (c.principal f) z).codRestrict _ hmem) fun _ => rfl
  obtain ⟨-, hind0⟩ := hD.toScOperator.isFredholm_restrict_zero hT hK hTK
    (L := (linAt c.U c.R (c.principal f) z).codRestrict _ hmem)
    (fun x => by rw [hD.toScOperator_zero]; rfl) hLF
  have hsurj0 : Surjective (hD.toScOperator.restrict hT hK hTK 0) := by
    intro k
    obtain ⟨x, hx⟩ := hLs ⟨k.1, k.2⟩
    exact ⟨⟨x.1, x.2⟩, Subtype.ext ((happ _).trans (congrArg Subtype.val hx))⟩
  refine ⟨hD, hT, hK, hTK, happ, hsc, fun m => ⟨hsc.isRegularizing.surjective hsurj0 m,
    (hlvl m).1, ?_⟩⟩
  rw [(hlvl m).2.1, hind0, hLind]

/-- **The index is locally constant along the solution set, sc form, germ reading** (phase 2; the
germ form of `theorem_3_54_index_locally_constant_sc_wholeChart`): for an sc-Fredholm section with tame germ
data in the germ reading, `f(x₀) = 0` and `(f, x₀)` in good position in a tame chart (germ
reading), there are an open `Vx ∋ x₀` and `d` such that at every zero `y ∈ Vx`, in **every** strong
bundle chart `c` of `P` around `y`, at the level-`1` point `z` over `φ(y)`, the linearization
`Lin(z) : T_zO → K_z` is an sc-Fredholm operator, onto on every level, of index `d` on every
level (`theorem_3_54_index_locally_constant`,
`linAt_isScFredholm_of_isSurjLinOfIndex`). -/
theorem theorem_3_54_index_locally_constant_sc (hf : B.IsScFredholmSectionTame f) {x₀ : X}
    (hg : B.IsGoodPositionGermTame f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ (Vx : Set X) (d : ℕ), IsOpen Vx ∧ x₀ ∈ Vx ∧
      ∀ y ∈ Vx, IsZeroAt P f y → ∀ (c : StrongBundleChart PX P) (_ : B.IsChart c)
        (_ : y ∈ c.φ.source) (z : c.φ.model.E 1) (_ : c.φ.model.E.toBase 1 z = c.φ y)
        (hzU : c.φ.model.E.toBase 1 z ∈ c.U),
        ∃ (hD : IsScOperator (scDeriv c.U (c.principal f ∘ r c.R) z))
          (hT : c.φ.model.E.IsScSubspace (rangeS (scDeriv c.U (r c.R) z)))
          (hK : c.F.IsScSubspace (rangeS (ρCLM c.isRetraction hzU)))
          (hTK : ∀ x ∈ rangeS (scDeriv c.U (r c.R) z),
            hD.toScOperator 0 x ∈ rangeS (ρCLM c.isRetraction hzU)),
          (∀ x : (c.φ.model.E.ofSubspace hT) 0,
            ((hD.toScOperator.restrict hT hK hTK 0 x).1 : c.F 0) =
              linAt c.U c.R (c.principal f) z ⟨x.1, x.2⟩) ∧
          IsScFredholm (hD.toScOperator.restrict hT hK hTK) ∧
          ∀ m, Surjective ((hD.toScOperator.restrict hT hK hTK) m) ∧
            ((hD.toScOperator.restrict hT hK hTK) m).IsFredholm ∧
            fredholmIndex ((hD.toScOperator.restrict hT hK hTK) m) = d := by
  obtain ⟨Vx, d, hVo, hx₀V, hall⟩ := theorem_3_54_index_locally_constant hf hg hx₀
  exact ⟨Vx, d, hVo, hx₀V, fun y hy hy0 c hc hyV z hz hzU =>
    StrongBundle.linAt_isScFredholm_of_isSurjLinOfIndex hf.toIsScFredholmSection hy0
      (hall y hy hy0) hc hyV hz hzU⟩

end Bundle

end Polyfold
