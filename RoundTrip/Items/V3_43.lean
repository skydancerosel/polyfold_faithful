import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_43

/-!
Round trip for V3_43 (Definition 3.48: filling, restated for a tame strong local bundle).
Refreshed 2026-11-02 (HEAD, germ reading).

The decls list only definitions (`Polyfold.IsFillingGerm`, the canonical germ-reading filling, and
`Polyfold.IsFillerOf`), so `A = True`; the comparison is between the project's notions and B's.
B asserts `IsFilledVersion hU hR h0 f g ↔ IsFillingB hU hR h0 f g` for every tame strong local
bundle and every sc-smooth section germ `f`, i.e. it identifies the text's filling with the
project's WHOLE-CHART `IsFilledVersion` (the project's notion at the audit).

* `germ_iff_B` (new): the canonical notion `IsFillingGerm` is B's `IsFillingB` field for field (the
  same germ `G ⊆ U`, conditions (1), (2), the derivative family `Dk` of the fill defect on `G` and
  the isomorphism `ker Dr(0) ≃ ker ρ(0)` agreeing with `Dk(0)`), so `B_germ` — B with
  `IsFillingGerm` in place of `IsFilledVersion` — is proved.
* `proj_to_B` (no hypothesis of `A` used): the project's filled version is a text filling (germ
  `ofSet U`; the derivative family `scDeriv U k` of `k = [1 − ρ(r(·))]g`, sc¹ on `U` by
  `IsFillerOf.isSc1`; the equivalence of `IsFillerOf.linearization`).
* `not_B`: **B as written is still false**: it names `IsFilledVersion`, which still asks `g` to be
  sc-smooth on the whole `U`, while the text's filling is a germ.  Counter-model: `E = F = ℝ`
  (constant sc-structure), `C = U = ℝ`, `R = id` (tame), `f = g = step` with `step = 0` on
  `(−∞, 1)` and `1` on `[1, ∞)`: `g` is an sc-smooth germ on `ofSet (−∞, 1)`, `k = 0`, both kernels
  of (3) are `0`, so `IsFillingB` holds, but `step` is not continuous, so it is not sc-smooth on
  `U = ℝ`.  The counter-model does NOT apply to the current notion: `step` is an `IsFillingGerm`
  filling (by `germ_iff_B`).
* `B_corrected`: the project's `IsFilledVersion` is exactly "`g` sc-smooth on `U` and a filling in
  the text's sense" (`←`: `k` is sc¹ on `U` by the chain rule, and B's `Dk 0` is `scDeriv U k 0`
  by uniqueness of the derivative on the germ at `0`).
-/

namespace RoundTrip.V3_43
open Polyfold Set Filter Topology StrongRetr

def A : Prop := True

theorem A_holds : A := trivial

section Glue

variable {E F : ScBanach} {C U : Set (E.lvl 0)} {R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0}

/-- The map `y ↦ [1 − ρ(r(y))]g(y)` is sc-smooth for `g` sc-smooth (chain rule; from V3_9). -/
theorem k_isScSmooth (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    {g : E.lvl 0 → F.lvl 0} (hg : IsScSmooth U g) :
    IsScSmooth U fun y => g y - ρ R (r R y) (g y) := by
  have hrs : IsScSmooth U (r R) := r_isScSmooth hU hR
  have hpair := hrs.scPair hU.isScDomain hg
  have hfib : IsScSmooth (U ×ˢ univ) fun p : (E.prod F).lvl 0 => (R p).2 :=
    hR.isScSmooth_zero.snd (hU.prod_univ F).isScDomain
  have hcomp := IsScSmooth.comp hU.isScDomain (hU.prod_univ F).isScDomain hfib hpair
    fun y hy => ⟨r_mem hR hy, mem_univ _⟩
  exact (hg.sub hU.isScDomain hcomp).congr hU.isScDomain fun y _ => rfl

/-- An sc¹ map on a relatively open `U ∋ 0` is an sc¹-germ on `ofSet U` with the derivative
family `scDeriv U k`. -/
theorem isSc1GermWith_ofSet (hU : IsRelOpenInQuadrant E C U) (h0 : (0 : E.lvl 0) ∈ U)
    {k : E.lvl 0 → F.lvl 0} (hk : IsSc1 U k) :
    IsSc1GermWith (ScNbhdGerm.ofSet hU.relOpen h0) k (scDeriv U k) :=
  ⟨hk.isSc0.isSc0Germ hU.relOpen h0, hk.isSc1With_scDeriv.hasFDerivWithinAt, by
    have := hk.tangentMap_isSc0
    rw [ScNbhdGerm.ofSet_tangent]
    exact this.isSc0Germ _ _⟩

/-- **project ⇒ text**: a filled version is a filling in the text's (germ) sense. -/
theorem proj_to_B (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (h0 : (0 : E.lvl 0) ∈ U) {f g : E.lvl 0 → F.lvl 0} (h : IsFilledVersion hU hR h0 f g) :
    IsFillingB hU hR h0 f g := by
  have hQ := hU.isPartialQuadrant.isQuadrantLike
  obtain ⟨Φ, hΦ⟩ := h.filler.linearization
  exact ⟨ScNbhdGerm.ofSet hU.relOpen h0, fun u hu => hu,
    h.isScSmooth.isScSmoothGerm hQ hU.relOpen h0, h.filler.eq_on, h.filler.mem_of_fixed,
    scDeriv U (fillDefect R g), isSc1GermWith_ofSet hU h0 h.filler.isSc1, Φ, hΦ⟩

/-- **text ⇒ project, for `g` sc-smooth on `U`**. -/
theorem B_to_proj (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (h0 : (0 : E.lvl 0) ∈ U) {f g : E.lvl 0 → F.lvl 0} (hg : IsScSmooth U g)
    (h : IsFillingB hU hR h0 f g) : IsFilledVersion hU hR h0 f g := by
  obtain ⟨G, hGU, -, h1, h2, Dk, hDk, e, he⟩ := h
  have hQ := hU.isPartialQuadrant.isQuadrantLike
  have hk : IsSc1 U (fillDefect R g) := (k_isScSmooth hU hR hg).isSc1
  have hsub : ∀ m, G.U m ⊆ (ScNbhdGerm.ofSet hU.relOpen h0).U m := fun m x hx => by
    rw [ScNbhdGerm.ofSet_U, ScBanach.mem_lvlSet]
    exact hGU (G.toBase_mem hx)
  have hDk' : IsSc1GermWith G (fillDefect R g) (scDeriv U (fillDefect R g)) :=
    (isSc1GermWith_ofSet hU h0 hk).mono hsub
  have heq : Dk 0 = scDeriv U (fillDefect R g) 0 :=
    hDk.eq_of_uniqueDiffWithinAt hDk' (G.zero_mem 1) (G.uniqueDiffWithinAt hQ 1 (G.zero_mem 1))
  refine ⟨hg, h1, h2, hk, e, fun v => ?_⟩
  rw [he v, heq]
  rfl

/-- **The corrected dictionary**: the project's filled version is "`g` sc-smooth on `U` and a
filling in the text's sense". -/
theorem B_corrected (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (h0 : (0 : E.lvl 0) ∈ U) (f g : E.lvl 0 → F.lvl 0) :
    IsFilledVersion hU hR h0 f g ↔ IsScSmooth U g ∧ IsFillingB hU hR h0 f g :=
  ⟨fun h => ⟨h.isScSmooth, proj_to_B hU hR h0 h⟩, fun h => B_to_proj hU hR h0 h.1 h.2⟩

/-- **The canonical germ filling is B's text filling**, field for field. -/
theorem germ_iff_B (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (h0 : (0 : E.lvl 0) ∈ U) (f g : E.lvl 0 → F.lvl 0) :
    IsFillingGerm hU hR h0 f g ↔ IsFillingB hU hR h0 f g := by
  constructor
  · intro h
    obtain ⟨G, hGU, hg, Dk, hDk, Φ, hΦ⟩ := h.germ
    exact ⟨G, hGU, hg, h.eq_on, h.mem_of_fixed, Dk, hDk, Φ, hΦ⟩
  · rintro ⟨G, hGU, hg, h1, h2, Dk, hDk, e, he⟩
    exact ⟨h1, h2, G, hGU, hg, Dk, hDk, e, he⟩

end Glue

/-- **B with the canonical germ filling in place of `IsFilledVersion`**: proved. -/
theorem B_germ :
    ∀ (E F : ScBanach) (C U : Set (E.lvl 0)) (R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0)
      (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R) (h0 : 0 ∈ U),
      (IsStrongBundleRetraction.baseRetraction hU hR).IsTame → StrongRetr.r R 0 = 0 →
      ∀ f g : E.lvl 0 → F.lvl 0, IsSectionGermB (C := C) (U := U) R f →
        (IsFillingGerm hU hR h0 f g ↔ IsFillingB hU hR h0 f g) :=
  fun _ _ _ _ _ hU hR h0 _ _ f g _ => germ_iff_B hU hR h0 f g

/-! ### The counter-model -/

/-- The step function: `0` on `(−∞, 1)`, `1` on `[1, ∞)`. -/
noncomputable def step : ℝ → ℝ := fun y => if y < 1 then 0 else 1

lemma step_not_continuous : ¬ Continuous step := by
  intro hc
  have hmem : (1 / 2 : ℝ) ∈ Icc (step 0) (step 2) := by
    simp only [step]; norm_num
  obtain ⟨y, hy⟩ := intermediate_value_univ (0 : ℝ) 2 hc hmem
  simp only [step] at hy
  split_ifs at hy <;> norm_num at hy

/-- **B is false**: a germ filling need not be a project filled version. -/
theorem not_B : ¬ B := by
  intro hB
  have hU : IsRelOpenInQuadrant (ScBanach.const ℝ) univ univ :=
    ⟨isPartialQuadrant_univ _, univ, isOpen_univ, (inter_univ _).symm⟩
  have hR : IsStrongBundleRetraction (E := ScBanach.const ℝ) (F := ScBanach.const ℝ) univ id :=
    isStrongBundleRetraction_id
  have h0 : (0 : (ScBanach.const ℝ).lvl 0) ∈ (univ : Set ((ScBanach.const ℝ).lvl 0)) := mem_univ _
  have htame : (IsStrongBundleRetraction.baseRetraction hU hR).IsTame :=
    (ScRetraction.id_isTame hU).congr rfl (fun _ _ => rfl)
  have hr0 : StrongRetr.r (id : (ScBanach.const ℝ).lvl 0 × (ScBanach.const ℝ).lvl 0 → _) 0 = 0 :=
    rfl
  -- the germ on `(−∞, 1)`
  have hrel : ∃ O : Set ((ScBanach.const ℝ).lvl 0), IsOpen O ∧
      (Iio (1 : ℝ) : Set ((ScBanach.const ℝ).lvl 0)) = O ∩ univ :=
    ⟨Iio 1, isOpen_Iio, (inter_univ _).symm⟩
  have h0' : (0 : (ScBanach.const ℝ).lvl 0) ∈ (Iio (1 : ℝ) : Set ((ScBanach.const ℝ).lvl 0)) := by
    show (0 : ℝ) < 1; norm_num
  have hQ : IsQuadrantLike (ScBanach.const ℝ) univ := (isPartialQuadrant_univ _).isQuadrantLike
  have hdom : IsScDomain (ScBanach.const ℝ) (Iio (1 : ℝ)) :=
    (⟨isPartialQuadrant_univ _, hrel⟩ :
      IsRelOpenInQuadrant (ScBanach.const ℝ) univ (Iio (1 : ℝ))).isScDomain
  have hsm : ∀ φ : ℝ → ℝ, (∀ y < 1, φ y = 0) →
      IsScSmoothGerm (F := ScBanach.const ℝ) (ScNbhdGerm.ofSet hrel h0') φ := by
    intro φ hφ
    have : IsScSmooth (E := ScBanach.const ℝ) (F := ScBanach.const ℝ) (Iio (1 : ℝ)) φ :=
      isScSmooth_of_bijective_toBase (bijective_toBase_const ℝ) (bijective_toBase_const ℝ) hdom
        (contDiffOn_const.congr fun y hy => hφ y hy)
    exact this.isScSmoothGerm hQ hrel h0'
  have hstep : ∀ y < (1 : ℝ), step y = 0 := fun y hy => if_pos hy
  have hsec : IsSectionGermB (C := univ) (U := univ)
      (id : (ScBanach.const ℝ).lvl 0 × (ScBanach.const ℝ).lvl 0 → _) step :=
    ⟨Eventually.of_forall fun _ _ => rfl, ScNbhdGerm.ofSet hrel h0', subset_univ _,
      hsm _ hstep⟩
  -- both kernels of condition (3) are trivial
  have hker1 : ∀ v ∈ LinearMap.ker (scDeriv (E := ScBanach.const ℝ) (F := ScBanach.const ℝ) univ
      (StrongRetr.r (id : (ScBanach.const ℝ).lvl 0 × (ScBanach.const ℝ).lvl 0 → _)) 0 :
        ℝ →ₗ[ℝ] ℝ), v = 0 := by
    intro v hv
    have hid : (StrongRetr.r (id : (ScBanach.const ℝ).lvl 0 × (ScBanach.const ℝ).lvl 0 → _)) =
        (_root_.id : ℝ → ℝ) := rfl
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hid,
      scDeriv_univ_const (V := ℝ) (V' := ℝ) contDiff_id] at hv
    simpa using hv
  have hker2 : ∀ v ∈ LinearMap.ker (StrongRetr.ρCLM hR h0 : ℝ →ₗ[ℝ] ℝ), v = 0 := by
    intro v hv
    exact hv
  have hfill : IsFillingB hU hR h0 step step := by
    refine ⟨ScNbhdGerm.ofSet hrel h0', subset_univ _, hsm _ hstep,
      Eventually.of_forall fun _ _ => rfl,
      Eventually.of_forall fun y _ _ => ⟨y, mem_univ _, rfl⟩, ?_⟩
    have hk : IsScSmoothGerm (F := ScBanach.const ℝ) (ScNbhdGerm.ofSet hrel h0')
        (fillDefect id step) := hsm _ fun y _ => sub_self (step y)
    refine ⟨_, (hk 1).1.isSc1GermWith_scDerivGerm, ?_⟩
    have : Subsingleton (LinearMap.ker (scDeriv (E := ScBanach.const ℝ)
        (F := ScBanach.const ℝ) univ
        (StrongRetr.r (id : (ScBanach.const ℝ).lvl 0 × (ScBanach.const ℝ).lvl 0 → _)) 0 :
          ℝ →ₗ[ℝ] ℝ)) :=
      ⟨fun a b => Subtype.ext (by rw [hker1 a a.2, hker1 b b.2])⟩
    have : Subsingleton (LinearMap.ker (StrongRetr.ρCLM hR h0 : ℝ →ₗ[ℝ] ℝ)) :=
      ⟨fun a b => Subtype.ext (by rw [hker2 a a.2, hker2 b b.2])⟩
    refine ⟨⟨LinearEquiv.ofSubsingleton _ _, continuous_of_const fun _ _ => Subsingleton.elim _ _,
      continuous_of_const fun _ _ => Subsingleton.elim _ _⟩, fun v => ?_⟩
    rw [Subsingleton.elim v 0, map_zero]
    simp
  have hfv := (hB (ScBanach.const ℝ) (ScBanach.const ℝ) univ univ id hU hR h0 htame hr0 step step
    hsec).2 hfill
  have hc : ContinuousOn step univ := hfv.isScSmooth.isSc1.isSc0.continuousOn_base
  exact step_not_continuous (continuousOn_univ.1 hc)

/-- Trivial (`A = True`); flagged as vacuous. -/
theorem B_to_A : B → A := fun _ => trivial

#rt_check RoundTrip.V3_43.B_to_A []
#rt_overlap RoundTrip.V3_43.B_to_A []
#rt_check RoundTrip.V3_43.not_B []
#rt_check RoundTrip.V3_43.B_corrected []
#rt_check RoundTrip.V3_43.B_germ []

end RoundTrip.V3_43
