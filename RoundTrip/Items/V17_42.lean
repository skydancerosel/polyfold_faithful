import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V17_42

set_option maxSynthPendingDepth 3

/-! Round trip for V17_42 (2021 Proposition 17.2.5, p. 770, (17.32): `α ↦ T_αC`, `φ ↦ Tφ` is a
functor `C_1 → Ban`).

`A` is the conjunction of the types of `tangentMorAt_indep` and `proposition_17_2_5`, universe `0`
(`B` uses `GCT.{0}`); `tangentMorAt`, `tangentMorCLE` are vocabulary.

* `tangentChart_tangentMorAt`: the project's `tangentMorAt` satisfies (17.31) through the charts,
  `S_{Ψ'}(Tφ v) = Tσ(q)(S_Ψ v)` (from the definitions and `transMap_comp'`).
* `B_to_A`: `B`'s `T` is `tangentMorAt` for every `Ψ'` (`eq_tangentMorAt`: injectivity of `S_{Ψ'}`
  and the two chart identities); hence `tangentMorAt_indep`; with the non-item lemma
  `coe_tangentMorCLE` (`⇑tangentMorCLE = tangentMorAt` for the reference uniformizer) the three
  parts of `proposition_17_2_5` are `B`'s (17.31), `T(1) = id`, `T(ψφ) = Tψ ∘ Tφ`.
* `A → B` does not hold: `not_B`.  `B` asks for a map `T_αC → T_{α'}C` for EVERY morphism
  `φ : α → α'`, also when `T_{α'}C = ∅`.  Definition 17.1.8 does not ask `F(α) ≠ ∅` nor that `F`
  be invariant under isomorphism; `singleConstruction` (`F(1) = {Ψ₀}`, `F(x) = ∅` otherwise, on
  the reflection GCT) has `T_1 C ≠ ∅`, `T_{-1} C = ∅` and a morphism `1 → -1`.  `A` only speaks of
  `α, α'` with `Fact (TangentObj α)`, `Fact (TangentObj α')`.
* `A_to_B_hU`: with `HasUniformizers` (`F(α) ≠ ∅` for every `α`, which the text presupposes), `A`
  gives `B`: `T φ v := tangentMorAt φ` through the reference uniformizer of `α'` (which has tangents
  since regularity is invariant under isomorphism); (17.31) from `tangentMorAt_indep` and
  `tangentChart_tangentMorAt`; unit and composition from `proposition_17_2_5`.
-/

namespace RoundTrip.V17_42
open Polyfold GCT.PolyfoldConstruction

def A : Prop :=
  (type_of% @Polyfold.GCT.PolyfoldConstruction.tangentMorAt_indep.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_2_5.{0})

theorem A_holds : A :=
  ⟨@Polyfold.GCT.PolyfoldConstruction.tangentMorAt_indep.{0},
    @Polyfold.GCT.PolyfoldConstruction.proposition_17_2_5.{0}⟩

section Key
variable {C : GCT.{0}} {S : C.PolyfoldConstruction}

/-- **(17.31) through the charts for the project's `Tφ`**: `S_{Ψ'}(Tφ v) = Tσ(q)(S_Ψ v)`. -/
theorem tangentChart_tangentMorAt {α α' : C.Obj} (φ : C.Mor) (hs : C.toGroupoidStr.src φ = α)
    (ht : C.toGroupoidStr.tgt φ = α') (Ψ : S.Unif) (hΨ : Ψ.1 ∈ S.F α) (x : Ψ.1.P.Level 1)
    (hx : Ψ.1.obj (Ψ.1.P.levelVal 1 x) = α) (Ψ' : S.Unif) (hΨ' : Ψ'.1 ∈ S.F α')
    (x' : Ψ'.1.P.Level 1) (hx' : Ψ'.1.obj (Ψ'.1.P.levelVal 1 x') = α')
    (v : S.TangentSpaceAt α) :
    S.tangentChart Ψ' hΨ' x' hx' (S.tangentMorAt φ hs ht Ψ' hΨ' x' hx' v) =
      S.transTangentCLM (S.morTr (Ψ.1.P.levelVal 1 x) φ (Ψ'.1.P.levelVal 1 x') hx hs hx' ht)
        rfl rfl (S.tangentChart Ψ hΨ x hx v) := by
  obtain ⟨t, rfl⟩ := tangentVector_surjective α v
  refine Subtype.ext ?_
  refine (tangentChart_mk Ψ' hΨ' x' hx' _).trans ?_
  refine Eq.trans ?_ (transTangentCLM_apply _ rfl rfl _).symm
  change _ = S.transMap _ (S.transMap (S.unitTr t.base (Ψ.1.P.levelVal 1 x) t.obj_eq hx) t.vec)
  have hb := base_transMap (S.morTr t.base φ (Ψ'.1.P.levelVal 1 x') t.obj_eq hs hx' ht)
    (h := t.vec) rfl
  refine (congrFun (transMap_unitTr_congr hb rfl _ _ hx' hx') _).trans ?_
  refine (transMap_unitTr_self _ hx' hb).trans ?_
  exact transMap_comp' (S.morTr (Ψ.1.P.levelVal 1 x) φ (Ψ'.1.P.levelVal 1 x') hx hs hx' ht)
    (S.unitTr t.base (Ψ.1.P.levelVal 1 x) t.obj_eq hx)
    (S.morTr t.base φ (Ψ'.1.P.levelVal 1 x') t.obj_eq hs hx' ht) rfl
    (GroupoidStr.comp_unit_of_eq hs).symm rfl rfl rfl

theorem tangentObj_of_point {α : C.Obj} (Ψ : S.Unif) (hΨ : Ψ.1 ∈ S.F α) (x : Ψ.1.P.Level 1)
    (hx : Ψ.1.obj (Ψ.1.P.levelVal 1 x) = α) : S.TangentObj α :=
  ⟨(regularity_eq_of_mem hΨ hx 1).2 (MPolyfold.levelVal_mem _), ⟨_, hΨ⟩⟩

/-- `B`'s `Tφ` is the project's `tangentMorAt` (for every choice of `Ψ'`). -/
theorem eq_tangentMorAt
    (T : ∀ {α α' : C.Obj} (φ : C.Mor), C.toGroupoidStr.src φ = α → C.toGroupoidStr.tgt φ = α' →
        S.TangentSpaceAt α → S.TangentSpaceAt α')
    (h31 : ∀ (α α' : C.Obj) (φ : C.Mor) (hs : C.toGroupoidStr.src φ = α)
          (ht : C.toGroupoidStr.tgt φ = α'), S.TangentObj α → S.TangentObj α' →
        ∀ (Ψ : S.Unif) (hΨ : Ψ.1 ∈ S.F α) (x : Ψ.1.P.Level 1)
          (hx : Ψ.1.obj (Ψ.1.P.levelVal 1 x) = α)
          (Ψ' : S.Unif) (hΨ' : Ψ'.1 ∈ S.F α') (x' : Ψ'.1.P.Level 1)
          (hx' : Ψ'.1.obj (Ψ'.1.P.levelVal 1 x') = α') (v : S.TangentSpaceAt α),
          S.tangentChart Ψ' hΨ' x' hx' (T φ hs ht v) =
            S.transTangentCLM
              (S.morTr (Ψ.1.P.levelVal 1 x) φ (Ψ'.1.P.levelVal 1 x') hx hs hx' ht) rfl rfl
              (S.tangentChart Ψ hΨ x hx v))
    {α α' : C.Obj} (φ : C.Mor) (hs : C.toGroupoidStr.src φ = α)
    (ht : C.toGroupoidStr.tgt φ = α') (Ψ' : S.Unif) (hΨ' : Ψ'.1 ∈ S.F α') (x' : Ψ'.1.P.Level 1)
    (hx' : Ψ'.1.obj (Ψ'.1.P.levelVal 1 x') = α') :
    T φ hs ht = S.tangentMorAt φ hs ht Ψ' hΨ' x' hx' := by
  funext v
  have hα := tangentObj_of_tangentSpaceAt v
  refine (S.tangentChart Ψ' hΨ' x' hx').injective ?_
  rw [h31 α α' φ hs ht hα (tangentObj_of_point Ψ' hΨ' x' hx') (S.refUnif hα) (refUnif_mem hα)
    (S.refPoint hα) (obj_refPoint hα) Ψ' hΨ' x' hx' v,
    tangentChart_tangentMorAt φ hs ht (S.refUnif hα) (refUnif_mem hα) (S.refPoint hα)
      (obj_refPoint hα) Ψ' hΨ' x' hx' v]

end Key

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun {C S} α α' φ hs ht Ψ₁ hΨ₁ x₁ hx₁ Ψ₂ hΨ₂ x₂ hx₂ => ?_, fun {C S} => ?_⟩
  · obtain ⟨T, h31, -, -⟩ := hB C S
    exact (eq_tangentMorAt T h31 φ hs ht Ψ₁ hΨ₁ x₁ hx₁).symm.trans
      (eq_tangentMorAt T h31 φ hs ht Ψ₂ hΨ₂ x₂ hx₂)
  · obtain ⟨T, h31, hunit, hcomp⟩ := hB C S
    refine ⟨fun α α' hα hα' φ hs ht Ψ' hΨ' x' hx' => ?_, fun α hα => ?_,
      fun α α' α'' hα hα' hα'' φ ψ hs ht hs' ht' => ?_⟩
    · rw [coe_tangentMorCLE, ← eq_tangentMorAt T h31, ← eq_tangentMorAt T h31]
    · refine ContinuousLinearEquiv.ext ?_
      rw [coe_tangentMorCLE, ← eq_tangentMorAt T h31, hunit α hα.out]
      rfl
    · refine ContinuousLinearEquiv.ext ?_
      change ⇑(S.tangentMorCLE _ _ _) = ⇑(S.tangentMorCLE ψ hs' ht') ∘ ⇑(S.tangentMorCLE φ hs ht)
      rw [coe_tangentMorCLE, coe_tangentMorCLE, coe_tangentMorCLE, ← eq_tangentMorAt T h31,
        ← eq_tangentMorAt T h31, ← eq_tangentMorAt T h31]
      exact hcomp α α' α'' φ ψ hα.out hα'.out hα''.out hs ht hs' ht' _ _

/-- The main conjunct alone. -/
theorem B_to_main : B → (type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_2_5.{0}) :=
  fun h => (B_to_A h).2

/-! ### `A ⇒ B` under `F(α) ≠ ∅` for all `α` -/

/-- `B` restricted to polyfold structures with `HasUniformizers` (`F(α) ≠ ∅` for every `α`). -/
def B_hU : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction), S.HasUniformizers →
    ∃ T : ∀ {α α' : C.Obj} (φ : C.Mor), C.toGroupoidStr.src φ = α → C.toGroupoidStr.tgt φ = α' →
        S.TangentSpaceAt α → S.TangentSpaceAt α',
      (∀ (α α' : C.Obj) (φ : C.Mor) (hs : C.toGroupoidStr.src φ = α)
          (ht : C.toGroupoidStr.tgt φ = α'), S.TangentObj α → S.TangentObj α' →
        ∀ (Ψ : S.Unif) (hΨ : Ψ.1 ∈ S.F α) (x : Ψ.1.P.Level 1)
          (hx : Ψ.1.obj (Ψ.1.P.levelVal 1 x) = α)
          (Ψ' : S.Unif) (hΨ' : Ψ'.1 ∈ S.F α') (x' : Ψ'.1.P.Level 1)
          (hx' : Ψ'.1.obj (Ψ'.1.P.levelVal 1 x') = α') (v : S.TangentSpaceAt α),
          S.tangentChart Ψ' hΨ' x' hx' (T φ hs ht v) =
            S.transTangentCLM
              (S.morTr (Ψ.1.P.levelVal 1 x) φ (Ψ'.1.P.levelVal 1 x') hx hs hx' ht) rfl rfl
              (S.tangentChart Ψ hΨ x hx v)) ∧
      (∀ (α : C.Obj), S.TangentObj α →
        ∀ (h₁ : C.toGroupoidStr.src (C.toGroupoidStr.unit α) = α)
          (h₂ : C.toGroupoidStr.tgt (C.toGroupoidStr.unit α) = α),
          T (C.toGroupoidStr.unit α) h₁ h₂ = id) ∧
      (∀ (α α' α'' : C.Obj) (φ ψ : C.Mor), S.TangentObj α → S.TangentObj α' →
          S.TangentObj α'' →
        ∀ (hs : C.toGroupoidStr.src φ = α) (ht : C.toGroupoidStr.tgt φ = α')
          (hs' : C.toGroupoidStr.src ψ = α') (ht' : C.toGroupoidStr.tgt ψ = α'')
          (h₁ : C.toGroupoidStr.src (C.toGroupoidStr.comp ψ φ) = α)
          (h₂ : C.toGroupoidStr.tgt (C.toGroupoidStr.comp ψ φ) = α''),
          T (C.toGroupoidStr.comp ψ φ) h₁ h₂ = T ψ hs' ht' ∘ T φ hs ht)

theorem B_to_B_hU : B → B_hU := fun h C S _ => h C S

/-- Under `HasUniformizers`, a morphism `α → α'` carries `T_αC ≠ ∅` to `α'` having tangents. -/
theorem tangentObj_tgt {C : GCT.{0}} {S : C.PolyfoldConstruction} (hU : S.HasUniformizers)
    {α α' : C.Obj} {φ : C.Mor} (hs : C.toGroupoidStr.src φ = α) (ht : C.toGroupoidStr.tgt φ = α')
    (v : S.TangentSpaceAt α) : S.TangentObj α' := by
  obtain ⟨⟨Ψ, q, hiso, hq⟩, -⟩ := tangentObj_of_tangentSpaceAt v
  exact ⟨⟨Ψ, q, hiso.trans ⟨φ, hs, ht⟩, hq⟩, hU α'⟩

theorem A_to_B_hU : A → B_hU := by
  rintro ⟨hind, h5⟩ C S hU
  obtain ⟨hcle, hunit, hcomp⟩ := @h5 C S
  let T : ∀ {α α' : C.Obj} (φ : C.Mor), C.toGroupoidStr.src φ = α →
      C.toGroupoidStr.tgt φ = α' → S.TangentSpaceAt α → S.TangentSpaceAt α' :=
    fun {α α'} φ hs ht v => S.tangentMorAt φ hs ht (S.refUnif (tangentObj_tgt hU hs ht v))
      (refUnif_mem _) (S.refPoint _) (obj_refPoint _) v
  -- `T` is `tangentMorAt` for every choice of `Ψ'` (A's `tangentMorAt_indep`)
  have hT : ∀ {α α' : C.Obj} (φ : C.Mor) (hs : C.toGroupoidStr.src φ = α)
      (ht : C.toGroupoidStr.tgt φ = α') (Ψ' : S.Unif) (hΨ' : Ψ'.1 ∈ S.F α')
      (x' : Ψ'.1.P.Level 1) (hx' : Ψ'.1.obj (Ψ'.1.P.levelVal 1 x') = α'),
      T φ hs ht = S.tangentMorAt φ hs ht Ψ' hΨ' x' hx' := by
    intro α α' φ hs ht Ψ' hΨ' x' hx'
    funext v
    exact congrFun (hind φ hs ht _ _ _ _ Ψ' hΨ' x' hx') v
  -- and it is `tangentMorCLE` (A's `proposition_17_2_5`, first part)
  have hTc : ∀ {α α' : C.Obj} [Fact (S.TangentObj α)] [hα' : Fact (S.TangentObj α')]
      (φ : C.Mor) (hs : C.toGroupoidStr.src φ = α) (ht : C.toGroupoidStr.tgt φ = α'),
      T φ hs ht = ⇑(S.tangentMorCLE φ hs ht) := by
    intro α α' _ hα' φ hs ht
    rw [hT φ hs ht _ (refUnif_mem hα'.out) (S.refPoint hα'.out) (obj_refPoint hα'.out)]
    exact (hcle α α' φ hs ht _ (refUnif_mem hα'.out) (S.refPoint hα'.out)
      (obj_refPoint hα'.out)).symm
  refine ⟨@T, fun α α' φ hs ht hα hα' Ψ hΨ x hx Ψ' hΨ' x' hx' v => ?_, fun α hα h₁ h₂ => ?_,
    fun α α' α'' φ ψ hα hα' hα'' hs ht hs' ht' h₁ h₂ => ?_⟩
  · rw [hT φ hs ht Ψ' hΨ' x' hx']
    exact tangentChart_tangentMorAt φ hs ht Ψ hΨ x hx Ψ' hΨ' x' hx' v
  · have : Fact (S.TangentObj α) := ⟨hα⟩
    rw [hTc]
    exact congrArg DFunLike.coe (hunit α)
  · have : Fact (S.TangentObj α) := ⟨hα⟩
    have : Fact (S.TangentObj α') := ⟨hα'⟩
    have : Fact (S.TangentObj α'') := ⟨hα''⟩
    rw [hTc, hTc, hTc]
    exact congrArg DFunLike.coe (hcomp α α' α'' φ ψ hs ht hs' ht')

/-! ### `B` does not hold when `F` is not invariant under isomorphism

On the reflection GCT `ℤ/2 ⋉ ℝ` take `F(x) = {Ψ₀}` for `x = 1` and `F(x) = ∅` otherwise (the
tautological uniformizer `Ψ₀`, with the transition M-polyfold of `reflectionConstruction`).  This
satisfies Definition 17.1.8 (the project's `PolyfoldConstruction`).  Then `T_1 C ≠ ∅` but
`T_{-1} C = ∅` (`F(-1) = ∅`), while `(-1, 1) : 1 → -1` is a morphism; `B` asks for a map
`T_1 C → T_{-1} C`. -/

section Counter

open EpGroupoid.Examples

/-- The point `1 ∈ ℝ`. -/
abbrev one₀ : Fin 1 → ℝ := fun _ => 1

/-- `Ψ₀` as the local uniformizer of the reflection GCT. -/
abbrev taut₀ : GCT.reflection.LocalUniformizer :=
  GCT.LocalUniformizer.tautological _ isScSmoothMap_units_smul

theorem single_eq (Ψ : GCT.Unif fun x : GCT.reflection.Obj => {L | x = one₀ ∧ L = taut₀}) :
    Ψ.1 = GCT.LocalUniformizer.tautological _ isScSmoothMap_units_smul := Ψ.2.choose_spec.2

/-- **The construction `F(1) = {Ψ₀}`, `F(x) = ∅` for `x ≠ 1`.** -/
noncomputable def singleConstruction : GCT.reflection.PolyfoldConstruction where
  F x := {L | x = one₀ ∧ L = taut₀}
  isAt x Ψ hΨ := by
    rw [hΨ.2]
    exact GCT.LocalUniformizer.tautological_isAt isScSmoothMap_units_smul x
  topM Ψ Ψ' := twistTopOf isScSmoothMap_units_smul (TranslationTwist.refl ℤˣ (Fin 1 → ℝ))
    Ψ.1 Ψ'.1 (single_eq Ψ) (single_eq Ψ')
  t2M Ψ Ψ' := twistT2Of isScSmoothMap_units_smul (TranslationTwist.refl ℤˣ (Fin 1 → ℝ))
    Ψ.1 Ψ'.1 (single_eq Ψ) (single_eq Ψ')
  paraM Ψ Ψ' := twistParaOf isScSmoothMap_units_smul (TranslationTwist.refl ℤˣ (Fin 1 → ℝ))
    Ψ.1 Ψ'.1 (single_eq Ψ) (single_eq Ψ')
  M Ψ Ψ' := twistMOf isScSmoothMap_units_smul (TranslationTwist.refl ℤˣ (Fin 1 → ℝ))
    Ψ.1 Ψ'.1 (single_eq Ψ) (single_eq Ψ')
  isLocalScDiffeo_src := by
    rintro ⟨L, x, -, rfl⟩ ⟨L', x', -, rfl⟩
    exact twist_isLocalScDiffeo_src _ _
  isLocalScDiffeo_tgt := by
    rintro ⟨L, x, -, rfl⟩ ⟨L', x', -, rfl⟩
    exact twist_isLocalScDiffeo_tgt _ _
  isScSmoothMap_unit := by
    rintro ⟨L, x, -, rfl⟩
    exact twist_isScSmoothMap_unit _ _
  isScSmoothMap_inv := by
    rintro ⟨L, x, -, rfl⟩ ⟨L', x', -, rfl⟩
    exact twist_isScSmoothMap_inv _ _
  isScSmoothMap_mul := by
    rintro ⟨L, x, -, rfl⟩ ⟨L', x', -, rfl⟩ ⟨L'', x'', -, rfl⟩
    exact twist_isScSmoothMap_mul _ _

theorem tangentObj_one₀ : singleConstruction.TangentObj one₀ :=
  ⟨⟨⟨taut₀, one₀, rfl, rfl⟩, one₀, GroupoidStr.isomorphic_refl _ _,
    by rw [rnPolyfold_levelSet]; exact Set.mem_univ _⟩, ⟨taut₀, rfl, rfl⟩⟩

/-- **`B` does not hold**: in `singleConstruction`, `(-1, 1) : 1 → -1` with `T_1 C ≠ ∅` and
`T_{-1} C = ∅`. -/
theorem not_B : ¬ B := by
  intro h
  obtain ⟨T, -, -, -⟩ := h GCT.reflection singleConstruction
  let φ : GCT.reflection.Mor := ((-1 : ℤˣ), one₀)
  let e : singleConstruction.TangentSpaceAt one₀ :=
    (singleConstruction.refChart tangentObj_one₀).symm 0
  let e' : singleConstruction.TangentSpaceAt ((-1 : ℤˣ) • one₀) :=
    T (α := one₀) (α' := (-1 : ℤˣ) • one₀) φ rfl rfl e
  obtain ⟨-, L, hL, -⟩ := tangentObj_of_tangentSpaceAt e'
  have h0 := congrFun hL 0
  rw [EpGroupoid.Examples.units_smul_rn_neg_one] at h0
  norm_num at h0

end Counter

#rt_check RoundTrip.V17_42.A_to_B_hU [Polyfold.GCT.PolyfoldConstruction.tangentMorAt_indep,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_2_5]

#rt_check RoundTrip.V17_42.not_B [Polyfold.GCT.PolyfoldConstruction.tangentMorAt_indep,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_2_5]
#rt_check RoundTrip.V17_42.B_to_A [Polyfold.GCT.PolyfoldConstruction.tangentMorAt_indep,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_2_5]
#rt_check RoundTrip.V17_42.B_to_main [Polyfold.GCT.PolyfoldConstruction.tangentMorAt_indep,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_2_5]
#rt_overlap RoundTrip.V17_42.B_to_A [Polyfold.GCT.PolyfoldConstruction.tangentMorAt_indep,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_2_5]

end RoundTrip.V17_42
