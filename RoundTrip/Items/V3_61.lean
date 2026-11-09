import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_61

/-! Round trip for V3_61 (Corollary 3.75: `f : U → V` is a homeomorphism).

`A` is the type of `Polyfold.corollary_3_8_19` (no universe parameters: `V : Type`).

`A → B`: `B`'s hypotheses (`Hyp373`) give the project's `InvData C U f 1` (C^∞ ⇒ C¹; the
`d_C`-equality is used only through `d_C = 0 ⟺ interior`, `degIndex_eq_zero_iff`).  `A` gives
continuity of `f` and of `g = invFunOn f U` and the two inverse identities, from which the
homeomorphism `U ≃ₜ f(U)` is assembled.  `A` does **not** contain the relative openness of
`f(U)` (it is in `proposition_3_8_17` / `InvData.image_relOpen`, Lemma 3.74); that clause of `B` is
supplied by the separate project theorem `InvData.image_relOpen`.

`B → A` is not proved: `A` holds for `C^j` maps (`j ≥ 1`) preserving only interior points, without
`0 ∈ U`, `f(0) = 0`, while `B` assumes `C^∞`, `0 ∈ U`, `f(0) = 0` and `d_C(x) = d_C(f(x))`.  The
diagnostic `B_to_A_smooth` shows that `B` yields `A`'s conclusion for every map satisfying `B`'s
hypotheses (the restriction of `A` to `B`'s hypothesis set). -/

open Set Filter Topology Function Module
open scoped ContDiff NNReal

noncomputable section

namespace RoundTrip.V3_61
open Polyfold

/-- The project's statement (no universe parameters; `V : Type`). -/
def A : Prop := type_of% @Polyfold.corollary_3_8_19

theorem A_holds : A := @Polyfold.corollary_3_8_19

/-- `B`'s hypotheses give the project's `InvData` with `j = 1`. -/
lemma invData_of_hyp {Rn : Type} [NormedAddCommGroup Rn] [NormedSpace ℝ Rn]
    [FiniteDimensional ℝ Rn] {C U : Set Rn} {f : Rn → Rn} (h : Hyp373 Rn C U f) :
    InvData C U f 1 := by
  obtain ⟨hC, hUrel, hconv, -, hf, hmaps, -, hDf, hdeg⟩ := h
  have hUC : U ⊆ C := by obtain ⟨O, -, rfl⟩ := hUrel; exact inter_subset_right
  refine ⟨hC, hUrel, hconv, hmaps, le_rfl, contDiffOn_infty.1 hf 1, fun x hx => hDf x hx,
    fun x hx => ?_⟩
  rw [← degIndex_eq_zero_iff hC (hUC hx), ← degIndex_eq_zero_iff hC (hmaps hx), hdeg x hx]

/-- The homeomorphism `U ≃ₜ f(U)` from continuity of `f`, `g` and the inverse identities. -/
def homeoOf {Rn : Type} [TopologicalSpace Rn] {U : Set Rn} {f g : Rn → Rn}
    (hf : ContinuousOn f U) (hg : ContinuousOn g (f '' U)) (hgU : ∀ y ∈ f '' U, g y ∈ U)
    (hgf : ∀ x ∈ U, g (f x) = x) (hfg : ∀ y ∈ f '' U, f (g y) = y) : U ≃ₜ (f '' U) where
  toFun x := ⟨f x, mem_image_of_mem f x.2⟩
  invFun y := ⟨g y, hgU y y.2⟩
  left_inv x := Subtype.ext (hgf x x.2)
  right_inv y := Subtype.ext (hfg y y.2)
  continuous_toFun := (continuousOn_iff_continuous_domRestrict.1 hf).subtype_mk _
  continuous_invFun := (continuousOn_iff_continuous_domRestrict.1 hg).subtype_mk _

theorem A_to_B : A → B := by
  intro hA Rn _ _ _ C U f hyp
  have h := invData_of_hyp hyp
  obtain ⟨hfc, hgc, hgf, hfg⟩ := hA h
  refine ⟨h.image_relOpen, homeoOf hfc hgc (fun y hy => Function.invFunOn_mem hy) hgf hfg,
    fun x => rfl⟩

#rt_check RoundTrip.V3_61.A_to_B [Polyfold.corollary_3_8_19]
#rt_overlap RoundTrip.V3_61.A_to_B [Polyfold.corollary_3_8_19]

/-! ### `B → A` on `B`'s hypothesis set (diagnostic)

`B → A` is not proved: `A` is stated for `InvData C U f j` (`C^j`, `j ≥ 1`, only interior points
preserved, no `0 ∈ U`, no `f(0) = 0`), and such an `f` need not satisfy `B`'s hypotheses.  On
`B`'s hypothesis set `B` does give `A`'s conclusion. -/

/-- `A`'s conclusion for the maps satisfying `B`'s hypotheses. -/
def ARestricted : Prop :=
  ∀ (Rn : Type) [NormedAddCommGroup Rn] [NormedSpace ℝ Rn] [FiniteDimensional ℝ Rn]
    (C U : Set Rn) (f : Rn → Rn), Hyp373 Rn C U f →
      ContinuousOn f U ∧ ContinuousOn (InvData.inv U f) (f '' U) ∧
        (∀ x ∈ U, InvData.inv U f (f x) = x) ∧ ∀ y ∈ f '' U, f (InvData.inv U f y) = y

theorem B_to_A_smooth : B → ARestricted := by
  intro hB Rn _ _ _ C U f hyp
  obtain ⟨-, ⟨e, he⟩⟩ := hB Rn C U f hyp
  obtain ⟨-, -, -, -, hf, -, -, -, -⟩ := hyp
  have hinj : InjOn f U := by
    intro x hx x' hx' hxx'
    have : e ⟨x, hx⟩ = e ⟨x', hx'⟩ := Subtype.ext (by rw [he, he]; exact hxx')
    exact congrArg Subtype.val (e.injective this)
  have hfg : ∀ y ∈ f '' U, f (InvData.inv U f y) = y := fun y hy => Function.invFunOn_eq hy
  have hgU : ∀ y ∈ f '' U, InvData.inv U f y ∈ U := fun y hy => Function.invFunOn_mem hy
  have hsymm : ∀ y : (f '' U), (e.symm y : Rn) = InvData.inv U f y := fun y => by
    apply hinj (e.symm y).2 (hgU y y.2)
    rw [hfg y y.2, ← he]
    simp
  refine ⟨hf.continuousOn, ?_, fun x hx => hinj.leftInvOn_invFunOn hx, hfg⟩
  rw [continuousOn_iff_continuous_domRestrict]
  have : (f '' U).domRestrict (InvData.inv U f) = fun y => (e.symm y : Rn) := by
    ext y; exact (hsymm y).symm
  rw [this]
  exact continuous_subtype_val.comp e.symm.continuous

#rt_check RoundTrip.V3_61.B_to_A_smooth [Polyfold.corollary_3_8_19]

end RoundTrip.V3_61

end
