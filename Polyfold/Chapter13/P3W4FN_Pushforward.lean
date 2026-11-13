import Polyfold.Chapter13.P3W4FN_PushChart

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 13,
§13.4, pp. 625–626: **Theorem 13.4.3** (2017: Theorem 13.4), the push-forward of structurable
sc⁺-multisections along a strong bundle equivalence.

# Push-forward of structurable sc⁺-multisections

## The text, paraphrased

(Theorem 13.4.3) For a strong bundle equivalence `Φ : W → W'` covering `F : X → X'` and a
structurable sc⁺-multisection functor `Λ` on `W`, the push-forward `Φ_*Λ` is structurable.  The
proof equips the points of `F(X)` with the structures `s'ʸᵢ = Φ ∘ s^{x_y}ᵢ ∘ (F|U(x_y))⁻¹` and
`τ'_{y,y'}(φ') = τ_{x_y,x_{y'}}((F|·)⁻¹(φ'))`, and reaches the remaining points by
Proposition 13.4.2.

## What is formalized (namespace `Polyfold.SBLocalization`)

The proof without Proposition 13.4.2: every `y ∈ X'` gets the chart of `P3W4FN_PushChart`
(`Q = t ∘ (s|U(σ_y))⁻¹ ∘ F` along a morphism `σ_y : F(x_y) → y`), which moves the structure at
`x_y` to `y` in one step.
* `liftMor T T' φ'`: the morphism `φ : u → u'` of `X` with `ψ'_{u'} ∘ F(φ) = φ' ∘ ψ_u`
  (`u = Q⁻¹(s(φ'))`, `u' = Q'⁻¹(t(φ'))`; `F` full and faithful), `comp_liftMor`,
  `continuousOn_liftMor` (`F` a local sc-diffeomorphism), `injOn_liftMor`, `liftMor_comp`,
  `liftMor_inv`, `liftMor_Γ`, `liftMor_biact`.
* `pushGood`: the good system `(U'(y))` (condition (3) from that of `𝒰` through `liftMor`),
  `pushDecoration`, `pushTau` (`τ'_{y,y'}(φ') = τ_{x_y,x_{y'}}(liftMor φ')`).
* **`theorem_13_4_3`**, as printed, no added hypothesis; `theorem_13_4_3_structured`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

open scoped Classical

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A C : SEP.{u}} {F : C ⟶ A} (hF : SEP.equivalences F)

namespace PushChart

/-! ### Lifts through `F` are continuous -/

include hF in
/-- **A map into the morphisms of `X` is continuous when its `s`, its `t` and its image under
`F` are** (`F` faithful and a local sc-diffeomorphism). -/
theorem continuousAt_of_mor {α : Type*} [TopologicalSpace α] {f : α → C.Mor} {a : α}
    (hs : ContinuousAt (fun b => C.X.src (f b)) a) (ht : ContinuousAt (fun b => C.X.tgt (f b)) a)
    (hm : ContinuousAt (fun b => (SEP.Hom.ϕ F).mor (f b)) a) : ContinuousAt f a := by
  have hE := (sbe hF).isEquivalence_base
  obtain ⟨U, V, g, hU, hd⟩ := (SEP.Hom.ϕ F).isLocalScDiffeo_mor hE.isLocalScDiffeo_obj (f a)
  obtain ⟨Os, Vs, gs, hsOs, hds⟩ := hE.isLocalScDiffeo_obj (C.X.src (f a))
  obtain ⟨Ot, Vt, gt, htOt, hdt⟩ := hE.isLocalScDiffeo_obj (C.X.tgt (f a))
  have hinjs : InjOn (SEP.Hom.ϕ F).obj Os := fun p hp q hq e => by
    rw [← hds.left_inv p hp, e, hds.left_inv q hq]
  have hinjt : InjOn (SEP.Hom.ϕ F).obj Ot := fun p hp q hq e => by
    rw [← hdt.left_inv p hp, e, hdt.left_inv q hq]
  have hV : (SEP.Hom.ϕ F).mor (f a) ∈ V := hd.mapsTo hU
  have hg : ContinuousAt g ((SEP.Hom.ϕ F).mor (f a)) :=
    hd.isScSmoothOn_inv.continuousOn.continuousAt (hd.isOpen_target.mem_nhds hV)
  have hG : ContinuousAt (fun b => g ((SEP.Hom.ϕ F).mor (f b))) a :=
    ContinuousAt.comp (f := fun b => (SEP.Hom.ϕ F).mor (f b)) hg hm
  have hGa : g ((SEP.Hom.ϕ F).mor (f a)) = f a := hd.left_inv _ hU
  have hW : U ∩ C.X.src ⁻¹' Os ∩ C.X.tgt ⁻¹' Ot ∈ 𝓝 (g ((SEP.Hom.ϕ F).mor (f a))) := by
    rw [hGa]
    exact ((hd.isOpen_source.inter (hds.isOpen_source.preimage C.X.continuous_src)).inter
      (hdt.isOpen_source.preimage C.X.continuous_tgt)).mem_nhds ⟨⟨hU, hsOs⟩, htOt⟩
  refine hG.congr ?_
  filter_upwards [hm.preimage_mem_nhds (hd.isOpen_target.mem_nhds hV), hG.preimage_mem_nhds hW,
    hs.preimage_mem_nhds (hds.isOpen_source.mem_nhds hsOs),
    ht.preimage_mem_nhds (hdt.isOpen_source.mem_nhds htOt)] with b hb1 hb2 hb3 hb4
  have hmφ : (SEP.Hom.ϕ F).mor (g ((SEP.Hom.ϕ F).mor (f b))) = (SEP.Hom.ϕ F).mor (f b) :=
    hd.right_inv _ hb1
  refine hE.mor_injective (hinjs hb2.1.2 hb3 ?_) (hinjt hb2.2 hb4 ?_) hmφ
  · rw [← (SEP.Hom.ϕ F).src_mor, ← (SEP.Hom.ϕ F).src_mor, hmφ]
  · rw [← (SEP.Hom.ϕ F).tgt_mor, ← (SEP.Hom.ϕ F).tgt_mor, hmφ]

/-- A continuous map sends the component of `a` in `S` into the component of `f(a)` in `S'`. -/
theorem mapsTo_connectedComponentIn {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β} {S : Set α} {S' : Set β} (hf : ContinuousOn f S) (hS : MapsTo f S S') {a : α}
    (ha : a ∈ S) : MapsTo f (connectedComponentIn S a) (connectedComponentIn S' (f a)) := by
  intro b hb
  have hpre := (isPreconnected_connectedComponentIn :
    IsPreconnected (connectedComponentIn S a)).image f
    (hf.mono (connectedComponentIn_subset S a))
  refine hpre.subset_connectedComponentIn ⟨a, mem_connectedComponentIn ha, rfl⟩ ?_ ⟨b, hb, rfl⟩
  rintro _ ⟨c, hc, rfl⟩
  exact hS (connectedComponentIn_subset S a hc)

/-! ### The lift of a morphism -/

variable {x x' : C.Obj} {y y' : A.Obj}

theorem tgt_ψ_Qinv (T : (SEP.Hom.ϕ F).TransportChart x y) {z : A.Obj} (hz : z ∈ T.W') :
    A.X.tgt (T.ψ (T.Qinv z)) = z := by
  rw [T.tgt_ψ _ (T.isScDiffeoOn_Q.mapsTo_inv hz), T.isScDiffeoOn_Q.right_inv z hz]

theorem src_ψ_Qinv (T : (SEP.Hom.ϕ F).TransportChart x y) {z : A.Obj} (hz : z ∈ T.W') :
    A.X.src (T.ψ (T.Qinv z)) = (SEP.Hom.ϕ F).obj (T.Qinv z) :=
  T.src_ψ _ (T.isScDiffeoOn_Q.mapsTo_inv hz)

/-- The morphisms `φ'` with `s(φ')` and `t(φ')` in the two charts. -/
def Dom (T : (SEP.Hom.ϕ F).TransportChart x y) (T' : (SEP.Hom.ϕ F).TransportChart x' y') :
    Set A.Mor :=
  A.X.morBetween T.W' T'.W'

theorem isOpen_Dom (T : (SEP.Hom.ϕ F).TransportChart x y)
    (T' : (SEP.Hom.ϕ F).TransportChart x' y') : IsOpen (Dom T T') :=
  isOpen_morBetween T.isOpen_W' T'.isOpen_W'

/-- `ψ'_{u'}⁻¹ ∘ φ' ∘ ψ_u`, `u = Q⁻¹(s(φ'))`, `u' = Q'⁻¹(t(φ'))`. -/
def liftTarget (T : (SEP.Hom.ϕ F).TransportChart x y) (T' : (SEP.Hom.ϕ F).TransportChart x' y')
    (φ' : A.Mor) : A.Mor :=
  A.X.comp (A.X.inv (T'.ψ (T'.Qinv (A.X.tgt φ')))) (A.X.comp φ' (T.ψ (T.Qinv (A.X.src φ'))))

/-- `φ` lifts `φ'`: `s(φ) = Q⁻¹(s(φ'))`, `t(φ) = Q'⁻¹(t(φ'))`, `F(φ) = ψ'_{u'}⁻¹ ∘ φ' ∘ ψ_u`. -/
def IsLift (T : (SEP.Hom.ϕ F).TransportChart x y) (T' : (SEP.Hom.ϕ F).TransportChart x' y')
    (φ' : A.Mor) (φ : C.Mor) : Prop :=
  C.X.src φ = T.Qinv (A.X.src φ') ∧ C.X.tgt φ = T'.Qinv (A.X.tgt φ') ∧
    (SEP.Hom.ϕ F).mor φ = liftTarget T T' φ'

/-- **The lift** of `φ'` (`F` is full and faithful). -/
def liftMor (T : (SEP.Hom.ϕ F).TransportChart x y) (T' : (SEP.Hom.ϕ F).TransportChart x' y')
    (φ' : A.Mor) : C.Mor :=
  if h : ∃ φ, IsLift T T' φ' φ then h.choose else C.X.unit x

section Lift

variable {T : (SEP.Hom.ϕ F).TransportChart x y} {T' : (SEP.Hom.ϕ F).TransportChart x' y'}
  {φ' : A.Mor}

theorem src_comp_ψ (hφ : φ' ∈ Dom T T') : A.X.src φ' = A.X.tgt (T.ψ (T.Qinv (A.X.src φ'))) :=
  (tgt_ψ_Qinv T hφ.1).symm

theorem src_inv_ψ' (hφ : φ' ∈ Dom T T') :
    A.X.src (A.X.inv (T'.ψ (T'.Qinv (A.X.tgt φ')))) =
      A.X.tgt (A.X.comp φ' (T.ψ (T.Qinv (A.X.src φ')))) := by
  rw [A.X.src_inv, tgt_ψ_Qinv T' hφ.2, A.X.tgt_comp _ _ (src_comp_ψ hφ)]

theorem src_liftTarget (hφ : φ' ∈ Dom T T') :
    A.X.src (liftTarget T T' φ') = (SEP.Hom.ϕ F).obj (T.Qinv (A.X.src φ')) := by
  rw [liftTarget, A.X.src_comp _ _ (src_inv_ψ' hφ), A.X.src_comp _ _ (src_comp_ψ hφ),
    src_ψ_Qinv T hφ.1]

theorem tgt_liftTarget (hφ : φ' ∈ Dom T T') :
    A.X.tgt (liftTarget T T' φ') = (SEP.Hom.ϕ F).obj (T'.Qinv (A.X.tgt φ')) := by
  rw [liftTarget, A.X.tgt_comp _ _ (src_inv_ψ' hφ), A.X.tgt_inv, src_ψ_Qinv T' hφ.2]

include hF

theorem exists_isLift (hφ : φ' ∈ Dom T T') : ∃ φ, IsLift T T' φ' φ :=
  (sbe hF).isEquivalence_base.exists_mor_eq (src_liftTarget hφ) (tgt_liftTarget hφ)

theorem isLift_liftMor (hφ : φ' ∈ Dom T T') : IsLift T T' φ' (liftMor T T' φ') := by
  rw [liftMor, dif_pos (exists_isLift hF hφ)]
  exact (exists_isLift hF hφ).choose_spec

theorem src_liftMor (hφ : φ' ∈ Dom T T') : C.X.src (liftMor T T' φ') = T.Qinv (A.X.src φ') :=
  (isLift_liftMor hF hφ).1

theorem tgt_liftMor (hφ : φ' ∈ Dom T T') : C.X.tgt (liftMor T T' φ') = T'.Qinv (A.X.tgt φ') :=
  (isLift_liftMor hF hφ).2.1

theorem liftMor_eq (hφ : φ' ∈ Dom T T') {φ : C.Mor} (h : IsLift T T' φ' φ) :
    liftMor T T' φ' = φ :=
  (sbe hF).isEquivalence_base.mor_injective ((src_liftMor hF hφ).trans h.1.symm)
    ((tgt_liftMor hF hφ).trans h.2.1.symm) ((isLift_liftMor hF hφ).2.2.trans h.2.2.symm)

/-- **The defining identity** `ψ'_{u'} ∘ F(φ) = φ' ∘ ψ_u`. -/
theorem comp_liftMor (hφ : φ' ∈ Dom T T') :
    A.X.comp (T'.ψ (C.X.tgt (liftMor T T' φ'))) ((SEP.Hom.ϕ F).mor (liftMor T T' φ')) =
      A.X.comp φ' (T.ψ (C.X.src (liftMor T T' φ'))) := by
  rw [src_liftMor hF hφ, tgt_liftMor hF hφ, (isLift_liftMor hF hφ).2.2, liftTarget]
  have e := A.X.inv_comp_cancel_left (φ := A.X.inv (T'.ψ (T'.Qinv (A.X.tgt φ'))))
    (src_inv_ψ' hφ)
  rwa [A.X.inv_inv] at e

/-- The lift is characterized by the defining identity. -/
theorem liftMor_eq_of_comp (hφ : φ' ∈ Dom T T') {φ : C.Mor}
    (hs : C.X.src φ = T.Qinv (A.X.src φ')) (ht : C.X.tgt φ = T'.Qinv (A.X.tgt φ'))
    (hc : A.X.comp (T'.ψ (C.X.tgt φ)) ((SEP.Hom.ϕ F).mor φ) = A.X.comp φ' (T.ψ (C.X.src φ))) :
    liftMor T T' φ' = φ := by
  refine liftMor_eq hF hφ ⟨hs, ht, ?_⟩
  have hW : C.X.tgt φ ∈ T'.W := by rw [ht]; exact T'.isScDiffeoOn_Q.mapsTo_inv hφ.2
  rw [liftTarget, ← hs, ← ht, ← hc]
  refine (A.X.inv_comp_cancel_left ?_).symm
  rw [T'.src_ψ _ hW, (SEP.Hom.ϕ F).tgt_mor]

omit hF in
theorem continuousOn_liftTarget :
    ContinuousOn (liftTarget T T') (Dom T T') := by
  have hQ : ContinuousOn T.Qinv T.W' := T.isScDiffeoOn_Q.isScSmoothOn_inv.continuousOn
  have hQ' : ContinuousOn T'.Qinv T'.W' := T'.isScDiffeoOn_Q.isScSmoothOn_inv.continuousOn
  have h1 : ContinuousOn (fun φ' => A.X.inv (T'.ψ (T'.Qinv (A.X.tgt φ')))) (Dom T T') :=
    A.X.continuous_inv.comp_continuousOn (T'.continuousOn_ψ.comp
      (hQ'.comp A.X.continuous_tgt.continuousOn fun _ hb => hb.2)
      fun _ hb => T'.isScDiffeoOn_Q.mapsTo_inv hb.2)
  have h2 : ContinuousOn (fun φ' => A.X.comp φ' (T.ψ (T.Qinv (A.X.src φ')))) (Dom T T') :=
    A.X.continuousOn_comp_of continuousOn_id (T.continuousOn_ψ.comp
      (hQ.comp A.X.continuous_src.continuousOn fun _ hb => hb.1)
      fun _ hb => T.isScDiffeoOn_Q.mapsTo_inv hb.1) fun _ hb => src_comp_ψ hb
  exact A.X.continuousOn_comp_of h1 h2 fun _ hb => src_inv_ψ' hb

/-- **The lift is continuous** (`F` a local sc-diffeomorphism, `continuousAt_of_mor`). -/
theorem continuousOn_liftMor : ContinuousOn (liftMor T T') (Dom T T') := by
  intro φ' hφ
  have hN : Dom T T' ∈ 𝓝 φ' := (isOpen_Dom T T').mem_nhds hφ
  have hQ : ContinuousOn T.Qinv T.W' := T.isScDiffeoOn_Q.isScSmoothOn_inv.continuousOn
  have hQ' : ContinuousOn T'.Qinv T'.W' := T'.isScDiffeoOn_Q.isScSmoothOn_inv.continuousOn
  refine (continuousAt_of_mor hF ?_ ?_ ?_).continuousWithinAt
  · refine ContinuousAt.congr ((hQ.continuousAt (T.isOpen_W'.mem_nhds hφ.1)).comp
      A.X.continuous_src.continuousAt) ?_
    filter_upwards [hN] with b hb using (src_liftMor hF hb).symm
  · refine ContinuousAt.congr ((hQ'.continuousAt (T'.isOpen_W'.mem_nhds hφ.2)).comp
      A.X.continuous_tgt.continuousAt) ?_
    filter_upwards [hN] with b hb using (tgt_liftMor hF hb).symm
  · refine ContinuousAt.congr ((continuousOn_liftTarget (T := T) (T' := T')).continuousAt hN) ?_
    filter_upwards [hN] with b hb using (isLift_liftMor hF hb).2.2.symm

/-- **The lift is injective.** -/
theorem injOn_liftMor : InjOn (liftMor T T') (Dom T T') := by
  intro a ha b hb e
  have ca := comp_liftMor hF ha
  have cb := comp_liftMor hF hb
  rw [e] at ca
  have hsa : C.X.src (liftMor T T' b) = T.Qinv (A.X.src a) := by rw [← e, src_liftMor hF ha]
  have hsb := src_liftMor hF hb
  refine A.X.comp_right_cancel ?_ ?_ (ca.symm.trans cb)
  · rw [hsa]; exact src_comp_ψ ha
  · rw [hsb]; exact src_comp_ψ hb

end Lift

include hF

/-- **The lift respects composition.** -/
theorem liftMor_comp {x₁ x₂ x₃ : C.Obj} {y₁ y₂ y₃ : A.Obj}
    (T₁ : (SEP.Hom.ϕ F).TransportChart x₁ y₁) (T₂ : (SEP.Hom.ϕ F).TransportChart x₂ y₂)
    (T₃ : (SEP.Hom.ϕ F).TransportChart x₃ y₃) {φ₁ φ₂ : A.Mor} (h₁ : φ₁ ∈ Dom T₁ T₂)
    (h₂ : φ₂ ∈ Dom T₂ T₃) (h : A.X.src φ₂ = A.X.tgt φ₁) :
    liftMor T₁ T₃ (A.X.comp φ₂ φ₁) = C.X.comp (liftMor T₂ T₃ φ₂) (liftMor T₁ T₂ φ₁) := by
  have hL : C.X.src (liftMor T₂ T₃ φ₂) = C.X.tgt (liftMor T₁ T₂ φ₁) := by
    rw [src_liftMor hF h₂, tgt_liftMor hF h₁, h]
  have h₁₂ : A.X.comp φ₂ φ₁ ∈ Dom T₁ T₃ :=
    ⟨by rw [A.X.src_comp _ _ h]; exact h₁.1, by rw [A.X.tgt_comp _ _ h]; exact h₂.2⟩
  have hW₂ : C.X.tgt (liftMor T₂ T₃ φ₂) ∈ T₃.W := by
    rw [tgt_liftMor hF h₂]; exact T₃.isScDiffeoOn_Q.mapsTo_inv h₂.2
  have hW₁ : C.X.src (liftMor T₂ T₃ φ₂) ∈ T₂.W := by
    rw [src_liftMor hF h₂]; exact T₂.isScDiffeoOn_Q.mapsTo_inv h₂.1
  have e1 : A.X.src (T₃.ψ (C.X.tgt (liftMor T₂ T₃ φ₂))) =
      A.X.tgt ((SEP.Hom.ϕ F).mor (liftMor T₂ T₃ φ₂)) := by
    rw [T₃.src_ψ _ hW₂, (SEP.Hom.ϕ F).tgt_mor]
  have e2 : A.X.src ((SEP.Hom.ϕ F).mor (liftMor T₂ T₃ φ₂)) =
      A.X.tgt ((SEP.Hom.ϕ F).mor (liftMor T₁ T₂ φ₁)) := by
    rw [(SEP.Hom.ϕ F).src_mor, (SEP.Hom.ϕ F).tgt_mor, hL]
  have e3 : A.X.src φ₂ = A.X.tgt (T₂.ψ (C.X.src (liftMor T₂ T₃ φ₂))) := by
    rw [src_liftMor hF h₂]; exact src_comp_ψ h₂
  have e4 : A.X.src (T₂.ψ (C.X.src (liftMor T₂ T₃ φ₂))) =
      A.X.tgt ((SEP.Hom.ϕ F).mor (liftMor T₁ T₂ φ₁)) := by
    rw [T₂.src_ψ _ hW₁, (SEP.Hom.ϕ F).tgt_mor, hL]
  have e5 : A.X.src φ₁ = A.X.tgt (T₁.ψ (C.X.src (liftMor T₁ T₂ φ₁))) := by
    rw [src_liftMor hF h₁]; exact src_comp_ψ h₁
  refine liftMor_eq_of_comp hF h₁₂ ?_ ?_ ?_
  · rw [C.X.src_comp _ _ hL, src_liftMor hF h₁, A.X.src_comp _ _ h]
  · rw [C.X.tgt_comp _ _ hL, tgt_liftMor hF h₂, A.X.tgt_comp _ _ h]
  · rw [C.X.src_comp _ _ hL, C.X.tgt_comp _ _ hL, (SEP.Hom.ϕ F).mor_comp _ _ hL,
      ← A.X.comp_assoc _ _ _ e1 e2, comp_liftMor hF h₂, A.X.comp_assoc _ _ _ e3 e4, hL,
      comp_liftMor hF h₁, ← A.X.comp_assoc _ _ _ h e5]

/-- **The lift respects inverses.** -/
theorem liftMor_inv (T : (SEP.Hom.ϕ F).TransportChart x y)
    (T' : (SEP.Hom.ϕ F).TransportChart x' y') {φ' : A.Mor} (hφ : φ' ∈ Dom T T') :
    liftMor T' T (A.X.inv φ') = C.X.inv (liftMor T T' φ') := by
  have hD : A.X.inv φ' ∈ Dom T' T :=
    ⟨by rw [A.X.src_inv]; exact hφ.2, by rw [A.X.tgt_inv]; exact hφ.1⟩
  refine liftMor_eq hF hD ⟨by rw [C.X.src_inv, tgt_liftMor hF hφ, A.X.src_inv],
    by rw [C.X.tgt_inv, src_liftMor hF hφ, A.X.tgt_inv], ?_⟩
  have k3 : A.X.src (A.X.inv (T.ψ (T.Qinv (A.X.src φ')))) = A.X.tgt (A.X.inv φ') := by
    rw [A.X.src_inv, A.X.tgt_inv]; exact (src_comp_ψ hφ).symm
  have k4 : A.X.src (A.X.inv φ') = A.X.tgt (T'.ψ (T'.Qinv (A.X.tgt φ'))) := by
    rw [A.X.src_inv, tgt_ψ_Qinv T' hφ.2]
  rw [(SEP.Hom.ϕ F).mor_inv, (isLift_liftMor hF hφ).2.2, liftTarget, liftTarget, A.X.src_inv,
    A.X.tgt_inv, A.X.inv_comp_rev (src_inv_ψ' hφ), A.X.inv_comp_rev (src_comp_ψ hφ),
    A.X.inv_inv, A.X.comp_assoc _ _ _ k3 k4]

variable {T : (SEP.Hom.ϕ F).TransportChart x y} {T' : (SEP.Hom.ϕ F).TransportChart x' y'}
  {N : C.X.NatNbhd x} {N' : A.X.NatNbhd y} {M : C.X.NatNbhd x'} {M' : A.X.NatNbhd y'}

omit hF in
theorem morBetween_subset_Dom (h : IsPushNbhd T N N') (h' : IsPushNbhd T' M M') :
    A.X.morBetween N'.U M'.U ⊆ Dom T T' :=
  fun _ hφ => ⟨h.subset_W' hφ.1, h'.subset_W' hφ.2⟩

theorem liftMor_mem (h : IsPushNbhd T N N') (h' : IsPushNbhd T' M M') {φ' : A.Mor}
    (hφ : φ' ∈ A.X.morBetween N'.U M'.U) : liftMor T T' φ' ∈ C.X.morBetween N.U M.U := by
  have hD := morBetween_subset_Dom h h' hφ
  exact ⟨by rw [src_liftMor hF hD]; exact h.Qinv_mem hφ.1,
    by rw [tgt_liftMor hF hD]; exact h'.Qinv_mem hφ.2⟩

/-- **The lift of `Γ'`**: `liftMor (Γ'(ψ F(g) ψ⁻¹, z)) = Γ(g, Q⁻¹(z))`. -/
theorem liftMor_Γ (h : IsPushNbhd T N N') (g : C.X.Isotropy x) {z : A.Obj} (hz : z ∈ N'.U) :
    liftMor T T (N'.rep.Γ (T.conj g) z) = N.rep.Γ g (T.Qinv z) := by
  have hD : N'.rep.Γ (T.conj g) z ∈ Dom T T :=
    ⟨by rw [N'.src_Γ _ hz]; exact h.subset_W' hz,
      by rw [N'.tgt_Γ _ hz]; exact h.subset_W' (N'.Φ_mem _ hz)⟩
  have hu := h.Qinv_mem hz
  refine liftMor_eq_of_comp hF hD (by rw [N.src_Γ g hu, N'.src_Γ _ hz])
    (by rw [N.tgt_Γ g hu, N'.tgt_Γ _ hz, h.Qinv_Φ g hz]) ?_
  rw [N.tgt_Γ g hu, N.src_Γ g hu]
  exact (h.Γ_comp_ψ g hz).symm

/-- **The lift intertwines the bi-actions**:
`liftMor (ψ F(g') ψ⁻¹ ∗ φ' ∗ ψ F(g) ψ⁻¹) = g' ∗ liftMor φ' ∗ g`. -/
theorem liftMor_biact (h : IsPushNbhd T N N') (h' : IsPushNbhd T' M M') {φ' : A.Mor}
    (hφ : φ' ∈ A.X.morBetween N'.U M'.U) (k' : C.X.Isotropy x') (k : C.X.Isotropy x) :
    liftMor T T' (EpGroupoid.biact N' M' (T'.conj k') φ' (T.conj k)) =
      EpGroupoid.biact N M k' (liftMor T T' φ') k := by
  have hφD := morBetween_subset_Dom h h' hφ
  set w := N'.rep.Φ (T.conj k)⁻¹ (A.X.src φ') with hwdef
  have hw : w ∈ N'.U := N'.Φ_mem _ hφ.1
  have hb : N'.rep.Γ (T.conj k) w ∈ Dom T T :=
    ⟨by rw [N'.src_Γ _ hw]; exact h.subset_W' hw,
      by rw [N'.tgt_Γ _ hw]; exact h.subset_W' (N'.Φ_mem _ hw)⟩
  have hbt : A.X.src φ' = A.X.tgt (N'.rep.Γ (T.conj k) w) := by
    rw [N'.tgt_Γ _ hw, hwdef, N'.Φ_Φ_inv _ hφ.1]
  have ha : M'.rep.Γ (T'.conj k') (A.X.tgt φ') ∈ Dom T' T' :=
    ⟨by rw [M'.src_Γ _ hφ.2]; exact h'.subset_W' hφ.2,
      by rw [M'.tgt_Γ _ hφ.2]; exact h'.subset_W' (M'.Φ_mem _ hφ.2)⟩
  have hc : A.X.comp φ' (N'.rep.Γ (T.conj k) w) ∈ Dom T T' :=
    ⟨by rw [A.X.src_comp _ _ hbt]; exact hb.1, by rw [A.X.tgt_comp _ _ hbt]; exact hφD.2⟩
  have hac : A.X.src (M'.rep.Γ (T'.conj k') (A.X.tgt φ')) =
      A.X.tgt (A.X.comp φ' (N'.rep.Γ (T.conj k) w)) := by
    rw [M'.src_Γ _ hφ.2, A.X.tgt_comp _ _ hbt]
  rw [EpGroupoid.biact, EpGroupoid.biact, ← hwdef, liftMor_comp hF T T' T' hc ha hac,
    liftMor_comp hF T T T' hb hφD hbt, liftMor_Γ hF h' k' hφ.2, liftMor_Γ hF h k hw,
    tgt_liftMor hF hφD, src_liftMor hF hφD, hwdef,
    show (T.conj k)⁻¹ = T.conj k⁻¹ from (map_inv T.conj k).symm, h.Qinv_Φ k⁻¹ hφ.1]

/-- **The pushed sections satisfy the compatibility along `φ'` when the given ones do along
the lift.** -/
theorem pushSec_compat (h : IsPushNbhd T N N') (h' : IsPushNbhd T' M M')
    {s s' : C.Obj → C.W} (hs : ∀ u ∈ N.U, C.P (s u) = u) (hs' : ∀ u ∈ M.U, C.P (s' u) = u)
    {ψ' : A.Mor} (hψ : ψ' ∈ A.X.morBetween N'.U M'.U)
    (hc : s' (C.X.tgt (liftMor T T' ψ')) =
      fibAct (liftMor T T' ψ') (s (C.X.src (liftMor T T' ψ')))) :
    pushSec T' s' (A.X.tgt ψ') = fibAct ψ' (pushSec T s (A.X.src ψ')) := by
  have hD := morBetween_subset_Dom h h' hψ
  have hsL := src_liftMor hF hD
  have htL := tgt_liftMor hF hD
  have hu : C.X.src (liftMor T T' ψ') ∈ N.U := by rw [hsL]; exact h.Qinv_mem hψ.1
  have huW : C.X.src (liftMor T T' ψ') ∈ T.W := by
    rw [hsL]; exact T.isScDiffeoOn_Q.mapsTo_inv hD.1
  have hu'W : C.X.tgt (liftMor T T' ψ') ∈ T'.W := by
    rw [htL]; exact T'.isScDiffeoOn_Q.mapsTo_inv hD.2
  rw [h'.pushSec_eq hF hs' hψ.2, h.pushSec_eq hF hs hψ.1, ← htL, ← hsL, hc]
  have hP : C.P (s (C.X.src (liftMor T T' ψ'))) = C.X.src (liftMor T T' ψ') := hs _ hu
  have e1 := (PullMap.ofEquivalence hF).obj_fibAct hP
  have hcov := (PullMap.ofEquivalence hF).covers (s (C.X.src (liftMor T T' ψ')))
  simp only [PullMap.ofEquivalence_Φ, PullMap.ofEquivalence_ϕ] at e1 hcov
  have hv : A.P ((SEP.Hom.Φ F).obj (s (C.X.src (liftMor T T' ψ')))) =
      A.X.src ((SEP.Hom.ϕ F).mor (liftMor T T' ψ')) := by
    rw [hcov, hP, (SEP.Hom.ϕ F).src_mor]
  have hv2 : A.P ((SEP.Hom.Φ F).obj (s (C.X.src (liftMor T T' ψ')))) =
      A.X.src (T.ψ (C.X.src (liftMor T T' ψ'))) := by
    rw [hcov, hP, T.src_ψ _ huW]
  rw [e1, ← PushChart.fibAct_comp hv (by rw [T'.src_ψ _ hu'W, (SEP.Hom.ϕ F).tgt_mor]),
    comp_liftMor hF hD, PushChart.fibAct_comp hv2 (by rw [hsL]; exact src_comp_ψ hD)]

/-- **Condition (3) of good systems is carried forward**: a component `Σ'` of
`𝒰'(y, y')` is sent by the lift into a component `Σ` of `𝒰(x_y, x_{y'})`, where `s` and `t`
are injective; the lift is injective. -/
theorem isDiffeoComponent_push (𝒰 : C.X.GoodSystem) {T : (SEP.Hom.ϕ F).TransportChart x y}
    {T' : (SEP.Hom.ϕ F).TransportChart x' y'} {N' : A.X.NatNbhd y} {M' : A.X.NatNbhd y'}
    (h : IsPushNbhd T (𝒰.nbhd x) N') (h' : IsPushNbhd T' (𝒰.nbhd x') M') {φ' : A.Mor}
    (hφ : φ' ∈ A.X.morBetween N'.U M'.U) :
    A.X.IsDiffeoComponent (connectedComponentIn (A.X.morBetween N'.U M'.U) φ') := by
  have hsubD := morBetween_subset_Dom h h'
  have hmaps : MapsTo (liftMor T T') (connectedComponentIn (A.X.morBetween N'.U M'.U) φ')
      (𝒰.comp x x' (liftMor T T' φ')) :=
    mapsTo_connectedComponentIn ((continuousOn_liftMor hF).mono hsubD)
      (fun _ hψ => liftMor_mem hF h h' hψ) hφ
  have hL : liftMor T T' φ' ∈ 𝒰.mor x x' := liftMor_mem hF h h' hφ
  have hsub : ∀ {ψ}, ψ ∈ connectedComponentIn (A.X.morBetween N'.U M'.U) φ' → ψ ∈ Dom T T' :=
    fun hψ => hsubD (connectedComponentIn_subset _ _ hψ)
  refine (isDiffeoComponent_iff_injOn (isOpen_connectedComponentIn_mor A.X
    (isOpen_morBetween N'.isOpen_U M'.isOpen_U) φ')).2
    ⟨fun ψ₁ hψ₁ ψ₂ hψ₂ e => ?_, fun ψ₁ hψ₁ ψ₂ hψ₂ e => ?_⟩
  · refine injOn_liftMor hF (hsub hψ₁) (hsub hψ₂)
      (𝒰.injOn_src_comp hL (hmaps hψ₁) (hmaps hψ₂) ?_)
    rw [src_liftMor hF (hsub hψ₁), src_liftMor hF (hsub hψ₂), e]
  · refine injOn_liftMor hF (hsub hψ₁) (hsub hψ₂)
      (𝒰.injOn_tgt_comp hL (hmaps hψ₁) (hmaps hψ₂) ?_)
    rw [tgt_liftMor hF (hsub hψ₁), tgt_liftMor hF (hsub hψ₂), e]

end PushChart

open PushChart

/-! ### The pushed good system, decoration and correspondences -/

/-- The neighbourhood `U'(y)`, adapted to `U(x_y)` along the chosen chart. -/
def pushNbhd (𝒰 : C.X.GoodSystem) (y : A.Obj) : A.X.NatNbhd y :=
  (exists_isPushNbhd (pushChart hF y).T (𝒰.nbhd (pushChart hF y).x)).choose

theorem isPushNbhd_pushNbhd (𝒰 : C.X.GoodSystem) (y : A.Obj) :
    IsPushNbhd (pushChart hF y).T (𝒰.nbhd (pushChart hF y).x) (pushNbhd hF 𝒰 y) :=
  (exists_isPushNbhd (pushChart hF y).T (𝒰.nbhd (pushChart hF y).x)).choose_spec.1

/-- **The pushed good system** `(U'(y))_{y ∈ X'}`. -/
def pushGood (𝒰 : C.X.GoodSystem) : A.X.GoodSystem where
  nbhd := pushNbhd hF 𝒰
  isProperSubset_closure y :=
    (exists_isPushNbhd (pushChart hF y).T (𝒰.nbhd (pushChart hF y).x)).choose_spec.2
  isDiffeoComponent _ _ _ hφ :=
    isDiffeoComponent_push hF 𝒰 (isPushNbhd_pushNbhd hF 𝒰 _) (isPushNbhd_pushNbhd hF 𝒰 _) hφ

/-- **The pushed decoration** `(𝒰', S')` of `Φ_*Λ`. -/
def pushDecoration {Λ : C.W → ℚ≥0} (hΛ : IsWFunctor C Λ) (D : Decoration C Λ) :
    Decoration A (pushMult F hF Λ) :=
  ⟨pushGood hF D.𝒰, fun y =>
    pushStructure hF (isPushNbhd_pushNbhd hF D.𝒰 y) hΛ (D.S (pushChart hF y).x)⟩

/-- **The pushed correspondences** `τ'_{y,y'}(φ') = τ_{x_y,x_{y'}}(liftMor φ')`. -/
def pushTau {Λ : C.W → ℚ≥0} (hΛ : IsWFunctor C Λ) {D : Decoration C Λ} (t : D.Tau) :
    (pushDecoration hF hΛ D).Tau where
  τ y y' φ' :=
    t.τ (pushChart hF y).x (pushChart hF y').x (liftMor (pushChart hF y).T (pushChart hF y').T φ')
  isCorrespondence y y' :=
    have h := isPushNbhd_pushNbhd hF D.𝒰 y
    have h' := isPushNbhd_pushNbhd hF D.𝒰 y'
    { locallyConstant := fun φ' hφ' =>
        ((continuousOn_liftMor hF).continuousAt ((isOpen_Dom _ _).mem_nhds
          (morBetween_subset_Dom h h' hφ'))).eventually
          ((t.isCorrespondence _ _).locallyConstant _ (liftMor_mem hF h h' hφ'))
      finite := (t.isCorrespondence _ _).finite.subset (by
        rintro _ ⟨φ', hφ', rfl⟩
        exact ⟨_, liftMor_mem hF h h' hφ', rfl⟩)
      biact := fun φ' hφ' g' g => by
        obtain ⟨k, rfl⟩ := (conjEquiv hF (pushChart hF y).T).surjective g
        obtain ⟨k', rfl⟩ := (conjEquiv hF (pushChart hF y').T).surjective g'
        change t.τ _ _ (liftMor _ _ (EpGroupoid.biact (pushNbhd hF D.𝒰 y) (pushNbhd hF D.𝒰 y')
          ((pushChart hF y').T.conj k') φ' ((pushChart hF y).T.conj k))) = _
        rw [liftMor_biact hF h h' hφ' k' k]
        have hb := (t.isCorrespondence _ _).biact _ (liftMor_mem hF h h' hφ') k' k
        have e := PullMap.biact_compHom (conjEquiv hF (pushChart hF y).T).symm.toMonoidHom
          (conjEquiv hF (pushChart hF y').T).symm.toMonoidHom
          (conjEquiv hF (pushChart hF y').T k')
          (t.τ (pushChart hF y).x (pushChart hF y').x
            (liftMor (pushChart hF y).T (pushChart hF y').T φ'))
          (conjEquiv hF (pushChart hF y).T k)
        simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at e
        exact hb.trans e.symm
      compat := fun φ' hφ' => IndexCorr.sat_mono (fun i j H ψ' hψ' => by
          have hψm : ψ' ∈ A.X.morBetween (pushNbhd hF D.𝒰 y).U (pushNbhd hF D.𝒰 y').U :=
            connectedComponentIn_subset _ _ hψ'
          have hmaps := mapsTo_connectedComponentIn
            ((continuousOn_liftMor hF).mono (morBetween_subset_Dom h h'))
            (fun _ hψ => liftMor_mem hF h h' hψ) hφ'
          exact pushSec_compat hF h h' (fun u hu => (D.S _).P_s i hu)
            (fun u hu => (D.S _).P_s j hu) hψm (H _ (hmaps hψ')))
        ((t.isCorrespondence _ _).compat _ (liftMor_mem hF h h' hφ')) }
  diag y g z hz := by
    have h := isPushNbhd_pushNbhd hF D.𝒰 y
    obtain ⟨k, rfl⟩ := (conjEquiv hF (pushChart hF y).T).surjective g
    change t.τ _ _ (liftMor _ _ ((pushNbhd hF D.𝒰 y).rep.Γ ((pushChart hF y).T.conj k) z)) = _
    rw [liftMor_Γ hF h k hz, t.diag _ k _ (h.Qinv_mem hz)]
    have e := PullMap.ofPerm_compHom (α := (D.S (pushChart hF y).x).I)
      (conjEquiv hF (pushChart hF y).T).symm.toMonoidHom (conjEquiv hF (pushChart hF y).T k)
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at e
    exact e.symm
  swap y y' φ' hφ' := by
    have hD := morBetween_subset_Dom (isPushNbhd_pushNbhd hF D.𝒰 y')
      (isPushNbhd_pushNbhd hF D.𝒰 y) hφ'
    change t.τ _ _ (liftMor _ _ φ') = (t.τ _ _ (liftMor _ _ (A.X.inv φ'))).swap
    rw [liftMor_inv hF _ _ hD]
    exact t.swap _ _ _ (liftMor_mem hF (isPushNbhd_pushNbhd hF D.𝒰 y')
      (isPushNbhd_pushNbhd hF D.𝒰 y) hφ')

/-- **The pushed structured tuple** `(Φ_*Λ, 𝒰', S', τ')`. -/
def pushTuple (T : StructuredTuple C) : StructuredTuple A :=
  ⟨⟨pushMult F hF T.Λ, lemma_11_5_2_book hF T.isScPlusMultisection,
    pushDecoration hF T.isScPlusMultisection.1 T.dec⟩, pushTau hF T.isScPlusMultisection.1 T.tau⟩

@[simp] theorem pushTuple_Λ (T : StructuredTuple C) : (pushTuple hF T).Λ = pushMult F hF T.Λ :=
  rfl

/-! ### Theorem 13.4.3 -/

/-- **2021 Theorem 13.4.3, p. 625 (2017: Theorem 13.4)**: for a strong bundle equivalence
`Φ : W → W'` covering `F : X → X'` and a structurable sc⁺-multisection functor `Λ` on `W`, the
push-forward `Φ_*Λ` is structurable.  As printed, no added hypothesis (proved without
Proposition 13.4.2, see the module docstring). -/
theorem theorem_13_4_3 {Λ : C.W → ℚ≥0} (h : IsStructurable C Λ) :
    IsStructurable A (pushMult F hF Λ) := by
  obtain ⟨hΛ, D, ⟨t⟩⟩ := h
  exact ⟨lemma_11_5_2_book hF hΛ, pushDecoration hF hΛ.1 D, ⟨pushTau hF hΛ.1 t⟩⟩

/-- **Theorem 13.4.3, structured form** (the proof): a structured `(Λ, 𝒰, S, τ)` gives a
structured `(Φ_*Λ, 𝒰', S', τ')` with `I'_y = I_{x_y}` and
`τ'_{y,y'}(φ') = τ_{x_y,x_{y'}}(φ)`, where `φ : x_y`-side lift of `φ'`. -/
theorem theorem_13_4_3_structured (T : StructuredTuple C) :
    (pushTuple hF T).Λ = pushMult F hF T.Λ ∧
      (∀ y, ((pushTuple hF T).dec.S y).I = (T.dec.S (pushChart hF y).x).I) ∧
      ∀ y y' φ', (pushTuple hF T).tau.τ y y' φ' =
        T.tau.τ (pushChart hF y).x (pushChart hF y').x
          (liftMor (pushChart hF y).T (pushChart hF y').T φ') :=
  ⟨rfl, fun _ => rfl, fun _ _ _ => rfl⟩

/-! ### Generalized strong bundle isomorphisms -/

namespace SDiagram

variable {A' : SEP.{u}}

/-- **Structurability is preserved by `[D]_* = Ψ_* Φ^*`** (Theorems 13.4.1 and 13.4.3; the
interior case of the proof of Proposition 14.1.8, and the remark opening §16.5). -/
theorem isStructurable_pushMult (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ)
    {Λ : A.W → ℚ≥0} (h : IsStructurable A Λ) : IsStructurable A' (D.pushMult hΨ Λ) :=
  theorem_13_4_3 hΨ (theorem_13_4_1 D.isEquivalence_Φ h)

/-- **Structurability is preserved by `[D]^* = Φ_* Ψ^*`.** -/
theorem isStructurable_pullMult (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ)
    {Λ' : A'.W → ℚ≥0} (h : IsStructurable A' Λ') : IsStructurable A (D.pullMult hΨ Λ') :=
  isStructurable_pushMult (D.symm hΨ) D.isEquivalence_Φ h

end SDiagram

namespace GenSBMap

variable {A' : SEP.{u}} {f : GenSBMap A A'} (hf : f.IsGeneralizedIso)

/-- **Push-forwards of structurable sc⁺-multisections along generalized strong bundle
isomorphisms are structurable.** -/
theorem isStructurable_pushMult {Λ : A.W → ℚ≥0} (h : IsStructurable A Λ) :
    IsStructurable A' (pushMult hf Λ) :=
  SDiagram.isStructurable_pushMult _ _ h

/-- **Pull-backs of structurable sc⁺-multisections along generalized strong bundle
isomorphisms are structurable.** -/
theorem isStructurable_pullMult {Λ' : A'.W → ℚ≥0} (h : IsStructurable A' Λ') :
    IsStructurable A (pullMult hf Λ') :=
  SDiagram.isStructurable_pullMult _ _ h

end GenSBMap

end SBLocalization

end Polyfold
