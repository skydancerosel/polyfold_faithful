import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V13_52

set_option maxSynthPendingDepth 3

/-! Round trip for V13_52 (2021 Theorem 13.4.3, pp. 625–626; 2017: Theorem 13.4: the push-forward
along a strong bundle equivalence is structurable).

`A` is the conjunction of the types of the 25 listed theorems at universe `0` (the definitions
of the list are vocabulary; `continuousAt_of_mor`, `mapsTo_connectedComponentIn` with their
extra `Type*` universes at `0`).  The main conjunct is `theorem_13_4_3`
(`IsStructurable A (pushMult F hF Λ)`); `theorem_13_4_3_structured` records the structure of the
proof (`(pushTuple hF T).Λ = Φ_*Λ`, `I'_y = I_{x_y}`, `τ'` through `liftMor`), all `rfl`; the
others are proof steps.

* `A_to_B`: `B`'s `Λ'` is `pushMult F hF Λ`: `pushMult` evaluates `Λ` at the chosen `w` with
  `Φ(w) ≅ w'` (`exists_iso`), and `B`'s hypothesis on `Λ'` gives `Λ' w' = Λ w` there.
* `B_to_A`: `theorem_13_4_3` from `B` with `Λ' := pushMult F hF Λ`, whose defining property is
  `pushMult_eq` (Chapter 11; `Λ` is a functor).  `theorem_13_4_3_structured` is `rfl`.  The
  helper conjuncts do not follow from `B`; they are re-proved outright by copying the project's
  proofs (suffix `_rt`).

**Harness note.**  `A` mentions `pushTuple`, `pushDecoration`, `pushTau`, `pushGood`,
`pushStructure`, whose proof fields use banned helpers, so `#rt_check_soft` is used. -/

/-! ### Copies of the project's proofs (suffix `_rt`) -/

open Set Function Topology Filter CategoryTheory
open scoped Classical

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle EpGroupoid

section SO
variable {A : SEP.{u}}
theorem fibAct_comp_rt {ψ χ : A.Mor} {v : A.W} (hv : A.P v = A.X.src χ)
    (h : A.X.src ψ = A.X.tgt χ) : fibAct (A.X.comp ψ χ) v = fibAct ψ (fibAct χ v) := by
  rw [fibAct_of (hv.trans (A.X.src_comp ψ χ h).symm), fibAct_of hv,
    fibAct_of ((A.E.P_μ _).trans h.symm)]
  exact A.E.μ_comp ψ χ v hv h


theorem fibAct_unit_rt {y : A.Obj} {v : A.W} (hv : A.P v = y) : fibAct (A.X.unit y) v = v := by
  subst hv
  rw [fibAct_of (A.X.src_unit _).symm]
  exact A.E.μ_unit v
end SO

section SSP
variable {A C : SEP.{u}}
namespace PushChart

theorem fibAct_inv_fibAct_rt {ψ : A.Mor} {v : A.W} (hv : A.P v = A.X.src ψ) :
    fibAct (A.X.inv ψ) (fibAct ψ v) = v := by
  rw [← fibAct_comp_rt hv (A.X.src_inv ψ), A.X.inv_comp, fibAct_unit_rt hv]

theorem fibAct_fibAct_inv_rt {ψ : A.Mor} {v : A.W} (hv : A.P v = A.X.tgt ψ) :
    fibAct ψ (fibAct (A.X.inv ψ) v) = v := by
  rw [← fibAct_comp_rt (hv.trans (A.X.src_inv ψ).symm) (A.X.tgt_inv ψ).symm, A.X.comp_inv,
    fibAct_unit_rt hv]

theorem π_fibAct_rt {ψ : A.Mor} {v : A.W} (hv : A.P v = A.X.src ψ) :
    A.E.toEpGroupoid.π (fibAct ψ v) = A.E.toEpGroupoid.π v := by
  rw [fibAct_of hv, EpStrongBundle.π_μ]

end PushChart

variable {F : C ⟶ A} (hF : SEP.equivalences F)
namespace IsPushNbhd

variable {hF} {x : C.Obj} {y : A.Obj} {T : (SEP.Hom.ϕ F).TransportChart x y}
  {N : C.X.NatNbhd x} {N' : A.X.NatNbhd y} (h : IsPushNbhd T N N')
include h

theorem Qinv_mem_W_rt {z : A.Obj} (hz : z ∈ N'.U) : T.Qinv z ∈ T.W :=
  T.isScDiffeoOn_Q.mapsTo_inv (h.subset_W' hz)

theorem Q_Qinv_rt {z : A.Obj} (hz : z ∈ N'.U) : T.Q (T.Qinv z) = z :=
  T.isScDiffeoOn_Q.right_inv z (h.subset_W' hz)

theorem tgt_ψ_Qinv_rt {z : A.Obj} (hz : z ∈ N'.U) : A.X.tgt (T.ψ (T.Qinv z)) = z := by
  rw [T.tgt_ψ _ (h.Qinv_mem_W_rt hz), h.Q_Qinv_rt hz]

theorem src_ψ_Qinv_rt {z : A.Obj} (hz : z ∈ N'.U) :
    A.X.src (T.ψ (T.Qinv z)) = (SEP.Hom.ϕ F).obj (T.Qinv z) :=
  T.src_ψ _ (h.Qinv_mem_W_rt hz)


theorem Φ_eq_rt (g : C.X.Isotropy x) {z : A.Obj} (hz : z ∈ N'.U) :
    N'.rep.Φ (T.conj g) z = T.Q (N.rep.Φ g (T.Qinv z)) := by
  have e := congrArg A.X.tgt (h.Γ_eq g z hz)
  rw [N'.tgt_Γ _ hz, A.X.tgt_comp _ _ (TransportChartLemmas.src_comp_eq_tgt_inv T N
      (h.Qinv_mem hz) (h.Qinv_mem_W_rt hz) (h.Φ_mem_W z hz g)),
    A.X.tgt_comp _ _ (TransportChartLemmas.src_ψ_eq_tgt T N (h.Qinv_mem hz) (h.Φ_mem_W z hz g)),
    T.tgt_ψ _ (h.Φ_mem_W z hz g)] at e
  exact e

theorem Qinv_Φ_rt (g : C.X.Isotropy x) {z : A.Obj} (hz : z ∈ N'.U) :
    T.Qinv (N'.rep.Φ (T.conj g) z) = N.rep.Φ g (T.Qinv z) := by
  rw [h.Φ_eq_rt g hz, T.isScDiffeoOn_Q.left_inv _ (h.Φ_mem_W z hz g)]


theorem Γ_comp_ψ_rt (g : C.X.Isotropy x) {z : A.Obj} (hz : z ∈ N'.U) :
    A.X.comp (N'.rep.Γ (T.conj g) z) (T.ψ (T.Qinv z)) =
      A.X.comp (T.ψ (N.rep.Φ g (T.Qinv z))) ((SEP.Hom.ϕ F).mor (N.rep.Γ g (T.Qinv z))) := by
  rw [h.Γ_eq g z hz, A.X.comp_assoc _ _ _ (TransportChartLemmas.src_comp_eq_tgt_inv T N
      (h.Qinv_mem hz) (h.Qinv_mem_W_rt hz) (h.Φ_mem_W z hz g)) (A.X.src_inv _), A.X.inv_comp]
  have e := TransportChartLemmas.src_comp_eq_tgt_inv T N (h.Qinv_mem hz) (h.Qinv_mem_W_rt hz)
      (h.Φ_mem_W z hz g)
  rw [A.X.tgt_inv] at e
  exact A.X.comp_unit_of_eq e

end IsPushNbhd


theorem exists_isPushNbhd_rt {x : C.Obj} {y : A.Obj} (T : (SEP.Hom.ϕ F).TransportChart x y)
    (N : C.X.NatNbhd x) :
    ∃ N' : A.X.NatNbhd y, IsPushNbhd T N N' ∧ A.X.IsProperSubset (closure N'.U) := by
  set W₀ := N.invariantCore T.W with hW₀def
  have hW₀ : IsOpen W₀ := N.isOpen_invariantCore T.isOpen_W
  have hQinv : ContinuousOn T.Qinv T.W' := T.isScDiffeoOn_Q.isScSmoothOn_inv.continuousOn
  set O' := T.W' ∩ T.Qinv ⁻¹' W₀ with hO'def
  have hO' : IsOpen O' := hQinv.isOpen_inter_preimage T.isOpen_W' hW₀
  have hQx : T.Qinv y = x := by
    have e := T.isScDiffeoOn_Q.left_inv x T.mem_W
    rwa [T.Q_self] at e
  have hyO' : y ∈ O' :=
    ⟨T.mem_W', by rw [mem_preimage, hQx]; exact N.mem_invariantCore T.mem_W⟩
  obtain ⟨N₀, hN₀O, hprop⟩ := A.X.exists_natNbhd_isProperSubset y hO' hyO'
  have hW' : ∀ z ∈ N₀.U, z ∈ T.W' := fun z hz => (hN₀O hz).1
  have hu : ∀ z ∈ N₀.U, T.Qinv z ∈ W₀ := fun z hz => (hN₀O hz).2
  have huN : ∀ z ∈ N₀.U, T.Qinv z ∈ N.U := fun z hz => (N.invariantCore_subset _ (hu z hz)).1
  have huW : ∀ z ∈ N₀.U, T.Qinv z ∈ T.W := fun z hz =>
    T.isScDiffeoOn_Q.mapsTo_inv (hW' z hz)
  have hgW : ∀ z ∈ N₀.U, ∀ g, N.rep.Φ g (T.Qinv z) ∈ T.W := fun z hz g =>
    (N.invariantCore_subset _ (N.mapsTo_Φ_invariantCore _ g (hu z hz))).2
  have hQinv₀ : ContinuousOn T.Qinv N₀.U := hQinv.mono hW'
  set e : C.X.Isotropy x → A.Obj → A.Mor := fun g z =>
    A.X.comp (A.X.comp (T.ψ (N.rep.Φ g (T.Qinv z))) ((SEP.Hom.ϕ F).mor (N.rep.Γ g (T.Qinv z))))
      (A.X.inv (T.ψ (T.Qinv z))) with hedef
  set E : Set A.Obj := N₀.U ∩ ⋂ g, {z | z ∈ N₀.U ∧ N₀.rep.Γ (T.conj g) z = e g z} with hEdef
  have hE : IsOpen E := by
    refine N₀.isOpen_U.inter (isOpen_iInter_of_finite fun g => ?_)
    have h1 : ContinuousOn (fun z => T.ψ (N.rep.Φ g (T.Qinv z))) N₀.U :=
      T.continuousOn_ψ.comp ((N.rep.continuousOn_Φ g).comp hQinv₀ fun z hz =>
        N.U_subset (huN z hz)) fun z hz => hgW z hz g
    have h2 : ContinuousOn (fun z => (SEP.Hom.ϕ F).mor (N.rep.Γ g (T.Qinv z))) N₀.U :=
      (SEP.Hom.ϕ F).continuous_mor.comp_continuousOn
        ((N.rep.isScSmoothOn_Γ g).continuousOn.comp hQinv₀ fun z hz => N.U_subset (huN z hz))
    have h3 : ContinuousOn (fun z => A.X.inv (T.ψ (T.Qinv z))) N₀.U :=
      A.X.continuous_inv.comp_continuousOn (T.continuousOn_ψ.comp hQinv₀ huW)
    have he : ContinuousOn (e g) N₀.U :=
      A.X.continuousOn_comp_of (A.X.continuousOn_comp_of h1 h2 fun z hz =>
        TransportChartLemmas.src_ψ_eq_tgt T N (huN z hz) (hgW z hz g)) h3 fun z hz =>
          TransportChartLemmas.src_comp_eq_tgt_inv T N (huN z hz) (huW z hz) (hgW z hz g)
    refine A.X.isOpen_setOf_eq_of_src N₀.isOpen_U
      ((N₀.rep.isScSmoothOn_Γ _).continuousOn.mono N₀.U_subset) he fun z hz => ?_
    rw [N₀.src_Γ _ hz, hedef, A.X.src_comp _ _ (TransportChartLemmas.src_comp_eq_tgt_inv T N
      (huN z hz) (huW z hz) (hgW z hz g)), A.X.src_inv, T.tgt_ψ _ (huW z hz),
      T.isScDiffeoOn_Q.right_inv z (hW' z hz)]
  have hyE : y ∈ E := ⟨N₀.mem_U, mem_iInter.2 fun g => ⟨N₀.mem_U, by
    rw [N₀.rep.Γ_self, hedef]
    simp only
    rw [hQx, N.rep.Φ_self, N.rep.Γ_self, T.ψ_self, T.conj_val]⟩⟩
  obtain ⟨N', hrep, hsub⟩ := N₀.exists_restrict_subset hE hyE
  refine ⟨N', ⟨fun z hz => hW' z (hsub hz).1, fun hz => huN _ (hsub hz).1,
    fun z hz => hgW z (hsub hz).1, fun g z hz => ?_⟩,
    isProperMap_domRestrict_of_subset_of_isClosed A.X.continuous_src hprop
      (closure_mono fun z hz => (hsub hz).1) isClosed_closure⟩
  rw [hrep]
  exact (mem_iInter.1 (hsub hz).2.2 g).2




namespace IsPushNbhd

variable {x : C.Obj} {y : A.Obj} {T : (SEP.Hom.ϕ F).TransportChart x y}
  {N : C.X.NatNbhd x} {N' : A.X.NatNbhd y} (h : IsPushNbhd T N N')
include hF h

theorem P_obj_rt {s : C.Obj → C.W} (hs : ∀ u ∈ N.U, C.P (s u) = u) {z : A.Obj} (hz : z ∈ N'.U) :
    A.P ((SEP.Hom.Φ F).obj (s (T.Qinv z))) = A.X.src (T.ψ (T.Qinv z)) := by
  have e := (PullMap.ofEquivalence hF).covers (s (T.Qinv z))
  simp only [PullMap.ofEquivalence_Φ, PullMap.ofEquivalence_ϕ] at e
  rw [e, hs _ (h.Qinv_mem hz), h.src_ψ_Qinv_rt hz]

theorem pushSec_eq_rt {s : C.Obj → C.W} (hs : ∀ u ∈ N.U, C.P (s u) = u) {z : A.Obj}
    (hz : z ∈ N'.U) :
    pushSec T s z = fibAct (T.ψ (T.Qinv z)) ((SEP.Hom.Φ F).obj (s (T.Qinv z))) := by
  rw [pushSec, transportSection_of_mem (h.P_obj_rt hF hs hz), fibAct_of (h.P_obj_rt hF hs hz)]; rfl


theorem isScPlusSectionOn_pushSec_rt {s : C.Obj → C.W} (hs : IsScPlusSectionOn C s N.U) :
    IsScPlusSectionOn A (pushSec T s) N'.U := by
  obtain ⟨hsec, G, hG, hGs⟩ := hs
  have hFs := (sbe hF).isStrongBundleFunctor.isStrongBundleMap_obj
  have hQ : A.X.PObj.IsScSmoothOn C.X.PObj T.Qinv N'.U :=
    T.isScDiffeoOn_Q.isScSmoothOn_inv.mono N'.isOpen_U h.subset_W'
  refine isScPlusSectionOn_transportSection
    (G := oneRestrict C.B A.B (SEP.Hom.Φ F).obj hFs.mapsTo_oneSet ∘ G ∘ T.Qinv)
    (MPolyfold.IsScSmoothOn.comp T.isScSmoothOn_ψ hQ fun z hz => h.Qinv_mem_W_rt hz)
    (fun z hz => ?_)
    (MPolyfold.IsScSmoothOn.comp hFs.isScSmoothMap_one
      (MPolyfold.IsScSmoothOn.comp hGs hQ fun z hz => h.Qinv_mem hz) (mapsTo_univ _ _))
    (fun z hz => h.P_obj_rt hF hsec hz) fun z hz => h.tgt_ψ_Qinv_rt hz
  change A.B.oneVal (oneRestrict C.B A.B _ _ (G (T.Qinv z))) = (SEP.Hom.Φ F).obj (s (T.Qinv z))
  rw [oneVal_oneRestrict, hG _ (h.Qinv_mem hz)]

end IsPushNbhd
end SSP

section MP
variable {A C : SEP.{u}} {F : C ⟶ A} (hF : SEP.equivalences F)
namespace PushChart



include hF in

theorem continuousAt_of_mor_rt {α : Type*} [TopologicalSpace α] {f : α → C.Mor} {a : α}
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


theorem mapsTo_connectedComponentIn_rt {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β} {S : Set α} {S' : Set β} (hf : ContinuousOn f S) (hS : MapsTo f S S') {a : α}
    (ha : a ∈ S) : MapsTo f (connectedComponentIn S a) (connectedComponentIn S' (f a)) := by
  intro b hb
  have hpre := (isPreconnected_connectedComponentIn :
    IsPreconnected (connectedComponentIn S a)).image f
    (hf.mono (connectedComponentIn_subset S a))
  refine hpre.subset_connectedComponentIn ⟨a, mem_connectedComponentIn ha, rfl⟩ ?_ ⟨b, hb, rfl⟩
  rintro _ ⟨c, hc, rfl⟩
  exact hS (connectedComponentIn_subset S a hc)



variable {x x' : C.Obj} {y y' : A.Obj}

theorem tgt_ψ_Qinv_rt (T : (SEP.Hom.ϕ F).TransportChart x y) {z : A.Obj} (hz : z ∈ T.W') :
    A.X.tgt (T.ψ (T.Qinv z)) = z := by
  rw [T.tgt_ψ _ (T.isScDiffeoOn_Q.mapsTo_inv hz), T.isScDiffeoOn_Q.right_inv z hz]

theorem src_ψ_Qinv_rt (T : (SEP.Hom.ϕ F).TransportChart x y) {z : A.Obj} (hz : z ∈ T.W') :
    A.X.src (T.ψ (T.Qinv z)) = (SEP.Hom.ϕ F).obj (T.Qinv z) :=
  T.src_ψ _ (T.isScDiffeoOn_Q.mapsTo_inv hz)


theorem isOpen_Dom_rt (T : (SEP.Hom.ϕ F).TransportChart x y)
    (T' : (SEP.Hom.ϕ F).TransportChart x' y') : IsOpen (Dom T T') :=
  isOpen_morBetween T.isOpen_W' T'.isOpen_W'


section Lift

variable {T : (SEP.Hom.ϕ F).TransportChart x y} {T' : (SEP.Hom.ϕ F).TransportChart x' y'}
  {φ' : A.Mor}

theorem src_comp_ψ_rt (hφ : φ' ∈ Dom T T') : A.X.src φ' = A.X.tgt (T.ψ (T.Qinv (A.X.src φ'))) :=
  (tgt_ψ_Qinv_rt T hφ.1).symm

theorem src_inv_ψ'_rt (hφ : φ' ∈ Dom T T') :
    A.X.src (A.X.inv (T'.ψ (T'.Qinv (A.X.tgt φ')))) =
      A.X.tgt (A.X.comp φ' (T.ψ (T.Qinv (A.X.src φ')))) := by
  rw [A.X.src_inv, tgt_ψ_Qinv_rt T' hφ.2, A.X.tgt_comp _ _ (src_comp_ψ_rt hφ)]

theorem src_liftTarget_rt (hφ : φ' ∈ Dom T T') :
    A.X.src (liftTarget T T' φ') = (SEP.Hom.ϕ F).obj (T.Qinv (A.X.src φ')) := by
  rw [liftTarget, A.X.src_comp _ _ (src_inv_ψ'_rt hφ), A.X.src_comp _ _ (src_comp_ψ_rt hφ),
    src_ψ_Qinv_rt T hφ.1]

theorem tgt_liftTarget_rt (hφ : φ' ∈ Dom T T') :
    A.X.tgt (liftTarget T T' φ') = (SEP.Hom.ϕ F).obj (T'.Qinv (A.X.tgt φ')) := by
  rw [liftTarget, A.X.tgt_comp _ _ (src_inv_ψ'_rt hφ), A.X.tgt_inv, src_ψ_Qinv_rt T' hφ.2]

include hF

theorem exists_isLift_rt (hφ : φ' ∈ Dom T T') : ∃ φ, IsLift T T' φ' φ :=
  (sbe hF).isEquivalence_base.exists_mor_eq (src_liftTarget_rt hφ) (tgt_liftTarget_rt hφ)

theorem isLift_liftMor_rt (hφ : φ' ∈ Dom T T') : IsLift T T' φ' (liftMor T T' φ') := by
  rw [liftMor, dif_pos (exists_isLift_rt hF hφ)]
  exact (exists_isLift_rt hF hφ).choose_spec

theorem src_liftMor_rt (hφ : φ' ∈ Dom T T') : C.X.src (liftMor T T' φ') = T.Qinv (A.X.src φ') :=
  (isLift_liftMor_rt hF hφ).1

theorem tgt_liftMor_rt (hφ : φ' ∈ Dom T T') : C.X.tgt (liftMor T T' φ') = T'.Qinv (A.X.tgt φ') :=
  (isLift_liftMor_rt hF hφ).2.1

theorem liftMor_eq_rt (hφ : φ' ∈ Dom T T') {φ : C.Mor} (h : IsLift T T' φ' φ) :
    liftMor T T' φ' = φ :=
  (sbe hF).isEquivalence_base.mor_injective ((src_liftMor_rt hF hφ).trans h.1.symm)
    ((tgt_liftMor_rt hF hφ).trans h.2.1.symm) ((isLift_liftMor_rt hF hφ).2.2.trans h.2.2.symm)


theorem comp_liftMor_rt (hφ : φ' ∈ Dom T T') :
    A.X.comp (T'.ψ (C.X.tgt (liftMor T T' φ'))) ((SEP.Hom.ϕ F).mor (liftMor T T' φ')) =
      A.X.comp φ' (T.ψ (C.X.src (liftMor T T' φ'))) := by
  rw [src_liftMor_rt hF hφ, tgt_liftMor_rt hF hφ, (isLift_liftMor_rt hF hφ).2.2, liftTarget]
  have e := A.X.inv_comp_cancel_left (φ := A.X.inv (T'.ψ (T'.Qinv (A.X.tgt φ'))))
    (src_inv_ψ'_rt hφ)
  rwa [A.X.inv_inv] at e


theorem liftMor_eq_of_comp_rt (hφ : φ' ∈ Dom T T') {φ : C.Mor}
    (hs : C.X.src φ = T.Qinv (A.X.src φ')) (ht : C.X.tgt φ = T'.Qinv (A.X.tgt φ'))
    (hc : A.X.comp (T'.ψ (C.X.tgt φ)) ((SEP.Hom.ϕ F).mor φ) = A.X.comp φ' (T.ψ (C.X.src φ))) :
    liftMor T T' φ' = φ := by
  refine liftMor_eq_rt hF hφ ⟨hs, ht, ?_⟩
  have hW : C.X.tgt φ ∈ T'.W := by rw [ht]; exact T'.isScDiffeoOn_Q.mapsTo_inv hφ.2
  rw [liftTarget, ← hs, ← ht, ← hc]
  refine (A.X.inv_comp_cancel_left ?_).symm
  rw [T'.src_ψ _ hW, (SEP.Hom.ϕ F).tgt_mor]

omit hF in
theorem continuousOn_liftTarget_rt :
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
      fun _ hb => T.isScDiffeoOn_Q.mapsTo_inv hb.1) fun _ hb => src_comp_ψ_rt hb
  exact A.X.continuousOn_comp_of h1 h2 fun _ hb => src_inv_ψ'_rt hb


theorem continuousOn_liftMor_rt : ContinuousOn (liftMor T T') (Dom T T') := by
  intro φ' hφ
  have hN : Dom T T' ∈ 𝓝 φ' := (isOpen_Dom_rt T T').mem_nhds hφ
  have hQ : ContinuousOn T.Qinv T.W' := T.isScDiffeoOn_Q.isScSmoothOn_inv.continuousOn
  have hQ' : ContinuousOn T'.Qinv T'.W' := T'.isScDiffeoOn_Q.isScSmoothOn_inv.continuousOn
  refine (continuousAt_of_mor_rt hF ?_ ?_ ?_).continuousWithinAt
  · refine ContinuousAt.congr ((hQ.continuousAt (T.isOpen_W'.mem_nhds hφ.1)).comp
      A.X.continuous_src.continuousAt) ?_
    filter_upwards [hN] with b hb using (src_liftMor_rt hF hb).symm
  · refine ContinuousAt.congr ((hQ'.continuousAt (T'.isOpen_W'.mem_nhds hφ.2)).comp
      A.X.continuous_tgt.continuousAt) ?_
    filter_upwards [hN] with b hb using (tgt_liftMor_rt hF hb).symm
  · refine ContinuousAt.congr ((continuousOn_liftTarget_rt (T := T) (T' := T')).continuousAt hN) ?_
    filter_upwards [hN] with b hb using (isLift_liftMor_rt hF hb).2.2.symm


theorem injOn_liftMor_rt : InjOn (liftMor T T') (Dom T T') := by
  intro a ha b hb e
  have ca := comp_liftMor_rt hF ha
  have cb := comp_liftMor_rt hF hb
  rw [e] at ca
  have hsa : C.X.src (liftMor T T' b) = T.Qinv (A.X.src a) := by rw [← e, src_liftMor_rt hF ha]
  have hsb := src_liftMor_rt hF hb
  refine A.X.comp_right_cancel ?_ ?_ (ca.symm.trans cb)
  · rw [hsa]; exact src_comp_ψ_rt ha
  · rw [hsb]; exact src_comp_ψ_rt hb

end Lift

include hF


theorem liftMor_comp_rt {x₁ x₂ x₃ : C.Obj} {y₁ y₂ y₃ : A.Obj}
    (T₁ : (SEP.Hom.ϕ F).TransportChart x₁ y₁) (T₂ : (SEP.Hom.ϕ F).TransportChart x₂ y₂)
    (T₃ : (SEP.Hom.ϕ F).TransportChart x₃ y₃) {φ₁ φ₂ : A.Mor} (h₁ : φ₁ ∈ Dom T₁ T₂)
    (h₂ : φ₂ ∈ Dom T₂ T₃) (h : A.X.src φ₂ = A.X.tgt φ₁) :
    liftMor T₁ T₃ (A.X.comp φ₂ φ₁) = C.X.comp (liftMor T₂ T₃ φ₂) (liftMor T₁ T₂ φ₁) := by
  have hL : C.X.src (liftMor T₂ T₃ φ₂) = C.X.tgt (liftMor T₁ T₂ φ₁) := by
    rw [src_liftMor_rt hF h₂, tgt_liftMor_rt hF h₁, h]
  have h₁₂ : A.X.comp φ₂ φ₁ ∈ Dom T₁ T₃ :=
    ⟨by rw [A.X.src_comp _ _ h]; exact h₁.1, by rw [A.X.tgt_comp _ _ h]; exact h₂.2⟩
  have hW₂ : C.X.tgt (liftMor T₂ T₃ φ₂) ∈ T₃.W := by
    rw [tgt_liftMor_rt hF h₂]; exact T₃.isScDiffeoOn_Q.mapsTo_inv h₂.2
  have hW₁ : C.X.src (liftMor T₂ T₃ φ₂) ∈ T₂.W := by
    rw [src_liftMor_rt hF h₂]; exact T₂.isScDiffeoOn_Q.mapsTo_inv h₂.1
  have e1 : A.X.src (T₃.ψ (C.X.tgt (liftMor T₂ T₃ φ₂))) =
      A.X.tgt ((SEP.Hom.ϕ F).mor (liftMor T₂ T₃ φ₂)) := by
    rw [T₃.src_ψ _ hW₂, (SEP.Hom.ϕ F).tgt_mor]
  have e2 : A.X.src ((SEP.Hom.ϕ F).mor (liftMor T₂ T₃ φ₂)) =
      A.X.tgt ((SEP.Hom.ϕ F).mor (liftMor T₁ T₂ φ₁)) := by
    rw [(SEP.Hom.ϕ F).src_mor, (SEP.Hom.ϕ F).tgt_mor, hL]
  have e3 : A.X.src φ₂ = A.X.tgt (T₂.ψ (C.X.src (liftMor T₂ T₃ φ₂))) := by
    rw [src_liftMor_rt hF h₂]; exact src_comp_ψ_rt h₂
  have e4 : A.X.src (T₂.ψ (C.X.src (liftMor T₂ T₃ φ₂))) =
      A.X.tgt ((SEP.Hom.ϕ F).mor (liftMor T₁ T₂ φ₁)) := by
    rw [T₂.src_ψ _ hW₁, (SEP.Hom.ϕ F).tgt_mor, hL]
  have e5 : A.X.src φ₁ = A.X.tgt (T₁.ψ (C.X.src (liftMor T₁ T₂ φ₁))) := by
    rw [src_liftMor_rt hF h₁]; exact src_comp_ψ_rt h₁
  refine liftMor_eq_of_comp_rt hF h₁₂ ?_ ?_ ?_
  · rw [C.X.src_comp _ _ hL, src_liftMor_rt hF h₁, A.X.src_comp _ _ h]
  · rw [C.X.tgt_comp _ _ hL, tgt_liftMor_rt hF h₂, A.X.tgt_comp _ _ h]
  · rw [C.X.src_comp _ _ hL, C.X.tgt_comp _ _ hL, (SEP.Hom.ϕ F).mor_comp _ _ hL,
      ← A.X.comp_assoc _ _ _ e1 e2, comp_liftMor_rt hF h₂, A.X.comp_assoc _ _ _ e3 e4, hL,
      comp_liftMor_rt hF h₁, ← A.X.comp_assoc _ _ _ h e5]


theorem liftMor_inv_rt (T : (SEP.Hom.ϕ F).TransportChart x y)
    (T' : (SEP.Hom.ϕ F).TransportChart x' y') {φ' : A.Mor} (hφ : φ' ∈ Dom T T') :
    liftMor T' T (A.X.inv φ') = C.X.inv (liftMor T T' φ') := by
  have hD : A.X.inv φ' ∈ Dom T' T :=
    ⟨by rw [A.X.src_inv]; exact hφ.2, by rw [A.X.tgt_inv]; exact hφ.1⟩
  refine liftMor_eq_rt hF hD ⟨by rw [C.X.src_inv, tgt_liftMor_rt hF hφ, A.X.src_inv],
    by rw [C.X.tgt_inv, src_liftMor_rt hF hφ, A.X.tgt_inv], ?_⟩
  have k3 : A.X.src (A.X.inv (T.ψ (T.Qinv (A.X.src φ')))) = A.X.tgt (A.X.inv φ') := by
    rw [A.X.src_inv, A.X.tgt_inv]; exact (src_comp_ψ_rt hφ).symm
  have k4 : A.X.src (A.X.inv φ') = A.X.tgt (T'.ψ (T'.Qinv (A.X.tgt φ'))) := by
    rw [A.X.src_inv, tgt_ψ_Qinv_rt T' hφ.2]
  rw [(SEP.Hom.ϕ F).mor_inv, (isLift_liftMor_rt hF hφ).2.2, liftTarget, liftTarget, A.X.src_inv,
    A.X.tgt_inv, A.X.inv_comp_rev (src_inv_ψ'_rt hφ), A.X.inv_comp_rev (src_comp_ψ_rt hφ),
    A.X.inv_inv, A.X.comp_assoc _ _ _ k3 k4]

variable {T : (SEP.Hom.ϕ F).TransportChart x y} {T' : (SEP.Hom.ϕ F).TransportChart x' y'}
  {N : C.X.NatNbhd x} {N' : A.X.NatNbhd y} {M : C.X.NatNbhd x'} {M' : A.X.NatNbhd y'}

omit hF in
theorem morBetween_subset_Dom_rt (h : IsPushNbhd T N N') (h' : IsPushNbhd T' M M') :
    A.X.morBetween N'.U M'.U ⊆ Dom T T' :=
  fun _ hφ => ⟨h.subset_W' hφ.1, h'.subset_W' hφ.2⟩

theorem liftMor_mem_rt (h : IsPushNbhd T N N') (h' : IsPushNbhd T' M M') {φ' : A.Mor}
    (hφ : φ' ∈ A.X.morBetween N'.U M'.U) : liftMor T T' φ' ∈ C.X.morBetween N.U M.U := by
  have hD := morBetween_subset_Dom_rt h h' hφ
  exact ⟨by rw [src_liftMor_rt hF hD]; exact h.Qinv_mem hφ.1,
    by rw [tgt_liftMor_rt hF hD]; exact h'.Qinv_mem hφ.2⟩


theorem liftMor_Γ_rt (h : IsPushNbhd T N N') (g : C.X.Isotropy x) {z : A.Obj} (hz : z ∈ N'.U) :
    liftMor T T (N'.rep.Γ (T.conj g) z) = N.rep.Γ g (T.Qinv z) := by
  have hD : N'.rep.Γ (T.conj g) z ∈ Dom T T :=
    ⟨by rw [N'.src_Γ _ hz]; exact h.subset_W' hz,
      by rw [N'.tgt_Γ _ hz]; exact h.subset_W' (N'.Φ_mem _ hz)⟩
  have hu := h.Qinv_mem hz
  refine liftMor_eq_of_comp_rt hF hD (by rw [N.src_Γ g hu, N'.src_Γ _ hz])
    (by rw [N.tgt_Γ g hu, N'.tgt_Γ _ hz, h.Qinv_Φ_rt g hz]) ?_
  rw [N.tgt_Γ g hu, N.src_Γ g hu]
  exact (h.Γ_comp_ψ_rt g hz).symm


theorem liftMor_biact_rt (h : IsPushNbhd T N N') (h' : IsPushNbhd T' M M') {φ' : A.Mor}
    (hφ : φ' ∈ A.X.morBetween N'.U M'.U) (k' : C.X.Isotropy x') (k : C.X.Isotropy x) :
    liftMor T T' (EpGroupoid.biact N' M' (T'.conj k') φ' (T.conj k)) =
      EpGroupoid.biact N M k' (liftMor T T' φ') k := by
  have hφD := morBetween_subset_Dom_rt h h' hφ
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
  rw [EpGroupoid.biact, EpGroupoid.biact, ← hwdef, liftMor_comp_rt hF T T' T' hc ha hac,
    liftMor_comp_rt hF T T T' hb hφD hbt, liftMor_Γ_rt hF h' k' hφ.2, liftMor_Γ_rt hF h k hw,
    tgt_liftMor_rt hF hφD, src_liftMor_rt hF hφD, hwdef,
    show (T.conj k)⁻¹ = T.conj k⁻¹ from (map_inv T.conj k).symm, h.Qinv_Φ_rt k⁻¹ hφ.1]


theorem pushSec_compat_rt (h : IsPushNbhd T N N') (h' : IsPushNbhd T' M M')
    {s s' : C.Obj → C.W} (hs : ∀ u ∈ N.U, C.P (s u) = u) (hs' : ∀ u ∈ M.U, C.P (s' u) = u)
    {ψ' : A.Mor} (hψ : ψ' ∈ A.X.morBetween N'.U M'.U)
    (hc : s' (C.X.tgt (liftMor T T' ψ')) =
      fibAct (liftMor T T' ψ') (s (C.X.src (liftMor T T' ψ')))) :
    pushSec T' s' (A.X.tgt ψ') = fibAct ψ' (pushSec T s (A.X.src ψ')) := by
  have hD := morBetween_subset_Dom_rt h h' hψ
  have hsL := src_liftMor_rt hF hD
  have htL := tgt_liftMor_rt hF hD
  have hu : C.X.src (liftMor T T' ψ') ∈ N.U := by rw [hsL]; exact h.Qinv_mem hψ.1
  have huW : C.X.src (liftMor T T' ψ') ∈ T.W := by
    rw [hsL]; exact T.isScDiffeoOn_Q.mapsTo_inv hD.1
  have hu'W : C.X.tgt (liftMor T T' ψ') ∈ T'.W := by
    rw [htL]; exact T'.isScDiffeoOn_Q.mapsTo_inv hD.2
  rw [h'.pushSec_eq_rt hF hs' hψ.2, h.pushSec_eq_rt hF hs hψ.1, ← htL, ← hsL, hc]
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
  rw [e1, ← SBLocalization.fibAct_comp_rt hv (by rw [T'.src_ψ _ hu'W, (SEP.Hom.ϕ F).tgt_mor]),
    comp_liftMor_rt hF hD, SBLocalization.fibAct_comp_rt hv2 (by rw [hsL]; exact src_comp_ψ_rt hD)]


theorem isDiffeoComponent_push_rt (𝒰 : C.X.GoodSystem) {T : (SEP.Hom.ϕ F).TransportChart x y}
    {T' : (SEP.Hom.ϕ F).TransportChart x' y'} {N' : A.X.NatNbhd y} {M' : A.X.NatNbhd y'}
    (h : IsPushNbhd T (𝒰.nbhd x) N') (h' : IsPushNbhd T' (𝒰.nbhd x') M') {φ' : A.Mor}
    (hφ : φ' ∈ A.X.morBetween N'.U M'.U) :
    A.X.IsDiffeoComponent (connectedComponentIn (A.X.morBetween N'.U M'.U) φ') := by
  have hsubD := morBetween_subset_Dom_rt h h'
  have hmaps : MapsTo (liftMor T T') (connectedComponentIn (A.X.morBetween N'.U M'.U) φ')
      (𝒰.comp x x' (liftMor T T' φ')) :=
    mapsTo_connectedComponentIn_rt ((continuousOn_liftMor_rt hF).mono hsubD)
      (fun _ hψ => liftMor_mem_rt hF h h' hψ) hφ
  have hL : liftMor T T' φ' ∈ 𝒰.mor x x' := liftMor_mem_rt hF h h' hφ
  have hsub : ∀ {ψ}, ψ ∈ connectedComponentIn (A.X.morBetween N'.U M'.U) φ' → ψ ∈ Dom T T' :=
    fun hψ => hsubD (connectedComponentIn_subset _ _ hψ)
  refine (isDiffeoComponent_iff_injOn (isOpen_connectedComponentIn_mor A.X
    (isOpen_morBetween N'.isOpen_U M'.isOpen_U) φ')).2
    ⟨fun ψ₁ hψ₁ ψ₂ hψ₂ e => ?_, fun ψ₁ hψ₁ ψ₂ hψ₂ e => ?_⟩
  · refine injOn_liftMor_rt hF (hsub hψ₁) (hsub hψ₂)
      (𝒰.injOn_src_comp hL (hmaps hψ₁) (hmaps hψ₂) ?_)
    rw [src_liftMor_rt hF (hsub hψ₁), src_liftMor_rt hF (hsub hψ₂), e]
  · refine injOn_liftMor_rt hF (hsub hψ₁) (hsub hψ₂)
      (𝒰.injOn_tgt_comp hL (hmaps hψ₁) (hmaps hψ₂) ?_)
    rw [tgt_liftMor_rt hF (hsub hψ₁), tgt_liftMor_rt hF (hsub hψ₂), e]

end PushChart
end MP

end SBLocalization

end Polyfold

end

namespace RoundTrip.V13_52
open Polyfold Polyfold.SBLocalization CategoryTheory

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.SBLocalization.fibAct_comp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.fibAct_unit.{0}) ∧
  (type_of% @Polyfold.SBLocalization.PushChart.fibAct_inv_fibAct.{0}) ∧
  (type_of% @Polyfold.SBLocalization.PushChart.fibAct_fibAct_inv.{0}) ∧
  (type_of% @Polyfold.SBLocalization.PushChart.π_fibAct.{0}) ∧
  (type_of% @Polyfold.SBLocalization.IsPushNbhd.Φ_eq.{0}) ∧
  (type_of% @Polyfold.SBLocalization.IsPushNbhd.Qinv_Φ.{0}) ∧
  (type_of% @Polyfold.SBLocalization.IsPushNbhd.Γ_comp_ψ.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_isPushNbhd.{0}) ∧
  (type_of% @Polyfold.SBLocalization.IsPushNbhd.pushSec_eq.{0}) ∧
  (type_of% @Polyfold.SBLocalization.IsPushNbhd.isScPlusSectionOn_pushSec.{0}) ∧
  (type_of% @Polyfold.SBLocalization.PushChart.continuousAt_of_mor.{0, 0}) ∧
  (type_of% @Polyfold.SBLocalization.PushChart.mapsTo_connectedComponentIn.{0, 0}) ∧
  (type_of% @Polyfold.SBLocalization.PushChart.comp_liftMor.{0}) ∧
  (type_of% @Polyfold.SBLocalization.PushChart.liftMor_eq_of_comp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.PushChart.continuousOn_liftMor.{0}) ∧
  (type_of% @Polyfold.SBLocalization.PushChart.injOn_liftMor.{0}) ∧
  (type_of% @Polyfold.SBLocalization.PushChart.liftMor_comp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.PushChart.liftMor_inv.{0}) ∧
  (type_of% @Polyfold.SBLocalization.PushChart.liftMor_Γ.{0}) ∧
  (type_of% @Polyfold.SBLocalization.PushChart.liftMor_biact.{0}) ∧
  (type_of% @Polyfold.SBLocalization.PushChart.pushSec_compat.{0}) ∧
  (type_of% @Polyfold.SBLocalization.PushChart.isDiffeoComponent_push.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_13_4_3.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_13_4_3_structured.{0})

theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.fibAct_comp.{0}, @Polyfold.SBLocalization.fibAct_unit.{0},
    @Polyfold.SBLocalization.PushChart.fibAct_inv_fibAct.{0},
    @Polyfold.SBLocalization.PushChart.fibAct_fibAct_inv.{0},
    @Polyfold.SBLocalization.PushChart.π_fibAct.{0},
    @Polyfold.SBLocalization.IsPushNbhd.Φ_eq.{0}, @Polyfold.SBLocalization.IsPushNbhd.Qinv_Φ.{0},
    @Polyfold.SBLocalization.IsPushNbhd.Γ_comp_ψ.{0},
    @Polyfold.SBLocalization.exists_isPushNbhd.{0},
    @Polyfold.SBLocalization.IsPushNbhd.pushSec_eq.{0},
    @Polyfold.SBLocalization.IsPushNbhd.isScPlusSectionOn_pushSec.{0},
    @Polyfold.SBLocalization.PushChart.continuousAt_of_mor.{0, 0},
    @Polyfold.SBLocalization.PushChart.mapsTo_connectedComponentIn.{0, 0},
    @Polyfold.SBLocalization.PushChart.comp_liftMor.{0},
    @Polyfold.SBLocalization.PushChart.liftMor_eq_of_comp.{0},
    @Polyfold.SBLocalization.PushChart.continuousOn_liftMor.{0},
    @Polyfold.SBLocalization.PushChart.injOn_liftMor.{0},
    @Polyfold.SBLocalization.PushChart.liftMor_comp.{0},
    @Polyfold.SBLocalization.PushChart.liftMor_inv.{0},
    @Polyfold.SBLocalization.PushChart.liftMor_Γ.{0},
    @Polyfold.SBLocalization.PushChart.liftMor_biact.{0},
    @Polyfold.SBLocalization.PushChart.pushSec_compat.{0},
    @Polyfold.SBLocalization.PushChart.isDiffeoComponent_push.{0},
    @Polyfold.SBLocalization.theorem_13_4_3.{0},
    @Polyfold.SBLocalization.theorem_13_4_3_structured.{0}⟩

theorem A_to_B : A → B := by
  intro hA C A F hF Λ hΛ Λ' hΛ'
  have h13 : type_of% @Polyfold.SBLocalization.theorem_13_4_3.{0} := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have e : Λ' = pushMult F hF Λ := by
    funext w'
    obtain ⟨ψ, hs, ht⟩ := ((sbe hF).isEquivalence.exists_iso w').choose_spec
    exact hΛ' _ w' ⟨ψ, hs, ht⟩
  rw [e]
  exact h13 hF hΛ

theorem B_to_A : B → A := by
  intro hB
  refine ⟨@fibAct_comp_rt.{0}, @fibAct_unit_rt.{0}, @PushChart.fibAct_inv_fibAct_rt.{0},
    @PushChart.fibAct_fibAct_inv_rt.{0}, @PushChart.π_fibAct_rt.{0}, @IsPushNbhd.Φ_eq_rt.{0},
    @IsPushNbhd.Qinv_Φ_rt.{0}, @IsPushNbhd.Γ_comp_ψ_rt.{0}, @exists_isPushNbhd_rt.{0},
    @IsPushNbhd.pushSec_eq_rt.{0}, @IsPushNbhd.isScPlusSectionOn_pushSec_rt.{0},
    @PushChart.continuousAt_of_mor_rt.{0, 0}, @PushChart.mapsTo_connectedComponentIn_rt.{0, 0},
    @PushChart.comp_liftMor_rt.{0}, @PushChart.liftMor_eq_of_comp_rt.{0},
    @PushChart.continuousOn_liftMor_rt.{0}, @PushChart.injOn_liftMor_rt.{0},
    @PushChart.liftMor_comp_rt.{0}, @PushChart.liftMor_inv_rt.{0}, @PushChart.liftMor_Γ_rt.{0},
    @PushChart.liftMor_biact_rt.{0}, @PushChart.pushSec_compat_rt.{0},
    @PushChart.isDiffeoComponent_push_rt.{0}, ?_, ?_⟩
  · intro A C F hF Λ h
    exact hB C A F hF Λ h (pushMult F hF Λ) fun w w' hiso =>
      pushMult_eq hF h.1.1 ((GroupoidStr.π_eq_π_iff _).2 hiso)
  · intro A C F hF T
    exact ⟨rfl, fun _ => rfl, fun _ _ _ => rfl⟩

#rt_check_soft RoundTrip.V13_52.A_to_B [Polyfold.SBLocalization.fibAct_comp, Polyfold.SBLocalization.fibAct_unit, Polyfold.SBLocalization.PushChart.fibAct_inv_fibAct, Polyfold.SBLocalization.PushChart.fibAct_fibAct_inv, Polyfold.SBLocalization.PushChart.π_fibAct, Polyfold.SBLocalization.IsPushNbhd.Φ_eq, Polyfold.SBLocalization.IsPushNbhd.Qinv_Φ, Polyfold.SBLocalization.IsPushNbhd.Γ_comp_ψ, Polyfold.SBLocalization.exists_isPushNbhd, Polyfold.SBLocalization.IsPushNbhd.pushSec_eq, Polyfold.SBLocalization.IsPushNbhd.isScPlusSectionOn_pushSec, Polyfold.SBLocalization.PushChart.continuousAt_of_mor, Polyfold.SBLocalization.PushChart.mapsTo_connectedComponentIn, Polyfold.SBLocalization.PushChart.comp_liftMor, Polyfold.SBLocalization.PushChart.liftMor_eq_of_comp, Polyfold.SBLocalization.PushChart.continuousOn_liftMor, Polyfold.SBLocalization.PushChart.injOn_liftMor, Polyfold.SBLocalization.PushChart.liftMor_comp, Polyfold.SBLocalization.PushChart.liftMor_inv, Polyfold.SBLocalization.PushChart.liftMor_Γ, Polyfold.SBLocalization.PushChart.liftMor_biact, Polyfold.SBLocalization.PushChart.pushSec_compat, Polyfold.SBLocalization.PushChart.isDiffeoComponent_push, Polyfold.SBLocalization.theorem_13_4_3, Polyfold.SBLocalization.theorem_13_4_3_structured]
#rt_check_soft RoundTrip.V13_52.B_to_A [Polyfold.SBLocalization.fibAct_comp, Polyfold.SBLocalization.fibAct_unit, Polyfold.SBLocalization.PushChart.fibAct_inv_fibAct, Polyfold.SBLocalization.PushChart.fibAct_fibAct_inv, Polyfold.SBLocalization.PushChart.π_fibAct, Polyfold.SBLocalization.IsPushNbhd.Φ_eq, Polyfold.SBLocalization.IsPushNbhd.Qinv_Φ, Polyfold.SBLocalization.IsPushNbhd.Γ_comp_ψ, Polyfold.SBLocalization.exists_isPushNbhd, Polyfold.SBLocalization.IsPushNbhd.pushSec_eq, Polyfold.SBLocalization.IsPushNbhd.isScPlusSectionOn_pushSec, Polyfold.SBLocalization.PushChart.continuousAt_of_mor, Polyfold.SBLocalization.PushChart.mapsTo_connectedComponentIn, Polyfold.SBLocalization.PushChart.comp_liftMor, Polyfold.SBLocalization.PushChart.liftMor_eq_of_comp, Polyfold.SBLocalization.PushChart.continuousOn_liftMor, Polyfold.SBLocalization.PushChart.injOn_liftMor, Polyfold.SBLocalization.PushChart.liftMor_comp, Polyfold.SBLocalization.PushChart.liftMor_inv, Polyfold.SBLocalization.PushChart.liftMor_Γ, Polyfold.SBLocalization.PushChart.liftMor_biact, Polyfold.SBLocalization.PushChart.pushSec_compat, Polyfold.SBLocalization.PushChart.isDiffeoComponent_push, Polyfold.SBLocalization.theorem_13_4_3, Polyfold.SBLocalization.theorem_13_4_3_structured]
#rt_overlap RoundTrip.V13_52.B_to_A [Polyfold.SBLocalization.fibAct_comp, Polyfold.SBLocalization.fibAct_unit, Polyfold.SBLocalization.PushChart.fibAct_inv_fibAct, Polyfold.SBLocalization.PushChart.fibAct_fibAct_inv, Polyfold.SBLocalization.PushChart.π_fibAct, Polyfold.SBLocalization.IsPushNbhd.Φ_eq, Polyfold.SBLocalization.IsPushNbhd.Qinv_Φ, Polyfold.SBLocalization.IsPushNbhd.Γ_comp_ψ, Polyfold.SBLocalization.exists_isPushNbhd, Polyfold.SBLocalization.IsPushNbhd.pushSec_eq, Polyfold.SBLocalization.IsPushNbhd.isScPlusSectionOn_pushSec, Polyfold.SBLocalization.PushChart.continuousAt_of_mor, Polyfold.SBLocalization.PushChart.mapsTo_connectedComponentIn, Polyfold.SBLocalization.PushChart.comp_liftMor, Polyfold.SBLocalization.PushChart.liftMor_eq_of_comp, Polyfold.SBLocalization.PushChart.continuousOn_liftMor, Polyfold.SBLocalization.PushChart.injOn_liftMor, Polyfold.SBLocalization.PushChart.liftMor_comp, Polyfold.SBLocalization.PushChart.liftMor_inv, Polyfold.SBLocalization.PushChart.liftMor_Γ, Polyfold.SBLocalization.PushChart.liftMor_biact, Polyfold.SBLocalization.PushChart.pushSec_compat, Polyfold.SBLocalization.PushChart.isDiffeoComponent_push, Polyfold.SBLocalization.theorem_13_4_3, Polyfold.SBLocalization.theorem_13_4_3_structured]

end RoundTrip.V13_52
