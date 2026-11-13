import Polyfold.Chapter14.P3W5FM_BoundaryPull

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §14.1, Proposition 14.1.8,
p. 645 (2017: Proposition 14.1): the **push-forward step** of its proof ("employing an argument as
in the proof of Theorem 13.4.3") and the assembly for a representative `W ←Φ V →Ψ W'` of a
generalized strong bundle isomorphism.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `IsBoundaryWFunctor.eq_of_π_eq_fm`, `mem_boundary_of_π_eq_fm`, `pushMult_eq_bdry_fm`,
  `isBoundaryWFunctor_pushMult_fm`: `Φ_*Λ` is a functor over `∂X'` when `Λ` is one over `∂X`
  (the boundary form of Lemma 11.5.2; only values over `∂X` enter).
* `transportChart_mem_boundary_iff_fm`, `IsPushNbhd.Qinv_mem_bdry_fm`: FN's transport charts
  preserve the boundary (the degeneracy index is invariant under morphisms and `F`).
* `exists_isPushNbhd_bdry_fm`, `bdryPushGood`: the pushed good system for `∂X'` (Definition
  14.1.5), each `U'(y)` a good open neighbourhood (Proposition 14.1.1) inside FN's adapted one.
* `bdryPushStructure`, `bdryPushDecoration`, `bdryPushTau`: `I'_y = I_{x_y}`,
  `s'ᵢ(z) = μ'(ψ_u, Φ(sᵢ(u)))`, `τ'_{y,y'}(φ') = τ_{x_y,x_{y'}}(liftMor φ')` (FN's construction,
  with the boundary versions of its pointwise lemmas `pushSec_eq_fm`, `pushSec_compat_fm`).
* `isBoundaryStructurable_pushMult_hyp`, and the assembly `proposition_14_1_8_hyp` (`f̄_*Λ`) and
  `proposition_14_1_8_pullMult_hyp` (`f̄^*Λ'`) for a diagram with tame middle.

## The added hypotheses

As for the pull-back (`P3W5FM_BoundaryPull`): (1) of Definition 14.1.3 is chart-defined, and its
transport along a transport chart (`FacePush_hyp`) or a local strong bundle isomorphism
(`PullMap.FacePull_hyp`) is assumed.  Witness for `FacePush_hyp`:
`facePush_hyp_of_boundary_eq_empty`.  The middle strong bundle of the representative is assumed tame, as in the text's proof ("a strong
bundle over a tame ep-groupoid").
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

open scoped Classical

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle EpGroupoid PushChart

/-! ### Boundary functors and orbits -/

section Groupoid

variable {A : SEP.{u}}

/-- The degeneracy index is invariant under morphisms. -/
theorem mem_boundary_src_iff_fm (φ : A.Mor) :
    A.X.src φ ∈ A.X.PObj.boundary ↔ A.X.tgt φ ∈ A.X.PObj.boundary := by
  change 1 ≤ _ ↔ 1 ≤ _
  rw [← A.X.degIndex_src, A.X.degIndex_tgt]

/-- Isomorphic points of `W` lie over `∂X` together. -/
theorem mem_boundary_of_π_eq_fm {a b : A.W}
    (hab : A.E.toEpGroupoid.π a = A.E.toEpGroupoid.π b) (ha : A.P a ∈ A.X.PObj.boundary) :
    A.P b ∈ A.X.PObj.boundary := by
  obtain ⟨q, hs, ht⟩ := (GroupoidStr.π_eq_π_iff _).1 hab
  have hs' : (q : A.Mor × A.W).2 = a := hs
  have ht' : A.E.μ q = b := ht
  have hq : A.P (q : A.Mor × A.W).2 = A.X.src (q : A.Mor × A.W).1 := q.2
  have e : A.E.μ q = fibAct (q : A.Mor × A.W).1 (q : A.Mor × A.W).2 := (fibAct_of hq).symm
  rw [← ht', e, P_fibAct hq, ← mem_boundary_src_iff_fm, ← hq, hs']
  exact ha

/-- A functor over `∂X` takes equal values on isomorphic points over `∂X`. -/
theorem IsBoundaryWFunctor.eq_of_π_eq_fm {Λ : A.W → ℚ≥0} (h : IsBoundaryWFunctor A Λ)
    {a b : A.W} (hab : A.E.toEpGroupoid.π a = A.E.toEpGroupoid.π b)
    (ha : A.P a ∈ A.X.PObj.boundary) : Λ a = Λ b := by
  obtain ⟨q, hs, ht⟩ := (GroupoidStr.π_eq_π_iff _).1 hab
  have hs' : (q : A.Mor × A.W).2 = a := hs
  have ht' : A.E.μ q = b := ht
  have hq : A.P (q : A.Mor × A.W).2 = A.X.src (q : A.Mor × A.W).1 := q.2
  rw [← hs', ← ht']
  exact (h q (by rw [← hq, hs']; exact ha)).symm

end Groupoid

variable {A C : SEP.{u}} {F : C ⟶ A} (hF : SEP.equivalences F)

/-- **`Φ_*Λ(w') = Λ(w)` over the boundary**: for `Λ` a functor over `∂X`, `w` over `∂X` and
`Φ(w) ≅ w'`. -/
theorem pushMult_eq_bdry_fm {Λ : C.W → ℚ≥0} (hΛ : IsBoundaryWFunctor C Λ) {w : C.W} {w' : A.W}
    (hw : C.P w ∈ C.X.PObj.boundary)
    (h : A.E.toEpGroupoid.π ((SEP.Hom.Φ F).obj w) = A.E.toEpGroupoid.π w') :
    pushMult F hF Λ w' = Λ w := by
  have e : C.E.toEpGroupoid.π ((sbe hF).isEquivalence.exists_iso w').choose =
      C.E.toEpGroupoid.π w := by
    refine (sbe hF).isEquivalence.isHomeomorph_orbitMap.injective ?_
    rw [GroupoidFunctor.orbitMap_π, GroupoidFunctor.orbitMap_π, π_obj_choose hF w', h]
  exact (hΛ.eq_of_π_eq_fm e.symm hw).symm

/-- **`Φ_*Λ` is a functor over `∂X'`** (Lemma 11.5.2 over the boundary). -/
theorem isBoundaryWFunctor_pushMult_fm {Λ : C.W → ℚ≥0} (hΛ : IsBoundaryWFunctor C Λ) :
    IsBoundaryWFunctor A (pushMult F hF Λ) := by
  intro q' hq'
  set w := ((sbe hF).isEquivalence.exists_iso (q' : A.Mor × A.W).2).choose with hwdef
  have hw := π_obj_choose hF (q' : A.Mor × A.W).2
  have hP : A.P (q' : A.Mor × A.W).2 ∈ A.X.PObj.boundary := by
    rw [show A.P (q' : A.Mor × A.W).2 = A.X.src (q' : A.Mor × A.W).1 from q'.2]; exact hq'
  have hPw : C.P w ∈ C.X.PObj.boundary := by
    have h1 : A.P ((SEP.Hom.Φ F).obj w) ∈ A.X.PObj.boundary := mem_boundary_of_π_eq_fm hw.symm hP
    have hcov := (PullMap.ofEquivalence hF).covers w
    simp only [PullMap.ofEquivalence_Φ, PullMap.ofEquivalence_ϕ] at hcov
    rw [hcov] at h1
    exact ((PullMap.ofEquivalence hF).mem_boundary_iff _).1 h1
  exact pushMult_eq_bdry_fm hF hΛ hPw (hw.trans (A.E.toEpGroupoid.π_src_eq_π_tgt q'))

/-! ### Transport charts and the boundary -/

include hF in
/-- `y ∈ ∂X'` iff `x ∈ ∂X` for a transport chart `x ↦ y` (`ψ₀ : F(x) → y`). -/
theorem transportChart_mem_boundary_iff_fm {x : C.Obj} {y : A.Obj}
    (T : (SEP.Hom.ϕ F).TransportChart x y) :
    y ∈ A.X.PObj.boundary ↔ x ∈ C.X.PObj.boundary := by
  rw [← T.tgt_ψ₀, ← mem_boundary_src_iff_fm, T.src_ψ₀]
  exact (PullMap.ofEquivalence hF).mem_boundary_iff x

include hF in
/-- `Q(u) ∈ ∂X'` iff `u ∈ ∂X` on the chart domain. -/
theorem Q_mem_boundary_iff_fm {x : C.Obj} {y : A.Obj} (T : (SEP.Hom.ϕ F).TransportChart x y)
    {u : C.Obj} (hu : u ∈ T.W) : T.Q u ∈ A.X.PObj.boundary ↔ u ∈ C.X.PObj.boundary := by
  rw [← T.tgt_ψ u hu, ← mem_boundary_src_iff_fm, T.src_ψ u hu]
  exact (PullMap.ofEquivalence hF).mem_boundary_iff u

/-- **The added hypothesis** (see the module docstring): (1) of Definition 14.1.3 is carried by
the pushed sections `z ↦ μ'(ψ_u, Φ(s(u)))`, `u = Q⁻¹(z)`, from `U(x)` to `U'(y)`. -/
def FacePush_hyp (F : C ⟶ A) : Prop :=
  ∀ {x : C.Obj} {y : A.Obj} (T : (SEP.Hom.ϕ F).TransportChart x y) (N : C.X.NatNbhd x)
    (N' : A.X.NatNbhd y) (s : C.Obj → C.W), IsPushNbhd T N N' →
    IsFaceScPlusSectionOn C s N.bdry → IsFaceScPlusSectionOn A (pushSec T s) N'.bdry

/-- **Witness**: the hypothesis holds when `∂X' = ∅`. -/
theorem facePush_hyp_of_boundary_eq_empty (h : A.X.PObj.boundary = ∅) : FacePush_hyp F := by
  intro x y T N N' s _ _
  rw [NatNbhd.bdry_eq_inter, h, inter_empty]
  exact ⟨fun _ hx => hx.elim, fun _ _ _ _ _ _ _ hx => hx.1.elim⟩

namespace IsPushNbhd

variable {x : C.Obj} {y : A.Obj} {T : (SEP.Hom.ϕ F).TransportChart x y}
  {N : C.X.NatNbhd x} {N' : A.X.NatNbhd y} (h : IsPushNbhd T N N')
include hF h

theorem Qinv_mem_bdry_fm {z : A.Obj} (hz : z ∈ N'.bdry) : T.Qinv z ∈ N.bdry := by
  refine ⟨h.Qinv_mem hz.1, ?_⟩
  rw [← Q_mem_boundary_iff_fm hF T (h.Qinv_mem_W hz.1), h.Q_Qinv hz.1]
  exact hz.2

/-- FN's `P_obj` with the section property at the one point used. -/
theorem P_obj_fm {s : C.Obj → C.W} {z : A.Obj} (hz : z ∈ N'.U)
    (hs : C.P (s (T.Qinv z)) = T.Qinv z) :
    A.P ((SEP.Hom.Φ F).obj (s (T.Qinv z))) = A.X.src (T.ψ (T.Qinv z)) := by
  have e := (PullMap.ofEquivalence hF).covers (s (T.Qinv z))
  simp only [PullMap.ofEquivalence_Φ, PullMap.ofEquivalence_ϕ] at e
  rw [e, hs, h.src_ψ_Qinv hz]

/-- FN's `pushSec_eq` with the section property at the one point used. -/
theorem pushSec_eq_fm {s : C.Obj → C.W} {z : A.Obj} (hz : z ∈ N'.U)
    (hs : C.P (s (T.Qinv z)) = T.Qinv z) :
    pushSec T s z = fibAct (T.ψ (T.Qinv z)) ((SEP.Hom.Φ F).obj (s (T.Qinv z))) := by
  rw [pushSec, transportSection_of_mem (h.P_obj_fm hF hz hs), fibAct_of (h.P_obj_fm hF hz hs)]
  rfl

end IsPushNbhd

namespace PushChart

variable {x x' : C.Obj} {y y' : A.Obj}
  {T : (SEP.Hom.ϕ F).TransportChart x y} {T' : (SEP.Hom.ϕ F).TransportChart x' y'}
  {N : C.X.NatNbhd x} {N' : A.X.NatNbhd y} {N₁ : C.X.NatNbhd x'} {N₁' : A.X.NatNbhd y'}

include hF in
/-- FN's `pushSec_compat` with the section properties at the points used. -/
theorem pushSec_compat_fm (h : IsPushNbhd T N N') (h' : IsPushNbhd T' N₁ N₁')
    {s s' : C.Obj → C.W} {ψ' : A.Mor} (hψ : ψ' ∈ A.X.morBetween N'.U N₁'.U)
    (hs : C.P (s (T.Qinv (A.X.src ψ'))) = T.Qinv (A.X.src ψ'))
    (hs' : C.P (s' (T'.Qinv (A.X.tgt ψ'))) = T'.Qinv (A.X.tgt ψ'))
    (hc : s' (C.X.tgt (liftMor T T' ψ')) =
      fibAct (liftMor T T' ψ') (s (C.X.src (liftMor T T' ψ')))) :
    pushSec T' s' (A.X.tgt ψ') = fibAct ψ' (pushSec T s (A.X.src ψ')) := by
  have hD := morBetween_subset_Dom h h' hψ
  have hsL := src_liftMor hF hD
  have htL := tgt_liftMor hF hD
  have huW : C.X.src (liftMor T T' ψ') ∈ T.W := by
    rw [hsL]; exact T.isScDiffeoOn_Q.mapsTo_inv hD.1
  have hu'W : C.X.tgt (liftMor T T' ψ') ∈ T'.W := by
    rw [htL]; exact T'.isScDiffeoOn_Q.mapsTo_inv hD.2
  rw [h'.pushSec_eq_fm hF hψ.2 hs', h.pushSec_eq_fm hF hψ.1 hs, ← htL, ← hsL, hc]
  have hP : C.P (s (C.X.src (liftMor T T' ψ'))) = C.X.src (liftMor T T' ψ') := by
    rw [hsL]; exact hs
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

include hF in
/-- The lift maps morphisms between the boundary neighbourhoods to such morphisms. -/
theorem liftMor_mem_bdry_fm (h : IsPushNbhd T N N') (h' : IsPushNbhd T' N₁ N₁') {φ' : A.Mor}
    (hφ : φ' ∈ A.X.morBetween N'.bdry N₁'.bdry) :
    liftMor T T' φ' ∈ C.X.morBetween N.bdry N₁.bdry := by
  have hD := morBetween_subset_Dom h h' ⟨hφ.1.1, hφ.2.1⟩
  exact ⟨by rw [src_liftMor hF hD]; exact h.Qinv_mem_bdry_fm hF hφ.1,
    by rw [tgt_liftMor hF hD]; exact h'.Qinv_mem_bdry_fm hF hφ.2⟩

include hF in
/-- FN's `isDiffeoComponent_push` for any neighbourhoods `N`, `N₁` whose morphism set has the
property (condition (2) of Definition 14.1.5 is carried forward). -/
theorem isDiffeoComponent_push_fm (h : IsPushNbhd T N N') (h' : IsPushNbhd T' N₁ N₁')
    (hd : ∀ φ ∈ C.X.morBetween N.U N₁.U,
      C.X.IsDiffeoComponent (connectedComponentIn (C.X.morBetween N.U N₁.U) φ))
    {φ' : A.Mor} (hφ : φ' ∈ A.X.morBetween N'.U N₁'.U) :
    A.X.IsDiffeoComponent (connectedComponentIn (A.X.morBetween N'.U N₁'.U) φ') := by
  have hsubD := morBetween_subset_Dom h h'
  have hmaps : MapsTo (liftMor T T') (connectedComponentIn (A.X.morBetween N'.U N₁'.U) φ')
      (connectedComponentIn (C.X.morBetween N.U N₁.U) (liftMor T T' φ')) :=
    mapsTo_connectedComponentIn ((continuousOn_liftMor hF).mono hsubD)
      (fun _ hψ => liftMor_mem hF h h' hψ) hφ
  have hL : liftMor T T' φ' ∈ C.X.morBetween N.U N₁.U := liftMor_mem hF h h' hφ
  have hsub : ∀ {ψ}, ψ ∈ connectedComponentIn (A.X.morBetween N'.U N₁'.U) φ' → ψ ∈ Dom T T' :=
    fun hψ => hsubD (connectedComponentIn_subset _ _ hψ)
  refine (isDiffeoComponent_iff_injOn (isOpen_connectedComponentIn_mor A.X
    (isOpen_morBetween N'.isOpen_U N₁'.isOpen_U) φ')).2
    ⟨fun ψ₁ hψ₁ ψ₂ hψ₂ e => ?_, fun ψ₁ hψ₁ ψ₂ hψ₂ e => ?_⟩
  · refine injOn_liftMor hF (hsub hψ₁) (hsub hψ₂)
      ((hd _ hL).injOn_src (hmaps hψ₁) (hmaps hψ₂) ?_)
    rw [src_liftMor hF (hsub hψ₁), src_liftMor hF (hsub hψ₂), e]
  · refine injOn_liftMor hF (hsub hψ₁) (hsub hψ₂)
      ((hd _ hL).injOn_tgt (hmaps hψ₁) (hmaps hψ₂) ?_)
    rw [tgt_liftMor hF (hsub hψ₁), tgt_liftMor hF (hsub hψ₂), e]

end PushChart

/-! ### The pushed good system for `∂X'` -/

/-- **Adapted good neighbourhoods in `∂X'`** (`X'` tame): FN's adapted neighbourhood, then a good
open neighbourhood inside it with the same action (Proposition 14.1.1). -/
theorem exists_isPushNbhd_bdry_fm (hA : A.X.IsTame) {x : C.Obj} {y : A.Obj}
    (T : (SEP.Hom.ϕ F).TransportChart x y) (N : C.X.NatNbhd x) (hy : y ∈ A.X.PObj.boundary) :
    ∃ N' : A.X.NatNbhd y, IsPushNbhd T N N' ∧ A.X.IsGoodBoundaryNbhd N' := by
  obtain ⟨N₀, h₀, hprop⟩ := exists_isPushNbhd T N
  obtain ⟨V, hrep, hsub, hV⟩ :=
    exists_isGoodBoundaryNbhd_le hA hy N₀ hprop isOpen_univ (mem_univ _)
  refine ⟨V, ⟨fun z hz => h₀.subset_W' (hsub hz).1, fun hz => h₀.Qinv_mem (hsub hz).1,
    fun z hz => h₀.Φ_mem_W z (hsub hz).1, fun g z hz => ?_⟩, hV⟩
  rw [hrep]; exact h₀.Γ_eq g z (hsub hz).1

/-- The point `x_y ∈ ∂X` of the chosen chart at `y ∈ ∂X'`. -/
def bdryX (y : A.X.PObj.boundary) : C.X.PObj.boundary :=
  ⟨(pushChart hF y).x, (transportChart_mem_boundary_iff_fm hF (pushChart hF y).T).1 y.2⟩

/-- The neighbourhood `U'(y)`, `y ∈ ∂X'`. -/
def bdryPushNbhd (hA : A.X.IsTame) (𝒰 : C.X.BoundaryGoodSystem) (y : A.X.PObj.boundary) :
    A.X.NatNbhd y :=
  (exists_isPushNbhd_bdry_fm hA (pushChart hF y).T (𝒰.nbhd (bdryX hF y)) y.2).choose

theorem isPush_bdryPushNbhd (hA : A.X.IsTame) (𝒰 : C.X.BoundaryGoodSystem)
    (y : A.X.PObj.boundary) :
    IsPushNbhd (pushChart hF y).T (𝒰.nbhd (bdryX hF y)) (bdryPushNbhd hF hA 𝒰 y) :=
  (exists_isPushNbhd_bdry_fm hA (pushChart hF y).T (𝒰.nbhd (bdryX hF y)) y.2).choose_spec.1

/-- **The pushed good system for `∂X'`.** -/
def bdryPushGood (hA : A.X.IsTame) (𝒰 : C.X.BoundaryGoodSystem) : A.X.BoundaryGoodSystem where
  nbhd := bdryPushNbhd hF hA 𝒰
  isGood y :=
    (exists_isPushNbhd_bdry_fm hA (pushChart hF y).T (𝒰.nbhd (bdryX hF y)) y.2).choose_spec.2
  isDiffeoComponent _ _ _ hφ :=
    isDiffeoComponent_push_fm hF (isPush_bdryPushNbhd hF hA 𝒰 _) (isPush_bdryPushNbhd hF hA 𝒰 _)
      (𝒰.isDiffeoComponent _ _) hφ

/-! ### The pushed data over `∂X'` -/

/-- **The pushed symmetric structure near `y` in `∂X'`**: `I'_y = I_{x_y}`, `h(i) = conj⁻¹(h)(i)`,
`s'ᵢ(z) = μ'(ψ_u, Φ(sᵢ(u)))`. -/
def bdryPushStructure (hface : FacePush_hyp F) {x : C.Obj} {y : A.Obj}
    {T : (SEP.Hom.ϕ F).TransportChart x y} {N : C.X.NatNbhd x} {N' : A.X.NatNbhd y}
    (h : IsPushNbhd T N N') {Λ : C.W → ℚ≥0} (hΛ : IsBoundaryWFunctor C Λ)
    (S : BoundarySymmetricStructure C Λ N) :
    BoundarySymmetricStructure A (pushMult F hF Λ) N' where
  I := S.I
  fintype := S.fintype
  mulAction := MulAction.compHom S.I (conjEquiv hF T).symm.toMonoidHom
  s i := pushSec T (S.s i)
  isFaceScPlus i := hface T N N' (S.s i) h (S.isFaceScPlus i)
  equivariant k i z hz := by
    obtain ⟨g, rfl⟩ := (conjEquiv hF T).surjective k
    have hgi : (conjEquiv hF T).symm (conjEquiv hF T g) • i = g • i := by
      rw [MulEquiv.symm_apply_apply]
    change pushSec T (S.s ((conjEquiv hF T).symm (conjEquiv hF T g) • i)) _ = _
    rw [hgi, conjEquiv_apply]
    have hgz := N'.mapsTo_Φ_bdry (T.conj g) hz
    have hu := h.Qinv_mem_bdry_fm hF hz
    have hgu := h.Qinv_mem_bdry_fm hF hgz
    rw [h.pushSec_eq_fm hF hgz.1 (S.P_s (g • i) hgu), h.pushSec_eq_fm hF hz.1 (S.P_s i hu),
      h.Qinv_Φ g hz.1, S.equivariant g i _ hu]
    have hsrc : C.P (S.s i (T.Qinv z)) = C.X.src (N.rep.Γ g (T.Qinv z)) := by
      rw [S.P_s i hu, N.src_Γ g hu.1]
    have e1 := (PullMap.ofEquivalence hF).obj_fibAct hsrc
    simp only [PullMap.ofEquivalence_Φ, PullMap.ofEquivalence_ϕ] at e1
    have hv := h.P_obj_fm hF hz.1 (S.P_s i hu)
    have hv1 : A.P ((SEP.Hom.Φ F).obj (S.s i (T.Qinv z))) =
        A.X.src ((SEP.Hom.ϕ F).mor (N.rep.Γ g (T.Qinv z))) := by
      rw [hv, h.src_ψ_Qinv hz.1, (SEP.Hom.ϕ F).src_mor, N.src_Γ g hu.1]
    rw [e1, ← PushChart.fibAct_comp hv1
        (TransportChartLemmas.src_ψ_eq_tgt T N hu.1 (h.Φ_mem_W z hz.1 g)), ← h.Γ_comp_ψ g hz.1,
      PushChart.fibAct_comp hv (by rw [N'.src_Γ _ hz.1, h.tgt_ψ_Qinv hz.1])]
  rep w' hw' := by
    set z := A.P w' with hzdef
    have hu := h.Qinv_mem_bdry_fm hF hw'
    set u := T.Qinv z with hudef
    have hw'1 : A.P w' = A.X.src (A.X.inv (T.ψ u)) := by
      rw [A.X.src_inv]; exact (h.tgt_ψ_Qinv hw'.1).symm
    set m := fibAct (A.X.inv (T.ψ u)) w' with hmdef
    have hm : A.P m = (SEP.Hom.ϕ F).obj u := by
      rw [hmdef, P_fibAct hw'1, A.X.tgt_inv]; exact h.src_ψ_Qinv hw'.1
    set M := PullMap.ofEquivalence hF
    set v : C.W := ((M.fiberEquiv u).symm ⟨m, hm⟩).1 with hvdef
    have hΦv : (SEP.Hom.Φ F).obj v = m := by
      change M.Φ v = m
      rw [hvdef, ← PullMap.fiberEquiv_apply, ContinuousLinearEquiv.apply_symm_apply]
    have hPv : C.P v = u := ((M.fiberEquiv u).symm ⟨m, hm⟩).2
    have hπ : A.E.toEpGroupoid.π ((SEP.Hom.Φ F).obj v) = A.E.toEpGroupoid.π w' := by
      rw [hΦv, hmdef, PushChart.π_fibAct hw'1]
    rw [pushMult_eq_bdry_fm hF hΛ (by rw [hPv]; exact hu.2) hπ,
      S.rep v (by rw [hPv]; exact hu), hPv]
    have e : (Finset.univ.filter fun i => S.s i u = v) =
        Finset.univ.filter fun i => pushSec T (S.s i) z = w' := by
      refine Finset.filter_congr fun i _ => ?_
      rw [h.pushSec_eq_fm hF hw'.1 (S.P_s i hu)]
      have hPs : A.P ((SEP.Hom.Φ F).obj (S.s i u)) = A.X.src (T.ψ u) :=
        h.P_obj_fm hF hw'.1 (S.P_s i hu)
      constructor
      · intro e
        rw [e, hΦv, hmdef, PushChart.fibAct_fibAct_inv (h.tgt_ψ_Qinv hw'.1).symm]
      · intro e
        refine M.eq_of_obj_eq ((S.P_s i hu).trans hPv.symm) ?_
        change (SEP.Hom.Φ F).obj (S.s i u) = (SEP.Hom.Φ F).obj v
        rw [hΦv, hmdef, ← e, PushChart.fibAct_inv_fibAct hPs]
    rw [e]

/-- **The pushed decoration** over `∂X'`. -/
def bdryPushDecoration (hA : A.X.IsTame) (hface : FacePush_hyp F) {Λ : C.W → ℚ≥0}
    (hΛ : IsBoundaryWFunctor C Λ) (D : BoundaryDecoration C Λ) :
    BoundaryDecoration A (pushMult F hF Λ) :=
  ⟨bdryPushGood hF hA D.𝒰, fun y =>
    bdryPushStructure hF hface (isPush_bdryPushNbhd hF hA D.𝒰 y) hΛ (D.S (bdryX hF y))⟩

/-- **The pushed correspondences** `τ'_{y,y'}(φ') = τ_{x_y,x_{y'}}(liftMor φ')` over `∂X'`. -/
def bdryPushTau (hA : A.X.IsTame) (hface : FacePush_hyp F) {Λ : C.W → ℚ≥0}
    (hΛ : IsBoundaryWFunctor C Λ) {D : BoundaryDecoration C Λ} (t : D.Tau) :
    (bdryPushDecoration hF hA hface hΛ D).Tau where
  τ y y' φ' := t.τ (bdryX hF y) (bdryX hF y') (liftMor (pushChart hF y).T (pushChart hF y').T φ')
  locallyConstant y y' φ' hφ' := by
    have h := isPush_bdryPushNbhd hF hA D.𝒰 y
    have h' := isPush_bdryPushNbhd hF hA D.𝒰 y'
    have hcont : ContinuousAt (liftMor (pushChart hF y).T (pushChart hF y').T) φ' :=
      (continuousOn_liftMor hF).continuousAt ((isOpen_Dom _ _).mem_nhds
        (morBetween_subset_Dom h h' ⟨hφ'.1.1, hφ'.2.1⟩))
    have ht : Tendsto (liftMor (pushChart hF y).T (pushChart hF y').T)
        (𝓝[(bdryPushGood hF hA D.𝒰).mor y y'] φ')
        (𝓝[D.𝒰.mor (bdryX hF y) (bdryX hF y')]
          (liftMor (pushChart hF y).T (pushChart hF y').T φ')) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (hcont.tendsto.mono_left nhdsWithin_le_nhds)
        (eventually_nhdsWithin_of_forall fun ψ hψ => liftMor_mem_bdry_fm hF h h' hψ)
    exact ht.eventually (t.locallyConstant _ _ _ (liftMor_mem_bdry_fm hF h h' hφ'))
  finite y y' := by
    have h := isPush_bdryPushNbhd hF hA D.𝒰 y
    have h' := isPush_bdryPushNbhd hF hA D.𝒰 y'
    refine (t.finite _ _).subset ?_
    rintro _ ⟨φ', hφ', rfl⟩
    exact ⟨_, liftMor_mem_bdry_fm hF h h' hφ', rfl⟩
  swap y y' φ' hφ' := by
    have h := isPush_bdryPushNbhd hF hA D.𝒰 y
    have h' := isPush_bdryPushNbhd hF hA D.𝒰 y'
    have hD := morBetween_subset_Dom h h' ⟨hφ'.1.1, hφ'.2.1⟩
    change t.τ _ _ (liftMor _ _ (A.X.inv φ')) = (t.τ _ _ (liftMor _ _ φ')).swap
    rw [liftMor_inv hF _ _ hD]
    exact t.swap _ _ _ (liftMor_mem_bdry_fm hF h h' hφ')
  diag y g z hz := by
    have h := isPush_bdryPushNbhd hF hA D.𝒰 y
    obtain ⟨k, rfl⟩ := (conjEquiv hF (pushChart hF y).T).surjective g
    change t.τ _ _ (liftMor _ _ ((bdryPushNbhd hF hA D.𝒰 y).rep.Γ
      ((pushChart hF y).T.conj k) z)) = _
    rw [liftMor_Γ hF h k hz.1]
    have hd := t.diag (bdryX hF y) k _ (h.Qinv_mem_bdry_fm hF hz)
    have e := PullMap.ofPerm_compHom (α := (D.S (bdryX hF y)).I)
      (H := C.X.Isotropy (bdryX hF y : C.Obj))
      (conjEquiv hF (pushChart hF y).T).symm.toMonoidHom (conjEquiv hF (pushChart hF y).T k)
    have h1 : (conjEquiv hF (pushChart hF y).T).symm.toMonoidHom
        (conjEquiv hF (pushChart hF y).T k) = k := MulEquiv.symm_apply_apply _ k
    exact hd.trans (e.trans (congrArg (fun g : C.X.Isotropy (bdryX hF y : C.Obj) =>
      IndexCorr.ofPerm (α := (D.S (bdryX hF y)).I) g) h1)).symm
  biact y y' φ' hφ' g' g := by
    have h := isPush_bdryPushNbhd hF hA D.𝒰 y
    have h' := isPush_bdryPushNbhd hF hA D.𝒰 y'
    obtain ⟨k, rfl⟩ := (conjEquiv hF (pushChart hF y).T).surjective g
    obtain ⟨k', rfl⟩ := (conjEquiv hF (pushChart hF y').T).surjective g'
    change t.τ _ _ (liftMor _ _ (EpGroupoid.biact (bdryPushNbhd hF hA D.𝒰 y)
      (bdryPushNbhd hF hA D.𝒰 y') ((pushChart hF y').T.conj k') φ'
      ((pushChart hF y).T.conj k))) = _
    rw [liftMor_biact hF h h' ⟨hφ'.1.1, hφ'.2.1⟩ k' k]
    have hb := t.biact _ _ _ (liftMor_mem_bdry_fm hF h h' hφ') k' k
    have e := PullMap.biact_compHom (H := C.X.Isotropy (bdryX hF y : C.Obj))
      (H' := C.X.Isotropy (bdryX hF y' : C.Obj)) (conjEquiv hF (pushChart hF y).T).symm.toMonoidHom
      (conjEquiv hF (pushChart hF y').T).symm.toMonoidHom
      (conjEquiv hF (pushChart hF y').T k')
      (t.τ (bdryX hF y) (bdryX hF y') (liftMor (pushChart hF y).T (pushChart hF y').T φ'))
      (conjEquiv hF (pushChart hF y).T k)
    have h1 : (conjEquiv hF (pushChart hF y).T).symm.toMonoidHom
        (conjEquiv hF (pushChart hF y).T k) = k := MulEquiv.symm_apply_apply _ k
    have h2 : (conjEquiv hF (pushChart hF y').T).symm.toMonoidHom
        (conjEquiv hF (pushChart hF y').T k') = k' := MulEquiv.symm_apply_apply _ k'
    exact hb.trans (e.trans (congrArg₂ (fun (a : C.X.Isotropy (bdryX hF y' : C.Obj))
      (b : C.X.Isotropy (bdryX hF y : C.Obj)) => IndexCorr.biact a
        (t.τ (bdryX hF y) (bdryX hF y') (liftMor (pushChart hF y).T (pushChart hF y').T φ')) b)
      h2 h1)).symm
  compat y y' φ' hφ' := by
    have h := isPush_bdryPushNbhd hF hA D.𝒰 y
    have h' := isPush_bdryPushNbhd hF hA D.𝒰 y'
    exact IndexCorr.sat_mono (fun i j H => pushSec_compat_fm hF h h' ⟨hφ'.1.1, hφ'.2.1⟩
      ((D.S _).P_s i (h.Qinv_mem_bdry_fm hF hφ'.1))
      ((D.S _).P_s j (h'.Qinv_mem_bdry_fm hF hφ'.2)) H)
      (t.compat _ _ _ (liftMor_mem_bdry_fm hF h h' hφ'))

/-- **Push-forwards of structurable sc⁺-multisections over `∂X` are structurable over `∂X'`**
(the second step of the proof of Proposition 14.1.8), for tame `X'`, under `FacePush_hyp`. -/
theorem isBoundaryStructurable_pushMult_hyp (hA : A.X.IsTame) (hface : FacePush_hyp F)
    {Λ : C.W → ℚ≥0} (h : IsBoundaryStructurable C Λ) :
    IsBoundaryStructurable A (pushMult F hF Λ) := by
  obtain ⟨hΛ, D, ⟨t⟩⟩ := h
  exact ⟨(bdryPushDecoration hF hA hface hΛ.1 D).isBoundaryScPlusMultisection_fm
    (isBoundaryWFunctor_pushMult_fm hF hΛ.1), bdryPushDecoration hF hA hface hΛ.1 D,
    ⟨bdryPushTau hF hA hface hΛ.1 t⟩⟩

/-! ### Proposition 14.1.8 -/

/-- **2021 Proposition 14.1.8, p. 645 (2017: Proposition 14.1), `f̄_*Λ`**: for a representative
`W ←Φ V →Ψ W'` (`D`) of a generalized strong bundle isomorphism with `V` over a tame ep-groupoid
and `X'` tame, and `Λ` structurable over `∂X`, `f̄_*Λ = Ψ_*Φ^*Λ` is structurable over `∂X'`;
with the added hypotheses `FacePull_hyp` (for `Φ`) and `FacePush_hyp` (for `Ψ`). -/
theorem proposition_14_1_8_hyp {A A' : SEP.{u}} (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ)
    (hB : D.B.X.IsTame) (hA' : A'.X.IsTame)
    (hpull : (PullMap.ofEquivalence D.isEquivalence_Φ).FacePull_hyp) (hpush : FacePush_hyp D.Ψ)
    {Λ : A.W → ℚ≥0} (h : IsBoundaryStructurable A Λ) :
    IsBoundaryStructurable A' (D.pushMult hΨ Λ) :=
  isBoundaryStructurable_pushMult_hyp hΨ hA' hpush
    ((PullMap.ofEquivalence D.isEquivalence_Φ).isBoundaryStructurable_pull_hyp hB hpull h)

/-- **Proposition 14.1.8, `f̄^*Λ'`**: `f̄^*Λ' = Φ_*Ψ^*Λ'` is structurable over `∂X` for `Λ'`
structurable over `∂X'` (`X` and the middle tame; `FacePull_hyp` for `Ψ`, `FacePush_hyp` for
`Φ`). -/
theorem proposition_14_1_8_pullMult_hyp {A A' : SEP.{u}} (D : SDiagram A A')
    (hΨ : SEP.equivalences D.Ψ) (hB : D.B.X.IsTame) (hA : A.X.IsTame)
    (hpull : (PullMap.ofEquivalence hΨ).FacePull_hyp) (hpush : FacePush_hyp D.Φ)
    {Λ' : A'.W → ℚ≥0} (h : IsBoundaryStructurable A' Λ') :
    IsBoundaryStructurable A (D.pullMult hΨ Λ') :=
  proposition_14_1_8_hyp (D.symm hΨ) D.isEquivalence_Φ hB hA hpull hpush h

end SBLocalization

end Polyfold
