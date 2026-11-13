import Polyfold.Chapter13.P3W4FN_Pullback
import Polyfold.Chapter14.P3W3B1_BoundaryStructured
import Polyfold.Chapter13.P3W5FM_ExtensionData

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §14.1, Proposition 14.1.8,
p. 645 (2017: Proposition 14.1): the **pull-back step** of its proof ("an argument similar to
that used in the proof of Theorem 13.4.1"): structurable sc⁺-multisections over `∂X'` pull back
along strong bundle equivalences (and, more generally, along FN's `PullMap`s) to structurable
sc⁺-multisections over `∂X`.

## The text, paraphrased

(p. 646) For a representative `W ←Φ V →Ψ W'` of a generalized strong bundle isomorphism, with `V`
over a tame ep-groupoid, `Φ^*Λ` is structurable over the boundary by the argument of Theorem
13.4.1; then `Ψ_*Φ^*Λ` is structurable by the argument of Theorem 13.4.3.

## What is formalized (namespace `Polyfold.SBLocalization.PullMap`)

* `degIndex_obj`, `mem_boundary_iff`: `F` preserves the degeneracy index, so `F(∂X) ⊆ ∂X'` and
  `F⁻¹(∂X') = ∂X` (`F` is a local sc-diffeomorphism, Proposition 2.4.4).
* `BdryPullData`, `exists_bdryPullData`: a good system for `∂X` (Definition 14.1.5) adapted to a
  given good system for `∂X'`; each `V(x)` is a good open neighbourhood (Proposition 14.1.1,
  B1's `exists_isGoodBoundaryNbhd_le`) inside FN's adapted neighbourhood, with the same action.
* `bdryPullStructure`, `bdryPullDecoration`, `bdryPullTau`, `bdryPullTuple`: the pulled-back
  data `I_x = I'_{F(x)}`, `Φ(sˣᵢ(z)) = s'^{F(x)}ᵢ(F(z))`, `τ_{x,y}(φ) = τ'_{F(x),F(y)}(F(φ))`
  (Definitions 14.1.3, 14.1.7).
* `isBoundaryStructurable_pull_hyp` and, for equivalences, `proposition_14_1_8_pull_hyp`.

## The added hypothesis

Condition (1) of Definition 14.1.3 is read in the charts (B1's `IsFaceScPlusSectionOn`: in every
tame strong bundle chart and every tame presentation of its corner).  That the pull-back of a
section with this property along a local strong bundle isomorphism has it again is the
hypothesis `FacePull_hyp` (it needs that a tame strong bundle chart composed with a local strong
bundle isomorphism is again a tame strong bundle chart, which the project does not have).
Witnesses: `facePull_hyp_id` (the identity of every `A`) and
`facePull_hyp_of_boundary_eq_empty`.  The helper `IsFaceScPlusSectionOn.congr_fm` (only the
values on `∂X` near `U` enter) is proved on the way.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

open scoped Classical

noncomputable section

namespace Polyfold

universe u

open TameBoundary

/-! ### `IsScPlusOnFaceNear` only depends on the section near the point -/

section Local

variable {E F W : ScBanach} {n : ℕ}

/-- If `s = s'` on `O ∩ N ∩ {tᵢ = 0}` for an open `N ∋ x`, `IsScPlusOnFaceNear` passes from `s` to
`s'` (shrink the neighbourhood, Proposition 2.3.1 (1)). -/
theorem IsScPlusOnFaceNear.congr_open_fm {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)}
    {C O : Set (E 0)} {K : Set (E 0 × F 0)} {s s' : E 0 → E 0 × F 1} {x : E 0} {i : Fin n}
    (h : IsScPlusOnFaceNear T C O K s x i) {N : Set (E 0)} (hN : IsOpen N) (hxN : x ∈ N)
    (hss' : EqOn s s' (O ∩ N ∩ coordHyper T i)) : IsScPlusOnFaceNear T C O K s' x i := by
  obtain ⟨V, hV, hxV, hret, hsec⟩ := h
  have hset : O ∩ (V ∩ N) ∩ coordHyper T i = (O ∩ V ∩ coordHyper T i) ∩ N := by
    ext z; simp only [mem_inter_iff]; tauto
  refine ⟨V ∩ N, hV.inter hN, ⟨hxV, hxN⟩, ?_, ?_⟩
  · rw [hset]; exact proposition_2_3_1_one hret hN
  · rw [hset]
    refine ⟨fun z hz => ?_, ?_⟩
    · rw [← hss' ⟨⟨hz.1.1.1, hz.2⟩, hz.1.2⟩]; exact hsec.fst_eq z hz.1
    · exact (hsec.isScSmooth.restrict hret).congr fun z hz =>
        hss' ⟨⟨hz.1.1.1, hz.2⟩, hz.1.2⟩

end Local

namespace SBLocalization

open StrongBundle EpGroupoid

/-! ### Local faces of tame charts lie in `∂X`; congruence of face-sc⁺ -/

section Congr

variable {A : SEP.{u}}

/-- **A point of a local face `{tᵢ = 0}` of a tame chart lies in `∂X`**: `d_X = d_C` on a tame
chart (Proposition 2.5.6) and `d_C ≥ 1` on `{tᵢ = 0}`. -/
theorem symm_mem_boundary_fm (c : StrongBundleChart A.X.PObj A.P) (hc : A.B.IsTameChart c)
    {n : ℕ} {W : ScBanach} {T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)}
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant n W 0) {z : c.φ.model.E 0} (hz : z ∈ c.φ.model.O)
    {i : Fin n} (hi : (T 0 z).1 i = 0) : c.φ.symm z ∈ A.X.PObj.boundary := by
  have hRO := c.base_retract
  have hR := hc.isTame n W T hT
  have hzs : c.φ.symm z ∈ c.φ.source := c.φ.symm_mapsTo hz
  have hzC : z ∈ c.φ.model.C :=
    (hRO ▸ hz : z ∈ (c.isRetraction.baseRetraction c.relOpen).retract) |>
      (c.isRetraction.baseRetraction c.relOpen).retract_subset_C
  change 1 ≤ A.X.PObj.degIndex _
  rw [MPolyfold.degIndex_eq_chartDegIndex_of_isTameWith A.X.PObj c.isChart _ hRO hT hR hzs,
    MPolyfold.chartDegIndex]
  have e : c.φ (c.φ.symm z) = z := c.φ.toPartialEquiv.right_inv (c.φ.target_eq ▸ hz)
  rw [e, degIndex_eq T hT hzC, degIndexWith_eq_card_zeroSet]
  exact Finset.card_pos.2 ⟨i, (mem_zeroSet T).2 hi⟩

/-- **(1) of Definition 14.1.3 only depends on the values on `∂X` near `U`**: if `s = s'` on
`O ∩ ∂X` for an open `O ⊇ U`, `U ⊆ ∂X`, then `s` and `s'` satisfy it on `U` together. -/
theorem IsFaceScPlusSectionOn.congr_fm {s s' : A.Obj → A.W} {U O : Set A.Obj}
    (h : IsFaceScPlusSectionOn A s U) (hO : IsOpen O) (hUO : U ⊆ O)
    (hU : U ⊆ A.X.PObj.boundary) (hss' : EqOn s s' (O ∩ A.X.PObj.boundary)) :
    IsFaceScPlusSectionOn A s' U := by
  refine ⟨fun x hx => by rw [← hss' ⟨hUO hx, hU hx⟩]; exact h.1 x hx,
    fun c hc n W T hT x hx i hi => ?_⟩
  have hface := h.2 c hc n W T hT x hx i hi
  obtain ⟨N', hN', hN'eq⟩ := continuousOn_iff'.1 c.φ.continuousOn_invFun O hO
  have hxN' : c.φ x ∈ N' := by
    have : c.φ x ∈ c.φ.symm ⁻¹' O ∩ c.φ.model.O :=
      ⟨by rw [mem_preimage, c.φ.symm_apply_apply hx.2]; exact hUO hx.1,
        c.φ.mapsTo_model x hx.2⟩
    rw [hN'eq] at this; exact this.1
  refine hface.congr_open_fm hN' hxN' fun z hz => ?_
  have hz1 : c.φ.symm z ∈ O := by
    have : z ∈ N' ∩ c.φ.model.O := ⟨hz.1.2, hz.1.1⟩
    rw [← hN'eq] at this; exact this.1
  have hz2 := symm_mem_boundary_fm c hc hT hz.1.1 hz.2
  simp only [localRepOne, hss' ⟨hz1, hz2⟩]

end Congr

variable {A C : SEP.{u}} (M : PullMap C A)

namespace PullMap

/-! ### `F` preserves the boundary -/

/-- `d_{X'}(F(y)) = d_X(y)`: `F` is a local sc-diffeomorphism (Proposition 2.4.4). -/
theorem degIndex_obj (y : C.Obj) : A.X.PObj.degIndex (M.ϕ.obj y) = C.X.PObj.degIndex y := by
  obtain ⟨W, hy, h⟩ := M.isLocalScDiffeo_obj.isDLocalHomeo y
  exact h.deg_eq y hy

theorem mem_boundary_iff (y : C.Obj) :
    M.ϕ.obj y ∈ A.X.PObj.boundary ↔ y ∈ C.X.PObj.boundary := by
  change 1 ≤ _ ↔ 1 ≤ _
  rw [M.degIndex_obj]

/-- `F` as a map `∂X → ∂X'`. -/
def bdryObj (x : C.X.PObj.boundary) : A.X.PObj.boundary :=
  ⟨M.ϕ.obj x, (M.mem_boundary_iff x).2 x.2⟩

@[simp] theorem coe_bdryObj (x : C.X.PObj.boundary) : (M.bdryObj x : A.Obj) = M.ϕ.obj x := rfl

/-- `Φ^*Λ'` is a functor over `∂X`. -/
theorem isBoundaryWFunctor_pull {Λ' : A.W → ℚ≥0} (h : IsBoundaryWFunctor A Λ') :
    IsBoundaryWFunctor C (M.pull Λ') := by
  rintro ⟨⟨γ, w⟩, hq⟩ hγ
  change Λ' (M.Φ (C.E.μ ⟨(γ, w), hq⟩)) = Λ' (M.Φ w)
  rw [M.isMap.map_μ γ w hq]
  exact h _ (by rw [M.ϕ.src_mor]; exact (M.mem_boundary_iff _).2 hγ)

/-! ### The added hypothesis: face-sc⁺ sections pull back -/

/-- **Added hypothesis** (see the module docstring): (1) of Definition 14.1.3 pulls back along
`Φ`: if `s'` has it on `O' ∩ ∂X'` (`O'` open) and `F(O) ⊆ O'` (`O` open), then the pulled-back
section `Φ_z⁻¹ s'(F(z))` has it on `O ∩ ∂X`. -/
def FacePull_hyp : Prop :=
  ∀ (s' : A.Obj → A.W) (O : Set C.Obj) (O' : Set A.Obj), IsOpen O → IsOpen O' →
    MapsTo M.ϕ.obj O O' → IsFaceScPlusSectionOn A s' (O' ∩ A.X.PObj.boundary) →
    IsFaceScPlusSectionOn C (M.pullSec s') (O ∩ C.X.PObj.boundary)

/-- **Witness**: the hypothesis holds when `∂X = ∅`. -/
theorem facePull_hyp_of_boundary_eq_empty (h : C.X.PObj.boundary = ∅) : M.FacePull_hyp := by
  intro s' O O' _ _ _ _
  rw [h, inter_empty]
  exact ⟨fun _ hx => hx.elim, fun _ _ _ _ _ _ _ hx => hx.1.elim⟩

/-- **Witness**: the hypothesis holds for the identity of every `A` (through
`IsFaceScPlusSectionOn.congr_fm`). -/
theorem facePull_hyp_id (A : SEP.{u}) :
    (PullMap.ofEquivalence (equivalences_id_sep A)).FacePull_hyp := by
  intro s' O O' hO hO' hOO' hs'
  have hmono : IsFaceScPlusSectionOn A s' (O ∩ A.X.PObj.boundary) :=
    hs'.mono fun z hz => ⟨hOO' hz.1, hz.2⟩
  refine hmono.congr_fm hO' (fun z hz => hOO' hz.1) inter_subset_right fun z hz => ?_
  have hP : A.P (s' z) = z := (hs'.1 z hz).1
  exact (((PullMap.ofEquivalence (equivalences_id_sep A)).pullSec_eq_iff hP hP).2 rfl).symm

/-! ### Adapted good systems for `∂X` -/

variable {M}

/-- `F(U(x)) ⊆ U'(F(x))` for the good neighbourhoods in the boundary. -/
theorem IsPullNbhd.mapsTo_bdry {x : C.Obj} {N : C.X.NatNbhd x} {N' : A.X.NatNbhd (M.ϕ.obj x)}
    (h : M.IsPullNbhd N N') : MapsTo M.ϕ.obj N.bdry N'.bdry := fun y hy =>
  ⟨h.mapsTo hy.1, (M.mem_boundary_iff y).2 hy.2⟩

variable (M)

/-- **Condition (2) of Definition 14.1.5 is carried back** (as in FN's
`isDiffeoComponent_of_isPull`, for any neighbourhoods `N'`, `N₁'` whose morphism set has the
property). -/
theorem isDiffeoComponent_of_isPull_fm {x x' : C.Obj} {N : C.X.NatNbhd x}
    {N₁ : C.X.NatNbhd x'} {N' : A.X.NatNbhd (M.ϕ.obj x)} {N₁' : A.X.NatNbhd (M.ϕ.obj x')}
    (h : M.IsPullNbhd N N') (h₁ : M.IsPullNbhd N₁ N₁')
    (hd : ∀ φ' ∈ A.X.morBetween N'.U N₁'.U,
      A.X.IsDiffeoComponent (connectedComponentIn (A.X.morBetween N'.U N₁'.U) φ'))
    {φ : C.Mor} (hφ : φ ∈ C.X.morBetween N.U N₁.U) :
    C.X.IsDiffeoComponent (connectedComponentIn (C.X.morBetween N.U N₁.U) φ) := by
  have hmaps := M.mapsTo_connectedComponentIn h.mapsTo h₁.mapsTo hφ
  have hφ' : M.ϕ.mor φ ∈ A.X.morBetween N'.U N₁'.U := M.mem_morBetween h.mapsTo h₁.mapsTo hφ
  have hsub : ∀ {ψ}, ψ ∈ connectedComponentIn (C.X.morBetween N.U N₁.U) φ →
      ψ ∈ C.X.morBetween N.U N₁.U := fun hψ => connectedComponentIn_subset _ _ hψ
  refine (isDiffeoComponent_iff_injOn (isOpen_connectedComponentIn_mor C.X
    (isOpen_morBetween N.isOpen_U N₁.isOpen_U) φ)).2
    ⟨fun ψ₁ hψ₁ ψ₂ hψ₂ e => ?_, fun ψ₁ hψ₁ ψ₂ hψ₂ e => ?_⟩
  · have e' : M.ϕ.mor ψ₁ = M.ϕ.mor ψ₂ := (hd _ hφ').injOn_src (hmaps hψ₁) (hmaps hψ₂)
      (by rw [M.ϕ.src_mor, M.ϕ.src_mor, e])
    have et : C.X.tgt ψ₁ = C.X.tgt ψ₂ := h₁.injOn (hsub hψ₁).2 (hsub hψ₂).2
      (by rw [← M.ϕ.tgt_mor, ← M.ϕ.tgt_mor, e'])
    exact M.mor_injective _ _ e et e'
  · have e' : M.ϕ.mor ψ₁ = M.ϕ.mor ψ₂ := (hd _ hφ').injOn_tgt (hmaps hψ₁) (hmaps hψ₂)
      (by rw [M.ϕ.tgt_mor, M.ϕ.tgt_mor, e])
    have es : C.X.src ψ₁ = C.X.src ψ₂ := h.injOn (hsub hψ₁).1 (hsub hψ₂).1
      (by rw [← M.ϕ.src_mor, ← M.ϕ.src_mor, e'])
    exact M.mor_injective _ _ es e e'

/-- **A good system for `∂X` adapted to a good system `𝒰'` for `∂X'`**. -/
structure BdryPullData (𝒰' : A.X.BoundaryGoodSystem) where
  /-- The good system `(V(x))_{x ∈ ∂X}`. -/
  𝒰 : C.X.BoundaryGoodSystem
  isPull : ∀ x, M.IsPullNbhd (𝒰.nbhd x) (𝒰'.nbhd (M.bdryObj x))

/-- **Adapted good systems for `∂X` exist** when `X` is tame: FN's adapted neighbourhood, then a
good open neighbourhood inside it with the same action (Proposition 14.1.1). -/
theorem exists_bdryPullData (hX : C.X.IsTame) (𝒰' : A.X.BoundaryGoodSystem) :
    Nonempty (M.BdryPullData 𝒰') := by
  have key : ∀ x : C.X.PObj.boundary, ∃ N : C.X.NatNbhd x,
      M.IsPullNbhd N (𝒰'.nbhd (M.bdryObj x)) ∧ C.X.IsGoodBoundaryNbhd N := by
    intro x
    obtain ⟨N, hN, hprop, -⟩ :=
      M.exists_isPullNbhd (𝒰'.nbhd (M.bdryObj x)) isOpen_univ (mem_univ _)
    obtain ⟨V, hrep, hsub, hV⟩ :=
      exists_isGoodBoundaryNbhd_le hX x.2 N hprop isOpen_univ (mem_univ _)
    refine ⟨V, ⟨hN.injOn.mono fun y hy => (hsub hy).1, fun y hy => hN.mapsTo (hsub hy).1,
      fun g y hy => ?_⟩, hV⟩
    rw [hrep]; exact hN.Γ_eq g y (hsub hy).1
  choose N hN hgood using key
  exact ⟨⟨⟨N, hgood, fun x x' φ hφ =>
    M.isDiffeoComponent_of_isPull_fm (hN x) (hN x') (𝒰'.isDiffeoComponent _ _) hφ⟩, hN⟩⟩

namespace BdryPullData

variable {M} {𝒰' : A.X.BoundaryGoodSystem} (P : M.BdryPullData 𝒰')

theorem mapsTo (x : C.X.PObj.boundary) : MapsTo M.ϕ.obj (P.𝒰.U x) (𝒰'.U (M.bdryObj x)) :=
  fun _ hy => (P.isPull x).mapsTo_bdry hy

theorem mor_mem {x y : C.X.PObj.boundary} {φ : C.Mor} (hφ : φ ∈ P.𝒰.mor x y) :
    M.ϕ.mor φ ∈ 𝒰'.mor (M.bdryObj x) (M.bdryObj y) :=
  M.mem_morBetween (P.mapsTo x) (P.mapsTo y) hφ

end BdryPullData

/-! ### The pulled-back data over `∂X` -/

variable {M}

/-- **The pulled-back symmetric structure near `x` in `∂X`**: `I_x = I'_{F(x)}` with
`g(i) = F(g)(i)` and `Φ(sᵢ(z)) = s'ᵢ(F(z))`. -/
def bdryPullStructure (hface : M.FacePull_hyp) {Λ' : A.W → ℚ≥0} {x : C.Obj}
    {N : C.X.NatNbhd x} {N' : A.X.NatNbhd (M.ϕ.obj x)} (hN : M.IsPullNbhd N N')
    (S' : BoundarySymmetricStructure A Λ' N') : BoundarySymmetricStructure C (M.pull Λ') N where
  I := S'.I
  fintype := S'.fintype
  mulAction := MulAction.compHom S'.I (M.ϕ.isotropyHom x)
  s i := M.pullSec (S'.s i)
  isFaceScPlus i :=
    hface _ N.U N'.U N.isOpen_U N'.isOpen_U hN.mapsTo (S'.isFaceScPlus i)
  equivariant g i y hy := by
    have hy' := hN.mapsTo_bdry hy
    have hgy := N.mapsTo_Φ_bdry g hy
    have hsrc : C.P (M.pullSec (S'.s i) y) = C.X.src (N.rep.Γ g y) := by
      rw [M.P_pullSec, N.src_Γ g hy.1]
    refine M.eq_of_obj_eq ?_ ?_
    · rw [M.P_pullSec, P_fibAct hsrc, N.tgt_Γ g hy.1]
    · rw [M.obj_pullSec (S'.P_s _ (hN.mapsTo_bdry hgy)), M.obj_fibAct hsrc,
        M.obj_pullSec (S'.P_s _ hy'), hN.Φ_eq g hy.1, hN.Γ_eq g y hy.1]
      exact S'.equivariant (M.ϕ.isotropyHom x g) i (M.ϕ.obj y) hy'
  rep w hw := by
    have hw' : A.P (M.Φ w) ∈ N'.bdry := by rw [M.covers]; exact hN.mapsTo_bdry hw
    rw [pull_apply, S'.rep (M.Φ w) hw', M.covers]
    have e : (Finset.univ.filter fun i => S'.s i (M.ϕ.obj (C.P w)) = M.Φ w) =
        Finset.univ.filter fun i => M.pullSec (S'.s i) (C.P w) = w :=
      Finset.filter_congr fun i _ =>
        (M.pullSec_eq_iff (S'.P_s i (hN.mapsTo_bdry hw)) rfl).symm
    rw [e]

/-- **The pulled-back decoration** `(𝒰, S)` over `∂X`. -/
def bdryPullDecoration (hface : M.FacePull_hyp) {Λ' : A.W → ℚ≥0}
    (D' : BoundaryDecoration A Λ') (P : M.BdryPullData D'.𝒰) :
    BoundaryDecoration C (M.pull Λ') :=
  ⟨P.𝒰, fun x => bdryPullStructure hface (P.isPull x) (D'.S (M.bdryObj x))⟩

/-- **The pulled-back correspondences** `τ_{x,y}(φ) = τ'_{F(x),F(y)}(F(φ))` over `∂X`. -/
def bdryPullTau (hface : M.FacePull_hyp) {Λ' : A.W → ℚ≥0} {D' : BoundaryDecoration A Λ'}
    (t' : D'.Tau) (P : M.BdryPullData D'.𝒰) : (bdryPullDecoration hface D' P).Tau where
  τ x y φ := t'.τ (M.bdryObj x) (M.bdryObj y) (M.ϕ.mor φ)
  locallyConstant x y φ hφ := by
    have ht : Tendsto M.ϕ.mor (𝓝[P.𝒰.mor x y] φ)
        (𝓝[D'.𝒰.mor (M.bdryObj x) (M.bdryObj y)] (M.ϕ.mor φ)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((M.ϕ.continuous_mor.tendsto φ).mono_left nhdsWithin_le_nhds)
        (eventually_nhdsWithin_of_forall fun ψ hψ => P.mor_mem hψ)
    exact ht.eventually (t'.locallyConstant _ _ _ (P.mor_mem hφ))
  finite x y := (t'.finite _ _).subset (by
    rintro _ ⟨φ, hφ, rfl⟩
    exact ⟨M.ϕ.mor φ, P.mor_mem hφ, rfl⟩)
  swap x y φ hφ := by
    change t'.τ _ _ (M.ϕ.mor (C.X.inv φ)) = (t'.τ _ _ (M.ϕ.mor φ)).swap
    rw [M.ϕ.mor_inv]
    exact t'.swap _ _ _ (P.mor_mem hφ)
  diag x g z hz := by
    change t'.τ _ _ (M.ϕ.mor ((P.𝒰.nbhd x).rep.Γ g z)) = _
    rw [(P.isPull x).Γ_eq g z hz.1]
    exact (t'.diag (M.bdryObj x) (M.ϕ.isotropyHom x g) (M.ϕ.obj z) (P.mapsTo x hz)).trans
      (ofPerm_compHom _ g).symm
  biact x y φ hφ g' g := by
    change t'.τ _ _ (M.ϕ.mor (EpGroupoid.biact (P.𝒰.nbhd x) (P.𝒰.nbhd y) g' φ g)) = _
    rw [(P.isPull x).mor_biact (P.isPull y) ⟨hφ.1.1, hφ.2.1⟩ g' g]
    exact (t'.biact _ _ _ (P.mor_mem hφ) (M.ϕ.isotropyHom y g') (M.ϕ.isotropyHom x g)).trans
      (biact_compHom _ _ g' _ g).symm
  compat x y φ hφ := IndexCorr.sat_mono (fun i j H => by
      have hsrc : C.P (M.pullSec ((D'.S (M.bdryObj x)).s i) (C.X.src φ)) = C.X.src φ :=
        M.P_pullSec _ _
      change M.pullSec ((D'.S (M.bdryObj y)).s j) (C.X.tgt φ) =
        fibAct φ (M.pullSec ((D'.S (M.bdryObj x)).s i) (C.X.src φ))
      refine M.eq_of_obj_eq ?_ ?_
      · rw [M.P_pullSec, P_fibAct hsrc]
      · rw [M.obj_pullSec ((D'.S _).P_s j (P.mapsTo y hφ.2)), M.obj_fibAct hsrc,
          M.obj_pullSec ((D'.S _).P_s i (P.mapsTo x hφ.1)), ← M.ϕ.tgt_mor, ← M.ϕ.src_mor]
        exact H)
    (t'.compat _ _ _ (P.mor_mem hφ))

end PullMap

/-- A decoration over `∂X` gives the local structures of Definition 14.1.3 at every boundary
point, so a functor over `∂X` with a decoration is an sc⁺-multisection over `∂X`. -/
theorem BoundaryDecoration.isBoundaryScPlusMultisection_fm {Λ : C.W → ℚ≥0}
    (hΛ : IsBoundaryWFunctor C Λ) (D : BoundaryDecoration C Λ) :
    IsBoundaryScPlusMultisection C Λ :=
  ⟨hΛ, fun x hx => ⟨D.𝒰.nbhd ⟨x, hx⟩, D.𝒰.isGood _, ⟨D.S _⟩⟩⟩

namespace PullMap

variable {M}

/-- **The pulled-back structured tuple over `∂X`** `(Φ^*Λ', 𝒰, S, τ)`. -/
def bdryPullTuple (hface : M.FacePull_hyp) (T' : BoundaryStructuredTuple A)
    (P : M.BdryPullData T'.dec.𝒰) : BoundaryStructuredTuple C where
  Λ := M.pull T'.Λ
  isBoundaryScPlusMultisection :=
    (bdryPullDecoration hface T'.dec P).isBoundaryScPlusMultisection_fm
      (M.isBoundaryWFunctor_pull T'.isBoundaryScPlusMultisection.1)
  dec := bdryPullDecoration hface T'.dec P
  tau := bdryPullTau hface T'.tau P

variable (M)

/-- **Pull-backs of structurable sc⁺-multisections over `∂X'` are structurable over `∂X`**
(the first step of the proof of Proposition 14.1.8), for tame `X`, under `FacePull_hyp`. -/
theorem isBoundaryStructurable_pull_hyp (hX : C.X.IsTame) (hface : M.FacePull_hyp)
    {Λ' : A.W → ℚ≥0} (h : IsBoundaryStructurable A Λ') :
    IsBoundaryStructurable C (M.pull Λ') := by
  obtain ⟨hΛ', D', ⟨t'⟩⟩ := h
  obtain ⟨P⟩ := M.exists_bdryPullData hX D'.𝒰
  exact ⟨(bdryPullDecoration hface D' P).isBoundaryScPlusMultisection_fm
    (M.isBoundaryWFunctor_pull hΛ'.1), bdryPullDecoration hface D' P,
    ⟨bdryPullTau hface t' P⟩⟩

end PullMap

/-- **2021 Proposition 14.1.8, p. 645 (2017: Proposition 14.1), the pull-back step of the
proof**: for a strong bundle equivalence `F : W → W'` over a tame ep-groupoid and `Λ'`
structurable over `∂X'`, `F^*Λ'` is structurable over `∂X`; with the added hypothesis
`FacePull_hyp` (face-sc⁺ sections pull back; witnesses `PullMap.facePull_hyp_id`,
`PullMap.facePull_hyp_of_boundary_eq_empty`). -/
theorem proposition_14_1_8_pull_hyp {F : C ⟶ A} (hF : SEP.equivalences F) (hX : C.X.IsTame)
    (hface : (PullMap.ofEquivalence hF).FacePull_hyp) {Λ' : A.W → ℚ≥0}
    (h : IsBoundaryStructurable A Λ') : IsBoundaryStructurable C (pullMult F Λ') :=
  (PullMap.ofEquivalence hF).isBoundaryStructurable_pull_hyp hX hface h

end SBLocalization

end Polyfold
