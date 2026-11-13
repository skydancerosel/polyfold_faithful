import Polyfold.Chapter16.P3H_BranchedSuborbifold
import Polyfold.Chapter11.GapP2_H4Measure

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 16,
§16.4, p. 729 and **Definition 16.4.2 (5)** (2017: Definition 16.30): tameness of branched
ep⁺-subgroupoids is invariant under generalized isomorphisms.  Numbers and pages are the 2021
text's.

# Tameness of branched suborbifolds does not depend on the representative

## The text, paraphrased

(p. 729) If `Θ` is tame, so are `f_*Θ` and `f^*Θ` for a generalized isomorphism `f`;
(Definition 16.4.2 (5)) `θ = [Θ, (X, α)]` is tame if `Θ` is, and then every representative is.

## What is formalized

* `TameBranchingStructure.restrictRep`, `TameBranchingStructure.move` (Definition 9.3.6's tame
  local branching structures restricted to a smaller natural representation and moved by an
  sc-diffeomorphism; the unoriented versions of Chapter 11's `OrientedTameStructure.restrictRep`,
  `move`).
* `EpFunctor.isTameBranched_pullbackTheta`, `EpFunctor.isTameBranched_pushforwardTheta`: for an
  equivalence `Φ` and functorial `Θ'`, `Θ` tame ⇒ `Φ^*Θ'`, `Φ_*Θ` tame (the structures moved along
  transport charts `Q = ψ̂ ∘ Φ`, as in the proof of Theorem 11.4.1).
* `EpFunctor.isTameBranched_pullbackTheta_iff`: `Φ^*Θ'` is tame iff `Θ'` is.
* `EPLoc.isTameBranched_pullTheta`: for a generalized isomorphism `f`, `f^*Θ'` is tame if `Θ'`
  is (`f^* = F_* Φ^*`).
* **`BranchedSuborbifold.definition_16_4_2_tame`**: `θ` is tame iff every representative is
  (closing the "(5)" part of Definition 16.4.2 left open in `P3H_BranchedSuborbifold`).
* `OrientedRep.Rel.isTameOriented(_iff)`, `OrientedSuborbifold.IsTameOriented`,
  `OrientedSuborbifold.isTameOriented_iff`: the same for oriented tameness (`IsTameOriented`, the
  tameness hypothesis of the integrals on p. 732), from the structures of Theorem 11.4.1.
* `OrientedSuborbifold.integral`, `integralEff` with `integral_eq`, `integralEff_eq`: `∫_θ̂ τ`,
  `∮_θ̂ τ` for tame compact `θ̂`, computed on every representative.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

open EpGroupoid MPolyfold

namespace EpGroupoid.TameBranchingStructure

variable {Obj Mor Obj' Mor' : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {Θ : Obj → ℚ} {x : Obj}

/-- A tame local branching structure restricted to a natural representation on a smaller
neighbourhood `R.U ⊆ U(x)`. -/
def restrictRep (C : X.TameBranchingStructure Θ x) (R : X.NaturalRep x) (hR : R.U ⊆ C.U) :
    X.TameBranchingStructure Θ x where
  toLocalBranchingStructure := C.toLocalBranchingStructure.restrict R.isOpen_U R.mem_U hR
  rep := R
  U_eq := rfl
  hasPropernessProperty := C.hasPropernessProperty.mono R.isOpen_U hR
  hasTameInducedStructure i := MPolyfold.HasTameInducedStructure.inter_isOpen
    (C.isSmoothSubmanifold i) (C.hasTameInducedStructure i) R.isOpen_U

@[simp] theorem restrictRep_U (C : X.TameBranchingStructure Θ x) (R : X.NaturalRep x)
    (hR : R.U ⊆ C.U) : (C.restrictRep R hR).U = R.U := rfl

variable {Θ' : Obj' → ℚ} {f : Obj → Obj'} {g : Obj' → Obj} {W : Set Obj} {W' : Set Obj'}

theorem mapU_eq (C : X.TameBranchingStructure Θ x) (hf : X.PObj.IsScDiffeoOn Y.PObj f g W W')
    (hUW : C.U ⊆ W) : C.toLocalBranchingStructure.mapU g W W' = f '' C.U := by
  ext z
  constructor
  · rintro ⟨hzW', hzU, -⟩
    exact ⟨g z, hzU, hf.right_inv z hzW'⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨hf.mapsTo (hUW hu), by rw [mem_preimage, hf.left_inv u (hUW hu)]; exact ⟨hu, hUW hu⟩⟩

/-- **A tame local branching structure moved by an sc-diffeomorphism** `f : W → W'` with
`U(x) ⊆ W`: the sheets `f(Mᵢ ∩ W)` with the weights `σᵢ` on `f(U(x))`, with a given natural
representation `R'` of `G_{f(x)}` on `f(U(x))` having the properness property. -/
def move (C : X.TameBranchingStructure Θ x) (hf : X.PObj.IsScDiffeoOn Y.PObj f g W W')
    (hUW : C.U ⊆ W) {y : Obj'} (hxy : f x = y) (hΘ : ∀ u ∈ W, Θ' (f u) = Θ u)
    (R' : Y.NaturalRep y) (hR' : R'.U = f '' C.U) (hP : Y.HasPropernessProperty (f '' C.U)) :
    Y.TameBranchingStructure Θ' y where
  toLocalBranchingStructure := C.toLocalBranchingStructure.mapDiffeo hf (hUW C.mem_U) hxy hΘ
  rep := R'
  U_eq := (C.mapU_eq hf hUW).trans hR'.symm
  hasPropernessProperty := by
    change Y.HasPropernessProperty (C.toLocalBranchingStructure.mapU g W W')
    rw [C.mapU_eq hf hUW]
    exact hP
  hasTameInducedStructure i := MPolyfold.HasTameInducedStructure.image_of_isScDiffeoOn
    ((C.isSmoothSubmanifold i).inter_isOpen hf.isScSmoothOn.isOpen)
    (MPolyfold.HasTameInducedStructure.inter_isOpen (C.isSmoothSubmanifold i)
      (C.hasTameInducedStructure i) hf.isScSmoothOn.isOpen) hf inter_subset_right

end EpGroupoid.TameBranchingStructure

namespace EpFunctor

variable {Obj Mor Obj' Mor' : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {Φ : EpFunctor X Y}

open OrientedTameStructure

/-- **The pull-back of a tame `Θ'` along an equivalence is tame** (2021 p. 729). -/
theorem isTameBranched_pullbackTheta (hΦ : Φ.IsEquivalence) {Θ' : Obj' → ℚ}
    (hΘ' : Y.IsFunctorial Θ') (h : Y.IsTameBranched Θ') :
    X.IsTameBranched (Φ.pullbackTheta Θ') := by
  intro x hx
  obtain ⟨Tc⟩ := TransportChart.nonempty hΦ x
  obtain ⟨D⟩ := h (Φ.obj x) hx
  obtain ⟨V, hxV, hVP⟩ := X.exists_hasPropernessProperty x
  obtain ⟨R₀, hR₀⟩ := X.theorem_7_1_13 x hVP.1 hxV
  obtain ⟨R, R', hRR₀, hRW, hRD, hR'⟩ := Tc.exists_rep_push hΦ R₀ D.isOpen_U D.mem_U
  have hRP : X.HasPropernessProperty R.U := hVP.mono R.isOpen_U (hRR₀.trans hR₀)
  have hR'D : R'.U ⊆ D.U := hR' ▸ hRD
  have hΘ := Tc.pullbackTheta_Q hΘ'
  refine ⟨(D.restrictRep R' hR'D).move Tc.isScDiffeoOn_Q.symm ?_ (Qinv_y Tc) ?_ R ?_ ?_⟩
  · rw [TameBranchingStructure.restrictRep_U, hR']
    exact image_subset_iff.2 fun u hu => Tc.isScDiffeoOn_Q.mapsTo (hRW hu)
  · intro z hz
    rw [← hΘ _ (Tc.isScDiffeoOn_Q.mapsTo_inv hz), Tc.isScDiffeoOn_Q.right_inv z hz]
  · rw [TameBranchingStructure.restrictRep_U, hR', Qinv_image_Q_image Tc hRW]
  · rw [TameBranchingStructure.restrictRep_U, hR', Qinv_image_Q_image Tc hRW]
    exact hRP

/-- **The push-forward of a tame `Θ` along an equivalence is tame** (2021 p. 729). -/
theorem isTameBranched_pushforwardTheta (hΦ : Φ.IsEquivalence) {Θ : Obj → ℚ}
    (hΘ : X.IsFunctorial Θ) (h : X.IsTameBranched Θ) :
    Y.IsTameBranched (Φ.pushforwardTheta Θ) := by
  intro y hy
  have hΘ' := isFunctorial_pushforwardTheta hΦ.full hΘ
  have he := pullbackTheta_pushforwardTheta hΦ.full hΘ
  obtain ⟨x, hx, ⟨Tc⟩⟩ := exists_transportChart_of_mem_supp hΦ hΘ' hy
  rw [he] at hx
  obtain ⟨C⟩ := h x hx
  have hΘQ : ∀ u ∈ Tc.W, Φ.pushforwardTheta Θ (Tc.Q u) = Θ u := fun u hu => by
    rw [Tc.pullbackTheta_Q hΘ' u hu, he]
  obtain ⟨V', hyV', hV'P⟩ := Y.exists_hasPropernessProperty y
  obtain ⟨R, R', hRC, hRW, hRV', hR'⟩ := Tc.exists_rep_push hΦ C.rep hV'P.1 hyV'
  have hRU : R.U ⊆ C.U := C.U_eq ▸ hRC
  have hP' : Y.HasPropernessProperty (Tc.Q '' (C.restrictRep R hRU).U) :=
    hV'P.mono (hR' ▸ R'.isOpen_U) hRV'
  exact ⟨(C.restrictRep R hRU).move Tc.isScDiffeoOn_Q hRW Tc.Q_self hΘQ R' hR' hP'⟩

/-- For an equivalence and functorial `Θ'`: `Φ^*Θ'` is tame iff `Θ'` is (`Φ_*Φ^*Θ' = Θ'`). -/
theorem isTameBranched_pullbackTheta_iff (hΦ : Φ.IsEquivalence) {Θ' : Obj' → ℚ}
    (hΘ' : Y.IsFunctorial Θ') : X.IsTameBranched (Φ.pullbackTheta Θ') ↔ Y.IsTameBranched Θ' := by
  refine ⟨fun h => ?_, isTameBranched_pullbackTheta hΦ hΘ'⟩
  have e := pushforwardTheta_pullbackTheta (F := Φ) hΦ.essSurj hΘ'
  rw [← e]
  exact isTameBranched_pushforwardTheta hΦ (isFunctorial_pullbackTheta Φ hΘ') h

end EpFunctor

namespace EPLocalization.EPLoc

variable {X Y : EP.{u}}

/-- **`f^*Θ'` is tame for a tame `Θ'` and a generalized isomorphism `f`** (2021 p. 729;
`f^* = F_* Φ^*` on a representative with both legs equivalences). -/
theorem isTameBranched_pullTheta {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) {Θ' : Y.Obj → ℚ}
    (hΘ' : Y.X.IsFunctorial Θ') (h : Y.X.IsTameBranched Θ') :
    X.X.IsTameBranched (pullTheta f Θ') := by
  obtain ⟨d, rfl, hΦ⟩ := exists_diagram_of_isGeneralizedIso hf
  rw [pullTheta_homMk d hΘ']
  exact EpFunctor.isTameBranched_pushforwardTheta d.isEquivalence_F
    (EpFunctor.isFunctorial_pullbackTheta _ hΘ')
    (EpFunctor.isTameBranched_pullbackTheta hΦ hΘ' h)

end EPLocalization.EPLoc

namespace PolyfoldClass.BranchedSuborbifold

variable {Z : Type u} [TopologicalSpace Z] {c : PolyfoldClass Z}

open EPLocalization EPLocalization.EPLoc

/-- **2021 Definition 16.4.2 (5), p. 730 (2017: Definition 16.30), well posed**: `θ` is tame iff
every representative `Θ` is tame (Definition 9.3.6), since generalized isomorphisms preserve
tameness (p. 729). -/
theorem definition_16_4_2_tame (θ : BranchedSuborbifold c) :
    θ.IsTame ↔ ∀ a : BranchedRep c, ⟦a⟧ = θ → a.p.X.X.IsTameBranched a.Θ :=
  hasRepProperty_iff _ (fun hf _ hΘ' h => isTameBranched_pullTheta hf hΘ'.isFunctorial h) θ

end PolyfoldClass.BranchedSuborbifold

namespace PolyfoldClass.OrientedRep

variable {Z : Type u} [TopologicalSpace Z] {c : PolyfoldClass Z} {n : ℕ}

open EPLocalization EPLocalization.EPLoc EpGroupoid

/-- **Oriented tameness passes to related representatives** (2021 p. 729 for oriented tame
structures describing `T̂`): if `((Θ, T̂), (X, α)) ∼ ((Θ', T̂'), (X', α'))` and `Θ̂'` is tame of
dimension `n` in the form of Chapter 9, so is `Θ̂ = f^*Θ̂'` (the structures of Theorem 11.4.1,
`hcov_pullTheta`). -/
theorem Rel.isTameOriented {a b : OrientedRep c} (h : Rel a b) (hb : b.IsTameOriented n) :
    a.IsTameOriented n := by
  obtain ⟨f, hf, -, hA⟩ := h
  unfold IsTameOriented
  rw [← hA]
  intro x hx
  obtain ⟨C, -, hC⟩ := (rep f).hcov_pullTheta (isEquivalence_rep_Φ hf)
    (EP.epFormsInftyEval_isPullback (rep f).isEquivalence_F n)
    (EP.epFormsInftyEval_isPullback (isEquivalence_rep_Φ hf) n) b.A.isBranchedEpSubgroupoid
    b.A.hasIndependentTangentSums b.A.isOrientation
    (FormEval.hcov_of_tameOpen (FormEval.tameOpen b.p.X.X) hb) x hx
  exact ⟨C, hC⟩

theorem Rel.isTameOriented_iff {a b : OrientedRep c} (h : Rel a b) :
    a.IsTameOriented n ↔ b.IsTameOriented n :=
  ⟨(Rel.symm h).isTameOriented, h.isTameOriented⟩

end PolyfoldClass.OrientedRep

namespace PolyfoldClass.OrientedSuborbifold

variable {Z : Type u} [TopologicalSpace Z] {c : PolyfoldClass Z} {n : ℕ}

/-- **`θ̂` is tame of dimension `n`**: a representative is (oriented tame structures describing
`T̂_Θ`, Definition 9.5.6). -/
def IsTameOriented (θ : OrientedSuborbifold c) (n : ℕ) : Prop :=
  ∃ a : OrientedRep c, ⟦a⟧ = θ ∧ a.IsTameOriented n

/-- **Oriented tameness of `θ̂` does not depend on the representative** (2021 p. 729): `θ̂` is
tame iff every representative is. -/
theorem isTameOriented_iff (θ : OrientedSuborbifold c) :
    θ.IsTameOriented n ↔ ∀ a : OrientedRep c, ⟦a⟧ = θ → a.IsTameOriented n := by
  refine ⟨fun ⟨a, ha, h⟩ b hb => ?_, fun h => ?_⟩
  · exact (OrientedRep.Rel.isTameOriented_iff (Quotient.exact (hb.trans ha.symm))).2 h
  · obtain ⟨a, rfl⟩ := Quotient.exists_rep θ
    exact ⟨a, rfl, h a rfl⟩

theorem toBranched_mk (a : OrientedRep c) :
    OrientedSuborbifold.toBranched (⟦a⟧ : OrientedSuborbifold c) = ⟦a.toBranchedRep⟧ := rfl

theorem isCompactBranched_of_mk {θ : OrientedSuborbifold c} (hcpt : θ.toBranched.IsCompact)
    (a : OrientedRep c) (ha : ⟦a⟧ = θ) : a.p.X.X.IsCompactBranched a.A.Θ :=
  (BranchedSuborbifold.definition_16_4_2_compact _).1 hcpt a.toBranchedRep
    (by rw [← toBranched_mk, ha])

/-- **The integral `∫_θ̂ τ`** (2021 p. 732) of a tame compact oriented branched suborbifold
`θ̂` of dimension `n ≥ 1`: `µ^Θ̂_ω(|supp Θ|)` on a chosen representative. -/
def integral (θ : OrientedSuborbifold c) (hn : 0 < n) (hcpt : θ.toBranched.IsCompact)
    (htame : θ.IsTameOriented n) (τ : ScForm c n) : ℝ :=
  θ.out.integral hn (isCompactBranched_of_mk hcpt _ (Quotient.out_eq θ))
    ((isTameOriented_iff θ).1 htame _ (Quotient.out_eq θ)) τ

/-- **`∫_θ̂ τ` is computed on every representative** (2021 p. 732, "does not depend on the
choice of the representatives"). -/
theorem integral_eq (θ : OrientedSuborbifold c) (hn : 0 < n) (hcpt : θ.toBranched.IsCompact)
    (htame : θ.IsTameOriented n) (τ : ScForm c n) (a : OrientedRep c) (ha : ⟦a⟧ = θ) :
    θ.integral hn hcpt htame τ = a.integral hn (isCompactBranched_of_mk hcpt a ha)
      ((isTameOriented_iff θ).1 htame a ha) τ :=
  OrientedRep.integral_eq_of_rel (Quotient.exact ((Quotient.out_eq θ).trans ha.symm)) hn _ _ _ _ τ

/-- **The effective integral `∮_θ̂ τ`** (2021 p. 732) on a chosen representative. -/
def integralEff (θ : OrientedSuborbifold c) (hn : 0 < n) (hcpt : θ.toBranched.IsCompact)
    (htame : θ.IsTameOriented n) (τ : ScForm c n) : ℝ :=
  θ.out.integralEff hn (isCompactBranched_of_mk hcpt _ (Quotient.out_eq θ))
    ((isTameOriented_iff θ).1 htame _ (Quotient.out_eq θ)) τ

/-- **`∮_θ̂ τ` is computed on every representative** (2021 p. 732). -/
theorem integralEff_eq (θ : OrientedSuborbifold c) (hn : 0 < n) (hcpt : θ.toBranched.IsCompact)
    (htame : θ.IsTameOriented n) (τ : ScForm c n) (a : OrientedRep c) (ha : ⟦a⟧ = θ) :
    θ.integralEff hn hcpt htame τ = a.integralEff hn (isCompactBranched_of_mk hcpt a ha)
      ((isTameOriented_iff θ).1 htame a ha) τ :=
  OrientedRep.integralEff_eq_of_rel (Quotient.exact ((Quotient.out_eq θ).trans ha.symm)) hn _ _ _ _
    τ

end PolyfoldClass.OrientedSuborbifold

end Polyfold
