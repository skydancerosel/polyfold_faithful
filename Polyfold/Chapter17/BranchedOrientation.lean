import Polyfold.Chapter17.BranchedTangent
import Polyfold.Chapter11.BranchedEquivalenceTangentOrientation

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.5 "Branched Ep⁺-Subcategories" (p. 817): **Remark 17.5.9** (orientations tested on the
uniformizers).  Numbers and pages are the 2021 text's.

# Orientations of branched ep⁺-subcategories on the uniformizers

## The text, paraphrased

(Remark 17.5.9) The part of Definition 17.5.8 requiring that the pull-back `TΓ^*T̂Θ` is an
orientation of `Θ ∘ Γ` can be replaced by requiring that, for `α ∈ supp(Θ)` and `Ψ ∈ F(α)`, the
pull-back `TΨ^*T̂Θ` is an orientation of `Θ ∘ Ψ` (Definition 9.3.2 on `G ⋉ O`).

## What is formalized

* `unifOrPull`, `unifSectionPull` (`TΨ^*T̂`, the preimages under `TΨ(q) : T_qO → T_{Ψ(q)}C`).
* Transport between the model `X_Ψ` and its summands (`ι_λ = Sigma.mk λ`): `orTCPull_mk`,
  `sectionPull_mk` (`TΓ^*T̂ = Tι_λ(TΨ_λ^*T̂)`), `hasOrientedRepAt_model_of_unif`,
  `hasOrientedRepAt_unif_of_model` (condition (9.9) in both directions).
* The four clauses of Definition 9.3.2 for the pull-backs: values in `Gr̂` and the lift of `TΘ`
  from (9.9) and the vanishing off `supp(Θ)` (`mem_grHat_of_hasOrientedRepAt`,
  `grForget_eq_tangentValue`, `branchedTangentSection_eq_zero`, `eq_zero_of_not_mem_supp`);
  naturality on `X_Ψ` from naturality on `C` (`orTCPull_move`, `grHatPush_sectionPull`) and on
  `G ⋉ O` for continuous `Ψ̂` (`tangentUnifObj_tangentMor`, `unifOrPull_move`,
  `grHatPush_unifSectionPull`); (9.9) moved along morphisms of an ep-groupoid
  (`exists_orientedBranchingStructure_tgt`, `hasOrientedRepAt_tgt`).
* `isOrientation_model_of_unif`: the model condition for every family of uniformizers from (9.9)
  for one uniformizer at a point over each `α ∈ supp(Θ)`;
  `isOrientationC_of_unif` (Remark 17.5.9, "⇐", no further condition).
* `hasOrientedRepAt_unif`, `unif_of_isOrientationC` ("⇒" for the values in `Gr̂`, the lift and
  (9.9), every uniformizer of `F`), `isOrientation_unif_of_isOrientationC` ("⇒" for continuous
  `Ψ̂`), and **`remark_17_5_9_hyp`** (the equivalence, for continuous `Ψ̂`).
* `branchedTangentSection_eq_unif` (`TΘ(α) = Tφ(TΨ(T(Θ ∘ Ψ)(q)))`, Proposition 17.5.7 through a
  uniformizer).

## Readings

* `TΨ^*T̂` is read as `TΓ^*T̂` of Definition 17.5.8: preimages of the carriers and of the frames
  under `TΨ(q)`.  Theorem 9.2.1's independence is `hasIndependentTangentSums`.
* "For `α ∈ supp(Θ)` and `Ψ ∈ F(α)`" is read as "for all such `α` and `Ψ`"; the direction "⇐"
  uses one uniformizer at one point over each `α ∈ supp(Θ)` (`isOrientation_model_of_unif`), the
  model condition is obtained for every family of uniformizers, in particular for every covering
  family.
* The direction "⇒" for the naturality clause of Definition 9.3.2 on `G ⋉ O` uses that
  `TΨ(T(g ∗ ·)(h)) = T(Ψ(g, q))(TΨ(h))` (Lemma 17.2.10 on morphisms), which holds for continuous
  `Ψ̂` (`tangentUnifMor_tgt_of_continuous`) and does not hold as we read it in general
  (`not_lemma_17_2_10`).  `remark_17_5_9_hyp` therefore assumes that every `Ψ̂` is continuous
  (the condition `HatContinuous`; witnessed by the reflection polyfold,
  `reflection_continuous_hat_all`).  We do not know whether "⇒" holds without it; the other three
  clauses hold for every uniformizer (`unif_of_isOrientationC`).
* `tangentMor_actionEpGroupoid` (`Tφ = T(k ∗ ·)` on `K ⋉ U`) is the statement of Chapter 19's
  `action_tangentMor_eq`, proved here because Chapter 17 does not import Chapter 19.
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

universe u

/-! ### Ep-groupoids: tangent maps on sheets, oriented structures moved along morphisms -/

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

/-- **`Tφ = Tφ̂_𝐔(s φ)` for every sheet `𝐔 ∋ φ`** (`tangentMor_eq_tangentMapOn_hat` is the chosen
sheet). -/
theorem tangentMor_eq_tangentMapOn_sheetHat (Sh : X.Sheet) {φ : Mor} (hφS : φ ∈ Sh.carrier)
    (hφ : φ ∈ X.PMor.levelSet 1) {α : X.PObj.TangentSpace}
    (hα : X.PObj.levelVal 1 (X.PObj.tangentProj α) = X.src φ) :
    X.tangentMor φ α = MPolyfold.tangentMapOn Sh.isScDiffeoOn_hat.isScSmoothOn α := by
  obtain ⟨v, hv, rfl⟩ := X.exists_tSrc_eq' hφ hα
  have hd := Sh.isScDiffeoOn_src
  have hvS : X.tBase v ∈ Sh.carrier := by rw [hv]; exact hφS
  have hαS : X.tSrc v ∈ X.PObj.tangentPreimage Sh.srcSet := by
    change X.PObj.levelVal 1 (X.PObj.tangentProj (X.tSrc v)) ∈ Sh.srcSet
    rw [X.levelVal_tangentProj_tSrc]; exact hd.mapsTo hvS
  have key : X.tangentMor (X.tBase v) (X.tSrc v) = X.tTgt v := X.tangentMor_tSrc v
  rw [hv] at key
  rw [key]
  have h1 := MPolyfold.tangentMap_tangentMapOn X.isScSmoothMap_tgt hd.isScSmoothOn_inv hαS
  rw [tangentMapOn_srcInv_tSrc hd hvS] at h1
  change MPolyfold.tangentMap X.isScSmoothMap_tgt v = _
  rw [h1]
  exact MPolyfold.tangentMapOn_congr _ _ hd.isScSmoothOn_inv.isOpen subset_rfl subset_rfl
    (fun _ _ => rfl) hαS

/-- **An oriented local representation (9.9) is carried along a morphism** `φ : x → y` by the
local sc-diffeomorphism `φ̂` of the chosen sheet, for a natural section `T` of `Gr̂(X)`: if
`T = ∑ σᵢ T(Mᵢ, oᵢ)` near `x`, then `T = ∑ σᵢ T(φ̂(Mᵢ), φ̂_* oᵢ)` near `y`. -/
theorem exists_orientedBranchingStructure_tgt {Θ : Obj → ℚ} (hΘ : X.IsFunctorial Θ)
    {T : Obj → X.PObj.OrTangent →₀ ℚ}
    (hnat : ∀ φ : Mor, X.src φ ∈ X.PObj.smoothSet →
      X.grHatPush φ (T (X.src φ)) = T (X.tgt φ))
    (φ : Mor) (B : X.OrientedBranchingStructure Θ (X.src φ))
    (hB : ∀ y ∈ B.U, y ∈ X.PObj.smoothSet → T y = B.orientedSum y) :
    ∃ B' : X.OrientedBranchingStructure Θ (X.tgt φ),
      ∀ y ∈ B'.U, y ∈ X.PObj.smoothSet → T y = B'.orientedSum y := by
  set Sh := X.sheetAt φ
  have hf := X.isScDiffeoOn_hat' φ
  have hΘ' : ∀ u ∈ Sh.srcSet, Θ (X.hat φ u) = Θ u := fun u hu => Sheet.apply_hat hΘ Sh hu
  refine ⟨B.mapDiffeo hf (X.src_mem_sheetAt φ) (X.hat_src φ) hΘ', fun z hz hzs => ?_⟩
  rw [B.orientedSum_mapDiffeo hf (X.src_mem_sheetAt φ) (X.hat_src φ) hΘ' hz]
  obtain ⟨hzW', hzU, hzW⟩ := hz
  set u := X.hatInv φ z
  set ψ := Sh.srcInv u
  have hψS : ψ ∈ Sh.carrier := Sh.isScDiffeoOn_src.mapsTo_inv hzW
  have hsψ : X.src ψ = u := Sh.isScDiffeoOn_src.right_inv u hzW
  have htψ : X.tgt ψ = z := hf.right_inv z hzW'
  have hψ1 := X.mem_levelSet_one_of_tgt_mem_smoothSet (htψ ▸ hzs : X.tgt ψ ∈ _)
  have hus : u ∈ X.PObj.smoothSet := hsψ ▸ X.src_mem_smoothSet_of_tgt (htψ ▸ hzs : X.tgt ψ ∈ _)
  have h := hnat ψ (hsψ ▸ hus)
  rw [hsψ, htψ, hB u hzU hus] at h
  rw [← h, grHatPush]
  exact mapDomain_map_congr (B.orientedSum_mem u) (f := X.tangentMor ψ) fun α hα =>
    tangentMor_eq_tangentMapOn_sheetHat Sh hψS hψ1 (hα.trans hsψ.symm)

/-- **An oriented local representation of `T` at `x`** (the condition (9.9) of Definition 9.3.2
at one point): a local branching structure with orientations at `x` whose oriented sum is `T`
on its domain. -/
def HasOrientedRepAt (Θ : Obj → ℚ) (T : Obj → X.PObj.OrTangent →₀ ℚ) (x : Obj) : Prop :=
  ∃ B : X.OrientedBranchingStructure Θ x, ∀ y ∈ B.U, y ∈ X.PObj.smoothSet → T y = B.orientedSum y

theorem hasOrientedRepAt_tgt {Θ : Obj → ℚ} (hΘ : X.IsFunctorial Θ)
    {T : Obj → X.PObj.OrTangent →₀ ℚ}
    (hnat : ∀ φ : Mor, X.src φ ∈ X.PObj.smoothSet →
      X.grHatPush φ (T (X.src φ)) = T (X.tgt φ))
    {φ : Mor} (h : X.HasOrientedRepAt Θ T (X.src φ)) : X.HasOrientedRepAt Θ T (X.tgt φ) := by
  obtain ⟨B, hB⟩ := h
  exact exists_orientedBranchingStructure_tgt hΘ hnat φ B hB

/-- **The lifting condition of Definition 9.3.2 from (9.9)** (as in `IsOrientation.mk'`): a section
vanishing off `supp(Θ)` and with oriented local representations on `supp(Θ)` lifts `TΘ`. -/
theorem grForget_eq_tangentValue {Θ : Obj → ℚ} (hind : X.HasIndependentTangentSums Θ)
    {T : Obj → X.PObj.OrTangent →₀ ℚ}
    (hzero : ∀ x ∈ X.PObj.smoothSet, x ∉ supp Θ → T x = 0)
    (hloc : ∀ x ∈ supp Θ, X.HasOrientedRepAt Θ T x) {x : Obj} (hx : x ∈ X.PObj.smoothSet) :
    X.grForget (T x) = X.tangentValue Θ x := by
  by_cases hxs : x ∈ supp Θ
  · obtain ⟨B, hB⟩ := hloc x hxs
    rw [hB x B.mem_U hx, B.grForget_orientedSum_self,
      X.tangentValue_eq hind B.toLocalBranchingStructure]
  · rw [hzero x hx hxs, X.tangentValue_eq_zero hxs, grForget, Finsupp.mapDomain_zero]

/-- Values in `Gr̂` from (9.9) and the vanishing off `supp(Θ)`. -/
theorem mem_grHat_of_hasOrientedRepAt {Θ : Obj → ℚ} {T : Obj → X.PObj.OrTangent →₀ ℚ}
    (hzero : ∀ x ∈ X.PObj.smoothSet, x ∉ supp Θ → T x = 0)
    (hloc : ∀ x ∈ supp Θ, X.HasOrientedRepAt Θ T x) {x : Obj} (hx : x ∈ X.PObj.smoothSet) :
    T x ∈ X.GrHat x := by
  by_cases hxs : x ∈ supp Θ
  · obtain ⟨B, hB⟩ := hloc x hxs
    rw [hB x B.mem_U hx]
    exact B.orientedSum_mem x
  · rw [hzero x hx hxs]
    exact X.zero_mem_GrHat x

/-- **Definition 9.3.2 from naturality, vanishing off `supp(Θ)` and (9.9)** (Theorem 9.2.1's
independence holds, `hasIndependentTangentSums`). -/
theorem isOrientation_of_hasOrientedRepAt {Θ : Obj → ℚ} {T : Obj → X.PObj.OrTangent →₀ ℚ}
    (hnat : ∀ φ : Mor, X.src φ ∈ X.PObj.smoothSet →
      X.grHatPush φ (T (X.src φ)) = T (X.tgt φ))
    (hzero : ∀ x ∈ X.PObj.smoothSet, x ∉ supp Θ → T x = 0)
    (hloc : ∀ x ∈ supp Θ, X.HasOrientedRepAt Θ T x) : X.IsOrientation Θ T :=
  IsOrientation.mk' (X.hasIndependentTangentSums Θ)
    (fun _ hx => mem_grHat_of_hasOrientedRepAt hzero hloc hx) hnat hzero hloc

end EpGroupoid

namespace EpGroupoid.Examples

variable {K : Type u} [Group K] [Finite K] [TopologicalSpace K] [DiscreteTopology K]
  {U : Type u} [TopologicalSpace U] [T2Space U] [ParacompactSpace U] [MulAction K U]
  {P : MPolyfold U} (hP : ∀ k : K, P.IsScSmoothMap P fun y => k • y)

/-- **The tangent map of the morphism `(k, x)` of `K ⋉ U` is `T(k ∗ ·)`** on `T_xU` (the local
sc-diffeomorphism of the sheet of `(k, x)` is `k ∗ ·` near `x`). -/
theorem tangentMor_actionEpGroupoid {φ : K × U}
    (hφ : φ ∈ (actionEpGroupoid hP).PMor.levelSet 1) {α : P.TangentSpace}
    (hα : P.levelVal 1 (P.tangentProj α) = φ.2) :
    (actionEpGroupoid hP).tangentMor φ α = MPolyfold.tangentMap (hP φ.1) α := by
  set X := actionEpGroupoid hP
  rw [X.tangentMor_eq_tangentMapOn_hat hφ hα]
  set Sh := X.sheetAt φ
  have hd := Sh.isScDiffeoOn_src
  have hc : ContinuousOn Sh.srcInv Sh.srcSet := hd.isScSmoothOn_inv.continuousOn
  have hWo : IsOpen (Sh.srcSet ∩ Sh.srcInv ⁻¹' ({φ.1} ×ˢ univ)) :=
    hc.isOpen_inter_preimage hd.isScSmoothOn_inv.isOpen ((isOpen_discrete _).prod isOpen_univ)
  have hxW : φ.2 ∈ Sh.srcSet ∩ Sh.srcInv ⁻¹' ({φ.1} ×ˢ univ) := by
    refine ⟨X.src_mem_sheetAt φ, ?_⟩
    have h1 : Sh.srcInv (X.src φ) = φ := hd.left_inv φ (X.mem_sheetAt φ)
    change Sh.srcInv (X.src φ) ∈ ({φ.1} ×ˢ univ : Set (K × U))
    rw [h1]
    exact ⟨rfl, mem_univ _⟩
  have heq : EqOn (X.hat φ) (fun y => φ.1 • y) (Sh.srcSet ∩ Sh.srcInv ⁻¹' ({φ.1} ×ˢ univ)) := by
    intro y hy
    have h1 : (Sh.srcInv y).1 = φ.1 := hy.2.1
    have h2 : (Sh.srcInv y).2 = y := hd.right_inv y hy.1
    change (Sh.srcInv y).1 • (Sh.srcInv y).2 = φ.1 • y
    rw [h1, h2]
  have hk := (hP φ.1).mono hWo (subset_univ _)
  have hαW : α ∈ P.tangentPreimage (Sh.srcSet ∩ Sh.srcInv ⁻¹' ({φ.1} ×ˢ univ)) := by
    change P.levelVal 1 (P.tangentProj α) ∈ (Sh.srcSet ∩ Sh.srcInv ⁻¹' ({φ.1} ×ˢ univ))
    rw [hα]
    exact hxW
  rw [MPolyfold.tangentMapOn_congr (X.isScDiffeoOn_hat φ).isScSmoothOn hk hWo inter_subset_left
    subset_rfl heq hαW]
  exact MPolyfold.tangentMapOn_eq_tangentMap (hP φ.1) hk hαW

end EpGroupoid.Examples

/-! ### Preimages under fibrewise bijections -/

/-- `{b ∈ P' | u'(b) ∈ m(L)} = f({a ∈ P | u(a) ∈ L})` for `f : P → P'` with right inverse `f'`,
`u' ∘ f = m ∘ u` on `P` and `m` injective on a set `D ⊇ u(P) ∪ L`. -/
theorem setOf_mem_image_eq_image {A A' E E' : Type*} {P : Set A} {P' : Set A'} {f : A → A'}
    {f' : A' → A} {u : A → E} {u' : A' → E'} {m : E → E'} {D L : Set E}
    (hf : MapsTo f P P') (hf' : MapsTo f' P' P) (hff' : ∀ b ∈ P', f (f' b) = b)
    (hcomm : ∀ a ∈ P, u' (f a) = m (u a)) (huD : MapsTo u P D) (hLD : L ⊆ D)
    (hm : InjOn m D) :
    {b | b ∈ P' ∧ u' b ∈ m '' L} = f '' {a | a ∈ P ∧ u a ∈ L} := by
  ext b
  constructor
  · rintro ⟨hb, e, he, hbe⟩
    refine ⟨f' b, ⟨hf' hb, ?_⟩, hff' b hb⟩
    have h1 : m (u (f' b)) = m e := by rw [← hcomm _ (hf' hb), hff' b hb, hbe]
    rw [hm (huD (hf' hb)) (hLD he) h1]
    exact he
  · rintro ⟨a, ⟨ha, haL⟩, rfl⟩
    exact ⟨hf ha, u a, haL, (hcomm a ha).symm⟩

/-- The same for frames `Fin n → ·`. -/
theorem setOf_frames_eq_image {A A' E E' : Type*} {P : Set A} {P' : Set A'} {f : A → A'}
    {f' : A' → A} {u : A → E} {u' : A' → E'} {m : E → E'} {D : Set E} {n : ℕ}
    {L : Set (Fin n → E)}
    (hf : MapsTo f P P') (hf' : MapsTo f' P' P) (hff' : ∀ b ∈ P', f (f' b) = b)
    (hcomm : ∀ a ∈ P, u' (f a) = m (u a)) (huD : MapsTo u P D) (hLD : ∀ v ∈ L, ∀ i, v i ∈ D)
    (hm : InjOn m D) :
    {v : Fin n → A' | (∀ i, v i ∈ P') ∧ u' ∘ v ∈ (fun w => m ∘ w) '' L} =
      (fun w => f ∘ w) '' {w | (∀ i, w i ∈ P) ∧ u ∘ w ∈ L} :=
  setOf_mem_image_eq_image (P := {w : Fin n → A | ∀ i, w i ∈ P})
    (P' := {v : Fin n → A' | ∀ i, v i ∈ P'}) (D := {w : Fin n → E | ∀ i, w i ∈ D})
    (fun _ hw i => hf (hw i)) (fun _ hv i => hf' (hv i))
    (fun v hv => funext fun i => hff' (v i) (hv i))
    (fun w hw => funext fun i => hcomm (w i) (hw i)) (fun _ hw i => huD (hw i)) hLD
    (fun _ hw _ hw' h => funext fun i => hm (hw i) (hw' i) (congrFun h i))

/-- A finitely supported function with non-negative values whose push-forward vanishes is `0`. -/
theorem eq_zero_of_mapDomain_eq_zero_of_nonneg {α β : Type*} {w : α →₀ ℚ}
    (hw : ∀ a, 0 ≤ w a) (f : α → β) (h : w.mapDomain f = 0) : w = 0 := by
  classical
  have hnn : ∀ a' b, 0 ≤ (Finsupp.single (f a') (w a')) b :=
    fun a' b => by rw [Finsupp.single_apply]; split_ifs; exacts [hw a', le_rfl]
  ext a
  have key : w a ≤ (w.mapDomain f) (f a) := by
    rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
    by_cases ha : a ∈ w.support
    · calc w a = (Finsupp.single (f a) (w a)) (f a) := by rw [Finsupp.single_eq_same]
        _ ≤ _ := Finset.single_le_sum (f := fun a' => (Finsupp.single (f a') (w a')) (f a))
          (fun a' _ => hnn a' _) ha
    · rw [Finsupp.notMem_support_iff.1 ha]
      exact Finset.sum_nonneg fun a' _ => hnn a' _
  rw [h, Finsupp.coe_zero, Pi.zero_apply] at key
  exact le_antisymm key (hw a)

/-! ### Chapter 17: smooth objects and `Tφ` -/

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} {S : C.PolyfoldConstruction}

/-- `Ψ(q)` is smooth iff `q ∈ O_∞`. -/
theorem isSmoothObj_obj_iff (Ψ : S.Unif) (q : Ψ.1.O) :
    S.IsSmoothObj (Ψ.1.obj q) ↔ q ∈ Ψ.1.P.smoothSet := by
  rw [IsSmoothObj, MPolyfold.smoothSet, mem_iInter]
  exact forall_congr' fun m => hasRegularity_iff Ψ (C.toGroupoidStr.isomorphic_refl _) m

/-- `Γ(x)` is smooth iff `x ∈ (X_Ψ)_∞`. -/
theorem isSmoothObj_model_iff {ι : Type u} {Φ : ι → S.Unif} (x : S.ModelObj Φ) :
    S.IsSmoothObj ((S.modelFunctor Φ).obj x) ↔ x ∈ (S.modelEpGroupoid Φ).PObj.smoothSet :=
  (isSmoothObj_obj_iff (Φ x.1) x.2).trans (mem_smoothSet_model_iff x.1 x.2).symm

theorem tangentObj_of_isSmoothObj (hU : S.HasUniformizers) {α : C.Obj} (h : S.IsSmoothObj α) :
    S.TangentObj α :=
  ⟨h 1, hU α⟩

/-- `Tφ⁻¹ ∘ Tφ = id` on `T_{s φ}C`. -/
theorem tcMove_inv_tcMove (hU : S.HasUniformizers) {φ : C.Mor} {e : S.TangentCatObj}
    (hs : C.toGroupoidStr.src φ = e.base) :
    S.tcMove (C.toGroupoidStr.inv φ) (S.tcMove φ e) = e := by
  have h0 : S.TangentObj (C.toGroupoidStr.src φ) := by rw [hs]; exact e.isObj
  have ht : S.TangentObj (C.toGroupoidStr.tgt φ) := tangentObj_tgt_of_src hU h0
  have ht' : S.TangentObj (C.toGroupoidStr.tgt (C.toGroupoidStr.inv φ)) := by
    rw [C.toGroupoidStr.tgt_inv]; exact h0
  rw [tcMove_tcMove hs ht (C.toGroupoidStr.src_inv φ) ht', C.toGroupoidStr.inv_comp, hs]
  exact (tcMove_eq e.unitMor).trans e.tgt_unitMor

/-- `Tφ` is injective on `T_{s φ}C`. -/
theorem tcMove_injOn (hU : S.HasUniformizers) (φ : C.Mor) :
    InjOn (S.tcMove φ) {e | e.base = C.toGroupoidStr.src φ} := fun e he e' he' h => by
  rw [← tcMove_inv_tcMove hU he.symm, h, tcMove_inv_tcMove hU he'.symm]

/-- `T1_α = id` on `T_αC`. -/
theorem tcMove_unit (e : S.TangentCatObj) : S.tcMove (C.toGroupoidStr.unit e.base) e = e :=
  (tcMove_eq e.unitMor).trans e.tgt_unitMor

/-! ### The pull-back `TΨ^*T̂` along a uniformizer -/

section UnifPull

variable (hU : S.HasUniformizers)

variable (S) in
/-- The preimage of `L̂ ⊂ T_{Ψ(q)}C` under `TΨ(q) : T_qO → T_{Ψ(q)}C` (Remark 17.5.9; the
uniformizer version of `orTCPull`). -/
def unifOrPull (Ψ : S.Unif) (q : Ψ.1.O) (g : S.OrTC) : Ψ.1.P.OrTangent :=
  ⟨g.dim, {k | basePt Ψ k = q ∧ S.tangentUnifObj hU Ψ k ∈ g.carrier},
    {v | (∀ i, basePt Ψ (v i) = q) ∧ S.tangentUnifObj hU Ψ ∘ v ∈ g.frames}⟩

variable (S) in
/-- **The pull-back `TΨ^*T̂`** (2021 Remark 17.5.9, p. 817): `(TΨ^*T̂)(q) = TΨ(q)⁻¹(T̂(Ψ(q)))`, the
preimages of the oriented subsets of `T̂(Ψ(q))` under `TΨ(q)`. -/
def unifSectionPull (Ψ : S.Unif) (T : C.Obj → S.OrTC →₀ ℚ) (q : Ψ.1.O) :
    Ψ.1.P.OrTangent →₀ ℚ :=
  (T (Ψ.1.obj q)).mapDomain (S.unifOrPull hU Ψ q)

variable {ι : Type u} {Φ : ι → S.Unif}

/-- `TΓ^*L̂` at `(λ, q)` is the image of `TΨ_λ^*L̂` under `Tι_λ`, `ι_λ = Sigma.mk λ`. -/
theorem orTCPull_mk (i : ι) (q : (Φ i).1.O) (g : S.OrTC) :
    S.orTCPull hU Φ ⟨i, q⟩ g = (S.unifOrPull hU (Φ i) q g).map (modelTObjMk Φ i) := by
  have hd := MPolyfold.isScDiffeoOn_sigmaMk (fun i => (Φ i).1.P) i q
  have hT : MPolyfold.tangentMapOn hd.isScSmoothOn = modelTObjMk Φ i :=
    MPolyfold.tangentMapOn_univ _
  have hmem : ∀ b : (S.modelEpGroupoid Φ).PObj.TangentSpace,
      (S.modelEpGroupoid Φ).PObj.levelVal 1 ((S.modelEpGroupoid Φ).PObj.tangentProj b) = ⟨i, q⟩ →
      b ∈ (S.modelEpGroupoid Φ).PObj.tangentPreimage (range (Sigma.mk i)) := fun b hb => by
    change (S.modelEpGroupoid Φ).PObj.levelVal 1 ((S.modelEpGroupoid Φ).PObj.tangentProj b) ∈
      range (Sigma.mk i)
    rw [hb]; exact mem_range_self q
  have hf : MapsTo (modelTObjMk Φ i) {k | basePt (Φ i) k = q}
      {b | (S.modelEpGroupoid Φ).PObj.levelVal 1 ((S.modelEpGroupoid Φ).PObj.tangentProj b) =
        ⟨i, q⟩} := fun k hk => by
    change _ = _
    rw [basePt_modelTObjMk]
    exact congrArg (Sigma.mk i) hk
  have hf' : MapsTo (MPolyfold.tangentMapOn hd.isScSmoothOn_inv)
      {b | (S.modelEpGroupoid Φ).PObj.levelVal 1 ((S.modelEpGroupoid Φ).PObj.tangentProj b) =
        ⟨i, q⟩} {k | basePt (Φ i) k = q} := fun b hb => by
    change (Φ i).1.P.levelVal 1 ((Φ i).1.P.tangentProj _) = q
    rw [MPolyfold.levelVal_tangentProj_tangentMapOn hd.isScSmoothOn_inv (hmem b hb)]
    have hb' : (MPolyfold.sigma fun i => (Φ i).1.P).levelVal 1
        ((MPolyfold.sigma fun i => (Φ i).1.P).tangentProj b) = ⟨i, q⟩ := hb
    rw [hb']
    exact sigmaProj_mk (X := fun i => (Φ i).1.O) i q q
  have hff' : ∀ b ∈ {b : (S.modelEpGroupoid Φ).PObj.TangentSpace |
      (S.modelEpGroupoid Φ).PObj.levelVal 1 ((S.modelEpGroupoid Φ).PObj.tangentProj b) = ⟨i, q⟩},
      modelTObjMk Φ i (MPolyfold.tangentMapOn hd.isScSmoothOn_inv b) = b := fun b hb => by
    rw [← hT]
    exact hd.tangent.right_inv b (hmem b hb)
  have hcomm : ∀ k ∈ {k | basePt (Φ i) k = q},
      S.tangentModelObj hU Φ (modelTObjMk Φ i k) = id (S.tangentUnifObj hU (Φ i) k) :=
    fun k _ => tangentModelObj_mk hU i k
  have h1 := setOf_mem_image_eq_image hf hf' hff' hcomm (mapsTo_univ _ _) (subset_univ g.carrier)
    (injOn_id _)
  have h2 := setOf_frames_eq_image (L := g.frames) hf hf' hff' hcomm (mapsTo_univ _ _)
    (fun _ _ _ => mem_univ _) (injOn_id _)
  rw [image_id] at h1
  simp only [Function.id_comp, image_id'] at h2
  simp only [orTCPull, unifOrPull, MPolyfold.OrTangent.map]
  congr 1

/-- **`TΓ^*T̂` on a summand**: `(TΓ^*T̂)(λ, q) = Tι_λ((TΨ_λ^*T̂)(q))`. -/
theorem sectionPull_mk (T : C.Obj → S.OrTC →₀ ℚ) (i : ι) (q : (Φ i).1.O) :
    S.sectionPull hU Φ T ⟨i, q⟩ =
      (S.unifSectionPull hU (Φ i) T q).mapDomain (MPolyfold.OrTangent.map (modelTObjMk Φ i)) := by
  rw [sectionPull, unifSectionPull, ← Finsupp.mapDomain_comp]
  exact Finsupp.mapDomain_congr fun g _ => orTCPull_mk hU i q g

variable {Θ : C.Obj → ℚ} {T : C.Obj → S.OrTC →₀ ℚ}

/-- **(9.9) from a summand to the model**: an oriented local representation of `TΨ_λ^*T̂` at `q`
for `Θ ∘ Ψ_λ` gives one of `TΓ^*T̂` at `(λ, q)` for `Γ^*Θ` (moved by `ι_λ = Sigma.mk λ`). -/
theorem hasOrientedRepAt_model_of_unif (i : ι) (q : (Φ i).1.O)
    (h : (Φ i).1.ep.HasOrientedRepAt (Θ ∘ (Φ i).1.obj) (S.unifSectionPull hU (Φ i) T) q) :
    (S.modelEpGroupoid Φ).HasOrientedRepAt (S.modelPull Φ Θ) (S.sectionPull hU Φ T) ⟨i, q⟩ := by
  obtain ⟨B, hB⟩ := h
  have hd := MPolyfold.isScDiffeoOn_sigmaMk (fun i => (Φ i).1.P) i q
  refine ⟨B.mapDiffeo (Y := S.modelEpGroupoid Φ) hd (mem_univ q) rfl (fun _ _ => rfl),
    fun y hy hys => ?_⟩
  rw [B.orientedSum_mapDiffeo (Y := S.modelEpGroupoid Φ) hd (mem_univ q) rfl (fun _ _ => rfl) hy]
  obtain ⟨⟨z, rfl⟩, hzU, -⟩ := hy
  have hz : sigmaProj (X := fun i => (Φ i).1.O) i q ⟨i, z⟩ = z :=
    sigmaProj_mk (X := fun i => (Φ i).1.O) i q z
  have hzU' : z ∈ B.U := hz ▸ hzU
  have hzs : z ∈ (Φ i).1.P.smoothSet := (mem_smoothSet_model_iff i z).1 hys
  have hT : MPolyfold.tangentMapOn hd.isScSmoothOn = modelTObjMk Φ i :=
    MPolyfold.tangentMapOn_univ _
  rw [sectionPull_mk, hB z hzU' hzs]
  simp only [hz]
  exact congrArg (fun f => Finsupp.mapDomain (MPolyfold.OrTangent.map f) (B.orientedSum z)) hT.symm

/-- **(9.9) from the model to a summand**: an oriented local representation of `TΓ^*T̂` at
`(λ, q)` for `Γ^*Θ` gives one of `TΨ_λ^*T̂` at `q` for `Θ ∘ Ψ_λ` (moved by `ι_λ⁻¹`). -/
theorem hasOrientedRepAt_unif_of_model (i : ι) (q : (Φ i).1.O)
    (h : (S.modelEpGroupoid Φ).HasOrientedRepAt (S.modelPull Φ Θ) (S.sectionPull hU Φ T)
      ⟨i, q⟩) :
    (Φ i).1.ep.HasOrientedRepAt (Θ ∘ (Φ i).1.obj) (S.unifSectionPull hU (Φ i) T) q := by
  obtain ⟨B, hB⟩ := h
  have hd0 := MPolyfold.isScDiffeoOn_sigmaMk (fun i => (Φ i).1.P) i q
  have hd := hd0.symm
  have hΘ' : ∀ u ∈ range (S.objMk Φ i),
      (Θ ∘ (Φ i).1.obj) (sigmaProj i q u) = S.modelPull Φ Θ u := by
    rintro _ ⟨v, rfl⟩
    rw [sigmaProj_mk]
    rfl
  have hq : sigmaProj (X := fun i => (Φ i).1.O) i q ⟨i, q⟩ = q :=
    sigmaProj_mk (X := fun i => (Φ i).1.O) i q q
  refine ⟨B.mapDiffeo (Y := (Φ i).1.ep) hd (mem_range_self q) hq hΘ', fun z hz hzs => ?_⟩
  rw [B.orientedSum_mapDiffeo (Y := (Φ i).1.ep) hd (mem_range_self q) hq hΘ' hz]
  have hzU : (⟨i, z⟩ : S.ModelObj Φ) ∈ B.U := hz.2.1
  rw [← hB ⟨i, z⟩ hzU ((mem_smoothSet_model_iff i z).2 hzs), sectionPull_mk,
    ← Finsupp.mapDomain_comp]
  have hid : MPolyfold.tangentMapOn hd.isScSmoothOn ∘ modelTObjMk Φ i = id := by
    have hT0 : MPolyfold.tangentMapOn hd0.isScSmoothOn = modelTObjMk Φ i :=
      MPolyfold.tangentMapOn_univ _
    funext k
    change MPolyfold.tangentMapOn hd.isScSmoothOn (modelTObjMk Φ i k) = k
    rw [← hT0]
    exact hd0.tangent.left_inv k (mem_univ _)
  conv_lhs => rw [← Finsupp.mapDomain_id (v := S.unifSectionPull hU (Φ i) T z)]
  refine Finsupp.mapDomain_congr fun g _ => ?_
  rw [Function.comp_apply, MPolyfold.OrTangent.map_map]
  exact (MPolyfold.OrTangent.map_id g).symm.trans
    (congrArg (fun f => MPolyfold.OrTangent.map f g) hid.symm)

/-- **`TΓ^*` commutes with morphisms**: for `ψ : x → y` in `X_Ψ` and `L̂ ⊂ T_{Γ(x)}C`,
`TΓ(y)⁻¹(T(Γψ)(L̂)) = Tψ(TΓ(x)⁻¹(L̂))` (`TΓ ∘ Tψ = T(Γψ) ∘ TΓ`, and `T(Γψ)` is injective). -/
theorem orTCPull_move {ψ : S.ModelMor Φ} (hψ : ψ ∈ (S.modelEpGroupoid Φ).PMor.levelSet 1)
    {g : S.OrTC}
    (hg : (∀ e ∈ g.carrier, e.base = (S.modelFunctor Φ).obj ((S.modelEpGroupoid Φ).src ψ)) ∧
      ∀ v ∈ g.frames, ∀ j, v j ∈ g.carrier) :
    S.orTCPull hU Φ ((S.modelEpGroupoid Φ).tgt ψ) (OrTC.move S ((S.modelFunctor Φ).mor ψ) g) =
      (S.orTCPull hU Φ ((S.modelEpGroupoid Φ).src ψ) g).push
        ((S.modelEpGroupoid Φ).tangentMor ψ) := by
  set X := S.modelEpGroupoid Φ
  set χ := (S.modelFunctor Φ).mor ψ
  have hψi : X.inv ψ ∈ X.PMor.levelSet 1 := by
    rw [← X.mem_levelSet_src_iff, X.src_inv, X.mem_levelSet_tgt_iff]; exact hψ
  have hf : MapsTo (X.tangentMor ψ)
      {a | X.PObj.levelVal 1 (X.PObj.tangentProj a) = X.src ψ}
      {b | X.PObj.levelVal 1 (X.PObj.tangentProj b) = X.tgt ψ} := fun a ha =>
    X.levelVal_tangentProj_tangentMor hψ ha
  have hf' : MapsTo (X.tangentMor (X.inv ψ))
      {b | X.PObj.levelVal 1 (X.PObj.tangentProj b) = X.tgt ψ}
      {a | X.PObj.levelVal 1 (X.PObj.tangentProj a) = X.src ψ} := fun b hb =>
    (X.levelVal_tangentProj_tangentMor hψi
      ((show X.PObj.levelVal 1 (X.PObj.tangentProj b) = X.tgt ψ from hb).trans
        (X.src_inv ψ).symm)).trans (X.tgt_inv ψ)
  have hff' : ∀ b ∈ {b | X.PObj.levelVal 1 (X.PObj.tangentProj b) = X.tgt ψ},
      X.tangentMor ψ (X.tangentMor (X.inv ψ) b) = b := fun b hb =>
    X.tangentMor_tangentMor_inv hψ hb
  have hcomm : ∀ a ∈ {a | X.PObj.levelVal 1 (X.PObj.tangentProj a) = X.src ψ},
      S.tangentModelObj hU Φ (X.tangentMor ψ a) = S.tcMove χ (S.tangentModelObj hU Φ a) :=
    fun a ha => tangentModelObj_tangentMor hU ha
  have huD : MapsTo (S.tangentModelObj hU Φ)
      {a | X.PObj.levelVal 1 (X.PObj.tangentProj a) = X.src ψ}
      {e | e.base = C.toGroupoidStr.src χ} := fun a ha =>
    (tangentModelObj_base hU a).trans
      ((congrArg _ (show X.PObj.levelVal 1 (X.PObj.tangentProj a) = X.src ψ from ha)).trans
        ((S.modelFunctor Φ).src_mor ψ).symm)
  have hLD : g.carrier ⊆ {e | e.base = C.toGroupoidStr.src χ} := fun e he =>
    (hg.1 e he).trans ((S.modelFunctor Φ).src_mor ψ).symm
  have h1 := setOf_mem_image_eq_image hf hf' hff' hcomm huD hLD (tcMove_injOn hU χ)
  have h2 := setOf_frames_eq_image (L := g.frames) hf hf' hff' hcomm huD
    (fun v hv j => hLD (hg.2 v hv j)) (tcMove_injOn hU χ)
  simp only [orTCPull, OrTC.move, MPolyfold.OrTangent.push]
  congr 1

/-- **Naturality of `TΓ^*T̂`** (the second condition of Definition 9.3.2 for the pull-back): if
`T̂` takes values in `Gr̂` and is natural on `C`, then `Tψ_*((TΓ^*T̂)(x)) = (TΓ^*T̂)(y)` for every
morphism `ψ : x → y` of `X_Ψ` with `x` smooth. -/
theorem grHatPush_sectionPull (hmem : ∀ α, S.IsSmoothObj α → T α ∈ S.GrHatC α)
    (hnat : ∀ χ : C.Mor, S.IsSmoothObj (C.toGroupoidStr.src χ) →
      T (C.toGroupoidStr.tgt χ) = S.grHatPushC χ (T (C.toGroupoidStr.src χ)))
    (ψ : S.ModelMor Φ) (hs : (S.modelEpGroupoid Φ).src ψ ∈ (S.modelEpGroupoid Φ).PObj.smoothSet) :
    (S.modelEpGroupoid Φ).grHatPush ψ (S.sectionPull hU Φ T ((S.modelEpGroupoid Φ).src ψ)) =
      S.sectionPull hU Φ T ((S.modelEpGroupoid Φ).tgt ψ) := by
  set X := S.modelEpGroupoid Φ
  set χ := (S.modelFunctor Φ).mor ψ
  have hψ : ψ ∈ X.PMor.levelSet 1 := (X.mem_levelSet_src_iff ψ 1).1 (mem_iInter.1 hs 1)
  have hsm : S.IsSmoothObj ((S.modelFunctor Φ).obj (X.src ψ)) := (isSmoothObj_model_iff _).2 hs
  have hsm' : S.IsSmoothObj (C.toGroupoidStr.src χ) := by
    rw [(S.modelFunctor Φ).src_mor ψ]; exact hsm
  have ht : T ((S.modelFunctor Φ).obj (X.tgt ψ)) =
      S.grHatPushC χ (T ((S.modelFunctor Φ).obj (X.src ψ))) := by
    have h := hnat χ hsm'
    rw [(S.modelFunctor Φ).tgt_mor ψ, (S.modelFunctor Φ).src_mor ψ] at h
    exact h
  rw [sectionPull, sectionPull, ht, grHatPushC, EpGroupoid.grHatPush, ← Finsupp.mapDomain_comp,
    ← Finsupp.mapDomain_comp]
  refine Finsupp.mapDomain_congr fun g hg => ?_
  have hg' := (hmem _ hsm).2 g hg
  exact (orTCPull_move hU hψ hg').symm

section UnifNatural

variable {Ψ : S.Unif} (hc : Continuous (S.hat Ψ))

include hc in
/-- `TΨ(T(g ∗ ·)(k)) = T(Ψ(g, q))(TΨ(k))` for `k ∈ T_qO`, when `Ψ̂` is continuous (Lemma 17.2.10 on
morphisms; `not_lemma_17_2_10` shows that it does not hold as we read it without that
condition). -/
theorem tangentUnifObj_tangentMor {g : Ψ.1.G} {q : Ψ.1.O}
    (hq : (g, q) ∈ Ψ.1.ep.PMor.levelSet 1) {a : Ψ.1.P.TangentSpace} (ha : basePt Ψ a = q) :
    S.tangentUnifObj hU Ψ (Ψ.1.ep.tangentMor (g, q) a) =
      S.tcMove (Ψ.1.mor (g, q)) (S.tangentUnifObj hU Ψ a) := by
  have h1 : Ψ.1.ep.tangentMor (g, q) a = MPolyfold.tangentMap (Ψ.1.smooth_smul g) a :=
    EpGroupoid.Examples.tangentMor_actionEpGroupoid Ψ.1.smooth_smul hq ha
  have h2 := tcMove_eq (S.tangentUnifMor hU Ψ (ULift.up g, a))
  rw [tangentUnifMor_tgt_of_continuous hU Ψ hc] at h2
  change S.tcMove (Ψ.1.mor (g, basePt Ψ a)) (S.tangentUnifObj hU Ψ a) = _ at h2
  rw [ha] at h2
  rw [h1, h2]
  rfl

include hc in
/-- **`TΨ^*` commutes with the morphisms of `G ⋉ O`** (for continuous `Ψ̂`):
`TΨ(g ∗ q)⁻¹(T(Ψ(g, q))(L̂)) = T(g ∗ ·)(TΨ(q)⁻¹(L̂))`. -/
theorem unifOrPull_move {g : Ψ.1.G} {q : Ψ.1.O} (hq : (g, q) ∈ Ψ.1.ep.PMor.levelSet 1)
    {L : S.OrTC}
    (hL : (∀ e ∈ L.carrier, e.base = Ψ.1.obj q) ∧ ∀ v ∈ L.frames, ∀ j, v j ∈ L.carrier) :
    S.unifOrPull hU Ψ (g • q) (OrTC.move S (Ψ.1.mor (g, q)) L) =
      (S.unifOrPull hU Ψ q L).push (Ψ.1.ep.tangentMor (g, q)) := by
  set X := Ψ.1.ep
  set χ := Ψ.1.mor (g, q)
  have hqi : X.inv (g, q) ∈ X.PMor.levelSet 1 := by
    rw [← X.mem_levelSet_src_iff, X.src_inv, X.mem_levelSet_tgt_iff]; exact hq
  have hf : MapsTo (X.tangentMor (g, q)) {k | basePt Ψ k = q} {k | basePt Ψ k = g • q} :=
    fun a ha => X.levelVal_tangentProj_tangentMor hq ha
  have hf' : MapsTo (X.tangentMor (X.inv (g, q))) {k | basePt Ψ k = g • q}
      {k | basePt Ψ k = q} := fun b hb =>
    X.levelVal_tangentProj_tangentMor hqi
      ((show basePt Ψ b = g • q from hb).trans (X.src_inv (g, q)).symm) |>.trans
      (X.tgt_inv (g, q))
  have hff' : ∀ b ∈ {k | basePt Ψ k = g • q},
      X.tangentMor (g, q) (X.tangentMor (X.inv (g, q)) b) = b := fun b hb =>
    X.tangentMor_tangentMor_inv hq hb
  have hcomm : ∀ a ∈ {k | basePt Ψ k = q},
      S.tangentUnifObj hU Ψ (X.tangentMor (g, q) a) = S.tcMove χ (S.tangentUnifObj hU Ψ a) :=
    fun a ha => tangentUnifObj_tangentMor hU hc hq ha
  have huD : MapsTo (S.tangentUnifObj hU Ψ) {k | basePt Ψ k = q}
      {e | e.base = C.toGroupoidStr.src χ} := fun a ha =>
    (tangentUnifObj_base hU Ψ a).trans
      ((congrArg Ψ.1.obj (show basePt Ψ a = q from ha)).trans (Ψ.1.src_mor (g, q)).symm)
  have hLD : L.carrier ⊆ {e | e.base = C.toGroupoidStr.src χ} := fun e he =>
    (hL.1 e he).trans (Ψ.1.src_mor (g, q)).symm
  have h1 := setOf_mem_image_eq_image hf hf' hff' hcomm huD hLD (tcMove_injOn hU χ)
  have h2 := setOf_frames_eq_image (L := L.frames) hf hf' hff' hcomm huD
    (fun v hv j => hLD (hL.2 v hv j)) (tcMove_injOn hU χ)
  simp only [unifOrPull, OrTC.move, MPolyfold.OrTangent.push]
  congr 1

include hc in
/-- **Naturality of `TΨ^*T̂` on `G ⋉ O`** (for continuous `Ψ̂`): if `T̂` takes values in `Gr̂` and
is natural on `C`, then `T(g ∗ ·)_*((TΨ^*T̂)(q)) = (TΨ^*T̂)(g ∗ q)` for smooth `q`. -/
theorem grHatPush_unifSectionPull {T : C.Obj → S.OrTC →₀ ℚ}
    (hmem : ∀ α, S.IsSmoothObj α → T α ∈ S.GrHatC α)
    (hnat : ∀ χ : C.Mor, S.IsSmoothObj (C.toGroupoidStr.src χ) →
      T (C.toGroupoidStr.tgt χ) = S.grHatPushC χ (T (C.toGroupoidStr.src χ)))
    (φ : Ψ.1.G × Ψ.1.O) (hs : Ψ.1.ep.src φ ∈ Ψ.1.ep.PObj.smoothSet) :
    Ψ.1.ep.grHatPush φ (S.unifSectionPull hU Ψ T (Ψ.1.ep.src φ)) =
      S.unifSectionPull hU Ψ T (Ψ.1.ep.tgt φ) := by
  obtain ⟨g, q⟩ := φ
  set X := Ψ.1.ep
  have hq : (g, q) ∈ X.PMor.levelSet 1 := (X.mem_levelSet_src_iff (g, q) 1).1 (mem_iInter.1 hs 1)
  have hsm : S.IsSmoothObj (Ψ.1.obj q) := (isSmoothObj_obj_iff Ψ q).2 hs
  have hsm' : S.IsSmoothObj (C.toGroupoidStr.src (Ψ.1.mor (g, q))) := by
    rw [Ψ.1.src_mor]; exact hsm
  have ht : T (Ψ.1.obj (g • q)) = S.grHatPushC (Ψ.1.mor (g, q)) (T (Ψ.1.obj q)) := by
    have h := hnat _ hsm'
    rw [Ψ.1.tgt_mor, Ψ.1.src_mor] at h
    exact h
  change Finsupp.mapDomain _ ((T (Ψ.1.obj q)).mapDomain (S.unifOrPull hU Ψ q)) =
    (T (Ψ.1.obj (g • q))).mapDomain (S.unifOrPull hU Ψ (g • q))
  rw [ht, grHatPushC, ← Finsupp.mapDomain_comp]
  refine Finsupp.mapDomain_comp.symm.trans (Finsupp.mapDomain_congr fun L hL => ?_)
  exact (unifOrPull_move hU hc hq ((hmem _ hsm).2 L hL)).symm

end UnifNatural

/-! ### Vanishing off `supp(Θ)` -/

/-- **`TΘ(α) = 0` off `supp(Θ)`**: `TΘ(α) = Tφ(TΓ(TΓ^*Θ(x)))` with `Θ(Γ(x)) = Θ(α) = 0`. -/
theorem branchedTangentSection_eq_zero (hΘ : S.IsBranchedSubcategory Θ) {α : C.Obj}
    (hα : S.TangentObj α) (h : ¬ 0 < Θ α) : S.branchedTangentSection hU Θ α = 0 := by
  obtain ⟨x, φ, hs, ht⟩ := (GroupoidFunctor.essSurj_iff _).1
    (S.modelFunctor_essSurj (S.tangentCover hU).isCoveringFamily) α
  rw [(proposition_17_5_7 hU hΘ).2.1 _ α hα x φ hs ht]
  have hx : x ∉ EpGroupoid.supp (S.modelPull (S.tangentCover hU).Ψ Θ) := fun hx => by
    have h1 : Θ (C.toGroupoidStr.src φ) = Θ (C.toGroupoidStr.tgt φ) := hΘ.isFunctorial φ
    rw [hs, ht] at h1
    exact h (h1 ▸ hx)
  rw [(S.modelEpGroupoid _).tangentValue_eq_zero hx, modelGrPush]
  exact Finsupp.mapDomain_zero

/-- **`T̂Θ(α) = 0` off `supp(Θ)`** for a section of `Gr̂(C)` lifting `TΘ` (the weights are
non-negative and `f(T̂Θ(α)) = TΘ(α) = 0`). -/
theorem eq_zero_of_not_mem_supp (hΘ : S.IsBranchedSubcategory Θ)
    (hmem : ∀ α, S.IsSmoothObj α → T α ∈ S.GrHatC α)
    (hlifts : ∀ α, S.IsSmoothObj α → S.grForgetC (T α) = S.branchedTangentSection hU Θ α)
    {α : C.Obj} (hα : S.IsSmoothObj α) (h : ¬ 0 < Θ α) : T α = 0 :=
  eq_zero_of_mapDomain_eq_zero_of_nonneg (hmem α hα).1 OrTC.carrier
    ((hlifts α hα).trans
      (branchedTangentSection_eq_zero hU hΘ (tangentObj_of_isSmoothObj hU hα) h))

/-- **Proposition 17.5.7 through a uniformizer**: `TΘ(α) = Tφ(TΨ(T(Θ ∘ Ψ)(q)))` for every
uniformizer `Ψ` of `F` and `φ : Ψ(q) → α` (the covering family `tangentCover hU ⊕ {Ψ}`). -/
theorem branchedTangentSection_eq_unif (hΘ : S.IsBranchedSubcategory Θ) (Ψ : S.Unif) (q : Ψ.1.O)
    {α : C.Obj} (hα : S.TangentObj α) {φ : C.Mor} (hs : C.toGroupoidStr.src φ = Ψ.1.obj q)
    (ht : C.toGroupoidStr.tgt φ = α) :
    S.branchedTangentSection hU Θ α = (Ψ.1.ep.tangentValue (Θ ∘ Ψ.1.obj) q).mapDomain
      (image (S.tcMove φ ∘ S.tangentUnifObj hU Ψ)) := by
  let c := S.tangentCover hU
  let c' : S.CoveringFamily :=
    ⟨c.ι ⊕ PUnit.{u + 1}, Sum.elim c.Ψ fun _ => Ψ, IsCoveringFamily.of_comp (σ := Sum.inl) c.cover⟩
  have h1 := (proposition_17_5_7 hU hΘ).2.1 c' α hα ⟨Sum.inr PUnit.unit, q⟩ φ hs ht
  have h2 := tangentValue_model_mk (Ψ := c'.Ψ) hΘ (Sum.inr PUnit.unit) q
  refine h1.trans ((congrArg (Finsupp.mapDomain _) h2).trans ?_)
  refine Finsupp.mapDomain_comp.symm.trans (Finsupp.mapDomain_congr fun L _ => ?_)
  refine (image_image _ _ L).trans (image_congr fun k _ => ?_)
  exact congrArg (S.tcMove φ) (tangentModelObj_mk hU (Ψ := c'.Ψ) (Sum.inr PUnit.unit) k)

/-! ### From the uniformizers to the model -/

/-- **Definition 9.3.2 for `TΓ^*T̂Θ` on the model of any family** from the conditions on `C` and
oriented local representations (9.9) of `TΨ^*T̂Θ` for one uniformizer `Ψ` at a point over each
`α ∈ supp(Θ)`.  The representation is moved to the model of the family together with `Ψ`,
along a morphism of that model over `1_α`, and back to the summand. -/
theorem isOrientation_model_of_unif (hΘ : S.IsBranchedSubcategory Θ)
    (hmem : ∀ α, S.IsSmoothObj α → T α ∈ S.GrHatC α)
    (hnat : ∀ χ : C.Mor, S.IsSmoothObj (C.toGroupoidStr.src χ) →
      T (C.toGroupoidStr.tgt χ) = S.grHatPushC χ (T (C.toGroupoidStr.src χ)))
    (hlifts : ∀ α, S.IsSmoothObj α → S.grForgetC (T α) = S.branchedTangentSection hU Θ α)
    (hunif : ∀ α, 0 < Θ α → ∃ (Ψ : S.Unif) (q : Ψ.1.O), Ψ.1.obj q = α ∧
      Ψ.1.ep.HasOrientedRepAt (Θ ∘ Ψ.1.obj) (S.unifSectionPull hU Ψ T) q)
    (Φ : ι → S.Unif) :
    (S.modelEpGroupoid Φ).IsOrientation (S.modelPull Φ Θ) (S.sectionPull hU Φ T) := by
  refine EpGroupoid.isOrientation_of_hasOrientedRepAt
    (fun ψ hs => grHatPush_sectionPull hU hmem hnat ψ hs) (fun x hx hxs => ?_) (fun x hx => ?_)
  · rw [sectionPull, eq_zero_of_not_mem_supp hU hΘ hmem hlifts ((isSmoothObj_model_iff x).2 hx)
      hxs, Finsupp.mapDomain_zero]
  · obtain ⟨i, q⟩ := x
    obtain ⟨Ψ', q', hq', hrep⟩ := hunif _ hx
    let Φ' : ι ⊕ PUnit.{u + 1} → S.Unif := Sum.elim Φ fun _ => Ψ'
    have h1 : (S.modelEpGroupoid Φ').HasOrientedRepAt (S.modelPull Φ' Θ) (S.sectionPull hU Φ' T)
        ⟨Sum.inr PUnit.unit, q'⟩ :=
      hasOrientedRepAt_model_of_unif hU (Φ := Φ') (Sum.inr PUnit.unit) q' hrep
    obtain ⟨ψ, hψs, hψt, -⟩ := (GroupoidFunctor.full_iff _).1 (S.modelFunctor_full Φ')
      ⟨Sum.inr PUnit.unit, q'⟩ ⟨Sum.inl i, q⟩ (C.toGroupoidStr.unit ((Φ i).1.obj q))
      ((C.toGroupoidStr.src_unit _).trans hq'.symm) (C.toGroupoidStr.tgt_unit _)
    have h2 := EpGroupoid.hasOrientedRepAt_tgt (X := S.modelEpGroupoid Φ')
      (isFunctorial_modelPull hΘ.isFunctorial) (fun ψ hs => grHatPush_sectionPull hU hmem hnat ψ hs)
      (φ := ψ) (hψs ▸ h1)
    have h3 : (S.modelEpGroupoid Φ').HasOrientedRepAt (S.modelPull Φ' Θ) (S.sectionPull hU Φ' T)
        ⟨Sum.inl i, q⟩ := hψt ▸ h2
    exact hasOrientedRepAt_model_of_unif hU i q
      (hasOrientedRepAt_unif_of_model hU (Φ := Φ') (Sum.inl i) q h3)

/-! ### From the model to the uniformizers -/

/-- **(9.9) for `TΨ^*T̂Θ` from Definition 17.5.8**: for every uniformizer `Ψ` of `F` and
`q ∈ supp(Θ ∘ Ψ)`, the orientation of the pull-back to the model of `tangentCover hU ⊕ {Ψ}` gives
an oriented local representation of `TΨ^*T̂Θ` at `q`. -/
theorem hasOrientedRepAt_unif (hT : S.IsOrientationC hU Θ T) (Ψ : S.Unif) {q : Ψ.1.O}
    (hq : q ∈ EpGroupoid.supp (Θ ∘ Ψ.1.obj)) :
    Ψ.1.ep.HasOrientedRepAt (Θ ∘ Ψ.1.obj) (S.unifSectionPull hU Ψ T) q := by
  let c := S.tangentCover hU
  let c' : S.CoveringFamily :=
    ⟨c.ι ⊕ PUnit.{u + 1}, Sum.elim c.Ψ fun _ => Ψ, IsCoveringFamily.of_comp (σ := Sum.inl) c.cover⟩
  obtain ⟨B, hB⟩ := (hT.pull c').locallyOriented ⟨Sum.inr PUnit.unit, q⟩ hq
  exact hasOrientedRepAt_unif_of_model hU (Φ := c'.Ψ) (Sum.inr PUnit.unit) q ⟨B, hB⟩

/-- **The conditions of Definition 9.3.2 for `TΨ^*T̂Θ` other than naturality** (for every
uniformizer `Ψ` of `F`): values in `Gr̂`, the lift of `T(Θ ∘ Ψ)`, and (9.9). -/
theorem unif_of_isOrientationC (hΘ : S.IsBranchedSubcategory Θ) (hT : S.IsOrientationC hU Θ T)
    (Ψ : S.Unif) :
    (∀ q ∈ Ψ.1.ep.PObj.smoothSet, S.unifSectionPull hU Ψ T q ∈ Ψ.1.ep.GrHat q) ∧
    (∀ q ∈ Ψ.1.ep.PObj.smoothSet,
      Ψ.1.ep.grForget (S.unifSectionPull hU Ψ T q) = Ψ.1.ep.tangentValue (Θ ∘ Ψ.1.obj) q) ∧
    (∀ q ∈ EpGroupoid.supp (Θ ∘ Ψ.1.obj),
      Ψ.1.ep.HasOrientedRepAt (Θ ∘ Ψ.1.obj) (S.unifSectionPull hU Ψ T) q) := by
  have hzero : ∀ q ∈ Ψ.1.ep.PObj.smoothSet, q ∉ EpGroupoid.supp (Θ ∘ Ψ.1.obj) →
      S.unifSectionPull hU Ψ T q = 0 := fun q hq hqs => by
    rw [unifSectionPull, eq_zero_of_not_mem_supp hU hΘ hT.mem hT.lifts
      ((isSmoothObj_obj_iff Ψ q).2 hq) hqs, Finsupp.mapDomain_zero]
  have hloc := fun q (hq : q ∈ EpGroupoid.supp (Θ ∘ Ψ.1.obj)) => hasOrientedRepAt_unif hU hT Ψ hq
  exact ⟨fun q hq => EpGroupoid.mem_grHat_of_hasOrientedRepAt hzero hloc hq,
    fun q hq => EpGroupoid.grForget_eq_tangentValue (Ψ.1.ep.hasIndependentTangentSums _) hzero
      hloc hq, hloc⟩

/-- **`TΨ^*T̂Θ` is an orientation of `Θ ∘ Ψ`** (Definition 9.3.2) for every uniformizer `Ψ` of `F`
with continuous `Ψ̂`. -/
theorem isOrientation_unif_of_isOrientationC (hΘ : S.IsBranchedSubcategory Θ)
    (hT : S.IsOrientationC hU Θ T) (Ψ : S.Unif) (hc : Continuous (S.hat Ψ)) :
    Ψ.1.ep.IsOrientation (Θ ∘ Ψ.1.obj) (S.unifSectionPull hU Ψ T) := by
  obtain ⟨hmem, hlift, hloc⟩ := unif_of_isOrientationC hU hΘ hT Ψ
  exact ⟨hmem, fun φ hs => grHatPush_unifSectionPull hU hc hT.mem hT.natural φ hs, hlift, hloc⟩

/-- **Remark 17.5.9, "⇐"** (2021 p. 817): the condition on the pull-backs `TΓ^*T̂Θ` in
Definition 17.5.8 follows from the conditions on `C` and the condition that `TΨ^*T̂Θ` is an
orientation of `Θ ∘ Ψ` (Definition 9.3.2) for `α ∈ supp(Θ)` and `Ψ ∈ F(α)`. -/
theorem isOrientationC_of_unif (hΘ : S.IsBranchedSubcategory Θ)
    (hmem : ∀ α, S.IsSmoothObj α → T α ∈ S.GrHatC α)
    (hnat : ∀ χ : C.Mor, S.IsSmoothObj (C.toGroupoidStr.src χ) →
      T (C.toGroupoidStr.tgt χ) = S.grHatPushC χ (T (C.toGroupoidStr.src χ)))
    (hlifts : ∀ α, S.IsSmoothObj α → S.grForgetC (T α) = S.branchedTangentSection hU Θ α)
    (hunif : ∀ α, 0 < Θ α → ∀ (Ψ : C.LocalUniformizer) (hΨ : Ψ ∈ S.F α),
      Ψ.ep.IsOrientation (Θ ∘ Ψ.obj) (S.unifSectionPull hU ⟨Ψ, α, hΨ⟩ T)) :
    S.IsOrientationC hU Θ T where
  mem := hmem
  natural := hnat
  lifts := hlifts
  pull c := isOrientation_model_of_unif hU hΘ hmem hnat hlifts (fun α hα => by
    obtain ⟨Ψ, hΨ⟩ := hU α
    obtain ⟨q, hq⟩ := S.isAt α Ψ hΨ
    exact ⟨⟨Ψ, α, hΨ⟩, q, hq, (hunif α hα Ψ hΨ).locallyOriented q
      (show 0 < Θ (Ψ.obj q) from (congrArg Θ hq).symm ▸ hα)⟩) c.Ψ

/-- **Remark 17.5.9** (2021 p. 817): the part of Definition 17.5.8 requiring that `TΓ^*T̂Θ` is an
orientation of `Θ ∘ Γ` can be replaced by requiring that `TΨ^*T̂Θ` is an orientation of `Θ ∘ Ψ`
for `α ∈ supp(Θ)` and `Ψ ∈ F(α)`.  The direction "⇒" uses that the maps `Ψ̂` are continuous
(the condition `HatContinuous` under which `TΨ` is `G`-equivariant, Lemma 17.2.10;
`not_lemma_17_2_10`); the direction "⇐" is `isOrientationC_of_unif`. -/
theorem remark_17_5_9_hyp (hcont : ∀ Ψ : S.Unif, Continuous (S.hat Ψ))
    (hΘ : S.IsBranchedSubcategory Θ) :
    S.IsOrientationC hU Θ T ↔
      (∀ α, S.IsSmoothObj α → T α ∈ S.GrHatC α) ∧
      (∀ χ : C.Mor, S.IsSmoothObj (C.toGroupoidStr.src χ) →
        T (C.toGroupoidStr.tgt χ) = S.grHatPushC χ (T (C.toGroupoidStr.src χ))) ∧
      (∀ α, S.IsSmoothObj α → S.grForgetC (T α) = S.branchedTangentSection hU Θ α) ∧
      (∀ α, 0 < Θ α → ∀ (Ψ : C.LocalUniformizer) (hΨ : Ψ ∈ S.F α),
        Ψ.ep.IsOrientation (Θ ∘ Ψ.obj) (S.unifSectionPull hU ⟨Ψ, α, hΨ⟩ T)) :=
  ⟨fun hT => ⟨hT.mem, hT.natural, hT.lifts, fun α _ Ψ hΨ =>
      isOrientation_unif_of_isOrientationC hU hΘ hT ⟨Ψ, α, hΨ⟩ (hcont _)⟩,
    fun ⟨hmem, hnat, hlifts, hunif⟩ => isOrientationC_of_unif hU hΘ hmem hnat hlifts hunif⟩

end UnifPull

end GCT.PolyfoldConstruction

end Polyfold
