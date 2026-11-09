import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V11_22

/-!
Round trip for V11_22 (2021 Definition 11.3.6 and (11.10), p. 541: oriented branched
ep⁺-subgroupoids along generalized isomorphisms).

The item lists the structure `OrientedBranched` (an oriented branched ep⁺-subgroupoid **with**
Theorem 9.2.1's independence `HasIndependentTangentSums Θ` as a field) and the definitions
`OrientedBranched.push`, `OrientedBranched.pull` (vocabulary), and five theorems; `A` is the
conjunction of their types, universes at `0` (`X Y Z : EP.{0}`): `push_comp`, `pull_comp`,
`pull_push` (for `T` vanishing off `X_∞`), `EPLoc.pushTheta_pullTheta` (every functorial `Θ'`),
`EPLoc.pushSection_pullSection` (every `T' ∈ Γ(π̂_Y)`).

`B = PairsB ∧ CompB ∧ InvB` on pairs `(Θ, T)` with `Θ` branched and `T` an orientation of `Θ`
(**no independence hypothesis**), for every choice of representatives: the pushed and pulled pairs
are such pairs (Definition 11.3.6, i.e. Theorems 11.3.3, 11.3.5); the composition laws; and
`f^*f_* = id`, `f_*f^* = id` (the orientations compared on the smooth points).

* `A ⇒ B` fails because of the independence hypothesis.  `PairsB` is Theorem 11.3.5 without
  `HasIndependentTangentSums`, which the project does not have (see V11_21: it would need
  Theorem 9.2.1 (1) in general); and `A`'s `push_comp`, `pull_comp`, `pull_push` speak only of
  `OrientedBranched`, i.e. of pairs with the independence.  With the independence added to `B`'s
  hypotheses (`BInd`, implied by `B`), `A ⇒ BInd` holds (`A_to_BInd`): `PairsBInd` from the fields
  of the vocabulary `OrientedBranched.push/pull`; `CompBInd` from `push_comp`, `pull_comp`;
  `InvBInd` from `pull_push` (applied to `T` made `0` off `X_∞`, which is again an orientation
  and has the same push-forward), `EPLoc.pushTheta_pullTheta`, `EPLoc.pushSection_pullSection`;
  each moved to arbitrary representatives by the non-item `push/pullTheta_homMk`,
  `push/pullSection_homMk`.
* `B ⇒ A` fails for a genuine reason (`A` is more general there): `EPLoc.pushTheta_pullTheta`
  holds for every functorial `Θ'` and `EPLoc.pushSection_pullSection` for every section functor
  in `Γ(π̂_Y)`, while `B` speaks only of oriented branched pairs.  `push_comp`, `pull_comp`,
  `pull_push` do follow from `B` (`B_to_A_core`).
-/

namespace RoundTrip.V11_22
open Polyfold Polyfold.EPLocalization CategoryTheory

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  type_of% @Polyfold.EPLocalization.OrientedBranched.push_comp.{0} ∧
  type_of% @Polyfold.EPLocalization.OrientedBranched.pull_comp.{0} ∧
  type_of% @Polyfold.EPLocalization.OrientedBranched.pull_push.{0} ∧
  type_of% @Polyfold.EPLocalization.EPLoc.pushTheta_pullTheta.{0} ∧
  type_of% @Polyfold.EPLocalization.EPLoc.pushSection_pullSection.{0}

theorem A_holds : A :=
  ⟨@OrientedBranched.push_comp, @OrientedBranched.pull_comp, @OrientedBranched.pull_push,
    @EPLoc.pushTheta_pullTheta, @EPLoc.pushSection_pullSection⟩

/-! ### `B` with the independence hypothesis -/

/-- An oriented pair with Theorem 9.2.1's independence. -/
def IsOrientedPairInd (X : EP.{0}) (Θ : X.Obj → ℚ) (T : X.Obj → X.X.PObj.OrTangent →₀ ℚ) :
    Prop :=
  X.X.IsBranchedEpSubgroupoid Θ ∧ X.X.HasIndependentTangentSums Θ ∧ X.X.IsOrientation Θ T

def PairsBInd : Prop :=
  ∀ (X Y : EP.{0}) (f : EPLoc.of X ⟶ EPLoc.of Y), EPLoc.IsGeneralizedIso f →
    ∀ d : Diagram X Y, EPLoc.homMk d = f →
      (∀ Θ T, IsOrientedPairInd X Θ T → IsOrientedPairB Y (d.pushTheta Θ) (d.pushSection T)) ∧
      (∀ Θ' T', IsOrientedPairInd Y Θ' T' →
        IsOrientedPairB X (d.pullTheta Θ') (d.pullSection T'))

def CompBInd : Prop :=
  ∀ (X Y Z : EP.{0}) (f : EPLoc.of X ⟶ EPLoc.of Y) (g : EPLoc.of Y ⟶ EPLoc.of Z),
    EPLoc.IsGeneralizedIso f → EPLoc.IsGeneralizedIso g →
    ∀ (d : Diagram X Y) (e : Diagram Y Z) (c : Diagram X Z),
      EPLoc.homMk d = f → EPLoc.homMk e = g → EPLoc.homMk c = f ≫ g →
      (∀ Θ T, IsOrientedPairInd X Θ T →
        c.pushTheta Θ = e.pushTheta (d.pushTheta Θ) ∧
        c.pushSection T = e.pushSection (d.pushSection T)) ∧
      (∀ Θ'' T'', IsOrientedPairInd Z Θ'' T'' →
        c.pullTheta Θ'' = d.pullTheta (e.pullTheta Θ'') ∧
        c.pullSection T'' = d.pullSection (e.pullSection T''))

def InvBInd : Prop :=
  ∀ (X Y : EP.{0}) (f : EPLoc.of X ⟶ EPLoc.of Y), EPLoc.IsGeneralizedIso f →
    ∀ d d' : Diagram X Y, EPLoc.homMk d = f → EPLoc.homMk d' = f →
      (∀ Θ T, IsOrientedPairInd X Θ T →
        d'.pullTheta (d.pushTheta Θ) = Θ ∧
        ∀ x ∈ X.X.PObj.smoothSet, d'.pullSection (d.pushSection T) x = T x) ∧
      (∀ Θ' T', IsOrientedPairInd Y Θ' T' →
        d'.pushTheta (d.pullTheta Θ') = Θ' ∧
        ∀ y ∈ Y.X.PObj.smoothSet, d'.pushSection (d.pullSection T') y = T' y)

/-- `B` with the independence hypothesis. -/
def BInd : Prop := PairsBInd ∧ CompBInd ∧ InvBInd

theorem B_to_BInd (hB : B) : BInd :=
  ⟨fun X Y f hf d hd => ⟨fun Θ T h => (hB.1 X Y f hf d hd).1 Θ T ⟨h.1, h.2.2⟩,
      fun Θ' T' h => (hB.1 X Y f hf d hd).2 Θ' T' ⟨h.1, h.2.2⟩⟩,
    fun X Y Z f g hf hg d e c hd he hc =>
      ⟨fun Θ T h => (hB.2.1 X Y Z f g hf hg d e c hd he hc).1 Θ T ⟨h.1, h.2.2⟩,
        fun Θ T h => (hB.2.1 X Y Z f g hf hg d e c hd he hc).2 Θ T ⟨h.1, h.2.2⟩⟩,
    fun X Y f hf d d' hd hd' =>
      ⟨fun Θ T h => (hB.2.2 X Y f hf d d' hd hd').1 Θ T ⟨h.1, h.2.2⟩,
        fun Θ T h => (hB.2.2 X Y f hf d d' hd hd').2 Θ T ⟨h.1, h.2.2⟩⟩⟩

/-! ### Glue -/

theorem isGeneralizedIso_comp {X Y Z : EP.{0}} {f : EPLoc.of X ⟶ EPLoc.of Y}
    {g : EPLoc.of Y ⟶ EPLoc.of Z} (hf : EPLoc.IsGeneralizedIso f) (hg : EPLoc.IsGeneralizedIso g) :
    EPLoc.IsGeneralizedIso (f ≫ g) := by
  rw [EPLoc.isGeneralizedIso_iff_isIso] at hf hg ⊢
  infer_instance

theorem isEquivalence_Φ {X Y : EP.{0}} {f : EPLoc.of X ⟶ EPLoc.of Y}
    (hf : EPLoc.IsGeneralizedIso f) {d : Diagram X Y} (hd : EPLoc.homMk d = f) :
    d.Φ.IsEquivalence :=
  (EPLoc.theorem_10_3_10 d).1.1 (hd ▸ hf)

section Zero

variable {Obj Mor Obj' Mor' : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}

open scoped Classical in
/-- `T` made `0` off the smooth points. -/
noncomputable def zeroOff (X : EpGroupoid Obj Mor) (T : Obj → X.PObj.OrTangent →₀ ℚ) :
    Obj → X.PObj.OrTangent →₀ ℚ :=
  fun x => if x ∈ X.PObj.smoothSet then T x else 0

theorem zeroOff_of_mem {T : Obj → X.PObj.OrTangent →₀ ℚ} {x : Obj} (hx : x ∈ X.PObj.smoothSet) :
    zeroOff X T x = T x := by
  classical
  simp only [zeroOff, if_pos hx]

theorem zeroOff_of_not_mem {T : Obj → X.PObj.OrTangent →₀ ℚ} {x : Obj}
    (hx : x ∉ X.PObj.smoothSet) : zeroOff X T x = 0 := by
  classical
  simp only [zeroOff, if_neg hx]

theorem isOrientation_zeroOff {Θ : Obj → ℚ} {T : Obj → X.PObj.OrTangent →₀ ℚ}
    (hT : X.IsOrientation Θ T) : X.IsOrientation Θ (zeroOff X T) where
  mem x hx := by rw [zeroOff_of_mem hx]; exact hT.mem x hx
  natural φ hφ := by
    rw [zeroOff_of_mem hφ, zeroOff_of_mem (EpGroupoid.tgt_mem_smoothSet_of_src hφ)]
    exact hT.natural φ hφ
  lifts x hx := by rw [zeroOff_of_mem hx]; exact hT.lifts x hx
  locallyOriented x hx := by
    obtain ⟨B, hB⟩ := hT.locallyOriented x hx
    exact ⟨B, fun y hy hys => by rw [zeroOff_of_mem hys]; exact hB y hy hys⟩

theorem zeroOff_mem {T : Obj → X.PObj.OrTangent →₀ ℚ} (hT : X.IsGrHatSection T) :
    zeroOff X T ∈ X.GrHatSections :=
  ⟨⟨fun x hx => by rw [zeroOff_of_mem hx]; exact hT.mem x hx, fun φ hφ => by
      rw [zeroOff_of_mem hφ, zeroOff_of_mem (EpGroupoid.tgt_mem_smoothSet_of_src hφ)]
      exact hT.natural φ hφ⟩,
    fun x hx => zeroOff_of_not_mem hx⟩

/-- `F^*` only reads a section at the smooth points. -/
theorem pullSection_congr (F : EpFunctor X Y) (hF : X.PObj.IsLocalScDiffeo Y.PObj F.obj)
    {T T₀ : Obj' → Y.PObj.OrTangent →₀ ℚ} (h : ∀ y ∈ Y.PObj.smoothSet, T y = T₀ y) :
    F.pullSection T = F.pullSection T₀ := by
  funext x
  by_cases hx : x ∈ X.PObj.smoothSet
  · rw [EpFunctor.pullSection_of_mem hx, EpFunctor.pullSection_of_mem hx,
      h _ ((hF.mem_smoothSet_iff x).2 hx)]
  · rw [EpFunctor.pullSection_of_not_mem hx, EpFunctor.pullSection_of_not_mem hx]

end Zero

theorem pushSection_zeroOff {X Y : EP.{0}} (d : Diagram X Y) (T : X.Obj → X.X.PObj.OrTangent →₀ ℚ) :
    d.pushSection T = d.pushSection (zeroOff X.X T) := by
  change d.Φ.pushSection (d.F.pullSection T) = d.Φ.pushSection (d.F.pullSection _)
  rw [pullSection_congr d.F d.isEquivalence_F.isLocalScDiffeo_obj
    (T₀ := zeroOff X.X T) fun x hx => (zeroOff_of_mem hx).symm]

theorem pullSection_zeroOff {X Y : EP.{0}} (d : Diagram X Y) (hΦ : d.Φ.IsEquivalence)
    (T : Y.Obj → Y.X.PObj.OrTangent →₀ ℚ) :
    d.pullSection T = d.pullSection (zeroOff Y.X T) := by
  change d.F.pushSection (d.Φ.pullSection T) = d.F.pushSection (d.Φ.pullSection _)
  rw [pullSection_congr d.Φ hΦ.isLocalScDiffeo_obj
    (T₀ := zeroOff Y.X T) fun x hx => (zeroOff_of_mem hx).symm]

/-! ### `A ⇒ BInd` -/

theorem A_to_BInd (hA : A) : BInd := by
  obtain ⟨hpushComp, hpullComp, hpullPush, hpushPullΘ, hpushPullT⟩ := hA
  refine ⟨?_, ?_, ?_⟩
  · -- the pushed and pulled pairs: the fields of the vocabulary `push`, `pull`
    intro X Y f hf d hd
    have hΦ := isEquivalence_Φ hf hd
    refine ⟨fun Θ T h => ?_, fun Θ' T' h => ?_⟩
    · obtain ⟨hΘ, hind, hT⟩ := h
      let P := OrientedBranched.push hf ⟨Θ, T, hΘ, hind, hT⟩
      have k1 := EPLoc.pushTheta_homMk d hΦ hΘ.isFunctorial
      have k2 := EPLoc.pushSection_homMk d hΦ (T := T) ⟨hT.mem, hT.natural⟩
      rw [hd] at k1 k2
      have h1 : Y.X.IsBranchedEpSubgroupoid (EPLoc.pushTheta f Θ) := P.isBranchedEpSubgroupoid
      have h2 : Y.X.IsOrientation (EPLoc.pushTheta f Θ) (EPLoc.pushSection f T) := P.isOrientation
      rw [k1, k2] at h2
      rw [k1] at h1
      exact ⟨h1, h2⟩
    · obtain ⟨hΘ', hind', hT'⟩ := h
      let P := OrientedBranched.pull hf ⟨Θ', T', hΘ', hind', hT'⟩
      have k1 := EPLoc.pullTheta_homMk d hΘ'.isFunctorial
      have k2 := EPLoc.pullSection_homMk d hΦ (T' := T') ⟨hT'.mem, hT'.natural⟩
      rw [hd] at k1 k2
      have h1 : X.X.IsBranchedEpSubgroupoid (EPLoc.pullTheta f Θ') := P.isBranchedEpSubgroupoid
      have h2 : X.X.IsOrientation (EPLoc.pullTheta f Θ') (EPLoc.pullSection f T') :=
        P.isOrientation
      rw [k1, k2] at h2
      rw [k1] at h1
      exact ⟨h1, h2⟩
  · -- the composition laws, from `push_comp`, `pull_comp`
    intro X Y Z f g hf hg d e c hd he hc
    have hfg := isGeneralizedIso_comp hf hg
    have hΦd := isEquivalence_Φ hf hd
    have hΦe := isEquivalence_Φ hg he
    have hΦc := isEquivalence_Φ hfg hc
    refine ⟨fun Θ T h => ?_, fun Θ'' T'' h => ?_⟩
    · obtain ⟨hΘ, hind, hT⟩ := h
      have hpc := hpushComp hf hg hfg ⟨Θ, T, hΘ, hind, hT⟩
      have hθ : EPLoc.pushTheta (f ≫ g) Θ = EPLoc.pushTheta g (EPLoc.pushTheta f Θ) :=
        congrArg OrientedBranched.Θ hpc
      have hs : EPLoc.pushSection (f ≫ g) T = EPLoc.pushSection g (EPLoc.pushSection f T) :=
        congrArg OrientedBranched.T hpc
      have hTs : X.X.IsGrHatSection T := ⟨hT.mem, hT.natural⟩
      have kc := EPLoc.pushTheta_homMk c hΦc hΘ.isFunctorial
      have kd := EPLoc.pushTheta_homMk d hΦd hΘ.isFunctorial
      have ke := EPLoc.pushTheta_homMk e hΦe (EPLoc.isFunctorial_pushTheta hf hΘ.isFunctorial)
      have kc' := EPLoc.pushSection_homMk c hΦc hTs
      have kd' := EPLoc.pushSection_homMk d hΦd hTs
      have ke' := EPLoc.pushSection_homMk e hΦe (EPLoc.pushSection_mem hf hTs).1
      rw [hc] at kc kc'
      rw [hd] at kd kd'
      rw [he] at ke ke'
      refine ⟨?_, ?_⟩
      · rw [← kc, ← kd, ← ke]; exact hθ
      · rw [← kc', ← kd', ← ke']; exact hs
    · obtain ⟨hΘ, hind, hT⟩ := h
      have hpc := hpullComp hf hg hfg ⟨Θ'', T'', hΘ, hind, hT⟩
      have hθ : EPLoc.pullTheta (f ≫ g) Θ'' = EPLoc.pullTheta f (EPLoc.pullTheta g Θ'') :=
        congrArg OrientedBranched.Θ hpc
      have hs : EPLoc.pullSection (f ≫ g) T'' = EPLoc.pullSection f (EPLoc.pullSection g T'') :=
        congrArg OrientedBranched.T hpc
      have hTs : Z.X.IsGrHatSection T'' := ⟨hT.mem, hT.natural⟩
      have kc := EPLoc.pullTheta_homMk c hΘ.isFunctorial
      have ke := EPLoc.pullTheta_homMk e hΘ.isFunctorial
      have kd := EPLoc.pullTheta_homMk d (EPLoc.isFunctorial_pullTheta g hΘ.isFunctorial)
      have kc' := EPLoc.pullSection_homMk c hΦc hTs
      have ke' := EPLoc.pullSection_homMk e hΦe hTs
      have kd' := EPLoc.pullSection_homMk d hΦd (EPLoc.pullSection_mem hg hTs).1
      rw [hc] at kc kc'
      rw [hd] at kd kd'
      rw [he] at ke ke'
      refine ⟨?_, ?_⟩
      · rw [← kc, ← ke, ← kd]; exact hθ
      · rw [← kc', ← ke', ← kd']; exact hs
  · -- `f^* f_* = id`, `f_* f^* = id`
    intro X Y f hf d d' hd hd'
    have hΦ := isEquivalence_Φ hf hd
    have hΦ' := isEquivalence_Φ hf hd'
    refine ⟨fun Θ T h => ?_, fun Θ' T' h => ?_⟩
    · obtain ⟨hΘ, hind, hT⟩ := h
      have hT0 := isOrientation_zeroOff hT
      have hpp := hpullPush hf ⟨Θ, zeroOff X.X T, hΘ, hind, hT0⟩
        fun x hx => zeroOff_of_not_mem hx
      have hθ : EPLoc.pullTheta f (EPLoc.pushTheta f Θ) = Θ := congrArg OrientedBranched.Θ hpp
      have hs : EPLoc.pullSection f (EPLoc.pushSection f (zeroOff X.X T)) = zeroOff X.X T :=
        congrArg OrientedBranched.T hpp
      have hT0s : X.X.IsGrHatSection (zeroOff X.X T) := ⟨hT0.mem, hT0.natural⟩
      have kd := EPLoc.pushTheta_homMk d hΦ hΘ.isFunctorial
      have kd' := EPLoc.pullTheta_homMk d' (EPLoc.isFunctorial_pushTheta hf hΘ.isFunctorial)
      have ks := EPLoc.pushSection_homMk d hΦ hT0s
      have ks' := EPLoc.pullSection_homMk d' hΦ' (EPLoc.pushSection_mem hf hT0s).1
      rw [hd] at kd ks
      rw [hd'] at kd' ks'
      refine ⟨?_, fun x hx => ?_⟩
      · rw [← kd, ← kd']; exact hθ
      · rw [pushSection_zeroOff d T, ← ks, ← ks', hs, zeroOff_of_mem hx]
    · obtain ⟨hΘ, hind, hT⟩ := h
      have hT0 := isOrientation_zeroOff hT
      have hT0m : zeroOff Y.X T' ∈ Y.X.GrHatSections := zeroOff_mem ⟨hT.mem, hT.natural⟩
      have hθ := hpushPullΘ hf hΘ.isFunctorial
      have hs := hpushPullT hf hT0m
      have kd := EPLoc.pullTheta_homMk d hΘ.isFunctorial
      have kd' := EPLoc.pushTheta_homMk d' hΦ' (EPLoc.isFunctorial_pullTheta f hΘ.isFunctorial)
      have ks := EPLoc.pullSection_homMk d hΦ hT0m.1
      have ks' := EPLoc.pushSection_homMk d' hΦ' (EPLoc.pullSection_mem hf hT0m.1).1
      rw [hd] at kd ks
      rw [hd'] at kd' ks'
      refine ⟨?_, fun y hy => ?_⟩
      · rw [← kd, ← kd']; exact hθ
      · rw [pullSection_zeroOff d hΦ T', ← ks, ← ks', hs, zeroOff_of_mem hy]

/-! ### What `B` gives -/

/-- `push_comp`, `pull_comp`, `pull_push` follow from `B` (on the chosen representatives). -/
theorem B_to_A_core (hB : B) :
    type_of% @Polyfold.EPLocalization.OrientedBranched.push_comp.{0} ∧
    type_of% @Polyfold.EPLocalization.OrientedBranched.pull_comp.{0} ∧
    type_of% @Polyfold.EPLocalization.OrientedBranched.pull_push.{0} := by
  refine ⟨fun {X Y Z f g} hf hg hfg A' => ?_, fun {X Y Z f g} hf hg hfg A' => ?_,
    fun {X Y f} hf A' hA' => ?_⟩
  · have h := (hB.2.1 X Y Z f g hf hg (EPLoc.rep f) (EPLoc.rep g) (EPLoc.rep (f ≫ g))
      (EPLoc.homMk_rep f) (EPLoc.homMk_rep g) (EPLoc.homMk_rep _)).1 A'.Θ A'.T
      ⟨A'.isBranchedEpSubgroupoid, A'.isOrientation⟩
    exact OrientedBranched.ext' h.1 h.2
  · have h := (hB.2.1 X Y Z f g hf hg (EPLoc.rep f) (EPLoc.rep g) (EPLoc.rep (f ≫ g))
      (EPLoc.homMk_rep f) (EPLoc.homMk_rep g) (EPLoc.homMk_rep _)).2 A'.Θ A'.T
      ⟨A'.isBranchedEpSubgroupoid, A'.isOrientation⟩
    exact OrientedBranched.ext' h.1 h.2
  · have h := (hB.2.2 X Y f hf (EPLoc.rep f) (EPLoc.rep f) (EPLoc.homMk_rep f)
      (EPLoc.homMk_rep f)).1 A'.Θ A'.T ⟨A'.isBranchedEpSubgroupoid, A'.isOrientation⟩
    refine OrientedBranched.ext' h.1 (funext fun x => ?_)
    by_cases hx : x ∈ X.X.PObj.smoothSet
    · exact h.2 x hx
    · rw [hA' x hx]
      exact EpFunctor.pushSection_of_not_mem hx

#rt_check RoundTrip.V11_22.A_to_BInd [Polyfold.EPLocalization.OrientedBranched.push_comp,
  Polyfold.EPLocalization.OrientedBranched.pull_comp,
  Polyfold.EPLocalization.OrientedBranched.pull_push,
  Polyfold.EPLocalization.EPLoc.pushTheta_pullTheta,
  Polyfold.EPLocalization.EPLoc.pushSection_pullSection]
#rt_check RoundTrip.V11_22.B_to_A_core [Polyfold.EPLocalization.OrientedBranched.push_comp,
  Polyfold.EPLocalization.OrientedBranched.pull_comp,
  Polyfold.EPLocalization.OrientedBranched.pull_push,
  Polyfold.EPLocalization.EPLoc.pushTheta_pullTheta,
  Polyfold.EPLocalization.EPLoc.pushSection_pullSection]
#rt_overlap RoundTrip.V11_22.A_to_BInd [Polyfold.EPLocalization.OrientedBranched.push_comp,
  Polyfold.EPLocalization.OrientedBranched.pull_comp,
  Polyfold.EPLocalization.OrientedBranched.pull_push,
  Polyfold.EPLocalization.EPLoc.pushTheta_pullTheta,
  Polyfold.EPLocalization.EPLoc.pushSection_pullSection]

end RoundTrip.V11_22
