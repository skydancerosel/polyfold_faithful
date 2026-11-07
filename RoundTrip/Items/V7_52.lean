import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_52

/-!
Round trip for V7_52 (Proposition 7.11: index lifting).

`A` is the conjunction of the types of the thirteen listed theorems (universes at `0`).  The
listed definition `EpGroupoid.liftOne` carries the banned theorems `isLocalScDiffeo_liftSrc`, …,
`isScSmoothComp_lift` as its structure fields *unabstracted* (`#print` shows
`isLocalScDiffeo_src := EpGroupoid.isLocalScDiffeo_liftSrc X`, no `_proof_N`), and the type of
`isScSmoothComp_lift` contains `isLocalScDiffeo_liftSrc` itself; so any term mentioning `A` (as the
binder type of `A_to_B`, or the `And.intro` arguments of `B_to_A`) fails `#rt_check` and even
`#rt_check_soft`.  We therefore prove the directions for `Ar`, a restatement of `A` that is
definitionally equal to it (checked by the kernel when `A_to_B := Ar_to_B` and `B_to_A := B_to_Ar`
are accepted): every `X.liftOne.F` is replaced by what it reduces to (`X.liftOne.PObj ↦
X.PObj.shift`, `X.liftOne.src ↦ X.liftSrc`, …, `X.liftOne.IsTame ↦ X.PObj.shift.IsTame`), and the
two proof arguments of `IsScSmoothComp` in the type of `isScSmoothComp_lift` are replaced by our own
proofs (`lsdLevelOne`, a copy of the 10-line proof of `IsLocalScDiffeo.levelOne` from the unbanned
`IsScDiffeoOn.levelOne`); by proof irrelevance nothing else changes.

* `A → B`: `Y` is assembled from the conjuncts of the hypothesis (the fields of `liftOne` are the
  hypotheses 4–8 and 10), with `X.liftGroupoidStr`; `IsLiftB` is `MAtlas.Equiv.refl` and the
  conjuncts of `proposition_7_11`.
* `B → A`: from `B`'s `Y` (atlases equivalent to `X¹`, `𝐗¹`; structure maps those of `X` on level
  `1`): (1), (2), (3), (4) of `Y` give `isLocalScDiffeo_liftSrc`, `_liftTgt`,
  `isScSmoothMap_liftUnit`, `_liftInv`, `exists_isProperMap_lift`, `isScSmoothCompSheet_lift`,
  `isScSmoothComp_lift` (transport along the atlas equivalences: every notion involved depends on
  the M-polyfold only through `IsChart`, which depends only on the equivalence class,
  `MPolyfold.isChart_congr`; `Y.comp = liftComp` on composable pairs suffices for the sheet form);
  `IsTame.levelOne` from `B` applied to the trivial ep-groupoid of `P` (`EpGroupoid.trivial`).
  Not from `B` but proved outright from unbanned project lemmas: the general Part I statements
  `comp_mem_levelSet` (for every level `m`; three lines), `IsLocalScDiffeo.levelOne` (copy of its
  proof via `IsScDiffeoOn.levelOne`), `IsScSmoothMap.levelOne` (from `IsScSmoothOn.levelOne`).
  These three are statements about arbitrary M-polyfolds and arbitrary levels which `B`, a
  statement about ep-groupoids at level `1`, cannot give.
-/

namespace RoundTrip.V7_52
open Polyfold Set

/-- The listed theorems (universes at `0`). -/
def A : Prop :=
  type_of% @Polyfold.EpGroupoid.comp_mem_levelSet.{0} ∧
  type_of% @Polyfold.MPolyfold.IsLocalScDiffeo.levelOne.{0, 0} ∧
  type_of% @Polyfold.MPolyfold.IsScSmoothMap.levelOne.{0, 0} ∧
  type_of% @Polyfold.EpGroupoid.isLocalScDiffeo_liftSrc.{0} ∧
  type_of% @Polyfold.EpGroupoid.isLocalScDiffeo_liftTgt.{0} ∧
  type_of% @Polyfold.EpGroupoid.isScSmoothMap_liftUnit.{0} ∧
  type_of% @Polyfold.EpGroupoid.isScSmoothMap_liftInv.{0} ∧
  type_of% @Polyfold.EpGroupoid.exists_isProperMap_lift.{0} ∧
  type_of% @Polyfold.EpGroupoid.isScSmoothCompSheet_lift.{0} ∧
  type_of% @Polyfold.EpGroupoid.isScSmoothComp_lift.{0} ∧
  type_of% @Polyfold.MPolyfold.IsTame.levelOne.{0} ∧
  type_of% @Polyfold.EpGroupoid.isTame_liftOne.{0} ∧
  type_of% @Polyfold.EpGroupoid.proposition_7_11.{0}

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.comp_mem_levelSet.{0}, @Polyfold.MPolyfold.IsLocalScDiffeo.levelOne.{0, 0},
    @Polyfold.MPolyfold.IsScSmoothMap.levelOne.{0, 0},
    @Polyfold.EpGroupoid.isLocalScDiffeo_liftSrc.{0},
    @Polyfold.EpGroupoid.isLocalScDiffeo_liftTgt.{0},
    @Polyfold.EpGroupoid.isScSmoothMap_liftUnit.{0},
    @Polyfold.EpGroupoid.isScSmoothMap_liftInv.{0},
    @Polyfold.EpGroupoid.exists_isProperMap_lift.{0},
    @Polyfold.EpGroupoid.isScSmoothCompSheet_lift.{0},
    @Polyfold.EpGroupoid.isScSmoothComp_lift.{0}, @Polyfold.MPolyfold.IsTame.levelOne.{0},
    @Polyfold.EpGroupoid.isTame_liftOne.{0}, @Polyfold.EpGroupoid.proposition_7_11.{0}⟩

/-! ### Glue: an unbanned proof of `IsLocalScDiffeo.levelOne`, and transport of the sc-notions
along equivalent atlases -/

section Glue
variable {X Y : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]

/-- The proof of `MPolyfold.IsLocalScDiffeo.levelOne`, from the unbanned
`MPolyfold.IsScDiffeoOn.levelOne`. -/
theorem lsdLevelOne {P : MPolyfold X} {Q : MPolyfold Y} {f : X → Y} (hf : P.IsLocalScDiffeo Q f) :
    P.shift.IsLocalScDiffeo Q.shift
      (MPolyfold.levelOneMap P Q f (hf.isScSmoothMap.mapsTo_levelSet 1)) := fun x => by
  classical
  obtain ⟨U, V, g, hx, hd⟩ := hf (P.levelVal 1 x)
  let g₁ : Q.Level 1 → P.Level 1 := fun y =>
    if hy : g (Q.levelVal 1 y) ∈ P.levelSet 1 then P.levelMk 1 _ hy else x
  refine ⟨{x' | P.levelVal 1 x' ∈ U}, {y | Q.levelVal 1 y ∈ V}, g₁, hx,
    MPolyfold.IsScDiffeoOn.levelOne hd (fun _ _ => rfl) fun y hy => ?_⟩
  have hg1 : g (Q.levelVal 1 y) ∈ P.levelSet 1 :=
    hd.isScSmoothOn_inv.mapsTo_levelSet 1 ⟨hy, MPolyfold.levelVal_mem y⟩
  simp only [g₁, dif_pos hg1, MPolyfold.levelVal_levelMk]

variable {P P' : MPolyfold X} {Q Q' : MPolyfold Y}

theorem onT (hP : P.atlas.Equiv P'.atlas) (hQ : Q.atlas.Equiv Q'.atlas) {f : X → Y} {U : Set X}
    (h : P.IsScSmoothOn Q f U) : P'.IsScSmoothOn Q' f U :=
  ⟨h.isOpen, h.continuousOn, fun φ ψ hφ hψ => h.smooth φ ψ ((MPolyfold.isChart_congr hP φ).2 hφ)
    ((MPolyfold.isChart_congr hQ ψ).2 hψ)⟩

theorem diffeoT (hP : P.atlas.Equiv P'.atlas) (hQ : Q.atlas.Equiv Q'.atlas) {f : X → Y}
    {g : Y → X} {U : Set X} {V : Set Y} (h : P.IsScDiffeoOn Q f g U V) :
    P'.IsScDiffeoOn Q' f g U V :=
  ⟨onT hP hQ h.isScSmoothOn, onT hQ hP h.isScSmoothOn_inv, h.mapsTo, h.mapsTo_inv, h.left_inv,
    h.right_inv⟩

theorem lsdT (hP : P.atlas.Equiv P'.atlas) (hQ : Q.atlas.Equiv Q'.atlas) {f : X → Y}
    (h : P.IsLocalScDiffeo Q f) : P'.IsLocalScDiffeo Q' f := fun x => by
  obtain ⟨U, V, g, hx, hd⟩ := h x
  exact ⟨U, V, g, hx, diffeoT hP hQ hd⟩

end Glue

/-- `A` with every `X.liftOne.F` replaced by what it reduces to and the proof arguments of
`IsScSmoothComp` replaced by `lsdLevelOne`; definitionally equal to `A`. -/
def Ar : Prop :=
  type_of% @Polyfold.EpGroupoid.comp_mem_levelSet.{0} ∧
  type_of% @Polyfold.MPolyfold.IsLocalScDiffeo.levelOne.{0, 0} ∧
  type_of% @Polyfold.MPolyfold.IsScSmoothMap.levelOne.{0, 0} ∧
  type_of% @Polyfold.EpGroupoid.isLocalScDiffeo_liftSrc.{0} ∧
  type_of% @Polyfold.EpGroupoid.isLocalScDiffeo_liftTgt.{0} ∧
  type_of% @Polyfold.EpGroupoid.isScSmoothMap_liftUnit.{0} ∧
  type_of% @Polyfold.EpGroupoid.isScSmoothMap_liftInv.{0} ∧
  type_of% @Polyfold.EpGroupoid.exists_isProperMap_lift.{0} ∧
  type_of% @Polyfold.EpGroupoid.isScSmoothCompSheet_lift.{0} ∧
  (∀ {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    IsScSmoothComp X.PObj.shift X.PMor.shift X.liftSrc X.liftTgt X.liftComp
      (lsdLevelOne X.isLocalScDiffeo_src) (lsdLevelOne X.isLocalScDiffeo_tgt).isScSmoothMap) ∧
  type_of% @Polyfold.MPolyfold.IsTame.levelOne.{0} ∧
  (∀ {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    X.IsTame → X.PObj.shift.IsTame) ∧
  (∀ {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    X.PObj.shift = X.PObj.shift ∧ X.PMor.shift = X.PMor.shift ∧
      (∀ φ, X.PObj.levelVal 1 (X.liftSrc φ) = X.src (X.PMor.levelVal 1 φ)) ∧
      (∀ φ, X.PObj.levelVal 1 (X.liftTgt φ) = X.tgt (X.PMor.levelVal 1 φ)) ∧
      (∀ x, X.PMor.levelVal 1 (X.liftUnit x) = X.unit (X.PObj.levelVal 1 x)) ∧
      (∀ φ, X.PMor.levelVal 1 (X.liftInv φ) = X.inv (X.PMor.levelVal 1 φ)) ∧
      (∀ φ ψ, X.liftSrc φ = X.liftTgt ψ → X.PMor.levelVal 1 (X.liftComp φ ψ) =
        X.comp (X.PMor.levelVal 1 φ) (X.PMor.levelVal 1 ψ)) ∧
      (X.IsTame → X.PObj.shift.IsTame))

/-! ### `A → B` -/

theorem Ar_to_B : Ar → B := by
  rintro ⟨-, -, -, h4, h5, h6, h7, h8, -, h10, -, h12, h13⟩ Obj Mor _ _ _ _ _ _ X
  let Y : EpGroupoid (X.PObj.Level 1) (X.PMor.Level 1) :=
    { toGroupoidStr := X.liftGroupoidStr
      PObj := X.PObj.shift
      PMor := X.PMor.shift
      isLocalScDiffeo_src := h4 X
      isLocalScDiffeo_tgt := h5 X
      isScSmoothMap_unit := h6 X
      isScSmoothMap_inv := h7 X
      exists_isProperMap := h8 X
      isScSmoothComp := h10 X }
  obtain ⟨-, -, hs, ht, hu, hi, hc, -⟩ := h13 X
  exact ⟨Y, ⟨MAtlas.Equiv.refl _, MAtlas.Equiv.refl _, hs, ht, hu, hi, hc⟩, h12 X⟩

theorem A_to_B : A → B := Ar_to_B

/-! ### `B → A` -/

section BA
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- `comp_mem_levelSet`, its three-line proof (from the unbanned `mem_levelSet_tgt_iff`). -/
theorem compMem (X : EpGroupoid Obj Mor) {φ ψ : Mor} {m : ℕ} (hφ : φ ∈ X.PMor.levelSet m)
    (h : X.src φ = X.tgt ψ) : X.comp φ ψ ∈ X.PMor.levelSet m := by
  rw [← X.mem_levelSet_tgt_iff, X.tgt_comp _ _ h, X.mem_levelSet_tgt_iff]
  exact hφ

theorem lvComp (X : EpGroupoid Obj Mor) {φ ψ : X.PMor.Level 1}
    (h : X.src (X.PMor.levelVal 1 φ) = X.tgt (X.PMor.levelVal 1 ψ)) :
    X.PMor.levelVal 1 (X.liftComp φ ψ) = X.comp (X.PMor.levelVal 1 φ) (X.PMor.levelVal 1 ψ) := by
  rw [EpGroupoid.liftComp, dif_pos (compMem X (MPolyfold.levelVal_mem φ) h)]
  rfl

/-- What `B` gives for one `X`, with `Y.src = liftSrc`, `Y.tgt = liftTgt`, `Y.unit = liftUnit`,
`Y.inv = liftInv` as functions. -/
theorem fromB (hB : B) (X : EpGroupoid Obj Mor) :
    ∃ Y : EpGroupoid (X.PObj.Level 1) (X.PMor.Level 1),
      Y.PObj.atlas.Equiv X.PObj.shift.atlas ∧ Y.PMor.atlas.Equiv X.PMor.shift.atlas ∧
      Y.src = X.liftSrc ∧ Y.tgt = X.liftTgt ∧ Y.unit = X.liftUnit ∧ Y.inv = X.liftInv ∧
      (∀ φ ψ : X.PMor.Level 1, Y.src φ = Y.tgt ψ →
        X.PMor.levelVal 1 (Y.comp φ ψ) = X.comp (X.PMor.levelVal 1 φ) (X.PMor.levelVal 1 ψ)) ∧
      (X.IsTame → Y.IsTame) := by
  obtain ⟨Y, ⟨hO, hM, hs, ht, hu, hi, hc⟩, htame⟩ := hB Obj Mor X
  exact ⟨Y, hO, hM, funext fun φ => MPolyfold.level_ext (hs φ),
    funext fun φ => MPolyfold.level_ext (ht φ), funext fun x => MPolyfold.level_ext (hu x),
    funext fun φ => MPolyfold.level_ext (hi φ), hc, htame⟩

/-- (4) on level `1`, sheet form, from `B`: transport `Y`'s sheet condition along the atlas
equivalences; `Y.comp = liftComp` on the composable pairs `(σ(t ψ), ψ)`. -/
theorem sheetB (hB : B) (X : EpGroupoid Obj Mor) :
    IsScSmoothCompSheet X.PObj.shift X.PMor.shift X.liftSrc X.liftTgt X.liftComp := by
  obtain ⟨Y, hO, hM, hs, ht, -, -, hc, -⟩ := fromB hB X
  have hY := (isScSmoothComp_iff_sheet Y.isLocalScDiffeo_src
    Y.isLocalScDiffeo_tgt.isScSmoothMap).1 Y.isScSmoothComp
  intro σ W V hd
  have hd' : Y.PMor.IsScDiffeoOn Y.PObj Y.src σ W V := by
    rw [hs]; exact diffeoT hM.symm hO.symm hd
  have h1 := onT hM hM (hY σ W V hd')
  rw [ht] at h1
  refine h1.congr fun ψ hψ => ?_
  have hr : X.liftSrc (σ (X.liftTgt ψ)) = X.liftTgt ψ := hd.right_inv _ hψ
  have hcomp : Y.src (σ (Y.tgt ψ)) = Y.tgt ψ := by rw [hs, ht]; exact hr
  refine MPolyfold.level_ext ?_
  have e1 := hc _ _ hcomp
  rw [ht] at e1
  simp only
  rw [e1, lvComp X (congrArg (X.PObj.levelVal 1) hr)]

end BA

theorem B_to_Ar (hB : B) : Ar := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- comp_mem_levelSet (every level `m`): outright
  · intro Obj Mor _ _ _ _ _ _ X φ ψ m hφ h
    exact compMem X hφ h
  -- IsLocalScDiffeo.levelOne (arbitrary M-polyfolds): outright
  · intro X _ _ _ P Y _ _ _ Q f hf
    exact lsdLevelOne hf
  -- IsScSmoothMap.levelOne (arbitrary M-polyfolds): outright, from `IsScSmoothOn.levelOne`
  · intro X _ _ _ PX Z _ _ _ Q f f₁ hf hf₁
    have h := MPolyfold.IsScSmoothOn.levelOne hf (f₁ := f₁) fun x _ => hf₁ x
    have e : {x : PX.Level 1 | PX.levelVal 1 x ∈ (univ : Set X)} = univ :=
      eq_univ_of_forall fun _ => mem_univ _
    rw [e] at h
    exact h
  -- (1) on level 1, from `B`
  · intro Obj Mor _ _ _ _ _ _ X
    obtain ⟨Y, hO, hM, hs, -, -, -, -, -⟩ := fromB hB X
    have := lsdT hM hO Y.isLocalScDiffeo_src
    rwa [hs] at this
  · intro Obj Mor _ _ _ _ _ _ X
    obtain ⟨Y, hO, hM, -, ht, -, -, -, -⟩ := fromB hB X
    have := lsdT hM hO Y.isLocalScDiffeo_tgt
    rwa [ht] at this
  -- (2) on level 1, from `B`
  · intro Obj Mor _ _ _ _ _ _ X
    obtain ⟨Y, hO, hM, -, -, hu, -, -, -⟩ := fromB hB X
    have := onT hO hM Y.isScSmoothMap_unit
    rwa [hu] at this
  · intro Obj Mor _ _ _ _ _ _ X
    obtain ⟨Y, hO, hM, -, -, -, hi, -, -⟩ := fromB hB X
    have := onT hM hM Y.isScSmoothMap_inv
    rwa [hi] at this
  -- (3) on level 1, from `B`
  · intro Obj Mor _ _ _ _ _ _ X x
    obtain ⟨Y, -, -, hs, ht, -, -, -, -⟩ := fromB hB X
    have := Y.exists_isProperMap x
    rwa [hs, ht] at this
  -- (4) on level 1, sheet form, from `B`
  · intro Obj Mor _ _ _ _ _ _ X
    exact sheetB hB X
  -- (4) on level 1, literal form, from the sheet form
  · intro Obj Mor _ _ _ _ _ _ X
    exact (isScSmoothComp_iff_sheet _ _).2 (sheetB hB X)
  -- tameness of index lifts of M-polyfolds, from `B` for the trivial ep-groupoid
  · intro Z _ _ _ P h
    obtain ⟨Y, hO, -, -, -, -, -, -, ht⟩ := fromB hB (EpGroupoid.trivial P)
    obtain ⟨A, hA, hAt⟩ := ht h
    exact ⟨A, hA.trans hO, hAt⟩
  · intro Obj Mor _ _ _ _ _ _ X h
    obtain ⟨Y, hO, -, -, -, -, -, -, ht⟩ := fromB hB X
    obtain ⟨A, hA, hAt⟩ := ht h
    exact ⟨A, hA.trans hO, hAt⟩
  · intro Obj Mor _ _ _ _ _ _ X
    refine ⟨rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
      fun φ ψ h => lvComp X (congrArg (X.PObj.levelVal 1) h), fun h => ?_⟩
    obtain ⟨Y, hO, -, -, -, -, -, -, ht⟩ := fromB hB X
    obtain ⟨A, hA, hAt⟩ := ht h
    exact ⟨A, hA.trans hO, hAt⟩

theorem B_to_A : B → A := B_to_Ar

#rt_check_soft RoundTrip.V7_52.A_to_B [Polyfold.EpGroupoid.comp_mem_levelSet,
  Polyfold.MPolyfold.IsLocalScDiffeo.levelOne, Polyfold.MPolyfold.IsScSmoothMap.levelOne,
  Polyfold.EpGroupoid.isLocalScDiffeo_liftSrc, Polyfold.EpGroupoid.isLocalScDiffeo_liftTgt,
  Polyfold.EpGroupoid.isScSmoothMap_liftUnit, Polyfold.EpGroupoid.isScSmoothMap_liftInv,
  Polyfold.EpGroupoid.exists_isProperMap_lift, Polyfold.EpGroupoid.isScSmoothCompSheet_lift,
  Polyfold.EpGroupoid.isScSmoothComp_lift, Polyfold.MPolyfold.IsTame.levelOne,
  Polyfold.EpGroupoid.isTame_liftOne, Polyfold.EpGroupoid.proposition_7_11]
#rt_check RoundTrip.V7_52.B_to_A [Polyfold.EpGroupoid.comp_mem_levelSet,
  Polyfold.MPolyfold.IsLocalScDiffeo.levelOne, Polyfold.MPolyfold.IsScSmoothMap.levelOne,
  Polyfold.EpGroupoid.isLocalScDiffeo_liftSrc, Polyfold.EpGroupoid.isLocalScDiffeo_liftTgt,
  Polyfold.EpGroupoid.isScSmoothMap_liftUnit, Polyfold.EpGroupoid.isScSmoothMap_liftInv,
  Polyfold.EpGroupoid.exists_isProperMap_lift, Polyfold.EpGroupoid.isScSmoothCompSheet_lift,
  Polyfold.EpGroupoid.isScSmoothComp_lift, Polyfold.MPolyfold.IsTame.levelOne,
  Polyfold.EpGroupoid.isTame_liftOne, Polyfold.EpGroupoid.proposition_7_11]
#rt_overlap RoundTrip.V7_52.B_to_A [Polyfold.EpGroupoid.comp_mem_levelSet,
  Polyfold.MPolyfold.IsLocalScDiffeo.levelOne, Polyfold.MPolyfold.IsScSmoothMap.levelOne,
  Polyfold.EpGroupoid.isLocalScDiffeo_liftSrc, Polyfold.EpGroupoid.isLocalScDiffeo_liftTgt,
  Polyfold.EpGroupoid.isScSmoothMap_liftUnit, Polyfold.EpGroupoid.isScSmoothMap_liftInv,
  Polyfold.EpGroupoid.exists_isProperMap_lift, Polyfold.EpGroupoid.isScSmoothCompSheet_lift,
  Polyfold.EpGroupoid.isScSmoothComp_lift, Polyfold.MPolyfold.IsTame.levelOne,
  Polyfold.EpGroupoid.isTame_liftOne, Polyfold.EpGroupoid.proposition_7_11]

end RoundTrip.V7_52
