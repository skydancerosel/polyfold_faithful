import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_32

/-! Round trip for V7_32 (Proposition 7.7: the full subcategory on a saturated sub-M-polyfold
`A` is an ep-groupoid with the induced structures and the restricted structure maps).

`A` is the conjunction of the types of the listed theorems, at universe `0` (B lives in `Type`),
all in `Polyfold.EpGroupoid`: the conditions of Definition 7.3 for the full subcategory with the
structures `subObjPolyfold hA`, `subMorPolyfold hA` (`isLocalScDiffeo_fullSub_src`, `_tgt`,
`isScSmoothMap_fullSub_unit`, `_inv`, `exists_isProperMap_fullSub`, `isScSmoothComp_fullSub`),
the equations `subEpGroupoid_src_val`, `subEpGroupoid_comp_val`, `proposition_7_7`, and the
inclusion functor's `subEpFunctor_full`, `subEpFunctor_faithful`.  `subEpGroupoid`,
`subEpFunctor` are definitions (vocabulary).

`A → B` (proved, with the hypothesis).  B asks for SOME `Y : EpGroupoid ↥A ↥𝐀` whose structures
satisfy facts (1), (2) and whose maps are the restrictions.  `Y` is assembled from A's six
conditions (not from the definition `subEpGroupoid`): `toGroupoidStr = fullSub A`,
`PObj = subObjPolyfold hA`, `PMor = subMorPolyfold hA`; (1), (2) for these structures are Part I's
`subPolyfold_inclusion_isScSmooth`, `subPolyfold_retraction_isScSmooth`; the equations are `rfl`
and `fullSub_comp_val`.

`B → A` (proved).  The core (`A_core`: the six conditions of Definition 7.3 for the PROJECT'S
structures) is derived from B's `Y` by transport: two structures on a sub-M-polyfold with facts
(1), (2) are related by the identity, sc-smooth both ways (`id_isScSmoothMap`, locally
`id = (i⁻¹ ∘ r) ∘ i`); hence local sc-diffeomorphisms, sc-smooth maps, properness (purely
topological, same subspace topologies) and condition (4) (through its sheet form,
`isScSmoothComp_iff_sheet`, using that `Y.comp` is `X.comp` on composable pairs) pass from `Y` to
`subObjPolyfold`, `subMorPolyfold`.  So the uniqueness of the induced structure is all that A adds
to B on this part.  The remaining conjuncts (`A_rest`) are proved outright: they are `rfl`-level
facts about the definition `subEpGroupoid` (`src_val`, `comp_val`, `proposition_7_7`), which B
cannot name, and the fullness/faithfulness of the inclusion functor `subEpFunctor`, which the text
does not state.

Harness: A's statement itself contains banned theorems: the type of `isScSmoothComp_fullSub`
passes `isLocalScDiffeo_fullSub_src hA` and `(isLocalScDiffeo_fullSub_tgt hA).isScSmoothMap` as
the (irrelevant) proof arguments of `IsScSmoothComp`, and `subEpGroupoid`, `subEpFunctor` have the
banned theorems as their (non-abstracted) fields.  So no term mentioning `A` can pass `#rt_check`
or `#rt_check_soft`.  As in V2_24, the directions are factored through `A_core` (the six
conditions, with the proof arguments of `IsScSmoothComp` universally quantified) and `A_rest`:
`A_to_B = A_core_to_B ∘ A_to_A_core` (a projection) and
`B_to_A = A_of_core_rest (B_to_A_core ·) A_rest_holds` (an assembly); `#rt_check` passes on
`A_core_to_B` and `B_to_A_core`, and `A_rest_holds` passes the traversal with the bodies of
`subEpGroupoid`, `subEpFunctor` not unfolded. -/

namespace RoundTrip.V7_32
open Polyfold Set
open scoped Polyfold.EpGroupoid

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.isLocalScDiffeo_fullSub_src.{0}) ∧
    (type_of% @Polyfold.EpGroupoid.isLocalScDiffeo_fullSub_tgt.{0}) ∧
    (type_of% @Polyfold.EpGroupoid.isScSmoothMap_fullSub_unit.{0}) ∧
    (type_of% @Polyfold.EpGroupoid.isScSmoothMap_fullSub_inv.{0}) ∧
    (type_of% @Polyfold.EpGroupoid.exists_isProperMap_fullSub.{0}) ∧
    (type_of% @Polyfold.EpGroupoid.isScSmoothComp_fullSub.{0}) ∧
    (type_of% @Polyfold.EpGroupoid.subEpGroupoid_src_val.{0}) ∧
    (type_of% @Polyfold.EpGroupoid.subEpGroupoid_comp_val.{0}) ∧
    (type_of% @Polyfold.EpGroupoid.proposition_7_7.{0}) ∧
    (type_of% @Polyfold.EpGroupoid.subEpFunctor_full.{0}) ∧
    (type_of% @Polyfold.EpGroupoid.subEpFunctor_faithful.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.isLocalScDiffeo_fullSub_src.{0},
    @Polyfold.EpGroupoid.isLocalScDiffeo_fullSub_tgt.{0},
    @Polyfold.EpGroupoid.isScSmoothMap_fullSub_unit.{0},
    @Polyfold.EpGroupoid.isScSmoothMap_fullSub_inv.{0},
    @Polyfold.EpGroupoid.exists_isProperMap_fullSub.{0},
    @Polyfold.EpGroupoid.isScSmoothComp_fullSub.{0},
    @Polyfold.EpGroupoid.subEpGroupoid_src_val.{0},
    @Polyfold.EpGroupoid.subEpGroupoid_comp_val.{0},
    @Polyfold.EpGroupoid.proposition_7_7.{0},
    @Polyfold.EpGroupoid.subEpFunctor_full.{0},
    @Polyfold.EpGroupoid.subEpFunctor_faithful.{0}⟩

/-- A's six conditions of Definition 7.3 for the project's structures, with the proof arguments
of `IsScSmoothComp` universally quantified (they are irrelevant). -/
def A_core : Prop :=
  (type_of% @Polyfold.EpGroupoid.isLocalScDiffeo_fullSub_src.{0}) ∧
    (type_of% @Polyfold.EpGroupoid.isLocalScDiffeo_fullSub_tgt.{0}) ∧
    (type_of% @Polyfold.EpGroupoid.isScSmoothMap_fullSub_unit.{0}) ∧
    (type_of% @Polyfold.EpGroupoid.isScSmoothMap_fullSub_inv.{0}) ∧
    (type_of% @Polyfold.EpGroupoid.exists_isProperMap_fullSub.{0}) ∧
    ∀ {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
      {S : Set Obj} (hA : X.IsEpSubgroupoid S) [ParacompactSpace S]
      (hs : (EpGroupoid.subMorPolyfold hA).IsLocalScDiffeo (EpGroupoid.subObjPolyfold hA)
        (X.fullSub S).src)
      (ht : (EpGroupoid.subMorPolyfold hA).IsScSmoothMap (EpGroupoid.subObjPolyfold hA)
        (X.fullSub S).tgt),
      IsScSmoothComp (EpGroupoid.subObjPolyfold hA) (EpGroupoid.subMorPolyfold hA)
        (X.fullSub S).src (X.fullSub S).tgt (X.fullSub S).comp hs ht

/-- The rest of A: statements about the definitions `subEpGroupoid`, `subEpFunctor`. -/
def A_rest : Prop :=
  (type_of% @Polyfold.EpGroupoid.subEpGroupoid_src_val.{0}) ∧
    (type_of% @Polyfold.EpGroupoid.subEpGroupoid_comp_val.{0}) ∧
    (type_of% @Polyfold.EpGroupoid.proposition_7_7.{0}) ∧
    (type_of% @Polyfold.EpGroupoid.subEpFunctor_full.{0}) ∧
    (type_of% @Polyfold.EpGroupoid.subEpFunctor_faithful.{0})

theorem A_to_A_core : A → A_core := by
  rintro ⟨h1, h2, h3, h4, h5, h6, -⟩
  exact ⟨h1, h2, h3, h4, h5, fun hA _ _ _ => h6 hA⟩

theorem A_of_core_rest : A_core → A_rest → A := by
  rintro ⟨h1, h2, h3, h4, h5, h6⟩ ⟨h7, h8, h9, h10, h11⟩
  exact ⟨h1, h2, h3, h4, h5, fun hA _ => h6 hA _ _, h7, h8, h9, h10, h11⟩

/-! ### Facts (1), (2) and the identity between two induced structures -/

section Sub

variable {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {P : MPolyfold Z}

/-- The project's sub-M-polyfold structure satisfies B's facts (1), (2). -/
theorem isNaturalSubB_subPolyfold {S : Set Z} (hS : P.IsSubMPolyfold S) [ParacompactSpace S] :
    IsNaturalSubB P S (MPolyfold.subPolyfold hS) := by
  refine ⟨⟨MPolyfold.subPolyfold_inclusion_isScSmooth hS, Topology.IsEmbedding.subtypeVal⟩, ?_⟩
  intro V r hV hrV hsm hid him g hg
  let d : P.SubData S := ⟨V, r, hV, hrV, hsm, hid, him⟩
  rcases V.eq_empty_or_nonempty with hV0 | ⟨x₀, _⟩
  · subst hV0
    exact MPolyfold.IsScSmoothOn.of_exists_charts isOpen_empty (continuousOn_empty _)
      fun x hx => absurd hx (notMem_empty x)
  · refine (MPolyfold.subPolyfold_retraction_isScSmooth hS d (g x₀)).congr fun x hx =>
      Subtype.ext ?_
    rw [MPolyfold.SubData.retractInto_val d (g x₀) hx, hg x hx]

/-- **Two structures on a sub-M-polyfold with facts (1), (2) are related by the identity**: near
`a`, `id = (i⁻¹ ∘ r) ∘ i` with `i` sc-smooth for `Q₁` (fact (1)) and `i⁻¹ ∘ r` sc-smooth into
`Q₂` (fact (2)). -/
theorem id_isScSmoothMap {S : Set Z} (hS : P.IsSubMPolyfold S) [ParacompactSpace S]
    {Q₁ Q₂ : MPolyfold S} (h₁ : IsNaturalSubB P S Q₁) (h₂ : IsNaturalSubB P S Q₂) :
    Q₁.IsScSmoothMap Q₂ id := by
  refine MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun a _ => ?_
  obtain ⟨V, hV, haV, r, hrV, hrs, hri, hrA⟩ := hS a a.2
  have hrS : ∀ z ∈ V, r z ∈ S := fun z hz => by
    have h : r z ∈ r '' V := mem_image_of_mem r hz
    rw [hrA] at h
    exact h.1
  classical
  let g : Z → S := fun z => if h : r z ∈ S then ⟨r z, h⟩ else a
  have hg : ∀ z ∈ V, (g z : Z) = r z := fun z hz => by
    simp only [g, dif_pos (hrS z hz)]
  have hgs := h₂.2 V r hV hrV hrs hri hrA g hg
  have hU : IsOpen (Subtype.val ⁻¹' V : Set S) := hV.preimage continuous_subtype_val
  refine ⟨Subtype.val ⁻¹' V, hU, haV, subset_univ _, ?_⟩
  refine (MPolyfold.IsScSmoothOn.comp hgs (h₁.1.1.mono hU (subset_univ _))
    fun s hs => hs).congr fun s hs => Subtype.ext ?_
  change (g s : Z) = s
  rw [hg s hs]
  have h : (s : Z) ∈ r '' V := by rw [hrA]; exact ⟨s.2, hs⟩
  obtain ⟨z, hz, hzs⟩ := h
  rw [← hzs, hri z hz]

end Sub

/-! ### Transport along identities -/

section Transport

variable {M O : Type} [TopologicalSpace M] [T2Space M] [ParacompactSpace M]
  [TopologicalSpace O] [T2Space O] [ParacompactSpace O]
  {P₁ P₂ : MPolyfold M} {Q₁ Q₂ : MPolyfold O}

theorem isScDiffeoOn_id_of {W : Set M} (hW : IsOpen W) (h₁₂ : P₁.IsScSmoothMap P₂ id)
    (h₂₁ : P₂.IsScSmoothMap P₁ id) : P₁.IsScDiffeoOn P₂ id id W W :=
  ⟨h₁₂.mono hW (subset_univ _), h₂₁.mono hW (subset_univ _), mapsTo_id _, mapsTo_id _,
    fun _ _ => rfl, fun _ _ => rfl⟩

theorem isScDiffeoOn_transport {f : M → O} {g : O → M} {W : Set M} {V : Set O}
    (hP₁₂ : P₁.IsScSmoothMap P₂ id) (hP₂₁ : P₂.IsScSmoothMap P₁ id)
    (hQ₁₂ : Q₁.IsScSmoothMap Q₂ id) (hQ₂₁ : Q₂.IsScSmoothMap Q₁ id)
    (hd : P₁.IsScDiffeoOn Q₁ f g W V) : P₂.IsScDiffeoOn Q₂ f g W V :=
  (isScDiffeoOn_id_of hd.isOpen_target hQ₁₂ hQ₂₁).comp
    (hd.comp (isScDiffeoOn_id_of hd.isOpen_source hP₂₁ hP₁₂))

theorem isLocalScDiffeo_transport {f : M → O}
    (hP₁₂ : P₁.IsScSmoothMap P₂ id) (hP₂₁ : P₂.IsScSmoothMap P₁ id)
    (hQ₁₂ : Q₁.IsScSmoothMap Q₂ id) (hQ₂₁ : Q₂.IsScSmoothMap Q₁ id)
    (h : P₁.IsLocalScDiffeo Q₁ f) : P₂.IsLocalScDiffeo Q₂ f := fun x => by
  obtain ⟨W, V, g, hx, hd⟩ := h x
  exact ⟨W, V, g, hx, isScDiffeoOn_transport hP₁₂ hP₂₁ hQ₁₂ hQ₂₁ hd⟩

theorem isScSmoothOn_transport {f : M → O} {W : Set M} (hP₂₁ : P₂.IsScSmoothMap P₁ id)
    (hQ₁₂ : Q₁.IsScSmoothMap Q₂ id) (h : P₁.IsScSmoothOn Q₁ f W) : P₂.IsScSmoothOn Q₂ f W := by
  have h' := MPolyfold.IsScSmoothOn.comp hQ₁₂ (MPolyfold.IsScSmoothOn.comp h
    (hP₂₁.mono h.isOpen (subset_univ _)) fun _ hx => hx) (mapsTo_univ _ _)
  exact h'

end Transport

/-! ### `A → B` -/

theorem A_core_to_B : A_core → B := by
  rintro ⟨h1, h2, h3, h4, h5, h6⟩ Obj Mor _ _ _ _ _ _ X S hsat hsub
  have hA : X.IsEpSubgroupoid S := ⟨hsub, hsat⟩
  have : ParacompactSpace S := X.PObj.paracompactSpace_subtype S
  let Y : EpGroupoid S (X.morOn S) :=
    { toGroupoidStr := X.fullSub S
      PObj := EpGroupoid.subObjPolyfold hA
      PMor := EpGroupoid.subMorPolyfold hA
      isLocalScDiffeo_src := h1 hA
      isLocalScDiffeo_tgt := h2 hA
      isScSmoothMap_unit := h3 hA
      isScSmoothMap_inv := h4 hA
      exists_isProperMap := h5 hA
      isScSmoothComp := h6 hA _ _ }
  refine ⟨⟨hsub, X.isSubMPolyfold_morOn hA⟩, inferInstance, inferInstance, Y,
    isNaturalSubB_subPolyfold _, isNaturalSubB_subPolyfold _, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl, fun φ ψ h => X.fullSub_comp_val φ ψ (congrArg Subtype.val h)⟩

theorem A_to_B : A → B := fun h => A_core_to_B (A_to_A_core h)

/-! ### `B → A` -/

theorem B_to_A_core : B → A_core := by
  intro hB
  -- B's `Y`, with its maps written as those of `fullSub`, and the identities between its
  -- structures and the project's
  have key : ∀ {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
      {S : Set Obj} (hA : X.IsEpSubgroupoid S) [ParacompactSpace S],
      ∃ (Y : EpGroupoid S (X.morOn S)),
        Y.src = (X.fullSub S).src ∧ Y.tgt = (X.fullSub S).tgt ∧ Y.unit = (X.fullSub S).unit ∧
        Y.inv = (X.fullSub S).inv ∧
        (∀ φ ψ, Y.src φ = Y.tgt ψ → Y.comp φ ψ = (X.fullSub S).comp φ ψ) ∧
        Y.PObj.IsScSmoothMap (EpGroupoid.subObjPolyfold hA) id ∧
        (EpGroupoid.subObjPolyfold hA).IsScSmoothMap Y.PObj id ∧
        Y.PMor.IsScSmoothMap (EpGroupoid.subMorPolyfold hA) id ∧
        (EpGroupoid.subMorPolyfold hA).IsScSmoothMap Y.PMor id := by
    intro Obj Mor _ _ _ _ _ _ X S hA _
    obtain ⟨⟨-, hmor⟩, _, _, Y, hO, hM, hsrc, htgt, hunit, hinv, hcomp⟩ :=
      hB Obj Mor X S hA.isSaturated hA.isSubMPolyfold
    have hO' := isNaturalSubB_subPolyfold (P := X.PObj) hA.isSubMPolyfold
    have hM' := isNaturalSubB_subPolyfold (P := X.PMor) hmor
    refine ⟨Y, funext fun φ => Subtype.ext (hsrc φ), funext fun φ => Subtype.ext (htgt φ),
      funext fun a => Subtype.ext (hunit a), funext fun φ => Subtype.ext (hinv φ),
      fun φ ψ h => Subtype.ext ((hcomp φ ψ h).trans (X.fullSub_comp_val φ ψ
        ((hsrc φ).symm.trans ((congrArg Subtype.val h).trans (htgt ψ)))).symm),
      id_isScSmoothMap hA.isSubMPolyfold hO hO', id_isScSmoothMap hA.isSubMPolyfold hO' hO,
      id_isScSmoothMap hmor hM hM', id_isScSmoothMap hmor hM' hM⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Obj Mor _ _ _ _ _ _ X S hA _
    obtain ⟨Y, hsrc, -, -, -, -, hO1, hO2, hM1, hM2⟩ := key hA
    rw [← hsrc]
    exact isLocalScDiffeo_transport hM1 hM2 hO1 hO2 Y.isLocalScDiffeo_src
  · intro Obj Mor _ _ _ _ _ _ X S hA _
    obtain ⟨Y, -, htgt, -, -, -, hO1, hO2, hM1, hM2⟩ := key hA
    rw [← htgt]
    exact isLocalScDiffeo_transport hM1 hM2 hO1 hO2 Y.isLocalScDiffeo_tgt
  · intro Obj Mor _ _ _ _ _ _ X S hA _
    obtain ⟨Y, -, -, hunit, -, -, hO1, hO2, hM1, hM2⟩ := key hA
    rw [← hunit]
    exact isScSmoothOn_transport hO2 hM1 Y.isScSmoothMap_unit
  · intro Obj Mor _ _ _ _ _ _ X S hA
    have : ParacompactSpace S := X.PObj.paracompactSpace_subtype S
    obtain ⟨Y, -, -, -, hinv, -, hO1, hO2, hM1, hM2⟩ := key hA
    rw [← hinv]
    exact isScSmoothOn_transport hM2 hM1 Y.isScSmoothMap_inv
  · intro Obj Mor _ _ _ _ _ _ X S hA _ a
    obtain ⟨Y, hsrc, htgt, -⟩ := key hA
    rw [← hsrc, ← htgt]
    exact Y.exists_isProperMap a
  · intro Obj Mor _ _ _ _ _ _ X S hA _ hs ht
    obtain ⟨Y, hsrc, htgt, -, -, hcomp, hO1, hO2, hM1, hM2⟩ := key hA
    refine (isScSmoothComp_iff_sheet hs ht).2 fun σ W V hd => ?_
    have hd' : Y.PMor.IsScDiffeoOn Y.PObj Y.src σ W V := by
      rw [hsrc]
      exact isScDiffeoOn_transport hM2 hM1 hO2 hO1 hd
    have hsh := (isScSmoothComp_iff_sheet Y.isLocalScDiffeo_src
      Y.isLocalScDiffeo_tgt.isScSmoothMap).1 Y.isScSmoothComp σ W V hd'
    rw [htgt] at hsh
    refine (isScSmoothOn_transport hM2 hM1 hsh).congr fun ψ hψ => hcomp _ _ ?_
    rw [hsrc, htgt]
    exact hd.right_inv _ hψ

/-- `A_rest`, outright: statements about the definitions `subEpGroupoid`, `subEpFunctor`. -/
theorem A_rest_holds : A_rest := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro Obj Mor _ _ _ _ _ _ X S hA _ φ
    rfl
  · intro Obj Mor _ _ _ _ _ _ X S hA _ φ ψ h
    exact X.fullSub_comp_val φ ψ (congrArg Subtype.val h)
  · intro Obj Mor _ _ _ _ _ _ X S hA _
    exact ⟨hA.isSubMPolyfold, X.isSubMPolyfold_morOn hA, rfl, rfl, rfl, fun _ => rfl,
      fun _ => rfl, fun _ => rfl, fun _ => rfl,
      fun φ ψ h => X.fullSub_comp_val φ ψ (congrArg Subtype.val h)⟩
  · intro Obj Mor _ _ _ _ _ _ X S hA _
    exact
      { map_surjective := fun {x y} f => by
          let x' : S := x
          let y' : S := y
          have hx : X.src f.1 = x'.1 := f.2.1
          have hy : X.tgt f.1 = y'.1 := f.2.2
          exact ⟨⟨⟨f.1, by rw [hx]; exact x'.2, by rw [hy]; exact y'.2⟩, Subtype.ext hx,
            Subtype.ext hy⟩, Subtype.ext rfl⟩ }
  · intro Obj Mor _ _ _ _ _ _ X S hA _
    exact
      { map_injective := fun {_ _} {_ _} he => by
          have h := congrArg Subtype.val he
          exact Subtype.ext (Subtype.ext h) }

theorem B_to_A : B → A := fun h => A_of_core_rest (B_to_A_core h) A_rest_holds

open Lean Elab Command in
/-- `#rt_check_except_defs T [d₁, …] [n₁, …]`: the harness traversal `rtCollect` with the bodies of
the definitions `dᵢ` not unfolded; fails if the proof of `T` reaches some `nᵢ` elsewhere. -/
elab "#rt_check_except_defs " t:ident " [" ds:ident,* "]" " [" bs:ident,* "]" : command => do
  let env ← getEnv
  let some ci := env.find? t.getId | throwError "unknown {t.getId}"
  let roots := ((rtValue? ci).map (·.getUsedConstants)).getD #[]
  let seen := ds.getElems.foldl (fun s d => s.insert d.getId) NameSet.empty
  let used := rtCollect env roots.toList seen
  if used.contains ``sorryAx then throwError "FAIL: {t.getId} contains sorry"
  let bad := bs.getElems.toList.map (·.getId) |>.filter used.contains
  unless bad.isEmpty do throwError "FAIL: {t.getId} uses {bad} outside the bodies of the definitions"
  logInfo m!"OK: {t.getId} reaches the banned declarations only through the bodies of the definitions {ds.getElems.toList.map (·.getId)}"

#rt_check RoundTrip.V7_32.A_core_to_B [Polyfold.EpGroupoid.isLocalScDiffeo_fullSub_src,
  Polyfold.EpGroupoid.isLocalScDiffeo_fullSub_tgt, Polyfold.EpGroupoid.isScSmoothMap_fullSub_unit,
  Polyfold.EpGroupoid.isScSmoothMap_fullSub_inv, Polyfold.EpGroupoid.exists_isProperMap_fullSub,
  Polyfold.EpGroupoid.isScSmoothComp_fullSub, Polyfold.EpGroupoid.subEpGroupoid_src_val,
  Polyfold.EpGroupoid.subEpGroupoid_comp_val, Polyfold.EpGroupoid.proposition_7_7,
  Polyfold.EpGroupoid.subEpFunctor_full, Polyfold.EpGroupoid.subEpFunctor_faithful]
#rt_check RoundTrip.V7_32.B_to_A_core [Polyfold.EpGroupoid.isLocalScDiffeo_fullSub_src,
  Polyfold.EpGroupoid.isLocalScDiffeo_fullSub_tgt, Polyfold.EpGroupoid.isScSmoothMap_fullSub_unit,
  Polyfold.EpGroupoid.isScSmoothMap_fullSub_inv, Polyfold.EpGroupoid.exists_isProperMap_fullSub,
  Polyfold.EpGroupoid.isScSmoothComp_fullSub, Polyfold.EpGroupoid.subEpGroupoid_src_val,
  Polyfold.EpGroupoid.subEpGroupoid_comp_val, Polyfold.EpGroupoid.proposition_7_7,
  Polyfold.EpGroupoid.subEpFunctor_full, Polyfold.EpGroupoid.subEpFunctor_faithful]
#rt_check_except_defs RoundTrip.V7_32.A_rest_holds [Polyfold.EpGroupoid.subEpGroupoid,
  Polyfold.EpGroupoid.subEpFunctor] [Polyfold.EpGroupoid.isLocalScDiffeo_fullSub_src,
  Polyfold.EpGroupoid.isLocalScDiffeo_fullSub_tgt, Polyfold.EpGroupoid.isScSmoothMap_fullSub_unit,
  Polyfold.EpGroupoid.isScSmoothMap_fullSub_inv, Polyfold.EpGroupoid.exists_isProperMap_fullSub,
  Polyfold.EpGroupoid.isScSmoothComp_fullSub, Polyfold.EpGroupoid.subEpGroupoid_src_val,
  Polyfold.EpGroupoid.subEpGroupoid_comp_val, Polyfold.EpGroupoid.proposition_7_7,
  Polyfold.EpGroupoid.subEpFunctor_full, Polyfold.EpGroupoid.subEpFunctor_faithful]
-- `A_to_B` (and every term mentioning `A`) fails by the harness: A's statement contains the
-- banned theorems (proof arguments of `IsScSmoothComp`, fields of `subEpGroupoid`).
/-- error: rt_check FAIL: RoundTrip.V7_32.A_to_B uses [Polyfold.EpGroupoid.isLocalScDiffeo_fullSub_src,
 Polyfold.EpGroupoid.isLocalScDiffeo_fullSub_tgt,
 Polyfold.EpGroupoid.isScSmoothMap_fullSub_unit,
 Polyfold.EpGroupoid.isScSmoothMap_fullSub_inv,
 Polyfold.EpGroupoid.exists_isProperMap_fullSub,
 Polyfold.EpGroupoid.isScSmoothComp_fullSub,
 Polyfold.EpGroupoid.subEpGroupoid_comp_val] -/
#guard_msgs in
#rt_check RoundTrip.V7_32.A_to_B [Polyfold.EpGroupoid.isLocalScDiffeo_fullSub_src,
  Polyfold.EpGroupoid.isLocalScDiffeo_fullSub_tgt, Polyfold.EpGroupoid.isScSmoothMap_fullSub_unit,
  Polyfold.EpGroupoid.isScSmoothMap_fullSub_inv, Polyfold.EpGroupoid.exists_isProperMap_fullSub,
  Polyfold.EpGroupoid.isScSmoothComp_fullSub, Polyfold.EpGroupoid.subEpGroupoid_src_val,
  Polyfold.EpGroupoid.subEpGroupoid_comp_val, Polyfold.EpGroupoid.proposition_7_7,
  Polyfold.EpGroupoid.subEpFunctor_full, Polyfold.EpGroupoid.subEpFunctor_faithful]
#rt_overlap RoundTrip.V7_32.B_to_A_core [Polyfold.EpGroupoid.isLocalScDiffeo_fullSub_src,
  Polyfold.EpGroupoid.isLocalScDiffeo_fullSub_tgt, Polyfold.EpGroupoid.isScSmoothMap_fullSub_unit,
  Polyfold.EpGroupoid.isScSmoothMap_fullSub_inv, Polyfold.EpGroupoid.exists_isProperMap_fullSub,
  Polyfold.EpGroupoid.isScSmoothComp_fullSub, Polyfold.EpGroupoid.subEpGroupoid_src_val,
  Polyfold.EpGroupoid.subEpGroupoid_comp_val, Polyfold.EpGroupoid.proposition_7_7,
  Polyfold.EpGroupoid.subEpFunctor_full, Polyfold.EpGroupoid.subEpFunctor_faithful]

end RoundTrip.V7_32
