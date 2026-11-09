import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_35

/-! Round trip for V8_35 (Proposition 8.3 of the 2017 text, 2021: Proposition 8.5.7, Geometric
Lift: the proper covering functor of a geometric lift).

`A` is the conjunction of the types of the thirteen listed theorems, universes at `0`:
`GeometricLift.isLocalScDiffeo_ySrc`, `isLocalScDiffeo_yTgt`, `isProperMap_yTgt`,
`isScSmoothCompSheet_y`, `geometricLiftFunctor_surjective` (`[Nonempty D]`),
`geometricLiftFunctor_surjective_iff` (`F` surjective iff `D ≠ ∅` or `U(x) = ∅`),
`geometricLiftFunctor_isLocalScDiffeo`, `_finite_fiber`, `_evenlyCovered`,
`GeometricLift.isScSmoothMap_fibredInv`, `geometricLiftFunctor_isScDiffeo_fibredMap`,
`proposition_8_3` (`[Nonempty D]`, a covering functor `f`: the project's `F` is a proper covering
functor) and `CoveringExamples.isProperCovering_reflectionLift`.  The constructions (`YObj`,
`YMor`, `sourceStr`, `yObjPolyfold`, `yMorPolyfold`, `geometricLiftSource`, `geometricLiftTarget`,
`geometricLiftFunctor`, `fibredInv`, `actionEpGroupoid`) are definitions.

* `B` asserts the proposition for every covering functor, including `D = ∅`, and, as its author
  says, is **false**: `not_B` with `D = Discrete PEmpty`, `G = Unit`, `L_C(⋆) = ℝ`, `L_D` empty;
  then `Y = ∅` and no functor `Y → X` is surjective onto `U(x) = ℝ`.  The project assumes
  `[Nonempty D]` and records the failure (`geometricLiftFunctor_surjective_iff`).  So `A → B` is
  false (`not_A_to_B`) and `B → A` holds only ex falso.
* `BRepaired`: `B` with `[Nonempty D]`.  `A_to_BRepaired` is proved: `EY` is the project's
  `geometricLiftSource L` (its object and morphism types are `B`'s `Σ`-types on the nose), `EX`
  is Chapter 7's `actionEpGroupoid` for `G` itself (the project's `geometricLiftTarget` uses
  `ULift G`, `B` fixes the morphism type `G × U(x)`), and `A` is the project's functor with
  `ULift.up` removed (`functorG`).  Its proper-covering property comes from `A`'s
  `proposition_8_3`: conditions (1), (2) are literally the same (same object spaces and
  structures), and (3) is transported along `((g, z), y) ↦ ((up g, z), y)` between the two fibred
  products (`Φ` in `isProperCovering_functorG`), an sc-smooth map of sub-M-polyfolds.  The summand clauses of `IsModelB`
  use `Sigma.mk` (`MPolyfold.isScSmoothMap_sigmaMk`) with the inverse `τ(y)⁻¹ ∘ F`.
* `BRepaired → A`: not proved (see the JSON).  Eleven of `A`'s thirteen conjuncts are lemmas
  about the project's specific constructions, stated in a generality `BRepaired` does not cover
  (arbitrary, possibly infinite `D`; no covering hypothesis; `D = ∅` in `surjective_iff`); and
  `BRepaired` only asserts *some* model `(EY, EX, A)`, so even `proposition_8_3` for the
  project's `F` would need a transport of the proper-covering property from that model, through
  the identity `EY.PObj ≅ yObjPolyfold` (pinned down by the summand clauses) and `G` vs `ULift G`,
  including the fibred-product sub-M-polyfolds.  That is effort, not a mathematical gap.
* Checks: `not_B` passes `#rt_check`; `B_to_A` and `A_to_BRepaired` pass the local
  `#rt_check_fields` (see the section *Checks*), not `#rt_check`/`#rt_check_soft`, which no proof
  mentioning `A` can pass here. -/

namespace RoundTrip.V8_35
open Polyfold CategoryTheory Set Function
open scoped Polyfold.GeometricLift

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.GeometricLift.isLocalScDiffeo_ySrc.{0}) ∧
  (type_of% @Polyfold.GeometricLift.isLocalScDiffeo_yTgt.{0}) ∧
  (type_of% @Polyfold.GeometricLift.isProperMap_yTgt.{0}) ∧
  (type_of% @Polyfold.GeometricLift.isScSmoothCompSheet_y.{0}) ∧
  (type_of% @Polyfold.geometricLiftFunctor_surjective.{0}) ∧
  (type_of% @Polyfold.geometricLiftFunctor_surjective_iff.{0}) ∧
  (type_of% @Polyfold.geometricLiftFunctor_isLocalScDiffeo.{0}) ∧
  (type_of% @Polyfold.geometricLiftFunctor_finite_fiber.{0}) ∧
  (type_of% @Polyfold.geometricLiftFunctor_evenlyCovered.{0}) ∧
  (type_of% @Polyfold.GeometricLift.isScSmoothMap_fibredInv.{0}) ∧
  (type_of% @Polyfold.geometricLiftFunctor_isScDiffeo_fibredMap.{0}) ∧
  (type_of% @Polyfold.proposition_8_3.{0}) ∧
  (type_of% @Polyfold.CoveringExamples.isProperCovering_reflectionLift)

theorem A_holds : A :=
  ⟨@Polyfold.GeometricLift.isLocalScDiffeo_ySrc.{0},
    @Polyfold.GeometricLift.isLocalScDiffeo_yTgt.{0},
    @Polyfold.GeometricLift.isProperMap_yTgt.{0},
    @Polyfold.GeometricLift.isScSmoothCompSheet_y.{0},
    @Polyfold.geometricLiftFunctor_surjective.{0},
    @Polyfold.geometricLiftFunctor_surjective_iff.{0},
    @Polyfold.geometricLiftFunctor_isLocalScDiffeo.{0},
    @Polyfold.geometricLiftFunctor_finite_fiber.{0},
    @Polyfold.geometricLiftFunctor_evenlyCovered.{0},
    @Polyfold.GeometricLift.isScSmoothMap_fibredInv.{0},
    @Polyfold.geometricLiftFunctor_isScDiffeo_fibredMap.{0},
    @Polyfold.proposition_8_3.{0},
    @Polyfold.CoveringExamples.isProperCovering_reflectionLift⟩

/-! ### `B` is false: `D = ∅` -/

/-- `L_C(⋆) = ℝ`, `L_C(g) = id`. -/
abbrev emptyLC : SingleObj Unit ⥤ MPolyfoldCat.{0} :=
  (Functor.const (SingleObj Unit)).obj CoveringExamples.rCat

/-- The geometric lift of the empty functor `∅ → SingleObj Unit` with `U(x) = ℝ`. -/
def emptyLift : GeometricLift.{0} (Functor.empty.{0} (SingleObj Unit)) where
  LD := Functor.empty MPolyfoldCat.{0}
  LC := emptyLC
  τ := { app := fun a => a.as.elim, naturality := fun a => a.as.elim }

theorem not_B : ¬ B := by
  intro hB
  have hf : IsCoveringFunctor (Functor.empty.{0} (SingleObj Unit)) :=
    ⟨fun a => a.1.as.elim, fun p => p.2.as.elim⟩
  obtain ⟨_, _, _, EY, EX, F, -, hF, -⟩ :=
    hB (Discrete PEmpty) Unit (Functor.empty.{0} (SingleObj Unit)) hf emptyLift
  obtain ⟨p, -⟩ := hF.surjective (0 : Fin 1 → ℝ)
  exact p.1.as.elim

theorem not_A_to_B : ¬ (A → B) := fun h => not_B (h A_holds)

/-- `B → A` only ex falso. -/
theorem B_to_A : B → A := fun h => absurd h not_B

/-! ### The repaired statement: `D` nonempty -/

/-- `B` with `D` nonempty (the project's hypothesis `[Nonempty D]`). -/
def BRepaired : Prop :=
  ∀ (D : Type) [Groupoid D] [Fintype D] [∀ a b : D, Fintype (a ⟶ b)] [Nonempty D]
    (G : Type) [Group G] [Fintype G] (f : D ⥤ SingleObj G),
    IsCoveringFunctor f → ∀ L : GeometricLift.{0} f,
      letI : TopologicalSpace G := ⊥
      haveI : DiscreteTopology G := ⟨rfl⟩
      ∃ (_ : ParacompactSpace (ObjYB L)) (_ : ParacompactSpace (MorYB L))
        (_ : ParacompactSpace (G × UxB L))
        (EY : EpGroupoid (ObjYB L) (MorYB L)) (EX : EpGroupoid (UxB L) (G × UxB L))
        (A : EpFunctor EY EX),
        IsModelB L EY EX A ∧ A.IsProperCovering ∧ Function.Bijective A.fibredMap

/-! #### Glue -/

section Glue

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}

/-- A map into a sub-M-polyfold is sc-smooth into it as soon as it is sc-smooth into the ambient
M-polyfold (Proposition 2.21 (2); the project's lemma of this name is private). -/
theorem isScSmoothOn_subPolyfold_of_val' {A : Set Y} (hA : Q.IsSubMPolyfold A)
    [ParacompactSpace A] {f : X → A} {U : Set X}
    (hf : P.IsScSmoothOn Q (fun x => (f x : Y)) U) :
    P.IsScSmoothOn (MPolyfold.subPolyfold hA) f U := by
  refine MPolyfold.IsScSmoothOn.of_locally hf.isOpen fun x hx => ?_
  set d := hA.data (f x).2
  have hU' : IsOpen (U ∩ (fun x => (f x : Y)) ⁻¹' d.V) :=
    hf.continuousOn.isOpen_inter_preimage hf.isOpen d.isOpen
  refine ⟨_, hU', ⟨hx, hA.mem_data_V (f x).2⟩, inter_subset_left, ?_⟩
  refine (MPolyfold.IsScSmoothOn.comp (MPolyfold.subPolyfold_retraction_isScSmooth hA d (f x))
    (hf.mono hU' inter_subset_left) fun y hy => hy.2).congr fun y hy => Subtype.ext ?_
  simp only [Function.comp_apply]
  rw [d.retractInto_val (f x) hy.2]
  exact d.apply_eq_self ⟨(f y).2, hy.2⟩

end Glue

section Model

variable {D : Type} [Groupoid D] [Fintype D] [∀ a b : D, Fintype (a ⟶ b)]
  {G : Type} [Group G] [Fintype G] [TopologicalSpace G] [DiscreteTopology G]
  {f : D ⥤ SingleObj G} (L : GeometricLift.{0} f)

omit [Fintype D] [∀ a b : D, Fintype (a ⟶ b)] in
/-- `X = G ⋉ U(x)` with the morphism type `G × U(x)` (Chapter 7's translation groupoid for `G`
itself, not `ULift G`). -/
def targetG : EpGroupoid L.Ux (G × L.Ux) :=
  EpGroupoid.Examples.actionEpGroupoid (K := G) (P := (L.LC.obj (SingleObj.star G)).P)
    fun k => (L.LC.map (k : SingleObj.star G ⟶ SingleObj.star G)).isScDiffeoOn.isScSmoothOn

/-- The project's functor `F` with values in `targetG`. -/
def functorG : EpFunctor (geometricLiftSource L) (targetG L) where
  obj p := L.τy p.1 p.2
  mor p := ((f.map p.1.2.2 : G), L.τy p.1.1 p.2)
  src_mor _ := rfl
  tgt_mor p := (congrFun (congrArg ScDiffeo.toFun (L.τ.naturality p.1.2.2)) p.2).symm
  mor_comp p q h := by
    refine L.composable_cases (P := fun p q => (((f.map (L.yComp p q).1.2.2 : G),
      L.τy (L.yComp p q).1.1 (L.yComp p q).2) : G × L.Ux) =
      ((f.map p.1.2.2 : G) * (f.map q.1.2.2 : G), L.τy q.1.1 q.2)) h ?_
    intro a b c ψ γ z
    rw [GeometricLift.yComp_mk]
    refine Prod.ext ?_ rfl
    change (f.map (γ ≫ ψ) : G) = (f.map ψ : G) * (f.map γ : G)
    rw [f.map_comp, SingleObj.comp_as_mul]
  mor_unit x := by
    refine Prod.ext ?_ rfl
    change (f.map (𝟙 x.1) : G) = 1
    rw [f.map_id, SingleObj.id_as_one]
  isScSmoothMap_obj := (MPolyfold.isScSmoothMap_sigma_iff _).2 fun y =>
    (L.τ.app y).isScDiffeoOn.isScSmoothOn
  isScSmoothMap_mor := (MPolyfold.isScSmoothMap_sigma_iff _).2 fun ψ =>
    MPolyfold.IsScSmoothOn.prodMk (isScSmoothMap_const_discrete (f.map ψ.2.2 : G))
      (L.τ.app ψ.1).isScDiffeoOn.isScSmoothOn

omit [Fintype D] [∀ a b : D, Fintype (a ⟶ b)] in
/-- `(g, z) ↦ (up g, z)` is sc-smooth `G × U(x) → ULift G × U(x)`. -/
theorem isScSmoothMap_up :
    (targetG L).PMor.IsScSmoothMap (geometricLiftTarget L).PMor
      (fun p : G × L.Ux => ((ULift.up p.1 : ULift.{0} G), p.2)) :=
  isScSmoothMap_prod_discrete_iff.2 fun g =>
    MPolyfold.IsScSmoothOn.prodMk (isScSmoothMap_const_discrete (ULift.up g))
      MPolyfold.isScSmoothMap_id

/-- The project's proper-covering property of `F` gives that of `functorG`. -/
theorem isProperCovering_functorG (hP : (geometricLiftFunctor L).IsProperCovering) :
    (functorG L).IsProperCovering where
  surjective := hP.surjective
  isLocalScDiffeo := hP.isLocalScDiffeo
  finite_fiber := hP.finite_fiber
  evenlyCovered := hP.evenlyCovered
  isScDiffeo_fibredMap := by
    let _ := MPolyfold.paracompactSpace_prod (targetG L).PMor (geometricLiftSource L).PObj
    let _ := ((targetG L).PMor.prod (geometricLiftSource L).PObj).paracompactSpace_subtype
      (MPolyfold.fibredProduct (targetG L).src (functorG L).obj)
    let _ := MPolyfold.paracompactSpace_prod (geometricLiftTarget L).PMor
      (geometricLiftSource L).PObj
    let _ := ((geometricLiftTarget L).PMor.prod (geometricLiftSource L).PObj).paracompactSpace_subtype
      (MPolyfold.fibredProduct (geometricLiftTarget L).src (geometricLiftFunctor L).obj)
    obtain ⟨gU, hgU⟩ := hP.isScDiffeo_fibredMap
    have hBG := MPolyfold.isSubMPolyfold_fibredProduct (targetG L).isLocalScDiffeo_src
      (functorG L).isScSmoothMap_obj
    have hBU := MPolyfold.isSubMPolyfold_fibredProduct (geometricLiftTarget L).isLocalScDiffeo_src
      (geometricLiftFunctor L).isScSmoothMap_obj
    -- `Φ : 𝐗_G ₛ×_F Y → 𝐗_{ULift G} ₛ×_F Y`
    let Φ : MPolyfold.fibredProduct (targetG L).src (functorG L).obj →
        MPolyfold.fibredProduct (geometricLiftTarget L).src (geometricLiftFunctor L).obj :=
      fun q => ⟨((ULift.up q.1.1.1, q.1.1.2), q.1.2), q.2⟩
    have hvalG := MPolyfold.subPolyfold_inclusion_isScSmooth hBG
    have hΦ : (MPolyfold.subPolyfold hBG).IsScSmoothMap (MPolyfold.subPolyfold hBU) Φ :=
      isScSmoothOn_subPolyfold_of_val' hBU (f := Φ) (MPolyfold.IsScSmoothOn.prodMk
        ((isScSmoothMap_up L).comp ((MPolyfold.isScSmoothMap_fst (targetG L).PMor
          (geometricLiftSource L).PObj).comp hvalG))
        ((MPolyfold.isScSmoothMap_snd (targetG L).PMor (geometricLiftSource L).PObj).comp hvalG))
    have hΦF : ∀ p, Φ ((functorG L).fibredMap p) = (geometricLiftFunctor L).fibredMap p :=
      fun _ => rfl
    have hΦinj : Injective Φ := by
      rintro ⟨⟨⟨g, z⟩, y⟩, h⟩ ⟨⟨⟨g', z'⟩, y'⟩, h'⟩ he
      have he' := congrArg Subtype.val he
      simp only [Φ, Prod.mk.injEq, ULift.up.injEq] at he'
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he'
      rfl
    refine ⟨gU ∘ Φ, ?_, ?_, mapsTo_univ _ _, mapsTo_univ _ _, fun p _ => ?_, fun q _ => ?_⟩
    · exact isScSmoothOn_subPolyfold_of_val' hBG (MPolyfold.IsScSmoothOn.prodMk
        (functorG L).isScSmoothMap_mor (geometricLiftSource L).isScSmoothMap_src)
    · exact MPolyfold.IsScSmoothOn.comp hgU.isScSmoothOn_inv hΦ (mapsTo_univ _ _)
    · change gU (Φ ((functorG L).fibredMap p)) = p
      rw [hΦF]
      exact hgU.left_inv p (mem_univ _)
    · apply hΦinj
      rw [hΦF]
      exact hgU.right_inv (Φ q) (mem_univ _)

/-- The clauses of `IsModelB` for `geometricLiftSource L`, `targetG L`, `functorG L`. -/
theorem isModelB_functorG [ParacompactSpace (G × UxB L)] :
    IsModelB L (geometricLiftSource L) (targetG L) (functorG L) := by
  refine ⟨fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl, fun _ => rfl, fun _ => rfl,
    ⟨id, MPolyfold.isScDiffeoOn_id isOpen_univ⟩, fun g => ?_, fun _ _ => rfl,
    fun _ _ _ _ => rfl, fun a b c γ ψ z => geometricLiftSource_comp_mk L ψ γ _ z,
    fun _ _ => rfl, fun _ _ _ _ => rfl, fun y => ?_, fun ψ => ?_, fun _ _ => rfl,
    fun _ _ _ _ => rfl⟩
  · -- the sheet `{g} × U(x)` of `G × U(x)`
    have hO : IsOpen {p : G × L.Ux | p.1 = g} := (isOpen_discrete {g}).preimage continuous_fst
    refine ⟨Prod.snd, MPolyfold.IsScSmoothOn.prodMk (isScSmoothMap_const_discrete g)
      MPolyfold.isScSmoothMap_id, (MPolyfold.isScSmoothMap_snd _ _).mono hO (subset_univ _),
      fun _ _ => rfl, mapsTo_univ _ _, fun _ _ => rfl, ?_⟩
    rintro ⟨g', z⟩ (rfl : g' = g)
    rfl
  · -- the summand `U(y)` of `Y`, inverse `τ(y)⁻¹ ∘ F`
    refine ⟨fun p => (L.τ.app y).invFun ((functorG L).obj p),
      MPolyfold.isScSmoothMap_sigmaMk (fun y : D => (L.LD.obj y).P) y,
      ((L.τ.app y).isScDiffeoOn.isScSmoothOn_inv.comp (functorG L).isScSmoothMap_obj
        (mapsTo_univ _ _)).mono isOpen_range_sigmaMk (subset_univ _),
      fun z _ => mem_range_self z, mapsTo_univ _ _,
      fun z _ => (L.τ.app y).isScDiffeoOn.left_inv z (mem_univ z), ?_⟩
    rintro _ ⟨z, rfl⟩
    change (⟨y, (L.τ.app y).invFun ((L.τ.app y).toFun z)⟩ : ObjYB L) = ⟨y, z⟩
    rw [(L.τ.app y).isScDiffeoOn.left_inv z (mem_univ z)]
  · -- the summand `U(s ψ)` of `𝐘`, inverse `τ(s ψ)⁻¹ ∘ F ∘ s`
    refine ⟨fun p => (L.τ.app ψ.1).invFun ((functorG L).obj ((geometricLiftSource L).src p)),
      MPolyfold.isScSmoothMap_sigmaMk (fun ψ : (Σ a b : D, a ⟶ b) => (L.LD.obj ψ.1).P) ψ,
      ((L.τ.app ψ.1).isScDiffeoOn.isScSmoothOn_inv.comp
        ((functorG L).isScSmoothMap_obj.comp (geometricLiftSource L).isScSmoothMap_src)
        (mapsTo_univ _ _)).mono isOpen_range_sigmaMk (subset_univ _),
      fun z _ => mem_range_self z, mapsTo_univ _ _,
      fun z _ => (L.τ.app ψ.1).isScDiffeoOn.left_inv z (mem_univ z), ?_⟩
    rintro _ ⟨z, rfl⟩
    change (⟨ψ, (L.τ.app ψ.1).invFun ((L.τ.app ψ.1).toFun z)⟩ : MorYB L) = ⟨ψ, z⟩
    rw [(L.τ.app ψ.1).isScDiffeoOn.left_inv z (mem_univ z)]

end Model

theorem A_to_BRepaired : A → BRepaired := by
  intro hA D _ _ _ _ G _ _ f hf L
  let _ : TopologicalSpace G := ⊥
  have _ : DiscreteTopology G := ⟨rfl⟩
  have hP : (geometricLiftFunctor L).IsProperCovering := hA.2.2.2.2.2.2.2.2.2.2.2.1 hf L
  have hF := isProperCovering_functorG L hP
  refine ⟨inferInstance, inferInstance, inferInstance, geometricLiftSource L, targetG L,
    functorG L, isModelB_functorG L, hF, ?_⟩
  let _ := MPolyfold.paracompactSpace_prod (targetG L).PMor (geometricLiftSource L).PObj
  let _ := ((targetG L).PMor.prod (geometricLiftSource L).PObj).paracompactSpace_subtype
    (MPolyfold.fibredProduct (targetG L).src (functorG L).obj)
  obtain ⟨g, hg⟩ := hF.isScDiffeo_fibredMap
  exact ⟨fun p q h => by
      rw [← hg.left_inv p (mem_univ _), ← hg.left_inv q (mem_univ _), h],
    fun q => ⟨g q, hg.right_inv q (mem_univ _)⟩⟩

/-! ### Checks

`not_B` passes `#rt_check`.  `B_to_A` and `A_to_BRepaired` cannot pass `#rt_check` or
`#rt_check_soft` for any proof: `A`'s own statement mentions `geometricLiftSource` (and
`geometricLiftFunctor`, whose type does), a project *definition* whose fields are filled with the
banned theorems as plain constants (`isLocalScDiffeo_src := L.isLocalScDiffeo_ySrc`,
`exists_isProperMap := … L.isProperMap_yTgt …`, `isScSmoothComp := … L.isScSmoothCompSheet_y`),
not abstracted `_proof_N` terms, so `#rt_check_soft` counts them as hard.  (Even the ex-falso
`B_to_A := fun h => absurd h not_B` fails, through the type `A`.)  `#rt_check_fields` below is
`#rt_check_soft` with one change: a theorem reached from the body of a `Polyfold.*` definition is
soft whether or not Lean abstracted it as `_proof_N` (bodies of `RoundTrip.*` definitions, e.g.
`functorG`, `targetG`, stay hard).  It lists the banned theorems reached only that way and the
definitions involved. -/

open Lean Elab Command in
/-- Like `rtCollectSoft`, but every theorem used in the body of a `Polyfold.*` definition is
soft. -/
partial def rtCollectFields (env : Environment) (todo : List (Name × Bool)) (hard soft : NameSet) :
    NameSet × NameSet := Id.run do
  let mut todo := todo
  let mut hard := hard
  let mut soft := soft
  while true do
    match todo with
    | [] => break
    | (n, isHard) :: rest =>
      todo := rest
      if hard.contains n then continue
      if !isHard && soft.contains n then continue
      if isHard then hard := hard.insert n else soft := soft.insert n
      let some ci := env.find? n | continue
      let mod? := (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!
      let inProject := match mod? with
        | none => true
        | some m => (`Polyfold).isPrefixOf m || (`RoundTrip).isPrefixOf m
      unless inProject do continue
      let isPolyDef := match ci, mod? with
        | .defnInfo _, some m => (`Polyfold).isPrefixOf m
        | _, _ => false
      let tys := ci.type.getUsedConstants.toList.map (·, isHard)
      let vals := (((rtValue? ci).map (·.getUsedConstants)).getD #[]).toList.map fun c =>
        let isThm := match env.find? c with | some (.thmInfo _) => true | _ => false
        (c, isHard && !(isPolyDef && (isThm || rtIsDefProof c)))
      todo := tys ++ vals ++ todo
  return (hard, soft)

open Lean Elab Command in
/-- `#rt_check_fields T [n₁, …]`: `#rt_check_soft`, with every theorem in the body of a
`Polyfold.*` definition counted as a (possibly non-abstracted) proof field. -/
elab "#rt_check_fields " t:ident " [" bs:ident,* "]" : command => do
  let env ← getEnv
  let some ci := env.find? t.getId | throwError "unknown {t.getId}"
  let roots := ((rtValue? ci).map (·.getUsedConstants)).getD #[]
  let (hard, soft) := rtCollectFields env (roots.toList.map (·, true)) {} {}
  if hard.contains ``sorryAx || soft.contains ``sorryAx then
    throwError "rt_check_fields FAIL: {t.getId} contains sorry (or failed to elaborate)"
  let banned := bs.getElems.toList.map (·.getId)
  let badHard := banned.filter hard.contains
  let badSoft := banned.filter fun b => soft.contains b && !hard.contains b
  unless badHard.isEmpty do throwError "rt_check_fields FAIL: {t.getId} uses {badHard}"
  let defs := hard.toList.filter fun n => match env.find? n with
    | some (.defnInfo v) =>
      ((env.getModuleIdxFor? n).map fun i =>
        (`Polyfold).isPrefixOf env.header.moduleNames[i.toNat]!).getD false &&
      v.value.getUsedConstants.any fun c =>
        (match env.find? c with | some (.thmInfo _) => true | _ => false) &&
        (let cl := rtCollect env [c] {}; badSoft.any fun b => c == b || cl.contains b)
    | _ => false
  logInfo m!"rt_check_fields OK: {t.getId} reaches {badSoft} only through the bodies of the project definitions {defs}"

#rt_check RoundTrip.V8_35.not_B [Polyfold.GeometricLift.isLocalScDiffeo_ySrc,
  Polyfold.GeometricLift.isLocalScDiffeo_yTgt, Polyfold.GeometricLift.isProperMap_yTgt,
  Polyfold.GeometricLift.isScSmoothCompSheet_y, Polyfold.geometricLiftFunctor_surjective,
  Polyfold.geometricLiftFunctor_surjective_iff, Polyfold.geometricLiftFunctor_isLocalScDiffeo,
  Polyfold.geometricLiftFunctor_finite_fiber, Polyfold.geometricLiftFunctor_evenlyCovered,
  Polyfold.GeometricLift.isScSmoothMap_fibredInv,
  Polyfold.geometricLiftFunctor_isScDiffeo_fibredMap, Polyfold.proposition_8_3,
  Polyfold.CoveringExamples.isProperCovering_reflectionLift]
#rt_check_fields RoundTrip.V8_35.B_to_A [Polyfold.GeometricLift.isLocalScDiffeo_ySrc,
  Polyfold.GeometricLift.isLocalScDiffeo_yTgt, Polyfold.GeometricLift.isProperMap_yTgt,
  Polyfold.GeometricLift.isScSmoothCompSheet_y, Polyfold.geometricLiftFunctor_surjective,
  Polyfold.geometricLiftFunctor_surjective_iff, Polyfold.geometricLiftFunctor_isLocalScDiffeo,
  Polyfold.geometricLiftFunctor_finite_fiber, Polyfold.geometricLiftFunctor_evenlyCovered,
  Polyfold.GeometricLift.isScSmoothMap_fibredInv,
  Polyfold.geometricLiftFunctor_isScDiffeo_fibredMap, Polyfold.proposition_8_3,
  Polyfold.CoveringExamples.isProperCovering_reflectionLift]
#rt_check_fields RoundTrip.V8_35.A_to_BRepaired [Polyfold.GeometricLift.isLocalScDiffeo_ySrc,
  Polyfold.GeometricLift.isLocalScDiffeo_yTgt, Polyfold.GeometricLift.isProperMap_yTgt,
  Polyfold.GeometricLift.isScSmoothCompSheet_y, Polyfold.geometricLiftFunctor_surjective,
  Polyfold.geometricLiftFunctor_surjective_iff, Polyfold.geometricLiftFunctor_isLocalScDiffeo,
  Polyfold.geometricLiftFunctor_finite_fiber, Polyfold.geometricLiftFunctor_evenlyCovered,
  Polyfold.GeometricLift.isScSmoothMap_fibredInv,
  Polyfold.geometricLiftFunctor_isScDiffeo_fibredMap, Polyfold.proposition_8_3,
  Polyfold.CoveringExamples.isProperCovering_reflectionLift]
#rt_overlap RoundTrip.V8_35.B_to_A [Polyfold.GeometricLift.isLocalScDiffeo_ySrc,
  Polyfold.GeometricLift.isLocalScDiffeo_yTgt, Polyfold.GeometricLift.isProperMap_yTgt,
  Polyfold.GeometricLift.isScSmoothCompSheet_y, Polyfold.geometricLiftFunctor_surjective,
  Polyfold.geometricLiftFunctor_surjective_iff, Polyfold.geometricLiftFunctor_isLocalScDiffeo,
  Polyfold.geometricLiftFunctor_finite_fiber, Polyfold.geometricLiftFunctor_evenlyCovered,
  Polyfold.GeometricLift.isScSmoothMap_fibredInv,
  Polyfold.geometricLiftFunctor_isScDiffeo_fibredMap, Polyfold.proposition_8_3,
  Polyfold.CoveringExamples.isProperCovering_reflectionLift]
#rt_overlap RoundTrip.V8_35.A_to_BRepaired [Polyfold.GeometricLift.isLocalScDiffeo_ySrc,
  Polyfold.GeometricLift.isLocalScDiffeo_yTgt, Polyfold.GeometricLift.isProperMap_yTgt,
  Polyfold.GeometricLift.isScSmoothCompSheet_y, Polyfold.geometricLiftFunctor_surjective,
  Polyfold.geometricLiftFunctor_surjective_iff, Polyfold.geometricLiftFunctor_isLocalScDiffeo,
  Polyfold.geometricLiftFunctor_finite_fiber, Polyfold.geometricLiftFunctor_evenlyCovered,
  Polyfold.GeometricLift.isScSmoothMap_fibredInv,
  Polyfold.geometricLiftFunctor_isScDiffeo_fibredMap, Polyfold.proposition_8_3,
  Polyfold.CoveringExamples.isProperCovering_reflectionLift]

end RoundTrip.V8_35
