import Polyfold.Chapter17.ProperCoveringUniformizer
import Polyfold.Chapter17.PolyfoldConstructionExamples
import Polyfold.Chapter8.TangentFibred
import Polyfold.Chapter7.LocalDiffeo

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17, §17.8:
**Definition 17.8.13** (p. 836, proper polyfold covering structure and proper polyfold covering
functor) and **Proposition 17.8.15** (pp. 837–838, the map (17.103) is an sc-diffeomorphism).
Numbers and pages are the 2021 text's.

# Proper polyfold covering structures

## The text, paraphrased

(Definition 17.8.13) A proper polyfold covering structure for a proper covering functor
`P : A → B` of GCTs is a pair `(F, M)`: a proper covering uniformizer construction `F` and
M-polyfold structures on the transition sets `M(Ψ, Ψ')` and `M(Ψ̂, Ψ̂')` such that `A` and `B`
with the induced structures become polyfolds and `p` of (17.101) is a local sc-diffeomorphism.
A proper polyfold covering functor is a proper covering functor with such a structure.
(Proposition 17.8.15) For a proper polyfold covering functor the bijection
`M(Ψ̂, Ψ̂') → M(Ψ, Ψ') ₛ×_τ̂ E` of Lemma 17.8.14 is an sc-diffeomorphism.  *Proof*: it is
sc-smooth since `p` is; since `p` and `τ̂` are local sc-diffeomorphisms it is a local
sc-diffeomorphism, and a bijective local sc-diffeomorphism is an sc-diffeomorphism.

## What is formalized

* `MPolyfold.isLocalScDiffeo_fstOfFibredProduct`: `π₁ : X _f×_g Y → X` is a local
  sc-diffeomorphism when `g` is one (the mirror of Chapter 8's
  `isLocalScDiffeo_sndOfFibredProduct`).
* **Definition 17.8.13**: `ProperPolyfoldCoveringStructure P` with the polyfold structure `SB` of
  `B` on the induced uniformizers (`SB_F`), the M-polyfolds `MH U U'` of the `M(Ψ̂, Ψ̂')` with
  the conditions of Definition 17.1.8 for the `Ψ̂` ("`A` becomes a polyfold"), and
  `isLocalScDiffeo_p`; `baseUnif` (the uniformizer `Ψ` of `(Ψ̂, Ψ) ∈ F(β)` as a uniformizer of
  `SB`).  `ProperPolyfoldCoveringFunctor A B`.
* **Proposition 17.8.15**: `proposition_17_8_15`.
* Witnesses: `sheetPolyfoldCoveringStructure` (for a trivial action on `O`: the sheet
  construction, `B` with the tautological structure `twistConstruction`, `M(Ψ̂, Ψ̂')` the
  tautological transition M-polyfold of `A = G ⋉ (S × O)`), and `z3PolyfoldCoveringFunctor`:
  two sheets of `ℤ/3 ⋉ ℝ` (`ℤ/3` acting trivially, isotropy `ℤ/3` at every point) over `ℤ/3 ⋉ ℝ`,
  with `F(β) ≠ ∅` for every `β` (`z3PolyfoldCoveringFunctor_nondegenerate`).

## Readings

* "`A` and `B` for the induced structures become polyfolds": for `B`, a polyfold structure
  (Definition 17.1.8) whose uniformizers are the `Ψ` of the pairs in `F` (`SB_F`); for `A`, the
  conditions (a)–(c) of Definition 17.1.8 for the transition M-polyfolds `M(Ψ̂, Ψ̂')` over the
  object M-polyfolds of the `E` (the `Ψ̂` are not uniformizers, Remark 17.8.11).
* "`M(Ψ, Ψ') ₛ×_τ̂ E`" carries Part I's fibred-product sub-M-polyfold structure of
  `M(Ψ, Ψ') × E` (`s` and `τ̂` are local sc-diffeomorphisms).
* The witness has a trivial action on `O`: a proper covering uniformizer needs `Ψ(o_β) = β` with
  `o_β` fixed by `G`, so for the tautological `Ψ` of `G ⋉ O` every `β` with `F(β) ≠ ∅` is fixed.
  For the reflection the sheet construction has `F(β) ≠ ∅` only at `β = 0`.
-/

open Set Function Topology

noncomputable section

universe u v w

namespace Polyfold

open EpGroupoid EpGroupoid.Examples

/-! ### The first projection of a fibred product -/

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
  {Z : Type w} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {S : MPolyfold Z}

/-- For an sc-smooth `f` and a local sc-diffeomorphism `g`, the projection `π₁ : X _f×_g Y → X`
is a local sc-diffeomorphism. -/
theorem isLocalScDiffeo_fstOfFibredProduct [ParacompactSpace (X × Y)] {f : X → Z} {g : Y → Z}
    [ParacompactSpace (fibredProduct f g)] (hf : P.IsScSmoothMap S f)
    (hg : Q.IsLocalScDiffeo S g) :
    (subPolyfold (isSubMPolyfold_fibredProduct' hf hg)).IsLocalScDiffeo P
      (fun a => (a : X × Y).1) := by
  intro a
  obtain ⟨W, V, k, haW, hd⟩ := hg a.1.2
  refine ⟨_, _, _, ?_, isScDiffeoOn_fst_fibredProduct (isSubMPolyfold_fibredProduct' hf hg) hd
    hf a⟩
  refine ⟨?_, haW⟩
  change f a.1.1 ∈ V
  rw [show f a.1.1 = g a.1.2 from a.2]
  exact hd.mapsTo haW

end MPolyfold

/-! ### Definition 17.8.13 -/

variable {A B : GCT.{u}} {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr}

namespace ProperCoveringUniformizerConstruction

/-- The uniformizer `Ψ` of `(Ψ̂, Ψ) ∈ F(β)`, as a uniformizer of a polyfold structure `SB` of `B`
whose uniformizers are those of `F`. -/
def baseUnif (F : ProperCoveringUniformizerConstruction P) (SB : B.PolyfoldConstruction)
    (hSB : ∀ β, SB.F β = F.toUniformizerConstruction.F β) (U : F.Unif) : SB.Unif :=
  ⟨U.unif.toLocalUniformizer, U.1.1, (hSB U.1.1).symm ▸ F.mem_toUniformizerConstruction⟩

@[simp] theorem baseUnif_val (F : ProperCoveringUniformizerConstruction P)
    (SB : B.PolyfoldConstruction) (hSB : ∀ β, SB.F β = F.toUniformizerConstruction.F β)
    (U : F.Unif) : (F.baseUnif SB hSB U).1 = U.unif.toLocalUniformizer := rfl

end ProperCoveringUniformizerConstruction

open ProperCoveringUniformizer ProperCoveringUniformizerConstruction

variable (P) in
/-- **Definition 17.8.13 (proper polyfold covering structure)**, p. 836: a proper covering
uniformizer construction `F` (`toC`), a polyfold structure `SB` of `B` (Definition 17.1.8) on the
uniformizers `Ψ` of `F` (`SB_F`), M-polyfold structures `MH U U'` on the transition sets
`M(Ψ̂, Ψ̂')` with (a) `s`, `t` local sc-diffeomorphisms into the object M-polyfolds of `E`,
`E'`, (b) unit and inversion sc-smooth, (c) multiplication sc-smooth (`A` becomes a polyfold),
and `p : M(Ψ̂, Ψ̂') → M(Ψ, Ψ')` a local sc-diffeomorphism. -/
structure ProperPolyfoldCoveringStructure : Type (u + 1) where
  /-- The proper covering uniformizer construction `F`. -/
  toC : ProperCoveringUniformizerConstruction P
  /-- The polyfold structure of `B`. -/
  SB : B.PolyfoldConstruction
  /-- Its uniformizers are the `Ψ` of the pairs in `F`. -/
  SB_F : ∀ β, SB.F β = toC.toUniformizerConstruction.F β
  /-- The topology of `M(Ψ̂, Ψ̂')`. -/
  [topH : ∀ U U' : toC.Unif, TopologicalSpace (HatTrans U.unif U'.unif)]
  [t2H : ∀ U U' : toC.Unif, T2Space (HatTrans U.unif U'.unif)]
  [paraH : ∀ U U' : toC.Unif, ParacompactSpace (HatTrans U.unif U'.unif)]
  /-- The M-polyfold structure of `M(Ψ̂, Ψ̂')`. -/
  MH : ∀ U U' : toC.Unif, MPolyfold (HatTrans U.unif U'.unif)
  /-- (a) `s : M(Ψ̂, Ψ̂') → E` is a local sc-diffeomorphism. -/
  isLocalScDiffeo_src : ∀ U U' : toC.Unif,
    (MH U U').IsLocalScDiffeo U.unif.E.PObj GroupoidStr.TransitionSet.src
  /-- (a) `t : M(Ψ̂, Ψ̂') → E'` is a local sc-diffeomorphism. -/
  isLocalScDiffeo_tgt : ∀ U U' : toC.Unif,
    (MH U U').IsLocalScDiffeo U'.unif.E.PObj GroupoidStr.TransitionSet.tgt
  /-- (b) The unit map `E → M(Ψ̂, Ψ̂)` is sc-smooth. -/
  isScSmoothMap_unit : ∀ U : toC.Unif,
    U.unif.E.PObj.IsScSmoothMap (MH U U) GroupoidStr.TransitionSet.unit
  /-- (b) The inversion `M(Ψ̂, Ψ̂') → M(Ψ̂', Ψ̂)` is sc-smooth. -/
  isScSmoothMap_inv : ∀ U U' : toC.Unif,
    (MH U U').IsScSmoothMap (MH U' U) GroupoidStr.TransitionSet.inv
  /-- (c) The multiplication `M(Ψ̂', Ψ̂'') ₛ×ₜ M(Ψ̂, Ψ̂') → M(Ψ̂, Ψ̂'')` is sc-smooth. -/
  isScSmoothMap_mul : ∀ U U' U'' : toC.Unif,
    MPolyfold.IsScSmoothOnFibredProduct (MH U' U'') (MH U U') (MH U U'')
      (isLocalScDiffeo_src U' U'') (isLocalScDiffeo_tgt U U').isScSmoothMap
      GroupoidStr.TransitionSet.mul
  /-- `p : M(Ψ̂, Ψ̂') → M(Ψ, Ψ')` of (17.101) is a local sc-diffeomorphism. -/
  isLocalScDiffeo_p : ∀ U U' : toC.Unif,
    (MH U U').IsLocalScDiffeo (SB.transPolyfold (toC.baseUnif SB SB_F U) (toC.baseUnif SB SB_F U'))
      fun a => (transMap U.unif U'.unif a : SB.Tr (toC.baseUnif SB SB_F U)
        (toC.baseUnif SB SB_F U'))

attribute [instance] ProperPolyfoldCoveringStructure.topH ProperPolyfoldCoveringStructure.t2H
  ProperPolyfoldCoveringStructure.paraH

variable (A B) in
/-- **Definition 17.8.13 (proper polyfold covering functor)**: a proper covering functor of GCTs
(Definition 17.8.1) with a proper polyfold covering structure. -/
structure ProperPolyfoldCoveringFunctor : Type (u + 1) where
  /-- The functor `P : A → B`. -/
  P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr
  /-- `P` is a proper covering functor (Definition 17.8.1). -/
  isProperCovering : P.IsProperCoveringGCT
  /-- The proper polyfold covering structure. -/
  S : ProperPolyfoldCoveringStructure P

/-! ### Proposition 17.8.15 -/

namespace ProperPolyfoldCoveringStructure

variable (S : ProperPolyfoldCoveringStructure P)

/-- The transition M-polyfold `M(Ψ, Ψ')` of `SB` for `(Ψ̂, Ψ)`, `(Ψ̂', Ψ')`. -/
abbrev BaseTr (U U' : S.toC.Unif) : Type u :=
  S.SB.Tr (S.toC.baseUnif S.SB S.SB_F U) (S.toC.baseUnif S.SB S.SB_F U')

/-- **Proposition 17.8.15**, pp. 837–838: for a proper polyfold covering functor the bijection
(17.103) `M(Ψ̂, Ψ̂') → M(Ψ, Ψ') ₛ×_τ̂ E`, `(e, φ, e') ↦ (p(e, φ, e'), e)`, is an sc-diffeomorphism
onto the fibred-product sub-M-polyfold of `M(Ψ, Ψ') × E`. -/
theorem proposition_17_8_15 (hPc : P.IsProperCoveringGCT) (U U' : S.toC.Unif) :
    letI := MPolyfold.paracompactSpace_prod
      (S.SB.transPolyfold (S.toC.baseUnif S.SB S.SB_F U) (S.toC.baseUnif S.SB S.SB_F U'))
      U.unif.E.PObj
    letI := ((S.SB.transPolyfold (S.toC.baseUnif S.SB S.SB_F U)
      (S.toC.baseUnif S.SB S.SB_F U')).prod U.unif.E.PObj).paracompactSpace_subtype
      (MPolyfold.fibredProduct (fun a : S.BaseTr U U' => a.src) U.unif.τ.obj)
    ∃ g, (S.MH U U').IsScDiffeoOn (MPolyfold.subPolyfold
      (MPolyfold.isSubMPolyfold_fibredProduct'
        (S.SB.isLocalScDiffeo_trSrc (S.toC.baseUnif S.SB S.SB_F U)
          (S.toC.baseUnif S.SB S.SB_F U')).isScSmoothMap U.unif.model.isLocalScDiffeo))
      (fun a => ⟨((transMap U.unif U'.unif a : S.BaseTr U U'), a.src),
        (fibredTransMap U.unif U'.unif a).2⟩) g univ univ := by
  let := MPolyfold.paracompactSpace_prod
    (S.SB.transPolyfold (S.toC.baseUnif S.SB S.SB_F U) (S.toC.baseUnif S.SB S.SB_F U'))
    U.unif.E.PObj
  let := ((S.SB.transPolyfold (S.toC.baseUnif S.SB S.SB_F U)
    (S.toC.baseUnif S.SB S.SB_F U')).prod U.unif.E.PObj).paracompactSpace_subtype
    (MPolyfold.fibredProduct (fun a : S.BaseTr U U' => a.src) U.unif.τ.obj)
  set Φ : HatTrans U.unif U'.unif →
      MPolyfold.fibredProduct (fun a : S.BaseTr U U' => a.src) U.unif.τ.obj :=
    fun a => ⟨((transMap U.unif U'.unif a : S.BaseTr U U'), a.src),
      (fibredTransMap U.unif U'.unif a).2⟩ with hΦ
  have hπ := MPolyfold.isLocalScDiffeo_fstOfFibredProduct
    (S.SB.isLocalScDiffeo_trSrc (S.toC.baseUnif S.SB S.SB_F U)
      (S.toC.baseUnif S.SB S.SB_F U')).isScSmoothMap U.unif.model.isLocalScDiffeo
  have hcont : Continuous Φ := by
    refine continuous_induced_rng.2 (Continuous.prodMk ?_ ?_)
    · exact (S.isLocalScDiffeo_p U U').continuous
    · exact (S.isLocalScDiffeo_src U U').continuous
  have hloc : (S.MH U U').IsLocalScDiffeo _ Φ :=
    MPolyfold.isLocalScDiffeo_of_comp_eq (S.isLocalScDiffeo_p U U') hπ hcont fun _ => rfl
  have hbij : Bijective Φ := lemma_17_8_14 U.unif hPc U'.unif
  exact ⟨_, hloc.isScDiffeoOn_of_bijective (Equiv.ofBijective Φ hbij) fun _ => rfl⟩

end ProperPolyfoldCoveringStructure

/-! ### Witnesses -/

section Sheet

open GCT GCT.PolyfoldConstruction

variable {G : Type u} [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
  {O : Type u} [TopologicalSpace O] [T2Space O] [ParacompactSpace O] [MulAction G O]
  {PO : MPolyfold O} (hP : ∀ g : G, PO.IsScSmoothMap PO fun y => g • y)
  (S : Type u) [TopologicalSpace S] [DiscreteTopology S] [MulAction G S]
  [ParacompactSpace (S × O)] [Nonempty S]

/-- The tautological transition M-polyfold of `A = G ⋉ (S × O)`. -/
abbrev SheetHatTrans : Type u :=
  TwistTrans (isScSmoothMap_sheet_smul' hP S) (TranslationTwist.refl G (S × O))

/-- The topology of `M(Ψ̂, Ψ̂')` for sheet uniformizers. -/
@[instance_reducible]
def sheetTopOf {β β' : O} (h : ∀ g : G, g • β = β) (h' : ∀ g : G, g • β' = β') :
    ∀ (V : ProperCoveringUniformizer (sheetGCTFunctor hP S) β)
      (V' : ProperCoveringUniformizer (sheetGCTFunctor hP S) β'),
      V = sheetUniformizer hP S β h → V' = sheetUniformizer hP S β' h' →
      TopologicalSpace (HatTrans V V')
  | _, _, rfl, rfl => (inferInstance : TopologicalSpace (SheetHatTrans hP S))

theorem sheetT2Of {β β' : O} (h : ∀ g : G, g • β = β) (h' : ∀ g : G, g • β' = β') :
    ∀ (V : ProperCoveringUniformizer (sheetGCTFunctor hP S) β)
      (V' : ProperCoveringUniformizer (sheetGCTFunctor hP S) β')
      (hV : V = sheetUniformizer hP S β h) (hV' : V' = sheetUniformizer hP S β' h'),
      @T2Space (HatTrans V V') (sheetTopOf hP S h h' V V' hV hV')
  | _, _, rfl, rfl => (inferInstance : T2Space (SheetHatTrans hP S))

theorem sheetParaOf {β β' : O} (h : ∀ g : G, g • β = β) (h' : ∀ g : G, g • β' = β') :
    ∀ (V : ProperCoveringUniformizer (sheetGCTFunctor hP S) β)
      (V' : ProperCoveringUniformizer (sheetGCTFunctor hP S) β')
      (hV : V = sheetUniformizer hP S β h) (hV' : V' = sheetUniformizer hP S β' h'),
      @ParacompactSpace (HatTrans V V') (sheetTopOf hP S h h' V V' hV hV')
  | _, _, rfl, rfl => (inferInstance : ParacompactSpace (SheetHatTrans hP S))

/-- The M-polyfold `M(Ψ̂, Ψ̂')` for sheet uniformizers. -/
def sheetMOf {β β' : O} (h : ∀ g : G, g • β = β) (h' : ∀ g : G, g • β' = β') :
    ∀ (V : ProperCoveringUniformizer (sheetGCTFunctor hP S) β)
      (V' : ProperCoveringUniformizer (sheetGCTFunctor hP S) β')
      (hV : V = sheetUniformizer hP S β h) (hV' : V' = sheetUniformizer hP S β' h'),
      @MPolyfold (HatTrans V V') (sheetTopOf hP S h h' V V' hV hV')
        (sheetT2Of hP S h h' V V' hV hV') (sheetParaOf hP S h h' V V' hV hV')
  | _, _, rfl, rfl => twistM (isScSmoothMap_sheet_smul' hP S) (TranslationTwist.refl G (S × O))

/-- For a uniformizer of the sheet construction: `V = sheetUniformizer β h`. -/
theorem sheet_eq (V : (sheetConstruction hP S).Unif) :
    V.unif = sheetUniformizer hP S V.1.1 V.2.1 := V.2.2

/-- The tautological uniformizer is the uniformizer of every sheet uniformizer. -/
theorem sheetUniformizer_toLocalUniformizer (β : O) (h : ∀ g : G, g • β = β) :
    (sheetUniformizer hP S β h).toLocalUniformizer = LocalUniformizer.tautological PO hP := rfl

variable (htriv : ∀ (g : G) (x : O), g • x = x)

include htriv in
/-- For a trivial action, the uniformizers of the sheet construction are the tautological
one at every point. -/
theorem sheetConstruction_F_eq (β : O) :
    (twistConstruction hP (TranslationTwist.refl G O)).F β =
      (sheetConstruction hP S).toUniformizerConstruction.F β := by
  ext L
  constructor
  · intro hL
    rw [Set.mem_singleton_iff.1 hL]
    exact ⟨_, ⟨(htriv · β), rfl⟩, sheetUniformizer_toLocalUniformizer hP S β _⟩
  · rintro ⟨_, ⟨h, rfl⟩, rfl⟩
    exact Set.mem_singleton _

/-- `p = e_B ∘ (id × π₂) ∘ e_A⁻¹` on the tautological transition M-polyfolds. -/
theorem sheet_transMap_eq {β β' : O} (h : ∀ g : G, g • β = β) (h' : ∀ g : G, g • β' = β')
    (a : SheetHatTrans hP S) :
    (transMap (sheetUniformizer hP S β h) (sheetUniformizer hP S β' h') a :
      TwistTrans hP (TranslationTwist.refl G O)) =
      twistHomeomorph hP (TranslationTwist.refl G O)
        (((twistHomeomorph (isScSmoothMap_sheet_smul' hP S)
          (TranslationTwist.refl G (S × O))).symm a).1,
         ((twistHomeomorph (isScSmoothMap_sheet_smul' hP S)
          (TranslationTwist.refl G (S × O))).symm a).2.2) := by
  have hs : a.mor.2 = a.src := a.src_mor
  have ht : a.mor.1 • a.mor.2 = a.tgt := a.tgt_mor
  refine GroupoidStr.TransitionSet.ext ?_ rfl ?_
  · change a.src.2 = a.mor.2.2
    rw [hs]
  · change a.tgt.2 = a.mor.1 • a.mor.2.2
    rw [← ht]
    rfl

/-- `p` is a local sc-diffeomorphism for sheet uniformizers (over `src`). -/
theorem sheet_isLocalScDiffeo_p {β β' : O} (h : ∀ g : G, g • β = β)
    (h' : ∀ g : G, g • β' = β') :
    (twistM (isScSmoothMap_sheet_smul' hP S) (TranslationTwist.refl G (S × O))).IsLocalScDiffeo
      (twistM hP (TranslationTwist.refl G O))
      fun a : SheetHatTrans hP S => (transMap (sheetUniformizer hP S β h)
        (sheetUniformizer hP S β' h') a : TwistTrans hP (TranslationTwist.refl G O)) := by
  have hsnd : ((discretePolyfold S).prod PO).IsLocalScDiffeo PO Prod.snd :=
    (sheetModel hP S β h).isLocalScDiffeo
  have ha := hsnd.comp (twist_isLocalScDiffeo_src (isScSmoothMap_sheet_smul' hP S)
    (TranslationTwist.refl G (S × O)))
  have hcont : @Continuous _ (TwistTrans hP (TranslationTwist.refl G O)) _ _
      fun a : SheetHatTrans hP S => (transMap (sheetUniformizer hP S β h)
      (sheetUniformizer hP S β' h') a : TwistTrans hP (TranslationTwist.refl G O)) := by
    have e := funext (sheet_transMap_eq hP S h h')
    rw [e]
    exact (twistHomeomorph hP _).continuous.comp
      ((continuous_fst.prodMk (continuous_snd.comp continuous_snd)).comp
        (twistHomeomorph (isScSmoothMap_sheet_smul' hP S) _).symm.continuous)
  exact MPolyfold.isLocalScDiffeo_of_comp_eq ha
    (twist_isLocalScDiffeo_src hP (TranslationTwist.refl G O)) hcont fun _ => rfl

section Fields

variable {β β' β'' : O} (h : ∀ g : G, g • β = β) (h' : ∀ g : G, g • β' = β')
  (h'' : ∀ g : G, g • β'' = β'')

/-- (a) for sheet uniformizers: `s` is a local sc-diffeomorphism. -/
theorem sheetSrcOf : ∀ (V : ProperCoveringUniformizer (sheetGCTFunctor hP S) β)
    (V' : ProperCoveringUniformizer (sheetGCTFunctor hP S) β')
    (hV : V = sheetUniformizer hP S β h) (hV' : V' = sheetUniformizer hP S β' h'),
    letI := sheetTopOf hP S h h' V V' hV hV'
    letI := sheetT2Of hP S h h' V V' hV hV'
    letI := sheetParaOf hP S h h' V V' hV hV'
    (sheetMOf hP S h h' V V' hV hV').IsLocalScDiffeo V.E.PObj GroupoidStr.TransitionSet.src
  | _, _, rfl, rfl => twist_isLocalScDiffeo_src (isScSmoothMap_sheet_smul' hP S) _

/-- (a) for sheet uniformizers: `t` is a local sc-diffeomorphism. -/
theorem sheetTgtOf : ∀ (V : ProperCoveringUniformizer (sheetGCTFunctor hP S) β)
    (V' : ProperCoveringUniformizer (sheetGCTFunctor hP S) β')
    (hV : V = sheetUniformizer hP S β h) (hV' : V' = sheetUniformizer hP S β' h'),
    letI := sheetTopOf hP S h h' V V' hV hV'
    letI := sheetT2Of hP S h h' V V' hV hV'
    letI := sheetParaOf hP S h h' V V' hV hV'
    (sheetMOf hP S h h' V V' hV hV').IsLocalScDiffeo V'.E.PObj GroupoidStr.TransitionSet.tgt
  | _, _, rfl, rfl => twist_isLocalScDiffeo_tgt (isScSmoothMap_sheet_smul' hP S) _

/-- (b) for sheet uniformizers: the unit map is sc-smooth. -/
theorem sheetUnitOf : ∀ (V : ProperCoveringUniformizer (sheetGCTFunctor hP S) β)
    (hV : V = sheetUniformizer hP S β h),
    letI := sheetTopOf hP S h h V V hV hV
    letI := sheetT2Of hP S h h V V hV hV
    letI := sheetParaOf hP S h h V V hV hV
    V.E.PObj.IsScSmoothMap (sheetMOf hP S h h V V hV hV) GroupoidStr.TransitionSet.unit
  | _, rfl => twist_isScSmoothMap_unit (isScSmoothMap_sheet_smul' hP S) _

/-- (b) for sheet uniformizers: the inversion is sc-smooth. -/
theorem sheetInvOf : ∀ (V : ProperCoveringUniformizer (sheetGCTFunctor hP S) β)
    (V' : ProperCoveringUniformizer (sheetGCTFunctor hP S) β')
    (hV : V = sheetUniformizer hP S β h) (hV' : V' = sheetUniformizer hP S β' h'),
    letI := sheetTopOf hP S h h' V V' hV hV'
    letI := sheetT2Of hP S h h' V V' hV hV'
    letI := sheetParaOf hP S h h' V V' hV hV'
    letI := sheetTopOf hP S h' h V' V hV' hV
    letI := sheetT2Of hP S h' h V' V hV' hV
    letI := sheetParaOf hP S h' h V' V hV' hV
    (sheetMOf hP S h h' V V' hV hV').IsScSmoothMap (sheetMOf hP S h' h V' V hV' hV)
      GroupoidStr.TransitionSet.inv
  | _, _, rfl, rfl => twist_isScSmoothMap_inv (isScSmoothMap_sheet_smul' hP S) _

/-- (c) for sheet uniformizers: the multiplication is sc-smooth. -/
theorem sheetMulOf : ∀ (V : ProperCoveringUniformizer (sheetGCTFunctor hP S) β)
    (V' : ProperCoveringUniformizer (sheetGCTFunctor hP S) β')
    (V'' : ProperCoveringUniformizer (sheetGCTFunctor hP S) β'')
    (hV : V = sheetUniformizer hP S β h) (hV' : V' = sheetUniformizer hP S β' h')
    (hV'' : V'' = sheetUniformizer hP S β'' h''),
    letI := sheetTopOf hP S h' h'' V' V'' hV' hV''
    letI := sheetT2Of hP S h' h'' V' V'' hV' hV''
    letI := sheetParaOf hP S h' h'' V' V'' hV' hV''
    letI := sheetTopOf hP S h h' V V' hV hV'
    letI := sheetT2Of hP S h h' V V' hV hV'
    letI := sheetParaOf hP S h h' V V' hV hV'
    letI := sheetTopOf hP S h h'' V V'' hV hV''
    letI := sheetT2Of hP S h h'' V V'' hV hV''
    letI := sheetParaOf hP S h h'' V V'' hV hV''
    MPolyfold.IsScSmoothOnFibredProduct (sheetMOf hP S h' h'' V' V'' hV' hV'')
      (sheetMOf hP S h h' V V' hV hV') (sheetMOf hP S h h'' V V'' hV hV'')
      (sheetSrcOf hP S h' h'' V' V'' hV' hV'') (sheetTgtOf hP S h h' V V' hV hV').isScSmoothMap
      GroupoidStr.TransitionSet.mul
  | _, _, _, rfl, rfl, rfl => twist_isScSmoothMap_mul (isScSmoothMap_sheet_smul' hP S) _

/-- `p` is a local sc-diffeomorphism for sheet uniformizers, over the tautological structure
of `B`. -/
theorem sheetPOf : ∀ (V : ProperCoveringUniformizer (sheetGCTFunctor hP S) β)
    (V' : ProperCoveringUniformizer (sheetGCTFunctor hP S) β')
    (hV : V = sheetUniformizer hP S β h) (hV' : V' = sheetUniformizer hP S β' h')
    (hL : V.toLocalUniformizer = LocalUniformizer.tautological PO hP)
    (hL' : V'.toLocalUniformizer = LocalUniformizer.tautological PO hP),
    letI := sheetTopOf hP S h h' V V' hV hV'
    letI := sheetT2Of hP S h h' V V' hV hV'
    letI := sheetParaOf hP S h h' V V' hV hV'
    letI := twistTopOf hP (TranslationTwist.refl G O) _ _ hL hL'
    letI := twistT2Of hP (TranslationTwist.refl G O) _ _ hL hL'
    letI := twistParaOf hP (TranslationTwist.refl G O) _ _ hL hL'
    (sheetMOf hP S h h' V V' hV hV').IsLocalScDiffeo
      (twistMOf hP (TranslationTwist.refl G O) _ _ hL hL')
      fun a => (transMap V V' a : V.toLocalUniformizer.Trans V'.toLocalUniformizer)
  | _, _, rfl, rfl, _, _ => sheet_isLocalScDiffeo_p hP S h h'

end Fields

/-- **A proper polyfold covering structure** (Definition 17.8.13) for the sheet functor of a
trivial action: the sheet construction, the tautological structure of `B = G ⋉ O`, and the
tautological transition M-polyfolds of `A = G ⋉ (S × O)`. -/
def sheetPolyfoldCoveringStructure :
    ProperPolyfoldCoveringStructure (sheetGCTFunctor hP S) where
  toC := sheetConstruction hP S
  SB := twistConstruction hP (TranslationTwist.refl G O)
  SB_F := sheetConstruction_F_eq hP S htriv
  topH U U' := sheetTopOf hP S U.2.1 U'.2.1 U.unif U'.unif (sheet_eq hP S U) (sheet_eq hP S U')
  t2H U U' := sheetT2Of hP S U.2.1 U'.2.1 U.unif U'.unif (sheet_eq hP S U) (sheet_eq hP S U')
  paraH U U' := sheetParaOf hP S U.2.1 U'.2.1 U.unif U'.unif (sheet_eq hP S U) (sheet_eq hP S U')
  MH U U' := sheetMOf hP S U.2.1 U'.2.1 U.unif U'.unif (sheet_eq hP S U) (sheet_eq hP S U')
  isLocalScDiffeo_src U U' :=
    sheetSrcOf hP S U.2.1 U'.2.1 U.unif U'.unif (sheet_eq hP S U) (sheet_eq hP S U')
  isLocalScDiffeo_tgt U U' :=
    sheetTgtOf hP S U.2.1 U'.2.1 U.unif U'.unif (sheet_eq hP S U) (sheet_eq hP S U')
  isScSmoothMap_unit U := sheetUnitOf hP S U.2.1 U.unif (sheet_eq hP S U)
  isScSmoothMap_inv U U' :=
    sheetInvOf hP S U.2.1 U'.2.1 U.unif U'.unif (sheet_eq hP S U) (sheet_eq hP S U')
  isScSmoothMap_mul U U' U'' :=
    sheetMulOf hP S U.2.1 U'.2.1 U''.2.1 U.unif U'.unif U''.unif (sheet_eq hP S U)
      (sheet_eq hP S U') (sheet_eq hP S U'')
  isLocalScDiffeo_p U U' :=
    sheetPOf hP S U.2.1 U'.2.1 U.unif U'.unif (sheet_eq hP S U) (sheet_eq hP S U') _ _

end Sheet

section Z3

open GCT GCT.PolyfoldConstruction

/-- `ℤ/3` acting trivially on the two sheets `Bool`. -/
local instance instMulActionZ3Bool : MulAction (Multiplicative (ZMod 3)) Bool where
  smul _ b := b
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- **A proper polyfold covering functor** (Definition 17.8.13): two sheets of `ℤ/3 ⋉ ℝ` over
`ℤ/3 ⋉ ℝ` (`ℤ/3` acting trivially). -/
def z3PolyfoldCoveringFunctor :
    ProperPolyfoldCoveringFunctor (sheetGCT isScSmoothMap_z3_smul Bool)
      (GCT.translation (Multiplicative (ZMod 3)) (Fin 1 → ℝ) isScSmoothMap_z3_smul) where
  P := sheetGCTFunctor isScSmoothMap_z3_smul Bool
  isProperCovering := isProperCoveringGCT_sheet isScSmoothMap_z3_smul fun _ _ => rfl
  S := sheetPolyfoldCoveringStructure isScSmoothMap_z3_smul Bool fun _ _ => rfl

/-- The witness is non-degenerate: every `F(β)` is non-empty, `τ̂⁻¹(o_β)` has two points, and the
isotropy group `ℤ/3` of every point is non-trivial. -/
theorem z3PolyfoldCoveringFunctor_nondegenerate :
    (∀ β, (z3PolyfoldCoveringFunctor.S.toC.F β).Nonempty) ∧
      (∀ β (U : ProperCoveringUniformizer z3PolyfoldCoveringFunctor.P β),
        U ∈ z3PolyfoldCoveringFunctor.S.toC.F β → U.model.fiber.ncard = 2) ∧
      Nontrivial (Multiplicative (ZMod 3)) := by
  refine ⟨fun β => sheetConstruction_nonempty isScSmoothMap_z3_smul Bool (fun _ _ => rfl) β,
    ?_, inferInstance⟩
  rintro β _ ⟨h, rfl⟩
  change (sheetModel isScSmoothMap_z3_smul Bool β h).fiber.ncard = 2
  rw [sheetModel_fiber]
  have : (univ ×ˢ {β} : Set (Bool × (Fin 1 → ℝ))) = {(true, β), (false, β)} := by
    ext ⟨b, x⟩
    cases b <;> simp
  rw [this, ncard_pair (by simp)]

end Z3

end Polyfold
