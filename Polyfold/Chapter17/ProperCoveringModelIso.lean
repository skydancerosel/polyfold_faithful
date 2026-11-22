import Polyfold.Chapter17.ProperCoveringLift

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17, §17.8,
p. 834, after Lemma 17.8.9: a connected proper covering model is isomorphic to the model of
pp. 829–831 built from data `A, B, τ` ("an easy exercise").  Numbers and pages are the 2021 text's.

# A connected proper covering model is the model of its data `A, B, τ`

## The text, paraphrased

(p. 834) Let `τ̂ : E → G ⋉ O` be a proper covering model with `O` connected.  Take `D = 𝐀_ō`, the
full subcategory of `E` on `τ̂⁻¹(ō)`, with the covering functor `φ ↦ g_φ` into `G`; `A(y) = (U(y),
y)`, `A(φ) = φ ∗`; `B(β) = (O, ō)`, `B(g) = g ∗`; `τ_y = τ̂|U(y)`.  "It is an easy exercise" that
the construction (17.94)–(17.98) applied to these data gives an ep-groupoid isomorphic to `E`, by
an isomorphism compatible with `τ̂`.

## What is formalized

* `ProperCoveringModel.FibD` (`𝐀_ō`, the full subcategory on `τ̂⁻¹(ō)`), `coveringD` (`φ ↦ g_φ`),
  **`isCoveringFunctor_coveringD`** (Definition 8.5.5).  `isClosed_U`, `U_eq_preimage`; the data
  `objA`, `modelA`, `actionScDiffeo`, `modelB`, `tauApp`, `modelτ`, **`modelLift`**.
* The isomorphism: `objMap` (`(y, q) ↦ q`) and `objInv` (`q ↦ (y_q, q)`); `morMap`
  (`((a, b, φ), q) ↦ Γ⁻¹((g_φ, τ̂ q), q)`) and `morInv hO`.  `objInv_objMap`, `objMap_objInv`,
  `morInv_morMap`, `morMap_morInv`; `src_morMap`, `tgt_morMap` (for `O` connected), `obj_objMap`,
  `mor_morMap` (`τ̂ ∘ Ψ = τ̂'`), `morMap_comp`, `morMap_unit`; `isScDiffeoOn_obj` and
  `isScDiffeoOn_mor` (both maps are sc-diffeomorphisms).
* **`easy_exercise`**: all of it in one statement.
* Witness: `sheetModel_units` (two sheets `{±1} × ℝ`, `ℤˣ` acting by `±1`), `easy_exercise_units`.

## Readings

* **Universe.**  `A(y) = U(y) ⊆ E` and `B(β) = O` are objects of one `Diff*_sc`, so `E` and `O`
  live in one universe.
* **Finiteness.**  The construction of p. 830 is for finite `A_β` with finite morphism sets;
  we take `Fintype` instances on `𝐀_ō` and its morphism sets (they exist exactly when `τ̂⁻¹(ō)` is
  finite, `fintypeFibD`).
* **`G`** carries a `Fintype` instance as in Chapter 8's `geometricLiftTarget`; the target there is
  `ULift G ⋉ O`, and `mor_morMap` compares group elements through `ULift.down`.
* **Connectedness** of `O` is used only for the target: `t(Ψ((a, b, φ), q)) = φ ∗ q`, i.e. that the
  morphisms of `E` through `U(a)` with group index `g_φ` end in `U(b)` (Lemma 17.8.9).
-/

open Set Function Topology CategoryTheory

noncomputable section

universe u

namespace Polyfold

open EpGroupoid EpGroupoid.Examples GeometricLift

section Iso

variable {G : Type u} [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
  {O : Type u} [TopologicalSpace O] [T2Space O] [ParacompactSpace O] [MulAction G O]
  {P : MPolyfold O} {hP : ∀ g : G, P.IsScSmoothMap P fun y => g • y}
  {ObjE MorE : Type u} [TopologicalSpace ObjE] [T2Space ObjE] [ParacompactSpace ObjE]
  [TopologicalSpace MorE] [T2Space MorE] [ParacompactSpace MorE] {E : EpGroupoid ObjE MorE}

namespace ProperCoveringModel

variable {τ : EpFunctor E (actionEpGroupoid hP)} (M : ProperCoveringModel τ)

/-! ### The data `A, B, τ` of a model -/

/-- **`𝐀_ō`**: the full subcategory of `E` on `τ̂⁻¹(ō)`. -/
abbrev FibD : Type u := E.toGroupoidStr.FullOb M.fiber

/-- **The covering functor `𝐀_ō → G`, `φ ↦ g_φ`.** -/
def coveringD : M.FibD ⥤ SingleObj G where
  obj _ := SingleObj.star G
  map ψ := (M.groupIndex ψ.1 : G)
  map_id a := M.groupIndex_unit a.val
  map_comp ψ ψ' := by
    rw [SingleObj.comp_as_mul]
    exact M.groupIndex_comp (ψ'.2.1.trans ψ.2.2.symm)

theorem coveringD_map {a b : M.FibD} (ψ : a ⟶ b) :
    ((M.coveringD.map ψ : SingleObj.star G ⟶ SingleObj.star G) : G) = M.groupIndex ψ.1 := rfl

/-- `Γ⁻¹((g, a), a)` ends in `τ̂⁻¹(ō)` for `a ∈ τ̂⁻¹(ō)`. -/
theorem tgt_liftMor_mem {a : ObjE} (ha : a ∈ M.fiber) (g : G) :
    E.tgt (M.liftMor g a) ∈ M.fiber := by
  change τ.obj _ = M.pt
  rw [M.obj_tgt, M.src_liftMor, M.groupIndex_liftMor, show τ.obj a = M.pt from ha, M.smul_pt]

/-- **`φ ↦ g_φ` is a covering functor** (Definition 8.5.5): `φ ↦ (g_φ, s φ)` is a bijection onto
`G × τ̂⁻¹(ō)`. -/
theorem isCoveringFunctor_coveringD : IsCoveringFunctor M.coveringD := by
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨φ, hφs, hφt⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩, ⟨φ', hφs', hφt'⟩⟩ h
    simp only [coveringMap, Prod.mk.injEq] at h
    obtain ⟨hg, h2⟩ := h
    obtain rfl : a = a' := congrArg GroupoidStr.FullOb.val h2
    obtain rfl : φ = φ' := M.eq_of_groupIndex_eq hg ((hφs.trans hφs'.symm))
    obtain rfl : b = b' := hφt.symm.trans hφt'
    rfl
  · rintro ⟨g, ⟨a, ha⟩⟩
    refine ⟨⟨⟨a, ha⟩, ⟨_, M.tgt_liftMor_mem ha g⟩, ⟨M.liftMor g a, M.src_liftMor g a, rfl⟩⟩, ?_⟩
    exact Prod.ext (M.groupIndex_liftMor g a) rfl

/-- `U(y) = {q | y_q = y}`. -/
theorem U_eq_preimage {y : ObjE} (hy : y ∈ M.fiber) : M.U y = M.sheetIndex ⁻¹' {y} := by
  ext e
  refine ⟨fun he => M.sheetIndex_eq hy he, fun h => ?_⟩
  rw [← (h : M.sheetIndex e = y)]
  exact M.mem_U_sheetIndex e

/-- The sheets `U(y)` are closed (their complement is the union of the other sheets). -/
theorem isClosed_U {y : ObjE} (hy : y ∈ M.fiber) : IsClosed (M.U y) := by
  rw [M.U_eq_preimage hy]
  exact M.isLocallyConstant_sheetIndex.isClosed_fiber y

instance instParacompactU (y : M.FibD) : ParacompactSpace (M.U y.val) :=
  (M.isClosed_U y.mem).isClosedEmbedding_subtypeVal.paracompactSpace

instance instNonemptyU (y : M.FibD) : Nonempty (M.U y.val) := ⟨⟨y.val, M.mem_U _ y.mem⟩⟩

/-- **`A(y) = (U(y), y)`.** -/
def objA (y : M.FibD) : PointedMPolyfoldCat.{u} :=
  ⟨MPolyfoldCat.ofOpen E.PObj (M.isOpen_U y.mem), ⟨y.val, M.mem_U _ y.mem⟩⟩

theorem mem_morOn_of_hom {a b : M.FibD} (ψ : a ⟶ b) : ψ.1 ∈ E.morOn M.fiber :=
  ⟨by rw [ψ.2.1]; exact a.mem, by rw [ψ.2.2]; exact b.mem⟩

theorem isScDiffeoOn_fiberAct_hom {a b : M.FibD} (ψ : a ⟶ b) :
    E.PObj.IsScDiffeoOn E.PObj (M.fiberAct ψ.1) (M.fiberAct (E.inv ψ.1)) (M.U a.val)
      (M.U b.val) := by
  have h := M.isScDiffeoOn_fiberAct (M.mem_morOn_of_hom ψ)
  rwa [ψ.2.1, ψ.2.2] at h

theorem fiberAct_hom_pt {a b : M.FibD} (ψ : a ⟶ b) : M.fiberAct ψ.1 a.val = b.val := by
  have h := M.fiberAct_src (M.mem_morOn_of_hom ψ)
  rwa [ψ.2.1, ψ.2.2] at h

/-- **`A : 𝐀_ō → Diff*_sc`**, `A(φ) = φ ∗ : (U(s φ), s φ) → (U(t φ), t φ)`. -/
def modelA : M.FibD ⥤ PointedMPolyfoldCat.{u} where
  obj := M.objA
  map {a b} ψ := ⟨ScDiffeo.ofOpen (M.isOpen_U a.mem) (M.isOpen_U b.mem)
    (M.isScDiffeoOn_fiberAct_hom ψ),
    Subtype.ext (M.fiberAct_hom_pt ψ)⟩
  map_id a := PointedScDiffeo.ext (funext fun z => Subtype.ext (M.fiberAct_unit a.mem z.2))
  map_comp ψ ψ' := PointedScDiffeo.ext (funext fun z => Subtype.ext
    (M.fiberAct_comp (M.mem_morOn_of_hom ψ) (ψ'.2.1.trans ψ.2.2.symm) z.1))

/-- The M-polyfold `O`, as an object of `Diff_sc`. -/
abbrev objO (_M : ProperCoveringModel τ) : MPolyfoldCat.{u} := { carrier := O, P := P }

/-- `g ∗ : O → O`, as a morphism of `Diff_sc`. -/
def actionScDiffeo (g : G) : ScDiffeo M.objO M.objO where
  toFun o := g • o
  invFun o := g⁻¹ • o
  isScDiffeoOn :=
    { isScSmoothOn := hP g
      isScSmoothOn_inv := hP g⁻¹
      mapsTo := mapsTo_univ _ _
      mapsTo_inv := mapsTo_univ _ _
      left_inv := fun o _ => inv_smul_smul g o
      right_inv := fun o _ => smul_inv_smul g o }

/-- **`B : G ⋉ {β} → Diff*_sc`**, `B(β) = (O, ō)`, `B(g) = g ∗`. -/
def modelB : SingleObj G ⥤ PointedMPolyfoldCat.{u} where
  obj _ := ⟨M.objO, M.pt⟩
  map g := ⟨M.actionScDiffeo g, M.smul_pt g⟩
  map_id _ := PointedScDiffeo.ext (funext fun o => one_smul G o)
  map_comp g h := PointedScDiffeo.ext (funext fun o => mul_smul (α := G) (β := O) h g o)

/-- `τ_y = τ̂|U(y) : U(y) → O`, as a morphism of `Diff_sc`. -/
def tauApp (y : M.FibD) : ScDiffeo (M.objA y).obj M.objO where
  toFun z := τ.obj z.1
  invFun o := ⟨M.σ y.val o, M.σ_mem_U y.mem o⟩
  isScDiffeoOn :=
    have h := M.isScDiffeoOn_U _ y.mem
    { isScSmoothOn := h.isScSmoothOn.comp (MPolyfold.isScSmoothMap_subtypeVal (M.isOpen_U y.mem))
        fun z _ => z.2
      isScSmoothOn_inv := MPolyfold.IsScSmoothMap.codRestrict_restrictOpen (M.isOpen_U y.mem)
        h.isScSmoothOn_inv _
      mapsTo := mapsTo_univ _ _
      mapsTo_inv := mapsTo_univ _ _
      left_inv := fun z _ => Subtype.ext (h.left_inv z.1 z.2)
      right_inv := fun o _ => h.right_inv o (mem_univ o) }

/-- **`τ : A → B ∘ P`**, `τ_y = τ̂|U(y)`. -/
def modelτ : M.modelA ⟶ M.coveringD ⋙ M.modelB where
  app y := ⟨M.tauApp y, M.mem_fiber_iff.1 y.mem⟩
  naturality _ _ ψ := PointedScDiffeo.ext (funext fun z =>
    M.obj_fiberAct (M.mem_morOn_of_hom ψ) z.1)

/-- **The data `A, B, τ` of a proper covering model** (p. 834). -/
def modelLift : PointedGeometricLift M.coveringD := ⟨M.modelA, M.modelB, M.modelτ⟩

/-- With `τ̂⁻¹(ō)` finite, `𝐀_ō` and its morphism sets are finite. -/
theorem finite_hom (a b : M.FibD) : Finite (a ⟶ b) :=
  Finite.of_injective (fun ψ : a ⟶ b => M.groupIndex ψ.1) fun ψ ψ' h =>
    Subtype.ext (M.eq_of_groupIndex_eq h (ψ.2.1.trans ψ'.2.1.symm))

theorem finite_fibD (hfin : M.fiber.Finite) : Finite M.FibD :=
  have := hfin.to_subtype
  Finite.of_injective (fun y : M.FibD => (⟨y.val, y.mem⟩ : M.fiber)) fun _ _ h =>
    GroupoidStr.FullOb.ext (congrArg Subtype.val h)

/-! ### The isomorphism -/

/-- The ep-groupoid built from `A, B, τ` (17.94)–(17.95). -/
abbrev L : GeometricLift M.coveringD := M.modelLift.toGeometricLift

theorem yObj_ext {p p' : M.L.YObj} (h1 : p.1.val = p'.1.val)
    (h2 : (p.2 : M.U p.1.val).1 = (p'.2 : M.U p'.1.val).1) : p = p' := by
  obtain ⟨⟨a, ha⟩, ⟨z, hz⟩⟩ := p
  obtain ⟨⟨a', ha'⟩, ⟨z', hz'⟩⟩ := p'
  obtain rfl : a = a' := h1
  obtain rfl : z = z' := h2
  rfl

theorem yMor_ext {p p' : M.L.YMor} (h1 : p.1.1.val = p'.1.1.val)
    (h2 : p.1.2.1.val = p'.1.2.1.val) (h3 : p.1.2.2.1 = p'.1.2.2.1)
    (h4 : (p.2 : M.U p.1.1.val).1 = (p'.2 : M.U p'.1.1.val).1) : p = p' := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨φ, hφ⟩⟩, ⟨z, hz⟩⟩ := p
  obtain ⟨⟨⟨a', ha'⟩, ⟨b', hb'⟩, ⟨φ', hφ'⟩⟩, ⟨z', hz'⟩⟩ := p'
  obtain rfl : a = a' := h1
  obtain rfl : b = b' := h2
  obtain rfl : φ = φ' := h3
  obtain rfl : z = z' := h4
  rfl

/-- **`Ψ : ⊔ U(y) → E`** on objects, `(y, q) ↦ q`. -/
def objMap (p : M.L.YObj) : ObjE := (p.2 : M.U p.1.val).1

/-- The inverse, `q ↦ (y_q, q)`. -/
def objInv (e : ObjE) : M.L.YObj :=
  ⟨⟨M.sheetIndex e, M.sheetIndex_mem e⟩, (⟨e, M.mem_U_sheetIndex e⟩ : M.U (M.sheetIndex e))⟩

theorem objMap_objInv (e : ObjE) : M.objMap (M.objInv e) = e := rfl

theorem objInv_objMap (p : M.L.YObj) : M.objInv (M.objMap p) = p :=
  M.yObj_ext (M.sheetIndex_eq p.1.mem (p.2 : M.U p.1.val).2) rfl

/-- **`Ψ` on morphisms**, `((a, b, φ), q) ↦ Γ⁻¹((g_φ, τ̂ q), q)`. -/
def morMap (p : M.L.YMor) : MorE := M.liftMor (M.groupIndex p.1.2.2.1) (p.2 : M.U p.1.1.val).1

theorem tgt_baseMor (hO : M.Connected) (ψ : MorE) :
    E.tgt (M.baseMor ψ) = M.sheetIndex (E.tgt ψ) := by
  rw [(M.constant_on_component (M.mem_connectedComponent_baseMor hO ψ)).2.1,
    M.sheetIndex_of_mem_fiber (M.baseMor_mem ψ).2]

theorem src_baseMor (ψ : MorE) : E.src (M.baseMor ψ) = M.sheetIndex (E.src ψ) :=
  M.src_liftMor _ _

/-- The inverse of `Ψ` on morphisms, `ψ ↦ ((y_{s ψ}, y_{t ψ}, φ_ψ), s ψ)`. -/
def morInv (hO : M.Connected) (ψ : MorE) : M.L.YMor :=
  ⟨⟨⟨M.sheetIndex (E.src ψ), M.sheetIndex_mem _⟩, ⟨M.sheetIndex (E.tgt ψ), M.sheetIndex_mem _⟩,
    ⟨M.baseMor ψ, M.src_baseMor ψ, M.tgt_baseMor hO ψ⟩⟩,
    (⟨E.src ψ, M.mem_U_sheetIndex _⟩ : M.U (M.sheetIndex (E.src ψ)))⟩

theorem groupIndex_baseMor (ψ : MorE) : M.groupIndex (M.baseMor ψ) = M.groupIndex ψ :=
  M.groupIndex_liftMor _ _

theorem morMap_morInv (hO : M.Connected) (ψ : MorE) : M.morMap (M.morInv hO ψ) = ψ := by
  change M.liftMor (M.groupIndex (M.baseMor ψ)) (E.src ψ) = ψ
  rw [M.groupIndex_baseMor, M.liftMor_eq]

theorem src_morMap (p : M.L.YMor) : E.src (M.morMap p) = (p.2 : M.U p.1.1.val).1 :=
  M.src_liftMor _ _

theorem groupIndex_morMap (p : M.L.YMor) : M.groupIndex (M.morMap p) = M.groupIndex p.1.2.2.1 :=
  M.groupIndex_liftMor _ _

theorem baseMor_morMap (p : M.L.YMor) : M.baseMor (M.morMap p) = p.1.2.2.1 := by
  rw [baseMor, M.groupIndex_morMap, M.src_morMap,
    M.sheetIndex_eq p.1.1.mem (p.2 : M.U p.1.1.val).2]
  have h := M.liftMor_eq p.1.2.2.1
  rwa [p.1.2.2.2.1] at h

theorem morInv_morMap (hO : M.Connected) (p : M.L.YMor) : M.morInv hO (M.morMap p) = p := by
  refine M.yMor_ext ?_ ?_ (M.baseMor_morMap p) (M.src_morMap p)
  · change M.sheetIndex (E.src (M.morMap p)) = _
    rw [M.src_morMap]
    exact M.sheetIndex_eq p.1.1.mem (p.2 : M.U p.1.1.val).2
  · change M.sheetIndex (E.tgt (M.morMap p)) = _
    rw [← M.tgt_baseMor hO, M.baseMor_morMap]
    exact p.1.2.2.2.2

/-- `t(Ψ((a, b, φ), q)) = φ ∗ q` (Lemma 17.8.9), for `O` connected. -/
theorem tgt_morMap (hO : M.Connected) (p : M.L.YMor) :
    E.tgt (M.morMap p) = M.objMap (M.L.yTgt p) := by
  have hc := M.mem_connectedComponent_baseMor hO (M.morMap p)
  rw [M.baseMor_morMap] at hc
  rw [M.lemma_17_8_9 (M.mem_morOn_of_hom p.1.2.2) hc, M.src_morMap]
  rfl

/-- `Ψ` preserves composition. -/
theorem morMap_comp (p q : M.L.YMor) (h : M.L.ySrc p = M.L.yTgt q) (hO : M.Connected) :
    M.morMap (M.L.yComp p q) = E.comp (M.morMap p) (M.morMap q) := by
  have hpq : E.src (M.morMap p) = E.tgt (M.morMap q) := by
    rw [M.tgt_morMap hO, M.src_morMap, ← h]
    rfl
  refine M.eq_of_groupIndex_eq ?_ ?_
  · rw [M.groupIndex_comp hpq, M.groupIndex_morMap, M.groupIndex_morMap, M.groupIndex_morMap]
    refine GeometricLift.composable_cases (L := M.L)
      (P := fun p q => M.groupIndex (M.L.yComp p q).1.2.2.1 =
        M.groupIndex p.1.2.2.1 * M.groupIndex q.1.2.2.1) h ?_
    intro a b c ψ γ z
    change M.groupIndex (homComp ⟨a, b, ψ⟩ ⟨c, a, γ⟩).2.1 = _
    rw [homComp_mk]
    exact M.groupIndex_comp (ψ.2.1.trans γ.2.2.symm)
  · rw [E.src_comp _ _ hpq, M.src_morMap, M.src_morMap]
    rfl

/-- `Ψ` preserves units. -/
theorem morMap_unit (p : M.L.YObj) : M.morMap (M.L.yUnit p) = E.unit (M.objMap p) := by
  refine M.eq_of_groupIndex_eq ?_ ?_
  · rw [M.groupIndex_morMap, M.groupIndex_unit]
    exact M.groupIndex_unit p.1.val
  · rw [M.src_morMap, E.src_unit]
    rfl

/-- `q ↦ Γ⁻¹((g, τ̂ q), q)` is sc-smooth. -/
theorem isScSmoothMap_liftMor (g : G) : E.PObj.IsScSmoothMap E.PMor (M.liftMor g) := by
  have := MPolyfold.paracompactSpace_prod (actionEpGroupoid hP).PMor E.PObj
  have := ((actionEpGroupoid hP).PMor.prod E.PObj).paracompactSpace_subtype
    (MPolyfold.fibredProduct (actionEpGroupoid hP).src τ.obj)
  have := MPolyfold.paracompactSpace_prod (discretePolyfold G) P
  refine M.isScDiffeoOn_ΓInv.isScSmoothOn_inv.comp ?_ (mapsTo_univ _ _)
  refine MPolyfold.isScSmoothOn_subPolyfold_of_val
    (MPolyfold.isSubMPolyfold_fibredProduct (actionEpGroupoid hP).isLocalScDiffeo_src
      τ.isScSmoothMap_obj) (f := fun e : ObjE => (⟨((g, τ.obj e), e), rfl⟩ :
      MPolyfold.fibredProduct (actionEpGroupoid hP).src τ.obj)) ?_
  exact MPolyfold.IsScSmoothOn.prodMk (MPolyfold.IsScSmoothOn.prodMk
    (isScSmoothMap_const_discrete g) τ.isScSmoothMap_obj) MPolyfold.isScSmoothMap_id

/-! ### Compatibility with `τ̂` and sc-smoothness -/

variable [Fintype G] [Fintype M.FibD] [∀ a b : M.FibD, Fintype (a ⟶ b)]

/-- `τ̂ ∘ Ψ = τ̂'` on objects. -/
theorem obj_objMap (p : M.L.YObj) :
    τ.obj (M.objMap p) = (geometricLiftFunctor M.L).obj p := rfl

/-- `τ̂ ∘ Ψ = τ̂'` on morphisms (through `ULift.down`). -/
theorem mor_morMap (p : M.L.YMor) :
    τ.mor (M.morMap p) = (((geometricLiftFunctor M.L).mor p).1.down,
      ((geometricLiftFunctor M.L).mor p).2) := by
  rw [M.mor_eq, M.groupIndex_morMap, M.src_morMap]
  rfl

omit [Fintype G] in
/-- The map `o ↦ (y, τ_y⁻¹ o)` into the summand `U(y)` of `⊔ U(y)`. -/
theorem isScSmoothMap_sigma_σ (y : M.FibD) :
    P.IsScSmoothMap (geometricLiftSource M.L).PObj fun o =>
      (⟨y, (⟨M.σ y.val o, M.σ_mem_U y.mem o⟩ : M.U y.val)⟩ : M.L.YObj) :=
  (MPolyfold.isScSmoothMap_sigmaMk (fun y : M.FibD => (M.L.LD.obj y).P) y).comp
    (MPolyfold.IsScSmoothMap.codRestrict_restrictOpen (M.isOpen_U y.mem)
      (M.isScDiffeoOn_U _ y.mem).isScSmoothOn_inv _)

omit [Fintype G] in
/-- **`Ψ` is an sc-diffeomorphism on objects.** -/
theorem isScDiffeoOn_obj :
    (geometricLiftSource M.L).PObj.IsScDiffeoOn E.PObj M.objMap M.objInv univ univ where
  isScSmoothOn := (MPolyfold.isScSmoothMap_sigma_iff _).2 fun y =>
    MPolyfold.isScSmoothMap_subtypeVal (M.isOpen_U y.mem)
  isScSmoothOn_inv := by
    refine MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun e _ => ?_
    set y : M.FibD := ⟨M.sheetIndex e, M.sheetIndex_mem e⟩
    refine ⟨M.U y.val, M.isOpen_U y.mem, M.mem_U_sheetIndex e, subset_univ _, ?_⟩
    refine ((M.isScSmoothMap_sigma_σ y).comp τ.isScSmoothMap_obj).mono
      (M.isOpen_U y.mem) (subset_univ _) |>.congr fun e' he' => ?_
    exact M.yObj_ext (M.sheetIndex_eq y.mem he').symm (M.σ_obj y.mem he')
  mapsTo := mapsTo_univ _ _
  mapsTo_inv := mapsTo_univ _ _
  left_inv p _ := M.objInv_objMap p
  right_inv e _ := M.objMap_objInv e

omit [Fintype G] in
/-- **`Ψ` is an sc-diffeomorphism on morphisms** (for `O` connected). -/
theorem isScDiffeoOn_mor (hO : M.Connected) :
    (geometricLiftSource M.L).PMor.IsScDiffeoOn E.PMor M.morMap (M.morInv hO) univ univ where
  isScSmoothOn := (MPolyfold.isScSmoothMap_sigma_iff _).2 fun ψ =>
    (M.isScSmoothMap_liftMor (M.groupIndex ψ.2.2.1)).comp
      (MPolyfold.isScSmoothMap_subtypeVal (M.isOpen_U ψ.1.mem))
  isScSmoothOn_inv := by
    refine MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun ψ _ => ?_
    obtain ⟨W, hW, hψW, hWc⟩ := (IsLocallyConstant.iff_exists_open _).1
      M.isLocallyConstant_groupIndex_sheetIndex ψ
    set i := (M.morInv hO ψ).1
    have hsm : (geometricLiftSource M.L).PMor.IsScSmoothOn E.PMor M.morMap univ :=
      (MPolyfold.isScSmoothMap_sigma_iff _).2 fun ψ =>
        (M.isScSmoothMap_liftMor (M.groupIndex ψ.2.2.1)).comp
          (MPolyfold.isScSmoothMap_subtypeVal (M.isOpen_U ψ.1.mem))
    have hmk : P.IsScSmoothMap (geometricLiftSource M.L).PMor fun o =>
        (⟨i, (⟨M.σ i.1.val o, M.σ_mem_U i.1.mem o⟩ : M.U i.1.val)⟩ : M.L.YMor) :=
      (MPolyfold.isScSmoothMap_sigmaMk
        (fun ψ : (Σ a b : M.FibD, a ⟶ b) => (M.L.LD.obj ψ.1).P) i).comp
        (MPolyfold.IsScSmoothMap.codRestrict_restrictOpen (M.isOpen_U i.1.mem)
          (M.isScDiffeoOn_U _ i.1.mem).isScSmoothOn_inv _)
    refine ⟨W, hW, hψW, subset_univ _, ?_⟩
    refine ((hmk.comp τ.isScSmoothMap_obj).comp E.isScSmoothMap_src).mono hW (subset_univ _)
      |>.congr fun ψ' hψ' => ?_
    have hc := hWc ψ' hψ'
    simp only [Prod.mk.injEq] at hc
    obtain ⟨hg, hs⟩ := hc
    have hb : M.baseMor ψ' = M.baseMor ψ := by rw [baseMor, baseMor, hg, hs]
    refine M.yMor_ext ?_ ?_ ?_ ?_
    · exact hs.symm
    · change M.sheetIndex (E.tgt ψ) = M.sheetIndex (E.tgt ψ')
      rw [← M.tgt_baseMor hO, ← M.tgt_baseMor hO, hb]
    · exact hb.symm
    · change M.σ (M.sheetIndex (E.src ψ)) (τ.obj (E.src ψ')) = E.src ψ'
      rw [← hs, M.σ_sheetIndex]
  mapsTo := mapsTo_univ _ _
  mapsTo_inv := mapsTo_univ _ _
  left_inv p _ := M.morInv_morMap hO p
  right_inv ψ _ := M.morMap_morInv hO ψ

/-- **The "easy exercise" (p. 834)**: a connected proper covering model `τ̂ : E → G ⋉ O` with
finite `τ̂⁻¹(ō)` is isomorphic to the model of its data `A, B, τ` (`modelLift`): `Ψ` is an
sc-diffeomorphism on objects and on morphisms, commutes with source, target, composition and
units, and `τ̂ ∘ Ψ = τ̂'`. -/
theorem easy_exercise (hO : M.Connected) :
    IsCoveringFunctor M.coveringD ∧
    (geometricLiftSource M.L).PObj.IsScDiffeoOn E.PObj M.objMap M.objInv univ univ ∧
    (geometricLiftSource M.L).PMor.IsScDiffeoOn E.PMor M.morMap (M.morInv hO) univ univ ∧
    (∀ p, E.src (M.morMap p) = M.objMap (M.L.ySrc p)) ∧
    (∀ p, E.tgt (M.morMap p) = M.objMap (M.L.yTgt p)) ∧
    (∀ p q, M.L.ySrc p = M.L.yTgt q →
      M.morMap (M.L.yComp p q) = E.comp (M.morMap p) (M.morMap q)) ∧
    (∀ p, M.morMap (M.L.yUnit p) = E.unit (M.objMap p)) ∧
    (∀ p, τ.obj (M.objMap p) = (geometricLiftFunctor M.L).obj p) ∧
    (∀ p, τ.mor (M.morMap p) = (((geometricLiftFunctor M.L).mor p).1.down,
      ((geometricLiftFunctor M.L).mor p).2)) :=
  ⟨M.isCoveringFunctor_coveringD, M.isScDiffeoOn_obj, M.isScDiffeoOn_mor hO, M.src_morMap,
    M.tgt_morMap hO, fun p q h => M.morMap_comp p q h hO, M.morMap_unit, M.obj_objMap,
    M.mor_morMap⟩

end ProperCoveringModel

end Iso

/-! ### Witness: the two-sheet model `ℤˣ ⋉ ({±1} × ℝ) → ℤˣ ⋉ ℝ` -/

section Witness

open ProperCoveringModel

noncomputable instance : Fintype sheetModel_units.FibD :=
  have := sheetModel_units.finite_fibD
    (Set.finite_of_ncard_ne_zero (by rw [sheetModel_units_nontrivial.1]; norm_num))
  Fintype.ofFinite _

noncomputable instance (a b : sheetModel_units.FibD) : Fintype (a ⟶ b) :=
  have := sheetModel_units.finite_hom a b
  Fintype.ofFinite _

/-- **The "easy exercise" for the two-sheet model** (`τ̂⁻¹(0)` has two points, `-1 ∈ ℤˣ` acts
nontrivially on `ℝ`). -/
theorem easy_exercise_units :
    IsCoveringFunctor sheetModel_units.coveringD ∧
    (geometricLiftSource sheetModel_units.L).PObj.IsScDiffeoOn
      (sheetEp isScSmoothMap_units_smul ℤˣ).PObj sheetModel_units.objMap
      sheetModel_units.objInv univ univ ∧
    sheetModel_units.fiber.ncard = 2 :=
  ⟨(sheetModel_units.easy_exercise sheetModel_units_connected).1,
    (sheetModel_units.easy_exercise sheetModel_units_connected).2.1,
    sheetModel_units_nontrivial.1⟩

end Witness

end Polyfold
