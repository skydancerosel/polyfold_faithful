import Polyfold.Chapter17.ProperCoveringModel
import Polyfold.Chapter7.SubGroupoid

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17, §17.8:
the discussion after Remark 17.8.5 (pp. 831–832, (17.99)) and **Proposition 17.8.6** (p. 832).
Numbers and pages are the 2021 text's.

# Restricting a proper covering model; connected models

## The text, paraphrased

(pp. 831–832) For a proper covering model `τ̂ : E → G ⋉ O` with distinguished point `ō`, the
connected component `C` of `ō` satisfies `g ∗ C = C` (a path from `ō` to `x` is moved by `g` to a
path from `ō` to `g ∗ x`); with `U'(y) = (τ̂|U(y))⁻¹(C)` and `E' = ⊔ U'(y)`, the restriction
`τ̂' : E' → G ⋉ C` to the full subcategory on `E'` is a connected proper covering model (17.99).
One may first replace `O` by a `G`-invariant open neighbourhood `O*` of `ō` and `E` by
`E* = τ̂⁻¹(O*)`; the restriction is a proper covering model `E* → G ⋉ O*`.
(Proposition 17.8.6) For every open neighbourhood `U` of `ō` there is a `G`-invariant connected
open neighbourhood `O' ⊆ U` of `ō` such that the restriction `τ̂' : E' → G ⋉ O'` to the full
subcategory on `τ̂⁻¹(O')` is a connected proper covering model with distinguished element `ō`.

## What is formalized

* `MPolyfold.isScDiffeoOn_subtype`: an sc-diffeomorphism restricts to sub-M-polyfolds.
* **Restriction to an open `G`-invariant `O'`** (`O' : SubMulAction G O`, open, `ō ∈ O'`):
  `restrictObjPolyfold` (the open sub-M-polyfold `O'`), `isScSmoothMap_restrict_smul`,
  `isSaturated_preimage` (`τ̂⁻¹(O')` is saturated), `restrictSource` (the full subcategory `E'` on
  `τ̂⁻¹(O')`, Proposition 7.1.22's `subEpGroupoid`), `restrictFunctor : E' → G ⋉ O'`
  (`restrictFunctor_obj_val`, `restrictFunctor_mor`), and **`restrictModel`**: the restriction is a
  proper covering model with distinguished point `ō` and `U'(y) = U(y) ∩ τ̂⁻¹(O')`.
* `invariantComponent`: the connected component of `ō` in `O* = ⋂_g g⁻¹ U` as a `SubMulAction`
  (`isOpen_invariantComponent`, `mem_invariantComponent`, `invariantComponent_subset`,
  `isConnected_invariantComponent`).
* **Proposition 17.8.6**: `proposition_17_8_6`.  The discussion before it, (17.99), is the case
  `U = O` (`O* = O`, `O'` the component of `ō`): `exists_connected_restriction`.

## Readings

* "`g ∗ C = C`": the text uses paths; we use that `g ∗ C` is connected, contains `ō` and lies in the
  `G`-invariant `O*`, so `g ∗ C ⊆ C` (a homeomorphism maps connected sets to connected sets).
* "`E'` the full subcategory associated to the objects in `E' = τ̂⁻¹(O')`" is Chapter 7's
  `subEpGroupoid` on the saturated open set `τ̂⁻¹(O')`; `G ⋉ O'` is the translation ep-groupoid of
  the
  open sub-M-polyfold `O'` (`O'` is open, so the sub-M-polyfold structure is the restriction of the
  charts).  The paracompactness of the subspaces `O'` and `τ̂⁻¹(O')` (true, they are subspaces of
  metrizable spaces) enters as instance arguments, discharged by `paracompactSpace_subtype`.
* The connected component of `ō` in `O*` is open since M-polyfolds are locally connected
  (`MPolyfold.isOpen_connectedComponentIn`, Chapter 2).
-/

open Set Function Topology

noncomputable section

namespace Polyfold

open EpGroupoid EpGroupoid.Examples
open scoped Polyfold.EpGroupoid

universe u v

/-! ### Sc-diffeomorphisms between sub-M-polyfolds -/

namespace MPolyfold

/-- **An sc-diffeomorphism restricts to sub-M-polyfolds**: if `f : U → V` is an sc-diffeomorphism
with inverse `g`, `A ⊆ X`, `B ⊆ Y` are sub-M-polyfolds and `f'`, `g'` are maps `A → B`, `B → A`
lifting `f`, `g`, then `f' : A ∩ U → B ∩ V` is an sc-diffeomorphism with inverse `g'`. -/
theorem isScDiffeoOn_subtype {X : Type u} {Y : Type v} [TopologicalSpace X] [T2Space X]
    [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
    {PX : MPolyfold X} {PY : MPolyfold Y} {A : Set X} {B : Set Y} (hA : PX.IsSubMPolyfold A)
    (hB : PY.IsSubMPolyfold B) [ParacompactSpace A] [ParacompactSpace B] {f : X → Y}
    {g : Y → X} {U : Set X} {V : Set Y} (h : PX.IsScDiffeoOn PY f g U V) {f' : A → B}
    {g' : B → A} (hf' : ∀ a, (f' a : Y) = f a) (hg' : ∀ b, (g' b : X) = g b) :
    (subPolyfold hA).IsScDiffeoOn (subPolyfold hB) f' g' (Subtype.val ⁻¹' U)
      (Subtype.val ⁻¹' V) where
  isScSmoothOn := isScSmoothOn_subPolyfold_of_val _
    ((IsScSmoothOn.comp h.isScSmoothOn ((subPolyfold_inclusion_isScSmooth hA).mono
      (h.isScSmoothOn.isOpen.preimage continuous_subtype_val) (subset_univ _))
      fun _ ha => ha).congr fun a _ => (hf' a).symm)
  isScSmoothOn_inv := isScSmoothOn_subPolyfold_of_val _
    ((IsScSmoothOn.comp h.isScSmoothOn_inv ((subPolyfold_inclusion_isScSmooth hB).mono
      (h.isScSmoothOn_inv.isOpen.preimage continuous_subtype_val) (subset_univ _))
      fun _ hb => hb).congr fun b _ => (hg' b).symm)
  mapsTo a ha := by
    change (f' a : Y) ∈ V
    rw [hf']
    exact h.mapsTo ha
  mapsTo_inv b hb := by
    change (g' b : X) ∈ U
    rw [hg']
    exact h.mapsTo_inv hb
  left_inv a ha := Subtype.ext (by rw [hg', hf', h.left_inv _ ha])
  right_inv b hb := Subtype.ext (by rw [hf', hg', h.right_inv _ hb])

/-- An open subset is a sub-M-polyfold (`r = id`). -/
theorem isSubMPolyfold_of_isOpen' {X : Type u} [TopologicalSpace X] [T2Space X]
    [ParacompactSpace X] {P : MPolyfold X} {A : Set X} (hA : IsOpen A) : P.IsSubMPolyfold A :=
  fun a ha => ⟨A, hA, ha, id, mapsTo_id _, MPolyfold.isScSmoothMap_id.mono hA (subset_univ _),
    fun _ _ => rfl, by rw [image_id, inter_self]⟩

end MPolyfold

section Restrict

variable {G : Type u} [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
  {O : Type u} [TopologicalSpace O] [T2Space O] [ParacompactSpace O] [MulAction G O]
  {P : MPolyfold O} {hP : ∀ g : G, P.IsScSmoothMap P fun y => g • y}
  {ObjE MorE : Type v} [TopologicalSpace ObjE] [T2Space ObjE] [ParacompactSpace ObjE]
  [TopologicalSpace MorE] [T2Space MorE] [ParacompactSpace MorE] {E : EpGroupoid ObjE MorE}
  {τ : EpFunctor E (actionEpGroupoid hP)}

namespace ProperCoveringModel

variable (P) in
/-- The open sub-M-polyfold `O' ⊆ O`. -/
abbrev restrictObjPolyfold (O' : SubMulAction G O) (hO' : IsOpen (O' : Set O))
    [ParacompactSpace O'] : MPolyfold O' :=
  MPolyfold.subPolyfold (MPolyfold.isSubMPolyfold_of_isOpen' (P := P) hO')

include hP in
/-- `G` acts on `O'` by sc-diffeomorphisms. -/
theorem isScSmoothMap_restrict_smul (O' : SubMulAction G O) (hO' : IsOpen (O' : Set O))
    [ParacompactSpace O'] (g : G) :
    (restrictObjPolyfold P O' hO').IsScSmoothMap (restrictObjPolyfold P O' hO')
      fun y : O' => g • y :=
  MPolyfold.isScSmoothOn_subPolyfold_of_val _
    ((hP g).comp (MPolyfold.subPolyfold_inclusion_isScSmooth _))

/-- `τ̂⁻¹(O')` is saturated for a `G`-invariant `O'`: `τ̂(t ψ) = g_ψ ∗ τ̂(s ψ)`. -/
theorem isSaturated_preimage (M : ProperCoveringModel τ) (O' : SubMulAction G O) :
    E.IsSaturated (τ.obj ⁻¹' (O' : Set O)) :=
  E.isSaturated_iff.2 fun ψ hψ => by
    change τ.obj (E.tgt ψ) ∈ O'
    rw [M.obj_tgt]
    exact O'.smul_mem _ hψ

theorem isEpSubgroupoid_preimage (M : ProperCoveringModel τ) (O' : SubMulAction G O)
    (hO' : IsOpen (O' : Set O)) : E.IsEpSubgroupoid (τ.obj ⁻¹' (O' : Set O)) :=
  E.isEpSubgroupoid_of_isOpen
    (hO'.preimage (continuousOn_univ.1 τ.isScSmoothMap_obj.continuousOn))
    (M.isSaturated_preimage O')

variable (M : ProperCoveringModel τ) (O' : SubMulAction G O) (hO' : IsOpen (O' : Set O))
  [ParacompactSpace O'] [ParacompactSpace (τ.obj ⁻¹' (O' : Set O))]

/-- **The full subcategory `E'` on `τ̂⁻¹(O')`** (Proposition 7.1.22). -/
abbrev restrictSource : EpGroupoid (τ.obj ⁻¹' (O' : Set O)) (E.morOn (τ.obj ⁻¹' (O' : Set O))) :=
  subEpGroupoid (M.isEpSubgroupoid_preimage O' hO')

omit [ParacompactSpace O'] [ParacompactSpace (τ.obj ⁻¹' (O' : Set O))] in
theorem mor_mem_restrict (ψ : E.morOn (τ.obj ⁻¹' (O' : Set O))) : (τ.mor ψ.1).2 ∈ O' := by
  rw [show (τ.mor ψ.1).2 = τ.obj (E.src ψ.1) from τ.src_mor ψ.1]
  exact ψ.2.1

/-- **The restriction `τ̂' : E' → G ⋉ O'`**. -/
def restrictFunctor :
    EpFunctor (M.restrictSource O' hO')
      (actionEpGroupoid (isScSmoothMap_restrict_smul (hP := hP) O' hO')) where
  obj e := ⟨τ.obj e, e.2⟩
  mor ψ := ((τ.mor ψ.1).1, ⟨(τ.mor ψ.1).2, mor_mem_restrict O' ψ⟩)
  src_mor ψ := Subtype.ext (τ.src_mor ψ.1)
  tgt_mor ψ := Subtype.ext (τ.tgt_mor ψ.1)
  mor_comp ψ ψ' h := by
    have h' : E.src ψ.1 = E.tgt ψ'.1 := congrArg Subtype.val h
    have hc := subEpGroupoid_comp_val (M.isEpSubgroupoid_preimage O' hO') h
    refine Prod.ext ?_ (Subtype.ext ?_)
    · change (τ.mor ((M.restrictSource O' hO').comp ψ ψ').1).1 = (τ.mor ψ.1).1 * (τ.mor ψ'.1).1
      rw [hc, τ.mor_comp _ _ h']
      rfl
    · change (τ.mor ((M.restrictSource O' hO').comp ψ ψ').1).2 = (τ.mor ψ'.1).2
      rw [hc, τ.mor_comp _ _ h']
      rfl
  mor_unit e := by
    refine Prod.ext ?_ (Subtype.ext ?_)
    · change (τ.mor (E.unit e.1)).1 = 1
      rw [τ.mor_unit]
      rfl
    · change (τ.mor (E.unit e.1)).2 = τ.obj e.1
      rw [τ.mor_unit]
      rfl
  isScSmoothMap_obj := MPolyfold.isScSmoothOn_subPolyfold_of_val _
    (τ.isScSmoothMap_obj.comp (isScSmoothMap_val_subObj (M.isEpSubgroupoid_preimage O' hO')).1)
  isScSmoothMap_mor := by
    have hmor := τ.isScSmoothMap_mor.comp (isScSmoothMap_val_subMor
      (M.isEpSubgroupoid_preimage O' hO')).1
    refine MPolyfold.IsScSmoothOn.prodMk ?_ ?_
    · exact isScSmoothMap_discrete_of_continuous
        (continuous_fst.comp (continuousOn_univ.1 hmor.continuousOn))
    · exact MPolyfold.isScSmoothOn_subPolyfold_of_val _
        ((MPolyfold.isScSmoothMap_snd _ _).comp hmor)

@[simp] theorem restrictFunctor_obj_val (e : τ.obj ⁻¹' (O' : Set O)) :
    ((M.restrictFunctor O' hO').obj e : O) = τ.obj e := rfl

theorem restrictFunctor_mor (ψ : E.morOn (τ.obj ⁻¹' (O' : Set O))) :
    (M.restrictFunctor O' hO').mor ψ =
      ((τ.mor ψ.1).1, ⟨(τ.mor ψ.1).2, mor_mem_restrict O' ψ⟩) := rfl

/-! #### The model -/

open scoped Classical in
/-- The inverse `τ'_y⁻¹ : O' → U'(y)` (for `y` in the fibre; a junk value otherwise). -/
def restrictσ (y : τ.obj ⁻¹' (O' : Set O)) (o : O') : τ.obj ⁻¹' (O' : Set O) :=
  if hy : y.1 ∈ M.fiber then
    ⟨M.σ y.1 o.1, by
      change τ.obj (M.σ y.1 o.1) ∈ O'
      rw [M.obj_σ hy]
      exact o.2⟩
  else y

theorem restrictσ_val {y : τ.obj ⁻¹' (O' : Set O)} (hy : y.1 ∈ M.fiber) (o : O') :
    (M.restrictσ O' y o : ObjE) = M.σ y.1 o.1 := by
  rw [restrictσ, dif_pos hy]

theorem mem_fiber_of_restrict (hpt : M.pt ∈ O') {y : τ.obj ⁻¹' (O' : Set O)}
    (hy : y ∈ (M.restrictFunctor O' hO').obj ⁻¹' {⟨M.pt, hpt⟩}) : y.1 ∈ M.fiber :=
  congrArg Subtype.val (show (M.restrictFunctor O' hO').obj y = ⟨M.pt, hpt⟩ from hy)

/-- `τ̂' : U'(y) → O'` is an sc-diffeomorphism. -/
theorem isScDiffeoOn_restrict_U {y : τ.obj ⁻¹' (O' : Set O)} (hy : y.1 ∈ M.fiber) :
    (M.restrictSource O' hO').PObj.IsScDiffeoOn (restrictObjPolyfold P O' hO')
      (M.restrictFunctor O' hO').obj (M.restrictσ O' y) (Subtype.val ⁻¹' M.U y.1) univ := by
  have h := MPolyfold.isScDiffeoOn_subtype (M.isEpSubgroupoid_preimage O' hO').isSubMPolyfold
    (MPolyfold.isSubMPolyfold_of_isOpen' (P := P) hO') (M.isScDiffeoOn_U y.1 hy)
    (f' := (M.restrictFunctor O' hO').obj) (g' := M.restrictσ O' y) (fun _ => rfl)
    (fun o => M.restrictσ_val O' hy o)
  rwa [preimage_univ] at h

/-- The inverse of `Γ'`: `((g, o), e) ↦ Γ⁻¹((g, τ̂ e), e)`. -/
def restrictΓInv
    (q : MPolyfold.fibredProduct
      (actionEpGroupoid (isScSmoothMap_restrict_smul (hP := hP) O' hO')).src
      (M.restrictFunctor O' hO').obj) : E.morOn (τ.obj ⁻¹' (O' : Set O)) :=
  ⟨M.liftMor (q : (G × O') × τ.obj ⁻¹' (O' : Set O)).1.1
      (q : (G × O') × τ.obj ⁻¹' (O' : Set O)).2.1, by
    rw [M.src_liftMor]
    exact (q : (G × O') × τ.obj ⁻¹' (O' : Set O)).2.2, by
    change τ.obj (E.tgt _) ∈ O'
    rw [M.obj_tgt, M.groupIndex_liftMor, M.src_liftMor]
    exact O'.smul_mem _ (q : (G × O') × τ.obj ⁻¹' (O' : Set O)).2.2⟩

/-- **Definition 17.8.4 (3) for the restriction**: `Γ' : 𝐄' → (G ⋉ O') ₛ×_τ̂' E'` is an
sc-diffeomorphism, with inverse `restrictΓInv`. -/
theorem isScDiffeoOn_restrict_fibredMap
    [ParacompactSpace ((G × O') × τ.obj ⁻¹' (O' : Set O))]
    [ParacompactSpace (MPolyfold.fibredProduct
      (actionEpGroupoid (isScSmoothMap_restrict_smul (hP := hP) O' hO')).src
      (M.restrictFunctor O' hO').obj)] :
    (M.restrictSource O' hO').PMor.IsScDiffeoOn (MPolyfold.subPolyfold
      (MPolyfold.isSubMPolyfold_fibredProduct
        (actionEpGroupoid (isScSmoothMap_restrict_smul (hP := hP) O' hO')).isLocalScDiffeo_src
        (M.restrictFunctor O' hO').isScSmoothMap_obj)) (M.restrictFunctor O' hO').fibredMap
      (M.restrictΓInv O' hO') univ univ := by
  have := MPolyfold.paracompactSpace_prod (actionEpGroupoid hP).PMor E.PObj
  have := ((actionEpGroupoid hP).PMor.prod E.PObj).paracompactSpace_subtype
    (MPolyfold.fibredProduct (actionEpGroupoid hP).src τ.obj)
  have hA := M.isEpSubgroupoid_preimage O' hO'
  have hB := MPolyfold.isSubMPolyfold_of_isOpen' (P := P) hO'
  have hτo : E.PObj.IsScSmoothMap P τ.obj := τ.isScSmoothMap_obj
  have hvalA := (isScSmoothMap_val_subObj hA).1
  -- the map `k : (G × O') × E' → (G × O) × E`, `((g, o), e) ↦ ((g, τ̂ e), e)`
  have hk : (((discretePolyfold G).prod (restrictObjPolyfold P O' hO')).prod
      (subObjPolyfold hA)).IsScSmoothMap ((actionEpGroupoid hP).PMor.prod E.PObj)
      (fun r : (G × O') × τ.obj ⁻¹' (O' : Set O) => ((r.1.1, τ.obj r.2.1), r.2.1)) := by
    have h1 : (((discretePolyfold G).prod (restrictObjPolyfold P O' hO')).prod
        (subObjPolyfold hA)).IsScSmoothMap (subObjPolyfold hA) Prod.snd :=
      MPolyfold.isScSmoothMap_snd _ _
    refine MPolyfold.IsScSmoothOn.prodMk (MPolyfold.IsScSmoothOn.prodMk ?_ ?_) ?_
    · exact (MPolyfold.isScSmoothMap_fst (discretePolyfold G) (restrictObjPolyfold P O' hO')).comp
        (MPolyfold.isScSmoothMap_fst _ _)
    · exact hτo.comp (hvalA.comp h1)
    · exact hvalA.comp h1
  refine
    { isScSmoothOn := MPolyfold.isScSmoothOn_subPolyfold_of_val _
        (MPolyfold.IsScSmoothOn.prodMk (M.restrictFunctor O' hO').isScSmoothMap_mor
          (M.restrictSource O' hO').isScSmoothMap_src)
      isScSmoothOn_inv := ?_
      mapsTo := mapsTo_univ _ _
      mapsTo_inv := mapsTo_univ _ _
      left_inv := fun ψ _ => Subtype.ext (M.liftMor_eq ψ.1)
      right_inv := fun q _ => ?_ }
  · refine MPolyfold.isScSmoothOn_subPolyfold_of_val _ ?_
    have hj : (MPolyfold.subPolyfold (MPolyfold.isSubMPolyfold_fibredProduct
        (actionEpGroupoid (isScSmoothMap_restrict_smul (hP := hP) O' hO')).isLocalScDiffeo_src
        (M.restrictFunctor O' hO').isScSmoothMap_obj)).IsScSmoothMap
        (MPolyfold.subPolyfold (MPolyfold.isSubMPolyfold_fibredProduct
          (actionEpGroupoid hP).isLocalScDiffeo_src τ.isScSmoothMap_obj))
        (fun q => (⟨(((q : (G × O') × τ.obj ⁻¹' (O' : Set O)).1.1,
          τ.obj (q : (G × O') × τ.obj ⁻¹' (O' : Set O)).2.1),
          (q : (G × O') × τ.obj ⁻¹' (O' : Set O)).2.1), rfl⟩ :
            MPolyfold.fibredProduct (actionEpGroupoid hP).src τ.obj)) :=
      MPolyfold.isScSmoothOn_subPolyfold_of_val _
        (hk.comp (MPolyfold.subPolyfold_inclusion_isScSmooth _))
    exact (MPolyfold.IsScSmoothOn.comp M.isScDiffeoOn_ΓInv.isScSmoothOn_inv hj
      (mapsTo_univ _ _)).congr fun _ _ => rfl
  · obtain ⟨⟨⟨g, o⟩, e⟩, hq⟩ := q
    have ho : o = ⟨τ.obj e.1, e.2⟩ := hq
    subst ho
    refine Subtype.ext (Prod.ext (Prod.ext (M.groupIndex_liftMor _ _) (Subtype.ext ?_))
      (Subtype.ext (M.src_liftMor _ _)))
    change (τ.mor (M.liftMor g e.1)).2 = τ.obj e.1
    rw [M.mor_eq, M.src_liftMor]

/-- **The restriction to `τ̂⁻¹(O')` is a proper covering model** `E' → G ⋉ O'` (p. 832) for every
open `G`-invariant `O' ∋ ō`, with `U'(y) = U(y) ∩ τ̂⁻¹(O')` and distinguished point `ō`. -/
def restrictModel (hpt : M.pt ∈ O') : ProperCoveringModel (M.restrictFunctor O' hO') where
  pt := ⟨M.pt, hpt⟩
  smul_pt g := Subtype.ext (M.smul_pt g)
  surjective o := by
    obtain ⟨y, hy⟩ := M.surjective M.pt
    refine ⟨⟨M.σ y o.1, ?_⟩, Subtype.ext (M.obj_σ hy o.1)⟩
    change τ.obj (M.σ y o.1) ∈ O'
    rw [M.obj_σ hy]
    exact o.2
  isLocalScDiffeo e := by
    have hy : M.sheetIndex e.1 ∈ M.fiber := M.sheetIndex_mem e.1
    have hy' : M.sheetIndex e.1 ∈ τ.obj ⁻¹' (O' : Set O) := by
      change τ.obj _ ∈ O'
      rw [show τ.obj (M.sheetIndex e.1) = M.pt from hy]
      exact hpt
    exact ⟨_, _, _, M.mem_U_sheetIndex e.1,
      M.isScDiffeoOn_restrict_U O' hO' (y := ⟨M.sheetIndex e.1, hy'⟩) hy⟩
  U y := Subtype.val ⁻¹' M.U y.1
  σ := M.restrictσ O'
  mem_U y hy := M.mem_U y.1 (M.mem_fiber_of_restrict O' hO' hpt hy)
  pairwiseDisjoint_U y hy z hz hne :=
    (M.pairwiseDisjoint_U (M.mem_fiber_of_restrict O' hO' hpt hy)
      (M.mem_fiber_of_restrict O' hO' hpt hz) fun h => hne (Subtype.ext h)).preimage _
  iUnion_U := by
    refine eq_univ_of_forall fun e => ?_
    simp only [mem_iUnion, exists_prop]
    have hy : M.sheetIndex e.1 ∈ M.fiber := M.sheetIndex_mem e.1
    have hy' : M.sheetIndex e.1 ∈ τ.obj ⁻¹' (O' : Set O) := by
      change τ.obj _ ∈ O'
      rw [show τ.obj (M.sheetIndex e.1) = M.pt from hy]
      exact hpt
    exact ⟨⟨M.sheetIndex e.1, hy'⟩, Subtype.ext hy, M.mem_U_sheetIndex e.1⟩
  isScDiffeoOn_U y hy :=
    M.isScDiffeoOn_restrict_U O' hO' (M.mem_fiber_of_restrict O' hO' hpt hy)
  isScDiffeo_fibredMap := by
    have := MPolyfold.paracompactSpace_prod
      (actionEpGroupoid (isScSmoothMap_restrict_smul (hP := hP) O' hO')).PMor
      (M.restrictSource O' hO').PObj
    have := ((actionEpGroupoid (isScSmoothMap_restrict_smul (hP := hP) O' hO')).PMor.prod
      (M.restrictSource O' hO').PObj).paracompactSpace_subtype
      (MPolyfold.fibredProduct
        (actionEpGroupoid (isScSmoothMap_restrict_smul (hP := hP) O' hO')).src
        (M.restrictFunctor O' hO').obj)
    exact ⟨_, M.isScDiffeoOn_restrict_fibredMap O' hO'⟩

theorem restrictModel_pt (hpt : M.pt ∈ O') : (M.restrictModel O' hO' hpt).pt = ⟨M.pt, hpt⟩ := rfl

/-- The restricted model is connected if `O'` is. -/
theorem restrictModel_connected (hpt : M.pt ∈ O') (hc : IsConnected (O' : Set O)) :
    (M.restrictModel O' hO' hpt).Connected :=
  isConnected_iff_connectedSpace.1 hc

end ProperCoveringModel

end Restrict

/-! ### The `G`-invariant connected component of `ō` -/

section Component

/-- `O* = ⋂_g g⁻¹ U`, the largest `G`-invariant subset of `U`. -/
def invariantCore (G : Type u) [Group G] {O : Type u} [MulAction G O] (U : Set O) : Set O :=
  ⋂ g : G, (fun x : O => g • x) ⁻¹' U

variable {G : Type u} [Group G] [Finite G]
  {O : Type u} [TopologicalSpace O] [T2Space O] [ParacompactSpace O] [MulAction G O]
  {P : MPolyfold O} (hP : ∀ g : G, P.IsScSmoothMap P fun y => g • y)

omit [Finite G] [T2Space O] [ParacompactSpace O] in
theorem smul_mem_invariantCore {U : Set O} {x : O} (hx : x ∈ invariantCore G U) (h : G) :
    h • x ∈ invariantCore G U :=
  mem_iInter.2 fun g => by
    change g • h • x ∈ U
    rw [← mul_smul]
    exact mem_iInter.1 hx (g * h)

omit [Finite G] [T2Space O] [ParacompactSpace O] in
theorem invariantCore_subset (U : Set O) : invariantCore G U ⊆ U := fun x hx => by
  have h := mem_iInter.1 hx 1
  rwa [mem_preimage, one_smul] at h

include hP in
theorem isOpen_invariantCore {U : Set O} (hU : IsOpen U) : IsOpen (invariantCore G U) :=
  isOpen_iInter_of_finite fun g => hU.preimage (continuousOn_univ.1 (hP g).continuousOn)

omit [Finite G] [T2Space O] [ParacompactSpace O] in
theorem mem_invariantCore {U : Set O} {x₀ : O} (hx₀ : ∀ g : G, g • x₀ = x₀) (h : x₀ ∈ U) :
    x₀ ∈ invariantCore G U :=
  mem_iInter.2 fun g => by
    change g • x₀ ∈ U
    rw [hx₀]
    exact h

/-- **The connected component of `x₀` in `O* = ⋂_g g⁻¹ U`, a `G`-invariant set** (p. 831–832): for
`g ∈ G`, `g ∗ C` is connected, contains `g ∗ x₀ = x₀` and lies in the `G`-invariant `O*`. -/
def invariantComponent (U : Set O) (x₀ : O) (hx₀ : ∀ g : G, g • x₀ = x₀) :
    SubMulAction G O where
  carrier := connectedComponentIn (invariantCore G U) x₀
  smul_mem' g x hx := by
    have hc : Continuous fun y : O => g • y := continuousOn_univ.1 (hP g).continuousOn
    have hs :
        IsPreconnected ((fun y : O => g • y) '' connectedComponentIn (invariantCore G U) x₀) :=
      isPreconnected_connectedComponentIn.image _ hc.continuousOn
    have hx₀C : x₀ ∈ connectedComponentIn (invariantCore G U) x₀ :=
      mem_connectedComponentIn (connectedComponentIn_nonempty_iff.1 ⟨x, hx⟩)
    refine hs.subset_connectedComponentIn ⟨x₀, hx₀C, hx₀ g⟩ ?_ ⟨x, hx, rfl⟩
    rintro _ ⟨y, hy, rfl⟩
    exact smul_mem_invariantCore (connectedComponentIn_subset _ _ hy) g

theorem coe_invariantComponent (U : Set O) (x₀ : O) (hx₀ : ∀ g : G, g • x₀ = x₀) :
    (invariantComponent hP U x₀ hx₀ : Set O) = connectedComponentIn (invariantCore G U) x₀ := rfl

theorem isOpen_invariantComponent {U : Set O} (hU : IsOpen U) (x₀ : O)
    (hx₀ : ∀ g : G, g • x₀ = x₀) : IsOpen (invariantComponent hP U x₀ hx₀ : Set O) :=
  P.isOpen_connectedComponentIn (isOpen_invariantCore hP hU) x₀

theorem mem_invariantComponent {U : Set O} {x₀ : O} (hx₀ : ∀ g : G, g • x₀ = x₀) (h : x₀ ∈ U) :
    x₀ ∈ invariantComponent hP U x₀ hx₀ :=
  mem_connectedComponentIn (mem_invariantCore hx₀ h)

theorem invariantComponent_subset (U : Set O) (x₀ : O) (hx₀ : ∀ g : G, g • x₀ = x₀) :
    (invariantComponent hP U x₀ hx₀ : Set O) ⊆ U :=
  (connectedComponentIn_subset _ _).trans (invariantCore_subset U)

theorem isConnected_invariantComponent {U : Set O} {x₀ : O} (hx₀ : ∀ g : G, g • x₀ = x₀)
    (h : x₀ ∈ U) : IsConnected (invariantComponent hP U x₀ hx₀ : Set O) :=
  isConnected_connectedComponentIn_iff.2 (mem_invariantCore hx₀ h)

/-- For `U = O`, the set is the connected component of `x₀` in `O` (the set `C` of p. 831). -/
theorem invariantComponent_univ (x₀ : O) (hx₀ : ∀ g : G, g • x₀ = x₀) :
    (invariantComponent hP univ x₀ hx₀ : Set O) = connectedComponent x₀ := by
  rw [coe_invariantComponent, show invariantCore G (univ : Set O) = univ from
    eq_univ_of_forall fun x => mem_iInter.2 fun _ => mem_univ _, connectedComponentIn_univ]

end Component

/-! ### Proposition 17.8.6 -/

section Proposition

variable {G : Type u} [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
  {O : Type u} [TopologicalSpace O] [T2Space O] [ParacompactSpace O] [MulAction G O]
  {P : MPolyfold O} {hP : ∀ g : G, P.IsScSmoothMap P fun y => g • y}
  {ObjE MorE : Type v} [TopologicalSpace ObjE] [T2Space ObjE] [ParacompactSpace ObjE]
  [TopologicalSpace MorE] [T2Space MorE] [ParacompactSpace MorE] {E : EpGroupoid ObjE MorE}
  {τ : EpFunctor E (actionEpGroupoid hP)}

/-- **Proposition 17.8.6**: for a proper covering model `τ̂ : E → G ⋉ O` with distinguished point
`ō` and an open neighbourhood `U` of `ō` there is a `G`-invariant connected open neighbourhood
`O' ⊆ U` of `ō` such that the restriction `τ̂' : E' → G ⋉ O'` to the full subcategory `E'` on
`τ̂⁻¹(O')` is a connected proper covering model with distinguished element `ō`.  `O'` is the
connected component of `ō` in `⋂_g g⁻¹ U`. -/
theorem proposition_17_8_6 (M : ProperCoveringModel τ) {U : Set O} (hU : IsOpen U)
    (hpt : M.pt ∈ U) :
    ∃ (O' : SubMulAction G O) (hO' : IsOpen (O' : Set O)) (hpt' : M.pt ∈ O'),
      (O' : Set O) ⊆ U ∧ IsConnected (O' : Set O) ∧
      ∀ [ParacompactSpace O'] [ParacompactSpace (τ.obj ⁻¹' (O' : Set O))],
        ∃ M' : ProperCoveringModel (M.restrictFunctor O' hO'), M'.pt = ⟨M.pt, hpt'⟩ ∧
          M'.Connected :=
  ⟨invariantComponent hP U M.pt M.smul_pt, isOpen_invariantComponent hP hU M.pt M.smul_pt,
    mem_invariantComponent hP M.smul_pt hpt, invariantComponent_subset hP U M.pt M.smul_pt,
    isConnected_invariantComponent hP M.smul_pt hpt, by
      intro _ _
      exact ⟨M.restrictModel _ _ _, rfl,
        M.restrictModel_connected _ _ _ (isConnected_invariantComponent hP M.smul_pt hpt)⟩⟩

/-- **(17.99)**: the restriction to the connected component `C` of `ō` in `O` (and to
`E' = ⊔ (τ̂|U(y))⁻¹(C) = τ̂⁻¹(C)`) is a connected proper covering model `E' → G ⋉ C`. -/
theorem exists_connected_restriction (M : ProperCoveringModel τ) :
    ∃ (C : SubMulAction G O) (hC : IsOpen (C : Set O)) (hpt' : M.pt ∈ C),
      (C : Set O) = connectedComponent M.pt ∧
      ∀ [ParacompactSpace C] [ParacompactSpace (τ.obj ⁻¹' (C : Set O))],
        ∃ M' : ProperCoveringModel (M.restrictFunctor C hC), M'.pt = ⟨M.pt, hpt'⟩ ∧
          M'.Connected :=
  ⟨invariantComponent hP univ M.pt M.smul_pt, isOpen_invariantComponent hP isOpen_univ M.pt
    M.smul_pt, mem_invariantComponent hP M.smul_pt (mem_univ _),
    invariantComponent_univ hP M.pt M.smul_pt, by
      intro _ _
      exact ⟨M.restrictModel _ _ _, rfl, M.restrictModel_connected _ _ _
        (isConnected_invariantComponent hP M.smul_pt (mem_univ _))⟩⟩

end Proposition

end Polyfold
