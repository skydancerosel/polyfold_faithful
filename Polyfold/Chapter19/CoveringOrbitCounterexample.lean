import Polyfold.Chapter8.NonVacuityBundle
import Polyfold.Chapter8.NonVacuity

set_option maxSynthPendingDepth 3

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 19, §19.7
"Covering Constructions": **Proposition 19.7.18** (p. 919, `|P| : |A| → |B|` is a surjective local
homeomorphism), **Corollary 19.7.20 (3)** (p. 922, `|P| : W(z̄ᵢ) → W(z)` is a homeomorphism) and
**Theorem 19.7.25 (4b)** (p. 926, local homeomorphisms), for a covering functor `P : A → B`.

# A covering functor whose map of orbit spaces is not a local homeomorphism

## The text, paraphrased

(Proposition 19.7.18) For a basic construction for a covering functor `P : A → B`, the map
`|P| : |A| → |B|` is a surjective local homeomorphism. (Corollary 19.7.20 (3)) Near a point `z ∈ |B|`
with preimages `z̄₁, …, z̄ₖ`, `|P| : W(z̄ᵢ) → W(z)` is a homeomorphism; the proof identifies
`|G_{aᵢ} ⋉ V(aᵢ)|` with `|G ⋉ O′|`. (Theorem 19.7.25 (4b)) The structural maps are local
homeomorphisms.

## What is formalized

The statements `not_proposition_19_7_18` etc. need Definition 17.8.4; here are the concrete facts
they will rest on, with ep-groupoids and functors of Chapters 7–8.

* `orbitMap_continuous`, `orbitMap_isOpenMap`, `orbitMap_surjective`: `|F|` of an ep-functor is
  continuous, and open (surjective) if `F` is on objects.
* `sheetProj : K ⋉ (K × ℝ) → K ⋉ ℝ`, `(i, x) ↦ x`, for a finite group `K` acting on `ℝ` by
  sc-diffeomorphisms (`k (i, x) = (k i, k x)`), and `sheetProj_isProperCovering`: it is a proper
  covering functor in the sense of **Definition 8.5.1** (surjective local sc-diffeomorphism on
  objects, fibres `K × {x}` evenly covered by the disjoint sheets `{i} × ℝ`, and `𝐀 ≅ 𝐁 ₛ×_P A`), the
  strongest covering notion of Parts I–III.
* The example: `absA = ℤ/2 ⋉ (ℤˣ × ℝ)` (`ℝ × {1, 2}` with `g(x, i) = (−x, σ i)`), `absB = ℤ/2 ⋉ ℝ`
  (the reflection, Chapter 7's `reflectionEpGroupoid`), `absP = sheetProj` for `ℤˣ`, a proper
  covering functor (`absP_isProperCovering`).
* `absAOrbitHomeomorph : |absA| ≃ₜ ℝ`, `absBOrbitHomeomorph : |absB| ≃ₜ [0, ∞)`, and
  `absBOrbitHomeomorph_orbitMap`: under them `|absP|` is `t ↦ |t|`.
* `absCovering_orbitMap_not_isLocalHomeomorph`: `|absP|` is not a local homeomorphism (serves
  Proposition 19.7.18, Corollary 19.7.20 (3), Theorem 19.7.25 (4b): does not hold as we read it);
  `absCovering_orbitMap_not_isLocalHomeomorphOn_zero` at `|(i, 0)|`: `|(i, t)| ≠ |(i, −t)|` while
  `|absP|` identifies them. `|absP|` is continuous, open, surjective, with finite fibres
  (`absP_orbitMap_continuous`, `absP_orbitMap_isOpenMap`, `absP_orbitMap_surjective`,
  `absP_orbitMap_finite_fiber`): the 2017 form of Proposition 19.7.18.
* **The isotropy criterion.** `isLocalHomeomorphOn_orbitMap_of_isotropy_surjective`: for an
  ep-functor `F : K ⋉ U → L ⋉ V` of translation groupoids (finite groups, Hausdorff `V`) that is a
  local homeomorphism on objects, if `F` maps `Aut(a)` onto `Aut(F a)`, then `|F|` is a local
  homeomorphism at `|a|` (with `exists_slice`). In the example both conditions say `a = (i, x)`
  with `x ≠ 0` (`absP_isotropy_surjective_iff`, `absP_isLocalHomeomorphOn_iff`), so there the
  criterion is an equivalence: at `(i, 0)`, `Aut(i, 0) = 1` and `Aut(0) = ℤ/2`.
* `isotropy_surjective_not_necessary`: the converse is not general. For `ℤ/3` acting trivially on
  `ℝ`, `sheetProj` is a proper covering functor and `|P|` is a local homeomorphism (a
  homeomorphism), while `Aut(a) = 1` does not map onto `Aut(P a) = ℤ/3` at any `a`.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

namespace Chapter19

open EpGroupoid EpGroupoid.Examples

universe u v

/-! ### Maps of orbit spaces -/

section OrbitMap

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}

/-- `|F| : |X| → |Y|` is continuous for an ep-functor `F`. -/
theorem orbitMap_continuous (F : EpFunctor X Y) : Continuous F.orbitMap :=
  continuous_quot_lift _ (Y.continuous_π.comp (continuousOn_univ.1 F.isScSmoothMap_obj.continuousOn))

/-- `|F|` is open if `F` is open on objects (`|F|(π S) = π(F S)`, `π` open, Proposition 7.1.8). -/
theorem orbitMap_isOpenMap (F : EpFunctor X Y) (hF : IsOpenMap F.obj) : IsOpenMap F.orbitMap := by
  intro S hS
  have : F.orbitMap '' S = Y.π '' (F.obj '' (X.π ⁻¹' S)) := by
    conv_lhs => rw [← image_preimage_eq S X.surjective_π]
    rw [image_image, image_image]
    rfl
  rw [this]
  exact Y.proposition_7_1_8 _ (hF _ (hS.preimage X.continuous_π))

/-- `|F|` is surjective if `F` is surjective on objects. -/
theorem orbitMap_surjective (F : EpFunctor X Y) (hF : Surjective F.obj) :
    Surjective F.orbitMap := by
  intro z
  obtain ⟨y, rfl⟩ := Y.surjective_π z
  obtain ⟨x, rfl⟩ := hF y
  exact ⟨X.π x, rfl⟩

end OrbitMap

/-! ### The isotropy criterion for translation groupoids -/

section Criterion

/-- A slice at `b` for a finite group acting continuously on a Hausdorff space: an open `S ∋ b`
with `y, l y ∈ S ⇒ l b = b`. -/
theorem exists_slice {L : Type v} [Group L] [Finite L] {V : Type v} [TopologicalSpace V]
    [T2Space V] [MulAction L V] (hc : ∀ l : L, Continuous fun y : V => l • y) (b : V) :
    ∃ S : Set V, IsOpen S ∧ b ∈ S ∧ ∀ l : L, ∀ y ∈ S, l • y ∈ S → l • b = b := by
  have : ∀ l : L, ∃ T : Set V, IsOpen T ∧ b ∈ T ∧ ∀ y ∈ T, l • y ∈ T → l • b = b := by
    intro l
    by_cases hl : l • b = b
    · exact ⟨univ, isOpen_univ, mem_univ b, fun _ _ _ => hl⟩
    · obtain ⟨A, B, hA, hB, hbA, hbB, hAB⟩ := t2_separation hl
      refine ⟨B ∩ (fun y => l • y) ⁻¹' A, hB.inter (hA.preimage (hc l)), ⟨hbB, hbA⟩, ?_⟩
      intro y hy hly
      exact (Set.disjoint_left.1 hAB hy.2 hly.1).elim
  choose T hTo hbT hT using this
  exact ⟨⋂ l, T l, isOpen_iInter_of_finite hTo, mem_iInter.2 hbT, fun l y hy hly =>
    hT l y (mem_iInter.1 hy l) (mem_iInter.1 hly l)⟩

variable {K : Type u} [Group K] [Finite K] [TopologicalSpace K] [DiscreteTopology K]
  {U : Type u} [TopologicalSpace U] [T2Space U] [ParacompactSpace U] [MulAction K U]
  {PU : MPolyfold U} {hPU : ∀ k : K, PU.IsScSmoothMap PU fun y => k • y}
  {L : Type v} [Group L] [Finite L] [TopologicalSpace L] [DiscreteTopology L]
  {V : Type v} [TopologicalSpace V] [T2Space V] [ParacompactSpace V] [MulAction L V]
  {PV : MPolyfold V} {hPV : ∀ l : L, PV.IsScSmoothMap PV fun y => l • y}

/-- **The isotropy criterion** (serves Proposition 19.7.18, Corollary 19.7.20 (3),
Theorem 19.7.25 (4b)) for translation groupoids: let `F : K ⋉ U → L ⋉ V` be an ep-functor (finite
groups acting by sc-diffeomorphisms) which is a local homeomorphism on objects. If `F` maps
`Aut(a)` onto `Aut(F a)`, then `|F| : |K ⋉ U| → |L ⋉ V|` is a local homeomorphism at `|a|`.
*Proof*: on a `K_a`-invariant `W ∋ a` on which `F` is injective, `F(W)` lies in a slice at `F a`, and
the group component of `F(g, ·)` is constant for `g ∈ K_a`, `|F|` is injective on `π(W)`; it is
continuous and open. -/
theorem isLocalHomeomorphOn_orbitMap_of_isotropy_surjective
    (F : EpFunctor (actionEpGroupoid hPU) (actionEpGroupoid hPV)) (hF : IsLocalHomeomorph F.obj)
    (a : U)
    (hsurj : ∀ ψ : (actionEpGroupoid hPV).Isotropy (F.obj a),
      ∃ φ : (actionEpGroupoid hPU).Isotropy a, F.mor φ.val = ψ.val) :
    IsLocalHomeomorphOn F.orbitMap {(actionEpGroupoid hPU).π a} := by
  obtain ⟨e, hae, he⟩ := hF a
  obtain ⟨S, hSo, hbS, hS⟩ := exists_slice (action_continuous_smul hPV) (F.obj a)
  have hmor : Continuous F.mor := continuousOn_univ.1 F.isScSmoothMap_mor.continuousOn
  have hobj : Continuous F.obj := hF.continuous
  set W₂ : Set U := e.source ∩ F.obj ⁻¹' S ∩
    ⋂ g : K, {w | (F.mor (g, w)).1 = (F.mor (g, a)).1} with hW₂
  have hW₂o : IsOpen W₂ := by
    refine (e.open_source.inter (hSo.preimage hobj)).inter (isOpen_iInter_of_finite fun g => ?_)
    exact (isOpen_discrete {(F.mor (g, a)).1}).preimage
      (continuous_fst.comp (hmor.comp (continuous_const.prodMk continuous_id)))
  have haW₂ : a ∈ W₂ := ⟨⟨hae, hbS⟩, mem_iInter.2 fun _ => rfl⟩
  set W : Set U := ⋂ h : K, ⋂ (_ : h • a = a), (fun w => h • w) ⁻¹' W₂ with hW
  have hWo : IsOpen W := isOpen_iInter_of_finite fun h => isOpen_iInter_of_finite fun _ =>
    hW₂o.preimage (action_continuous_smul hPU h)
  have haW : a ∈ W := mem_iInter.2 fun h => mem_iInter.2 fun hh => by
    simpa [hh] using haW₂
  have hWW₂ : W ⊆ W₂ := fun w hw => by
    simpa using mem_iInter.1 (mem_iInter.1 hw 1) (one_smul K a)
  have hWinv : ∀ g : K, g • a = a → ∀ w ∈ W, g • w ∈ W := by
    intro g hg w hw
    refine mem_iInter.2 fun h => mem_iInter.2 fun hh => ?_
    have := mem_iInter.1 (mem_iInter.1 hw (h * g)) (by rw [mul_smul, hg, hh])
    simpa [mul_smul] using this
  -- injectivity of `|F|` on `π(W)`
  have hinj : InjOn F.orbitMap ((actionEpGroupoid hPU).π '' W) := by
    rintro _ ⟨w, hw, rfl⟩ _ ⟨w', hw', rfl⟩ hww'
    obtain ⟨l, hl⟩ := (action_π_eq_π_iff hPV).1 (hww' : (actionEpGroupoid hPV).π (F.obj w) = (actionEpGroupoid hPV).π (F.obj w'))
    have hwS : F.obj w ∈ S := (hWW₂ hw).1.2
    have hw'S : F.obj w' ∈ S := (hWW₂ hw').1.2
    have hlb : l • F.obj a = F.obj a := hS l (F.obj w) hwS (hl ▸ hw'S)
    obtain ⟨φ, hφ⟩ := hsurj ⟨(l, F.obj a), rfl, hlb⟩
    set g := φ.val.1
    have hφval : φ.val = (g, a) := Prod.ext rfl φ.src_val
    have hga : g • a = a := by
      have := φ.tgt_val
      rw [hφval] at this
      exact this
    have hFga : (F.mor (g, a)).1 = l := by
      rw [← hφval, hφ]
    have hFgw1 : (F.mor (g, w)).1 = l := by
      rw [← hFga]
      exact mem_iInter.1 (hWW₂ hw).2 g
    have hFgw : F.mor (g, w) = (l, F.obj w) := Prod.ext hFgw1 (F.src_mor (g, w))
    have htgt : F.obj (g • w) = l • F.obj w := by
      have := F.tgt_mor (g, w)
      rw [hFgw] at this
      exact this.symm
    have hgw : g • w = w' := by
      have hs1 : g • w ∈ e.source := (hWW₂ (hWinv g hga w hw)).1.1
      have hs2 : w' ∈ e.source := (hWW₂ hw').1.1
      refine e.injOn hs1 hs2 ?_
      rw [← he, htgt, hl]
    exact (action_π_eq_π_iff hPU).2 ⟨g, hgw⟩
  rw [isLocalHomeomorphOn_iff_isOpenEmbedding_restrict]
  rintro _ rfl
  have hπW : IsOpen ((actionEpGroupoid hPU).π '' W) :=
    (actionEpGroupoid hPU).proposition_7_1_8 _ hWo
  refine ⟨(actionEpGroupoid hPU).π '' W, hπW.mem_nhds ⟨a, haW, rfl⟩, ?_⟩
  refine isOpenEmbedding_iff_continuous_injective_isOpenMap.2 ⟨?_, ?_, ?_⟩
  · exact (orbitMap_continuous F).comp continuous_subtype_val
  · exact injOn_iff_injective.1 hinj
  · exact (orbitMap_isOpenMap F hF.isOpenMap).comp hπW.isOpenMap_subtype_val

end Criterion

/-! ### The example: `ℤ/2 ⋉ (ℤˣ × ℝ) → ℤ/2 ⋉ ℝ` -/

/-! ### Sheets over `ℝ`: `K ⋉ (K × ℝ) → K ⋉ ℝ` for a finite group `K` acting on `ℝ` -/

section Sheets

variable {K : Type} [Group K] [Finite K] [TopologicalSpace K] [DiscreteTopology K]
  [MulAction K (Fin 1 → ℝ)] (hK : ∀ k : K, (rnPolyfold 1).IsScSmoothMap (rnPolyfold 1) fun y => k • y)

variable (K) in
/-- The objects `K × ℝ` (`#K` copies of `ℝ`), as an M-polyfold. -/
def sheetPolyfold : MPolyfold (K × (Fin 1 → ℝ)) := (discretePolyfold K).prod (rnPolyfold 1)

include hK in
/-- `k (i, x) = (k i, k x)` is sc-smooth (on each sheet `{i} × ℝ`: a constant and `x ↦ k x`). -/
theorem isScSmoothMap_sheet_smul (k : K) :
    (sheetPolyfold K).IsScSmoothMap (sheetPolyfold K) fun p : K × (Fin 1 → ℝ) => k • p :=
  isScSmoothMap_prod_discrete_iff.2 fun i =>
    MPolyfold.IsScSmoothOn.prodMk (isScSmoothMap_const_discrete (k * i)) (hK k)

/-- `K ⋉ (K × ℝ)`, `k (i, x) = (k i, k x)`. -/
def sheetActionEp : EpGroupoid (K × (Fin 1 → ℝ)) (K × (K × (Fin 1 → ℝ))) :=
  actionEpGroupoid (isScSmoothMap_sheet_smul hK)

/-- The projection `K ⋉ (K × ℝ) → K ⋉ ℝ`, `(i, x) ↦ x`, `(k, (i, x)) ↦ (k, x)`. -/
def sheetProj : EpFunctor (sheetActionEp hK) (actionEpGroupoid hK) where
  obj := Prod.snd
  mor φ := (φ.1, φ.2.2)
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp _ _ _ := rfl
  mor_unit _ := rfl
  isScSmoothMap_obj := MPolyfold.isScSmoothMap_snd _ _
  isScSmoothMap_mor := MPolyfold.IsScSmoothOn.prodMk (MPolyfold.isScSmoothMap_fst _ _)
    ((MPolyfold.isScSmoothMap_snd _ _).comp (MPolyfold.isScSmoothMap_snd _ _))

theorem preimage_sheetProj_obj (x : Fin 1 → ℝ) : (sheetProj hK).obj ⁻¹' {x} = univ ×ˢ {x} := by
  ext p
  simp [sheetProj]

/-- Definition 8.5.1 (3) for `sheetProj`: `φ ↦ (P φ, s φ)` is an sc-diffeomorphism
`𝐀 → 𝐁 ₛ×_P A`, with inverse `((k, y), (i, x)) ↦ (k, (i, x))`. -/
theorem isScDiffeoOn_sheetProj_fibredMap
    [ParacompactSpace ((K × (Fin 1 → ℝ)) × (K × (Fin 1 → ℝ)))]
    [ParacompactSpace (MPolyfold.fibredProduct (actionEpGroupoid hK).src (sheetProj hK).obj)] :
    (sheetActionEp hK).PMor.IsScDiffeoOn (MPolyfold.subPolyfold
      (MPolyfold.isSubMPolyfold_fibredProduct (actionEpGroupoid hK).isLocalScDiffeo_src
        (sheetProj hK).isScSmoothMap_obj)) (sheetProj hK).fibredMap
      (fun q => ((q : (K × (Fin 1 → ℝ)) × (K × (Fin 1 → ℝ))).1.1,
        (q : (K × (Fin 1 → ℝ)) × (K × (Fin 1 → ℝ))).2)) univ univ where
  isScSmoothOn := MPolyfold.isScSmoothOn_subPolyfold_of_val _
    (MPolyfold.IsScSmoothOn.prodMk (sheetProj hK).isScSmoothMap_mor
      (sheetActionEp hK).isScSmoothMap_src)
  isScSmoothOn_inv :=
    MPolyfold.IsScSmoothMap.comp
      (g := fun r : (K × (Fin 1 → ℝ)) × (K × (Fin 1 → ℝ)) => (r.1.1, r.2))
      (MPolyfold.IsScSmoothOn.prodMk
        ((MPolyfold.isScSmoothMap_fst (discretePolyfold K) (rnPolyfold 1)).comp
          (MPolyfold.isScSmoothMap_fst (actionEpGroupoid hK).PMor (sheetActionEp hK).PObj))
        (MPolyfold.isScSmoothMap_snd (actionEpGroupoid hK).PMor (sheetActionEp hK).PObj))
      (MPolyfold.subPolyfold_inclusion_isScSmooth _)
  mapsTo := mapsTo_univ _ _
  mapsTo_inv := mapsTo_univ _ _
  left_inv _ _ := rfl
  right_inv q _ := Subtype.ext (Prod.ext (Prod.ext rfl q.2.symm) rfl)

/-- **`K ⋉ (K × ℝ) → K ⋉ ℝ` is a proper covering functor** (Definition 8.5.1): a surjective local
sc-diffeomorphism on objects, `P⁻¹(x) = K × {x}` evenly covered by the disjoint sheets `{i} × ℝ`,
and `𝐀 ≅ 𝐁 ₛ×_P A` (`isScDiffeoOn_sheetProj_fibredMap`). -/
theorem sheetProj_isProperCovering : (sheetProj hK).IsProperCovering where
  surjective x := ⟨(1, x), rfl⟩
  isLocalScDiffeo p :=
    ⟨{p.1} ×ˢ univ, univ, fun y => (p.1, y), ⟨rfl, mem_univ _⟩, isScDiffeoOn_snd_sheet p.1⟩
  finite_fiber x := by
    rw [preimage_sheetProj_obj]
    exact finite_univ.prod (finite_singleton x)
  evenlyCovered x := by
    refine ⟨univ, fun y => {y.1} ×ˢ univ, fun y z => (y.1, z), isOpen_univ, mem_univ x, ?_,
      fun y _ => ⟨⟨rfl, mem_univ _⟩, isScDiffeoOn_snd_sheet y.1⟩, ?_⟩
    · intro y hy z hz hyz
      refine Set.disjoint_left.2 fun p hp hp' => hyz (Prod.ext ?_ ?_)
      · exact (hp.1 : p.1 = y.1).symm.trans hp'.1
      · exact (hy : y.2 = x).trans (hz : z.2 = x).symm
    · rw [preimage_univ]
      refine (eq_univ_of_forall fun p => ?_).symm
      exact mem_iUnion₂.2 ⟨(p.1, x), rfl, ⟨rfl, mem_univ _⟩⟩
  isScDiffeo_fibredMap := by
    have := MPolyfold.paracompactSpace_prod (actionEpGroupoid hK).PMor (sheetActionEp hK).PObj
    have := ((actionEpGroupoid hK).PMor.prod (sheetActionEp hK).PObj).paracompactSpace_subtype
      (MPolyfold.fibredProduct (actionEpGroupoid hK).src (sheetProj hK).obj)
    exact ⟨_, isScDiffeoOn_sheetProj_fibredMap hK⟩

end Sheets

section Example

/-- The objects `ℤˣ × ℝ` of `absA` (`ℝ × {1, 2}`, two copies of `ℝ`), as an M-polyfold. -/
def coverPolyfold : MPolyfold (ℤˣ × (Fin 1 → ℝ)) := sheetPolyfold ℤˣ

/-- `k (i, x) = (k i, k x)` is sc-smooth. -/
theorem isScSmoothMap_cover_smul (k : ℤˣ) :
    coverPolyfold.IsScSmoothMap coverPolyfold fun p : ℤˣ × (Fin 1 → ℝ) => k • p :=
  isScSmoothMap_sheet_smul isScSmoothMap_units_smul k

/-- **`A = ℤ/2 ⋉ (ℝ × {1, 2})`**: `ℤ/2 = ℤˣ` acting on `ℤˣ × ℝ` by `k (i, x) = (k i, k x)`, that is
`g(x, i) = (−x, σ i)` for the generator. -/
def absA : EpGroupoid (ℤˣ × (Fin 1 → ℝ)) (ℤˣ × (ℤˣ × (Fin 1 → ℝ))) :=
  actionEpGroupoid isScSmoothMap_cover_smul

/-- **`B = ℤ/2 ⋉ ℝ`** by the reflection (Chapter 7's `reflectionEpGroupoid`). -/
def absB : EpGroupoid (Fin 1 → ℝ) (ℤˣ × (Fin 1 → ℝ)) := reflectionEpGroupoid

theorem absA_smul (k i : ℤˣ) (x : Fin 1 → ℝ) : k • (i, x) = (k * i, k • x) := rfl

/-- **The projection functor `P : A → B`**, `(i, x) ↦ x` on objects and `(k, (i, x)) ↦ (k, x)` on
morphisms (`sheetProj` for `ℤˣ`). -/
def absP : EpFunctor absA absB := sheetProj isScSmoothMap_units_smul

@[simp] theorem absP_obj (p : ℤˣ × (Fin 1 → ℝ)) : absP.obj p = p.2 := rfl

@[simp] theorem absP_mor (φ : ℤˣ × (ℤˣ × (Fin 1 → ℝ))) : absP.mor φ = (φ.1, φ.2.2) := rfl

/-- **`P` is a proper covering functor** (Definition 8.5.1): `P` is a surjective local
sc-diffeomorphism on objects, `P⁻¹(x) = {(1, x), (−1, x)}` is evenly covered by the disjoint sheets
`{±1} × ℝ`, and `𝐀 ≅ 𝐁 ₛ×_P A`. -/
theorem absP_isProperCovering : absP.IsProperCovering :=
  sheetProj_isProperCovering isScSmoothMap_units_smul

theorem units_smul_fin_one_apply (k : ℤˣ) (x : Fin 1 → ℝ) (j : Fin 1) :
    (k • x) j = (k : ℤ) * x j := by
  rcases Int.units_eq_one_or k with rfl | rfl
  · simp
  · rw [units_smul_rn_neg_one]
    simp

theorem units_mul_self_real (k : ℤˣ) : ((k : ℤ) : ℝ) * (k : ℤ) = 1 := by
  rcases Int.units_eq_one_or k with rfl | rfl <;> norm_num

theorem fin_one_ext {x y : Fin 1 → ℝ} (h : x 0 = y 0) : x = y :=
  funext fun j => by rw [Fin.fin_one_eq_zero j]; exact h

/-! #### The orbit spaces -/

/-- `|A| → ℝ`, `|(i, x)| ↦ i x`. -/
def absAOrbitToReal : absA.OrbitSpace → ℝ :=
  Quotient.lift (fun p : ℤˣ × (Fin 1 → ℝ) => ((p.1 : ℤ) : ℝ) * p.2 0) fun p q hpq => by
    obtain ⟨k, rfl⟩ := (action_isomorphic_iff isScSmoothMap_cover_smul).1 hpq
    change ((p.1 : ℤ) : ℝ) * p.2 0 = (((k * p.1 : ℤˣ) : ℤ) : ℝ) * (k • p.2) 0
    rw [units_smul_fin_one_apply, Units.val_mul, Int.cast_mul]
    calc ((p.1 : ℤ) : ℝ) * p.2 0 = (((k : ℤ) : ℝ) * (k : ℤ)) * ((p.1 : ℤ) * p.2 0) := by
          rw [units_mul_self_real, one_mul]
      _ = _ := by ring

/-- **`|A| ≃ₜ ℝ`**, `|(i, x)| ↦ i x`, with inverse `t ↦ |(1, t)|`. -/
def absAOrbitHomeomorph : absA.OrbitSpace ≃ₜ ℝ where
  toFun := absAOrbitToReal
  invFun t := absA.π (1, fun _ => t)
  left_inv z := by
    induction z using Quotient.inductionOn with | h p => ?_
    refine (action_π_eq_π_iff isScSmoothMap_cover_smul).2 ⟨p.1, Prod.ext (mul_one _) ?_⟩
    refine fin_one_ext ?_
    change (p.1 • fun _ : Fin 1 => ((p.1 : ℤ) : ℝ) * p.2 0) 0 = p.2 0
    rw [units_smul_fin_one_apply, ← mul_assoc, units_mul_self_real, one_mul]
  right_inv t := by
    change (((1 : ℤˣ) : ℤ) : ℝ) * t = t
    simp
  continuous_toFun := continuous_quot_lift _
    (((continuous_of_discreteTopology (f := fun k : ℤˣ => ((k : ℤ) : ℝ))).comp continuous_fst).mul
      ((continuous_apply 0).comp continuous_snd))
  continuous_invFun := absA.continuous_π.comp
    (continuous_const.prodMk (continuous_pi fun _ => continuous_id))

@[simp] theorem absAOrbitHomeomorph_π (p : ℤˣ × (Fin 1 → ℝ)) :
    absAOrbitHomeomorph (absA.π p) = ((p.1 : ℤ) : ℝ) * p.2 0 := rfl

/-- `|B| → [0, ∞)`, `|x| ↦ |x|`. -/
def absBOrbitToIci : absB.OrbitSpace → Ici (0 : ℝ) :=
  Quotient.lift (fun x : Fin 1 → ℝ => (⟨|x 0|, mem_Ici.2 (abs_nonneg _)⟩ : Ici (0 : ℝ))) fun x y hxy => by
    obtain ⟨k, rfl⟩ := (action_isomorphic_iff isScSmoothMap_units_smul).1 hxy
    refine Subtype.ext ?_
    change |x 0| = |(k • x) 0|
    rw [units_smul_fin_one_apply, abs_mul]
    rcases Int.units_eq_one_or k with rfl | rfl <;> simp

/-- **`|B| ≃ₜ [0, ∞)`**, `|x| ↦ |x|`, with inverse `t ↦ |t|`. -/
def absBOrbitHomeomorph : absB.OrbitSpace ≃ₜ Ici (0 : ℝ) where
  toFun := absBOrbitToIci
  invFun t := absB.π fun _ => (t : ℝ)
  left_inv z := by
    induction z using Quotient.inductionOn with | h x => ?_
    rcases le_total 0 (x 0) with hx | hx
    · refine (action_π_eq_π_iff isScSmoothMap_units_smul).2 ⟨1, fin_one_ext ?_⟩
      change ((1 : ℤˣ) • fun _ : Fin 1 => |x 0|) 0 = x 0
      rw [one_smul, abs_of_nonneg hx]
    · refine (action_π_eq_π_iff isScSmoothMap_units_smul).2 ⟨-1, fin_one_ext ?_⟩
      change ((-1 : ℤˣ) • fun _ : Fin 1 => |x 0|) 0 = x 0
      rw [units_smul_rn_neg_one, abs_of_nonpos hx]
      simp
  right_inv t := Subtype.ext (by
    change |(t : ℝ)| = t
    exact abs_of_nonneg (mem_Ici.1 t.2))
  continuous_toFun := continuous_quot_lift _
    (((continuous_apply 0).abs).subtype_mk _)
  continuous_invFun := absB.continuous_π.comp
    (continuous_pi fun _ => continuous_subtype_val)

@[simp] theorem absBOrbitHomeomorph_π (x : Fin 1 → ℝ) :
    (absBOrbitHomeomorph (absB.π x) : ℝ) = |x 0| := rfl

/-- **`|P|` is the absolute value**: under `|A| ≃ₜ ℝ` and `|B| ≃ₜ [0, ∞)`, `|P|(t) = |t|`. -/
theorem absBOrbitHomeomorph_orbitMap (z : absA.OrbitSpace) :
    (absBOrbitHomeomorph (absP.orbitMap z) : ℝ) = |absAOrbitHomeomorph z| := by
  induction z using Quotient.inductionOn with | h p => ?_
  change (absBOrbitHomeomorph (absB.π p.2) : ℝ) = |absAOrbitHomeomorph (absA.π p)|
  rw [absBOrbitHomeomorph_π, absAOrbitHomeomorph_π, abs_mul]
  rcases Int.units_eq_one_or p.1 with h | h <;> rw [h] <;> simp

/-! #### `|P|`: the 2017 form of Proposition 19.7.18 holds -/

/-- `|P|` is continuous. -/
theorem absP_orbitMap_continuous : Continuous absP.orbitMap := orbitMap_continuous absP

/-- `|P|` is open. -/
theorem absP_orbitMap_isOpenMap : IsOpenMap absP.orbitMap :=
  orbitMap_isOpenMap absP
    (absP_isProperCovering.isLocalScDiffeo.isLocalHomeomorph.isOpenMap)

/-- `|P|` is surjective. -/
theorem absP_orbitMap_surjective : Surjective absP.orbitMap :=
  orbitMap_surjective absP absP_isProperCovering.surjective

/-- The fibres of `|P|` are finite (at most `|(1, ±t)|`). -/
theorem absP_orbitMap_finite_fiber (w : absB.OrbitSpace) : (absP.orbitMap ⁻¹' {w}).Finite := by
  have hsub : absP.orbitMap ⁻¹' {w} ⊆ absAOrbitHomeomorph.symm ''
      {(absBOrbitHomeomorph w : ℝ), -(absBOrbitHomeomorph w : ℝ)} := by
    intro z hz
    refine ⟨absAOrbitHomeomorph z, ?_, absAOrbitHomeomorph.symm_apply_apply z⟩
    have := absBOrbitHomeomorph_orbitMap z
    rw [show absP.orbitMap z = w from hz] at this
    rcases abs_choice (absAOrbitHomeomorph z) with h | h
    · left; rw [this, h]
    · right; rw [this, h, neg_neg]; rfl
  exact ((toFinite _).image _).subset hsub

/-! #### `|P|` is not a local homeomorphism -/

theorem absA_π_ne (i : ℤˣ) {t : ℝ} (ht : t ≠ 0) :
    absA.π (i, fun _ => t) ≠ absA.π (i, fun _ => -t) := by
  intro h
  have := congrArg absAOrbitHomeomorph h
  rw [absAOrbitHomeomorph_π, absAOrbitHomeomorph_π] at this
  have hi : ((i : ℤ) : ℝ) ≠ 0 := by
    rcases Int.units_eq_one_or i with rfl | rfl <;> norm_num
  have : t = -t := mul_left_cancel₀ hi this
  exact ht (by linarith)

theorem absP_orbitMap_neg (i : ℤˣ) (t : ℝ) :
    absP.orbitMap (absA.π (i, fun _ => t)) = absP.orbitMap (absA.π (i, fun _ => -t)) := by
  change absB.π (fun _ => t) = absB.π (fun _ => -t)
  refine (action_π_eq_π_iff isScSmoothMap_units_smul).2 ⟨-1, ?_⟩
  rw [units_smul_rn_neg_one]
  rfl

/-- **`|P|` is not a local homeomorphism at `|(i, 0)|`**: every neighbourhood of `|(i, 0)|` contains
`|(i, t)| ≠ |(i, −t)|` (`t ≠ 0` small), which `|P|` identifies. -/
theorem absCovering_orbitMap_not_isLocalHomeomorphOn_zero (i : ℤˣ) :
    ¬ IsLocalHomeomorphOn absP.orbitMap {absA.π (i, 0)} := by
  intro h
  obtain ⟨N, hN, hemb⟩ :=
    (isLocalHomeomorphOn_iff_isOpenEmbedding_restrict _).1 h _ (mem_singleton _)
  have hinj : InjOn absP.orbitMap N := injOn_iff_injective.2 hemb.injective
  set c : ℝ → absA.OrbitSpace := fun t => absA.π (i, fun _ => t) with hc
  have hcc : Continuous c := absA.continuous_π.comp
    (continuous_const.prodMk (continuous_pi fun _ => continuous_id))
  have hc0 : c 0 = absA.π (i, 0) := rfl
  have h1 : ∀ᶠ t in 𝓝 (0 : ℝ), c t ∈ N := hcc.continuousAt.preimage_mem_nhds (hc0 ▸ hN)
  have h2 : ∀ᶠ t in 𝓝 (0 : ℝ), c (-t) ∈ N := by
    have : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_neg.tendsto (0 : ℝ))
    exact this.eventually h1
  obtain ⟨t, ⟨ht1, ht2⟩, ht0⟩ :=
    ((h1.and h2).filter_mono nhdsWithin_le_nhds |>.and self_mem_nhdsWithin).exists
      (f := 𝓝[≠] (0 : ℝ))
  exact absA_π_ne i ht0 (hinj ht1 ht2 (absP_orbitMap_neg i t))

/-- **`|P| : |A| → |B|` is not a local homeomorphism** (serves Proposition 19.7.18,
Corollary 19.7.20 (3), Theorem 19.7.25 (4b): does not hold as we read it), although `P` is a proper
covering functor (`absP_isProperCovering`) and `|P|` is a continuous open surjection with finite
fibres: under `|A| ≅ ℝ`, `|B| ≅ [0, ∞)` it is `t ↦ |t|`. -/
theorem absCovering_orbitMap_not_isLocalHomeomorph : ¬ IsLocalHomeomorph absP.orbitMap :=
  fun h => absCovering_orbitMap_not_isLocalHomeomorphOn_zero 1
    (h.isLocalHomeomorphOn (s := {absA.π (1, 0)}))

/-! #### The criterion in the example -/

/-- **`P` maps `Aut(a)` onto `Aut(P a)` iff `a = (i, x)` with `x ≠ 0`**: for `x ≠ 0` both groups are
trivial; at `x = 0`, `Aut(i, 0) = 1` (`k i = i` forces `k = 1`) while `(−1, 0) ∈ Aut(0)`. -/
theorem absP_isotropy_surjective_iff (a : ℤˣ × (Fin 1 → ℝ)) :
    (∀ ψ : absB.Isotropy (absP.obj a), ∃ φ : absA.Isotropy a, absP.mor φ.val = ψ.val) ↔
      a.2 ≠ 0 := by
  constructor
  · intro h ha
    obtain ⟨φ, hφ⟩ := h ⟨(-1, a.2), rfl, by
      change (-1 : ℤˣ) • a.2 = a.2
      rw [ha, smul_zero]⟩
    have hφa : φ.val.2 = a := φ.src_val
    have hφt : φ.val.1 • φ.val.2 = a := φ.tgt_val
    rw [hφa] at hφt
    have h1 : φ.val.1 * a.1 = a.1 := congrArg Prod.fst hφt
    have h2 : φ.val.1 = 1 := by simpa using h1
    have : φ.val.1 = -1 := congrArg Prod.fst hφ
    rw [h2] at this
    exact absurd this (by decide)
  · intro ha ψ
    have hψs : ψ.val.2 = a.2 := ψ.src_val
    have hψt : ψ.val.1 • ψ.val.2 = a.2 := ψ.tgt_val
    rw [hψs] at hψt
    have hψ1 : ψ.val.1 = 1 := by
      rcases Int.units_eq_one_or ψ.val.1 with h | h
      · exact h
      · exfalso
        rw [h, units_smul_rn_neg_one] at hψt
        have h0 : (-a.2) 0 = a.2 0 := congrFun hψt 0
        rw [Pi.neg_apply] at h0
        exact ha (fin_one_ext (by rw [Pi.zero_apply]; linarith))
    refine ⟨⟨(1, a), rfl, one_smul _ _⟩, Prod.ext hψ1.symm hψs.symm⟩

/-- **The criterion is an equivalence in the example**: `|P|` is a local homeomorphism at `|a|` iff
`P` maps `Aut(a)` onto `Aut(P a)` (iff `a = (i, x)`, `x ≠ 0`). The "if" direction is
`isLocalHomeomorphOn_orbitMap_of_isotropy_surjective`. -/
theorem absP_isLocalHomeomorphOn_iff (a : ℤˣ × (Fin 1 → ℝ)) :
    IsLocalHomeomorphOn absP.orbitMap {absA.π a} ↔
      ∀ ψ : absB.Isotropy (absP.obj a), ∃ φ : absA.Isotropy a, absP.mor φ.val = ψ.val := by
  constructor
  · intro h
    rw [absP_isotropy_surjective_iff]
    intro ha
    have : a = (a.1, 0) := Prod.ext rfl ha
    rw [this] at h
    exact absCovering_orbitMap_not_isLocalHomeomorphOn_zero a.1 h
  · exact isLocalHomeomorphOn_orbitMap_of_isotropy_surjective (hPU := isScSmoothMap_cover_smul)
      (hPV := isScSmoothMap_units_smul) absP
      absP_isProperCovering.isLocalScDiffeo.isLocalHomeomorph a

end Example

/-! ### The converse of the criterion needs more: a trivial action -/

section TrivialAction

/-- `ℤ/3 ⋉ (ℤ/3 × ℝ) → ℤ/3 ⋉ ℝ` with `ℤ/3` acting trivially on `ℝ` (Chapter 7's
`trivialZ3EpGroupoid`), `(i, x) ↦ x`. -/
def trivialSheetProj : EpFunctor (sheetActionEp isScSmoothMap_z3_smul) trivialZ3EpGroupoid :=
  sheetProj isScSmoothMap_z3_smul

theorem trivialSheetProj_orbitMap_injective : Injective trivialSheetProj.orbitMap := by
  intro z w hzw
  induction z using Quotient.inductionOn with | h p => ?_
  induction w using Quotient.inductionOn with | h q => ?_
  obtain ⟨k, hk⟩ := (action_π_eq_π_iff isScSmoothMap_z3_smul).1
    (hzw : trivialZ3EpGroupoid.π p.2 = trivialZ3EpGroupoid.π q.2)
  rw [z3_smul_eq] at hk
  refine (action_π_eq_π_iff (isScSmoothMap_sheet_smul isScSmoothMap_z3_smul)).2
    ⟨q.1 * p.1⁻¹, Prod.ext ?_ ?_⟩
  · change q.1 * p.1⁻¹ * p.1 = q.1
    rw [inv_mul_cancel_right]
  · exact (z3_smul_eq _ _).trans hk

/-- **The "only if" of the criterion does not hold in general**: for `ℤ/3` acting trivially on `ℝ`
and by translation on `ℤ/3 × ℝ`, `P : ℤ/3 ⋉ (ℤ/3 × ℝ) → ℤ/3 ⋉ ℝ` is a proper covering functor
(Definition 8.5.1) and `|P|` is a local homeomorphism (a homeomorphism `|A| ≅ ℝ ≅ |B|`), but at every
`a`, `Aut(a) = 1` does not map onto `Aut(P a) = ℤ/3`. -/
theorem isotropy_surjective_not_necessary :
    trivialSheetProj.IsProperCovering ∧ IsLocalHomeomorph trivialSheetProj.orbitMap ∧
      ∀ a, ¬ ∀ ψ : trivialZ3EpGroupoid.Isotropy (trivialSheetProj.obj a),
        ∃ φ : (sheetActionEp isScSmoothMap_z3_smul).Isotropy a, trivialSheetProj.mor φ.val = ψ.val := by
  have hcov : trivialSheetProj.IsProperCovering := sheetProj_isProperCovering isScSmoothMap_z3_smul
  refine ⟨hcov, ?_, fun a h => ?_⟩
  · refine IsOpenEmbedding.isLocalHomeomorph
      (isOpenEmbedding_iff_continuous_injective_isOpenMap.2 ⟨orbitMap_continuous _,
        trivialSheetProj_orbitMap_injective,
        orbitMap_isOpenMap _ hcov.isLocalScDiffeo.isLocalHomeomorph.isOpenMap⟩)
  · obtain ⟨φ, hφ⟩ := h ⟨(Multiplicative.ofAdd 1, a.2), rfl, rfl⟩
    have hφa : φ.val.2 = a := φ.src_val
    have hφt : φ.val.1 • φ.val.2 = a := φ.tgt_val
    rw [hφa] at hφt
    have h1 : φ.val.1 * a.1 = a.1 := congrArg Prod.fst hφt
    have h2 : φ.val.1 = 1 := by simpa using h1
    have h3 : φ.val.1 = Multiplicative.ofAdd 1 := congrArg Prod.fst hφ
    rw [h2] at h3
    exact absurd h3 (by decide)

end TrivialAction

end Chapter19

end Polyfold
