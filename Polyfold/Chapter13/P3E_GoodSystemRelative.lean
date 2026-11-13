import Polyfold.Chapter13.P3G_GoodSystemExistence

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2021), Part III, §13.1, p. 602:
**Theorem 13.1.7** (extension of good partial systems; 2017: Theorem 13.1) with the hypothesis
read *inside* the full subcategory on `Q`.

# Properness relative to `Q` versus relative to `X`

## The text, paraphrased

Theorem 13.1.7 starts from an open `Q` of the object space with `|Q| = |X|`, equips the full
subcategory on `Q` with the induced ep-groupoid structure, and takes a good system
`(U(q))_{q ∈ Q}` *for the ep-groupoid `Q`*.  Its condition (1) is therefore read in `Q`:
`t : s⁻¹(cl_Q U(q)) → Q` is proper, where `s, t` are the source and target maps of the
morphisms of `Q` (the morphisms of `X` with source and target in `Q`).

## What is formalized (namespace `Polyfold.EpGroupoid`)

* The full subcategory on `Q`: its morphism set is `X.morOn Q` (Definition 7.1.1's `morOn`),
  with `subSrc Q, subTgt Q : X.morOn Q → Q`.  `IsProperSubsetIn Q A` (for `A ⊆ Q`) is
  Definition 7.5.8 inside `Q`: `subTgt Q : subSrc Q⁻¹(A) → Q` is proper.
* `IsGoodIn N Q`: the good-system conditions for the ep-groupoid `Q`, with (1) read in `Q`
  (`cl_Q U(q)` is the closure in the subspace `Q`).
* `closure_subset_of_isProperSubsetIn`: for open `Q` with `|Q| = |X|`, `Q`-properness of
  `cl_Q U` forces `cl_X U ⊆ Q`.
* `isProperSubset_of_isProperSubsetIn`: … and then `cl_X U` is proper in `X`.
* `isProperSubsetIn_of_isProperSubset`: the converse, when `cl_X U ⊆ Q`.
* `isGoodIn_iff`: `IsGoodIn N Q ↔ IsGoodOn N Q ∧ ∀ q ∈ Q, cl_X U(q) ⊆ Q`.
* **Theorem 13.1.7 as printed**: `theorem_13_1_7_book` (hypothesis `IsGoodIn N Q`), from the
  project's `theorem_13_1_7` (hypothesis `IsGoodOn N Q`).
* Witness: `GoodSystem.isGoodIn_univ` (every good system is a good system for `Q = X`).

## Reading

* The natural actions and the sets `𝒰(q, q')` are the same in `X` and in the full subcategory
  on the open `Q` (all their morphisms lie in `Q`), so conditions (2) and (3) are taken over
  verbatim from `IsGoodOn`; only (1) changes.
* The proofs use ultrafilters (`isProperMap_iff_ultrafilter`) instead of the text's
  sequences.  Both directions use a local section `σ` of `s` through a morphism `χ : z → q''`
  with `q'' ∈ Q` (it exists since `|Q| = |X|`), defined on an open `V ∋ z` with `t ∘ σ ∈ Q`:
  * `cl_X U ⊆ Q`: for `y ∈ cl_X U`, the morphisms `σ(y')`, `y' ∈ U` near `y`, have targets in `Q`
    near `t(χ)`; `Q`-properness gives a limit in `Mor(Q)` with source in `Q`, which is `χ`
    (Hausdorff), so `y = s(χ) ∈ Q`.
  * properness in `X`: a family `φ` with `s(φ) ∈ cl_X U` and `t(φ) → z` is moved into `Q` by
    `φ ↦ σ(t φ) ∘ φ`; a limit `ρ` there gives the limit `χ⁻¹ ∘ ρ` of `φ`.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-! ### Proper maps through inducing maps and ultrafilters -/

/-- A map `f : α → β` is proper iff ultrafilters on the ambient `γ ⊇ α` (through the inducing
injective `j`) with target limits in `β` (through the inducing `e`) converge in `α`. -/
theorem isProperMap_iff_ultrafilter_of_isInducing {α β γ δ : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ] {j : α → γ}
    (hj : IsInducing j) (hinj : Injective j) {e : β → δ} (he : IsInducing e) {f : α → β}
    (hf : Continuous f) {g : γ → δ} (hfg : ∀ a, e (f a) = g (j a)) :
    IsProperMap f ↔ ∀ (𝒱 : Ultrafilter γ) (b : β), range j ∈ 𝒱 → Tendsto g 𝒱 (𝓝 (e b)) →
      ∃ a, f a = b ∧ (𝒱 : Filter γ) ≤ 𝓝 (j a) := by
  have hgj : g ∘ j = e ∘ f := funext fun a => (hfg a).symm
  constructor
  · intro h 𝒱 b hR hT
    let 𝒰 := 𝒱.comap hinj hR
    have hT' : Tendsto f 𝒰 (𝓝 b) := by
      rw [he.tendsto_nhds_iff, ← hgj, Ultrafilter.coe_comap]
      exact hT.comp tendsto_comap
    obtain ⟨a, hfa, ha⟩ := (isProperMap_iff_ultrafilter.1 h).2 hT'
    refine ⟨a, hfa, ?_⟩
    have h1 : ((𝒱 : Filter γ).comap j).map j = 𝒱 := map_comap_of_mem hR
    rw [← h1]
    have h2 : ((𝒱 : Filter γ).comap j) ≤ 𝓝 a := by rw [← Ultrafilter.coe_comap _ hinj hR]; exact ha
    exact (map_mono h2).trans (hj.continuous.tendsto a)
  · intro h
    refine isProperMap_iff_ultrafilter.2 ⟨hf, fun 𝒰 b hT => ?_⟩
    have hR : range j ∈ 𝒰.map j := by
      rw [Ultrafilter.mem_map, preimage_range]; exact univ_mem
    have hT' : Tendsto g (𝒰.map j) (𝓝 (e b)) := by
      rw [Ultrafilter.coe_map, tendsto_map'_iff, hgj]
      exact (he.continuous.tendsto b).comp hT
    obtain ⟨a, hfa, ha⟩ := h (𝒰.map j) b hR hT'
    refine ⟨a, hfa, ?_⟩
    rw [hj.nhds_eq_comap a]
    exact le_comap_map.trans (comap_mono (by rw [← Ultrafilter.coe_map]; exact ha))

/-- **Properness of `cl` sets by ultrafilters** (Definition 7.5.8): `K` is proper iff every
ultrafilter on `𝐗` concentrated on `s⁻¹(K)` with `t`-limit `z` converges to some `φ` with
`s φ ∈ K` and `t φ = z`. -/
theorem isProperSubset_iff_ultrafilter (K : Set Obj) :
    X.IsProperSubset K ↔ ∀ (𝒱 : Ultrafilter Mor) (z : Obj), X.src ⁻¹' K ∈ 𝒱 →
      Tendsto X.tgt 𝒱 (𝓝 z) → ∃ φ, X.src φ ∈ K ∧ X.tgt φ = z ∧ (𝒱 : Filter Mor) ≤ 𝓝 φ := by
  unfold IsProperSubset
  rw [isProperMap_iff_ultrafilter_of_isInducing IsInducing.subtypeVal Subtype.val_injective
    IsInducing.id (f := (X.src ⁻¹' K).domRestrict X.tgt)
    (X.continuous_tgt.comp continuous_subtype_val) (g := X.tgt) (fun _ => rfl),
    Subtype.range_coe]
  refine forall₂_congr fun 𝒱 z => imp_congr_right fun _ => imp_congr_right fun _ => ?_
  constructor
  · rintro ⟨a, rfl, ha⟩; exact ⟨a, a.2, rfl, ha⟩
  · rintro ⟨φ, hφ, rfl, ha⟩; exact ⟨⟨φ, hφ⟩, rfl, ha⟩

/-! ### The full subcategory on `Q` -/

/-- The source map of the full subcategory on `Q`, `Mor(Q) = X.morOn Q → Q`. -/
def subSrc (Q : Set Obj) : X.morOn Q → Q := fun φ => ⟨X.src φ, φ.2.1⟩

/-- The target map of the full subcategory on `Q`, `Mor(Q) = X.morOn Q → Q`. -/
def subTgt (Q : Set Obj) : X.morOn Q → Q := fun φ => ⟨X.tgt φ, φ.2.2⟩

theorem continuous_subTgt (Q : Set Obj) : Continuous (X.subTgt Q) :=
  (X.continuous_tgt.comp continuous_subtype_val).subtype_mk _

/-- **Definition 7.5.8 inside the full subcategory on `Q`**: `A ⊆ Q` is proper for the
ep-groupoid `Q` if `t : s⁻¹(A) ∩ Mor(Q) → Q` is proper. -/
def IsProperSubsetIn (Q : Set Obj) (A : Set Q) : Prop :=
  IsProperMap ((X.subSrc Q ⁻¹' A).domRestrict (X.subTgt Q))

/-- **A good system for the ep-groupoid `Q`** (the hypothesis of Theorem 13.1.7 as printed):
for `q ∈ Q`, `U(q) ⊆ Q` carries the natural action, (1) `t : s⁻¹(cl_Q U(q)) → Q` is proper in
the full subcategory on `Q` (the closure taken in the subspace `Q`), and (3) holds for
`q, q' ∈ Q`. -/
structure IsGoodIn (N : ∀ x : Obj, X.NatNbhd x) (Q : Set Obj) : Prop where
  subset : ∀ q ∈ Q, (N q).U ⊆ Q
  isProperSubsetIn_closure : ∀ q ∈ Q,
    X.IsProperSubsetIn Q (closure ((↑) ⁻¹' (N q).U : Set Q))
  isDiffeoComponent : ∀ q ∈ Q, ∀ q' ∈ Q, ∀ φ ∈ X.morBetween (N q).U (N q').U,
    X.IsDiffeoComponent (connectedComponentIn (X.morBetween (N q).U (N q').U) φ)

variable {X}

omit [T2Space Obj] [ParacompactSpace Obj] in
/-- For `U ⊆ Q`, a point of `Q` lies in `cl_Q U` iff it lies in `cl_X U`. -/
theorem mem_closure_preimage_val_iff {Q U : Set Obj} (hUQ : U ⊆ Q) (y : Q) :
    y ∈ closure ((↑) ⁻¹' U : Set Q) ↔ (y : Obj) ∈ closure U := by
  rw [closure_subtype, Subtype.image_preimage_coe, inter_eq_right.2 hUQ]

/-- **`Q`-properness by ultrafilters on `𝐗`**: for `U ⊆ Q`, `cl_Q U` is proper in `Q` iff
every ultrafilter on `𝐗` concentrated on `Mor(Q) ∩ s⁻¹(cl_X U)` with `t`-limit `z ∈ Q`
converges to such a morphism with target `z`. -/
theorem isProperSubsetIn_iff_ultrafilter {Q U : Set Obj} (hUQ : U ⊆ Q) :
    X.IsProperSubsetIn Q (closure ((↑) ⁻¹' U : Set Q)) ↔
      ∀ (𝒱 : Ultrafilter Mor) (z : Obj), z ∈ Q →
        X.morOn Q ∩ X.src ⁻¹' closure U ∈ 𝒱 → Tendsto X.tgt 𝒱 (𝓝 z) →
          ∃ φ ∈ X.morOn Q ∩ X.src ⁻¹' closure U, X.tgt φ = z ∧ (𝒱 : Filter Mor) ≤ 𝓝 φ := by
  set D := X.subSrc Q ⁻¹' closure ((↑) ⁻¹' U : Set Q)
  let j : D → Mor := fun a => (a.1 : Mor)
  have hj : IsInducing j := IsInducing.subtypeVal.comp IsInducing.subtypeVal
  have hinj : Injective j := Subtype.val_injective.comp Subtype.val_injective
  have hrange : range j = X.morOn Q ∩ X.src ⁻¹' closure U := by
    ext φ
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a.1.2, (mem_closure_preimage_val_iff hUQ (X.subSrc Q a.1)).1 a.2⟩
    · rintro ⟨hφ, hcl⟩
      exact ⟨⟨⟨φ, hφ⟩, (mem_closure_preimage_val_iff hUQ (X.subSrc Q ⟨φ, hφ⟩)).2 hcl⟩, rfl⟩
  unfold IsProperSubsetIn
  rw [isProperMap_iff_ultrafilter_of_isInducing hj hinj IsInducing.subtypeVal
    (f := D.domRestrict (X.subTgt Q))
    ((X.continuous_subTgt Q).comp continuous_subtype_val) (g := X.tgt) (fun _ => rfl), hrange]
  constructor
  · intro h 𝒱 z hz hS hT
    obtain ⟨a, ha, hle⟩ := h 𝒱 ⟨z, hz⟩ hS hT
    refine ⟨j a, ?_, congrArg Subtype.val ha, hle⟩
    rw [← hrange]; exact mem_range_self a
  · intro h 𝒱 b hS hT
    obtain ⟨φ, hφ, htφ, hle⟩ := h 𝒱 b b.2 hS hT
    rw [← hrange] at hφ
    obtain ⟨a, rfl⟩ := hφ
    exact ⟨a, Subtype.ext htφ, hle⟩

/-! ### Local sections of `s` -/

/-- **A local section of `s` through `χ` with targets in an open `O ∋ t(χ)`**: an open
`V ∋ s(χ)` and `σ` continuous on `V` with `σ(s χ) = χ`, `s ∘ σ = id` and `t ∘ σ ∈ O` on `V`. -/
theorem exists_localSection (χ : Mor) {O : Set Obj} (hO : IsOpen O) (hχO : X.tgt χ ∈ O) :
    ∃ (V : Set Obj) (σ : Obj → Mor), IsOpen V ∧ X.src χ ∈ V ∧ ContinuousOn σ V ∧
      σ (X.src χ) = χ ∧ ∀ z ∈ V, X.src (σ z) = z ∧ X.tgt (σ z) ∈ O := by
  obtain ⟨W, V, σ, hχW, hd⟩ := X.isLocalScDiffeo_src χ
  have hσc : ContinuousOn σ V := hd.isScSmoothOn_inv.continuousOn
  have hVo : IsOpen V := hd.isScSmoothOn_inv.isOpen
  have hV' : IsOpen (V ∩ σ ⁻¹' (X.tgt ⁻¹' O)) :=
    hσc.isOpen_inter_preimage hVo (hO.preimage X.continuous_tgt)
  have hσχ : σ (X.src χ) = χ := hd.left_inv χ hχW
  refine ⟨_, σ, hV', ⟨hd.mapsTo hχW, ?_⟩, hσc.mono inter_subset_left, hσχ, fun z hz => ?_⟩
  · change X.tgt (σ (X.src χ)) ∈ O
    rw [hσχ]; exact hχO
  · refine ⟨?_, hz.2⟩
    have := hd.right_inv z hz.1
    exact this

/-- Every object `z` is the source of a morphism with target in `Q` when `|Q| = |X|`. -/
theorem exists_mor_tgt_mem {Q : Set Obj} (hπQ : X.π '' Q = univ) (z : Obj) :
    ∃ χ, X.src χ = z ∧ X.tgt χ ∈ Q := by
  obtain ⟨q, hq, hqz⟩ := hπQ.symm ▸ mem_univ (X.π z)
  obtain ⟨χ, h1, h2⟩ := (X.π_eq_π_iff).1 hqz.symm
  exact ⟨χ, h1, h2 ▸ hq⟩

/-! ### `Q`-properness implies `X`-properness -/

/-- **Step 1**: for open `Q` with `|Q| = |X|` and `U ⊆ Q`, if `cl_Q U` is proper in the full
subcategory on `Q`, then `cl_X U ⊆ Q` (so `cl_Q U = cl_X U`). -/
theorem closure_subset_of_isProperSubsetIn {Q U : Set Obj} (hQ : IsOpen Q)
    (hπQ : X.π '' Q = univ) (hUQ : U ⊆ Q)
    (hp : X.IsProperSubsetIn Q (closure ((↑) ⁻¹' U : Set Q))) : closure U ⊆ Q := by
  intro y hy
  obtain ⟨χ, rfl, hχQ⟩ := exists_mor_tgt_mem hπQ y
  obtain ⟨V, σ, hV, hyV, hσc, hσχ, hσ⟩ := exists_localSection (X := X) χ hQ hχQ
  have hne : (𝓝[U ∩ V] X.src χ).NeBot := by
    rw [nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hyV))]
    exact mem_closure_iff_nhdsWithin_neBot.1 hy
  let 𝒴 : Ultrafilter Obj := Ultrafilter.of (𝓝[U ∩ V] X.src χ)
  have h𝒴 : (𝒴 : Filter Obj) ≤ 𝓝[U ∩ V] X.src χ := Ultrafilter.of_le _
  have hUV : U ∩ V ∈ 𝒴 := h𝒴 self_mem_nhdsWithin
  have hσt : Tendsto σ 𝒴 (𝓝 χ) := by
    have := (hσc.continuousAt (hV.mem_nhds hyV)).tendsto
    rw [hσχ] at this
    exact this.mono_left (h𝒴.trans nhdsWithin_le_nhds)
  have hS : X.morOn Q ∩ X.src ⁻¹' closure U ∈ 𝒴.map σ := by
    rw [Ultrafilter.mem_map]
    refine Filter.mem_of_superset hUV fun z hz => ?_
    obtain ⟨h1, h2⟩ := hσ z hz.2
    refine ⟨⟨?_, h2⟩, ?_⟩
    · rw [h1]; exact hUQ hz.1
    · change X.src (σ z) ∈ closure U
      rw [h1]; exact subset_closure hz.1
  have hT : Tendsto X.tgt (𝒴.map σ) (𝓝 (X.tgt χ)) := by
    rw [Ultrafilter.coe_map]
    exact (X.continuous_tgt.tendsto χ).comp hσt
  obtain ⟨ρ, hρ, -, hle⟩ := (isProperSubsetIn_iff_ultrafilter hUQ).1 hp (𝒴.map σ) _ hχQ hS hT
  have hρχ : ρ = χ := by
    have h1 : Tendsto id (𝒴.map σ : Filter Mor) (𝓝 ρ) := hle
    have h2 : Tendsto id (𝒴.map σ : Filter Mor) (𝓝 χ) := by
      rw [Ultrafilter.coe_map]; exact hσt
    exact tendsto_nhds_unique h1 h2
  rw [← hρχ]
  exact hρ.1.1

/-- **Step 2**: for open `Q` with `|Q| = |X|` and `U ⊆ Q`, if `cl_Q U` is proper in the full
subcategory on `Q`, then `cl_X U` is proper in `X`. -/
theorem isProperSubset_of_isProperSubsetIn {Q U : Set Obj} (hQ : IsOpen Q)
    (hπQ : X.π '' Q = univ) (hUQ : U ⊆ Q)
    (hp : X.IsProperSubsetIn Q (closure ((↑) ⁻¹' U : Set Q))) :
    X.IsProperSubset (closure U) := by
  have hcl : closure U ⊆ Q := closure_subset_of_isProperSubsetIn hQ hπQ hUQ hp
  rw [isProperSubset_iff_ultrafilter]
  intro 𝒱 z hK hT
  obtain ⟨χ, rfl, hχQ⟩ := exists_mor_tgt_mem hπQ z
  obtain ⟨V, σ, hV, hzV, hσc, hσχ, hσ⟩ := exists_localSection (X := X) χ hQ hχQ
  set M := X.tgt ⁻¹' V
  have hMo : IsOpen M := hV.preimage X.continuous_tgt
  have hM𝒱 : M ∈ 𝒱 := hT (hV.mem_nhds hzV)
  let F : Mor → Mor := fun φ => X.comp (σ (X.tgt φ)) φ
  have hτ : ContinuousOn (fun φ => σ (X.tgt φ)) M :=
    hσc.comp X.continuous_tgt.continuousOn fun φ hφ => hφ
  have hFc : ContinuousOn F M :=
    continuousOn_comp_of_continuousOn hτ continuousOn_id fun φ hφ => (hσ _ hφ).1
  have hsrcF : ∀ φ ∈ M, X.src (F φ) = X.src φ := fun φ hφ =>
    X.src_comp _ _ (hσ _ hφ).1
  have htgtF : ∀ φ ∈ M, X.tgt (F φ) = X.tgt (σ (X.tgt φ)) := fun φ hφ =>
    X.tgt_comp _ _ (hσ _ hφ).1
  have hS : X.morOn Q ∩ X.src ⁻¹' closure U ∈ 𝒱.map F := by
    rw [Ultrafilter.mem_map]
    refine Filter.mem_of_superset (inter_mem hM𝒱 hK) fun φ hφ => ?_
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hsrcF φ hφ.1]; exact hcl hφ.2
    · rw [htgtF φ hφ.1]; exact (hσ _ hφ.1).2
    · change X.src (F φ) ∈ closure U
      rw [hsrcF φ hφ.1]; exact hφ.2
  have hσt : Tendsto (fun φ => σ (X.tgt φ)) 𝒱 (𝓝 χ) := by
    have := (hσc.continuousAt (hV.mem_nhds hzV)).tendsto
    rw [hσχ] at this
    exact this.comp hT
  have hT' : Tendsto X.tgt (𝒱.map F) (𝓝 (X.tgt χ)) := by
    rw [Ultrafilter.coe_map, tendsto_map'_iff]
    refine ((X.continuous_tgt.tendsto χ).comp hσt).congr' ?_
    filter_upwards [hM𝒱] with φ hφ
    exact (htgtF φ hφ).symm
  obtain ⟨ρ, hρ, htρ, hle⟩ :=
    (isProperSubsetIn_iff_ultrafilter hUQ).1 hp (𝒱.map F) _ hχQ hS hT'
  have hFt : Tendsto F 𝒱 (𝓝 ρ) := by
    have h := hle
    rwa [Ultrafilter.coe_map] at h
  -- `φ = σ(t φ)⁻¹ ∘ F φ` and composition is continuous on composable pairs
  have hcomp : ContinuousOn (fun p : Mor × Mor => X.comp p.1 p.2)
      {p | X.src p.1 = X.tgt p.2} :=
    continuousOn_comp_of_continuousOn continuous_fst.continuousOn continuous_snd.continuousOn
      fun _ hp => hp
  have hpair : Tendsto (fun φ => (X.inv (σ (X.tgt φ)), F φ)) 𝒱
      (𝓝[{p | X.src p.1 = X.tgt p.2}] (X.inv χ, ρ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨((X.continuous_inv.tendsto χ).comp hσt).prodMk_nhds hFt, ?_⟩
    filter_upwards [hM𝒱] with φ hφ
    rw [X.src_inv, htgtF φ hφ]
  have hlim := (hcomp (X.inv χ, ρ) (by
    change X.src (X.inv χ) = X.tgt ρ
    rw [X.src_inv, htρ])).tendsto.comp hpair
  have heq : ∀ φ ∈ M, X.comp (X.inv (σ (X.tgt φ))) (F φ) = φ := fun φ hφ => by
    have h1 := (hσ _ hφ).1
    change X.comp (X.inv (σ (X.tgt φ))) (X.comp (σ (X.tgt φ)) φ) = φ
    rw [← X.comp_assoc _ _ _ (by rw [X.src_inv]) h1, X.inv_comp, h1, X.unit_comp]
  refine ⟨X.comp (X.inv χ) ρ, ?_, ?_, ?_⟩
  · rw [X.src_comp _ _ (by rw [X.src_inv, htρ])]; exact hρ.2
  · rw [X.tgt_comp _ _ (by rw [X.src_inv, htρ]), X.tgt_inv]
  · have : Tendsto id (𝒱 : Filter Mor) (𝓝 (X.comp (X.inv χ) ρ)) := by
      refine hlim.congr' ?_
      filter_upwards [hM𝒱] with φ hφ
      exact heq φ hφ
    exact this

/-- **The converse**: if `cl_X U ⊆ Q` is proper in `X`, then `cl_Q U` is proper in the full
subcategory on `Q` (no openness of `Q` or `|Q| = |X|` needed). -/
theorem isProperSubsetIn_of_isProperSubset {Q U : Set Obj} (hUQ : U ⊆ Q)
    (hcl : closure U ⊆ Q) (hp : X.IsProperSubset (closure U)) :
    X.IsProperSubsetIn Q (closure ((↑) ⁻¹' U : Set Q)) := by
  rw [isProperSubsetIn_iff_ultrafilter hUQ]
  intro 𝒱 z hz hS hT
  obtain ⟨φ, hφ, htφ, hle⟩ :=
    (isProperSubset_iff_ultrafilter X (closure U)).1 hp 𝒱 z (mem_of_superset hS
      inter_subset_right) hT
  exact ⟨φ, ⟨⟨hcl hφ, htφ ▸ hz⟩, hφ⟩, htφ, hle⟩

/-! ### Good systems for `Q` and Theorem 13.1.7 as printed -/

/-- **A good system for the ep-groupoid `Q` is a partial good system on `Q`** (for open `Q`
with `|Q| = |X|`): `Q`-properness of `cl_Q U(q)` gives `X`-properness of `cl_X U(q)`. -/
theorem IsGoodIn.isGoodOn {N : ∀ x : Obj, X.NatNbhd x} {Q : Set Obj} (hQ : IsOpen Q)
    (hπQ : X.π '' Q = univ) (h : X.IsGoodIn N Q) : X.IsGoodOn N Q :=
  ⟨h.subset, fun q hq => isProperSubset_of_isProperSubsetIn hQ hπQ (h.subset q hq)
    (h.isProperSubsetIn_closure q hq), h.isDiffeoComponent⟩

/-- `IsGoodIn N Q` forces `cl_X U(q) ⊆ Q` for `q ∈ Q`. -/
theorem IsGoodIn.closure_subset {N : ∀ x : Obj, X.NatNbhd x} {Q : Set Obj} (hQ : IsOpen Q)
    (hπQ : X.π '' Q = univ) (h : X.IsGoodIn N Q) {q : Obj} (hq : q ∈ Q) :
    closure (N q).U ⊆ Q :=
  closure_subset_of_isProperSubsetIn hQ hπQ (h.subset q hq) (h.isProperSubsetIn_closure q hq)

/-- **Good systems for `Q` versus partial good systems on `Q`**: for open `Q` with
`|Q| = |X|`, `N` is a good system for the ep-groupoid `Q` iff it is a partial good system on
`Q` (properness read in `X`) whose closures `cl_X U(q)` stay in `Q`. -/
theorem isGoodIn_iff {N : ∀ x : Obj, X.NatNbhd x} {Q : Set Obj} (hQ : IsOpen Q)
    (hπQ : X.π '' Q = univ) :
    X.IsGoodIn N Q ↔ X.IsGoodOn N Q ∧ ∀ q ∈ Q, closure (N q).U ⊆ Q :=
  ⟨fun h => ⟨h.isGoodOn hQ hπQ, fun _ hq => h.closure_subset hQ hπQ hq⟩,
    fun ⟨h, hcl⟩ => ⟨h.subset, fun q hq => isProperSubsetIn_of_isProperSubset (h.subset q hq)
      (hcl q hq) (h.isProperSubset_closure q hq), h.isDiffeoComponent⟩⟩

/-- **Theorem 13.1.7 (extension of good partial systems, p. 602; 2017: Theorem 13.1), as
printed**: let `Q` be open with `|Q| = |X|` and `(U(q))_{q ∈ Q}` a good system for the
ep-groupoid `Q` (properness read in the full subcategory on `Q`).  Then for open
`W(y) ∋ y` there is a good system `𝒰` of `X` extending it, with `U(y) ⊆ W(y)` for `y ∉ Q`. -/
theorem theorem_13_1_7_book {Q : Set Obj} (hQ : IsOpen Q) (hπQ : X.π '' Q = univ)
    (N : ∀ x : Obj, X.NatNbhd x) (hN : X.IsGoodIn N Q) (W : Obj → Set Obj)
    (hW : ∀ y, IsOpen (W y)) (hyW : ∀ y, y ∈ W y) :
    ∃ 𝒰 : X.GoodSystem, (∀ q ∈ Q, 𝒰.nbhd q = N q) ∧ ∀ y ∉ Q, 𝒰.U y ⊆ W y :=
  X.theorem_13_1_7 hπQ N (hN.isGoodOn hQ hπQ) W hW hyW

/-- **Witness**: every good system of `X` is a good system for the ep-groupoid `Q = X`, so the
hypothesis of `theorem_13_1_7_book` is satisfiable (with `nonempty_goodSystem_trivial`). -/
theorem GoodSystem.isGoodIn_univ (𝒰 : X.GoodSystem) : X.IsGoodIn 𝒰.nbhd univ :=
  (isGoodIn_iff isOpen_univ (by
    rw [image_univ]; exact X.surjective_π.range_eq)).2
    ⟨𝒰.isGoodOn, fun _ _ => subset_univ _⟩

end EpGroupoid

end Polyfold
