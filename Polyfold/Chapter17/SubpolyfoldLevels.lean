import Polyfold.Chapter17.SubpolyfoldStructure
import Polyfold.Chapter5.SmoothLevelContinuity
import Polyfold.Chapter17.LevelStructures

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.3, p. 786: the vertical maps of the square relating `Ψ_A : G ⋉ A_Ψ → A` and `Ψ : G ⋉ O → C`
are topological embeddings, and the text adds that this holds level-wise.  Numbers and pages are
the 2021 text's.

# The level-wise statement of p. 786

## The text, paraphrased

(p. 786) For a sub-polyfold `A ⊆ C` and a uniformizer `Ψ : G ⋉ O → C` with `A_Ψ = Ψ⁻¹(A)` a
sub-M-polyfold of `O`, the left vertical map `|G ⋉ A_Ψ| → |G ⋉ O|` and the right vertical map
`|A| → |C|` are topological embeddings, and this is also the case level-wise.

## What is formalized

* `MPolyfold.mem_subPolyfold_levelSet_iff`: for a sub-M-polyfold `A ⊆ X` with its induced
  structure (Proposition 2.3.19, 2021 p. 64), `A_m = A ∩ X_m`.
* `MPolyfold.subLevelIncl hA m : A_m → X_m` and **`MPolyfold.isEmbedding_subLevelIncl`**: the
  inclusion `A_m → X_m` is a topological embedding for the level topologies, with range
  `{x ∈ X_m | x ∈ A}` (`range_subLevelIncl`).  Continuity comes from the sc-smoothness of the
  inclusion; the inverse near a point is `i⁻¹ ∘ r` for a retraction `r` onto `A`
  (Proposition 2.3.19 (2)), continuous on level `m`.
* `MPolyfold.levelMulAction hG m`: a group acting by sc-smooth maps acts on every level `X_m`,
  by homeomorphisms (`continuous_levelSmul`); `subSmul_isScSmooth` (for `A` invariant, `G` acts on
  `A` by sc-smooth maps); `subLevelIncl_smul` (the inclusion `A_m → X_m` is equivariant).
* `GroupoidStr.translationMapFunctor j hj` and **`GroupoidStr.isEmbedding_orbitMap_translationMap`**:
  for an equivariant topological embedding `j : B → O` (`G` acting on `O` by homeomorphisms),
  `|G ⋉ B| → |G ⋉ O|` is a topological embedding.
* **`MPolyfold.isEmbedding_orbitMap_levelSub`** and, for the restricted uniformizer `Ψ_A` of
  `SubpolyfoldStructure.lean`, **`GCT.LocalUniformizer.isEmbedding_orbitMap_restrict_level`**:
  for every level `m`, `|G ⋉ (A_Ψ)_m| → |G ⋉ O_m|` is a topological embedding.
* Witness: `isEmbedding_orbitMap_levelSub_univ` (the case `A = X`, which needs no hypothesis
  beyond a group action by sc-smooth maps).  The hypotheses of `isEmbedding_orbitMap_levelSub`
  are those of the text: a sub-M-polyfold, invariant under a group acting by sc-smooth maps.
* The right vertical map on levels.  `isEmbedding_of_forall_local` and `local_of_charts` (a local
  criterion for topological embeddings through pairs of charts); `hasUniformizers_subConstruction`,
  `hasRegularity_sub_iff` (an object of `A` has the same regularity in `A`, for the structure
  `(F_A, M)` of Proposition 17.3.6, and in `C`); `subRegOrbitMap hu hS m : |A_m| → |C_m|`,
  `injective_subRegOrbitMap`; `levelFunctor Ψ m : G ⋉ O_m → C_m`.
  **`isEmbedding_subRegOrbitMap_of_charts`**: for topologies on `|A_m|` and `|C_m|` for which the
  maps `|Ψ_m|` (`Ψ ∈ F(α)`, `α ∈ C_m`) and `|L_m|` (`L ∈ F_A(α)`, `α ∈ A_m`) are open
  embeddings, `|A_m| → |C_m|` is a topological embedding.
  **`isEmbedding_subRegOrbitMap_one`**: for `m = 1`, with the topologies of Theorem 17.1.28
  (2021 p. 766) for `C` and for `A`, `|A_1| → |C_1|` is a topological embedding.  Witness:
  `reflection_isEmbedding_subRegOrbitMap_one` (`A = {0}` in `ℤ/2 ⋉ ℝ`, `|A_1|` non-empty).
* The charts of `|C_m|` for every `m`.  `MPolyfold.levelZeroHomeomorph` (`X ≅ X_0`),
  `GroupoidStr.translationHomeomorph` (`|G ⋉ U| ≅ |H ⋉ V|` for an equivariant homeomorphism along
  a group isomorphism), `UniformizedPolyfold.LevelLift` and `levelLift` (for `Ψ ∈ F(α)` and
  `α ∈ C_m`, a uniformizer `L` of the iterated GCT `C^m = (C^{m-1})¹` over `α`, built by induction
  on `m` from the lift of Theorem 17.1.28, with `(O_L)_j ≅ O_{j+m}` for every `j`).
  **`UniformizedPolyfold.isOpenEmbedding_levelFunctor`**: for `α ∈ C_m` and `Ψ ∈ F(α)`,
  `|Ψ_m| : |G ⋉ O_m| → |C_m|` is an open embedding for `levelTopology m`.
* **`isEmbedding_subRegOrbitMap`**: for every `m`, with the topologies `levelTopology m` of
  2021 p. 766 for `C` (structure `(F, M)`) and for `A` (structure `(F_A, M)`), `|A_m| → |C_m|` is
  a topological embedding.  Witness: `reflection_isEmbedding_subRegOrbitMap` (`A = {0}` in
  `ℤ/2 ⋉ ℝ`, every `m`, `|A_m|` non-empty).

## Readings

* "Level-wise" is read for the left vertical map: `(A_Ψ)_m` is the level `m` of the induced
  M-polyfold structure on `A_Ψ` (the levels of `subPolyfold`), with the level topology of
  Definition 2.3.8 (2021 p. 60), and `O_m` likewise.
* For the right vertical map, `|C_m|` and `|A_m|` carry the topologies of 2021 p. 766: for
  `m = 1` that of Theorem 17.1.28, and for every `m` the topology transported from the iterated
  GCT `C^m = (C^{m-1})¹` (`UniformizedPolyfold.levelTopology`), for `A` with the polyfold
  structure `(F_A, M)`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

universe u

namespace Polyfold

/-! ### `|G ⋉ B| → |G ⋉ O|` for an equivariant embedding -/

namespace GroupoidStr

variable {G B O : Type u} [Group G] [TopologicalSpace B] [TopologicalSpace O] [MulAction G B]
  [MulAction G O]

/-- The functor `G ⋉ B → G ⋉ O` of an equivariant map `j : B → O`. -/
def translationMapFunctor (j : B → O) (hj : ∀ (g : G) (b : B), j (g • b) = g • j b) :
    GroupoidFunctor (GroupoidStr.translation G B) (GroupoidStr.translation G O) where
  obj := j
  mor p := (p.1, j p.2)
  src_mor _ := rfl
  tgt_mor p := (hj p.1 p.2).symm
  mor_comp _ _ _ := rfl
  mor_unit _ := rfl

/-- **`|G ⋉ B| → |G ⋉ O|` is a topological embedding** for an equivariant topological embedding
`j : B → O`, `G` acting on `O` by homeomorphisms.  As in `isEmbedding_orbitMap_translationSub`:
for `W` open in `|G ⋉ B|`, `π_B⁻¹(W) = j⁻¹(W₀)` with `W₀` open in `O`, and `W` is the preimage of
the open set `π(W₀)`, since the range of `j` is invariant. -/
theorem isEmbedding_orbitMap_translationMap (hc : ∀ g : G, Continuous fun y : O => g • y)
    {j : B → O} (hj : ∀ (g : G) (b : B), j (g • b) = g • j b) (he : IsEmbedding j) :
    IsEmbedding (translationMapFunctor j hj).orbitMap := by
  set J := (translationMapFunctor j hj).orbitMap with hJ
  have hcont : Continuous J := by
    refine continuous_quot_lift _ ?_
    exact continuous_quot_mk.comp he.continuous
  have hinj : Injective J := by
    intro z w h
    induction z using Quotient.inductionOn with
    | h x =>
    induction w using Quotient.inductionOn with
    | h y =>
      obtain ⟨φ, hs, ht⟩ := ((GroupoidStr.translation G O).π_eq_π_iff).1 h
      change φ.2 = j x at hs
      change φ.1 • φ.2 = j y at ht
      refine ((GroupoidStr.translation G B).π_eq_π_iff).2 ⟨(φ.1, x), rfl, he.injective ?_⟩
      change j (φ.1 • x) = j y
      rw [hj, ← hs, ht]
  refine ⟨⟨?_⟩, hinj⟩
  apply le_antisymm
  · intro W hW
    rw [isOpen_induced_iff] at hW
    obtain ⟨W', hW', rfl⟩ := hW
    exact hW'.preimage hcont
  · intro W hW
    have hW₁ : IsOpen ((GroupoidStr.translation G B).π ⁻¹' W) := hW
    rw [he.isInducing.isOpen_iff] at hW₁
    obtain ⟨W₀, hW₀, hW₀eq⟩ := hW₁
    refine isOpen_induced_iff.2 ⟨(GroupoidStr.translation G O).π '' W₀,
      GroupoidStr.isOpenMap_π_translation hc W₀ hW₀, ?_⟩
    ext z
    induction z using Quotient.inductionOn with
    | h b =>
    simp only [mem_preimage]
    change (GroupoidStr.translation G O).π (j b) ∈ (GroupoidStr.translation G O).π '' W₀ ↔
      (GroupoidStr.translation G B).π b ∈ W
    constructor
    · rintro ⟨o, ho, hob⟩
      obtain ⟨φ, hs, ht⟩ := ((GroupoidStr.translation G O).π_eq_π_iff).1 hob
      change φ.2 = o at hs
      change φ.1 • φ.2 = j b at ht
      have hjo : j (φ.1⁻¹ • b) = o := by
        rw [hj, ← ht, inv_smul_smul, hs]
      have hmem : φ.1⁻¹ • b ∈ (GroupoidStr.translation G B).π ⁻¹' W := by
        rw [← hW₀eq, mem_preimage, hjo]; exact ho
      have heq : (GroupoidStr.translation G B).π (φ.1⁻¹ • b) =
          (GroupoidStr.translation G B).π b :=
        ((GroupoidStr.translation G B).π_eq_π_iff).2 ⟨(φ.1, φ.1⁻¹ • b), rfl, by
          change φ.1 • φ.1⁻¹ • b = b
          rw [smul_inv_smul]⟩
      rw [← heq]
      exact hmem
    · intro hb
      have : b ∈ (GroupoidStr.translation G B).π ⁻¹' W := hb
      rw [← hW₀eq] at this
      exact ⟨j b, this, rfl⟩

end GroupoidStr

/-! ### The levels of a sub-M-polyfold -/

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {A : Set X} (hA : P.IsSubMPolyfold A) [ParacompactSpace A]

/-- **`A_m = A ∩ X_m`** for the induced M-polyfold structure on a sub-M-polyfold (Proposition
2.3.19, 2021 p. 64): a chart of `A` is a chart of `X` restricted to `W ∩ A`, with the same
sc-Banach space. -/
theorem mem_subPolyfold_levelSet_iff (a : A) (m : ℕ) :
    a ∈ (subPolyfold hA).levelSet m ↔ a.1 ∈ P.levelSet m := by
  obtain ⟨φ, hφ, haφ⟩ := P.exists_isChart_mem_source a.1
  set d := hA.data a.2
  have hsrc : a ∈ (subChart d hφ a).source :=
    d.mem_shrink φ a.2 (hA.mem_data_V a.2) haφ
  rw [(subPolyfold hA).mem_levelSet_iff (subPolyfold_isChart hA d hφ a) hsrc,
    P.mem_levelSet_iff hφ haφ]
  rfl

/-- The inclusion `A_m → X_m`. -/
def subLevelIncl (m : ℕ) (a : (subPolyfold hA).Level m) : P.Level m :=
  P.levelMk m ((subPolyfold hA).levelVal m a).1
    ((mem_subPolyfold_levelSet_iff hA _ m).1 (levelVal_mem a))

@[simp] theorem levelVal_subLevelIncl (m : ℕ) (a : (subPolyfold hA).Level m) :
    P.levelVal m (subLevelIncl hA m a) = ((subPolyfold hA).levelVal m a).1 := rfl

theorem continuous_subLevelIncl (m : ℕ) : Continuous (subLevelIncl hA m) :=
  continuousOn_univ.1 (IsScSmoothOn.continuousOn_level_comp (subPolyfold_inclusion_isScSmooth hA)
    (u := id) continuousOn_id (fun _ _ => mem_univ _) fun _ _ => rfl)

theorem injective_subLevelIncl (m : ℕ) : Injective (subLevelIncl hA m) := fun _ _ h =>
  level_ext (Subtype.ext (congrArg (P.levelVal m) h))

/-- **The inclusion `A_m → X_m` is a topological embedding.**  Near `a`, with a retraction `r`
onto `A` on `V ∋ a` (Definition 2.3.18, 2021 p. 63), the map `i⁻¹ ∘ r` is sc-smooth
(Proposition 2.3.19 (2)), hence continuous `V_m → A_m`, and it is a left inverse of the
inclusion on `A ∩ V`. -/
theorem isEmbedding_subLevelIncl (m : ℕ) : IsEmbedding (subLevelIncl hA m) := by
  refine ⟨isInducing_iff_nhds.2 fun a => le_antisymm
    ((continuous_subLevelIncl hA m).tendsto a).le_comap ?_, injective_subLevelIncl hA m⟩
  intro N hN
  set a₀ : A := (subPolyfold hA).levelVal m a
  set d := hA.data a₀.2
  set s : Set (P.Level m) := {x | P.levelVal m x ∈ d.V}
  have hs : IsOpen s := d.isOpen.preimage (continuous_levelVal m)
  have hsm := subPolyfold_retraction_isScSmooth hA d a₀
  have hlev : ∀ x : P.Level m, P.levelVal m x ∈ d.V →
      d.retractInto a₀ (P.levelVal m x) ∈ (subPolyfold hA).levelSet m := fun x hx =>
    hsm.mapsTo_levelSet m ⟨hx, levelVal_mem x⟩
  classical
  let v : P.Level m → (subPolyfold hA).Level m := fun x =>
    if hx : P.levelVal m x ∈ d.V then
      (subPolyfold hA).levelMk m (d.retractInto a₀ (P.levelVal m x)) (hlev x hx)
    else a
  have hv : ContinuousOn v s :=
    IsScSmoothOn.continuousOn_level_comp hsm (u := id) continuousOn_id (fun _ hz => hz)
      fun z hz => by
        simp only [v, dif_pos (show P.levelVal m z ∈ d.V from hz)]
        rfl
  have hvb : ∀ b : (subPolyfold hA).Level m, subLevelIncl hA m b ∈ s →
      v (subLevelIncl hA m b) = b := by
    intro b hb
    simp only [v, dif_pos (show P.levelVal m (subLevelIncl hA m b) ∈ d.V from hb)]
    refine level_ext (Subtype.ext ?_)
    change (d.retractInto a₀ ((subPolyfold hA).levelVal m b).1).1 = ((subPolyfold hA).levelVal m b).1
    rw [d.retractInto_val a₀ (show ((subPolyfold hA).levelVal m b).1 ∈ d.V from hb)]
    exact d.apply_eq_self ⟨((subPolyfold hA).levelVal m b).2, hb⟩
  have has : subLevelIncl hA m a ∈ s := hA.mem_data_V a₀.2
  have hva := hvb a has
  have hcont : ContinuousAt v (subLevelIncl hA m a) := hv.continuousAt (hs.mem_nhds has)
  have hN' : v ⁻¹' N ∈ 𝓝 (subLevelIncl hA m a) := hcont (by rw [hva]; exact hN)
  refine mem_comap.2 ⟨v ⁻¹' N ∩ s, inter_mem hN' (hs.mem_nhds has), fun b hb => ?_⟩
  have := hb.1
  rwa [mem_preimage, hvb b hb.2] at this

/-- The range of `A_m → X_m` is `{x ∈ X_m | x ∈ A}`. -/
theorem range_subLevelIncl (m : ℕ) :
    range (subLevelIncl hA m) = {x : P.Level m | P.levelVal m x ∈ A} := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ((subPolyfold hA).levelVal m a).2
  · intro hx
    refine ⟨(subPolyfold hA).levelMk m ⟨P.levelVal m x, hx⟩
      ((mem_subPolyfold_levelSet_iff hA _ m).2 (levelVal_mem x)), level_ext rfl⟩

/-! ### Group actions on the levels -/

section Action

variable {G : Type u} [Group G] [MulAction G X]

omit [ParacompactSpace A] in
variable (P) in
/-- **The action of `G` on `X_m`**, for `G` acting by sc-smooth maps (sc-smooth maps preserve
the levels). -/
abbrev levelMulAction (hG : ∀ g : G, P.IsScSmoothMap P fun x => g • x) (m : ℕ) :
    MulAction G (P.Level m) where
  smul g x := P.levelMk m (g • P.levelVal m x) ((hG g).mapsTo_levelSet m (levelVal_mem x))
  one_smul x := level_ext (one_smul G (P.levelVal m x))
  mul_smul g h x := level_ext (mul_smul g h (P.levelVal m x))

omit [ParacompactSpace A] in
theorem levelVal_levelSmul (hG : ∀ g : G, P.IsScSmoothMap P fun x => g • x) (m : ℕ) (g : G)
    (x : P.Level m) :
    letI := P.levelMulAction hG m
    P.levelVal m (g • x) = g • P.levelVal m x := rfl

omit [ParacompactSpace A] in
/-- `G` acts on `X_m` by homeomorphisms. -/
theorem continuous_levelSmul (hG : ∀ g : G, P.IsScSmoothMap P fun x => g • x) (m : ℕ) (g : G) :
    letI := P.levelMulAction hG m
    Continuous fun x : P.Level m => g • x := by
  let _ := P.levelMulAction hG m
  exact continuousOn_univ.1 (IsScSmoothOn.continuousOn_level_comp (hG g) (u := id)
    continuousOn_id (fun _ _ => mem_univ _) fun _ _ => rfl)

variable (hAinv : ∀ (g : G) (x : X), x ∈ A → g • x ∈ A)

/-- `G` acts on the sub-M-polyfold `A` by sc-smooth maps (Proposition 2.3.19, 2021 p. 64: a map
into `A` is sc-smooth as soon as it is sc-smooth into `X`). -/
theorem subSmul_isScSmooth (hG : ∀ g : G, P.IsScSmoothMap P fun x => g • x) :
    letI := GroupoidStr.subMulAction hAinv
    ∀ g : G, (subPolyfold hA).IsScSmoothMap (subPolyfold hA) fun x => g • x := by
  let _ := GroupoidStr.subMulAction hAinv
  exact fun g => isScSmoothOn_subPolyfold_of_val hA
    ((hG g).comp (subPolyfold_inclusion_isScSmooth hA))

/-- **The inclusion `A_m → X_m` is equivariant**, for `G` acting on `A` by restriction. -/
theorem subLevelIncl_smul (hG : ∀ g : G, P.IsScSmoothMap P fun x => g • x) (m : ℕ) (g : G)
    (b : (subPolyfold hA).Level m) :
    letI := GroupoidStr.subMulAction hAinv
    letI := (subPolyfold hA).levelMulAction (subSmul_isScSmooth hA hAinv hG) m
    letI := P.levelMulAction hG m
    subLevelIncl hA m (g • b) = g • subLevelIncl hA m b :=
  level_ext rfl

/-- **The level-wise statement of p. 786, for the left vertical map**: for a `G`-invariant
sub-M-polyfold `A ⊆ X` (`G` acting by sc-smooth maps), and every level `m`,
the map `|G ⋉ A_m| → |G ⋉ X_m|` is a topological embedding. -/
theorem isEmbedding_orbitMap_levelSub (hG : ∀ g : G, P.IsScSmoothMap P fun x => g • x)
    (m : ℕ) :
    letI := GroupoidStr.subMulAction hAinv
    letI := (subPolyfold hA).levelMulAction (subSmul_isScSmooth hA hAinv hG) m
    letI := P.levelMulAction hG m
    IsEmbedding (GroupoidStr.translationMapFunctor (subLevelIncl hA m)
      (subLevelIncl_smul hA hAinv hG m)).orbitMap := by
  let _ := GroupoidStr.subMulAction hAinv
  let _ := (subPolyfold hA).levelMulAction (subSmul_isScSmooth hA hAinv hG) m
  let _ := P.levelMulAction hG m
  exact GroupoidStr.isEmbedding_orbitMap_translationMap (continuous_levelSmul hG m)
    (subLevelIncl_smul hA hAinv hG m) (isEmbedding_subLevelIncl hA m)

end Action

end MPolyfold

/-! ### The restricted uniformizer `Ψ_A` on the levels -/

namespace GCT.LocalUniformizer

variable {C : GCT.{u}} {A : Set C.Obj} (hA : C.toGroupoidStr.IsSaturated A)
  {Ψ : C.LocalUniformizer}

/-- **The level-wise statement of p. 786** (2021 §17.3): for a uniformizer `Ψ : G ⋉ O → C` with
`A_Ψ = Ψ⁻¹(A)` a sub-M-polyfold of `O`, and every level `m`, the left vertical map
`|G ⋉ (A_Ψ)_m| → |G ⋉ O_m|` is a topological embedding.  Here `(A_Ψ)_m` is the level `m` of the
M-polyfold of the restricted uniformizer `Ψ_A` (`restrict`), with the action of `G`. -/
theorem isEmbedding_orbitMap_restrict_level (hΨ : Ψ.P.IsSubMPolyfold (Ψ.obj ⁻¹' A)) (m : ℕ) :
    haveI : ParacompactSpace (Ψ.obj ⁻¹' A) := Ψ.P.paracompactSpace_subtype _
    letI := Ψ.restrictMulAction hA
    letI := (MPolyfold.subPolyfold hΨ).levelMulAction
      (MPolyfold.subSmul_isScSmooth hΨ (Ψ.smul_mem_preimage hA) Ψ.smooth_smul) m
    letI := Ψ.P.levelMulAction Ψ.smooth_smul m
    IsEmbedding (GroupoidStr.translationMapFunctor (MPolyfold.subLevelIncl hΨ m)
      (MPolyfold.subLevelIncl_smul hΨ (Ψ.smul_mem_preimage hA) Ψ.smooth_smul m)).orbitMap :=
  haveI : ParacompactSpace (Ψ.obj ⁻¹' A) := Ψ.P.paracompactSpace_subtype _
  MPolyfold.isEmbedding_orbitMap_levelSub hΨ (Ψ.smul_mem_preimage hA) Ψ.smooth_smul m

/-- The M-polyfold and the action of `Ψ_A` are those used in
`isEmbedding_orbitMap_restrict_level`. -/
theorem restrict_P (hΨ : Ψ.P.IsSubMPolyfold (Ψ.obj ⁻¹' A)) :
    haveI : ParacompactSpace (Ψ.obj ⁻¹' A) := Ψ.P.paracompactSpace_subtype _
    HEq (Ψ.restrict hA hΨ).P (MPolyfold.subPolyfold hΨ) :=
  HEq.rfl

end GCT.LocalUniformizer

/-! ### A local criterion for topological embeddings -/

section EmbeddingCriterion

variable {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z] {e : X → Z}

/-- **A local criterion for an embedding**: `e` is injective, and every point has an open
neighbourhood `U` on which `e` is continuous and induces the topology, in the form: `e⁻¹(W') ∩ U`
is open for `W'` open, and every `W ∩ U` (`W` open) is `e⁻¹(W')` for an open `W'`. -/
theorem isEmbedding_of_forall_local (he : Injective e)
    (h : ∀ x, ∃ U : Set X, x ∈ U ∧ (∀ W' : Set Z, IsOpen W' → IsOpen (e ⁻¹' W' ∩ U)) ∧
      ∀ W : Set X, IsOpen W → ∃ W' : Set Z, IsOpen W' ∧ e ⁻¹' W' = W ∩ U) :
    IsEmbedding e := by
  choose U hxU hcont hind using h
  have hc : Continuous e := by
    rw [continuous_def]
    intro W' hW'
    have : e ⁻¹' W' = ⋃ x, (e ⁻¹' W' ∩ U x) := by
      ext y
      simp only [mem_iUnion, mem_inter_iff]
      exact ⟨fun hy => ⟨y, hy, hxU y⟩, fun ⟨_, hy, _⟩ => hy⟩
    rw [this]
    exact isOpen_iUnion fun x => hcont x W' hW'
  refine ⟨⟨?_⟩, he⟩
  apply le_antisymm
  · intro W hW
    rw [isOpen_induced_iff] at hW
    obtain ⟨W', hW', rfl⟩ := hW
    exact hW'.preimage hc
  · intro W hW
    rw [isOpen_induced_iff]
    choose W' hW' hW'eq using fun x => hind x W hW
    refine ⟨⋃ x, W' x, isOpen_iUnion hW', ?_⟩
    ext y
    simp only [mem_preimage, mem_iUnion]
    constructor
    · rintro ⟨x, hx⟩
      have : y ∈ e ⁻¹' W' x := hx
      rw [hW'eq] at this
      exact this.1
    · intro hy
      refine ⟨y, ?_⟩
      have : y ∈ W ∩ U y := ⟨hy, hxU y⟩
      rw [← hW'eq] at this
      exact this

/-- **The local data of `isEmbedding_of_forall_local` from a pair of charts**: for open
embeddings `f : Y → X`, `g : Y' → Z` and an embedding `J : Y → Y'` with `e ∘ f = g ∘ J`, such that
a point of `range g` in `range e` comes from `range J`, the open set `U = range f` has the
properties asked for. -/
theorem local_of_charts {Y Y' : Type*} [TopologicalSpace Y] [TopologicalSpace Y']
    (he : Injective e) {f : Y → X} (hf : IsOpenEmbedding f) {g : Y' → Z} (hg : IsOpenEmbedding g)
    {J : Y → Y'} (hJ : IsEmbedding J) (hcomm : ∀ y, e (f y) = g (J y))
    (hrange : ∀ y', g y' ∈ range e → y' ∈ range J) :
    (∀ W' : Set Z, IsOpen W' → IsOpen (e ⁻¹' W' ∩ range f)) ∧
      ∀ W : Set X, IsOpen W → ∃ W' : Set Z, IsOpen W' ∧ e ⁻¹' W' = W ∩ range f := by
  constructor
  · intro W' hW'
    have : e ⁻¹' W' ∩ range f = f '' (J ⁻¹' (g ⁻¹' W')) := by
      ext x
      constructor
      · rintro ⟨hx, y, rfl⟩
        refine ⟨y, ?_, rfl⟩
        change g (J y) ∈ W'
        rw [← hcomm]; exact hx
      · rintro ⟨y, hy, rfl⟩
        refine ⟨?_, y, rfl⟩
        change e (f y) ∈ W'
        rw [hcomm]; exact hy
    rw [this]
    exact hf.isOpenMap _ ((hW'.preimage hg.continuous).preimage hJ.continuous)
  · intro W hW
    obtain ⟨T', hT', hT'eq⟩ := hJ.isInducing.isOpen_iff.1 (hW.preimage hf.continuous)
    refine ⟨g '' T', hg.isOpenMap _ hT', ?_⟩
    ext x
    constructor
    · rintro ⟨y', hy', hxe⟩
      obtain ⟨y, rfl⟩ := hrange y' ⟨x, hxe.symm⟩
      have hx : f y = x := he (by rw [hcomm, hxe])
      have : y ∈ J ⁻¹' T' := hy'
      rw [hT'eq] at this
      exact ⟨hx ▸ this, y, hx⟩
    · rintro ⟨hx, y, rfl⟩
      refine ⟨J y, ?_, (hcomm y).symm⟩
      have : y ∈ f ⁻¹' W := hx
      rw [← hT'eq] at this
      exact this

end EmbeddingCriterion

/-! ### The right vertical map on level `1`: `|A_1| → |C_1|` -/

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} {S : C.PolyfoldConstruction} {A : Set C.Obj}

/-- `F_A(α) ≠ ∅` for all `α` when `F(α) ≠ ∅` for all `α`. -/
theorem hasUniformizers_subConstruction (hu : S.HasUniformizers) (hS : S.IsSubpolyfold A) :
    (subConstruction hS).HasUniformizers := fun α => by
  obtain ⟨Ψ, hΨ⟩ := hu (show A from α).1
  exact ⟨_, (mem_subF_iff hS α _).2 ⟨Ψ, hΨ, rfl⟩⟩

/-- **The regularity of `α ∈ A` is the same in `A` and in `C`** (p. 765 for the polyfold
structure `(F_A, M)` of Proposition 17.3.6): the levels of `A_Ψ` are `A_Ψ ∩ O_m`. -/
theorem hasRegularity_sub_iff (hu : S.HasUniformizers) (hS : S.IsSubpolyfold A) (m : ℕ)
    (a : (C.sub A).Obj) :
    (subConstruction hS).HasRegularity m a ↔ S.HasRegularity m (show A from a).1 := by
  constructor
  · rintro ⟨⟨L, α, Ψ, hΨ, p, rfl⟩, q, hiso, hq⟩
    exact ⟨⟨Ψ, _, hΨ⟩, q.1, GroupoidStr.isomorphic_fullSub_iff.1 hiso,
      (MPolyfold.mem_subPolyfold_levelSet_iff p q m).1 hq⟩
  · intro h
    obtain ⟨Ψ, hΨ⟩ := hu (show A from a).1
    obtain ⟨q, hq⟩ := S.isAt _ Ψ hΨ
    have hq' : Ψ.obj q = (show A from a).1 := hq
    have hqA : q ∈ Ψ.obj ⁻¹' A := by
      change Ψ.obj q ∈ A
      rw [hq']; exact (show A from a).2
    have hm := (regularity_eq_of_mem hΨ hq' m).1 h
    refine ⟨⟨LocalUniformizer.restrict hS.1 (hS.2 _ (show A from a).2 Ψ hΨ), a, Ψ, hΨ, _, rfl⟩,
      ⟨q, hqA⟩, ?_, (MPolyfold.mem_subPolyfold_levelSet_iff _ ⟨q, hqA⟩ m).2 hm⟩
    have he : (⟨Ψ.obj q, hqA⟩ : A) = a := Subtype.ext hq'
    change (C.toGroupoidStr.fullSub A).Isomorphic ⟨Ψ.obj q, hqA⟩ a
    rw [he]
    exact GroupoidStr.isomorphic_refl _ _

/-- The inclusion `A_m → C_m` on objects. -/
def subRegIncl (hu : S.HasUniformizers) (hS : S.IsSubpolyfold A) (m : ℕ)
    (a : (subConstruction hS).regSet m) : S.regSet m :=
  ⟨(show A from a.1).1, (hasRegularity_sub_iff hu hS m a.1).1 a.2⟩

/-- **The right vertical map on level `m`**, `|A_m| → |C_m|`. -/
def subRegOrbitMap (hu : S.HasUniformizers) (hS : S.IsSubpolyfold A) (m : ℕ) :
    ((subConstruction hS).regSub m).OrbitSpace → (S.regSub m).OrbitSpace :=
  Quotient.map (subRegIncl hu hS m) fun x y h =>
    have h₁ : (C.toGroupoidStr.fullSub A).Isomorphic x.1 y.1 :=
      GroupoidStr.isomorphic_fullSub_iff.1 h
    have h₂ : C.toGroupoidStr.Isomorphic x.1.1 y.1.1 := GroupoidStr.isomorphic_fullSub_iff.1 h₁
    GroupoidStr.isomorphic_fullSub_iff.2 h₂

theorem subRegOrbitMap_π (hu : S.HasUniformizers) (hS : S.IsSubpolyfold A) (m : ℕ)
    (a : (subConstruction hS).regSet m) :
    subRegOrbitMap hu hS m (((subConstruction hS).regSub m).π a) =
      (S.regSub m).π (subRegIncl hu hS m a) := rfl

/-- `|A_m| → |C_m|` is injective. -/
theorem injective_subRegOrbitMap (hu : S.HasUniformizers) (hS : S.IsSubpolyfold A) (m : ℕ) :
    Injective (subRegOrbitMap hu hS m) := by
  intro z w h
  induction z using Quotient.inductionOn with | h x => ?_
  induction w using Quotient.inductionOn with | h y => ?_
  change (S.regSub m).π (subRegIncl hu hS m x) = (S.regSub m).π (subRegIncl hu hS m y) at h
  have h' := GroupoidStr.isomorphic_fullSub_iff.1 (((S.regSub m).π_eq_π_iff).1 h)
  exact (((subConstruction hS).regSub m).π_eq_π_iff).2
    (GroupoidStr.isomorphic_fullSub_iff.2 (GroupoidStr.isomorphic_fullSub_iff.2 h'))

variable (S) in
/-- A point of `O_m` has regularity `m`. -/
theorem mem_regSet_levelObj (Ψ : S.Unif) (m : ℕ) (x : Ψ.1.P.Level m) :
    Ψ.1.obj (Ψ.1.P.levelVal m x) ∈ S.regSet m :=
  (hasRegularity_iff Ψ (GroupoidStr.isomorphic_refl _ _) m).2 (MPolyfold.levelVal_mem x)

variable (S) in
/-- **The functor `Ψ_m : G ⋉ O_m → C_m`**: `Ψ` on the points of level `m` (for `m = 1` the
functor `Ψ¹` of Theorem 17.1.28, `levelFunctor_one`). -/
def levelFunctor (Ψ : S.Unif) (m : ℕ) :
    letI := Ψ.1.P.levelMulAction Ψ.1.smooth_smul m
    GroupoidFunctor (GroupoidStr.translation Ψ.1.G (Ψ.1.P.Level m)) (S.regSub m) :=
  letI := Ψ.1.P.levelMulAction Ψ.1.smooth_smul m
  { obj := fun x => ⟨Ψ.1.obj (Ψ.1.P.levelVal m x), S.mem_regSet_levelObj Ψ m x⟩
    mor := fun p => ⟨Ψ.1.toUniformizer.mor (p.1, Ψ.1.P.levelVal m p.2), by
      rw [Ψ.1.toUniformizer.src_mor]; exact S.mem_regSet_levelObj Ψ m p.2, by
      rw [Ψ.1.toUniformizer.tgt_mor]; exact S.mem_regSet_levelObj Ψ m (p.1 • p.2)⟩
    src_mor := fun p => Subtype.ext (Ψ.1.toUniformizer.src_mor (p.1, Ψ.1.P.levelVal m p.2))
    tgt_mor := fun p => Subtype.ext (Ψ.1.toUniformizer.tgt_mor (p.1, Ψ.1.P.levelVal m p.2))
    mor_comp := fun p p' h => by
      refine Subtype.ext ?_
      have h' : (GroupoidStr.translation Ψ.1.G Ψ.1.O).src (p.1, Ψ.1.P.levelVal m p.2) =
          (GroupoidStr.translation Ψ.1.G Ψ.1.O).tgt (p'.1, Ψ.1.P.levelVal m p'.2) :=
        congrArg (Ψ.1.P.levelVal m) h
      rw [C.toGroupoidStr.fullSub_comp_coe _ _ _ (by
        change C.toGroupoidStr.src (Ψ.1.toUniformizer.mor (p.1, Ψ.1.P.levelVal m p.2)) =
          C.toGroupoidStr.tgt (Ψ.1.toUniformizer.mor (p'.1, Ψ.1.P.levelVal m p'.2))
        rw [Ψ.1.toUniformizer.src_mor, Ψ.1.toUniformizer.tgt_mor]
        exact congrArg Ψ.1.obj h')]
      exact Ψ.1.functor.mor_comp (p.1, Ψ.1.P.levelVal m p.2) (p'.1, Ψ.1.P.levelVal m p'.2) h'
    mor_unit := fun x => Subtype.ext (Ψ.1.functor.mor_unit (Ψ.1.P.levelVal m x)) }

/-- **The reduction of the level-wise statement of p. 786 (right vertical map) to charts**: let
`|A_m|` and `|C_m|` carry topologies for which the maps `|Ψ_m| : |G ⋉ O_m| → |C_m|`
(`Ψ ∈ F(α)`, `α ∈ C_m`) and `|L_m| : |G ⋉ (O_L)_m| → |A_m|` (`L ∈ F_A(α)`, `α ∈ A_m`) are open
embeddings.  Then `|A_m| → |C_m|` is a topological embedding.  Near `|α|`, `α ∈ A_m`, with
`Ψ ∈ F(α)` and `L = Ψ_A`, the square `|A_m| → |C_m|` over
`|G ⋉ (A_Ψ)_m| → |G ⋉ O_m|` commutes and the left vertical map is an embedding
(`MPolyfold.isEmbedding_orbitMap_levelSub`). -/
theorem isEmbedding_subRegOrbitMap_of_charts (hu : S.HasUniformizers) (hS : S.IsSubpolyfold A)
    (m : ℕ) [TopologicalSpace ((subConstruction hS).regSub m).OrbitSpace]
    [TopologicalSpace (S.regSub m).OrbitSpace]
    (hC : ∀ (α : C.Obj) (Ψ : C.LocalUniformizer) (hΨ : Ψ ∈ S.F α), α ∈ S.regSet m →
      letI := Ψ.P.levelMulAction Ψ.smooth_smul m
      IsOpenEmbedding (S.levelFunctor ⟨Ψ, α, hΨ⟩ m).orbitMap)
    (hA : ∀ (α : (C.sub A).Obj) (L : (C.sub A).LocalUniformizer)
      (hL : L ∈ (subConstruction hS).F α), α ∈ (subConstruction hS).regSet m →
      letI := L.P.levelMulAction L.smooth_smul m
      IsOpenEmbedding ((subConstruction hS).levelFunctor ⟨L, α, hL⟩ m).orbitMap) :
    IsEmbedding (subRegOrbitMap hu hS m) := by
  refine isEmbedding_of_forall_local (injective_subRegOrbitMap hu hS m) fun z => ?_
  induction z using Quotient.inductionOn with | h a => ?_
  obtain ⟨Ψ, hΨ⟩ := hu (show A from a.1).1
  obtain ⟨q, hq⟩ := S.isAt _ Ψ hΨ
  have hq' : Ψ.obj q = (show A from a.1).1 := hq
  set p := hS.2 _ (show A from a.1).2 Ψ hΨ
  let ΨU : S.Unif := ⟨Ψ, _, hΨ⟩
  have hL : LocalUniformizer.restrict hS.1 p ∈ (subConstruction hS).F a.1 := ⟨Ψ, hΨ, p, rfl⟩
  let L : (subConstruction hS).Unif := ⟨LocalUniformizer.restrict hS.1 p, a.1, hL⟩
  let _ := Ψ.restrictMulAction hS.1
  let _ : MulAction Ψ.G ((MPolyfold.subPolyfold p).Level m) :=
    (MPolyfold.subPolyfold p).levelMulAction
      (MPolyfold.subSmul_isScSmooth p (Ψ.smul_mem_preimage hS.1) Ψ.smooth_smul) m
  let _ : MulAction Ψ.G (Ψ.P.Level m) := Ψ.P.levelMulAction Ψ.smooth_smul m
  have hqA : q ∈ Ψ.obj ⁻¹' A := by
    change Ψ.obj q ∈ A
    rw [hq']; exact (show A from a.1).2
  have hreg : S.HasRegularity m (show A from a.1).1 := (hasRegularity_sub_iff hu hS m a.1).1 a.2
  have hqm : q ∈ Ψ.P.levelSet m := (regularity_eq_of_mem hΨ hq' m).1 hreg
  have hqm' : (⟨q, hqA⟩ : Ψ.obj ⁻¹' A) ∈ (MPolyfold.subPolyfold p).levelSet m :=
    (MPolyfold.mem_subPolyfold_levelSet_iff p _ m).2 hqm
  have hcont : ∀ g : Ψ.G, Continuous fun y : Ψ.P.Level m => g • y := fun g =>
    continuousOn_univ.1 (MPolyfold.IsScSmoothOn.continuousOn_level_comp (Ψ.smooth_smul g)
      (u := id) continuousOn_id (fun _ _ => mem_univ _) fun _ _ => rfl)
  have hj : ∀ (g : Ψ.G) (b : (MPolyfold.subPolyfold p).Level m),
      MPolyfold.subLevelIncl p m (g • b) = g • MPolyfold.subLevelIncl p m b :=
    fun _ _ => MPolyfold.level_ext rfl
  have hJ := GroupoidStr.isEmbedding_orbitMap_translationMap hcont hj
    (MPolyfold.isEmbedding_subLevelIncl p m)
  have hrange : ∀ y', (S.levelFunctor ΨU m).orbitMap y' ∈ range (subRegOrbitMap hu hS m) →
      y' ∈ range (GroupoidStr.translationMapFunctor (MPolyfold.subLevelIncl p m) hj).orbitMap := by
    intro y' ⟨w, hw⟩
    induction y' using Quotient.inductionOn with | h x => ?_
    induction w using Quotient.inductionOn with | h b => ?_
    change (S.regSub m).π (subRegIncl hu hS m b) = (S.regSub m).π ((S.levelFunctor ΨU m).obj x)
      at hw
    obtain ⟨φ, hs, ht⟩ := GroupoidStr.isomorphic_fullSub_iff.1 (((S.regSub m).π_eq_π_iff).1 hw)
    have hxA : Ψ.obj (Ψ.P.levelVal m x) ∈ A := by
      have h' := C.toGroupoidStr.src_mem_iff_tgt_mem_of_isSaturated hS.1 φ
      rw [hs, ht] at h'
      exact h'.1 (show A from b.1).2
    obtain ⟨v, hv⟩ : x ∈ range (MPolyfold.subLevelIncl p m) := by
      rw [MPolyfold.range_subLevelIncl p m]; exact hxA
    exact ⟨(GroupoidStr.translation Ψ.G ((MPolyfold.subPolyfold p).Level m)).π v,
      congrArg (GroupoidStr.translation Ψ.G (Ψ.P.Level m)).π hv⟩
  have hloc := local_of_charts (injective_subRegOrbitMap hu hS m)
    (hA a.1 _ hL a.2) (hC _ Ψ hΨ hreg) hJ
    (fun y => by induction y using Quotient.inductionOn with | h _ => rfl) hrange
  refine ⟨range ((subConstruction hS).levelFunctor L m).orbitMap,
    ⟨(GroupoidStr.translation Ψ.G ((MPolyfold.subPolyfold p).Level m)).π
      ((MPolyfold.subPolyfold p).levelMk m ⟨q, hqA⟩ hqm'), ?_⟩, hloc.1, hloc.2⟩
  change ((subConstruction hS).regSub m).π _ = ((subConstruction hS).regSub m).π a
  exact congrArg _ (Subtype.ext (Subtype.ext hq'))

/-- For `m = 1`, `|Ψ_1|` is the map `|Ψ¹|` of Theorem 17.1.28. -/
theorem levelFunctor_one_orbitMap (Ψ : S.Unif) :
    letI := Ψ.1.P.levelMulAction Ψ.1.smooth_smul 1
    (S.levelFunctor Ψ 1).orbitMap = (S.levelOneFunctor Ψ).orbitMap := by
  let _ := Ψ.1.P.levelMulAction Ψ.1.smooth_smul 1
  funext z
  induction z using Quotient.inductionOn with | h _ => rfl

/-- **The level-wise statement of p. 786 for the right vertical map, level `1`**: for a
subpolyfold `A` of `C` (Definition 17.3.1, `F(α) ≠ ∅` for all `α`), with `|A_1|` carrying the
topology of Theorem 17.1.28 for the polyfold structure `(F_A, M)` of Proposition 17.3.6 and
`|C_1|` that of Theorem 17.1.28 for `(F, M)`, the map `|A_1| → |C_1|` is a topological
embedding.  The charts are the maps `|Ψ¹|` of Theorem 17.1.28
(`isOpenEmbedding_levelOneFunctor`). -/
theorem isEmbedding_subRegOrbitMap_one (hu : S.HasUniformizers) (hS : S.IsSubpolyfold A) :
    @IsEmbedding _ _
      ((subConstruction hS).levelOneTopology
        ((subConstruction hS).hasCoveringUniformizers_of_hasUniformizers
          (hasUniformizers_subConstruction hu hS)))
      (S.levelOneTopology (S.hasCoveringUniformizers_of_hasUniformizers hu))
      (subRegOrbitMap hu hS 1) := by
  let _ := (subConstruction hS).levelOneTopology
    ((subConstruction hS).hasCoveringUniformizers_of_hasUniformizers
      (hasUniformizers_subConstruction hu hS))
  let _ := S.levelOneTopology (S.hasCoveringUniformizers_of_hasUniformizers hu)
  refine isEmbedding_subRegOrbitMap_of_charts hu hS 1 (fun α Ψ hΨ _ => ?_) fun α L hL _ => ?_
  · exact S.isOpenEmbedding_levelOneFunctor _ ⟨Ψ, α, hΨ⟩
  · exact (subConstruction hS).isOpenEmbedding_levelOneFunctor _ ⟨L, α, hL⟩

end GCT.PolyfoldConstruction

/-! ### Witness -/

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- **Witness**: the case `A = X` of `isEmbedding_orbitMap_levelSub`, for every group acting by
sc-smooth maps and every level `m`. -/
theorem isEmbedding_orbitMap_levelSub_univ {G : Type u} [Group G] [MulAction G X]
    (hG : ∀ g : G, P.IsScSmoothMap P fun x => g • x) (m : ℕ) :
    haveI : ParacompactSpace (univ : Set X) := P.paracompactSpace_subtype _
    letI := GroupoidStr.subMulAction (fun (g : G) (x : X) (_ : x ∈ univ) => mem_univ (g • x))
    letI := (subPolyfold P.isSubMPolyfold_univ).levelMulAction
      (subSmul_isScSmooth P.isSubMPolyfold_univ (fun g x _ => mem_univ (g • x)) hG) m
    letI := P.levelMulAction hG m
    IsEmbedding (GroupoidStr.translationMapFunctor (subLevelIncl P.isSubMPolyfold_univ m)
      (subLevelIncl_smul P.isSubMPolyfold_univ (fun g x _ => mem_univ (g • x)) hG m)).orbitMap :=
  haveI : ParacompactSpace (univ : Set X) := P.paracompactSpace_subtype _
  isEmbedding_orbitMap_levelSub P.isSubMPolyfold_univ (fun g x _ => mem_univ (g • x)) hG m

end MPolyfold


/-! ### Witness for the right vertical map on level `1` -/

namespace GCT.PolyfoldConstruction

open EpGroupoid.Examples

/-- **Witness**: for the subpolyfold `A = {0}` of `C = ℤ/2 ⋉ ℝ`, `|A_1|` is non-empty and
`|A_1| → |C_1|` is a topological embedding. -/
theorem reflection_isEmbedding_subRegOrbitMap_one :
    Nonempty ((subConstruction reflection_isSubpolyfold_zero.1).regSub 1).OrbitSpace ∧
    @IsEmbedding _ _
      ((subConstruction reflection_isSubpolyfold_zero.1).levelOneTopology
        ((subConstruction reflection_isSubpolyfold_zero.1).hasCoveringUniformizers_of_hasUniformizers
          (hasUniformizers_subConstruction reflectionConstruction_hasUniformizers
            reflection_isSubpolyfold_zero.1)))
      (reflectionConstruction.levelOneTopology
        (reflectionConstruction.hasCoveringUniformizers_of_hasUniformizers
          reflectionConstruction_hasUniformizers))
      (subRegOrbitMap reflectionConstruction_hasUniformizers reflection_isSubpolyfold_zero.1 1) := by
  refine ⟨⟨((subConstruction reflection_isSubpolyfold_zero.1).regSub 1).π
    ⟨⟨0, rfl⟩, (hasRegularity_sub_iff reflectionConstruction_hasUniformizers
      reflection_isSubpolyfold_zero.1 1 ⟨0, rfl⟩).2
      ⟨reflectionUnif, 0, GroupoidStr.isomorphic_refl _ _,
        mem_iInter.1 rn_one_zero_mem_smoothSet 1⟩⟩⟩, ?_⟩
  exact isEmbedding_subRegOrbitMap_one _ _

end GCT.PolyfoldConstruction


/-! ### The charts of `|C_m|` for every level `m` -/

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

theorem mem_levelSet_zero (x : X) : x ∈ P.levelSet 0 := by
  rw [P.levelSet_zero]; exact mem_univ x

/-- **`X ≅ X_0`**: the level topology of `X_0` (Definition 2.3.8, 2021 p. 60) is that of `X`;
on a chart domain the lift to `E_0` is the chart itself. -/
def levelZeroHomeomorph : X ≃ₜ P.Level 0 where
  toFun x := P.levelMk 0 x (P.mem_levelSet_zero x)
  invFun := P.levelVal 0
  left_inv _ := rfl
  right_inv _ := level_ext rfl
  continuous_toFun := by
    refine continuous_generateFrom_iff.2 ?_
    rintro _ ⟨φ, hφ, W, hW, rfl⟩
    have heq : {x : X | x ∈ φ.source ∧ levelLift φ 0 x ∈ W} = φ.source ∩ φ ⁻¹' W := by
      ext x
      constructor
      · rintro ⟨hx, hxW⟩
        have h : levelLift φ 0 x = φ x := P.toBase_levelLift hφ hx (P.mem_levelSet_zero x)
        refine ⟨hx, ?_⟩
        change φ x ∈ W
        rw [← h]; exact hxW
      · rintro ⟨hx, hxW⟩
        have h : levelLift φ 0 x = φ x := P.toBase_levelLift hφ hx (P.mem_levelSet_zero x)
        refine ⟨hx, ?_⟩
        rw [h]; exact hxW
    change IsOpen {x : X | x ∈ φ.source ∧ levelLift φ 0 x ∈ W}
    rw [heq]
    exact φ.continuousOn_toFun.isOpen_inter_preimage φ.isOpen_source hW
  continuous_invFun := continuous_levelVal 0

end MPolyfold

namespace GroupoidStr

variable {G H U V : Type u} [Group G] [Group H] [MulAction G U] [MulAction H V]
  [TopologicalSpace U] [TopologicalSpace V]

/-- The functor `G ⋉ U → H ⋉ V` of an equivariant map along a group isomorphism. -/
def translationEquivFunctor (φ : G ≃* H) (E : U ≃ₜ V)
    (hE : ∀ (g : G) (x : U), E (g • x) = φ g • E x) :
    GroupoidFunctor (GroupoidStr.translation G U) (GroupoidStr.translation H V) where
  obj := E
  mor p := (φ p.1, E p.2)
  src_mor _ := rfl
  tgt_mor p := (hE p.1 p.2).symm
  mor_comp p q _ := Prod.ext (map_mul φ p.1 q.1) rfl
  mor_unit _ := Prod.ext (map_one φ) rfl

theorem translation_symm_smul (φ : G ≃* H) (E : U ≃ₜ V)
    (hE : ∀ (g : G) (x : U), E (g • x) = φ g • E x) (h : H) (y : V) :
    E.symm (h • y) = φ.symm h • E.symm y := by
  have := hE (φ.symm h) (E.symm y)
  rw [MulEquiv.apply_symm_apply, Homeomorph.apply_symm_apply] at this
  exact E.symm_apply_eq.2 this.symm

/-- **The homeomorphism `|G ⋉ U| ≅ |H ⋉ V|`** of an equivariant homeomorphism along a group
isomorphism. -/
def translationHomeomorph (φ : G ≃* H) (E : U ≃ₜ V)
    (hE : ∀ (g : G) (x : U), E (g • x) = φ g • E x) :
    (GroupoidStr.translation G U).OrbitSpace ≃ₜ (GroupoidStr.translation H V).OrbitSpace where
  toFun := (translationEquivFunctor φ E hE).orbitMap
  invFun := (translationEquivFunctor φ.symm E.symm (translation_symm_smul φ E hE)).orbitMap
  left_inv z := by
    induction z using Quotient.inductionOn with
    | h x =>
      change (GroupoidStr.translation G U).π (E.symm (E x)) = _
      rw [E.symm_apply_apply]; rfl
  right_inv z := by
    induction z using Quotient.inductionOn with
    | h y =>
      change (GroupoidStr.translation H V).π (E (E.symm y)) = _
      rw [E.apply_symm_apply]; rfl
  continuous_toFun := continuous_quot_lift _ (continuous_quot_mk.comp E.continuous)
  continuous_invFun := continuous_quot_lift _ (continuous_quot_mk.comp E.symm.continuous)

theorem translationHomeomorph_π (φ : G ≃* H) (E : U ≃ₜ V)
    (hE : ∀ (g : G) (x : U), E (g • x) = φ g • E x) (x : U) :
    translationHomeomorph φ E hE ((GroupoidStr.translation G U).π x) =
      (GroupoidStr.translation H V).π (E x) := rfl

end GroupoidStr

namespace GCT.UniformizedPolyfold

variable (X : GCT.UniformizedPolyfold.{u})

/-- **The iterated lift of a uniformizer to `C^m`**: for `Ψ ∈ F(α)`, `α ∈ C_m`, a uniformizer
`L ∈ F^m(β)` of `C^m` at the lift `β` of `α`, with a map `e : O_L → O`, a group isomorphism and
the identification `(O_L)_j ≅ O_{j+m}` for every `j` (2021 p. 766, `C^{i+1} = (C^i)¹`). -/
structure LevelLift (Ψ : X.cat.LocalUniformizer) (α : X.cat.Obj) (m : ℕ) where
  /-- The object of `C^m` over `α`. -/
  β : (X.level m).cat.Obj
  incl_β : (X.levelIncl m).obj β = α
  /-- The uniformizer of `C^m`. -/
  L : (X.level m).cat.LocalUniformizer
  mem : L ∈ (X.level m).str.F β
  /-- The underlying map of points. -/
  e : L.O → Ψ.O
  /-- The groups. -/
  φ : L.G ≃* Ψ.G
  smul : ∀ (g : L.G) (x : L.O), e (g • x) = φ g • e x
  obj : ∀ x, (X.levelIncl m).obj (L.obj x) = Ψ.obj (e x)
  lev : ∀ j k, k = j + m → ∀ x, x ∈ L.P.levelSet j ↔ e x ∈ Ψ.P.levelSet k
  hom : ∀ j k (hk : k = j + m), IsHomeomorph fun y : L.P.Level j =>
    Ψ.P.levelMk k (e (L.P.levelVal j y)) ((lev j k hk _).1 (L.P.levelVal_mem y))

variable {X}

/-- The lift to `C^0 = C`: `Ψ` itself. -/
def levelLiftZero {Ψ : X.cat.LocalUniformizer} {α : X.cat.Obj} (hΨ : Ψ ∈ X.str.F α) :
    X.LevelLift Ψ α 0 where
  β := α
  incl_β := rfl
  L := Ψ
  mem := hΨ
  e := id
  φ := MulEquiv.refl _
  smul _ _ := rfl
  obj _ := rfl
  lev j k hk x := by obtain rfl : k = j := hk; rfl
  hom j k hk := by obtain rfl : k = j := hk; exact (Homeomorph.refl _).isHomeomorph

/-- The lift to `C^{m+1} = (C^m)¹`: the lifted uniformizer `L¹` of Theorem 17.1.28. -/
def levelLiftSucc {Ψ : X.cat.LocalUniformizer} {α : X.cat.Obj} {m : ℕ}
    (hα : α ∈ X.str.regSet (m + 1)) (I : X.LevelLift Ψ α m) : X.LevelLift Ψ α (m + 1) :=
  have hreg : (X.level m).str.HasRegularity 1 I.β := by
    rw [X.hasRegularity_level_iff m I.β 1, I.incl_β, Nat.add_comm]; exact hα
  { β := ⟨I.β, hreg⟩
    incl_β := I.incl_β
    L := (X.level m).str.levelOneUnif (X.level m).hasCoveringUniformizers ⟨I.L, I.β, I.mem⟩
    mem := ⟨⟨I.L, I.β, I.mem⟩, I.mem, rfl⟩
    e := fun x => I.e (I.L.P.levelVal 1 x)
    φ := I.φ
    smul := fun g x => I.smul g (I.L.P.levelVal 1 x)
    obj := fun x => I.obj (I.L.P.levelVal 1 x)
    lev := fun j k hk x =>
      (MPolyfold.mem_shift_levelSet_iff x).trans (I.lev (j + 1) k (by omega) _)
    hom := fun j k hk =>
      (I.hom (j + 1) k (by omega)).comp (I.L.P.shiftLevelHomeomorph j).isHomeomorph }

/-- **The lift of `Ψ ∈ F(α)` to `C^m`** for `α ∈ C_m`, by induction on `m`. -/
def levelLift {Ψ : X.cat.LocalUniformizer} {α : X.cat.Obj} (hΨ : Ψ ∈ X.str.F α) :
    ∀ m, α ∈ X.str.regSet m → X.LevelLift Ψ α m
  | 0, _ => levelLiftZero hΨ
  | m + 1, h => levelLiftSucc h (levelLift hΨ m (X.str.regSet_antitone (Nat.le_succ m) h))

/-- **The charts of `|C_m|`** (2021 p. 766): for `α ∈ C_m` and `Ψ ∈ F(α)`, the map
`|Ψ_m| : |G ⋉ O_m| → |C_m|` is an open embedding for the natural topology of `|C_m|`
(`levelTopology m`, transported from the GCT `C^m`).  It is `|L|` for the lift `L` of `Ψ` to
`C^m` (`levelLift`), composed with `|G ⋉ O_m| ≅ |G_L ⋉ O_L|` and `|C^m| ≅ |C_m|`. -/
theorem isOpenEmbedding_levelFunctor (m : ℕ) {α : X.cat.Obj} (hα : α ∈ X.str.regSet m)
    {Ψ : X.cat.LocalUniformizer} (hΨ : Ψ ∈ X.str.F α) :
    letI := Ψ.P.levelMulAction Ψ.smooth_smul m
    @IsOpenEmbedding _ _ _ (X.levelTopology m) (X.str.levelFunctor ⟨Ψ, α, hΨ⟩ m).orbitMap := by
  let I := levelLift hΨ m hα
  let _ := Ψ.P.levelMulAction Ψ.smooth_smul m
  let _ := X.levelTopology m
  let _ := (X.level m).cat.top
  let E : I.L.O ≃ₜ Ψ.P.Level m := I.L.P.levelZeroHomeomorph.trans
    (IsHomeomorph.homeomorph _ (I.hom 0 m (Nat.zero_add m).symm))
  have hE : ∀ (g : I.L.G) (x : I.L.O), E (g • x) = I.φ g • E x := fun g x =>
    MPolyfold.level_ext (I.smul g x)
  let k := GroupoidStr.translationHomeomorph I.φ E hE
  have hfac : (X.str.levelFunctor ⟨Ψ, α, hΨ⟩ m).orbitMap =
      (X.levelOrbitHomeomorph m) ∘ I.L.functor.orbitMap ∘ k.symm := by
    funext z
    obtain ⟨w, rfl⟩ := k.surjective z
    simp only [Function.comp_apply, Homeomorph.symm_apply_apply]
    induction w using Quotient.inductionOn with
    | h x =>
      change (X.str.regSub m).π _ = (X.str.regSub m).π _
      exact congrArg _ (Subtype.ext (I.obj x).symm)
  rw [hfac]
  exact (X.levelOrbitHomeomorph m).isOpenEmbedding.comp
    (I.L.isOpenEmbedding_orbitMap.comp k.symm.isOpenEmbedding)

end GCT.UniformizedPolyfold

/-! ### The right vertical map on every level -/

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} {S : C.PolyfoldConstruction} {A : Set C.Obj}

/-- `C` with its polyfold structure, `F(α) ≠ ∅` for all `α`. -/
abbrev uniformized (hu : S.HasUniformizers) : GCT.UniformizedPolyfold.{u} := ⟨C, S, hu⟩

/-- The subpolyfold `A` with the polyfold structure `(F_A, M)` of Proposition 17.3.6. -/
abbrev subUniformized (hu : S.HasUniformizers) (hS : S.IsSubpolyfold A) :
    GCT.UniformizedPolyfold.{u} :=
  ⟨C.sub A, subConstruction hS, hasUniformizers_subConstruction hu hS⟩

/-- **The level-wise statement of p. 786 for the right vertical map**: for a subpolyfold `A` of
`C` (Definition 17.3.1, `F(α) ≠ ∅` for all `α`) and every level `m`, with `|A_m|` and `|C_m|`
carrying their natural topologies (2021 p. 766: transported from the GCTs `A^m` and `C^m`, for
the polyfold structures `(F_A, M)` and `(F, M)`), the map `|A_m| → |C_m|` is a topological
embedding. -/
theorem isEmbedding_subRegOrbitMap (hu : S.HasUniformizers) (hS : S.IsSubpolyfold A) (m : ℕ) :
    @IsEmbedding _ _ ((subUniformized hu hS).levelTopology m) ((uniformized hu).levelTopology m)
      (subRegOrbitMap hu hS m) := by
  let _ := (subUniformized hu hS).levelTopology m
  let _ := (uniformized hu).levelTopology m
  exact isEmbedding_subRegOrbitMap_of_charts hu hS m
    (fun _ _ hΨ hα => (uniformized hu).isOpenEmbedding_levelFunctor m hα hΨ)
    (fun _ _ hL hα => (subUniformized hu hS).isOpenEmbedding_levelFunctor m hα hL)

open EpGroupoid.Examples in
/-- **Witness**: for the subpolyfold `A = {0}` of `C = ℤ/2 ⋉ ℝ` and every level `m`, `|A_m|` is
non-empty and `|A_m| → |C_m|` is a topological embedding. -/
theorem reflection_isEmbedding_subRegOrbitMap (m : ℕ) :
    Nonempty ((subConstruction reflection_isSubpolyfold_zero.1).regSub m).OrbitSpace ∧
    @IsEmbedding _ _
      ((subUniformized reflectionConstruction_hasUniformizers
        reflection_isSubpolyfold_zero.1).levelTopology m)
      ((uniformized reflectionConstruction_hasUniformizers).levelTopology m)
      (subRegOrbitMap reflectionConstruction_hasUniformizers reflection_isSubpolyfold_zero.1 m) :=
  ⟨⟨((subConstruction reflection_isSubpolyfold_zero.1).regSub m).π
    ⟨⟨0, rfl⟩, (hasRegularity_sub_iff reflectionConstruction_hasUniformizers
      reflection_isSubpolyfold_zero.1 m ⟨0, rfl⟩).2
      ⟨reflectionUnif, 0, GroupoidStr.isomorphic_refl _ _,
        mem_iInter.1 rn_one_zero_mem_smoothSet m⟩⟩⟩,
    isEmbedding_subRegOrbitMap _ _ m⟩

end GCT.PolyfoldConstruction

end Polyfold
