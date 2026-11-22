import Polyfold.Chapter17.ModelComparison
import Polyfold.Chapter17.TangentVectors
import Polyfold.Chapter16.BranchedTame

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.5 "Branched Ep⁺-Subcategories" (pp. 812–814): **Definition 17.5.1**, **Proposition 17.5.2**
with the identities of p. 813, **Definition 17.5.3** and **Definition 17.5.4**.  Numbers and pages
are the 2021 text's.

# Branched ep⁺-subcategories

## The text, paraphrased

`C` is a GCT with a polyfold structure `(F, M)`.  (Definition 17.5.1, p. 812) A functor
`Θ : C → ℚ⁺` is a branched ep⁺-subcategory if for every object `α` and `Ψ ∈ F(α)` the functor
`Θ ∘ Ψ : G ⋉ O → ℚ⁺` is a branched ep⁺-subgroupoid (Definition 9.1.2).  It suffices to check this
for a covering family.  For the equivalence `Γ : X → C` of a covering family, `Γ^*Θ = Θ ∘ Γ`;
for `Θ : X → ℚ⁺`, `(Γ_*Θ)(α) = Θ(x)` for an `x` with a morphism `Γ(x) → α` ("one easily verifies
that this is well-defined").  (Proposition 17.5.2, p. 813, "obvious") `Γ_*` and `Γ^*` exchange
branched ep⁺-subgroupoids of `X_Ψ` and branched ep⁺-subcategories.  (p. 813, "the reader will
easily verify") For the canonical generalized isomorphism `f : X → X'`:
`f_*(Γ')^*Θ = Γ^*Θ` and `Γ_*Θ' = Γ'_* f_*Θ'`.  (Definition 17.5.3) `Θ` is compact if
`|supp(Θ)|` is a compact subset of `|C|`; tame if `Γ^*Θ` is tame for a suitable covering family
(well defined since `f` preserves tameness).  (Definition 17.5.4) `Θ` is of manifold-type if
between two objects of `supp(Θ)` there is at most one morphism and `Θ` only takes the values `0`
and `1`; of orbifold-type if it only takes the values `0` and `1`; tame if `Θ ∘ Ψ` is tame for
`α ∈ supp(Θ)` and `Ψ ∈ F(α)`, "equivalently" if `Θ ∘ Γ` is tame for an sc-smooth model.

## What is formalized

* `GroupoidStr.IsFunctorial`, `GroupoidStr.orbitSupp` (functors to `ℚ`, `|supp(Θ)|` for a
  groupoid); `GroupoidFunctor.pushTheta` (the push-forward `Γ_*` along a functor of groupoids)
  with `pushTheta_eq` (well-definedness for a full functor), `pushTheta_obj`,
  `isFunctorial_pushTheta`, `pushTheta_nonneg`.
* `PolyfoldConstruction.IsBranchedSubcategory` (**Definition 17.5.1**).
* The transfer along transition sets: `localBranching_of_tr` (a local branching structure of
  `Θ ∘ Ψ'` at `t(a)` moved by `σ⁻¹ = s ∘ (t|U)⁻¹` to one of `Θ ∘ Ψ` at `s(a)`, for
  `a ∈ M(Ψ, Ψ')`), `isBranchedEpSubgroupoid_unif_of_isCoveringFamily`, and
  **`definition_17_5_1_covering`** (it suffices to check a covering family).
* The model: `modelPull Ψ Θ = Θ ∘ Γ_Ψ`, `modelPush Ψ Θ = (Γ_Ψ)_*Θ`;
  `isBranchedEpSubgroupoid_modelPull_iff` (`Θ ∘ Γ_Ψ` is branched iff every `Θ ∘ Ψ_λ` is);
  **`proposition_17_5_2_one`**, **`proposition_17_5_2_two`**.
* The identities of p. 813 for the canonical generalized isomorphism `f = S.comparison c c'`:
  **`pullTheta_comparison_modelPull`** (`f^*(Γ')^*Θ = Γ^*Θ`),
  **`pushTheta_comparison_modelPull`** (`f_*Γ^*Θ = (Γ')^*Θ`, used in the proof of 17.5.5 and on
  p. 815), **`modelPush_pushTheta_comparison`** (`Γ_*Θ' = Γ'_* f_*Θ'`).
* `C.toGroupoidStr.orbitSupp Θ` (`|supp(Θ)| ⊆ |C|`), `image_modelOrbitMap_orbitSupp`
  (`|Γ|(|supp(Γ^*Θ)|) = |supp(Θ)|`), `GCT.IsCompactBranched` (**Definition 17.5.3 (1)**),
  `isCompactBranched_iff_model`; `IsTameVia`, `IsTameModel`
  (**Definition 17.5.3 (2)**), **`definition_17_5_3_two`** (independence of the covering family).
* `GCT.IsManifoldTypeBranched`, `GCT.IsOrbifoldTypeBranched`, `IsTameSubcategory`
  (**Definition 17.5.4**); `isOrbifoldType_modelPull_iff`, `isManifoldType_modelPull_iff`
  (the first step of the proof of Proposition 17.5.5); `EpGroupoid.isTameBranched_iff_exists`
  (tameness is the existence of local branching structures with tame sheets), and
  **`definition_17_5_4_three`** (the "equivalently" of (3)).
* Witnesses (in `BranchedSubcategoryExamples.lean`).

## Readings

* `ℚ⁺` is `ℚ_{≥0}`, as in Chapter 9; a functor `C → ℚ` is a function constant along morphisms
  (`GroupoidStr.IsFunctorial`).  Definition 17.5.1 is read with the functor property and
  `Θ ≥ 0` on all of `C` (they are part of "a functor `Θ : C → ℚ⁺`"), and with the condition for
  every object `α` and every `Ψ ∈ F(α)`.
* The topological part of Definition 9.1.2 (1) (`|supp(Θ ∘ Ψ)|` paracompact) holds automatically:
  `|G ⋉ O|` is metrizable (Definition 17.1.2), hence so is every subspace.
* `Γ_*` is defined for every functor through a choice (`0` if no `Γ(x)` is isomorphic to `α`); it
  is the text's push-forward for a covering family, and the value does not depend on the choice
  since `Γ_Ψ` is full (`pushTheta_eq`).
* The identity "`f_*(Γ')^*Θ = Γ^*Θ`" (p. 813) is read as `f^*(Γ')^*Θ = Γ^*Θ` (`f : X → X'` pushes
  functors on `X` forward, and `(Γ')^*Θ` lives on `X'`); its push-forward form
  `f_*Γ^*Θ = (Γ')^*Θ` is the one used in the proof of Proposition 17.5.5 and on p. 815.  Both are
  proved.  In "`Γ_*Θ' = Γ'_* f_*Θ'` for `Θ' : X → ℚ⁺`" the functor `Θ'` is on `X`.
* Definition 17.5.3 (2) is formalized for the models (`IsTameVia c`); Definition 17.5.4 (3)
  through the uniformizers.  "Equivalently" in 17.5.4 (3) is proved under the standing reading
  `F(α) ≠ ∅` (`HasUniformizers`): a uniformizer through a point of `supp(Θ)` need not be in
  `F(α)` for an `α ∈ supp(Θ)` otherwise.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology CategoryTheory

noncomputable section

namespace Polyfold

universe u v

/-! ### Functors to `ℚ` on groupoids, and the push-forward along a functor -/

namespace GroupoidStr

variable {Obj Mor : Type u} (G : GroupoidStr Obj Mor)

/-- A function `Θ : Obj → ℚ` is a **functor** to `ℚ` (a category with only identity morphisms)
if `Θ(s φ) = Θ(t φ)` for every morphism `φ`. -/
def IsFunctorial (Θ : Obj → ℚ) : Prop := ∀ φ : Mor, Θ (G.src φ) = Θ (G.tgt φ)

/-- The orbit set `|supp(Θ)| = π({x | Θ(x) > 0})` in `|G|`. -/
def orbitSupp (Θ : Obj → ℚ) : Set G.OrbitSpace := G.π '' {x | 0 < Θ x}

variable {G}

theorem IsFunctorial.eq_of_isomorphic {Θ : Obj → ℚ} (hΘ : G.IsFunctorial Θ) {x y : Obj}
    (h : G.Isomorphic x y) : Θ x = Θ y := by
  obtain ⟨φ, rfl, rfl⟩ := h
  exact hΘ φ

theorem IsFunctorial.eq_of_π_eq {Θ : Obj → ℚ} (hΘ : G.IsFunctorial Θ) {x y : Obj}
    (h : G.π x = G.π y) : Θ x = Θ y :=
  hΘ.eq_of_isomorphic ((G.π_eq_π_iff).1 h)

theorem preimage_π_orbitSupp {Θ : Obj → ℚ} (hΘ : G.IsFunctorial Θ) :
    G.π ⁻¹' G.orbitSupp Θ = {x | 0 < Θ x} := by
  ext y
  constructor
  · rintro ⟨a, ha, hay⟩
    change 0 < Θ y
    rwa [← hΘ.eq_of_π_eq hay]
  · intro hy
    exact ⟨y, hy, rfl⟩

end GroupoidStr

namespace GroupoidFunctor

variable {Obj Mor : Type u} {Obj' Mor' : Type v} {G : GroupoidStr Obj Mor}
  {H : GroupoidStr Obj' Mor'}

/-- The pull-back `F^*Θ = Θ ∘ F` of a functor to `ℚ` is a functor. -/
theorem isFunctorial_comp (F : GroupoidFunctor G H) {Θ : Obj' → ℚ} (hΘ : H.IsFunctorial Θ) :
    G.IsFunctorial (Θ ∘ F.obj) := fun φ => by
  change Θ (F.obj (G.src φ)) = Θ (F.obj (G.tgt φ))
  rw [← F.src_mor, ← F.tgt_mor]
  exact hΘ _

theorem isomorphic_obj (F : GroupoidFunctor G H) {x x' : Obj} (h : G.Isomorphic x x') :
    H.Isomorphic (F.obj x) (F.obj x') := by
  obtain ⟨φ, rfl, rfl⟩ := h
  exact ⟨F.mor φ, F.src_mor φ, F.tgt_mor φ⟩

theorem isomorphic_of_full {F : GroupoidFunctor G H} (hF : F.toFunctor.Full) {x x' : Obj}
    (h : H.Isomorphic (F.obj x) (F.obj x')) : G.Isomorphic x x' := by
  obtain ⟨ψ, hs, ht⟩ := h
  obtain ⟨φ, h1, h2, -⟩ := (F.full_iff.1 hF) x x' ψ hs ht
  exact ⟨φ, h1, h2⟩

open scoped Classical in
/-- **The push-forward `F_*Θ : H → ℚ`** of `Θ : G → ℚ` along a functor `F` (2021 p. 812):
`(F_*Θ)(y) = Θ(x)` for a chosen `x` with a morphism `F(x) → y` (`0` if there is none). -/
def pushTheta (F : GroupoidFunctor G H) (Θ : Obj → ℚ) (y : Obj') : ℚ :=
  if h : ∃ x, H.Isomorphic (F.obj x) y then Θ h.choose else 0

variable {F : GroupoidFunctor G H}

/-- **Well-definedness of `F_*Θ`** (2021 p. 812, "one easily verifies"): for a full `F` and a
functor `Θ`, `(F_*Θ)(y) = Θ(x)` for every `x` with a morphism `F(x) → y`. -/
theorem pushTheta_eq (hF : F.toFunctor.Full) {Θ : Obj → ℚ} (hΘ : G.IsFunctorial Θ) {x : Obj}
    {y : Obj'} (h : H.Isomorphic (F.obj x) y) : F.pushTheta Θ y = Θ x := by
  have hex : ∃ x, H.Isomorphic (F.obj x) y := ⟨x, h⟩
  rw [pushTheta, dif_pos hex]
  exact hΘ.eq_of_isomorphic (isomorphic_of_full hF (hex.choose_spec.trans h.symm))

theorem pushTheta_obj (hF : F.toFunctor.Full) {Θ : Obj → ℚ} (hΘ : G.IsFunctorial Θ) (x : Obj) :
    F.pushTheta Θ (F.obj x) = Θ x :=
  pushTheta_eq hF hΘ (H.isomorphic_refl _)

/-- `F^*F_*Θ = Θ` for a full `F`. -/
theorem pushTheta_comp_obj (hF : F.toFunctor.Full) {Θ : Obj → ℚ} (hΘ : G.IsFunctorial Θ) :
    F.pushTheta Θ ∘ F.obj = Θ :=
  funext (pushTheta_obj hF hΘ)

theorem pushTheta_of_not_exists {Θ : Obj → ℚ} {y : Obj'}
    (h : ¬ ∃ x, H.Isomorphic (F.obj x) y) : F.pushTheta Θ y = 0 := by
  rw [pushTheta, dif_neg h]

theorem pushTheta_nonneg {Θ : Obj → ℚ} (hΘ : ∀ x, 0 ≤ Θ x) (y : Obj') : 0 ≤ F.pushTheta Θ y := by
  unfold pushTheta
  split_ifs
  · exact hΘ _
  · exact le_rfl

/-- `F_*Θ` is a functor (for full `F` and a functor `Θ`). -/
theorem isFunctorial_pushTheta (hF : F.toFunctor.Full) {Θ : Obj → ℚ} (hΘ : G.IsFunctorial Θ) :
    H.IsFunctorial (F.pushTheta Θ) := fun ψ => by
  by_cases hex : ∃ x, H.Isomorphic (F.obj x) (H.src ψ)
  · obtain ⟨x, hx⟩ := hex
    rw [pushTheta_eq hF hΘ hx, pushTheta_eq hF hΘ (hx.trans ⟨ψ, rfl, rfl⟩)]
  · rw [pushTheta_of_not_exists hex, pushTheta_of_not_exists fun ⟨x, hx⟩ =>
      hex ⟨x, hx.trans ⟨H.inv ψ, H.src_inv ψ, H.tgt_inv ψ⟩⟩]

/-- `F_*F^*Θ' = Θ'` for an essentially surjective `F` and a functor `Θ'`. -/
theorem pushTheta_comp_obj_eq (hF : F.toFunctor.Full) (hE : F.toFunctor.EssSurj) {Θ' : Obj' → ℚ}
    (hΘ' : H.IsFunctorial Θ') : F.pushTheta (Θ' ∘ F.obj) = Θ' := by
  funext y
  obtain ⟨x, ψ, hs, ht⟩ := (F.essSurj_iff.1 hE) y
  rw [pushTheta_eq hF (F.isFunctorial_comp hΘ') ⟨ψ, hs, ht⟩]
  exact hΘ'.eq_of_isomorphic ⟨ψ, hs, ht⟩

end GroupoidFunctor

/-! ### Tameness as a local condition on the sheets -/

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- **Tameness of `Θ` (Definition 9.3.6) is the existence, at every point of `supp(Θ)`, of a local
branching structure with tame sheets**: such a structure is restricted to the domain of a natural
representation (Theorem 7.1.13) inside a neighbourhood with the properness property. -/
theorem isTameBranched_iff_exists (Θ : Obj → ℚ) :
    X.IsTameBranched Θ ↔ ∀ x ∈ supp Θ, ∃ B : X.LocalBranchingStructure Θ x,
      ∀ i, X.PObj.HasTameInducedStructure (B.M i) := by
  constructor
  · intro h x hx
    obtain ⟨T⟩ := h x hx
    exact ⟨T.toLocalBranchingStructure, T.hasTameInducedStructure⟩
  · intro h x hx
    obtain ⟨B, hB⟩ := h x hx
    obtain ⟨V, hxV, hVP⟩ := X.exists_hasPropernessProperty x
    obtain ⟨R, hR⟩ := X.theorem_7_1_13 x (hVP.1.inter B.isOpen_U) ⟨hxV, B.mem_U⟩
    exact ⟨{ toLocalBranchingStructure :=
                B.restrict R.isOpen_U R.mem_U (hR.trans inter_subset_right)
             rep := R
             U_eq := rfl
             hasPropernessProperty := hVP.mono R.isOpen_U (hR.trans inter_subset_left)
             hasTameInducedStructure := fun i => MPolyfold.HasTameInducedStructure.inter_isOpen
               (B.isSmoothSubmanifold i) (hB i) R.isOpen_U }⟩

end EpGroupoid

/-! ### Definition 17.5.1 -/

namespace GCT

variable {C : GCT.{u}}

/-- `|G ⋉ O|` of a local uniformizer is metrizable, so every subspace is paracompact. -/
theorem LocalUniformizer.paracompactSpace_subset (Ψ : C.LocalUniformizer)
    (A : Set Ψ.ep.OrbitSpace) :
    ParacompactSpace A := by
  have : TopologicalSpace.MetrizableSpace Ψ.ep.OrbitSpace :=
    metrizableSpace_translation_orbitSpace Ψ.smooth_smul
  exact paracompactSpace_of_metrizableSpace A

/-- `Θ ∘ Ψ` is a functor on `G ⋉ O` for a functor `Θ` on `C`. -/
theorem LocalUniformizer.isFunctorial_comp (Ψ : C.LocalUniformizer) {Θ : C.Obj → ℚ}
    (hΘ : C.toGroupoidStr.IsFunctorial Θ) : Ψ.ep.IsFunctorial (Θ ∘ Ψ.obj) :=
  Ψ.functor.isFunctorial_comp hΘ

namespace PolyfoldConstruction

variable (S : C.PolyfoldConstruction)

/-- **Definition 17.5.1 (branched ep⁺-subcategory)**, 2021 p. 812: a functor `Θ : C → ℚ⁺`
(`Θ ≥ 0`, constant along morphisms) such that for every object `α` and every `Ψ ∈ F(α)` the
functor `Θ ∘ Ψ : G ⋉ O → ℚ⁺` is a branched ep⁺-subgroupoid (Definition 9.1.2). -/
structure IsBranchedSubcategory (Θ : C.Obj → ℚ) : Prop where
  nonneg : ∀ α, 0 ≤ Θ α
  isFunctorial : C.toGroupoidStr.IsFunctorial Θ
  isBranched : ∀ α, ∀ Ψ ∈ S.F α, Ψ.ep.IsBranchedEpSubgroupoid (Θ ∘ Ψ.obj)

variable {S}

/-! #### Transfer along transition sets -/

/-- For `a ∈ M(Ψ, Ψ')` and `u` near `s(a)`: `Θ(Ψ'(σ(u))) = Θ(Ψ(u))` (the element `(s|U)⁻¹(u)`
is a morphism `Ψ(u) → Ψ'(σ(u))`). -/
theorem theta_sigmaInv_eq {Θ : C.Obj → ℚ} (hΘ : C.toGroupoidStr.IsFunctorial Θ) {Ψ Ψ' : S.Unif}
    {a : S.Tr Ψ Ψ'} (T : S.AdmissibleTriple a) {u : Ψ'.1.O} (hu : u ∈ T.tgtSet) :
    Θ (Ψ.1.obj (T.sigmaInv u)) = Θ (Ψ'.1.obj u) := by
  set b := T.tgtInv u
  have hbt : b.tgt = u := T.isScDiffeoOn_tgt.right_inv u hu
  change Θ (Ψ.1.obj b.src) = _
  rw [← hbt]
  exact (congrArg Θ b.src_mor).symm.trans ((hΘ b.mor).trans (congrArg Θ b.tgt_mor))

/-- **A local branching structure moved along a transition set** (the step behind "it suffices
to check a covering family", p. 812): for `a ∈ M(Ψ, Ψ')`, a local branching structure of `Θ ∘ Ψ'`
at `t(a)` is moved by `σ⁻¹ = s ∘ (t|U)⁻¹` to one of `Θ ∘ Ψ` at `s(a)`; tame sheets stay tame. -/
theorem localBranching_of_tr {Θ : C.Obj → ℚ} (hΘ : C.toGroupoidStr.IsFunctorial Θ)
    {Ψ Ψ' : S.Unif} (a : S.Tr Ψ Ψ') (B : Ψ'.1.ep.LocalBranchingStructure (Θ ∘ Ψ'.1.obj) a.tgt) :
    ∃ B' : Ψ.1.ep.LocalBranchingStructure (Θ ∘ Ψ.1.obj) a.src,
      (∀ i, Ψ'.1.P.HasTameInducedStructure (B.M i)) →
        ∀ i, Ψ.1.P.HasTameInducedStructure (B'.M i) := by
  set T := S.triple a
  have hf : Ψ'.1.P.IsScDiffeoOn Ψ.1.P T.sigmaInv T.sigma T.tgtSet T.srcSet :=
    T.isScDiffeoOn_sigma.symm
  have hxW : a.tgt ∈ T.tgtSet := T.isScDiffeoOn_tgt.mapsTo T.mem_carrier
  have hxy : T.sigmaInv a.tgt = a.src := by
    change (T.tgtInv a.tgt).src = a.src
    rw [T.isScDiffeoOn_tgt.left_inv a T.mem_carrier]
  have hΘ' : ∀ u ∈ T.tgtSet, (Θ ∘ Ψ.1.obj) (T.sigmaInv u) = (Θ ∘ Ψ'.1.obj) u :=
    fun u hu => theta_sigmaInv_eq hΘ T hu
  refine ⟨B.mapDiffeo (X := Ψ'.1.ep) (Y := Ψ.1.ep) hf hxW hxy hΘ', fun ht i => ?_⟩
  exact MPolyfold.HasTameInducedStructure.image_of_isScDiffeoOn
    ((B.isSmoothSubmanifold i).inter_isOpen hf.isScSmoothOn.isOpen)
    (MPolyfold.HasTameInducedStructure.inter_isOpen (B.isSmoothSubmanifold i) (ht i)
      hf.isScSmoothOn.isOpen) hf inter_subset_right

/-- Through every point of a uniformizer passes an element of a transition set into some member
of a covering family. -/
theorem exists_tr_of_isCoveringFamily {ι : Type u} {Φ : ι → S.Unif}
    (hc : S.IsCoveringFamily Φ) (Ψ : S.Unif) (q : Ψ.1.O) :
    ∃ (i : ι) (a : S.Tr Ψ (Φ i)), a.src = q := by
  obtain ⟨i, hi⟩ := mem_iUnion.1 (hc.symm ▸ mem_univ (C.toGroupoidStr.π (Ψ.1.obj q)))
  obtain ⟨q', hq'⟩ := (Φ i).1.mem_footprint_iff.1 hi
  obtain ⟨φ, hs, ht⟩ := (GroupoidStr.π_eq_π_iff _).1 hq'.symm
  exact ⟨i, ⟨q, φ, q', hs, ht⟩, rfl⟩

theorem theta_tgt_eq {Θ : C.Obj → ℚ} (hΘ : C.toGroupoidStr.IsFunctorial Θ) {Ψ Ψ' : S.Unif}
    (a : S.Tr Ψ Ψ') : Θ (Ψ'.1.obj a.tgt) = Θ (Ψ.1.obj a.src) :=
  ((congrArg Θ a.src_mor).symm.trans ((hΘ a.mor).trans (congrArg Θ a.tgt_mor))).symm

/-- `s(a)` is smooth iff `t(a)` is (both are local sc-diffeomorphisms). -/
theorem src_mem_smoothSet_iff {Ψ Ψ' : S.Unif} (a : S.Tr Ψ Ψ') :
    a.src ∈ Ψ.1.P.smoothSet ↔ a.tgt ∈ Ψ'.1.P.smoothSet :=
  ((S.isLocalScDiffeo_trSrc Ψ Ψ').mem_smoothSet_iff a).trans
    ((S.isLocalScDiffeo_trTgt Ψ Ψ').mem_smoothSet_iff a).symm

/-- **Definition 17.5.1, "it suffices to check a covering family"** (2021 p. 812), the core: if
`Θ` is a functor and `Θ ∘ Φ_λ` is a branched ep⁺-subgroupoid for every member of a covering family,
then `Θ ∘ Ψ` is one for every uniformizer `Ψ` coming from `F`. -/
theorem isBranchedEpSubgroupoid_unif_of_isCoveringFamily {Θ : C.Obj → ℚ}
    (h0 : ∀ α, 0 ≤ Θ α) (hΘ : C.toGroupoidStr.IsFunctorial Θ) {ι : Type u} {Φ : ι → S.Unif}
    (hc : S.IsCoveringFamily Φ)
    (h : ∀ i, (Φ i).1.ep.IsBranchedEpSubgroupoid (Θ ∘ (Φ i).1.obj)) (Ψ : S.Unif) :
    Ψ.1.ep.IsBranchedEpSubgroupoid (Θ ∘ Ψ.1.obj) where
  nonneg _ := h0 _
  isFunctorial := Ψ.1.isFunctorial_comp hΘ
  support_subset q hq := by
    obtain ⟨i, a, rfl⟩ := exists_tr_of_isCoveringFamily hc Ψ q
    refine (src_mem_smoothSet_iff a).2 ((h i).support_subset ?_)
    change 0 < Θ ((Φ i).1.obj a.tgt)
    rw [theta_tgt_eq hΘ a]
    exact hq
  paracompactSpace_orbitSupp := Ψ.1.paracompactSpace_subset _
  localBranching q hq := by
    obtain ⟨i, a, rfl⟩ := exists_tr_of_isCoveringFamily hc Ψ q
    have hq' : a.tgt ∈ EpGroupoid.supp (Θ ∘ (Φ i).1.obj) := by
      change 0 < Θ ((Φ i).1.obj a.tgt)
      rw [theta_tgt_eq hΘ a]
      exact hq
    obtain ⟨B⟩ := (h i).localBranching _ hq'
    obtain ⟨B', -⟩ := localBranching_of_tr hΘ a B
    exact ⟨B'⟩

/-- **Definition 17.5.1, "it suffices to check a covering family"** (2021 p. 812): for a covering
family `(Φ_λ)`, `Θ` is a branched ep⁺-subcategory iff it is a functor `C → ℚ⁺` and every `Θ ∘ Φ_λ`
is a branched ep⁺-subgroupoid. -/
theorem definition_17_5_1_covering {Θ : C.Obj → ℚ} {ι : Type u} {Φ : ι → S.Unif}
    (hc : S.IsCoveringFamily Φ) :
    S.IsBranchedSubcategory Θ ↔ (∀ α, 0 ≤ Θ α) ∧ C.toGroupoidStr.IsFunctorial Θ ∧
      ∀ i, (Φ i).1.ep.IsBranchedEpSubgroupoid (Θ ∘ (Φ i).1.obj) := by
  constructor
  · intro h
    exact ⟨h.nonneg, h.isFunctorial, fun i => h.isBranched _ _ (Φ i).2.choose_spec⟩
  · rintro ⟨h0, hΘ, h⟩
    exact ⟨h0, hΘ, fun α Ψ hΨ =>
      isBranchedEpSubgroupoid_unif_of_isCoveringFamily h0 hΘ hc h ⟨Ψ, α, hΨ⟩⟩

/-- A branched ep⁺-subcategory gives a branched ep⁺-subgroupoid `Θ ∘ Ψ` for every uniformizer
coming from `F`. -/
theorem IsBranchedSubcategory.unif {Θ : C.Obj → ℚ} (h : S.IsBranchedSubcategory Θ) (Ψ : S.Unif) :
    Ψ.1.ep.IsBranchedEpSubgroupoid (Θ ∘ Ψ.1.obj) :=
  h.isBranched _ _ Ψ.2.choose_spec

/-! #### The model: `Γ^*` and `Γ_*` -/

variable (S) {ι : Type u} (Ψ : ι → S.Unif)

/-- **The pull-back `Γ^*Θ = Θ ∘ Γ`** of `Θ : C → ℚ⁺` to the model `X_Ψ` (2021 p. 812). -/
def modelPull (Θ : C.Obj → ℚ) : S.ModelObj Ψ → ℚ := Θ ∘ (S.modelFunctor Ψ).obj

/-- **The push-forward `Γ_*Θ : C → ℚ⁺`** of `Θ : X_Ψ → ℚ⁺` (2021 p. 812): `(Γ_*Θ)(α) = Θ(x)` for
an `x` with a morphism `Γ(x) → α`. -/
def modelPush (Θ : S.ModelObj Ψ → ℚ) : C.Obj → ℚ := (S.modelFunctor Ψ).pushTheta Θ

@[simp] theorem modelPull_apply (Θ : C.Obj → ℚ) (x : S.ModelObj Ψ) :
    S.modelPull Ψ Θ x = Θ ((Ψ x.1).1.obj x.2) := rfl

variable {S Ψ}

theorem isFunctorial_modelPull {Θ : C.Obj → ℚ} (hΘ : C.toGroupoidStr.IsFunctorial Θ) :
    (S.modelEP Ψ).X.IsFunctorial (S.modelPull Ψ Θ) :=
  (S.modelFunctor Ψ).isFunctorial_comp hΘ

/-- `|X_Ψ|` is metrizable for every family (`|Γ_Ψ|` is an open embedding into `|C|`). -/
theorem metrizableSpace_modelOrbitSpace_of_family :
    TopologicalSpace.MetrizableSpace (S.modelEP Ψ).X.OrbitSpace :=
  (IsOpenEmbedding.of_continuous_injective_isOpenMap (S.continuous_modelOrbitMap Ψ)
    ((S.modelFunctor Ψ).injective_orbitMap_of_full (S.modelFunctor_full Ψ))
    (S.isOpenMap_modelOrbitMap Ψ)).isEmbedding.metrizableSpace

theorem paracompactSpace_model_subset (A : Set (S.modelEP Ψ).X.OrbitSpace) :
    ParacompactSpace A := by
  have := metrizableSpace_modelOrbitSpace_of_family (S := S) (Ψ := Ψ)
  exact paracompactSpace_of_metrizableSpace A

/-- A local branching structure of `Θ ∘ Γ_Ψ` at `(λ, q)` restricted to the summand `O_λ` is one of
`Θ ∘ Ψ_λ` at `q`, and conversely (the summand inclusion is an sc-diffeomorphism onto an open
piece); tame sheets stay tame. -/
theorem localBranching_summand {Θ : C.Obj → ℚ} (i : ι) (q : (Ψ i).1.O)
    (B : (S.modelEP Ψ).X.LocalBranchingStructure (S.modelPull Ψ Θ) ⟨i, q⟩) :
    ∃ B' : (Ψ i).1.ep.LocalBranchingStructure (Θ ∘ (Ψ i).1.obj) q,
      (∀ j, (S.modelEP Ψ).X.PObj.HasTameInducedStructure (B.M j)) →
        ∀ j, (Ψ i).1.P.HasTameInducedStructure (B'.M j) := by
  have hd := (MPolyfold.isScDiffeoOn_sigmaMk (fun i => (Ψ i).1.P) i q).symm
  have hΘ' : ∀ u ∈ range (S.objMk Ψ i),
      (Θ ∘ (Ψ i).1.obj) (sigmaProj i q u) = S.modelPull Ψ Θ u := by
    rintro _ ⟨v, rfl⟩
    rw [sigmaProj_mk]
    rfl
  refine ⟨B.mapDiffeo (Y := (Ψ i).1.ep) hd (mem_range_self q)
    (sigmaProj_mk (X := fun i => (Ψ i).1.O) i q q) hΘ',
    fun ht j => ?_⟩
  exact MPolyfold.HasTameInducedStructure.image_of_isScDiffeoOn
    ((B.isSmoothSubmanifold j).inter_isOpen hd.isScSmoothOn.isOpen)
    (MPolyfold.HasTameInducedStructure.inter_isOpen (B.isSmoothSubmanifold j) (ht j)
      hd.isScSmoothOn.isOpen) hd inter_subset_right

theorem localBranching_of_summand {Θ : C.Obj → ℚ} (i : ι) (q : (Ψ i).1.O)
    (B : (Ψ i).1.ep.LocalBranchingStructure (Θ ∘ (Ψ i).1.obj) q) :
    ∃ B' : (S.modelEP Ψ).X.LocalBranchingStructure (S.modelPull Ψ Θ) ⟨i, q⟩,
      (∀ j, (Ψ i).1.P.HasTameInducedStructure (B.M j)) →
        ∀ j, (S.modelEP Ψ).X.PObj.HasTameInducedStructure (B'.M j) := by
  have hd := MPolyfold.isScDiffeoOn_sigmaMk (fun i => (Ψ i).1.P) i q
  refine ⟨B.mapDiffeo (Y := (S.modelEP Ψ).X) hd (mem_univ q) rfl (fun _ _ => rfl),
    fun ht j => ?_⟩
  exact MPolyfold.HasTameInducedStructure.image_of_isScDiffeoOn
    ((B.isSmoothSubmanifold j).inter_isOpen hd.isScSmoothOn.isOpen)
    (MPolyfold.HasTameInducedStructure.inter_isOpen (B.isSmoothSubmanifold j) (ht j)
      hd.isScSmoothOn.isOpen) hd inter_subset_right

theorem mem_smoothSet_model_iff (i : ι) (q : (Ψ i).1.O) :
    (⟨i, q⟩ : S.ModelObj Ψ) ∈ (S.modelEP Ψ).X.PObj.smoothSet ↔ q ∈ (Ψ i).1.P.smoothSet :=
  (MPolyfold.isLocalScDiffeo_sigmaMk (fun i => (Ψ i).1.P) i).mem_smoothSet_iff q

/-- **`Θ ∘ Γ_Ψ` is a branched ep⁺-subgroupoid of `X_Ψ` iff every `Θ ∘ Ψ_λ` is one** (for a
functor `Θ : C → ℚ⁺`; the structures live on the summands `O_λ`, and `|X_Ψ|` is metrizable). -/
theorem isBranchedEpSubgroupoid_modelPull_iff {Θ : C.Obj → ℚ} (h0 : ∀ α, 0 ≤ Θ α)
    (hΘ : C.toGroupoidStr.IsFunctorial Θ) :
    (S.modelEP Ψ).X.IsBranchedEpSubgroupoid (S.modelPull Ψ Θ) ↔
      ∀ i, (Ψ i).1.ep.IsBranchedEpSubgroupoid (Θ ∘ (Ψ i).1.obj) := by
  constructor
  · intro h i
    exact
      { nonneg := fun _ => h0 _
        isFunctorial := (Ψ i).1.isFunctorial_comp hΘ
        support_subset := fun q hq => (mem_smoothSet_model_iff i q).1
          (h.support_subset (a := ⟨i, q⟩) hq)
        paracompactSpace_orbitSupp := (Ψ i).1.paracompactSpace_subset _
        localBranching := fun q hq => by
          obtain ⟨B⟩ := h.localBranching ⟨i, q⟩ hq
          obtain ⟨B', -⟩ := localBranching_summand i q B
          exact ⟨B'⟩ }
  · intro h
    exact
      { nonneg := fun _ => h0 _
        isFunctorial := isFunctorial_modelPull hΘ
        support_subset := fun x hx => by
          obtain ⟨i, q⟩ := x
          exact (mem_smoothSet_model_iff i q).2 ((h i).support_subset hx)
        paracompactSpace_orbitSupp := paracompactSpace_model_subset _
        localBranching := fun x hx => by
          obtain ⟨i, q⟩ := x
          obtain ⟨B⟩ := (h i).localBranching q hx
          obtain ⟨B', -⟩ := localBranching_of_summand i q B
          exact ⟨B'⟩ }

/-- **Proposition 17.5.2 (2)** (2021 p. 813): for a branched ep⁺-subcategory `Θ`, `Γ_Ψ^*Θ` is a
branched ep⁺-subgroupoid of `X_Ψ` (for every family `Ψ` of uniformizers from `F`). -/
theorem proposition_17_5_2_two {Θ : C.Obj → ℚ} (h : S.IsBranchedSubcategory Θ) :
    (S.modelEP Ψ).X.IsBranchedEpSubgroupoid (S.modelPull Ψ Θ) :=
  (isBranchedEpSubgroupoid_modelPull_iff h.nonneg h.isFunctorial).2 fun i => h.unif (Ψ i)

theorem modelPull_modelPush {Θ : S.ModelObj Ψ → ℚ} (hΘ : (S.modelEP Ψ).X.IsFunctorial Θ) :
    S.modelPull Ψ (S.modelPush Ψ Θ) = Θ :=
  GroupoidFunctor.pushTheta_comp_obj (S.modelFunctor_full Ψ) hΘ

theorem modelPush_modelPull (hc : S.IsCoveringFamily Ψ) {Θ : C.Obj → ℚ}
    (hΘ : C.toGroupoidStr.IsFunctorial Θ) : S.modelPush Ψ (S.modelPull Ψ Θ) = Θ :=
  GroupoidFunctor.pushTheta_comp_obj_eq (S.modelFunctor_full Ψ) (modelFunctor_essSurj hc) hΘ

theorem isFunctorial_modelPush {Θ : S.ModelObj Ψ → ℚ} (hΘ : (S.modelEP Ψ).X.IsFunctorial Θ) :
    C.toGroupoidStr.IsFunctorial (S.modelPush Ψ Θ) :=
  GroupoidFunctor.isFunctorial_pushTheta (S.modelFunctor_full Ψ) hΘ

/-- **Proposition 17.5.2 (1)** (2021 p. 813): for a covering family `Ψ` and a branched
ep⁺-subgroupoid `Θ` of `X_Ψ`, `(Γ_Ψ)_*Θ` is a branched ep⁺-subcategory. -/
theorem proposition_17_5_2_one (hc : S.IsCoveringFamily Ψ) {Θ : S.ModelObj Ψ → ℚ}
    (h : (S.modelEP Ψ).X.IsBranchedEpSubgroupoid Θ) :
    S.IsBranchedSubcategory (S.modelPush Ψ Θ) := by
  have h0 : ∀ α, 0 ≤ S.modelPush Ψ Θ α := GroupoidFunctor.pushTheta_nonneg h.nonneg
  have hΘ := isFunctorial_modelPush h.isFunctorial
  refine (definition_17_5_1_covering hc).2 ⟨h0, hΘ, ?_⟩
  refine (isBranchedEpSubgroupoid_modelPull_iff h0 hΘ).1 ?_
  rw [modelPull_modelPush h.isFunctorial]
  exact h

/-! #### The canonical generalized isomorphism (p. 813) -/

open EPLocalization EPLocalization.EPLoc

/-- **`f_*Θ` at `y` is `Θ` at any `x` with `|f|(|x|) = |y|`** (`|f_*Θ| = |Θ| ∘ |f|⁻¹`). -/
theorem _root_.Polyfold.EPLocalization.EPLoc.pushTheta_eq_of_orbitMap {X Y : EP.{u}}
    {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) {Θ : X.Obj → ℚ} (hΘ : X.X.IsFunctorial Θ)
    {x : X.Obj} {y : Y.Obj} (h : orbitMap f (X.X.π x) = Y.X.π y) :
    EPLoc.pushTheta f Θ y = Θ x :=
  (pullTheta_eq_of_orbitMap hf (isFunctorial_pushTheta hf hΘ) h).symm.trans
    (congrFun (pullTheta_pushTheta hf hΘ) x)

variable (c c' : S.CoveringFamily)

/-- Points related by `|f|` (`f = f_{Ψ,Ψ'}`) have isomorphic images in `C` (`|Γ'| ∘ |f| = |Γ|`,
Theorem 17.1.18). -/
theorem isomorphic_of_orbitMap_comparison {x : (S.modelEP c.Ψ).Obj} {y : (S.modelEP c'.Ψ).Obj}
    (h : orbitMap (S.comparison c c') ((S.modelEP c.Ψ).X.π x) = (S.modelEP c'.Ψ).X.π y) :
    C.toGroupoidStr.Isomorphic ((S.modelFunctor c.Ψ).obj x) ((S.modelFunctor c'.Ψ).obj y) := by
  have := congrFun (S.orbitMap_comparison c c') ((S.modelEP c.Ψ).X.π x)
  exact (GroupoidStr.π_eq_π_iff _).1
    (this.symm.trans (congrArg (S.modelFunctor c'.Ψ).orbitMap h))

/-- **`f^*(Γ')^*Θ = Γ^*Θ`** (2021 p. 813, printed `f_*(Γ')^*Θ = Γ^*Θ`; read with `f^*`, since
`(Γ')^*Θ` lives on `X'`). -/
theorem pullTheta_comparison_modelPull {Θ : C.Obj → ℚ} (hΘ : C.toGroupoidStr.IsFunctorial Θ) :
    pullTheta (S.comparison c c') (S.modelPull c'.Ψ Θ) = S.modelPull c.Ψ Θ := by
  funext x
  obtain ⟨y, hy⟩ := (S.modelEP c'.Ψ).X.surjective_π
    (orbitMap (S.comparison c c') ((S.modelEP c.Ψ).X.π x))
  rw [pullTheta_eq_of_orbitMap (S.isGeneralizedIso_comparison c c') (isFunctorial_modelPull hΘ)
    hy.symm]
  exact (hΘ.eq_of_isomorphic (isomorphic_of_orbitMap_comparison c c' hy.symm)).symm

/-- **`f_*Γ^*Θ = (Γ')^*Θ`** (2021 p. 814, (17.85) ff., and p. 815: `f_*(Γ^*Θ) = Γ'^*Θ`). -/
theorem pushTheta_comparison_modelPull {Θ : C.Obj → ℚ} (hΘ : C.toGroupoidStr.IsFunctorial Θ) :
    EPLoc.pushTheta (S.comparison c c') (S.modelPull c.Ψ Θ) = S.modelPull c'.Ψ Θ := by
  funext y
  obtain ⟨q, hq⟩ := (S.isHomeomorph_orbitMap_comparison c c').surjective
    ((S.modelEP c'.Ψ).X.π y)
  obtain ⟨x, rfl⟩ := (S.modelEP c.Ψ).X.surjective_π q
  rw [pushTheta_eq_of_orbitMap (S.isGeneralizedIso_comparison c c') (isFunctorial_modelPull hΘ) hq]
  exact hΘ.eq_of_isomorphic (isomorphic_of_orbitMap_comparison c c' hq)

/-- **`Γ_*Θ' = Γ'_* f_*Θ'`** (2021 p. 813) for a functor `Θ' : X → ℚ⁺`. -/
theorem modelPush_pushTheta_comparison {Θ' : (S.modelEP c.Ψ).Obj → ℚ}
    (hΘ' : (S.modelEP c.Ψ).X.IsFunctorial Θ') :
    S.modelPush c.Ψ Θ' = S.modelPush c'.Ψ (EPLoc.pushTheta (S.comparison c c') Θ') := by
  funext α
  obtain ⟨y, ψ, hs, ht⟩ := ((S.modelFunctor c'.Ψ).essSurj_iff.1 (modelFunctor_essSurj c'.cover)) α
  obtain ⟨q, hq⟩ := (S.isHomeomorph_orbitMap_comparison c c').surjective
    ((S.modelEP c'.Ψ).X.π y)
  obtain ⟨x, rfl⟩ := (S.modelEP c.Ψ).X.surjective_π q
  have hf := S.isGeneralizedIso_comparison c c'
  change (S.modelFunctor c.Ψ).pushTheta Θ' α = (S.modelFunctor c'.Ψ).pushTheta _ α
  rw [GroupoidFunctor.pushTheta_eq (S.modelFunctor_full c'.Ψ)
    (isFunctorial_pushTheta hf hΘ') ⟨ψ, hs, ht⟩, pushTheta_eq_of_orbitMap hf hΘ' hq]
  exact GroupoidFunctor.pushTheta_eq (S.modelFunctor_full c.Ψ) hΘ'
    ((isomorphic_of_orbitMap_comparison c c' hq).trans ⟨ψ, hs, ht⟩)

/-! ### Definition 17.5.3 -/

variable {c c'}

/-- `|Γ_Ψ|` maps `|supp(Γ^*Θ)|` onto `|supp(Θ)|` (for a covering family and a functor `Θ`). -/
theorem image_modelOrbitMap_orbitSupp (hc : S.IsCoveringFamily Ψ) {Θ : C.Obj → ℚ}
    (hΘ : C.toGroupoidStr.IsFunctorial Θ) :
    (S.modelFunctor Ψ).orbitMap '' (S.modelEP Ψ).X.orbitSupp (S.modelPull Ψ Θ) =
      C.toGroupoidStr.orbitSupp Θ := by
  ext z
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, hx, rfl⟩
  · rintro ⟨α, hα, rfl⟩
    obtain ⟨x, ψ, hs, ht⟩ := ((S.modelFunctor Ψ).essSurj_iff.1 (modelFunctor_essSurj hc)) α
    have hiso : C.toGroupoidStr.Isomorphic ((S.modelFunctor Ψ).obj x) α := ⟨ψ, hs, ht⟩
    refine ⟨(S.modelEP Ψ).X.π x, ⟨x, ?_, rfl⟩, ?_⟩
    · change 0 < Θ ((S.modelFunctor Ψ).obj x)
      rw [hΘ.eq_of_isomorphic hiso]
      exact hα
    · exact (GroupoidStr.π_eq_π_iff _).2 hiso

end PolyfoldConstruction

/-- **Definition 17.5.3 (1)** (2021 p. 813): `Θ` is **compact** if `|supp(Θ)|` is a compact
subset of `|C|`. -/
def IsCompactBranched (C : GCT.{u}) (Θ : C.Obj → ℚ) : Prop :=
  IsCompact (C.toGroupoidStr.orbitSupp Θ)

/-- **Definition 17.5.4 (2)** (2021 p. 813): `Θ` is of **orbifold-type** if it only takes the
values `0` and `1`. -/
def IsOrbifoldTypeBranched (C : GCT.{u}) (Θ : C.Obj → ℚ) : Prop := ∀ α, Θ α = 0 ∨ Θ α = 1

/-- **Definition 17.5.4 (1)** (2021 p. 813): `Θ` is of **manifold-type** if between two objects of
`supp(Θ)` there is at most one morphism and `Θ` only takes the values `0` and `1`. -/
def IsManifoldTypeBranched (C : GCT.{u}) (Θ : C.Obj → ℚ) : Prop :=
  C.IsOrbifoldTypeBranched Θ ∧ ∀ φ ψ : C.Mor, 0 < Θ (C.toGroupoidStr.src φ) →
    0 < Θ (C.toGroupoidStr.tgt φ) → C.toGroupoidStr.src φ = C.toGroupoidStr.src ψ →
      C.toGroupoidStr.tgt φ = C.toGroupoidStr.tgt ψ → φ = ψ

namespace PolyfoldConstruction

variable {S : C.PolyfoldConstruction}

open EPLocalization EPLocalization.EPLoc

/-- **Definition 17.5.3 (1) through a model**: `Θ` is compact iff `Γ^*Θ` is a compact branched
ep⁺-subgroupoid (Definition 9.1.6), for every covering family. -/
theorem isCompactBranched_iff_model (c : S.CoveringFamily) {Θ : C.Obj → ℚ}
    (hΘ : C.toGroupoidStr.IsFunctorial Θ) :
    C.IsCompactBranched Θ ↔ (S.modelEP c.Ψ).X.IsCompactBranched (S.modelPull c.Ψ Θ) := by
  unfold GCT.IsCompactBranched EpGroupoid.IsCompactBranched
  rw [← image_modelOrbitMap_orbitSupp c.cover hΘ]
  exact (S.modelOrbitHomeomorph c).isCompact_image

variable (S)

/-- **Definition 17.5.3 (2) for one covering family**: `Γ^*Θ` is a tame branched
ep⁺-subgroupoid of `X_Ψ` (Definition 9.3.6). -/
def IsTameVia (c : S.CoveringFamily) (Θ : C.Obj → ℚ) : Prop :=
  (S.modelEP c.Ψ).X.IsTameBranched (S.modelPull c.Ψ Θ)

/-- **Definition 17.5.3 (2)** (2021 p. 813): `Θ` is **tame** if `Γ^*Θ` is tame for a suitable
covering family. -/
def IsTameModel (Θ : C.Obj → ℚ) : Prop := ∃ c : S.CoveringFamily, S.IsTameVia c Θ

variable {S}

/-- **Definition 17.5.3 (2), well-definedness** (2021 p. 813): tameness of `Γ^*Θ` does not depend
on the covering family (`f^*` preserves tameness, Chapter 16, and `f^*(Γ')^*Θ = Γ^*Θ`). -/
theorem definition_17_5_3_two {Θ : C.Obj → ℚ} (hΘ : C.toGroupoidStr.IsFunctorial Θ)
    (c c' : S.CoveringFamily) : S.IsTameVia c Θ ↔ S.IsTameVia c' Θ := by
  have key : ∀ c c' : S.CoveringFamily, S.IsTameVia c' Θ → S.IsTameVia c Θ := fun c c' h => by
    unfold IsTameVia
    rw [← pullTheta_comparison_modelPull c c' hΘ]
    exact isTameBranched_pullTheta (S.isGeneralizedIso_comparison c c')
      (isFunctorial_modelPull hΘ) h
  exact ⟨key c' c, key c c'⟩

theorem IsTameModel.forall {Θ : C.Obj → ℚ} (hΘ : C.toGroupoidStr.IsFunctorial Θ)
    (h : S.IsTameModel Θ) (c : S.CoveringFamily) : S.IsTameVia c Θ := by
  obtain ⟨c₀, h₀⟩ := h
  exact (definition_17_5_3_two hΘ c₀ c).1 h₀

/-! ### Definition 17.5.4 -/

variable (S)

/-- **Definition 17.5.4 (3)** (2021 p. 813): `Θ` is **tame** if for `α ∈ supp(Θ)` and `Ψ ∈ F(α)`
the functor `Θ ∘ Ψ` is a tame branched ep⁺-subgroupoid. -/
def IsTameSubcategory (Θ : C.Obj → ℚ) : Prop :=
  ∀ α, 0 < Θ α → ∀ Ψ ∈ S.F α, Ψ.ep.IsTameBranched (Θ ∘ Ψ.obj)

variable {S}

/-- **The first step of the proof of Proposition 17.5.5, orbifold-type** (2021 p. 814):
`Θ ∘ Γ` is of orbifold-type (Definition 9.1.8) iff `Θ` is (Definition 17.5.4). -/
theorem isOrbifoldType_modelPull_iff (c : S.CoveringFamily) {Θ : C.Obj → ℚ}
    (hΘ : C.toGroupoidStr.IsFunctorial Θ) :
    EpGroupoid.IsOrbifoldType (S.modelPull c.Ψ Θ) ↔ C.IsOrbifoldTypeBranched Θ := by
  constructor
  · intro h α
    obtain ⟨x, ψ, hs, ht⟩ := ((S.modelFunctor c.Ψ).essSurj_iff.1 (modelFunctor_essSurj c.cover)) α
    rw [← hΘ.eq_of_isomorphic ⟨ψ, hs, ht⟩]
    exact h x
  · intro h x
    exact h _

/-- **The first step of the proof of Proposition 17.5.5, manifold-type** (2021 p. 814):
`Θ ∘ Γ` is of manifold-type (Definition 9.1.8) iff `Θ` is (Definition 17.5.4); `Γ` is full and
faithful, and every object of `C` is isomorphic to some `Γ(x)`. -/
theorem isManifoldType_modelPull_iff (c : S.CoveringFamily) {Θ : C.Obj → ℚ}
    (hΘ : C.toGroupoidStr.IsFunctorial Θ) :
    (S.modelEP c.Ψ).X.IsManifoldType (S.modelPull c.Ψ Θ) ↔ C.IsManifoldTypeBranched Θ := by
  have hfull := ((S.modelFunctor c.Ψ).full_iff).1 (S.modelFunctor_full c.Ψ)
  have hfaith := ((S.modelFunctor c.Ψ).faithful_iff).1 (S.modelFunctor_faithful c.Ψ)
  have hess := ((S.modelFunctor c.Ψ).essSurj_iff).1 (modelFunctor_essSurj c.cover)
  set G := C.toGroupoidStr
  constructor
  · rintro ⟨ho, hm⟩
    refine ⟨(isOrbifoldType_modelPull_iff c hΘ).1 ho, fun φ ψ h1 h2 hs ht => ?_⟩
    obtain ⟨x, χ, hχs, hχt⟩ := hess (G.src φ)
    obtain ⟨y, χ', hχ's, hχ't⟩ := hess (G.tgt φ)
    have hφχ : G.src φ = G.tgt χ := hχt.symm
    have hψχ : G.src ψ = G.tgt χ := hs ▸ hχt.symm
    have hφc : G.src (G.inv χ') = G.tgt (G.comp φ χ) := by
      rw [G.src_inv, G.tgt_comp _ _ hφχ, hχ't]
    have hψc : G.src (G.inv χ') = G.tgt (G.comp ψ χ) := by
      rw [G.src_inv, G.tgt_comp _ _ hψχ, hχ't, ht]
    have hsrc : ∀ {θ}, G.src θ = G.tgt χ → G.tgt θ = G.tgt φ →
        G.src (G.comp (G.inv χ') (G.comp θ χ)) = (S.modelFunctor c.Ψ).obj x ∧
          G.tgt (G.comp (G.inv χ') (G.comp θ χ)) = (S.modelFunctor c.Ψ).obj y := fun {θ} h h' => by
      have hc : G.src (G.inv χ') = G.tgt (G.comp θ χ) := by
        rw [G.src_inv, G.tgt_comp _ _ h, hχ't, h']
      rw [G.src_comp _ _ hc, G.src_comp _ _ h, G.tgt_comp _ _ hc, G.tgt_inv, hχs, hχ's]
      exact ⟨rfl, rfl⟩
    obtain ⟨hs1, ht1⟩ := hsrc hφχ rfl
    obtain ⟨hs2, ht2⟩ := hsrc hψχ ht.symm
    obtain ⟨φ₁, hφ₁s, hφ₁t, hφ₁⟩ := hfull x y _ hs1 ht1
    obtain ⟨ψ₁, hψ₁s, hψ₁t, hψ₁⟩ := hfull x y _ hs2 ht2
    have hx : (S.modelEP c.Ψ).X.src φ₁ ∈ EpGroupoid.supp (S.modelPull c.Ψ Θ) := by
      change 0 < Θ ((S.modelFunctor c.Ψ).obj ((S.modelEP c.Ψ).X.src φ₁))
      rw [hφ₁s, hΘ.eq_of_isomorphic ⟨χ, hχs, hχt⟩]
      exact h1
    have hy : (S.modelEP c.Ψ).X.tgt φ₁ ∈ EpGroupoid.supp (S.modelPull c.Ψ Θ) := by
      change 0 < Θ ((S.modelFunctor c.Ψ).obj ((S.modelEP c.Ψ).X.tgt φ₁))
      rw [hφ₁t, hΘ.eq_of_isomorphic ⟨χ', hχ's, hχ't⟩]
      exact h2
    have he := hm φ₁ ψ₁ hx hy (hφ₁s.trans hψ₁s.symm) (hφ₁t.trans hψ₁t.symm)
    have h3 : G.comp (G.inv χ') (G.comp φ χ) = G.comp (G.inv χ') (G.comp ψ χ) := by
      rw [← hφ₁, ← hψ₁, he]
    exact G.comp_right_cancel hφχ hψχ (G.comp_left_cancel hφc hψc h3)
  · rintro ⟨ho, hm⟩
    refine ⟨(isOrbifoldType_modelPull_iff c hΘ).2 ho, fun φ ψ h1 h2 hs ht => ?_⟩
    refine hfaith φ ψ hs ht (hm _ _ ?_ ?_ ?_ ?_)
    · rw [(S.modelFunctor c.Ψ).src_mor]; exact (h1 : 0 < Θ ((S.modelFunctor c.Ψ).obj _))
    · rw [(S.modelFunctor c.Ψ).tgt_mor]; exact (h2 : 0 < Θ ((S.modelFunctor c.Ψ).obj _))
    · rw [(S.modelFunctor c.Ψ).src_mor, (S.modelFunctor c.Ψ).src_mor, hs]
    · rw [(S.modelFunctor c.Ψ).tgt_mor, (S.modelFunctor c.Ψ).tgt_mor, ht]

/-- **Definition 17.5.4 (3), "equivalently"** (2021 p. 813): under the standing reading
`F(α) ≠ ∅` (`HasUniformizers`), `Θ` is tame in the sense of 17.5.4 (3) (through the uniformizers)
iff `Θ ∘ Γ` is a tame branched ep⁺-subgroupoid of the model of a covering family (Definition
17.5.3 (2)).  Tame sheets are moved along transition sets and summand inclusions;
`EpGroupoid.isTameBranched_iff_exists` supplies the natural representations. -/
theorem definition_17_5_4_three (hU : S.HasUniformizers) {Θ : C.Obj → ℚ}
    (hΘ : C.toGroupoidStr.IsFunctorial Θ) (c : S.CoveringFamily) :
    S.IsTameSubcategory Θ ↔ S.IsTameVia c Θ := by
  unfold IsTameVia
  refine Iff.trans ?_
    (EpGroupoid.isTameBranched_iff_exists (S.modelEP c.Ψ).X (S.modelPull c.Ψ Θ)).symm
  constructor
  · rintro h ⟨i, q⟩ hx
    set α := (c.Ψ i).1.obj q
    have hα : 0 < Θ α := hx
    obtain ⟨Ψ', hΨ'⟩ := hU α
    obtain ⟨q', hq'⟩ := S.isAt α Ψ' hΨ'
    have ht := (EpGroupoid.isTameBranched_iff_exists _ _).1 (h α hα Ψ' hΨ') q'
      (show 0 < Θ (Ψ'.obj q') from (congrArg Θ hq').symm ▸ hα)
    obtain ⟨B, hB⟩ := ht
    let Φ : S.Unif := ⟨Ψ', α, hΨ'⟩
    let a : S.Tr (c.Ψ i) Φ :=
      ⟨q, C.toGroupoidStr.unit α, q', C.toGroupoidStr.src_unit α,
        (C.toGroupoidStr.tgt_unit α).trans hq'.symm⟩
    obtain ⟨B₁, hB₁⟩ := localBranching_of_tr (Ψ' := Φ) hΘ a B
    obtain ⟨B₂, hB₂⟩ := localBranching_of_summand (S := S) (Ψ := c.Ψ) i q B₁
    exact ⟨B₂, hB₂ (hB₁ hB)⟩
  · intro h α _ Ψ hΨ
    rw [EpGroupoid.isTameBranched_iff_exists]
    intro q hq
    obtain ⟨i, a, rfl⟩ := exists_tr_of_isCoveringFamily c.cover (⟨Ψ, α, hΨ⟩ : S.Unif) q
    have hx : (⟨i, a.tgt⟩ : S.ModelObj c.Ψ) ∈ EpGroupoid.supp (S.modelPull c.Ψ Θ) := by
      change 0 < Θ ((c.Ψ i).1.obj a.tgt)
      rw [theta_tgt_eq hΘ a]
      exact hq
    obtain ⟨B, hB⟩ := h _ hx
    obtain ⟨B₁, hB₁⟩ := localBranching_summand (S := S) (Ψ := c.Ψ) i a.tgt B
    obtain ⟨B₂, hB₂⟩ := localBranching_of_tr hΘ a B₁
    exact ⟨B₂, hB₂ (hB₁ hB)⟩

end PolyfoldConstruction

end GCT

end Polyfold
