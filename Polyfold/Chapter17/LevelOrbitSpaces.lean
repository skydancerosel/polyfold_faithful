import Polyfold.Chapter17.LevelStructuresExamples

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.1 (pp. 765–766): the natural topology of `|C_i|` for every level `i`, transported from
`|X_Ψ^i|` (the paragraph before **Theorem 17.1.28**), and its comparison with the levels
`C^{i+1} := (C^i)¹` after **Corollary 17.1.29**.  Numbers and pages are the 2021 text's.

# The orbit spaces `|C_i|` and `|X_Ψ^i|`

## The text, paraphrased

(p. 766) The equivalence `Γ_Ψ : X_Ψ → C` induces the homeomorphism `|Γ_Ψ| : |X_Ψ| → |C|`.  With
`X := X_Ψ`, `|X|` is metrizable, hence paracompact and Hausdorff; so `|X^i|` is paracompact,
Hausdorff and locally metrizable, therefore metrizable, and consequently `|C_i|` has a natural
metrizable topology (Section 7.3).  After Corollary 17.1.29: `C^{i+1} := (C^i)¹`.

## What is formalized

* `EP.liftInclLevel A i : Xⁱ → X` (the composite of the inclusions `X^{j+1} → X^j`), with
  `liftInclLevel_obj_mem` (a point of level `m` of `Xⁱ` is a point of level `m + i` of `X`),
  `exists_liftInclLevel_obj_eq` (every point of `X_{m+i}` comes from a point of level `m` of
  `Xⁱ`), `orbitMap_liftInclLevel_succ`, `injective_orbitMap_liftInclLevel` (`|Xⁱ| → |X|` is
  injective), `hasParacompactOrbitSpace_lift`, `metrizableSpace_lift_orbitSpace` (the text's
  route: `|X|` paracompact gives `|Xⁱ|` metrizable), `isZhou_lift` ((ZHOU) passes to `Xⁱ`).
* `EPLoc.liftHomLevel f i : Xⁱ → Yⁱ` (the `i`-fold index raise of a generalized map),
  `isGeneralizedIso_liftHomLevel`, `orbitMap_liftInclLevel_liftHomLevel`
  (`|Yⁱ → Y| ∘ |fⁱ| = |f| ∘ |Xⁱ → X|`), `orbitMap_localizationFunctor_map_π`.
* `modelFunctorLevel Ψ i : X_Ψ^i → C_i` (the functor `Γ_Ψ` on the points of level `i`),
  `orbitIncl_modelFunctorLevel` (`|C_i → C| ∘ |Γ_Ψ^i| = |Γ_Ψ| ∘ |X_Ψ^i → X_Ψ|`),
  `bijective_orbitMap_modelFunctorLevel` (a covering family), `modelFunctorLevel_one` (for
  `i = 1` it is `modelFunctorOne`), `modelOrbitLevel_eq_comp`
  (`|Γ_Ψ^i| = |Γ_Ψ'^i| ∘ |f_{Ψ,Ψ'}^i|` for two covering families).
* Namespace `GCT.UniformizedPolyfold`: `exists_levelModel_comparison` (for every covering family
  `Ψ` of `F` and every `i` there are a covering family `L` of `F^i` and a generalized isomorphism
  `X_Ψ^i → X_L` over `C`); **`isHomeomorph_modelOrbitLevel`**: for every covering family `Ψ` and
  every `i`, `|Γ_Ψ^i| : |X_Ψ^i| → |C_i|` is a homeomorphism for the topology of `|C_i|`
  transported from the GCT `C^i` (`levelTopology`); **`levelTopology_eq_coinduced`** (that
  topology is the one transported from `|X_Ψ^i|`, for every covering family);
  `modelOrbitHomeomorphLevel`, `modelOrbitHomeomorphLevelCat` (`|X_Ψ^i| ≃ₜ |C^i|`),
  `levelPolyfoldStructure` (under (ZHOU) for `X_Ψ`: `(X_Ψ^i, |Γ_Ψ^i|)` is a polyfold structure on
  `|C^i|`, Definition 16.1.1), `levelPolyfoldStructure_equiv`, and the summary
  **`theorem_17_1_28_levels`**.
* Witness: `z3Uniformized_levelOrbit` (for `ℤ/3 ⋉ ℝ`, all of `ℤ/3` the isotropy of every point:
  `|Γ_Ψ^2|` is a homeomorphism onto a non-empty `|C_2|`).

## Readings

* "`|C_i|` has a natural metrizable topology" is read as: the topology transported from
  `|X_Ψ^i|` along `|Γ_Ψ^i|` for a covering family `Ψ`; it does not depend on `Ψ`
  (`modelOrbitLevel_eq_comp` and `levelTopology_eq_coinduced`).  The levels `C^i` of
  `LevelStructures.lean` carry the topology of the GCT `(C^{i-1})¹`; `levelTopology_eq_coinduced`
  shows that the two agree for every `i` (for `i = 1` this is `levelTopology_one`).
* `X^i` is `EP.lift` (`X^{i+1} = (X^i)¹`), and `X_Ψ^i → X_Ψ` is the composite of the inclusions
  of Section 7.3.
* The comparison for `i + 1` passes through Corollary 17.1.29: a covering family `L` of `F^{i+1}`
  has a model `X_L` generalized isomorphic to `(X_Φ)¹` for a covering family `Φ` of `F^i`
  (`levelOneModelHom`), and `X_Φ` is generalized isomorphic to `X_Ψ^i` by induction.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology TopologicalSpace CategoryTheory

noncomputable section

universe u

namespace Polyfold

open EPLocalization EPLocalization.EPLoc

/-! ### The inclusion `Xⁱ → X` -/

namespace EP

/-- **The inclusion `Xⁱ → X`** (2021 p. 329, Section 7.3): the composite of the inclusions
`X^{j+1} = (X^j)¹ → X^j`. -/
def liftInclLevel (A : EP.{u}) : ∀ i, GroupoidFunctor (A.lift i).X.toGroupoidStr A.X.toGroupoidStr
  | 0 => GroupoidFunctor.id _
  | i + 1 => (liftInclLevel A i).comp (A.lift i).X.liftIncl

theorem liftInclLevel_succ_obj (A : EP.{u}) (i : ℕ) (x : (A.lift (i + 1)).Obj) :
    (A.liftInclLevel (i + 1)).obj x =
      (A.liftInclLevel i).obj ((A.lift i).X.PObj.levelVal 1 x) :=
  rfl

/-- **A point of level `m` of `Xⁱ` is a point of level `m + i` of `X`.** -/
theorem liftInclLevel_obj_mem (A : EP.{u}) : ∀ (i m : ℕ) (x : (A.lift i).Obj),
    x ∈ (A.lift i).X.PObj.levelSet m → (A.liftInclLevel i).obj x ∈ A.X.PObj.levelSet (m + i)
  | 0, _, _, hx => hx
  | i + 1, m, x, hx => by
    have h1 : (A.lift i).X.PObj.levelVal 1 x ∈ (A.lift i).X.PObj.levelSet (m + 1) :=
      (MPolyfold.mem_shift_levelSet_iff (PX := (A.lift i).X.PObj) x).1 hx
    have h2 := liftInclLevel_obj_mem A i (m + 1) _ h1
    rwa [show m + 1 + i = m + (i + 1) by omega] at h2

/-- **The points of `Xⁱ` lie on level `i` of `X`.** -/
theorem liftInclLevel_obj_mem_level (A : EP.{u}) (i : ℕ) (x : (A.lift i).Obj) :
    (A.liftInclLevel i).obj x ∈ A.X.PObj.levelSet i := by
  have h := A.liftInclLevel_obj_mem i 0 x (by rw [MPolyfold.levelSet_zero]; exact mem_univ x)
  rwa [Nat.zero_add] at h

/-- **Every point of `X_{m+i}` comes from a point of level `m` of `Xⁱ`.** -/
theorem exists_liftInclLevel_obj_eq (A : EP.{u}) : ∀ (i m : ℕ) (x : A.Obj),
    x ∈ A.X.PObj.levelSet (m + i) →
      ∃ y : (A.lift i).Obj, y ∈ (A.lift i).X.PObj.levelSet m ∧ (A.liftInclLevel i).obj y = x
  | 0, _, x, hx => ⟨x, hx, rfl⟩
  | i + 1, m, x, hx => by
    obtain ⟨y, hy, rfl⟩ := exists_liftInclLevel_obj_eq A i (m + 1) x
      (by rwa [show m + 1 + i = m + (i + 1) by omega])
    have hy1 : y ∈ (A.lift i).X.PObj.levelSet 1 :=
      (A.lift i).X.PObj.levelSet_antitone (by omega : 1 ≤ m + 1) hy
    refine ⟨(A.lift i).X.PObj.levelMk 1 y hy1, ?_, rfl⟩
    exact (MPolyfold.mem_shift_levelSet_iff (PX := (A.lift i).X.PObj) _).2 hy

/-- `|X^{i+1} → X| = |Xⁱ → X| ∘ |X^{i+1} → Xⁱ|`. -/
theorem orbitMap_liftInclLevel_succ (A : EP.{u}) (i : ℕ) :
    (A.liftInclLevel (i + 1)).orbitMap = (A.liftInclLevel i).orbitMap ∘ (A.lift i).X.orbitIncl := by
  funext z
  induction z using Quotient.inductionOn with
  | h x => rfl

/-- **`|Xⁱ| → |X|` is injective** (Section 7.3, iterated). -/
theorem injective_orbitMap_liftInclLevel (A : EP.{u}) : ∀ i,
    Injective (A.liftInclLevel i).orbitMap
  | 0 => by
    intro a b h
    induction a using Quotient.inductionOn with | h x => ?_
    induction b using Quotient.inductionOn with | h y => exact h
  | i + 1 => by
    rw [orbitMap_liftInclLevel_succ]
    exact (injective_orbitMap_liftInclLevel A i).comp (A.lift i).X.orbitIncl_injective

/-- **`|Xⁱ|` is paracompact** if `|X|` is (Proposition 7.5.3, iterated). -/
theorem hasParacompactOrbitSpace_lift (A : EP.{u}) (h : A.X.HasParacompactOrbitSpace) :
    ∀ i, (A.lift i).X.HasParacompactOrbitSpace
  | 0 => h
  | i + 1 => (A.lift i).X.proposition_7_5_3 (hasParacompactOrbitSpace_lift A h i)

/-- **`|Xⁱ|` is metrizable** if `|X|` is paracompact (2021 p. 766: "`|X^i|` is paracompact,
Hausdorff and locally metrizable, and therefore metrizable"; Section 7.3). -/
theorem metrizableSpace_lift_orbitSpace (A : EP.{u}) (h : A.X.HasParacompactOrbitSpace) (i : ℕ) :
    MetrizableSpace (A.lift (i + 1)).X.OrbitSpace :=
  (A.lift i).X.metrizableSpace_liftOne_orbitSpace (A.hasParacompactOrbitSpace_lift h i)

/-- **(ZHOU) passes to `Xⁱ`** (Propositions 7.4.8, 7.4.9, iterated). -/
theorem isZhou_lift (A : EP.{u}) (h : A.X.IsZhou) : ∀ i, (A.lift i).X.IsZhou
  | 0 => h
  | i + 1 => (A.lift i).X.liftOne.proposition_7_4_8_unconditional.2
    ((A.lift i).X.isZhou'_liftOne
      ((A.lift i).X.proposition_7_4_8_unconditional.1 (isZhou_lift A h i)))

end EP

/-! ### The `i`-fold index raise of a generalized map -/

namespace EPLocalization.EPLoc

variable {X Y : EP.{u}}

/-- **The orbit map of `[Φ]` for an ep-functor `Φ`** is `|Φ|`. -/
theorem orbitMap_localizationFunctor_map_π {A B : EP.{u}} (Φ : A ⟶ B) (x : A.Obj) :
    orbitMap (localizationFunctor.map Φ) (A.X.π x) = B.X.π (Φ.obj x) := by
  have h := (Diagram.ofFunctor Φ).orbitMap_orbitMap_F (A.X.π x)
  change (Diagram.ofFunctor Φ).orbitMap ((EpFunctor.id A.X).orbitMap (A.X.π x)) =
    Φ.orbitMap (A.X.π x) at h
  rw [EpFunctor.orbitMap_id, GroupoidFunctor.orbitMap_π] at h
  exact h

/-- **`fⁱ : Xⁱ → Yⁱ`**, the `i`-fold index raise of a generalized map (`f^{i+1} = (fⁱ)¹`). -/
def liftHomLevel (f : of X ⟶ of Y) : ∀ i, of (X.lift i) ⟶ of (Y.lift i)
  | 0 => f
  | i + 1 => liftOneHom (liftHomLevel f i)

/-- The raises of a generalized isomorphism are generalized isomorphisms. -/
theorem isGeneralizedIso_liftHomLevel {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) :
    ∀ i, IsGeneralizedIso (liftHomLevel f i)
  | 0 => hf
  | i + 1 => isGeneralizedIso_liftOneHom (isGeneralizedIso_liftHomLevel hf i)

/-- **`|fⁱ|` is `|f|` on `|Xⁱ| ⊆ |X|`**: `|Yⁱ → Y| ∘ |fⁱ| = |f| ∘ |Xⁱ → X|`. -/
theorem orbitMap_liftInclLevel_liftHomLevel (f : of X ⟶ of Y) : ∀ i,
    (Y.liftInclLevel i).orbitMap ∘ orbitMap (liftHomLevel f i) =
      orbitMap f ∘ (X.liftInclLevel i).orbitMap
  | 0 => by
    funext z
    have hX : (X.liftInclLevel 0).orbitMap z = z := by
      induction z using Quotient.inductionOn with | h x => rfl
    have hY : ∀ w, (Y.liftInclLevel 0).orbitMap w = w := fun w => by
      induction w using Quotient.inductionOn with | h x => rfl
    exact (hY _).trans (congrArg (orbitMap f) hX.symm)
  | i + 1 => by
    funext z
    have h1 := congrFun (orbitIncl_orbitMap_liftOneHom (liftHomLevel f i)) z
    have h2 := congrFun (orbitMap_liftInclLevel_liftHomLevel f i) ((X.lift i).X.orbitIncl z)
    have h3 := congrFun (EP.orbitMap_liftInclLevel_succ Y i) (orbitMap (liftHomLevel f (i + 1)) z)
    have h4 := congrFun (EP.orbitMap_liftInclLevel_succ X i) z
    simp only [Function.comp_apply] at h1 h2 h3 h4
    exact h3.trans ((congrArg (Y.liftInclLevel i).orbitMap h1).trans
      (h2.trans (congrArg (orbitMap f) h4.symm)))

end EPLocalization.EPLoc

/-! ### The functor `Γ_Ψ^i : X_Ψ^i → C_i` -/

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} (S : C.PolyfoldConstruction) {ι : Type u} (Ψ : ι → S.Unif)

/-- **`Γ_Ψ^i : X_Ψ^i → C_i`** (2021 p. 766): `Γ_Ψ` on the points of level `i` (they have
regularity `i`). -/
def modelFunctorLevel (i : ℕ) :
    GroupoidFunctor ((S.modelEP Ψ).lift i).X.toGroupoidStr (S.regSub i) :=
  ((S.modelFunctor Ψ).comp ((S.modelEP Ψ).liftInclLevel i)).corestrict (S.regSet i) fun x =>
    (S.hasRegularity_modelFunctor_obj Ψ _ i).2 ((S.modelEP Ψ).liftInclLevel_obj_mem_level i x)

/-- `|C_i → C| ∘ |Γ_Ψ^i| = |Γ_Ψ| ∘ |X_Ψ^i → X_Ψ|`. -/
theorem orbitIncl_modelFunctorLevel (i : ℕ) :
    (C.toGroupoidStr.fullSubInclusion (S.regSet i)).orbitMap ∘
        (S.modelFunctorLevel Ψ i).orbitMap =
      (S.modelFunctor Ψ).orbitMap ∘ ((S.modelEP Ψ).liftInclLevel i).orbitMap := by
  funext z
  induction z using Quotient.inductionOn with
  | h x => rfl

/-- For `i = 1`, `|Γ_Ψ^i|` is `|Γ_Ψ¹|` of Theorem 17.1.28 (`modelFunctorOne`). -/
theorem modelFunctorLevel_one :
    (S.modelFunctorLevel Ψ 1).orbitMap = (S.modelFunctorOne Ψ).orbitMap := by
  funext z
  induction z using Quotient.inductionOn with
  | h x => rfl

/-- **`|Γ_Ψ^i| : |X_Ψ^i| → |C_i|` is bijective** for a covering family. -/
theorem bijective_orbitMap_modelFunctorLevel (c : S.CoveringFamily) (i : ℕ) :
    Bijective (S.modelFunctorLevel c.Ψ i).orbitMap := by
  have hΓ := (S.lemma_17_1_15 c).2
  refine ⟨fun a b h => ?_, fun z => ?_⟩
  · have h' := congrArg (C.toGroupoidStr.fullSubInclusion (S.regSet i)).orbitMap h
    simp only [← Function.comp_apply
      (f := (C.toGroupoidStr.fullSubInclusion (S.regSet i)).orbitMap),
      orbitIncl_modelFunctorLevel] at h'
    exact (S.modelEP c.Ψ).injective_orbitMap_liftInclLevel i (hΓ.injective h')
  · induction z using Quotient.inductionOn with
    | h α => ?_
    obtain ⟨w, hw⟩ := hΓ.surjective (C.toGroupoidStr.π α.1)
    induction w using Quotient.inductionOn with
    | h x => ?_
    have hiso : C.toGroupoidStr.Isomorphic ((S.modelFunctor c.Ψ).obj x) α.1 :=
      (C.toGroupoidStr.π_eq_π_iff).1 hw
    have hx : x ∈ (S.modelEP c.Ψ).X.PObj.levelSet (0 + i) := by
      rw [Nat.zero_add]
      exact (S.hasRegularity_modelFunctor_obj c.Ψ x i).1 (α.2.of_isomorphic hiso.symm)
    obtain ⟨y, -, hy⟩ := (S.modelEP c.Ψ).exists_liftInclLevel_obj_eq i 0 x hx
    refine ⟨((S.modelEP c.Ψ).lift i).X.π y, ?_⟩
    refine ((S.regSub i).π_eq_π_iff).2 (GroupoidStr.isomorphic_fullSub_iff.2 ?_)
    change C.toGroupoidStr.Isomorphic ((S.modelFunctor c.Ψ).obj
      (((S.modelEP c.Ψ).liftInclLevel i).obj y)) α.1
    rw [hy]
    exact hiso

/-- **`|Γ_Ψ^i| = |Γ_Ψ'^i| ∘ |f_{Ψ,Ψ'}^i|`** for two covering families (`f^i` the `i`-fold index
raise of the comparison of Theorem 17.1.18). -/
theorem modelOrbitLevel_eq_comp (c c' : S.CoveringFamily) (i : ℕ) :
    (S.modelFunctorLevel c.Ψ i).orbitMap =
      (S.modelFunctorLevel c'.Ψ i).orbitMap ∘ orbitMap (liftHomLevel (S.comparison c c') i) := by
  funext z
  apply C.toGroupoidStr.injective_orbitMap_fullSubInclusion (S.regSet i)
  have h1 := congrFun (S.orbitIncl_modelFunctorLevel c.Ψ i) z
  have h2 := congrFun (S.orbitIncl_modelFunctorLevel c'.Ψ i)
    (orbitMap (liftHomLevel (S.comparison c c') i) z)
  have h3 := congrFun (orbitMap_liftInclLevel_liftHomLevel (S.comparison c c') i) z
  have h4 := congrFun (S.orbitMap_comparison c c') (((S.modelEP c.Ψ).liftInclLevel i).orbitMap z)
  simp only [Function.comp_apply] at h1 h2 h3 ⊢
  rw [h1, h2, h3]
  exact h4.symm

end GCT.PolyfoldConstruction

/-! ### The levels `C^i` and the models `X_Ψ^i` -/

namespace GCT.UniformizedPolyfold

variable (X : GCT.UniformizedPolyfold.{u})

/-- `|C^i| → |C|` is `|C_i → C|` after `|C^i| ≃ |C_i|`. -/
theorem orbitIncl_levelOrbitEquiv (i : ℕ) :
    (X.cat.toGroupoidStr.fullSubInclusion (X.str.regSet i)).orbitMap ∘ X.levelOrbitEquiv i =
      (X.levelIncl i).orbitMap :=
  GroupoidFunctor.orbitMap_fullSubInclusion_corestrict _ _ _

/-- **The comparison of `X_Ψ^i` with a model of `C^i`**: for every covering family `Ψ` of `F`
and every `i`, there are a covering family `L` of `F^i` and a generalized isomorphism
`f : X_Ψ^i → X_L` with `|C^i → C| ∘ |Γ_L| ∘ |f| = |Γ_Ψ| ∘ |X_Ψ^i → X_Ψ|`. -/
theorem exists_levelModel_comparison : ∀ (i : ℕ) (c : X.str.CoveringFamily),
    ∃ (d : (X.level i).str.CoveringFamily)
      (f : of ((X.str.modelEP c.Ψ).lift i) ⟶ of ((X.level i).str.modelEP d.Ψ)),
      IsGeneralizedIso f ∧
        (X.levelIncl i).orbitMap ∘ ((X.level i).str.modelFunctor d.Ψ).orbitMap ∘ orbitMap f =
          (X.str.modelFunctor c.Ψ).orbitMap ∘ ((X.str.modelEP c.Ψ).liftInclLevel i).orbitMap
  | 0, c => by
    refine ⟨c, 𝟙 _, ⟨𝟙 _, Category.id_comp _, Category.id_comp _⟩, ?_⟩
    funext z
    have h0 : ∀ w, (X.levelIncl 0).orbitMap w = w := fun w => by
      induction w using Quotient.inductionOn with | h x => rfl
    have h1 : ((X.str.modelEP c.Ψ).liftInclLevel 0).orbitMap z = z := by
      induction z using Quotient.inductionOn with | h x => rfl
    have hid : orbitMap (𝟙 (of ((X.str.modelEP c.Ψ).lift 0))) z = z :=
      congrFun (orbitMap_id _) z
    exact (h0 _).trans (congrArg (X.str.modelFunctor c.Ψ).orbitMap (hid.trans h1.symm))
  | i + 1, c => by
    obtain ⟨d, f, hf, hfc⟩ := exists_levelModel_comparison i c
    let T := (X.level i).str
    let hc := (X.level i).hasCoveringUniformizers
    obtain ⟨L⟩ := (X.level (i + 1)).str.exists_coveringFamily_iff.2
      (X.level (i + 1)).hasCoveringUniformizers
    let L' : (T.levelOneConstruction hc).CoveringFamily := L
    let e := T.levelOneModelFamily hc L' d
    let g : of ((X.level (i + 1)).str.modelEP L.Ψ) ⟶ of (T.modelEP e.Ψ).liftOne :=
      localizationFunctor.map (T.levelOneModelHom hc L' d)
    obtain ⟨g', hgg', hg'g⟩ := T.isGeneralizedIso_levelOneModelHom hc L' d
    let g'' : of (T.modelEP e.Ψ).liftOne ⟶ of ((X.level (i + 1)).str.modelEP L.Ψ) := g'
    have hg'' : g'' ≫ g = 𝟙 _ := hg'g
    let k : of (T.modelEP d.Ψ) ⟶ of (T.modelEP e.Ψ) := T.comparisonOf d e
    have hk : IsGeneralizedIso k := T.isGeneralizedIso_comparison d e
    have hcomp : IsGeneralizedIso (liftOneHom f ≫ liftOneHom k ≫ g'') := by
      have h1 := (isGeneralizedIso_iff_isIso _).1 (isGeneralizedIso_liftOneHom hf)
      have h2 := (isGeneralizedIso_iff_isIso _).1 (isGeneralizedIso_liftOneHom hk)
      have h3 : IsIso g'' := ⟨⟨g, hg'', hgg'⟩⟩
      exact (isGeneralizedIso_iff_isIso _).2 inferInstance
    refine ⟨L, liftOneHom f ≫ liftOneHom k ≫ g'', hcomp, ?_⟩
    funext z
    -- the level-one step: `|C^{i+1} → C| ∘ |Γ_L| = |C^i → C| ∘ |Γ_e| ∘ |X_e¹ → X_e| ∘ |g|`
    have K1 : ∀ w, (X.levelIncl (i + 1)).orbitMap
          (((X.level (i + 1)).str.modelFunctor L.Ψ).orbitMap w) =
        (X.levelIncl i).orbitMap ((T.modelFunctor e.Ψ).orbitMap
          ((T.modelEP e.Ψ).X.orbitIncl (orbitMap g w))) := by
      intro w
      induction w using Quotient.inductionOn with
      | h x =>
        have hg : orbitMap g (((X.level (i + 1)).str.modelEP L.Ψ).X.π x) =
            (T.modelEP e.Ψ).liftOne.X.π (T.lFunObj hc L' d x) :=
          orbitMap_localizationFunctor_map_π _ x
        refine Eq.trans ?_ (congrArg (fun w => (X.levelIncl i).orbitMap
          ((T.modelFunctor e.Ψ).orbitMap ((T.modelEP e.Ψ).X.orbitIncl w))) hg).symm
        exact congrArg (fun a => X.cat.toGroupoidStr.π ((X.levelIncl i).obj a))
          (T.modelObjMap_lFunObj hc L' d x).symm
    let a := orbitMap (liftOneHom f) z
    let b := orbitMap (liftOneHom k) a
    have hc3 : orbitMap (liftOneHom f ≫ liftOneHom k ≫ g'') z = orbitMap g'' b := by
      rw [proposition_10_3_11, proposition_10_3_11]
      rfl
    have hgw : orbitMap g (orbitMap g'' b) = b := by
      have h := congrFun (proposition_10_3_11 g'' g) b
      rw [hg'', orbitMap_id] at h
      exact h.symm
    have hk1 : (T.modelEP e.Ψ).X.orbitIncl b = orbitMap k ((T.modelEP d.Ψ).X.orbitIncl a) :=
      congrFun (orbitIncl_orbitMap_liftOneHom k) a
    have hf1 : (T.modelEP d.Ψ).X.orbitIncl a =
        orbitMap f (((X.str.modelEP c.Ψ).lift i).X.orbitIncl z) :=
      congrFun (orbitIncl_orbitMap_liftOneHom f) z
    have hΓ : ∀ y, (T.modelFunctor e.Ψ).orbitMap (orbitMap k y) = (T.modelFunctor d.Ψ).orbitMap y :=
      fun y => congrFun (T.orbitMap_comparison d e) y
    have hfz := congrFun hfc (((X.str.modelEP c.Ψ).lift i).X.orbitIncl z)
    have hsucc := congrFun ((X.str.modelEP c.Ψ).orbitMap_liftInclLevel_succ i) z
    refine (congrArg (fun w => (X.levelIncl (i + 1)).orbitMap
      (((X.level (i + 1)).str.modelFunctor L.Ψ).orbitMap w)) hc3).trans ?_
    refine (K1 _).trans ?_
    refine (congrArg (fun w => (X.levelIncl i).orbitMap ((T.modelFunctor e.Ψ).orbitMap
      ((T.modelEP e.Ψ).X.orbitIncl w))) hgw).trans ?_
    refine (congrArg (fun w => (X.levelIncl i).orbitMap ((T.modelFunctor e.Ψ).orbitMap w))
      hk1).trans ?_
    refine (congrArg (X.levelIncl i).orbitMap (hΓ _)).trans ?_
    refine (congrArg (fun w => (X.levelIncl i).orbitMap ((T.modelFunctor d.Ψ).orbitMap w))
      hf1).trans ?_
    exact hfz.trans (congrArg (X.str.modelFunctor c.Ψ).orbitMap hsucc.symm)

/-- **`|Γ_Ψ^i| = (|C^i| ≃ |C_i|) ∘ |Γ_L| ∘ |f|`** for the data of
`exists_levelModel_comparison`. -/
theorem modelFunctorLevel_eq_comp (i : ℕ) (c : X.str.CoveringFamily)
    (d : (X.level i).str.CoveringFamily)
    (f : of ((X.str.modelEP c.Ψ).lift i) ⟶ of ((X.level i).str.modelEP d.Ψ))
    (hfc : (X.levelIncl i).orbitMap ∘ ((X.level i).str.modelFunctor d.Ψ).orbitMap ∘ orbitMap f =
          (X.str.modelFunctor c.Ψ).orbitMap ∘ ((X.str.modelEP c.Ψ).liftInclLevel i).orbitMap) :
    (X.str.modelFunctorLevel c.Ψ i).orbitMap =
      X.levelOrbitEquiv i ∘ ((X.level i).str.modelFunctor d.Ψ).orbitMap ∘ orbitMap f := by
  funext z
  apply X.cat.toGroupoidStr.injective_orbitMap_fullSubInclusion (X.str.regSet i)
  have h1 := congrFun (X.str.orbitIncl_modelFunctorLevel c.Ψ i) z
  have h2 := congrFun (X.orbitIncl_levelOrbitEquiv i)
    (((X.level i).str.modelFunctor d.Ψ).orbitMap (orbitMap f z))
  have h3 := congrFun hfc z
  exact h1.trans (h3.symm.trans h2.symm)

/-- **2021 p. 766: `|Γ_Ψ^i| : |X_Ψ^i| → |C_i|` is a homeomorphism** for every covering family `Ψ`
of `F` and every level `i`, `|C_i|` with the topology of the GCT `C^i`. -/
theorem isHomeomorph_modelOrbitLevel (c : X.str.CoveringFamily) (i : ℕ) :
    @IsHomeomorph _ _ _ (X.levelTopology i) (X.str.modelFunctorLevel c.Ψ i).orbitMap := by
  obtain ⟨d, f, hf, hfc⟩ := X.exists_levelModel_comparison i c
  rw [X.modelFunctorLevel_eq_comp i c d f hfc]
  let _ := X.levelTopology i
  exact (X.levelOrbitHomeomorph i).isHomeomorph.comp
    (((X.level i).str.lemma_17_1_15 d).2.comp (isHomeomorph_orbitMap_of_isGeneralizedIso hf))

/-- **The natural topology of `|C_i|` is the one transported from `|X_Ψ^i|`** (2021 p. 766), for
every covering family `Ψ` of `F`. -/
theorem levelTopology_eq_coinduced (c : X.str.CoveringFamily) (i : ℕ) :
    X.levelTopology i =
      TopologicalSpace.coinduced (X.str.modelFunctorLevel c.Ψ i).orbitMap inferInstance := by
  let _ := X.levelTopology i
  exact (X.isHomeomorph_modelOrbitLevel c i).isQuotientMap.eq_coinduced

/-- `|Γ_Ψ^i|` as a homeomorphism `|X_Ψ^i| ≃ₜ |C_i|`. -/
def modelOrbitHomeomorphLevel (c : X.str.CoveringFamily) (i : ℕ) :
    @Homeomorph ((X.str.modelEP c.Ψ).lift i).X.OrbitSpace (X.str.regSub i).OrbitSpace _
      (X.levelTopology i) :=
  @IsHomeomorph.homeomorph _ _ _ (X.levelTopology i) _ (X.isHomeomorph_modelOrbitLevel c i)

theorem modelOrbitHomeomorphLevel_apply (c : X.str.CoveringFamily) (i : ℕ)
    (z : ((X.str.modelEP c.Ψ).lift i).X.OrbitSpace) :
    X.modelOrbitHomeomorphLevel c i z = (X.str.modelFunctorLevel c.Ψ i).orbitMap z := rfl

/-- `|X_Ψ^i| ≃ₜ |C^i|` (the GCT `C^i`). -/
def modelOrbitHomeomorphLevelCat (c : X.str.CoveringFamily) (i : ℕ) :
    ((X.str.modelEP c.Ψ).lift i).X.OrbitSpace ≃ₜ (X.level i).cat.toGroupoidStr.OrbitSpace := by
  letI := X.levelTopology i
  exact (X.modelOrbitHomeomorphLevel c i).trans (X.levelOrbitHomeomorph i).symm

/-- **`|X_Ψ^i|` is metrizable** for every covering family and every `i`. -/
theorem metrizableSpace_modelLift (c : X.str.CoveringFamily) (i : ℕ) :
    MetrizableSpace ((X.str.modelEP c.Ψ).lift i).X.OrbitSpace := by
  have := (X.level i).cat.metrizable
  exact (X.modelOrbitHomeomorphLevelCat c i).isEmbedding.metrizableSpace

/-- **`(X_Ψ^i, |Γ_Ψ^i|)`, a polyfold structure on `|C^i|`** (Definition 16.1.1) when `X_Ψ`
satisfies (ZHOU). -/
def levelPolyfoldStructure (c : X.str.CoveringFamily) (hZ : (X.str.modelEP c.Ψ).X.IsZhou)
    (i : ℕ) : PolyfoldStructure (X.level i).cat.toGroupoidStr.OrbitSpace :=
  ⟨(X.str.modelEP c.Ψ).lift i,
    (X.str.modelEP c.Ψ).hasParacompactOrbitSpace_lift (X.str.hasParacompactOrbitSpace_model c) i,
    (X.str.modelEP c.Ψ).isZhou_lift hZ i, X.modelOrbitHomeomorphLevelCat c i⟩

/-- `|Γ_Ψ^i| = |Γ_Ψ'^i| ∘ |f_{Ψ,Ψ'}^i|` on `|C^i|`. -/
theorem modelOrbitHomeomorphLevelCat_eq_comp (c c' : X.str.CoveringFamily) (i : ℕ) :
    ⇑(X.modelOrbitHomeomorphLevelCat c i) =
      ⇑(X.modelOrbitHomeomorphLevelCat c' i) ∘
        orbitMap (liftHomLevel (X.str.comparison c c') i) := by
  funext z
  exact congrArg (X.levelOrbitEquiv i).symm (congrFun (X.str.modelOrbitLevel_eq_comp c c' i) z)

/-- **The polyfold structures of two covering families are equivalent** (Definition 16.1.3), via
`f_{Ψ,Ψ'}^i`. -/
theorem levelPolyfoldStructure_equiv (c c' : X.str.CoveringFamily)
    (hZ : (X.str.modelEP c.Ψ).X.IsZhou) (hZ' : (X.str.modelEP c'.Ψ).X.IsZhou) (i : ℕ) :
    PolyfoldStructure.Equiv (X.levelPolyfoldStructure c hZ i) (X.levelPolyfoldStructure c' hZ' i) :=
  ⟨liftHomLevel (X.str.comparison c c') i,
    isGeneralizedIso_liftHomLevel (X.str.isGeneralizedIso_comparison c c') i,
    X.modelOrbitHomeomorphLevelCat_eq_comp c c' i⟩

/-- **2021 p. 766 (the natural topology of `|C_i|`, all levels)**: for every covering family `Ψ`
of `F` and every `i`:
`|Γ_Ψ^i| : |X_Ψ^i| → |C_i|` is a homeomorphism for the topology of the GCT `C^i`, that topology is
the one transported from `|X_Ψ^i|`, `|X_Ψ^i|` is metrizable, and `|Γ_Ψ^i| = |Γ_Ψ'^i| ∘ |f^i|` for
every second covering family `Ψ'`, `f^i` the raise of the generalized isomorphism `f_{Ψ,Ψ'}`. -/
theorem theorem_17_1_28_levels (c : X.str.CoveringFamily) (i : ℕ) :
    @IsHomeomorph _ _ _ (X.levelTopology i) (X.str.modelFunctorLevel c.Ψ i).orbitMap ∧
      X.levelTopology i =
        TopologicalSpace.coinduced (X.str.modelFunctorLevel c.Ψ i).orbitMap inferInstance ∧
      MetrizableSpace ((X.str.modelEP c.Ψ).lift i).X.OrbitSpace ∧
      ∀ c' : X.str.CoveringFamily,
        IsGeneralizedIso (liftHomLevel (X.str.comparison c c') i) ∧
        (X.str.modelFunctorLevel c.Ψ i).orbitMap =
          (X.str.modelFunctorLevel c'.Ψ i).orbitMap ∘
            orbitMap (liftHomLevel (X.str.comparison c c') i) :=
  ⟨X.isHomeomorph_modelOrbitLevel c i, X.levelTopology_eq_coinduced c i,
    X.metrizableSpace_modelLift c i, fun c' =>
      ⟨isGeneralizedIso_liftHomLevel (X.str.isGeneralizedIso_comparison c c') i,
        X.str.modelOrbitLevel_eq_comp c c' i⟩⟩

end GCT.UniformizedPolyfold

/-! ### Witness -/

namespace GCT.PolyfoldConstruction

open EpGroupoid.Examples LocalizationLRCounterexample

/-- **Witness for the levels of the natural topology**: for `ℤ/3 ⋉ ℝ` (`ℤ/3` acting trivially, so
every point has isotropy `ℤ/3` and the polyfold is not effective) and its covering family,
`|Γ_Ψ^2| : |X_Ψ^2| → |C_2|` is a homeomorphism and `|X_Ψ^2|` is non-empty. -/
theorem z3Uniformized_levelOrbit :
    @IsHomeomorph _ _ _ (z3Uniformized.levelTopology 2)
        (z3TautConstruction.modelFunctorLevel z3Family.Ψ 2).orbitMap ∧
      Nonempty ((z3TautConstruction.modelEP z3Family.Ψ).lift 2).X.OrbitSpace ∧
      ¬ z3TautConstruction.IsEffective := by
  refine ⟨z3Uniformized.isHomeomorph_modelOrbitLevel z3Family 2, ?_, not_isEffective_z3Taut⟩
  have h0 : (0 : Fin 1 → ℝ) ∈ z3TautConstruction.regSet 2 := by
    rw [z3Taut_regSet]
    exact mem_univ _
  obtain ⟨z, -⟩ := (z3TautConstruction.bijective_orbitMap_modelFunctorLevel z3Family 2).2
    ((z3TautConstruction.regSub 2).π ⟨0, h0⟩)
  exact ⟨z⟩

end GCT.PolyfoldConstruction

end Polyfold
