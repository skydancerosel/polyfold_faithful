import Polyfold.Chapter16.PolyfoldStructure
import Polyfold.Chapter10.StrongBundleIsoConverse
import Polyfold.Chapter8.BundleOrbitParacompact2021
import Polyfold.Chapter8.TangentZhou

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 16,
§16.3 (pp. 721–723; 2017: §16.3): **Definition 16.3.1, Lemma 16.3.2, Definitions 16.3.3, 16.3.4,
16.3.5**, and the polyfold induced by a strong polyfold bundle (p. 723).  Numbers and pages are
the 2021 text's.

# Strong polyfold bundle structures

## The text, paraphrased

(Definition 16.3.1) For a continuous surjection `p : Y → Z`, a strong polyfold bundle structure
is `((P : W → X, μ), Γ, γ)`: a strong bundle over an ep-groupoid `X` with (ZHOU), paracompact
`|X|` and the local regularity property (Definition 8.4.2), and homeomorphisms `Γ : |W| → Y`,
`γ : |X| → Z` with `p ∘ Γ = γ ∘ |P|`.  (Lemma 16.3.2) Then `Y` and `Z` are metrizable.
(Definition 16.3.3) Two structures are equivalent if a generalized strong bundle isomorphism
`F : W → W'`, covering `f : X → X'`, has `γ' ∘ |f| = γ` and `Γ' ∘ |F| = Γ`; the text adds that
`f` and `F` are then unique.  An equivalence class induces a class of polyfold structures on `Z`.
(Definition 16.3.4) A strong polyfold bundle is `p` with an equivalence class.  (Definition
16.3.5) It is tame, weakly face-structured, face-structured if the polyfold `(Z, c)` is.

## What is formalized

* `SDiagram.orbitMap_comp'`, `GenSBMap.orbitMap_comp`, `SEPLoc.orbitMap_comp`, `orbitMap_id`,
  `orbitMap_inv_comp`, `orbitMap_comp_inv` (`|[E] ∘ [D]| = |[E]| ∘ |[D]|` for generalized strong
  bundle maps, the strong bundle form of Proposition 10.3.11, not yet in Chapter 10), and the
  same for the base maps (`GenSBMap.base_comp`, `baseOrbitMap_comp`).
* `StrongPolyfoldBundleStructure p` (**Definition 16.3.1**); `continuous_p`, `surjective_p` (the
  text's assumptions on `p` follow from the structure); **`lemma_16_3_2`**.
* `StrongPolyfoldBundleStructure.Equiv` (**Definition 16.3.3**), an equivalence relation;
  `StrongPolyfoldBundle p` (**Definition 16.3.4**), the quotient.
* `toPolyfoldStructure`, `toPolyfoldStructure_equiv`, `StrongPolyfoldBundle.polyfold` (the
  induced polyfold `(Z, c)`, p. 723).
* `StrongPolyfoldBundle.IsTame`, `IsWeaklyFaceStructured`, `IsFaceStructured`
  (**Definition 16.3.5**), through the polyfold notions `PolyfoldClass.IsWeaklyFaceStructured`,
  `PolyfoldClass.IsFaceStructured` (Definition 16.1.21, in the form these need);
  `PolyfoldClass.isFaceStructured_iff` (one representative iff all, Remark 11.1.7).

The uniqueness claim after Definition 16.3.3 is checked in `PolyfoldBundleUniqueness.lean`.

## Readings

* `Y`, `Z` live in the universe of the object sets (as for `PolyfoldStructure`).
* "Continuous and surjective" for `p` is not a field: with `Γ`, `γ` homeomorphisms, `p` is
  `γ ∘ |P| ∘ Γ⁻¹`, continuous and surjective (`continuous_p`, `surjective_p`).
* Weakly face-structured polyfolds (Definition 16.1.21) are read through one representative; for
  face-structured ones every representative works (`isFaceStructured_iff`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory TopologicalSpace

noncomputable section

namespace Polyfold

universe u

open EPLocalization

/-! ### Orbit maps of composites of generalized strong bundle maps -/

namespace SBLocalization

namespace SDiagram

variable {A A' A'' : SEP.{u}}

/-- **`|D ∘ E| = |E| ∘ |D|`** for diagrams of strong bundles (the strong bundle form of
Proposition 10.3.11): on the middle `W'' ×_{W'} V''`, `Φ'(ΠV''(m)) = φ · Ψ(ΠW''(m))`. -/
theorem orbitMap_comp' (D : SDiagram A A') (E : SDiagram A' A'') :
    (D.comp E).orbitMap = E.orbitMap ∘ D.orbitMap := by
  funext q
  obtain ⟨r, rfl⟩ := (D.comp E).hΦ.isEquivalence.isHomeomorph_orbitMap.surjective q
  induction r using Quotient.inductionOn with | h m => ?_
  rw [orbitMap_orbitMap_Φ]
  change A''.E.toEpGroupoid.π ((SEP.Hom.Φ E.Ψ).obj ((SEP.Hom.Φ (compRight D E)).obj m)) =
    E.orbitMap (D.orbitMap (A.E.toEpGroupoid.π ((SEP.Hom.Φ D.Φ).obj (fib D E m))))
  have h1 := D.orbitMap_orbitMap_Φ (D.B.E.toEpGroupoid.π (fib D E m))
  change D.orbitMap (A.E.toEpGroupoid.π ((SEP.Hom.Φ D.Φ).obj (fib D E m))) =
    A'.E.toEpGroupoid.π ((SEP.Hom.Φ D.Ψ).obj (fib D E m)) at h1
  have h2 := E.orbitMap_orbitMap_Φ (E.B.E.toEpGroupoid.π ((SEP.Hom.Φ (compRight D E)).obj m))
  change E.orbitMap (A'.E.toEpGroupoid.π
      ((SEP.Hom.Φ E.Φ).obj ((SEP.Hom.Φ (compRight D E)).obj m))) =
    A''.E.toEpGroupoid.π ((SEP.Hom.Φ E.Ψ).obj ((SEP.Hom.Φ (compRight D E)).obj m)) at h2
  rw [h1, ← h2, obj_compRight, EpStrongBundle.act_eq (act_mem D E m), EpStrongBundle.π_μ]

/-- `|[1_W]| = id`. -/
theorem orbitMap_id' (A : SEP.{u}) : (SDiagram.id A).orbitMap = _root_.id := by
  funext q
  induction q using Quotient.inductionOn with | h w => ?_
  exact (SDiagram.id A).orbitMap_orbitMap_Φ (A.E.toEpGroupoid.π w)

end SDiagram

namespace GenSBMap

variable {A A' A'' : SEP.{u}}

theorem orbitMap_comp (f : GenSBMap A A') (g : GenSBMap A' A'') :
    (f.comp g).orbitMap = g.orbitMap ∘ f.orbitMap := by
  obtain ⟨D, rfl⟩ := SDiagram.cls_surjective f
  obtain ⟨E, rfl⟩ := SDiagram.cls_surjective g
  exact SDiagram.orbitMap_comp' D E

theorem base_comp (f : GenSBMap A A') (g : GenSBMap A' A'') :
    (f.comp g).base = f.base ≫ g.base :=
  SEPLoc.baseFunctor.map_comp (X := SEPLoc.of A) (Y := SEPLoc.of A') (Z := SEPLoc.of A'') f g

theorem baseOrbitMap_comp (f : GenSBMap A A') (g : GenSBMap A' A'') :
    EPLoc.orbitMap (f.comp g).base = EPLoc.orbitMap g.base ∘ EPLoc.orbitMap f.base := by
  rw [base_comp, EPLoc.proposition_10_3_11]

end GenSBMap

namespace SEPLoc

variable {A A' A'' : SEP.{u}}

/-- `|[E] ∘ [D]| = |[E]| ∘ |[D]|` in `SEP(F⁻¹)`. -/
theorem orbitMap_comp (f : of A ⟶ of A') (g : of A' ⟶ of A'') :
    GenSBMap.orbitMap (show GenSBMap A A'' from f ≫ g) =
      GenSBMap.orbitMap (show GenSBMap A' A'' from g) ∘
        GenSBMap.orbitMap (show GenSBMap A A' from f) :=
  GenSBMap.orbitMap_comp f g

theorem orbitMap_id (A : SEP.{u}) :
    GenSBMap.orbitMap (show GenSBMap A A from 𝟙 (of A)) = _root_.id :=
  SDiagram.orbitMap_id' A

theorem baseOrbitMap_comp (f : of A ⟶ of A') (g : of A' ⟶ of A'') :
    EPLoc.orbitMap (GenSBMap.base (show GenSBMap A A'' from f ≫ g)) =
      EPLoc.orbitMap (GenSBMap.base (show GenSBMap A' A'' from g)) ∘
        EPLoc.orbitMap (GenSBMap.base (show GenSBMap A A' from f)) :=
  GenSBMap.baseOrbitMap_comp f g

theorem baseOrbitMap_id (A : SEP.{u}) :
    EPLoc.orbitMap (GenSBMap.base (show GenSBMap A A from 𝟙 (of A))) = _root_.id := by
  have h : GenSBMap.base (show GenSBMap A A from 𝟙 (of A)) = 𝟙 (EPLoc.of A.baseEP) :=
    baseFunctor.map_id (of A)
  rw [h, EPLoc.orbitMap_id]

theorem orbitMap_inv_comp (f : of A ⟶ of A') [IsIso f] :
    GenSBMap.orbitMap (show GenSBMap A' A from inv f) ∘
      GenSBMap.orbitMap (show GenSBMap A A' from f) = _root_.id := by
  rw [← orbitMap_comp, IsIso.hom_inv_id, orbitMap_id]

theorem orbitMap_comp_inv (f : of A ⟶ of A') [IsIso f] :
    GenSBMap.orbitMap (show GenSBMap A A' from f) ∘
      GenSBMap.orbitMap (show GenSBMap A' A from inv f) = _root_.id := by
  rw [← orbitMap_comp, IsIso.inv_hom_id, orbitMap_id]

theorem baseOrbitMap_comp_inv (f : of A ⟶ of A') [IsIso f] :
    EPLoc.orbitMap (GenSBMap.base (show GenSBMap A A' from f)) ∘
      EPLoc.orbitMap (GenSBMap.base (show GenSBMap A' A from inv f)) = _root_.id := by
  rw [← baseOrbitMap_comp, IsIso.inv_hom_id, baseOrbitMap_id]

end SEPLoc

end SBLocalization

/-! ### Definition 16.3.1 -/

open SBLocalization

/-- **2021 Definition 16.3.1, p. 721 (2017: Definition 16.16)**: a **strong polyfold bundle
structure** for `p : Y → Z`: a strong bundle `(P : W → X, μ)` over an ep-groupoid `X` with
(ZHOU), paracompact orbit space and the local regularity property (Definition 8.4.2), and
homeomorphisms `Γ : |W| → Y`, `γ : |X| → Z` with `p ∘ Γ = γ ∘ |P|`. -/
structure StrongPolyfoldBundleStructure {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
    (p : Y → Z) : Type (u + 1) where
  /-- The strong bundle `(P : W → X, μ)` over the ep-groupoid `X`. -/
  A : SEP.{u}
  /-- `X` satisfies (ZHOU). -/
  isZhou : A.X.IsZhou
  /-- `|X|` is paracompact. -/
  paracompact : A.X.HasParacompactOrbitSpace
  /-- The local regularity property of Definition 8.4.2. -/
  isLR : A.E.IsLR
  /-- `Γ : |W| → Y`. -/
  Γ : A.E.toEpGroupoid.OrbitSpace ≃ₜ Y
  /-- `γ : |X| → Z`. -/
  γ : A.X.OrbitSpace ≃ₜ Z
  /-- `p ∘ Γ = γ ∘ |P|`. -/
  comm : p ∘ Γ = γ ∘ A.E.projFunctor.orbitMap

namespace StrongPolyfoldBundleStructure

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}

/-- `p = γ ∘ |P| ∘ Γ⁻¹`. -/
theorem p_eq (S : StrongPolyfoldBundleStructure p) :
    p = S.γ ∘ S.A.E.projFunctor.orbitMap ∘ S.Γ.symm := by
  funext y
  have h := congrFun S.comm (S.Γ.symm y)
  simp only [Function.comp_apply, Homeomorph.apply_symm_apply] at h
  exact h

theorem p_Γ (S : StrongPolyfoldBundleStructure p) (q : S.A.E.toEpGroupoid.OrbitSpace) :
    p (S.Γ q) = S.γ (S.A.E.projFunctor.orbitMap q) :=
  congrFun S.comm q

/-- The text's assumption that `p` is continuous follows from the structure. -/
theorem continuous_p (S : StrongPolyfoldBundleStructure p) : Continuous p := by
  rw [S.p_eq]
  exact S.γ.continuous.comp (S.A.E.continuous_orbitMap_projFunctor.comp S.Γ.symm.continuous)

/-- The text's assumption that `p` is surjective follows from the structure. -/
theorem surjective_p (S : StrongPolyfoldBundleStructure p) : Surjective p := by
  rw [S.p_eq]
  exact S.γ.surjective.comp (S.A.E.surjective_orbitMap_projFunctor.comp S.Γ.symm.surjective)

/-- **2021 Lemma 16.3.2, p. 722 (new in 2021)**: if `p : Y → Z` admits a strong polyfold
bundle structure, `Y` and `Z` are metrizable (`|X|` by Theorem 7.3.1, `|W|` by Proposition
8.4.1's proof). -/
theorem lemma_16_3_2 (S : StrongPolyfoldBundleStructure p) :
    MetrizableSpace Y ∧ MetrizableSpace Z := by
  have := S.A.X.theorem_7_3_1_metrizable S.paracompact
  have := S.A.E.metrizableSpace_orbitSpace S.paracompact
  exact ⟨S.Γ.symm.isEmbedding.metrizableSpace, S.γ.symm.isEmbedding.metrizableSpace⟩

/-! ### Definition 16.3.3 -/

/-- **2021 Definition 16.3.3, p. 722 (2017: Definition 16.17)**: two strong polyfold bundle
structures are **equivalent** if a generalized strong bundle isomorphism `F : W → W'`, covering
`f : X → X'`, has `γ' ∘ |f| = γ` and `Γ' ∘ |F| = Γ`. -/
def Equiv (S S' : StrongPolyfoldBundleStructure p) : Prop :=
  ∃ F : GenSBMap S.A S'.A, F.IsGeneralizedIso ∧
    ⇑S'.γ ∘ EPLoc.orbitMap F.base = ⇑S.γ ∧ ⇑S'.Γ ∘ F.orbitMap = ⇑S.Γ

theorem Equiv.refl (S : StrongPolyfoldBundleStructure p) : Equiv S S := by
  refine ⟨show GenSBMap S.A S.A from 𝟙 (SEPLoc.of S.A),
    GenSBMap.isGeneralizedIso_ofHom (SEP.equivalences.id_mem _), ?_, ?_⟩
  · rw [SEPLoc.baseOrbitMap_id]; rfl
  · rw [SEPLoc.orbitMap_id]; rfl

theorem Equiv.symm {S S' : StrongPolyfoldBundleStructure p} (h : Equiv S S') : Equiv S' S := by
  obtain ⟨F, hF, hγ, hΓ⟩ := h
  have : IsIso (show SEPLoc.of S.A ⟶ SEPLoc.of S'.A from F) :=
    SEPLoc.isIso_of_isGeneralizedIso hF
  refine ⟨show GenSBMap S'.A S.A from inv (show SEPLoc.of S.A ⟶ SEPLoc.of S'.A from F),
    (SEPLoc.isIso_iff_isGeneralizedIso _).1 inferInstance, ?_, ?_⟩
  · rw [← hγ, Function.comp_assoc, SEPLoc.baseOrbitMap_comp_inv]; rfl
  · rw [← hΓ, Function.comp_assoc, SEPLoc.orbitMap_comp_inv]; rfl

theorem Equiv.trans {S S' S'' : StrongPolyfoldBundleStructure p} (h : Equiv S S')
    (h' : Equiv S' S'') : Equiv S S'' := by
  obtain ⟨F, hF, hγ, hΓ⟩ := h
  obtain ⟨G, hG, hγ', hΓ'⟩ := h'
  have : IsIso (show SEPLoc.of S.A ⟶ SEPLoc.of S'.A from F) :=
    SEPLoc.isIso_of_isGeneralizedIso hF
  have : IsIso (show SEPLoc.of S'.A ⟶ SEPLoc.of S''.A from G) :=
    SEPLoc.isIso_of_isGeneralizedIso hG
  refine ⟨F.comp G, (SEPLoc.isIso_iff_isGeneralizedIso _).1
    (inferInstance : IsIso ((show SEPLoc.of S.A ⟶ SEPLoc.of S'.A from F) ≫
      (show SEPLoc.of S'.A ⟶ SEPLoc.of S''.A from G))), ?_, ?_⟩
  · rw [GenSBMap.baseOrbitMap_comp, ← Function.comp_assoc, hγ', hγ]
  · rw [GenSBMap.orbitMap_comp, ← Function.comp_assoc, hΓ', hΓ]

/-- **Definition 16.3.3**: equivalence of strong polyfold bundle structures is an equivalence
relation. -/
instance setoid (p : Y → Z) : Setoid (StrongPolyfoldBundleStructure p) where
  r := Equiv
  iseqv := ⟨Equiv.refl, Equiv.symm, Equiv.trans⟩

theorem equiv_iff {S S' : StrongPolyfoldBundleStructure p} : S ≈ S' ↔ Equiv S S' := Iff.rfl

/-! ### The induced polyfold structure (p. 723) -/

/-- The polyfold structure `(X, γ)` on `Z` underlying a strong polyfold bundle structure. -/
def toPolyfoldStructure (S : StrongPolyfoldBundleStructure p) : PolyfoldStructure Z :=
  ⟨S.A.baseEP, S.paracompact, S.isZhou, S.γ⟩

/-- Equivalent strong polyfold bundle structures have equivalent underlying polyfold structures
(2021 p. 723): the generalized isomorphism `f` covered by `F` (Remark 10.5.3). -/
theorem toPolyfoldStructure_equiv {S S' : StrongPolyfoldBundleStructure p} (h : Equiv S S') :
    PolyfoldStructure.Equiv S.toPolyfoldStructure S'.toPolyfoldStructure := by
  obtain ⟨F, hF, hγ, -⟩ := h
  exact ⟨F.base, (GenSBMap.remark_10_5_3 hF).1, hγ.symm⟩

end StrongPolyfoldBundleStructure

/-! ### Definition 16.3.4 -/

/-- **2021 Definition 16.3.4, p. 723 (2017: Definition 16.18)**: a **strong polyfold bundle**
`(p : Y → Z, c̄)`: an equivalence class `c̄` of strong polyfold bundle structures for `p`. -/
abbrev StrongPolyfoldBundle {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
    (p : Y → Z) : Type (u + 1) :=
  Quotient (StrongPolyfoldBundleStructure.setoid p)

/-! ### Face-structured polyfolds (Definition 16.1.21, as Definition 16.3.5 uses it) -/

namespace PolyfoldClass

variable {Z : Type u} [TopologicalSpace Z]

/-- A polyfold is **weakly face-structured** (Definition 16.1.21, read through one
representative) if some `(X, β) ∈ c` has `X` weakly face structured (Definition 11.1.3). -/
def IsWeaklyFaceStructured (c : PolyfoldClass Z) : Prop :=
  ∃ q : PolyfoldStructure Z, ⟦q⟧ = c ∧ q.X.X.IsWeaklyFaceStructured

/-- A polyfold is **face-structured** (Definition 16.1.21) if some `(X, β) ∈ c` has `X` face
structured in the ep-groupoid sense (Definition 11.1.3). -/
def IsFaceStructured (c : PolyfoldClass Z) : Prop :=
  ∃ q : PolyfoldStructure Z, ⟦q⟧ = c ∧ q.X.X.IsEpFaceStructured

/-- One representative is face structured iff all are (Remark 11.1.7). -/
theorem isFaceStructured_iff (c : PolyfoldClass Z) :
    c.IsFaceStructured ↔ ∀ q : PolyfoldStructure Z, ⟦q⟧ = c → q.X.X.IsEpFaceStructured := by
  refine ⟨fun ⟨q, hq, hX⟩ q' hq' => ?_, fun h => ?_⟩
  · obtain ⟨f, hf, -⟩ := Quotient.exact (hq.trans hq'.symm)
    exact (EPLoc.remark_11_1_7 hf).1 hX
  · obtain ⟨q, rfl⟩ := Quotient.exists_rep c
    exact ⟨q, rfl, h q rfl⟩

end PolyfoldClass

namespace StrongPolyfoldBundle

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}

/-- **The polyfold `(Z, c)` of a strong polyfold bundle** (2021 p. 723): the class of the
underlying polyfold structures. -/
def polyfold (c : StrongPolyfoldBundle p) : PolyfoldClass Z :=
  Quotient.map StrongPolyfoldBundleStructure.toPolyfoldStructure
    (fun _ _ h => StrongPolyfoldBundleStructure.toPolyfoldStructure_equiv h) c

@[simp] theorem polyfold_mk (S : StrongPolyfoldBundleStructure p) :
    polyfold ⟦S⟧ = ⟦S.toPolyfoldStructure⟧ := rfl

/-- **2021 Definition 16.3.5 (1), p. 723 (2017: Definition 16.19)**: `(p, c̄)` is **tame** if the
polyfold `(Z, c)` is tame. -/
def IsTame (c : StrongPolyfoldBundle p) : Prop := c.polyfold.IsTame

/-- **Definition 16.3.5 (2)**: weakly face-structured if `(Z, c)` is. -/
def IsWeaklyFaceStructured (c : StrongPolyfoldBundle p) : Prop :=
  c.polyfold.IsWeaklyFaceStructured

/-- **Definition 16.3.5 (3)**: face-structured if `(Z, c)` is. -/
def IsFaceStructured (c : StrongPolyfoldBundle p) : Prop := c.polyfold.IsFaceStructured

/-- Tameness of `(p, c̄)` can be read in any representative. -/
theorem isTame_iff (c : StrongPolyfoldBundle p) :
    c.IsTame ↔ ∀ S : StrongPolyfoldBundleStructure p, ⟦S⟧ = c → S.A.X.IsTame := by
  refine ⟨fun h S hS => ?_, fun h => ?_⟩
  · exact (c.polyfold.definition_16_1_20.1 h) S.toPolyfoldStructure (by rw [← hS]; rfl)
  · obtain ⟨S, rfl⟩ := Quotient.exists_rep c
    exact ⟨S.toPolyfoldStructure, rfl, h S rfl⟩

end StrongPolyfoldBundle

end Polyfold
