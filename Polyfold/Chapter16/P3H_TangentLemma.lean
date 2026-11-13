import Polyfold.Chapter16.P3Z_ZhouUniquenessCheck

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 16,
§16.2 "Tangent of a Polyfold" (pp. 715–716; 2017: §16.2): the tangent `Tf` of a generalized
isomorphism and **Lemma 16.2.1** (p. 716; 2017: Lemma 16.3).  Numbers and pages are the 2021
text's.

# Tangents of generalized isomorphisms and Lemma 16.2.1

## The text, paraphrased

(p. 715) For a generalized isomorphism `f = [X ←F A →H Y]` its tangent is
`Tf = [TX ←TF TA →TH TY]`, a generalized isomorphism by Theorem 10.1.7, independent of the
representative by Theorem 11.1.1.  (Lemma 16.2.1) If two isomorphisms `(f, 𝔣)`, `(g, 𝔤)` of
polyfold structures `(X, α) → (Y, β)` have `f = g`, then `𝔣 = 𝔤` and `T𝔣 = T𝔤`; the proof
quotes Theorem 10.3.19 for `|𝔣| = |𝔤|`.

## What is formalized

* `EP.tangentAny`, `Diagram.tangentAny`, `EPLoc.tangentHom`: the tangent of an ep-groupoid and of
  a generalized map for ep-groupoids in every universe (Chapter 11's `EPLoc.tangentFunctor` lives
  on `EPLoc.{max u 1}`; `tangentHom_eq_tangentFunctor_map` says they agree there), with
  `tangentHom_id`, `tangentHom_comp`, `isGeneralizedIso_tangentHom`.
* `EPLoc.orbitMap_tangentHom_eq`: **if one of `X`, `Y` has (LR) and the generalized isomorphisms
  `𝔣, 𝔤 : X → Y` have `|𝔣| = |𝔤|`, then `|T𝔣| = |T𝔤|`** (Proposition 10.1.10 (2) on a
  representative of `𝔤⁻¹ ∘ 𝔣`).  This is what the construction of `T(Z, c)` on pp. 716–718 uses.
* `PolyfoldStructure.Lemma_16_2_1` (the statement) and **`not_lemma_16_2_1`: Lemma 16.2.1 does
  not hold as we read it**, on the polyfold structure `ℤ/3 × ℝ ⇉ ℝ` of `ℝ` (trivial action;
  (ZHOU), paracompact orbit space), with `f = g = id`, `𝔣 = [X ←1 X →Inv X]`, `𝔤 = [1_X]`
  (`lemma_16_2_1_counterexample`; the same pair as `not_uniqueness_16_1_2`): `𝔣 ≠ 𝔤`.  For this
  pair `|T𝔣| = |T𝔤|` holds.
* The strongest forms we prove: `lemma_16_2_1_orbit` (no hypothesis beyond the text's: `f = g`
  gives `|𝔣| = |𝔤|` and `|T𝔣| = |T𝔤|`, the orbit-level content used on pp. 716–718) and
  `lemma_16_2_1_of_isEffective` (the printed conclusion `𝔣 = 𝔤 ∧ T𝔣 = T𝔤` when `Y` is
  effective).

## Reading

An isomorphism `(f, 𝔣) : (X, α) → (Y, β)` of the category `PS` (p. 709) is a homeomorphism
`f : Z_α → Z_β` with a generalized isomorphism `𝔣` and `f ∘ α = β ∘ |𝔣|`.  Whether the second
conclusion `T𝔣 = T𝔤` alone also fails for the pair above is not decided here (the conjunction
fails by its first part).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

/-- The tangent `TX` of a bundled ep-groupoid `A ∈ EP.{u}`, in `EP.{max u 1}` (Theorem 8.1.1;
Chapter 8's `EP.tangent` is the case `u = max u' 1`). -/
def EP.tangentAny (A : EP.{u}) : EP.{max u 1} where
  Obj := A.X.PObj.TangentSpace
  Mor := A.X.PMor.TangentSpace
  X := A.X.tangentEpGroupoid

theorem EP.tangentAny_eq_tangent (A : EP.{max u 1}) : A.tangentAny = A.tangent := rfl

namespace EPLocalization

open WeakFibredProduct

namespace Diagram

variable {X Y Z : EP.{u}}

/-- **The tangent diagram** `TX ←TF TA →TΦ TY` of `d : X ←F A →Φ Y` (Theorem 10.1.7), for
ep-groupoids in any universe. -/
def tangentAny (d : Diagram X Y) : Diagram X.tangentAny Y.tangentAny :=
  ⟨d.A.tangentAny, d.F.tangent, EpFunctor.theorem_10_1_7 d.isEquivalence_F, d.Φ.tangent⟩

theorem IsRefinement.tangentAny {d d' : Diagram X Y} (h : d'.IsRefinement d) :
    d'.tangentAny.IsRefinement d.tangentAny := by
  obtain ⟨H, hH, ⟨σ⟩, ⟨τ⟩⟩ := h
  refine ⟨H.tangent, EpFunctor.theorem_10_1_7 hH, ⟨σ.tangent.castEq ?_ rfl⟩,
    ⟨τ.tangent.castEq ?_ rfl⟩⟩
  · exact EpFunctor.tangent_comp _ _
  · exact EpFunctor.tangent_comp _ _

theorem Equiv.tangentAny {d d' : Diagram X Y} (h : Equiv d d') :
    Equiv d.tangentAny d'.tangentAny := by
  obtain ⟨d'', h₁, h₂⟩ := h
  exact ⟨d''.tangentAny, h₁.tangentAny, h₂.tangentAny⟩

theorem isRefinement_tangentAny_id (X : EP.{u}) :
    (Diagram.id X).tangentAny.IsRefinement (Diagram.id X.tangentAny) := by
  refine ⟨EpFunctor.id _, EpFunctor.IsEquivalence.id _, .of_eq ?_, .of_eq ?_⟩ <;>
  · change EpFunctor.id _ = (EpFunctor.id X.X).tangent
    rw [EpFunctor.tangent_id]

/-- `T(d ∘ e)` refines `Td ∘ Te` (the argument of `Diagram.isRefinement_tangent_comp`, in any
universe). -/
theorem isRefinement_tangentAny_comp (d : Diagram X Y) (e : Diagram Y Z) :
    (d.comp e).tangentAny.IsRefinement (d.tangentAny.comp e.tangentAny) := by
  have h := d.admissible e
  have h' : Admissible d.Φ.tangent e.F.tangent :=
    .of_isEquivalence_right (EpFunctor.theorem_10_1_7 e.isEquivalence_F)
  let πA := projLeft d.Φ e.F (d.admissible e)
  let πB := projRight d.Φ e.F (d.admissible e)
  let τ : EpNatTrans (d.Φ.tangent.comp πA.tangent) (e.F.tangent.comp πB.tangent) :=
    (natTrans d.Φ e.F (d.admissible e)).tangent.castEq (EpFunctor.tangent_comp _ _)
      (EpFunctor.tangent_comp _ _)
  let L := wfpLift πA.tangent πB.tangent τ h'
  have hL : L.IsEquivalence :=
    EpFunctor.IsEquivalence.of_comp_left
      (isEquivalence_projLeft (EpFunctor.theorem_10_1_7 e.isEquivalence_F) h')
      (by
        rw [projLeft_comp_wfpLift]
        exact EpFunctor.theorem_10_1_7 (isEquivalence_projLeft e.isEquivalence_F h))
  refine ⟨L, hL, .of_eq ?_, .of_eq ?_⟩
  · exact EpFunctor.ext
      (MPolyfold.tangentMap_comp d.F.isScSmoothMap_obj πA.isScSmoothMap_obj).symm
      (MPolyfold.tangentMap_comp d.F.isScSmoothMap_mor πA.isScSmoothMap_mor).symm
  · exact EpFunctor.ext
      (MPolyfold.tangentMap_comp e.Φ.isScSmoothMap_obj πB.isScSmoothMap_obj).symm
      (MPolyfold.tangentMap_comp e.Φ.isScSmoothMap_mor πB.isScSmoothMap_mor).symm

end Diagram

namespace EPLoc

variable {X Y Z : EP.{u}}

/-- **The tangent `Tf = [TX ←TF TA →TΦ TY]` of a generalized map** `f = [X ←F A →Φ Y]`
(2021 p. 715), for ep-groupoids in any universe. -/
def tangentHom (f : of X ⟶ of Y) : of X.tangentAny ⟶ of Y.tangentAny :=
  Quotient.map Diagram.tangentAny (fun _ _ h => Diagram.Equiv.tangentAny h) f

@[simp] theorem tangentHom_homMk (d : Diagram X Y) : tangentHom (homMk d) = homMk d.tangentAny :=
  rfl

theorem tangentHom_id (X : EP.{u}) : tangentHom (𝟙 (of X)) = 𝟙 (of X.tangentAny) :=
  Quotient.sound (Diagram.isRefinement_tangentAny_id X).equiv

theorem tangentHom_comp (f : of X ⟶ of Y) (g : of Y ⟶ of Z) :
    tangentHom (f ≫ g) = tangentHom f ≫ tangentHom g :=
  Quotient.inductionOn₂ (motive := fun (f : of X ⟶ of Y) (g : of Y ⟶ of Z) =>
    tangentHom (f ≫ g) = tangentHom f ≫ tangentHom g) f g fun d e =>
      Quotient.sound (Diagram.isRefinement_tangentAny_comp d e).equiv

/-- On `EPLoc.{max u 1}`, `tangentHom` is Chapter 11's tangent functor (Theorem 11.1.1). -/
theorem tangentHom_eq_tangentFunctor_map {X Y : EP.{max u 1}} (f : of X ⟶ of Y) :
    tangentHom f = tangentFunctor.map f := rfl

/-- The tangent of a generalized isomorphism is a generalized isomorphism (2021 p. 715). -/
theorem isGeneralizedIso_tangentHom {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) :
    IsGeneralizedIso (tangentHom f) := by
  obtain ⟨g, hfg, hgf⟩ := hf
  exact ⟨tangentHom g, by rw [← tangentHom_comp, hfg, tangentHom_id],
    by rw [← tangentHom_comp, hgf, tangentHom_id]⟩

/-- If `X` has (LR), a generalized automorphism `e` of `X` with `|e| = 1` has `|Te| = 1`:
on a representative `X ←F A →Φ X` (both legs equivalences, `|F| = |Φ|`, `A` with (LR) by
Proposition 10.1.9) Proposition 10.1.10 (2) gives `|TF| = |TΦ|`. -/
theorem orbitMap_tangentHom_eq_id (hX : X.X.IsLR) {e : of X ⟶ of X} (he : IsGeneralizedIso e)
    (heo : orbitMap e = _root_.id) : orbitMap (tangentHom e) = _root_.id := by
  obtain ⟨d, rfl, hΦ⟩ := exists_diagram_of_isGeneralizedIso he
  have hdo : d.orbitMap = _root_.id := heo
  have hFΦ : d.F.orbitMap = d.Φ.orbitMap := funext fun q => by
    rw [← d.orbitMap_orbitMap_F q, hdo]
    rfl
  have hA : d.A.X.IsLR := (EpFunctor.proposition_10_1_9 d.isEquivalence_F).2 hX
  have hT := EpFunctor.proposition_10_1_10_two d.isEquivalence_F hΦ hFΦ hA
  funext q
  obtain ⟨r, rfl⟩ := d.tangentAny.isEquivalence_F.isHomeomorph_orbitMap.surjective q
  change d.tangentAny.orbitMap (d.tangentAny.F.orbitMap r) = d.tangentAny.F.orbitMap r
  rw [Diagram.orbitMap_orbitMap_F]
  exact (congrFun hT r).symm

/-- **The orbit-level uniqueness of tangents** (the content of Lemma 16.2.1 that survives, and
what the construction of `T(Z, c)`, 2021 pp. 716–718, uses): if one of `X`, `Y` has (LR) and the
generalized isomorphisms `f, f' : X → Y` have `|f| = |f'|`, then `|Tf| = |Tf'|`.  (`f = f'`
itself need not hold: `not_theorem_10_3_19`.) -/
theorem orbitMap_tangentHom_eq (hLR : X.X.IsLR ∨ Y.X.IsLR) {f f' : of X ⟶ of Y}
    (hf : IsGeneralizedIso f) (hf' : IsGeneralizedIso f') (h : orbitMap f = orbitMap f') :
    orbitMap (tangentHom f) = orbitMap (tangentHom f') := by
  have hYLR : Y.X.IsLR := hLR.elim (proposition_10_3_16 hf).1 _root_.id
  obtain ⟨g, hfg, hgf⟩ := hf
  have he : IsGeneralizedIso (g ≫ f') := by
    rw [isGeneralizedIso_iff_isIso] at hf' ⊢
    have : IsIso g := ⟨⟨f, hgf, hfg⟩⟩
    infer_instance
  have heo : orbitMap (g ≫ f') = _root_.id := by
    rw [proposition_10_3_11, ← h, ← proposition_10_3_11, hgf, orbitMap_id]
  have hT := orbitMap_tangentHom_eq_id hYLR he heo
  have e1 : f' = f ≫ g ≫ f' := by rw [← Category.assoc, hfg, Category.id_comp]
  rw [e1, tangentHom_comp, proposition_10_3_11, hT, Function.id_comp]

end EPLoc

end EPLocalization

namespace PolyfoldStructure

open EPLocalization EPLocalization.EPLoc EpGroupoid.Examples LocalizationLRCounterexample

/-- The statement of **2021 Lemma 16.2.1, p. 716 (2017: Lemma 16.3)**, in universe `u`: if two
isomorphisms `(f, 𝔣), (g, 𝔤) : (X, α) → (Y, β)` of polyfold structures (homeomorphisms
`f, g : Z → W`, generalized isomorphisms `𝔣, 𝔤 : X → Y` with `f ∘ α = β ∘ |𝔣|`,
`g ∘ α = β ∘ |𝔤|`) have `f = g`, then `𝔣 = 𝔤` and `T𝔣 = T𝔤`.  It does not hold as we read it:
`not_lemma_16_2_1`. -/
def Lemma_16_2_1 : Prop :=
  ∀ (Z W : Type u) [TopologicalSpace Z] [TopologicalSpace W] (p : PolyfoldStructure Z)
    (q : PolyfoldStructure W) (f g : Z ≃ₜ W) (𝔣 𝔤 : EPLoc.of p.X ⟶ EPLoc.of q.X),
    IsGeneralizedIso 𝔣 → IsGeneralizedIso 𝔤 → ⇑f ∘ ⇑p.β = ⇑q.β ∘ orbitMap 𝔣 →
    ⇑g ∘ ⇑p.β = ⇑q.β ∘ orbitMap 𝔤 → f = g → 𝔣 = 𝔤 ∧ tangentHom 𝔣 = tangentHom 𝔤

/-- **The counterexample to Lemma 16.2.1** (the pair of `uniqueness_16_1_2_counterexample`): on
the polyfold structure `ℤ/3 × ℝ ⇉ ℝ` of `ℝ` ((ZHOU), paracompact orbit space), the isomorphisms
`(id, [X ←1 X →Inv X])` and `(id, [1_X])` of `PS` have the same homeomorphism, the generalized
isomorphisms differ, and their tangents have the same orbit map. -/
theorem lemma_16_2_1_counterexample :
    z3PolyfoldStructure.X.X.IsZhou ∧ z3PolyfoldStructure.X.X.HasParacompactOrbitSpace ∧
      IsGeneralizedIso genInv ∧ IsGeneralizedIso genId ∧
      ⇑(Homeomorph.refl _) ∘ ⇑z3PolyfoldStructure.β =
        ⇑z3PolyfoldStructure.β ∘ orbitMap genInv ∧
      ⇑(Homeomorph.refl _) ∘ ⇑z3PolyfoldStructure.β =
        ⇑z3PolyfoldStructure.β ∘ orbitMap genId ∧
      genInv ≠ genId ∧ orbitMap (tangentHom genInv) = orbitMap (tangentHom genId) :=
  ⟨z3PolyfoldStructure.isZhou, z3PolyfoldStructure.paracompact, isGeneralizedIso_genInv,
    isGeneralizedIso_genId, β_eq_β_comp_orbitMap_genInv, β_eq_β_comp_orbitMap_genId,
    genInv_ne_genId,
    orbitMap_tangentHom_eq (Or.inl isLR_trivialZ3) isGeneralizedIso_genInv
      isGeneralizedIso_genId orbitMap_genInv⟩

/-- **2021 Lemma 16.2.1, p. 716, does not hold as we read it**: `lemma_16_2_1_counterexample`
(`f = g = id`, `𝔣 = [X ←1 X →Inv X] ≠ [1_X] = 𝔤`). -/
theorem not_lemma_16_2_1 : ¬ Lemma_16_2_1.{0} := fun h =>
  genInv_ne_genId (h _ _ z3PolyfoldStructure z3PolyfoldStructure (Homeomorph.refl _)
    (Homeomorph.refl _) genInv genId isGeneralizedIso_genInv isGeneralizedIso_genId
    β_eq_β_comp_orbitMap_genInv β_eq_β_comp_orbitMap_genId rfl).1

variable {Z W : Type u} [TopologicalSpace Z] [TopologicalSpace W]

/-- `|𝔣| = β⁻¹ ∘ f ∘ α` for an isomorphism `(f, 𝔣)` of `PS`. -/
theorem orbitMap_eq_of_comp {p : PolyfoldStructure Z} {q : PolyfoldStructure W} {f : Z → W}
    {𝔣 : EPLoc.of p.X ⟶ EPLoc.of q.X} (h : f ∘ ⇑p.β = ⇑q.β ∘ orbitMap 𝔣) :
    orbitMap 𝔣 = ⇑q.β.symm ∘ f ∘ ⇑p.β := by
  rw [h, ← Function.comp_assoc, q.β.symm_comp_self, Function.id_comp]

/-- **Lemma 16.2.1 at the level of orbit spaces** (2021 p. 716; the strongest form we prove with
the text's hypotheses): if two isomorphisms `(f, 𝔣), (g, 𝔤) : (X, α) → (Y, β)` of polyfold
structures have `f = g`, then `|𝔣| = |𝔤|` and `|T𝔣| = |T𝔤|` ((ZHOU) gives (LR),
`orbitMap_tangentHom_eq`).  This is what the canonical bijections `Ψ` of pp. 716–717 use. -/
theorem lemma_16_2_1_orbit {p : PolyfoldStructure Z} {q : PolyfoldStructure W} {f g : Z ≃ₜ W}
    {𝔣 𝔤 : EPLoc.of p.X ⟶ EPLoc.of q.X} (h𝔣 : IsGeneralizedIso 𝔣) (h𝔤 : IsGeneralizedIso 𝔤)
    (hf : ⇑f ∘ ⇑p.β = ⇑q.β ∘ orbitMap 𝔣) (hg : ⇑g ∘ ⇑p.β = ⇑q.β ∘ orbitMap 𝔤) (hfg : f = g) :
    orbitMap 𝔣 = orbitMap 𝔤 ∧ orbitMap (tangentHom 𝔣) = orbitMap (tangentHom 𝔤) := by
  have e : orbitMap 𝔣 = orbitMap 𝔤 := by
    rw [orbitMap_eq_of_comp hf, orbitMap_eq_of_comp hg, hfg]
  exact ⟨e, orbitMap_tangentHom_eq (Or.inl p.isLR) h𝔣 h𝔤 e⟩

/-- **Lemma 16.2.1 for an effective target** (2021 p. 716): if `Y` is effective, `f = g` gives
`𝔣 = 𝔤` and `T𝔣 = T𝔤` (Theorem 10.3.19 for an effective target). -/
theorem lemma_16_2_1_of_isEffective {p : PolyfoldStructure Z} {q : PolyfoldStructure W}
    (hq : q.X.X.IsEffective) {f g : Z ≃ₜ W} {𝔣 𝔤 : EPLoc.of p.X ⟶ EPLoc.of q.X}
    (h𝔣 : IsGeneralizedIso 𝔣) (h𝔤 : IsGeneralizedIso 𝔤) (hf : ⇑f ∘ ⇑p.β = ⇑q.β ∘ orbitMap 𝔣)
    (hg : ⇑g ∘ ⇑p.β = ⇑q.β ∘ orbitMap 𝔤) (hfg : f = g) :
    𝔣 = 𝔤 ∧ tangentHom 𝔣 = tangentHom 𝔤 := by
  subst hfg
  have e := remark_16_1_7_of_isEffective f hq h𝔣 h𝔤 hf hg
  exact ⟨e, congrArg tangentHom e⟩

/-- **Witness** for `lemma_16_2_1_of_isEffective`: the hypotheses hold for the point ep-groupoid
(`(Y, β)` effective with an isomorphism over a homeomorphism) — see
`theorem_10_3_19_of_isEffective_hypotheses`: the point ep-groupoid is effective and satisfies
(ZHOU). -/
theorem lemma_16_2_1_of_isEffective_hypotheses :
    EpGroupoid.Examples.pointEP.X.IsEffective ∧ EpGroupoid.Examples.pointEP.X.IsZhou :=
  ⟨EquivalenceLREffectiveExamples.isEffective_pointEP,
    EpGroupoid.isZhou_of_subsingleton _ fun _ =>
      ⟨fun a b => GroupoidStr.Isotropy.ext (Subsingleton.elim (α := Unit) a.val b.val)⟩⟩

end PolyfoldStructure

end Polyfold
