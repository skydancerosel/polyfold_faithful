import Polyfold.Chapter16.P3H_PolyfoldForms
import Polyfold.Chapter16.P3Z_PolyfoldPartitions
import Polyfold.Chapter16.P3Z_PolyfoldExamples
import Polyfold.Chapter11.GapP2_H4EffDiagram
import Polyfold.Chapter11.BoundaryOrientationEquiv
import Polyfold.Chapter9.GapP3_K1_Theorems
import Polyfold.Chapter9.GapP3_K2_StokesDim1
import Polyfold.Chapter9.GapP3_K2_LUCDim1
import Polyfold.Chapter9.GapP2_CProp919
import Polyfold.Chapter9.GapP2_CProp919Manifold
import Polyfold.Chapter7.SmoothRegularAssembly

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 16,
§16.4, pp. 729–732: **branched finite-dimensional orbifolds** (2017: §16.4).  Numbers and pages
are the 2021 text's.

## The text, paraphrased

(Definition 16.4.1) A branched suborbifold of the polyfold `(Z, c)` is a class `θ = [Θ, (X, α)]`,
`(X, α) ∈ c`, `Θ` a branched ep⁺-subgroupoid of `X`; `(Θ, (X, α)) ∼ (Θ', (X', α'))` if a generalized
isomorphism `f : X → X'` has `α' ∘ |f| = α` and `f^*Θ' = Θ`.  `θ = |Θ| ∘ α⁻¹ : Z → ℚ⁺` is well
defined.  (Definition 16.4.2) `θ` is closed, compact, of manifold-type, of orbifold-type or tame if
`Θ` is.  (Proposition 16.4.3) `supp θ` carries a natural manifold (orbifold) structure for `θ` of
manifold-type (orbifold-type).  (Definition 16.4.4) Oriented branched suborbifolds
`[(Θ, T̂_Θ), (X, α)]`, with `f^*(Θ', T̂_Θ') = (Θ, T̂_Θ)`.  (Definition 16.4.5)
`∂θ̂ = [∂(Θ, T̂_Θ), (X, α)]` for `θ̂` tame (Theorem 11.3.9).  The integrals
`∫_θ̂ τ = µ^Θ̂_ω(|supp Θ|)`, `∮_θ̂ τ` do not depend on
the representatives.  (Theorem 16.4.6, Stokes) `∫_θ̂ dτ = ∫_∂θ̂ τ` and `∮_θ̂ dτ = ∮_∂θ̂ τ` for
`θ̂` oriented, tame, compact, of dimension `n`, and `τ` of degree `n - 1`.

## What is formalized

Namespace `Polyfold.PolyfoldClass`:
* `BranchedRep c`, `BranchedRep.Rel` (Definition 16.4.1's relation, an equivalence relation),
  **`BranchedSuborbifold c`** (the quotient), **`BranchedSuborbifold.toFun`** (`θ = |Θ| ∘ α⁻¹`,
  `definition_16_4_1_wellDefined`).  Needs `EPLoc.pullTheta_eq_of_orbitMap` (`f^*Θ'` at `x` is `Θ'`
  at any `y` with `|f|(|x|) = |y|`).
* Definition 16.4.2 (1)–(4) and `n`-dimensionality: `HasRepProperty P θ` (some representative has
  `P`), and **`hasRepProperty_iff`**: for `P` stable under pull-backs by generalized isomorphisms,
  some representative has `P` iff all have (`definition_16_4_2_closed`, `_compact`, `_manifold`,
  `_orbifold`, `_nDim`, from Theorem 11.3.3).  (5), tameness, is `IsTame` (some representative is
  tame, Definition 9.3.6); its invariance is not formalized (gap).
* Proposition 16.4.3, topological part: **`proposition_16_4_3_supp`**, `supp θ = α(|supp Θ|)`, and
  `proposition_16_4_3_homeomorph : supp θ ≃ₜ |supp Θ|` for every representative; with
  Proposition 9.1.9 this gives the manifold (orbifold) structure of each representative
  (`proposition_16_4_3_manifold`, `proposition_16_4_3_orbifold`).  That the structures from two
  representatives agree is not formalized (gap).
* `OrientedRep c` (with `T̂` zero off `X_∞`, where it is never read), `OrientedRep.Rel`
  (Definition 16.4.4, an equivalence relation), **`OrientedSuborbifold c`**.
* Definition 16.4.5: **`definition_16_4_5_wellDefined`**: related representatives have related
  boundaries `(∂Θ, T̂_∂Θ)` (Theorem 11.3.9, no tameness needed for the relation).
* The integrals on a representative: `OrientedRep.integral`, `integralEff`, `boundaryIntegral`,
  `boundaryIntegralEff`; **`integral_eq_of_rel`, `integralEff_eq_of_rel`** (independence of the
  representative, among tame compact representatives; Theorems 11.4.1, 11.4.2 and the p. 720
  independence of `h_*`).
* **`theorem_16_4_6_hyp`, `theorem_16_4_6_eff_hyp`** (`n = m + 1 ≥ 2`) and
  **`theorem_16_4_6_dim1_hyp`, `theorem_16_4_6_eff_dim1_hyp`** (`n = 1`): Stokes on every tame
  compact oriented representative, with the added hypothesis that `c` admits sc-smooth partitions of
  unity (Definition 16.1.5; Theorem 9.5.17 assumes them, Theorem 16.4.6 does not state them);
  witness `z3Polyfold_admitsScPartitionsOfUnity`.  Corollaries `boundaryIntegral_eq_of_rel`,
  `boundaryIntegralEff_eq_of_rel`, `boundaryIntegralDim1_eq_of_rel`: the boundary integrals do not
  depend on the representative either.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory MeasureTheory

noncomputable section

namespace Polyfold

universe u

open EPLocalization EPLocalization.EPLoc

namespace EPLocalization.EPLoc

open EpGroupoid MPolyfold

variable {X Y : EP.{u}}

/-- `1^*Θ = Θ` for a functorial `Θ`. -/
theorem pullTheta_id_of_isFunctorial {Θ : X.Obj → ℚ} (hΘ : X.X.IsFunctorial Θ) :
    pullTheta (𝟙 (of X)) Θ = Θ := by
  have h1 := pushTheta_inv (isGeneralizedIso_id X) (Category.comp_id _) (Category.comp_id _) hΘ
  calc pullTheta (𝟙 (of X)) Θ = pullTheta (𝟙 (of X)) (pushTheta (𝟙 (of X)) Θ) := by
        rw [h1, ← pullTheta_comp _ _ hΘ, Category.comp_id]
    _ = Θ := pullTheta_pushTheta (isGeneralizedIso_id X) hΘ

/-- `1^*T = T` for a section functor vanishing off `X_∞`. -/
theorem pullSection_id_of_mem {T : X.Obj → X.X.PObj.OrTangent →₀ ℚ}
    (hT : T ∈ X.X.GrHatSections) : pullSection (𝟙 (of X)) T = T := by
  have h1 := pushSection_inv (isGeneralizedIso_id X) (Category.comp_id _) (Category.comp_id _) hT.1
  calc pullSection (𝟙 (of X)) T = pullSection (𝟙 (of X)) (pushSection (𝟙 (of X)) T) := by
        rw [h1, ← pullSection_comp (isGeneralizedIso_id X) (isGeneralizedIso_id X) hT.1,
          Category.comp_id]
    _ = T := pullSection_pushSection (isGeneralizedIso_id X) hT

/-- **`f^*Θ'` at `x` is `Θ'` at any `y` with `|f|(|x|) = |y|`** (2021 p. 730:
`|f^*Θ'| = |Θ'| ∘ |f|`). -/
theorem pullTheta_eq_of_orbitMap {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) {Θ' : Y.Obj → ℚ}
    (hΘ' : Y.X.IsFunctorial Θ') {x : X.Obj} {y : Y.Obj}
    (h : orbitMap f (X.X.π x) = Y.X.π y) : pullTheta f Θ' x = Θ' y := by
  have _hf := hf
  set d := rep f with hd
  obtain ⟨r, hr⟩ := d.isEquivalence_F.isHomeomorph_orbitMap.bijective.2 (X.X.π x)
  obtain ⟨a, rfl⟩ := d.A.X.surjective_π r
  have hax : X.X.Isomorphic (d.F.obj a) x := (X.X.π_eq_π_iff).1 hr
  have h1 : pullTheta f Θ' x = Θ' (d.Φ.obj a) := by
    change d.F.pushforwardTheta (d.Φ.pullbackTheta Θ') x = _
    rw [EpFunctor.pushforwardTheta_eq d.isEquivalence_F.full
      (d.Φ.isFunctorial_pullbackTheta hΘ') hax]
    rfl
  have h2 : Y.X.π (d.Φ.obj a) = Y.X.π y := by
    rw [← h, orbitMap_eq_rep, ← hd, Diagram.orbitMap_eq_of hr]
    rfl
  obtain ⟨φ, hφs, hφt⟩ := (Y.X.π_eq_π_iff).1 h2
  rw [h1, ← hφs, ← hφt]
  exact hΘ' φ

theorem pull_congr {f f' : of X ⟶ of Y} (hf : IsGeneralizedIso f) (hf' : IsGeneralizedIso f')
    (h : f = f') (A : OrientedBranched Y) :
    OrientedBranched.pull hf A = OrientedBranched.pull hf' A := by
  subst h
  rfl

/-- `1^*Θ̂ = Θ̂` for `T̂` vanishing off `X_∞`. -/
theorem pull_id_of_mem (A : OrientedBranched X) (hA : A.T ∈ X.X.GrHatSections) :
    OrientedBranched.pull (isGeneralizedIso_id X) A = A :=
  OrientedBranched.ext' (pullTheta_id_of_isFunctorial A.isBranchedEpSubgroupoid.isFunctorial)
    (pullSection_id_of_mem hA)

variable {n : ℕ}

/-- **The tame integral is invariant under pull-back** (Theorem 11.4.1 with `K = |supp Θ|`):
`∫_{f^*Θ̂'} f^*ω' = ∫_Θ̂' ω'`, for `A = f^*B` (both tame and compact). -/
theorem tameBranchedIntegral_pull {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) (hn : 0 < n)
    (A : OrientedBranched X) (B : OrientedBranched Y) (hAB : OrientedBranched.pull hf B = A)
    (hcptA : X.X.IsCompactBranched A.Θ)
    (hlocA : ∀ x ∈ supp A.Θ, ∃ C : X.X.OrientedTameStructure n A.Θ x, C.Represents A.T)
    (hcptB : Y.X.IsCompactBranched B.Θ)
    (hlocB : ∀ y ∈ supp B.Θ, ∃ C : Y.X.OrientedTameStructure n B.Θ y, C.Represents B.T)
    (ω' : Y.epFormsInfty n) :
    (X.epFormsInftyEval n).tameBranchedIntegral hn A.isBranchedEpSubgroupoid hcptA
        A.isOrientation hlocA (formsPullback f n ω') =
      (Y.epFormsInftyEval n).tameBranchedIntegral hn B.isBranchedEpSubgroupoid hcptB
        B.isOrientation hlocB ω' := by
  subst hAB
  exact integral_pull hf hn B.isBranchedEpSubgroupoid hcptB B.hasIndependentTangentSums
    B.isOrientation (FormEval.hcov_of_tameOpen (FormEval.tameOpen Y.X) hlocB) ω'

/-- **The effective tame integral is invariant under pull-back** (Theorem 11.4.2 with
`K = |supp f^*Θ'|`), for ep-groupoids with (LUC). -/
theorem tameBranchedIntegralEff_pull {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) (hn : 0 < n)
    (hLX : X.X.IsLUC) (hLY : Y.X.IsLUC)
    (A : OrientedBranched X) (B : OrientedBranched Y) (hAB : OrientedBranched.pull hf B = A)
    (hcptA : X.X.IsCompactBranched A.Θ)
    (hlocA : ∀ x ∈ supp A.Θ, ∃ C : X.X.OrientedTameStructure n A.Θ x, C.Represents A.T)
    (hcptB : Y.X.IsCompactBranched B.Θ)
    (hlocB : ∀ y ∈ supp B.Θ, ∃ C : Y.X.OrientedTameStructure n B.Θ y, C.Represents B.T)
    (ω' : Y.epFormsInfty n) :
    (X.epFormsInftyEval n).tameBranchedIntegralEff hn A.isBranchedEpSubgroupoid hcptA
        A.isOrientation (X.hloc_hasLUC hLX hlocA) (formsPullback f n ω') =
      (Y.epFormsInftyEval n).tameBranchedIntegralEff hn B.isBranchedEpSubgroupoid hcptB
        B.isOrientation (Y.hloc_hasLUC hLY hlocB) ω' := by
  subst hAB
  have h := (theorem_11_4_2_pull hf hn hLX hLY B.isBranchedEpSubgroupoid hcptB
    B.hasIndependentTangentSums B.isOrientation
    (FormEval.hcovEff_of_tameOpen (FormEval.tameOpen Y.X) (Y.hloc_hasLUC hLY hlocB)) ω'
    (K := univ) MeasurableSet.univ).2
  rw [image_univ, Subtype.range_coe, ← orbitSupp_eq_image_pullTheta hf B.isBranchedEpSubgroupoid,
    Subtype.coe_preimage_self] at h
  exact h

end EPLocalization.EPLoc

namespace PolyfoldClass

open EpGroupoid MPolyfold

variable {Z : Type u} [TopologicalSpace Z]

/-! ### Forms read on related structures -/

/-- For `f : p → q` with `α = β ∘ |f|`, the representative of `τ` on `p` is `f^*` of the one on
`q`. -/
theorem ScForm.toStructure_eq_formsPullback {c : PolyfoldClass Z} {k : ℕ}
    {p q : PolyfoldStructure Z} (hp : (⟦p⟧ : PolyfoldClass Z) = c)
    (hq : (⟦q⟧ : PolyfoldClass Z) = c) {f : EPLoc.of p.X ⟶ EPLoc.of q.X}
    (hf : IsGeneralizedIso f) (hβ : ⇑p.β = ⇑q.β ∘ orbitMap f) (τ : ScForm c k) :
    ScForm.toStructure p hp τ = formsPullback f k (ScForm.toStructure q hq τ) := by
  conv_rhs => rw [← ScForm.mk_toStructure p hp τ, ScForm.toStructure_mk_of hp hq _ hf hβ]
  obtain ⟨g, hfg, hgf⟩ := id hf
  rw [formsPush_eq_formsPullback hf hfg hgf, ← LinearMap.comp_apply, ← formsPullback_comp, hfg,
    formsPullback_id]
  rfl

/-! ### Definition 16.4.1 -/

/-- A representative `(Θ, (X, α))` of a branched suborbifold of `(Z, c)` (Definition 16.4.1). -/
structure BranchedRep (c : PolyfoldClass Z) : Type (u + 1) where
  /-- The polyfold structure `(X, α) ∈ c`. -/
  p : PolyfoldStructure Z
  mem : (⟦p⟧ : PolyfoldClass Z) = c
  /-- The branched ep⁺-subgroupoid `Θ : X → ℚ⁺`. -/
  Θ : p.X.Obj → ℚ
  isBranched : p.X.X.IsBranchedEpSubgroupoid Θ

variable {c : PolyfoldClass Z}

namespace BranchedRep

/-- **The relation of Definition 16.4.1** (2021 p. 730): `(Θ, (X, α)) ∼ (Θ', (X', α'))` if a
generalized isomorphism `f : X → X'` has `α' ∘ |f| = α` and `f^*Θ' = Θ`. -/
def Rel (a b : BranchedRep c) : Prop :=
  ∃ (f : EPLoc.of a.p.X ⟶ EPLoc.of b.p.X) (_ : IsGeneralizedIso f),
    ⇑a.p.β = ⇑b.p.β ∘ orbitMap f ∧ pullTheta f b.Θ = a.Θ

theorem Rel.refl (a : BranchedRep c) : Rel a a :=
  ⟨𝟙 _, isGeneralizedIso_id _, by rw [orbitMap_id]; rfl,
    pullTheta_id_of_isFunctorial a.isBranched.isFunctorial⟩

theorem Rel.symm {a b : BranchedRep c} (h : Rel a b) : Rel b a := by
  obtain ⟨f, hf, hβ, hΘ⟩ := h
  obtain ⟨g, hfg, hgf⟩ := id hf
  refine ⟨g, ⟨f, hgf, hfg⟩, ?_, ?_⟩
  · rw [hβ, Function.comp_assoc, ← proposition_10_3_11, hgf, orbitMap_id]
    rfl
  · rw [← hΘ, ← pullTheta_comp _ _ b.isBranched.isFunctorial, hgf,
      pullTheta_id_of_isFunctorial b.isBranched.isFunctorial]

theorem Rel.trans {a b e : BranchedRep c} (h₁ : Rel a b) (h₂ : Rel b e) : Rel a e := by
  obtain ⟨f, hf, hβ, hΘ⟩ := h₁
  obtain ⟨f', hf', hβ', hΘ'⟩ := h₂
  refine ⟨f ≫ f', isGeneralizedIso_comp hf hf', ?_, ?_⟩
  · rw [hβ, hβ', proposition_10_3_11]
    rfl
  · rw [pullTheta_comp _ _ e.isBranched.isFunctorial, hΘ', hΘ]

instance setoid (c : PolyfoldClass Z) : Setoid (BranchedRep c) where
  r := Rel
  iseqv := ⟨Rel.refl, Rel.symm, Rel.trans⟩

/-- `|Θ| ∘ α⁻¹ : Z → ℚ` on a representative. -/
def toFun (a : BranchedRep c) (z : Z) : ℚ := a.Θ (a.p.β.symm z).out

theorem toFun_eq (a : BranchedRep c) {z : Z} {x : a.p.X.Obj} (hx : a.p.β (a.p.X.X.π x) = z) :
    a.toFun z = a.Θ x := by
  have h : a.p.X.X.π (a.p.β.symm z).out = a.p.X.X.π x := by
    rw [← hx, Homeomorph.symm_apply_apply]
    exact Quotient.out_eq _
  obtain ⟨φ, hs, ht⟩ := (a.p.X.X.π_eq_π_iff).1 h
  rw [toFun, ← hs, ← ht]
  exact a.isBranched.isFunctorial φ

theorem toFun_eq_of_rel {a b : BranchedRep c} (h : Rel a b) : a.toFun = b.toFun := by
  obtain ⟨f, hf, hβ, hΘ⟩ := h
  funext z
  set x := (a.p.β.symm z).out
  obtain ⟨y, hy⟩ := b.p.X.X.surjective_π (orbitMap f (a.p.X.X.π x))
  have hx : a.p.β (a.p.X.X.π x) = z := by
    rw [show a.p.X.X.π x = a.p.β.symm z from Quotient.out_eq _, Homeomorph.apply_symm_apply]
  rw [a.toFun_eq hx, ← hΘ, pullTheta_eq_of_orbitMap hf b.isBranched.isFunctorial hy.symm,
    b.toFun_eq (z := z)]
  rw [hy, ← hx, hβ]
  rfl

end BranchedRep

/-- **2021 Definition 16.4.1, p. 730 (2017: Definition 16.29)**: the branched (weighted)
suborbifolds `θ = [Θ, (X, α)]` of the polyfold `(Z, c)`. -/
def BranchedSuborbifold (c : PolyfoldClass Z) : Type (u + 1) := Quotient (BranchedRep.setoid c)

namespace BranchedSuborbifold

/-- **The map `θ = |Θ| ∘ α⁻¹ : Z → ℚ⁺`** of Definition 16.4.1 (2021 p. 730). -/
def toFun (θ : BranchedSuborbifold c) : Z → ℚ :=
  Quotient.lift BranchedRep.toFun (fun _ _ h => BranchedRep.toFun_eq_of_rel h) θ

/-- **2021 Definition 16.4.1, p. 730**: `|Θ| ∘ α⁻¹ = |Θ'| ∘ α'⁻¹` for related representatives, so
`θ : Z → ℚ` is well defined; it is `|Θ| ∘ α⁻¹` for every representative. -/
theorem definition_16_4_1_wellDefined (a : BranchedRep c) {z : Z} {x : a.p.X.Obj}
    (hx : a.p.β (a.p.X.X.π x) = z) : toFun ⟦a⟧ z = a.Θ x :=
  a.toFun_eq hx

theorem toFun_nonneg (θ : BranchedSuborbifold c) (z : Z) : 0 ≤ θ.toFun z := by
  induction θ using Quotient.inductionOn with | h a => ?_
  exact a.isBranched.nonneg _

/-- `supp θ = {z | θ(z) > 0}` (Proposition 16.4.3). -/
def supp (θ : BranchedSuborbifold c) : Set Z := {z | 0 < θ.toFun z}

/-! ### Definition 16.4.2 -/

/-- Some representative of `θ` has the property `P`. -/
def HasRepProperty (P : ∀ X : EP.{u}, (X.Obj → ℚ) → Prop) (θ : BranchedSuborbifold c) : Prop :=
  ∃ a : BranchedRep c, ⟦a⟧ = θ ∧ P a.p.X a.Θ

/-- **For a property stable under pull-backs by generalized isomorphisms, some representative
has it iff all have it** (2021 p. 730). -/
theorem hasRepProperty_iff (P : ∀ X : EP.{u}, (X.Obj → ℚ) → Prop)
    (hP : ∀ {X Y : EP.{u}} {f : EPLoc.of X ⟶ EPLoc.of Y}, IsGeneralizedIso f →
      ∀ Θ' : Y.Obj → ℚ, Y.X.IsBranchedEpSubgroupoid Θ' → P Y Θ' → P X (pullTheta f Θ'))
    (θ : BranchedSuborbifold c) :
    HasRepProperty P θ ↔ ∀ a : BranchedRep c, ⟦a⟧ = θ → P a.p.X a.Θ := by
  refine ⟨fun ⟨b, hb, hPb⟩ a ha => ?_, fun h => ?_⟩
  · obtain ⟨f, hf, -, hΘ⟩ := (Quotient.exact (ha.trans hb.symm) : BranchedRep.Rel a b)
    rw [← hΘ]
    exact hP hf b.Θ b.isBranched hPb
  · obtain ⟨a, rfl⟩ := Quotient.exists_rep θ
    exact ⟨a, rfl, h a rfl⟩

/-- **Definition 16.4.2 (1)**, 2021 p. 730 (2017: Definition 16.30): `θ` is closed. -/
def IsClosed (θ : BranchedSuborbifold c) : Prop :=
  HasRepProperty (fun X Θ => X.X.IsClosedBranched Θ) θ

/-- **Definition 16.4.2 (2)**: `θ` is compact. -/
def IsCompact (θ : BranchedSuborbifold c) : Prop :=
  HasRepProperty (fun X Θ => X.X.IsCompactBranched Θ) θ

/-- **Definition 16.4.2 (3)**: `θ` is of manifold-type. -/
def IsManifoldType (θ : BranchedSuborbifold c) : Prop :=
  HasRepProperty (fun X Θ => X.X.IsManifoldType Θ) θ

/-- **Definition 16.4.2 (4)**: `θ` is of orbifold-type. -/
def IsOrbifoldType (θ : BranchedSuborbifold c) : Prop :=
  HasRepProperty (fun _ Θ => EpGroupoid.IsOrbifoldType Θ) θ

/-- `θ` is `n`-dimensional (Theorem 11.3.3 (6), used in Theorem 16.4.6). -/
def IsNDimensional (θ : BranchedSuborbifold c) (n : ℕ) : Prop :=
  HasRepProperty (fun X Θ => X.X.IsNDimensional Θ n) θ

/-- **Definition 16.4.2 (5)**: `θ` is tame, i.e. a representative `Θ` is tame (Definition 9.3.6).
That then every representative is tame (2021 p. 729) is not formalized. -/
def IsTame (θ : BranchedSuborbifold c) : Prop :=
  HasRepProperty (fun X Θ => X.X.IsTameBranched Θ) θ

/-- **Definition 16.4.2 (1) is well posed** (Theorem 11.3.3 (3)). -/
theorem definition_16_4_2_closed (θ : BranchedSuborbifold c) :
    θ.IsClosed ↔ ∀ a : BranchedRep c, ⟦a⟧ = θ → a.p.X.X.IsClosedBranched a.Θ :=
  hasRepProperty_iff _ (fun hf _ hΘ' h =>
    (theorem_11_3_3_three hf (Θ := fun _ => 0) (fun _ => rfl) hΘ'.isFunctorial).2 h) θ

/-- **Definition 16.4.2 (2) is well posed** (Theorem 11.3.3 (4)). -/
theorem definition_16_4_2_compact (θ : BranchedSuborbifold c) :
    θ.IsCompact ↔ ∀ a : BranchedRep c, ⟦a⟧ = θ → a.p.X.X.IsCompactBranched a.Θ :=
  hasRepProperty_iff _ (fun hf _ hΘ' h =>
    (theorem_11_3_3_four hf (Θ := fun _ => 0) (fun _ => rfl) hΘ'.isFunctorial).2 h) θ

/-- **Definition 16.4.2 (3) is well posed** (Theorem 11.3.3 (5)). -/
theorem definition_16_4_2_manifold (θ : BranchedSuborbifold c) :
    θ.IsManifoldType ↔ ∀ a : BranchedRep c, ⟦a⟧ = θ → a.p.X.X.IsManifoldType a.Θ :=
  hasRepProperty_iff _ (fun hf _ hΘ' h =>
    (theorem_11_3_3_five hf (Θ := fun _ => 0) (fun _ => rfl) hΘ'.isFunctorial).2.2.2 h) θ

/-- **Definition 16.4.2 (4) is well posed** (Theorem 11.3.3 (5)). -/
theorem definition_16_4_2_orbifold (θ : BranchedSuborbifold c) :
    θ.IsOrbifoldType ↔ ∀ a : BranchedRep c, ⟦a⟧ = θ → EpGroupoid.IsOrbifoldType a.Θ :=
  hasRepProperty_iff _ (fun hf _ hΘ' h =>
    (theorem_11_3_3_five hf (Θ := fun _ => 0) (fun _ => rfl) hΘ'.isFunctorial).2.1 h) θ

/-- `n`-dimensionality is well posed (Theorem 11.3.3 (6)). -/
theorem definition_16_4_2_nDim (θ : BranchedSuborbifold c) (n : ℕ) :
    θ.IsNDimensional n ↔ ∀ a : BranchedRep c, ⟦a⟧ = θ → a.p.X.X.IsNDimensional a.Θ n :=
  hasRepProperty_iff _ (fun hf _ hΘ' h => isNDimensional_pullTheta hf hΘ'.isFunctorial h) θ

/-! ### Proposition 16.4.3 -/

/-- **Proposition 16.4.3, the set** (2021 p. 730; 2017: Proposition 16.6):
`supp θ = α(|supp Θ|)` for every representative. -/
theorem proposition_16_4_3_supp (a : BranchedRep c) :
    supp ⟦a⟧ = a.p.β '' a.p.X.X.orbitSupp a.Θ := by
  ext z
  constructor
  · intro hz
    refine ⟨a.p.β.symm z, ⟨(a.p.β.symm z).out, ?_, Quotient.out_eq _⟩,
      Homeomorph.apply_symm_apply _ _⟩
    exact hz
  · rintro ⟨q, ⟨x, hx, rfl⟩, rfl⟩
    change 0 < toFun ⟦a⟧ _
    rw [definition_16_4_1_wellDefined a rfl]
    exact hx

/-- **Proposition 16.4.3, the topology**: `α` restricts to a homeomorphism `|supp Θ| ≃ₜ supp θ`. -/
def proposition_16_4_3_homeomorph (a : BranchedRep c) :
    a.p.X.X.orbitSupp a.Θ ≃ₜ supp ⟦a⟧ :=
  (a.p.β.image _).trans (Homeomorph.setCongr (proposition_16_4_3_supp a).symm)

theorem proposition_16_4_3_homeomorph_apply (a : BranchedRep c)
    (q : a.p.X.X.orbitSupp a.Θ) : (proposition_16_4_3_homeomorph a q : Z) = a.p.β q :=
  rfl

/-- **Proposition 16.4.3, manifold-type** (with Proposition 9.1.9 (1)): for every representative,
`supp θ ≃ₜ |supp Θ|` and `|supp Θ|` carries the M-polyfold structure induced by `X`, for which
`supp Θ → |supp Θ|` is a local sc-diffeomorphism. -/
theorem proposition_16_4_3_manifold (a : BranchedRep c) (hm : a.p.X.X.IsManifoldType a.Θ) :
    Nonempty (a.p.X.X.orbitSupp a.Θ ≃ₜ supp ⟦a⟧) ∧
      ∃ hA : a.p.X.X.IsEpSubgroupoid (EpGroupoid.supp a.Θ),
        a.p.X.X.PObj.IsSmoothSubmanifold (EpGroupoid.supp a.Θ) ∧
        haveI := a.p.X.X.PObj.paracompactSpace_subtype (EpGroupoid.supp a.Θ)
        haveI := a.isBranched.paracompactSpace_orbitSupp
        ∃ PZ : MPolyfold (a.p.X.X.orbitSupp a.Θ),
          (subEpGroupoid hA).PObj.IsLocalScDiffeo PZ (a.p.X.X.orbitSuppProj a.Θ) :=
  ⟨⟨proposition_16_4_3_homeomorph a⟩, a.p.X.X.proposition_9_1_9_one a.isBranched hm⟩

/-- **Proposition 16.4.3, orbifold-type** (with Proposition 9.1.9 (2)): for every representative,
`supp θ ≃ₜ |supp Θ|`, and `|supp Θ|` is the orbit space of the ep-groupoid on `supp Θ`. -/
theorem proposition_16_4_3_orbifold (a : BranchedRep c) (ho : EpGroupoid.IsOrbifoldType a.Θ) :
    Nonempty (a.p.X.X.orbitSupp a.Θ ≃ₜ supp ⟦a⟧) ∧
      ∃ hA : a.p.X.X.IsEpSubgroupoid (EpGroupoid.supp a.Θ),
        a.p.X.X.PObj.IsSmoothSubmanifold (EpGroupoid.supp a.Θ) ∧
        haveI := a.p.X.X.PObj.paracompactSpace_subtype (EpGroupoid.supp a.Θ)
        ∃ e : (subEpGroupoid hA).OrbitSpace ≃ₜ a.p.X.X.orbitSupp a.Θ,
          ∀ x : EpGroupoid.supp a.Θ,
            (e ((subEpGroupoid hA).π x) : a.p.X.X.OrbitSpace) = a.p.X.X.π x.1 :=
  ⟨⟨proposition_16_4_3_homeomorph a⟩, a.p.X.X.proposition_9_1_9_two a.isBranched ho⟩

end BranchedSuborbifold

/-! ### Definition 16.4.4 -/

/-- A representative `((Θ, T̂_Θ), (X, α))` of an oriented branched suborbifold (Definition
16.4.4).  `T̂` is taken zero off `X_∞` (it is only read there: `EPLoc.pullSection_congr`). -/
structure OrientedRep (c : PolyfoldClass Z) : Type (u + 1) where
  /-- The polyfold structure `(X, α) ∈ c`. -/
  p : PolyfoldStructure Z
  mem : (⟦p⟧ : PolyfoldClass Z) = c
  /-- The oriented branched ep⁺-subgroupoid `(Θ, T̂_Θ)`. -/
  A : OrientedBranched p.X
  smooth : ∀ x, x ∉ p.X.X.PObj.smoothSet → A.T x = 0

namespace OrientedRep

theorem mem_grHatSections (a : OrientedRep c) : a.A.T ∈ a.p.X.X.GrHatSections :=
  ⟨a.A.isOrientation.isGrHatSection, a.smooth⟩

/-- **The relation of Definition 16.4.4** (2021 p. 731): `f^*(Θ', T̂_Θ') = (Θ, T̂_Θ)` and
`α' ∘ |f| = α`. -/
def Rel (a b : OrientedRep c) : Prop :=
  ∃ (f : EPLoc.of a.p.X ⟶ EPLoc.of b.p.X) (hf : IsGeneralizedIso f),
    ⇑a.p.β = ⇑b.p.β ∘ orbitMap f ∧ OrientedBranched.pull hf b.A = a.A

theorem Rel.refl (a : OrientedRep c) : Rel a a :=
  ⟨𝟙 _, isGeneralizedIso_id _, by rw [orbitMap_id]; rfl, pull_id_of_mem a.A a.mem_grHatSections⟩

theorem Rel.symm {a b : OrientedRep c} (h : Rel a b) : Rel b a := by
  obtain ⟨f, hf, hβ, hA⟩ := h
  obtain ⟨g, hfg, hgf⟩ := id hf
  have hg : IsGeneralizedIso g := ⟨f, hgf, hfg⟩
  refine ⟨g, hg, ?_, ?_⟩
  · rw [hβ, Function.comp_assoc, ← proposition_10_3_11, hgf, orbitMap_id]
    rfl
  · rw [← hA, ← OrientedBranched.pull_comp hg hf (isGeneralizedIso_comp hg hf),
      pull_congr _ (isGeneralizedIso_id _) hgf, pull_id_of_mem b.A b.mem_grHatSections]

theorem Rel.trans {a b e : OrientedRep c} (h₁ : Rel a b) (h₂ : Rel b e) : Rel a e := by
  obtain ⟨f, hf, hβ, hA⟩ := h₁
  obtain ⟨f', hf', hβ', hA'⟩ := h₂
  refine ⟨f ≫ f', isGeneralizedIso_comp hf hf', ?_, ?_⟩
  · rw [hβ, hβ', proposition_10_3_11]
    rfl
  · rw [OrientedBranched.pull_comp hf hf', hA', hA]

instance setoid (c : PolyfoldClass Z) : Setoid (OrientedRep c) where
  r := Rel
  iseqv := ⟨Rel.refl, Rel.symm, Rel.trans⟩

/-- The underlying branched representative. -/
def toBranchedRep (a : OrientedRep c) : BranchedRep c :=
  ⟨a.p, a.mem, a.A.Θ, a.A.isBranchedEpSubgroupoid⟩

theorem Rel.toBranchedRep {a b : OrientedRep c} (h : Rel a b) :
    BranchedRep.Rel a.toBranchedRep b.toBranchedRep := by
  obtain ⟨f, hf, hβ, hA⟩ := h
  exact ⟨f, hf, hβ, congrArg OrientedBranched.Θ hA⟩

end OrientedRep

/-- **2021 Definition 16.4.4, p. 730 (2017: Definition 16.31)**: the oriented branched
suborbifolds `θ̂ = [(Θ, T̂_Θ), (X, α)]` of `(Z, c)`. -/
def OrientedSuborbifold (c : PolyfoldClass Z) : Type (u + 1) := Quotient (OrientedRep.setoid c)

/-- The underlying branched suborbifold `θ` of `θ̂`. -/
def OrientedSuborbifold.toBranched (θ : OrientedSuborbifold c) : BranchedSuborbifold c :=
  Quotient.map OrientedRep.toBranchedRep (fun _ _ h => OrientedRep.Rel.toBranchedRep h) θ

/-! ### Definition 16.4.5 -/

/-- **2021 Definition 16.4.5, p. 731 (2017: Definition 16.34), well posed**: if
`((Θ, T̂), (X, α)) ∼ ((Θ', T̂'), (X', α'))` via `f`, then `f^*` carries
`∂(Θ', T̂') = (∂Θ', T̂_∂Θ')` to
`∂(Θ, T̂)` (Theorem 11.3.9), so `∂θ̂ = [∂(Θ, T̂_Θ), (X, α)]` does not depend on the
representative.  (`∂(Θ, T̂)` is formalized componentwise: `boundaryTheta`,
`boundaryOrientation`.) -/
theorem definition_16_4_5_wellDefined {a b : OrientedRep c} (h : OrientedRep.Rel a b) :
    ∃ (f : EPLoc.of a.p.X ⟶ EPLoc.of b.p.X) (_ : IsGeneralizedIso f),
      ⇑a.p.β = ⇑b.p.β ∘ orbitMap f ∧
      pullTheta f (b.p.X.X.boundaryTheta b.A.Θ) = a.p.X.X.boundaryTheta a.A.Θ ∧
      pullSection f (b.p.X.X.boundaryOrientation b.A.T) = a.p.X.X.boundaryOrientation a.A.T := by
  obtain ⟨f, hf, hβ, hA⟩ := h
  obtain ⟨h1, h2⟩ := theorem_11_3_9_pull_boundaryOrientation hf b.A.isBranchedEpSubgroupoid
    b.A.hasIndependentTangentSums b.A.isOrientation.isGrHatSection
  refine ⟨f, hf, hβ, ?_, ?_⟩
  · rw [h1, ← hA]
    rfl
  · rw [h2, ← hA]
    rfl

/-- The boundary support function `∂θ = |∂Θ| ∘ α⁻¹ : Z → ℚ` on a representative. -/
def OrientedRep.boundaryFun (a : OrientedRep c) (z : Z) : ℚ :=
  a.p.X.X.boundaryTheta a.A.Θ (a.p.β.symm z).out

/-- `∂θ : Z → ℚ` does not depend on the representative (so `∂S = supp ∂θ` does not either). -/
theorem OrientedRep.boundaryFun_eq_of_rel {a b : OrientedRep c} (h : OrientedRep.Rel a b) :
    a.boundaryFun = b.boundaryFun := by
  obtain ⟨f, hf, hβ, h1, -⟩ := definition_16_4_5_wellDefined h
  have hfa := isFunctorial_boundaryTheta a.A.isBranchedEpSubgroupoid a.A.hasIndependentTangentSums
  have hfb := isFunctorial_boundaryTheta b.A.isBranchedEpSubgroupoid b.A.hasIndependentTangentSums
  funext z
  set x := (a.p.β.symm z).out
  obtain ⟨y, hy⟩ := b.p.X.X.surjective_π (orbitMap f (a.p.X.X.π x))
  have hx : a.p.β (a.p.X.X.π x) = z := by
    rw [show a.p.X.X.π x = a.p.β.symm z from Quotient.out_eq _, Homeomorph.apply_symm_apply]
  have hyz : b.p.X.X.π (b.p.β.symm z).out = b.p.X.X.π y := by
    rw [show b.p.X.X.π (b.p.β.symm z).out = b.p.β.symm z from Quotient.out_eq _, hy, ← hx, hβ]
    exact Homeomorph.symm_apply_apply _ _
  obtain ⟨φ, hs, ht⟩ := (b.p.X.X.π_eq_π_iff).1 hyz
  change a.p.X.X.boundaryTheta a.A.Θ x = b.p.X.X.boundaryTheta b.A.Θ (b.p.β.symm z).out
  rw [← h1, pullTheta_eq_of_orbitMap hf hfb hy.symm, ← hs, hfb φ, ht]

/-! ### The integrals and their independence of the representative -/

namespace OrientedRep

variable {n m : ℕ}

/-- `Θ̂` is tame of dimension `n` in the form of Chapter 9 (oriented tame structures describing
`T̂_Θ` at every point of `supp Θ`, Definition 9.5.6). -/
def IsTameOriented (a : OrientedRep c) (n : ℕ) : Prop :=
  ∀ x ∈ EpGroupoid.supp a.A.Θ, ∃ C : a.p.X.X.OrientedTameStructure n a.A.Θ x, C.Represents a.A.T

/-- **The branched integral `∫_θ̂ τ = µ^Θ̂_ω(|supp Θ|)`** (2021 p. 732) on a tame compact
representative, `ω` the representative of `τ` on `(X, α)`. -/
def integral (a : OrientedRep c) (hn : 0 < n) (hcpt : a.p.X.X.IsCompactBranched a.A.Θ)
    (hloc : a.IsTameOriented n) (τ : ScForm c n) : ℝ :=
  (a.p.X.epFormsInftyEval n).tameBranchedIntegral hn a.A.isBranchedEpSubgroupoid hcpt
    a.A.isOrientation hloc (ScForm.toStructure a.p a.mem τ)

/-- **The effective branched integral `∮_θ̂ τ = µ^{Θ̂,eff}_ω(|supp Θ|)`** (2021 p. 732); (ZHOU)
gives (LUC) (Proposition 7.4.10). -/
def integralEff (a : OrientedRep c) (hn : 0 < n) (hcpt : a.p.X.X.IsCompactBranched a.A.Θ)
    (hloc : a.IsTameOriented n) (τ : ScForm c n) : ℝ :=
  (a.p.X.epFormsInftyEval n).tameBranchedIntegralEff hn a.A.isBranchedEpSubgroupoid hcpt
    a.A.isOrientation (a.p.X.hloc_hasLUC (a.p.X.X.proposition_7_4_10_of_isZhou a.p.isZhou) hloc)
    (ScForm.toStructure a.p a.mem τ)

/-- **The integral does not depend on the representative** (2021 p. 732), among tame compact
representatives. -/
theorem integral_eq_of_rel {a b : OrientedRep c} (h : Rel a b) (hn : 0 < n)
    (hcpta : a.p.X.X.IsCompactBranched a.A.Θ) (hloca : a.IsTameOriented n)
    (hcptb : b.p.X.X.IsCompactBranched b.A.Θ) (hlocb : b.IsTameOriented n) (τ : ScForm c n) :
    a.integral hn hcpta hloca τ = b.integral hn hcptb hlocb τ := by
  obtain ⟨f, hf, hβ, hA⟩ := h
  unfold integral
  rw [ScForm.toStructure_eq_formsPullback a.mem b.mem hf hβ τ]
  exact tameBranchedIntegral_pull hf hn a.A b.A hA hcpta hloca hcptb hlocb _

/-- **The effective integral does not depend on the representative** (2021 p. 732). -/
theorem integralEff_eq_of_rel {a b : OrientedRep c} (h : Rel a b) (hn : 0 < n)
    (hcpta : a.p.X.X.IsCompactBranched a.A.Θ) (hloca : a.IsTameOriented n)
    (hcptb : b.p.X.X.IsCompactBranched b.A.Θ) (hlocb : b.IsTameOriented n) (τ : ScForm c n) :
    a.integralEff hn hcpta hloca τ = b.integralEff hn hcptb hlocb τ := by
  obtain ⟨f, hf, hβ, hA⟩ := h
  unfold integralEff
  rw [ScForm.toStructure_eq_formsPullback a.mem b.mem hf hβ τ]
  exact tameBranchedIntegralEff_pull hf hn (a.p.X.X.proposition_7_4_10_of_isZhou a.p.isZhou)
    (b.p.X.X.proposition_7_4_10_of_isZhou b.p.isZhou) a.A b.A hA hcpta hloca hcptb hlocb _

/-- **The boundary integral `∫_∂θ̂ τ = µ^{∂Θ̂}_ω(|supp ∂Θ|)`** (2021 p. 732, Theorem 9.5.15),
`τ` of degree `m ≥ 1`, `θ̂` of dimension `m + 1`. -/
def boundaryIntegral (a : OrientedRep c) (hm : 0 < m) (hcpt : a.p.X.X.IsCompactBranched a.A.Θ)
    (hloc : a.IsTameOriented (m + 1)) (τ : ScForm c m) : ℝ :=
  a.p.X.boundaryMeasure hm a.A.isBranchedEpSubgroupoid hcpt a.A.isOrientation hloc
    (ScForm.toStructure a.p a.mem τ) univ

/-- **The effective boundary integral `∮_∂θ̂ τ`** (2021 p. 732, Theorem 9.5.16). -/
def boundaryIntegralEff (a : OrientedRep c) (hm : 0 < m)
    (hcpt : a.p.X.X.IsCompactBranched a.A.Θ) (hloc : a.IsTameOriented (m + 1))
    (τ : ScForm c m) : ℝ :=
  a.p.X.boundaryMeasureEff hm (a.p.X.X.proposition_7_4_10_of_isZhou a.p.isZhou)
    a.A.isBranchedEpSubgroupoid hcpt a.A.isOrientation hloc (ScForm.toStructure a.p a.mem τ) univ

/-- The boundary integral for `θ̂` of dimension `1` (Theorem 9.5.15 for `n = 1`). -/
def boundaryIntegralDim1 (a : OrientedRep c) (hcpt : a.p.X.X.IsCompactBranched a.A.Θ)
    (hloc : a.IsTameOriented (0 + 1)) (τ : ScForm c 0) : ℝ :=
  a.p.X.boundaryBranchedMeasureDim1 a.A.isBranchedEpSubgroupoid hcpt a.A.isOrientation hloc
    (ScForm.toStructure a.p a.mem τ) univ

/-- The effective boundary integral for `θ̂` of dimension `1` (Theorem 9.5.16 for `n = 1`). -/
def boundaryIntegralEffDim1 (a : OrientedRep c) (hcpt : a.p.X.X.IsCompactBranched a.A.Θ)
    (hloc : a.IsTameOriented (0 + 1)) (τ : ScForm c 0) : ℝ :=
  a.p.X.boundaryBranchedMeasureEffDim1 a.A.isBranchedEpSubgroupoid hcpt a.A.isOrientation
    (a.p.X.hloc_hasLUC_dim1 (a.p.X.X.proposition_7_4_10_of_isZhou a.p.isZhou) hloc)
    (ScForm.toStructure a.p a.mem τ) univ

theorem toStructure_d (a : OrientedRep c) (τ : ScForm c m) :
    ScForm.toStructure a.p a.mem (ScForm.d τ) =
      a.p.X.epFormsInftyD m (ScForm.toStructure a.p a.mem τ) := by
  rw [ScForm.d_apply, ScForm.toStructure_dFun]

end OrientedRep

/-! ### Theorem 16.4.6 -/

namespace OrientedRep

variable {m : ℕ}

/-- **2021 Theorem 16.4.6 (Stokes), p. 732 (2017: Theorem 16.5), branched integration, `n ≥ 2`**,
with the added hypothesis `_hyp` that `c` admits sc-smooth partitions of unity (Definition 16.1.5;
Theorem 9.5.17 assumes them): for `θ̂ = [(Θ, T̂_Θ), (X, α)]` oriented, tame, compact, of dimension
`m + 1` and `τ` of degree `m ≥ 1`, `∫_θ̂ dτ = ∫_∂θ̂ τ`.  Witness: `theorem_16_4_6_hyp_witness`. -/
theorem theorem_16_4_6_hyp (hPU : c.AdmitsScPartitionsOfUnity) (a : OrientedRep c) (hm : 0 < m)
    (hcpt : a.p.X.X.IsCompactBranched a.A.Θ) (hloc : a.IsTameOriented (m + 1))
    (τ : ScForm c m) :
    a.integral (Nat.succ_pos m) hcpt hloc (ScForm.d τ) = a.boundaryIntegral hm hcpt hloc τ := by
  unfold integral boundaryIntegral
  rw [toStructure_d]
  exact a.p.X.theorem_9_5_17 hm ((c.definition_16_1_5_two).1 hPU a.p a.mem)
    a.A.isBranchedEpSubgroupoid hcpt a.A.isOrientation hloc _

/-- **2021 Theorem 16.4.6 (Stokes), effective branched integration, `n ≥ 2`**, with the added
hypothesis `_hyp` (partitions of unity): `∮_θ̂ dτ = ∮_∂θ̂ τ`.  (LUC) comes from (ZHOU). -/
theorem theorem_16_4_6_eff_hyp (hPU : c.AdmitsScPartitionsOfUnity) (a : OrientedRep c)
    (hm : 0 < m) (hcpt : a.p.X.X.IsCompactBranched a.A.Θ) (hloc : a.IsTameOriented (m + 1))
    (τ : ScForm c m) :
    a.integralEff (Nat.succ_pos m) hcpt hloc (ScForm.d τ) =
      a.boundaryIntegralEff hm hcpt hloc τ := by
  unfold integralEff boundaryIntegralEff
  rw [toStructure_d]
  exact a.p.X.theorem_9_5_18 hm ((c.definition_16_1_5_two).1 hPU a.p a.mem)
    (a.p.X.X.proposition_7_4_10_of_isZhou a.p.isZhou)
    a.A.isBranchedEpSubgroupoid hcpt a.A.isOrientation hloc _

/-- **2021 Theorem 16.4.6 (Stokes), branched integration, `n = 1`**, with the added hypothesis
`_hyp` (partitions of unity). -/
theorem theorem_16_4_6_dim1_hyp (hPU : c.AdmitsScPartitionsOfUnity) (a : OrientedRep c)
    (hcpt : a.p.X.X.IsCompactBranched a.A.Θ) (hloc : a.IsTameOriented (0 + 1))
    (τ : ScForm c 0) :
    a.integral (Nat.succ_pos 0) hcpt hloc (ScForm.d τ) = a.boundaryIntegralDim1 hcpt hloc τ := by
  unfold integral boundaryIntegralDim1
  rw [toStructure_d]
  exact a.p.X.theorem_9_5_17_dim1 ((c.definition_16_1_5_two).1 hPU a.p a.mem)
    a.A.isBranchedEpSubgroupoid hcpt a.A.isOrientation hloc _

/-- **2021 Theorem 16.4.6 (Stokes), effective branched integration, `n = 1`**, with the added
hypothesis `_hyp` (partitions of unity). -/
theorem theorem_16_4_6_eff_dim1_hyp (hPU : c.AdmitsScPartitionsOfUnity) (a : OrientedRep c)
    (hcpt : a.p.X.X.IsCompactBranched a.A.Θ) (hloc : a.IsTameOriented (0 + 1))
    (τ : ScForm c 0) :
    a.integralEff (Nat.succ_pos 0) hcpt hloc (ScForm.d τ) =
      a.boundaryIntegralEffDim1 hcpt hloc τ := by
  unfold integralEff boundaryIntegralEffDim1
  rw [toStructure_d]
  exact a.p.X.theorem_9_5_18_dim1 ((c.definition_16_1_5_two).1 hPU a.p a.mem)
    a.A.isBranchedEpSubgroupoid hcpt a.A.isOrientation _ _

/-- **The boundary integral does not depend on the representative** (2021 p. 732), among tame
compact representatives of dimension `m + 1 ≥ 2`, when `c` admits partitions of unity: both are
`∫_θ̂ dτ`. -/
theorem boundaryIntegral_eq_of_rel (hPU : c.AdmitsScPartitionsOfUnity) {a b : OrientedRep c}
    (h : Rel a b) (hm : 0 < m)
    (hcpta : a.p.X.X.IsCompactBranched a.A.Θ) (hloca : a.IsTameOriented (m + 1))
    (hcptb : b.p.X.X.IsCompactBranched b.A.Θ) (hlocb : b.IsTameOriented (m + 1))
    (τ : ScForm c m) :
    a.boundaryIntegral hm hcpta hloca τ = b.boundaryIntegral hm hcptb hlocb τ := by
  rw [← theorem_16_4_6_hyp hPU a hm, ← theorem_16_4_6_hyp hPU b hm]
  exact integral_eq_of_rel h _ _ _ _ _ _

/-- The effective boundary integral does not depend on the representative (`n ≥ 2`, partitions
of unity). -/
theorem boundaryIntegralEff_eq_of_rel (hPU : c.AdmitsScPartitionsOfUnity) {a b : OrientedRep c}
    (h : Rel a b) (hm : 0 < m)
    (hcpta : a.p.X.X.IsCompactBranched a.A.Θ) (hloca : a.IsTameOriented (m + 1))
    (hcptb : b.p.X.X.IsCompactBranched b.A.Θ) (hlocb : b.IsTameOriented (m + 1))
    (τ : ScForm c m) :
    a.boundaryIntegralEff hm hcpta hloca τ = b.boundaryIntegralEff hm hcptb hlocb τ := by
  rw [← theorem_16_4_6_eff_hyp hPU a hm, ← theorem_16_4_6_eff_hyp hPU b hm]
  exact integralEff_eq_of_rel h _ _ _ _ _ _

/-- The boundary integrals for `n = 1` do not depend on the representative (partitions of
unity). -/
theorem boundaryIntegralDim1_eq_of_rel (hPU : c.AdmitsScPartitionsOfUnity) {a b : OrientedRep c}
    (h : Rel a b)
    (hcpta : a.p.X.X.IsCompactBranched a.A.Θ) (hloca : a.IsTameOriented (0 + 1))
    (hcptb : b.p.X.X.IsCompactBranched b.A.Θ) (hlocb : b.IsTameOriented (0 + 1))
    (τ : ScForm c 0) :
    a.boundaryIntegralDim1 hcpta hloca τ = b.boundaryIntegralDim1 hcptb hlocb τ ∧
      a.boundaryIntegralEffDim1 hcpta hloca τ = b.boundaryIntegralEffDim1 hcptb hlocb τ := by
  refine ⟨?_, ?_⟩
  · rw [← theorem_16_4_6_dim1_hyp hPU a, ← theorem_16_4_6_dim1_hyp hPU b]
    exact integral_eq_of_rel h _ _ _ _ _ _
  · rw [← theorem_16_4_6_eff_dim1_hyp hPU a, ← theorem_16_4_6_eff_dim1_hyp hPU b]
    exact integralEff_eq_of_rel h _ _ _ _ _ _

/-- **Theorem 16.4.6, all four identities**, for a tame compact oriented representative of
dimension `m + 1 ≥ 2`. -/
theorem theorem_16_4_6_both_hyp (hPU : c.AdmitsScPartitionsOfUnity) (a : OrientedRep c)
    (hm : 0 < m) (hcpt : a.p.X.X.IsCompactBranched a.A.Θ) (hloc : a.IsTameOriented (m + 1))
    (τ : ScForm c m) :
    a.integral (Nat.succ_pos m) hcpt hloc (ScForm.d τ) = a.boundaryIntegral hm hcpt hloc τ ∧
      a.integralEff (Nat.succ_pos m) hcpt hloc (ScForm.d τ) =
        a.boundaryIntegralEff hm hcpt hloc τ :=
  ⟨theorem_16_4_6_hyp hPU a hm hcpt hloc τ, theorem_16_4_6_eff_hyp hPU a hm hcpt hloc τ⟩

/-- **Satisfiability of the added hypothesis** of `theorem_16_4_6_hyp`: `[ℤ/3 ⋉ ℝ]` admits
sc-smooth partitions of unity. -/
theorem theorem_16_4_6_hyp_witness : PolyfoldStructure.z3Polyfold.AdmitsScPartitionsOfUnity :=
  PolyfoldStructure.z3Polyfold_admitsScPartitionsOfUnity

end OrientedRep

end PolyfoldClass

end Polyfold
