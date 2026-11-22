import Polyfold.Chapter17.ModelProperties
import Polyfold.Chapter17.ModelExamples
import Polyfold.Chapter17.LevelOneCategory

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.1 (pp. 758–767): witnesses for Definition 17.1.22, Propositions 17.1.23–17.1.25,
Theorems 17.1.26, 17.1.28, Corollary 17.1.29 and Definition 17.1.30, and **Proposition 17.1.25
does not hold as we read it**.  Numbers and pages are
the 2021 text's.

# Models of translation GCTs, and Proposition 17.1.25

## The model of one uniformizer whose footprint is `|C|`

For a uniformizer `Ψ_λ : G ⋉ O → C` of a family `Ψ` with `Ψ̂_λ` continuous,
`pieceFunctor Ψ λ : G ⋉ O → X_Ψ` (`q ↦ q_λ`, `(g, q) ↦ Ψ̂_λ(g, q)`) is an sc-smooth functor, and
it is an equivalence of ep-groupoids (Definition 10.1.1) when the footprint of `Ψ_λ` is `|C|`
(`isEquivalence_pieceFunctor`).  So every property invariant under generalized isomorphisms
holds for `C` iff it holds for `G ⋉ O` (`hasModelProperty_iff_piece`).

For the translation GCT `K ⋉ U` with the tautological polyfold structure (`tautConstruction`,
Chapter 17's `twistConstruction` with the identity twist) and the covering family
`tautSingleFamily` of the tautological uniformizer, `tautModelFunctor : K ⋉ U → X_Ψ` is such an
equivalence (`isEquivalence_tautModelFunctor`).

## Proposition 17.1.25 does not hold as we read it

`C = ℤ/3 ⋉ ℝ` with the trivial action (`z3TautConstruction`): its model is equivalent to the
ep-groupoid `ℤ/3 × ℝ ⇉ ℝ` of `not_theorem_10_3_19`, so `C` satisfies (ZHOU), hence (LUC), (SLUC),
(LR), (SLR) (`z3Taut_properties`).  For the one-element covering family `Ψ`, `f_{Ψ,Ψ} = 1`
(Theorem 17.1.18), and `h = e⁻¹ ∘ [Inv] ∘ e` (`e : ℤ/3 × ℝ ⇉ ℝ → X_Ψ` the equivalence,
`[Inv] = [X ←1 X →Inv X]`) is a generalized isomorphism with `|Γ_Ψ| ∘ |h| = |Γ_Ψ|` and `h ≠ 1`
(`z3Taut_counterexample`).  Hence `not_proposition_17_1_25` (the printed (LUC) reading) and
`not_proposition_17_1_25_LR` (the (LR) reading).  The model is not effective
(`not_isEffective_z3Taut`).

## Witnesses for the forms we prove and for Theorem 17.1.26

* (ZHOU), hence all five properties of Definition 17.1.22, and the class `c_C` of Theorem
  17.1.26, for `C = ℤ/3 ⋉ ℝ` (isotropy `ℤ/3` everywhere): `z3Taut_properties`,
  `z3Taut_polyfoldClass`.
* Effectiveness of `C` (the effectiveness hypothesis of `proposition_17_1_25_of_isEffective'`) with
  non-trivial isotropy: the reflection GCT `ℤ/2 ⋉ ℝ` (`reflection_isEffective`; it also has
  (LUC), `reflection_isLUC`).
* (LR) and effectiveness together: the translation GCT of the trivial group on `ℝ`
  (`unitTaut_isLR_isEffective`, with the conclusion of Proposition 17.1.25 for it,
  `unitTaut_proposition_17_1_25`).

## Witnesses for the levels, `C¹` and the boundary

* `z3Taut_hasCoveringUniformizers` (the hypothesis of the topology of `|C_1|`) and
  `z3Taut_levelOne`: for `ℤ/3 ⋉ ℝ`, the class of polyfold structures on `|C¹|`
  (Theorem 17.1.28), (ZHOU), (SLUC), (SLR) for `X_Ψ¹` (Corollary 17.1.29), and `|C¹|` as the
  raised polyfold `(|C|, c_C)¹`.
* `cornerTautConstruction` (`{1} ⋉ [0, ∞)`): `d(0) = 1` (`cornerTaut_degIndex_zero`), so
  `∂C ≠ ∅` (`cornerTaut_boundarySet_nonempty`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology CategoryTheory

noncomputable section

universe u

namespace Polyfold

open EPLocalization EPLocalization.EPLoc

namespace GCT.PolyfoldConstruction

/-! ### The piece functor `G_λ ⋉ O_λ → X_Ψ` -/

section Piece

variable {C : GCT.{u}} {S : C.PolyfoldConstruction} {ι : Type u} (Ψ : ι → S.Unif)

/-- **The functor `G_λ ⋉ O_λ → X_Ψ`** of the piece `λ` of a family with `Ψ̂_λ` continuous:
`q ↦ q_λ`, `(g, q) ↦ Ψ̂_λ(g, q) = (q, Ψ_λ(g, q), g ∗ q)` (Lemma 17.1.9). -/
def pieceFunctor (i : ι) (hc : Continuous (S.hat (Ψ i))) :
    EpFunctor (Ψ i).1.toUniformizer.ep (S.modelEP Ψ).X where
  obj q := ⟨i, q⟩
  mor p := ⟨(i, i), S.hat (Ψ i) p⟩
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp φ ψ h := by
    have h' : φ.2 = ψ.1 • ψ.2 := h
    have hc' : C.toGroupoidStr.src (S.hat (Ψ i) φ).mor =
        C.toGroupoidStr.tgt (S.hat (Ψ i) ψ).mor := by
      change C.toGroupoidStr.src ((Ψ i).1.toUniformizer.mor φ) =
        C.toGroupoidStr.tgt ((Ψ i).1.toUniformizer.mor ψ)
      rw [(Ψ i).1.toUniformizer.src_mor, (Ψ i).1.toUniformizer.tgt_mor, h']
    refine Eq.trans ?_ (modelGroupoid_comp_of (Ψ := Ψ) _ _ hc').symm
    refine congrArg (Sigma.mk (β := fun p : ι × ι => S.Tr (Ψ p.1) (Ψ p.2)) (i, i)) ?_
    refine GroupoidStr.TransitionSet.ext rfl ?_ ?_
    · exact (Ψ i).1.functor.mor_comp φ ψ h
    · change (φ.1 * ψ.1) • ψ.2 = φ.1 • φ.2
      rw [mul_smul, h']
  mor_unit q :=
    congrArg (Sigma.mk (β := fun p : ι × ι => S.Tr (Ψ p.1) (Ψ p.2)) (i, i))
      ((Ψ i).1.toUniformizer.hat_one q)
  isScSmoothMap_obj := MPolyfold.isScSmoothMap_sigmaMk (fun i => (Ψ i).1.P) i
  isScSmoothMap_mor :=
    (MPolyfold.isScSmoothMap_sigmaMk (fun p : ι × ι => S.transPolyfold (Ψ p.1) (Ψ p.2))
      (i, i)).comp (S.isScSmoothMap_hat_of_continuous (Ψ i) hc)

@[simp] theorem pieceFunctor_obj (i : ι) (hc : Continuous (S.hat (Ψ i))) (q : (Ψ i).1.O) :
    (pieceFunctor Ψ i hc).obj q = ⟨i, q⟩ := rfl

/-- **`G_λ ⋉ O_λ → X_Ψ` is an equivalence** (Definition 10.1.1) when the footprint of `Ψ_λ` is
`|C|`: full and faithful (Lemma 17.1.9: `Ψ̂_λ` is a bijection onto `M(Ψ_λ, Ψ_λ)`), essentially
surjective (every `Ψ_μ(q)` is isomorphic to some `Ψ_λ(q')`), and `q ↦ q_λ` is a local
sc-diffeomorphism. -/
theorem isEquivalence_pieceFunctor (i : ι) (hc : Continuous (S.hat (Ψ i)))
    (hcov : (Ψ i).1.footprint = univ) : (pieceFunctor Ψ i hc).IsEquivalence := by
  refine EpFunctor.lemma_10_1_2 _ ?_
    (MPolyfold.isLocalScDiffeo_sigmaMk (fun i => (Ψ i).1.P) i)
  refine { full := ?_, faithful := ?_, essSurj := ?_ }
  · refine (GroupoidFunctor.faithful_iff _).2 fun φ φ' _ _ he => ?_
    have he' := sigma_mk_injective he
    exact (S.lemma_17_1_9_bijective (Ψ i)).1 he'
  · refine (GroupoidFunctor.full_iff _).2 fun x x' ψ hs ht => ?_
    obtain ⟨⟨j, k⟩, a⟩ := ψ
    have hs' : (⟨j, a.src⟩ : S.ModelObj Ψ) = ⟨i, x⟩ := hs
    have ht' : (⟨k, a.tgt⟩ : S.ModelObj Ψ) = ⟨i, x'⟩ := ht
    obtain ⟨hj, hsa⟩ := Sigma.mk.inj_iff.1 hs'
    obtain ⟨hk, hta⟩ := Sigma.mk.inj_iff.1 ht'
    subst hj hk
    have hsa : a.src = x := eq_of_heq hsa
    have hta : a.tgt = x' := eq_of_heq hta
    obtain ⟨g, hg, hgm⟩ := (Ψ k).1.toUniformizer.exists_smul_eq_mor
      (a.src_mor.trans (by rw [hsa])) (a.tgt_mor.trans (by rw [hta]))
    refine ⟨(g, x), rfl, hg, ?_⟩
    refine congrArg (Sigma.mk (β := fun p : ι × ι => S.Tr (Ψ p.1) (Ψ p.2)) (k, k)) ?_
    exact GroupoidStr.TransitionSet.ext hsa.symm hgm (hg.trans hta.symm)
  · refine (GroupoidFunctor.essSurj_iff _).2 fun y => ?_
    obtain ⟨j, q⟩ := y
    obtain ⟨x, hx⟩ := (Ψ i).1.mem_footprint_iff.1
      (hcov.symm ▸ mem_univ (C.toGroupoidStr.π ((Ψ j).1.obj q)))
    obtain ⟨φ, hs, ht⟩ := (GroupoidStr.π_eq_π_iff _).1 hx
    exact ⟨x, ⟨(i, j), ⟨x, φ, q, hs, ht⟩⟩, rfl, rfl⟩

/-- `G_λ ⋉ O_λ` as an object of `EP`. -/
abbrev unifEP (Φ : S.Unif) : EP.{u} := ⟨Φ.1.O, Φ.1.G × Φ.1.O, Φ.1.toUniformizer.ep⟩

/-- **A property invariant under generalized isomorphisms holds for `C` iff it holds for
`G ⋉ O`** when one uniformizer `Ψ_λ` of a covering family has footprint `|C|` and `Ψ̂_λ`
continuous. -/
theorem hasModelProperty_iff_piece {P : EP.{u} → Prop} (hP : IsGenIsoInvariant P)
    (c : S.CoveringFamily) (i : c.ι) (hc : Continuous (S.hat (c.Ψ i)))
    (hcov : (c.Ψ i).1.footprint = univ) : S.HasModelProperty P ↔ P (unifEP (c.Ψ i)) := by
  have hF := isEquivalence_pieceFunctor c.Ψ i hc hcov
  have : IsIso (localizationFunctor.map (X := unifEP (c.Ψ i)) (Y := S.modelEP c.Ψ)
      (pieceFunctor c.Ψ i hc)) := isInvertedBy_localizationFunctor _ hF
  rw [hasModelProperty_iff hP c]
  exact (hP ((isGeneralizedIso_iff_isIso _).2 this)).symm

end Piece

/-! ### Translation GCTs with the tautological polyfold structure -/

section Taut

variable {K U : Type u} [Group K] [MulAction K U] [Finite K] [TopologicalSpace K]
  [DiscreteTopology K] [TopologicalSpace U] [T2Space U] [ParacompactSpace U] {P : MPolyfold U}
  (hP : ∀ k : K, P.IsScSmoothMap P fun y => k • y)

/-- **The tautological polyfold structure on the translation GCT `K ⋉ U`**: `F(x) = {Ψ₀}` with
`Ψ₀ = id : K ⋉ U → K ⋉ U`, `M(Ψ₀, Ψ₀) ≅ K × U` (`twistConstruction` with the identity twist). -/
abbrev tautConstruction : (GCT.translation K U hP).PolyfoldConstruction :=
  twistConstruction hP (TranslationTwist.refl K U)

/-- **The covering family `{Ψ₀}`** of the tautological polyfold structure (`x₀` names the base
point of `Ψ₀ ∈ F(x₀)`). -/
def tautSingleFamily (x₀ : U) : (tautConstruction hP).CoveringFamily where
  ι := PUnit
  Ψ := fun _ => tautUnif hP _ x₀
  cover := eq_univ_of_forall fun z => mem_iUnion.2 ⟨PUnit.unit, by
    change z ∈ (LocalUniformizer.tautological P hP).footprint
    rw [LocalUniformizer.tautological_footprint]
    exact mem_univ z⟩

/-- `K ⋉ U` as an object of `EP`. -/
abbrev actionEP : EP.{u} := ⟨U, K × U, EpGroupoid.Examples.actionEpGroupoid hP⟩

/-- **The equivalence `K ⋉ U → X_Ψ`** for `Ψ = {Ψ₀}`. -/
def tautModelFunctor (x₀ : U) :
    EpFunctor (EpGroupoid.Examples.actionEpGroupoid hP)
      ((tautConstruction hP).modelEP (tautSingleFamily hP x₀).Ψ).X :=
  pieceFunctor (tautSingleFamily hP x₀).Ψ PUnit.unit (twist_continuous_hat hP _ x₀ continuous_id)

theorem isEquivalence_tautModelFunctor (x₀ : U) : (tautModelFunctor hP x₀).IsEquivalence :=
  isEquivalence_pieceFunctor _ _ _ (LocalUniformizer.tautological_footprint hP)

/-- **A property invariant under generalized isomorphisms holds for `K ⋉ U` with the tautological
structure iff it holds for the ep-groupoid `K ⋉ U`.** -/
theorem tautConstruction_hasModelProperty_iff {Pr : EP.{u} → Prop} (hPr : IsGenIsoInvariant Pr)
    (x₀ : U) : (tautConstruction hP).HasModelProperty Pr ↔ Pr (actionEP hP) :=
  hasModelProperty_iff_piece hPr (tautSingleFamily hP x₀) PUnit.unit
    (twist_continuous_hat hP _ x₀ continuous_id) (LocalUniformizer.tautological_footprint hP)

end Taut

/-! ### `ℤ/3 ⋉ ℝ` (trivial action) and Proposition 17.1.25 -/

section Z3

open EpGroupoid.Examples LocalizationLRCounterexample

/-- **The GCT `ℤ/3 ⋉ ℝ` (trivial action) with its tautological polyfold structure.** -/
abbrev z3TautConstruction :
    (GCT.translation (Multiplicative (ZMod 3)) (Fin 1 → ℝ)
      isScSmoothMap_z3_smul).PolyfoldConstruction :=
  tautConstruction isScSmoothMap_z3_smul

/-- The covering family `{Ψ₀}` of `ℤ/3 ⋉ ℝ`. -/
abbrev z3Family : z3TautConstruction.CoveringFamily := tautSingleFamily isScSmoothMap_z3_smul 0

/-- **`ℤ/3 ⋉ ℝ` satisfies (ZHOU), (LUC), (SLUC), (LR) and (SLR)** (Definition 17.1.22): its model
is equivalent to `ℤ/3 × ℝ ⇉ ℝ`, which satisfies (ZHOU) (every element acts trivially);
Proposition 17.1.23 gives the others.  The isotropy group of every object is `ℤ/3`. -/
theorem z3Taut_properties :
    z3TautConstruction.IsZhou ∧ z3TautConstruction.IsLUC ∧ z3TautConstruction.IsSLUC ∧
      z3TautConstruction.IsLR ∧ z3TautConstruction.IsSLR := by
  have hZ : z3TautConstruction.IsZhou :=
    (tautConstruction_hasModelProperty_iff isScSmoothMap_z3_smul isGenIsoInvariant_isZhou 0).2
      isZhou_trivialZ3
  exact ⟨hZ, z3TautConstruction.proposition_17_1_23 hZ⟩

/-- The model of `ℤ/3 ⋉ ℝ` is not effective. -/
theorem not_isEffective_z3Taut : ¬ z3TautConstruction.IsEffective := fun h =>
  not_isEffective_trivialZ3
    ((tautConstruction_hasModelProperty_iff isScSmoothMap_z3_smul
      isGenIsoInvariant_isEffective 0).1 h)

/-- **Witness for Theorem 17.1.26**: `ℤ/3 ⋉ ℝ` carries the class `c_C`, represented by its model
`X_Ψ` (isotropy `ℤ/3` at every object). -/
theorem z3Taut_polyfoldClass :
    ∃ hZ : (z3TautConstruction.modelEP z3Family.Ψ).X.IsZhou,
      (⟦z3TautConstruction.modelPolyfoldStructure z3Family hZ⟧ :
          PolyfoldClass (GCT.translation (Multiplicative (ZMod 3)) (Fin 1 → ℝ)
            isScSmoothMap_z3_smul).toGroupoidStr.OrbitSpace) =
        z3TautConstruction.polyfoldClass z3Taut_properties.1 :=
  ⟨_, z3TautConstruction.polyfoldClass_eq z3Taut_properties.1 z3Family⟩

/-- `e : ℤ/3 × ℝ ⇉ ℝ → X_Ψ` in `EP(E⁻¹)` (an isomorphism). -/
abbrev z3ModelIso :
    EPLoc.of z3EP ⟶ localizationFunctor.obj (z3TautConstruction.modelEP z3Family.Ψ) :=
  localizationFunctor.map (X := z3EP) (Y := z3TautConstruction.modelEP z3Family.Ψ)
    (tautModelFunctor isScSmoothMap_z3_smul 0)

instance : IsIso z3ModelIso :=
  isInvertedBy_localizationFunctor _ (isEquivalence_tautModelFunctor isScSmoothMap_z3_smul 0)

/-- **The generalized isomorphism `h = e⁻¹ ∘ [Inv] ∘ e : X_Ψ → X_Ψ`** (`[Inv]` of
`not_theorem_10_3_19`). -/
abbrev z3TwistedIso :
    localizationFunctor.obj (z3TautConstruction.modelEP z3Family.Ψ) ⟶
      localizationFunctor.obj (z3TautConstruction.modelEP z3Family.Ψ) :=
  inv z3ModelIso ≫ genInv ≫ z3ModelIso

/-- **The counterexample to Proposition 17.1.25**: `ℤ/3 ⋉ ℝ` has (LUC) and (LR) (even (ZHOU)); for
its covering family `Ψ = {Ψ₀}`, `h = e⁻¹ ∘ [Inv] ∘ e` is a generalized isomorphism
`X_Ψ → X_Ψ` with `|Γ_Ψ| ∘ |h| = |Γ_Ψ|`, and `h ≠ f_{Ψ,Ψ} = 1`. -/
theorem z3Taut_counterexample :
    z3TautConstruction.IsLUC ∧ z3TautConstruction.IsLR ∧ z3TautConstruction.IsZhou ∧
      IsGeneralizedIso z3TwistedIso ∧
      (z3TautConstruction.modelFunctor z3Family.Ψ).orbitMap ∘ EPLoc.orbitMap z3TwistedIso =
        (z3TautConstruction.modelFunctor z3Family.Ψ).orbitMap ∧
      z3TwistedIso ≠ z3TautConstruction.comparison z3Family z3Family := by
  obtain ⟨hZ, hLUC, -, hLR, -⟩ := z3Taut_properties
  refine ⟨hLUC, hLR, hZ, ?_, ?_, ?_⟩
  · rw [isGeneralizedIso_iff_isIso]
    have : IsIso genInv := (isGeneralizedIso_iff_isIso _).1 isGeneralizedIso_genInv
    infer_instance
  · have ho : EPLoc.orbitMap z3TwistedIso = _root_.id := by
      rw [proposition_10_3_11, proposition_10_3_11, orbitMap_genInv]
      change EPLoc.orbitMap z3ModelIso ∘ EPLoc.orbitMap (𝟙 (EPLoc.of z3EP)) ∘
        EPLoc.orbitMap (inv z3ModelIso) = _
      rw [orbitMap_id, Function.id_comp, ← proposition_10_3_11, IsIso.inv_hom_id,
        orbitMap_id]
    funext q
    exact congrArg (z3TautConstruction.modelFunctor z3Family.Ψ).orbitMap (congrFun ho q)
  · rw [comparison_self]
    intro h
    apply genInv_ne_genId
    have e : genInv = z3ModelIso ≫ z3TwistedIso ≫ inv z3ModelIso := by
      simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id, IsIso.hom_inv_id_assoc]
    rw [e, h, Category.id_comp, IsIso.hom_inv_id]
    rfl

/-- **2021 Proposition 17.1.25, p. 758, does not hold as we read it** (with (LUC), as printed):
`z3Taut_counterexample`. -/
theorem not_proposition_17_1_25 : ¬ Proposition_17_1_25.{0} := fun h => by
  obtain ⟨hLUC, -, -, hgen, ho, hne⟩ := z3Taut_counterexample
  exact hne (h _ z3TautConstruction hLUC z3Family z3Family _ hgen ho)

/-- **Proposition 17.1.25 with (LR) does not hold as we read it either**:
`z3Taut_counterexample`. -/
theorem not_proposition_17_1_25_LR : ¬ Proposition_17_1_25_LR.{0} := fun h => by
  obtain ⟨-, hLR, -, hgen, ho, hne⟩ := z3Taut_counterexample
  exact hne (h _ z3TautConstruction hLR z3Family z3Family _ hgen ho)

end Z3

/-! ### Witnesses for the forms we prove -/

/-! ### Witnesses for the levels, `C¹` and the boundary -/

section LevelOne

/-- **`ℤ/3 ⋉ ℝ` has a covering family** (the hypothesis of the topology of `|C_1|`). -/
theorem z3Taut_hasCoveringUniformizers : z3TautConstruction.HasCoveringUniformizers :=
  z3TautConstruction.exists_coveringFamily_iff.1 ⟨z3Family⟩

/-- **Witness for Theorem 17.1.28 and Corollary 17.1.29**: for `ℤ/3 ⋉ ℝ` (isotropy `ℤ/3`), `C¹`
is a GCT carrying the class of polyfold structures `[(X_Ψ¹, |Γ_Ψ¹|)]`, `X_Ψ¹` satisfies (ZHOU),
(SLUC), (SLR), and `|C¹|` is the raised polyfold `(|C|, c_C)¹`. -/
theorem z3Taut_levelOne :
    (⟦z3TautConstruction.levelOnePolyfoldStructure z3Taut_hasCoveringUniformizers z3Family
        (z3Taut_properties.1.model z3Family)⟧ :
        PolyfoldClass (z3TautConstruction.levelOneGCT
          z3Taut_hasCoveringUniformizers).toGroupoidStr.OrbitSpace) =
      z3TautConstruction.levelOnePolyfoldClass z3Taut_hasCoveringUniformizers
        z3Taut_properties.1 ∧
      (z3TautConstruction.modelEP z3Family.Ψ).liftOne.X.IsZhou ∧
      (z3TautConstruction.modelEP z3Family.Ψ).liftOne.IsSLUC ∧
      (z3TautConstruction.modelEP z3Family.Ψ).liftOne.IsSLR ∧
      PolyfoldClass.raiseIncl (z3TautConstruction.polyfoldClass z3Taut_properties.1) ∘
          z3TautConstruction.levelOneHomeomorphRaised z3Taut_hasCoveringUniformizers
            z3Taut_properties.1 =
        z3TautConstruction.orbitInclLevelOne := by
  obtain ⟨hZ, -, hSLUC, -, hSLR⟩ := z3Taut_properties
  obtain ⟨h1, h2, h3⟩ := z3TautConstruction.corollary_17_1_29_model z3Family
  exact ⟨z3TautConstruction.levelOnePolyfoldClass_eq _ hZ z3Family, h1 hZ, h2 hSLUC, h3 hSLR,
    z3TautConstruction.raiseIncl_levelOneHomeomorphRaised _ hZ⟩

end LevelOne

section Corner

open MPolyfold

/-- The half-line `[0, ∞)` (the quadrant `[0, ∞)¹ ⊕ ℝ⁰`). -/
abbrev Corner : Type := quadrant 1 (ScBanach.const (Fin 0 → ℝ)) 0

/-- The trivial group `{1}` acting on `[0, ∞)`. -/
scoped instance instMulActionZ1Corner : MulAction (Multiplicative (ZMod 1)) Corner where
  smul _ y := y
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem isScSmoothMap_z1_smul_corner (k : Multiplicative (ZMod 1)) :
    (quadrantPolyfold 1 (ScBanach.const (Fin 0 → ℝ))).IsScSmoothMap
      (quadrantPolyfold 1 (ScBanach.const (Fin 0 → ℝ))) fun y : Corner => k • y :=
  MPolyfold.isScSmoothMap_id

/-- **The translation GCT `{1} ⋉ [0, ∞)`** with its tautological polyfold structure. -/
abbrev cornerTautConstruction :
    (GCT.translation (Multiplicative (ZMod 1)) Corner
      isScSmoothMap_z1_smul_corner).PolyfoldConstruction :=
  tautConstruction isScSmoothMap_z1_smul_corner

/-- The corner `0 ∈ [0, ∞)`. -/
abbrev cornerZero : Corner := ⟨0, zero_mem_quadrant 1 _⟩

/-- **Witness for Definition 17.1.30**: the object `0` of `{1} ⋉ [0, ∞)` has `d(0) = 1`. -/
theorem cornerTaut_degIndex_zero : cornerTautConstruction.degIndex cornerZero = 1 := by
  exact (degIndex_eq (S := cornerTautConstruction)
    (tautUnif isScSmoothMap_z1_smul_corner (TranslationTwist.refl _ _) cornerZero)
    (q := cornerZero) (α := cornerZero) (GroupoidStr.isomorphic_refl _ _)).trans
    (quadrantPolyfold_degIndex_zero 1 _)

/-- **`∂C ≠ ∅`** for `{1} ⋉ [0, ∞)`. -/
theorem cornerTaut_boundarySet_nonempty : cornerTautConstruction.boundarySet.Nonempty :=
  ⟨cornerZero, cornerTaut_degIndex_zero.ge⟩

end Corner

section Reflection

open EpGroupoid.Examples

/-- **The reflection GCT `ℤ/2 ⋉ ℝ` is effective** (non-trivial isotropy `ℤ/2` at `0`): the
effectiveness hypothesis of `proposition_17_1_25_of_isEffective'` is satisfiable
non-degenerately. -/
theorem reflection_isEffective : reflectionConstruction.IsEffective :=
  (tautConstruction_hasModelProperty_iff isScSmoothMap_units_smul isGenIsoInvariant_isEffective
    0).2 isEffective_reflection

/-- The reflection GCT has (LUC). -/
theorem reflection_isLUC : reflectionConstruction.IsLUC :=
  (tautConstruction_hasModelProperty_iff isScSmoothMap_units_smul isGenIsoInvariant_isLUC 0).2
    isLUC_reflection

end Reflection

section Unit

/-- The trivial group `{1}` (as `Multiplicative (ZMod 1)`) acting on `ℝ`. -/
scoped instance instMulActionZ1 : MulAction (Multiplicative (ZMod 1)) (Fin 1 → ℝ) where
  smul _ y := y
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem isScSmoothMap_z1_smul (k : Multiplicative (ZMod 1)) :
    (rnPolyfold 1).IsScSmoothMap (rnPolyfold 1) fun y : Fin 1 → ℝ => k • y :=
  MPolyfold.isScSmoothMap_id

/-- **The translation GCT `{1} ⋉ ℝ`** with its tautological polyfold structure. -/
abbrev unitTautConstruction :
    (GCT.translation (Multiplicative (ZMod 1)) (Fin 1 → ℝ)
      isScSmoothMap_z1_smul).PolyfoldConstruction :=
  tautConstruction isScSmoothMap_z1_smul

theorem subsingleton_isotropy_z1 (x : Fin 1 → ℝ) :
    Subsingleton ((EpGroupoid.Examples.actionEpGroupoid isScSmoothMap_z1_smul).Isotropy x) :=
  ⟨fun g g' => GroupoidStr.Isotropy.ext (Prod.ext (Subsingleton.elim _ _)
    (g.src_val.trans g'.src_val.symm))⟩

/-- **(LR) and effectiveness together**: `{1} ⋉ ℝ` satisfies (ZHOU), hence (LR), and is
effective. -/
theorem unitTaut_isLR_isEffective :
    unitTautConstruction.IsZhou ∧ unitTautConstruction.IsLR ∧ unitTautConstruction.IsEffective := by
  have hZ : unitTautConstruction.IsZhou :=
    (tautConstruction_hasModelProperty_iff isScSmoothMap_z1_smul isGenIsoInvariant_isZhou 0).2
      (EpGroupoid.isZhou_of_subsingleton _ subsingleton_isotropy_z1)
  refine ⟨hZ, (unitTautConstruction.proposition_17_1_23 hZ).2.2.1,
    (tautConstruction_hasModelProperty_iff isScSmoothMap_z1_smul isGenIsoInvariant_isEffective
      0).2 fun x g hg => absurd (Subsingleton.elim (h := subsingleton_isotropy_z1 x) g 1) hg⟩

/-- **Proposition 17.1.25 in the form we prove applies to `{1} ⋉ ℝ`**: every generalized isomorphism
`h : X_Ψ → X_Ψ'` with `|Γ_Ψ'| ∘ |h| = |Γ_Ψ|` is `f_{Ψ,Ψ'}`. -/
theorem unitTaut_proposition_17_1_25 (c c' : unitTautConstruction.CoveringFamily)
    {h : localizationFunctor.obj (unitTautConstruction.modelEP c.Ψ) ⟶
      localizationFunctor.obj (unitTautConstruction.modelEP c'.Ψ)}
    (hgen : IsGeneralizedIso h)
    (hh : (unitTautConstruction.modelFunctor c'.Ψ).orbitMap ∘ EPLoc.orbitMap h =
      (unitTautConstruction.modelFunctor c.Ψ).orbitMap) :
    h = unitTautConstruction.comparison c c' :=
  unitTautConstruction.proposition_17_1_25_of_isEffective' unitTaut_isLR_isEffective.2.1
    unitTaut_isLR_isEffective.2.2 c c' hgen hh

end Unit

end GCT.PolyfoldConstruction

end Polyfold
