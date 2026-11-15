import Polyfold.Chapter16.OrientationOrbitMapIndependence
import Polyfold.Chapter12.OrientationNonEffectiveExample
import Polyfold.Chapter12.OrientationGeneralizedIsoOriented
import Polyfold.Chapter16.PolyfoldBundleUniqueness

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
p. 595, **Theorem 12.5.7 (2)** (2017: Theorem 12.12 (2)), with **Remark 10.5.5** (p. 508) and
**Definition 12.5.4** (p. 594): the push-forward orientation in an example where the
generalized strong bundle isomorphism is not determined by its map of orbit spaces.

## The example

`W = ℝ × ℝᵏ → ℝ` over `ℤ/3 × ℝ ⇉ ℝ` with the trivial actions (`z3SEP k`): the base is not
effective, `[Inv] ≠ [1_W]` and `|[Inv]| = |[1_W]|` (Remark 10.5.5).  `f` is the graph section of
a `C^∞` map `φ : ℝ → ℝᵏ`.

* `equiv_eq_self_of_two_of_cube`: a permutation `e` of a set with two elements with `e³ = 1` is
  the identity.
* `orMor_z3`: every morphism `(g, x)` acts as the identity on `Or^f_x` (`(g, x)³ = 1_x`, and
  `Or^f_x` has two elements).
* `z3Orientation`, `definition_12_5_4_z3Orientation`: an orientation of `f` (Definition 12.5.4):
  a continuous section of `σ : O_f → ℝ` (every sc-Fredholm section over `ℝ` is orientable), which
  is invariant under the morphisms by `orMor_z3`.
* **`theorem_12_5_7_two_orbitMap_unique_z3`**: every hypothesis of
  `GenSBMap.theorem_12_5_7_two_orbitMap_unique_of_isLRLocal` holds, with this orientation, a base
  which is not effective and two different generalized strong bundle isomorphisms `[1_W]`,
  `[Inv]` with the same map of orbit spaces, both pushing `f` to `f`; hence its conclusion: one
  orientation `o'` corresponds to `o` over every diagram of both.
* `z3GraphRep`, `z3FredholmSection`, **`z3OrientationRep`**: the sc-Fredholm section
  `|x| ↦ |(x, φ(x))|` of the strong polyfold bundle `z3Bundle k` (Definition 16.6.1) with an
  orientation (Definition 16.6.5); **`exists_unique_transport_z3`**: the hypotheses of
  `OrientationRep.exists_unique_transport_of_isLRLocal` hold for it although the base is not
  effective, hence its conclusion for every representative `b`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

open scoped ContDiff

noncomputable section

namespace Polyfold

/-- **A permutation `e` of a set with two elements with `e³ = 1` is the identity.** -/
theorem equiv_eq_self_of_two_of_cube {α : Type*} (h2 : ∃ a b : α, a ≠ b ∧ ∀ c, c = a ∨ c = b)
    (e : α ≃ α) (h3 : ∀ o, e (e (e o)) = o) (o : α) : e o = o := by
  by_contra hne
  obtain ⟨a, b, -, hall⟩ := h2
  have hne' : e (e o) ≠ e o := fun h => hne (e.injective h)
  have key : e (e o) = o := by
    rcases hall o with ho | ho <;> rcases hall (e o) with h1 | h1 <;>
      rcases hall (e (e o)) with h2 | h2
    · exact absurd (h1.trans ho.symm) hne
    · exact absurd (h1.trans ho.symm) hne
    · exact h2.trans ho.symm
    · exact absurd (h2.trans h1.symm) hne'
    · exact absurd (h2.trans h1.symm) hne'
    · exact h2.trans ho.symm
    · exact absurd (h1.trans ho.symm) hne
    · exact absurd (h1.trans ho.symm) hne
  exact hne ((congrArg e key).symm.trans (h3 o))

namespace StrongBundleLocalizationExamples

open SBLocalization StrongBundleEquivalenceExamples TrivialBundle EpStrongBundle
open LocalizationLRBundleBaseExamples EpGroupoid.Examples

variable {k : ℕ} {φ : (Fin 1 → ℝ) → (Fin k → ℝ)}

theorem isTame_z3SEP (k : ℕ) : (z3SEP k).X.PObj.IsTame := rnPolyfold_isTame

theorem admitsBumpFunctions_z3SEP (k : ℕ) : (z3SEP k).X.PObj.AdmitsBumpFunctions :=
  admitsBumpFunctions_rn 1

theorem hasScPlusSectionsThrough_z3SEP (k : ℕ) : (z3SEP k).B.HasScPlusSectionsThrough :=
  hasScPlusSectionsThrough_epSEP 1 k

theorem isScFredholmSectionTame_graphSection_z3 (hφ : ContDiff ℝ ∞ φ) :
    (z3SEP k).B.IsScFredholmSectionTame (graphSection φ) :=
  isScFredholmSectionTame_graphSection hφ

/-- **Every morphism `(g, x)` of `ℤ/3 × ℝ ⇉ ℝ` acts as the identity on `Or^f_x`**: its third
power is `1_x`, and `Or^f_x` has two elements. -/
theorem orMor_z3 (hφ : ContDiff ℝ ∞ φ) (σ : (z3SEP k).Mor)
    (hs : (z3SEP k).X.src σ ∈ (z3SEP k).X.PObj.smoothSet)
    (o : Orx (B := (z3SEP k).B) (graphSection φ)
      (isScFredholmSectionFunctor_graphSection_z3 hφ).2 ((z3SEP k).X.src σ) hs) :
    (z3SEP k).E.orMor (isScFredholmSectionFunctor_graphSection_z3 hφ)
      (hasScPlusSectionsThrough_z3SEP k) σ rfl rfl hs hs o = o := by
  have hF := isScFredholmSectionFunctor_graphSection_z3 (k := k) hφ
  have hsec := hasScPlusSectionsThrough_z3SEP k
  refine equiv_eq_self_of_two_of_cube (exists_two_orx hF.2 hs hsec)
    ((z3SEP k).E.orMor hF hsec σ rfl rfl hs hs) (fun o => ?_) o
  have c₁ := (z3SEP k).E.orMor_comp (hF := hF) (hsec := hsec) (φ := σ) (ψ := σ) rfl rfl rfl
    rfl hs hs hs
  have c₂ := (z3SEP k).E.orMor_comp (hF := hF) (hsec := hsec) (φ := (z3SEP k).X.comp σ σ)
    (ψ := σ) (x := (z3SEP k).X.src σ) (y := (z3SEP k).X.src σ) (z := (z3SEP k).X.src σ) rfl
    rfl rfl rfl hs hs hs
  have hg : ∀ g : Multiplicative (ZMod 3), g * (g * g) = 1 := by decide
  have hu : (z3SEP k).X.comp σ ((z3SEP k).X.comp σ σ) = (z3SEP k).X.unit ((z3SEP k).X.src σ) :=
    Prod.ext (hg σ.1) rfl
  have c₃ := (z3SEP k).E.orMor_unit hF hsec hu rfl rfl hs
  have e₁ := DFunLike.congr_fun c₁ o
  have e₂ := DFunLike.congr_fun c₂ o
  have e₃ := DFunLike.congr_fun c₃ o
  rw [Equiv.trans_apply] at e₁ e₂
  exact (congrArg _ e₁).trans (e₂.trans e₃)

/-- **`σ : O_f → ℝ` has a continuous global section** for the graph section `f` over
`ℤ/3 × ℝ ⇉ ℝ` (every sc-Fredholm section over `ℝ` is orientable, Definition 6.6.14). -/
theorem exists_continuous_orSec_graphSection_z3 (hφ : ContDiff ℝ ∞ φ) :
    haveI := paracompactSpace_rn_prod (z3SEP k).X.PObj
    haveI := paracompactSpace_rn_pullback (z3SEP k).B
    haveI := paracompactSpace_rn_rn_prod (z3SEP k).X.PObj
    haveI := paracompactSpace_rn_rn_pullback (z3SEP k).B
    ∃ o : ∀ a (hs : a ∈ (z3SEP k).X.PObj.smoothSet),
        Orx (B := (z3SEP k).B) (graphSection φ)
          (isScFredholmSectionFunctor_graphSection_z3 hφ).2 a hs,
      @Continuous _ _ _ (orTopology (orLocalTransport (isTame_z3SEP k)
        (admitsBumpFunctions_z3SEP k) (isScFredholmSectionTame_graphSection_z3 hφ)
        (hasScPlusSectionsThrough_z3SEP k))) (orSec o) := by
  have := paracompactSpace_rn_prod (z3SEP k).X.PObj
  have := paracompactSpace_rn_pullback (z3SEP k).B
  have := paracompactSpace_rn_rn_prod (z3SEP k).X.PObj
  have := paracompactSpace_rn_rn_pullback (z3SEP k).B
  obtain ⟨o, ho⟩ := (exists_isSectionOrientation_iff (isTame_z3SEP k)
    (admitsBumpFunctions_z3SEP k) (isScFredholmSectionTame_graphSection_z3 hφ)
    (hasScPlusSectionsThrough_z3SEP k)).2 fun _ _ a b =>
      congrArg (fun c => orFunctorMap (isTame_z3SEP k) (admitsBumpFunctions_z3SEP k)
        (isScFredholmSectionTame_graphSection_z3 hφ) (hasScPlusSectionsThrough_z3SEP k) c)
        (PathCat.hom_eq_rn (n := 1) a b)
  exact ⟨o, (isSectionOrientation_iff_continuous (isTame_z3SEP k)
    (admitsBumpFunctions_z3SEP k) (isScFredholmSectionTame_graphSection_z3 hφ)
    (hasScPlusSectionsThrough_z3SEP k) o).1 ho⟩

/-- **An orientation of the graph section over `ℤ/3 × ℝ ⇉ ℝ`**: a continuous section of
`σ : O_f → ℝ` (one of the two is chosen). -/
def z3Orientation (hφ : ContDiff ℝ ∞ φ) : ∀ a (hs : a ∈ (z3SEP k).X.PObj.smoothSet),
    Orx (B := (z3SEP k).B) (graphSection φ)
      (isScFredholmSectionFunctor_graphSection_z3 hφ).2 a hs :=
  (exists_continuous_orSec_graphSection_z3 hφ).choose

/-- **`z3Orientation` is an orientation in the sense of Definition 12.5.4**: continuous, and
invariant under the morphisms `(g, x)`, which act as the identity on `Or^f_x`. -/
theorem definition_12_5_4_z3Orientation (hφ : ContDiff ℝ ∞ φ) :
    haveI := paracompactSpace_rn_prod (z3SEP k).X.PObj
    haveI := paracompactSpace_rn_pullback (z3SEP k).B
    haveI := paracompactSpace_rn_rn_prod (z3SEP k).X.PObj
    haveI := paracompactSpace_rn_rn_pullback (z3SEP k).B
    (z3SEP k).E.definition_12_5_4 (isScFredholmSectionFunctor_graphSection_z3 hφ)
      (hasScPlusSectionsThrough_z3SEP k)
      (orTopology (orLocalTransport (isTame_z3SEP k) (admitsBumpFunctions_z3SEP k)
        (isScFredholmSectionTame_graphSection_z3 hφ) (hasScPlusSectionsThrough_z3SEP k)))
      (z3Orientation hφ) :=
  ⟨(exists_continuous_orSec_graphSection_z3 hφ).choose_spec,
    fun σ x x' hx hx' hs hs' => by
      obtain rfl : (z3SEP k).X.src σ = x := hx
      obtain rfl : (z3SEP k).X.src σ = x' := hx'
      exact orMor_z3 hφ σ hs (z3Orientation hφ _ hs)⟩

/-- Part I's topology on `O_f` is a topology with the properties of Theorem 12.5.3. -/
theorem isOrientationTopology_graphSection_z3 (hφ : ContDiff ℝ ∞ φ) :
    haveI := paracompactSpace_rn_prod (z3SEP k).X.PObj
    haveI := paracompactSpace_rn_pullback (z3SEP k).B
    haveI := paracompactSpace_rn_rn_prod (z3SEP k).X.PObj
    haveI := paracompactSpace_rn_rn_pullback (z3SEP k).B
    IsOrientationTopology (B := (z3SEP k).B) (graphSection φ)
      (isScFredholmSectionFunctor_graphSection_z3 hφ).2
      (orTopology (orLocalTransport (isTame_z3SEP k) (admitsBumpFunctions_z3SEP k)
        (isScFredholmSectionTame_graphSection_z3 hφ) (hasScPlusSectionsThrough_z3SEP k))) := by
  have := paracompactSpace_rn_prod (z3SEP k).X.PObj
  have := paracompactSpace_rn_pullback (z3SEP k).B
  have := paracompactSpace_rn_rn_prod (z3SEP k).X.PObj
  have := paracompactSpace_rn_rn_pullback (z3SEP k).B
  obtain ⟨t₀, ht₀⟩ := (theorem_6_6_17 (isTame_z3SEP k) (admitsBumpFunctions_z3SEP k)
    (isScFredholmSectionTame_graphSection_z3 hφ)).exists
  exact eq_orTopology_of (isTame_z3SEP k) (admitsBumpFunctions_z3SEP k)
    (isScFredholmSectionTame_graphSection_z3 hφ) (hasScPlusSectionsThrough_z3SEP k)
    ht₀.isLocalHomeomorph ht₀.propagation ▸ ht₀

/-- **Theorem 12.5.7 (2) where the generalized isomorphism is not unique**: on
`W = ℝ × ℝᵏ → ℝ` over `ℤ/3 × ℝ ⇉ ℝ` (not effective, non-zero fibres for `k ≥ 1`, with the local
regularity property), for the graph section `f` of a `C^∞` map with the orientation
`z3Orientation`: `[Inv] ≠ [1_W]`, `|[Inv]| = |[1_W]|`, both push `f` to `f`, and there is
exactly one orientation `o'` of `f` corresponding to the given one over every diagram of every
generalized strong bundle isomorphism `𝔄'` with `|𝔄'| = |[1_W]|` and `𝔄'_* f = f`, among them
`[Inv]`. -/
theorem theorem_12_5_7_two_orbitMap_unique_z3 (hφ : ContDiff ℝ ∞ φ) :
    ∃ (hInv : (SDiagram.ofHom (z3InvHom k)).cls.IsGeneralizedIso)
      (_ : graphSection φ = GenSBMap.pushforward hInv (graphSection φ)),
      (SDiagram.ofHom (z3InvHom k)).cls ≠ (SDiagram.id (z3SEP k)).cls ∧
      (SDiagram.ofHom (z3InvHom k)).cls.orbitMap = (SDiagram.id (z3SEP k)).cls.orbitMap ∧
      ¬ (z3SEP k).X.IsEffective ∧ (z3SEP k).E.IsLRLocal ∧
      ∃! o' : ∀ x (hs : x ∈ (z3SEP k).X.PObj.smoothSet), Orx (B := (z3SEP k).B) (graphSection φ)
          (isScFredholmSectionFunctor_graphSection_z3 hφ).2 x hs,
        (∀ t' : TopologicalSpace (OrSpace (B := (z3SEP k).B) (graphSection φ)
            (isScFredholmSectionFunctor_graphSection_z3 hφ).2),
          (haveI := paracompactSpace_rn_prod (z3SEP k).X.PObj
           haveI := paracompactSpace_rn_pullback (z3SEP k).B
           IsOrientationTopology (B := (z3SEP k).B) (graphSection φ)
            (isScFredholmSectionFunctor_graphSection_z3 hφ).2 t') →
            (z3SEP k).E.definition_12_5_4 (isScFredholmSectionFunctor_graphSection_z3 hφ)
              (hasScPlusSectionsThrough_z3SEP k) t' o') ∧
        ∀ (𝔄' : GenSBMap (z3SEP k) (z3SEP k)) (h𝔄' : 𝔄'.IsGeneralizedIso)
          (_ : 𝔄'.orbitMap = (SDiagram.id (z3SEP k)).cls.orbitMap)
          (hf'' : graphSection φ = GenSBMap.pushforward h𝔄' (graphSection φ))
          (D : SDiagram (z3SEP k) (z3SEP k)) (hD : D.cls = 𝔄') v
          (hv : v ∈ D.B.X.PObj.smoothSet),
          (sbe (GenSBMap.equivalences_Ψ_of_cls h𝔄' hD)).orEqv
              (D.isScFredholm_pullback (isScFredholmSectionFunctor_graphSection_z3 hφ))
              (isScFredholmSectionFunctor_graphSection_z3 hφ)
              (GenSBMap.pullback_eq_of_cls' h𝔄' hD
                (isScFredholmSectionFunctor_graphSection_z3 hφ).1 hf'')
              (D.hasScPlusSectionsThrough_B (hasScPlusSectionsThrough_z3SEP k))
              (hasScPlusSectionsThrough_z3SEP k) v hv
              (o' (D.Ψ.ϕ.obj v) ((sbe (GenSBMap.equivalences_Ψ_of_cls h𝔄' hD)).smooth_obj hv)) =
            D.hΦ.orEqv
              (D.isScFredholm_pullback (isScFredholmSectionFunctor_graphSection_z3 hφ))
              (isScFredholmSectionFunctor_graphSection_z3 hφ) rfl
              (D.hasScPlusSectionsThrough_B (hasScPlusSectionsThrough_z3SEP k))
              (hasScPlusSectionsThrough_z3SEP k) v hv
              (z3Orientation hφ (D.Φ.ϕ.obj v) (D.hΦ.smooth_obj hv)) := by
  have hF := isScFredholmSectionFunctor_graphSection_z3 (k := k) hφ
  obtain ⟨hInv, hId, horb, -, hne⟩ := remark_10_5_5 k
  have h₂ : graphSection φ = GenSBMap.pushforward hId (graphSection φ) :=
    ((GenSBMap.pushforward_eq hId rfl (SEP.equivalences.id_mem _) hF.1).trans
      (SDiagram.pushforward_id _ hF.1)).symm
  have h₁ : graphSection φ = GenSBMap.pushforward hInv (graphSection φ) :=
    h₂.trans (pushforward_inv_eq_pushforward_id k hInv hId hF.1).symm
  exact ⟨hInv, h₁, hne, horb, not_isEffective_trivialZ3, isLRLocal_z3EpBundle k,
    GenSBMap.theorem_12_5_7_two_orbitMap_unique_of_isLRLocal hId hF hF h₂
      (hasScPlusSectionsThrough_z3SEP k) (hasScPlusSectionsThrough_z3SEP k) (isTame_z3SEP k)
      (admitsBumpFunctions_z3SEP k) (isScFredholmSectionTame_graphSection_z3 hφ)
      (isLRLocal_z3EpBundle k) (isOrientationTopology_graphSection_z3 hφ)
      (definition_12_5_4_z3Orientation hφ)⟩

/-! ### The oriented sc-Fredholm section of the strong polyfold bundle -/

open StrongPolyfoldBundle StrongPolyfoldBundleStructure

/-- **The representative `(z3Structure, graph φ)`** of the section `|x| ↦ |(x, φ(x))|` of the
strong polyfold bundle over `|ℤ/3 × ℝ ⇉ ℝ|` (Definition 16.3.18). -/
def z3GraphRep (hφ : ContDiff ℝ ∞ φ) : SectionRep (z3Bundle k) where
  S := z3Structure k
  hS := rfl
  F := graphSection φ
  hF := (isScFredholmSectionFunctor_graphSection_z3 hφ).1
  f := Quotient.lift
    (fun x : (z3SEP k).Obj => (z3SEP k).E.toEpGroupoid.π (graphSection φ x))
    fun x y h => by
      have e : x = y := injective_π_trivialZ3 (Quotient.sound h)
      rw [e]
  continuous_f := Continuous.quotient_lift ((z3SEP k).E.toEpGroupoid.continuous_π.comp
    (continuous_id.prodMk hφ.continuous)) _
  isSection z := Quotient.inductionOn z fun _ => rfl
  comm _ := rfl

/-- **The sc-Fredholm section `|x| ↦ |(x, φ(x))|`** (Definition 16.6.1). -/
def z3FredholmSection (hφ : ContDiff ℝ ∞ φ) : FredholmSection (z3Bundle k) :=
  ⟨⟦z3GraphRep hφ⟧, z3GraphRep hφ, rfl, isScFredholmSectionFunctor_graphSection_z3 hφ⟩

/-- **An orientation of the sc-Fredholm section over `|ℤ/3 × ℝ ⇉ ℝ|`** (Definition 16.6.5). -/
def z3OrientationRep (hφ : ContDiff ℝ ∞ φ) : OrientationRep (z3FredholmSection (k := k) hφ) where
  a := z3GraphRep hφ
  ha := rfl
  hF := isScFredholmSectionFunctor_graphSection_z3 hφ
  hsec := hasScPlusSectionsThrough_z3SEP k
  t := haveI := paracompactSpace_rn_prod (z3SEP k).X.PObj
    haveI := paracompactSpace_rn_pullback (z3SEP k).B
    haveI := paracompactSpace_rn_rn_prod (z3SEP k).X.PObj
    haveI := paracompactSpace_rn_rn_pullback (z3SEP k).B
    orTopology (orLocalTransport (isTame_z3SEP k) (admitsBumpFunctions_z3SEP k)
      (isScFredholmSectionTame_graphSection_z3 hφ) (hasScPlusSectionsThrough_z3SEP k))
  isOrientationTopology := isOrientationTopology_graphSection_z3 hφ
  o := z3Orientation hφ
  isOrientation := definition_12_5_4_z3Orientation hφ

/-- **Definition 16.6.5 over a polyfold which is not effective**: for the oriented sc-Fredholm
section `|x| ↦ |(x, φ(x))|` over `|ℤ/3 × ℝ ⇉ ℝ|` the base is not effective, and the hypotheses of
`OrientationRep.exists_unique_transport_of_isLRLocal` hold (tame, sc-smooth bump functions, tame
germ data, the local regularity property); so for every representative `b` of the section
exactly one orientation of `F_b` corresponds to the orientation over every diagram of every
generalized strong bundle isomorphism `𝔄` with `Γ_b ∘ |𝔄| = Γ` and `𝔄_* F = F_b`. -/
theorem exists_unique_transport_z3 (hφ : ContDiff ℝ ∞ φ) :
    ¬ (z3SEP k).X.IsEffective ∧ (z3SEP k).X.PObj.IsTame ∧
    (z3SEP k).X.PObj.AdmitsBumpFunctions ∧
    (z3SEP k).B.IsScFredholmSectionTame (graphSection φ) ∧ (z3SEP k).E.IsLRLocal ∧
    ∀ (b : SectionRep (z3Bundle k)) (_ : ⟦b⟧ = (z3FredholmSection hφ).1),
      ∃ (hFb : b.S.A.E.IsScFredholmSectionFunctor b.F)
        (hsec' : b.S.A.B.HasScPlusSectionsThrough),
        ∃! o' : ∀ x (hs : x ∈ b.S.A.X.PObj.smoothSet), Orx b.F hFb.2 x hs,
          (∀ t' : TopologicalSpace (OrSpace b.F hFb.2),
            (haveI := paracompactSpace_rn_prod b.S.A.X.PObj
             haveI := paracompactSpace_rn_pullback b.S.A.B
             IsOrientationTopology b.F hFb.2 t') →
              b.S.A.E.definition_12_5_4 hFb hsec' t' o') ∧
          ∀ (𝔄 : GenSBMap (z3OrientationRep hφ).a.S.A b.S.A) (h𝔄 : 𝔄.IsGeneralizedIso)
            (_ : ⇑b.S.Γ ∘ 𝔄.orbitMap = ⇑(z3OrientationRep hφ).a.S.Γ)
            (hpush : b.F = GenSBMap.pushforward h𝔄 (z3OrientationRep hφ).a.F)
            (D : SDiagram (z3OrientationRep hφ).a.S.A b.S.A) (hD : D.cls = 𝔄) v
            (hv : v ∈ D.B.X.PObj.smoothSet),
            (sbe (GenSBMap.equivalences_Ψ_of_cls h𝔄 hD)).orEqv
                (D.isScFredholm_pullback (z3OrientationRep hφ).hF) hFb
                (GenSBMap.pullback_eq_of_cls' h𝔄 hD (z3OrientationRep hφ).hF.1 hpush)
                (D.hasScPlusSectionsThrough_B (z3OrientationRep hφ).hsec) hsec' v hv
                (o' (D.Ψ.ϕ.obj v)
                  ((sbe (GenSBMap.equivalences_Ψ_of_cls h𝔄 hD)).smooth_obj hv)) =
              D.hΦ.orEqv (D.isScFredholm_pullback (z3OrientationRep hφ).hF)
                (z3OrientationRep hφ).hF rfl
                (D.hasScPlusSectionsThrough_B (z3OrientationRep hφ).hsec)
                (z3OrientationRep hφ).hsec v hv
                ((z3OrientationRep hφ).o (D.Φ.ϕ.obj v) (D.hΦ.smooth_obj hv)) :=
  ⟨not_isEffective_trivialZ3, isTame_z3SEP k, admitsBumpFunctions_z3SEP k,
    isScFredholmSectionTame_graphSection_z3 hφ, isLRLocal_z3EpBundle k, fun b hb =>
      (z3OrientationRep hφ).exists_unique_transport_of_isLRLocal b hb (isTame_z3SEP k)
        (admitsBumpFunctions_z3SEP k) (isScFredholmSectionTame_graphSection_z3 hφ)
        (isLRLocal_z3EpBundle k)⟩

end StrongBundleLocalizationExamples

end Polyfold
