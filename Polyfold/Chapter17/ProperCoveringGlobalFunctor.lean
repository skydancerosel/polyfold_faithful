import Polyfold.Chapter17.ProperCoveringGlobalModel
import Polyfold.Chapter17.ProperCoveringBranched
import Polyfold.Chapter17.SigmaStrongBundle
import Polyfold.Chapter8.ProperCoveringFibredMap

set_option maxSynthPendingDepth 3

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17, §17.8,
(17.104) (p. 838): **`τ̂ : E → X` is a proper covering functor** in the sense of Definition 8.5.1
(p. 383), for a proper polyfold covering functor `P : A → B` (Definition 17.8.13, p. 836) and any
family of proper covering uniformizers.  Numbers and pages are the 2021 text's.

# The functor `τ̂` of (17.104) is a proper covering functor

## The text, paraphrased

(p. 838) With `E = ⊔ E_λ`, `X = ⊔ O_λ`, `τ̂(e_λ) = τ̂_λ(e_λ)`, `𝐄 = ⊔ M(Ψ̂_λ, Ψ̂_λ')`,
`𝐗 = ⊔ M(Ψ_λ, Ψ_λ')`: "one easily verifies" that `τ̂` extends to a proper covering functor
`E → X`.

## What is formalized

* General, for disjoint unions of M-polyfolds and `Sigma.map id f` (`f i : Y i → X i`), in
  namespace `Polyfold.MPolyfold`: `sigmaMap_preimage_singleton` (the fibre over `(i, x)` is
  `{i} × f_i⁻¹(x)`), `finite_sigmaMap_preimage_singleton`, `sigmaMap_preimage_image`, and
  **`evenlyCovered_sigmaMap`**: condition (2) of Definition 8.5.1 passes from the `f i` to
  `Sigma.map id f`.
* For a proper polyfold covering structure `S` and a family `Uf` (namespace
  `Polyfold.ProperPolyfoldCoveringStructure`): `hatModelFunctor_obj_eq` (`τ̂` on objects is
  `Sigma.map id τ̂_λ`), `surjective_hatModelObj`, `isLocalScDiffeo_hatModelObj`,
  `finite_hatModelObj_preimage`, `evenlyCovered_hatModelObj`, `isLocalScDiffeo_hatModelMor`
  (`τ̂` on morphisms is `⊔ p`, a local sc-diffeomorphism), **`bijective_hatModel_fibredMap`**
  (`L_τ̂ : 𝐄 → 𝐗 ₛ×_τ̂ E` is bijective, from Lemma 17.8.14 on each summand),
  `isScDiffeo_hatModel_fibredMap` (Definition 8.5.1 (3) for `τ̂`: the gluing of Proposition
  17.8.15 over the disjoint unions) and **`hatModelFunctor_isProperCovering`**.
* Witness: **`z3HatModel_isProperCovering`**, for the two sheets of `ℤ/3 ⋉ ℝ` over `ℤ/3 ⋉ ℝ`
  (`z3HatFam` of `ProperCoveringGlobalModel`): `τ̂` is a proper covering functor, its fibre over
  `0` has two points, the object `(true, 0)` of `E` has the non-unit automorphism `z3HatMor`,
  and `τ̂(z3HatMor)` is a non-unit automorphism of `τ̂(true, 0)` in `X`.

## Readings and proof

* "`τ̂` extends to a proper covering functor `E → X`" is read as: the sc-smooth functor
  `hatModelFunctor` of (17.104) satisfies Definition 8.5.1 (`EpFunctor.IsProperCovering`).  No
  hypothesis beyond Definition 17.8.13 and Definition 17.8.1 for `P` is used, and none on the
  family `Uf` (the covering condition is not needed).
* (1) and (2) hold summand by summand: each `τ̂_λ` is a proper covering functor (Remark 17.8.5;
  `ProperCoveringUniformizer.isProperCovering_τ`, whose fibre is finite because `Ψ̂_λ` maps it
  bijectively onto the finite fibre `P⁻¹(β)`).
* (3): the map `L_τ̂ : 𝐄 → 𝐗 ₛ×_τ̂ E` is a local sc-diffeomorphism for every sc-smooth
  functor (`EpFunctor.isLocalScDiffeo_fibredMap`, Chapter 8), so (3) is its bijectivity
  (`EpFunctor.isScDiffeo_fibredMap_iff_bijective`).  On the summand `M(Ψ̂_λ, Ψ̂_λ')` the map
  `L_τ̂` is the bijection (17.103) of Lemma 17.8.14 (the map of Proposition 17.8.15) followed by
  the inclusion of the summand `M(Ψ_λ, Ψ_λ') ₛ×_τ̂ E_λ`, and these summands partition
  `𝐗 ₛ×_τ̂ E`.  This is the gluing of Proposition 17.8.15 over the disjoint unions; it needs no
  identification of the fibred-product sub-M-polyfold of the disjoint unions with the disjoint
  union of the fibred products.
-/

open Set Function Topology CategoryTheory

noncomputable section

namespace Polyfold

universe u

/-! ### Condition (2) of Definition 8.5.1 for `Sigma.map id f` -/

namespace MPolyfold

section SigmaCovering

variable {ι : Type*} {Y : ι → Type u} [∀ i, TopologicalSpace (Y i)] [∀ i, T2Space (Y i)]
  [∀ i, ParacompactSpace (Y i)] (P : ∀ i, MPolyfold (Y i))
  {X : ι → Type u} [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)]
  [∀ i, ParacompactSpace (X i)] (R : ∀ i, MPolyfold (X i))
  {f : ∀ i, Y i → X i}

omit [∀ i, TopologicalSpace (Y i)] [∀ i, T2Space (Y i)] [∀ i, ParacompactSpace (Y i)]
  [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)] [∀ i, ParacompactSpace (X i)] in
/-- The preimage of `{i} × U` under `Sigma.map id f` is `{i} × f_i⁻¹(U)`. -/
theorem sigmaMap_preimage_image (i : ι) (U : Set (X i)) :
    Sigma.map id f ⁻¹' (Sigma.mk i '' U) = Sigma.mk i '' (f i ⁻¹' U) := by
  ext ⟨j, y⟩
  constructor
  · rintro ⟨x, hx, hxy⟩
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 hxy
    exact ⟨y, by rw [eq_of_heq h] at hx; exact hx, rfl⟩
  · rintro ⟨y', hy', hyy⟩
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 hyy
    rw [← eq_of_heq h]
    exact ⟨f i y', hy', rfl⟩

omit [∀ i, TopologicalSpace (Y i)] [∀ i, T2Space (Y i)] [∀ i, ParacompactSpace (Y i)]
  [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)] [∀ i, ParacompactSpace (X i)] in
/-- The fibre of `Sigma.map id f` over `(i, x)` is `{i} × f_i⁻¹(x)`. -/
theorem sigmaMap_preimage_singleton (i : ι) (x : X i) :
    Sigma.map id f ⁻¹' {⟨i, x⟩} = Sigma.mk i '' (f i ⁻¹' {x}) := by
  rw [← image_singleton, sigmaMap_preimage_image]

omit [∀ i, TopologicalSpace (Y i)] [∀ i, T2Space (Y i)] [∀ i, ParacompactSpace (Y i)]
  [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)] [∀ i, ParacompactSpace (X i)] in
/-- Finite fibres of the `f i` give finite fibres of `Sigma.map id f`. -/
theorem finite_sigmaMap_preimage_singleton (h : ∀ i (x : X i), (f i ⁻¹' {x}).Finite)
    (x : Σ i, X i) : (Sigma.map id f ⁻¹' {x}).Finite := by
  obtain ⟨i, x⟩ := x
  rw [sigmaMap_preimage_singleton]
  exact (h i x).image _

/-- **Condition (2) of Definition 8.5.1 for disjoint unions**: if every `f i` has evenly covered
fibres, so has `Sigma.map id f`.  Over `(i, x)` the neighbourhood is `{i} × U` and the sheets
are `{i} × V(y)`, with the data `U`, `V`, `σ` of `f i` at `x`. -/
theorem evenlyCovered_sigmaMap
    (h : ∀ i (x : X i), ∃ (U : Set (X i)) (V : Y i → Set (Y i)) (σ : Y i → X i → Y i),
      IsOpen U ∧ x ∈ U ∧ (f i ⁻¹' {x}).PairwiseDisjoint V ∧
      (∀ y ∈ f i ⁻¹' {x}, y ∈ V y ∧ (P i).IsScDiffeoOn (R i) (f i) (σ y) (V y) U) ∧
      f i ⁻¹' U = ⋃ y ∈ f i ⁻¹' {x}, V y) (x : Σ i, X i) :
    ∃ (U : Set (Σ i, X i)) (V : (Σ i, Y i) → Set (Σ i, Y i))
      (σ : (Σ i, Y i) → (Σ i, X i) → Σ i, Y i),
      IsOpen U ∧ x ∈ U ∧ (Sigma.map id f ⁻¹' {x}).PairwiseDisjoint V ∧
      (∀ y ∈ Sigma.map id f ⁻¹' {x}, y ∈ V y ∧
        (sigma P).IsScDiffeoOn (sigma R) (Sigma.map id f) (σ y) (V y) U) ∧
      Sigma.map id f ⁻¹' U = ⋃ y ∈ Sigma.map id f ⁻¹' {x}, V y := by
  obtain ⟨i, x⟩ := x
  obtain ⟨U, V, σ, hU, hxU, hdisj, hV, hpre⟩ := h i x
  have hUo : IsOpen (Sigma.mk i '' U) := isOpenMap_sigmaMk _ hU
  rcases isEmpty_or_nonempty (Y i) with hY | ⟨⟨y₀⟩⟩
  · -- no point over `(i, x)`
    have hfib : Sigma.map id f ⁻¹' {⟨i, x⟩} = ∅ := by
      rw [sigmaMap_preimage_singleton]
      exact image_eq_empty.2 (eq_empty_of_isEmpty _)
    refine ⟨Sigma.mk i '' U, fun _ => ∅, fun p _ => p, hUo, ⟨x, hxU, rfl⟩, ?_, ?_, ?_⟩
    · rw [hfib]
      exact pairwiseDisjoint_empty
    · rw [hfib]
      exact fun _ h => absurd h (notMem_empty _)
    · rw [hfib, sigmaMap_preimage_image]
      simp only [mem_empty_iff_false, iUnion_of_empty, iUnion_empty]
      exact image_eq_empty.2 (eq_empty_of_isEmpty _)
  · refine ⟨Sigma.mk i '' U, fun p => Sigma.mk i '' V (sigmaProj i y₀ p),
      fun p => Sigma.mk i ∘ σ (sigmaProj i y₀ p) ∘ sigmaProj (id i) x, hUo, ⟨x, hxU, rfl⟩,
      ?_, ?_, ?_⟩
    · rw [sigmaMap_preimage_singleton]
      rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ hne
      have hne' : y ≠ y' := fun h => hne (by rw [h])
      simp only [Function.onFun, sigmaProj_mk]
      exact (disjoint_image_iff sigma_mk_injective).2 (hdisj hy hy' hne')
    · rw [sigmaMap_preimage_singleton]
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨hyV, hd⟩ := hV y hy
      simp only [sigmaProj_mk]
      exact ⟨⟨y, hyV, rfl⟩, isScDiffeoOn_sigmaMap_image P R (σ := id) hd x⟩
    · rw [sigmaMap_preimage_image, hpre, sigmaMap_preimage_singleton, image_iUnion₂,
        biUnion_image]
      simp only [sigmaProj_mk]

end SigmaCovering

end MPolyfold

/-! ### `τ̂ : E → X` is a proper covering functor -/

namespace ProperPolyfoldCoveringStructure

open ProperCoveringUniformizer ProperCoveringUniformizerConstruction GCT GCT.PolyfoldConstruction

variable {A B : GCT.{u}} {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr}
  (S : ProperPolyfoldCoveringStructure P) {ι : Type u} (Uf : ι → S.toC.Unif)
  (hPc : P.IsProperCoveringGCT)

/-- `τ̂` on objects is `Sigma.map id τ̂_λ`. -/
theorem hatModelFunctor_obj_eq :
    (S.hatModelFunctor Uf hPc).obj = Sigma.map id fun i => (Uf i).unif.τ.obj := rfl

/-- Definition 8.5.1 (1): `τ̂` is surjective on objects. -/
theorem surjective_hatModelObj : Surjective (S.hatModelFunctor Uf hPc).obj := by
  rw [hatModelFunctor_obj_eq]
  exact Function.surjective_id.sigma_map fun i => ((Uf i).unif.isProperCovering_τ hPc).surjective

/-- Definition 8.5.1 (1): `τ̂` is a local sc-diffeomorphism on objects. -/
theorem isLocalScDiffeo_hatModelObj :
    (S.hatEpGroupoid Uf hPc).PObj.IsLocalScDiffeo (S.baseEP Uf).X.PObj
      (S.hatModelFunctor Uf hPc).obj :=
  MPolyfold.isLocalScDiffeo_sigmaMap (fun i => (Uf i).unif.E.PObj)
    (R := fun i => (S.baseFam Uf i).1.P) (σ := id) (g := fun i => (Uf i).unif.τ.obj)
    fun i => ((Uf i).unif.isProperCovering_τ hPc).isLocalScDiffeo

/-- Definition 8.5.1 (2): the fibres of `τ̂` are finite. -/
theorem finite_hatModelObj_preimage (x : S.SB.ModelObj (S.baseFam Uf)) :
    ((S.hatModelFunctor Uf hPc).obj ⁻¹' {x}).Finite :=
  MPolyfold.finite_sigmaMap_preimage_singleton (f := fun i => (Uf i).unif.τ.obj)
    (fun i => ((Uf i).unif.isProperCovering_τ hPc).finite_fiber) x

/-- Definition 8.5.1 (2): the fibres of `τ̂` are evenly covered. -/
theorem evenlyCovered_hatModelObj (x : S.SB.ModelObj (S.baseFam Uf)) :
    ∃ (U : Set (S.SB.ModelObj (S.baseFam Uf))) (V : S.HatObj Uf → Set (S.HatObj Uf))
      (σ : S.HatObj Uf → S.SB.ModelObj (S.baseFam Uf) → S.HatObj Uf),
      IsOpen U ∧ x ∈ U ∧ ((S.hatModelFunctor Uf hPc).obj ⁻¹' {x}).PairwiseDisjoint V ∧
      (∀ y ∈ (S.hatModelFunctor Uf hPc).obj ⁻¹' {x}, y ∈ V y ∧
        (S.hatEpGroupoid Uf hPc).PObj.IsScDiffeoOn (S.baseEP Uf).X.PObj
          (S.hatModelFunctor Uf hPc).obj (σ y) (V y) U) ∧
      (S.hatModelFunctor Uf hPc).obj ⁻¹' U =
        ⋃ y ∈ (S.hatModelFunctor Uf hPc).obj ⁻¹' {x}, V y :=
  MPolyfold.evenlyCovered_sigmaMap (fun i => (Uf i).unif.E.PObj)
    (fun i => (S.baseFam Uf i).1.P) (f := fun i => (Uf i).unif.τ.obj)
    (fun i => ((Uf i).unif.isProperCovering_τ hPc).evenlyCovered) x

/-- `τ̂` on morphisms is `⊔ p : 𝐄 → 𝐗`, a local sc-diffeomorphism (Definition 17.8.13). -/
theorem isLocalScDiffeo_hatModelMor :
    (S.hatEpGroupoid Uf hPc).PMor.IsLocalScDiffeo (S.baseEP Uf).X.PMor
      (S.hatModelFunctor Uf hPc).mor :=
  MPolyfold.isLocalScDiffeo_sigmaMap (fun p : ι × ι => S.hatTransPolyfold (Uf p.1) (Uf p.2))
    (R := fun p : ι × ι => S.SB.transPolyfold (S.baseFam Uf p.1) (S.baseFam Uf p.2))
    (σ := id) (g := fun p a => transMap (Uf p.1).unif (Uf p.2).unif a)
    fun p => S.isLocalScDiffeo_p (Uf p.1) (Uf p.2)

/-- **`L_τ̂ : 𝐄 → 𝐗 ₛ×_τ̂ E`, `φ ↦ (τ̂(φ), s(φ))`, is bijective**: on the summand
`M(Ψ̂_λ, Ψ̂_λ')` it is the bijection (17.103) of Lemma 17.8.14 onto the summand
`M(Ψ_λ, Ψ_λ') ₛ×_τ̂ E_λ`, and these summands partition `𝐗 ₛ×_τ̂ E`. -/
theorem bijective_hatModel_fibredMap : Bijective (S.hatModelFunctor Uf hPc).fibredMap := by
  constructor
  · rintro ⟨p, a⟩ ⟨q, b⟩ h
    have h1 := congrArg (fun z => (z.1.1 : S.SB.ModelMor (S.baseFam Uf))) h
    have h2 := congrArg (fun z => (z.1.2 : S.HatObj Uf)) h
    obtain ⟨rfl, h1'⟩ := Sigma.mk.inj_iff.1 h1
    have h2' := eq_of_heq (Sigma.mk.inj_iff.1 h2).2
    have hab : fibredTransMap (Uf p.1).unif (Uf p.2).unif a =
        fibredTransMap (Uf p.1).unif (Uf p.2).unif b :=
      Subtype.ext (Prod.ext (eq_of_heq h1') h2')
    rw [(lemma_17_8_14 (Uf p.1).unif hPc (Uf p.2).unif).1 hab]
  · rintro ⟨⟨⟨p, c⟩, ⟨i, e⟩⟩, hce⟩
    have hce' : (⟨p.1, c.src⟩ : S.SB.ModelObj (S.baseFam Uf)) = ⟨i, (Uf i).unif.τ.obj e⟩ := hce
    obtain ⟨rfl, hce''⟩ := Sigma.mk.inj_iff.1 hce'
    obtain ⟨a, ha⟩ := (lemma_17_8_14 (Uf p.1).unif hPc (Uf p.2).unif).2
      ⟨(c, e), eq_of_heq hce''⟩
    refine ⟨⟨p, a⟩, Subtype.ext (Prod.ext ?_ ?_)⟩
    · exact Sigma.ext rfl (heq_of_eq (congrArg (fun z => z.1.1) ha))
    · exact Sigma.ext rfl (heq_of_eq (congrArg (fun z => z.1.2) ha))

/-- **Definition 8.5.1 (3) for `τ̂`**: `L_τ̂ : 𝐄 → 𝐗 ₛ×_τ̂ E` is an sc-diffeomorphism onto the
fibred-product sub-M-polyfold of `𝐗 × E` (Proposition 17.8.15 glued over the disjoint unions). -/
theorem isScDiffeo_hatModel_fibredMap :
    letI := MPolyfold.paracompactSpace_prod (S.baseEP Uf).X.PMor (S.hatEpGroupoid Uf hPc).PObj
    letI := ((S.baseEP Uf).X.PMor.prod (S.hatEpGroupoid Uf hPc).PObj).paracompactSpace_subtype
      (MPolyfold.fibredProduct (S.baseEP Uf).X.src (S.hatModelFunctor Uf hPc).obj)
    ∃ g : MPolyfold.fibredProduct (S.baseEP Uf).X.src (S.hatModelFunctor Uf hPc).obj →
        S.HatMor Uf,
      (S.hatEpGroupoid Uf hPc).PMor.IsScDiffeoOn (MPolyfold.subPolyfold
        (MPolyfold.isSubMPolyfold_fibredProduct (S.baseEP Uf).X.isLocalScDiffeo_src
          (S.hatModelFunctor Uf hPc).isScSmoothMap_obj))
        (S.hatModelFunctor Uf hPc).fibredMap g univ univ :=
  (S.hatModelFunctor Uf hPc).isScDiffeo_fibredMap_of_bijective
    (S.bijective_hatModel_fibredMap Uf hPc)

/-- **(17.104), p. 838: `τ̂ : E → X` is a proper covering functor** (Definition 8.5.1), for every
family of proper covering uniformizers of a proper polyfold covering structure. -/
theorem hatModelFunctor_isProperCovering : (S.hatModelFunctor Uf hPc).IsProperCovering :=
  (S.hatModelFunctor Uf hPc).isProperCovering_of_bijective (S.surjective_hatModelObj Uf hPc)
    (S.isLocalScDiffeo_hatModelObj Uf hPc) (S.finite_hatModelObj_preimage Uf hPc)
    (S.evenlyCovered_hatModelObj Uf hPc) (S.bijective_hatModel_fibredMap Uf hPc)

end ProperPolyfoldCoveringStructure

/-! ### Witness: two sheets of `ℤ/3 ⋉ ℝ` -/

section Z3

open GCT GCT.PolyfoldConstruction ProperPolyfoldCoveringStructure EpGroupoid.Examples

/-- **(17.104) for the two sheets of `ℤ/3 ⋉ ℝ` over `ℤ/3 ⋉ ℝ`**: `τ̂` is a proper covering
functor, its fibre over `0` has two points, the object `(true, 0)` of `E` has the non-unit
automorphism `z3HatMor`, and `τ̂(z3HatMor)` is a non-unit automorphism of `τ̂(true, 0)`. -/
theorem z3HatModel_isProperCovering :
    let F := z3PolyfoldCoveringFunctor
    let hPc := F.isProperCovering
    (F.S.hatModelFunctor z3HatFam hPc).IsProperCovering ∧
      ((F.S.hatModelFunctor z3HatFam hPc).obj ⁻¹' {⟨PUnit.unit, (0 : Fin 1 → ℝ)⟩}).ncard = 2 ∧
      (F.S.hatEpGroupoid z3HatFam hPc).src z3HatMor = z3HatPt ∧
      (F.S.hatEpGroupoid z3HatFam hPc).tgt z3HatMor = z3HatPt ∧
      z3HatMor ≠ (F.S.hatEpGroupoid z3HatFam hPc).unit z3HatPt ∧
      (F.S.hatModelFunctor z3HatFam hPc).mor z3HatMor ≠
        (F.S.baseEP z3HatFam).X.unit ((F.S.hatModelFunctor z3HatFam hPc).obj z3HatPt) := by
  intro F hPc
  obtain ⟨-, -, -, -, hs, ht, hne, hcard⟩ := z3HatModel_nondegenerate
  refine ⟨F.S.hatModelFunctor_isProperCovering z3HatFam hPc, hcard, hs, ht, hne, fun h => ?_⟩
  have h1 := congrArg (fun φ : F.S.SB.ModelMor (F.S.baseFam z3HatFam) => φ.2.mor.1) h
  change Multiplicative.ofAdd (1 : ZMod 3) = 1 at h1
  exact absurd h1 (by decide)

end Z3

end Polyfold
