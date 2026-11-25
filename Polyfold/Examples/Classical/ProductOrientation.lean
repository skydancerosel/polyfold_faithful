import Polyfold.Examples.Classical.ProductCharts
import Polyfold.Examples.Classical.ProductPaths
import Polyfold.Examples.OrInvariantSmooth

/-!
# The classical reduction crossed with the weighted `ℓ²` factor: the canonical orientation

For Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Theorem 16.6.6,
2021 p. 739, with Definitions 12.5.4 (2021 p. 594) and 16.6.5 (2021 p. 739).  The section
`f(x, e) = ((x, φ x), (e, e))` of `(ℝⁿ × ℝⁿ) × (H ◁ H)` over `(G ⋉ ℝⁿ) × H` (`ProductSection.lean`)
has an orientation for which the sign of an isomorphism `(f + S)'(y, 0) = D(φ + ψ)(y) ⊕ id_H` is
the sign of `det D(φ + ψ)(y)`.  The comparison of two block isomorphisms `A ⊕ id_H` is
`isPos_iff_blk_of_isPos` (`ProductDetSign.lean`); the readings in the product chart points are
those of `ProductCharts.lean`.

## What is formalized (namespace `Polyfold.Examples.Classical.Product`)

* `sectionAdd_gP`: the sum of the sections `((x, a x), (e, 0))` and `((x, b x), (e, 0))`.
* `idSecP φ y`: the section `((x, (x − y) − φ x), (e, 0))`, with `(f + S)'(y, 0) = id ⊕ id`;
  **`isPosOr_iff_det_of_isPosIdP`**: if `o` is positive at it, `o` is positive at an isomorphism
  `(f + S)'(y, 0) = D(φ + ψ)(y) ⊕ id` iff `det D(φ + ψ)(y) > 0`.
* `famP g`: the section `(t, (x, e)) ↦ ((x, g(t)), (e, 0))` of the pull-back bundle;
  `isPosIdP_iff`: for a continuous orientation, positivity at the identity at `(0, 0)` and at
  `(y, 0)` agree (along `t ↦ (t y, 0)`).
* `prOrientation σ hφ heq`; **`isPosOr_prOrientation_iff`**.
* `orMor_zero_eqP`: an isotropy morphism `((g, 0), 0)` preserves an orientation positive at the
  identity at `(0, 0)` when `det ρ(g) · det σ(g) > 0`; **`isOrInvariant_prOrientation`**
  (Definition 12.5.4): at `((g, q), e)` with `e` smooth the invariance is constant along
  `t ↦ ((g, t q), t e)`.
* **`prOrientationRep σ hφ heq hdet`** (Definition 16.6.5),
  `canonicalGermInput_prOrientationRep`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter Module

open scoped ContDiff

noncomputable section

namespace Polyfold.Examples.Classical.Product

open TrivialBundle EpGroupoid.Examples StrongBundle MPolyfold StrongPolyfoldBundle
  StrongPolyfoldBundleStructure StrongBundleEquivalenceExamples
  StrongBundleLocalizationExamples WeightedEllTwo SBLocalization StrongRetr
  Polyfold.Examples.OrbifoldSquareInf Polyfold.Examples.Classical

variable {G : Type} [Group G] [Fintype G] [TopologicalSpace G] [DiscreteTopology G]
  {n : ℕ} [DistribMulAction G (Fin n → ℝ)] [SMulCommClass G ℝ (Fin n → ℝ)]
  [FaithfulSMul G (Fin n → ℝ)]
  (σ : G →* ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ))) {φ : (Fin n → ℝ) → (Fin n → ℝ)}

/-! ### Sums of the sections `((x, a x), (e, 0))` -/

/-- **The sum of `((x, a x), (e, 0))` and `((x, b x), (e, 0))` is `((x, (a + b) x), (e, 0))`.** -/
theorem sectionAdd_gP {a b : (Fin n → ℝ) → (Fin n → ℝ)} (ha : ContDiff ℝ ∞ a)
    (hb : ContDiff ℝ ∞ b) : sectionAdd (AP σ).P (gP σ a) (gP σ b) = gP σ (a + b) := by
  have hsa : IsSection (AP σ).P (gP σ a) := (isScPlusSection_gP σ ha).1
  have hsb : IsSection (AP σ).P (gP σ b) := (isScPlusSection_gP σ hb).1
  funext x
  obtain ⟨z, e⟩ : (Fin n → ℝ) × HObj := x
  refine (sectionAdd_apply hsa hsb ((z, e) : (AP σ).Obj)).trans ?_
  let PH' : HObj × H 0 → HObj := LocalBundle.proj (E := H) (U := (univ : Set (H 0))) (F := H)
  let Φ := prodFiberCLE (proj n n) PH' ((z, e) : (Fin n → ℝ) × HObj)
  let v : Prod.map (proj n n) PH' ⁻¹' {((z, e) : (Fin n → ℝ) × HObj)} :=
    ⟨gP σ a ((z, e) : (AP σ).Obj), rfl⟩
  let w : Prod.map (proj n n) PH' ⁻¹' {((z, e) : (Fin n → ℝ) × HObj)} :=
    ⟨gP σ b ((z, e) : (AP σ).Obj), rfl⟩
  change (((v + w : Prod.map (proj n n) PH' ⁻¹' {((z, e) : (Fin n → ℝ) × HObj)}) :
    ((Fin n → ℝ) × (Fin n → ℝ)) × (HObj × H 0))) = ((z, a z + b z), (e, (0 : H 0)))
  have hΦ : Φ (v + w) = Φ v + Φ w := map_add Φ _ _
  have h1 : (((Φ (v + w)).1 : proj n n ⁻¹' {z}) : (Fin n → ℝ) × (Fin n → ℝ)) =
      (z, a z + b z) := by
    refine (congrArg Subtype.val (congrArg Prod.fst hΦ)).trans ?_
    exact Prod.ext (fst_fiber _) (snd_add _ _)
  have h2 : (((Φ (v + w)).2 : PH' ⁻¹' {e}) : HObj × H 0) = (e, (0 : H 0)) := by
    refine (congrArg Subtype.val (congrArg Prod.snd hΦ)).trans ?_
    have h0v : (Φ v).2 = 0 := by
      apply (LocalBundle.fibEquiv (F := H) e).injective
      exact ((LocalBundle.fibEquiv (F := H) e).linearEquiv ℝ).map_zero.symm
    have h0w : (Φ w).2 = 0 := by
      apply (LocalBundle.fibEquiv (F := H) e).injective
      exact ((LocalBundle.fibEquiv (F := H) e).linearEquiv ℝ).map_zero.symm
    have hs : (Φ v + Φ w).2 = 0 := by
      change (Φ v).2 + (Φ w).2 = 0
      rw [h0v, h0w, add_zero]
    refine (congrArg Subtype.val hs).trans ?_
    refine Prod.ext rfl ?_
    exact ((LocalBundle.fibEquiv (F := H) e).linearEquiv ℝ).map_zero
  exact Prod.ext h1 h2

/-! ### The identity at `(y, 0)` -/

/-- **The section `((x, (x − y) − φ x), (e, 0))`**: `(f + S)(x, e) = ((x, x − y), (e, e))`. -/
abbrev idSecP (φ : (Fin n → ℝ) → (Fin n → ℝ)) (y : Fin n → ℝ) : (AP σ).Obj → (AP σ).W :=
  gP σ (idFun φ y)

theorem isScPlusSection_idSecP (hφ : ContDiff ℝ ∞ φ) (y : Fin n → ℝ) :
    (AP σ).B.IsScPlusSection (idSecP σ φ y) :=
  isScPlusSection_gP σ (contDiff_idFun hφ y)

/-- `(f + S)(y, 0) = 0` for `S = idSecP φ y`. -/
theorem isZeroAt_idSecP (hφ : ContDiff ℝ ∞ φ) (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    (y : Fin n → ℝ) :
    IsZeroAt (AP σ).P (sectionAdd (AP σ).P (fP σ φ) (idSecP σ φ y)) ((y, h0) : (AP σ).Obj) :=
  isZeroAt_gP σ (isScFredholmSectionFunctor_fP hφ heq).2 (isScPlusSection_idSecP σ hφ y)
    (by rw [add_idFun]; exact sub_self y)

/-- `(f + S)'(y, 0)` is an isomorphism in every chart point for `S = idSecP φ y`. -/
theorem bijective_stabT_idSecP (hφ : ContDiff ℝ ∞ φ) (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    {y : Fin n → ℝ} {S : (AP σ).Obj → (AP σ).W} (hSe : S = idSecP σ φ y)
    (hS : (AP σ).B.IsScPlusSection S)
    (hz : IsZeroAt (AP σ).P (sectionAdd (AP σ).P (fP σ φ) S) ((y, h0) : (AP σ).Obj))
    (p : ChartPoint (AP σ).B ((y, h0) : (AP σ).Obj)) :
    Bijective (p.stabT (isScFredholmSectionFunctor_fP hφ heq).2 hS hz) := by
  subst hSe
  refine bijective_stabT_P σ hφ (contDiff_idFun hφ y) _ hS hz ?_ p
  rw [fderiv_add_idFun, ContinuousLinearMap.coe_id']
  exact bijective_id

/-- **The sign of an isomorphism `(f + S)'(y, 0)`** for an orientation `o` positive at the identity
`(f + idSecP φ y)'(y, 0)`: `o` is positive at `(f + S)'(y, 0) = D(φ + ψ)(y) ⊕ id`, `S` the section
`((x, ψ x), (e, 0))`, iff `det D(φ + ψ)(y) > 0` (`isPos_iff_blk_of_isPos`). -/
theorem isPosOr_iff_det_of_isPosIdP (hφ : ContDiff ℝ ∞ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x)) (hf : (AP σ).B.IsScFredholmSection (fP σ φ))
    {y : Fin n → ℝ} (hs : ((y, h0) : (AP σ).Obj) ∈ (AP σ).X.PObj.smoothSet)
    (o : Orx (B := (AP σ).B) (fP σ φ) hf ((y, h0) : (AP σ).Obj) hs)
    (hpos : IsPosOr hf hs o (idSecP σ φ y) (isScPlusSection_idSecP σ hφ y)
      (isZeroAt_idSecP σ hφ heq y))
    {ψ : (Fin n → ℝ) → (Fin n → ℝ)} (hψ : ContDiff ℝ ∞ ψ) (hS : (AP σ).B.IsScPlusSection (gP σ ψ))
    (hz : IsZeroAt (AP σ).P (sectionAdd (AP σ).P (fP σ φ) (gP σ ψ)) ((y, h0) : (AP σ).Obj))
    (hb : Bijective (fderiv ℝ (φ + ψ) y)) :
    IsPosOr hf hs o (gP σ ψ) hS hz ↔
      0 < LinearMap.det (fderiv ℝ (φ + ψ) y : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) := by
  have h₀ : (orPt (AP σ).B ((y, h0) : (AP σ).Obj) hs).IsPos o
      (blk (orTEquivP σ y hs) (orKEquivP σ y hs) (fderiv ℝ (φ + idFun φ y) y)) := by
    rw [← stabT_eq_blk σ hφ (contDiff_idFun hφ y) hf (isScPlusSection_idSecP σ hφ y)
      (isZeroAt_idSecP σ hφ heq y) hs]
    exact hpos
  change (orPt (AP σ).B ((y, h0) : (AP σ).Obj) hs).IsPos o
    ((orPt (AP σ).B ((y, h0) : (AP σ).Obj) hs).stabT hf hS hz) ↔ _
  rw [stabT_eq_blk σ hφ hψ hf hS hz hs,
    isPos_iff_blk_of_isPos _ o _ _ (blk_mem_linSet hφ heq y hs) hb h₀, fderiv_add_idFun,
    ContinuousLinearMap.coe_id, LinearMap.det_id, one_mul]

/-! ### The family `(t, (x, e)) ↦ ((x, g(t)), (e, 0))` -/

section Family

variable {m : ℕ}

/-- The constant section through the `i`-th basis vector of the fibre `ℝⁿ`, and `0` in `H`. -/
def basisP (i : Fin n) : (AP σ).Obj → (AP σ).W := Prod.map (OrbifoldSquare.basisSection n n i) (constSec 0)

theorem isScPlusSection_basisP (i : Fin n) : (AP σ).B.IsScPlusSection (basisP σ i) :=
  StrongBundle.IsScPlusSection.prod (isScPlusSection_graphSection contDiff_const)
    (isScPlusSection_constSec H.smooth.zero_mem)

/-- **The section `(t, (x, e)) ↦ ((x, g(t)), (e, 0))`** of the pull-back of `(AP σ).B` to
`ℝᵐ × (ℝⁿ × H)`. -/
def famP (g : (Fin m → ℝ) → (Fin n → ℝ)) :
    (Fin m → ℝ) × (AP σ).Obj →
      pullbackSpace (AP σ).P (Prod.snd : (Fin m → ℝ) × (AP σ).Obj → _) :=
  reparamSection g (paramComb (basisP σ) fun i => (isScPlusSection_basisP σ i).1)
    (isSection_pullbackLift _)

/-- The slices of `famP g` are the sections `((x, g(t)), (e, 0))`. -/
theorem pullbackSlice_famP (g : (Fin m → ℝ) → (Fin n → ℝ)) (q : Fin m → ℝ) :
    pullbackSlice (famP σ g) q = gP σ (fun _ => g q) := by
  funext x
  obtain ⟨z, e⟩ : (Fin n → ℝ) × HObj := x
  set w : (AP σ).P ⁻¹' {((z, e) : (AP σ).Obj)} :=
    fiberComb (basisP σ) (fun i => (isScPlusSection_basisP σ i).1)
      (g q, ((z, e) : (AP σ).Obj)) with hw
  change (w : (AP σ).W) = gP σ (fun _ => g q) ((z, e) : (AP σ).Obj)
  let PH' : HObj × H 0 → HObj := LocalBundle.proj (E := H) (U := (univ : Set (H 0))) (F := H)
  let Φ := prodFiberCLE (proj n n) PH' ((z, e) : (Fin n → ℝ) × HObj)
  let b : Fin n → (Prod.map (proj n n) PH' ⁻¹' {((z, e) : (Fin n → ℝ) × HObj)}) := fun i =>
    ⟨basisP σ i ((z, e) : (AP σ).Obj), rfl⟩
  have hsum : Φ w = ∑ i, g q i • Φ (b i) := by
    have hw' : w = ∑ i, g q i • b i := rfl
    rw [hw', map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smul Φ _ _
  have h1 : (((Φ w).1 : proj n n ⁻¹' {z}) : (Fin n → ℝ) × (Fin n → ℝ)) = (z, g q) := by
    have := congrArg Prod.fst hsum
    rw [Prod.fst_sum] at this
    refine (congrArg Subtype.val this).trans ?_
    have h := OrbifoldSquare.pullbackSlice_famSection (n := n) (k := n) (m := m) g q
    exact congrFun h z
  have h2 : (((Φ w).2 : PH' ⁻¹' {e}) : HObj × H 0) = (e, (0 : H 0)) := by
    have := congrArg Prod.snd hsum
    rw [Prod.snd_sum] at this
    refine (congrArg Subtype.val this).trans ?_
    have h0' : (⟨(e, (0 : H 0)), rfl⟩ : PH' ⁻¹' {e}) = 0 := by
      apply (LocalBundle.fibEquiv (F := H) e).injective
      exact ((LocalBundle.fibEquiv (F := H) e).linearEquiv ℝ).map_zero.symm
    have hs : (∑ i : Fin n, (g q i • (Φ (b i)).2)) = 0 :=
      Finset.sum_eq_zero fun i _ => by
        have hb : (Φ (b i)).2 = (⟨(e, (0 : H 0)), rfl⟩ : PH' ⁻¹' {e}) := rfl
        rw [hb, h0', smul_zero]
    refine (congrArg Subtype.val hs).trans ?_
    refine Prod.ext rfl ?_
    exact ((LocalBundle.fibEquiv (F := H) e).linearEquiv ℝ).map_zero
  exact Prod.ext h1 h2

/-- **`famP g` is an sc⁺-section** for a `C^∞` map `g`. -/
theorem isScPlusSection_famP {g : (Fin m → ℝ) → (Fin n → ℝ)} (hg : ContDiff ℝ ∞ g) :
    haveI := paracompactSpace_rn_prod (AP σ).X.PObj
    haveI := paracompactSpace_rn_pullback (AP σ).B
    ((AP σ).B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m)
      (AP σ).X.PObj)).IsScPlusSection (famP σ g) := by
  have := paracompactSpace_rn_prod (AP σ).X.PObj
  have := paracompactSpace_rn_pullback (AP σ).B
  exact (StrongBundle.isScPlusSection_paramComb (B := (AP σ).B)
    (fun i : Fin n => isScPlusSection_basisP σ i)).reparamSmooth hg

end Family

/-! ### Positivity at the identity along paths -/

/-- **`o` is positive at the identity at `(y, 0)`**: at `(f + idSecP φ y)'(y, 0)`. -/
def IsPosIdP (hφ : ContDiff ℝ ∞ φ) (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    {hf : (AP σ).B.IsScFredholmSection (fP σ φ)}
    (o : ∀ a (hs : a ∈ (AP σ).X.PObj.smoothSet), Orx (B := (AP σ).B) (fP σ φ) hf a hs)
    (y : Fin n → ℝ) : Prop :=
  IsPosOr hf (mem_smoothSet_mk_h0P (σ := σ) y)
    (o ((y, h0) : (AP σ).Obj) (mem_smoothSet_mk_h0P (σ := σ) y)) (idSecP σ φ y)
    (isScPlusSection_idSecP σ hφ y) (isZeroAt_idSecP σ hφ heq y)

section Path

variable [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × (AP σ).Obj)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace (AP σ).P
    (Prod.snd : (Fin n → ℝ) × (AP σ).Obj → (AP σ).Obj))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × (AP σ).Obj))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace
    (pullbackProj (AP σ).P (Prod.snd : (Fin n → ℝ) × (AP σ).Obj → (AP σ).Obj))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × (AP σ).Obj) → (Fin n → ℝ) × (AP σ).Obj))]

/-- **For a continuous orientation, positivity at the identity at `(0, 0)` and at `(y, 0)`
agree**: along `γ(t) = (t • y, 0)` the sc⁺-section
`(t, (x, e)) ↦ ((x, (x − t • y) − φ x), (e, 0))` of the pull-back bundle has `(f + S_t)(γ t) = 0`
and `(f + S_t)'(γ t) = id ⊕ id` (`isPosOr_iff_of_path`). -/
theorem isPosIdP_iff (hφ : ContDiff ℝ ∞ φ) (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    {o : ∀ a (hs : a ∈ (AP σ).X.PObj.smoothSet),
      Orx (B := (AP σ).B) (fP σ φ)
        (isScFredholmSectionTame_fP σ hφ heq).toIsScFredholmSection a hs}
    (ho : IsContOrOn (orLocalTransport (isTame_AP σ) (admitsBumpFunctions_AP σ)
      (isScFredholmSectionTame_fP σ hφ heq) (hasScPlusSectionsThrough_AP σ)) univ o)
    (y : Fin n → ℝ) : IsPosIdP σ hφ heq o 0 ↔ IsPosIdP σ hφ heq o y := by
  have hft := isScFredholmSectionTame_fP σ hφ heq
  let γ₁ : (Fin 1 → ℝ) → (Fin n → ℝ) := fun q => q 0 • y
  have hγd : ContDiff ℝ ∞ γ₁ := (contDiff_apply ℝ ℝ (0 : Fin 1)).smul contDiff_const
  let γ : (Fin 1 → ℝ) → (AP σ).Obj := fun q => ((γ₁ q, h0) : (Fin n → ℝ) × HObj)
  have hγs : (rnPolyfold 1).IsScSmoothMap (AP σ).X.PObj γ :=
    isScSmoothMap_rn_AP σ hγd (e := fun _ => (0 : H 0))
      (isScSmooth_const_of_mem_smooth (isScDomain_univ _) H.smooth.zero_mem)
  have hP : (AP σ).B.IsScPlusSection (gP σ fun u => u - φ u) :=
    isScPlusSection_gP σ (contDiff_id.sub hφ)
  have hL := isScPlusSection_paramLift hP
  have hg : ContDiff ℝ ∞ fun q : Fin 1 → ℝ => -γ₁ q := hγd.neg
  have hF := isScPlusSection_famP σ hg
  have hS := hL.add hF
  set S := sectionAdd (pullbackProj (AP σ).P Prod.snd)
    (paramLift (n := 1) (gP σ fun u => u - φ u) hP.1)
    (famP σ fun q : Fin 1 → ℝ => -γ₁ q) with hSdef
  have hslice : ∀ q, pullbackSlice S q = idSecP σ φ (γ₁ q) := fun q => by
    have hpl : pullbackSlice (paramLift (n := 1) (gP σ fun u => u - φ u) hP.1) q =
        gP σ fun u => u - φ u := rfl
    refine (pullbackSlice_sectionAdd hL.1 hF.1 q).trans ?_
    refine (congrArg₂ (sectionAdd (AP σ).P) hpl (pullbackSlice_famP σ _ q)).trans ?_
    refine (sectionAdd_gP σ (contDiff_id.sub hφ) contDiff_const).trans ?_
    congr 1
    funext u
    change (u - φ u) + -γ₁ q = (u - γ₁ q) - φ u
    abel
  have hzq : ∀ q, IsZeroAt (AP σ).P
      (sectionAdd (AP σ).P (fP σ φ) (pullbackSlice S q)) (γ q) := fun q => by
    rw [hslice q]
    exact isZeroAt_idSecP σ hφ heq (γ₁ q)
  have hz : ∀ q : Fin 1 → ℝ, IsZeroAt (pullbackProj (AP σ).P Prod.snd)
      (sectionAdd (pullbackProj (AP σ).P Prod.snd)
        (paramLift (fP σ φ) hft.isScSmooth.1) S) (q, γ q) := fun q => by
    refine (isZeroAt_pullback_iff_pullbackSlice (P := (AP σ).P)
      ((isSection_pullbackLift _).sectionAdd hS.1) q (γ q)).2 ?_
    rw [pullbackSlice_sectionAdd_paramLift hft.isScSmooth.1 hS.1 q]
    exact hzq q
  have key := isPosOr_iff_of_path (isTame_AP σ) (admitsBumpFunctions_AP σ) hft
    (hasScPlusSectionsThrough_AP σ) ho hγs (fun _ _ => mem_univ _) hS (Eventually.of_forall hz)
    (fun q _ p hz0 => bijective_stabT_idSecP σ hφ heq (hslice q) _ hz0 p)
    (mem_smoothSet_mk_h0P (σ := σ) _) (mem_smoothSet_mk_h0P (σ := σ) _) (hzq _) (hzq _)
  have e0 : γ₁ (pt1 0) = 0 := zero_smul ℝ y
  have e1 : γ₁ (pt1 1) = y := one_smul ℝ y
  have e0' : γ (pt1 0) = (((0 : Fin n → ℝ), h0) : (AP σ).Obj) :=
    congrArg (fun a => ((a, h0) : (AP σ).Obj)) e0
  have e1' : γ (pt1 1) = ((y, h0) : (AP σ).Obj) := congrArg (fun a => ((a, h0) : (AP σ).Obj)) e1
  have c0 := isPosOr_congr_pt hft.toIsScFredholmSection o e0' (mem_smoothSet_mk_h0P (σ := σ) _)
    (mem_smoothSet_mk_h0P (σ := σ) _) ((hslice (pt1 0)).trans (by rw [e0]))
    (hS.pullbackSlice _) (isScPlusSection_idSecP σ hφ 0) (hzq _) (isZeroAt_idSecP σ hφ heq 0)
  have c1 := isPosOr_congr_pt hft.toIsScFredholmSection o e1' (mem_smoothSet_mk_h0P (σ := σ) _)
    (mem_smoothSet_mk_h0P (σ := σ) _) ((hslice (pt1 1)).trans (by rw [e1]))
    (hS.pullbackSlice _) (isScPlusSection_idSecP σ hφ y) (hzq _) (isZeroAt_idSecP σ hφ heq y)
  exact c0.symm.trans (key.trans c1)

end Path

/-! ### The orientation positive at the identity -/

/-- **`f` has a continuous orientation over `ℝⁿ × H` positive at the identity at `(0, 0)`**: a
continuous orientation exists (Theorem 6.6.17; paths in `ℝⁿ × H` with the same end points are
homotopic), and of it and the opposite orientation exactly one is positive at the isomorphism
`(f + idSecP φ 0)'(0, 0)`. -/
theorem exists_isContOrOn_isPosIdP (hφ : ContDiff ℝ ∞ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x)) :
    haveI := paracompactSpace_rn_prod (AP σ).X.PObj
    haveI := paracompactSpace_rn_pullback (AP σ).B
    haveI := paracompactSpace_rn_rn_prod (AP σ).X.PObj
    haveI := paracompactSpace_rn_rn_pullback (AP σ).B
    ∃ o : ∀ a (hs : a ∈ (AP σ).X.PObj.smoothSet),
        Orx (B := (AP σ).B) (fP σ φ)
          (isScFredholmSectionTame_fP σ hφ heq).toIsScFredholmSection a hs,
      IsContOrOn (orLocalTransport (isTame_AP σ) (admitsBumpFunctions_AP σ)
        (isScFredholmSectionTame_fP σ hφ heq) (hasScPlusSectionsThrough_AP σ)) univ o ∧
      IsPosIdP σ hφ heq o 0 := by
  have := paracompactSpace_rn_prod (AP σ).X.PObj
  have := paracompactSpace_rn_pullback (AP σ).B
  have := paracompactSpace_rn_rn_prod (AP σ).X.PObj
  have := paracompactSpace_rn_rn_pullback (AP σ).B
  have hft := isScFredholmSectionTame_fP σ hφ heq
  have hf := hft.toIsScFredholmSection
  have hsec := hasScPlusSectionsThrough_AP σ
  obtain ⟨o, -, hc⟩ := exists_continuous_orSec_of_hom_eq (isTame_AP σ)
    (admitsBumpFunctions_AP σ) hft hsec (fun {_ _} a b => PathCat.hom_eq_AP σ a b)
  have ho := isContOrOn_univ_of_continuous_orSec
    (fun _ hy => exists_two_orx _ hy hsec) (AP σ).X.PObj.hasConnectedSmoothNbhds hc
  have h2 : IsTwoPointed (B := (AP σ).B) (fP σ φ) hf := fun x hs =>
    exists_two_orx hf hs hsec
  by_cases hp : IsPosIdP σ hφ heq o 0
  · exact ⟨o, ho, hp⟩
  · refine ⟨fun y hy => orOther (o y hy), ho.other _ h2, ?_⟩
    have hs := mem_smoothSet_mk_h0P (σ := σ) (0 : Fin n → ℝ)
    have hall : ∀ a : Orx (B := (AP σ).B) (fP σ φ) hf (((0 : Fin n → ℝ), h0) : (AP σ).Obj) hs,
        a = o _ hs ∨ a = orOther (o _ hs) := fun a => by
      by_cases h : a = o _ hs
      · exact Or.inl h
      · exact Or.inr ((eq_orOther_iff h2 _ _).2 h)
    have hb := bijective_stabT_idSecP σ hφ heq rfl (isScPlusSection_idSecP σ hφ 0)
      (isZeroAt_idSecP σ hφ heq 0) (orPt (AP σ).B (((0 : Fin n → ℝ), h0) : (AP σ).Obj) hs)
    rcases ChartPoint.isPos_or_isPos (ChartPoint.stabT_mem_linSet _ hf
      (isScPlusSection_idSecP σ hφ 0) (isZeroAt_idSecP σ hφ heq 0) hs) hb hall with h | h
    · exact absurd h hp
    · exact h

/-- **The canonical orientation of `|(x, e)| ↦ |((x, φ x), (e, e))|`**: the continuous orientation
positive at the identity `(f + idSecP φ 0)'(0, 0)`. -/
def prOrientation (hφ : ContDiff ℝ ∞ φ) (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x)) :
    ∀ a (hs : a ∈ (AP σ).X.PObj.smoothSet),
      Orx (B := (AP σ).B) (fP σ φ)
        (isScFredholmSectionTame_fP σ hφ heq).toIsScFredholmSection a hs :=
  (exists_isContOrOn_isPosIdP σ hφ heq).choose

theorem isContOrOn_prOrientation (hφ : ContDiff ℝ ∞ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x)) :
    haveI := paracompactSpace_rn_prod (AP σ).X.PObj
    haveI := paracompactSpace_rn_pullback (AP σ).B
    haveI := paracompactSpace_rn_rn_prod (AP σ).X.PObj
    haveI := paracompactSpace_rn_rn_pullback (AP σ).B
    IsContOrOn (orLocalTransport (isTame_AP σ) (admitsBumpFunctions_AP σ)
      (isScFredholmSectionTame_fP σ hφ heq) (hasScPlusSectionsThrough_AP σ)) univ
      (prOrientation σ hφ heq) :=
  (exists_isContOrOn_isPosIdP σ hφ heq).choose_spec.1

/-- **`prOrientation` is positive at the identity at every point `(y, 0)`.** -/
theorem isPosIdP_prOrientation (hφ : ContDiff ℝ ∞ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x)) (y : Fin n → ℝ) :
    IsPosIdP σ hφ heq (prOrientation σ hφ heq) y := by
  have := paracompactSpace_rn_prod (AP σ).X.PObj
  have := paracompactSpace_rn_pullback (AP σ).B
  have := paracompactSpace_rn_rn_prod (AP σ).X.PObj
  have := paracompactSpace_rn_rn_pullback (AP σ).B
  exact (isPosIdP_iff σ hφ heq (isContOrOn_prOrientation σ hφ heq) y).1
    (exists_isContOrOn_isPosIdP σ hφ heq).choose_spec.2

/-- **The sign of `(f + S)'(y, 0)` for the canonical orientation is the sign of the
determinant**: for the section `S(x, e) = ((x, ψ x), (e, 0))` of a `C^∞` map `ψ` with
`(f + S)(y, 0) = 0` and `D(φ + ψ)(y)` bijective, `prOrientation` is positive at
`(f + S)'(y, 0) = D(φ + ψ)(y) ⊕ id` iff `det D(φ + ψ)(y) > 0`. -/
theorem isPosOr_prOrientation_iff (hφ : ContDiff ℝ ∞ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x)) (hf : (AP σ).B.IsScFredholmSection (fP σ φ))
    {y : Fin n → ℝ} (hs : ((y, h0) : (AP σ).Obj) ∈ (AP σ).X.PObj.smoothSet)
    {ψ : (Fin n → ℝ) → (Fin n → ℝ)} (hψ : ContDiff ℝ ∞ ψ) (hS : (AP σ).B.IsScPlusSection (gP σ ψ))
    (hz : IsZeroAt (AP σ).P (sectionAdd (AP σ).P (fP σ φ) (gP σ ψ)) ((y, h0) : (AP σ).Obj))
    (hb : Bijective (fderiv ℝ (φ + ψ) y)) :
    IsPosOr hf hs (prOrientation σ hφ heq ((y, h0) : (AP σ).Obj) hs) (gP σ ψ) hS hz ↔
      0 < LinearMap.det (fderiv ℝ (φ + ψ) y : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :=
  isPosOr_iff_det_of_isPosIdP σ hφ heq hf hs _ (isPosIdP_prOrientation σ hφ heq y) hψ hS hz hb

/-! ### Invariance under the morphisms -/

omit [Fintype G] [FaithfulSMul G (Fin n → ℝ)] in
/-- `det σ(g) · det ρ(g⁻¹) > 0` when `det ρ(g) · det σ(g) > 0`. -/
theorem det_sigma_mul_rho_inv_pos
    (hdet : ∀ g : G, 0 < LinearMap.det (rhoL (n := n) g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) *
      LinearMap.det (σ g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) (g : G) :
    0 < LinearMap.det (σ g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) *
      LinearMap.det (rhoL (n := n) g⁻¹ : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) := by
  have h1 := det_rhoL_mul_inv (n := n) g
  have ha' : LinearMap.det (rhoL (n := n) g⁻¹ : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ≠ 0 :=
    right_ne_zero_of_mul_eq_one h1
  have e : LinearMap.det (σ g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) *
      LinearMap.det (rhoL (n := n) g⁻¹ : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) =
      (LinearMap.det (rhoL (n := n) g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) *
        LinearMap.det (σ g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) *
      (LinearMap.det (rhoL (n := n) g⁻¹ : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) *
        LinearMap.det (rhoL (n := n) g⁻¹ : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) := by
    linear_combination (-(LinearMap.det (σ g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) *
      LinearMap.det (rhoL (n := n) g⁻¹ : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))) * h1
  rw [e]
  exact mul_pos (hdet g) (mul_self_pos.2 ha')

omit [Fintype G] [FaithfulSMul G (Fin n → ℝ)] in
theorem sigma_apply_sigma (a b : G) (y : Fin n → ℝ) : σ a (σ b y) = σ (a * b) y := by
  rw [map_mul]
  rfl

omit [Fintype G] [FaithfulSMul G (Fin n → ℝ)] in
/-- `σ(g) ∘ ρ(g⁻¹)` is bijective. -/
theorem bijective_sigma_comp_rho_inv (g : G) :
    Bijective ((σ g).comp (rhoL (n := n) g⁻¹)) := by
  refine (bijective_iff_has_inverse).2 ⟨(rhoL (n := n) g).comp (σ g⁻¹), fun x => ?_, fun x => ?_⟩
  · change g • (σ g⁻¹ (σ g (g⁻¹ • x))) = x
    rw [sigma_apply_sigma, inv_mul_cancel, map_one]
    exact smul_inv_smul g x
  · change σ g (g⁻¹ • (g • σ g⁻¹ x)) = x
    rw [inv_smul_smul, sigma_apply_sigma, mul_inv_cancel, map_one]
    rfl

/-- A block operator read in the product chart. -/
theorem orKEquivP_blk (y : Fin n → ℝ) (hs : ((y, h0) : (AP σ).Obj) ∈ (AP σ).X.PObj.smoothSet)
    (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (v : ↥(orPt (AP σ).B ((y, h0) : (AP σ).Obj) hs).T) :
    orKEquivP σ y hs (blk (orTEquivP σ y hs) (orKEquivP σ y hs) A v) =
      (A (orTEquivP σ y hs v).1, (orTEquivP σ y hs v).2) := by
  rw [blk_apply, ContinuousLinearEquiv.apply_symm_apply]

/-- The inverse of `T((g, 0), 0)` read in the product chart: `(v, w) ↦ (g⁻¹ • v, w)`. -/
theorem morTx_symm_stdP (g : G)
    (hgx : (AP σ).X.tgt (((g, (0 : Fin n → ℝ)), h0) : (AP σ).Mor) =
      (((0 : Fin n → ℝ), h0) : (AP σ).Obj))
    (hs : (((0 : Fin n → ℝ), h0) : (AP σ).Obj) ∈ (AP σ).X.PObj.smoothSet)
    (w : ↥(orPt (AP σ).B (((0 : Fin n → ℝ), h0) : (AP σ).Obj) hs).T) :
    orTEquivP σ 0 hs (((AP σ).E.morTx (((g, (0 : Fin n → ℝ)), h0) : (AP σ).Mor)
      (x := (((0 : Fin n → ℝ), h0) : (AP σ).Obj)) rfl hgx hs hs).symm w) =
      (g⁻¹ • (orTEquivP σ 0 hs w).1, (orTEquivP σ 0 hs w).2) := by
  have e := morTx_stdP σ g (x := 0) (x' := 0) rfl hgx hs hs
    (((AP σ).E.morTx (((g, (0 : Fin n → ℝ)), h0) : (AP σ).Mor)
      (x := (((0 : Fin n → ℝ), h0) : (AP σ).Obj)) rfl hgx hs hs).symm w)
  rw [ContinuousLinearEquiv.apply_symm_apply] at e
  rw [e, inv_smul_smul]

/-- **`((g, 0), 0)_*` of a block operator `A ⊕ id` is `σ(g) A ρ(g)⁻¹ ⊕ id`.** -/
theorem linMor_blkP (g : G)
    (hgx : (AP σ).X.tgt (((g, (0 : Fin n → ℝ)), h0) : (AP σ).Mor) =
      (((0 : Fin n → ℝ), h0) : (AP σ).Obj))
    (hs : (((0 : Fin n → ℝ), h0) : (AP σ).Obj) ∈ (AP σ).X.PObj.smoothSet)
    (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    (AP σ).E.linMor (((g, (0 : Fin n → ℝ)), h0) : (AP σ).Mor)
      (x := (((0 : Fin n → ℝ), h0) : (AP σ).Obj)) rfl hgx hs hs
      (blk (orTEquivP σ 0 hs) (orKEquivP σ 0 hs) A) =
      blk (orTEquivP σ 0 hs) (orKEquivP σ 0 hs) ((σ g).comp (A.comp (rhoL g⁻¹))) := by
  ext1 w
  apply (orKEquivP σ 0 hs).injective
  have e1 := morKx_stdP σ g (x := 0) (x' := 0) rfl hgx hs hs
    (blk (orTEquivP σ 0 hs) (orKEquivP σ 0 hs) A
      (((AP σ).E.morTx (((g, (0 : Fin n → ℝ)), h0) : (AP σ).Mor)
        (x := (((0 : Fin n → ℝ), h0) : (AP σ).Obj)) rfl hgx hs hs).symm w))
  have e2 := morTx_symm_stdP σ g hgx hs w
  refine e1.trans ?_
  rw [orKEquivP_blk, orKEquivP_blk, e2]
  rfl

/-- **An isotropy morphism `((g, 0), 0)` preserves an orientation positive at the identity at
`(0, 0)`**, when `det ρ(g) · det σ(g) > 0`: `((g, 0), 0)_*` is the conjugation by `T((g, 0), 0)`
and `μ(((g, 0), 0), ·)` (`orMor_apply`), which carries the unit of `det L` to the unit of
`det L'`, `L' = μ(((g, 0), 0), ·) ∘ L ∘ T((g, 0), 0)⁻¹`; read in `ℝⁿ × H`,
`L = id ⊕ id` and `L' = σ(g) ρ(g)⁻¹ ⊕ id`, so `o` is positive at `L'` as well
(`isPos_iff_blk_of_isPos`). -/
theorem orMor_zero_eqP (hφ : ContDiff ℝ ∞ φ) (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    (hdet : ∀ g : G, 0 < LinearMap.det (rhoL (n := n) g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) *
      LinearMap.det (σ g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
    (g : G)
    (hgx : (AP σ).X.tgt (((g, (0 : Fin n → ℝ)), h0) : (AP σ).Mor) =
      (((0 : Fin n → ℝ), h0) : (AP σ).Obj))
    (hs : (((0 : Fin n → ℝ), h0) : (AP σ).Obj) ∈ (AP σ).X.PObj.smoothSet)
    (o0 : Orx (B := (AP σ).B) (fP σ φ) (isScFredholmSectionFunctor_fP hφ heq).2
      (((0 : Fin n → ℝ), h0) : (AP σ).Obj) hs)
    (hpos : IsPosOr (isScFredholmSectionFunctor_fP hφ heq).2 hs o0 (idSecP σ φ 0)
      (isScPlusSection_idSecP σ hφ 0) (isZeroAt_idSecP σ hφ heq 0)) :
    (AP σ).E.orMor (isScFredholmSectionFunctor_fP hφ heq)
      (hasScPlusSectionsThrough_AP σ) (((g, (0 : Fin n → ℝ)), h0) : (AP σ).Mor)
      (x := (((0 : Fin n → ℝ), h0) : (AP σ).Obj)) rfl hgx hs hs o0 = o0 := by
  have hF := isScFredholmSectionFunctor_fP (σ := σ) hφ heq
  have hsec := hasScPlusSectionsThrough_AP σ
  set p := orPt (AP σ).B (((0 : Fin n → ℝ), h0) : (AP σ).Obj) hs with hp
  set L := p.stabT hF.2 (isScPlusSection_idSecP σ hφ 0) (isZeroAt_idSecP σ hφ heq 0) with hLdef
  have hL : L ∈ p.linSet (B := (AP σ).B) (fP σ φ) := p.stabT_mem_linSet hF.2 _ _ hs
  have hb : Bijective L := ChartPoint.IsPos.bijective hpos
  set Tm := (AP σ).E.morTx (((g, (0 : Fin n → ℝ)), h0) : (AP σ).Mor)
    (x := (((0 : Fin n → ℝ), h0) : (AP σ).Obj)) rfl hgx hs hs with hTm
  set Km := (AP σ).E.morKx (((g, (0 : Fin n → ℝ)), h0) : (AP σ).Mor)
    (x := (((0 : Fin n → ℝ), h0) : (AP σ).Obj)) rfl hgx hs hs with hKm
  set L' := (AP σ).E.linMor (((g, (0 : Fin n → ℝ)), h0) : (AP σ).Mor)
    (x := (((0 : Fin n → ℝ), h0) : (AP σ).Obj)) rfl hgx hs hs L with hL'def
  have hL' : L' ∈ p.linSet (B := (AP σ).B) (fP σ φ) :=
    (AP σ).E.lemma_12_5_1_one hF hsec _ (x := (((0 : Fin n → ℝ), h0) : (AP σ).Obj)) rfl hgx hs
      hs hL
  have h : ∀ v, L' (Tm v) = Km (L v) := fun v =>
    congrArg (fun w => Km (L w)) (Tm.symm_apply_apply v)
  have hb' : Bijective L' := by
    have e : ⇑L' = ⇑Km ∘ ⇑L ∘ ⇑Tm.symm := by
      funext w
      exact EpStrongBundle.linMor_apply _ _ _ _ _ _ _ _
    rw [e]
    exact Km.bijective.comp (hb.comp Tm.symm.bijective)
  have hu : o0 ⟨L, hL⟩ = unitRay' hb := (isPos_iff_eq_unitRay' p o0 hL hb).1 hpos
  -- the readings of `L` and `L'`
  have hLblk : L = blk (orTEquivP σ 0 hs) (orKEquivP σ 0 hs) (fderiv ℝ (φ + idFun φ 0) 0) :=
    stabT_eq_blk σ hφ (contDiff_idFun hφ 0) hF.2 _ _ hs
  have hL'blk : L' = blk (orTEquivP σ 0 hs) (orKEquivP σ 0 hs)
      ((σ g).comp ((ContinuousLinearMap.id ℝ (Fin n → ℝ)).comp (rhoL g⁻¹))) := by
    rw [hL'def, hLblk, fderiv_add_idFun]
    exact linMor_blkP σ g hgx hs _
  have hpos' : p.IsPos o0 L' := by
    have h₀ : p.IsPos o0 (blk (orTEquivP σ 0 hs) (orKEquivP σ 0 hs)
        (fderiv ℝ (φ + idFun φ 0) 0)) := by
      rw [← hLblk]
      exact hpos
    rw [hL'blk, ContinuousLinearMap.id_comp]
    refine (isPos_iff_blk_of_isPos p o0 _ _ (blk_mem_linSet hφ heq 0 hs)
      (bijective_sigma_comp_rho_inv σ g) h₀).2 ?_
    rw [fderiv_add_idFun, ContinuousLinearMap.coe_id, LinearMap.det_id, one_mul,
      ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp]
    exact det_sigma_mul_rho_inv_pos σ hdet g
  have h2 : o0 ⟨L', hL'⟩ = unitRay' hb' := (isPos_iff_eq_unitRay' p o0 hL' hb').1 hpos'
  have : ContractibleSpace (p.linSet (B := (AP σ).B) (fP σ φ)) :=
    (p.convex_linSet hF.2).contractibleSpace ⟨_, hL⟩
  have hc := LineOrientation.conj_apply (hC := p.isFredholm_of_mem_linSet hF.2)
    (hC' := p.isFredholm_of_mem_linSet hF.2) Tm Km
    ((AP σ).E.morTx_mem hF hsec _ (x := (((0 : Fin n → ℝ), h0) : (AP σ).Obj)) rfl hgx hs hs)
    o0 hL hL' h
  refine ((AP σ).E.orMor_apply hF hsec (((g, (0 : Fin n → ℝ)), h0) : (AP σ).Mor)
    (x := (((0 : Fin n → ℝ), h0) : (AP σ).Obj)) rfl hgx hs hs o0).trans ?_
  refine LineOrientation.eq_of_apply_eq ⟨L', hL'⟩ (hc.trans ?_)
  have hm := ray_map_conjDet_unitRay' _ _ h hb hb'
  exact (congrArg (Module.Ray.map (conjDet _ _ h)) hu).trans (hm.trans h2.symm)

section Invariance

variable [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × (AP σ).Obj)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace (AP σ).P
    (Prod.snd : (Fin n → ℝ) × (AP σ).Obj → (AP σ).Obj))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × (AP σ).Obj))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace
    (pullbackProj (AP σ).P (Prod.snd : (Fin n → ℝ) × (AP σ).Obj → (AP σ).Obj))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × (AP σ).Obj) → (Fin n → ℝ) × (AP σ).Obj))]

/-- **`prOrientation` is invariant under the morphisms** (Definition 12.5.4), when
`det ρ(g) · det σ(g) > 0` for all `g`: at a morphism `((g, q), e)` with `e` smooth the invariance
is constant along `t ↦ ((g, t q), t e)` (`isOrInvariantAt_iff_of_continuous`, from
Theorem 12.5.3) and holds at `t = 0` by `orMor_zero_eqP`; at the other morphisms there is nothing
to show. -/
theorem isOrInvariant_prOrientation (hφ : ContDiff ℝ ∞ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    (hdet : ∀ g : G, 0 < LinearMap.det (rhoL (n := n) g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) *
      LinearMap.det (σ g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) :
    (AP σ).E.IsOrInvariant (isScFredholmSectionFunctor_fP hφ heq)
      (hasScPlusSectionsThrough_AP σ) (prOrientation σ hφ heq) := by
  have hF := isScFredholmSectionFunctor_fP (σ := σ) hφ heq
  have hsec := hasScPlusSectionsThrough_AP σ
  refine ((AP σ).E.isOrInvariant_iff_forall_isOrInvariantAt hF hsec).2 fun m => ?_
  obtain ⟨⟨g, q⟩, e⟩ : (G × (Fin n → ℝ)) × HObj := m
  by_cases he : ((e : HObj) : H 0) ∈ H.smooth
  · let γ : ℝ → (AP σ).Mor := fun t =>
      (((g, t • q), hpt (t • (e : H 0))) : (G × (Fin n → ℝ)) × HObj)
    have hc : Continuous γ :=
      (continuous_const.prodMk (continuous_id.smul continuous_const)).prodMk
        ((continuous_id.smul continuous_const).subtype_mk fun _ => mem_univ _)
    have hs1 : ∀ t, (AP σ).X.src (γ t) ∈ (AP σ).X.PObj.smoothSet := fun t =>
      (mem_smoothSet_AP_iff (σ := σ)
        (x := ((t • q, hpt (t • (e : H 0))) : (Fin n → ℝ) × HObj))).2
        (H.smooth.smul_mem t he)
    have hs2 : ∀ t, (AP σ).X.tgt (γ t) ∈ (AP σ).X.PObj.smoothSet := fun t =>
      (mem_smoothSet_AP_iff (σ := σ)
        (x := ((g • t • q, hpt (t • (e : H 0))) : (Fin n → ℝ) × HObj))).2
        (H.smooth.smul_mem t he)
    have h := (AP σ).E.isOrInvariantAt_iff_of_continuous hF hsec (isTame_AP σ)
      (admitsBumpFunctions_AP σ) (isScFredholmSectionTame_fP σ hφ heq)
      (isContOrOn_prOrientation σ hφ heq) hc hs1 hs2 1 0
    have e1 : γ 1 = (((g, q), e) : (G × (Fin n → ℝ)) × HObj) :=
      Prod.ext (Prod.ext rfl (one_smul ℝ q)) (Subtype.ext (one_smul ℝ _))
    have e0 : γ 0 = (((g, (0 : Fin n → ℝ)), h0) : (G × (Fin n → ℝ)) × HObj) :=
      Prod.ext (Prod.ext rfl (zero_smul ℝ q)) (Subtype.ext (zero_smul ℝ _))
    rw [e1, e0] at h
    refine h.2 ?_
    refine ((AP σ).E.isOrInvariantAt_iff' hF hsec).2 fun {x x'} hx hx' hs₁ hs₂ => ?_
    obtain rfl : (((0 : Fin n → ℝ), h0) : (AP σ).Obj) = x := hx
    have ht : (AP σ).X.tgt (((g, (0 : Fin n → ℝ)), h0) : (AP σ).Mor) =
        (((0 : Fin n → ℝ), h0) : (AP σ).Obj) := by
      change (((g • (0 : Fin n → ℝ)), h0) : (AP σ).Obj) = _
      rw [smul_zero]
    obtain rfl : (((0 : Fin n → ℝ), h0) : (AP σ).Obj) = x' := ht.symm.trans hx'
    exact orMor_zero_eqP σ hφ heq hdet g hx' hs₁ _ (isPosIdP_prOrientation σ hφ heq 0)
  · intro hs _
    exact absurd ((mem_smoothSet_AP_iff (σ := σ)
      (x := ((q, e) : (Fin n → ℝ) × HObj))).1 hs) he

end Invariance

/-- **`prOrientation` is an orientation in the sense of Definition 12.5.4**: continuous for
Part I's topology on `O_f` and invariant under the morphisms. -/
theorem definition_12_5_4_prOrientation (hφ : ContDiff ℝ ∞ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    (hdet : ∀ g : G, 0 < LinearMap.det (rhoL (n := n) g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) *
      LinearMap.det (σ g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) :
    haveI := paracompactSpace_rn_prod (AP σ).X.PObj
    haveI := paracompactSpace_rn_pullback (AP σ).B
    haveI := paracompactSpace_rn_rn_prod (AP σ).X.PObj
    haveI := paracompactSpace_rn_rn_pullback (AP σ).B
    (AP σ).E.definition_12_5_4 (isScFredholmSectionFunctor_fP hφ heq)
      (hasScPlusSectionsThrough_AP σ)
      (orTopology (orLocalTransport (isTame_AP σ) (admitsBumpFunctions_AP σ)
        (isScFredholmSectionTame_fP σ hφ heq) (hasScPlusSectionsThrough_AP σ)))
      (prOrientation σ hφ heq) := by
  have := paracompactSpace_rn_prod (AP σ).X.PObj
  have := paracompactSpace_rn_pullback (AP σ).B
  have := paracompactSpace_rn_rn_prod (AP σ).X.PObj
  have := paracompactSpace_rn_rn_pullback (AP σ).B
  refine ⟨?_, isOrInvariant_prOrientation σ hφ heq hdet⟩
  let := orTopology (orLocalTransport (isTame_AP σ) (admitsBumpFunctions_AP σ)
    (isScFredholmSectionTame_fP σ hφ heq) (hasScPlusSectionsThrough_AP σ))
  have h := continuousOn_orSec (isContOrOn_prOrientation σ hφ heq)
  rw [preimage_univ] at h
  exact continuousOn_univ.1 h

/-- Part I's topology on `O_f` is a topology with the properties of Theorem 12.5.3. -/
theorem isOrientationTopology_fP (hφ : ContDiff ℝ ∞ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x)) :
    haveI := paracompactSpace_rn_prod (AP σ).X.PObj
    haveI := paracompactSpace_rn_pullback (AP σ).B
    haveI := paracompactSpace_rn_rn_prod (AP σ).X.PObj
    haveI := paracompactSpace_rn_rn_pullback (AP σ).B
    IsOrientationTopology (B := (AP σ).B) (fP σ φ)
      (isScFredholmSectionTame_fP σ hφ heq).toIsScFredholmSection
      (orTopology (orLocalTransport (isTame_AP σ) (admitsBumpFunctions_AP σ)
        (isScFredholmSectionTame_fP σ hφ heq) (hasScPlusSectionsThrough_AP σ))) := by
  have := paracompactSpace_rn_prod (AP σ).X.PObj
  have := paracompactSpace_rn_pullback (AP σ).B
  have := paracompactSpace_rn_rn_prod (AP σ).X.PObj
  have := paracompactSpace_rn_rn_pullback (AP σ).B
  obtain ⟨t₀, ht₀⟩ := (theorem_6_6_17 (isTame_AP σ) (admitsBumpFunctions_AP σ)
    (isScFredholmSectionTame_fP σ hφ heq)).exists
  exact eq_orTopology_of (isTame_AP σ) (admitsBumpFunctions_AP σ)
    (isScFredholmSectionTame_fP σ hφ heq) (hasScPlusSectionsThrough_AP σ) ht₀.isLocalHomeomorph
    ht₀.propagation ▸ ht₀

/-- **The canonical orientation of the sc-Fredholm section `|(x, e)| ↦ |((x, φ x), (e, e))|` of
`|(ℝⁿ × ℝⁿ) × (H ◁ H)| → (ℝⁿ × H)/G`** (Definition 16.6.5, 2021 p. 739), for
`det ρ(g) · det σ(g) > 0`. -/
def prOrientationRep (hφ : ContDiff ℝ ∞ φ) (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    (hdet : ∀ g : G, 0 < LinearMap.det (rhoL (n := n) g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) *
      LinearMap.det (σ g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) :
    OrientationRep (prFredholmSection σ hφ heq) where
  a := prRep σ hφ heq
  ha := rfl
  hF := isScFredholmSectionFunctor_fP hφ heq
  hsec := hasScPlusSectionsThrough_AP σ
  t := haveI := paracompactSpace_rn_prod (AP σ).X.PObj
    haveI := paracompactSpace_rn_pullback (AP σ).B
    haveI := paracompactSpace_rn_rn_prod (AP σ).X.PObj
    haveI := paracompactSpace_rn_rn_pullback (AP σ).B
    orTopology (orLocalTransport (isTame_AP σ) (admitsBumpFunctions_AP σ)
      (isScFredholmSectionTame_fP σ hφ heq) (hasScPlusSectionsThrough_AP σ))
  isOrientationTopology := isOrientationTopology_fP σ hφ heq
  o := prOrientation σ hφ heq
  isOrientation := definition_12_5_4_prOrientation σ hφ heq hdet

/-- **The standing hypotheses of Theorem 16.6.6 (2021 p. 739) for index `0` hold in the model
of `prOrientationRep`**: tame germ data and Fredholm index `0`. -/
theorem canonicalGermInput_prOrientationRep (hφ : ContDiff ℝ ∞ φ)
    (heq : ∀ (g : G) x, φ (g • x) = σ g (φ x))
    (hdet : ∀ g : G, 0 < LinearMap.det (rhoL (n := n) g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) *
      LinearMap.det (σ g : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) :
    CanonicalGermInput (prOrientationRep σ hφ heq hdet) 0 :=
  ⟨isScFredholmSectionTame_fP σ hφ heq, fun x hx => by
    exact_mod_cast isIndexAt_fP σ hφ heq x hx⟩

end Polyfold.Examples.Classical.Product
