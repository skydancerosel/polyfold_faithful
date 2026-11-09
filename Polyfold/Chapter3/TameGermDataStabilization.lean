import Polyfold.Chapter3.TameGermData
import Polyfold.Chapter3.FredholmGermLinearizationSc

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Definition 3.1.4 (3)
(p. 91), Definition 3.1.11 (p. 96) and Definition 3.6.3, with Definition 2.5.2 (tame retractions,
p. 53) and Definition 2.6.1 (strong bundle retractions, p. 65) *(preprint 2014: Definitions 3.4,
3.11, 3.50, 2.34 and 2.47)*: **the normal-space condition of a filling can always be met in a tame
local model, by stabilization** (Findings, Chapter 3, items 199 and 350–359: the open question
whether an sc-Fredholm germ has germ data in a tame chart when the atlas is tame).

# Stabilizing a strong bundle retraction: the normal spaces are not an obstruction

## The text, paraphrased

(Definition 3.1.4 (3)) The linearization at `0` of `y ↦ [1 − ρ(r(y))]g(y)`, restricted to
`ker Dr(0)`, is a topological linear isomorphism onto `ker ρ(0)`.  (Definition 3.1.11) "There exists
a strong bundle chart" centred at `x₀` with a filling `g`, a local sc⁺-section `s` and `g − s`
conjugated to a basic germ.  (Definition 3.6.3) For a tame strong bundle the chart is required to
have a tame local bundle.  (Definition 2.5.2) An sc-smooth retraction `r : U → U`, `U` relatively
open in the partial quadrant `C`, is tame if `d_C(r(x)) = d_C(x)` on `U` and every tangent space
`T_xO`, `x ∈ O` smooth, has an sc-complement inside the minimal subspace `E_x`.

## What is formalized

Findings items 350–353 showed that whether a chart admits a filling of any section depends on the
chart, through the necessary condition `ker Dr(0) ≃ ker ρ(0)` (`IsFillingGerm.nonempty_kerEquiv`),
and asked whether this invariant could obstruct moving germ data into a tame chart.  It cannot:

* `Polyfold.Stabilize.stabilize`: for a strong bundle retraction `R(u, h) = (r(u), ρ(u)h)` on
  `U ◁ F` and sc-Banach spaces `M`, `N`, the **stabilized** map
  `R̂((u, m), (h, n)) = ((r(u), 0), (ρ(u)h, 0))` on `(U × M) ◁ (F ⊕ N)`, a strong bundle retraction
  (`isStrongBundleRetraction_stabilize`) with the same retract `O × {0} ≅ O` and the same fibres
  `K_u ⊕ 0 ≅ K_u`: the local strong bundle `K → O` is unchanged.
* Its base retraction is `r × 0` (`baseRetraction_stabilize`), the product of `r` with the constant
  retraction of `M` onto `0` (`zeroRetrOf`, tame: `zeroRetrOf_isTameWith`), and is **tame whenever
  `r` is** (`isTame_baseRetraction_stabilize`; `M` has no boundary, so the degeneracy index is
  unchanged and `A ⊕ M` complements `T_xO ⊕ 0` inside `E_x ⊕ M`).
* The normal spaces of the stabilized model are `ker Dr̂(0) = ker Dr(0) ⊕ M` and
  `ker ρ̂(0) = ker ρ(0) ⊕ N` (`scDeriv_r_stabilize`, `ρCLM_stabilize`).  Hence, with
  `M ≅ ker ρ(0)` and `N ≅ ker Dr(0)`, **the normal spaces of the stabilized model are isomorphic**
  (`nonempty_kerEquiv_stabilize`), and such `M`, `N` exist: `ker Dr(0)` and `ker ρ(0)` are
  sc-subspaces (the kernels of the sc-projections `Dr(0)`, `ρ(0)`; `isScSubspace_ker_scDeriv_r`,
  `isScSubspace_ker_ρCLM`), hence sc-Banach spaces (`exists_stabilization_kerEquiv`).

## What the text leaves implicit, and the choices made (the findings)

* **What this settles.**  The necessary condition of item 350 is never an obstruction to tame germ
  data: every compatible tame chart centred at `x₀` can be stabilized, without leaving the class of
  tame local models and without changing the local strong bundle `K → O`, to one whose normal
  spaces are isomorphic.  A counterexample to "germ data in some chart ⟹ germ data in some
  compatible tame chart" cannot be built from the normal-space invariant alone (as item 353
  already suspected for infinite-dimensional normal spaces; here it is excluded in general).
* **What stays open.**  The stabilized model is a local model only: that the stabilized chart is
  compatible with the atlas (the transitions `((u, 0), (h, 0)) ↦ T(u, h)` as sc-smooth retract maps)
  is the same infrastructure as the first part of item 199 (item 354) and is not formalized.  More
  importantly, conditions (1)–(2) of Definition 3.1.4 and the conjugation to a basic germ in the
  stabilized tame model are not addressed.  The natural filling in the stabilized model of a tame
  chart `c₀` with principal part `f̂`, `ĝ((u, m), ·) = (f̂(r(u)) + m, π(u − r(u)))` with
  `π = 1 − Dr(0)`, has (1) and (3), while (2) — zeros of `((1 − ρ(r(u)))m, π(u − r(u)))` near `0`
  lie in `O × 0` — asks for the injectivity of `(1 − ρ(u))|_{ker ρ(0)}` and of `π|_{(1 − r)(U)}`
  at points `u` close to `0` on level `0` only, where `u ↦ ρ(u)` and `r` are not norm-continuous:
  this is the level-`0` inverse function theorem that the sc-calculus does not provide, the same
  gap as in Findings item 263 for whole-chart fillings.  Whether every sc-Fredholm germ has tame
  germ data when the atlas is tame remains open (item 353 (iii)).
-/

open Set Filter Topology Function ContinuousLinearMap

noncomputable section

namespace Polyfold

namespace Stabilize

variable {E F M N : ScBanach}

/-! ### The zero operator and the constant retraction onto `0` (products of sc-operators:
`ScOperator.prodMap`, `Chapter3/BasicClassComposition.lean`) -/

/-- The zero sc-operator `M → M`. -/
def zeroOp (M : ScBanach) : ScOperator M M where
  lvl _ := 0
  incl_comm _ _ := by simp

/-- `univ` is relatively open in the partial quadrant `univ` of any sc-Banach space. -/
lemma relOpenUniv (M : ScBanach) : IsRelOpenInQuadrant M univ univ :=
  ⟨isPartialQuadrant_univ M, univ, isOpen_univ, (univ_inter _).symm⟩

/-- **The constant retraction** `m ↦ 0` of the sc-Banach space `M` (no boundary) onto `{0}`
(the general form of `TrivialBundle.zeroRetr`). -/
def zeroRetrOf (M : ScBanach) : ScRetraction M univ where
  U := univ
  toFun := (zeroOp M) 0
  relOpen := relOpenUniv M
  mapsTo := fun _ _ => mem_univ _
  isScSmooth := (zeroOp M).isScSmooth (isScDomain_univ M)
  idem := fun _ _ => by simp [zeroOp]

lemma zeroRetrOf_apply (M : ScBanach) (x : M 0) : zeroRetrOf M x = 0 := rfl

/-- `zeroRetrOf M` is tame (Definition 2.5.2, preprint 2.34): the degeneracy index of `M` is `0`
everywhere, and `T_0{0} = 0` has the sc-complement `M ⊆ E_0 = M`. -/
theorem zeroRetrOf_isTameWith (M : ScBanach) : (zeroRetrOf M).IsTameWith (TrivialBundle.univPres M) := by
  refine ⟨fun x _ => ?_, fun x _ _ => ⟨⊤, ?_, ?_⟩⟩
  · rw [TrivialBundle.univ_degIndex_eq_zero, TrivialBundle.univ_degIndex_eq_zero]
  · have hD : scDeriv (zeroRetrOf M).U (zeroRetrOf M) x = 0 :=
      scDeriv_eq_of_hasFDerivAt (relOpenUniv M) (zeroRetrOf M).isScSmooth.isSc1
        (M.mem_lvlSet.2 (mem_univ _)) ((0 : M 0 →L[ℝ] M 0).hasFDerivAt)
    rw [hD, ContinuousLinearMap.toLinearMap_zero, LinearMap.range_zero]
    exact M.isScSplitting_bot_top
  · rw [TrivialBundle.minimalSubspaceWith_univPres]

/-! ### The stabilized strong bundle retraction -/

variable {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

/-- **The stabilization** of a strong bundle retraction `R(u, h) = (r(u), ρ(u)h)` on `U ◁ F` by
the sc-Banach spaces `M` (base) and `N` (fibre):
`R̂((u, m), (h, n)) = ((r(u), 0), (ρ(u)h, 0))` on `(U × M) ◁ (F ⊕ N)`. -/
def stabilize (R : E 0 × F 0 → E 0 × F 0) (M N : ScBanach) :
    (E.prod M) 0 × (F.prod N) 0 → (E.prod M) 0 × (F.prod N) 0 :=
  fun q => (((R (q.1.1, q.2.1)).1, 0), ((R (q.1.1, q.2.1)).2, 0))

/-- `R̂ = (ι_E × ι_F) ∘ R ∘ (π_E × π_F)` with the linear projections and inclusions. -/
lemma stabilize_eq (R : E 0 × F 0 → E 0 × F 0) (M N : ScBanach) :
    stabilize R M N =
      (((E.prodInlOp M).prodMap (F.prodInlOp N)) 0) ∘
        (R ∘ (((E.prodFstOp M).prodMap (F.prodFstOp N)) 0)) := rfl

/-- The base map of `R̂` is `r × 0`. -/
lemma r_stabilize (R : E 0 × F 0 → E 0 × F 0) (M N : ScBanach) :
    StrongRetr.r (stabilize R M N) = Prod.map (StrongRetr.r R) ((zeroOp M) 0) := rfl

variable (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)

include hU hR in
/-- **The stabilization is a strong bundle retraction** on `(U × M) ◁ (F ⊕ N)` (Definition 2.6.1,
preprint 2.47): `R̂ = L₂ ∘ R ∘ L₁` with sc-operators `L₁`, `L₂`, on both `(U ◁ F)[0]` and
`(U ◁ F)[1]`. -/
theorem isStrongBundleRetraction_stabilize (M N : ScBanach) :
    IsStrongBundleRetraction (U ×ˢ (univ : Set (M 0))) (stabilize R M N) where
  mapsTo q hq := ⟨⟨hR.mapsTo_fst ⟨hq.1.1, mem_univ _⟩, mem_univ _⟩, mem_univ _⟩
  fst_independent u hu h h' := by
    change (((R (u.1, h.1)).1, (0 : M 0)) : (E.prod M) 0) = ((R (u.1, h'.1)).1, 0)
    rw [hR.fst_independent u.1 hu.1 h.1 h'.1]
  fiber_linear u hu := by
    have hl := hR.fiber_linear u.1 hu.1
    refine ⟨fun h h' => Prod.ext ?_ ?_, fun c h => Prod.ext ?_ ?_⟩
    · exact hl.map_add h.1 h'.1
    · simp [stabilize]
    · exact hl.map_smul c h.1
    · simp [stabilize]
  preserves_filtration m k hk u hu hum h hh := by
    obtain ⟨a, ha⟩ := hum
    obtain ⟨b, hb⟩ := hh
    rw [ScBanach.prod_toBase] at ha hb
    have h1 : u.1 ∈ range (E.toBase m) := ⟨a.1, congrArg Prod.fst ha⟩
    have h2 : h.1 ∈ range (F.toBase k) := ⟨b.1, congrArg Prod.fst hb⟩
    obtain ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ := hR.preserves_filtration m k hk u.1 hu.1 h1 h.1 h2
    refine ⟨⟨(c, 0), ?_⟩, ⟨(d, 0), ?_⟩⟩
    · rw [ScBanach.prod_toBase, map_zero]; exact Prod.ext hc rfl
    · rw [ScBanach.prod_toBase, map_zero]; exact Prod.ext hd rfl
  isScSmooth_zero := by
    have hD1 := ((hU.prod_univ M).prod_univ (F.prod N)).isScDomain
    have hD2 := (hU.prod_univ F).isScDomain
    rw [stabilize_eq]
    refine IsScSmooth.comp hD1 hD2 (ScOperator.isScSmooth _ hD2) ?_ fun q hq =>
      hR.mapsTo ⟨hq.1.1, mem_univ _⟩
    exact IsScSmooth.comp hD1 hD2 hR.isScSmooth_zero (ScOperator.isScSmooth _ hD1)
      fun q hq => ⟨hq.1.1, mem_univ _⟩
  isScSmooth_one := by
    have hD1 := ((hU.prod_univ M).prod_univ (F.prod N).shift).isScDomain
    have hD2 := (hU.prod_univ F.shift).isScDomain
    have hsm : IsScSmooth (E := (E.prod M).prod (F.prod N).shift)
        (F := (E.prod M).prod (F.prod N).shift) ((U ×ˢ univ) ×ˢ univ)
        ((((E.prodInlOp M).prodMap (F.shift.prodInlOp N.shift)) 0) ∘
          (shiftFiber R ∘ (((E.prodFstOp M).prodMap (F.shift.prodFstOp N.shift)) 0))) := by
      refine IsScSmooth.comp hD1 hD2 (ScOperator.isScSmooth _ hD2) ?_ fun q hq => ?_
      · exact IsScSmooth.comp hD1 hD2 hR.isScSmooth_one (ScOperator.isScSmooth _ hD1)
          fun q hq => ⟨hq.1.1, mem_univ _⟩
      · exact ⟨hR.mapsTo_fst ⟨hq.1.1, mem_univ _⟩, mem_univ _⟩
    refine hsm.congr hD1 ?_
    rintro ⟨⟨u, m⟩, ⟨f₁, n₁⟩⟩ ⟨⟨hu, -⟩, -⟩
    obtain ⟨y₁, hy₁⟩ := (hR.preserves_filtration 0 1 (by norm_num) u hu ⟨u, rfl⟩
      (F.toBase 1 f₁) ⟨f₁, rfl⟩).2
    have hpair : ((F.prod N).toBase 1) (f₁, n₁) = (F.toBase 1 f₁, N.toBase 1 n₁) :=
      ScBanach.prod_toBase F N 1 (f₁, n₁)
    have hy₀ : ((F.prod N).toBase 1) (y₁, 0) = (F.toBase 1 y₁, 0) := by
      rw [ScBanach.prod_toBase, map_zero]
    simp only [Function.comp, shiftFiber, stabilize]
    rw [hpair]
    refine Prod.ext rfl ?_
    change (invFun (F.toBase 1) (R (u, F.toBase 1 f₁)).2, (0 : N 1)) =
      invFun ((F.prod N).toBase 1) ((R (u, F.toBase 1 f₁)).2, 0)
    rw [← hy₁, leftInverse_invFun (F.toBase_injective 1), ← hy₀,
      leftInverse_invFun ((F.prod N).toBase_injective 1)]
  idem q hq := by
    have h := hR.idem (q.1.1, q.2.1) ⟨hq.1.1, mem_univ _⟩
    simp [stabilize, h]

/-- The base retraction of `R̂` is the product `r × 0` of the base retraction of `R` with the
constant retraction of `M` onto `0`. -/
theorem baseRetraction_stabilize (M N : ScBanach) :
    (isStrongBundleRetraction_stabilize hU hR M N).baseRetraction (hU.prod_univ M) =
      (hR.baseRetraction hU).prod (zeroRetrOf M) := rfl

/-- **The stabilization of a tame local model is tame** (Definition 2.5.2, preprint 2.34): `M` has
no boundary, so `r × 0` is the product of two tame retractions (`ScRetraction.IsTameWith.prod`),
tame for the product presentation, hence for every presentation
(`ScRetraction.IsTameWith.isTame`). -/
theorem isTame_baseRetraction_stabilize (M N : ScBanach)
    (ht : (hR.baseRetraction hU).IsTame) :
    ((isStrongBundleRetraction_stabilize hU hR M N).baseRetraction (hU.prod_univ M)).IsTame := by
  rw [baseRetraction_stabilize hU hR M N]
  obtain ⟨n, W, T, hT⟩ := hU.isPartialQuadrant
  exact (ScRetraction.IsTameWith.prod hT (TrivialBundle.univ_eq_univPres M) (ht n W T hT)
    (zeroRetrOf_isTameWith M)).isTame (prod_eq_prodPresentation T (TrivialBundle.univPres M) hT
      (TrivialBundle.univ_eq_univPres M))

/-! ### The normal spaces of the stabilized model -/

variable (h0 : (0 : E 0) ∈ U)

include h0 in
lemma zero_mem_stabilize (M : ScBanach) : (0 : (E.prod M) 0) ∈ U ×ˢ (univ : Set (M 0)) :=
  ⟨h0, mem_univ _⟩

/-- `ρ̂(0) = ρ(0) × 0 : F ⊕ N → F ⊕ N`. -/
theorem ρCLM_stabilize (M N : ScBanach) :
    StrongRetr.ρCLM (isStrongBundleRetraction_stabilize hU hR M N) (zero_mem_stabilize h0 M) =
      (StrongRetr.ρCLM hR h0).prodMap (0 : N 0 →L[ℝ] N 0) :=
  ContinuousLinearMap.ext fun _ => Prod.ext rfl rfl

include hU hR h0 in
/-- `Dr̂(0) = Dr(0) × 0 : E ⊕ M → E ⊕ M`. -/
theorem scDeriv_r_stabilize (M N : ScBanach) :
    scDeriv (U ×ˢ (univ : Set (M 0))) (StrongRetr.r (stabilize R M N)) (0 : (E.prod M) 1) =
      (scDeriv U (StrongRetr.r R) (0 : E 1)).prodMap (0 : M 0 →L[ℝ] M 0) := by
  have hr : IsScSmooth U (StrongRetr.r R) := (hR.baseRetraction hU).isScSmooth
  have hz : IsScSmooth (univ : Set (M 0)) ((zeroOp M) 0) :=
    (zeroOp M).isScSmooth (isScDomain_univ M)
  have hx : (0 : (E.prod M) 1) ∈ (E.prod M).lvlSet (U ×ˢ univ) 1 := by
    rw [lvlSet_prod]
    refine ⟨?_, mem_univ _⟩
    change E.toBase 1 (0 : E 1) ∈ U
    rw [map_zero]; exact h0
  rw [r_stabilize, scDeriv_prodMap hU (relOpenUniv M) hr hz hx]
  have hD : scDeriv (univ : Set (M 0)) ((zeroOp M) 0) (0 : M 1) = 0 :=
    scDeriv_eq_of_hasFDerivAt (relOpenUniv M) hz.isSc1 (M.mem_lvlSet.2 (mem_univ _))
      ((0 : M 0 →L[ℝ] M 0).hasFDerivAt)
  change (scDeriv U (StrongRetr.r R) (0 : E 1)).prodMap
    (scDeriv (univ : Set (M 0)) ((zeroOp M) 0) (0 : M 1)) = _
  rw [hD]

/-- `ker (A × 0) ≃ ker A × Z` for a continuous linear map `A : X → Y` and the zero map `Z → Z'`. -/
def kerProdMapZeroEquiv {X Y Z Z' : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup Z'] [NormedSpace ℝ Z'] (A : X →L[ℝ] Y) :
    LinearMap.ker ((A.prodMap (0 : Z →L[ℝ] Z') : X × Z →L[ℝ] Y × Z') : X × Z →ₗ[ℝ] Y × Z') ≃L[ℝ]
      LinearMap.ker (A : X →ₗ[ℝ] Y) × Z where
  toFun p := (⟨p.1.1, LinearMap.mem_ker.2 (by
    have := congrArg Prod.fst (LinearMap.mem_ker.1 p.2)
    simp at this; exact this)⟩, p.1.2)
  invFun q := ⟨(q.1.1, q.2), LinearMap.mem_ker.2 (Prod.ext (LinearMap.mem_ker.1 q.1.2) rfl)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    refine Continuous.prodMk (Continuous.subtype_mk ?_ _) ?_
    · exact continuous_fst.comp continuous_subtype_val
    · exact continuous_snd.comp continuous_subtype_val
  continuous_invFun := by
    refine Continuous.subtype_mk (Continuous.prodMk ?_ continuous_snd) _
    exact continuous_subtype_val.comp continuous_fst

/-- **The normal spaces of the stabilized model are isomorphic** when `N ≅ ker Dr(0)` and
`M ≅ ker ρ(0)`: `ker Dr̂(0) = ker Dr(0) ⊕ M ≅ ker Dr(0) ⊕ ker ρ(0) ≅ ker ρ(0) ⊕ N = ker ρ̂(0)`.
This is the necessary condition of Definition 3.1.4 (3) (preprint 3.4; `IsFillingGerm.nonempty_kerEquiv`,
Findings item 350), met in the stabilized model whatever the normal spaces of `R` are. -/
theorem nonempty_kerEquiv_stabilize (M N : ScBanach)
    (eN : LinearMap.ker ((scDeriv U (StrongRetr.r R) (0 : E 1) : E 0 →L[ℝ] E 0) :
      E 0 →ₗ[ℝ] E 0) ≃L[ℝ] N 0)
    (eM : LinearMap.ker ((StrongRetr.ρCLM hR h0 : F 0 →L[ℝ] F 0) : F 0 →ₗ[ℝ] F 0) ≃L[ℝ] M 0) :
    Nonempty
      (LinearMap.ker ((scDeriv (U ×ˢ (univ : Set (M 0))) (StrongRetr.r (stabilize R M N))
          (0 : (E.prod M) 1) : (E.prod M) 0 →L[ℝ] (E.prod M) 0) :
          (E.prod M) 0 →ₗ[ℝ] (E.prod M) 0) ≃L[ℝ]
        LinearMap.ker ((StrongRetr.ρCLM (isStrongBundleRetraction_stabilize hU hR M N)
          (zero_mem_stabilize h0 M) : (F.prod N) 0 →L[ℝ] (F.prod N) 0) :
          (F.prod N) 0 →ₗ[ℝ] (F.prod N) 0)) := by
  rw [scDeriv_r_stabilize hU hR h0 M N, ρCLM_stabilize hU hR h0 M N]
  exact ⟨(kerProdMapZeroEquiv _).trans ((eN.prodCongr eM.symm).trans
    ((ContinuousLinearEquiv.prodComm ℝ _ _).trans (kerProdMapZeroEquiv _).symm))⟩

/-! ### The stabilizing spaces exist: `ker Dr(0)` and `ker ρ(0)` are sc-Banach spaces -/

include hU hR in
/-- `ker Dr(0)` is an sc-subspace of `E` (`0 ∈ O`): `Dr(0)` is an sc-projection (Lemma 2.B). -/
theorem isScSubspace_ker_scDeriv_r (h0O : (0 : E 0) ∈ StrongRetr.r R '' U) :
    E.IsScSubspace (LinearMap.ker ((scDeriv U (StrongRetr.r R) (0 : E 1) : E 0 →L[ℝ] E 0) :
      E 0 →ₗ[ℝ] E 0)) := by
  have hop := StrongRetr.isScOperator_scDeriv_r hU hR (StrongRetr.mem_U_of_mem_O hR h0O)
  have hidem : ∀ x, hop.toScOperator 0 (hop.toScOperator 0 x) = hop.toScOperator 0 x := by
    rw [hop.toScOperator_zero]; exact StrongRetr.scDeriv_r_idem hU hR h0O
  have h := ScBanach.isScSplitting_of_idem hop.toScOperator hidem
  rw [hop.toScOperator_zero] at h
  exact h.2.1

include hR in
/-- `ker ρ(0)` is an sc-subspace of `F` (`0 ∈ O`): `ρ(0)` is an sc-projection (Lemma 2.B). -/
theorem isScSubspace_ker_ρCLM (h0O : (0 : E 0) ∈ StrongRetr.r R '' U) :
    F.IsScSubspace (LinearMap.ker ((StrongRetr.ρCLM hR h0 : F 0 →L[ℝ] F 0) : F 0 →ₗ[ℝ] F 0)) := by
  have hop := StrongRetr.isScOperator_ρCLM hR h0
  have hidem : ∀ x, hop.toScOperator 0 (hop.toScOperator 0 x) = hop.toScOperator 0 x := by
    rw [hop.toScOperator_zero]; exact StrongRetr.ρCLM_idem hR h0 h0O
  have h := ScBanach.isScSplitting_of_idem hop.toScOperator hidem
  rw [hop.toScOperator_zero] at h
  exact h.2.1

/-- The level `0` of the sc-Banach space `E.ofSubspace hA` is `A`. -/
def ofSubspaceZeroEquiv {A : Submodule ℝ (E 0)} (hA : E.IsScSubspace A) :
    (E.ofSubspace hA) 0 ≃L[ℝ] A where
  toLinearEquiv := LinearEquiv.ofEq _ _ (E.levelSub_zero A)
  continuous_toFun := continuous_induced_rng.2 continuous_subtype_val
  continuous_invFun := continuous_induced_rng.2 continuous_subtype_val

include hU hR h0 in
/-- **Stabilizing spaces exist**: for every strong bundle retraction `R` on `U ◁ F` with `0 ∈ O`
there are sc-Banach spaces `M`, `N` (namely `ker ρ(0)` and `ker Dr(0)`) such that the stabilized
model `R̂` on `(U × M) ◁ (F ⊕ N)` — a strong bundle retraction, tame when `R` is — satisfies the
normal-space condition `ker Dr̂(0) ≃ ker ρ̂(0)` of Definition 3.1.4 (3) (preprint 3.4). -/
theorem exists_stabilization_kerEquiv (h0O : (0 : E 0) ∈ StrongRetr.r R '' U) :
    ∃ M N : ScBanach,
      Nonempty
        (LinearMap.ker ((scDeriv (U ×ˢ (univ : Set (M 0))) (StrongRetr.r (stabilize R M N))
            (0 : (E.prod M) 1) : (E.prod M) 0 →L[ℝ] (E.prod M) 0) :
            (E.prod M) 0 →ₗ[ℝ] (E.prod M) 0) ≃L[ℝ]
          LinearMap.ker ((StrongRetr.ρCLM (isStrongBundleRetraction_stabilize hU hR M N)
            (zero_mem_stabilize h0 M) : (F.prod N) 0 →L[ℝ] (F.prod N) 0) :
            (F.prod N) 0 →ₗ[ℝ] (F.prod N) 0)) :=
  ⟨F.ofSubspace (isScSubspace_ker_ρCLM hR h0 h0O),
    E.ofSubspace (isScSubspace_ker_scDeriv_r hU hR h0O),
    nonempty_kerEquiv_stabilize hU hR h0 _ _
      (ofSubspaceZeroEquiv (isScSubspace_ker_scDeriv_r hU hR h0O)).symm
      (ofSubspaceZeroEquiv (isScSubspace_ker_ρCLM hR h0 h0O)).symm⟩

end Stabilize

end Polyfold
