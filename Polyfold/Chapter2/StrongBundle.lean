import Polyfold.Chapter2.TangentBundle
import Polyfold.Chapter2.Tame

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §2.5,
Definitions 2.6.4–2.6.7 (preprint 2.50–2.53) and the statements around Definitions 2.47–2.54 (the local strong bundle
retracts, `K[i]`, sections, the strong bundle charts and atlases, the M-polyfold `Y[0]`, the
pull-back), with the local construction of the proof of Proposition 2.6.8 (preprint 2.54).

# Strong bundles

## The text, paraphrased

(After Definition 2.6.1 (preprint 2.47)) A strong bundle retraction has the form `R(u, h) = (r(u), Γ(u, h))` with
`r : U → U` an sc-smooth retraction; for `r(u) = u` the map `h ↦ Γ(u, h)` is a projection (an
sc-projection at smooth points).  (After Definition 2.6.2 (preprint 2.48))
`K_{m,k} = {(u, h) ∈ O_m ⊕ F_k | Γ(u, h) = h}`,
`K[i]` with the filtrations `K_{m,m+i}`; the projections `p : K[i] → O` are sc-smooth.
(Definition 2.6.4 (preprint 2.50)) A strong bundle chart for a continuous surjection `P : Y → X` (Y paracompact
Hausdorff, Banachable fibres) is `(Φ, P⁻¹(V), K, U ◁ F)`: a homeomorphism `Φ : P⁻¹(V) → K` covering
a homeomorphism `φ : V → O`, bounded linear on the fibres; two charts are compatible if
`(Φ' ∘ Φ⁻¹)[i]` are sc-diffeomorphisms for `i = 0, 1`; strong bundle atlases and their equivalence.
(Definition 2.6.5 (preprint 2.51)) A strong bundle is `P : Y → X` with an equivalence class of strong bundle atlases;
`Y` gets a double filtration `Y_{m,k}` and M-polyfold structures `Y[i]`, `P[i] : Y[i] → X`
sc-smooth.  (Definition 2.6.6 (preprint 2.52)) Sections, sc-smooth sections (into `Y[0]`), sc⁺-sections (into
`Y[1]`).  (Definition 2.6.7 (preprint 2.53)) The pull-back `f*Y = {(z, y) | P(y) = f(z)}`.  (Proposition 2.6.8 (preprint 2.54)) It
carries a natural strong bundle structure ("the easy proof is left to the reader").

## What is formalized

* Pairings of sc^k maps (`Polyfold.IsSck.scPair`, `IsScSmooth.scPair`; exposition Lemma 3.G(3) of
  Chapter 1) and the sc-operators `prodFstOp`, `prodSndOp`, `prodInlOp`, `prodShiftInclOp`.
* `Polyfold.IsPartialQuadrant.prod_univ`, `IsRelOpenInQuadrant.prod_univ`: `U ◁ F` is relatively
  open in the partial quadrant `C ⊕ F` of `E ⊕ F` (so `(U ◁ F)[i] = U ⊕ F^i` is an sc-domain; the
  sc-isomorphism `E ⊕ F ≅ ℝⁿ ⊕ (W ⊕ F)` is `prodQuadrantIso`).
* **Lemma 5.A**: `IsStrongBundleRetraction.baseRetraction` (`r` is an sc-smooth retraction),
  `fiber_idem` (`Γ(u, ·)` is a projection for `u ∈ O`), `mem_image_iff` (`K = {(u, h) | u ∈ O,
  Γ(u, h) = h}`), `toScRetraction`, `toScRetractionOne` (`R` on `(U ◁ F)[0]` and `[1]`).
* **Lemma 5.B**: `IsStrongBundleRetract.isScRetract`, `isScRetract_one` (`K[0]`, `K[1]` are
  sc-smooth retracts, `toScRetractionOne_retract`), `isScSmoothRetractMap_fst`,
  `isScSmoothRetractMap_fst_one` (`p : K[i] → O` sc-smooth), `isScSmoothRetractMap_shiftIncl`
  (`K[1] → K[0]` sc-smooth), and `IsScPlusSection.isScSmoothSection` (an sc⁺-section is sc-smooth).
* `Polyfold.StrongBundleChart` (**Definition 2.6.4 (preprint 2.50)**), with `StrongBundleChart.Compatible`,
  `StrongBundleChart.continuous_fiber` (boundedness on the fibres is automatic),
  `Polyfold.StrongBundleAtlas` and `StrongBundleAtlas.Equiv`; `Polyfold.StrongBundle`
  (**Definition 2.6.5 (preprint 2.51)**), `StrongBundle.toMPolyfold0` (the M-polyfold `Y[0]`, charts
  `StrongBundleChart.toMChart`), `StrongBundle.isScSmoothMap_proj` (`P[0] : Y[0] → X` is
  sc-smooth), `StrongBundle.doubleLevel` (`Y_{m,k}`).
* `Polyfold.IsSection`, `StrongBundle.IsScSmoothSection`, `StrongBundle.IsScPlusSection`
  (**Definition 2.6.6 (preprint 2.52)**); `Polyfold.pullbackSpace`, `pullbackProj`, `pullbackProj'`, `pullback_comm`
  (**Definition 2.6.7 (preprint 2.53)**).
* The local content of **Proposition 2.6.8 (preprint 2.54)**: `pullbackRetraction` (`R_g(w, h) = (r'(w),
  Γ(g(r'(w)), h))`), `isStrongBundleRetraction_pullback` and `pullback_image`
  (`R_g(U' ◁ F) = {(w, h) | w ∈ O', (g(w), h) ∈ K}`), `isStrongBundleRetract_pullback`.

## What the text leaves implicit, and the choices made

* The fibres `P⁻¹(x)` carry vector space structures given as instance families
  `[∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]`, with the subspace topology;
  "Banachable" (`Polyfold.IsBanachable`) is "linearly homeomorphic to a Banach space".
* The base chart `φ` of a strong bundle chart is required to be a chart of the M-polyfold structure
  of `X` (`StrongBundleChart.isChart`); the text only says "homeomorphic to the retract `O`", but
  without this the strong bundle charts would define their own structure on `X`.
* "Bounded linear on the fibres" is `fiber_linear`; continuity follows from `Φ` being a
  homeomorphism (`continuous_fiber`).
* "sc-diffeomorphisms" in Definition 2.6.4 (preprint 2.50) is read as: both `(Φ' ∘ Φ⁻¹)[i]` and `(Φ ∘ Φ'⁻¹)[i]` are
  sc-smooth between the retracts `Φ(P⁻¹(V ∩ V'))[i]` and `Φ'(P⁻¹(V ∩ V'))[i]` (they are inverse to
  each other there).  `[1]` is formalized with `shiftFiber` and `strongShiftOne`; that
  `(Φ' ∘ Φ⁻¹)[1]` is the restriction of `Φ' ∘ Φ⁻¹` to `K[1]` (fibre components in `F₁` go to
  fibre components in `F'₁`) is stated explicitly.
* An equivalence class of atlases is represented by one atlas, as for M-polyfolds.  The M-polyfold
  `Y[0]` is constructed here (it is what the text calls "the M-polyfold `Y`"); the M-polyfold
  `Y[1]` (whose underlying set `Y_{0,1}` carries a finer topology) is constructed in
  `StrongBundleOne.lean`.  Sc⁺-sections are defined here in the charts
  `Φ[1] : P⁻¹(V)[1] → K[1]` (`StrongBundle.localRepOne`); that this is sc-smoothness into `Y[1]`
  is `StrongBundle.isScPlusSection_iff` there.
* The double filtration `Y_{m,k}` is defined with all charts of the atlas around the point; its
  independence of the chart is `StrongBundle.mem_doubleLevel_iff` in `StrongBundleOne.lean`.

## Elsewhere, and not formalized

* Proposition 2.6.8 (preprint 2.54) as a statement about strong bundles is `Polyfold.proposition_2_6_8` in
  `StrongBundlePullback.lean` (it needs the metrizability of Theorem 2.3.10 (preprint 2.16) for the paracompactness
  of `f*Y`); its local content is `isStrongBundleRetract_pullback` here.
* `P[1] : Y[1] → X` sc-smooth is `StrongBundle.isScSmoothMap_proj1` in `StrongBundleOne.lean`;
  strong bundle isomorphisms, the category `SBR` and the forgetful functors are not formalized
  (gap G.14 of the report).
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

variable {E F G : ScBanach}

/-! ### Pairings of sc^k maps -/

section Pair

/-- The whole space is an sc-domain. -/
lemma isScDomain_univ (E : ScBanach) : IsScDomain E univ :=
  (show IsRelOpenInQuadrant E univ univ from
    ⟨isPartialQuadrant_univ E, univ, isOpen_univ, (inter_univ _).symm⟩).isScDomain

/-- The pairing `x ↦ (f x, g x)`. -/
def scPair (f : E 0 → F 0) (g : E 0 → G 0) : E 0 → (F.prod G) 0 := fun x => (f x, g x)

variable {U : Set (E 0)} {f : E 0 → F 0} {g : E 0 → G 0}

lemma IsSc0.levelMap_scPair (hf : IsSc0 E F U f) (hg : IsSc0 E G U g) {m : ℕ} {x : E m}
    (hx : x ∈ E.lvlSet U m) :
    levelMap (scPair f g) m x = ((levelMap f m x, levelMap g m x) : (F.prod G) m) := by
  apply levelMap_eq_of_toBase_eq
  rw [ScBanach.prod_toBase, hf.toBase_levelMap hx, hg.toBase_levelMap hx]
  rfl

lemma IsSc0.scPair (hf : IsSc0 E F U f) (hg : IsSc0 E G U g) :
    IsSc0 E (F.prod G) U (scPair f g) where
  mem_range m x hx := ⟨(levelMap f m x, levelMap g m x), by
    rw [ScBanach.prod_toBase, hf.toBase_levelMap hx, hg.toBase_levelMap hx]; rfl⟩
  continuousOn m := ((hf.continuousOn m).prodMk (hg.continuousOn m)).congr
    fun x hx => hf.levelMap_scPair hg hx

/-- The sc-operator `TF ⊕ TG → T(F ⊕ G)`, `((a, b), (c, d)) ↦ ((a, c), (b, d))`. -/
def tangentProdSwap (F G : ScBanach) :
    ScOperator (F.tangent.prod G.tangent) (F.prod G).tangent where
  lvl m := (ContinuousLinearEquiv.prodProdProdComm ℝ (F (m + 1)) (F m) (G (m + 1)) (G m) :
    _ →L[ℝ] _)
  incl_comm _ _ := rfl

lemma tangentMapWith_scPair {Df : E 1 → E 0 →L[ℝ] F 0} {Dg : E 1 → E 0 →L[ℝ] G 0}
    (hf : IsSc0 E F U f) (hg : IsSc0 E G U g) :
    EqOn (tangentMapWith (scPair f g) fun x => (Df x).prod (Dg x))
      (tangentProdSwap F G 0 ∘ scPair (tangentMapWith f Df) (tangentMapWith g Dg))
      (E.tangentSet U) := by
  intro p hp
  change (levelMap (scPair f g) 1 p.1, (Df p.1 p.2, Dg p.1 p.2)) =
    ((levelMap f 1 p.1, levelMap g 1 p.1), (Df p.1 p.2, Dg p.1 p.2))
  rw [hf.levelMap_scPair hg hp]

lemma IsSc1With.scPair {Df : E 1 → E 0 →L[ℝ] F 0} {Dg : E 1 → E 0 →L[ℝ] G 0}
    (hf : IsSc1With U f Df) (hg : IsSc1With U g Dg) :
    IsSc1With U (scPair f g) fun x => (Df x).prod (Dg x) where
  isSc0 := hf.isSc0.scPair hg.isSc0
  hasFDerivWithinAt x hx := by
    have := (hf.hasFDerivWithinAt x hx).prodMk (hg.hasFDerivWithinAt x hx)
    exact this.congr_fderiv (ContinuousLinearMap.ext fun v => rfl)
  tangent_isSc0 :=
    (IsSc0.comp ((tangentProdSwap F G).isScSmooth (isScDomain_univ _) 0)
      (hf.tangent_isSc0.scPair hg.tangent_isSc0) (mapsTo_univ _ _)).congr
      (tangentMapWith_scPair hf.isSc0 hg.isSc0).symm

/-- The pairing of sc^k maps is sc^k (exposition Lemma 3.G(3) of Chapter 1). -/
theorem IsSck.scPair : ∀ {k : ℕ} {E F G : ScBanach} {U : Set (E 0)} {f : E 0 → F 0}
    {g : E 0 → G 0}, IsScDomain E U → IsSck k E F U f → IsSck k E G U g →
    IsSck k E (F.prod G) U (scPair f g)
  | 0, _, _, _, _, _, _, _, hf, hg => IsSc0.scPair hf hg
  | k + 1, _, _, _, U, f, g, hU, hf, hg => by
    have h1 := hf.1.isSc1With_scDeriv.scPair hg.1.isSc1With_scDeriv
    refine ⟨h1.isSc1, ?_⟩
    have h2 : EqOn (tangentMap U (Polyfold.scPair f g))
        (tangentProdSwap _ _ 0 ∘ Polyfold.scPair (tangentMap U f) (tangentMap U g))
        (ScBanach.tangentSet _ U) :=
      (IsSc1.tangentMap_eqOn h1 (hU.uniqueDiffWithinAt 1)).trans
        (tangentMapWith_scPair hf.1.isSc0 hg.1.isSc0)
    refine IsSck.congr hU.tangentSet h2.symm ?_
    exact IsSck.comp hU.tangentSet (isScDomain_univ _)
      ((tangentProdSwap _ _).isScSmooth (isScDomain_univ _) k)
      (IsSck.scPair (k := k) hU.tangentSet hf.2 hg.2) (mapsTo_univ _ _)

theorem IsScSmooth.scPair (hU : IsScDomain E U) (hf : IsScSmooth U f) (hg : IsScSmooth U g) :
    IsScSmooth U (scPair f g) := fun k => (hf k).scPair hU (hg k)

end Pair

/-! ### The sc-structures `(U ◁ F)[i]`: partial quadrants and the projections -/

section ProdQuadrant

variable {n : ℕ} {W : ScBanach} {C U : Set (E 0)}

/-- The projection `E ⊕ F → E` as an sc-operator. -/
def ScBanach.prodFstOp (E F : ScBanach) : ScOperator (E.prod F) E where
  lvl m := ContinuousLinearMap.fst ℝ (E m) (F m)
  incl_comm _ _ := rfl

/-- The projection `E ⊕ F → F` as an sc-operator. -/
def ScBanach.prodSndOp (E F : ScBanach) : ScOperator (E.prod F) F where
  lvl m := ContinuousLinearMap.snd ℝ (E m) (F m)
  incl_comm _ _ := rfl

/-- The inclusion `E → E ⊕ F`, `u ↦ (u, 0)`, as an sc-operator. -/
def ScBanach.prodInlOp (E F : ScBanach) : ScOperator E (E.prod F) where
  lvl m := ContinuousLinearMap.inl ℝ (E m) (F m)
  incl_comm m _ := Prod.ext rfl (map_zero (F.incl m))

/-- `E ⊕ F¹ → E ⊕ F`, `(u, h) ↦ (u, h)` (the identity on `E`, the inclusion `F¹ → F`). -/
def ScBanach.prodShiftInclOp (E F : ScBanach) : ScOperator (E.prod F.shift) (E.prod F) where
  lvl m := (ContinuousLinearMap.id ℝ (E m)).prodMap (F.incl m)
  incl_comm _ _ := rfl

lemma ScBanach.prodShiftInclOp_apply (E F : ScBanach) (p : (E.prod F.shift) 0) :
    E.prodShiftInclOp F 0 p = (p.1, F.toBase 1 p.2) := rfl

/-- The re-association `(ℝⁿ ⊕ W) ⊕ F ≅ ℝⁿ ⊕ (W ⊕ F)`. -/
def prodQuadrantIso (n : ℕ) (W F : ScBanach) :
    ScIso (((ScBanach.const (Fin n → ℝ)).prod W).prod F)
      ((ScBanach.const (Fin n → ℝ)).prod (W.prod F)) where
  lvl m := ContinuousLinearEquiv.prodAssoc ℝ (Fin n → ℝ) (W m) (F m)
  incl_comm _ _ := rfl

/-- `C ◁ F = C × F` is a partial quadrant in `E ⊕ F` (the text's "`(U ◁ F)[i]` are
sc-manifolds"; exposition Lemma 1.B). -/
theorem IsPartialQuadrant.prod_univ (hC : IsPartialQuadrant E C) (F : ScBanach) :
    IsPartialQuadrant (E.prod F) (C ×ˢ (univ : Set (F 0))) := by
  obtain ⟨n, W, T, rfl⟩ := hC
  let T₁ : ScIso (E.prod F) (((ScBanach.const (Fin n → ℝ)).prod W).prod F) :=
    { lvl := fun m => (T m).prodCongr (ContinuousLinearEquiv.refl ℝ (F m))
      incl_comm := fun m x => Prod.ext (T.incl_comm m x.1) rfl }
  refine ⟨n, W.prod F, T₁.trans (prodQuadrantIso n W F), ?_⟩
  ext p
  change (p.1 ∈ T 0 ⁻¹' quadrant n W 0 ∧ p.2 ∈ univ) ↔ ∀ i, 0 ≤ (T 0 p.1).1 i
  simp only [mem_preimage, mem_univ, and_true]
  rfl

/-- `U ◁ F = U × F` is relatively open in `C ◁ F`. -/
theorem IsRelOpenInQuadrant.prod_univ (hU : IsRelOpenInQuadrant E C U) (F : ScBanach) :
    IsRelOpenInQuadrant (E.prod F) (C ×ˢ (univ : Set (F 0))) (U ×ˢ univ) := by
  obtain ⟨O, hO, rfl⟩ := hU.relOpen
  refine ⟨hU.isPartialQuadrant.prod_univ F, O ×ˢ univ, hO.prod isOpen_univ, ?_⟩
  rw [prod_inter_prod, inter_univ]

end ProdQuadrant

/-! ### Strong bundle retractions: Lemmas 5.A and 5.B of the exposition -/

namespace IsStrongBundleRetraction

variable {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

/-- The first component of `R(u, h)` is `r(u)` (the text's "`R(u, h) = (r(u), Γ(u, h))`"). -/
lemma apply_fst (hR : IsStrongBundleRetraction U R) {u : E 0} (hu : u ∈ U) (h : F 0) :
    (R (u, h)).1 = IsStrongBundleMap.base R u :=
  hR.fst_independent u hu h 0

lemma mapsTo_fst (hR : IsStrongBundleRetraction U R) {p : E 0 × F 0} (hp : p ∈ U ×ˢ univ) :
    (R p).1 ∈ U := (hR.mapsTo hp).1

/-- The base retraction `r : U → U` of a strong bundle retraction `R(u, h) = (r(u), Γ(u, h))`
is an sc-smooth retraction (Definition 2.6.1 (preprint 2.47)). -/
def baseRetraction (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R) :
    ScRetraction E C where
  U := U
  toFun := IsStrongBundleMap.base R
  relOpen := hU
  mapsTo u hu := hR.mapsTo_fst ⟨hu, mem_univ _⟩
  isScSmooth := by
    have hUF := (hU.prod_univ F).isScDomain
    have h1 : IsScSmooth (E := E) (F := E.prod F) U (R ∘ E.prodInlOp F 0) :=
      IsScSmooth.comp (G := E.prod F) hU.isScDomain hUF hR.isScSmooth_zero
        ((E.prodInlOp F).isScSmooth hU.isScDomain) fun u hu =>
          show (u, (0 : F 0)) ∈ U ×ˢ univ from ⟨hu, mem_univ _⟩
    exact IsScSmooth.comp hU.isScDomain (isScDomain_univ _)
      ((E.prodFstOp F).isScSmooth (isScDomain_univ _)) h1 (mapsTo_univ _ _)
  idem u hu := by
    have h := congrArg Prod.fst (hR.idem (u, 0) ⟨hu, mem_univ _⟩)
    change (R (R (u, 0))).1 = (R (u, 0)).1 at h
    have hu' : (R (u, 0)).1 ∈ U := hR.mapsTo_fst ⟨hu, mem_univ _⟩
    change (R ((R (u, 0)).1, 0)).1 = (R (u, 0)).1
    have h2 : (R ((R (u, 0)).1, 0)).1 = (R ((R (u, 0)).1, (R (u, 0)).2)).1 :=
      hR.fst_independent _ hu' 0 _
    rw [h2]
    exact h

lemma baseRetraction_apply (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    (u : E 0) : hR.baseRetraction hU u = (R (u, 0)).1 := rfl

/-- **Lemma 5.A (1)**: for `u ∈ O = r(U)`, `h ↦ Γ(u, h)` is a projection: `Γ(u, Γ(u, h)) = Γ(u, h)`
(the text's remark after Definition 2.6.1 (preprint 2.47)). -/
theorem fiber_idem (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R) {u : E 0}
    (hu : u ∈ (hR.baseRetraction hU).retract) (h : F 0) :
    (R (u, (R (u, h)).2)).2 = (R (u, h)).2 := by
  have huU : u ∈ U := (hR.baseRetraction hU).retract_subset hu
  have hfix : IsStrongBundleMap.base R u = u :=
    (hR.baseRetraction hU).apply_eq_self_of_mem_retract hu
  have h1 := congrArg Prod.snd (hR.idem (u, h) ⟨huU, mem_univ _⟩)
  have h2 : R (u, h) = (u, (R (u, h)).2) := Prod.ext ((hR.apply_fst huU h).trans hfix) rfl
  rw [h2] at h1
  exact h1

/-- The text's description `K = {(u, h) | u ∈ O, Γ(u, h) = h}` of `K = R(U ◁ F)`. -/
theorem mem_image_iff (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    {p : E 0 × F 0} :
    p ∈ R '' (U ×ˢ univ) ↔ p.1 ∈ (hR.baseRetraction hU).retract ∧ (R p).2 = p.2 := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨?_, by rw [hR.idem q hq]⟩
    rw [hR.apply_fst hq.1 q.2]
    exact (hR.baseRetraction hU).apply_mem_retract hq.1
  · rintro ⟨hp1, hp2⟩
    have hpU : p.1 ∈ U := (hR.baseRetraction hU).retract_subset hp1
    refine ⟨p, ⟨hpU, mem_univ _⟩, Prod.ext ?_ hp2⟩
    rw [hR.apply_fst hpU p.2]
    exact (hR.baseRetraction hU).apply_eq_self_of_mem_retract hp1

/-- **Lemma 5.A (2)**, `i = 0`: `R : (U ◁ F)[0] → (U ◁ F)[0]` is an sc-smooth retraction on
`U ⊕ F ⊆ C ⊕ F`. -/
def toScRetraction (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R) :
    ScRetraction (E.prod F) (C ×ˢ univ) where
  U := U ×ˢ univ
  toFun := R
  relOpen := hU.prod_univ F
  mapsTo := hR.mapsTo
  isScSmooth := hR.isScSmooth_zero
  idem := hR.idem

lemma toScRetraction_retract (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R) :
    (hR.toScRetraction hU).retract = R '' (U ×ˢ univ) := rfl

/-- `R` lifts the fibre component to `F₁` on `U ⊕ F₁`: `Γ(u, h) ∈ F₁` for `h ∈ F₁`. -/
lemma snd_mem_range (hR : IsStrongBundleRetraction U R) {p : (E.prod F.shift) 0} (hp : p.1 ∈ U) :
    (R (p.1, F.toBase 1 p.2)).2 ∈ range (F.toBase 1) :=
  (hR.preserves_filtration 0 1 (by norm_num) p.1 hp ⟨p.1, rfl⟩ _ ⟨p.2, rfl⟩).2

lemma toBase_shiftFiber_snd (hR : IsStrongBundleRetraction U R) {p : (E.prod F.shift) 0}
    (hp : p.1 ∈ U) : F.toBase 1 (shiftFiber R p).2 = (R (p.1, F.toBase 1 p.2)).2 :=
  Function.invFun_eq (hR.snd_mem_range hp)

/-- **Lemma 5.A (2)**, `i = 1`: `R : (U ◁ F)[1] → (U ◁ F)[1]` is an sc-smooth retraction on
`U ⊕ F¹ ⊆ C ⊕ F¹`. -/
def toScRetractionOne (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R) :
    ScRetraction (E.prod F.shift) (C ×ˢ univ) where
  U := U ×ˢ univ
  toFun := shiftFiber R
  relOpen := hU.prod_univ F.shift
  mapsTo p hp := ⟨hR.mapsTo_fst ⟨hp.1, mem_univ _⟩, mem_univ _⟩
  isScSmooth := hR.isScSmooth_one
  idem p hp := by
    have hq : R (p.1, F.toBase 1 p.2) ∈ U ×ˢ univ := hR.mapsTo ⟨hp.1, mem_univ _⟩
    have h1 := hR.toBase_shiftFiber_snd hp.1
    have hfix := hR.idem (p.1, F.toBase 1 p.2) ⟨hp.1, mem_univ _⟩
    change ((R ((shiftFiber R p).1, F.toBase 1 (shiftFiber R p).2)).1,
      Function.invFun (F.toBase 1) (R ((shiftFiber R p).1, F.toBase 1 (shiftFiber R p).2)).2) =
        shiftFiber R p
    rw [h1]
    change ((R (R (p.1, F.toBase 1 p.2))).1,
      Function.invFun (F.toBase 1) (R (R (p.1, F.toBase 1 p.2))).2) = shiftFiber R p
    rw [hfix]; rfl

/-- **Lemma 5.B**, `i = 1`: the image of `R` on `(U ◁ F)[1]` is `K[1] = {(u, h) ∈ K | h ∈ F₁}`. -/
theorem toScRetractionOne_retract (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) :
    (hR.toScRetractionOne hU).retract = strongShiftOne (R '' (U ×ˢ univ)) := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    change ((shiftFiber R p).1, F.toBase 1 (shiftFiber R p).2) ∈ R '' (U ×ˢ univ)
    rw [hR.toBase_shiftFiber_snd hp.1]
    exact ⟨_, ⟨hp.1, mem_univ _⟩, rfl⟩
  · intro hq
    obtain ⟨p, hp, hpq⟩ := hq
    have hqU : q.1 ∈ U := by
      have := hR.mapsTo_fst hp
      rw [hpq] at this; exact this
    refine ⟨q, ⟨hqU, mem_univ _⟩, ?_⟩
    have hfix : R (q.1, F.toBase 1 q.2) = (q.1, F.toBase 1 q.2) := by
      rw [← hpq, hR.idem p hp]
    change ((R (q.1, F.toBase 1 q.2)).1,
      Function.invFun (F.toBase 1) (R (q.1, F.toBase 1 q.2)).2) = q
    rw [hfix]
    exact Prod.ext rfl (Function.leftInverse_invFun (F.toBase_injective 1) q.2)

end IsStrongBundleRetraction

namespace IsStrongBundleRetract

variable {C : Set (E 0)} {K : Set (E 0 × F 0)}

/-- **Lemma 5.B**, `i = 0`: a local strong bundle retract `K` is an sc-smooth retract in
`(C ⊕ F, E ⊕ F)`. -/
theorem isScRetract (hK : IsStrongBundleRetract C K) :
    IsScRetract (E.prod F) (C ×ˢ univ) K := by
  obtain ⟨U, R, hU, hR, rfl⟩ := hK
  exact ⟨hR.toScRetraction hU, rfl⟩

/-- **Lemma 5.B**, `i = 1`: `K[1]` is an sc-smooth retract in `(C ⊕ F¹, E ⊕ F¹)`. -/
theorem isScRetract_one (hK : IsStrongBundleRetract C K) :
    IsScRetract (E.prod F.shift) (C ×ˢ univ) (strongShiftOne K) := by
  obtain ⟨U, R, hU, hR, rfl⟩ := hK
  exact ⟨hR.toScRetractionOne hU, hR.toScRetractionOne_retract hU⟩

/-- The base `O = p(K)` of a local strong bundle retract. -/
def base (K : Set (E 0 × F 0)) : Set (E 0) := Prod.fst '' K

/-- `O = p(K)` is the retract `r(U)` of the base retraction. -/
lemma base_eq {U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0} (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) :
    base (R '' (U ×ˢ univ)) = (hR.baseRetraction hU).retract := by
  ext u
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ((hR.mem_image_iff hU).1 hp).1
  · intro hu
    have huU : u ∈ U := (hR.baseRetraction hU).retract_subset hu
    refine ⟨R (u, 0), ⟨_, ⟨huU, mem_univ _⟩, rfl⟩, ?_⟩
    rw [hR.apply_fst huU]
    exact (hR.baseRetraction hU).apply_eq_self_of_mem_retract hu

/-- **Lemma 5.B**: the projection `p : K[0] → O` is sc-smooth. -/
theorem isScSmoothRetractMap_fst (hK : IsStrongBundleRetract C K) :
    IsScSmoothRetractMap (E.prod F) (C ×ˢ univ) K E C (base K) Prod.fst := by
  rw [isScSmoothRetractMap_iff_exists hK.isScRetract]
  obtain ⟨U, R, hU, hR, rfl⟩ := hK
  refine ⟨fun p hp => ⟨p, hp, rfl⟩, hR.toScRetraction hU, rfl, ?_⟩
  exact IsScSmooth.comp (hU.prod_univ F).isScDomain (isScDomain_univ _)
    ((E.prodFstOp F).isScSmooth (isScDomain_univ _)) hR.isScSmooth_zero (mapsTo_univ _ _)

/-- **Lemma 5.B**: the projection `p : K[1] → O` is sc-smooth. -/
theorem isScSmoothRetractMap_fst_one (hK : IsStrongBundleRetract C K) :
    IsScSmoothRetractMap (E.prod F.shift) (C ×ˢ univ) (strongShiftOne K) E C (base K) Prod.fst := by
  rw [isScSmoothRetractMap_iff_exists hK.isScRetract_one]
  obtain ⟨U, R, hU, hR, rfl⟩ := hK
  refine ⟨fun p hp => ⟨_, hp, rfl⟩, hR.toScRetractionOne hU, hR.toScRetractionOne_retract hU, ?_⟩
  exact IsScSmooth.comp (hU.prod_univ F.shift).isScDomain (isScDomain_univ _)
    ((E.prodFstOp F.shift).isScSmooth (isScDomain_univ _)) hR.isScSmooth_one (mapsTo_univ _ _)

/-- The inclusion `K[1] → K[0]`, `(u, h) ↦ (u, h)` (`h ∈ F₁ ⊆ F₀`), is sc-smooth. -/
theorem isScSmoothRetractMap_shiftIncl (hK : IsStrongBundleRetract C K) :
    IsScSmoothRetractMap (E.prod F.shift) (C ×ˢ univ) (strongShiftOne K) (E.prod F) (C ×ˢ univ) K
      (E.prodShiftInclOp F 0) := by
  rw [isScSmoothRetractMap_iff_exists hK.isScRetract_one]
  obtain ⟨U, R, hU, hR, rfl⟩ := hK
  refine ⟨fun p hp => hp, hR.toScRetractionOne hU, hR.toScRetractionOne_retract hU, ?_⟩
  exact IsScSmooth.comp (hU.prod_univ F.shift).isScDomain (isScDomain_univ _)
    ((E.prodShiftInclOp F).isScSmooth (isScDomain_univ _)) hR.isScSmooth_one (mapsTo_univ _ _)

end IsStrongBundleRetract

/-- An **sc⁺-section is an sc-smooth section** (the remark after Definition 2.6.3 (preprint 2.49)): composing with
`K[1] → K[0]`. -/
theorem IsScPlusSection.isScSmoothSection {C O : Set (E 0)} {K : Set (E 0 × F 0)}
    (hK : IsStrongBundleRetract C K) {f : E 0 → E 0 × F 1}
    (hf : IsScPlusSection C O K f) :
    IsScSmoothSection C O K (fun x => ((f x).1, F.toBase 1 (f x).2)) where
  fst_eq x hx := hf.fst_eq x hx
  isScSmooth := hK.isScSmoothRetractMap_shiftIncl.comp hf.isScSmooth hK.isScRetract_one

/-! ### The pulled-back strong bundle retraction (the local content of Proposition 2.6.8 (preprint 2.54)) -/

section Pullback

variable {E' : ScBanach} {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0} {C' : Set (E' 0)}

/-- The pulled-back strong bundle retraction `R_g(w, h) = (r'(w), Γ(g(r'(w)), h))` on `U' ◁ F`, for
a retraction `r' : U' → U'` and a map `g : O' → O` (exposition, proof of Proposition 2.6.8 (preprint 2.54)). -/
def pullbackRetraction (R : E 0 × F 0 → E 0 × F 0) (R' : ScRetraction E' C') (g : E' 0 → E 0) :
    E' 0 × F 0 → E' 0 × F 0 :=
  fun p => (R' p.1, (R (g (R' p.1), p.2)).2)

variable (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
  (R' : ScRetraction E' C') {g : E' 0 → E 0}
  (hg : IsScSmoothRetractMap E' C' R'.retract E C (hR.baseRetraction hU).retract g)

include hg in
lemma pullback_mem_O {w : E' 0} (hw : w ∈ R'.U) : g (R' w) ∈ (hR.baseRetraction hU).retract :=
  hg.mapsTo (R'.apply_mem_retract hw)

include hg in
lemma pullback_mem_U {w : E' 0} (hw : w ∈ R'.U) : g (R' w) ∈ U :=
  (hR.baseRetraction hU).retract_subset (pullback_mem_O hU hR R' hg hw)

include hg in
/-- **Proposition 2.6.8 (preprint 2.54)**, the local construction: `R_g` is a strong bundle retraction on
`U' ◁ F` (it preserves the double filtration, is linear in the fibre, sc-smooth on `[0]` and
`[1]`, and `R_g ∘ R_g = R_g` because `Γ(o, ·)` is a projection for `o ∈ O`). -/
theorem isStrongBundleRetraction_pullback :
    IsStrongBundleRetraction R'.U (pullbackRetraction R R' g) where
  mapsTo p hp := ⟨R'.mapsTo hp.1, mem_univ _⟩
  fst_independent _ _ _ _ := rfl
  fiber_linear w hw := hR.fiber_linear _ (pullback_mem_U hU hR R' hg hw)
  preserves_filtration m k hk w hw hwm h hh := by
    obtain ⟨w₀, rfl⟩ := hwm
    have hw₀ : w₀ ∈ E'.lvlSet R'.U m := hw
    refine ⟨R'.isSc1.isSc0.mem_range m w₀ hw₀, ?_⟩
    have hgr := (hg.comp_isScSmooth R' rfl).isSc1.isSc0.mem_range m w₀ hw₀
    exact (hR.preserves_filtration m k hk _ (pullback_mem_U hU hR R' hg hw) hgr h hh).2
  isScSmooth_zero := by
    have hUF := (R'.relOpen.prod_univ F).isScDomain
    have hfst : IsScSmooth (E := E'.prod F) (F := E') (R'.U ×ˢ univ) Prod.fst :=
      (E'.prodFstOp F).isScSmooth hUF
    have hsnd : IsScSmooth (E := E'.prod F) (F := F) (R'.U ×ˢ univ) Prod.snd :=
      (E'.prodSndOp F).isScSmooth hUF
    have h1 : IsScSmooth (E := E'.prod F) (F := E') (R'.U ×ˢ univ) (R' ∘ Prod.fst) :=
      IsScSmooth.comp hUF R'.isScDomain R'.isScSmooth hfst fun p hp => hp.1
    have h2 : IsScSmooth (E := E'.prod F) (F := E) (R'.U ×ˢ univ) ((g ∘ R') ∘ Prod.fst) :=
      IsScSmooth.comp hUF R'.isScDomain (hg.comp_isScSmooth R' rfl) hfst fun p hp => hp.1
    have h3 : IsScSmooth (E := E'.prod F) (F := E.prod F) (R'.U ×ˢ univ)
        (R ∘ scPair ((g ∘ R') ∘ Prod.fst) Prod.snd) :=
      IsScSmooth.comp (G := E.prod F) hUF (hU.prod_univ F).isScDomain hR.isScSmooth_zero
        (IsScSmooth.scPair hUF h2 hsnd) fun p hp =>
          show (g (R' p.1), p.2) ∈ U ×ˢ univ from ⟨pullback_mem_U hU hR R' hg hp.1, mem_univ _⟩
    have h4 : IsScSmooth (E := E'.prod F) (F := F) (R'.U ×ˢ univ)
        (Prod.snd ∘ R ∘ scPair ((g ∘ R') ∘ Prod.fst) Prod.snd) :=
      IsScSmooth.comp hUF (isScDomain_univ _) ((E.prodSndOp F).isScSmooth (isScDomain_univ _)) h3
        (mapsTo_univ _ _)
    exact IsScSmooth.scPair hUF h1 h4
  isScSmooth_one := by
    have hUF := (R'.relOpen.prod_univ F.shift).isScDomain
    have hfst : IsScSmooth (E := E'.prod F.shift) (F := E') (R'.U ×ˢ univ) Prod.fst :=
      (E'.prodFstOp F.shift).isScSmooth hUF
    have hsnd : IsScSmooth (E := E'.prod F.shift) (F := F.shift) (R'.U ×ˢ univ) Prod.snd :=
      (E'.prodSndOp F.shift).isScSmooth hUF
    have h1 : IsScSmooth (E := E'.prod F.shift) (F := E') (R'.U ×ˢ univ) (R' ∘ Prod.fst) :=
      IsScSmooth.comp hUF R'.isScDomain R'.isScSmooth hfst fun p hp => hp.1
    have h2 : IsScSmooth (E := E'.prod F.shift) (F := E) (R'.U ×ˢ univ) ((g ∘ R') ∘ Prod.fst) :=
      IsScSmooth.comp hUF R'.isScDomain (hg.comp_isScSmooth R' rfl) hfst fun p hp => hp.1
    have h3 : IsScSmooth (E := E'.prod F.shift) (F := E.prod F.shift) (R'.U ×ˢ univ)
        (shiftFiber R ∘ scPair ((g ∘ R') ∘ Prod.fst) Prod.snd) :=
      IsScSmooth.comp (G := E.prod F.shift) hUF (hU.prod_univ F.shift).isScDomain hR.isScSmooth_one
        (IsScSmooth.scPair hUF h2 hsnd) fun p hp =>
          show (g (R' p.1), p.2) ∈ U ×ˢ univ from ⟨pullback_mem_U hU hR R' hg hp.1, mem_univ _⟩
    have h4 : IsScSmooth (E := E'.prod F.shift) (F := F.shift) (R'.U ×ˢ univ)
        (Prod.snd ∘ shiftFiber R ∘ scPair ((g ∘ R') ∘ Prod.fst) Prod.snd) :=
      IsScSmooth.comp hUF (isScDomain_univ _)
        ((E.prodSndOp F.shift).isScSmooth (isScDomain_univ _)) h3 (mapsTo_univ _ _)
    exact IsScSmooth.scPair hUF h1 h4
  idem p hp := by
    have ho := pullback_mem_O hU hR R' hg hp.1
    change (R' (R' p.1), (R (g (R' (R' p.1)), (R (g (R' p.1), p.2)).2)).2) =
      (R' p.1, (R (g (R' p.1), p.2)).2)
    rw [R'.idem _ hp.1, hR.fiber_idem hU ho]

include hg in
/-- **Proposition 2.6.8 (preprint 2.54)**, the local construction: the image of `R_g` is
`K_g = {(w, h) | w ∈ O', (g(w), h) ∈ K}`, the pull-back of `K` along `g`. -/
theorem pullback_image :
    pullbackRetraction R R' g '' (R'.U ×ˢ univ) =
      {p | p.1 ∈ R'.retract ∧ (g p.1, p.2) ∈ R '' (U ×ˢ univ)} := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    have ho := pullback_mem_O hU hR R' hg hq.1
    refine ⟨R'.apply_mem_retract hq.1, ?_⟩
    have hoU := (hR.baseRetraction hU).retract_subset ho
    refine ⟨(g (R' q.1), q.2), ⟨hoU, mem_univ _⟩, Prod.ext ?_ rfl⟩
    rw [hR.apply_fst hoU]
    exact (hR.baseRetraction hU).apply_eq_self_of_mem_retract ho
  · rintro ⟨hp1, hp2⟩
    refine ⟨p, ⟨R'.retract_subset hp1, mem_univ _⟩, ?_⟩
    have hfix := ((hR.mem_image_iff hU).1 hp2).2
    change (R' p.1, (R (g (R' p.1), p.2)).2) = p
    rw [R'.apply_eq_self_of_mem_retract hp1]
    exact Prod.ext rfl hfix

include hg in
/-- The pull-back `K_g` is a local strong bundle retract. -/
theorem isStrongBundleRetract_pullback :
    IsStrongBundleRetract C'
      {p : E' 0 × F 0 | p.1 ∈ R'.retract ∧ (g p.1, p.2) ∈ R '' (U ×ˢ univ)} :=
  ⟨R'.U, pullbackRetraction R R' g, R'.relOpen, isStrongBundleRetraction_pullback hU hR R' hg,
    (pullback_image hU hR R' hg).symm⟩

end Pullback

/-! ### Strong bundles over M-polyfolds (Definitions 2.6.4–2.6.7 (preprint 2.50–2.53)) -/

/-- A topological vector space is **Banachable** if it is linearly homeomorphic to a Banach space
(its topology comes from a complete norm). -/
def IsBanachable (V : Type*) [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] : Prop :=
  ∃ (B : Type) (_ : NormedAddCommGroup B) (_ : NormedSpace ℝ B) (_ : CompleteSpace B),
    Nonempty (V ≃L[ℝ] B)

universe u v

section StrongBundleDefs

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
  {Y : Type v} [TopologicalSpace Y] (P : Y → X)
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- **Definition 2.6.4 (preprint 2.50)**: a **strong bundle chart** `(Φ, P⁻¹(V), K, U ◁ F)` for `P : Y → X`: a chart
`φ : V → O` of `X`, a strong bundle retraction `R(u, h) = (r(u), Γ(u, h))` on `U ◁ F` with
`r(U) = O` and image `K = R(U ◁ F)`, and a homeomorphism `Φ : P⁻¹(V) → K` covering `φ`
(`p ∘ Φ = φ ∘ P`) which is linear on the fibres `P⁻¹(x) → p⁻¹(φ(x))` (bounded, since `Φ` is a
homeomorphism: `StrongBundleChart.continuous_fiber`). -/
structure StrongBundleChart where
  /-- The chart `φ : V → O` of the base. -/
  φ : MChart X
  isChart : PX.IsChart φ
  /-- The fibre model `F`. -/
  F : ScBanach
  /-- The domain `U ⊆ C` of the strong bundle retraction. -/
  U : Set (φ.model.E 0)
  /-- The strong bundle retraction `R : U ◁ F → U ◁ F`. -/
  R : φ.model.E 0 × F 0 → φ.model.E 0 × F 0
  relOpen : IsRelOpenInQuadrant φ.model.E φ.model.C U
  isRetraction : IsStrongBundleRetraction U R
  base_retract : (isRetraction.baseRetraction relOpen).retract = φ.model.O
  /-- The bundle chart `Φ : P⁻¹(V) → K`. -/
  toPartialEquiv : PartialEquiv Y (φ.model.E 0 × F 0)
  source_eq : toPartialEquiv.source = P ⁻¹' φ.source
  target_eq : toPartialEquiv.target = R '' (U ×ˢ univ)
  continuousOn_toFun : ContinuousOn toPartialEquiv toPartialEquiv.source
  continuousOn_invFun : ContinuousOn toPartialEquiv.symm toPartialEquiv.target
  covers : ∀ y ∈ toPartialEquiv.source, (toPartialEquiv y).1 = φ (P y)
  fiber_linear : ∀ x ∈ φ.source, IsLinearMap ℝ fun v : P ⁻¹' {x} => (toPartialEquiv v).2

namespace StrongBundleChart

variable {PX P} (c : StrongBundleChart PX P)

instance : CoeFun (StrongBundleChart PX P) (fun c => Y → c.φ.model.E 0 × c.F 0) :=
  ⟨fun c => c.toPartialEquiv⟩

/-- The local strong bundle retract `K = R(U ◁ F)` of the chart. -/
def K : Set (c.φ.model.E 0 × c.F 0) := c.R '' (c.U ×ˢ univ)

lemma isStrongBundleRetract : IsStrongBundleRetract c.φ.model.C c.K :=
  ⟨c.U, c.R, c.relOpen, c.isRetraction, rfl⟩

lemma isScRetract : IsScRetract (c.φ.model.E.prod c.F) (c.φ.model.C ×ˢ univ) c.K :=
  c.isStrongBundleRetract.isScRetract

lemma isScRetract_one :
    IsScRetract (c.φ.model.E.prod c.F.shift) (c.φ.model.C ×ˢ univ) (strongShiftOne c.K) :=
  c.isStrongBundleRetract.isScRetract_one

/-- The local model `(K, C ◁ F, E ◁ F)` of `Y[0]`. -/
def model : LocalModel := ⟨c.φ.model.E.prod c.F, c.φ.model.C ×ˢ univ, c.K, c.isScRetract⟩

/-- The source `P⁻¹(V)` of a strong bundle chart is open. -/
lemma isOpen_source (hP : Continuous P) : IsOpen c.toPartialEquiv.source := by
  rw [c.source_eq]; exact c.φ.isOpen_source.preimage hP

/-- The chart `Φ : P⁻¹(V) → K` as a chart of the M-polyfold `Y[0]`. -/
def toMChart (hP : Continuous P) : MChart Y where
  model := c.model
  toPartialEquiv := c.toPartialEquiv
  isOpen_source := c.isOpen_source hP
  target_eq := c.target_eq
  continuousOn_toFun := c.continuousOn_toFun
  continuousOn_invFun := by
    have := c.continuousOn_invFun
    rwa [c.target_eq] at this

/-- The fibre maps of a strong bundle chart are continuous (bounded): `Φ` is a homeomorphism. -/
lemma continuous_fiber (x : X) (hx : x ∈ c.φ.source) :
    Continuous fun v : P ⁻¹' {x} => (c v).2 := by
  have hsub : ∀ v : P ⁻¹' {x}, (v : Y) ∈ c.toPartialEquiv.source := fun v => by
    rw [c.source_eq, mem_preimage, show P v = x from v.2]; exact hx
  have := (c.continuousOn_toFun.comp_continuous continuous_subtype_val hsub)
  exact continuous_snd.comp this

/-- The overlap `Φ(P⁻¹(V ∩ V'))`. -/
def overlap (c' : StrongBundleChart PX P) : Set (c.φ.model.E 0 × c.F 0) :=
  c.toPartialEquiv '' (c.toPartialEquiv.source ∩ c'.toPartialEquiv.source)

/-- The transition map `Φ' ∘ Φ⁻¹`. -/
def transition (c' : StrongBundleChart PX P) : c.φ.model.E 0 × c.F 0 → c'.φ.model.E 0 × c'.F 0 :=
  c'.toPartialEquiv ∘ c.toPartialEquiv.symm

/-- **Definition 2.6.4 (preprint 2.50)**: two strong bundle charts are **compatible** if the transition maps
`(Φ' ∘ Φ⁻¹)[i] : Φ(P⁻¹(V ∩ V'))[i] → Φ'(P⁻¹(V ∩ V'))[i]` are sc-smooth (hence, with the reverse
transition, sc-diffeomorphisms) for `i = 0, 1`.  For `(Φ' ∘ Φ⁻¹)[1]` to be the restriction of
`Φ' ∘ Φ⁻¹` to `K[1]`, the transition must map points with fibre component in `F₁` to points with
fibre component in `F'₁` (the last two conditions; implicit in the text). -/
def Compatible (c' : StrongBundleChart PX P) : Prop :=
  IsScSmoothRetractMap (c.φ.model.E.prod c.F) (c.φ.model.C ×ˢ univ) (c.overlap c')
      (c'.φ.model.E.prod c'.F) (c'.φ.model.C ×ˢ univ) (c'.overlap c) (c.transition c') ∧
    IsScSmoothRetractMap (c'.φ.model.E.prod c'.F) (c'.φ.model.C ×ˢ univ) (c'.overlap c)
      (c.φ.model.E.prod c.F) (c.φ.model.C ×ˢ univ) (c.overlap c') (c'.transition c) ∧
    IsScSmoothRetractMap (c.φ.model.E.prod c.F.shift) (c.φ.model.C ×ˢ univ)
      (strongShiftOne (c.overlap c')) (c'.φ.model.E.prod c'.F.shift) (c'.φ.model.C ×ˢ univ)
      (strongShiftOne (c'.overlap c)) (shiftFiber (c.transition c')) ∧
    IsScSmoothRetractMap (c'.φ.model.E.prod c'.F.shift) (c'.φ.model.C ×ˢ univ)
      (strongShiftOne (c'.overlap c)) (c.φ.model.E.prod c.F.shift) (c.φ.model.C ×ˢ univ)
      (strongShiftOne (c.overlap c')) (shiftFiber (c'.transition c)) ∧
    (∀ x ∈ c.overlap c', x.2 ∈ range (c.F.toBase 1) →
      (c.transition c' x).2 ∈ range (c'.F.toBase 1)) ∧
    (∀ x ∈ c'.overlap c, x.2 ∈ range (c'.F.toBase 1) →
      (c'.transition c x).2 ∈ range (c.F.toBase 1))

lemma Compatible.symm {c c' : StrongBundleChart PX P} (h : c.Compatible c') : c'.Compatible c :=
  ⟨h.2.1, h.1, h.2.2.2.1, h.2.2.1, h.2.2.2.2.2, h.2.2.2.2.1⟩

/-- Compatibility of strong bundle charts on `[0]` is the compatibility of the charts of `Y[0]`. -/
lemma Compatible.toMChart {c c' : StrongBundleChart PX P} (h : c.Compatible c')
    (hP : Continuous P) : (c.toMChart hP).Compatible (c'.toMChart hP) :=
  ⟨h.1, h.2.1⟩

/-- The image `Φ(P⁻¹(V))` of a strong bundle chart is `K`. -/
lemma image_source :
    c.toPartialEquiv '' c.toPartialEquiv.source = c.K := by
  rw [c.toPartialEquiv.image_source_eq_target, c.target_eq]; rfl

/-- The projection `p : K → O` of a strong bundle chart is the base `O` of `K`. -/
lemma base_K :
    IsStrongBundleRetract.base c.K = c.φ.model.O := by
  rw [StrongBundleChart.K, IsStrongBundleRetract.base_eq c.relOpen c.isRetraction, c.base_retract]

end StrongBundleChart

/-- **Definition 2.6.4 (preprint 2.50)**: a **strong bundle atlas**: pairwise compatible strong bundle charts whose
domains cover `Y`; two atlases are equivalent if their union is an atlas. -/
structure StrongBundleAtlas where
  charts : Set (StrongBundleChart PX P)
  compatible : ∀ c ∈ charts, ∀ c' ∈ charts, c.Compatible c'
  cover : ∀ y : Y, ∃ c ∈ charts, y ∈ c.toPartialEquiv.source

variable {PX P} in
/-- Equivalence of strong bundle atlases: their union is an atlas. -/
def StrongBundleAtlas.Equiv (A B : StrongBundleAtlas PX P) : Prop :=
  ∃ D : StrongBundleAtlas PX P, D.charts = A.charts ∪ B.charts

/-- **Definition 2.6.5 (preprint 2.51)**: a **strong bundle** over the M-polyfold `X`: a continuous surjection
`P : Y → X` from a paracompact Hausdorff space, with Banachable fibres, equipped with (an
equivalence class of, represented by) a strong bundle atlas. -/
structure StrongBundle [T2Space Y] [ParacompactSpace Y] where
  continuous : Continuous P
  surjective : Surjective P
  banachable : ∀ x, IsBanachable (P ⁻¹' {x})
  atlas : StrongBundleAtlas PX P

/-- **Definition 2.6.6 (preprint 2.52)**: a **section** of `P : Y → X` is a map `f : X → Y` with `P ∘ f = 1_X`. -/
def IsSection (f : X → Y) : Prop := ∀ x, P (f x) = x

namespace StrongBundle

variable {PX P} [T2Space Y] [ParacompactSpace Y] (B : StrongBundle PX P)

/-- The sc-smooth atlas of `Y[0]`: the charts `Φ : P⁻¹(V) → K`. -/
def atlas0 : MAtlas Y where
  charts := (fun c => c.toMChart B.continuous) '' B.atlas.charts
  compatible := by
    rintro _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩
    exact (B.atlas.compatible c hc c' hc').toMChart B.continuous
  cover y := by
    obtain ⟨c, hc, hy⟩ := B.atlas.cover y
    exact ⟨_, ⟨c, hc, rfl⟩, hy⟩

/-- The M-polyfold `Y[0]` (after Definition 2.6.5 (preprint 2.51)), with the charts `Φ : P⁻¹(V) → K = K[0]`. -/
def toMPolyfold0 : MPolyfold Y := ⟨B.atlas0⟩

lemma isChart_toMChart {c : StrongBundleChart PX P} (hc : c ∈ B.atlas.charts) :
    B.toMPolyfold0.IsChart (c.toMChart B.continuous) :=
  B.toMPolyfold0.isChart_of_mem ⟨c, hc, rfl⟩

/-- **After Definition 2.6.5 (preprint 2.51)**: the projection `P[0] : Y[0] → X` is sc-smooth; in the charts `Φ`
and `φ` it is the projection `p : K → O` (Lemma 5.B). -/
theorem isScSmoothMap_proj : B.toMPolyfold0.IsScSmoothMap PX P := by
  refine MPolyfold.IsScSmoothOn.of_exists_charts isOpen_univ B.continuous.continuousOn
    fun y _ => ?_
  obtain ⟨c, hc, hy⟩ := B.atlas.cover y
  refine ⟨c.toMChart B.continuous, c.φ, c.toPartialEquiv.source, B.isChart_toMChart hc, c.isChart,
    c.isOpen_source B.continuous, hy, fun z hz => ⟨mem_univ _, hz⟩, fun z hz => ?_, ?_⟩
  · rw [c.source_eq] at hz; exact hz
  · have h1 := c.isStrongBundleRetract.isScSmoothRetractMap_fst
    rw [c.base_K] at h1
    change IsScSmoothRetractMap (c.φ.model.E.prod c.F) (c.φ.model.C ×ˢ univ)
      (c.toPartialEquiv '' c.toPartialEquiv.source) c.φ.model.E c.φ.model.C c.φ.model.O
      (c.φ ∘ P ∘ c.toPartialEquiv.symm)
    rw [c.image_source]
    refine h1.congr fun k hk => ?_
    have hk' : k ∈ c.toPartialEquiv.target := by rw [c.target_eq]; exact hk
    have hs := c.toPartialEquiv.map_target hk'
    have := c.covers _ hs
    rw [c.toPartialEquiv.right_inv hk'] at this
    exact this

/-- The double filtration `Y_{m,k}` (after Definition 2.6.5 (preprint 2.51)), `0 ≤ k ≤ m + 1`: `y ∈ Y_{m,k}` if
`Φ(y) ∈ K_{m,k} = K ∩ (E_m ⊕ F_k)` in the charts of the atlas around `y`. -/
def doubleLevel (m k : ℕ) : Set Y :=
  {y | ∀ c ∈ B.atlas.charts, y ∈ c.toPartialEquiv.source →
    (c y).1 ∈ range (c.φ.model.E.toBase m) ∧ (c y).2 ∈ range (c.F.toBase k)}

/-- **Definition 2.6.6 (preprint 2.52)**: an **sc-smooth section** is a section which is sc-smooth as a map into the
M-polyfold `Y[0]` (Definition 2.3.8 (preprint 2.14)). -/
def IsScSmoothSection (f : X → Y) : Prop :=
  IsSection P f ∧ PX.IsScSmoothMap B.toMPolyfold0 f

/-- The local representative `z ↦ Φ(f(φ⁻¹ z))[1] ∈ K[1]` of a section in a strong bundle chart: the
fibre component is lifted to `F₁`. -/
def localRepOne (c : StrongBundleChart PX P) (f : X → Y) :
    c.φ.model.E 0 → (c.φ.model.E.prod c.F.shift) 0 :=
  fun z => ((c (f (c.φ.symm z))).1, Function.invFun (c.F.toBase 1) (c (f (c.φ.symm z))).2)

/-- **Definition 2.6.6 (preprint 2.52)**: an **sc⁺-section** is a section which is sc-smooth as a map into `Y[1]`:
in every strong bundle chart its principal part takes values in `F₁` and its representative
`O → K[1]` (the chart `Φ[1]` of `Y[1]`) is sc-smooth. -/
def IsScPlusSection (f : X → Y) : Prop :=
  IsSection P f ∧ ∀ c ∈ B.atlas.charts,
    (∀ x ∈ c.φ.source, (c (f x)).2 ∈ range (c.F.toBase 1)) ∧
    IsScSmoothRetractMap c.φ.model.E c.φ.model.C c.φ.model.O (c.φ.model.E.prod c.F.shift)
      (c.φ.model.C ×ˢ univ) (strongShiftOne c.K) (localRepOne c f)

end StrongBundle

end StrongBundleDefs

/-- **Definition 2.6.7 (preprint 2.53)**: the **pull-back** `f*Y = {(z, y) ∈ Z × Y | P(y) = f(z)}` of `P : Y → X`
along `f : Z → X`, with `P_f(z, y) = z` and `P'(z, y) = y`, so that `P ∘ P' = f ∘ P_f`. -/
def pullbackSpace {X Y Z : Type*} (P : Y → X) (f : Z → X) : Set (Z × Y) :=
  {p | P p.2 = f p.1}

/-- The projection `P_f : f*Y → Z`. -/
def pullbackProj {X Y Z : Type*} (P : Y → X) (f : Z → X) : pullbackSpace P f → Z := fun p => p.1.1

/-- The projection `P' : f*Y → Y`. -/
def pullbackProj' {X Y Z : Type*} (P : Y → X) (f : Z → X) : pullbackSpace P f → Y := fun p => p.1.2

/-- The square of Definition 2.6.7 (preprint 2.53) commutes: `P ∘ P' = f ∘ P_f`. -/
theorem pullback_comm {X Y Z : Type*} (P : Y → X) (f : Z → X) :
    P ∘ pullbackProj' P f = f ∘ pullbackProj P f := funext fun p => p.2

lemma continuous_pullbackProj {X Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (P : Y → X) (f : Z → X) : Continuous (pullbackProj P f) :=
  continuous_fst.comp continuous_subtype_val

/-- `f*Y` is closed in `Z × Y` (`X` Hausdorff, `P`, `f` continuous). -/
lemma isClosed_pullbackSpace {X Y Z : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
    [TopologicalSpace Z] {P : Y → X} {f : Z → X} (hP : Continuous P) (hf : Continuous f) :
    IsClosed (pullbackSpace P f) :=
  isClosed_eq (hP.comp continuous_snd) (hf.comp continuous_fst)

end Polyfold
