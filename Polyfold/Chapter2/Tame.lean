import Polyfold.Chapter2.DegeneracyIndex

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §2.4,
Definitions 2.5.1, 2.5.2, 2.5.7, 2.5.8, 2.5.10 (preprint 2.33, 2.34, 2.37, 2.38, 2.39), and §2.5, the non-symmetric product `U ◁ F`,
Definitions 2.6.1, 2.6.2, 2.6.3 (preprint 2.47, 2.48, 2.49): **definitions only**.

# Tame retractions and tame M-polyfolds; strong bundle retractions (definitions)

## The text, paraphrased

(§2.4) For `E = ℝᵏ ⊕ W`, `C = [0,∞)ᵏ ⊕ W`, `E_i = {a_i = 0}`, `H_i = {a_i ≥ 0}`; for `e ∈ C`,
`C_e = ⋂_{i ∈ I(e)} H_i` is the partial quadrant and `E_e = ⋂_{i ∈ I(e)} E_i` the minimal linear
subspace associated with `e` (Definition 2.5.1 (preprint 2.33)).  (Definition 2.5.2 (preprint 2.34)) An sc-smooth retraction
`r : U → U` is tame if (1) `d_C(r(x)) = d_C(x)` for all `x ∈ U` and (2) at every smooth point
`x ∈ O = r(U)` there is an sc-subspace `A ⊆ E_x` with `E = T_xO ⊕ A`; a tame retract is the image
of a tame retraction.  (Proposition 2.5.3 (preprint 2.35)) one can take `A = (1 − Dr(x))E`.  (Proposition 2.5.6 (preprint 2.36))
For a tame retract, `dim(T_xO / T_x^R O) = d_O(x)` at smooth points and `d_O = d_C` on `O`.
(Definition 2.5.7 (preprint 2.37)) A tame M-polyfold has an equivalent atlas whose charts are modelled on tame
retracts.  (Definition 2.5.8 (preprint 2.38)) The reduced tangent space `T_x^R X` and the partial cone `C_xX` of an
M-polyfold at a smooth point, defined through a chart.  (Definition 2.5.10 (preprint 2.39)) A face of a tame
M-polyfold is the closure of a connected component of `{d_X = 1}`; `X` is face-structured if every
`x` lies in exactly `d_X(x)` faces.  (§2.5) `U ◁ F` is `U × F` with the double filtration
`(U ◁ F)_{m,k} = U_m ⊕ F_k`, `0 ≤ k ≤ m + 1`, and `(U ◁ F)[i]`, `i = 0, 1`, has the filtration
`U_m ⊕ F_{m+i}`.  (Definition 2.6.1 (preprint 2.47)) A strong bundle map `Φ : U ◁ F → U' ◁ F'` preserves the double
filtration, has the form `Φ(u, h) = (φ(u), Γ(u, h))` with `Γ` linear in `h`, and is sc-smooth
`(U ◁ F)[i] → (U' ◁ F')[i]` for `i = 0, 1`; a strong bundle retraction is one with `R ∘ R = R`.
(Definition 2.6.2 (preprint 2.48)) A local strong bundle retract is `K = R(U ◁ F)` with `p : K → O`, and
`K_{m,k} = K ∩ (U_m ⊕ F_k)`, `K[i]_m = K_{m,m+i}`.  (Definition 2.6.3 (preprint 2.49)) A section `f : O → K`
(`p ∘ f = 1`) is sc-smooth if it is sc-smooth into `K[0]`, sc⁺ if sc-smooth into `K[1]`.

## What is formalized (definitions, with the lemmas that make them well formed)

* `Polyfold.partialQuadrantAtWith T e` (`C_e`) and `minimalSubspaceWith T e` (`E_e`, from
  `DegeneracyIndex.lean`), **Definition 2.5.1 (preprint 2.33)**, for a presentation `T` of `C`; `E_e ⊆ C_e`.
* `Polyfold.ScRetraction.IsTameWith T` and `ScRetraction.IsTame` (**Definition 2.5.2 (preprint 2.34)**, over all
  presentations of `C`), `Polyfold.IsTameRetract`.
* `Polyfold.reducedTangentSpaceWith` (`T_x^R O = T_xO ∩ E_x`) and `Polyfold.partialConeWith`
  (`C_xO = T_xO ∩ C_x`) for a retraction and `x ∈ O₁` (**Definition 2.4.7 (preprint 2.27)/2.38**, local form).
* `Polyfold.MPolyfold.IsTame` (**Definition 2.5.7 (preprint 2.37)**), `MPolyfold.IsFace`, `MPolyfold.IsFaceStructured`
  (**Definition 2.5.10 (preprint 2.39)**).
* `Polyfold.doubleLevel U F m k` (`(U ◁ F)_{m,k}`), `Polyfold.shiftFiber Φ` (the map induced by
  `Φ` on `(U ◁ F)[1]`), `Polyfold.IsStrongBundleMap` (**Definition 2.6.1 (preprint 2.47)**),
  `Polyfold.IsStrongBundleRetraction`, `Polyfold.IsStrongBundleRetract` (**Definition 2.6.2 (preprint 2.48)**) with
  `strongLevel K m k` (`K_{m,k}`), and `Polyfold.IsScSmoothSection`, `Polyfold.IsScPlusSection`
  (**Definition 2.6.3 (preprint 2.49)**).

## What the text leaves implicit, and the choices made

* `E_e`, `C_e` are defined through a presentation `T : E ≅ ℝᵏ ⊕ W`; the text defines them
  intrinsically through the extended faces (the connected components of `{d_C = 1}`) and asserts
  the agreement.  `IsTame` quantifies over all presentations; independence of `T` (the argument
  of Lemma 1.3.4 (preprint 1.24), `S(E_x) = E'_{S x}`) is proved in `TameFaces.lean`: `minimalSubspaceWith_eq`
  (`E_x` does not depend on `T`) and `ScRetraction.IsTameWith.isTame` (tameness for one
  presentation implies `IsTame`).  The intrinsic description through extended faces is not
  formalized (gap G.12 of the report).
* "Smooth point `x ∈ O`" in Definition 2.5.2 (preprint 2.34) (2) is `x : E 1` with `ι₁ x ∈ O` and `x ∈ E_∞`; the
  tangent space `T_xO = Dr(x)E` is `LinearMap.range (scDeriv U r x)`, and "`E = T_xO ⊕ A` with `A`
  an sc-subspace" is `ScBanach.IsScSplitting`, which asks both summands to be sc-subspaces (as the
  text's `E = T_xO ⊕ A` must, for `A` to be an sc-complement).
* Definition 2.6.1 (preprint 2.47)'s "preserves the double filtration" is read as: `Φ` maps `U_m ⊕ F_k` into
  `U'_m ⊕ F'_k` for `k ≤ m + 1`.  Sc-smoothness of `Φ : (U ◁ F)[1] → (U' ◁ F')[1]` is
  sc-smoothness of the induced map `shiftFiber Φ : U ⊕ F₁ → U' ⊕ F'₁` with respect to the
  sc-structures `E ⊕ F¹`, `E' ⊕ F'¹`.
* That `U ⊕ F` is relatively open in the partial quadrant `C ⊕ F` of `E ⊕ F` (so that strong
  bundle retractions are sc-smooth retractions in the sense of §2.1 and `K[i]` are retracts) needs
  an sc-isomorphism `E ⊕ F ≅ ℝⁿ ⊕ (W ⊕ F)`; it is `prodQuadrantIso`, with
  `IsRelOpenInQuadrant.prod_univ`, in `StrongBundle.lean`, where `K[0]` and `K[1]` are also proved
  to be sc-smooth retracts (`IsStrongBundleRetract.isScRetract`, `isScRetract_one`).  The section
  notions here are stated with `IsScSmoothRetractMap`, whose quantifier over the retractions onto
  `K[i]` is therefore not vacuous.
* The statements of §2.4–§2.5 are proved in later files: Propositions 2.5.3, 2.5.6 (preprint 2.35, 2.36) (13)–(14),
  Lemma 2.5.12 (preprint 2.40), Corollary 2.5.13 (preprint 2.41), Propositions 2.5.14, 2.5.15 (preprint 2.42, 2.43) and the interior part of Theorem 2.5.17 (preprint 2.45) in
  `TameRetracts.lean`; Proposition 2.5.6 (preprint 2.36) (`C_xO` a partial quadrant) in `PartialCone.lean`; the
  tameness in Proposition 2.5.15 (preprint 2.43), Proposition 2.5.16 (preprint 2.44) (first sentence) and the rest of Theorem 2.5.17 (preprint 2.45) in
  `TameFaces.lean`; Proposition 2.5.16 (preprint 2.44) (second sentence) in `CornerGerms.lean`; Proposition 2.5.20 (preprint 2.46) in
  `FibredProduct.lean`; the global strong bundles (Definitions 2.6.4–2.6.7 (preprint 2.50–2.53), `Y[0]`) in
  `StrongBundle.lean`, Proposition 2.6.8 (preprint 2.54) in `StrongBundlePullback.lean`, `Y[1]` and `P[1]` in
  `StrongBundleOne.lean`.  Not formalized: the intrinsic extended faces (G.12), Definition 2.5.8 (preprint 2.38) in
  `T_xX` (G.13), strong bundle isomorphisms and the category `SBR` (G.14).
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

variable {E F E' F' : ScBanach}

/-! ### `C_e`, `E_e` (Definition 2.5.1 (preprint 2.33)) and tame retractions (Definition 2.5.2 (preprint 2.34)) -/

section Tame

variable {n : ℕ} {W : ScBanach}

/-- The partial quadrant `C_e = ⋂_{i ∈ I(e)} H_i` associated with `e` (Definition 2.5.1 (preprint 2.33)), for the
presentation `T` of `C`. -/
def partialQuadrantAtWith (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (e : E 0) :
    Set (E 0) :=
  {v | ∀ i, (T 0 e).1 i = 0 → 0 ≤ (T 0 v).1 i}

lemma minimalSubspaceWith_subset_partialQuadrantAtWith
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (e : E 0) :
    (minimalSubspaceWith T e : Set (E 0)) ⊆ partialQuadrantAtWith T e := fun v hv i hi => by
  rw [(mem_minimalSubspaceWith T).1 hv i hi]

lemma convex_partialQuadrantAtWith (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (e : E 0) :
    Convex ℝ (partialQuadrantAtWith T e) := by
  intro v hv w hw a b ha hb _ i hi
  have h1 := hv i hi
  have h2 := hw i hi
  simp only [map_add, map_smul, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  exact add_nonneg (mul_nonneg ha h1) (mul_nonneg hb h2)

variable {C : Set (E 0)}

/-- **Definition 2.5.2 (preprint 2.34)**, for a presentation `T` of `C`: the sc-smooth retraction `r : U → U` is
**tame** if (1) `d_C(r(x)) = d_C(x)` on `U` and (2) at every smooth point `x ∈ O₁`, the tangent
space `T_xO = Dr(x)E` has an sc-complement `A ⊆ E_x`. -/
structure ScRetraction.IsTameWith (R : ScRetraction E C)
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) : Prop where
  degIndex_apply : ∀ x ∈ R.U, degIndex E C (R x) = degIndex E C x
  exists_complement : ∀ x : E 1, x ∈ E.lvlSet R.retract 1 → x ∈ E.smoothLvl 1 →
    ∃ A : Submodule ℝ (E 0),
      E.IsScSplitting (LinearMap.range (scDeriv R.U R x : E 0 →ₗ[ℝ] E 0)) A ∧
        A ≤ minimalSubspaceWith T (E.toBase 1 x)

/-- **Definition 2.5.2 (preprint 2.34)**: a **tame sc-retraction**, with respect to every presentation of `C`. -/
def ScRetraction.IsTame (R : ScRetraction E C) : Prop :=
  ∀ (n : ℕ) (W : ScBanach) (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)),
    C = T 0 ⁻¹' quadrant n W 0 → R.IsTameWith T

/-- **Definition 2.5.2 (preprint 2.34)**: `(O, C, E)` is a **tame sc-smooth retract** if `O` is the image of a tame
sc-smooth retraction. -/
def IsTameRetract (E : ScBanach) (C O : Set (E 0)) : Prop :=
  ∃ R : ScRetraction E C, R.retract = O ∧ R.IsTame

lemma IsTameRetract.isScRetract {O : Set (E 0)} (h : IsTameRetract E C O) : IsScRetract E C O := by
  obtain ⟨R, hR, _⟩ := h
  exact ⟨R, hR⟩

/-- The identity retraction of a relatively open subset of a partial quadrant is tame
(`T_xU = E`, `A = 0`). -/
theorem ScRetraction.id_isTame {U : Set (E 0)} (hU : IsRelOpenInQuadrant E C U) :
    (ScRetraction.id hU).IsTame := by
  intro n W T hT
  refine ⟨fun _ _ => rfl, fun x hx _ => ⟨⊥, ?_, bot_le⟩⟩
  have hret : (ScRetraction.id hU).retract = U := image_id U
  have hxU : x ∈ E.lvlSet U 1 := by rw [← hret]; exact hx
  have hD : scDeriv (ScRetraction.id hU).U (ScRetraction.id hU) x = ContinuousLinearMap.id ℝ (E 0) :=
    IsSc1.scDeriv_eqOn (isSc1With_id U) (hU.isScDomain.uniqueDiffWithinAt 1) hxU
  have hrange : LinearMap.range (scDeriv (ScRetraction.id hU).U (ScRetraction.id hU) x :
      E 0 →ₗ[ℝ] E 0) = ⊤ := by
    rw [hD]; exact LinearMap.range_id
  rw [hrange]
  refine ⟨⟨by rw [Submodule.top_coe]; exact isClosed_univ, fun m => ?_⟩,
    ⟨by rw [Submodule.bot_coe]; exact isClosed_singleton, fun m => ?_⟩, fun m => ?_⟩
  · intro y _
    have : (E.levelSub ⊤ m : Set (E m)) ∩ E.smoothLvl m = E.smoothLvl m := by
      ext z; simp [ScBanach.mem_levelSub]
    rw [this, (E.dense_smooth m).closure_eq]; exact mem_univ _
  · intro y hy
    have hy0 : y = 0 := by
      have : E.toBase m y ∈ (⊥ : Submodule ℝ (E 0)) := hy
      rw [Submodule.mem_bot] at this
      exact E.toBase_injective m (by rw [this, map_zero])
    subst hy0
    refine subset_closure ⟨(E.levelSub ⊥ m).zero_mem, ?_⟩
    change E.toBase m 0 ∈ E.smooth
    rw [map_zero]; exact E.smooth.zero_mem
  · have h1 : E.levelSub ⊤ m = ⊤ := by ext z; simp [ScBanach.mem_levelSub]
    have h2 : E.levelSub ⊥ m = ⊥ := by
      ext z
      simp only [ScBanach.mem_levelSub, Submodule.mem_bot]
      exact ⟨fun h => E.toBase_injective m (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩
    rw [h1, h2]; exact isCompl_top_bot

/-- The reduced tangent space `T_x^R O = T_xO ∩ E_x` at `x ∈ O₁` (Definitions 2.4.7, 2.5.8 (preprint 2.27, 2.38), with the
presentation `T` of `C`). -/
def reducedTangentSpaceWith (R : ScRetraction E C) (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (x : E 1) : Submodule ℝ (E 0) :=
  LinearMap.range (scDeriv R.U R x : E 0 →ₗ[ℝ] E 0) ⊓ minimalSubspaceWith T (E.toBase 1 x)

/-- The partial cone `C_xO = T_xO ∩ C_x` at `x ∈ O₁` (Definition 2.4.7 (preprint 2.27)). -/
def partialConeWith (R : ScRetraction E C) (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (x : E 1) : Set (E 0) :=
  range (scDeriv R.U R x) ∩ partialQuadrantAtWith T (E.toBase 1 x)

/-- `T_x^R O ⊆ C_xO ⊆ T_xO` (Remark 2.4.8 (preprint 2.28)). -/
lemma reducedTangentSpaceWith_subset_partialConeWith (R : ScRetraction E C)
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (x : E 1) :
    (reducedTangentSpaceWith R T x : Set (E 0)) ⊆ partialConeWith R T x := by
  rintro v ⟨hv1, hv2⟩
  exact ⟨by obtain ⟨u, hu⟩ := hv1; exact ⟨u, hu⟩,
    minimalSubspaceWith_subset_partialQuadrantAtWith T _ hv2⟩

end Tame

/-! ### Tame M-polyfolds (Definition 2.5.7 (preprint 2.37)) and faces (Definition 2.5.10 (preprint 2.39)) -/

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

/-- **Definition 2.5.7 (preprint 2.37)**: a **tame M-polyfold** has an equivalent atlas all of whose charts are
modelled on tame sc-smooth retracts. -/
def IsTame : Prop :=
  ∃ A : MAtlas X, A.Equiv P.atlas ∧ ∀ φ ∈ A.charts, IsTameRetract φ.model.E φ.model.C φ.model.O

/-- **Definition 2.5.10 (preprint 2.39)**: a **face** of `X` is the closure of a connected component of
`{x | d_X(x) = 1}`. -/
def IsFace (F : Set X) : Prop :=
  ∃ x, P.degIndex x = 1 ∧ F = closure (connectedComponentIn {y | P.degIndex y = 1} x)

/-- **Definition 2.5.10 (preprint 2.39)**: `X` is **face-structured** if every point lies in exactly `d_X(x)` faces. -/
def IsFaceStructured : Prop :=
  ∀ x : X, {F : Set X | P.IsFace F ∧ x ∈ F}.encard = (P.degIndex x : ℕ∞)

/-- A face is closed. -/
lemma IsFace.isClosed {F : Set X} (h : P.IsFace F) : IsClosed F := by
  obtain ⟨x, _, rfl⟩ := h
  exact isClosed_closure

end MPolyfold

/-! ### The non-symmetric product `U ◁ F` and strong bundle maps (§2.5) -/

section StrongBundle

variable (E F)

/-- `(U ◁ F)_{m,k} = U_m ⊕ F_k`, the double filtration of `U ◁ F` (meaningful for `k ≤ m + 1`). -/
def doubleLevel (U : Set (E 0)) (m k : ℕ) : Set (E m × F k) :=
  E.lvlSet U m ×ˢ univ

variable {E F}

/-- The map `U ⊕ F₁ → U' ⊕ F'₁` induced by `Φ : U ⊕ F → U' ⊕ F'` (meaningful when `Φ` maps
`U ⊕ F₁` into `U' ⊕ F'₁`): the fibre component is lifted to `F'₁` through the injectivity of
`F'₁ → F'₀`. -/
def shiftFiber (Φ : E 0 × F 0 → E' 0 × F' 0) : (E.prod F.shift) 0 → (E'.prod F'.shift) 0 :=
  fun p => ((Φ (p.1, F.toBase 1 p.2)).1, Function.invFun (F'.toBase 1) (Φ (p.1, F.toBase 1 p.2)).2)

/-- **Definition 2.6.1 (preprint 2.47)**: `Φ : U ◁ F → U' ◁ F'` is a **strong bundle map** if it has the form
`Φ(u, h) = (φ(u), Γ(u, h))` with `Γ` linear in `h`, preserves the double filtration
(`U_m ⊕ F_k → U'_m ⊕ F'_k` for `k ≤ m + 1`), and is sc-smooth `(U ◁ F)[i] → (U' ◁ F')[i]` for
`i = 0, 1`. -/
structure IsStrongBundleMap (U : Set (E 0)) (U' : Set (E' 0)) (Φ : E 0 × F 0 → E' 0 × F' 0) :
    Prop where
  mapsTo : MapsTo Φ (U ×ˢ univ) (U' ×ˢ univ)
  fst_independent : ∀ u ∈ U, ∀ h h', (Φ (u, h)).1 = (Φ (u, h')).1
  fiber_linear : ∀ u ∈ U, IsLinearMap ℝ fun h => (Φ (u, h)).2
  preserves_filtration : ∀ m k, k ≤ m + 1 → ∀ u ∈ U, u ∈ range (E.toBase m) →
    ∀ h ∈ range (F.toBase k), (Φ (u, h)).1 ∈ range (E'.toBase m) ∧ (Φ (u, h)).2 ∈ range (F'.toBase k)
  isScSmooth_zero : IsScSmooth (E := E.prod F) (F := E'.prod F') (U ×ˢ univ) Φ
  isScSmooth_one : IsScSmooth (E := E.prod F.shift) (F := E'.prod F'.shift) (U ×ˢ univ) (shiftFiber Φ)

/-- The base map `φ` of a strong bundle map (`Φ(u, h) = (φ(u), Γ(u, h))`). -/
def IsStrongBundleMap.base (Φ : E 0 × F 0 → E' 0 × F' 0) : E 0 → E' 0 := fun u => (Φ (u, 0)).1

/-- **Definition 2.6.1 (preprint 2.47)**: a **strong bundle retraction** on `U ◁ F` is a strong bundle map
`R : U ◁ F → U ◁ F` with `R ∘ R = R` on `U ⊕ F`; it is **tame** if its base retraction is. -/
structure IsStrongBundleRetraction (U : Set (E 0)) (R : E 0 × F 0 → E 0 × F 0) : Prop
    extends IsStrongBundleMap U U R where
  idem : ∀ p ∈ U ×ˢ univ, R (R p) = R p

/-- **Definition 2.6.2 (preprint 2.48)**: `K ⊆ C ◁ F` is a **local strong bundle retract** if `K = R(U ◁ F)` for a
strong bundle retraction `R` on `U ◁ F`, `U` relatively open in `C`. -/
def IsStrongBundleRetract (C : Set (E 0)) (K : Set (E 0 × F 0)) : Prop :=
  ∃ (U : Set (E 0)) (R : E 0 × F 0 → E 0 × F 0), IsRelOpenInQuadrant E C U ∧
    IsStrongBundleRetraction U R ∧ K = R '' (U ×ˢ univ)

/-- The double filtration `K_{m,k} = K ∩ (U_m ⊕ F_k)` of a local strong bundle retract, as a subset
of `E_m × F_k`. -/
def strongLevel (K : Set (E 0 × F 0)) (m k : ℕ) : Set (E m × F k) :=
  {p | (E.toBase m p.1, F.toBase k p.2) ∈ K}

/-- `K[i]_m = K_{m,m+i}`: the filtration of `K[i]`, `i = 0, 1`. -/
def strongLevelShift (K : Set (E 0 × F 0)) (i m : ℕ) : Set (E m × F (m + i)) :=
  strongLevel K m (m + i)

/-- `K[1]` as a subset of `(E ⊕ F¹)₀ = E₀ × F₁`. -/
def strongShiftOne (K : Set (E 0 × F 0)) : Set ((E.prod F.shift) 0) :=
  {p | (p.1, F.toBase 1 p.2) ∈ K}

/-- The projection `p : K → O` onto the base. -/
def strongProj : E 0 × F 0 → E 0 := Prod.fst

/-- **Definition 2.6.3 (preprint 2.49)**: a **section** of `p : K → O` is a map `f : O → K` with `p ∘ f = 1_O`; it
is **sc-smooth** if it is sc-smooth as a map between the retracts `(O, C, E)` and
`(K = K[0], C ◁ F, E ◁ F)`. -/
structure IsScSmoothSection (C O : Set (E 0)) (K : Set (E 0 × F 0)) (f : E 0 → E 0 × F 0) :
    Prop where
  fst_eq : ∀ x ∈ O, (f x).1 = x
  isScSmooth : IsScSmoothRetractMap E C O (E.prod F) (C ×ˢ univ) K f

/-- **Definition 2.6.3 (preprint 2.49)**: an **sc⁺-section** is a section which is sc-smooth into `K[1]`, i.e. as a
map into the retract `(K[1], C ◁ F¹, E ◁ F¹)`; its principal part takes values in `F₁`. -/
structure IsScPlusSection (C O : Set (E 0)) (K : Set (E 0 × F 0)) (f : E 0 → E 0 × F 1) :
    Prop where
  fst_eq : ∀ x ∈ O, (f x).1 = x
  isScSmooth : IsScSmoothRetractMap E C O (E.prod F.shift) (C ×ˢ univ) (strongShiftOne K) f

/-- An sc⁺-section is in particular a section of `K` (its principal part lies in `F₁ ⊆ F₀`). -/
lemma IsScPlusSection.mem {C O : Set (E 0)} {K : Set (E 0 × F 0)} {f : E 0 → E 0 × F 1}
    (hf : IsScPlusSection C O K f) {x : E 0} (hx : x ∈ O) : ((f x).1, F.toBase 1 (f x).2) ∈ K :=
  hf.isScSmooth.mapsTo hx

end StrongBundle

end Polyfold
