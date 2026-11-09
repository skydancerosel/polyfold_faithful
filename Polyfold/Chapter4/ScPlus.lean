import Polyfold.Chapter2.TameInvariance

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §4.1,
Remark 4.1.3 (preprint 4.3), Definitions 4.1.4 and 4.1.6 (preprint 4.4 and 4.6), Lemmas 4.1.5 and 4.1.7 (preprint 4.5 and 4.7), Proposition 4.1.8 (preprint 4.8) *(book 2017: Remark 4.1,
Definitions 4.2, 4.3, Lemmas 4.1, 4.2, Proposition 4.1; see `BookConcordance.md`)*.

# sc⁺-maps, sc⁺-retractions and sc⁺-retracts

## The text, paraphrased

(Remark 4.1.3 (preprint 4.3)) If `X₀ = X_∞`, the identity `1₀¹ : X → X¹` has the inverse `1₁⁰ : X¹ → X`, which is
always sc-smooth; so if `1₀¹` is sc-smooth it is an sc-diffeomorphism.  `X¹ ≠ X` as M-polyfolds is
possible although the underlying sets agree.  A finite-dimensional space with the constant
sc-structure has `X = X¹`.  (Definition 4.1.4 (preprint 4.4)) An sc-smooth retraction `r : U → U` is an
sc⁺-retraction if `r(U_m) ⊆ U_{m+1}` and `r : U → U¹` is sc-smooth; on an open `V ⊆ X` of an
M-polyfold, if `r : V → V¹` is sc-smooth.  (Lemma 4.1.5 (preprint 4.5)) If some sc⁺-retraction `t` has image `O`,
every sc-smooth retraction `s` onto `O` is sc⁺, because `s = t ∘ s`.  (Definition 4.1.6 (preprint 4.6)) `(O, C, E)` is
an sc⁺-retract if it is the image of an sc⁺-retraction; by Lemma 4.1.5 (preprint 4.5) this is intrinsic.
(Lemma 4.1.7 (preprint 4.7)) For an sc⁺-retraction `r` onto `O`: (i) `O = O_∞`; (ii) `T_oO = Dr(o)E` is
finite-dimensional, because `Dr(o)` is an sc⁺-operator, hence compact, and a projection.
(Proposition 4.1.8 (preprint 4.8)) `O` is an sc⁺-retract iff `O₀ = O_∞` and `1₀¹ : O → O¹` is sc-smooth.

## What is formalized

* `Polyfold.IsScPlus U f`: an **sc⁺-map** on `U` (`f(U) ⊆ F₁` and the lift `U → F¹` is
  sc-smooth), with `IsScPlus.mem_range_succ` (`f(U_m) ⊆ F_{m+1}`), `IsScPlus.iff_exists` (the
  lift may be any map into `F¹`), `IsScPlus.isScSmooth` (sc⁺ ⇒ sc-smooth), the composition rules
  `IsScPlus.comp_isScSmooth` (sc⁺ ∘ sc-smooth) and `IsScSmooth.comp_isScPlus` (sc-smooth ∘ sc⁺,
  through Proposition 1.2.2 (preprint 1.17)), `ScPlus.isScPlus` (sc⁺-operators), and
  `IsScPlus.exists_scPlus_deriv` / `IsScPlus.isCompactOperator_deriv`: **the derivative of an
  sc⁺-map at a smooth point is an sc⁺-operator, compact on every level**.
* `ScRetraction.IsScPlus` (**Definition 4.1.4 (preprint 4.4)**), `Polyfold.lemma_4_1_5` (**Lemma 4.1.5 (preprint 4.5)**),
  `Polyfold.IsScPlusRetract` (**Definition 4.1.6 (preprint 4.6)**) with `IsScPlusRetract.isScPlus` /
  `isScPlusRetract_iff_forall` (the property is intrinsic), `Polyfold.lemma_4_1_7_i`,
  `Polyfold.lemma_4_1_7_ii`, `lemma_4_1_7_ii_tangentSpace` (**Lemma 4.1.7 (preprint 4.7)**; the linear algebra is
  `finiteDimensional_range_of_isCompactOperator_of_idem`), `Polyfold.proposition_4_1_8`
  (**Proposition 4.1.8 (preprint 4.8)**, retract form, with `1₀¹ = ScBanach.liftOne`).
* `ScBanach.toBase_surjective`, `ScBanach.scIsoConst`: **a finite-dimensional sc-Banach space has
  all levels equal and is sc-isomorphic to `E₀` with the constant structure**.
* `Polyfold.remark_4_1_3_const`, `MPolyfold.remark_4_1_3_levelVal` (`1₁⁰ : X¹ → X` is sc-smooth),
  `MPolyfold.remark_4_1_3_isScDiffeo` (**Remark 4.1.3 (preprint 4.3)**); `MPolyfold.toLevelOne` (`1₀¹`),
  `MPolyfold.proposition_4_1_8_chart` (**Proposition 4.1.8 (preprint 4.8) for the charts of an M-polyfold**: the model
  of a chart `φ : V → O` is an sc⁺-retract iff `V ⊆ X_∞` and `1₀¹` is sc-smooth on `V`),
  `MPolyfold.isScSmoothMap_toLevelOne_iff` (the condition "`X₀ = X_∞` and `1₀¹` sc-smooth" of
  Theorem 4.1.2 (preprint 4.2) (ii) holds iff every chart is modelled on an sc⁺-retract), and
  `MPolyfold.IsScPlusRetractionOn` (Definition 4.1.4 (preprint 4.4) on an open subset of an M-polyfold).

## What the text leaves implicit, and the choices made

* "sc⁺-map" is used by the text (proof of Lemma 4.1.7 (preprint 4.7)) but defined only for retractions; it is
  defined here for maps on any `U`, as Definition 4.1.4 (preprint 4.4) does for retractions.  The lift `U → F¹` is
  the canonical one, `F.liftOne ∘ f`.  The project already treats the neighbouring notions the same
  way: sc⁺-operators are sc-operators into `F¹` (`ScPlus`, reused here), sc⁺-sections are
  sc-smooth maps into `K[1]` (Definitions 2.6.3, 2.6.6 (preprint 2.49, 2.52): `IsScPlusSection`), and the sc⁺-germs of
  Chapter 3 are germs into `F¹` (`BasicClass.lean`); `IsScPlus` is the notion for maps on sets.
* Lemma 4.1.7 (preprint 4.7) (ii) is stated at a lift `o₁ ∈ E₁` of `o ∈ O` (the tangent space `T_oO` of
  Definition 2.3.12 (preprint 2.17) is indexed by points of `O₁`; by (i) every point of `O` has one, and it is
  smooth).  The step "`Dr(o)` is an sc⁺-operator since `r` is a sc⁺-map" is
  `IsScPlus.exists_scPlus_deriv` (chain rule for `r = ι ∘ r¹` and Proposition 1.2.1 (preprint 1.16)'s remark that
  the derivative at a smooth point is an sc-operator).
* The text's `1₀¹` is a map `X → X¹` only when `X₀ = X₁` as sets; `MPolyfold.toLevelOne` carries a
  junk value off `X₁`, which plays no role on `X₁`.  For retracts it is the lift `E.liftOne`, as a
  map between the retracts `(O, C, E)` and `(O¹, C¹, E¹)`.
* Remark 4.1.3 (preprint 4.3)'s "it is possible that `X¹ ≠ X` as M-polyfolds although the underlying sets agree" is
  given without an example and is **not formalized**.  "`X = X¹` for a finite-dimensional space with
  the constant structure" is `remark_4_1_3_const`: `(ℝⁿ)¹ = ℝⁿ` holds definitionally and every
  retract in `ℝⁿ` is an sc⁺-retract.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

variable {E F G : ScBanach}

/-! ### The lift `E₀ ⊇ E₁ → E₁` -/

/-- The lift `x ↦ x` of a point of `E₁ ⊆ E₀` to `E₁` (a junk value off `E₁`): the map the text
writes `1₀¹`. -/
def ScBanach.liftOne (E : ScBanach) (x : E 0) : E 1 := Function.invFun (E.toBase 1) x

lemma ScBanach.toBase_liftOne (E : ScBanach) {x : E 0} (hx : x ∈ range (E.toBase 1)) :
    E.toBase 1 (E.liftOne x) = x :=
  Function.invFun_eq hx

@[simp] lemma ScBanach.liftOne_toBase (E : ScBanach) (y : E 1) : E.liftOne (E.toBase 1 y) = y :=
  Function.leftInverse_invFun (E.toBase_injective 1) y

lemma ScBanach.liftOne_eq_iff (E : ScBanach) {x : E 0} (hx : x ∈ range (E.toBase 1)) {y : E 1} :
    E.liftOne x = y ↔ E.toBase 1 y = x := by
  constructor
  · rintro rfl; exact E.toBase_liftOne hx
  · rintro rfl; exact E.liftOne_toBase y

/-! ### sc⁺-maps -/

/-- An **sc⁺-map** `f : U → F` on a subset `U ⊆ E₀` (the notion of Definition 4.1.4 (preprint 4.4), for maps; the
text uses it for retractions and, in the proof of Lemma 4.1.7 (preprint 4.7), says "`r` is a sc⁺-map"): `f(U) ⊆ F₁`
and the lift `U → F¹`, `x ↦ f(x) ∈ F₁`, is sc-smooth.  Then `f(U_m) ⊆ F_{m+1}` for every `m`
(`IsScPlus.mem_range_succ`). -/
structure IsScPlus (U : Set (E 0)) (f : E 0 → F 0) : Prop where
  mem_range : ∀ x ∈ U, f x ∈ range (F.toBase 1)
  isScSmooth_lift : IsScSmooth (E := E) (F := F.shift) U (F.liftOne ∘ f)

namespace IsScPlus

variable {U : Set (E 0)} {V : Set (F 0)} {f : E 0 → F 0}

lemma toBase_lift (hf : IsScPlus U f) {x : E 0} (hx : x ∈ U) :
    F.toBase 1 (F.liftOne (f x)) = f x :=
  F.toBase_liftOne (hf.mem_range x hx)

/-- An sc⁺-map maps `U_m` into `F_{m+1}` (Definition 4.1.4 (preprint 4.4): `r(U_m) ⊆ U_{m+1}`). -/
theorem mem_range_succ (hf : IsScPlus U f) (m : ℕ) {x : E m} (hx : x ∈ E.lvlSet U m) :
    f (E.toBase m x) ∈ range (F.toBase (m + 1)) := by
  obtain ⟨y, hy⟩ := hf.isScSmooth_lift.isSc1.isSc0.mem_range m x hx
  refine ⟨y, ?_⟩
  rw [F.shift_toBase, hy, Function.comp_apply, hf.toBase_lift hx]

/-- The text's form: `f` is sc⁺ iff it has a lift `g : U → F¹` (`ι ∘ g = f` on `U`) which is
sc-smooth into `F¹`. -/
theorem iff_exists (hU : IsScDomain E U) :
    IsScPlus U f ↔ ∃ g : E 0 → F 1,
      IsScSmooth (E := E) (F := F.shift) U g ∧ ∀ x ∈ U, F.toBase 1 (g x) = f x := by
  constructor
  · intro hf
    exact ⟨F.liftOne ∘ f, hf.isScSmooth_lift, fun x hx => hf.toBase_lift hx⟩
  · rintro ⟨g, hg, hgf⟩
    refine ⟨fun x hx => ⟨g x, hgf x hx⟩, hg.congr hU fun x hx => ?_⟩
    rw [Function.comp_apply, ← hgf x hx, F.liftOne_toBase]

/-- **An sc⁺-map is sc-smooth**: `f = ι ∘ (lift of f)` with the sc-operator `ι : F¹ → F`. -/
theorem isScSmooth (hU : IsScDomain E U) (hf : IsScPlus U f) : IsScSmooth U f := by
  have h := IsScSmooth.comp hU (isScDomain_univ _) (F.shiftIncl.isScSmooth (isScDomain_univ _))
    hf.isScSmooth_lift (mapsTo_univ _ _)
  refine h.congr hU fun x hx => ?_
  change F.toBase 1 (F.liftOne (f x)) = f x
  exact hf.toBase_lift hx

/-- sc⁺ depends only on the values on `U`. -/
theorem congr (hU : IsScDomain E U) (hf : IsScPlus U f) {f' : E 0 → F 0} (h : EqOn f f' U) :
    IsScPlus U f' :=
  ⟨fun x hx => h hx ▸ hf.mem_range x hx,
    hf.isScSmooth_lift.congr hU fun x hx => by simp only [Function.comp_apply, h hx]⟩

/-- sc⁺-maps restrict to smaller domains. -/
theorem mono {U' : Set (E 0)} (hU' : IsScDomain E U') (hf : IsScPlus U f) (h : U' ⊆ U) :
    IsScPlus U' f :=
  ⟨fun x hx => hf.mem_range x (h hx), hf.isScSmooth_lift.of_subset hU' h⟩

/-- **sc⁺ ∘ sc-smooth is sc⁺**: the lift of `g ∘ f` is (lift of `g`) ∘ `f`. -/
theorem comp_isScSmooth {g : F 0 → G 0} (hU : IsScDomain E U) (hV : IsScDomain F V)
    (hg : IsScPlus V g) (hf : IsScSmooth U f) (hfV : MapsTo f U V) : IsScPlus U (g ∘ f) :=
  ⟨fun x hx => hg.mem_range (f x) (hfV hx),
    IsScSmooth.comp (E := E) (F := F) (G := G.shift) hU hV hg.isScSmooth_lift hf hfV⟩

end IsScPlus

/-- **sc-smooth ∘ sc⁺ is sc⁺** (via Proposition 1.2.2 (preprint 1.17)): if `f : U → V` is sc⁺ and `g : V → G` is
sc-smooth then `g ∘ f` is sc⁺; its lift is `g¹ ∘ (lift of f)`, where `g¹ : V¹ → G¹` is the map
induced on level `1`, sc-smooth by Proposition 1.2.2 (preprint 1.17) (`IsScSmooth.shift`). -/
theorem IsScSmooth.comp_isScPlus {U : Set (E 0)} {V : Set (F 0)} {f : E 0 → F 0} {g : F 0 → G 0}
    (hU : IsScDomain E U) (hV : IsScDomain F V) (hg : IsScSmooth V g) (hf : IsScPlus U f)
    (hfV : MapsTo f U V) : IsScPlus U (g ∘ f) := by
  have hg0 := hg.isSc1.isSc0
  -- the lift of `f` maps `U` into `V¹ = V_1`
  have hlift : MapsTo (F.liftOne ∘ f) U (F.lvlSet V 1) := fun x hx => by
    rw [ScBanach.mem_lvlSet, Function.comp_apply, hf.toBase_lift hx]; exact hfV hx
  have hlev : ∀ x ∈ U, G.toBase 1 (levelMap g 1 (F.liftOne (f x))) = g (f x) := fun x hx => by
    have hx' : F.liftOne (f x) ∈ F.lvlSet V 1 := hlift hx
    rw [hg0.toBase_levelMap hx', hf.toBase_lift hx]
  rw [IsScPlus.iff_exists hU]
  refine ⟨levelMap g 1 ∘ (F.liftOne ∘ f), ?_, fun x hx => hlev x hx⟩
  exact IsScSmooth.comp (E := E) (F := F.shift) (G := G.shift) hU hV.shift (hg.shift hV)
    hf.isScSmooth_lift hlift

/-- An **sc⁺-operator is an sc⁺-map** on every sc-domain. -/
theorem ScPlus.isScPlus (S : ScPlus E F) {U : Set (E 0)} (hU : IsScDomain E U) :
    IsScPlus U (S.toScOperator 0) := by
  rw [IsScPlus.iff_exists hU]
  exact ⟨S 0, S.isScSmooth hU, fun x _ => rfl⟩

/-- **The derivative of an sc⁺-map at a smooth point is an sc⁺-operator** (the step "`Dr(o)` is a
sc⁺-operator, since `r` is a sc⁺-map" of the proof of Lemma 4.1.7 (preprint 4.7)): at `x ∈ U₁ ∩ E_∞` there is an
sc⁺-operator `S : E → F` (an sc-operator `E → F¹`) whose underlying sc-operator `E → F` is
`Df(x)`. -/
theorem IsScPlus.exists_scPlus_deriv {U : Set (E 0)} {f : E 0 → F 0} (hU : IsScDomain E U)
    (hf : IsScPlus U f) {x : E 1} (hx : x ∈ E.lvlSet U 1) (hs : x ∈ E.smoothLvl 1) :
    ∃ S : ScPlus E F, ∀ v, S.toScOperator 0 v = scDeriv U f x v := by
  set g : E 0 → F 1 := F.liftOne ∘ f with hg
  have hgsc : IsScSmooth (E := E) (F := F.shift) U g := hf.isScSmooth_lift
  have hop : IsScOperator (E := E) (F := F.shift) (scDeriv U g x) :=
    hgsc.isSc1.isSc1With_scDeriv.scOperator_deriv hx hs
  refine ⟨hop.toScOperator, fun v => ?_⟩
  -- `f = ι ∘ g` on `U`, so `Df(x) = ι ∘ Dg(x)` (chain rule and uniqueness)
  have hfg : EqOn (F.shiftIncl 0 ∘ g) f U := fun y hy => hf.toBase_lift hy
  have h1 := scDeriv_comp_apply_of_isScDomain hU (isScDomain_univ _) hgsc.isSc1
    ((F.shiftIncl.isScSmooth (isScDomain_univ _)).isSc1) (mapsTo_univ _ _) hx v
  rw [ScOperator.scDeriv_eq _ (isScDomain_univ _) (mem_univ _)] at h1
  have h2 : scDeriv U (F.shiftIncl 0 ∘ g) x v = scDeriv U f x v := by
    have hsc : IsScSmooth U (F.shiftIncl 0 ∘ g) := IsScSmooth.comp hU (isScDomain_univ _)
      (F.shiftIncl.isScSmooth (isScDomain_univ _)) hgsc (mapsTo_univ _ _)
    have := IsSc1.scDeriv_eqOn (hsc.isSc1.isSc1With_scDeriv) (hU.uniqueDiffWithinAt 1)
    have hf1 : IsSc1With U f (scDeriv U (F.shiftIncl 0 ∘ g)) :=
      hsc.isSc1.isSc1With_scDeriv.congr hfg
    exact congrArg (fun L : E 0 →L[ℝ] F 0 => L v)
      (IsSc1.scDeriv_eqOn hf1 (hU.uniqueDiffWithinAt 1) hx).symm
  rw [← h2, ← h1]
  change F.shiftIncl 0 (hop.toScOperator 0 v) = _
  rw [IsScOperator.toScOperator_zero]

/-- **The derivative of an sc⁺-map at a smooth point is compact on every level** (Definition 1.1.5 (preprint 1.4)
and the proof of Lemma 4.1.7 (preprint 4.7): "`Dr(o) : E → E` is a compact operator between every level"):
`Df(x) : E₀ → F₀` is a compact operator, and so are its level-`m` restrictions. -/
theorem IsScPlus.isCompactOperator_deriv {U : Set (E 0)} {f : E 0 → F 0} (hU : IsScDomain E U)
    (hf : IsScPlus U f) {x : E 1} (hx : x ∈ E.lvlSet U 1) (hs : x ∈ E.smoothLvl 1) :
    IsCompactOperator (scDeriv U f x) ∧
      ∃ S : ScPlus E F, (∀ v, S.toScOperator 0 v = scDeriv U f x v) ∧
        ∀ m, IsCompactOperator (S.toScOperator m) := by
  obtain ⟨S, hS⟩ := hf.exists_scPlus_deriv hU hx hs
  refine ⟨?_, S, hS, fun m => S.isCompactOperator m⟩
  have : (scDeriv U f x : E 0 → F 0) = S.toScOperator 0 := funext fun v => (hS v).symm
  rw [this]
  exact S.isCompactOperator 0

/-! ### A compact projection has finite-dimensional range -/

/-- The range of a compact continuous linear projection `P = P ∘ P` of a normed space is
finite-dimensional: `P` restricts to the identity of its (closed) range, and a normed space whose
identity is compact is finite-dimensional (Riesz).  This is the last step of the proof of
Lemma 4.1.7 (preprint 4.7) (ii). -/
theorem finiteDimensional_range_of_isCompactOperator_of_idem {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (P : V →L[ℝ] V) (hP : IsCompactOperator P) (hPP : ∀ v, P (P v) = P v) :
    FiniteDimensional ℝ (LinearMap.range (P : V →ₗ[ℝ] V)) := by
  set K := LinearMap.range (P : V →ₗ[ℝ] V) with hK
  have hfix : ∀ v ∈ K, P v = v := by rintro _ ⟨u, rfl⟩; exact hPP u
  have hclosed : IsClosed (K : Set V) := by
    have : (K : Set V) = {v | P v = v} := by
      ext v
      exact ⟨fun hv => hfix v hv, fun hv => ⟨v, hv⟩⟩
    rw [this]
    exact isClosed_eq P.continuous continuous_id
  have hmaps : ∀ v ∈ K, (P : V →ₗ[ℝ] V) v ∈ K := fun v _ => ⟨v, rfl⟩
  have hres := IsCompactOperator.restrict (f := (P : V →ₗ[ℝ] V)) hP hmaps hclosed
  have hid : ((P : V →ₗ[ℝ] V).restrict hmaps : K → K) = id := by
    funext v
    exact Subtype.ext (hfix v v.2)
  rw [hid] at hres
  exact FiniteDimensional.of_isCompactOperator_id hres

/-! ### sc⁺-retractions (Definition 4.1.4 (preprint 4.4)) and sc⁺-retracts (Definition 4.1.6 (preprint 4.6)) -/

section Retractions

variable {C : Set (E 0)}

/-- **Definition 4.1.4 (preprint 4.4)**: an sc-smooth retraction `r : U → U` is an **sc⁺-retraction** if
`r(U_m) ⊆ U_{m+1}` for all `m` and `r : U → U¹` is sc-smooth, i.e. `r` is an sc⁺-map on `U`
(`IsScPlus`; `r(U_m) ⊆ U_{m+1}` is then `ScRetraction.IsScPlus.mapsTo_lvlSet_succ`). -/
def ScRetraction.IsScPlus (R : ScRetraction E C) : Prop := Polyfold.IsScPlus R.U R

/-- The condition `r(U_m) ⊆ U_{m+1}` of Definition 4.1.4 (preprint 4.4). -/
theorem ScRetraction.IsScPlus.mem_lvlSet_succ {R : ScRetraction E C} (hR : R.IsScPlus) (m : ℕ)
    {x : E m} (hx : x ∈ E.lvlSet R.U m) :
    ∃ y ∈ E.lvlSet R.U (m + 1), E.toBase (m + 1) y = R (E.toBase m x) := by
  obtain ⟨y, hy⟩ := Polyfold.IsScPlus.mem_range_succ hR m hx
  exact ⟨y, by rw [ScBanach.mem_lvlSet, hy]; exact R.mapsTo hx, hy⟩

/-- **Lemma 4.1.5 (preprint 4.5)**: if `t : U → U` is an sc⁺-retraction onto `O`, then every sc-smooth retraction
`s : V → V` onto `s(V) = O` is an sc⁺-retraction.  *Proof* (the text's): `s = t ∘ s` on `V`, and
`t ∘ s` is sc⁺ (sc⁺ ∘ sc-smooth). -/
theorem lemma_4_1_5 {T S : ScRetraction E C} (hT : T.IsScPlus) (hTS : T.retract = S.retract) :
    S.IsScPlus := by
  have hmaps : MapsTo S S.U T.U := fun v hv => T.retract_subset (hTS ▸ S.apply_mem_retract hv)
  have h := Polyfold.IsScPlus.comp_isScSmooth S.isScDomain T.isScDomain hT S.isScSmooth hmaps
  refine h.congr S.isScDomain fun v hv => ?_
  exact T.apply_eq_self_of_mem_retract (hTS ▸ S.apply_mem_retract hv)

/-- **Definition 4.1.6 (preprint 4.6)**: the sc-smooth retract `(O, C, E)` is an **sc⁺-retract** if there is an
sc⁺-retraction `t : U → U` of a relatively open `U ⊆ C` onto `O`. -/
def IsScPlusRetract (E : ScBanach) (C O : Set (E 0)) : Prop :=
  ∃ R : ScRetraction E C, R.retract = O ∧ R.IsScPlus

lemma IsScPlusRetract.isScRetract {O : Set (E 0)} (h : IsScPlusRetract E C O) :
    IsScRetract E C O := by
  obtain ⟨R, hR, -⟩ := h
  exact ⟨R, hR⟩

/-- The remark after Definition 4.1.6 (preprint 4.6): **being an sc⁺-retract is intrinsic** — then every sc-smooth
retraction onto `O` is an sc⁺-retraction (Lemma 4.1.5 (preprint 4.5)). -/
theorem IsScPlusRetract.isScPlus {O : Set (E 0)} (h : IsScPlusRetract E C O)
    (S : ScRetraction E C) (hS : S.retract = O) : S.IsScPlus := by
  obtain ⟨R, hR, hRp⟩ := h
  exact lemma_4_1_5 hRp (hR.trans hS.symm)

theorem isScPlusRetract_iff_forall {O : Set (E 0)} :
    IsScPlusRetract E C O ↔ IsScRetract E C O ∧ ∀ S : ScRetraction E C, S.retract = O → S.IsScPlus :=
  ⟨fun h => ⟨h.isScRetract, h.isScPlus⟩, fun ⟨⟨R, hR⟩, h⟩ => ⟨R, hR, h R hR⟩⟩

/-- **Lemma 4.1.7 (preprint 4.7) (i)**: the image of an sc⁺-retraction consists of smooth points, `O = O_∞`.
*Proof* (the text's): `r(x) ∈ U₁`, and `r(x) = r(r(x)) ∈ U₂`, and so on. -/
theorem lemma_4_1_7_i {R : ScRetraction E C} (hR : R.IsScPlus) : R.retract ⊆ E.smooth := by
  have key : ∀ m, ∀ y ∈ R.retract, y ∈ range (E.toBase m) := by
    intro m
    induction m with
    | zero => exact fun y _ => ⟨y, rfl⟩
    | succ m ih =>
      intro y hy
      obtain ⟨z, rfl⟩ := ih y hy
      have hz : z ∈ E.lvlSet R.U m := R.retract_subset hy
      have := Polyfold.IsScPlus.mem_range_succ hR m hz
      rwa [R.apply_eq_self_of_mem_retract hy] at this
  exact fun y hy => (E.mem_smooth_iff).2 fun m => key m y hy

/-- **Lemma 4.1.7 (preprint 4.7) (ii)**: at every point `o ∈ O` (lifted to `o₁ ∈ E₁`, which is smooth by (i)), the
tangent space `T_oO = Dr(o)E` is finite-dimensional.  *Proof* (the text's): `Dr(o)` is an
sc⁺-operator (the derivative of an sc⁺-map at a smooth point), hence compact, and it is a
projection, so its range is finite-dimensional. -/
theorem lemma_4_1_7_ii {R : ScRetraction E C} (hR : R.IsScPlus) {o : E 1}
    (ho : E.toBase 1 o ∈ R.retract) :
    FiniteDimensional ℝ (LinearMap.range (scDeriv R.U R o : E 0 →ₗ[ℝ] E 0)) := by
  have hs : o ∈ E.smoothLvl 1 := lemma_4_1_7_i hR ho
  have hoU : o ∈ E.lvlSet R.U 1 := R.retract_subset ho
  have hc := (Polyfold.IsScPlus.isCompactOperator_deriv R.isScDomain hR hoU hs).1
  exact finiteDimensional_range_of_isCompactOperator_of_idem _ hc fun v =>
    congrArg (fun L : E 0 →L[ℝ] E 0 => L v) (R.scDeriv_comp_self ho)

/-- **Lemma 4.1.7 (preprint 4.7) (ii)** for the tangent space `T_oO` of Definition 2.3.12 (preprint 2.17): at every `o ∈ O` there is
a lift `o₁ ∈ E₁` (smooth), and `T_{o₁}O` is a finite-dimensional linear subspace (the range of
`Dr(o₁)`). -/
theorem lemma_4_1_7_ii_tangentSpace {R : ScRetraction E C} (hR : R.IsScPlus) {o : E 0}
    (ho : o ∈ R.retract) :
    ∃ o₁ : E 1, E.toBase 1 o₁ = o ∧ o₁ ∈ E.smoothLvl 1 ∧
      tangentSpace E C R.retract o₁ =
        (LinearMap.range (scDeriv R.U R o₁ : E 0 →ₗ[ℝ] E 0) : Set (E 0)) ∧
      FiniteDimensional ℝ (LinearMap.range (scDeriv R.U R o₁ : E 0 →ₗ[ℝ] E 0)) := by
  obtain ⟨o₁, ho₁, hs⟩ := exists_smoothLvl_one_of_mem_smooth (lemma_4_1_7_i hR ho)
  have ho₁' : E.toBase 1 o₁ ∈ R.retract := ho₁ ▸ ho
  exact ⟨o₁, ho₁, hs, tangentSpace_eq_coe_submodule R ho₁', lemma_4_1_7_ii hR ho₁'⟩

/-- **Proposition 4.1.8 (preprint 4.8)** (the retract form): an sc-smooth retract `(O, C, E)` is an sc⁺-retract iff
`O₀ = O_∞` and the identity `1₀¹ : O → O¹` (the lift `E.liftOne`) is sc-smooth from `(O, C, E)` to
`(O¹, C¹, E¹)`.  *Proof* (the text's): (⇒) Lemma 4.1.7 (preprint 4.7) (i), and `1₀¹ ∘ r : U → E¹` is the lift of the
sc⁺-map `r`; (⇐) for a retraction `r` onto `O`, `U → O → O¹ → U¹` is the lift of `r`. -/
theorem proposition_4_1_8 {O : Set (E 0)} (hO : IsScRetract E C O) :
    IsScPlusRetract E C O ↔ O ⊆ E.smooth ∧
      IsScSmoothRetractMap E C O E.shift (E.lvlSet C 1) (E.lvlSet O 1) E.liftOne := by
  have hmaps : O ⊆ E.smooth → MapsTo E.liftOne O (E.lvlSet O 1) := fun hsm x hx => by
    rw [ScBanach.mem_lvlSet, E.toBase_liftOne ((E.mem_smooth_iff.1 (hsm hx)) 1)]; exact hx
  constructor
  · rintro ⟨R, rfl, hR⟩
    have hsm := lemma_4_1_7_i hR
    refine ⟨hsm, (isScSmoothRetractMap_iff_exists ⟨R, rfl⟩).2 ⟨hmaps hsm, R, rfl, ?_⟩⟩
    exact hR.isScSmooth_lift
  · rintro ⟨hsm, hlift⟩
    obtain ⟨R, rfl⟩ := hO
    refine ⟨R, rfl, ?_, hlift.comp_isScSmooth R rfl⟩
    intro x hx
    exact (E.mem_smooth_iff.1 (hsm (R.apply_mem_retract hx))) 1

end Retractions

/-! ### Finite-dimensional sc-Banach spaces carry the constant structure -/

namespace ScBanach

variable (E) [FiniteDimensional ℝ (E 0)]

/-- Every level of an sc-Banach space with finite-dimensional `E₀` is finite-dimensional (it
injects into `E₀`). -/
theorem finiteDimensional_lvl (m : ℕ) : FiniteDimensional ℝ (E m) :=
  FiniteDimensional.of_injective (E.toBase m : E m →ₗ[ℝ] E 0) (E.toBase_injective m)

/-- **All levels of a finite-dimensional sc-Banach space are equal**: `E_m → E₀` is onto, since its
range is a finite-dimensional, hence closed, subspace containing the dense set `E_∞`. -/
theorem toBase_surjective (m : ℕ) : Surjective (E.toBase m) := by
  have := E.finiteDimensional_lvl m
  have hclosed : IsClosed (LinearMap.range (E.toBase m : E m →ₗ[ℝ] E 0) : Set (E 0)) :=
    Submodule.closed_of_finiteDimensional _
  have hdense : Dense (LinearMap.range (E.toBase m : E m →ₗ[ℝ] E 0) : Set (E 0)) := by
    refine (E.dense_smooth 0).mono fun x hx => ?_
    obtain ⟨y, hy⟩ := (E.mem_smooth_iff).1 hx m
    exact ⟨y, hy⟩
  intro x
  have : x ∈ (LinearMap.range (E.toBase m : E m →ₗ[ℝ] E 0) : Set (E 0)) := by
    rw [← hclosed.closure_eq, hdense.closure_eq]; exact mem_univ x
  obtain ⟨y, hy⟩ := this
  exact ⟨y, hy⟩

/-- **A finite-dimensional sc-Banach space is sc-isomorphic to `E₀` with the constant structure**
(Definition 1.1.1 (preprint 1.1): "a finite-dimensional space has exactly one sc-structure, the constant one"):
the level maps are the inclusions `E_m → E₀`, which are bijective (`toBase_surjective`). -/
def scIsoConst : ScIso E (ScBanach.const (E 0)) where
  lvl m :=
    letI := E.finiteDimensional_lvl m
    (LinearEquiv.ofBijective (E.toBase m : E m →ₗ[ℝ] E 0)
      ⟨E.toBase_injective m, E.toBase_surjective m⟩).toContinuousLinearEquiv
  incl_comm _ _ := rfl

@[simp] lemma scIsoConst_apply (m : ℕ) (x : E m) : E.scIsoConst m x = E.toBase m x := rfl

end ScBanach

/-- **Remark 4.1.3 (preprint 4.3)**, last sentence: for a finite-dimensional space with the constant sc-structure,
`X = X¹` as sc-spaces: `(ℝⁿ)¹ = ℝⁿ` (definitionally), `1₀¹ = id`, and every sc-smooth retract
`(O, C, ℝⁿ)` is an sc⁺-retract. -/
theorem remark_4_1_3_const (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] :
    (ScBanach.const V).shift = ScBanach.const V ∧ (∀ x : V, (ScBanach.const V).liftOne x = x) ∧
      ∀ (C O : Set V), IsScRetract (ScBanach.const V) C O →
        IsScPlusRetract (ScBanach.const V) C O := by
  have hlift : ∀ x : V, (ScBanach.const V).liftOne x = x := fun x => by
    have := (ScBanach.const V).liftOne_toBase x
    rwa [ScBanach.constScale_toBase] at this
  refine ⟨rfl, hlift, fun C O hO => ?_⟩
  obtain ⟨R, rfl⟩ := hO
  refine ⟨R, rfl, fun x _ => ⟨R x, ScBanach.constScale_toBase V 1 _⟩, ?_⟩
  have : (ScBanach.const V).liftOne ∘ R = R := funext fun x => hlift (R x)
  rw [this]
  exact R.isScSmooth

/-! ### M-polyfolds: `1₀¹ : X → X¹`, Remark 4.1.3 (preprint 4.3) and Proposition 4.1.8 (preprint 4.8) in charts -/

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

open scoped Classical in
/-- The identity `1₀¹ : X → X¹`, `x ↦ x`, on the points of `X₁` (the text's map `1₀¹`, defined
when `X₀ = X₁` as sets); a junk value `x₀` off `X₁`. -/
def toLevelOne (x₀ : P.Level 1) (x : X) : P.Level 1 :=
  if h : x ∈ P.levelSet 1 then P.levelMk 1 x h else x₀

variable {P}

lemma levelVal_toLevelOne (x₀ : P.Level 1) {x : X} (hx : x ∈ P.levelSet 1) :
    P.levelVal 1 (P.toLevelOne x₀ x) = x := by
  rw [toLevelOne, dif_pos hx]; rfl

lemma toLevelOne_levelVal (x₀ : P.Level 1) (y : P.Level 1) : P.toLevelOne x₀ (P.levelVal 1 y) = y :=
  level_ext (levelVal_toLevelOne x₀ (levelVal_mem y))

/-- In the charts `φ` of `X` and `(V₁, φ, (O₁, C₁, E¹))` of `X¹`, the identity `1₀¹` is the lift
`O → O¹`, `z ↦ z ∈ E₁`. -/
lemma levelChart_toLevelOne {φ : MChart X} (hφ : P.IsChart φ) (x₀ y₀ : P.Level 1) {x : X}
    (hx1 : x ∈ P.levelSet 1) :
    levelChart hφ y₀ (P.toLevelOne x₀ x) = φ.model.E.liftOne (φ x) := by
  rw [levelChart_apply, levelVal_toLevelOne x₀ hx1]; rfl

/-- The inclusion `ι : (O¹, C¹, E¹) → (O, C, E)` is sc-smooth between retracts (it is the
sc-operator `E¹ → E`). -/
theorem _root_.Polyfold.isScSmoothRetractMap_toBase_one {E : ScBanach} {C O : Set (E 0)} :
    IsScSmoothRetractMap E.shift (E.lvlSet C 1) (E.lvlSet O 1) E C O (E.shiftIncl 0) where
  mapsTo _ hz := hz
  comp_isScSmooth R _ := IsScSmooth.comp R.isScDomain (isScDomain_univ _)
    (E.shiftIncl.isScSmooth (isScDomain_univ _)) R.isScSmooth (mapsTo_univ _ _)

variable (P) in
/-- **Remark 4.1.3 (preprint 4.3)**: the identity `1₁⁰ : X¹ → X` (the inclusion `X₁ → X`) is always sc-smooth; in the
charts `(V₁, φ, (O₁, C₁, E¹))` and `φ` it is the inclusion `ι : E¹ → E`. -/
theorem remark_4_1_3_levelVal : P.shift.IsScSmoothMap P (P.levelVal 1) := by
  refine IsScSmoothOn.of_exists_charts isOpen_univ (continuous_levelVal 1).continuousOn
    fun y _ => ?_
  obtain ⟨φ, hφ, hyφ⟩ := P.exists_isChart_mem_source (P.levelVal 1 y)
  refine ⟨levelChart hφ y, φ, (levelChart hφ y).source, P.shift_isChart hφ y, hφ,
    (levelChart hφ y).isOpen_source, hyφ, fun z hz => ⟨mem_univ _, hz⟩, fun z hz => hz, ?_⟩
  rw [MChart.image_source]
  refine isScSmoothRetractMap_toBase_one.congr fun z hz => ?_
  have hz' : φ.model.E.toBase 1 z ∈ φ.model.O := hz
  change φ.model.E.toBase 1 z = φ (P.levelVal 1 ((levelChart hφ y).symm z))
  rw [levelChart_symm_apply hφ y hz', φ.apply_symm_apply hz']

/-- **Remark 4.1.3 (preprint 4.3)**: if `X₀ = X₁` as sets and `1₀¹ : X → X¹` is sc-smooth, it is an
sc-diffeomorphism, with inverse `1₁⁰` (which is always sc-smooth, `remark_4_1_3_levelVal`). -/
theorem remark_4_1_3_isScDiffeo (h1 : ∀ x, x ∈ P.levelSet 1) (x₀ : P.Level 1)
    (hsm : P.IsScSmoothMap P.shift (P.toLevelOne x₀)) :
    P.IsScDiffeoOn P.shift (P.toLevelOne x₀) (P.levelVal 1) univ univ where
  isScSmoothOn := hsm
  isScSmoothOn_inv := remark_4_1_3_levelVal P
  mapsTo := mapsTo_univ _ _
  mapsTo_inv := mapsTo_univ _ _
  left_inv x _ := levelVal_toLevelOne x₀ (h1 x)
  right_inv y _ := toLevelOne_levelVal x₀ y

/-- A point of a chart domain is smooth iff its image is a smooth point of `E`. -/
lemma mem_smoothSet_iff {φ : MChart X} (hφ : P.IsChart φ) {x : X} (hx : x ∈ φ.source) :
    x ∈ P.smoothSet ↔ φ x ∈ φ.model.E.smooth := by
  rw [smoothSet, mem_iInter, ScScale.mem_smooth_iff]
  refine forall_congr' fun m => ?_
  rw [P.mem_levelSet_iff hφ hx]
  exact Iff.rfl

lemma smoothSet_subset_levelSet (m : ℕ) : P.smoothSet ⊆ P.levelSet m :=
  iInter_subset _ m

/-- **Proposition 4.1.8 (preprint 4.8) in the chart form**: for a chart `φ : V → O` of the M-polyfold `X`, the
retract `(O, C, E)` is an sc⁺-retract iff `V ⊆ X_∞` and `1₀¹ : V → X¹` is sc-smooth on `V`.  In the
charts `φ` and `(V₁, φ, (O₁, C₁, E¹))`, `1₀¹` is the lift `O → O¹` (`levelChart_toLevelOne`), and
the statement is Proposition 4.1.8 (preprint 4.8) for the retract `O`. -/
theorem proposition_4_1_8_chart {φ : MChart X} (hφ : P.IsChart φ) (x₀ : P.Level 1) :
    IsScPlusRetract φ.model.E φ.model.C φ.model.O ↔
      φ.source ⊆ P.smoothSet ∧ P.IsScSmoothOn P.shift (P.toLevelOne x₀) φ.source := by
  rw [proposition_4_1_8 φ.model.isScRetract]
  constructor
  · rintro ⟨hsm, hlift⟩
    have hsub : φ.source ⊆ P.smoothSet := fun x hx =>
      (mem_smoothSet_iff hφ hx).2 (hsm (φ.mapsTo_model x hx))
    have hlev : ∀ x ∈ φ.source, P.toLevelOne x₀ x ∈ (levelChart hφ x₀).source := fun x hx => by
      change P.levelVal 1 (P.toLevelOne x₀ x) ∈ φ.source
      rw [levelVal_toLevelOne x₀ (smoothSet_subset_levelSet 1 (hsub hx))]; exact hx
    have hcont : ContinuousOn (P.toLevelOne x₀) φ.source := by
      have h1 : ContinuousOn ((levelChart hφ x₀).symm ∘ φ.model.E.liftOne ∘ φ) φ.source := by
        refine (levelChart hφ x₀).continuousOn_invFun.comp
          ((hlift.continuousOn φ.model.isScRetract).comp φ.continuousOn_toFun
            fun x hx => φ.mapsTo_model x hx) fun x hx => ?_
        exact hlift.mapsTo (φ.mapsTo_model x hx)
      refine h1.congr fun x hx => ?_
      have e1 := (levelChart hφ x₀).symm_apply_apply (hlev x hx)
      have e2 := levelChart_toLevelOne hφ x₀ x₀ (smoothSet_subset_levelSet 1 (hsub hx))
      exact e1.symm.trans (congrArg (levelChart hφ x₀).symm e2)
    refine ⟨hsub, IsScSmoothOn.of_exists_charts φ.isOpen_source hcont fun x hx => ?_⟩
    refine ⟨φ, levelChart hφ x₀, φ.source, hφ, P.shift_isChart hφ x₀, φ.isOpen_source, hx,
      fun y hy => ⟨hy, hy⟩, hlev, ?_⟩
    rw [MChart.image_source]
    refine hlift.congr fun z hz => ?_
    have hzs : φ.symm z ∈ φ.source := φ.symm_mapsTo hz
    simp only [Function.comp_apply]
    rw [levelChart_toLevelOne hφ x₀ x₀ (smoothSet_subset_levelSet 1 (hsub hzs)),
      φ.apply_symm_apply hz]
  · rintro ⟨hsub, hsmooth⟩
    have hsm : φ.model.O ⊆ φ.model.E.smooth := fun z hz => by
      have := (mem_smoothSet_iff hφ (φ.symm_mapsTo hz)).1 (hsub (φ.symm_mapsTo hz))
      rwa [φ.apply_symm_apply hz] at this
    refine ⟨hsm, ?_⟩
    have hlev : MapsTo (P.toLevelOne x₀) φ.source (levelChart hφ x₀).source := fun x hx => by
      change P.levelVal 1 (P.toLevelOne x₀ x) ∈ φ.source
      rw [levelVal_toLevelOne x₀ (smoothSet_subset_levelSet 1 (hsub hx))]; exact hx
    have h := hsmooth.smooth φ (levelChart hφ x₀) hφ (P.shift_isChart hφ x₀) φ.source
      φ.isOpen_source (fun x hx => ⟨hx, hx⟩) hlev
    rw [MChart.image_source] at h
    refine h.congr fun z hz => ?_
    have hzs : φ.symm z ∈ φ.source := φ.symm_mapsTo hz
    simp only [Function.comp_apply]
    rw [levelChart_toLevelOne hφ x₀ x₀ (smoothSet_subset_levelSet 1 (hsub hzs)),
      φ.apply_symm_apply hz]

/-- **The first condition of Theorem 4.1.2 (preprint 4.2) (ii) in charts**: `X₀ = X_∞` and `1₀¹ : X → X¹` is
sc-smooth iff the model of every chart of `X` is an sc⁺-retract (Proposition 4.1.8 (preprint 4.8) in every chart;
sc-smoothness is local, `IsScSmoothOn.of_exists_charts`). -/
theorem isScSmoothMap_toLevelOne_iff (x₀ : P.Level 1) :
    (∀ x, x ∈ P.smoothSet) ∧ P.IsScSmoothMap P.shift (P.toLevelOne x₀) ↔
      ∀ φ : MChart X, P.IsChart φ → IsScPlusRetract φ.model.E φ.model.C φ.model.O := by
  constructor
  · rintro ⟨hsm, hmap⟩ φ hφ
    exact (proposition_4_1_8_chart hφ x₀).2 ⟨fun x _ => hsm x, hmap.mono φ.isOpen_source
      (subset_univ _)⟩
  · intro h
    have hloc : ∀ x, ∃ φ : MChart X, P.IsChart φ ∧ x ∈ φ.source ∧ φ.source ⊆ P.smoothSet ∧
        P.IsScSmoothOn P.shift (P.toLevelOne x₀) φ.source := fun x => by
      obtain ⟨φ, hφ, hx⟩ := P.exists_isChart_mem_source x
      exact ⟨φ, hφ, hx, (proposition_4_1_8_chart hφ x₀).1 (h φ hφ)⟩
    have hsm : ∀ x, x ∈ P.smoothSet := fun x => by
      obtain ⟨φ, -, hx, hsub, -⟩ := hloc x
      exact hsub hx
    refine ⟨hsm, IsScSmoothOn.of_exists_charts isOpen_univ ?_ fun x _ => ?_⟩
    · refine continuousOn_univ.2 (continuous_iff_continuousAt.2 fun x => ?_)
      obtain ⟨φ, -, hx, -, hφs⟩ := hloc x
      exact hφs.continuousOn.continuousAt (φ.isOpen_source.mem_nhds hx)
    · obtain ⟨φ, hφ, hx, hsub, hφs⟩ := hloc x
      have hlev : MapsTo (P.toLevelOne x₀) φ.source (levelChart hφ x₀).source := fun y hy => by
        change P.levelVal 1 (P.toLevelOne x₀ y) ∈ φ.source
        rw [levelVal_toLevelOne x₀ (smoothSet_subset_levelSet 1 (hsub hy))]; exact hy
      exact ⟨φ, levelChart hφ x₀, φ.source, hφ, P.shift_isChart hφ x₀, φ.isOpen_source, hx,
        fun y hy => ⟨mem_univ _, hy⟩, hlev, hφs.smooth φ (levelChart hφ x₀) hφ
          (P.shift_isChart hφ x₀) φ.source φ.isOpen_source (fun y hy => ⟨hy, hy⟩) hlev⟩

variable (P) in
/-- **Definition 4.1.4 (preprint 4.4)** (second sentence): an sc-smooth retraction `r : V → V` on an open subset `V`
of the M-polyfold `X` is an **sc⁺-retraction** if `r(V) ⊆ X₁` and `r : V → V¹` (that is,
`1₀¹ ∘ r : V → X¹`) is sc-smooth.  The junk value of `1₀¹` off `X₁` plays no role
(`IsScSmoothOn.congr`); the definition quantifies over it. -/
structure IsScPlusRetractionOn (r : X → X) (V : Set X) : Prop where
  isScSmoothOn : P.IsScSmoothOn P r V
  mapsTo : MapsTo r V V
  idem : ∀ x ∈ V, r (r x) = r x
  mem_levelSet : ∀ x ∈ V, r x ∈ P.levelSet 1
  isScSmoothOn_one : ∀ x₀ : P.Level 1, P.IsScSmoothOn P.shift (P.toLevelOne x₀ ∘ r) V

end MPolyfold

end Polyfold
