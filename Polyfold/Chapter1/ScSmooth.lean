import Polyfold.Chapter1.ScBanach

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §1.1,
Definitions 1.11–1.15 (the preprint's Definition 1.14 and the inductive definition of `sc^k`
that follows it; its Remark 1.1.17 (preprint 1.15) on partial cones is formalized in
`GapP1_PartialCones.lean`: `IsPartialCone.isScDomain`, `remark_1_1_17_chainRule`).

# Partial quadrants, sc⁰ maps, the tangent construction, sc¹, sc^k and sc-smooth maps

## The text, paraphrased

(Definition 1.1.12 (preprint 1.11)) A partial quadrant in an sc-Banach space `E` is a closed convex `C ⊆ E` for which
there is an sc-isomorphism `T : E → ℝⁿ ⊕ W` with `T(C) = [0,∞)ⁿ ⊕ W`.  One considers tuples
`(U, C, E)` with `U` relatively open in `C`.  (Definition 1.1.13 (preprint 1.12)) `f : U → U'` is sc⁰ if
`f(U_m) ⊆ U'_m` and `f : U_m → U'_m` is continuous for all `m`.  (Definition 1.1.14 (preprint 1.13)) The tangent of
`(U, C, E)` is `(TU, TC, TE) = (U¹ ⊕ E, C¹ ⊕ E, E¹ ⊕ E)`.  (Definition 1.1.15 (preprint 1.14)) `f : U → U'` is sc¹ if
(1) `f` is sc⁰; (2) for every `x ∈ U₁` there is a bounded linear `Df(x) : E₀ → F₀` with
`|f(x+h) − f(x) − Df(x)h|₀ / |h|₁ → 0` as `|h|₁ → 0`, `h ∈ E₁`, `x + h ∈ U₁`; (3) the tangent
map `Tf : TU → TU'`, `Tf(x, h) = (f(x), Df(x)h)`, is sc⁰.  Inductively, `f` is sc^{k+1} if it is sc¹
and `Tf` is sc^k; `f` is sc-smooth if it is sc^k for all `k`.

## What is formalized

* `ScBanach.lvlSet U m` is `U_m = U ∩ E_m` (the preimage of `U` in `E m`);
  `ScBanach.tangent E` is `TE = E¹ ⊕ E`, with levels `E_{m+1} × E_m`; `ScBanach.tangentSet U`
  is `TU = U¹ ⊕ E` as a subset of `(TE)₀ = E₁ × E₀`.
* `Polyfold.levelMap f m : E m → F m` is the map induced by `f : E₀ → F₀` on level `m` (defined
  through the injectivity of the inclusions, meaningful where `f` maps `E_m` into `F_m`).
* `Polyfold.IsSc0 E F U f` (**Definition 1.1.13 (preprint 1.12)**), `Polyfold.IsSc1With U f D` (**Definition 1.1.15 (preprint 1.14)**
  with the derivative family `D` made explicit), `Polyfold.IsSc1 U f` (`∃ D`),
  `Polyfold.scDeriv U f` (a choice of `D`), `Polyfold.tangentMap U f` (`Tf`),
  `Polyfold.IsSck k U f`, `Polyfold.IsScSmooth U f` (**Definition 1.1.15 and p. 10 (preprint: before Remark 1.15)** in the book's numbering).
* `Polyfold.IsPartialQuadrant E C` (**Definition 1.1.12 (preprint 1.11)**), `Polyfold.IsRelOpenInQuadrant E C U`
  (the tuple `(U, C, E)`), and `Polyfold.IsScDomain E U`, the level-wise consequences used by the
  chain rule: each `U_m` is open-in-convex, and each point of `U_m` is a point of unique
  differentiability; `IsScDomain.tangentSet` propagates this to `TU`.
* `IsSc1With.eq_of_uniqueDiffWithinAt`: on a domain with unique differentiability, `Df(x)` is
  determined by `f` for `x ∈ U₁` (so `Tf` is well defined).

## What the text leaves implicit, and the choices made

* Maps are total functions `f : E₀ → F₀`; only the values on `U` matter (`IsSc0.congr`,
  `IsSc1With.congr`).  The target `U'` plays no role in the definitions beyond `MapsTo f U U'`,
  so it is not an argument.
* Condition (2) of Definition 1.1.15 (preprint 1.14), a limit over `h ∈ E₁` with `x + h ∈ U₁`, is Mathlib's
  `HasFDerivWithinAt (f ∘ ι₁) (Df(x) ∘ ι₁) U₁ x`, `ι₁ : E₁ → E₀`: the differentiability of
  `f : U₁ → F₀` at `x` within `U₁`, with derivative `Df(x)|_{E₁}`.
* The text writes `Df(x)` as if unique.  It is, when `U₁` has unique differentiability at `x` and
  `E₁` is dense in `E₀` (`IsSc1With.eq_of_uniqueDiffWithinAt`); without such a hypothesis `Tf` is
  defined through a choice (`scDeriv`), and `IsSck` uses that choice.  For relatively open subsets
  of partial quadrants the choice is immaterial (`IsSc1.scDeriv_eqOn`).
* The text's `T(U, C, E)` is again a tuple; the formalization carries only the consequence
  needed for the chain rule (`IsScDomain`), which is stable under `T`.  That `TC` is a partial
  quadrant in `TE` (an sc-isomorphism `(ℝⁿ ⊕ W)¹ ⊕ (ℝⁿ ⊕ W) ≅ ℝⁿ ⊕ W'`) is not proved.
* `IsPartialQuadrant` asks for `C = T⁻¹([0,∞)ⁿ ⊕ W)`; closedness and convexity of `C` follow
  (`IsPartialQuadrant.isClosed_lvlSet`, `IsPartialQuadrant.convex_lvlSet`).
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

namespace ScBanach

variable (E : ScBanach)

/-! ### Levels of a subset -/

/-- `U_m = U ∩ E_m`, the part of `U ⊆ E₀` on level `m`, as a subset of `E m`. -/
def lvlSet (U : Set (E 0)) (m : ℕ) : Set (E m) := E.toBase m ⁻¹' U

lemma mem_lvlSet {U : Set (E 0)} {m : ℕ} {x : E m} : x ∈ E.lvlSet U m ↔ E.toBase m x ∈ U := Iff.rfl

@[simp] lemma lvlSet_zero (U : Set (E 0)) : E.lvlSet U 0 = U := rfl

lemma lvlSet_succ (U : Set (E 0)) (m : ℕ) : E.lvlSet U (m + 1) = E.incl m ⁻¹' E.lvlSet U m := rfl

lemma lvlSet_mono {U V : Set (E 0)} (h : U ⊆ V) (m : ℕ) : E.lvlSet U m ⊆ E.lvlSet V m :=
  preimage_mono h

lemma lvlSet_inter (U V : Set (E 0)) (m : ℕ) : E.lvlSet (U ∩ V) m = E.lvlSet U m ∩ E.lvlSet V m :=
  rfl

@[simp] lemma lvlSet_univ (m : ℕ) : E.lvlSet univ m = univ := rfl

lemma isOpen_lvlSet {U : Set (E 0)} (hU : IsOpen U) (m : ℕ) : IsOpen (E.lvlSet U m) :=
  hU.preimage (E.toBase m).continuous

lemma isClosed_lvlSet {U : Set (E 0)} (hU : IsClosed U) (m : ℕ) : IsClosed (E.lvlSet U m) :=
  hU.preimage (E.toBase m).continuous

lemma convex_lvlSet {C : Set (E 0)} (hC : Convex ℝ C) (m : ℕ) : Convex ℝ (E.lvlSet C m) :=
  hC.linear_preimage (E.toBase m : E m →ₗ[ℝ] E 0)

lemma mapsTo_toBase_lvlSet (U : Set (E 0)) (m : ℕ) : MapsTo (E.toBase m) (E.lvlSet U m) U :=
  fun _ hx => hx

/-! ### The tangent `TE = E¹ ⊕ E` -/

/-- The tangent `TE = E¹ ⊕ E` of an sc-Banach space (Definition 1.1.14 (preprint 1.13)), with levels
`(TE)_m = E_{m+1} × E_m`. -/
abbrev tangent : ScBanach := E.shift.prod E

@[simp] lemma tangent_lvl (m : ℕ) : E.tangent m = (E (m + 1) × E m) := rfl

lemma tangent_toBase (m : ℕ) (p : E.tangent m) :
    E.tangent.toBase m p = ((E.shift.toBase m p.1, E.toBase m p.2) : E.tangent 0) :=
  prod_toBase _ _ m p

lemma tangent_incl (m : ℕ) (p : E.tangent (m + 1)) :
    E.tangent.incl m p = ((E.incl (m + 1) p.1, E.incl m p.2) : E.tangent m) := rfl

/-- `TU = U¹ ⊕ E ⊆ (TE)₀ = E₁ × E₀` (Definition 1.1.14 (preprint 1.13)). -/
def tangentSet (U : Set (E 0)) : Set (E.tangent 0) := {p | p.1 ∈ E.lvlSet U 1}

lemma mem_tangentSet {U : Set (E 0)} {p : E.tangent 0} : p ∈ E.tangentSet U ↔ p.1 ∈ E.lvlSet U 1 :=
  Iff.rfl

/-- The level-`m` part of `TU` is `U_{m+1} × E_m`. -/
lemma mem_lvlSet_tangentSet {U : Set (E 0)} {m : ℕ} {p : E.tangent m} :
    p ∈ E.tangent.lvlSet (E.tangentSet U) m ↔ p.1 ∈ E.lvlSet U (m + 1) := by
  rw [mem_lvlSet, mem_tangentSet, tangent_toBase]
  change E.toBase 1 (E.shift.toBase m p.1) ∈ U ↔ E.toBase (m + 1) p.1 ∈ U
  rw [← E.shift_toBase m p.1]

lemma tangentSet_mono {U V : Set (E 0)} (h : U ⊆ V) : E.tangentSet U ⊆ E.tangentSet V :=
  fun _ hp => E.lvlSet_mono h 1 hp

/-- `(TU)_m = U_{m+1} × E_m` as sets. -/
lemma lvlSet_tangentSet (U : Set (E 0)) (m : ℕ) :
    E.tangent.lvlSet (E.tangentSet U) m = E.lvlSet U (m + 1) ×ˢ univ := by
  ext q
  rw [mem_lvlSet_tangentSet]
  change _ ↔ q.1 ∈ E.lvlSet U (m + 1) ∧ q.2 ∈ univ
  simp

end ScBanach

/-! ### Level maps and sc⁰ maps (Definition 1.1.13 (preprint 1.12)) -/

variable {E F G : ScBanach}

/-- The map `f_m : E_m → F_m` induced by `f : E₀ → F₀` on level `m`: `f_m x` is the (unique, by
injectivity) `y ∈ F_m` with `ι_m y = f (ι_m x)`, when it exists (otherwise a junk value). -/
def levelMap (f : E 0 → F 0) (m : ℕ) (x : E m) : F m :=
  Function.invFun (F.toBase m) (f (E.toBase m x))

lemma toBase_levelMap {f : E 0 → F 0} {m : ℕ} {x : E m}
    (h : f (E.toBase m x) ∈ range (F.toBase m)) :
    F.toBase m (levelMap f m x) = f (E.toBase m x) :=
  Function.invFun_eq h

@[simp] lemma levelMap_zero (f : E 0 → F 0) (x : E 0) : levelMap f 0 x = f x :=
  toBase_levelMap (F := F) ⟨f x, rfl⟩

lemma levelMap_eq_of_toBase_eq {f : E 0 → F 0} {m : ℕ} {x : E m} {y : F m}
    (h : F.toBase m y = f (E.toBase m x)) : levelMap f m x = y :=
  F.toBase_injective m (by rw [toBase_levelMap ⟨y, h⟩, h])

/-- `f : U → F` is **sc⁰** (Definition 1.1.13 (preprint 1.12)): for every `m`, `f` maps `U_m` into `F_m` and the
induced map `f_m : U_m → F_m` is continuous. -/
structure IsSc0 (E F : ScBanach) (U : Set (E 0)) (f : E 0 → F 0) : Prop where
  mem_range : ∀ m, ∀ x ∈ E.lvlSet U m, f (E.toBase m x) ∈ range (F.toBase m)
  continuousOn : ∀ m, ContinuousOn (levelMap f m) (E.lvlSet U m)

namespace IsSc0

variable {U : Set (E 0)} {V : Set (F 0)} {f : E 0 → F 0} {g : F 0 → G 0}

lemma toBase_levelMap (hf : IsSc0 E F U f) {m : ℕ} {x : E m} (hx : x ∈ E.lvlSet U m) :
    F.toBase m (levelMap f m x) = f (E.toBase m x) :=
  Polyfold.toBase_levelMap (hf.mem_range m x hx)

lemma levelMap_mapsTo (hf : IsSc0 E F U f) (hfV : MapsTo f U V) (m : ℕ) :
    MapsTo (levelMap f m) (E.lvlSet U m) (F.lvlSet V m) := fun x hx => by
  rw [ScBanach.mem_lvlSet, hf.toBase_levelMap hx]
  exact hfV hx

lemma continuousOn_base (hf : IsSc0 E F U f) : ContinuousOn f U := by
  have := hf.continuousOn 0
  simpa [funext (levelMap_zero f)] using this

lemma mono (hf : IsSc0 E F U f) {U' : Set (E 0)} (h : U' ⊆ U) : IsSc0 E F U' f :=
  ⟨fun m x hx => hf.mem_range m x (E.lvlSet_mono h m hx),
    fun m => (hf.continuousOn m).mono (E.lvlSet_mono h m)⟩

lemma levelMap_congr {f' : E 0 → F 0} (h : EqOn f f' U) {m : ℕ} {x : E m}
    (hx : x ∈ E.lvlSet U m) : levelMap f m x = levelMap f' m x := by
  simp only [levelMap, h hx]

/-- sc⁰ depends only on the values on `U`. -/
lemma congr (hf : IsSc0 E F U f) {f' : E 0 → F 0} (h : EqOn f f' U) : IsSc0 E F U f' :=
  ⟨fun m x hx => by rw [← h hx]; exact hf.mem_range m x hx,
    fun m => (hf.continuousOn m).congr fun x hx => (levelMap_congr h hx).symm⟩

lemma levelMap_comp (hg : IsSc0 F G V g) (hf : IsSc0 E F U f) (hfV : MapsTo f U V) {m : ℕ}
    {x : E m} (hx : x ∈ E.lvlSet U m) :
    levelMap (g ∘ f) m x = levelMap g m (levelMap f m x) := by
  apply levelMap_eq_of_toBase_eq
  rw [hg.toBase_levelMap (hf.levelMap_mapsTo hfV m hx), hf.toBase_levelMap hx]
  rfl

/-- The composition of sc⁰ maps is sc⁰. -/
lemma comp (hg : IsSc0 F G V g) (hf : IsSc0 E F U f) (hfV : MapsTo f U V) :
    IsSc0 E G U (g ∘ f) where
  mem_range m x hx := by
    change g (f (E.toBase m x)) ∈ _
    rw [← hf.toBase_levelMap hx]
    exact hg.mem_range m _ (hf.levelMap_mapsTo hfV m hx)
  continuousOn m :=
    ((hg.continuousOn m).comp (hf.continuousOn m) (hf.levelMap_mapsTo hfV m)).congr
      fun x hx => hg.levelMap_comp hf hfV hx

end IsSc0

lemma isSc0_id (U : Set (E 0)) : IsSc0 E E U id :=
  ⟨fun _ x _ => ⟨x, rfl⟩, fun _ => (continuousOn_id).congr fun _ _ =>
    levelMap_eq_of_toBase_eq (f := (id : E 0 → E 0)) rfl⟩

/-- An sc-operator is sc⁰ on all of `E`, with level maps `T m`. -/
lemma ScOperator.isSc0 (T : ScOperator E F) : IsSc0 E F univ (T 0) :=
  ⟨fun m x _ => ⟨T m x, T.toBase_comm m x⟩, fun m => (T m).continuous.continuousOn.congr
    fun x _ => levelMap_eq_of_toBase_eq (T.toBase_comm m x)⟩

lemma ScOperator.levelMap_eq (T : ScOperator E F) (m : ℕ) (x : E m) : levelMap (T 0) m x = T m x :=
  levelMap_eq_of_toBase_eq (T.toBase_comm m x)

/-! ### The tangent map and sc¹ maps (Definitions 1.1.14, 1.1.15 (preprint 1.13, 1.14)) -/

/-- The tangent map `Tf : TU → TF`, `Tf(x, h) = (f(x), Df(x) h)`, for a given family of
derivatives `D x = Df(x)`, `x ∈ E₁`. -/
def tangentMapWith (f : E 0 → F 0) (D : E 1 → E 0 →L[ℝ] F 0) (p : E.tangent 0) : F.tangent 0 :=
  (levelMap f 1 p.1, D p.1 p.2)

/-- `f : U → F` is **sc¹ with derivative family `D`** (Definition 1.1.15 (preprint 1.14)): `f` is sc⁰; for every
`x ∈ U₁`, `f : U₁ → F₀` is differentiable at `x` within `U₁` with derivative `D x ∘ ι₁`, where
`D x : E₀ → F₀` is bounded linear (condition (2)); and the tangent map `Tf : TU → TF` is sc⁰
(condition (3)). -/
structure IsSc1With (U : Set (E 0)) (f : E 0 → F 0) (D : E 1 → E 0 →L[ℝ] F 0) : Prop where
  isSc0 : IsSc0 E F U f
  hasFDerivWithinAt : ∀ x ∈ E.lvlSet U 1,
    HasFDerivWithinAt (f ∘ E.toBase 1) ((D x).comp (E.toBase 1)) (E.lvlSet U 1) x
  tangent_isSc0 : IsSc0 E.tangent F.tangent (E.tangentSet U) (tangentMapWith f D)

/-- `f : U → F` is **sc¹** (Definition 1.1.15 (preprint 1.14)): there is a family `Df(x)`, `x ∈ U₁`, as in
`IsSc1With`. -/
def IsSc1 (U : Set (E 0)) (f : E 0 → F 0) : Prop := ∃ D, IsSc1With U f D

open scoped Classical in
/-- A choice of derivative family `Df` for `f` on `U` (junk if `f` is not sc¹). -/
def scDeriv (U : Set (E 0)) (f : E 0 → F 0) : E 1 → E 0 →L[ℝ] F 0 :=
  if h : IsSc1 U f then h.choose else fun _ => 0

/-- The tangent map `Tf : TU → TF` of `f` (Definition 1.1.15 (preprint 1.14) (3)), with the chosen derivative. -/
def tangentMap (U : Set (E 0)) (f : E 0 → F 0) : E.tangent 0 → F.tangent 0 :=
  tangentMapWith f (scDeriv U f)

namespace IsSc1With

variable {U : Set (E 0)} {f : E 0 → F 0} {D : E 1 → E 0 →L[ℝ] F 0}

lemma isSc1 (h : IsSc1With U f D) : IsSc1 U f := ⟨D, h⟩

lemma tangentMapWith_mapsTo (h : IsSc1With U f D) {V : Set (F 0)} (hfV : MapsTo f U V) :
    MapsTo (tangentMapWith f D) (E.tangentSet U) (F.tangentSet V) :=
  fun _ hp => h.isSc0.levelMap_mapsTo hfV 1 hp

/-- The level-`0` part of the tangent map, `(x, h) ↦ Df(x) h`, is continuous on `U₁ × E₀`
(the "compact-open continuity" of `x ↦ Df(x)`). -/
lemma continuousOn_deriv (h : IsSc1With U f D) :
    ContinuousOn (fun p : E 1 × E 0 => D p.1 p.2) {p | p.1 ∈ E.lvlSet U 1} := by
  have := (h.tangent_isSc0.continuousOn 0)
  refine (continuous_snd.comp_continuousOn this).congr fun p _ => ?_
  change D p.1 p.2 = (levelMap (tangentMapWith f D) 0 p).2
  rw [levelMap_zero]; rfl

lemma congr (h : IsSc1With U f D) {f' : E 0 → F 0} (hff' : EqOn f f' U) : IsSc1With U f' D where
  isSc0 := h.isSc0.congr hff'
  hasFDerivWithinAt x hx := (h.hasFDerivWithinAt x hx).congr' (fun y hy => (hff' hy).symm) hx
  tangent_isSc0 := h.tangent_isSc0.congr fun p hp => by
    change (levelMap f 1 p.1, D p.1 p.2) = (levelMap f' 1 p.1, D p.1 p.2)
    rw [IsSc0.levelMap_congr hff' hp]

/-- The derivative family depends only on the values of `f` on `U`, at points of unique
differentiability: if `Df` and `Df'` both satisfy Definition 1.1.15 (preprint 1.14) then `Df(x) = Df'(x)` for
`x ∈ U₁` (using that `E₁` is dense in `E₀`). -/
lemma eq_of_uniqueDiffWithinAt (h : IsSc1With U f D) {D' : E 1 → E 0 →L[ℝ] F 0}
    (h' : IsSc1With U f D') {x : E 1} (hx : x ∈ E.lvlSet U 1)
    (hU : UniqueDiffWithinAt ℝ (E.lvlSet U 1) x) : D x = D' x := by
  have h1 := hU.eq (h.hasFDerivWithinAt x hx) (h'.hasFDerivWithinAt x hx)
  have hd : Dense (Submodule.span ℝ (range (E.toBase 1)) : Set (E 0)) := by
    refine Dense.mono Submodule.subset_span ?_
    exact E.denseRange_inclK 0 1
  refine ContinuousLinearMap.ext_on hd ?_
  rintro _ ⟨y, rfl⟩
  exact congrArg (fun L : E 1 →L[ℝ] F 0 => L y) h1

end IsSc1With

namespace IsSc1

variable {U : Set (E 0)} {f : E 0 → F 0}

lemma isSc1With_scDeriv (h : IsSc1 U f) : IsSc1With U f (scDeriv U f) := by
  rw [scDeriv, dif_pos h]; exact h.choose_spec

lemma isSc0 (h : IsSc1 U f) : IsSc0 E F U f := h.isSc1With_scDeriv.isSc0

lemma tangentMap_isSc0 (h : IsSc1 U f) :
    IsSc0 E.tangent F.tangent (E.tangentSet U) (tangentMap U f) :=
  h.isSc1With_scDeriv.tangent_isSc0

lemma tangentMap_mapsTo (h : IsSc1 U f) {V : Set (F 0)} (hfV : MapsTo f U V) :
    MapsTo (tangentMap U f) (E.tangentSet U) (F.tangentSet V) :=
  h.isSc1With_scDeriv.tangentMapWith_mapsTo hfV

/-- On a domain with unique differentiability, the chosen derivative agrees on `U₁` with any
family satisfying Definition 1.1.15 (preprint 1.14). -/
lemma scDeriv_eqOn {D : E 1 → E 0 →L[ℝ] F 0} (h : IsSc1With U f D)
    (hU : ∀ x ∈ E.lvlSet U 1, UniqueDiffWithinAt ℝ (E.lvlSet U 1) x) :
    EqOn (scDeriv U f) D (E.lvlSet U 1) :=
  fun x hx => h.isSc1.isSc1With_scDeriv.eq_of_uniqueDiffWithinAt h hx (hU x hx)

/-- On a domain with unique differentiability, the tangent map agrees on `TU` with the tangent
map built from any derivative family satisfying Definition 1.1.15 (preprint 1.14). -/
lemma tangentMap_eqOn {D : E 1 → E 0 →L[ℝ] F 0} (h : IsSc1With U f D)
    (hU : ∀ x ∈ E.lvlSet U 1, UniqueDiffWithinAt ℝ (E.lvlSet U 1) x) :
    EqOn (tangentMap U f) (tangentMapWith f D) (E.tangentSet U) := by
  intro p hp
  change (levelMap f 1 p.1, scDeriv U f p.1 p.2) = (levelMap f 1 p.1, D p.1 p.2)
  rw [scDeriv_eqOn h hU hp]

lemma congr (h : IsSc1 U f) {f' : E 0 → F 0} (hff' : EqOn f f' U) : IsSc1 U f' :=
  ⟨_, h.isSc1With_scDeriv.congr hff'⟩

end IsSc1

/-! ### sc^k and sc-smooth maps (Definition 1.1.15 and p. 10 (preprint: before Remark 1.15)) -/

/-- `f : U → F` is **sc^k** (Definition 1.1.15 and p. 10 (preprint: before Remark 1.15)): sc⁰ for `k = 0`; for `k + 1`, sc¹ with `Tf : TU → TF`
sc^k. -/
def IsSck : ℕ → ∀ (E F : ScBanach), Set (E 0) → (E 0 → F 0) → Prop
  | 0, E, F, U, f => IsSc0 E F U f
  | k + 1, E, F, U, f => IsSc1 U f ∧ IsSck k E.tangent F.tangent (E.tangentSet U) (tangentMap U f)

/-- `f : U → F` is **sc-smooth** (sc^∞, Definition 1.1.15 and p. 10 (preprint: before Remark 1.15)): sc^k for every `k`. -/
def IsScSmooth (U : Set (E 0)) (f : E 0 → F 0) : Prop := ∀ k, IsSck k E F U f

lemma isSck_zero_iff {U : Set (E 0)} {f : E 0 → F 0} : IsSck 0 E F U f ↔ IsSc0 E F U f := Iff.rfl

lemma isSck_succ_iff {k : ℕ} {U : Set (E 0)} {f : E 0 → F 0} :
    IsSck (k + 1) E F U f ↔
      IsSc1 U f ∧ IsSck k E.tangent F.tangent (E.tangentSet U) (tangentMap U f) := Iff.rfl

lemma IsSck.isSc0 : ∀ {k : ℕ} {E F : ScBanach} {U : Set (E 0)} {f : E 0 → F 0},
    IsSck k E F U f → IsSc0 E F U f
  | 0, _, _, _, _, h => h
  | _ + 1, _, _, _, _, h => h.1.isSc0

lemma IsSck.isSc1 {k : ℕ} {U : Set (E 0)} {f : E 0 → F 0} (h : IsSck (k + 1) E F U f) : IsSc1 U f :=
  h.1

/-- sc^{k+1} implies sc^k. -/
lemma IsSck.of_succ : ∀ {k : ℕ} {E F : ScBanach} {U : Set (E 0)} {f : E 0 → F 0},
    IsSck (k + 1) E F U f → IsSck k E F U f
  | 0, _, _, _, _, h => h.1.isSc0
  | k + 1, _, _, _, _, h => ⟨h.1, IsSck.of_succ (k := k) h.2⟩

lemma IsSck.of_le {k l : ℕ} (hkl : k ≤ l) {U : Set (E 0)} {f : E 0 → F 0} (h : IsSck l E F U f) :
    IsSck k E F U f := by
  induction hkl with
  | refl => exact h
  | step _ ih => exact ih h.of_succ

lemma IsScSmooth.isSck {U : Set (E 0)} {f : E 0 → F 0} (h : IsScSmooth U f) (k : ℕ) :
    IsSck k E F U f := h k

lemma IsScSmooth.isSc1 {U : Set (E 0)} {f : E 0 → F 0} (h : IsScSmooth U f) : IsSc1 U f :=
  (h 1).isSc1

/-- `f` is sc-smooth iff it is sc¹ with sc-smooth tangent map. -/
lemma isScSmooth_iff {U : Set (E 0)} {f : E 0 → F 0} :
    IsScSmooth U f ↔ IsSc1 U f ∧ IsScSmooth (E.tangentSet U) (tangentMap U f) :=
  ⟨fun h => ⟨h.isSc1, fun k => (h (k + 1)).2⟩, fun h k => by
    cases k with
    | zero => exact h.1.isSc0
    | succ k => exact ⟨h.1, h.2 k⟩⟩

/-! ### Partial quadrants (Definition 1.1.12 (preprint 1.11)) and the tuples `(U, C, E)` -/

/-- The quadrant `[0,∞)ⁿ ⊕ W` on level `m` of the sc-Banach space `ℝⁿ ⊕ W`. -/
def quadrant (n : ℕ) (W : ScBanach) (m : ℕ) : Set (((ScBanach.const (Fin n → ℝ)).prod W) m) :=
  {p | ∀ i, 0 ≤ p.1 i}

lemma quadrant_convex (n : ℕ) (W : ScBanach) (m : ℕ) : Convex ℝ (quadrant n W m) := by
  intro p hp q hq a b ha hb _ i
  exact add_nonneg (mul_nonneg ha (hp i)) (mul_nonneg hb (hq i))

lemma quadrant_isClosed (n : ℕ) (W : ScBanach) (m : ℕ) : IsClosed (quadrant n W m) := by
  have : quadrant n W m = ⋂ i, {p : (Fin n → ℝ) × W m | 0 ≤ p.1 i} := Set.ofPred_forall _
  rw [this]
  exact isClosed_iInter fun i =>
    isClosed_le continuous_const ((continuous_apply i).comp continuous_fst)

lemma quadrant_interior_nonempty (n : ℕ) (W : ScBanach) (m : ℕ) :
    (interior (quadrant n W m)).Nonempty := by
  refine ⟨((fun _ => 1, 0) : (Fin n → ℝ) × W m), ?_⟩
  rw [mem_interior]
  refine ⟨⋂ i, {p : (Fin n → ℝ) × W m | 0 < p.1 i}, fun p hp i => ?_, ?_, ?_⟩
  · exact le_of_lt (mem_iInter.1 hp i)
  · exact isOpen_iInter_of_finite fun i =>
      isOpen_lt continuous_const ((continuous_apply i).comp continuous_fst)
  · exact mem_iInter.2 fun i => show (0 : ℝ) < 1 from zero_lt_one

/-- The quadrants on the levels are the level sets of the quadrant on level `0`. -/
lemma lvlSet_quadrant (n : ℕ) (W : ScBanach) (m : ℕ) :
    ((ScBanach.const (Fin n → ℝ)).prod W).lvlSet (quadrant n W 0) m = quadrant n W m := by
  ext p
  rw [ScBanach.mem_lvlSet, ScBanach.prod_toBase]
  change (∀ i, 0 ≤ (ScBanach.const (Fin n → ℝ)).toBase m p.1 i) ↔ ∀ i, 0 ≤ p.1 i
  rw [ScBanach.const_toBase]

/-- `C ⊆ E` is a **partial quadrant** (Definition 1.1.12 (preprint 1.11)): `C = T⁻¹([0,∞)ⁿ ⊕ W)` for an
sc-isomorphism `T : E → ℝⁿ ⊕ W`. -/
def IsPartialQuadrant (E : ScBanach) (C : Set (E 0)) : Prop :=
  ∃ (n : ℕ) (W : ScBanach) (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)),
    C = T 0 ⁻¹' quadrant n W 0

namespace IsPartialQuadrant

variable {C : Set (E 0)}

/-- The level-`m` part of a partial quadrant is the preimage of the level-`m` quadrant. -/
lemma lvlSet_eq {n : ℕ} {W : ScBanach} (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (m : ℕ) : E.lvlSet (T 0 ⁻¹' quadrant n W 0) m = T m ⁻¹' quadrant n W m := by
  ext x
  rw [ScBanach.mem_lvlSet, mem_preimage, mem_preimage, ← T.toBase_comm,
    ← ScBanach.mem_lvlSet, lvlSet_quadrant]

lemma convex_lvlSet (hC : IsPartialQuadrant E C) (m : ℕ) : Convex ℝ (E.lvlSet C m) := by
  obtain ⟨n, W, T, rfl⟩ := hC
  rw [lvlSet_eq]
  exact (quadrant_convex n W m).linear_preimage (T m : E m →ₗ[ℝ] _)

lemma isClosed_lvlSet (hC : IsPartialQuadrant E C) (m : ℕ) : IsClosed (E.lvlSet C m) := by
  obtain ⟨n, W, T, rfl⟩ := hC
  rw [lvlSet_eq]
  exact (quadrant_isClosed n W m).preimage (T m).continuous

lemma interior_lvlSet_nonempty (hC : IsPartialQuadrant E C) (m : ℕ) :
    (interior (E.lvlSet C m)).Nonempty := by
  obtain ⟨n, W, T, rfl⟩ := hC
  rw [lvlSet_eq, ← (T m).isOpenMap.preimage_interior_eq_interior_preimage (T m).continuous]
  exact (quadrant_interior_nonempty n W m).preimage (T m).surjective

lemma convex (hC : IsPartialQuadrant E C) : Convex ℝ C := hC.convex_lvlSet 0

lemma isClosed (hC : IsPartialQuadrant E C) : IsClosed C := hC.isClosed_lvlSet 0

lemma uniqueDiffWithinAt_lvlSet (hC : IsPartialQuadrant E C) {m : ℕ} {x : E m}
    (hx : x ∈ E.lvlSet C m) : UniqueDiffWithinAt ℝ (E.lvlSet C m) x :=
  uniqueDiffWithinAt_convex (hC.convex_lvlSet m) (hC.interior_lvlSet_nonempty m) (subset_closure hx)

end IsPartialQuadrant

/-- The whole space is a partial quadrant (`n = 0`). -/
lemma isPartialQuadrant_univ (E : ScBanach) : IsPartialQuadrant E univ := by
  refine ⟨0, E, ?_, ?_⟩
  · exact
      { lvl := fun m => (ContinuousLinearEquiv.uniqueProd ℝ (E m) (Fin 0 → ℝ)).symm
        incl_comm := fun m x => Prod.ext (funext fun i => i.elim0) rfl }
  · ext x; simp [quadrant]

/-- The tuple `(U, C, E)` of the text: `U` is a **relatively open subset of the partial quadrant
`C`** in `E`. -/
structure IsRelOpenInQuadrant (E : ScBanach) (C U : Set (E 0)) : Prop where
  isPartialQuadrant : IsPartialQuadrant E C
  relOpen : ∃ O : Set (E 0), IsOpen O ∧ U = O ∩ C

/-- The level-wise regularity of a domain `U ⊆ E₀` used by the chain rule: on every level `m`,
`U_m` is the intersection of an open set with a convex set, and every point of `U_m` is a point of
unique differentiability of `U_m`.  Relatively open subsets of partial quadrants have it
(`IsRelOpenInQuadrant.isScDomain`), and it passes to the tangent `TU` (`IsScDomain.tangentSet`),
which lets the chain rule be iterated to sc^k. -/
structure IsScDomain (E : ScBanach) (U : Set (E 0)) : Prop where
  relOpenConvex : ∀ m, ∃ O C : Set (E m), IsOpen O ∧ Convex ℝ C ∧ E.lvlSet U m = O ∩ C
  uniqueDiffWithinAt : ∀ m, ∀ x ∈ E.lvlSet U m, UniqueDiffWithinAt ℝ (E.lvlSet U m) x

lemma IsRelOpenInQuadrant.isScDomain {C U : Set (E 0)} (h : IsRelOpenInQuadrant E C U) :
    IsScDomain E U where
  relOpenConvex m := by
    obtain ⟨O, hO, rfl⟩ := h.relOpen
    exact ⟨E.lvlSet O m, E.lvlSet C m, E.isOpen_lvlSet hO m, h.isPartialQuadrant.convex_lvlSet m,
      rfl⟩
  uniqueDiffWithinAt m x hx := by
    obtain ⟨O, hO, rfl⟩ := h.relOpen
    rw [ScBanach.lvlSet_inter] at hx ⊢
    rw [inter_comm]
    exact (h.isPartialQuadrant.uniqueDiffWithinAt_lvlSet hx.2).inter
      ((E.isOpen_lvlSet hO m).mem_nhds hx.1)

lemma IsScDomain.tangentSet {U : Set (E 0)} (h : IsScDomain E U) :
    IsScDomain E.tangent (E.tangentSet U) where
  relOpenConvex m := by
    obtain ⟨O, C, hO, hC, hU⟩ := h.relOpenConvex (m + 1)
    refine ⟨O ×ˢ univ, C ×ˢ univ, hO.prod isOpen_univ, hC.prod convex_univ, ?_⟩
    ext p
    rw [ScBanach.mem_lvlSet_tangentSet, hU]
    change p.1 ∈ O ∩ C ↔ (p.1 ∈ O ∧ p.2 ∈ univ) ∧ (p.1 ∈ C ∧ p.2 ∈ univ)
    simp
  uniqueDiffWithinAt m p hp := by
    have h1 := (h.uniqueDiffWithinAt (m + 1) p.1 (E.mem_lvlSet_tangentSet.1 hp)).prod
      (uniqueDiffWithinAt_univ (x := p.2))
    rw [ScBanach.lvlSet_tangentSet]
    exact h1

lemma IsScDomain.uniqueDiffWithinAt_one {U : Set (E 0)} (h : IsScDomain E U) :
    ∀ x ∈ E.lvlSet U 1, UniqueDiffWithinAt ℝ (E.lvlSet U 1) x :=
  h.uniqueDiffWithinAt 1

end Polyfold
