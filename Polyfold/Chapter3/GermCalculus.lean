import Polyfold.Chapter3.GermFilling
import Polyfold.Chapter3.GermLevels
import Polyfold.Chapter2.StrongBundle
import Polyfold.Chapter2.TangentBundle
import Polyfold.Chapter1.LevelsWeak

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.1,
Definitions 3.1–3.2, 3.4, 3.6, 3.11 and Lemma 3.17: **the calculus of sc-smooth germs** that the
germ reading of Definition 3.11 needs (phase 2; Findings, Chapter 3, items 270–274).

# The germ calculus for Definition 3.11

## The text, paraphrased

The text treats the filling `g` of Definition 3.6, the local sc⁺-section `s` of Definition 3.11
and the push-forward `Ψ_*(g)` as sc-smooth *germs* (Definition 3.2) on sc-germs of
neighbourhoods `O(C, 0)` (Definition 3.1) whose levels `U_m` may shrink with `m`, and it forms
sums (`g + s`, Lemma 3.17), differences (`g − s`), the map `[1 − ρ(r(y))]g(y)` of Definition
3.4 (3), compositions with the whole-chart maps `R`, `r`, `Ψ`, `ψ⁻¹` and products with `ℝⁿ`
(Theorem 3.18) without comment: "the usual calculus" of sc-smooth maps.

## What is formalized

* **Germ arithmetic**: `IsSc1GermWith.add`, `neg`, `sub`, `smul`, `operator_comp` (with the
  derivative families `Df + Dg`, `−Df`, `Df − Dg`, `c • Df`, `T ∘ Df`), `IsSckGerm.add`, `neg`,
  `sub`, `smul` and `IsScSmoothGerm.add`, `neg`, `sub`, `smul`, `operator_comp`; on the
  intersection `G₁ ∩ G₂` of two germs: `IsSckGerm.add_inter`, `sub_inter`,
  `IsScSmoothGerm.add_inter`, `sub_inter`, `IsSc1GermWith.add_inter`, `sub_inter`.
  Monotonicity is `IsSckGerm.mono`, `IsScSmoothGerm.mono` (`Germ.lean`); the step from a
  whole-chart map to a germ on a smaller germ is `IsScSmooth.isScSmoothGerm_of_subset`,
  `IsSc1.isSc1GermWith_of_subset`.
* **Composition with whole-chart maps.**  (a) *Outer whole-chart map*: `IsSc1With.comp_germ`
  (the chain rule `D(φ ∘ f)(x) = Dφ(f(x)) ∘ Df(x)` at every `x ∈ U₁`, for `φ` sc¹ on an sc-domain
  `V` and `f` an sc¹-germ on `G` with `f(G₀) ⊆ V`; the proof of `IsSc1GermWith.comp` with `V_m`
  in place of the outer germ, so that **no base-point condition** is needed), `IsSck.comp_germ`,
  `IsScSmooth.comp_germ`; the pairing `y ↦ (y, f(y))` is `IsSckGerm.pair_id`,
  `IsSc1GermWith.pair_id`.  (b) *Inner whole-chart map* `ψ` with `ψ(0) = 0`:
  `IsSckGerm.comp_preimage`, `IsScSmoothGerm.comp_preimage`, `IsSc1GermWith.comp_preimage`
  (derivative `Dg(ψ(x)) ∘ Dψ(x)`), on the germ `ofSet V ∩ ψ⁻¹(G)` (`ScNbhdGerm.preimage`).
* **The fill defect of a germ** (Definition 3.4 (3)): `fillDefect_isScSmoothGerm` (`[1 − ρ(r(·))]g`
  is an sc-smooth germ on `G` when `g` is and `G₀ ⊆ U`), `fillDefect_isSc1GermWith` with the
  explicit derivative family `fillDefectDeriv`, `fillDefectDeriv_zero` (its value at `0` when
  `g(0) = 0` and `0 ∈ O`), `fillDefect_deriv_zero_eq` (every derivative family of the sc¹-germ
  `[1 − ρ(r(·))]g` has this value at `0`).
* **Lemma 3.17 for germs**: `IsFillingGerm.add_section` (a filling germ `g` of `f̂` and a
  whole-chart sc-smooth section `ŝ` of `K → O` give the filling germ `g + ŝ ∘ r` of `f̂ + ŝ`),
  `IsFillingGerm.add_section_germ` (the same for `ŝ` an sc-smooth germ on a germ `G_s ⊆ U`, the
  filling living on `G ∩ r⁻¹(G_s)`).
* **The fibre part of a strong bundle map on a germ** (the push-forward `Ψ_*` of Definition
  3.11): `IsStrongBundleMap.fiber_comp_isScSmoothGerm` (`u ↦ (Ψ(u, k(u)))₂` is an sc-smooth germ
  on `G ⊆ U` when `k` is), `fiber_comp_isSc1GermWith` with the derivative family
  `fiberCompDeriv`, `fiberCompDeriv_zero`; the push-forward along a whole-chart `ψ'` with
  `ψ'(0) = 0` is then `IsStrongBundleMap.pushforward_isScSmoothGerm`,
  `pushforward_isSc1GermWith` (derivative `D[(Ψ(·, k(·)))₂](ψ'(x)) ∘ Dψ'(x)`) and
  `pushforwardDeriv_zero`.  The identification of the derivative at `0` with
  `Γ(0) ∘ Dk(0) ∘ Dψ'(0)` (through `IsStrongBundleMap.fiberCLM`) is in
  `Chapter3/GermCalculusParam.lean`, higher in the import chain.

## What the text leaves implicit, and the choices made

* **The outer chain rule without a base-point condition.**  The germ chain rule of `Germ.lean`
  composes two germs *at `0`*; the whole-chart maps `R`, `Ψ` are applied at `(r(y), g(y))`,
  `(u, k(u))`, which is not `0` unless `g(0) = 0` and `0 ∈ O`.  Rather than re-centring, the
  chain rule is re-proved with the outer map on a set `V` (its level sets `V_m`) and the inner
  map a germ; the proof is that of `IsSc1GermWith.hasFDerivWithinAt_comp` verbatim.
* **Which derivative family.**  Definition 3.2 does not say that `Df(x)` is unique; it is, on
  `U₁`, for a quadrant-like `C` (`IsSc1GermWith.eq_of_uniqueDiffWithinAt`).  The lemmas below
  give explicit families built from the given ones by the chain rule and the sum rule; any other
  family agrees with them on `U₁` (`IsSc1GermWith.congr_deriv` in the other direction).
* **The sc⁺-section in Lemma 3.17** is sc-smooth into `F¹`; only its sc-smoothness into `F` is
  used for the three filler conditions, as in `lemma_3_17`.  The germ version keeps the text's
  hypothesis that `ŝ` is a section of `K → O` (`(x, ŝ(x)) ∈ K` on `O`), on `O ∩ (G_s)₀` in the
  germ-section version.
-/

open Set Filter Topology Function Asymptotics

noncomputable section

namespace Polyfold

variable {E F G : ScBanach}

/-! ### Preliminaries -/

/-- Two bounded operators `E₀ → F₀` agreeing on the dense level `E₁` are equal (the pointwise
form of `ContinuousLinearMap.ext_of_comp_toBase_one` of `BasicGermLinearization.lean`, placed
here, lower in the import chain). -/
theorem ContinuousLinearMap.ext_of_toBase_one {F₀ : ScBanach} {A B : E 0 →L[ℝ] F₀ 0}
    (h : ∀ y : E 1, A (E.toBase 1 y) = B (E.toBase 1 y)) : A = B := by
  refine ContinuousLinearMap.ext fun y => congrFun ?_ y
  exact (E.denseRange_incl 0).equalizer A.continuous B.continuous (funext h)

section Prelim

variable {C : Set (E 0)} {G₁ : ScNbhdGerm E C} {f : E 0 → F 0}

/-- A relatively open subset of a partial quadrant lies in it. -/
lemma IsRelOpenInQuadrant.subset_quadrant {U : Set (E 0)} (hU : IsRelOpenInQuadrant E C U) :
    U ⊆ C := by
  obtain ⟨O, _, rfl⟩ := hU.relOpen
  exact inter_subset_right

/-- A derivative family may be replaced by one agreeing with it on `U₁`. -/
lemma IsSc1GermWith.congr_deriv {D D' : E 1 → E 0 →L[ℝ] F 0} (h : IsSc1GermWith G₁ f D)
    (hDD' : ∀ x ∈ G₁.U 1, D x = D' x) : IsSc1GermWith G₁ f D' where
  isSc0 := h.isSc0
  hasFDerivWithinAt x hx := hDD' x hx ▸ h.hasFDerivWithinAt x hx
  tangent_isSc0 := h.tangent_isSc0.congr fun p hp => by
    change (levelMap f 1 p.1, D p.1 p.2) = (levelMap f 1 p.1, D' p.1 p.2)
    rw [hDD' p.1 (G₁.mem_tangent_U.1 hp)]

/-- A germ with `G₀ ⊆ U` lies in the germ `ofSet U` level by level. -/
lemma ScNbhdGerm.U_subset_lvlSet {U : Set (E 0)} (hG : G₁.U 0 ⊆ U) (m : ℕ) :
    G₁.U m ⊆ E.lvlSet U m := fun _ hx => hG (G₁.toBase_mem hx)

/-- An sc-smooth map on a relatively open `U ∋ 0` is an sc-smooth germ on every germ `G` with
`G₀ ⊆ U`. -/
theorem IsScSmooth.isScSmoothGerm_of_subset {U : Set (E 0)} (hC : IsQuadrantLike E C)
    (hU : ∃ O : Set (E 0), IsOpen O ∧ U = O ∩ C) (h0 : (0 : E 0) ∈ U) (hf : IsScSmooth U f)
    (hG : G₁.U 0 ⊆ U) : IsScSmoothGerm G₁ f :=
  (hf.isScSmoothGerm hC hU h0).mono hC (G₁.U_subset_lvlSet hG)

/-- An sc¹ map on a relatively open `U ∋ 0` is an sc¹-germ on every germ `G` with `G₀ ⊆ U`, with
the derivative family `scDeriv U f`. -/
theorem IsSc1.isSc1GermWith_of_subset {U : Set (E 0)}
    (hU : ∃ O : Set (E 0), IsOpen O ∧ U = O ∩ C) (h0 : (0 : E 0) ∈ U) (hf : IsSc1 U f)
    (hG : G₁.U 0 ⊆ U) : IsSc1GermWith G₁ f (scDeriv U f) :=
  (hf.isSc1GermWith_ofSet hU h0).mono (G₁.U_subset_lvlSet hG)

/-- `f` maps the germ `G` into the set `V` level by level when `f(G₀) ⊆ V`. -/
lemma IsSc0Germ.levelMap_mapsTo {V : Set (F 0)} (hf : IsSc0Germ G₁ f) (hfV : MapsTo f (G₁.U 0) V)
    (m : ℕ) : MapsTo (levelMap f m) (G₁.U m) (F.lvlSet V m) := fun x hx => by
  rw [ScBanach.mem_lvlSet, hf.toBase_levelMap hx]
  exact hfV (G₁.toBase_mem hx)

lemma IsSc1GermWith.tangentMapWith_mapsTo_set {V : Set (F 0)} {D : E 1 → E 0 →L[ℝ] F 0}
    (h : IsSc1GermWith G₁ f D) (hfV : MapsTo f (G₁.U 0) V) :
    MapsTo (tangentMapWith f D) (G₁.tangent.U 0) (F.tangentSet V) := fun _ hp =>
  h.isSc0.levelMap_mapsTo hfV 1 (G₁.mem_tangent_U.1 hp)

lemma ScNbhdGerm.inter_subset_left (G₁ G₂ : ScNbhdGerm E C) (m : ℕ) :
    (G₁.inter G₂).U m ⊆ G₁.U m := fun _ hx => hx.1

lemma ScNbhdGerm.inter_subset_right (G₁ G₂ : ScNbhdGerm E C) (m : ℕ) :
    (G₁.inter G₂).U m ⊆ G₂.U m := fun _ hx => hx.2

lemma ScNbhdGerm.full_relOpenConvex (F : ScBanach) :
    ∃ O K : Set (F 1), IsOpen O ∧ Convex ℝ K ∧ (ScNbhdGerm.full F).U 1 = O ∩ K :=
  ⟨univ, univ, isOpen_univ, convex_univ, by simp⟩

end Prelim

/-! ### Germ arithmetic -/

/-- The negation `F → F` as an sc-operator. -/
def ScOperator.negOp (F : ScBanach) : ScOperator F F where
  lvl m := -ContinuousLinearMap.id ℝ (F m)
  incl_comm m x := by simp

/-- The scalar multiplication `c • · : F → F` as an sc-operator. -/
def ScOperator.smulOp (F : ScBanach) (c : ℝ) : ScOperator F F where
  lvl m := c • ContinuousLinearMap.id ℝ (F m)
  incl_comm m x := by simp

section Arithmetic

variable {C : Set (E 0)} {G₁ G₂ : ScNbhdGerm E C} {f g : E 0 → F 0}
  {Df Dg : E 1 → E 0 →L[ℝ] F 0}

namespace IsSc1GermWith

/-- Post-composition with an sc-operator `T`: the derivative family is `T ∘ Df`. -/
theorem operator_comp (T : ScOperator F G) (hf : IsSc1GermWith G₁ f Df) :
    IsSc1GermWith G₁ (T 0 ∘ f) fun x => (T 0).comp (Df x) :=
  (T.isSc1GermWith (ScNbhdGerm.full F)).comp (ScNbhdGerm.full_relOpenConvex F) hf
    (G₁.mapsToGerm_full f)

/-- **The sum rule for sc¹-germs**: `Df + Dg` is a derivative family of `f + g`. -/
theorem add (hf : IsSc1GermWith G₁ f Df) (hg : IsSc1GermWith G₁ g Dg) :
    IsSc1GermWith G₁ (fun x => f x + g x) fun x => Df x + Dg x := by
  have := (hf.pair hg).operator_comp (ScOperator.addOp F)
  refine (this.congr fun x _ => rfl).congr_deriv fun x _ => ?_
  ext v
  rfl

theorem neg (hf : IsSc1GermWith G₁ f Df) :
    IsSc1GermWith G₁ (fun x => -f x) fun x => -Df x := by
  have := hf.operator_comp (ScOperator.negOp F)
  refine (this.congr fun x _ => ?_).congr_deriv fun x _ => ?_
  · simp [ScOperator.negOp]
  · ext v; simp [ScOperator.negOp]

theorem sub (hf : IsSc1GermWith G₁ f Df) (hg : IsSc1GermWith G₁ g Dg) :
    IsSc1GermWith G₁ (fun x => f x - g x) fun x => Df x - Dg x := by
  refine ((hf.add hg.neg).congr fun x _ => ?_).congr_deriv fun x _ => ?_
  · simp [sub_eq_add_neg]
  · ext v; simp [sub_eq_add_neg]

theorem smul (c : ℝ) (hf : IsSc1GermWith G₁ f Df) :
    IsSc1GermWith G₁ (fun x => c • f x) fun x => c • Df x := by
  have := hf.operator_comp (ScOperator.smulOp F c)
  refine (this.congr fun x _ => ?_).congr_deriv fun x _ => ?_
  · simp [ScOperator.smulOp]
  · ext v; simp [ScOperator.smulOp]

/-- The sum of sc¹-germs on `G₁`, `G₂` is an sc¹-germ on `G₁ ∩ G₂`. -/
theorem add_inter (hf : IsSc1GermWith G₁ f Df) (hg : IsSc1GermWith G₂ g Dg) :
    IsSc1GermWith (G₁.inter G₂) (fun x => f x + g x) fun x => Df x + Dg x :=
  (hf.mono (G₁.inter_subset_left G₂)).add (hg.mono (G₁.inter_subset_right G₂))

theorem sub_inter (hf : IsSc1GermWith G₁ f Df) (hg : IsSc1GermWith G₂ g Dg) :
    IsSc1GermWith (G₁.inter G₂) (fun x => f x - g x) fun x => Df x - Dg x :=
  (hf.mono (G₁.inter_subset_left G₂)).sub (hg.mono (G₁.inter_subset_right G₂))

end IsSc1GermWith

namespace IsSckGerm

variable {k : ℕ}

/-- **The sum rule for sc^k-germs.** -/
theorem add (hC : IsQuadrantLike E C) (hf : IsSckGerm k G₁ f) (hg : IsSckGerm k G₁ g) :
    IsSckGerm k G₁ fun x => f x + g x :=
  ((hf.pair hC hg).operator_comp hC (ScOperator.addOp F)).congr hC fun _ _ => rfl

theorem neg (hC : IsQuadrantLike E C) (hf : IsSckGerm k G₁ f) : IsSckGerm k G₁ fun x => -f x :=
  (hf.operator_comp hC (ScOperator.negOp F)).congr hC fun x _ => by simp [ScOperator.negOp]

theorem sub (hC : IsQuadrantLike E C) (hf : IsSckGerm k G₁ f) (hg : IsSckGerm k G₁ g) :
    IsSckGerm k G₁ fun x => f x - g x :=
  (hf.add hC (hg.neg hC)).congr hC fun x _ => by simp [sub_eq_add_neg]

theorem smul (hC : IsQuadrantLike E C) (c : ℝ) (hf : IsSckGerm k G₁ f) :
    IsSckGerm k G₁ fun x => c • f x :=
  (hf.operator_comp hC (ScOperator.smulOp F c)).congr hC fun x _ => by simp [ScOperator.smulOp]

/-- The sum of sc^k-germs on `G₁`, `G₂` is an sc^k-germ on `G₁ ∩ G₂`. -/
theorem add_inter (hC : IsQuadrantLike E C) (hf : IsSckGerm k G₁ f) (hg : IsSckGerm k G₂ g) :
    IsSckGerm k (G₁.inter G₂) fun x => f x + g x :=
  (hf.mono hC (G₁.inter_subset_left G₂)).add hC (hg.mono hC (G₁.inter_subset_right G₂))

theorem sub_inter (hC : IsQuadrantLike E C) (hf : IsSckGerm k G₁ f) (hg : IsSckGerm k G₂ g) :
    IsSckGerm k (G₁.inter G₂) fun x => f x - g x :=
  (hf.mono hC (G₁.inter_subset_left G₂)).sub hC (hg.mono hC (G₁.inter_subset_right G₂))

end IsSckGerm

namespace IsScSmoothGerm

theorem operator_comp (hC : IsQuadrantLike E C) (T : ScOperator F G) (hf : IsScSmoothGerm G₁ f) :
    IsScSmoothGerm G₁ (T 0 ∘ f) := fun k => (hf k).operator_comp hC T

/-- **The sum rule for sc-smooth germs.** -/
theorem add (hC : IsQuadrantLike E C) (hf : IsScSmoothGerm G₁ f) (hg : IsScSmoothGerm G₁ g) :
    IsScSmoothGerm G₁ fun x => f x + g x := fun k => (hf k).add hC (hg k)

theorem neg (hC : IsQuadrantLike E C) (hf : IsScSmoothGerm G₁ f) :
    IsScSmoothGerm G₁ fun x => -f x := fun k => (hf k).neg hC

theorem sub (hC : IsQuadrantLike E C) (hf : IsScSmoothGerm G₁ f) (hg : IsScSmoothGerm G₁ g) :
    IsScSmoothGerm G₁ fun x => f x - g x := fun k => (hf k).sub hC (hg k)

theorem smul (hC : IsQuadrantLike E C) (c : ℝ) (hf : IsScSmoothGerm G₁ f) :
    IsScSmoothGerm G₁ fun x => c • f x := fun k => (hf k).smul hC c

theorem add_inter (hC : IsQuadrantLike E C) (hf : IsScSmoothGerm G₁ f)
    (hg : IsScSmoothGerm G₂ g) : IsScSmoothGerm (G₁.inter G₂) fun x => f x + g x :=
  fun k => (hf k).add_inter hC (hg k)

theorem sub_inter (hC : IsQuadrantLike E C) (hf : IsScSmoothGerm G₁ f)
    (hg : IsScSmoothGerm G₂ g) : IsScSmoothGerm (G₁.inter G₂) fun x => f x - g x :=
  fun k => (hf k).sub_inter hC (hg k)

end IsScSmoothGerm

end Arithmetic

/-! ### Composition with a whole-chart map on the outside (the chain rule, re-proved) -/

section CompOuter

variable {C : Set (E 0)} {G₁ : ScNbhdGerm E C} {V : Set (F 0)} {f : E 0 → F 0} {g : F 0 → G 0}
  {Df : E 1 → E 0 →L[ℝ] F 0} {Dg : F 1 → F 0 →L[ℝ] G 0}

lemma IsSc0.levelMap_comp_germ (hg : IsSc0 F G V g) (hf : IsSc0Germ G₁ f)
    (hfV : MapsTo f (G₁.U 0) V) {m : ℕ} {x : E m} (hx : x ∈ G₁.U m) :
    levelMap (g ∘ f) m x = levelMap g m (levelMap f m x) := by
  apply levelMap_eq_of_toBase_eq
  rw [hg.toBase_levelMap (hf.levelMap_mapsTo hfV m hx), hf.toBase_levelMap hx]
  rfl

/-- An sc⁰ map on `V` composed with an sc⁰-germ into `V` is an sc⁰-germ. -/
lemma IsSc0.comp_germ (hg : IsSc0 F G V g) (hf : IsSc0Germ G₁ f) (hfV : MapsTo f (G₁.U 0) V) :
    IsSc0Germ G₁ (g ∘ f) where
  mem_range m x hx := by
    change g (f (E.toBase m x)) ∈ _
    rw [← hf.toBase_levelMap hx]
    exact hg.mem_range m _ (hf.levelMap_mapsTo hfV m hx)
  continuousOn m :=
    ((hg.continuousOn m).comp (hf.continuousOn m) (hf.levelMap_mapsTo hfV m)).congr
      fun x hx => hg.levelMap_comp_germ hf hfV hx

/-- The mean value inequality along a segment in `V₁`. -/
private lemma norm_sub_le_of_segment_set (hg : IsSc1With V g Dg) {y₀ k : F 1}
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, y₀ + t • k ∈ F.lvlSet V 1) {K : ℝ}
    (hK : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Dg (y₀ + t • k) (F.toBase 1 k) - Dg y₀ (F.toBase 1 k)‖ ≤ K) :
    ‖g (F.toBase 1 (y₀ + k)) - g (F.toBase 1 y₀) - Dg y₀ (F.toBase 1 k)‖ ≤ K := by
  set φ : ℝ → G 0 := fun t => g (F.toBase 1 (y₀ + t • k)) - t • Dg y₀ (F.toBase 1 k) with hφ
  have hγ : ∀ t : ℝ, HasDerivAt (fun t : ℝ => y₀ + t • k) k t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const k).const_add y₀
  have hder : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt φ
      (Dg (y₀ + t • k) (F.toBase 1 k) - Dg y₀ (F.toBase 1 k)) (Icc 0 1) t := by
    intro t ht
    have h1 : HasDerivWithinAt (fun t : ℝ => g (F.toBase 1 (y₀ + t • k)))
        (((Dg (y₀ + t • k)).comp (F.toBase 1)) k) (Icc 0 1) t :=
      HasFDerivWithinAt.comp_hasDerivWithinAt (l := g ∘ F.toBase 1) (f := fun t : ℝ => y₀ + t • k)
        t (hg.hasFDerivWithinAt _ (hseg t ht)) (hγ t).hasDerivWithinAt hseg
    have h2 : HasDerivWithinAt (fun t : ℝ => t • Dg y₀ (F.toBase 1 k)) (Dg y₀ (F.toBase 1 k))
        (Icc 0 1) t := by
      simpa using ((hasDerivAt_id t).smul_const (Dg y₀ (F.toBase 1 k))).hasDerivWithinAt
    exact h1.sub h2
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hK (convex_Icc 0 1)
    (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
  have h01 : φ 1 - φ 0 = g (F.toBase 1 (y₀ + k)) - g (F.toBase 1 y₀) - Dg y₀ (F.toBase 1 k) := by
    simp only [hφ, one_smul, zero_smul, add_zero, sub_zero]; abel
  rwa [h01, sub_zero, norm_one, mul_one] at this

/-- Uniform smallness of `[Dg(y) − Dg(y₀)](w + b)` for `y` near `y₀` in `V₁`, `w` in a compact set
and `b` small. -/
private lemma exists_delta_set (hg : IsSc1With V g Dg) {y₀ : F 1} (hy₀ : y₀ ∈ F.lvlSet V 1)
    {K : Set (F 0)} (hK : IsCompact K) {c : ℝ} (hc : 0 < c) :
    ∃ δ > 0, ∀ y ∈ F.lvlSet V 1, ‖y - y₀‖ < δ → ∀ w ∈ K, ∀ b : F 0, ‖b‖ < δ →
      ‖Dg y (w + b) - Dg y₀ (w + b)‖ ≤ c := by
  let Θ : (F.lvlSet V 1 × F 0) × F 0 → G 0 :=
    fun q => Dg q.1.1.1 (q.2 + q.1.2) - Dg y₀ (q.2 + q.1.2)
  have hΘ : Continuous Θ := by
    have h1 : Continuous fun q : (F.lvlSet V 1 × F 0) × F 0 => Dg q.1.1.1 (q.2 + q.1.2) := by
      refine hg.continuousOn_deriv.comp_continuous
        (f := fun q : (F.lvlSet V 1 × F 0) × F 0 => ((q.1.1.1 : F 1), q.2 + q.1.2)) ?_ ?_
      · fun_prop
      · intro q; exact q.1.1.2
    exact h1.sub ((Dg y₀).continuous.comp (by fun_prop))
  have key : ∀ᶠ q in 𝓝 ((⟨y₀, hy₀⟩, (0 : F 0)) : F.lvlSet V 1 × F 0), ∀ w ∈ K,
      ‖Θ (q, w)‖ ≤ c := by
    refine hK.eventually_forall_of_forall_eventually (P := fun q w => ‖Θ (q, w)‖ ≤ c) fun w _ => ?_
    have h0 : Θ ((⟨y₀, hy₀⟩, 0), w) = 0 := by simp [Θ]
    have := hΘ.continuousAt.eventually_mem (x := ((⟨y₀, hy₀⟩, 0), w))
      (s := Metric.closedBall 0 c) (by rw [h0]; exact Metric.closedBall_mem_nhds 0 hc)
    exact this.mono fun q hq => by simpa using hq
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 key
  refine ⟨δ, hδ, fun y hy hyδ w hw b hb => ?_⟩
  have := hδ' (y := (⟨y, hy⟩, b)) ?_ w hw
  · simpa [Θ] using this
  · rw [Prod.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_zero_right]
    exact max_lt hyδ hb

/-- **The derivative part of the chain rule, outer map on a set**: for `g` sc¹ on the sc-domain
`V` and `f` an sc¹-germ on `G` with `f(G₀) ⊆ V`, `g ∘ f : U₁ → G₀` is differentiable at `x ∈ U₁`
within `U₁` with derivative `Dg(f(x)) ∘ Df(x)`.  The proof of
`IsSc1GermWith.hasFDerivWithinAt_comp` with `V_m` in place of the outer germ. -/
theorem IsSc1With.hasFDerivWithinAt_comp_germ (hV : IsScDomain F V) (hg : IsSc1With V g Dg)
    (hf : IsSc1GermWith G₁ f Df) (hfV : MapsTo f (G₁.U 0) V) {x : E 1} (hx : x ∈ G₁.U 1) :
    HasFDerivWithinAt (g ∘ f ∘ E.toBase 1)
      (((Dg (levelMap f 1 x)).comp (Df x)).comp (E.toBase 1)) (G₁.U 1) x := by
  obtain ⟨O, K', hO, hK', hVOC⟩ := hV.relOpenConvex 1
  set ι := E.toBase 1 with hι
  set ιF := F.toBase 1 with hιF
  set f₁ := levelMap f 1 with hf₁
  set y₀ := f₁ x with hy₀
  have hmaps := hf.isSc0.levelMap_mapsTo hfV 1
  have hy₀V : y₀ ∈ F.lvlSet V 1 := hmaps hx
  have hιF_f₁ : ∀ z ∈ G₁.U 1, ιF (f₁ z) = f (ι z) := fun z hz => hf.isSc0.toBase_levelMap hz
  obtain ⟨K₀, hK₀, hK₀sub⟩ :=
    (E.incl_isCompactOperator 0).image_closedBall_subset_compact (f := (E.incl 0 : E 1 →ₗ[ℝ] E 0)) 1
  set K := Df x '' K₀ with hK
  have hKc : IsCompact K := hK₀.image (Df x).continuous
  have hy₀O : y₀ ∈ O := (hVOC ▸ hy₀V).1
  obtain ⟨ρ, hρ, hρO⟩ := Metric.isOpen_iff.1 hO y₀ hy₀O
  rw [hasFDerivWithinAt_iff_isLittleO, isLittleO_iff]
  intro c hc
  have hc2 : 0 < c / 2 := by positivity
  obtain ⟨δ, hδ, hδ'⟩ := exists_delta_set hg hy₀V hKc hc2
  set ε := min (δ / 2) (c / 2 / (‖Dg y₀‖ + 1)) with hε
  have hε0 : 0 < ε := lt_min (by positivity) (by positivity)
  have hεδ : ε ≤ δ / 2 := min_le_left _ _
  have hεc : ‖Dg y₀‖ * ε ≤ c / 2 := by
    calc ‖Dg y₀‖ * ε ≤ (‖Dg y₀‖ + 1) * (c / 2 / (‖Dg y₀‖ + 1)) :=
          mul_le_mul (by linarith) (min_le_right _ _) hε0.le (by positivity)
      _ = c / 2 := by field_simp
  have ev1 : ∀ᶠ z in 𝓝[G₁.U 1] x, z ∈ G₁.U 1 := self_mem_nhdsWithin
  have ev2 : ∀ᶠ z in 𝓝[G₁.U 1] x, dist (f₁ z) (f₁ x) < min ρ δ :=
    Metric.tendsto_nhds.1 (hf.isSc0.continuousOn 1 x hx) _ (lt_min hρ hδ)
  have ev3 : ∀ᶠ z in 𝓝[G₁.U 1] x,
      ‖(f ∘ ι) z - (f ∘ ι) x - ((Df x).comp ι) (z - x)‖ ≤ ε * ‖z - x‖ :=
    isLittleO_iff.1 (hasFDerivWithinAt_iff_isLittleO.1 (hf.hasFDerivWithinAt x hx)) hε0
  filter_upwards [ev1, ev2, ev3] with z hz hz2 hz3
  set r := f (ι z) - f (ι x) - Df x (ι (z - x)) with hr
  have hr' : ‖r‖ ≤ ε * ‖z - x‖ := hz3
  have hsplit : f (ι z) - f (ι x) = Df x (ι (z - x)) + r := by rw [hr]; abel
  set k := f₁ z - y₀ with hk
  have hιk : ιF k = f (ι z) - f (ι x) := by
    rw [hk, map_sub, hιF_f₁ z hz, hy₀, hιF_f₁ x hx]
  have hknorm : ‖k‖ < min ρ δ := by rwa [hk, ← dist_eq_norm]
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, y₀ + t • k ∈ F.lvlSet V 1 := by
    intro t ht
    rw [hVOC]
    refine ⟨hρO ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg ht.1]
      calc t * ‖k‖ ≤ 1 * ‖k‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
        _ < ρ := by rw [one_mul]; exact lt_of_lt_of_le hknorm (min_le_left _ _)
    · have h1 : y₀ ∈ K' := (hVOC ▸ hy₀V).2
      have h2 : f₁ z ∈ K' := (hVOC ▸ hmaps hz).2
      have := hK'.add_smul_sub_mem h1 h2 ht
      rwa [hk]
  have hmain : ‖g (f (ι z)) - g (f (ι x)) - Dg y₀ (ιF k)‖ ≤ c / 2 * ‖z - x‖ := by
    by_cases hzx : z = x
    · subst hzx
      simp [hk, hy₀]
    have hs : 0 < ‖z - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hzx)
    set s := ‖z - x‖ with hs_def
    set u : E 1 := s⁻¹ • (z - x) with hu
    have hu1 : u ∈ Metric.closedBall (0 : E 1) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right, hu, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ hs.ne']
    set w₁ := Df x (ι u) with hw₁
    have hw₁K : w₁ ∈ K := ⟨ι u, hK₀sub ⟨u, hu1, rfl⟩, rfl⟩
    set b := s⁻¹ • r with hb
    have hbδ : ‖b‖ < δ := by
      rw [hb, norm_smul, norm_inv, norm_norm]
      calc s⁻¹ * ‖r‖ ≤ s⁻¹ * (ε * s) := by gcongr
        _ = ε := by field_simp
        _ ≤ δ / 2 := hεδ
        _ < δ := by linarith
    have hιk' : ιF k = s • (w₁ + b) := by
      rw [hιk, hsplit, hw₁, hb, smul_add, ← map_smul, ← map_smul, hu, smul_inv_smul₀ hs.ne',
        smul_inv_smul₀ hs.ne']
    have hbound : ∀ t ∈ Icc (0 : ℝ) 1,
        ‖Dg (y₀ + t • k) (ιF k) - Dg y₀ (ιF k)‖ ≤ c / 2 * s := by
      intro t ht
      have hyδ : ‖y₀ + t • k - y₀‖ < δ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        calc t * ‖k‖ ≤ 1 * ‖k‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
          _ < δ := by rw [one_mul]; exact lt_of_lt_of_le hknorm (min_le_right _ _)
      have := hδ' _ (hseg t ht) hyδ w₁ hw₁K b hbδ
      rw [hιk', map_smul, map_smul, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hs,
        mul_comm]
      exact mul_le_mul_of_nonneg_right this hs.le
    have := norm_sub_le_of_segment_set hg hseg hbound
    rwa [hk, add_sub_cancel, hιF_f₁ z hz, hy₀, hιF_f₁ x hx] at this
  have hsecond : ‖Dg y₀ r‖ ≤ c / 2 * ‖z - x‖ :=
    calc ‖Dg y₀ r‖ ≤ ‖Dg y₀‖ * ‖r‖ := (Dg y₀).le_opNorm r
      _ ≤ ‖Dg y₀‖ * (ε * ‖z - x‖) := by gcongr
      _ = ‖Dg y₀‖ * ε * ‖z - x‖ := by ring
      _ ≤ c / 2 * ‖z - x‖ := by gcongr
  have hid : (g ∘ f ∘ ι) z - (g ∘ f ∘ ι) x - (((Dg y₀).comp (Df x)).comp ι) (z - x)
      = (g (f (ι z)) - g (f (ι x)) - Dg y₀ (ιF k)) + Dg y₀ r := by
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply]
    rw [hιk, hsplit, map_add]
    abel
  rw [hid]
  calc ‖(g (f (ι z)) - g (f (ι x)) - Dg y₀ (ιF k)) + Dg y₀ r‖
      ≤ ‖g (f (ι z)) - g (f (ι x)) - Dg y₀ (ιF k)‖ + ‖Dg y₀ r‖ := norm_add_le _ _
    _ ≤ c / 2 * ‖z - x‖ + c / 2 * ‖z - x‖ := add_le_add hmain hsecond
    _ = c * ‖z - x‖ := by ring

lemma tangentMapWith_comp_germ (hg : IsSc0 F G V g) (hf : IsSc0Germ G₁ f)
    (hfV : MapsTo f (G₁.U 0) V) :
    EqOn (tangentMapWith (g ∘ f) fun x => (Dg (levelMap f 1 x)).comp (Df x))
      (tangentMapWith g Dg ∘ tangentMapWith f Df) (G₁.tangent.U 0) := by
  intro p hp
  change (levelMap (g ∘ f) 1 p.1, Dg (levelMap f 1 p.1) (Df p.1 p.2)) =
    (levelMap g 1 (levelMap f 1 p.1), Dg (levelMap f 1 p.1) (Df p.1 p.2))
  rw [hg.levelMap_comp_germ hf hfV (G₁.mem_tangent_U.1 hp)]

/-- **The chain rule, outer map on a set, with derivative families**: `g` sc¹ on the sc-domain
`V` with derivatives `Dg`, `f` an sc¹-germ on `G` with derivatives `Df` and `f(G₀) ⊆ V`; then
`g ∘ f` is an sc¹-germ on `G` with derivatives `Dg(f(x)) ∘ Df(x)`, `x ∈ U₁`. -/
theorem IsSc1With.comp_germ (hV : IsScDomain F V) (hg : IsSc1With V g Dg)
    (hf : IsSc1GermWith G₁ f Df) (hfV : MapsTo f (G₁.U 0) V) :
    IsSc1GermWith G₁ (g ∘ f) fun x => (Dg (levelMap f 1 x)).comp (Df x) where
  isSc0 := hg.isSc0.comp_germ hf.isSc0 hfV
  hasFDerivWithinAt _ hx := hg.hasFDerivWithinAt_comp_germ hV hf hfV hx
  tangent_isSc0 :=
    (hg.tangent_isSc0.comp_germ hf.tangent_isSc0 (hf.tangentMapWith_mapsTo_set hfV)).congr
      (tangentMapWith_comp_germ hg.isSc0 hf.isSc0 hfV).symm

/-- **The chain rule for sc^k, outer map on a set**: `g` sc^k on the sc-domain `V`, `f` an
sc^k-germ on `G` with `f(G₀) ⊆ V`; then `g ∘ f` is an sc^k-germ on `G`. -/
theorem IsSck.comp_germ : ∀ {k : ℕ} {E F G : ScBanach} {C : Set (E 0)} {G₁ : ScNbhdGerm E C}
    {V : Set (F 0)} {f : E 0 → F 0} {g : F 0 → G 0},
    IsQuadrantLike E C → IsScDomain F V → IsSck k F G V g → IsSckGerm k G₁ f →
    MapsTo f (G₁.U 0) V → IsSckGerm k G₁ (g ∘ f)
  | 0, _, _, _, _, _, _, _, _, _, _, hg, hf, hfV => IsSc0.comp_germ hg hf hfV
  | k + 1, _, _, _, _, G₁, V, f, g, hC, hV, hg, hf, hfV => by
    have hcomp := hg.1.isSc1With_scDeriv.comp_germ hV hf.1.isSc1GermWith_scDerivGerm hfV
    refine ⟨hcomp.isSc1Germ, ?_⟩
    have h2 : EqOn (tangentMapGerm G₁ (g ∘ f)) (tangentMap V g ∘ tangentMapGerm G₁ f)
        (G₁.tangent.U 0) :=
      (IsSc1Germ.tangentMapGerm_eqOn hC hcomp).trans
        (tangentMapWith_comp_germ hg.1.isSc0 hf.1.isSc0 hfV)
    have := IsSck.comp_germ (k := k) hC.tangentSet hV.tangentSet hg.2 hf.2
      (hf.1.isSc1GermWith_scDerivGerm.tangentMapWith_mapsTo_set hfV)
    exact IsSckGerm.congr hC.tangentSet h2.symm this

/-- **The chain rule for sc-smooth maps, outer map on a set.** -/
theorem IsScSmooth.comp_germ (hC : IsQuadrantLike E C) (hV : IsScDomain F V)
    (hg : IsScSmooth V g) (hf : IsScSmoothGerm G₁ f) (hfV : MapsTo f (G₁.U 0) V) :
    IsScSmoothGerm G₁ (g ∘ f) := fun k => IsSck.comp_germ hC hV (hg k) (hf k) hfV

/-- The pairing `y ↦ (y, f(y))` of an sc¹-germ with the identity. -/
theorem IsSc1GermWith.pair_id (hf : IsSc1GermWith G₁ f Df) :
    IsSc1GermWith G₁ (pairMap id f) fun x => (ContinuousLinearMap.id ℝ (E 0)).prod (Df x) :=
  ((ScOperator.id E).isSc1GermWith G₁).pair hf

/-- The pairing `y ↦ (y, f(y))` of an sc^k-germ with the identity. -/
theorem IsSckGerm.pair_id {k : ℕ} (hC : IsQuadrantLike E C) (hf : IsSckGerm k G₁ f) :
    IsSckGerm k G₁ (pairMap id f) :=
  ((ScOperator.id E).isSckGerm k G₁ hC).pair hC hf

theorem IsScSmoothGerm.pair_id (hC : IsQuadrantLike E C) (hf : IsScSmoothGerm G₁ f) :
    IsScSmoothGerm G₁ (pairMap id f) := fun k => (hf k).pair_id hC

end CompOuter

/-! ### Composition with a whole-chart map on the inside -/

section CompInner

variable {E' : ScBanach} {C : Set (E 0)} {C' : Set (E' 0)} {G₁ : ScNbhdGerm E C} {V : Set (E' 0)}
  {ψ : E' 0 → E 0} {g : E 0 → F 0}

/-- **Composition with a whole-chart sc^k map on the inside**: for `ψ : V → C` sc^k on a
relatively open `V ∋ 0` with `ψ(0) = 0` and `g` an sc^k-germ on `G`, `g ∘ ψ` is an sc^k-germ on
the germ `ofSet V ∩ ψ⁻¹(G)`. -/
theorem IsSckGerm.comp_preimage {k : ℕ} (hC : IsQuadrantLike E C) (hC' : IsQuadrantLike E' C')
    (hV : ∃ O : Set (E' 0), IsOpen O ∧ V = O ∩ C') (h0V : (0 : E' 0) ∈ V)
    (hψ : IsSck k E' E V ψ) (hψ0 : ψ 0 = 0) (hψC : MapsTo ψ V C) (hg : IsSckGerm k G₁ g) :
    IsSckGerm k ((ScNbhdGerm.ofSet hV h0V).preimage G₁ (hψ.isSc0.isSc0Germ hV h0V) hψ0 hψC)
      (g ∘ ψ) :=
  IsSckGerm.comp hC' hC hg
    ((hψ.isSckGerm hC' hV h0V).mono hC' (ScNbhdGerm.preimage_subset _ _ _ _ _))
    (ScNbhdGerm.preimage_mapsToGerm _ _ _ _ _)

theorem IsScSmoothGerm.comp_preimage (hC : IsQuadrantLike E C) (hC' : IsQuadrantLike E' C')
    (hV : ∃ O : Set (E' 0), IsOpen O ∧ V = O ∩ C') (h0V : (0 : E' 0) ∈ V)
    (hψ : IsScSmooth V ψ) (hψ0 : ψ 0 = 0) (hψC : MapsTo ψ V C) (hg : IsScSmoothGerm G₁ g) :
    IsScSmoothGerm
      ((ScNbhdGerm.ofSet hV h0V).preimage G₁ (hψ.isSc1.isSc0.isSc0Germ hV h0V) hψ0 hψC)
      (g ∘ ψ) :=
  fun k => (hg k).comp_preimage hC hC' hV h0V (hψ k) hψ0 hψC

/-- **The chain rule with a whole-chart inner map**: `D(g ∘ ψ)(x) = Dg(ψ(x)) ∘ Dψ(x)` on the
level `1` of the germ `ofSet V ∩ ψ⁻¹(G)`. -/
theorem IsSc1GermWith.comp_preimage {Dg : E 1 → E 0 →L[ℝ] F 0} (hC : IsQuadrantLike E C)
    (hV : ∃ O : Set (E' 0), IsOpen O ∧ V = O ∩ C') (h0V : (0 : E' 0) ∈ V)
    (hψ : IsSc1 V ψ) (hψ0 : ψ 0 = 0) (hψC : MapsTo ψ V C) (hg : IsSc1GermWith G₁ g Dg) :
    IsSc1GermWith ((ScNbhdGerm.ofSet hV h0V).preimage G₁ (hψ.isSc0.isSc0Germ hV h0V) hψ0 hψC)
      (g ∘ ψ) fun x => (Dg (levelMap ψ 1 x)).comp (scDeriv V ψ x) :=
  hg.comp (G₁.relOpenConvex hC 1)
    ((hψ.isSc1GermWith_ofSet hV h0V).mono (ScNbhdGerm.preimage_subset _ _ _ _ _))
    (ScNbhdGerm.preimage_mapsToGerm _ _ _ _ _)

end CompInner

/-! ### The fill defect of a germ (Definition 3.4 (3)) -/

section FillDefect

open StrongRetr

variable {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0} {G₁ : ScNbhdGerm E C}

/-- The fibre part `(u, h) ↦ (R(u, h))₂ = ρ(u)h` of a strong bundle retraction is sc-smooth on
`U ⊕ F`. -/
lemma StrongRetr.fiber_isScSmooth (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) :
    IsScSmooth (U ×ˢ univ) fun p : (E.prod F) 0 => (R p).2 :=
  (IsScSmooth.comp (hU.prod_univ F).isScDomain (isScDomain_univ _)
    ((E.prodSndOp F).isScSmooth (isScDomain_univ _)) hR.isScSmooth_zero (mapsTo_univ _ _)).congr
    (hU.prod_univ F).isScDomain fun _ _ => rfl

/-- `r` is an sc-smooth germ on every germ `G` with `G₀ ⊆ U`. -/
lemma StrongRetr.r_isScSmoothGerm (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U) (hG : G₁.U 0 ⊆ U) :
    IsScSmoothGerm G₁ (r R) :=
  (hR.baseRetraction hU).isScSmooth.isScSmoothGerm_of_subset hU.isPartialQuadrant.isQuadrantLike
    hU.relOpen h0 hG

/-- `r` is an sc¹-germ on every germ `G` with `G₀ ⊆ U`, with derivatives `scDeriv U r`. -/
lemma StrongRetr.r_isSc1GermWith (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U) (hG : G₁.U 0 ⊆ U) :
    IsSc1GermWith G₁ (r R) (scDeriv U (r R)) :=
  (hR.baseRetraction hU).isScSmooth.isSc1.isSc1GermWith_of_subset hU.relOpen h0 hG

lemma StrongRetr.pairMap_mapsTo (hR : IsStrongBundleRetraction U R) (hG : G₁.U 0 ⊆ U)
    (g : E 0 → F 0) : MapsTo (pairMap (r R) g) (G₁.U 0) (U ×ˢ univ) :=
  fun _ hy => ⟨r_mem hR (hG hy), mem_univ _⟩

/-- **The fill defect of a germ is a germ**: `[1 − ρ(r(·))]g` is an sc-smooth germ on `G` when
`g` is and `G₀ ⊆ U` (the germ analogue of `fillDefect_isScSmooth`; it is `g − (R(·))₂ ∘ (r, g)`,
by the sum rule and the outer chain rule). -/
theorem fillDefect_isScSmoothGerm (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U) (hG : G₁.U 0 ⊆ U) {g : E 0 → F 0}
    (hg : IsScSmoothGerm G₁ g) : IsScSmoothGerm G₁ (fillDefect R g) := by
  have hQ := hU.isPartialQuadrant.isQuadrantLike
  have hpair : IsScSmoothGerm G₁ (pairMap (r R) g) := (r_isScSmoothGerm hU hR h0 hG).pair hQ hg
  have hcomp := (fiber_isScSmooth hU hR).comp_germ hQ (hU.prod_univ F).isScDomain hpair
    (pairMap_mapsTo hR hG g)
  exact hg.sub hQ hcomp

/-- The derivative family of the fill defect `[1 − ρ(r(·))]g` of a germ `g` with derivative
family `Dg`: `Dg(x) − D(R₂)(r(x), g(x)) ∘ (Dr(x), Dg(x))`, `x ∈ U₁`. -/
def fillDefectDeriv (U : Set (E 0)) (R : E 0 × F 0 → E 0 × F 0) (g : E 0 → F 0)
    (Dg : E 1 → E 0 →L[ℝ] F 0) : E 1 → E 0 →L[ℝ] F 0 := fun x =>
  Dg x - (scDeriv (U ×ˢ univ) (fun p : (E.prod F) 0 => (R p).2)
    (levelMap (pairMap (r R) g) 1 x)).comp ((scDeriv U (r R) x).prod (Dg x))

/-- **The fill defect of an sc¹-germ is an sc¹-germ**, with the derivative family
`fillDefectDeriv` (the chain rule and the sum rule). -/
theorem fillDefect_isSc1GermWith (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U) (hG : G₁.U 0 ⊆ U) {g : E 0 → F 0}
    {Dg : E 1 → E 0 →L[ℝ] F 0} (hg : IsSc1GermWith G₁ g Dg) :
    IsSc1GermWith G₁ (fillDefect R g) (fillDefectDeriv U R g Dg) := by
  have hpair := (r_isSc1GermWith hU hR h0 hG).pair hg
  have hcomp := (fiber_isScSmooth hU hR).isSc1.isSc1With_scDeriv.comp_germ
    (hU.prod_univ F).isScDomain hpair (pairMap_mapsTo hR hG g)
  exact hg.sub hcomp

/-- The level-`1` map of `(r, g)` sends `0` to `0` when `r(0) = 0` and `g(0) = 0`. -/
lemma levelMap_pairMap_r_zero (hR : IsStrongBundleRetraction U R) (h0O : (0 : E 0) ∈ r R '' U)
    {g : E 0 → F 0} (hg0 : g 0 = 0) : levelMap (pairMap (r R) g) 1 (0 : E 1) = 0 := by
  apply levelMap_eq_of_toBase_eq
  rw [map_zero, map_zero]
  change (0 : (E.prod F) 0) = (r R 0, g 0)
  rw [r_eq_self hR h0O, hg0]; rfl

/-- **The derivative of the fill defect at `0`**, for `g(0) = 0` and `0 ∈ O`:
`Dk(0) = Dg(0) − D(R₂)(0, 0) ∘ (Dr(0), Dg(0))`.  With `StrongRetr.scDeriv_fiber_zero`
(`FillerLinearization.lean`), `D(R₂)(0, 0)(h, k) = ρ(0)k`, this is `(1 − ρ(0))Dg(0)`
(`fillDefectDeriv_zero_eq` in `GermCalculusParam.lean`). -/
theorem fillDefectDeriv_zero (hR : IsStrongBundleRetraction U R) (h0O : (0 : E 0) ∈ r R '' U)
    {g : E 0 → F 0} (hg0 : g 0 = 0) (Dg : E 1 → E 0 →L[ℝ] F 0) :
    fillDefectDeriv U R g Dg 0 = Dg 0 - (scDeriv (U ×ˢ univ) (fun p : (E.prod F) 0 => (R p).2)
      0).comp ((scDeriv U (r R) 0).prod (Dg 0)) := by
  unfold fillDefectDeriv
  rw [levelMap_pairMap_r_zero hR h0O hg0]

/-- **Every derivative family of the fill defect has the value `fillDefectDeriv … 0` at `0`**
(uniqueness of `Dk(0)`, `IsSc1GermWith.eq_of_uniqueDiffWithinAt`): the germ analogue of
`IsFillerOf.scDeriv_sub_eq`. -/
theorem fillDefect_deriv_zero_eq (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U) (hG : G₁.U 0 ⊆ U) {g : E 0 → F 0}
    {Dg Dk : E 1 → E 0 →L[ℝ] F 0} (hg : IsSc1GermWith G₁ g Dg)
    (hk : IsSc1GermWith G₁ (fillDefect R g) Dk) : Dk 0 = fillDefectDeriv U R g Dg 0 :=
  hk.eq_of_uniqueDiffWithinAt (fillDefect_isSc1GermWith hU hR h0 hG hg) (G₁.zero_mem 1)
    (G₁.uniqueDiffWithinAt hU.isPartialQuadrant.isQuadrantLike 1 (G₁.zero_mem 1))

end FillDefect

/-! ### Lemma 3.17 for germs -/

section Lemma317

open StrongRetr

variable {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

/-- **Lemma 3.17 in the germ reading**: if the germ `g` fills `f̂` (Definition 3.6, germ reading)
and `ŝ` is a section of `K → O` sc-smooth on `U` (as in Theorem 3.15, where `ŝ` is the principal
part of an sc⁺-section of the bundle), then `g + ŝ ∘ r` is a filling germ of `f̂ + ŝ`, on the
same germ `G` and with the same derivative family `Dk` of the fill defect: `(1)`, `(2)` by Lemma
3.16, and `[1 − ρ(r(y))](g(y) + ŝ(r(y))) = [1 − ρ(r(y))]g(y)` on `U`. -/
theorem IsFillingGerm.add_section (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U) {fb g : E 0 → F 0}
    (hfg : IsFillingGerm hU hR h0 fb g) {s : E 0 → F 0} (hs : IsScSmooth U s)
    (hsK : ∀ x ∈ r R '' U, (x, s x) ∈ R '' (U ×ˢ univ)) :
    IsFillingGerm hU hR h0 (fun x => fb x + s x) (fun y => g y + s (r R y)) := by
  obtain ⟨h1, h2⟩ := lemma_3_16 hR hsK
  have heq : EqOn (fillDefect R g) (fillDefect R fun y => g y + s (r R y)) U := by
    intro y hy
    simp only [fillDefect]
    rw [(ρ_isLinear hR (r_mem hR hy)).map_add, (h2 y hy).1]
    abel
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hfg.eq_on] with x hx hxO
    rw [hx hxO, h1 x hxO]
  · filter_upwards [hfg.mem_of_fixed] with y hy hyU hfix
    refine hy hyU ?_
    rw [(ρ_isLinear hR (r_mem hR hyU)).map_add, (h2 y hyU).1] at hfix
    exact add_right_cancel hfix
  · obtain ⟨G, hGU, hg, Dk, hDk, Φ, hΦ⟩ := hfg.germ
    have hQ := hU.isPartialQuadrant.isQuadrantLike
    have hsr : IsScSmoothGerm G fun y => s (r R y) :=
      (IsScSmooth.comp hU.isScDomain hU.isScDomain hs (hR.baseRetraction hU).isScSmooth
        fun u hu => r_mem hR hu).isScSmoothGerm_of_subset hQ hU.relOpen h0 hGU
    exact ⟨G, hGU, hg.add hQ hsr, Dk, hDk.congr fun _ hy => heq (hGU hy), Φ, hΦ⟩

/-- **Lemma 3.17 in the germ reading, with `ŝ` itself a germ**: if `g` fills `f̂` and `ŝ` is an
sc-smooth germ on a germ `G_s`, a section of `K → O` on `O ∩ (G_s)₀`, then `g + ŝ ∘ r` is a
filling germ of `f̂ + ŝ`, on the germ `G ∩ r⁻¹(G_s)` (`r⁻¹(G_s)` is formed inside `ofSet U`, so
no inclusion `(G_s)₀ ⊆ U` is needed). -/
theorem IsFillingGerm.add_section_germ (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U) (h0O : (0 : E 0) ∈ r R '' U)
    {fb g : E 0 → F 0} (hfg : IsFillingGerm hU hR h0 fb g) {Gs : ScNbhdGerm E C}
    {s : E 0 → F 0} (hs : IsScSmoothGerm Gs s)
    (hsK : ∀ x ∈ r R '' U, x ∈ Gs.U 0 → (x, s x) ∈ R '' (U ×ˢ univ)) :
    IsFillingGerm hU hR h0 (fun x => fb x + s x) (fun y => g y + s (r R y)) := by
  have hQ := hU.isPartialQuadrant.isQuadrantLike
  have hr : IsScSmooth U (r R) := (hR.baseRetraction hU).isScSmooth
  have hrU : MapsTo (r R) U U := fun u hu => r_mem hR hu
  have hrC : MapsTo (r R) ((ScNbhdGerm.ofSet hU.relOpen h0).U 0) C := fun u hu =>
    hU.subset_quadrant (hrU hu)
  have hr0 : r R 0 = 0 := r_eq_self hR h0O
  -- the germ `r⁻¹(G_s)` and the sc-smooth germ `ŝ ∘ r` on it
  set Gr := (ScNbhdGerm.ofSet hU.relOpen h0).preimage Gs (hr.isSc1.isSc0.isSc0Germ hU.relOpen h0)
    hr0 hrC with hGr
  have hsr : IsScSmoothGerm Gr (s ∘ r R) := hs.comp_preimage hQ hQ hU.relOpen h0 hr hr0 hrC
  have hGrU : Gr.U 0 ⊆ U := fun y hy => hy.1
  have hGr0 : ∀ y ∈ Gr.U 0, r R y ∈ Gs.U 0 := fun y hy => by
    have := hy.2; rwa [levelMap_zero] at this
  -- `ρ(r(y)) ŝ(r(y)) = ŝ(r(y))` on `(G_r)₀`
  have hfix : ∀ y ∈ Gr.U 0, ρ R (r R y) (s (r R y)) = s (r R y) := fun y hy =>
    ρ_eq_self_of_mem_K hR (r_mem hR (hGrU hy)) (hsK _ ⟨y, hGrU hy, rfl⟩ (hGr0 y hy))
  have heq : EqOn (fillDefect R g) (fillDefect R fun y => g y + s (r R y)) (Gr.U 0) := by
    intro y hy
    simp only [fillDefect]
    rw [(ρ_isLinear hR (r_mem hR (hGrU hy))).map_add, hfix y hy]
    abel
  -- `(G_r)₀` is a neighbourhood of `0` in `U`
  have hnhds : ∀ᶠ y in 𝓝 (0 : E 0), y ∈ U → y ∈ Gr.U 0 := by
    obtain ⟨O, hO, hOeq⟩ := Gr.relOpen 0
    have h0O' : (0 : E 0) ∈ O := (hOeq ▸ Gr.zero_mem 0).1
    filter_upwards [hO.mem_nhds h0O'] with y hy hyU
    rw [hOeq]
    exact ⟨hy, hU.subset_quadrant hyU⟩
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hfg.eq_on] with x hx hxO
    rw [hx hxO, r_eq_self hR hxO]
  · filter_upwards [hfg.mem_of_fixed, hnhds] with y hy hyG hyU hfix'
    refine hy hyU ?_
    rw [(ρ_isLinear hR (r_mem hR hyU)).map_add, hfix y (hyG hyU)] at hfix'
    exact add_right_cancel hfix'
  · obtain ⟨G, hGU, hg, Dk, hDk, Φ, hΦ⟩ := hfg.germ
    refine ⟨G.inter Gr, fun _ hy => hGU hy.1, hg.add_inter hQ hsr, Dk,
      (hDk.mono (G.inter_subset_left Gr)).congr fun _ hy => heq hy.2, Φ, hΦ⟩

end Lemma317

/-! ### The fibre part of a strong bundle map on a germ, and the push-forward -/

section Pushforward

variable {E' F' : ScBanach} {C : Set (E 0)} {C' : Set (E' 0)} {U : Set (E 0)} {U' : Set (E' 0)}
  {Ψ : E 0 × F 0 → E' 0 × F' 0} {G₁ : ScNbhdGerm E C}

/-- The fibre part `(u, k) ↦ (Ψ(u, k))₂` of a strong bundle map is sc-smooth on `U ⊕ F`. -/
lemma IsStrongBundleMap.fiber_isScSmooth (hU : IsRelOpenInQuadrant E C U)
    (hΨ : IsStrongBundleMap U U' Ψ) :
    IsScSmooth (U ×ˢ univ) fun p : (E.prod F) 0 => (Ψ p).2 :=
  (IsScSmooth.comp (hU.prod_univ F).isScDomain (isScDomain_univ _)
    ((E'.prodSndOp F').isScSmooth (isScDomain_univ _)) hΨ.isScSmooth_zero (mapsTo_univ _ _)).congr
    (hU.prod_univ F).isScDomain fun _ _ => rfl

lemma pairMap_id_mapsTo (hG : G₁.U 0 ⊆ U) (k : E 0 → F 0) :
    MapsTo (pairMap id k) (G₁.U 0) (U ×ˢ univ) := fun _ hy => ⟨hG hy, mem_univ _⟩

/-- **The fibre part of a strong bundle map along a germ**: `u ↦ (Ψ(u, k(u)))₂` is an sc-smooth
germ on `G` for an sc-smooth germ `k` on `G` with `G₀ ⊆ U` (the text's push-forward
`Ψ ∘ (u, k(u))`, before composing with `ψ⁻¹`). -/
theorem IsStrongBundleMap.fiber_comp_isScSmoothGerm (hU : IsRelOpenInQuadrant E C U)
    (hΨ : IsStrongBundleMap U U' Ψ) (hG : G₁.U 0 ⊆ U) {k : E 0 → F 0}
    (hk : IsScSmoothGerm G₁ k) : IsScSmoothGerm G₁ fun u => (Ψ (u, k u)).2 :=
  (hΨ.fiber_isScSmooth hU).comp_germ hU.isPartialQuadrant.isQuadrantLike
    (hU.prod_univ F).isScDomain (hk.pair_id hU.isPartialQuadrant.isQuadrantLike)
    (pairMap_id_mapsTo hG k)

/-- The derivative family of `u ↦ (Ψ(u, k(u)))₂` for a germ `k` with derivatives `Dk`:
`D(Ψ₂)(x, k(x)) ∘ (1, Dk(x))`. -/
def fiberCompDeriv (U : Set (E 0)) (Ψ : E 0 × F 0 → E' 0 × F' 0) (k : E 0 → F 0)
    (Dk : E 1 → E 0 →L[ℝ] F 0) : E 1 → E 0 →L[ℝ] F' 0 := fun x =>
  (scDeriv (U ×ˢ univ) (fun p : (E.prod F) 0 => (Ψ p).2) (levelMap (pairMap id k) 1 x)).comp
    ((ContinuousLinearMap.id ℝ (E 0)).prod (Dk x))

theorem IsStrongBundleMap.fiber_comp_isSc1GermWith (hU : IsRelOpenInQuadrant E C U)
    (hΨ : IsStrongBundleMap U U' Ψ) (hG : G₁.U 0 ⊆ U) {k : E 0 → F 0}
    {Dk : E 1 → E 0 →L[ℝ] F 0} (hk : IsSc1GermWith G₁ k Dk) :
    IsSc1GermWith G₁ (fun u => (Ψ (u, k u)).2) (fiberCompDeriv U Ψ k Dk) :=
  (hΨ.fiber_isScSmooth hU).isSc1.isSc1With_scDeriv.comp_germ (hU.prod_univ F).isScDomain
    hk.pair_id (pairMap_id_mapsTo hG k)

lemma levelMap_pairMap_id_zero {k : E 0 → F 0} (hk0 : k 0 = 0) :
    levelMap (pairMap id k) 1 (0 : E 1) = 0 := by
  apply levelMap_eq_of_toBase_eq
  rw [map_zero, map_zero]
  change (0 : (E.prod F) 0) = (0, k 0)
  rw [hk0]; rfl

/-- **The derivative of `u ↦ (Ψ(u, k(u)))₂` at `0`**, for `k(0) = 0`:
`D(Ψ₂)(0, 0) ∘ (1, Dk(0))`.  With `IsStrongBundleMap.scDeriv_fiber_zero`
(`FredholmGermLinearization.lean`) this is `Γ(0) ∘ Dk(0)` (`fiberCompDeriv_zero_eq` in
`GermCalculusParam.lean`). -/
theorem fiberCompDeriv_zero {k : E 0 → F 0} (hk0 : k 0 = 0) (Dk : E 1 → E 0 →L[ℝ] F 0) :
    fiberCompDeriv U Ψ k Dk 0 = (scDeriv (U ×ˢ univ) (fun p : (E.prod F) 0 => (Ψ p).2) 0).comp
      ((ContinuousLinearMap.id ℝ (E 0)).prod (Dk 0)) := by
  unfold fiberCompDeriv
  rw [levelMap_pairMap_id_zero hk0]

variable {ψ' : E' 0 → E 0}

/-- **The push-forward of a germ by a strong bundle map covering `ψ = ψ'⁻¹`**: for `k` an
sc-smooth germ on `G` with `G₀ ⊆ U` and `ψ' : U' → U` sc-smooth on a relatively open `U' ∋ 0`
with `ψ'(0) = 0`, the map `x ↦ (Ψ(ψ'(x), k(ψ'(x))))₂` is an sc-smooth germ on the germ
`ofSet U' ∩ ψ'⁻¹(G)` (the text's `Ψ_*(k) = Ψ ∘ (u, k(u)) ∘ ψ⁻¹`, Definition 3.11). -/
theorem IsStrongBundleMap.pushforward_isScSmoothGerm (hU : IsRelOpenInQuadrant E C U)
    (hU' : IsRelOpenInQuadrant E' C' U') (h0U' : (0 : E' 0) ∈ U') (hΨ : IsStrongBundleMap U U' Ψ)
    (hG : G₁.U 0 ⊆ U) (hψ' : IsScSmooth U' ψ') (hψ'0 : ψ' 0 = 0) (hψ'C : MapsTo ψ' U' C)
    {k : E 0 → F 0} (hk : IsScSmoothGerm G₁ k) :
    IsScSmoothGerm ((ScNbhdGerm.ofSet hU'.relOpen h0U').preimage G₁
      (hψ'.isSc1.isSc0.isSc0Germ hU'.relOpen h0U') hψ'0 hψ'C)
      ((fun u => (Ψ (u, k u)).2) ∘ ψ') :=
  (hΨ.fiber_comp_isScSmoothGerm hU hG hk).comp_preimage hU.isPartialQuadrant.isQuadrantLike
    hU'.isPartialQuadrant.isQuadrantLike hU'.relOpen h0U' hψ' hψ'0 hψ'C

/-- The derivative family of the push-forward `(Ψ(·, k(·)))₂ ∘ ψ'`:
`D[(Ψ(·, k(·)))₂](ψ'(x)) ∘ Dψ'(x)`. -/
def pushforwardDeriv (U : Set (E 0)) (U' : Set (E' 0)) (Ψ : E 0 × F 0 → E' 0 × F' 0)
    (ψ' : E' 0 → E 0) (k : E 0 → F 0) (Dk : E 1 → E 0 →L[ℝ] F 0) : E' 1 → E' 0 →L[ℝ] F' 0 :=
  fun x => (fiberCompDeriv U Ψ k Dk (levelMap ψ' 1 x)).comp (scDeriv U' ψ' x)

/-- **The chain rule for the push-forward**: `pushforwardDeriv` is a derivative family of
`(Ψ(·, k(·)))₂ ∘ ψ'` on the germ `ofSet U' ∩ ψ'⁻¹(G)`. -/
theorem IsStrongBundleMap.pushforward_isSc1GermWith (hU : IsRelOpenInQuadrant E C U)
    (hU' : IsRelOpenInQuadrant E' C' U') (h0U' : (0 : E' 0) ∈ U') (hΨ : IsStrongBundleMap U U' Ψ)
    (hG : G₁.U 0 ⊆ U) (hψ' : IsSc1 U' ψ') (hψ'0 : ψ' 0 = 0) (hψ'C : MapsTo ψ' U' C)
    {k : E 0 → F 0} {Dk : E 1 → E 0 →L[ℝ] F 0} (hk : IsSc1GermWith G₁ k Dk) :
    IsSc1GermWith ((ScNbhdGerm.ofSet hU'.relOpen h0U').preimage G₁
      (hψ'.isSc0.isSc0Germ hU'.relOpen h0U') hψ'0 hψ'C)
      ((fun u => (Ψ (u, k u)).2) ∘ ψ') (pushforwardDeriv U U' Ψ ψ' k Dk) :=
  (hΨ.fiber_comp_isSc1GermWith hU hG hk).comp_preimage hU.isPartialQuadrant.isQuadrantLike
    hU'.relOpen h0U' hψ' hψ'0 hψ'C

lemma levelMap_one_zero_of_zero {ψ : E' 0 → E 0} (hψ0 : ψ 0 = 0) :
    levelMap ψ 1 (0 : E' 1) = 0 :=
  levelMap_eq_of_toBase_eq (by rw [map_zero, map_zero, hψ0])

/-- **The derivative of the push-forward at `0`**, for `k(0) = 0` and `ψ'(0) = 0`:
`D(Ψ₂)(0, 0) ∘ (1, Dk(0)) ∘ Dψ'(0)`. -/
theorem pushforwardDeriv_zero {k : E 0 → F 0} (hk0 : k 0 = 0) (hψ'0 : ψ' 0 = 0)
    (Dk : E 1 → E 0 →L[ℝ] F 0) :
    pushforwardDeriv U U' Ψ ψ' k Dk 0 =
      ((scDeriv (U ×ˢ univ) (fun p : (E.prod F) 0 => (Ψ p).2) 0).comp
        ((ContinuousLinearMap.id ℝ (E 0)).prod (Dk 0))).comp (scDeriv U' ψ' 0) := by
  unfold pushforwardDeriv
  rw [levelMap_one_zero_of_zero hψ'0, fiberCompDeriv_zero hk0]

end Pushforward

end Polyfold
