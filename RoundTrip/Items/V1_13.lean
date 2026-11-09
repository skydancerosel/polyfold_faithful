import Polyfold
import Polyfold.Test
import RoundTrip.Check
import RoundTrip.Blind.V1_13

/-! Round trip for V1_13 (Definition 1.14: sc¹ maps, the tangent map, and the remarks after it).

`A` is the conjunction of the types of the theorems in the item's declaration list:
`IsSc1With.eq_of_uniqueDiffWithinAt`, `IsSc1.scDeriv_eqOn`, `IsSc1.tangentMap_eqOn`,
`IsSc1.congr`, `IsSc1With.continuousOn_deriv`, `IsSc1With.exists_delta_deriv`,
`isSc1_iff_contDiffOn_of_finiteDimensional`, and (refresh 2026-11-02, added to the row)
`exists_isSc1_not_continuousOn_deriv`, `ScOneExample.isSc1With`, `ScOneExample.not_continuousAt_D`
(the definitions `tangentMapWith`, `IsSc1With`, `IsSc1`, `scDeriv`, `tangentMap` are vocabulary).
None has universe parameters.  `isSc1_iff_contDiffOn_of_finiteDimensional` lives in
`Polyfold/Test.lean`, which `import Polyfold` does not include, hence `import Polyfold.Test`.

Blind vs project notions: `tanSet = tangentSet`, `tanMap f D = tangentMapWith f D` (`rfl`),
`Sc1With ↔ IsSc1With`, `Sc1 ↔ IsSc1` (same fields): Definition 1.14 itself is formalized the same
way on both sides.

`B` is the conjunction of the three remarks after the definition, (a) "`x ↦ Df(x)` is in general
not continuous into `L(E₀, F₀)` with the operator norm", (b) "but it is with the compact-open
topology", (c) "in finite dimensions sc¹ = C¹".

* `A → B` is proved.  (a) is now `A`'s `exists_isSc1_not_continuousOn_deriv` (the example
  `f(t, x)_k = cos(k t) x_k` on `ℝ ⊕ X`, `X` a weighted `c₀` sc-Banach space), word for word
  after `Sc1 ↔ IsSc1`, `Sc1With ↔ IsSc1With`.  (b) from `A`'s `continuousOn_deriv` (joint continuity
  of `(x, h) ↦ Df(x)h` on `U₁ × E₀`, curried into `C(E₀, F₀)`); (c) for ANY sc-structures with
  `E₀`, `F₀` finite-dimensional and `U` relatively open in a partial quadrant (so with boundary
  points), from `A`'s `continuousOn_deriv` (`⇒`) and the project's Proposition 1.19 for `k = 0`
  (`⇐`), the levels being identified with `E₀`, `F₀` (the inclusions are bijective: a dense
  finite-dimensional subspace is everything).  `A`'s own finite-dimensional statement is narrower:
  constant structures and OPEN `U` only.
* `B → A` is proved: `exists_isSc1_not_continuousOn_deriv` is (a); the finite-dimensional conjunct
  of `A` is the special case `C = E = V` (constant structure), `U` open, of (c); the other six
  general conjuncts (uniqueness of `Df(x)` on sets of unique differentiability, congruence, joint
  continuity, uniform continuity on compacts) concern arbitrary `U` and are not consequences of
  the remarks; they are re-proved outright.  The two conjuncts about the project's specific
  example (`ScOneExample.isSc1With`, `ScOneExample.not_continuousAt_D`) are not about `B` at all
  (`B`'s (a) is an existence statement); they are re-assembled outright from the example's
  unbanned project lemmas (`hasFDerivAt_f`, `isSc0_f`, `toBase_tangentLevel`,
  `continuous_tangentLevel`, `two_le_norm_D_sub`), which carry the analysis. -/

namespace RoundTrip.V1_13
open Polyfold Set Filter Topology Metric

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.IsSc1With.eq_of_uniqueDiffWithinAt) ∧
    (type_of% @Polyfold.IsSc1.scDeriv_eqOn) ∧ (type_of% @Polyfold.IsSc1.tangentMap_eqOn) ∧
    (type_of% @Polyfold.IsSc1.congr) ∧ (type_of% @Polyfold.IsSc1With.continuousOn_deriv) ∧
    (type_of% @Polyfold.IsSc1With.exists_delta_deriv) ∧
    (type_of% @Polyfold.isSc1_iff_contDiffOn_of_finiteDimensional) ∧
    (type_of% @Polyfold.exists_isSc1_not_continuousOn_deriv) ∧
    (type_of% @Polyfold.ScOneExample.isSc1With) ∧
    (type_of% @Polyfold.ScOneExample.not_continuousAt_D)

theorem A_holds : A :=
  ⟨@Polyfold.IsSc1With.eq_of_uniqueDiffWithinAt, @Polyfold.IsSc1.scDeriv_eqOn,
    @Polyfold.IsSc1.tangentMap_eqOn, @Polyfold.IsSc1.congr, @Polyfold.IsSc1With.continuousOn_deriv,
    @Polyfold.IsSc1With.exists_delta_deriv, @Polyfold.isSc1_iff_contDiffOn_of_finiteDimensional,
    @Polyfold.exists_isSc1_not_continuousOn_deriv, @Polyfold.ScOneExample.isSc1With,
    @Polyfold.ScOneExample.not_continuousAt_D⟩

/-! ### The blind notions are the project's -/

theorem tanSet_eq (E : ScBanach) (U : Set (E.lvl 0)) : tanSet E U = E.tangentSet U := rfl

theorem tanMap_eq {E F : ScBanach} (f : E.lvl 0 → F.lvl 0) (D : E.lvl 1 → E.lvl 0 →L[ℝ] F.lvl 0) :
    tanMap f D = tangentMapWith f D := rfl

theorem sc1With_iff {E F : ScBanach} (U : Set (E.lvl 0)) (f : E.lvl 0 → F.lvl 0)
    (D : E.lvl 1 → E.lvl 0 →L[ℝ] F.lvl 0) : Sc1With U f D ↔ IsSc1With U f D :=
  ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.isSc0, h.hasFDerivWithinAt, h.tangent_isSc0⟩⟩

theorem sc1_iff {E F : ScBanach} (U : Set (E.lvl 0)) (f : E.lvl 0 → F.lvl 0) :
    Sc1 U f ↔ IsSc1 U f :=
  ⟨fun ⟨D, h⟩ => ⟨D, (sc1With_iff U f D).1 h⟩, fun ⟨D, h⟩ => ⟨D, (sc1With_iff U f D).2 h⟩⟩

/-! ### The three remarks, separately -/

/-- (a) In general `x ↦ Df(x)` is not continuous into `L(E₀, F₀)` with the operator norm. -/
def Ba : Prop :=
  ∃ (E F : ScBanach) (C U : Set (E.lvl 0)) (f : E.lvl 0 → F.lvl 0),
    IsRelOpenInQuadrant E C U ∧ Sc1 U f ∧
      ∀ D, Sc1With U f D → ¬ ContinuousOn D (E.lvlSet U 1)

/-- (b) It is continuous with the compact-open topology. -/
def Bb : Prop :=
  ∀ (E F : ScBanach) (C U : Set (E.lvl 0)) (f : E.lvl 0 → F.lvl 0)
    (D : E.lvl 1 → E.lvl 0 →L[ℝ] F.lvl 0),
    IsRelOpenInQuadrant E C U → Sc1With U f D →
      ContinuousOn (fun x => ((D x : E.lvl 0 →L[ℝ] F.lvl 0) : C(E.lvl 0, F.lvl 0)))
        (E.lvlSet U 1)

/-- (c) Between finite-dimensional spaces, sc¹ = C¹. -/
def Bc : Prop :=
  ∀ (E F : ScBanach), FiniteDimensional ℝ (E.lvl 0) → FiniteDimensional ℝ (F.lvl 0) →
    ∀ (C U : Set (E.lvl 0)) (f : E.lvl 0 → F.lvl 0), IsRelOpenInQuadrant E C U →
      (Sc1 U f ↔ ContDiffOn ℝ 1 f U)

theorem B_iff : B ↔ Ba ∧ Bb ∧ Bc := Iff.rfl

/-! ### Finite-dimensional sc-Banach spaces: every level is identified with level `0` -/

/-- If `E₀` is finite-dimensional, every inclusion `E_m → E₀` is onto (its range is a dense,
finite-dimensional, hence closed, subspace). -/
theorem toBase_surjective (E : ScBanach) [FiniteDimensional ℝ (E.lvl 0)] (m : ℕ) :
    Function.Surjective (E.toBase m) := by
  let S := LinearMap.range (E.toBase m : E.lvl m →ₗ[ℝ] E.lvl 0)
  have hcl : IsClosed (S : Set (E.lvl 0)) := S.closed_of_finiteDimensional
  have hd : Dense (S : Set (E.lvl 0)) := by
    refine (E.dense_smooth 0).mono ?_
    intro x hx
    have hx' : x ∈ E.toScScale.smooth := hx
    obtain ⟨y, hy⟩ := (ScScale.mem_smooth_iff _).1 hx' m
    exact ⟨y, hy⟩
  have hS : (S : Set (E.lvl 0)) = univ := by rw [← hcl.closure_eq]; exact hd.closure_eq
  intro x
  have hx : x ∈ (S : Set (E.lvl 0)) := hS ▸ mem_univ x
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, hy⟩

/-- The inclusion `E_m → E₀` as a continuous linear equivalence (`E₀` finite-dimensional). -/
noncomputable def toBaseEquiv (E : ScBanach) [FiniteDimensional ℝ (E.lvl 0)] (m : ℕ) :
    E.lvl m ≃L[ℝ] E.lvl 0 :=
  ContinuousLinearEquiv.ofBijective (E.toBase m) (LinearMap.ker_eq_bot.2 (E.toBase_injective m))
    (LinearMap.range_eq_top.2 (toBase_surjective E m))

theorem toBaseEquiv_apply (E : ScBanach) [FiniteDimensional ℝ (E.lvl 0)] (m : ℕ) (x : E.lvl m) :
    toBaseEquiv E m x = E.toBase m x := by
  simp [toBaseEquiv]

theorem toBase_symm (E : ScBanach) [FiniteDimensional ℝ (E.lvl 0)] (m : ℕ) (y : E.lvl 0) :
    E.toBase m ((toBaseEquiv E m).symm y) = y := by
  rw [← toBaseEquiv_apply]; exact (toBaseEquiv E m).apply_symm_apply y

/-! ### `A → (b) ∧ (c)` -/

/-- (b) from `A`'s `continuousOn_deriv`. -/
theorem Bb_of_continuousOn_deriv (hcd : type_of% @Polyfold.IsSc1With.continuousOn_deriv) : Bb := by
  intro E F C U f D _ hD
  have hc := hcd ((sc1With_iff U f D).1 hD)
  rw [continuousOn_iff_continuous_domRestrict]
  let G : C(E.lvlSet U 1 × E.lvl 0, F.lvl 0) :=
    ⟨fun q => D q.1 q.2, hc.comp_continuous (f := fun q : E.lvlSet U 1 × E.lvl 0 =>
      ((q.1 : E.lvl 1), q.2)) (by fun_prop) (fun q => q.1.2)⟩
  have : (E.lvlSet U 1).domRestrict
      (fun x => ((D x : E.lvl 0 →L[ℝ] F.lvl 0) : C(E.lvl 0, F.lvl 0))) = G.curry := by
    funext x; ext h; rfl
  rw [this]
  exact G.curry.continuous

/-- (c) `⇒`, from `A`'s `continuousOn_deriv`: an sc¹ map between finite-dimensional sc-Banach
spaces is `C¹` within `U`. -/
theorem contDiffOn_of_sc1 (hcd : type_of% @Polyfold.IsSc1With.continuousOn_deriv)
    {E F : ScBanach} [FiniteDimensional ℝ (E.lvl 0)] {U : Set (E.lvl 0)} {f : E.lvl 0 → F.lvl 0}
    {D : E.lvl 1 → E.lvl 0 →L[ℝ] F.lvl 0} (hD : IsSc1With U f D) : ContDiffOn ℝ 1 f U := by
  set e := toBaseEquiv E 1
  have hmaps : MapsTo e.symm U (E.lvlSet U 1) := fun y hy => by
    rw [ScBanach.mem_lvlSet, toBase_symm]; exact hy
  have hder : ∀ y ∈ U, HasFDerivWithinAt f (D (e.symm y)) U y := by
    intro y hy
    have h1 := (hD.hasFDerivWithinAt (e.symm y) (hmaps hy)).comp y
      (e.symm : E.lvl 0 →L[ℝ] E.lvl 1).hasFDerivWithinAt hmaps
    have hfun : (f ∘ E.toBase 1) ∘ e.symm = f :=
      funext fun z => by simp [e, toBase_symm]
    have hlin : ((D (e.symm y)).comp (E.toBase 1)).comp (e.symm : E.lvl 0 →L[ℝ] E.lvl 1) =
        D (e.symm y) := by
      ext v; simp [e, toBase_symm]
    rwa [hfun, hlin] at h1
  have hcont : ContinuousOn (fun y => D (e.symm y)) U := by
    rw [continuousOn_clm_apply]
    intro v
    exact (hcd hD).comp (f := fun y : E.lvl 0 => ((e.symm y : E.lvl 1), v))
      (e.symm.continuous.prodMk continuous_const).continuousOn (fun y hy => hmaps hy)
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_hasFDerivWithinAt (by simp)]
  intro y hy
  refine ⟨U, ?_, fun h0 => absurd h0 (by simp), fun y => D (e.symm y), hder, ?_⟩
  · rw [insert_eq_of_mem hy]; exact self_mem_nhdsWithin
  · rw [contDiffOn_zero]; exact hcont

/-- (c) `⇐` (outright, from the project's Proposition 1.19 for `k = 0`): a `C¹` map between
finite-dimensional sc-Banach spaces is sc¹ on a relatively open subset of a partial quadrant. -/
theorem sc1_of_contDiffOn {E F : ScBanach} [FiniteDimensional ℝ (E.lvl 0)]
    [FiniteDimensional ℝ (F.lvl 0)] {C U : Set (E.lvl 0)} {f : E.lvl 0 → F.lvl 0}
    (hU : IsRelOpenInQuadrant E C U) (hf : ContDiffOn ℝ 1 f U) : IsSc1 U f := by
  have hlm : ∀ m, levelMap f m = fun x => (toBaseEquiv F m).symm (f (E.toBase m x)) :=
    fun m => funext fun x => levelMap_eq_of_toBase_eq (toBase_symm F m _)
  have hlev : ∀ m, ContDiffOn ℝ 1 (levelMap f m) (E.lvlSet U m) := fun m => by
    rw [hlm]
    exact ((toBaseEquiv F m).symm : F.lvl 0 →L[ℝ] F.lvl m).contDiff.comp_contDiffOn
      (hf.comp_continuousLinearMap (E.toBase m))
  have hsc0 : IsSc0 E F U f :=
    ⟨fun m x _ => ⟨(toBaseEquiv F m).symm (f (E.toBase m x)), toBase_symm F m _⟩,
      fun m => (hlev m).continuousOn⟩
  exact ⟨_, proposition_1_2_4_zero hU.isScDomain hsc0 hlev⟩

theorem Bc_of_continuousOn_deriv (hcd : type_of% @Polyfold.IsSc1With.continuousOn_deriv) : Bc := by
  intro E F hE hF C U f hU
  rw [sc1_iff]
  exact ⟨fun ⟨_, hD⟩ => contDiffOn_of_sc1 hcd hD, sc1_of_contDiffOn hU⟩

/-- `A` gives remarks (b) and (c). -/
theorem A_to_Bbc : A → Bb ∧ Bc := fun hA =>
  ⟨Bb_of_continuousOn_deriv hA.2.2.2.2.1, Bc_of_continuousOn_deriv hA.2.2.2.2.1⟩

/-- (a) is `A`'s `exists_isSc1_not_continuousOn_deriv`. -/
theorem Ba_of_exists (h : type_of% @Polyfold.exists_isSc1_not_continuousOn_deriv) : Ba := by
  obtain ⟨E, F, C, U, f, hU, hf, hD⟩ := h
  exact ⟨E, F, C, U, f, hU, (sc1_iff U f).2 hf, fun D hD' => hD D ((sc1With_iff U f D).1 hD')⟩

theorem A_to_B : A → B := fun hA =>
  ⟨Ba_of_exists hA.2.2.2.2.2.2.2.1, (A_to_Bbc hA).1, (A_to_Bbc hA).2⟩

/-! ### `B → A` -/

section Outright

variable {E F : ScBanach} {U : Set (E.lvl 0)} {f : E.lvl 0 → F.lvl 0}
  {D : E.lvl 1 → E.lvl 0 →L[ℝ] F.lvl 0}

theorem eq_of_uniqueDiffWithinAt' (h : IsSc1With U f D) {D' : E.lvl 1 → E.lvl 0 →L[ℝ] F.lvl 0}
    (h' : IsSc1With U f D') {x : E.lvl 1} (hx : x ∈ E.lvlSet U 1)
    (hU : UniqueDiffWithinAt ℝ (E.lvlSet U 1) x) : D x = D' x := by
  have h1 := hU.eq (h.hasFDerivWithinAt x hx) (h'.hasFDerivWithinAt x hx)
  have hd : Dense (Submodule.span ℝ (range (E.toBase 1)) : Set (E.lvl 0)) :=
    Dense.mono Submodule.subset_span (E.denseRange_inclK 0 1)
  refine ContinuousLinearMap.ext_on hd ?_
  rintro _ ⟨y, rfl⟩
  exact congrArg (fun L : E.lvl 1 →L[ℝ] F.lvl 0 => L y) h1

theorem scDeriv_eqOn' (h : IsSc1With U f D)
    (hU : ∀ x ∈ E.lvlSet U 1, UniqueDiffWithinAt ℝ (E.lvlSet U 1) x) :
    EqOn (scDeriv U f) D (E.lvlSet U 1) :=
  fun x hx => eq_of_uniqueDiffWithinAt' h.isSc1.isSc1With_scDeriv h hx (hU x hx)

theorem continuousOn_deriv' (h : IsSc1With U f D) :
    ContinuousOn (fun p : E.lvl 1 × E.lvl 0 => D p.1 p.2) {p | p.1 ∈ E.lvlSet U 1} := by
  have := (h.tangent_isSc0.continuousOn 0)
  refine (continuous_snd.comp_continuousOn this).congr fun p _ => ?_
  change D p.1 p.2 = (levelMap (tangentMapWith f D) 0 p).2
  rw [levelMap_zero]; rfl

end Outright

/-! ### The project's example, re-assembled from its unbanned lemmas (not from `B`) -/

/-- `ScOneExample.isSc1With`, from `isSc0_f`, `hasFDerivAt_f`, `toBase_tangentLevel`,
`continuous_tangentLevel`. -/
theorem isSc1With' : IsSc1With univ ScOneExample.f ScOneExample.D where
  isSc0 := ScOneExample.isSc0_f
  hasFDerivWithinAt p _ := by
    rw [ScBanach.lvlSet_univ]
    have hfun : ScOneExample.f ∘ ScOneExample.E.toBase 1 =
        fun q : ℝ × ScOneExample.c0 => ScOneExample.cosOp q.1 (ScOneExample.inclOp q.2) := by
      funext q
      simp only [Function.comp, ScOneExample.f]
      rw [ScOneExample.E_toBase]
      rfl
    rw [hfun]
    refine ((ScOneExample.hasFDerivAt_f p.1 p.2).congr_fderiv ?_).hasFDerivWithinAt
    refine ContinuousLinearMap.ext fun q => ?_
    rw [ContinuousLinearMap.comp_apply, ScOneExample.D_apply, ScOneExample.E_toBase]
    rfl
  tangent_isSc0 :=
    { mem_range := fun m p _ =>
        ⟨ScOneExample.tangentLevel p, ScOneExample.toBase_tangentLevel m p⟩
      continuousOn := fun m => ScOneExample.continuous_tangentLevel.continuousOn.congr fun p _ =>
        levelMap_eq_of_toBase_eq (ScOneExample.toBase_tangentLevel m p) }

/-- `ScOneExample.not_continuousAt_D`, from the estimate `two_le_norm_D_sub`. -/
theorem not_continuousAt_D' : ¬ ContinuousAt ScOneExample.D ((0, 0) : ScOneExample.E 1) := by
  intro h
  obtain ⟨δ, hδ, hδ'⟩ :=
    (Metric.continuousAt_iff (α := ScOneExample.E 1)
      (β := ScOneExample.E 0 →L[ℝ] ScOneExample.X 0) (f := ScOneExample.D) (a := (0, 0))).1
      h 2 two_pos
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.pi / δ)
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hsmall : Real.pi / ((n : ℝ) + 1) < δ := by
    rw [div_lt_iff₀ hpos]
    rw [div_lt_iff₀ hδ] at hn
    nlinarith [Real.pi_pos]
  have hd : dist ((Real.pi / ((n : ℝ) + 1), 0) : ScOneExample.E 1)
      ((0, 0) : ScOneExample.E 1) < δ := by
    rw [Prod.dist_eq, dist_self, Real.dist_eq, sub_zero,
      abs_of_pos (div_pos Real.pi_pos hpos)]
    exact max_lt hsmall hδ
  have h1 := hδ' hd
  have h2 : dist (ScOneExample.D ((Real.pi / ((n : ℝ) + 1), 0) : ScOneExample.E 1))
      (ScOneExample.D ((0, 0) : ScOneExample.E 1)) =
      ‖ScOneExample.D ((Real.pi / ((n : ℝ) + 1), 0) : ScOneExample.E 1) -
        ScOneExample.D ((0, 0) : ScOneExample.E 1)‖ :=
    dist_eq_norm (E := ScOneExample.E 0 →L[ℝ] ScOneExample.X 0) _ _
  have h3 := ScOneExample.two_le_norm_D_sub n
  linarith

/-- `B → A`: `exists_isSc1_not_continuousOn_deriv` is remark (a); the finite-dimensional conjunct
from remark (c); the six general conjuncts and the two about the project's example re-proved
outright. -/
theorem B_to_A : B → A := by
  intro hB
  refine ⟨@eq_of_uniqueDiffWithinAt', @scDeriv_eqOn', ?_, ?_, @continuousOn_deriv', ?_, ?_, ?_,
    isSc1With', not_continuousAt_D'⟩
  · -- tangentMap_eqOn
    intro E F U f D h hU p hp
    change (levelMap f 1 p.1, scDeriv U f p.1 p.2) = (levelMap f 1 p.1, D p.1 p.2)
    rw [scDeriv_eqOn' h hU hp]
  · -- IsSc1.congr
    intro E F U f h f' hff'
    exact ⟨_, h.isSc1With_scDeriv.congr hff'⟩
  · -- exists_delta_deriv
    intro E F U f D h x hx K hK c hc
    let Θ : E.lvlSet U 1 × E.lvl 0 → F.lvl 0 := fun q => D q.1.1 q.2 - D x q.2
    have hΘ : Continuous Θ := by
      have h1 : Continuous fun q : E.lvlSet U 1 × E.lvl 0 => D q.1.1 q.2 := by
        refine (continuousOn_deriv' h).comp_continuous
          (f := fun q : E.lvlSet U 1 × E.lvl 0 => ((q.1 : E.lvl 1), q.2)) ?_ ?_
        · fun_prop
        · intro q; exact q.1.2
      exact h1.sub ((D x).continuous.comp continuous_snd)
    have key : ∀ᶠ y in 𝓝 (⟨x, hx⟩ : E.lvlSet U 1), ∀ w ∈ K, ‖Θ (y, w)‖ ≤ c := by
      refine hK.eventually_forall_of_forall_eventually (P := fun y w => ‖Θ (y, w)‖ ≤ c)
        fun w _ => ?_
      have h0 : Θ (⟨x, hx⟩, w) = 0 := by simp [Θ]
      have := hΘ.continuousAt.eventually_mem (x := (⟨x, hx⟩, w))
        (s := Metric.closedBall 0 c) (by rw [h0]; exact Metric.closedBall_mem_nhds 0 hc)
      exact this.mono fun q hq => by simpa using hq
    obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 key
    refine ⟨δ, hδ, fun x' hx' hxδ w hw => ?_⟩
    have := hδ' (y := ⟨x', hx'⟩) (by rw [Subtype.dist_eq, dist_eq_norm]; exact hxδ) w hw
    simpa [Θ] using this
  · -- finite dimensions: remark (c) with `E = const V`, `C = V`, `U` open
    intro V W _ _ _ _ _ _ U hU f
    have hrel : IsRelOpenInQuadrant (ScBanach.const V) univ U :=
      ⟨isPartialQuadrant_univ _, U, hU, (inter_univ U).symm⟩
    exact (sc1_iff U f).symm.trans
      (hB.2.2 (ScBanach.const V) (ScBanach.const W) (inferInstanceAs (FiniteDimensional ℝ V))
        (inferInstanceAs (FiniteDimensional ℝ W)) univ U f hrel)
  · -- remark (a)
    obtain ⟨E, F, C, U, f, hU, hf, hD⟩ := hB.1
    exact ⟨E, F, C, U, f, hU, (sc1_iff U f).1 hf, fun D hD' => hD D ((sc1With_iff U f D).2 hD')⟩

#rt_check RoundTrip.V1_13.A_to_B [Polyfold.IsSc1With.eq_of_uniqueDiffWithinAt,
  Polyfold.IsSc1.scDeriv_eqOn, Polyfold.IsSc1.tangentMap_eqOn, Polyfold.IsSc1.congr,
  Polyfold.IsSc1With.continuousOn_deriv, Polyfold.IsSc1With.exists_delta_deriv,
  Polyfold.isSc1_iff_contDiffOn_of_finiteDimensional, Polyfold.exists_isSc1_not_continuousOn_deriv,
  Polyfold.ScOneExample.isSc1With, Polyfold.ScOneExample.not_continuousAt_D]
#rt_check RoundTrip.V1_13.B_to_A [Polyfold.IsSc1With.eq_of_uniqueDiffWithinAt,
  Polyfold.IsSc1.scDeriv_eqOn, Polyfold.IsSc1.tangentMap_eqOn, Polyfold.IsSc1.congr,
  Polyfold.IsSc1With.continuousOn_deriv, Polyfold.IsSc1With.exists_delta_deriv,
  Polyfold.isSc1_iff_contDiffOn_of_finiteDimensional, Polyfold.exists_isSc1_not_continuousOn_deriv,
  Polyfold.ScOneExample.isSc1With, Polyfold.ScOneExample.not_continuousAt_D]
#rt_overlap RoundTrip.V1_13.B_to_A [Polyfold.IsSc1With.eq_of_uniqueDiffWithinAt,
  Polyfold.IsSc1.scDeriv_eqOn, Polyfold.IsSc1.tangentMap_eqOn, Polyfold.IsSc1.congr,
  Polyfold.IsSc1With.continuousOn_deriv, Polyfold.IsSc1With.exists_delta_deriv,
  Polyfold.isSc1_iff_contDiffOn_of_finiteDimensional, Polyfold.exists_isSc1_not_continuousOn_deriv,
  Polyfold.ScOneExample.isSc1With, Polyfold.ScOneExample.not_continuousAt_D]

end RoundTrip.V1_13
