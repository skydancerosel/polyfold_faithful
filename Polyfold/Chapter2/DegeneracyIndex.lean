import Polyfold.Chapter1.Degeneracy
import Polyfold.Chapter2.MPolyfold

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §2.3,
Definition 2.22, Lemma 2.23, Proposition 2.24, Definition 2.25, the subspaces `E_x`, and
Corollary 2.32 (with the core of Theorem 2.31); and §1.3, Theorem 1.25, which the text quotes from
[20] and whose proof is the argument of §2.3.

# The degeneracy index of an M-polyfold; boundary recognition

## The text, paraphrased

For a chart `(V, φ, (O, C, E))` around `x ∈ X` put `d(x, φ) = d_C(φ(x))`.  (Definition 2.22) The
degeneracy index `d_X(x)` is the minimum of `d(x, φ)` over all charts around `x`.  (Lemma 2.23)
`d_X(y) ≤ d_X(x)` for `y` near `x`.  (Proposition 2.24) A germ of sc-diffeomorphisms
`f : (U, x) → (V, f(x))` has `d_X(x) = d_Y(f(x))`.  (Definition 2.25) `∂X = {d_X ≥ 1}`.
For `E = ℝᵏ ⊕ W`, `C = [0,∞)ᵏ ⊕ W` and `x ∈ C`, `E_x = {(a, w) | a_i = 0 for all i with x_i = 0}`;
for a retract `O` and `x ∈ O_∞`, `T_x^R O = T_xO ∩ E_x` (Definition 2.27).  (Theorem 2.31) For a
smooth `x ∈ O`, `dim(T_xO / T_x^R O) ≤ d_O(x)`, where `d_O` is the degeneracy index of `O` as an
M-polyfold, i.e. the minimum of `d_{C'}(φ(x))` over germs of sc-diffeomorphisms `φ : (O, x) →
(O', φ(x))` into retracts.  (Corollary 2.32) For a partial quadrant `C`, viewed as the M-polyfold
`X_C`, `d_{X_C} = d_C`: for smooth `x`, `T_xC = E` and `T_x^R C = E_x` give `d_C(x) =
dim(E/E_x) ≤ d_{X_C}(x) ≤ d_C(x)`; a general `x` is a limit of smooth `x_k` with
`d_C(x_k) = d_C(x)`, and `d_{X_C}(x_k) ≤ d_{X_C}(x)` for large `k` by Lemma 2.23.
(Theorem 1.25) For a germ `f : (U, x) → (U', f(x))` of local sc-diffeomorphisms between
relatively open subsets of partial quadrants, `d_C(x) = d_{C'}(f(x))`.

## What is formalized

* `Polyfold.minimalSubspaceWith T x` (`E_x`, for a presentation `T : E ≅ ℝⁿ ⊕ W` of `C`), with
  `finrank_quotient_minimalSubspaceWith : dim(E/E_x) = d_C(x)`.
* `Polyfold.eventually_degIndexWith_le`: upper semicontinuity of `d_C`.
* `IsSc1With.deriv_mem_minimalSubspace_of_lvl1` (the **sign argument** of Lemma 2.29 / Theorem
  2.31): if `f` is sc¹ on `U ⊆ C` with values in `C'`, `x ∈ U₁`, `v ∈ E₁ ∩ E_x`, then
  `Df(x)v ∈ E'_{f(x)}`; `IsSc1With.mapsTo_minimalSubspace` extends it to all `v ∈ E_x` by the
  density of `E₁ ∩ E_x` in `E_x` (`ScBanach.subset_closure_ker_inter_range_toBase`).
* `Polyfold.degIndexWith_le_of_germ`: the core of Theorem 2.31 in the form used by Corollary 2.32
  and Theorem 1.25.  For a germ `F : (U₀, x) → (O', F(x))` of sc-diffeomorphisms from a relatively
  open `U₀ ⊆ C` to a retract `O' = r'(U')`, with inverse `G`, and `x ∈ U₀` on level `1`:
  `d_C(x) = dim(E/E_x) = dim(T_yO'/T_y^R O') ≤ dim(E'/E'_y) = d_{C'}(y)`, `y = F(x)`.
* `Polyfold.theorem_1_25` (**Theorem 1.25**), `Polyfold.theorem_1_25_lvl1` (the level-`1` case).
* `MPolyfold.degIndex P x` (**Definition 2.22**, over the maximal atlas), `Polyfold.lemma_2_23`
  (**Lemma 2.23**), `MPolyfold.IsScDiffeoOn` and `Polyfold.proposition_2_24`
  (**Proposition 2.24**), `MPolyfold.boundary` (**Definition 2.25**).
* `Polyfold.corollary_2_32` (**Corollary 2.32**), for a nonempty relatively open subset `U` of a
  partial quadrant `C` viewed as an M-polyfold: `d_{X_U} = d_C` on `U`.

## What the text leaves implicit, and the choices made

* The text proves Theorem 2.31 for *smooth* points and Corollary 2.32 by approximating with smooth
  points.  The argument only needs points on level `1` (where the derivative exists), and the
  approximation by level-`1` points `T⁻¹(a, w')`, `w' ∈ W₁`, which keeps `d_C` constant; this is
  what is formalized.  Smoothness of `x` is not needed anywhere in §2.3's index computations.
* The "sign argument" (`x + tv ∈ C` for small `|t|`, differentiate a nonnegative function with a
  zero at `t = 0`) appears in the text in the proofs of Lemma 2.29 and Proposition 2.35; it is
  formalized once, through `IsLocalMin.hasDerivAt_eq_zero`, as the derivative of
  `t ↦ (T'(f(x + tv)))_j` at `0`.  Since `f` is differentiable only along `E₁` (Definition 1.14),
  the argument gives `Df(x)(E_x ∩ E₁) ⊆ E'_{f(x)}` and the density of `E_x ∩ E₁` in `E_x` is
  needed to conclude; the text asserts "the closure of `(T_x^R O)_∞` is `T_x^R O`" without proof.
  Here the density is proved for the kernel of any continuous linear map to a finite-dimensional
  space (`E_x` is such a kernel), without the sc-structure of `T_xO`.
* Theorem 2.31 is stated in the text for the degeneracy index `d_O` of a retract as an M-polyfold,
  i.e. over all sc-diffeomorphism germs into retracts.  The formalization proves the inequality for
  one germ (`degIndexWith_le_of_germ`) and deduces Corollary 2.32 by quantifying over the charts of
  the maximal atlas of `X_U`.  The general Theorem 2.31 (`dim(T_xO/T_x^R O) ≤ d_O(x)` for every
  retract `O`, and indeed for every chart of every M-polyfold) is `Polyfold.theorem_2_31` in
  `Boundary.lean` (with `theorem_2_31_retract`, the text's form), from the one-germ inequality
  between retracts `ScRetraction.IsDiffeoGerm.quotDim_le`, the same argument with `U₀` replaced
  by a retract.  Its second statement (if `dim(T_xO/T_x^R O) = d_O(x)` then `C_xO` is a partial
  quadrant in `T_xO`) is not formalized in general (gap G.11 of the report); for tame retracts
  the conclusion is proved directly (`proposition_2_36_partialCone` in `PartialCone.lean`).
* Theorem 1.25 is quoted in Chapter 1 from [20, Theorem 1.19] without proof; its hypotheses "germ
  of a local sc-diffeomorphism" are read as: `f : U → U'` and `g : U' → U` sc¹ (sc¹ suffices;
  the text has sc-smooth), inverse to each other on `U` and `U'`.
* Proposition 2.24's "germ of sc-diffeomorphisms" is `IsScDiffeoOn P Q f U V`: `f` sc-smooth on
  the open `U`, with an sc-smooth inverse on the open `V = f(U)`.  The proof constructs the chart
  `ψ ∘ f` of `X` from a chart `ψ` of `Y` (which the text calls "deduced immediately from the
  definitions"); that it is a chart of the maximal atlas uses Definition 2.14 for `f` and `g`.
-/

open Set Filter Topology Function Module

noncomputable section

namespace Polyfold

variable {E E' : ScBanach}

/-! ### The subspaces `E_x` and `dim(E/E_x) = d_C(x)` -/

section MinimalSubspace

variable {n : ℕ} {W : ScBanach}

/-- The base level `ℝⁿ × W₀` of `ℝⁿ ⊕ W`. -/
local macro "V" n:term:max W:term:max : term => `((((ScBanach.const (Fin $n → ℝ)).prod $W) 0))

/-- The coordinates `(u_i)_{i ∈ I(p)}`, `I(p) = {i | p_i = 0}`, as a continuous linear map. -/
def coordProj (p : V n W) : (V n W) →L[ℝ] ({i : Fin n // p.1 i = 0} → ℝ) :=
  ContinuousLinearMap.pi fun i => (ContinuousLinearMap.proj i.1).comp
    (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (W 0))

@[simp] lemma coordProj_apply (p u : V n W) (i : {i : Fin n // p.1 i = 0}) :
    coordProj p u i = u.1 i.1 := rfl

lemma coordProj_surjective (p : V n W) : Surjective (coordProj p) := by
  intro v
  classical
  refine ⟨((fun i => if h : p.1 i = 0 then v ⟨i, h⟩ else 0), 0), ?_⟩
  funext i
  change (if h : p.1 i.1 = 0 then v ⟨i.1, h⟩ else 0) = v i
  rw [dif_pos i.2]

/-- The coordinate map `v ↦ ((Tv)_i)_{i ∈ I(x)}` on `E₀`. -/
def coordMapL (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (x : E 0) :
    E 0 →L[ℝ] ({i : Fin n // (T 0 x).1 i = 0} → ℝ) :=
  (coordProj (T 0 x)).comp (T 0 : E 0 →L[ℝ] V n W)

@[simp] lemma coordMapL_apply (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (x v : E 0)
    (i : {i : Fin n // (T 0 x).1 i = 0}) : coordMapL T x v i = (T 0 v).1 i.1 := rfl

lemma coordMapL_surjective (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (x : E 0) :
    Surjective (coordMapL T x) :=
  (coordProj_surjective _).comp (T 0).surjective

/-- `E_x ⊆ E₀` for the presentation `T : E ≅ ℝⁿ ⊕ W` of a partial quadrant: the vectors `v` with
`(Tv)_i = 0` whenever `(Tx)_i = 0` (the text's `E_x = E_{I(x)}`, transported by `T`). -/
def minimalSubspaceWith (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (x : E 0) :
    Submodule ℝ (E 0) :=
  LinearMap.ker (coordMapL T x).toLinearMap

lemma mem_minimalSubspaceWith (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) {x v : E 0} :
    v ∈ minimalSubspaceWith T x ↔ ∀ i, (T 0 x).1 i = 0 → (T 0 v).1 i = 0 := by
  rw [minimalSubspaceWith, LinearMap.mem_ker]
  constructor
  · intro h i hi
    exact congrFun h ⟨i, hi⟩
  · intro h
    funext i
    exact h i.1 i.2

lemma isClosed_minimalSubspaceWith (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (x : E 0) :
    IsClosed (minimalSubspaceWith T x : Set (E 0)) :=
  (coordMapL T x).isClosed_ker

/-- `dim(E/E_x) = d_C(x)`: the codimension of `E_x` is the degeneracy index. -/
theorem finrank_quotient_minimalSubspaceWith (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (x : E 0) : finrank ℝ (E 0 ⧸ minimalSubspaceWith T x) = degIndexWith T x := by
  classical
  have e : (E 0 ⧸ minimalSubspaceWith T x) ≃ₗ[ℝ] ({i : Fin n // (T 0 x).1 i = 0} → ℝ) :=
    LinearMap.quotKerEquivOfSurjective (coordMapL T x).toLinearMap (coordMapL_surjective T x)
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_subtype]
  rfl

instance finiteDimensional_quotient_minimalSubspaceWith
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (x : E 0) :
    FiniteDimensional ℝ (E 0 ⧸ minimalSubspaceWith T x) := by
  have e : (E 0 ⧸ minimalSubspaceWith T x) ≃ₗ[ℝ] ({i : Fin n // (T 0 x).1 i = 0} → ℝ) :=
    LinearMap.quotKerEquivOfSurjective (coordMapL T x).toLinearMap (coordMapL_surjective T x)
  exact LinearEquiv.finiteDimensional e.symm

/-- Upper semicontinuity of the degeneracy index: `d_C(y) ≤ d_C(x)` for `y` near `x`. -/
theorem eventually_degIndexWith_le (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (x : E 0) :
    ∀ᶠ y in 𝓝 x, degIndexWith T y ≤ degIndexWith T x := by
  classical
  have h : ∀ i : Fin n, ∀ᶠ y in 𝓝 x, (T 0 y).1 i = 0 → (T 0 x).1 i = 0 := by
    intro i
    by_cases hi : (T 0 x).1 i = 0
    · exact Eventually.of_forall fun _ _ => hi
    · have hc : Continuous fun y : E 0 => (T 0 y).1 i :=
        (continuous_apply i).comp (continuous_fst.comp (T 0).continuous)
      exact ((hc.tendsto x).eventually (isOpen_ne.mem_nhds hi)).mono fun y hy h0 => (hy h0).elim
  refine (eventually_all.2 h).mono fun y hy => ?_
  change (Finset.univ.filter fun i => (T 0 y).1 i = 0).card ≤
    (Finset.univ.filter fun i => (T 0 x).1 i = 0).card
  exact Finset.card_le_card fun i hi => by
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, hy i hi.2⟩

/-- Points of the partial quadrant `C` on level `1` with the same degeneracy index accumulate at
every point of `C`: for `x ∈ C`, the points `T⁻¹(a, w')`, `w' ∈ W₁`, where `T x = (a, w)`. -/
theorem exists_tendsto_lvl1_degIndexWith (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (x : E 0) : ∃ (ι : Type) (l : Filter ι) (σ : ι → E 0), l.NeBot ∧ Tendsto σ l (𝓝 x) ∧
      (∀ᶠ i in l, σ i ∈ range (E.toBase 1)) ∧ (∀ i, degIndexWith T (σ i) = degIndexWith T x) ∧
      (∀ i, T 0 (σ i) ∈ quadrant n W 0 ↔ T 0 x ∈ quadrant n W 0) := by
  set a := (T 0 x).1 with ha
  set w := (T 0 x).2 with hw
  let W₁ : Set (W 0) := range (W.toBase 1)
  have hdense : Dense W₁ := by
    have := W.denseRange_incl 0
    exact this
  let σ : W 0 → E 0 := fun w' => (T 0).symm (a, w')
  refine ⟨W 0, 𝓝[W₁] w, σ, mem_closure_iff_nhdsWithin_neBot.1 (hdense w), ?_, ?_, ?_, ?_⟩
  · have hσ : Continuous σ := (T 0).symm.continuous.comp (continuous_const.prodMk continuous_id)
    have : σ w = x := by
      simp only [σ, ha, hw, Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply]
    rw [← this]
    exact (hσ.tendsto w).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with w' hw'
    obtain ⟨w₁, rfl⟩ := hw'
    refine ⟨(T 1).symm ((a, w₁) : ((ScBanach.const (Fin n → ℝ)).prod W) 1), ?_⟩
    rw [T.symm_toBase_comm, ScBanach.prod_toBase]
    simp only [σ]
    congr 2
  · intro w'
    show quadrantDeg (T 0 ((T 0).symm (a, w'))) = quadrantDeg (T 0 x)
    rw [ContinuousLinearEquiv.apply_symm_apply]
    rfl
  · intro w'
    show T 0 ((T 0).symm (a, w')) ∈ quadrant n W 0 ↔ _
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact Iff.rfl

end MinimalSubspace

/-! ### The sign argument -/

section Sign

variable {n n' : ℕ} {W W' : ScBanach} {C : Set (E 0)} {C' : Set (E' 0)} {U : Set (E 0)}
  {f : E 0 → E' 0} {D : E 1 → E 0 →L[ℝ] E' 0}

/-- `x + tv ∈ U₁` for `|t|` small, when `x ∈ U₁`, `U` is relatively open in `C = T⁻¹(quadrant)`,
and `v ∈ E_x` (the text's "`x + tv ∈ U` for `|t|` small"). -/
lemma eventually_add_smul_mem_lvlSet (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (hT : C = T 0 ⁻¹' quadrant n W 0) (hU : IsRelOpenInQuadrant E C U) {x : E 1}
    (hx : x ∈ E.lvlSet U 1) {v : E 1} (hv : E.toBase 1 v ∈ minimalSubspaceWith T (E.toBase 1 x)) :
    ∀ᶠ t : ℝ in 𝓝 0, x + t • v ∈ E.lvlSet U 1 := by
  obtain ⟨O, hO, hUO⟩ := hU.relOpen
  have hxU : E.toBase 1 x ∈ U := hx
  rw [hUO] at hxU
  rw [mem_minimalSubspaceWith] at hv
  have hcont : Tendsto (fun t : ℝ => E.toBase 1 (x + t • v)) (𝓝 0) (𝓝 (E.toBase 1 x)) := by
    have : Continuous fun t : ℝ => E.toBase 1 (x + t • v) := by fun_prop
    simpa using this.tendsto 0
  have h1 : ∀ᶠ t : ℝ in 𝓝 0, E.toBase 1 (x + t • v) ∈ O := hcont.eventually (hO.mem_nhds hxU.1)
  have h2 : ∀ i : Fin n, ∀ᶠ t : ℝ in 𝓝 0, 0 ≤ (T 0 (E.toBase 1 (x + t • v))).1 i := by
    intro i
    have heq : ∀ t : ℝ, (T 0 (E.toBase 1 (x + t • v))).1 i =
        (T 0 (E.toBase 1 x)).1 i + t * (T 0 (E.toBase 1 v)).1 i := fun t => by
      simp only [map_add, map_smul, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
    have hxC : T 0 (E.toBase 1 x) ∈ quadrant n W 0 := by
      have := hxU.2; rwa [hT] at this
    by_cases hi : (T 0 (E.toBase 1 x)).1 i = 0
    · exact Eventually.of_forall fun t => by rw [heq, hi, hv i hi, mul_zero, add_zero]
    · have hpos : 0 < (T 0 (E.toBase 1 x)).1 i := lt_of_le_of_ne (hxC i) (Ne.symm hi)
      have hc : Tendsto (fun t : ℝ => (T 0 (E.toBase 1 x)).1 i + t * (T 0 (E.toBase 1 v)).1 i)
          (𝓝 0) (𝓝 ((T 0 (E.toBase 1 x)).1 i)) := by
        have := (by fun_prop : Continuous fun t : ℝ =>
          (T 0 (E.toBase 1 x)).1 i + t * (T 0 (E.toBase 1 v)).1 i).tendsto (0 : ℝ)
        simpa using this
      exact (hc.eventually (lt_mem_nhds hpos)).mono fun t ht => by rw [heq]; exact le_of_lt ht
  filter_upwards [h1, eventually_all.2 h2] with t ht1 ht2
  change E.toBase 1 (x + t • v) ∈ U
  rw [hUO]
  exact ⟨ht1, by rw [hT]; exact fun i => ht2 i⟩

/-- **The sign argument** (Lemma 2.29, Theorem 2.31, Proposition 2.35): if `f` is sc¹ on `U ⊆ C`
with values in `C'`, `x ∈ U₁` and `v ∈ E₁ ∩ E_x`, then `Df(x)v ∈ E'_{f(x)}`.  Proof: the
function `t ↦ (T'(f(x + tv)))_j` is nonnegative near `0` and vanishes at `0`, so its derivative
`(T' Df(x) v)_j` at `0` is zero, for each `j` with `(T'(f(x)))_j = 0`. -/
theorem IsSc1With.deriv_mem_minimalSubspace_of_lvl1
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (hT : C = T 0 ⁻¹' quadrant n W 0)
    (T' : ScIso E' ((ScBanach.const (Fin n' → ℝ)).prod W')) (hT' : C' = T' 0 ⁻¹' quadrant n' W' 0)
    (hU : IsRelOpenInQuadrant E C U) (hf : IsSc1With U f D) (hfC : MapsTo f U C') {x : E 1}
    (hx : x ∈ E.lvlSet U 1) {v : E 1} (hv : E.toBase 1 v ∈ minimalSubspaceWith T (E.toBase 1 x)) :
    D x (E.toBase 1 v) ∈ minimalSubspaceWith T' (f (E.toBase 1 x)) := by
  rw [mem_minimalSubspaceWith]
  intro j hj
  -- the path `γ t = x + t v` and the set where it stays in `U₁`
  set γ : ℝ → E 1 := fun t => x + t • v with hγ
  have hev := eventually_add_smul_mem_lvlSet T hT hU hx hv
  set s : Set ℝ := {t | γ t ∈ E.lvlSet U 1} with hs
  have hs0 : s ∈ 𝓝 (0 : ℝ) := hev
  -- the real function `g t = (T'(f(γ t)))_j`
  let L : E' 0 →L[ℝ] ℝ := (ContinuousLinearMap.proj j).comp
    ((ContinuousLinearMap.fst ℝ (Fin n' → ℝ) (W' 0)).comp (T' 0 : E' 0 →L[ℝ] _))
  set g : ℝ → ℝ := fun t => L (f (E.toBase 1 (γ t))) with hg
  have hγ' : HasDerivAt γ v 0 := by
    simpa [hγ] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hγ0 : γ 0 = x := by simp [hγ]
  have hder : HasDerivAt g (L (D x (E.toBase 1 v))) 0 := by
    have h1 : HasDerivWithinAt ((f ∘ E.toBase 1) ∘ γ) (((D x).comp (E.toBase 1)) v) s 0 := by
      have hfx : HasFDerivWithinAt (f ∘ E.toBase 1) ((D x).comp (E.toBase 1)) (E.lvlSet U 1)
          (γ 0) := by
        rw [hγ0]; exact hf.hasFDerivWithinAt x hx
      exact HasFDerivWithinAt.comp_hasDerivWithinAt (l := f ∘ E.toBase 1) (f := γ)
        (t := E.lvlSet U 1) (s := s) (0 : ℝ) hfx hγ'.hasDerivWithinAt fun t ht => ht
    have h2 : HasDerivAt ((f ∘ E.toBase 1) ∘ γ) (((D x).comp (E.toBase 1)) v) 0 :=
      h1.hasDerivAt hs0
    exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
  have hmin : IsLocalMin g 0 := by
    filter_upwards [hev] with t ht
    have hC' : f (E.toBase 1 (γ t)) ∈ C' := hfC ht
    rw [hT'] at hC'
    have h0 : g 0 = 0 := by
      simp only [hg, hγ0]
      exact hj
    rw [h0]
    exact hC' j
  have := hmin.hasDerivAt_eq_zero hder
  exact this

end Sign

/-! ### Density of `E₁ ∩ ker L` in `ker L` for `L` of finite rank -/

/-- For a continuous linear `L : E₀ → V` into a finite-dimensional space, the level-`1` points of
`ker L` are dense in `ker L`.  (The text's "the closure of `(T_x^R O)_∞` is `T_x^R O`".) -/
theorem ScBanach.subset_closure_ker_inter_range_toBase (E : ScBanach) {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (L : E 0 →L[ℝ] V) :
    (LinearMap.ker (L : E 0 →ₗ[ℝ] V) : Set (E 0)) ⊆
      closure ((LinearMap.ker (L : E 0 →ₗ[ℝ] V) : Set (E 0)) ∩ range (E.toBase 1)) := by
  intro v hv
  set S : Submodule ℝ (E 0) := LinearMap.range (E.toBase 1 : E 1 →ₗ[ℝ] E 0) with hS
  have hSdense : Dense (S : Set (E 0)) := by
    have : (S : Set (E 0)) = range (E.incl 0) := by
      ext z; simp [hS, LinearMap.mem_range]; rfl
    rw [this]; exact E.denseRange_incl 0
  -- a right inverse of `L|S : S → L(S)` with values in `S`
  set L₁ : S →ₗ[ℝ] V := (L : E 0 →ₗ[ℝ] V).domRestrict S with hL₁
  obtain ⟨g, hg⟩ := L₁.rangeRestrict.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 L₁.surjective_rangeRestrict)
  have hgcont : Continuous g := LinearMap.continuous_of_finiteDimensional g
  have hLg : ∀ a : LinearMap.range L₁, L (g a : E 0) = a := fun a => by
    have := LinearMap.congr_fun hg a
    exact congrArg Subtype.val this
  -- approximate `v` by `v_k ∈ S`
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 (hSdense v)
  have hLu : ∀ k, L (u k) ∈ LinearMap.range L₁ := fun k => ⟨⟨u k, hu k⟩, rfl⟩
  set a : ℕ → LinearMap.range L₁ := fun k => ⟨L (u k), hLu k⟩ with ha
  have hLv : L v = 0 := LinearMap.mem_ker.1 hv
  have ha0 : Tendsto a atTop (𝓝 ⟨0, zero_mem _⟩) := by
    rw [tendsto_subtype_rng]
    change Tendsto (fun k => L (u k)) atTop (𝓝 (0 : V))
    rw [← hLv]
    exact (L.continuous.tendsto v).comp hlim
  have hga : Tendsto (fun k => (g (a k) : E 0)) atTop (𝓝 0) := by
    have := (continuous_subtype_val.comp hgcont).tendsto (⟨0, zero_mem _⟩ : LinearMap.range L₁)
    have h0 : ((g ⟨0, zero_mem _⟩ : S) : E 0) = 0 := by
      have : (⟨0, zero_mem _⟩ : LinearMap.range L₁) = 0 := rfl
      rw [this, map_zero]; rfl
    rw [Function.comp_apply, h0] at this
    exact this.comp ha0
  refine mem_closure_of_tendsto (b := atTop) (f := fun k => u k - (g (a k) : E 0)) ?_ ?_
  · simpa using hlim.sub hga
  · refine Eventually.of_forall fun k => ⟨?_, ?_⟩
    · rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub]
      change L (u k) - L (g (a k) : E 0) = 0
      rw [hLg]
      simp [ha]
    · exact S.sub_mem (hu k) (g (a k)).2

/-- `Df(x)` maps all of `E_x` into `E'_{f(x)}` (sign argument plus density). -/
theorem IsSc1With.mapsTo_minimalSubspace {n n' : ℕ} {W W' : ScBanach} {C : Set (E 0)}
    {C' : Set (E' 0)} {U : Set (E 0)} {f : E 0 → E' 0} {D : E 1 → E 0 →L[ℝ] E' 0}
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (hT : C = T 0 ⁻¹' quadrant n W 0)
    (T' : ScIso E' ((ScBanach.const (Fin n' → ℝ)).prod W')) (hT' : C' = T' 0 ⁻¹' quadrant n' W' 0)
    (hU : IsRelOpenInQuadrant E C U) (hf : IsSc1With U f D) (hfC : MapsTo f U C') {x : E 1}
    (hx : x ∈ E.lvlSet U 1) :
    MapsTo (D x) (minimalSubspaceWith T (E.toBase 1 x)) (minimalSubspaceWith T' (f (E.toBase 1 x))) := by
  intro v hv
  have hclosed : IsClosed ((D x) ⁻¹' (minimalSubspaceWith T' (f (E.toBase 1 x)) : Set (E' 0))) :=
    (isClosed_minimalSubspaceWith T' _).preimage (D x).continuous
  have hsub : (minimalSubspaceWith T (E.toBase 1 x) : Set (E 0)) ∩ range (E.toBase 1) ⊆
      (D x) ⁻¹' (minimalSubspaceWith T' (f (E.toBase 1 x)) : Set (E' 0)) := by
    rintro _ ⟨hw, w, rfl⟩
    exact hf.deriv_mem_minimalSubspace_of_lvl1 T hT T' hT' hU hfC hx hw
  have := E.subset_closure_ker_inter_range_toBase (coordMapL T (E.toBase 1 x)) hv
  exact hclosed.closure_subset_iff.2 hsub this

/-! ### Chain rule at a point -/

section ChainPoint

variable {C : Set (E 0)} {C' : Set (E' 0)} {U : Set (E 0)} {U' : Set (E' 0)} {f : E 0 → E' 0}
  {g : E' 0 → E 0}

/-- The derivative of a composition at a level-`1` point. -/
lemma scDeriv_comp_apply (hU : IsRelOpenInQuadrant E C U) (hU' : IsRelOpenInQuadrant E' C' U')
    (hf : IsSc1 U f) (hg : IsSc1 U' g) (hfU : MapsTo f U U') {x : E 1} (hx : x ∈ E.lvlSet U 1)
    (h : E 0) : scDeriv U' g (levelMap f 1 x) (scDeriv U f x h) = scDeriv U (g ∘ f) x h := by
  obtain ⟨_, hchain⟩ := theorem_1_21 hU hU' hf hg hfU
  have := hchain (show ((x, h) : E.tangent 0) ∈ E.tangentSet U from hx)
  exact (congrArg Prod.snd this).symm

/-- `levelMap (g ∘ f) 1 x = x` when `g ∘ f = id` on `U`. -/
lemma levelMap_comp_eq_self (hf : IsSc0 E E' U f) {x : E 1} (hx : x ∈ E.lvlSet U 1)
    (hgf : ∀ y ∈ U, g (f y) = y) : levelMap g 1 (levelMap f 1 x) = x := by
  apply levelMap_eq_of_toBase_eq
  rw [hf.toBase_levelMap hx]
  exact (hgf _ hx).symm

/-- `Dg(f(x)) ∘ Df(x) = id` when `g ∘ f = id` on `U`. -/
lemma scDeriv_comp_eq_self (hU : IsRelOpenInQuadrant E C U) (hU' : IsRelOpenInQuadrant E' C' U')
    (hf : IsSc1 U f) (hg : IsSc1 U' g) (hfU : MapsTo f U U') (hgf : ∀ y ∈ U, g (f y) = y)
    {x : E 1} (hx : x ∈ E.lvlSet U 1) (h : E 0) :
    scDeriv U' g (levelMap f 1 x) (scDeriv U f x h) = h := by
  rw [scDeriv_comp_apply hU hU' hf hg hfU hx]
  have h1 : EqOn (tangentMap U (g ∘ f)) (tangentMap U id) (E.tangentSet U) :=
    (IsSc1.tangentMap_congr hU.isScDomain (isSc1With_id U).isSc1 fun y hy => (hgf y hy).symm).symm
  have h2 := (h1.trans (tangentMap_id_eqOn hU.isScDomain))
    (show ((x, h) : E.tangent 0) ∈ E.tangentSet U from hx)
  exact congrArg Prod.snd h2

end ChainPoint

/-! ### The core of Theorem 2.31: the index does not increase along sc-diffeomorphism germs -/

section Core

variable {n n' : ℕ} {W W' : ScBanach} {C : Set (E 0)} {C' : Set (E' 0)}

/-- The core of Theorem 2.31 and Corollary 2.32.  Let `U₀` be relatively open in the partial
quadrant `C ⊆ E` (presented by `T`), `r' : U' → U'` an sc-smooth retraction in `C' ⊆ E'` (presented
by `T'`) onto `O'`, and `F : U₀ → O'`, `G : O' → U₀` sc-smooth and inverse to each other
(`G ∘ r'` sc-smooth on `U'`).  Then for `x ∈ U₀` on level `1`, `d_C(x) ≤ d_{C'}(F(x))`.

*Proof.* With `y = F(x)`, `D = DF(x)`, `D' = D(G ∘ r')(y)` one has `D' ∘ D = id`,
`D ∘ D' = Dr'(y)`, `D(E_x) ⊆ E'_y` and `D'(E'_y) ⊆ E_x` (sign argument), so `D` induces
`E/E_x ≅ T_yO'/(T_yO' ∩ E'_y)`, and the latter embeds in `E'/E'_y`. -/
theorem degIndexWith_le_of_germ (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (hT : C = T 0 ⁻¹' quadrant n W 0) (T' : ScIso E' ((ScBanach.const (Fin n' → ℝ)).prod W'))
    (hT' : C' = T' 0 ⁻¹' quadrant n' W' 0) {U₀ : Set (E 0)} (hU₀ : IsRelOpenInQuadrant E C U₀)
    (R' : ScRetraction E' C') {F : E 0 → E' 0} {G : E' 0 → E 0} (hF : IsSc1 U₀ F)
    (hG : IsSc1 R'.U (G ∘ R')) (hFO : MapsTo F U₀ R'.retract) (hGU : MapsTo (G ∘ R') R'.U U₀)
    (hGF : ∀ z ∈ U₀, G (F z) = z) (hFG : ∀ z ∈ R'.retract, F (G z) = z) {x : E 1}
    (hx : x ∈ E.lvlSet U₀ 1) : degIndexWith T (E.toBase 1 x) ≤ degIndexWith T' (F (E.toBase 1 x)) := by
  classical
  -- notation
  set ι := E.toBase 1 with hι
  set y : E' 1 := levelMap F 1 x with hy
  have hFU' : MapsTo F U₀ R'.U := fun z hz => R'.retract_subset (hFO hz)
  have hyO : y ∈ E'.lvlSet R'.retract 1 := hF.isSc0.levelMap_mapsTo hFO 1 hx
  have hyU' : y ∈ E'.lvlSet R'.U 1 := R'.lvlSet_retract_subset 1 hyO
  have hιy : E'.toBase 1 y = F (ι x) := hF.isSc0.toBase_levelMap hx
  set D : E 0 →L[ℝ] E' 0 := scDeriv U₀ F x with hD
  set D' : E' 0 →L[ℝ] E 0 := scDeriv R'.U (G ∘ R') y with hD'
  set P : E' 0 →L[ℝ] E' 0 := scDeriv R'.U R' y with hP
  -- `G ∘ r' ∘ F = id` on `U₀`
  have hGrF : ∀ z ∈ U₀, (G ∘ R') (F z) = z := fun z hz => by
    simp only [Function.comp_apply, R'.apply_eq_self_of_mem_retract (hFO hz), hGF z hz]
  -- `D' ∘ D = id`
  have hD'D : ∀ h, D' (D h) = h := fun h =>
    scDeriv_comp_eq_self hU₀ R'.relOpen hF hG hFU' hGrF hx h
  -- `D ∘ D' = P = Dr'(y)`
  have hlev : levelMap (G ∘ R') 1 y = x := levelMap_comp_eq_self hF.isSc0 hx hGrF
  have hDD' : ∀ w, D (D' w) = P w := fun w => by
    have h1 := scDeriv_comp_apply R'.relOpen hU₀ hG hF hGU hyU' w
    rw [hlev] at h1
    change D (D' w) = scDeriv R'.U R' y w
    rw [h1]
    have h2 : EqOn (tangentMap R'.U (F ∘ (G ∘ R'))) (tangentMap R'.U R') (E'.tangentSet R'.U) :=
      (R'.isSc1.tangentMap_congr R'.isScDomain fun z hz => by
        simp only [Function.comp_apply, hFG _ (R'.apply_mem_retract hz)]).symm
    exact congrArg Prod.snd (h2 (show ((y, w) : E'.tangent 0) ∈ E'.tangentSet R'.U from hyU'))
  -- the sign argument for `F` and for `G ∘ r'`
  have hRO' : R'.retract ⊆ C' := by
    obtain ⟨O, _, hO⟩ := R'.relOpen.relOpen
    exact R'.retract_subset.trans (hO ▸ inter_subset_right)
  have hU₀C : U₀ ⊆ C := by
    obtain ⟨O, _, hO⟩ := hU₀.relOpen
    exact hO ▸ inter_subset_right
  have hDmaps : MapsTo D (minimalSubspaceWith T (ι x)) (minimalSubspaceWith T' (F (ι x))) :=
    hF.isSc1With_scDeriv.mapsTo_minimalSubspace T hT T' hT' hU₀ (hFO.mono_right hRO') hx
  have hD'maps : MapsTo D' (minimalSubspaceWith T' (F (ι x))) (minimalSubspaceWith T (ι x)) := by
    have := hG.isSc1With_scDeriv.mapsTo_minimalSubspace T' hT' T hT R'.relOpen
      (hGU.mono_right hU₀C) hyU'
    rw [hιy] at this
    have hGy : (G ∘ R') (F (ι x)) = ι x := hGrF _ hx
    rwa [hGy] at this
  -- the subspaces
  set Ex : Submodule ℝ (E 0) := minimalSubspaceWith T (ι x) with hEx
  set Ey : Submodule ℝ (E' 0) := minimalSubspaceWith T' (F (ι x)) with hEy
  set Ty : Submodule ℝ (E' 0) := LinearMap.range (P : E' 0 →ₗ[ℝ] E' 0) with hTy
  set TR : Submodule ℝ (E' 0) := Ty ⊓ Ey with hTR
  -- `D` lands in `T_yO'`
  have hDTy : ∀ h, D h ∈ Ty := fun h => ⟨D h, by change P (D h) = D h; rw [← hDD', hD'D]⟩
  -- the map `Φ : E → T_yO' / T^R`
  let Dt : E 0 →ₗ[ℝ] Ty := (D : E 0 →ₗ[ℝ] E' 0).codRestrict Ty hDTy
  let Φ : E 0 →ₗ[ℝ] Ty ⧸ TR.comap Ty.subtype := (TR.comap Ty.subtype).mkQ.comp Dt
  have hΦsurj : Surjective Φ := by
    intro q
    obtain ⟨⟨w, hw⟩, rfl⟩ := (TR.comap Ty.subtype).mkQ_surjective q
    refine ⟨D' w, ?_⟩
    simp only [Φ, LinearMap.comp_apply, Submodule.mkQ_apply]
    congr 1
    apply Subtype.ext
    change D (D' w) = w
    rw [hDD']
    obtain ⟨u, rfl⟩ := hw
    change P (P u) = P u
    exact congrArg (fun L : E' 0 →L[ℝ] E' 0 => L u) (R'.scDeriv_comp_self hyO)
  have hΦker : LinearMap.ker Φ = Ex := by
    ext h
    simp only [Φ, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
    change D h ∈ TR ↔ h ∈ Ex
    constructor
    · intro hh
      have := hD'maps hh.2
      rwa [hD'D] at this
    · intro hh
      exact ⟨hDTy h, hDmaps hh⟩
  have hiso : (E 0 ⧸ Ex) ≃ₗ[ℝ] (Ty ⧸ TR.comap Ty.subtype) :=
    hΦker ▸ Φ.quotKerEquivOfSurjective hΦsurj
  -- `T_yO' / T^R` embeds in `E' / E'_y`
  let Ψ : Ty →ₗ[ℝ] E' 0 ⧸ Ey := Ey.mkQ.comp Ty.subtype
  have hΨker : LinearMap.ker Ψ = TR.comap Ty.subtype := by
    ext ⟨w, hw⟩
    simp only [Ψ, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    exact ⟨fun h => ⟨hw, h⟩, fun h => h.2⟩
  have hemb : (Ty ⧸ TR.comap Ty.subtype) ≃ₗ[ℝ] LinearMap.range Ψ :=
    hΨker ▸ Ψ.quotKerEquivRange
  -- conclude with dimensions
  rw [← finrank_quotient_minimalSubspaceWith T, ← finrank_quotient_minimalSubspaceWith T']
  calc finrank ℝ (E 0 ⧸ Ex) = finrank ℝ (Ty ⧸ TR.comap Ty.subtype) := hiso.finrank_eq
    _ = finrank ℝ (LinearMap.range Ψ) := hemb.finrank_eq
    _ ≤ finrank ℝ (E' 0 ⧸ Ey) := Submodule.finrank_le _

end Core

/-! ### Theorem 1.25 -/

section Theorem125

variable {C : Set (E 0)} {C' : Set (E' 0)} {U : Set (E 0)} {U' : Set (E' 0)} {f : E 0 → E' 0}
  {g : E' 0 → E 0}

/-- **Theorem 1.25** at points on level `1`: a germ of local sc-diffeomorphisms (here: `f : U → U'`
and `g : U' → U` sc¹ and inverse to each other) preserves the degeneracy index at `x ∈ U₁`. -/
theorem theorem_1_25_lvl1 (hU : IsRelOpenInQuadrant E C U) (hU' : IsRelOpenInQuadrant E' C' U')
    (hf : IsSc1 U f) (hg : IsSc1 U' g) (hfU : MapsTo f U U') (hgU : MapsTo g U' U)
    (hgf : ∀ x ∈ U, g (f x) = x) (hfg : ∀ y ∈ U', f (g y) = y) {x : E 1} (hx : x ∈ E.lvlSet U 1) :
    degIndex E C (E.toBase 1 x) = degIndex E' C' (f (E.toBase 1 x)) := by
  obtain ⟨n, W, T, hT⟩ := hU.isPartialQuadrant
  obtain ⟨n', W', T', hT'⟩ := hU'.isPartialQuadrant
  have hxC : E.toBase 1 x ∈ C := by
    obtain ⟨O, _, hO⟩ := hU.relOpen
    exact (hO ▸ hx).2
  have hfxC' : f (E.toBase 1 x) ∈ C' := by
    obtain ⟨O, _, hO⟩ := hU'.relOpen
    exact (hO ▸ hfU hx).2
  rw [degIndex_eq T hT hxC, degIndex_eq T' hT' hfxC']
  -- the identity retractions on `U` and `U'`
  set R := ScRetraction.id hU with hR
  set R' := ScRetraction.id hU' with hR'
  have hRret : R.retract = U := image_id U
  have hR'ret : R'.retract = U' := image_id U'
  have hRU : R.U = U := rfl
  have hR'U : R'.U = U' := rfl
  apply le_antisymm
  · refine degIndexWith_le_of_germ T hT T' hT' hU R' (F := f) (G := g) hf ?_ ?_ ?_ hgf ?_ hx
    · exact hg
    · rw [hR'ret]; exact hfU
    · exact hgU
    · rw [hR'ret]; exact hfg
  · -- the symmetric germ `g : (U', f x) → (U, x)`, at `f₁(x) ∈ U'₁`
    have hy : levelMap f 1 x ∈ E'.lvlSet U' 1 := hf.isSc0.levelMap_mapsTo hfU 1 hx
    have hιy : E'.toBase 1 (levelMap f 1 x) = f (E.toBase 1 x) := hf.isSc0.toBase_levelMap hx
    have := degIndexWith_le_of_germ T' hT' T hT hU' R (F := g) (G := f) hg
      (by exact hf) (by rw [hRret]; exact hgU) hfU hfg (by rw [hRret]; exact hgf) hy
    rwa [hιy, hgf _ hx] at this

/-- **Theorem 1.25** (boundary recognition): given relatively open subsets `U ⊆ C ⊆ E` and
`U' ⊆ C' ⊆ E'` of partial quadrants and a germ `f : (U, x) → (U', f(x))` of local
sc-diffeomorphisms (an sc¹ map `f : U → U'` with sc¹ inverse `g : U' → U`), `d_C(x) = d_{C'}(f(x))`
for every `x ∈ U`. -/
theorem theorem_1_25 (hU : IsRelOpenInQuadrant E C U) (hU' : IsRelOpenInQuadrant E' C' U')
    (hf : IsSc1 U f) (hg : IsSc1 U' g) (hfU : MapsTo f U U') (hgU : MapsTo g U' U)
    (hgf : ∀ x ∈ U, g (f x) = x) (hfg : ∀ y ∈ U', f (g y) = y) {x : E 0} (hx : x ∈ U) :
    degIndex E C x = degIndex E' C' (f x) := by
  -- the one-sided statement, applied to `f` and to `g`
  have key : ∀ {E E' : ScBanach} {C : Set (E 0)} {C' : Set (E' 0)} {U : Set (E 0)} {U' : Set (E' 0)}
      {f : E 0 → E' 0} {g : E' 0 → E 0}, IsRelOpenInQuadrant E C U → IsRelOpenInQuadrant E' C' U' →
      IsSc1 U f → IsSc1 U' g → MapsTo f U U' → MapsTo g U' U → (∀ x ∈ U, g (f x) = x) →
      (∀ y ∈ U', f (g y) = y) → ∀ {x : E 0}, x ∈ U → degIndex E C x ≤ degIndex E' C' (f x) := by
    intro E E' C C' U U' f g hU hU' hf hg hfU hgU hgf hfg x hx
    obtain ⟨n, W, T, hT⟩ := hU.isPartialQuadrant
    obtain ⟨n', W', T', hT'⟩ := hU'.isPartialQuadrant
    obtain ⟨O, hO, hUO⟩ := hU.relOpen
    have hxC : x ∈ C := (hUO ▸ hx).2
    have hfxC' : f x ∈ C' := by
      obtain ⟨O', _, hO'⟩ := hU'.relOpen
      exact (hO' ▸ hfU hx).2
    rw [degIndex_eq T hT hxC, degIndex_eq T' hT' hfxC']
    -- approximate `x` by level-`1` points with the same index
    obtain ⟨ι, l, σ, hl, hσ, hσ1, hσdeg, hσC⟩ := exists_tendsto_lvl1_degIndexWith T x
    have hxC' : T 0 x ∈ quadrant n W 0 := by rwa [hT] at hxC
    have hσU : ∀ᶠ i in l, σ i ∈ U := by
      filter_upwards [hσ.eventually (hO.mem_nhds (hUO ▸ hx).1)] with i hi
      rw [hUO]
      exact ⟨hi, by rw [hT, mem_preimage, hσC]; exact hxC'⟩
    have hfσ : Tendsto (fun i => f (σ i)) l (𝓝 (f x)) := by
      have hcont : ContinuousWithinAt f U x := hf.isSc0.continuousOn_base x hx
      exact hcont.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hσ, hσU⟩)
    have hle : ∀ᶠ i in l, degIndexWith T' (f (σ i)) ≤ degIndexWith T' (f x) :=
      hfσ.eventually (eventually_degIndexWith_le T' (f x))
    have hev : ∀ᶠ i in l, degIndexWith T x ≤ degIndexWith T' (f x) := by
      filter_upwards [hσ1, hσU, hle] with i hi1 hiU hile
      obtain ⟨z, hz⟩ := hi1
      have hzU : z ∈ E.lvlSet U 1 := by rw [ScBanach.mem_lvlSet, hz]; exact hiU
      have h := theorem_1_25_lvl1 hU hU' hf hg hfU hgU hgf hfg hzU
      rw [hz, degIndex_eq T hT (hUO ▸ hiU).2, degIndex_eq T' hT' (by
        obtain ⟨O', _, hO'⟩ := hU'.relOpen
        exact (hO' ▸ hfU hiU).2)] at h
      rw [← hσdeg i, h]
      exact hile
    have := hl
    exact hev.exists.elim fun _ h => h
  refine le_antisymm (key hU hU' hf hg hfU hgU hgf hfg hx) ?_
  have := key hU' hU hg hf hgU hfU hfg hgf (hfU hx)
  rwa [hgf x hx] at this

end Theorem125


/-! ### The degeneracy index of an M-polyfold (Definition 2.22) -/

lemma LocalModel.O_subset_C (M : LocalModel) : M.O ⊆ M.C := by
  obtain ⟨R, hR⟩ := M.isScRetract
  obtain ⟨O, _, hO⟩ := R.relOpen.relOpen
  rw [← hR]
  exact R.retract_subset.trans (hO ▸ inter_subset_right)

lemma MChart.apply_mem_C {X : Type*} [TopologicalSpace X] (φ : MChart X) {x : X}
    (hx : x ∈ φ.source) : φ x ∈ φ.model.C :=
  φ.model.O_subset_C (φ.mapsTo_model x hx)

lemma LocalModel.isPartialQuadrant (M : LocalModel) : IsPartialQuadrant M.E M.C := by
  obtain ⟨R, _⟩ := M.isScRetract
  exact R.relOpen.isPartialQuadrant

namespace MPolyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

/-- `d(x, φ) = d_C(φ(x))`, the index of `x` seen in the chart `φ`. -/
def chartDegIndex (φ : MChart X) (x : X) : ℕ := Polyfold.degIndex φ.model.E φ.model.C (φ x)

/-- **Definition 2.22**: the **degeneracy index** `d_X(x)`, the minimum of `d(x, φ)` over the charts
`φ` of the structure around `x`. -/
def degIndex (x : X) : ℕ :=
  sInf {d | ∃ φ : MChart X, P.IsChart φ ∧ x ∈ φ.source ∧ chartDegIndex φ x = d}

lemma degIndex_le {φ : MChart X} (hφ : P.IsChart φ) {x : X} (hx : x ∈ φ.source) :
    P.degIndex x ≤ chartDegIndex φ x :=
  Nat.sInf_le ⟨φ, hφ, hx, rfl⟩

/-- The minimum in Definition 2.22 is attained. -/
lemma exists_isChart_degIndex_eq (x : X) :
    ∃ φ : MChart X, P.IsChart φ ∧ x ∈ φ.source ∧ P.degIndex x = chartDegIndex φ x := by
  have hne : {d | ∃ φ : MChart X, P.IsChart φ ∧ x ∈ φ.source ∧ chartDegIndex φ x = d}.Nonempty := by
    obtain ⟨φ, hφ, hx⟩ := P.exists_isChart_mem_source x
    exact ⟨_, φ, hφ, hx, rfl⟩
  obtain ⟨φ, hφ, hx, h⟩ := Nat.sInf_mem hne
  exact ⟨φ, hφ, hx, h.symm⟩

omit [T2Space X] [ParacompactSpace X] in
/-- Upper semicontinuity of `d(·, φ)` on the source of a chart. -/
lemma eventually_chartDegIndex_le (φ : MChart X) {x : X} (hx : x ∈ φ.source) :
    ∀ᶠ y in 𝓝 x, chartDegIndex φ y ≤ chartDegIndex φ x := by
  obtain ⟨n, W, T, hT⟩ := φ.model.isPartialQuadrant
  have hcont : ContinuousAt φ x := φ.continuousOn_toFun.continuousAt (φ.isOpen_source.mem_nhds hx)
  filter_upwards [φ.isOpen_source.mem_nhds hx, hcont.eventually (eventually_degIndexWith_le T (φ x))]
    with y hy hle
  rw [chartDegIndex, chartDegIndex, degIndex_eq T hT (φ.apply_mem_C hy),
    degIndex_eq T hT (φ.apply_mem_C hx)]
  exact hle

/-- **Lemma 2.23**: every `x ∈ X` has a neighbourhood on which `d_X(y) ≤ d_X(x)`. -/
theorem _root_.Polyfold.lemma_2_23 (x : X) : ∀ᶠ y in 𝓝 x, P.degIndex y ≤ P.degIndex x := by
  obtain ⟨φ, hφ, hx, hd⟩ := P.exists_isChart_degIndex_eq x
  filter_upwards [φ.isOpen_source.mem_nhds hx, eventually_chartDegIndex_le φ hx] with y hy hle
  rw [hd]
  exact (P.degIndex_le hφ hy).trans hle

/-- **Definition 2.25**: the **boundary** `∂X = {x | d_X(x) ≥ 1}`. -/
def boundary : Set X := {x | 1 ≤ P.degIndex x}

/-- **Definition 2.25**: an M-polyfold **without boundary** has `d_X ≡ 0`. -/
def IsWithoutBoundary : Prop := ∀ x, P.degIndex x = 0

lemma isWithoutBoundary_iff : P.IsWithoutBoundary ↔ P.boundary = ∅ := by
  constructor
  · intro h
    exact eq_empty_iff_forall_notMem.2 fun x hx => by
      have h1 : 1 ≤ P.degIndex x := hx
      rw [h x] at h1
      exact absurd h1 (by norm_num)
  · intro h x
    by_contra hx
    exact eq_empty_iff_forall_notMem.1 h x (Nat.one_le_iff_ne_zero.2 hx)

/-! ### Proposition 2.24: invariance under germs of sc-diffeomorphisms -/

variable {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (Q : MPolyfold Y)

/-- `f : U → V` is an **sc-diffeomorphism between open subsets** of M-polyfolds (a germ of
sc-diffeomorphisms around each point of `U`): `f` is sc-smooth on `U` and has an sc-smooth
inverse `g : V → U`. -/
structure IsScDiffeoOn (f : X → Y) (g : Y → X) (U : Set X) (V : Set Y) : Prop where
  isScSmoothOn : P.IsScSmoothOn Q f U
  isScSmoothOn_inv : Q.IsScSmoothOn P g V
  mapsTo : MapsTo f U V
  mapsTo_inv : MapsTo g V U
  left_inv : ∀ x ∈ U, g (f x) = x
  right_inv : ∀ y ∈ V, f (g y) = y

variable {P Q}

lemma IsScDiffeoOn.symm {f : X → Y} {g : Y → X} {U : Set X} {V : Set Y}
    (h : P.IsScDiffeoOn Q f g U V) : Q.IsScDiffeoOn P g f V U :=
  ⟨h.isScSmoothOn_inv, h.isScSmoothOn, h.mapsTo_inv, h.mapsTo, h.right_inv, h.left_inv⟩

section Transport

variable {f : X → Y} {g : Y → X} {U : Set X} {V : Set Y}

/-- The domain `U ∩ f⁻¹(dom ψ)` of the transported chart. -/
private lemma isOpen_transport_source (h : P.IsScDiffeoOn Q f g U V) (ψ : MChart Y) :
    IsOpen (U ∩ f ⁻¹' ψ.source) :=
  h.isScSmoothOn.continuousOn.isOpen_inter_preimage h.isScSmoothOn.isOpen ψ.isOpen_source

private lemma isOpen_transport_target (h : P.IsScDiffeoOn Q f g U V) (ψ : MChart Y) :
    IsOpen (V ∩ ψ.source) :=
  h.isScSmoothOn_inv.isOpen.inter ψ.isOpen_source

private lemma image_transport_source (h : P.IsScDiffeoOn Q f g U V) (ψ : MChart Y) :
    f '' (U ∩ f ⁻¹' ψ.source) = V ∩ ψ.source := by
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hfx⟩, rfl⟩
    exact ⟨h.mapsTo hx, hfx⟩
  · rintro ⟨hy, hyψ⟩
    exact ⟨g y, ⟨h.mapsTo_inv hy, by rw [mem_preimage, h.right_inv y hy]; exact hyψ⟩,
      h.right_inv y hy⟩

/-- The chart `ψ ∘ f` of `X` obtained from a chart `ψ` of `Y` through the sc-diffeomorphism `f`
(the proof of Proposition 2.24). -/
def transportChart (h : P.IsScDiffeoOn Q f g U V) (ψ : MChart Y) : MChart X where
  model := ⟨ψ.model.E, ψ.model.C, ψ '' (V ∩ ψ.source),
    ψ.isScRetract_image inter_subset_right (isOpen_transport_target h ψ)⟩
  toPartialEquiv :=
    { toFun := ψ ∘ f
      invFun := g ∘ ψ.symm
      source := U ∩ f ⁻¹' ψ.source
      target := ψ '' (V ∩ ψ.source)
      map_source' := fun x hx => ⟨f x, ⟨h.mapsTo hx.1, hx.2⟩, rfl⟩
      map_target' := by
        rintro _ ⟨y, hy, rfl⟩
        simp only [Function.comp_apply, ψ.symm_apply_apply hy.2]
        exact ⟨h.mapsTo_inv hy.1, by rw [mem_preimage, h.right_inv y hy.1]; exact hy.2⟩
      left_inv' := fun x hx => by
        simp only [Function.comp_apply, ψ.symm_apply_apply hx.2, h.left_inv x hx.1]
      right_inv' := by
        rintro _ ⟨y, hy, rfl⟩
        simp only [Function.comp_apply, ψ.symm_apply_apply hy.2, h.right_inv y hy.1] }
  isOpen_source := isOpen_transport_source h ψ
  target_eq := rfl
  continuousOn_toFun :=
    ψ.continuousOn_toFun.comp (h.isScSmoothOn.continuousOn.mono inter_subset_left) fun _ hx => hx.2
  continuousOn_invFun := by
    refine h.isScSmoothOn_inv.continuousOn.comp
      (ψ.continuousOn_invFun.mono (ψ.image_subset_model inter_subset_right)) ?_
    rintro _ ⟨y, hy, rfl⟩
    rw [ψ.symm_apply_apply hy.2]; exact hy.1

lemma transportChart_source (h : P.IsScDiffeoOn Q f g U V) (ψ : MChart Y) :
    (transportChart h ψ).source = U ∩ f ⁻¹' ψ.source := rfl

lemma transportChart_apply (h : P.IsScDiffeoOn Q f g U V) (ψ : MChart Y) (x : X) :
    transportChart h ψ x = ψ (f x) := rfl

lemma transportChart_symm_apply (h : P.IsScDiffeoOn Q f g U V) (ψ : MChart Y)
    (z : ψ.model.E 0) : (transportChart h ψ).symm z = g (ψ.symm z) := rfl

/-- The transported chart is a chart of the structure of `X`. -/
theorem transportChart_isChart (h : P.IsScDiffeoOn Q f g U V) {ψ : MChart Y} (hψ : Q.IsChart ψ) :
    P.IsChart (transportChart h ψ) := by
  intro φ hφ
  have hφ' : P.IsChart φ := P.isChart_of_mem hφ
  set χ := transportChart h ψ with hχ
  -- the open sets
  set s := φ.source ∩ χ.source with hs
  have hso : IsOpen s := φ.isOpen_source.inter χ.isOpen_source
  set V'' := V ∩ ψ.source ∩ g ⁻¹' φ.source with hV''
  have hV''o : IsOpen V'' :=
    (h.isScSmoothOn_inv.continuousOn.mono inter_subset_left).isOpen_inter_preimage
      (isOpen_transport_target h ψ) φ.isOpen_source
  have hfs : f '' s = V'' := by
    ext y
    constructor
    · rintro ⟨x, ⟨hxφ, hxU, hxψ⟩, rfl⟩
      exact ⟨⟨h.mapsTo hxU, hxψ⟩, by rw [mem_preimage, h.left_inv x hxU]; exact hxφ⟩
    · rintro ⟨⟨hyV, hyψ⟩, hyφ⟩
      refine ⟨g y, ⟨hyφ, h.mapsTo_inv hyV, ?_⟩, h.right_inv y hyV⟩
      rw [mem_preimage, h.right_inv y hyV]; exact hyψ
  have hχs : χ.overlap φ = ψ '' V'' := by
    change (ψ ∘ f) '' (χ.source ∩ φ.source) = ψ '' V''
    rw [inter_comm, image_comp, ← hs, hfs]
  constructor
  · -- `φ ∘ χ⁻¹ = φ ∘ g ∘ ψ⁻¹` on `ψ(V'')`
    rw [hχs]
    have := h.isScSmoothOn_inv.smooth ψ φ hψ hφ' V'' hV''o (fun y hy => ⟨hy.1.1, hy.1.2⟩)
      fun y hy => hy.2
    refine this.mono_target ?_
    rintro _ ⟨y, hy, rfl⟩
    change φ (g (ψ.symm (ψ y))) ∈ φ.overlap χ
    rw [ψ.symm_apply_apply hy.1.2]
    refine ⟨g y, ⟨hy.2, h.mapsTo_inv hy.1.1, ?_⟩, rfl⟩
    rw [mem_preimage, h.right_inv y hy.1.1]; exact hy.1.2
  · -- `χ ∘ φ⁻¹ = ψ ∘ f ∘ φ⁻¹` on `φ(s)`
    have := h.isScSmoothOn.smooth φ ψ hφ' hψ s hso (fun x hx => ⟨hx.2.1, hx.1⟩) fun x hx => hx.2.2
    refine this.mono_target ?_
    rintro _ ⟨x, hx, rfl⟩
    change ψ (f (φ.symm (φ x))) ∈ χ.overlap φ
    rw [φ.symm_apply_apply hx.1]
    exact ⟨x, ⟨hx.2, hx.1⟩, rfl⟩

lemma chartDegIndex_transportChart (h : P.IsScDiffeoOn Q f g U V) (ψ : MChart Y) (x : X) :
    chartDegIndex (transportChart h ψ) x = chartDegIndex ψ (f x) := rfl

end Transport

/-- One half of Proposition 2.24: `d_X(x) ≤ d_Y(f(x))` along an sc-diffeomorphism germ. -/
theorem degIndex_le_of_isScDiffeoOn {f : X → Y} {g : Y → X} {U : Set X} {V : Set Y}
    (h : P.IsScDiffeoOn Q f g U V) {x : X} (hx : x ∈ U) : P.degIndex x ≤ Q.degIndex (f x) := by
  obtain ⟨ψ, hψ, hfx, hd⟩ := Q.exists_isChart_degIndex_eq (f x)
  rw [hd, ← chartDegIndex_transportChart h ψ x]
  exact P.degIndex_le (transportChart_isChart h hψ) ⟨hx, hfx⟩

/-- **Proposition 2.24**: a germ of sc-diffeomorphisms `f : (U, x) → (V, f(x))` between M-polyfolds
preserves the degeneracy index: `d_X(x) = d_Y(f(x))`. -/
theorem _root_.Polyfold.proposition_2_24 {f : X → Y} {g : Y → X} {U : Set X} {V : Set Y}
    (h : P.IsScDiffeoOn Q f g U V) {x : X} (hx : x ∈ U) : P.degIndex x = Q.degIndex (f x) := by
  refine le_antisymm (degIndex_le_of_isScDiffeoOn h hx) ?_
  have := degIndex_le_of_isScDiffeoOn h.symm (h.mapsTo hx)
  rwa [h.left_inv x hx] at this

end MPolyfold

/-! ### Corollary 2.32: `d_{X_U} = d_C` -/

section Corollary232

variable {C U : Set (E 0)} (hU : IsRelOpenInQuadrant E C U) (hne : U.Nonempty)

/-- The M-polyfold `X_U` of a nonempty relatively open subset `U` of a partial quadrant, and its
single chart `id`. -/
local notation "XU" => hU.toMPolyfold hne

lemma IsRelOpenInQuadrant.selfChart_isChart :
    (XU).IsChart ((LocalModel.ofRelOpen hU).selfChart hne) :=
  (XU).isChart_of_mem (mem_singleton _)

/-- `d_{X_U}(x) ≤ d_C(x)`: the chart `id`. -/
theorem IsRelOpenInQuadrant.degIndex_le (x : U) : (XU).degIndex x ≤ degIndex E C x :=
  (XU).degIndex_le (hU.selfChart_isChart hne) (mem_univ x)

/-- `d_C(x) ≤ d_{X_U}(x)` at points on level `1`: for every chart `ψ : (U ∩ V, x) → (O', ψ(x))` of
the structure, `d_C(x) ≤ d_{C'}(ψ(x))` by `degIndexWith_le_of_germ`. -/
theorem IsRelOpenInQuadrant.degIndex_le_degIndex_of_lvl1 (x : U) (hx1 : (x : E 0) ∈ range (E.toBase 1)) :
    degIndex E C x ≤ (XU).degIndex x := by
  obtain ⟨ψ, hψ, hxψ, hd⟩ := (XU).exists_isChart_degIndex_eq x
  rw [hd]
  set S : MChart U := (LocalModel.ofRelOpen hU).selfChart hne with hS
  have hcompat : ψ.Compatible S := hψ S (mem_singleton _)
  -- the overlaps: `S(V) = U₀ ⊆ U` relatively open, `ψ(V) = O'`
  have hSsrc : S.source = univ := rfl
  have hSapply : ∀ y : U, S y = (y : E 0) := fun _ => rfl
  have hover1 : S.overlap ψ = Subtype.val '' ψ.source := by
    ext z
    constructor
    · rintro ⟨y, ⟨_, hy⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, ⟨mem_univ _, hy⟩, rfl⟩
  have hover2 : ψ.overlap S = ψ.model.O := by
    rw [← ψ.image_source]
    ext z
    constructor
    · rintro ⟨y, ⟨hy, _⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, ⟨hy, mem_univ _⟩, rfl⟩
  obtain ⟨W₀, hW₀, hW₀eq⟩ := S.exists_isOpen_image_eq (s := ψ.source) (hSsrc ▸ subset_univ _)
    ψ.isOpen_source
  have hU₀eq : Subtype.val '' ψ.source = U ∩ W₀ := hW₀eq
  have hU₀ : IsRelOpenInQuadrant E C (Subtype.val '' ψ.source) := hU₀eq ▸ hU.inter_isOpen hW₀
  obtain ⟨R', hR'⟩ := ψ.model.isScRetract
  obtain ⟨n, W, T, hT⟩ := hU.isPartialQuadrant
  obtain ⟨n', W', T', hT'⟩ := ψ.model.isPartialQuadrant
  -- the maps `F = ψ ∘ S⁻¹` and `G = S ∘ ψ⁻¹`
  set F : E 0 → ψ.model.E 0 := S.transition ψ with hF
  set G : ψ.model.E 0 → E 0 := ψ.transition S with hG
  have h1 := hcompat.2
  have h2 := hcompat.1
  rw [hover1, hover2] at h1 h2
  have hFsc : IsSc1 (Subtype.val '' ψ.source) F := by
    have := h1.comp_isScSmooth (ScRetraction.id hU₀) (image_id _)
    exact this.isSc1
  have hGsc : IsSc1 R'.U (G ∘ R') := (h2.comp_isScSmooth R' hR').isSc1
  have hFO : MapsTo F (Subtype.val '' ψ.source) R'.retract := by rw [hR']; exact h1.mapsTo
  have hGU : MapsTo (G ∘ R') R'.U (Subtype.val '' ψ.source) := fun y hy =>
    h2.mapsTo (by rw [← hR']; exact R'.apply_mem_retract hy)
  have hGF : ∀ z ∈ Subtype.val '' ψ.source, G (F z) = z := by
    rintro _ ⟨y, hy, rfl⟩
    change ψ.transition S (S.transition ψ (S y)) = S y
    rw [S.transition_apply ψ (show y ∈ S.source from mem_univ y), ψ.transition_apply S hy]
  have hFG : ∀ z ∈ R'.retract, F (G z) = z := by
    rw [hR', ← ψ.image_source]
    rintro _ ⟨y, hy, rfl⟩
    change S.transition ψ (ψ.transition S (ψ y)) = ψ y
    rw [ψ.transition_apply S hy, S.transition_apply ψ (show y ∈ S.source from mem_univ y)]
  -- the inequality at `x`
  obtain ⟨x₁, hx₁⟩ := hx1
  have hx₁U₀ : x₁ ∈ E.lvlSet (Subtype.val '' ψ.source) 1 := by
    rw [ScBanach.mem_lvlSet, hx₁]; exact ⟨x, hxψ, rfl⟩
  have key := degIndexWith_le_of_germ T hT T' hT' hU₀ R' hFsc hGsc hFO hGU hGF hFG hx₁U₀
  rw [hx₁] at key
  have hFx : F x = ψ x := S.transition_apply ψ (show x ∈ S.source from mem_univ x)
  rw [hFx] at key
  have hxC : (x : E 0) ∈ C := by
    obtain ⟨O, _, hO⟩ := hU.relOpen
    have : (x : E 0) ∈ O ∩ C := by rw [← hO]; exact x.2
    exact this.2
  rw [MPolyfold.chartDegIndex, degIndex_eq T hT hxC, degIndex_eq T' hT' (ψ.apply_mem_C hxψ)]
  exact key

/-- **Corollary 2.32**: for a (nonempty, relatively open subset `U` of a) partial quadrant `C`,
viewed as the M-polyfold `X_U`, the degeneracy index of Definition 2.22 is `d_C`: `d_{X_U} = d_C`
on `U`. -/
theorem corollary_2_32 (x : U) : (XU).degIndex x = degIndex E C x := by
  refine le_antisymm (hU.degIndex_le hne x) ?_
  obtain ⟨n, W, T, hT⟩ := hU.isPartialQuadrant
  obtain ⟨O, hO, hUO⟩ := hU.relOpen
  have hxOC : (x : E 0) ∈ O ∩ C := by rw [← hUO]; exact x.2
  have hxC : (x : E 0) ∈ C := hxOC.2
  have hxO : (x : E 0) ∈ O := hxOC.1
  -- approximate `x` by level-`1` points of `U` with the same `d_C`
  obtain ⟨ι, l, σ, hl, hσ, hσ1, hσdeg, hσC⟩ := exists_tendsto_lvl1_degIndexWith T (x : E 0)
  have hxq : T 0 (x : E 0) ∈ quadrant n W 0 := by rwa [hT] at hxC
  have hσU : ∀ᶠ i in l, σ i ∈ U := by
    filter_upwards [hσ.eventually (hO.mem_nhds hxO)] with i hi
    rw [hUO]
    exact ⟨hi, by rw [hT, mem_preimage, hσC]; exact hxq⟩
  classical
  -- the approximating points as points of `X_U`
  let τ : ι → U := fun i => if h : σ i ∈ U then ⟨σ i, h⟩ else x
  have hτ : Tendsto τ l (𝓝 x) := by
    rw [tendsto_subtype_rng]
    refine hσ.congr' ?_
    filter_upwards [hσU] with i hi
    simp only [τ, dif_pos hi]
  have hle := hτ.eventually (lemma_2_23 (XU) x)
  have hev : ∀ᶠ i in l, degIndex E C x ≤ (XU).degIndex x := by
    filter_upwards [hσU, hσ1, hle] with i hiU hi1 hile
    have hτi : τ i = ⟨σ i, hiU⟩ := by simp only [τ, dif_pos hiU]
    rw [hτi] at hile
    have hiC : σ i ∈ C := (hUO ▸ hiU).2
    calc degIndex E C x = degIndexWith T x := degIndex_eq T hT hxC
      _ = degIndexWith T (σ i) := (hσdeg i).symm
      _ = degIndex E C (σ i) := (degIndex_eq T hT hiC).symm
      _ ≤ (XU).degIndex ⟨σ i, hiU⟩ := hU.degIndex_le_degIndex_of_lvl1 hne ⟨σ i, hiU⟩ hi1
      _ ≤ (XU).degIndex x := hile
  have := hl
  exact hev.exists.elim fun _ h => h

end Corollary232

end Polyfold
