import Polyfold.Chapter3.GoodPositionGerm
import Polyfold.Chapter2.Boundary

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I: the chart
independence of the linearization `f'(y)` of a section at a zero and of the good position of its
kernel — the local form of Definition 2.38 (gap G.13 of the report) that Definition 3.53 and the
proof of Theorem 3.54 (1) use at the zeros `y` near `x₀` — and the assembly of Definition 3.53 at
such a zero from the data in a chart which is not centred at it.

# The linearization of a section at a zero, in charts

## The text, paraphrased

(Definition 2.38) For a smooth point `x` of an M-polyfold, `T^R_xX` and `C_xX` are the preimages
of `T^R_oO = T_oO ∩ E_o` and `C_oO = T_oO ∩ C_o` under `Tψ(x)` for any chart `ψ`; "by
Proposition 2.30 these concepts are well defined and independent of the choice of the charts".
(Before Definition 3.4) "The linearization `Tf(0)` of the section `f : O → K` at `0 = r(0)` is
the restriction of `D(f ∘ r)(0)` to `T₀O`"; from `ρ(r(y))f(r(y)) = f(r(y))` and `f(0) = 0`,
`ρ(0)Tf(0) = Tf(0)`; from `g(r(y)) = f(r(y))`, `Tg(0) = Tf(0)` on `T₀O`.  (Definition 3.53) An
sc-Fredholm germ `(f, x)` with `f(x) = 0` is in good position if `f'(x) : T_xX → Y_x` is onto and,
if `d_X(x) ≥ 1`, `ker f'(x)` is in good position to `C_xX` in `T_xX`.  (Proof of Theorem 3.54,
last paragraph) "for every `y ∈ S` … `f'(y)` is a surjective Fredholm operator whose kernel is in
good position to `C_yV`, so that, proceeding as above we can construct a map `σ`": the argument
at `x₀` is repeated at `y` in a chart centred at `y`.

## What is formalized

* **Linear algebra of conjugate operators** `L' ∘ A = Γ ∘ L` (`A : T ≃L T'`, `Γ : K ≃L K'`):
  `surjective_iff_of_conj`, `isFredholm_iff_of_conj` (Fredholm property and index),
  `ker_eq_map_of_conj`, `dense_image_of_conj`; `restrictEquiv` (an isomorphism of subspaces from
  operators inverse to each other on them); `transportSub` and
  `IsInGoodPositionIn.transport` / `isInGoodPositionIn_transport_iff`: good position inside a
  subspace (Definition 3.53 (2), `IsInGoodPositionIn`) is carried by an isomorphism of the
  subspaces respecting the cones, with the constant `ε/(‖A‖‖A⁻¹‖ + 1)` of Lemma 3.45.
* **Derivatives at a level-`1` point**: `scDeriv_eq_of_eqOn_relOpen` (the derivative depends only
  on the map on a relatively open neighbourhood), `scDeriv_scPair`, and
  `scDeriv_fiber_of_vanishing`: the derivative at `(z, 0)` of a map vanishing on the zero
  section near `z` and linear on the fibre over `z` is the fibre map (`DΦ(z, 0)(h, k) = Γk`; the
  generalization of `StrongRetr.scDeriv_fiber_zero` and `IsStrongBundleMap.scDeriv_fiber_zero`
  from `0` to any `z`).
* **The linearization in a chart**: `linAt U R f̂ z = D(f̂ ∘ r)(z)|_{T_zO}`, `T_zO = Dr(z)E`,
  at any level-`1` point `z` of the retract; `rho_scDeriv_comp_r` (at a zero of `f̂` its values
  lie in `K_z = ρ(z)F`; `mem_rangeS_ρCLM_iff`: `K_z` is the fibre of `K` over `z`),
  `scDeriv_comp_r_eq_of_eventuallyEq` and `linAt_eq_scDeriv` (the bridge to fillers:
  `D(f̂ ∘ r)(z) = Dg(z)Dr(z)`, so `Lin(z) = Dg(z)` on `T_zO`, for every `g` agreeing with `f̂` on
  `O` near `z`), `IsFilledVersion.fillerRestrict_eq_linAt` (at a central zero `Lin(0)` is the
  `Tf̃(0) = fillerRestrict` of Proposition 3.5).
* **The fibres of a strong bundle chart and of a transition** (`StrongBundleChart`):
  `Φ⁻¹(x, ·)` is linear on the fibre of `K` over `x ∈ O` (`symm_add`, `symm_smul`), the
  transition `Θ = Φ' ∘ Φ⁻¹` covers `τ = φ' ∘ φ⁻¹` and is linear on the fibres
  (`transition_fst`, `transition_snd_add`, `transition_snd_smul`, `transition_snd_zero`), maps `K`
  into `K'` and is inverted by the reverse transition; `transitionFiberCLM` (the bounded fibre
  operator `Γ(x)`); `overlap_eq_inter_prod` (the overlap of `K` is `K ∩ (W × F)` for `W` open).
* **`linAt_chart_change` (the chart independence at a zero)**: for strong bundle charts `c`, `c'`
  whose transition is sc-smooth on `[0]`, a section with sc-smooth principal parts in both, and a
  zero `y` with level-`1` points `z`, `z'` over `φ(y)`, `φ'(y)`: isomorphisms
  `A : T_zO ≅ T_{z'}O'` and `Γ : K_z ≅ K'_{z'}` with `Γ ∘ Lin(z) = Lin'(z') ∘ A` and
  `x ∈ C_z ↔ Ax ∈ C'_{z'}` on `T_zO` (the partial cones `C_zO`, `C_{z'}O'` correspond).
  `StrongBundle.linAt_chart_independence`: for two strong bundle charts of `P` the linearizations
  `Lin(z) : T_zO → K_z` and `Lin'(z') : T_{z'}O' → K'_{z'}` are simultaneously surjective,
  simultaneously Fredholm with the same index, and their kernels are simultaneously in good
  position to the partial cones.
* **The assembly for Definition 3.53 at a non-central zero**:
  `StrongBundle.isGoodPositionGerm_of_chart_dense` (and `_of_chart`, `_of_linAt`,
  `_of_linAt_surj`): if `(f, y)` is an sc-Fredholm germ, `f(y) = 0`, and in some strong bundle
  chart `c` around `y` (e.g. the chart centred at `x₀`), with `g` agreeing with `f̂` on `O` near
  `φ(y)`, the range of `Dg(z)|_{T_zO}` contains `ρ(z)F_∞` (or all of `K_z`) and
  `ker Dg(z) ∩ T_zO` is in good position to `C_{φ(y)}` inside `T_zO`, then `(f, y)` is in good
  position in the sense of `StrongBundle.IsGoodPositionGermWholeChart` (Definition 3.53 in the chart `c'`
  centred at `y` given by Definition 3.11).  `StrongBundle.isGoodPositionAt_of_chart_dense`: the
  same conclusion in **every** chart `c'` carrying germ data at `y` (used to read the good
  position in a tame chart, `IsGoodPositionGermWholeChart.toTame`, `TameGerms.lean`).

## What the text leaves implicit, and the choices made

* **Definition 3.53 is stated in `T_xX`**, where the formalization has no linear structure (gap
  G.7), and `f'(x)` is defined (before Definition 3.4) only at the centre of a chart, through a
  filler; `IsGoodPositionAt` therefore states Definition 3.53 in the chart of Definition 3.11.
  Neither the independence of `f'(x)` of the chart and the filler nor that of the two conditions
  of Definition 3.53 is proved in the text (Definition 2.38 appeals to Proposition 2.30 for
  `T^R_xX` and `C_xX` only).  Here the linearization at a zero is the filler-free
  `Lin(z) = D(f̂ ∘ r)(z)|_{T_zO}`, defined at every level-`1` point of every chart; it agrees with
  `Tf̃(0)` at a centre (`fillerRestrict_eq_linAt`) and with `Dg(z)|_{T_zO}` for every `g` agreeing
  with `f̂` near `z`.
* **Only the fibre derivative survives at a zero.**  `Θ(x, h) = (τ(x), Γ(x)h)` with `Γ(x)`
  linear, so the derivative of `u ↦ Θ(r(u), f̂(r(u)))₂` at `z` is
  `D_xΓ(z)[Dr(z)·] f̂(z) + Γ(z) D(f̂ ∘ r)(z)`; the first term vanishes because `f̂(z) = 0`
  (formally: `Θ(x, 0) = (τ(x), 0)` near `z`, `scDeriv_fiber_of_vanishing`).  Away from zeros the
  linearization is not chart independent.
* **`Γ(z)` is a topological isomorphism `K_z ≅ K'_{z'}`**: `Φ⁻¹` is linear on the fibres of `K`
  (`Φ` is a fibrewise linear bijection onto `K`) and continuous (`Φ` is a homeomorphism); the
  inverse is the fibre map of the reverse transition.  The text's "bounded linear on the fibres"
  is for `Φ` only.
* **Proposition 2.30 is applied on the overlap retracts.**  The base transition `τ = φ' ∘ φ⁻¹` is
  a germ of sc-diffeomorphisms between `φ(V ∩ V') = O ∩ W` and `φ'(V ∩ V') = O' ∩ W'`, with the
  restricted retractions `r|_{U ∩ r⁻¹(W)}` (Proposition 2.10 (1)); `A = D(τ ∘ r_W)(z)` restricted
  to `T_zO` (inverse `D(τ' ∘ r'_{W'})(z')`, `IsDiffeoGerm.deriv_inv_deriv`), and
  `proposition_2_30_cone` gives `A(T_zO ∩ C_z) = T_{z'}O' ∩ C'_{z'}` — the formalized partial cone
  `partialConeWith R T z = range Dr(z) ∩ partialQuadrantAtWith T z` of Definition 2.27, with
  `Dr_W(z) = Dr(z)` by the uniqueness of the derivative on the smaller domain.  At a centre
  `C'_0 = C'` (`partialQuadrantAtWith_zero`).
* **Hypotheses.**  Of the compatibility of Definition 2.50 only the sc-smoothness of
  `Θ = Φ' ∘ Φ⁻¹` on `[0]` is used (not `[1]`, not the reverse transition); for two strong bundle
  charts of `P` it holds because both are charts of the M-polyfold `Y[0]`
  (`StrongBundle.IsChart.transition_isScSmoothRetractMap`), and the base charts are compatible
  because both are charts of `X` (`MPolyfold.IsChart.compatible`).  The points need only be on
  level `1` (as Proposition 2.30 in `Boundary.lean`); the text has smooth points.  Tameness is not
  used.  The section is assumed sc-smooth (its principal parts are sc-smooth in every strong
  bundle chart of `P`), which is part of Definition 3.14.
* **The assembly.**  At the centre of the chart `c'` of Definition 3.11 the kernel condition of
  `IsGoodPositionAt` is about `ker Dg'(0)`, which equals `ker Tf̃'(0) ⊕ 0` by condition (3) of the
  filler at `0` (`IsFillerOf.ker_deriv_le_range`).  In the non-centred chart `c` the hypothesis
  is on `ker Dg(z) ∩ T_zO`, not on `ker Dg(z)`: condition (3) holds at the centre only, so
  `ker Dg(z)` need not lie in `T_zO` (Finding 91 (b)).  The surjectivity of `Tf̃'(0)` needs only a
  dense subset of `K_z` in the range of `Lin(z)` (e.g. `ρ(z)F_∞`): the range of `Tf̃'(0)` is
  closed because `Tf̃'(0)` is Fredholm (Proposition 3.52 in the centred chart `c'`), and it
  contains the dense image of that subset under `Γ`.
-/

open Set Filter Topology Function Module ContinuousLinearMap

noncomputable section

namespace Polyfold

universe u v

/-! ### Linear algebra of conjugate operators -/

section Conjugate

variable {T K T' K' : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] [NormedAddCommGroup K]
  [NormedSpace ℝ K] [NormedAddCommGroup T'] [NormedSpace ℝ T'] [NormedAddCommGroup K']
  [NormedSpace ℝ K'] {L : T →L[ℝ] K} {L' : T' →L[ℝ] K'} {A : T ≃L[ℝ] T'} {Γ : K ≃L[ℝ] K'}

/-- A conjugate `L' ∘ A = Γ ∘ L` is `Γ ∘ L ∘ A⁻¹`. -/
lemma eq_comp_of_conj (h : ∀ x, L' (A x) = Γ (L x)) :
    L' = (Γ : K →L[ℝ] K').comp (L.comp (A.symm : T' →L[ℝ] T)) := by
  ext y
  have := h (A.symm y)
  rw [A.apply_symm_apply] at this
  simpa using this

/-- Surjectivity is invariant under conjugation. -/
theorem surjective_iff_of_conj (h : ∀ x, L' (A x) = Γ (L x)) : Surjective L ↔ Surjective L' := by
  constructor
  · intro hL y
    obtain ⟨x, hx⟩ := hL (Γ.symm y)
    exact ⟨A x, by rw [h, hx, Γ.apply_symm_apply]⟩
  · intro hL' y
    obtain ⟨x, hx⟩ := hL' (Γ y)
    refine ⟨A.symm x, Γ.injective ?_⟩
    rw [← h, A.apply_symm_apply, hx]

/-- The kernel of a conjugate: `ker L' = A(ker L)`. -/
theorem ker_eq_map_of_conj (h : ∀ x, L' (A x) = Γ (L x)) :
    LinearMap.ker (L' : T' →ₗ[ℝ] K') = (LinearMap.ker (L : T →ₗ[ℝ] K)).map (A : T →ₗ[ℝ] T') := by
  ext y
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, Submodule.mem_map]
  constructor
  · intro hy
    refine ⟨A.symm y, ?_, A.apply_symm_apply y⟩
    have := h (A.symm y)
    rw [A.apply_symm_apply, hy] at this
    exact Γ.map_eq_zero_iff.1 this.symm
  · rintro ⟨x, hx, rfl⟩
    change L' (A x) = 0
    rw [h, hx, map_zero]

variable [CompleteSpace T] [CompleteSpace K] [CompleteSpace T'] [CompleteSpace K']

/-- The Fredholm property and the index are invariant under conjugation. -/
theorem isFredholm_iff_of_conj (h : ∀ x, L' (A x) = Γ (L x)) :
    (IsFredholm L ↔ IsFredholm L') ∧ (IsFredholm L → fredholmIndex L' = fredholmIndex L) := by
  have hL' := eq_comp_of_conj h
  have hL : L = (Γ.symm : K' →L[ℝ] K).comp (L'.comp (A : T →L[ℝ] T')) := by
    ext x; simp [h]
  refine ⟨⟨fun hF => ?_, fun hF => ?_⟩, fun hF => ?_⟩
  · rw [hL']; exact (isFredholm_equiv_comp_equiv hF A.symm Γ).1
  · rw [hL]; exact (isFredholm_equiv_comp_equiv hF A Γ.symm).1
  · rw [hL']; exact (isFredholm_equiv_comp_equiv hF A.symm Γ).2

end Conjugate

/-- **Dense images.**  If `D ⊆ K` is dense and contained in the range of `L`, then `Γ(D)` is
dense in `K'` and contained in the range of the conjugate `L'`. -/
theorem dense_image_of_conj {T K T' K' : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
    [NormedAddCommGroup K] [NormedSpace ℝ K] [NormedAddCommGroup T'] [NormedSpace ℝ T']
    [NormedAddCommGroup K'] [NormedSpace ℝ K'] {L : T →L[ℝ] K} {L' : T' →L[ℝ] K'}
    {A : T ≃L[ℝ] T'} {Γ : K ≃L[ℝ] K'} (h : ∀ x, L' (A x) = Γ (L x)) {D : Set K} (hD : Dense D)
    (hDL : D ⊆ range L) : Dense (Γ '' D) ∧ Γ '' D ⊆ range L' := by
  refine ⟨Γ.surjective.denseRange.dense_image Γ.continuous hD, ?_⟩
  rintro _ ⟨k, hk, rfl⟩
  obtain ⟨x, rfl⟩ := hDL hk
  exact ⟨A x, h x⟩

/-! ### Isomorphisms of subspaces induced by operators -/

/-- The isomorphism `T ≃L T'` induced by bounded operators `a : E₀ → E'₀`, `a' : E'₀ → E₀` which
map `T` to `T'` and `T'` to `T` and are inverse to each other there. -/
def restrictEquiv {E₀ E₀' : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    [NormedAddCommGroup E₀'] [NormedSpace ℝ E₀'] (T : Submodule ℝ E₀) (T' : Submodule ℝ E₀')
    (a : E₀ →L[ℝ] E₀') (a' : E₀' →L[ℝ] E₀) (ha : ∀ x ∈ T, a x ∈ T') (ha' : ∀ y ∈ T', a' y ∈ T)
    (h1 : ∀ x ∈ T, a' (a x) = x) (h2 : ∀ y ∈ T', a (a' y) = y) : T ≃L[ℝ] T' :=
  ContinuousLinearEquiv.equivOfInverse ((a.comp T.subtypeL).codRestrict T' fun x => ha x x.2)
    ((a'.comp T'.subtypeL).codRestrict T fun y => ha' y y.2)
    (fun x => Subtype.ext (h1 x x.2)) (fun y => Subtype.ext (h2 y y.2))

@[simp] lemma restrictEquiv_apply {E₀ E₀' : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    [NormedAddCommGroup E₀'] [NormedSpace ℝ E₀'] (T : Submodule ℝ E₀) (T' : Submodule ℝ E₀')
    (a : E₀ →L[ℝ] E₀') (a' : E₀' →L[ℝ] E₀) (ha : ∀ x ∈ T, a x ∈ T') (ha' : ∀ y ∈ T', a' y ∈ T)
    (h1 : ∀ x ∈ T, a' (a x) = x) (h2 : ∀ y ∈ T', a (a' y) = y) (x : T) :
    (restrictEquiv T T' a a' ha ha' h1 h2 x : E₀') = a x := rfl

/-! ### Transport of subspaces and of good position through `A : T ≃L T'` -/

section Transport

variable {E₀ E₀' : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [NormedAddCommGroup E₀']
  [NormedSpace ℝ E₀'] {T : Submodule ℝ E₀} {T' : Submodule ℝ E₀'}

/-- The image `A(N) ⊆ T' ⊆ E'₀` of a subspace `N ⊆ E₀` (of `N ∩ T`) under `A : T ≃L T'`. -/
def transportSub (A : T ≃L[ℝ] T') (N : Submodule ℝ E₀) : Submodule ℝ E₀' :=
  ((N.comap T.subtype).map (A : T →ₗ[ℝ] T')).map T'.subtype

/-- `y ∈ A(N)` iff `y = Ax` for some `x ∈ T ∩ N`. -/
lemma mem_transportSub (A : T ≃L[ℝ] T') {N : Submodule ℝ E₀} {y : E₀'} :
    y ∈ transportSub A N ↔ ∃ x : T, (x : E₀) ∈ N ∧ (A x : E₀') = y := by
  simp only [transportSub, Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨A x, ⟨x, hx, rfl⟩, rfl⟩

/-- `A(N) ⊆ T'`. -/
lemma transportSub_le (A : T ≃L[ℝ] T') (N : Submodule ℝ E₀) : transportSub A N ≤ T' := by
  intro y hy
  obtain ⟨x, -, rfl⟩ := (mem_transportSub A).1 hy
  exact (A x).2

/-- For `y ∈ T'`: `y ∈ A(N)` iff `A⁻¹y ∈ N`. -/
lemma mem_transportSub_iff (A : T ≃L[ℝ] T') {N : Submodule ℝ E₀} (y : T') :
    (y : E₀') ∈ transportSub A N ↔ ((A.symm y : T) : E₀) ∈ N := by
  rw [mem_transportSub]
  constructor
  · rintro ⟨x, hx, hxy⟩
    have : A x = y := Subtype.ext hxy
    rwa [← this, A.symm_apply_apply]
  · intro hy
    exact ⟨A.symm y, hy, by rw [A.apply_symm_apply]⟩

/-- `A⁻¹(A(N)) = N` for `N ⊆ T`. -/
lemma transportSub_symm (A : T ≃L[ℝ] T') {N : Submodule ℝ E₀} (hN : N ≤ T) :
    transportSub A.symm (transportSub A N) = N := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := (mem_transportSub A.symm).1 hx
    exact (mem_transportSub_iff A y).1 hy
  · intro hx
    rw [mem_transportSub]
    refine ⟨A ⟨x, hN hx⟩, ?_, by rw [A.symm_apply_apply]⟩
    rw [mem_transportSub_iff, A.symm_apply_apply]
    exact hx

/-- The transport of `N` is the image of the subtype-level map. -/
lemma transportSub_eq_map (A : T ≃L[ℝ] T') (N : Submodule ℝ T) :
    transportSub A (N.map T.subtype) = (N.map (A : T →ₗ[ℝ] T')).map T'.subtype := by
  ext y
  rw [mem_transportSub]
  simp only [Submodule.mem_map, Submodule.subtype_apply]
  constructor
  · rintro ⟨x, ⟨x', hx', hxx'⟩, rfl⟩
    have : x' = x := Subtype.ext hxx'
    subst this
    exact ⟨A x', ⟨x', hx', rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, ⟨x, hx, rfl⟩, rfl⟩

end Transport

section TransportGood

variable {E E' : ScBanach} {T : Submodule ℝ (E 0)} {T' : Submodule ℝ (E' 0)}
  {C : Set (E 0)} {C' : Set (E' 0)}

/-- **Good position inside a subspace is carried by an isomorphism of the subspaces** (the
transport form of Lemma 3.45): if `A : T ≃L T'` respects the cones (`x ∈ C ↔ Ax ∈ C'` on `T`) and
`N ⊆ T` is in good position to `C` inside `T`, then `A(N)` is in good position to `C'` inside
`T'`, with the constant `ε' = ε/(‖A‖‖A⁻¹‖ + 1)`. -/
theorem IsInGoodPositionIn.transport (A : T ≃L[ℝ] T')
    (hA : ∀ x : T, (x : E 0) ∈ C ↔ (A x : E' 0) ∈ C') {N : Submodule ℝ (E 0)}
    (h : IsInGoodPositionIn E T C N) : IsInGoodPositionIn E' T' C' (transportSub A N) := by
  obtain ⟨hNT, hint, P, hPT, hNP, hNPT, ε, hε, hgood⟩ := h
  -- the homeomorphism `N ≅ A(N)`
  let fwd : N → transportSub A N := fun x =>
    ⟨A ⟨x, hNT x.2⟩, (mem_transportSub A).2 ⟨⟨x, hNT x.2⟩, x.2, rfl⟩⟩
  let bwd : transportSub A N → N := fun y =>
    ⟨A.symm ⟨y, transportSub_le A N y.2⟩,
      (mem_transportSub_iff A ⟨y, transportSub_le A N y.2⟩).1 y.2⟩
  have hfwd : Continuous fwd := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.comp (A.continuous.comp
      (Continuous.subtype_mk continuous_subtype_val _))
  have hbwd : Continuous bwd := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.comp (A.symm.continuous.comp
      (Continuous.subtype_mk continuous_subtype_val _))
  let ψ : N ≃ₜ transportSub A N :=
    { toFun := fwd
      invFun := bwd
      left_inv := fun x => Subtype.ext (by
        change ((A.symm (A ⟨x, hNT x.2⟩) : T) : E 0) = x
        rw [A.symm_apply_apply])
      right_inv := fun y => Subtype.ext (by
        change ((A (A.symm ⟨y, transportSub_le A N y.2⟩) : T') : E' 0) = y
        rw [A.apply_symm_apply])
      continuous_toFun := hfwd
      continuous_invFun := hbwd }
  have hpre : ψ ⁻¹' (Subtype.val ⁻¹' C' : Set (transportSub A N)) =
      (Subtype.val ⁻¹' C : Set N) := by
    ext x
    simp only [mem_preimage]
    exact (hA ⟨x, hNT x.2⟩).symm
  refine ⟨transportSub_le A N, ?_, transportSub A P, transportSub_le A P, ?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hint
    refine ⟨ψ x, ?_⟩
    rw [← mem_preimage, ψ.preimage_interior, hpre]
    exact hx
  · -- `A(N) ∩ A(P) = 0`
    rw [eq_bot_iff]
    rintro y ⟨hyN, hyP⟩
    have hyT : y ∈ T' := transportSub_le A N hyN
    have h1 := (mem_transportSub_iff A ⟨y, hyT⟩).1 hyN
    have h2 := (mem_transportSub_iff A ⟨y, hyT⟩).1 hyP
    have h3 : ((A.symm ⟨y, hyT⟩ : T) : E 0) ∈ N ⊓ P := ⟨h1, h2⟩
    rw [hNP, Submodule.mem_bot] at h3
    have h4 : A.symm ⟨y, hyT⟩ = 0 := Subtype.ext h3
    have h5 : (⟨y, hyT⟩ : T') = 0 := by
      have := congrArg A h4
      rwa [A.apply_symm_apply, map_zero] at this
    rw [Submodule.mem_bot]
    exact congrArg Subtype.val h5
  · -- `A(N) + A(P) = T'`
    apply le_antisymm (sup_le (transportSub_le A N) (transportSub_le A P))
    intro y hyT
    have hx : ((A.symm ⟨y, hyT⟩ : T) : E 0) ∈ N ⊔ P := by rw [hNPT]; exact (A.symm ⟨y, hyT⟩).2
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hx
    have hsum : (⟨a, hNT ha⟩ : T) + ⟨b, hPT hb⟩ = A.symm ⟨y, hyT⟩ := Subtype.ext hab
    refine Submodule.mem_sup.2 ⟨A ⟨a, hNT ha⟩, (mem_transportSub A).2 ⟨_, ha, rfl⟩,
      A ⟨b, hPT hb⟩, (mem_transportSub A).2 ⟨_, hb, rfl⟩, ?_⟩
    have := congrArg (fun t => ((A t : T') : E' 0)) hsum
    simp only [map_add, A.apply_symm_apply, Submodule.coe_add] at this
    exact this
  · -- the constant
    set a : ℝ := ‖(A : T →L[ℝ] T')‖ with ha
    set b : ℝ := ‖(A.symm : T' →L[ℝ] T)‖ with hb
    have hc : 0 < a * b + 1 := by positivity
    refine ⟨ε / (a * b + 1), by positivity, ?_⟩
    intro y hy q hq hle
    obtain ⟨x, hxN, rfl⟩ := (mem_transportSub A).1 hy
    obtain ⟨p, hpP, rfl⟩ := (mem_transportSub A).1 hq
    have hp : ‖(p : E 0)‖ ≤ ε * ‖(x : E 0)‖ := by
      have h1 : ‖p‖ ≤ b * ‖A p‖ := by
        have := (A.symm : T' →L[ℝ] T).le_opNorm (A p)
        simpa using this
      have h2 : ‖A x‖ ≤ a * ‖x‖ := (A : T →L[ℝ] T').le_opNorm x
      have hle' : ‖A p‖ ≤ ε / (a * b + 1) * ‖A x‖ := by simpa using hle
      have h3 : b * (ε / (a * b + 1) * a) ≤ ε := by
        have : b * (ε / (a * b + 1) * a) = ε * (a * b / (a * b + 1)) := by
          field_simp
        rw [this]
        calc ε * (a * b / (a * b + 1)) ≤ ε * 1 := by
              gcongr
              rw [div_le_one hc]; linarith
          _ = ε := mul_one ε
      have hb0 : 0 ≤ b := norm_nonneg (A.symm : T' →L[ℝ] T)
      calc ‖(p : E 0)‖ = ‖p‖ := rfl
        _ ≤ b * ‖A p‖ := h1
        _ ≤ b * (ε / (a * b + 1) * (a * ‖x‖)) := by gcongr; exact hle'.trans (by gcongr)
        _ = b * (ε / (a * b + 1) * a) * ‖x‖ := by ring
        _ ≤ ε * ‖x‖ := by gcongr
        _ = ε * ‖(x : E 0)‖ := rfl
    have key := hgood x hxN p hpP hp
    have hsum : ((A x : T') : E' 0) + (A p : E' 0) = ((A (x + p) : T') : E' 0) := by
      rw [map_add]; rfl
    rw [hsum, ← hA, ← hA]
    exact key

/-- Good position inside `T` holds iff its transport holds inside `T'`. -/
theorem isInGoodPositionIn_transport_iff (A : T ≃L[ℝ] T')
    (hA : ∀ x : T, (x : E 0) ∈ C ↔ (A x : E' 0) ∈ C') {N : Submodule ℝ (E 0)} (hN : N ≤ T) :
    IsInGoodPositionIn E T C N ↔ IsInGoodPositionIn E' T' C' (transportSub A N) := by
  refine ⟨fun h => h.transport A hA, fun h => ?_⟩
  have hA' : ∀ y : T', (y : E' 0) ∈ C' ↔ (A.symm y : E 0) ∈ C := fun y => by
    rw [hA, A.apply_symm_apply]
  have := h.transport A.symm hA'
  rwa [transportSub_symm A hN] at this

end TransportGood

/-! ### Derivatives at a level-`1` point -/

section DerivTools

variable {E F G : ScBanach}

/-- **Uniqueness of the derivative at a level-`1` point**: if `f₁ = f₂` on a relatively open
`V ⊆ U₁ ∩ U₂` containing `z`, then `Df₁(z) = Df₂(z)` (uniqueness within `V₁` and the density of
`E₁` in `E₀`). -/
theorem scDeriv_eq_of_eqOn_relOpen {C V U₁ U₂ : Set (E 0)} {f₁ f₂ : E 0 → F 0}
    (hV : IsRelOpenInQuadrant E C V) (h₁ : IsSc1 U₁ f₁) (h₂ : IsSc1 U₂ f₂) (hV₁ : V ⊆ U₁)
    (hV₂ : V ⊆ U₂) (heq : EqOn f₁ f₂ V) {z : E 1} (hz : z ∈ E.lvlSet V 1) :
    scDeriv U₁ f₁ z = scDeriv U₂ f₂ z := by
  apply ContinuousLinearMap.ext_of_comp_toBase_one (E := E)
  have d₁ := (h₁.isSc1With_scDeriv.hasFDerivWithinAt z (E.lvlSet_mono hV₁ 1 hz)).mono
    (E.lvlSet_mono hV₁ 1)
  have d₂ := (h₂.isSc1With_scDeriv.hasFDerivWithinAt z (E.lvlSet_mono hV₂ 1 hz)).mono
    (E.lvlSet_mono hV₂ 1)
  have d₂' : HasFDerivWithinAt (f₁ ∘ E.toBase 1) ((scDeriv U₂ f₂ z).comp (E.toBase 1))
      (E.lvlSet V 1) z := d₂.congr (fun x hx => heq hx) (heq hz)
  exact (hV.isScDomain.uniqueDiffWithinAt 1 z hz).eq d₁ d₂'

/-- The derivative of a pairing at a level-`1` point. -/
theorem scDeriv_scPair {C U : Set (E 0)} (hU : IsRelOpenInQuadrant E C U) {f : E 0 → F 0}
    {g : E 0 → G 0} (hf : IsSc1 U f) (hg : IsSc1 U g) {x : E 1} (hx : x ∈ E.lvlSet U 1) :
    scDeriv U (scPair f g) x = (scDeriv U f x).prod (scDeriv U g x) :=
  IsSc1.scDeriv_eqOn (hf.isSc1With_scDeriv.scPair hg.isSc1With_scDeriv)
    (hU.isScDomain.uniqueDiffWithinAt 1) hx

/-- The pairing of sc¹ maps is sc¹. -/
lemma IsSc1.scPair' {U : Set (E 0)} {f : E 0 → F 0} {g : E 0 → G 0} (hf : IsSc1 U f)
    (hg : IsSc1 U g) : IsSc1 U (scPair f g) :=
  (hf.isSc1With_scDeriv.scPair hg.isSc1With_scDeriv).isSc1

/-- **The linearization of a fibrewise map at a point `(z, 0)` of the zero section**: let
`Φ : D → G` be sc¹ on `D ⊆ E ⊕ F`, vanishing on `{(u, 0) | u ∈ S}` (`S` relatively open, `z ∈ S₁`)
and equal to the bounded linear `Γ` on the fibre `{ι z} × F ⊆ D`.  Then
`DΦ(z, 0)(h, k) = Γk`: the base direction drops out because `Φ(u, 0) = 0`. -/
theorem scDeriv_fiber_of_vanishing {C S : Set (E 0)} {D : Set ((E.prod F) 0)}
    (hS : IsRelOpenInQuadrant E C S) {Φ : (E.prod F) 0 → G 0} (hΦ : IsSc1 D Φ) {z : E 1}
    (hzS : z ∈ E.lvlSet S 1) (hSD : ∀ u ∈ S, ((u, 0) : (E.prod F) 0) ∈ D)
    (hzD : ∀ k : F 0, ((E.toBase 1 z, k) : (E.prod F) 0) ∈ D) (hzero : ∀ u ∈ S, Φ (u, 0) = 0)
    (Γ : F 0 →L[ℝ] G 0) (hΓ : ∀ k, Φ (E.toBase 1 z, k) = Γ k) (h : E 0) (k : F 0) :
    scDeriv D Φ ((z, 0) : (E.prod F) 1) (h, k) = Γ k := by
  set D' := scDeriv D Φ ((z, 0) : (E.prod F) 1) with hD'
  have hz0 : ((z, 0) : (E.prod F) 1) ∈ (E.prod F).lvlSet D 1 := by
    rw [ScBanach.mem_lvlSet, ScBanach.prod_toBase, map_zero]; exact hzD 0
  have hder := hΦ.isSc1With_scDeriv.hasFDerivWithinAt _ hz0
  -- the fibre direction
  have hinr : D'.comp (ContinuousLinearMap.inr ℝ (E 0) (F 0)) = Γ := by
    apply ContinuousLinearMap.ext_of_comp_toBase_one (E := F)
    let j : F 1 → (E.prod F) 1 := fun k₁ => (z, k₁)
    have hj : HasFDerivAt j (ContinuousLinearMap.inr ℝ (E 1) (F 1)) 0 := by
      have := (hasFDerivAt_const (𝕜 := ℝ) z (0 : F 1)).prodMk (hasFDerivAt_id (𝕜 := ℝ) (0 : F 1))
      convert this using 1
      · rfl
      · ext x <;> simp
    have hmaps : MapsTo j univ ((E.prod F).lvlSet D 1) := fun k₁ _ => by
      change (E.prod F).toBase 1 (z, k₁) ∈ D
      rw [ScBanach.prod_toBase]; exact hzD _
    have h1 : HasFDerivWithinAt ((Φ ∘ (E.prod F).toBase 1) ∘ j)
        ((D'.comp ((E.prod F).toBase 1)).comp (ContinuousLinearMap.inr ℝ (E 1) (F 1))) univ 0 :=
      HasFDerivWithinAt.comp (f := j) (0 : F 1) hder hj.hasFDerivWithinAt hmaps
    have h2 : HasFDerivWithinAt ((Φ ∘ (E.prod F).toBase 1) ∘ j) (Γ.comp (F.toBase 1)) univ 0 := by
      have : (Φ ∘ (E.prod F).toBase 1) ∘ j = fun k₁ => Γ (F.toBase 1 k₁) := by
        funext k₁
        simp only [Function.comp_apply, j]
        rw [ScBanach.prod_toBase]
        exact hΓ _
      rw [this]
      exact (Γ.comp (F.toBase 1)).hasFDerivAt.hasFDerivWithinAt
    have huniq := uniqueDiffWithinAt_univ.eq h1 h2
    ext k₁
    have := congrArg (fun L : F 1 →L[ℝ] G 0 => L k₁) huniq
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] at this ⊢
    rw [ScBanach.prod_toBase, map_zero] at this
    exact this
  -- the base direction
  have hinl : D'.comp (ContinuousLinearMap.inl ℝ (E 0) (F 0)) = 0 := by
    apply ContinuousLinearMap.ext_of_comp_toBase_one (E := E)
    have hmaps : MapsTo ⇑(ContinuousLinearMap.inl ℝ (E 1) (F 1)) (E.lvlSet S 1)
        ((E.prod F).lvlSet D 1) := by
      intro u₁ hu₁
      change (E.prod F).toBase 1 (u₁, 0) ∈ D
      rw [ScBanach.prod_toBase, map_zero]; exact hSD _ hu₁
    have h1 : HasFDerivWithinAt
        ((Φ ∘ (E.prod F).toBase 1) ∘ ⇑(ContinuousLinearMap.inl ℝ (E 1) (F 1)))
        ((D'.comp ((E.prod F).toBase 1)).comp (ContinuousLinearMap.inl ℝ (E 1) (F 1)))
        (E.lvlSet S 1) z :=
      HasFDerivWithinAt.comp (f := ⇑(ContinuousLinearMap.inl ℝ (E 1) (F 1))) z hder
        (ContinuousLinearMap.inl ℝ (E 1) (F 1)).hasFDerivWithinAt hmaps
    have hzero' : ∀ u₁ ∈ E.lvlSet S 1,
        ((Φ ∘ (E.prod F).toBase 1) ∘ ⇑(ContinuousLinearMap.inl ℝ (E 1) (F 1))) u₁ = 0 := by
      intro u₁ hu₁
      simp only [Function.comp_apply, ContinuousLinearMap.inl_apply]
      rw [ScBanach.prod_toBase, map_zero]; exact hzero _ hu₁
    have h2 : HasFDerivWithinAt
        ((Φ ∘ (E.prod F).toBase 1) ∘ ⇑(ContinuousLinearMap.inl ℝ (E 1) (F 1)))
        (0 : E 1 →L[ℝ] G 0) (E.lvlSet S 1) z :=
      (hasFDerivWithinAt_const (0 : G 0) z (E.lvlSet S 1)).congr hzero' (hzero' z hzS)
    have huniq := (hS.isScDomain.uniqueDiffWithinAt 1 z hzS).eq h1 h2
    ext u₁
    have := congrArg (fun T : E 1 →L[ℝ] G 0 => T u₁) huniq
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      zero_apply] at this ⊢
    rw [ScBanach.prod_toBase, map_zero] at this
    exact this
  have hhk : ((h, k) : (E.prod F) 0) = ContinuousLinearMap.inl ℝ (E 0) (F 0) h +
      ContinuousLinearMap.inr ℝ (E 0) (F 0) k := by simp
  rw [hhk, map_add]
  have e1 := congrArg (fun T : E 0 →L[ℝ] G 0 => T h) hinl
  have e2 := congrArg (fun T : F 0 →L[ℝ] G 0 => T k) hinr
  simp only [ContinuousLinearMap.comp_apply, zero_apply] at e1 e2
  rw [e1, e2, zero_add]

end DerivTools

/-! ### The linearization `Lin(z) = D(f̂ ∘ r)(z)|_{T_zO}` at a zero, in a chart -/

section Lin

variable {E F : ScBanach} {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

open StrongRetr

/-- **The linearization at a point `z` of the retract**, chart-intrinsically:
`Lin(z) = D(f̂ ∘ r)(z)|_{T_zO} : T_zO = Dr(z)E → F` for the principal part `f̂` of a section. -/
def linAt (U : Set (E 0)) (R : E 0 × F 0 → E 0 × F 0) (fb : E 0 → F 0) (z : E 1) :
    ↥(rangeS (scDeriv U (r R) z)) →L[ℝ] F 0 :=
  (scDeriv U (fb ∘ r R) z).comp (rangeS (scDeriv U (r R) z)).subtypeL

@[simp] lemma linAt_apply (fb : E 0 → F 0) (z : E 1) (x : ↥(rangeS (scDeriv U (r R) z))) :
    linAt U R fb z x = scDeriv U (fb ∘ r R) z x := rfl

variable (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
include hU hR

/-- `Dr(z)` is idempotent at a level-`1` point of the retract. -/
theorem scDeriv_r_idem_at {z : E 1} (hzO : E.toBase 1 z ∈ r R '' U) (h : E 0) :
    scDeriv U (r R) z (scDeriv U (r R) z h) = scDeriv U (r R) z h :=
  congrArg (fun L : E 0 →L[ℝ] E 0 => L h)
    ((hR.baseRetraction hU).scDeriv_comp_self (x := z) hzO)

/-- **The values of `Lin(z)` lie in `K_z = ρ(z)F`** at a zero `z` of `f̂` (the text's
"`ρ(0)Tf(0) = Tf(0)`" before Definition 3.4, at any zero instead of the centre): differentiate
`ρ(r(u)) f̂(r(u)) = f̂(r(u))` at `z`; the derivative of the left side is `ρ(z) D(f̂ ∘ r)(z)`
because `(r(z), f̂(r(z))) = (z, 0)` and `ρ(u)0 = 0` (`scDeriv_fiber_of_vanishing`). -/
theorem rho_scDeriv_comp_r {fb : E 0 → F 0} (hfr : IsSc1 U (fb ∘ r R))
    (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ)) {z : E 1}
    (hzO : E.toBase 1 z ∈ r R '' U) (hfz : fb (E.toBase 1 z) = 0) (v : E 0) :
    ρCLM hR (mem_U_of_mem_O hR hzO) (scDeriv U (fb ∘ r R) z v) = scDeriv U (fb ∘ r R) z v := by
  have hzU : E.toBase 1 z ∈ U := mem_U_of_mem_O hR hzO
  have hz1 : z ∈ E.lvlSet U 1 := hzU
  have hUF := (hU.prod_univ F).isScDomain
  have hr1 : IsSc1 U (r R) := (r_isScSmooth hU hR).isSc1
  have hpair : IsSc1 U (scPair (r R) (fb ∘ r R)) := hr1.scPair' hfr
  have hmaps : MapsTo (scPair (r R) (fb ∘ r R)) U (U ×ˢ univ) := fun u hu =>
    ⟨r_mem hR hu, mem_univ _⟩
  set Ψ₂ := (fun p : (E.prod F) 0 => (R p).2) ∘ scPair (r R) (fb ∘ r R) with hΨ₂def
  have hΨ₂ : IsSc1 U Ψ₂ :=
    (theorem_1_21' hU.isScDomain hUF hpair (fiber_isSc1 hU hR) hmaps).1
  have heq : EqOn Ψ₂ (fb ∘ r R) U := by
    intro u hu
    exact ρ_eq_self_of_mem_K hR (r_mem hR hu) (hfK _ ⟨u, hu, rfl⟩)
  have hD : scDeriv U (fb ∘ r R) z = scDeriv U Ψ₂ z :=
    scDeriv_eq_of_eqOn_relOpen hU hfr hΨ₂ subset_rfl subset_rfl heq.symm hz1
  have hlev : levelMap (scPair (r R) (fb ∘ r R)) 1 z = ((z, 0) : (E.prod F) 1) := by
    apply levelMap_eq_of_toBase_eq
    rw [ScBanach.prod_toBase, map_zero]
    change (E.toBase 1 z, (0 : F 0)) = (r R (E.toBase 1 z), fb (r R (E.toBase 1 z)))
    rw [r_eq_self hR hzO, hfz]
  have hchain := scDeriv_comp_apply' hU (hU.prod_univ F) hpair (fiber_isSc1 hU hR) hmaps hz1 v
  rw [hlev, scDeriv_scPair hU hr1 hfr hz1, ContinuousLinearMap.prod_apply,
    scDeriv_fiber_of_vanishing hU (fiber_isSc1 hU hR) hz1 (fun u hu => ⟨hu, mem_univ _⟩)
      (fun k => ⟨hzU, mem_univ _⟩) (fun u hu => (ρ_isLinear hR hu).map_zero)
      (ρCLM hR hzU) (fun k => rfl)] at hchain
  rw [hchain, hD]

/-- **The bridge to fillers** (the text's "`Tg(0) = Tf(0)` on `T₀O`" before Definition 3.4, at
any point): if `g` agrees with `f̂` on `O` near the point `z` of the retract,
then `D(f̂ ∘ r)(z) = Dg(z) ∘ Dr(z)` (`g ∘ r = f̂ ∘ r` near `z`, uniqueness of the derivative and
the chain rule). -/
theorem scDeriv_comp_r_eq_of_eventuallyEq {fb g : E 0 → F 0} (hfr : IsSc1 U (fb ∘ r R))
    (hg : IsSc1 U g) {z : E 1} (hzO : E.toBase 1 z ∈ r R '' U)
    (heq : ∀ᶠ x in 𝓝 (E.toBase 1 z), x ∈ r R '' U → fb x = g x) (v : E 0) :
    scDeriv U (fb ∘ r R) z v = scDeriv U g z (scDeriv U (r R) z v) := by
  have hzU : E.toBase 1 z ∈ U := mem_U_of_mem_O hR hzO
  have hz1 : z ∈ E.lvlSet U 1 := hzU
  have hr1 : IsSc1 U (r R) := (r_isScSmooth hU hR).isSc1
  obtain ⟨W, hWsub, hWo, hzW⟩ := mem_nhds_iff.1 heq
  set Rb := hR.baseRetraction hU with hRb
  have hV : IsRelOpenInQuadrant E C (U ∩ r R ⁻¹' W) := Rb.relOpen_inter_preimage hWo
  have hgr : IsSc1 U (g ∘ r R) :=
    (theorem_1_21' hU.isScDomain hU.isScDomain hr1 hg fun u hu => r_mem hR hu).1
  have hzV : z ∈ E.lvlSet (U ∩ r R ⁻¹' W) 1 := by
    refine ⟨hzU, ?_⟩
    change r R (E.toBase 1 z) ∈ W
    rw [r_eq_self hR hzO]; exact hzW
  have hEq : EqOn (fb ∘ r R) (g ∘ r R) (U ∩ r R ⁻¹' W) := fun u hu =>
    hWsub hu.2 ⟨u, hu.1, rfl⟩
  have hD := scDeriv_eq_of_eqOn_relOpen hV hfr hgr inter_subset_left inter_subset_left hEq hzV
  have hlev : levelMap (r R) 1 z = z :=
    levelMap_eq_of_toBase_eq (by rw [r_eq_self hR hzO])
  have hchain := scDeriv_comp_apply' hU hU hr1 hg (fun u hu => r_mem hR hu) hz1 v
  rw [hlev] at hchain
  rw [hD, hchain]

/-- On `T_zO`, `Lin(z) = Dg(z)` for any `g` agreeing with `f̂` on `O` near `z`. -/
theorem linAt_eq_scDeriv {fb g : E 0 → F 0} (hfr : IsSc1 U (fb ∘ r R)) (hg : IsSc1 U g)
    {z : E 1} (hzO : E.toBase 1 z ∈ r R '' U)
    (heq : ∀ᶠ x in 𝓝 (E.toBase 1 z), x ∈ r R '' U → fb x = g x)
    (x : ↥(rangeS (scDeriv U (r R) z))) : linAt U R fb z x = scDeriv U g z x := by
  obtain ⟨_, w, rfl⟩ := x
  rw [linAt_apply, scDeriv_comp_r_eq_of_eventuallyEq hU hR hfr hg hzO heq]
  change scDeriv U g z (scDeriv U (r R) z (scDeriv U (r R) z w)) =
    scDeriv U g z (scDeriv U (r R) z w)
  rw [scDeriv_r_idem_at hU hR hzO]

end Lin

section LinFibre

variable {E F : ScBanach} {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

open StrongRetr

/-- `K_u = ρ(u)F` is the fibre `{k | (u, k) ∈ K}` of `K` over `u ∈ O`. -/
lemma mem_rangeS_ρCLM_iff (hR : IsStrongBundleRetraction U R) {u : E 0} (huO : u ∈ r R '' U)
    (hu : u ∈ U) {k : F 0} : k ∈ rangeS (ρCLM hR hu) ↔ (u, k) ∈ R '' (U ×ˢ univ) := by
  constructor
  · rintro ⟨k₀, rfl⟩
    refine ⟨(u, k₀), ⟨hu, mem_univ _⟩, ?_⟩
    rw [apply_eq hR hu, r_eq_self hR huO]; rfl
  · intro hk
    exact ⟨k, ρ_eq_self_of_mem_K hR hu hk⟩


/-- **At a central zero, `Lin(0)` is the `Tf̃(0)` of the filler** (`fillerRestrict` of
`FillerLinearAlgebra.lean`, Proposition 3.5): for a filled version `g` of `f̂`,
`Tf̃(0)x = Dg(0)x = Lin(0)x` on `T₀O`. -/
theorem IsFilledVersion.fillerRestrict_eq_linAt (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) {h0 : (0 : E 0) ∈ U} (h0O : (0 : E 0) ∈ r R '' U)
    {fb g : E 0 → F 0} (hfill : IsFilledVersion hU hR h0 fb g) (hfr : IsSc1 U (fb ∘ r R))
    (h1 : ∀ x, ρCLM hR h0 (scDeriv U g 0 (scDeriv U (r R) 0 x)) =
      scDeriv U g 0 (scDeriv U (r R) 0 x))
    (x : ↥(rangeS (scDeriv U (r R) 0))) :
    (fillerRestrict (scDeriv U (r R) 0) (ρCLM hR h0) (scDeriv U g 0) h1 x : F 0) =
      linAt U R fb 0 x := by
  rw [fillerRestrict_apply, linAt_eq_scDeriv hU hR hfr hfill.isScSmooth.isSc1
    (by rw [map_zero]; exact h0O) (by rw [map_zero]; exact hfill.filler.eq_on)]

end LinFibre

/-- A point of the overlap `φ(V ∩ V')` is mapped by `φ⁻¹` into `V'`. -/
lemma MChart.symm_mem_of_mem_overlap {X : Type u} [TopologicalSpace X] (φ ψ : MChart X)
    {x : φ.model.E 0} (hx : x ∈ φ.overlap ψ) : φ.symm x ∈ ψ.source := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [φ.symm_apply_apply hy.1]; exact hy.2

/-! ### The fibres of a strong bundle chart and of a transition map -/

section ChartFibres

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

namespace StrongBundleChart

variable (c c' : StrongBundleChart PX P)

open StrongRetr

/-- The base point of a point of `K` lies in `O`. -/
lemma fst_mem_O {p : c.φ.model.E 0 × c.F 0} (hp : p ∈ c.K) : p.1 ∈ c.φ.model.O := by
  have := ((c.isRetraction.mem_image_iff c.relOpen).1 hp).1
  rwa [c.base_retract] at this

/-- `Φ⁻¹` maps `K` into `P⁻¹(V)`. -/
lemma symm_mem_source {p : c.φ.model.E 0 × c.F 0} (hp : p ∈ c.K) :
    c.toPartialEquiv.symm p ∈ c.toPartialEquiv.source :=
  c.toPartialEquiv.map_target (by rw [c.target_eq]; exact hp)

/-- `Φ(Φ⁻¹(p)) = p` on `K`. -/
lemma apply_symm {p : c.φ.model.E 0 × c.F 0} (hp : p ∈ c.K) :
    c (c.toPartialEquiv.symm p) = p :=
  c.toPartialEquiv.right_inv (by rw [c.target_eq]; exact hp)

/-- `P(Φ⁻¹(x, h)) = φ⁻¹(x)` for `(x, h) ∈ K`. -/
lemma proj_symm {p : c.φ.model.E 0 × c.F 0} (hp : p ∈ c.K) :
    P (c.toPartialEquiv.symm p) = c.φ.symm p.1 := by
  have hs := c.symm_mem_source hp
  have h1 := c.covers _ hs
  rw [c.apply_symm hp] at h1
  have hPV : P (c.toPartialEquiv.symm p) ∈ c.φ.source := by
    have := hs; rw [c.source_eq] at this; exact this
  rw [h1, c.φ.symm_apply_apply hPV]

/-- The fibre of `K` over `u ∈ O` is closed under scalar multiplication. -/
lemma smul_mem_K {u : c.φ.model.E 0} {a : c.F 0} (ha : (u, a) ∈ c.K) (t : ℝ) :
    (u, t • a) ∈ c.K := by
  have hR := c.isRetraction
  rw [StrongBundleChart.K, hR.mem_image_iff c.relOpen] at ha ⊢
  refine ⟨ha.1, ?_⟩
  have huU : u ∈ c.U := (hR.baseRetraction c.relOpen).retract_subset ha.1
  change (c.R (u, t • a)).2 = t • a
  rw [(hR.fiber_linear u huU).map_smul]
  exact congrArg (t • ·) ha.2

/-- `(u, ρ(u)k) = R(u, k) ∈ K` for `u ∈ O`. -/
lemma mem_K_ρ {u : c.φ.model.E 0} (hu : u ∈ c.φ.model.O) (k : c.F 0) :
    (u, ρ c.R u k) ∈ c.K := by
  have huO : u ∈ r c.R '' c.U := by rw [c.r_image]; exact hu
  have huU : u ∈ c.U := mem_U_of_mem_O c.isRetraction huO
  have : c.R (u, k) = (u, ρ c.R u k) := by
    rw [apply_eq c.isRetraction huU, r_eq_self c.isRetraction huO]
  rw [← this]
  exact ⟨(u, k), ⟨huU, mem_univ _⟩, rfl⟩

/-- The fibre of `Φ⁻¹` over `x ∈ O`: the element of `P⁻¹(φ⁻¹(x))` with `Φ`-image `(x, a)`. -/
def fiberSymm {x : c.φ.model.E 0} {a : c.F 0} (ha : (x, a) ∈ c.K) : P ⁻¹' {c.φ.symm x} :=
  ⟨c.toPartialEquiv.symm (x, a), c.proj_symm ha⟩

lemma fiberSymm_coe {x : c.φ.model.E 0} {a : c.F 0} (ha : (x, a) ∈ c.K) :
    ((c.fiberSymm ha : P ⁻¹' {c.φ.symm x}) : Y) = c.toPartialEquiv.symm (x, a) := rfl

/-- `Φ⁻¹(x, ·)` is additive on the fibre of `K` over `x`. -/
lemma symm_add {x : c.φ.model.E 0} {a b : c.F 0} (ha : (x, a) ∈ c.K) (hb : (x, b) ∈ c.K) :
    c.toPartialEquiv.symm (x, a + b) =
      ((c.fiberSymm ha + c.fiberSymm hb : P ⁻¹' {c.φ.symm x}) : Y) := by
  have hxO := c.fst_mem_O ha
  have hxV : c.φ.symm x ∈ c.φ.source := c.φ.symm_mapsTo hxO
  set w : P ⁻¹' {c.φ.symm x} := c.fiberSymm ha + c.fiberSymm hb
  have hw : (w : Y) ∈ c.toPartialEquiv.source :=
    c.mem_source_of_proj (by rw [show P (w : Y) = c.φ.symm x from w.2]; exact hxV)
  have hcw : c (w : Y) = (x, a + b) := by
    refine Prod.ext ?_ ?_
    · rw [c.fst_apply (by rw [show P (w : Y) = c.φ.symm x from w.2]; exact hxV),
        show P (w : Y) = c.φ.symm x from w.2, c.φ.apply_symm_apply hxO]
    · rw [c.snd_add hxV, c.fiberSymm_coe, c.fiberSymm_coe, c.apply_symm ha, c.apply_symm hb]
  rw [← hcw, c.toPartialEquiv.left_inv hw]

/-- `Φ⁻¹(x, ·)` is homogeneous on the fibre of `K` over `x`. -/
lemma symm_smul {x : c.φ.model.E 0} {a : c.F 0} (ha : (x, a) ∈ c.K) (t : ℝ) :
    c.toPartialEquiv.symm (x, t • a) = ((t • c.fiberSymm ha : P ⁻¹' {c.φ.symm x}) : Y) := by
  have hxO := c.fst_mem_O ha
  have hxV : c.φ.symm x ∈ c.φ.source := c.φ.symm_mapsTo hxO
  set w : P ⁻¹' {c.φ.symm x} := t • c.fiberSymm ha
  have hw : (w : Y) ∈ c.toPartialEquiv.source :=
    c.mem_source_of_proj (by rw [show P (w : Y) = c.φ.symm x from w.2]; exact hxV)
  have hcw : c (w : Y) = (x, t • a) := by
    refine Prod.ext ?_ ?_
    · rw [c.fst_apply (by rw [show P (w : Y) = c.φ.symm x from w.2]; exact hxV),
        show P (w : Y) = c.φ.symm x from w.2, c.φ.apply_symm_apply hxO]
    · change (c ((t • c.fiberSymm ha : P ⁻¹' {c.φ.symm x}) : Y)).2 = t • a
      rw [(c.fiber_linear _ hxV).map_smul, c.fiberSymm_coe, c.apply_symm ha]
  rw [← hcw, c.toPartialEquiv.left_inv hw]

/-- The transition `Φ' ∘ Φ⁻¹` covers the base transition: `(Φ'Φ⁻¹(x, a))₁ = φ'φ⁻¹(x)`. -/
lemma transition_fst {x : c.φ.model.E 0} {a : c.F 0} (ha : (x, a) ∈ c.K)
    (hxV' : c.φ.symm x ∈ c'.φ.source) :
    (c.transition c' (x, a)).1 = c.φ.transition c'.φ x := by
  have hP := c.proj_symm ha
  change (c' (c.toPartialEquiv.symm (x, a))).1 = c'.φ (c.φ.symm x)
  rw [c'.fst_apply (by rw [hP]; exact hxV'), hP]

/-- **The transition is linear on the fibres**: additivity. -/
lemma transition_snd_add {x : c.φ.model.E 0} {a b : c.F 0} (ha : (x, a) ∈ c.K)
    (hb : (x, b) ∈ c.K) (hxV' : c.φ.symm x ∈ c'.φ.source) :
    (c.transition c' (x, a + b)).2 = (c.transition c' (x, a)).2 + (c.transition c' (x, b)).2 := by
  change (c' (c.toPartialEquiv.symm (x, a + b))).2 = (c' (c.toPartialEquiv.symm (x, a))).2 +
    (c' (c.toPartialEquiv.symm (x, b))).2
  rw [c.symm_add ha hb, c'.snd_add hxV', c.fiberSymm_coe, c.fiberSymm_coe]

/-- **The transition is linear on the fibres**: homogeneity. -/
lemma transition_snd_smul {x : c.φ.model.E 0} {a : c.F 0} (ha : (x, a) ∈ c.K)
    (hxV' : c.φ.symm x ∈ c'.φ.source) (t : ℝ) :
    (c.transition c' (x, t • a)).2 = t • (c.transition c' (x, a)).2 := by
  change (c' (c.toPartialEquiv.symm (x, t • a))).2 = t • (c' (c.toPartialEquiv.symm (x, a))).2
  rw [c.symm_smul ha t]
  rw [(c'.fiber_linear _ hxV').map_smul, c.fiberSymm_coe]

/-- The transition maps the zero section to the zero section. -/
lemma transition_snd_zero {x : c.φ.model.E 0} (hx0 : (x, (0 : c.F 0)) ∈ c.K)
    (hxV' : c.φ.symm x ∈ c'.φ.source) : (c.transition c' (x, 0)).2 = 0 := by
  have := c.transition_snd_add c' hx0 hx0 hxV'
  have h2 : (c.transition c' (x, 0)).2 + (c.transition c' (x, 0)).2 =
      (c.transition c' (x, 0)).2 + 0 := by rw [add_zero, ← this, add_zero]
  exact add_left_cancel h2

/-- The transition maps `K` (over the overlap) into `K'`. -/
lemma transition_mem_K {x : c.φ.model.E 0} {a : c.F 0} (ha : (x, a) ∈ c.K)
    (hxV' : c.φ.symm x ∈ c'.φ.source) : c.transition c' (x, a) ∈ c'.K := by
  have hP := c.proj_symm ha
  rw [← c'.image_source]
  exact ⟨_, c'.mem_source_of_proj (by rw [hP]; exact hxV'), rfl⟩

/-- The reverse transition inverts the transition. -/
lemma transition_transition {x : c.φ.model.E 0} {a : c.F 0} (ha : (x, a) ∈ c.K)
    (hxV' : c.φ.symm x ∈ c'.φ.source) : c'.transition c (c.transition c' (x, a)) = (x, a) := by
  have hP := c.proj_symm ha
  change c (c'.toPartialEquiv.symm (c' (c.toPartialEquiv.symm (x, a)))) = (x, a)
  rw [c'.toPartialEquiv.left_inv (c'.mem_source_of_proj (by rw [hP]; exact hxV')), c.apply_symm ha]

/-- The fibre map `Γ(x) = (Φ'Φ⁻¹(x, ρ(x)·))₂ : F → F'` of the transition over a point `x` of the
base overlap, a bounded operator (composition of continuous maps, linear on the fibre of `K`). -/
def transitionFiberCLM {x : c.φ.model.E 0} (hxO : x ∈ c.φ.model.O)
    (hxV' : c.φ.symm x ∈ c'.φ.source) : c.F 0 →L[ℝ] c'.F 0 where
  toFun k := (c.transition c' (x, ρ c.R x k)).2
  map_add' a b := by
    have hxU : x ∈ c.U := mem_U_of_mem_O c.isRetraction (by rw [c.r_image]; exact hxO)
    rw [(ρ_isLinear c.isRetraction hxU).map_add]
    exact c.transition_snd_add c' (c.mem_K_ρ hxO a) (c.mem_K_ρ hxO b) hxV'
  map_smul' t a := by
    have hxU : x ∈ c.U := mem_U_of_mem_O c.isRetraction (by rw [c.r_image]; exact hxO)
    simp only [RingHom.id_apply]
    rw [(ρ_isLinear c.isRetraction hxU).map_smul]
    exact c.transition_snd_smul c' (c.mem_K_ρ hxO a) hxV' t
  cont := by
    have hxU : x ∈ c.U := mem_U_of_mem_O c.isRetraction (by rw [c.r_image]; exact hxO)
    have h1 : Continuous fun k : c.F 0 => ((x, ρ c.R x k) : c.φ.model.E 0 × c.F 0) :=
      continuous_const.prodMk (ρ_continuous c.isRetraction hxU)
    have h2 : Continuous fun k : c.F 0 => c.toPartialEquiv.symm (x, ρ c.R x k) :=
      c.continuousOn_invFun.comp_continuous h1 fun k => by
        rw [c.target_eq]; exact c.mem_K_ρ hxO k
    have h3 : Continuous fun k : c.F 0 => c' (c.toPartialEquiv.symm (x, ρ c.R x k)) :=
      c'.continuousOn_toFun.comp_continuous h2 fun k =>
        c'.mem_source_of_proj (by rw [c.proj_symm (c.mem_K_ρ hxO k)]; exact hxV')
    exact continuous_snd.comp h3

lemma transitionFiberCLM_apply {x : c.φ.model.E 0} (hxO : x ∈ c.φ.model.O)
    (hxV' : c.φ.symm x ∈ c'.φ.source) (k : c.F 0) :
    c.transitionFiberCLM c' hxO hxV' k = (c.transition c' (x, ρ c.R x k)).2 := rfl

/-- On the fibre `K_x = ρ(x)F`, `Γ(x)` is the transition itself. -/
lemma transitionFiberCLM_apply_of_mem {x : c.φ.model.E 0} (hxO : x ∈ c.φ.model.O)
    (hxV' : c.φ.symm x ∈ c'.φ.source) {k : c.F 0} (hk : (x, k) ∈ c.K) :
    c.transitionFiberCLM c' hxO hxV' k = (c.transition c' (x, k)).2 := by
  have hxU : x ∈ c.U := mem_U_of_mem_O c.isRetraction (by rw [c.r_image]; exact hxO)
  rw [transitionFiberCLM_apply, ρ_eq_self_of_mem_K c.isRetraction hxU hk]

/-- The overlap `Φ(P⁻¹(V ∩ V'))` is `K ∩ (W × F)` when `φ(V ∩ V') = O ∩ W`. -/
lemma overlap_eq_inter_prod {W : Set (c.φ.model.E 0)} (hW : c.φ.overlap c'.φ = c.φ.model.O ∩ W) :
    c.overlap c' = c.K ∩ (W ×ˢ univ) := by
  ext p
  constructor
  · rintro ⟨η, ⟨hη, hη'⟩, rfl⟩
    refine ⟨by rw [← c.image_source]; exact ⟨η, hη, rfl⟩, ?_, mem_univ _⟩
    have hPV : P η ∈ c.φ.source := by rw [c.source_eq] at hη; exact hη
    have hPV' : P η ∈ c'.φ.source := by rw [c'.source_eq] at hη'; exact hη'
    have : (c η).1 ∈ c.φ.overlap c'.φ := by
      rw [c.covers η hη]; exact c.φ.mem_overlap c'.φ hPV hPV'
    rw [hW] at this
    exact this.2
  · rintro ⟨hpK, hpW, -⟩
    have hp1 : p.1 ∈ c.φ.overlap c'.φ := by rw [hW]; exact ⟨c.fst_mem_O hpK, hpW⟩
    obtain ⟨y₁, ⟨hy₁, hy₁'⟩, hy₁p⟩ := hp1
    refine ⟨c.toPartialEquiv.symm p, ⟨c.symm_mem_source hpK, ?_⟩, c.apply_symm hpK⟩
    refine c'.mem_source_of_proj ?_
    rw [c.proj_symm hpK, ← hy₁p, c.φ.symm_apply_apply hy₁]
    exact hy₁'

end StrongBundleChart

end ChartFibres

section ChartChange

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {f : X → Y}

open StrongRetr

/-- **The chart independence of the linearization at a zero** (the local form of Definition 2.38
and gap G.13 for Definition 3.53).  Let `c`, `c'` be strong bundle charts whose transition
`Θ = Φ' ∘ Φ⁻¹` is sc-smooth on `[0]` (part of the compatibility of Definition 2.50), `f` a section
whose principal parts are sc-smooth in both charts, `y` a zero of `f` in both domains and
`z = φ(y)`, `z' = φ'(y)` on level `1`.  Then there are topological linear isomorphisms
`A : T_zO = Dr(z)E ≅ T_{z'}O' = Dr'(z')E'` (the derivative `D(τ ∘ r)(z)` of the base transition
`τ = φ' ∘ φ⁻¹`, inverse `D(τ' ∘ r')(z')`) and `Γ : K_z = ρ(z)F ≅ K'_{z'} = ρ'(z')F'` (the fibre part
of `Θ` over `z`) with
* `Γ ∘ Lin(z) = Lin'(z') ∘ A` for the linearizations `Lin(z) = D(f̂ ∘ r)(z)|_{T_zO}`
  (`linAt`): the chain rule for `u ↦ Θ(r(u), f̂(r(u)))₂ = f̂'(τ(r(u)))`, in which the derivative
  in the base direction drops out because `Θ(x, 0) = (τ(x), 0)` and `f̂(z) = 0`;
* `A` carries the partial cone `C_zO = T_zO ∩ C_z` onto `C_{z'}O' = T_{z'}O' ∩ C'_{z'}`
  (Proposition 2.30, `proposition_2_30_cone`, for the base transition). -/
theorem linAt_chart_change (c c' : StrongBundleChart PX P) (hf : IsSection P f)
    (hΘ : IsScSmoothRetractMap (c.φ.model.E.prod c.F) (c.φ.model.C ×ˢ univ) (c.overlap c')
      (c'.φ.model.E.prod c'.F) (c'.φ.model.C ×ˢ univ) (c'.overlap c) (c.transition c'))
    (hfc : IsScSmoothRetractMap c.φ.model.E c.φ.model.C c.φ.model.O (c.φ.model.E.prod c.F)
      (c.φ.model.C ×ˢ univ) c.K (fun z => (z, c.principal f z)))
    (hfc' : IsScSmoothRetractMap c'.φ.model.E c'.φ.model.C c'.φ.model.O
      (c'.φ.model.E.prod c'.F) (c'.φ.model.C ×ˢ univ) c'.K (fun z => (z, c'.principal f z)))
    {y : X} (hyV : y ∈ c.φ.source) (hyV' : y ∈ c'.φ.source) (hy0 : IsZeroAt P f y)
    {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z = c.φ y)
    {z' : c'.φ.model.E 1} (hz' : c'.φ.model.E.toBase 1 z' = c'.φ y)
    (hzU : c.φ.model.E.toBase 1 z ∈ c.U) (hzU' : c'.φ.model.E.toBase 1 z' ∈ c'.U)
    {n n' : ℕ} {Wq Wq' : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant n Wq 0)
    (T' : ScIso c'.φ.model.E ((ScBanach.const (Fin n' → ℝ)).prod Wq'))
    (hT' : c'.φ.model.C = T' 0 ⁻¹' quadrant n' Wq' 0) :
    ∃ (A : ↥(rangeS (scDeriv c.U (r c.R) z)) ≃L[ℝ] ↥(rangeS (scDeriv c'.U (r c'.R) z')))
      (Γ : ↥(rangeS (ρCLM c.isRetraction hzU)) ≃L[ℝ] ↥(rangeS (ρCLM c'.isRetraction hzU'))),
      (∀ (x : ↥(rangeS (scDeriv c.U (r c.R) z))) (k : ↥(rangeS (ρCLM c.isRetraction hzU))),
        (k : c.F 0) = linAt c.U c.R (c.principal f) z x →
        (Γ k : c'.F 0) = linAt c'.U c'.R (c'.principal f) z' (A x)) ∧
      (∀ x : ↥(rangeS (scDeriv c.U (r c.R) z)),
        (x : c.φ.model.E 0) ∈ partialQuadrantAtWith T (c.φ.model.E.toBase 1 z) ↔
        (A x : c'.φ.model.E 0) ∈ partialQuadrantAtWith T' (c'.φ.model.E.toBase 1 z')) := by
  classical
  -- the base charts are compatible (both are charts of `X`)
  have hbase : c.φ.Compatible c'.φ := c.isChart.compatible c'.isChart (P := PX)
  obtain ⟨W, hWo, hW⟩ := c.φ.exists_isOpen_image_eq (s := c.φ.source ∩ c'.φ.source)
    inter_subset_left (c.φ.isOpen_source.inter c'.φ.isOpen_source)
  obtain ⟨W', hWo', hW'⟩ := c'.φ.exists_isOpen_image_eq (s := c'.φ.source ∩ c.φ.source)
    inter_subset_left (c'.φ.isOpen_source.inter c.φ.isOpen_source)
  set Rb := c.isRetraction.baseRetraction c.relOpen with hRb
  set Rb' := c'.isRetraction.baseRetraction c'.relOpen with hRb'
  set Rw := Rb.restrict hWo with hRwdef
  set Rw' := Rb'.restrict hWo' with hRw'def
  have hRw : Rw.retract = c.φ.overlap c'.φ := by
    rw [ScRetraction.restrict_retract, c.base_retract]; exact hW.symm
  have hRw' : Rw'.retract = c'.φ.overlap c.φ := by
    rw [ScRetraction.restrict_retract, c'.base_retract]; exact hW'.symm
  set τ := c.φ.transition c'.φ with hτdef
  set τ' := c'.φ.transition c.φ with hτ'def
  have hdiff : Rw.IsDiffeoGerm Rw' τ τ' :=
    { isSc1 := (hbase.1.comp_isScSmooth Rw hRw).isSc1
      isSc1_inv := (hbase.2.comp_isScSmooth Rw' hRw').isSc1
      mapsTo := by rw [hRw, hRw']; exact c.φ.transition_mapsTo c'.φ
      mapsTo_inv := by rw [hRw, hRw']; exact c'.φ.transition_mapsTo c.φ
      left_inv := by
        rw [hRw]; rintro _ ⟨y₁, hy₁, rfl⟩
        rw [hτdef, hτ'def, c.φ.transition_apply c'.φ hy₁.1, c'.φ.transition_apply c.φ hy₁.2]
      right_inv := by
        rw [hRw']; rintro _ ⟨y₁, hy₁, rfl⟩
        rw [hτdef, hτ'def, c'.φ.transition_apply c.φ hy₁.1, c.φ.transition_apply c'.φ hy₁.2] }
  -- the points
  have hyO : c.φ y ∈ c.φ.overlap c'.φ := c.φ.mem_overlap c'.φ hyV hyV'
  have hyO' : c'.φ y ∈ c'.φ.overlap c.φ := c'.φ.mem_overlap c.φ hyV' hyV
  have hx : z ∈ c.φ.model.E.lvlSet Rw.retract 1 := by
    rw [ScBanach.mem_lvlSet, hz, hRw]; exact hyO
  have hzO : c.φ.model.E.toBase 1 z ∈ r c.R '' c.U := by
    rw [hz, c.r_image]; exact c.φ.mapsTo_model y hyV
  have hzO' : c'.φ.model.E.toBase 1 z' ∈ r c'.R '' c'.U := by
    rw [hz', c'.r_image]; exact c'.φ.mapsTo_model y hyV'
  have hzOO : c.φ.model.E.toBase 1 z ∈ c.φ.model.O := by rw [hz]; exact c.φ.mapsTo_model y hyV
  have hzOO' : c'.φ.model.E.toBase 1 z' ∈ c'.φ.model.O := by
    rw [hz']; exact c'.φ.mapsTo_model y hyV'
  have hzV' : c.φ.symm (c.φ.model.E.toBase 1 z) ∈ c'.φ.source := by
    rw [hz, c.φ.symm_apply_apply hyV]; exact hyV'
  have hzV : c'.φ.symm (c'.φ.model.E.toBase 1 z') ∈ c.φ.source := by
    rw [hz', c'.φ.symm_apply_apply hyV']; exact hyV
  have hτz : τ (c.φ.model.E.toBase 1 z) = c'.φ.model.E.toBase 1 z' := by
    rw [hz, hτdef, c.φ.transition_apply c'.φ hyV, hz']
  have hτz' : τ' (c'.φ.model.E.toBase 1 z') = c.φ.model.E.toBase 1 z := by
    rw [hz', hτ'def, c'.φ.transition_apply c.φ hyV', hz]
  have hlev : levelMap (τ ∘ Rw) 1 z = z' := by
    apply levelMap_eq_of_toBase_eq
    change c'.φ.model.E.toBase 1 z' = τ (r c.R (c.φ.model.E.toBase 1 z))
    rw [r_eq_self c.isRetraction hzO, hτz]
  have hz1 : z ∈ c.φ.model.E.lvlSet Rw.U 1 := Rw.lvlSet_retract_subset 1 hx
  have hRwU : Rw.U ⊆ c.U := inter_subset_left
  have hRwU' : Rw'.U ⊆ c'.U := inter_subset_left
  have hx' : z' ∈ c'.φ.model.E.lvlSet Rw'.retract 1 := by rw [← hlev]; exact hdiff.image_mem hx
  have hz1' : z' ∈ c'.φ.model.E.lvlSet Rw'.U 1 := Rw'.lvlSet_retract_subset 1 hx'
  -- derivatives of `r`, `f̂ ∘ r` on the restricted domains
  have hr1 : IsSc1 c.U (r c.R) := (r_isScSmooth c.relOpen c.isRetraction).isSc1
  have hr1' : IsSc1 c'.U (r c'.R) := (r_isScSmooth c'.relOpen c'.isRetraction).isSc1
  have hDr : scDeriv Rw.U Rw z = scDeriv c.U (r c.R) z :=
    scDeriv_eq_of_eqOn_relOpen Rw.relOpen Rw.isSc1 hr1 subset_rfl hRwU (fun _ _ => rfl) hz1
  have hDr' : scDeriv Rw'.U Rw' z' = scDeriv c'.U (r c'.R) z' :=
    scDeriv_eq_of_eqOn_relOpen Rw'.relOpen Rw'.isSc1 hr1' subset_rfl hRwU' (fun _ _ => rfl) hz1'
  have hσsm : IsScSmooth c.U (scPair (r c.R) (c.principal f ∘ r c.R)) :=
    (hfc.comp_isScSmooth Rb c.base_retract).congr c.relOpen.isScDomain fun _ _ => rfl
  have hfr : IsSc1 c.U (c.principal f ∘ r c.R) :=
    ((hσsm.snd c.relOpen.isScDomain).congr c.relOpen.isScDomain fun _ _ => rfl).isSc1
  have hσsm' : IsScSmooth c'.U (scPair (r c'.R) (c'.principal f ∘ r c'.R)) :=
    (hfc'.comp_isScSmooth Rb' c'.base_retract).congr c'.relOpen.isScDomain fun _ _ => rfl
  have hfr' : IsSc1 c'.U (c'.principal f ∘ r c'.R) :=
    ((hσsm'.snd c'.relOpen.isScDomain).congr c'.relOpen.isScDomain fun _ _ => rfl).isSc1
  have hrRw : IsSc1 Rw.U (r c.R) := hr1.of_subset hRwU
  have hfrRw : IsSc1 Rw.U (c.principal f ∘ r c.R) := hfr.of_subset hRwU
  have hDfr : scDeriv Rw.U (c.principal f ∘ r c.R) z = scDeriv c.U (c.principal f ∘ r c.R) z :=
    scDeriv_eq_of_eqOn_relOpen Rw.relOpen hfrRw hfr subset_rfl hRwU (fun _ _ => rfl) hz1
  -- the retraction onto the overlap of `K` and the transition `Θ`
  set RK := (c.isRetraction.toScRetraction c.relOpen).restrict (hWo.prod isOpen_univ) with hRKdef
  have hRK : RK.retract = c.overlap c' := by
    rw [ScRetraction.restrict_retract]; exact (c.overlap_eq_inter_prod c' hW).symm
  have hRKapp : ∀ p, RK p = c.R p := fun _ => rfl
  have hΘs : IsScSmooth (F := c'.φ.model.E.prod c'.F) RK.U (c.transition c' ∘ RK) :=
    hΘ.comp_isScSmooth RK hRK
  set Φ : (c.φ.model.E.prod c.F) 0 → c'.F 0 := fun p => ((c.transition c' ∘ RK) p).2 with hΦdef
  have hΦ : IsSc1 RK.U Φ := (hΘs.snd RK.isScDomain).isSc1
  -- the fibre operator `Γ(z)` and the vanishing of `Φ` on the zero section
  set Γt := c.transitionFiberCLM c' hzOO hzV' with hΓt
  have hzW : c.φ.model.E.toBase 1 z ∈ W := by
    have : c.φ.model.E.toBase 1 z ∈ c.φ.model.O ∩ W := by rw [← hW, hz]; exact hyO
    exact this.2
  have hRz : ∀ k, c.R (c.φ.model.E.toBase 1 z, k) =
      (c.φ.model.E.toBase 1 z, ρ c.R (c.φ.model.E.toBase 1 z) k) := fun k => by
    rw [apply_eq c.isRetraction hzU, r_eq_self c.isRetraction hzO]
  have hzD : ∀ k : c.F 0, ((c.φ.model.E.toBase 1 z, k) : (c.φ.model.E.prod c.F) 0) ∈ RK.U :=
    fun k => ⟨⟨hzU, mem_univ _⟩, by
      change c.R (c.φ.model.E.toBase 1 z, k) ∈ W ×ˢ univ
      rw [hRz]; exact ⟨hzW, mem_univ _⟩⟩
  have hSD : ∀ u ∈ Rw.U, ((u, 0) : (c.φ.model.E.prod c.F) 0) ∈ RK.U := fun u hu =>
    ⟨⟨hu.1, mem_univ _⟩, ⟨hu.2, mem_univ _⟩⟩
  have hΓ : ∀ k, Φ (c.φ.model.E.toBase 1 z, k) = Γt k := fun k => by
    rw [hΓt, StrongBundleChart.transitionFiberCLM_apply]
    change (c.transition c' (c.R (c.φ.model.E.toBase 1 z, k))).2 = _
    rw [hRz]
  have hzero : ∀ u ∈ Rw.U, Φ (u, 0) = 0 := by
    intro u hu
    have hru : r c.R u ∈ c.φ.overlap c'.φ := by rw [← hRw]; exact Rw.apply_mem_retract hu
    have hR0 : c.R (u, 0) = (r c.R u, 0) := by
      rw [apply_eq c.isRetraction hu.1, (ρ_isLinear c.isRetraction hu.1).map_zero]
    have hK0 : (r c.R u, (0 : c.F 0)) ∈ c.K := by
      rw [← hR0]; exact ⟨(u, 0), ⟨hu.1, mem_univ _⟩, rfl⟩
    change (c.transition c' (c.R (u, 0))).2 = 0
    rw [hR0]
    exact c.transition_snd_zero c' hK0 (c.φ.symm_mem_of_mem_overlap c'.φ hru)
  -- the section in the chart and the main identity
  set σ := scPair (r c.R) (c.principal f ∘ r c.R) with hσdef
  have hσmem : ∀ u ∈ Rw.U, ∃ y₁, y₁ ∈ c.φ.source ∧ y₁ ∈ c'.φ.source ∧ r c.R u = c.φ y₁ ∧
      σ u = c (f y₁) ∧ σ u ∈ RK.retract := by
    intro u hu
    have hru : r c.R u ∈ c.φ.overlap c'.φ := by rw [← hRw]; exact Rw.apply_mem_retract hu
    obtain ⟨y₁, ⟨hy₁, hy₁'⟩, hy₁u⟩ := hru
    have hσu : σ u = c (f y₁) := by
      change (r c.R u, c.principal f (r c.R u)) = c (f y₁)
      rw [← hy₁u, c.apply_section' hf hy₁]
    refine ⟨y₁, hy₁, hy₁', hy₁u.symm, hσu, ?_⟩
    rw [hRK, hσu]
    exact ⟨f y₁, ⟨c.mem_source_of_proj (by rw [hf]; exact hy₁),
      c'.mem_source_of_proj (by rw [hf]; exact hy₁')⟩, rfl⟩
  have hmapsσ : MapsTo σ Rw.U RK.U := fun u hu => by
    obtain ⟨-, -, -, -, -, h⟩ := hσmem u hu
    exact RK.retract_subset h
  have hσ1 : IsSc1 Rw.U σ := (hσsm.of_subset Rw.isScDomain hRwU).isSc1
  have hEq : EqOn ((c'.principal f ∘ r c'.R) ∘ (τ ∘ Rw)) (Φ ∘ σ) Rw.U := by
    intro u hu
    obtain ⟨y₁, hy₁, hy₁', hru, hσu, hσK⟩ := hσmem u hu
    have hτu : τ (r c.R u) = c'.φ y₁ := by rw [hru, hτdef, c.φ.transition_apply c'.φ hy₁]
    have hr' : r c'.R (c'.φ y₁) = c'.φ y₁ :=
      r_eq_self c'.isRetraction (by rw [c'.r_image]; exact c'.φ.mapsTo_model y₁ hy₁')
    change c'.principal f (r c'.R (τ (r c.R u))) = (c.transition c' (RK (σ u))).2
    rw [RK.apply_eq_self_of_mem_retract hσK, hσu]
    change _ = (c' (c.toPartialEquiv.symm (c (f y₁)))).2
    rw [c.toPartialEquiv.left_inv (c.mem_source_of_proj (by rw [hf]; exact hy₁)),
      c'.apply_section' hf hy₁', hτu, hr']
  have hmapsτ : MapsTo (τ ∘ Rw) Rw.U c'.U := fun u hu => (hdiff.mapsTo_U hu).1
  have hℓ : IsSc1 Rw.U ((c'.principal f ∘ r c'.R) ∘ (τ ∘ Rw)) :=
    (theorem_1_21' Rw.isScDomain c'.relOpen.isScDomain hdiff.isSc1 hfr' hmapsτ).1
  have hΦσ : IsSc1 Rw.U (Φ ∘ σ) :=
    (theorem_1_21' Rw.isScDomain RK.isScDomain hσ1 hΦ hmapsσ).1
  have hDeq : scDeriv Rw.U ((c'.principal f ∘ r c'.R) ∘ (τ ∘ Rw)) z = scDeriv Rw.U (Φ ∘ σ) z :=
    scDeriv_eq_of_eqOn_relOpen Rw.relOpen hℓ hΦσ subset_rfl subset_rfl hEq hz1
  have hfz : c.principal f (c.φ.model.E.toBase 1 z) = 0 := by
    rw [hz]; exact (c.isZeroAt_iff hf hyV).1 hy0
  have hlevσ : levelMap σ 1 z = ((z, 0) : (c.φ.model.E.prod c.F) 1) := by
    apply levelMap_eq_of_toBase_eq
    rw [ScBanach.prod_toBase, map_zero]
    change (c.φ.model.E.toBase 1 z, (0 : c.F 0)) =
      (r c.R (c.φ.model.E.toBase 1 z), c.principal f (r c.R (c.φ.model.E.toBase 1 z)))
    rw [r_eq_self c.isRetraction hzO, hfz]
  have key : ∀ v, scDeriv c'.U (c'.principal f ∘ r c'.R) z' (scDeriv Rw.U (τ ∘ Rw) z v) =
      Γt (scDeriv c.U (c.principal f ∘ r c.R) z v) := by
    intro v
    have h1 := scDeriv_comp_apply' Rw.relOpen c'.relOpen hdiff.isSc1 hfr' hmapsτ hz1 v
    rw [hlev] at h1
    have h2 := scDeriv_comp_apply' Rw.relOpen RK.relOpen hσ1 hΦ hmapsσ hz1 v
    rw [hlevσ, hσdef, scDeriv_scPair Rw.relOpen hrRw hfrRw hz1, ContinuousLinearMap.prod_apply,
      scDeriv_fiber_of_vanishing Rw.relOpen hΦ hz1 hSD hzD hzero Γt hΓ] at h2
    rw [h1, hDeq, ← h2, hDfr]
  -- the isomorphism `A` of the tangent spaces (Proposition 2.30)
  set A₀ := scDeriv Rw.U (τ ∘ Rw) z with hA₀
  set A₀' := scDeriv Rw'.U (τ' ∘ Rw') z' with hA₀'
  have hTA : ∀ v ∈ rangeS (scDeriv c.U (r c.R) z), A₀ v ∈ rangeS (scDeriv c'.U (r c'.R) z') := by
    rintro _ ⟨w, rfl⟩
    have := hdiff.deriv_mem_range hx (v := scDeriv c.U (r c.R) z w) (by rw [hDr]; exact ⟨w, rfl⟩)
    rw [hlev, hDr'] at this
    obtain ⟨u, hu⟩ := this
    exact ⟨u, hu⟩
  have himg : levelMap (τ' ∘ Rw') 1 z' = z := by rw [← hlev]; exact hdiff.image_image hx
  have hTA' : ∀ w ∈ rangeS (scDeriv c'.U (r c'.R) z'), A₀' w ∈ rangeS (scDeriv c.U (r c.R) z) := by
    rintro _ ⟨u, rfl⟩
    have := hdiff.symm.deriv_mem_range hx' (v := scDeriv c'.U (r c'.R) z' u)
      (by rw [hDr']; exact ⟨u, rfl⟩)
    rw [himg, hDr] at this
    obtain ⟨w, hw⟩ := this
    exact ⟨w, hw⟩
  have hinv1 : ∀ v ∈ rangeS (scDeriv c.U (r c.R) z), A₀' (A₀ v) = v := by
    rintro _ ⟨w, rfl⟩
    have := hdiff.deriv_inv_deriv hx (scDeriv c.U (r c.R) z w)
    rw [hlev, hDr] at this
    change A₀' (A₀ (scDeriv c.U (r c.R) z w)) = _
    rw [this]
    exact scDeriv_r_idem_at c.relOpen c.isRetraction hzO w
  have hinv2 : ∀ w ∈ rangeS (scDeriv c'.U (r c'.R) z'), A₀ (A₀' w) = w := by
    rintro _ ⟨u, rfl⟩
    have := hdiff.deriv_deriv_inv hx (scDeriv c'.U (r c'.R) z' u)
    rw [hlev, hDr'] at this
    change A₀ (A₀' (scDeriv c'.U (r c'.R) z' u)) = _
    rw [this]
    exact scDeriv_r_idem_at c'.relOpen c'.isRetraction hzO' u
  set A := restrictEquiv _ _ A₀ A₀' hTA hTA' hinv1 hinv2 with hAdef
  -- the isomorphism `Γ` of the fibres
  set Γt' := c'.transitionFiberCLM c hzOO' hzV with hΓt'
  have hKz : ∀ k ∈ rangeS (ρCLM c.isRetraction hzU), (c.φ.model.E.toBase 1 z, k) ∈ c.K := by
    rintro _ ⟨k₀, rfl⟩
    exact c.mem_K_ρ hzOO k₀
  have hKz' : ∀ k ∈ rangeS (ρCLM c'.isRetraction hzU'), (c'.φ.model.E.toBase 1 z', k) ∈ c'.K := by
    rintro _ ⟨k₀, rfl⟩
    exact c'.mem_K_ρ hzOO' k₀
  have hΘz : ∀ k, (c.φ.model.E.toBase 1 z, k) ∈ c.K →
      c.transition c' (c.φ.model.E.toBase 1 z, k) =
        (c'.φ.model.E.toBase 1 z', (c.transition c' (c.φ.model.E.toBase 1 z, k)).2) := by
    intro k hk
    refine Prod.ext ?_ rfl
    rw [c.transition_fst c' hk hzV']
    exact hτz
  have hΘz' : ∀ k, (c'.φ.model.E.toBase 1 z', k) ∈ c'.K →
      c'.transition c (c'.φ.model.E.toBase 1 z', k) =
        (c.φ.model.E.toBase 1 z, (c'.transition c (c'.φ.model.E.toBase 1 z', k)).2) := by
    intro k hk
    refine Prod.ext ?_ rfl
    rw [c'.transition_fst c hk hzV]
    exact hτz'
  have hΓK : ∀ k ∈ rangeS (ρCLM c.isRetraction hzU),
      (c'.φ.model.E.toBase 1 z', Γt k) ∈ c'.K := by
    intro k hk
    rw [hΓt, c.transitionFiberCLM_apply_of_mem c' hzOO hzV' (hKz k hk), ← hΘz k (hKz k hk)]
    exact c.transition_mem_K c' (hKz k hk) hzV'
  have hΓK' : ∀ k ∈ rangeS (ρCLM c'.isRetraction hzU'),
      (c.φ.model.E.toBase 1 z, Γt' k) ∈ c.K := by
    intro k hk
    rw [hΓt', c'.transitionFiberCLM_apply_of_mem c hzOO' hzV (hKz' k hk), ← hΘz' k (hKz' k hk)]
    exact c'.transition_mem_K c (hKz' k hk) hzV
  have hΓmem : ∀ k ∈ rangeS (ρCLM c.isRetraction hzU), Γt k ∈ rangeS (ρCLM c'.isRetraction hzU') :=
    fun k hk => ⟨Γt k, ρ_eq_self_of_mem_K c'.isRetraction hzU' (hΓK k hk)⟩
  have hΓmem' : ∀ k ∈ rangeS (ρCLM c'.isRetraction hzU'),
      Γt' k ∈ rangeS (ρCLM c.isRetraction hzU) :=
    fun k hk => ⟨Γt' k, ρ_eq_self_of_mem_K c.isRetraction hzU (hΓK' k hk)⟩
  have hΓinv1 : ∀ k ∈ rangeS (ρCLM c.isRetraction hzU), Γt' (Γt k) = k := by
    intro k hk
    rw [hΓt', c'.transitionFiberCLM_apply_of_mem c hzOO' hzV (hΓK k hk), hΓt,
      c.transitionFiberCLM_apply_of_mem c' hzOO hzV' (hKz k hk), ← hΘz k (hKz k hk),
      c.transition_transition c' (hKz k hk) hzV']
  have hΓinv2 : ∀ k ∈ rangeS (ρCLM c'.isRetraction hzU'), Γt (Γt' k) = k := by
    intro k hk
    rw [hΓt, c.transitionFiberCLM_apply_of_mem c' hzOO hzV' (hΓK' k hk), hΓt',
      c'.transitionFiberCLM_apply_of_mem c hzOO' hzV (hKz' k hk), ← hΘz' k (hKz' k hk),
      c'.transition_transition c (hKz' k hk) hzV]
  set Γ := restrictEquiv _ _ Γt Γt' hΓmem hΓmem' hΓinv1 hΓinv2 with hΓdef
  refine ⟨A, Γ, fun x k hk => ?_, fun x => ?_⟩
  · -- `Γ ∘ Lin(z) = Lin'(z') ∘ A`
    rw [hΓdef, restrictEquiv_apply, hk, hAdef, linAt_apply, linAt_apply, restrictEquiv_apply]
    exact (key x).symm
  · -- the partial cones (Proposition 2.30)
    have hcone := proposition_2_30_cone hdiff hx T hT T' hT'
    rw [hlev] at hcone
    simp only [partialConeWith] at hcone
    rw [hDr, hDr'] at hcone
    have hxT : (x : c.φ.model.E 0) ∈ range (scDeriv c.U (r c.R) z) := by
      obtain ⟨w, hw⟩ := x.2; exact ⟨w, hw⟩
    rw [hAdef, restrictEquiv_apply]
    constructor
    · intro hxC
      have : A₀ x ∈ A₀ '' (range (scDeriv c.U (r c.R) z) ∩
          partialQuadrantAtWith T (c.φ.model.E.toBase 1 z)) := ⟨x, ⟨hxT, hxC⟩, rfl⟩
      rw [hcone] at this
      exact this.2
    · intro hAxC
      have hAxT : A₀ x ∈ range (scDeriv c'.U (r c'.R) z') := by
        obtain ⟨w, hw⟩ := hTA x x.2; exact ⟨w, hw⟩
      have : A₀ x ∈ range (scDeriv c'.U (r c'.R) z') ∩
          partialQuadrantAtWith T' (c'.φ.model.E.toBase 1 z') := ⟨hAxT, hAxC⟩
      rw [← hcone] at this
      obtain ⟨w, ⟨hwT, hwC⟩, hwx⟩ := this
      have hwT' : w ∈ rangeS (scDeriv c.U (r c.R) z) := by obtain ⟨u, hu⟩ := hwT; exact ⟨u, hu⟩
      have : w = x := by rw [← hinv1 w hwT', hwx, hinv1 x x.2]
      rw [← this]; exact hwC

end ChartChange

section Bundle

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

open StrongRetr

/-- The transition of two strong bundle charts of `P` is sc-smooth on `[0]` (both are charts of
the M-polyfold `Y[0]`, hence compatible). -/
lemma StrongBundle.IsChart.transition_isScSmoothRetractMap {c c' : StrongBundleChart PX P}
    (hc : B.IsChart c) (hc' : B.IsChart c') :
    IsScSmoothRetractMap (c.φ.model.E.prod c.F) (c.φ.model.C ×ˢ univ) (c.overlap c')
      (c'.φ.model.E.prod c'.F) (c'.φ.model.C ×ˢ univ) (c'.overlap c) (c.transition c') :=
  (hc.toMChart.compatible hc'.toMChart (P := B.toMPolyfold0)).1

omit [T2Space Y] [ParacompactSpace Y] in
/-- The principal part of a section lies in `K` over `O`. -/
lemma StrongBundleChart.principal_mem_K (c : StrongBundleChart PX P) (hf : IsSection P f)
    {x : c.φ.model.E 0} (hx : x ∈ c.φ.model.O) : (x, c.principal f x) ∈ c.K := by
  rw [← c.apply_section hf hx, ← c.image_source]
  exact ⟨_, c.mem_source_of_proj (by rw [hf]; exact c.φ.symm_mapsTo hx), rfl⟩

/-- **Definition 3.53 at a zero, from a non-centred chart, in a given centred chart** (the
assembly step of Theorem 3.54 (1) at the zeros `y ≠ x₀`).  Let `f` be an sc-smooth section, `y`
a zero, `c` a strong bundle chart of `P` around `y` (not necessarily centred), `z` on level `1`
with `ι z = φ(y)`, and `g` sc¹ on `U` agreeing with `f̂` on `O` near `φ(y)` (e.g. a filled
version of the germ at another point `x₀`).  Assume, with a presentation `T` of `C`:
* the range of `Dg(z)|_{T_zO}` contains `ρ(z)k̂` for every smooth `k̂ ∈ F_∞`;
* `ker Dg(z) ∩ T_zO` is in good position to the partial quadrant `C_{φ(y)}` inside `T_zO`.
Then for **every** datum of Definition 3.11 at `y` (a strong bundle chart `c'` centred at `y`, a
filled version `g'` of `f̂'`, an sc⁺-section `s'` with `s'(0) = g'(0)` and `g' − s'` conjugated
to a basic germ) the germ is in good position in `c'` (`IsGoodPositionAt`): the linearizations
in `c` at `z` and in `c'` at `0` are conjugate (`linAt_chart_change`), so the kernel condition is
transported (`IsInGoodPositionIn.transport`) and becomes `ker Dg'(0)` by condition (3) of the
filler `g'` at `0` (`ker Dg'(0) ⊆ T₀O'`); the range of `Tf̃'(0)` is closed (Proposition 3.52 in
`c'`) and contains the dense image under `Γ` of `ρ(z)F_∞`, hence is all of `K'_0`.  (The chart
`c'` is arbitrary; this is what lets the good position be read in a tame chart,
`StrongBundle.IsGoodPositionGermWholeChart.toTame`, `TameGerms.lean`.) -/
theorem StrongBundle.isGoodPositionAt_of_chart_dense (hf : B.IsScSmoothSection f) {y : X}
    (hy0 : IsZeroAt P f y)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (hyV : y ∈ c.φ.source)
    {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z = c.φ y)
    {g : c.φ.model.E 0 → c.F 0} (hg : IsSc1 c.U g)
    (hfg : ∀ᶠ x in 𝓝 (c.φ y), x ∈ c.φ.model.O → c.principal f x = g x)
    {n : ℕ} {Wq : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant n Wq 0)
    (hsurj : ∀ k ∈ c.F.smooth, ∃ x ∈ rangeS (scDeriv c.U (r c.R) z),
      scDeriv c.U g z x = ρ c.R (c.φ y) k)
    (hker : IsInGoodPositionIn c.φ.model.E (rangeS (scDeriv c.U (r c.R) z))
      (partialQuadrantAtWith T (c.φ y))
      (LinearMap.ker (scDeriv c.U g z : c.φ.model.E 0 →ₗ[ℝ] c.F 0) ⊓
        rangeS (scDeriv c.U (r c.R) z)))
    {c' : StrongBundleChart PX P} (hc' : B.IsChart c') (hyV' : y ∈ c'.φ.source)
    (hφ0 : c'.φ y = 0) (h0U' : (0 : c'.φ.model.E 0) ∈ c'.U) {g' : c'.φ.model.E 0 → c'.F 0}
    {s' : c'.φ.model.E 0 → c'.F 1}
    (hfill' : IsFilledVersion c'.relOpen c'.isRetraction h0U' (c'.principal f) g')
    (hs' : IsScSmooth (F := c'.F.shift) c'.U s') (hs0' : c'.F.toBase 1 (s' 0) = g' 0)
    (hconj' : IsConjugateToBasicGerm c'.U (fun u => g' u - c'.F.toBase 1 (s' u))) :
    IsGoodPositionAt c'.relOpen c'.isRetraction h0U' g' := by
  classical
  obtain ⟨n', Wq', T', hT'⟩ := c'.relOpen.isPartialQuadrant
  -- the points
  have hz' : c'.φ.model.E.toBase 1 (0 : c'.φ.model.E 1) = c'.φ y := by rw [map_zero, hφ0]
  have hzOO : c.φ.model.E.toBase 1 z ∈ c.φ.model.O := by rw [hz]; exact c.φ.mapsTo_model y hyV
  have hzO : c.φ.model.E.toBase 1 z ∈ r c.R '' c.U := by rw [c.r_image]; exact hzOO
  have hzU : c.φ.model.E.toBase 1 z ∈ c.U := mem_U_of_mem_O c.isRetraction hzO
  have h0O' : (0 : c'.φ.model.E 0) ∈ r c'.R '' c'.U := by
    rw [c'.r_image, ← hφ0]; exact c'.φ.mapsTo_model y hyV'
  have hzO' : c'.φ.model.E.toBase 1 (0 : c'.φ.model.E 1) ∈ r c'.R '' c'.U := by
    rw [map_zero]; exact h0O'
  have hzU' : c'.φ.model.E.toBase 1 (0 : c'.φ.model.E 1) ∈ c'.U := by rw [map_zero]; exact h0U'
  -- the chart change
  obtain ⟨A, Γ, hconj, hcone⟩ := linAt_chart_change c c' hf.1
    (StrongBundle.IsChart.transition_isScSmoothRetractMap hc hc')
    (hf.isScSmoothRetractMap hc) (hf.isScSmoothRetractMap hc') hyV hyV' hy0 hz hz' hzU hzU'
    T hT T' hT'
  -- the section in the two charts
  have hσsm : ∀ {d : StrongBundleChart PX P}, B.IsChart d →
      IsSc1 d.U (d.principal f ∘ r d.R) := fun {d} hd => by
    have h1 := (hf.isScSmoothRetractMap hd).comp_isScSmooth
      (d.isRetraction.baseRetraction d.relOpen) d.base_retract
    exact ((h1.snd d.relOpen.isScDomain).congr d.relOpen.isScDomain fun _ _ => rfl).isSc1
  have hfK : ∀ x ∈ r c.R '' c.U, (x, c.principal f x) ∈ c.R '' (c.U ×ˢ univ) := fun x hx =>
    c.principal_mem_K hf.1 (c.r_image ▸ hx)
  have hfK' : ∀ x ∈ r c'.R '' c'.U, (x, c'.principal f x) ∈ c'.R '' (c'.U ×ˢ univ) := fun x hx =>
    c'.principal_mem_K hf.1 (c'.r_image ▸ hx)
  have hfz : c.principal f (c.φ.model.E.toBase 1 z) = 0 := by
    rw [hz]; exact (c.isZeroAt_iff hf.1 hyV).1 hy0
  have hfb0' : c'.principal f 0 = 0 := by
    have := (c'.isZeroAt_iff hf.1 hyV').1 hy0; rwa [hφ0] at this
  have hg's : IsScSmooth c'.U g' := hfill'.isScSmooth
  have hg'0 : g' 0 = 0 := by rw [← hfill'.filler.eq_on.self_of_nhds h0O', hfb0']
  -- the bridges `Lin = Dg` in both charts
  have hbr : ∀ x : ↥(rangeS (scDeriv c.U (r c.R) z)),
      linAt c.U c.R (c.principal f) z x = scDeriv c.U g z x := fun x =>
    linAt_eq_scDeriv c.relOpen c.isRetraction (hσsm hc) hg hzO (by
      rw [hz, c.r_image]; exact hfg) x
  have hbr' : ∀ x : ↥(rangeS (scDeriv c'.U (r c'.R) 0)),
      linAt c'.U c'.R (c'.principal f) 0 x = scDeriv c'.U g' 0 x := fun x =>
    linAt_eq_scDeriv c'.relOpen c'.isRetraction (hσsm hc') hg's.isSc1 hzO' (by
      rw [map_zero]; exact hfill'.filler.eq_on) x
  have hmem : ∀ x : ↥(rangeS (scDeriv c.U (r c.R) z)),
      linAt c.U c.R (c.principal f) z x ∈ rangeS (ρCLM c.isRetraction hzU) := fun x =>
    ⟨_, rho_scDeriv_comp_r c.relOpen c.isRetraction (hσsm hc) hfK hzO hfz x⟩
  refine ⟨?_, ?_⟩
  · -- (1) surjectivity of `Tf̃'(0)`
    obtain ⟨h1, -, -, -, -, hTF, -⟩ := proposition_3_52_local_wholeChart c'.relOpen c'.isRetraction h0U' h0O'
      hfill' hfb0' hfK' hs' hs0' hconj'
    set q := ρCLM c'.isRetraction h0U' with hq
    have hqidem : ∀ k, q (q k) = q k := ρCLM_idem c'.isRetraction h0U' h0O'
    -- the range of `Tf̃'(0)` as a closed subset of `F'`
    set S : Set (c'.F 0) := Subtype.val '' (range (fillerRestrict (scDeriv c'.U (r c'.R) 0) q
      (scDeriv c'.U g' 0) h1)) with hSdef
    have hSc : IsClosed S :=
      (isClosed_range_of_idem q hqidem).isClosedEmbedding_subtypeVal.isClosedMap _
        hTF.isClosed_range
    have hSmem : ∀ k ∈ S, ∃ x ∈ rangeS (scDeriv c'.U (r c'.R) 0), scDeriv c'.U g' 0 x = k := by
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, x.2, rfl⟩
    -- the dense image of `ρ(z)F_∞`
    set ψ : c.F 0 → c'.F 0 := fun k =>
      (Γ ⟨ρ c.R (c.φ.model.E.toBase 1 z) k, ⟨k, rfl⟩⟩ : c'.F 0) with hψ
    have hψc : Continuous ψ :=
      continuous_subtype_val.comp (Γ.continuous.comp
        ((ρ_continuous c.isRetraction hzU).subtype_mk _))
    have hψS : ψ '' (c.F.smooth : Set (c.F 0)) ⊆ S := by
      rintro _ ⟨k, hk, rfl⟩
      obtain ⟨x, hxT, hx⟩ := hsurj k hk
      have hlin : ((⟨ρ c.R (c.φ.model.E.toBase 1 z) k, ⟨k, rfl⟩⟩ :
          ↥(rangeS (ρCLM c.isRetraction hzU))) : c.F 0) =
          linAt c.U c.R (c.principal f) z ⟨x, hxT⟩ := by
        change ρ c.R (c.φ.model.E.toBase 1 z) k = _
        rw [hbr, hz]; exact hx.symm
      have := hconj ⟨x, hxT⟩ _ hlin
      rw [hbr'] at this
      exact ⟨fillerRestrict _ q _ h1 (A ⟨x, hxT⟩), ⟨_, rfl⟩, by
        rw [fillerRestrict_apply]; exact this.symm⟩
    have hψrange : ∀ k ∈ rangeS (ρCLM c'.isRetraction hzU'), k ∈ range ψ := by
      intro k hk
      refine ⟨(Γ.symm ⟨k, hk⟩ : c.F 0), ?_⟩
      have hfix : ρ c.R (c.φ.model.E.toBase 1 z) (Γ.symm ⟨k, hk⟩ : c.F 0) =
          (Γ.symm ⟨k, hk⟩ : c.F 0) := by
        obtain ⟨k₀, hk₀⟩ := (Γ.symm ⟨k, hk⟩).2
        rw [← hk₀]
        exact ρ_ρ c.isRetraction hzO k₀
      change (Γ ⟨ρ c.R (c.φ.model.E.toBase 1 z) (Γ.symm ⟨k, hk⟩ : c.F 0), _⟩ : c'.F 0) = k
      have : (⟨ρ c.R (c.φ.model.E.toBase 1 z) (Γ.symm ⟨k, hk⟩ : c.F 0), ⟨_, rfl⟩⟩ :
          ↥(rangeS (ρCLM c.isRetraction hzU))) = Γ.symm ⟨k, hk⟩ := Subtype.ext hfix
      rw [this, Γ.apply_symm_apply]
    intro k hk
    apply hSmem
    have hk' : k ∈ rangeS (ρCLM c'.isRetraction hzU') := by
      rw [mem_rangeS_ρCLM_iff c'.isRetraction hzO' hzU', map_zero]
      exact (mem_rangeS_ρCLM_iff c'.isRetraction h0O' h0U').1 hk
    obtain ⟨k₀, rfl⟩ := hψrange k hk'
    have hcl : ψ k₀ ∈ closure (ψ '' (c.F.smooth : Set (c.F 0))) :=
      image_closure_subset_closure_image hψc ⟨k₀, (c.F.dense_smooth 0) k₀, rfl⟩
    exact hSc.closure_subset_iff.2 hψS hcl
  · -- (2) the kernel
    have hker' := hker.transport A (C' := c'.φ.model.C) (fun x => by
      have := hcone x
      rwa [hz, map_zero, partialQuadrantAtWith_zero, ← hT'] at this)
    convert hker' using 1
    have hkerT : LinearMap.ker (scDeriv c'.U g' 0 : c'.φ.model.E 0 →ₗ[ℝ] c'.F 0) ≤
        rangeS (scDeriv c'.U (r c'.R) 0) :=
      hfill'.filler.ker_deriv_le_range hg's hg'0 h0O' hfK'
    ext w
    constructor
    · intro hw
      have hwT := hkerT hw
      rw [show w = ((⟨w, hwT⟩ : ↥(rangeS (scDeriv c'.U (r c'.R) 0))) : c'.φ.model.E 0) from rfl,
        mem_transportSub_iff]
      set x := A.symm ⟨w, hwT⟩ with hxdef
      refine ⟨?_, x.2⟩
      have hAx : A x = ⟨w, hwT⟩ := A.apply_symm_apply _
      have h1 := hconj x ⟨_, hmem x⟩ rfl
      rw [hAx, hbr'] at h1
      have hw0 : scDeriv c'.U g' 0 w = 0 := hw
      rw [hw0] at h1
      have h2 : (⟨_, hmem x⟩ : ↥(rangeS (ρCLM c.isRetraction hzU))) = 0 :=
        Γ.map_eq_zero_iff.1 (Subtype.ext h1)
      have h3 : linAt c.U c.R (c.principal f) z x = 0 := congrArg Subtype.val h2
      rw [hbr] at h3
      exact h3
    · intro hw
      obtain ⟨x, ⟨hxker, -⟩, hxw⟩ := (mem_transportSub A).1 hw
      have hxker' : scDeriv c.U g z x = 0 := hxker
      have hk0 : (⟨_, hmem x⟩ : ↥(rangeS (ρCLM c.isRetraction hzU))) = 0 :=
        Subtype.ext (show linAt c.U c.R (c.principal f) z x = 0 by rw [hbr]; exact hxker')
      have h1 := hconj x ⟨_, hmem x⟩ rfl
      rw [hk0, ContinuousLinearEquiv.map_zero, Submodule.coe_zero, hbr'] at h1
      change scDeriv c'.U g' 0 w = 0
      rw [← hxw]; exact h1.symm


/-- **Definition 3.53 at a zero, from a non-centred chart** (the assembly step of Theorem 3.54
(1) at the zeros `y ≠ x₀`).  Let `f` be an sc-smooth section, `y` a zero with `(f, y)` an
sc-Fredholm germ (Definition 3.11), `c` a strong bundle chart of `P` around `y` (not necessarily
centred), `z` on level `1` with `ι z = φ(y)`, and `g` sc¹ on `U` agreeing with `f̂` on `O` near
`φ(y)` (e.g. a filled version of the germ at another point `x₀`).  Assume, with a presentation
`T` of `C`:
* the range of `Dg(z)|_{T_zO}` contains `ρ(z)k̂` for every smooth `k̂ ∈ F_∞`;
* `ker Dg(z) ∩ T_zO` is in good position to the partial quadrant `C_{φ(y)}` inside `T_zO`.
Then `(f, y)` is in good position (`IsGoodPositionGermWholeChart`), in the chart `c'` centred at `y` given
by Definition 3.11 (`isGoodPositionAt_of_chart_dense`). -/
theorem StrongBundle.isGoodPositionGerm_of_chart_dense (hf : B.IsScSmoothSection f) {y : X}
    (hy : B.IsScFredholmGermWholeChart f y) (hy0 : IsZeroAt P f y)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (hyV : y ∈ c.φ.source)
    {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z = c.φ y)
    {g : c.φ.model.E 0 → c.F 0} (hg : IsSc1 c.U g)
    (hfg : ∀ᶠ x in 𝓝 (c.φ y), x ∈ c.φ.model.O → c.principal f x = g x)
    {n : ℕ} {Wq : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant n Wq 0)
    (hsurj : ∀ k ∈ c.F.smooth, ∃ x ∈ rangeS (scDeriv c.U (r c.R) z),
      scDeriv c.U g z x = ρ c.R (c.φ y) k)
    (hker : IsInGoodPositionIn c.φ.model.E (rangeS (scDeriv c.U (r c.R) z))
      (partialQuadrantAtWith T (c.φ y))
      (LinearMap.ker (scDeriv c.U g z : c.φ.model.E 0 →ₗ[ℝ] c.F 0) ⊓
        rangeS (scDeriv c.U (r c.R) z))) :
    B.IsGoodPositionGermWholeChart f y := by
  obtain ⟨hys, c', hc', hyV', hφ0, h0U', g', s', hfill', hs', hs0', hconj'⟩ := hy
  exact ⟨hys, c', hc', hyV', hφ0, h0U', g', s', hfill', hs', hs0', hconj',
    StrongBundle.isGoodPositionAt_of_chart_dense hf hy0 hc hyV hz hg hfg T hT hsurj hker hc' hyV'
      hφ0 h0U' hfill' hs' hs0' hconj'⟩

/-- **Definition 3.53 at a zero, from a non-centred chart**, with the surjectivity hypothesis
`Dg(z)(T_zO) ⊇ K_z = {k | (φ(y), k) ∈ K}` (`isGoodPositionGerm_of_chart_dense` with the weaker
hypothesis on `ρ(z)F_∞`). -/
theorem StrongBundle.isGoodPositionGerm_of_chart_wholeChart (hf : B.IsScSmoothSection f) {y : X}
    (hy : B.IsScFredholmGermWholeChart f y) (hy0 : IsZeroAt P f y)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (hyV : y ∈ c.φ.source)
    {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z = c.φ y)
    {g : c.φ.model.E 0 → c.F 0} (hg : IsSc1 c.U g)
    (hfg : ∀ᶠ x in 𝓝 (c.φ y), x ∈ c.φ.model.O → c.principal f x = g x)
    {n : ℕ} {Wq : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant n Wq 0)
    (hsurj : ∀ k, (c.φ y, k) ∈ c.K → ∃ x ∈ rangeS (scDeriv c.U (r c.R) z), scDeriv c.U g z x = k)
    (hker : IsInGoodPositionIn c.φ.model.E (rangeS (scDeriv c.U (r c.R) z))
      (partialQuadrantAtWith T (c.φ y))
      (LinearMap.ker (scDeriv c.U g z : c.φ.model.E 0 →ₗ[ℝ] c.F 0) ⊓
        rangeS (scDeriv c.U (r c.R) z))) :
    B.IsGoodPositionGermWholeChart f y :=
  StrongBundle.isGoodPositionGerm_of_chart_dense hf hy hy0 hc hyV hz hg hfg T hT
    (fun k _ => hsurj _ (c.mem_K_ρ (c.φ.mapsTo_model y hyV) k)) hker

/-- **Definition 3.53 at a zero, from the linearization in a non-centred chart**: the intrinsic
form of `isGoodPositionGerm_of_chart_dense`, with the hypotheses on `Lin(z) = D(f̂ ∘ r)(z)|_{T_zO}`
(`linAt`) itself: its range contains `ρ(z)F_∞`, and its kernel is in good position to `C_{φ(y)}`
inside `T_zO`.  (Take `g = f̂ ∘ r`.) -/
theorem StrongBundle.isGoodPositionGerm_of_linAt (hf : B.IsScSmoothSection f) {y : X}
    (hy : B.IsScFredholmGermWholeChart f y) (hy0 : IsZeroAt P f y)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (hyV : y ∈ c.φ.source)
    {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z = c.φ y)
    {n : ℕ} {Wq : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant n Wq 0)
    (hsurj : ∀ k ∈ c.F.smooth, ∃ x, linAt c.U c.R (c.principal f) z x = ρ c.R (c.φ y) k)
    (hker : IsInGoodPositionIn c.φ.model.E (rangeS (scDeriv c.U (r c.R) z))
      (partialQuadrantAtWith T (c.φ y))
      ((LinearMap.ker (linAt c.U c.R (c.principal f) z :
        ↥(rangeS (scDeriv c.U (r c.R) z)) →ₗ[ℝ] c.F 0)).map
          (rangeS (scDeriv c.U (r c.R) z)).subtype)) :
    B.IsGoodPositionGermWholeChart f y := by
  have h1 := (hf.isScSmoothRetractMap hc).comp_isScSmooth
    (c.isRetraction.baseRetraction c.relOpen) c.base_retract
  have hfr : IsSc1 c.U (c.principal f ∘ r c.R) :=
    ((h1.snd c.relOpen.isScDomain).congr c.relOpen.isScDomain fun _ _ => rfl).isSc1
  refine StrongBundle.isGoodPositionGerm_of_chart_dense hf hy hy0 hc hyV hz hfr
    (Filter.Eventually.of_forall fun x hx => ?_) T hT (fun k hk => ?_) ?_
  · change c.principal f x = c.principal f (r c.R x)
    rw [r_eq_self c.isRetraction (by rw [c.r_image]; exact hx)]
  · obtain ⟨x, hx⟩ := hsurj k hk
    exact ⟨x, x.2, hx⟩
  · convert hker using 1
    ext w
    simp only [Submodule.mem_inf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      Submodule.mem_map, Submodule.subtype_apply]
    constructor
    · rintro ⟨hw, hwT⟩
      exact ⟨⟨w, hwT⟩, hw, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, x.2⟩

/-- **Definition 3.53 at a zero, from the linearization in a non-centred chart**, with the
surjectivity of `Lin(z) : T_zO → K_z`. -/
theorem StrongBundle.isGoodPositionGerm_of_linAt_surj_wholeChart (hf : B.IsScSmoothSection f) {y : X}
    (hy : B.IsScFredholmGermWholeChart f y) (hy0 : IsZeroAt P f y)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (hyV : y ∈ c.φ.source)
    {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z = c.φ y)
    {n : ℕ} {Wq : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant n Wq 0)
    (hsurj : ∀ k, (c.φ y, k) ∈ c.K → ∃ x, linAt c.U c.R (c.principal f) z x = k)
    (hker : IsInGoodPositionIn c.φ.model.E (rangeS (scDeriv c.U (r c.R) z))
      (partialQuadrantAtWith T (c.φ y))
      ((LinearMap.ker (linAt c.U c.R (c.principal f) z :
        ↥(rangeS (scDeriv c.U (r c.R) z)) →ₗ[ℝ] c.F 0)).map
          (rangeS (scDeriv c.U (r c.R) z)).subtype)) :
    B.IsGoodPositionGermWholeChart f y :=
  StrongBundle.isGoodPositionGerm_of_linAt hf hy hy0 hc hyV hz T hT
    (fun k _ => hsurj _ (c.mem_K_ρ (c.φ.mapsTo_model y hyV) k)) hker

/-- **The chart independence of the linearization at a zero and of the good position of its
kernel** (the local form of gap G.13 for Definition 3.53).  For two strong bundle charts `c`,
`c'` of `P` around a zero `y` of the sc-smooth section `f`, with level-`1` points `z`, `z'` over
`φ(y)`, `φ'(y)`, the linearizations `L = Lin(z) : T_zO → K_z` and `L' = Lin'(z') : T_{z'}O' →
K'_{z'}` satisfy: `L` is surjective iff `L'` is; `L` is Fredholm iff `L'` is, with the same index;
`ker L` is in good position to `C_z` inside `T_zO` iff `ker L'` is in good position to `C'_{z'}`
inside `T_{z'}O'`. -/
theorem StrongBundle.linAt_chart_independence (hf : B.IsScSmoothSection f)
    {c c' : StrongBundleChart PX P} (hc : B.IsChart c) (hc' : B.IsChart c') {y : X}
    (hyV : y ∈ c.φ.source) (hyV' : y ∈ c'.φ.source) (hy0 : IsZeroAt P f y)
    {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z = c.φ y)
    {z' : c'.φ.model.E 1} (hz' : c'.φ.model.E.toBase 1 z' = c'.φ y)
    (hzU : c.φ.model.E.toBase 1 z ∈ c.U) (hzU' : c'.φ.model.E.toBase 1 z' ∈ c'.U)
    {n n' : ℕ} {Wq Wq' : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant n Wq 0)
    (T' : ScIso c'.φ.model.E ((ScBanach.const (Fin n' → ℝ)).prod Wq'))
    (hT' : c'.φ.model.C = T' 0 ⁻¹' quadrant n' Wq' 0) :
    ∃ (L : ↥(rangeS (scDeriv c.U (r c.R) z)) →L[ℝ] ↥(rangeS (ρCLM c.isRetraction hzU)))
      (L' : ↥(rangeS (scDeriv c'.U (r c'.R) z')) →L[ℝ] ↥(rangeS (ρCLM c'.isRetraction hzU'))),
      (∀ x, (L x : c.F 0) = linAt c.U c.R (c.principal f) z x) ∧
      (∀ x, (L' x : c'.F 0) = linAt c'.U c'.R (c'.principal f) z' x) ∧
      (Surjective L ↔ Surjective L') ∧ (IsFredholm L ↔ IsFredholm L') ∧
      (IsFredholm L → fredholmIndex L' = fredholmIndex L) ∧
      (IsInGoodPositionIn c.φ.model.E (rangeS (scDeriv c.U (r c.R) z))
          (partialQuadrantAtWith T (c.φ.model.E.toBase 1 z))
          ((LinearMap.ker (L : ↥(rangeS (scDeriv c.U (r c.R) z)) →ₗ[ℝ]
            ↥(rangeS (ρCLM c.isRetraction hzU)))).map (rangeS (scDeriv c.U (r c.R) z)).subtype) ↔
        IsInGoodPositionIn c'.φ.model.E (rangeS (scDeriv c'.U (r c'.R) z'))
          (partialQuadrantAtWith T' (c'.φ.model.E.toBase 1 z'))
          ((LinearMap.ker (L' : ↥(rangeS (scDeriv c'.U (r c'.R) z')) →ₗ[ℝ]
            ↥(rangeS (ρCLM c'.isRetraction hzU')))).map
              (rangeS (scDeriv c'.U (r c'.R) z')).subtype)) := by
  obtain ⟨A, Γ, hconj, hcone⟩ := linAt_chart_change c c' hf.1
    (StrongBundle.IsChart.transition_isScSmoothRetractMap hc hc')
    (hf.isScSmoothRetractMap hc) (hf.isScSmoothRetractMap hc') hyV hyV' hy0 hz hz' hzU hzU'
    T hT T' hT'
  have hfr : ∀ {d : StrongBundleChart PX P}, B.IsChart d →
      IsSc1 d.U (d.principal f ∘ r d.R) := fun {d} hd => by
    have h1 := (hf.isScSmoothRetractMap hd).comp_isScSmooth
      (d.isRetraction.baseRetraction d.relOpen) d.base_retract
    exact ((h1.snd d.relOpen.isScDomain).congr d.relOpen.isScDomain fun _ _ => rfl).isSc1
  have hzO : c.φ.model.E.toBase 1 z ∈ r c.R '' c.U := by
    rw [c.r_image, hz]; exact c.φ.mapsTo_model y hyV
  have hzO' : c'.φ.model.E.toBase 1 z' ∈ r c'.R '' c'.U := by
    rw [c'.r_image, hz']; exact c'.φ.mapsTo_model y hyV'
  have hmem : ∀ x : ↥(rangeS (scDeriv c.U (r c.R) z)),
      linAt c.U c.R (c.principal f) z x ∈ rangeS (ρCLM c.isRetraction hzU) := fun x =>
    ⟨_, rho_scDeriv_comp_r c.relOpen c.isRetraction (hfr hc)
      (fun x hx => c.principal_mem_K hf.1 (c.r_image ▸ hx)) hzO
      (by rw [hz]; exact (c.isZeroAt_iff hf.1 hyV).1 hy0) x⟩
  have hmem' : ∀ x : ↥(rangeS (scDeriv c'.U (r c'.R) z')),
      linAt c'.U c'.R (c'.principal f) z' x ∈ rangeS (ρCLM c'.isRetraction hzU') := fun x =>
    ⟨_, rho_scDeriv_comp_r c'.relOpen c'.isRetraction (hfr hc')
      (fun x hx => c'.principal_mem_K hf.1 (c'.r_image ▸ hx)) hzO'
      (by rw [hz']; exact (c'.isZeroAt_iff hf.1 hyV').1 hy0) x⟩
  set L := (linAt c.U c.R (c.principal f) z).codRestrict _ hmem with hL
  set L' := (linAt c'.U c'.R (c'.principal f) z').codRestrict _ hmem' with hL'
  have hLL : ∀ x, L' (A x) = Γ (L x) := fun x => Subtype.ext (hconj x (L x) rfl).symm
  have : CompleteSpace ↥(rangeS (scDeriv c.U (r c.R) z)) :=
    (isClosed_range_of_idem _ (scDeriv_r_idem_at c.relOpen c.isRetraction hzO)).completeSpace_coe
  have : CompleteSpace ↥(rangeS (scDeriv c'.U (r c'.R) z')) :=
    (isClosed_range_of_idem _
      (scDeriv_r_idem_at c'.relOpen c'.isRetraction hzO')).completeSpace_coe
  have : CompleteSpace ↥(rangeS (ρCLM c.isRetraction hzU)) :=
    (isClosed_range_of_idem _ fun k => ρ_ρ c.isRetraction hzO k).completeSpace_coe
  have : CompleteSpace ↥(rangeS (ρCLM c'.isRetraction hzU')) :=
    (isClosed_range_of_idem _ fun k => ρ_ρ c'.isRetraction hzO' k).completeSpace_coe
  refine ⟨L, L', fun x => rfl, fun x => rfl, surjective_iff_of_conj hLL,
    (isFredholm_iff_of_conj hLL).1, (isFredholm_iff_of_conj hLL).2, ?_⟩
  rw [isInGoodPositionIn_transport_iff A hcone (Submodule.map_subtype_le _ _),
    transportSub_eq_map, ← ker_eq_map_of_conj hLL]

end Bundle

end Polyfold
