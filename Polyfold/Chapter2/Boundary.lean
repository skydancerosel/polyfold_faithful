import Polyfold.Chapter2.Tame

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §2.3, the
remainder: the basic properties of the boundary `∂X` (Definition 2.4.5 (preprint 2.25)) and of faces (Definition
2.39), Proposition 2.4.10 (preprint 2.30) (invariance of the reduced tangent space and of the partial cone under germs
of sc-diffeomorphisms) and **Theorem 2.4.12 (preprint 2.31)** (`dim(T_xO/T_x^R O) ≤ d_O(x)`) in general, i.e. for
every chart of every M-polyfold.

# Boundary, partial cones, and Theorem 2.4.12 (preprint 2.31)

## The text, paraphrased

(Definition 2.4.5 (preprint 2.25)) `∂X = {d_X ≥ 1}`.  (Lemma 2.4.9 (preprint 2.29)) For a retract `(O, C, E)` with
`C = [0,∞)ᵏ ⊕ W` and `x ∈ O_∞`: `T_x^R O` is the closure of the derivatives `α̇(0)` of sc-smooth
paths `α : (−ε, ε) → O` with `α(0) = x`; `C_xO` the closure of the one-sided derivatives of
sc-smooth paths `α : [0, ε) → O`; `T_xO = C_xO − C_xO`.  (Proposition 2.4.10 (preprint 2.30)) A germ of
sc-diffeomorphisms `f : (O, x) → (O', y)` between retracts has `Tf(x)(T_x^R O) = T_y^R O'` and
`Tf(x)(C_xO) = C_yO'`.  (Theorem 2.4.12 (preprint 2.31)) For a retract `O`, viewed as an M-polyfold with the chart
`id`, and a smooth `x ∈ O`: `dim(T_xO/T_x^R O) ≤ d_O(x)`, where `d_O(x) = min d_{C'}(φ(x))` over
all germs of sc-diffeomorphisms `φ : (O, x) → (O', φ(x))` into retracts; if equality holds, `C_xO`
is a partial quadrant in `T_xO`.

## What is formalized

* `MPolyfold.isOpen_setOf_degIndex_lt`, `MPolyfold.isClosed_setOf_le_degIndex`,
  `MPolyfold.isClosed_boundary`, `MPolyfold.isOpen_interior`, `MPolyfold.corners` (the points with
  `d_X ≥ 2`), `MPolyfold.IsFace.subset_boundary`, `MPolyfold.IsScDiffeoOn.mem_boundary_iff`: the
  basic properties of Definitions 2.4.5 and 2.5.10 (preprint 2.25 and 2.39) that follow from Lemma 2.4.3 (preprint 2.23) and Proposition 2.4.4 (preprint 2.24).
* The **one-sided sign argument** `IsSc1With.deriv_mem_partialQuadrant_of_lvl1` (the content of
  Lemma 2.4.9 (preprint 2.29) (2)): for `f` sc¹ on `U ⊆ C` with values in `C'`, `x ∈ U₁`, `v ∈ E₁ ∩ C_x`, one has
  `Df(x)v ∈ C'_{f(x)}`; `IsSc1With.mapsTo_partialQuadrant` extends it to all of `C_x` by density
  (`partialQuadrantAtWith_subset_closure`).
* `ScRetraction.IsDiffeoGerm R R' F G`: a germ of sc-diffeomorphisms between the retracts
  `r(U)` and `r'(U')` (`F ∘ r` and `G ∘ r'` sc¹, inverse to each other on the retracts), with the
  identities `D(G ∘ r')(y) ∘ D(F ∘ r)(x) = Dr(x)`, `D(F ∘ r)(x) ∘ D(G ∘ r')(y) = Dr'(y)` and the
  sign arguments for `F ∘ r`, `G ∘ r'`.
* `Polyfold.proposition_2_4_10_reduced`, `Polyfold.proposition_2_4_10_cone` (**Proposition 2.4.10 (preprint 2.30)**).
* `Polyfold.quotDim A B = dim(A / (A ∩ B))`, the dimension `dim(T_xO/T_x^R O)` as a natural
  number, with `quotDim_inf_minimalSubspace_le : dim(T_xO/T_x^R O) ≤ d_C(x)` (and finite
  dimensionality).
* `ScRetraction.IsDiffeoGerm.quotDim_le`: the core of Theorem 2.4.12 (preprint 2.31) for one germ,
  `dim(T_xO/T_x^R O) ≤ d_{C'}(F(x))`; `MPolyfold.quotDim_le_chartDegIndex`: for two charts `φ`,
  `ψ` of an M-polyfold around `x`, `dim(T_{φ(x)}O/T^R) ≤ d_{C'}(ψ(x))`.
* `Polyfold.theorem_2_4_12` (**Theorem 2.4.12 (preprint 2.31)**, for every M-polyfold): for a chart `φ` of `X` around
  `x` with `φ(x)` on level `1`, `dim(T_{φ(x)}O/T_{φ(x)}^R O) ≤ d_X(x)`;
  `Polyfold.theorem_2_4_12_retract`: the text's form, for a retract `O` viewed as an M-polyfold.

## What the text leaves implicit, and the choices made

* Lemma 2.4.9 (preprint 2.29) is not formalized in its path formulation (gap G.10 of the report).  An sc-smooth path from an interval
  (with the constant sc-structure on `ℝ`) takes values in `O_∞` and has a smooth derivative, so the
  lemma is a statement about smooth vectors and needs the density of the smooth points of
  `T_x^R O` and of `C_xO` (the exposition's Lemma 3.A), which the text asserts without proof.
  The derivative-level content of the lemma — the two sign arguments and `Dr(x)v = v` on `T_xO` —
  is what Proposition 2.4.10 (preprint 2.30) and Theorem 2.4.12 (preprint 2.31) use, and it is formalized directly:
  `IsSc1With.deriv_mem_minimalSubspace_of_lvl1` (`DegeneracyIndex.lean`) is the two-sided
  argument, `IsSc1With.deriv_mem_partialQuadrant_of_lvl1` the one-sided one.  Proposition 2.4.10 (preprint 2.30) is
  then proved from these, not from Lemma 2.4.9 (preprint 2.29).
* Everything is stated for `x` on level `1` (where `Dr(x)` exists) instead of smooth `x`.
* The text proves Theorem 2.4.12 (preprint 2.31) for a retract `O` as an M-polyfold, by reducing to one germ.  Here
  the one-germ inequality is proved for a germ between retracts (`IsDiffeoGerm.quotDim_le`,
  which generalizes `degIndexWith_le_of_germ` of `DegeneracyIndex.lean` from `U₀` to a retract),
  and the theorem is then stated for an arbitrary M-polyfold `X` and any chart `φ` around `x`:
  `dim(T_{φ(x)}O/T^R) ≤ d(x, ψ)` for every other chart `ψ`, hence `≤ d_X(x)`.  The text's
  description of `d_O` as a minimum over germs of sc-diffeomorphisms into retracts is replaced by
  Definition 2.4.1 (preprint 2.22) for the M-polyfold `O` with the atlas `{id}`: its charts are exactly such germs
  (restricted to open subsets, Proposition 2.3.1 (preprint 2.10) (1)), and the restriction of a retraction to an
  open subset has the same derivative (`ScRetraction.scDeriv_restrict`).
* The second statement of Theorem 2.4.12 (preprint 2.31) (if `dim(T_xO/T_x^R O) = d_O(x)` then `C_xO` is a partial
  quadrant in `T_xO`) is not formalized: it needs the sc-Banach structure of `T_xO` (the range of
  the sc-projection `Dr(x)`) and smooth lifts of a basis of `T_xO/T_x^R O` (gap G.11 of the
  report).  For tame retracts the conclusion is proved directly, with explicit smooth lifts:
  `proposition_2_5_6_partialCone` in `PartialCone.lean`.
-/

open Set Filter Topology Function Module

noncomputable section

namespace Polyfold

variable {E E' : ScBanach}

/-! ### The boundary and faces: basic properties (Definitions 2.4.5, 2.5.10 (preprint 2.25, 2.39)) -/

namespace MPolyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

/-- The sets `{d_X < k}` are open (Lemma 2.4.3 (preprint 2.23)). -/
theorem isOpen_setOf_degIndex_lt (k : ℕ) : IsOpen {x | P.degIndex x < k} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  exact (lemma_2_4_3 P x).mono fun y hy => lt_of_le_of_lt hy hx

/-- The sets `{d_X ≥ k}` are closed. -/
theorem isClosed_setOf_le_degIndex (k : ℕ) : IsClosed {x | k ≤ P.degIndex x} := by
  have : {x | k ≤ P.degIndex x} = {x | P.degIndex x < k}ᶜ := by
    ext x; simp [not_lt]
  rw [this]
  exact (P.isOpen_setOf_degIndex_lt k).isClosed_compl

/-- **Definition 2.4.5 (preprint 2.25)**: the boundary `∂X` is closed. -/
theorem isClosed_boundary : IsClosed P.boundary := P.isClosed_setOf_le_degIndex 1

/-- The interior `{d_X = 0} = X \ ∂X` is open. -/
theorem isOpen_interior : IsOpen {x | P.degIndex x = 0} := by
  have : {x | P.degIndex x = 0} = {x | P.degIndex x < 1} := by
    ext x; simp
  rw [this]
  exact P.isOpen_setOf_degIndex_lt 1

/-- The **corners** of `X`: the points with `d_X ≥ 2` (Definition 1.3.3 (preprint 1.23)'s terminology, transported
to `X`). -/
def corners : Set X := {x | 2 ≤ P.degIndex x}

theorem isClosed_corners : IsClosed P.corners := P.isClosed_setOf_le_degIndex 2

lemma corners_subset_boundary : P.corners ⊆ P.boundary := fun _ hx =>
  show 1 ≤ _ from le_trans one_le_two hx

/-- A face is contained in the boundary. -/
theorem IsFace.subset_boundary {F : Set X} (h : P.IsFace F) : F ⊆ P.boundary := by
  obtain ⟨x, _, rfl⟩ := h
  refine P.isClosed_boundary.closure_subset_iff.2 ?_
  exact (connectedComponentIn_subset _ _).trans fun y hy => le_of_eq hy.symm

/-- The interior of a face, `{y ∈ F | d_X(y) = 1}`, contains the component it was built from. -/
lemma IsFace.connectedComponentIn_subset {F : Set X} {x : X} (hx : P.degIndex x = 1)
    (hF : F = closure (connectedComponentIn {y | P.degIndex y = 1} x)) :
    connectedComponentIn {y | P.degIndex y = 1} x ⊆ F := hF ▸ subset_closure

variable {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}

/-- The boundary is invariant under germs of sc-diffeomorphisms (Proposition 2.4.4 (preprint 2.24)). -/
theorem IsScDiffeoOn.mem_boundary_iff {P : MPolyfold X} {f : X → Y} {g : Y → X} {U : Set X}
    {V : Set Y} (h : P.IsScDiffeoOn Q f g U V) {x : X} (hx : x ∈ U) :
    x ∈ P.boundary ↔ f x ∈ Q.boundary := by
  change 1 ≤ P.degIndex x ↔ 1 ≤ Q.degIndex (f x)
  rw [proposition_2_4_4 h hx]

end MPolyfold

/-! ### The one-sided sign argument (Lemma 2.4.9 (preprint 2.29) (2)) -/

section Sign

variable {n n' : ℕ} {W W' : ScBanach} {C : Set (E 0)} {C' : Set (E' 0)} {U : Set (E 0)}
  {f : E 0 → E' 0} {D : E 1 → E 0 →L[ℝ] E' 0}

lemma isClosed_partialQuadrantAtWith (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (e : E 0) :
    IsClosed (partialQuadrantAtWith T e) := by
  have : partialQuadrantAtWith T e =
      ⋂ i : {i : Fin n // (T 0 e).1 i = 0}, {v : E 0 | 0 ≤ (T 0 v).1 i.1} := by
    ext v
    simp only [partialQuadrantAtWith, mem_ofPred_eq, mem_iInter, Subtype.forall]
  rw [this]
  exact isClosed_iInter fun i => isClosed_le continuous_const
    ((continuous_apply i.1).comp (continuous_fst.comp (T 0).continuous))

/-- The points of `C_e` on level `1` are dense in `C_e`. -/
theorem partialQuadrantAtWith_subset_closure (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (e : E 0) :
    partialQuadrantAtWith T e ⊆ closure (partialQuadrantAtWith T e ∩ range (E.toBase 1)) := by
  intro v hv
  set a := (T 0 v).1 with ha
  set w := (T 0 v).2 with hw
  let W₁ : Set (W 0) := range (W.toBase 1)
  have hdense : Dense W₁ := W.denseRange_incl 0
  have : (𝓝[W₁] w).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (hdense w)
  let σ : W 0 → E 0 := fun w' => (T 0).symm (a, w')
  have hσ : Continuous σ := (T 0).symm.continuous.comp (continuous_const.prodMk continuous_id)
  have hσw : σ w = v := by
    simp only [σ, ha, hw, Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply]
  refine mem_closure_of_tendsto (b := 𝓝[W₁] w) (f := σ) ?_ ?_
  · rw [← hσw]
    exact (hσ.tendsto w).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with w' hw'
    refine ⟨fun i hi => ?_, ?_⟩
    · have : (T 0 (σ w')).1 i = a i := by
        simp only [σ, ContinuousLinearEquiv.apply_symm_apply]
      rw [this]
      exact hv i hi
    · obtain ⟨w₁, rfl⟩ := hw'
      refine ⟨(T 1).symm ((a, w₁) : ((ScBanach.const (Fin n → ℝ)).prod W) 1), ?_⟩
      rw [T.symm_toBase_comm, ScBanach.prod_toBase]
      simp only [σ]
      congr 2

/-- `x + tv ∈ U₁` for small `t ≥ 0`, when `x ∈ U₁` and `v ∈ C_x` (`U` relatively open in
`C = T⁻¹(quadrant)`). -/
lemma eventually_add_smul_mem_lvlSet_of_cone (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (hT : C = T 0 ⁻¹' quadrant n W 0) (hU : IsRelOpenInQuadrant E C U) {x : E 1}
    (hx : x ∈ E.lvlSet U 1) {v : E 1} (hv : E.toBase 1 v ∈ partialQuadrantAtWith T (E.toBase 1 x)) :
    ∀ᶠ t : ℝ in 𝓝[≥] 0, x + t • v ∈ E.lvlSet U 1 := by
  obtain ⟨O, hO, hUO⟩ := hU.relOpen
  have hxU : E.toBase 1 x ∈ U := hx
  rw [hUO] at hxU
  have hcont : Tendsto (fun t : ℝ => E.toBase 1 (x + t • v)) (𝓝 0) (𝓝 (E.toBase 1 x)) := by
    have : Continuous fun t : ℝ => E.toBase 1 (x + t • v) := by fun_prop
    simpa using this.tendsto 0
  have h1 : ∀ᶠ t : ℝ in 𝓝[≥] 0, E.toBase 1 (x + t • v) ∈ O :=
    (hcont.eventually (hO.mem_nhds hxU.1)).filter_mono nhdsWithin_le_nhds
  have heq : ∀ (t : ℝ) i, (T 0 (E.toBase 1 (x + t • v))).1 i =
      (T 0 (E.toBase 1 x)).1 i + t * (T 0 (E.toBase 1 v)).1 i := fun t i => by
    simp only [map_add, map_smul, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
  have hxC : T 0 (E.toBase 1 x) ∈ quadrant n W 0 := by
    have := hxU.2; rwa [hT] at this
  have h2 : ∀ i : Fin n, ∀ᶠ t : ℝ in 𝓝[≥] 0, 0 ≤ (T 0 (E.toBase 1 (x + t • v))).1 i := by
    intro i
    by_cases hi : (T 0 (E.toBase 1 x)).1 i = 0
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [heq, hi, zero_add]
      exact mul_nonneg ht (hv i hi)
    · have hpos : 0 < (T 0 (E.toBase 1 x)).1 i := lt_of_le_of_ne (hxC i) (Ne.symm hi)
      have hc : Tendsto (fun t : ℝ => (T 0 (E.toBase 1 x)).1 i + t * (T 0 (E.toBase 1 v)).1 i)
          (𝓝 0) (𝓝 ((T 0 (E.toBase 1 x)).1 i)) := by
        have := (by fun_prop : Continuous fun t : ℝ =>
          (T 0 (E.toBase 1 x)).1 i + t * (T 0 (E.toBase 1 v)).1 i).tendsto (0 : ℝ)
        simpa using this
      exact ((hc.eventually (lt_mem_nhds hpos)).filter_mono nhdsWithin_le_nhds).mono
        fun t ht => by rw [heq]; exact le_of_lt ht
  filter_upwards [h1, eventually_all.2 h2] with t ht1 ht2
  change E.toBase 1 (x + t • v) ∈ U
  rw [hUO]
  exact ⟨ht1, by rw [hT]; exact fun i => ht2 i⟩

/-- A function `g ≥ 0` on `[0, ε)` with `g(0) = 0` and a one-sided derivative `c` at `0` has
`c ≥ 0`. -/
lemma nonneg_of_hasDerivWithinAt_Ici {g : ℝ → ℝ} {c : ℝ} (hg : HasDerivWithinAt g c (Ici 0) 0)
    (h0 : g 0 = 0) (hpos : ∀ᶠ t in 𝓝[≥] 0, 0 ≤ g t) : 0 ≤ c := by
  have hslope := hasDerivWithinAt_iff_tendsto_slope.1 hg
  have : (𝓝[Ici (0 : ℝ) \ {0}] 0).NeBot := by
    have : Ici (0 : ℝ) \ {0} = Ioi 0 := by
      ext t; simp
    rw [this]; infer_instance
  refine ge_of_tendsto hslope ?_
  filter_upwards [self_mem_nhdsWithin, (nhdsWithin_mono _ sdiff_subset) hpos] with t ht hgt
  rw [slope_def_field, h0, sub_zero, sub_zero]
  exact div_nonneg hgt ht.1

/-- **The one-sided sign argument** (Lemma 2.4.9 (preprint 2.29) (2)): if `f` is sc¹ on `U ⊆ C` with values in
`C'`, `x ∈ U₁` and `v ∈ E₁ ∩ C_x`, then `Df(x)v ∈ C'_{f(x)}`.  Proof: for `j` with
`(T'(f(x)))_j = 0`, the function `t ↦ (T'(f(x + tv)))_j` is nonnegative on `[0, ε)` and vanishes
at `0`, so its one-sided derivative `(T' Df(x) v)_j` at `0` is nonnegative. -/
theorem IsSc1With.deriv_mem_partialQuadrant_of_lvl1
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (hT : C = T 0 ⁻¹' quadrant n W 0)
    (T' : ScIso E' ((ScBanach.const (Fin n' → ℝ)).prod W')) (hT' : C' = T' 0 ⁻¹' quadrant n' W' 0)
    (hU : IsRelOpenInQuadrant E C U) (hf : IsSc1With U f D) (hfC : MapsTo f U C') {x : E 1}
    (hx : x ∈ E.lvlSet U 1) {v : E 1} (hv : E.toBase 1 v ∈ partialQuadrantAtWith T (E.toBase 1 x)) :
    D x (E.toBase 1 v) ∈ partialQuadrantAtWith T' (f (E.toBase 1 x)) := by
  intro j hj
  set γ : ℝ → E 1 := fun t => x + t • v with hγ
  have hev := eventually_add_smul_mem_lvlSet_of_cone T hT hU hx hv
  set s : Set ℝ := {t | γ t ∈ E.lvlSet U 1} with hs
  have hs0 : s ∈ 𝓝[≥] (0 : ℝ) := hev
  let L : E' 0 →L[ℝ] ℝ := (ContinuousLinearMap.proj j).comp
    ((ContinuousLinearMap.fst ℝ (Fin n' → ℝ) (W' 0)).comp (T' 0 : E' 0 →L[ℝ] _))
  set g : ℝ → ℝ := fun t => L (f (E.toBase 1 (γ t))) with hg
  have hγ' : HasDerivAt γ v 0 := by
    simpa [hγ] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hγ0 : γ 0 = x := by simp [hγ]
  have hder : HasDerivWithinAt g (L (D x (E.toBase 1 v))) (Ici 0) 0 := by
    have h1 : HasDerivWithinAt ((f ∘ E.toBase 1) ∘ γ) (((D x).comp (E.toBase 1)) v) s 0 := by
      have hfx : HasFDerivWithinAt (f ∘ E.toBase 1) ((D x).comp (E.toBase 1)) (E.lvlSet U 1)
          (γ 0) := by
        rw [hγ0]; exact hf.hasFDerivWithinAt x hx
      exact HasFDerivWithinAt.comp_hasDerivWithinAt (l := f ∘ E.toBase 1) (f := γ)
        (t := E.lvlSet U 1) (s := s) (0 : ℝ) hfx hγ'.hasDerivWithinAt fun t ht => ht
    have h2 : HasDerivWithinAt ((f ∘ E.toBase 1) ∘ γ) (((D x).comp (E.toBase 1)) v) (Ici 0) 0 :=
      h1.mono_of_mem_nhdsWithin hs0
    exact L.hasFDerivAt.comp_hasDerivWithinAt (0 : ℝ) h2
  have h0 : g 0 = 0 := by
    simp only [hg, hγ0]
    exact hj
  have hpos : ∀ᶠ t in 𝓝[≥] (0 : ℝ), 0 ≤ g t := by
    filter_upwards [hev] with t ht
    have hC' : f (E.toBase 1 (γ t)) ∈ C' := hfC ht
    rw [hT'] at hC'
    exact hC' j
  exact nonneg_of_hasDerivWithinAt_Ici hder h0 hpos

/-- `Df(x)` maps all of `C_x` into `C'_{f(x)}` (one-sided sign argument plus density). -/
theorem IsSc1With.mapsTo_partialQuadrant
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (hT : C = T 0 ⁻¹' quadrant n W 0)
    (T' : ScIso E' ((ScBanach.const (Fin n' → ℝ)).prod W')) (hT' : C' = T' 0 ⁻¹' quadrant n' W' 0)
    (hU : IsRelOpenInQuadrant E C U) (hf : IsSc1With U f D) (hfC : MapsTo f U C') {x : E 1}
    (hx : x ∈ E.lvlSet U 1) :
    MapsTo (D x) (partialQuadrantAtWith T (E.toBase 1 x))
      (partialQuadrantAtWith T' (f (E.toBase 1 x))) := by
  intro v hv
  have hclosed : IsClosed ((D x) ⁻¹' partialQuadrantAtWith T' (f (E.toBase 1 x))) :=
    (isClosed_partialQuadrantAtWith T' _).preimage (D x).continuous
  have hsub : partialQuadrantAtWith T (E.toBase 1 x) ∩ range (E.toBase 1) ⊆
      (D x) ⁻¹' partialQuadrantAtWith T' (f (E.toBase 1 x)) := by
    rintro _ ⟨hw, w, rfl⟩
    exact hf.deriv_mem_partialQuadrant_of_lvl1 T hT T' hT' hU hfC hx hw
  exact hclosed.closure_subset_iff.2 hsub (partialQuadrantAtWith_subset_closure T _ hv)

end Sign

/-! ### Germs of sc-diffeomorphisms between retracts -/

namespace ScRetraction

variable {C : Set (E 0)} {C' : Set (E' 0)}

lemma U_subset_C (R : ScRetraction E C) : R.U ⊆ C := by
  obtain ⟨O, _, hO⟩ := R.relOpen.relOpen
  exact hO ▸ inter_subset_right

lemma retract_subset_C (R : ScRetraction E C) : R.retract ⊆ C := R.retract_subset.trans R.U_subset_C

/-- A **germ of sc-diffeomorphisms** `F : (O, x) → (O', F(x))` between the retracts `O = r(U)` and
`O' = r'(U')`, in the form used by §2.3: `F ∘ r` and `G ∘ r'` are sc¹ (sc¹ suffices for the index
computations; the text has sc-smooth), `F(O) ⊆ O'`, `G(O') ⊆ O`, and `F`, `G` are inverse to each
other on `O`, `O'`. -/
structure IsDiffeoGerm (R : ScRetraction E C) (R' : ScRetraction E' C') (F : E 0 → E' 0)
    (G : E' 0 → E 0) : Prop where
  isSc1 : IsSc1 R.U (F ∘ R)
  isSc1_inv : IsSc1 R'.U (G ∘ R')
  mapsTo : MapsTo F R.retract R'.retract
  mapsTo_inv : MapsTo G R'.retract R.retract
  left_inv : ∀ z ∈ R.retract, G (F z) = z
  right_inv : ∀ z ∈ R'.retract, F (G z) = z

namespace IsDiffeoGerm

variable {R : ScRetraction E C} {R' : ScRetraction E' C'} {F : E 0 → E' 0} {G : E' 0 → E 0}
  (h : R.IsDiffeoGerm R' F G)
include h

lemma symm : R'.IsDiffeoGerm R G F :=
  ⟨h.isSc1_inv, h.isSc1, h.mapsTo_inv, h.mapsTo, h.right_inv, h.left_inv⟩

lemma mapsTo_U : MapsTo (F ∘ R) R.U R'.U := fun _ hz =>
  R'.retract_subset (h.mapsTo (R.apply_mem_retract hz))

lemma mapsTo_C' : MapsTo (F ∘ R) R.U C' := fun _ hz =>
  R'.retract_subset_C (h.mapsTo (R.apply_mem_retract hz))

/-- `(G ∘ r') ∘ (F ∘ r) = r` on `U`. -/
lemma comp_eq (z : E 0) (hz : z ∈ R.U) : (G ∘ R') ((F ∘ R) z) = R z := by
  simp only [Function.comp_apply, R'.apply_eq_self_of_mem_retract (h.mapsTo (R.apply_mem_retract hz)),
    h.left_inv _ (R.apply_mem_retract hz)]

omit h in
/-- An sc-smooth map between retracts, with an sc-smooth inverse, is a germ of
sc-diffeomorphisms. -/
theorem _root_.Polyfold.IsScSmoothRetractMap.isDiffeoGerm
    (hF : IsScSmoothRetractMap E C R.retract E' C' R'.retract F)
    (hG : IsScSmoothRetractMap E' C' R'.retract E C R.retract G) (hGF : ∀ z ∈ R.retract, G (F z) = z)
    (hFG : ∀ z ∈ R'.retract, F (G z) = z) : R.IsDiffeoGerm R' F G :=
  ⟨(hF.comp_isScSmooth R rfl).isSc1, (hG.comp_isScSmooth R' rfl).isSc1, hF.mapsTo, hG.mapsTo, hGF,
    hFG⟩

variable {x : E 1} (hx : x ∈ E.lvlSet R.retract 1)
include hx

/-- `y = (F ∘ r)₁(x) ∈ O'₁`. -/
lemma image_mem : levelMap (F ∘ R) 1 x ∈ E'.lvlSet R'.retract 1 :=
  h.isSc1.isSc0.levelMap_mapsTo (fun _ hz => h.mapsTo (R.apply_mem_retract hz)) 1
    ((R.lvlSet_retract_subset 1 hx))

lemma toBase_image : E'.toBase 1 (levelMap (F ∘ R) 1 x) = F (E.toBase 1 x) := by
  rw [h.isSc1.isSc0.toBase_levelMap ((R.lvlSet_retract_subset 1 hx)), Function.comp_apply,
    R.apply_eq_self_of_mem_retract hx]

/-- `(G ∘ r')₁(y) = x`. -/
lemma image_image : levelMap (G ∘ R') 1 (levelMap (F ∘ R) 1 x) = x := by
  apply levelMap_eq_of_toBase_eq
  rw [h.toBase_image hx, Function.comp_apply,
    R'.apply_eq_self_of_mem_retract (h.mapsTo hx), h.left_inv _ hx]

/-- `D(G ∘ r')(y) ∘ D(F ∘ r)(x) = Dr(x)`. -/
theorem deriv_inv_deriv (v : E 0) :
    scDeriv R'.U (G ∘ R') (levelMap (F ∘ R) 1 x) (scDeriv R.U (F ∘ R) x v) =
      scDeriv R.U R x v := by
  rw [scDeriv_comp_apply R.relOpen R'.relOpen h.isSc1 h.isSc1_inv h.mapsTo_U ((R.lvlSet_retract_subset 1 hx))]
  have hcongr : EqOn (tangentMap R.U R) (tangentMap R.U ((G ∘ R') ∘ (F ∘ R))) (E.tangentSet R.U) :=
    R.isSc1.tangentMap_congr R.isScDomain fun z hz => (h.comp_eq z hz).symm
  exact (congrArg Prod.snd (hcongr (show ((x, v) : E.tangent 0) ∈ E.tangentSet R.U from
    (R.lvlSet_retract_subset 1 hx)))).symm

/-- `D(F ∘ r)(x) ∘ D(G ∘ r')(y) = Dr'(y)`. -/
theorem deriv_deriv_inv (w : E' 0) :
    scDeriv R.U (F ∘ R) x (scDeriv R'.U (G ∘ R') (levelMap (F ∘ R) 1 x) w) =
      scDeriv R'.U R' (levelMap (F ∘ R) 1 x) w := by
  have := h.symm.deriv_inv_deriv (h.image_mem hx) w
  rwa [h.image_image hx] at this

/-- `D(F ∘ r)(x)` maps `T_xO = Dr(x)E` into `T_yO' = Dr'(y)E'`. -/
theorem deriv_mem_range {v : E 0} (hv : v ∈ range (scDeriv R.U R x)) :
    scDeriv R.U (F ∘ R) x v ∈ range (scDeriv R'.U R' (levelMap (F ∘ R) 1 x)) := by
  obtain ⟨u, rfl⟩ := hv
  refine ⟨scDeriv R.U (F ∘ R) x u, ?_⟩
  rw [← h.deriv_inv_deriv hx u, h.deriv_deriv_inv hx]

variable {n n' : ℕ} {W W' : ScBanach}

/-- The two-sided sign argument for `F ∘ r`: `D(F ∘ r)(x)(E_x) ⊆ E'_{F(x)}`. -/
theorem deriv_mapsTo_minimalSubspace (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (hT : C = T 0 ⁻¹' quadrant n W 0) (T' : ScIso E' ((ScBanach.const (Fin n' → ℝ)).prod W'))
    (hT' : C' = T' 0 ⁻¹' quadrant n' W' 0) :
    MapsTo (scDeriv R.U (F ∘ R) x) (minimalSubspaceWith T (E.toBase 1 x))
      (minimalSubspaceWith T' (F (E.toBase 1 x))) := by
  have := h.isSc1.isSc1With_scDeriv.mapsTo_minimalSubspace T hT T' hT' R.relOpen h.mapsTo_C'
    ((R.lvlSet_retract_subset 1 hx))
  rwa [Function.comp_apply, R.apply_eq_self_of_mem_retract hx] at this

/-- The one-sided sign argument for `F ∘ r`: `D(F ∘ r)(x)(C_x) ⊆ C'_{F(x)}`. -/
theorem deriv_mapsTo_partialQuadrant (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (hT : C = T 0 ⁻¹' quadrant n W 0) (T' : ScIso E' ((ScBanach.const (Fin n' → ℝ)).prod W'))
    (hT' : C' = T' 0 ⁻¹' quadrant n' W' 0) :
    MapsTo (scDeriv R.U (F ∘ R) x) (partialQuadrantAtWith T (E.toBase 1 x))
      (partialQuadrantAtWith T' (F (E.toBase 1 x))) := by
  have := h.isSc1.isSc1With_scDeriv.mapsTo_partialQuadrant T hT T' hT' R.relOpen h.mapsTo_C'
    ((R.lvlSet_retract_subset 1 hx))
  rwa [Function.comp_apply, R.apply_eq_self_of_mem_retract hx] at this

/-- **Proposition 2.4.10 (preprint 2.30)**, first half: `Tf(x)(T_x^R O) = T_y^R O'`, with `Tf(x) = D(F ∘ r)(x)`. -/
theorem _root_.Polyfold.proposition_2_4_10_reduced
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (hT : C = T 0 ⁻¹' quadrant n W 0)
    (T' : ScIso E' ((ScBanach.const (Fin n' → ℝ)).prod W')) (hT' : C' = T' 0 ⁻¹' quadrant n' W' 0) :
    (reducedTangentSpaceWith R T x).map (scDeriv R.U (F ∘ R) x : E 0 →ₗ[ℝ] E' 0) =
      reducedTangentSpaceWith R' T' (levelMap (F ∘ R) 1 x) := by
  set y := levelMap (F ∘ R) 1 x with hy
  have hy' : y ∈ E'.lvlSet R'.retract 1 := h.image_mem hx
  have hιy : E'.toBase 1 y = F (E.toBase 1 x) := h.toBase_image hx
  have hιx : E.toBase 1 x = G (E'.toBase 1 y) := by
    rw [hιy, h.left_inv _ hx]
  apply le_antisymm
  · rintro _ ⟨v, ⟨hv1, hv2⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · exact h.deriv_mem_range hx (by obtain ⟨u, hu⟩ := hv1; exact ⟨u, hu⟩)
    · change _ ∈ minimalSubspaceWith T' (E'.toBase 1 y)
      rw [hιy]
      exact h.deriv_mapsTo_minimalSubspace hx T hT T' hT' hv2
  · rintro w ⟨hw1, hw2⟩
    refine ⟨scDeriv R'.U (G ∘ R') y w, ⟨?_, ?_⟩, ?_⟩
    · -- `D'w ∈ T_xO`
      have := h.symm.deriv_mem_range hy' (by obtain ⟨u, hu⟩ := hw1; exact ⟨u, hu⟩)
      rw [h.image_image hx] at this
      obtain ⟨u, hu⟩ := this; exact ⟨u, hu⟩
    · have := h.symm.deriv_mapsTo_minimalSubspace hy' T' hT' T hT hw2
      rwa [← hιx] at this
    · change scDeriv R.U (F ∘ R) x (scDeriv R'.U (G ∘ R') y w) = w
      rw [h.deriv_deriv_inv hx]
      obtain ⟨u, rfl⟩ := hw1
      exact congrArg (fun L : E' 0 →L[ℝ] E' 0 => L u) (R'.scDeriv_comp_self hy')

/-- **Proposition 2.4.10 (preprint 2.30)**, second half: `Tf(x)(C_xO) = C_yO'`. -/
theorem _root_.Polyfold.proposition_2_4_10_cone
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (hT : C = T 0 ⁻¹' quadrant n W 0)
    (T' : ScIso E' ((ScBanach.const (Fin n' → ℝ)).prod W')) (hT' : C' = T' 0 ⁻¹' quadrant n' W' 0) :
    scDeriv R.U (F ∘ R) x '' partialConeWith R T x =
      partialConeWith R' T' (levelMap (F ∘ R) 1 x) := by
  set y := levelMap (F ∘ R) 1 x with hy
  have hy' : y ∈ E'.lvlSet R'.retract 1 := h.image_mem hx
  have hιy : E'.toBase 1 y = F (E.toBase 1 x) := h.toBase_image hx
  have hιx : E.toBase 1 x = G (E'.toBase 1 y) := by
    rw [hιy, h.left_inv _ hx]
  apply Subset.antisymm
  · rintro _ ⟨v, ⟨hv1, hv2⟩, rfl⟩
    refine ⟨h.deriv_mem_range hx hv1, ?_⟩
    rw [hιy]
    exact h.deriv_mapsTo_partialQuadrant hx T hT T' hT' hv2
  · rintro w ⟨hw1, hw2⟩
    refine ⟨scDeriv R'.U (G ∘ R') y w, ⟨?_, ?_⟩, ?_⟩
    · have := h.symm.deriv_mem_range hy' hw1
      rwa [h.image_image hx] at this
    · have := h.symm.deriv_mapsTo_partialQuadrant hy' T' hT' T hT hw2
      rwa [← hιx] at this
    · change scDeriv R.U (F ∘ R) x (scDeriv R'.U (G ∘ R') y w) = w
      rw [h.deriv_deriv_inv hx]
      obtain ⟨u, rfl⟩ := hw1
      exact congrArg (fun L : E' 0 →L[ℝ] E' 0 => L u) (R'.scDeriv_comp_self hy')

end IsDiffeoGerm

end ScRetraction

/-! ### The dimension `dim(T_xO / T_x^R O)` and Theorem 2.4.12 (preprint 2.31) -/

/-- `dim(A / (A ∩ B))` for subspaces `A`, `B` of a vector space, as a natural number (`0` if
infinite): the quotient of `A` by the trace of `B` on it. -/
def quotDim {V : Type*} [AddCommGroup V] [Module ℝ V] (A B : Submodule ℝ V) : ℕ :=
  finrank ℝ (A ⧸ B.comap A.subtype)

lemma quotDim_congr {V : Type*} [AddCommGroup V] [Module ℝ V] {A A' B B' : Submodule ℝ V}
    (hA : A = A') (hB : B = B') : quotDim A B = quotDim A' B' := by
  subst hA; subst hB; rfl

section QuotDim

variable {n : ℕ} {W : ScBanach}

/-- `A / (A ∩ E_e)` embeds in `E / E_e`: the map `A → E/E_e` has kernel `A ∩ E_e`. -/
theorem quotDim_inf_minimalSubspace_le (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (A : Submodule ℝ (E 0)) (e : E 0) :
    quotDim A (A ⊓ minimalSubspaceWith T e) ≤ degIndexWith T e := by
  set Ex := minimalSubspaceWith T e
  let Ψ : A →ₗ[ℝ] E 0 ⧸ Ex := Ex.mkQ.comp A.subtype
  have hΨker : LinearMap.ker Ψ = (A ⊓ Ex).comap A.subtype := by
    ext ⟨w, hw⟩
    simp only [Ψ, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.mem_inf]
    exact ⟨fun h => ⟨hw, h⟩, fun h => h.2⟩
  have hemb : (A ⧸ (A ⊓ Ex).comap A.subtype) ≃ₗ[ℝ] LinearMap.range Ψ :=
    hΨker ▸ Ψ.quotKerEquivRange
  rw [quotDim, ← finrank_quotient_minimalSubspaceWith T, hemb.finrank_eq]
  exact Submodule.finrank_le _

instance finiteDimensional_quot_inf_minimalSubspace
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (A : Submodule ℝ (E 0)) (e : E 0) :
    FiniteDimensional ℝ (A ⧸ (A ⊓ minimalSubspaceWith T e).comap A.subtype) := by
  set Ex := minimalSubspaceWith T e
  let Ψ : A →ₗ[ℝ] E 0 ⧸ Ex := Ex.mkQ.comp A.subtype
  have hΨker : LinearMap.ker Ψ = (A ⊓ Ex).comap A.subtype := by
    ext ⟨w, hw⟩
    simp only [Ψ, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.mem_inf]
    exact ⟨fun h => ⟨hw, h⟩, fun h => h.2⟩
  have hemb : (A ⧸ (A ⊓ Ex).comap A.subtype) ≃ₗ[ℝ] LinearMap.range Ψ :=
    hΨker ▸ Ψ.quotKerEquivRange
  exact LinearEquiv.finiteDimensional hemb.symm

variable {C : Set (E 0)}

/-- The trivial inequality `dim(T_xO/T_x^R O) ≤ d_C(x)` (the inequality `d_O ≤ d_C` seen in the
tangent space). -/
theorem quotDim_reducedTangentSpaceWith_le (R : ScRetraction E C)
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (x : E 1) :
    quotDim (LinearMap.range (scDeriv R.U R x : E 0 →ₗ[ℝ] E 0)) (reducedTangentSpaceWith R T x) ≤
      degIndexWith T (E.toBase 1 x) :=
  quotDim_inf_minimalSubspace_le T _ _

/-- The restriction of a retraction to `U ∩ r⁻¹(W)` has the same derivative at points of the
smaller domain. -/
theorem ScRetraction.scDeriv_restrict (R : ScRetraction E C) {V : Set (E 0)} (hV : IsOpen V)
    {x : E 1} (hx : x ∈ E.lvlSet (R.restrict hV).U 1) :
    scDeriv (R.restrict hV).U (R.restrict hV) x = scDeriv R.U R x := by
  ext v
  have h := R.isSc1.tangentMap_eqOn_of_subset (R.restrict hV).isScDomain inter_subset_left
    (show ((x, v) : E.tangent 0) ∈ E.tangentSet (R.restrict hV).U from hx)
  exact congrArg Prod.snd h

theorem reducedTangentSpaceWith_restrict (R : ScRetraction E C) {V : Set (E 0)} (hV : IsOpen V)
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) {x : E 1}
    (hx : x ∈ E.lvlSet (R.restrict hV).U 1) :
    reducedTangentSpaceWith (R.restrict hV) T x = reducedTangentSpaceWith R T x := by
  unfold reducedTangentSpaceWith
  rw [R.scDeriv_restrict hV hx]

end QuotDim

namespace ScRetraction.IsDiffeoGerm

variable {n n' : ℕ} {W W' : ScBanach} {C : Set (E 0)} {C' : Set (E' 0)} {R : ScRetraction E C}
  {R' : ScRetraction E' C'} {F : E 0 → E' 0} {G : E' 0 → E 0}

/-- **The core of Theorem 2.4.12 (preprint 2.31)**: along a germ of sc-diffeomorphisms `F : (O, x) → (O', F(x))`
between retracts, `dim(T_xO/T_x^R O) ≤ d_{C'}(F(x))` for `x ∈ O₁`.

*Proof.* With `D = D(F ∘ r)(x)`, `D' = D(G ∘ r')(y)`: `D' ∘ D = Dr(x)`, `D ∘ D' = Dr'(y)`,
`D(E_x) ⊆ E'_y`, `D'(E'_y) ⊆ E_x`, so `D` induces `T_xO/T_x^R O ≅ T_yO'/T_y^R O'`, which embeds in
`E'/E'_y`, of dimension `d_{C'}(y)`. -/
theorem quotDim_le (h : R.IsDiffeoGerm R' F G) (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (hT : C = T 0 ⁻¹' quadrant n W 0) (T' : ScIso E' ((ScBanach.const (Fin n' → ℝ)).prod W'))
    (hT' : C' = T' 0 ⁻¹' quadrant n' W' 0) {x : E 1} (hx : x ∈ E.lvlSet R.retract 1) :
    quotDim (LinearMap.range (scDeriv R.U R x : E 0 →ₗ[ℝ] E 0)) (reducedTangentSpaceWith R T x) ≤
      degIndexWith T' (F (E.toBase 1 x)) := by
  classical
  set ι := E.toBase 1 with hι
  set y : E' 1 := levelMap (F ∘ R) 1 x with hy
  have hy' : y ∈ E'.lvlSet R'.retract 1 := h.image_mem hx
  have hιy : E'.toBase 1 y = F (ι x) := h.toBase_image hx
  set D : E 0 →L[ℝ] E' 0 := scDeriv R.U (F ∘ R) x with hD
  set D' : E' 0 →L[ℝ] E 0 := scDeriv R'.U (G ∘ R') y with hD'
  set P : E 0 →L[ℝ] E 0 := scDeriv R.U R x with hP
  set P' : E' 0 →L[ℝ] E' 0 := scDeriv R'.U R' y with hP'
  have hD'D : ∀ v, D' (D v) = P v := h.deriv_inv_deriv hx
  have hDD' : ∀ w, D (D' w) = P' w := h.deriv_deriv_inv hx
  have hPP : ∀ v, P (P v) = P v := fun v =>
    congrArg (fun L : E 0 →L[ℝ] E 0 => L v) (R.scDeriv_comp_self hx)
  have hP'P' : ∀ w, P' (P' w) = P' w := fun w =>
    congrArg (fun L : E' 0 →L[ℝ] E' 0 => L w) (R'.scDeriv_comp_self hy')
  set Ex : Submodule ℝ (E 0) := minimalSubspaceWith T (ι x) with hEx
  set Ey : Submodule ℝ (E' 0) := minimalSubspaceWith T' (F (ι x)) with hEy
  have hDmaps : MapsTo D Ex Ey := h.deriv_mapsTo_minimalSubspace hx T hT T' hT'
  have hD'maps : MapsTo D' Ey Ex := by
    have := h.symm.deriv_mapsTo_minimalSubspace hy' T' hT' T hT
    rw [hιy, h.left_inv _ hx] at this
    exact this
  set Tx : Submodule ℝ (E 0) := LinearMap.range (P : E 0 →ₗ[ℝ] E 0) with hTx
  set Ty : Submodule ℝ (E' 0) := LinearMap.range (P' : E' 0 →ₗ[ℝ] E' 0) with hTy
  have hTxP : ∀ v ∈ Tx, P v = v := by
    rintro _ ⟨u, rfl⟩; exact hPP u
  have hTyP' : ∀ w ∈ Ty, P' w = w := by
    rintro _ ⟨u, rfl⟩; exact hP'P' u
  have hDTy : ∀ v ∈ Tx, D v ∈ Ty := by
    rintro _ ⟨u, rfl⟩
    exact ⟨D u, by change P' (D u) = D (P u); rw [← hD'D, hDD']⟩
  have hD'Tx : ∀ w ∈ Ty, D' w ∈ Tx := by
    rintro _ ⟨u, rfl⟩
    exact ⟨D' u, by change P (D' u) = D' (P' u); rw [← hDD', hD'D]⟩
  -- the reduced spaces as traces
  have hTR : reducedTangentSpaceWith R T x = Tx ⊓ Ex := rfl
  have hTR' : reducedTangentSpaceWith R' T' y = Ty ⊓ minimalSubspaceWith T' (E'.toBase 1 y) := rfl
  -- `Φ : T_xO → T_yO' / T_y^R O'`
  let Dt : Tx →ₗ[ℝ] Ty := (D : E 0 →ₗ[ℝ] E' 0).restrict hDTy
  let Φ : Tx →ₗ[ℝ] Ty ⧸ (Ty ⊓ Ey).comap Ty.subtype := ((Ty ⊓ Ey).comap Ty.subtype).mkQ.comp Dt
  have hΦsurj : Surjective Φ := by
    intro q
    obtain ⟨⟨w, hw⟩, rfl⟩ := ((Ty ⊓ Ey).comap Ty.subtype).mkQ_surjective q
    refine ⟨⟨D' w, hD'Tx w hw⟩, ?_⟩
    simp only [Φ, Dt, LinearMap.comp_apply, Submodule.mkQ_apply]
    congr 1
    apply Subtype.ext
    change D (D' w) = w
    rw [hDD', hTyP' w hw]
  have hΦker : LinearMap.ker Φ = (Tx ⊓ Ex).comap Tx.subtype := by
    ext ⟨v, hv⟩
    simp only [Φ, Dt, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply,
      Submodule.mem_inf, LinearMap.restrict_apply, LinearMap.coe_coe]
    constructor
    · rintro ⟨_, hh⟩
      refine ⟨hv, ?_⟩
      have h1 : D' (D v) ∈ Ex := hD'maps hh
      rwa [hD'D, hTxP v hv] at h1
    · rintro ⟨_, hh⟩
      exact ⟨hDTy v hv, hDmaps hh⟩
  have hiso : (Tx ⧸ (Tx ⊓ Ex).comap Tx.subtype) ≃ₗ[ℝ] (Ty ⧸ (Ty ⊓ Ey).comap Ty.subtype) :=
    hΦker ▸ Φ.quotKerEquivOfSurjective hΦsurj
  calc quotDim Tx (reducedTangentSpaceWith R T x)
      = finrank ℝ (Tx ⧸ (Tx ⊓ Ex).comap Tx.subtype) := by rw [hTR]; rfl
    _ = finrank ℝ (Ty ⧸ (Ty ⊓ Ey).comap Ty.subtype) := hiso.finrank_eq
    _ = quotDim Ty (Ty ⊓ Ey) := rfl
    _ ≤ degIndexWith T' (F (ι x)) := quotDim_inf_minimalSubspace_le T' Ty (F (ι x))

end ScRetraction.IsDiffeoGerm

/-! ### Theorem 2.4.12 (preprint 2.31) for M-polyfolds -/

namespace MChart

variable {X : Type*} [TopologicalSpace X]

/-- Two compatible charts give a germ of sc-diffeomorphisms `ψ ∘ φ⁻¹` between the overlap
retracts `φ(V ∩ V') = O ∩ W` and `ψ(V ∩ V') = O' ∩ W'`, with the restricted retractions. -/
theorem Compatible.isDiffeoGerm {φ ψ : MChart X} (h : φ.Compatible ψ)
    (R : ScRetraction φ.model.E φ.model.C) (hR : R.retract = φ.model.O)
    (R' : ScRetraction ψ.model.E ψ.model.C) (hR' : R'.retract = ψ.model.O) {W : Set (φ.model.E 0)}
    (hW : IsOpen W) (hWeq : φ.overlap ψ = φ.model.O ∩ W) {W' : Set (ψ.model.E 0)} (hW' : IsOpen W')
    (hW'eq : ψ.overlap φ = ψ.model.O ∩ W') :
    (R.restrict hW).IsDiffeoGerm (R'.restrict hW') (φ.transition ψ) (ψ.transition φ) := by
  have h1 : (R.restrict hW).retract = φ.overlap ψ := by rw [R.restrict_retract, hR, hWeq]
  have h2 : (R'.restrict hW').retract = ψ.overlap φ := by rw [R'.restrict_retract, hR', hW'eq]
  refine ⟨(h.1.comp_isScSmooth _ h1).isSc1, (h.2.comp_isScSmooth _ h2).isSc1, ?_, ?_, ?_, ?_⟩
  · rw [h1, h2]; exact h.1.mapsTo
  · rw [h1, h2]; exact h.2.mapsTo
  · rw [h1]
    rintro _ ⟨x, hx, rfl⟩
    rw [φ.transition_apply ψ hx.1, ψ.transition_apply φ hx.2]
  · rw [h2]
    rintro _ ⟨x, hx, rfl⟩
    rw [ψ.transition_apply φ hx.1, φ.transition_apply ψ hx.2]

end MChart

namespace MPolyfold

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)
  {n : ℕ} {W : ScBanach}

/-- For two charts `φ`, `ψ` of the structure around `x`, a retraction `r` onto `O = φ(V)` and a
presentation `T` of `C`: `dim(T_{φ(x)}O / T^R_{φ(x)}O) ≤ d_{C'}(ψ(x))` at a point `φ(x)` on level
`1` (the germ `ψ ∘ φ⁻¹` on `φ(V ∩ V')`). -/
theorem quotDim_le_chartDegIndex {φ ψ : MChart X} (hφ : P.IsChart φ) (hψ : P.IsChart ψ)
    (R : ScRetraction φ.model.E φ.model.C) (hR : R.retract = φ.model.O)
    (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W))
    (hT : φ.model.C = T 0 ⁻¹' quadrant n W 0) {x : X} (hx : x ∈ φ.source) (hx' : x ∈ ψ.source)
    {z : φ.model.E 1} (hz : φ.model.E.toBase 1 z = φ x) :
    quotDim (LinearMap.range (scDeriv R.U R z : φ.model.E 0 →ₗ[ℝ] φ.model.E 0))
      (reducedTangentSpaceWith R T z) ≤ chartDegIndex ψ x := by
  obtain ⟨W₀, hW₀, hW₀eq⟩ := φ.exists_isOpen_image_eq (s := φ.source ∩ ψ.source) inter_subset_left
    (φ.isOpen_source.inter ψ.isOpen_source)
  obtain ⟨W₀', hW₀', hW₀'eq⟩ := ψ.exists_isOpen_image_eq (s := ψ.source ∩ φ.source) inter_subset_left
    (ψ.isOpen_source.inter φ.isOpen_source)
  obtain ⟨R', hR'⟩ := ψ.model.isScRetract
  obtain ⟨n', W', T', hT'⟩ := ψ.model.isPartialQuadrant
  have germ := (hφ.compatible hψ (P := P)).isDiffeoGerm R hR R' hR' hW₀ hW₀eq hW₀' hW₀'eq
  have hzO : z ∈ φ.model.E.lvlSet (R.restrict hW₀).retract 1 := by
    rw [ScBanach.mem_lvlSet, hz, R.restrict_retract, hR, ← hW₀eq]
    exact φ.mem_overlap ψ hx hx'
  have key := germ.quotDim_le T hT T' hT' hzO
  have hzU : z ∈ φ.model.E.lvlSet (R.restrict hW₀).U 1 := (R.restrict hW₀).lvlSet_retract_subset 1 hzO
  rw [reducedTangentSpaceWith_restrict R hW₀ T hzU, hz, φ.transition_apply ψ hx] at key
  have hder : scDeriv (R.restrict hW₀).U (R.restrict hW₀) z = scDeriv R.U R z :=
    R.scDeriv_restrict hW₀ hzU
  rw [hder] at key
  rw [chartDegIndex, degIndex_eq T' hT' (ψ.apply_mem_C hx')]
  exact key

/-- **Theorem 2.4.12 (preprint 2.31)**, for every M-polyfold: for a chart `φ` of `X` around `x` with `φ(x)` on level
`1`, a retraction `r` onto `O = φ(V)` and a presentation `T` of `C`,
`dim(T_{φ(x)}O / T^R_{φ(x)}O) ≤ d_X(x)`. -/
theorem _root_.Polyfold.theorem_2_4_12 {φ : MChart X} (hφ : P.IsChart φ)
    (R : ScRetraction φ.model.E φ.model.C) (hR : R.retract = φ.model.O)
    (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W))
    (hT : φ.model.C = T 0 ⁻¹' quadrant n W 0) {x : X} (hx : x ∈ φ.source) {z : φ.model.E 1}
    (hz : φ.model.E.toBase 1 z = φ x) :
    quotDim (LinearMap.range (scDeriv R.U R z : φ.model.E 0 →ₗ[ℝ] φ.model.E 0))
      (reducedTangentSpaceWith R T z) ≤ P.degIndex x := by
  obtain ⟨ψ, hψ, hxψ, hd⟩ := P.exists_isChart_degIndex_eq x
  rw [hd]
  exact P.quotDim_le_chartDegIndex hφ hψ R hR T hT hx hxψ hz

end MPolyfold

/-- **Theorem 2.4.12 (preprint 2.31)** in the text's form: for an sc-smooth retract `(O, C, E)` viewed as the
M-polyfold with the single chart `id` (`LocalModel.toMPolyfold`), a retraction `r` onto `O` and
`x ∈ O₁`: `dim(T_xO / T_x^R O) ≤ d_O(x)`. -/
theorem theorem_2_4_12_retract (M : LocalModel) (hO : M.O.Nonempty) (R : ScRetraction M.E M.C)
    (hR : R.retract = M.O) {n : ℕ} {W : ScBanach} (T : ScIso M.E ((ScBanach.const (Fin n → ℝ)).prod W))
    (hT : M.C = T 0 ⁻¹' quadrant n W 0) {x : M.E 1} (hx : x ∈ M.E.lvlSet M.O 1) :
    quotDim (LinearMap.range (scDeriv R.U R x : M.E 0 →ₗ[ℝ] M.E 0)) (reducedTangentSpaceWith R T x) ≤
      (M.toMPolyfold hO).degIndex ⟨M.E.toBase 1 x, hx⟩ :=
  theorem_2_4_12 (M.toMPolyfold hO) ((M.toMPolyfold hO).isChart_of_mem (mem_singleton _)) R hR T hT
    (mem_univ _) rfl

end Polyfold
