import Polyfold.Chapter15.P3T_SeparationLemmas
import Polyfold.Chapter3.LinearizationCharts
import Polyfold.Chapter3.StrongBundleSections

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 15,
§15.1 (pp. 683–687): **Theorem 15.1.1** (2017: Theorem 15.1) on a strong bundle model, the
setting to which its proof reduces ("without loss of generality `X = O`"), and **Remark 15.1.2**
(2017: Remark 15.1).

# The linearization `T(f, Λ)` on a strong bundle model

## The text, paraphrased

(p. 683) For a smooth `x`, `GrF(x)` is the set of finite formal sums `∑ σ_L · L` with
nonnegative rational coefficients of sc-Fredholm operators `L : T_xX → W_x`.  (Theorem 15.1.1)
For an sc-Fredholm section `f` and an sc⁺-multisection `Λ` there is a section functor
`T(f,Λ)` of `GrF(X) → X_∞` with (1) `T(f,Λ)(x) = 0` off `supp(Λ ∘ f)`, (2) for any local
sc⁺-section structure `(sᵢ, σᵢ)` describing `Λ` near `x ∈ supp(Λ ∘ f)`,
`T(f,Λ)(y) = ∑_{i : f(y) = sᵢ(y)} σᵢ · (f − sᵢ)'(y)` at smooth `y` near `x`.  (Remark 15.1.2)
With the empty sum `0`, (1) follows from (2).  The proof reduces to a local model `O`, `x = 0`,
and shows that two structures give the same sum (Proposition 15.1.3, Lemmas 15.1.4–15.1.5).

## What is formalized (namespace `Polyfold.Linearization15`)

On a strong bundle model `U ◁ F` (`U` relatively open in a partial quadrant, `R` a strong bundle
retraction, `O = r(U)`), with principal parts `f̂` and `ŝᵢ` such that `f̂ ∘ r`, `ŝᵢ ∘ r` are
sc-smooth on `U`:

* `GrFModel U R z`: finite formal sums `(T_zO →L F) →₀ ℚ≥0` of operators at the level-`1`
  point `z` (`T_zO = Dr(z)E`, as in Part I's `linAt`).
* `linSumModel U R f̂ ŝ σ z = ∑_{i : ŝᵢ(z) = f̂(z)} σᵢ · (f̂ − ŝᵢ)'(z)`, with
  `(f̂ − ŝᵢ)'(z) = linAt U R (f̂ − ŝᵢ) z = D((f̂ − ŝᵢ) ∘ r)(z)|_{T_zO}`.
* **`theorem_15_1_1_model`**: if two local structures `(ŝᵢ, σᵢ)`, `(t̂ⱼ, τⱼ)` give the same
  weighted count `∑_{i : ŝᵢ(y) = v} σᵢ = ∑_{j : t̂ⱼ(y) = v} τⱼ` at every `y ∈ O ∩ N` (`N` open; the
  two describe the same `Λ` there), then `linSumModel` is the same for both at **every** level-`1`
  point of `O ∩ N` (the text: smooth points).
* **Remark 15.1.2**: `remark_15_1_2_model` — with positive weights, `linSumModel = 0` where the
  weighted count of `f̂(y)` is `0` (the formal sum is empty).
* `mem_support_linSumModel_iff`: the operators with nonzero coefficient are the `(f̂ − ŝᵢ)'(z)`
  with `ŝᵢ(y) = f̂(y)` (positive weights), the form used by Definition 15.2.1.
* `scDeriv_eq_of_eventuallyEq_lvl`: the derivative of an sc¹ map at a level-`1` point depends
  only on its values near the point in the level-`1` topology.

## Reading (Findings: the route of the proof of Theorem 15.1.1)

The text's proof takes the points `x_k` of Proposition 15.1.3 in the metric of `E₀` and passes to
the limit in `T(f − sᵢ)(x_k)`.  The derivative `x ↦ D(f − sᵢ)(x)` of an sc¹ map is continuous
only on `O₁` (in the level-`1` topology, pointwise on `E₀`, Definition 1.1.15 (3)); so here the
separation argument runs in the level-`1` topology (on the subspace `U₁ ⊆ E₁`), where it holds
as well (the separation lemmas of `P3T_SeparationLemmas.lean` hold in any topological space),
and the "weak topology" of the text is the topology of pointwise convergence of operators
`E₀ → F₀`.  The last step of the text sums over all `i` as if `sᵢ(0) = f(0)` for every `i`; here
the formal sums of the pairs `(sᵢ(0), (f − sᵢ)'(0))` are compared, and the terms with
`sᵢ(0) = f(0)` are then selected.  The statement itself holds as printed, at all level-`1` points.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

namespace Linearization15

open StrongRetr

variable {E F : ScBanach} {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

/-! ### Two facts of the sc-calculus at level `1` -/

/-- The derivative of an sc¹ map at a level-`1` point depends only on its values near the point in
the level-`1` topology (uniqueness of the derivative within `U₁` and the density of `E₁`). -/
theorem scDeriv_eq_of_eventuallyEq_lvl (hU : IsScDomain E U) {g g' : E 0 → F 0} (hg : IsSc1 U g)
    (hg' : IsSc1 U g') {x : E 1} (hx : x ∈ E.lvlSet U 1)
    (h : (g ∘ E.toBase 1) =ᶠ[𝓝[E.lvlSet U 1] x] (g' ∘ E.toBase 1)) :
    scDeriv U g x = scDeriv U g' x := by
  apply ContinuousLinearMap.ext_of_comp_toBase_one (E := E)
  have d := hg.isSc1With_scDeriv.hasFDerivWithinAt x hx
  have d' := hg'.isSc1With_scDeriv.hasFDerivWithinAt x hx
  have d2 : HasFDerivWithinAt (g ∘ E.toBase 1) ((scDeriv U g' x).comp (E.toBase 1))
      (E.lvlSet U 1) x := d'.congr_of_eventuallyEq h (h.self_of_nhdsWithin hx)
  exact (hU.uniqueDiffWithinAt 1 x hx).eq d d2

/-- An sc⁰ map is continuous on `U₁` in the level-`1` topology, read in `F₀`. -/
theorem continuousOn_comp_toBase_one {E' : ScBanach} {g : E 0 → E' 0} (hg : IsSc0 E E' U g) :
    ContinuousOn (fun u : E 1 => g (E.toBase 1 u)) (E.lvlSet U 1) :=
  ((E'.toBase 1).continuous.comp_continuousOn (hg.continuousOn 1)).congr fun _ hu =>
    (hg.toBase_levelMap hu).symm

/-- The derivative of an sc¹ map is continuous on `U₁` (level-`1` topology) for the topology of
pointwise convergence of operators `E₀ → F₀` (Definition 1.1.15 (3)). -/
theorem continuousOn_scDeriv_coe {g : E 0 → F 0} (hg : IsSc1 U g) :
    ContinuousOn (fun u : E 1 => (⇑(scDeriv U g u) : E 0 → F 0)) (E.lvlSet U 1) := by
  refine continuousOn_pi.2 fun h => ?_
  exact hg.isSc1With_scDeriv.continuousOn_deriv.comp
    (continuous_id.prodMk continuous_const).continuousOn fun _ hu => hu

/-! ### `GrF` and the formal sum on the model -/

/-- **`GrF(x)` on the model** (2021 p. 683): finite formal sums with nonnegative rational
coefficients of operators `T_zO → F` at the level-`1` point `z` (`T_zO = Dr(z)E`, the text's
`T_xX` read in the chart). -/
abbrev GrFModel (U : Set (E 0)) (R : E 0 × F 0 → E 0 × F 0) (z : E 1) : Type _ :=
  (↥(rangeS (scDeriv U (r R) z)) →L[ℝ] F 0) →₀ ℚ≥0

open Classical in
/-- **`∑_{i : f(y) = sᵢ(y)} σᵢ · (f − sᵢ)'(y)` on the model** (Theorem 15.1.1 (2)), at the
level-`1` point `z` over `y`: the operators `(f̂ − ŝᵢ)'(z) = linAt U R (f̂ − ŝᵢ) z`. -/
def linSumModel (U : Set (E 0)) (R : E 0 × F 0 → E 0 × F 0) (fh : E 0 → F 0) {k : ℕ}
    (sh : Fin k → E 0 → F 0) (σ : Fin k → ℚ≥0) (z : E 1) : GrFModel U R z :=
  ∑ i, if sh i (E.toBase 1 z) = fh (E.toBase 1 z) then
    Finsupp.single (linAt U R (fun y => fh y - sh i y) z) (σ i) else 0

open Classical in
theorem linSumModel_apply (fh : E 0 → F 0) {k : ℕ} (sh : Fin k → E 0 → F 0) (σ : Fin k → ℚ≥0)
    (z : E 1) (ℓ : ↥(rangeS (scDeriv U (r R) z)) →L[ℝ] F 0) :
    linSumModel U R fh sh σ z ℓ = ∑ i, if sh i (E.toBase 1 z) = fh (E.toBase 1 z) ∧
      linAt U R (fun y => fh y - sh i y) z = ℓ then σ i else 0 := by
  unfold linSumModel
  rw [Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h1 : sh i (E.toBase 1 z) = fh (E.toBase 1 z)
  · by_cases h2 : linAt U R (fun y => fh y - sh i y) z = ℓ
    · rw [if_pos h1, if_pos ⟨h1, h2⟩, Finsupp.single_apply, if_pos h2]
    · rw [if_pos h1, if_neg fun h => h2 h.2, Finsupp.single_apply, if_neg h2]
  · rw [if_neg h1, if_neg fun h => h1 h.1, Finsupp.coe_zero, Pi.zero_apply]

/-! ### Theorem 15.1.1 on the model -/

open Classical in
/-- **The core of Theorem 15.1.1 on the model**: two local structures `(ŝᵢ, σᵢ)`, `(t̂ⱼ, τⱼ)`
describing the same multisection on `O ∩ N` give the same finite formal sum of the pairs
`(ŝᵢ(y), D((f̂ − ŝᵢ) ∘ r)(z))` (ambient derivatives `E₀ → F₀`, as functions) at every level-`1`
point `z` over `y ∈ O ∩ N`. -/
theorem wsum_model_eq (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    {fh : E 0 → F 0} (hf : IsScSmooth U (fh ∘ r R)) {k l : ℕ} {sh : Fin k → E 0 → F 0}
    {σ : Fin k → ℚ≥0} {th : Fin l → E 0 → F 0} {τ : Fin l → ℚ≥0}
    (hs : ∀ i, IsScSmooth U (sh i ∘ r R)) (ht : ∀ j, IsScSmooth U (th j ∘ r R))
    {N : Set (E 0)} (hN : IsOpen N)
    (hΛ : ∀ y ∈ r R '' U, y ∈ N → ∀ v : F 0,
      (∑ i, if sh i y = v then σ i else 0) = ∑ j, if th j y = v then τ j else 0)
    {z : E 1} (hz : E.toBase 1 z ∈ r R '' U) (hzN : E.toBase 1 z ∈ N)
    (q : F 0 × (E 0 → F 0)) :
    wsum (fun i => (sh i (r R (E.toBase 1 z)),
      (⇑(scDeriv U ((fun y => fh y - sh i y) ∘ r R) z) : E 0 → F 0))) σ q =
    wsum (fun j => (th j (r R (E.toBase 1 z)),
      (⇑(scDeriv U ((fun y => fh y - th j y) ∘ r R) z) : E 0 → F 0))) τ q := by
  have hUd := hU.isScDomain
  -- the combined family of branches and their composites with `r`
  set sc : Fin k ⊕ Fin l → E 0 → F 0 := Sum.elim sh th with hscdef
  have hsc : ∀ α, IsScSmooth U (sc α ∘ r R) := fun α => by
    cases α with
    | inl i => exact hs i
    | inr j => exact ht j
  set G : Fin k ⊕ Fin l → E 0 → F 0 := fun α => (fun y => fh y - sc α y) ∘ r R with hGdef
  have hG : ∀ α, IsSc1 U (G α) := fun α => (hf.sub hUd (hsc α)).isSc1
  -- the space `U₁` (level-`1` topology) and the open set `V` over `N`
  let Z := ↥(E.lvlSet U 1)
  have hr0 : IsSc0 E E U (r R) := (r_isScSmooth hU hR).isSc1.isSc0
  have hrc : Continuous fun u : Z => r R (E.toBase 1 (u : E 1)) :=
    (continuousOn_comp_toBase_one hr0).domRestrict
  set V : Set Z := {u | r R (E.toBase 1 (u : E 1)) ∈ N} with hVdef
  have hV : IsOpen V := hN.preimage hrc
  let c : Fin k ⊕ Fin l → Z → F 0 := fun α u => sc α (r R (E.toBase 1 (u : E 1)))
  let D : Fin k ⊕ Fin l → Z → (E 0 → F 0) := fun α u => ⇑(scDeriv U (G α) (u : E 1))
  have hc : ∀ α, ContinuousOn (c α) V := fun α =>
    (continuousOn_comp_toBase_one (hsc α).isSc1.isSc0).domRestrict.continuousOn
  have hD : ∀ α, ContinuousOn (D α) V := fun α =>
    (continuousOn_scDeriv_coe (hG α)).domRestrict.continuousOn
  have hcount : ∀ u ∈ V, ∀ v, wsum (fun i => c (.inl i) u) σ v =
      wsum (fun j => c (.inr j) u) τ v := fun u hu v =>
    hΛ _ ⟨_, u.2, rfl⟩ hu v
  have hloc : ∀ u ∈ V, ∀ α β, c α =ᶠ[𝓝 u] c β → D α u = D β u := by
    intro u _ α β h
    refine congrArg DFunLike.coe (scDeriv_eq_of_eventuallyEq_lvl hUd (hG α) (hG β) u.2 ?_)
    rw [nhdsWithin_eq_map_subtype_coe u.2, Filter.EventuallyEq, Filter.eventually_map]
    filter_upwards [h] with w hw
    change fh _ - c α w = fh _ - c β w
    rw [hw]
  have hzU : z ∈ E.lvlSet U 1 := mem_U_of_mem_O hR hz
  exact wsum_pair_eq_of_isLocal c D σ τ hV hc hD hcount hloc (x₀ := ⟨z, hzU⟩)
    (by change r R (E.toBase 1 z) ∈ N; rw [r_eq_self hR hz]; exact hzN) q

open Classical in
/-- **Theorem 15.1.1 (2017: Theorem 15.1), pp. 684–687, on a strong bundle model**: two local
structures `(ŝᵢ, σᵢ)_{i<k}`, `(t̂ⱼ, τⱼ)_{j<l}` (principal parts with `ŝᵢ ∘ r`, `t̂ⱼ ∘ r`
sc-smooth on `U`) describing the same multisection on `O ∩ N` (equal weighted counts of every
value `v` at every `y ∈ O ∩ N`) give the same formal sum
`∑_{i : ŝᵢ(y) = f̂(y)} σᵢ · (f̂ − ŝᵢ)'(y)` at every level-`1` point `y` of `O ∩ N`, for any `f̂`
with `f̂ ∘ r` sc-smooth.  This is the well-definedness of `T(f,Λ)` in the text's reduction
"`X = O`, `x = 0`", at all level-`1` (in particular all smooth) points near `x`. -/
theorem theorem_15_1_1_model (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    {fh : E 0 → F 0} (hf : IsScSmooth U (fh ∘ r R)) {k l : ℕ} {sh : Fin k → E 0 → F 0}
    {σ : Fin k → ℚ≥0} {th : Fin l → E 0 → F 0} {τ : Fin l → ℚ≥0}
    (hs : ∀ i, IsScSmooth U (sh i ∘ r R)) (ht : ∀ j, IsScSmooth U (th j ∘ r R))
    {N : Set (E 0)} (hN : IsOpen N)
    (hΛ : ∀ y ∈ r R '' U, y ∈ N → ∀ v : F 0,
      (∑ i, if sh i y = v then σ i else 0) = ∑ j, if th j y = v then τ j else 0)
    {z : E 1} (hz : E.toBase 1 z ∈ r R '' U) (hzN : E.toBase 1 z ∈ N) :
    linSumModel U R fh sh σ z = linSumModel U R fh th τ z := by
  have hcore := wsum_model_eq hU hR hf hs ht hN hΛ hz hzN
  have hrz : r R (E.toBase 1 z) = E.toBase 1 z := r_eq_self hR hz
  refine Finsupp.ext fun ℓ => ?_
  set Nℓ : Set (F 0 × (E 0 → F 0)) :=
    {q | q.1 = fh (E.toBase 1 z) ∧ ∀ x : ↥(rangeS (scDeriv U (r R) z)), q.2 x = ℓ x} with hNℓ
  have hmass := mass_eq_of_wsum_eq hcore Nℓ
  have hlin : ∀ (g : E 0 → F 0),
      (linAt U R g z = ℓ ↔ ∀ x : ↥(rangeS (scDeriv U (r R) z)),
        scDeriv U (g ∘ r R) z x = ℓ x) := fun g => by
    rw [ContinuousLinearMap.ext_iff]; rfl
  rw [linSumModel_apply, linSumModel_apply]
  have e : ∀ {m : ℕ} (uh : Fin m → E 0 → F 0) (ω : Fin m → ℚ≥0),
      (∑ i, if uh i (E.toBase 1 z) = fh (E.toBase 1 z) ∧
        linAt U R (fun y => fh y - uh i y) z = ℓ then ω i else 0) =
      mass (fun i => (uh i (r R (E.toBase 1 z)),
        (⇑(scDeriv U ((fun y => fh y - uh i y) ∘ r R) z) : E 0 → F 0))) ω Nℓ := by
    intro m uh ω
    refine Finset.sum_congr rfl fun i _ => ite_iff_congr ?_ _ _
    change _ ↔ uh i (r R (E.toBase 1 z)) = fh (E.toBase 1 z) ∧
      ∀ x : ↥(rangeS (scDeriv U (r R) z)), scDeriv U ((fun y => fh y - uh i y) ∘ r R) z x = ℓ x
    rw [hrz, hlin]
  rw [e sh σ, e th τ]
  exact hmass

open Classical in
/-- `∑_{i : ŝᵢ(y) = f̂(y)} σᵢ · ψ(D((f̂ − ŝᵢ) ∘ r)(z))` for any map `ψ` of the ambient derivatives
`E₀ → F₀` (e.g. the passage to intrinsic operators `T_xX → W_x`). -/
def linSumModelMap {Q' : Type*} (U : Set (E 0)) (R : E 0 × F 0 → E 0 × F 0) (fh : E 0 → F 0)
    {k : ℕ} (sh : Fin k → E 0 → F 0) (σ : Fin k → ℚ≥0) (z : E 1)
    (ψ : (E 0 →L[ℝ] F 0) → Q') : Q' →₀ ℚ≥0 :=
  ∑ i, if sh i (E.toBase 1 z) = fh (E.toBase 1 z) then
    Finsupp.single (ψ (scDeriv U ((fun y => fh y - sh i y) ∘ r R) z)) (σ i) else 0

open Classical in
theorem linSumModelMap_apply {Q' : Type*} (fh : E 0 → F 0) {k : ℕ} (sh : Fin k → E 0 → F 0)
    (σ : Fin k → ℚ≥0) (z : E 1) (ψ : (E 0 →L[ℝ] F 0) → Q') (q' : Q') :
    linSumModelMap U R fh sh σ z ψ q' = ∑ i, if sh i (E.toBase 1 z) = fh (E.toBase 1 z) ∧
      ψ (scDeriv U ((fun y => fh y - sh i y) ∘ r R) z) = q' then σ i else 0 := by
  unfold linSumModelMap
  rw [Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h1 : sh i (E.toBase 1 z) = fh (E.toBase 1 z)
  · by_cases h2 : ψ (scDeriv U ((fun y => fh y - sh i y) ∘ r R) z) = q'
    · rw [if_pos h1, if_pos ⟨h1, h2⟩, Finsupp.single_apply, if_pos h2]
    · rw [if_pos h1, if_neg fun h => h2 h.2, Finsupp.single_apply, if_neg h2]
  · rw [if_neg h1, if_neg fun h => h1 h.1, Finsupp.coe_zero, Pi.zero_apply]

open Classical in
/-- **Theorem 15.1.1 on the model, for any map `ψ` of the operators**: the formal sums
`∑_{i : ŝᵢ(y) = f̂(y)} σᵢ · ψ((f̂ − ŝᵢ)'(z))` of two local structures agree. -/
theorem theorem_15_1_1_model_map {Q' : Type*} (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R)
    {fh : E 0 → F 0} (hf : IsScSmooth U (fh ∘ r R)) {k l : ℕ} {sh : Fin k → E 0 → F 0}
    {σ : Fin k → ℚ≥0} {th : Fin l → E 0 → F 0} {τ : Fin l → ℚ≥0}
    (hs : ∀ i, IsScSmooth U (sh i ∘ r R)) (ht : ∀ j, IsScSmooth U (th j ∘ r R))
    {N : Set (E 0)} (hN : IsOpen N)
    (hΛ : ∀ y ∈ r R '' U, y ∈ N → ∀ v : F 0,
      (∑ i, if sh i y = v then σ i else 0) = ∑ j, if th j y = v then τ j else 0)
    {z : E 1} (hz : E.toBase 1 z ∈ r R '' U) (hzN : E.toBase 1 z ∈ N)
    (ψ : (E 0 →L[ℝ] F 0) → Q') :
    linSumModelMap U R fh sh σ z ψ = linSumModelMap U R fh th τ z ψ := by
  have hcore := wsum_model_eq hU hR hf hs ht hN hΛ hz hzN
  have hrz : r R (E.toBase 1 z) = E.toBase 1 z := r_eq_self hR hz
  refine Finsupp.ext fun q' => ?_
  set Nq : Set (F 0 × (E 0 → F 0)) :=
    {q | q.1 = fh (E.toBase 1 z) ∧ ∀ L : E 0 →L[ℝ] F 0, ⇑L = q.2 → ψ L = q'} with hNq
  have hmass := mass_eq_of_wsum_eq hcore Nq
  rw [linSumModelMap_apply, linSumModelMap_apply]
  have e : ∀ {m : ℕ} (uh : Fin m → E 0 → F 0) (ω : Fin m → ℚ≥0),
      (∑ i, if uh i (E.toBase 1 z) = fh (E.toBase 1 z) ∧
        ψ (scDeriv U ((fun y => fh y - uh i y) ∘ r R) z) = q' then ω i else 0) =
      mass (fun i => (uh i (r R (E.toBase 1 z)),
        (⇑(scDeriv U ((fun y => fh y - uh i y) ∘ r R) z) : E 0 → F 0))) ω Nq := by
    intro m uh ω
    refine Finset.sum_congr rfl fun i _ => ite_iff_congr ?_ _ _
    change _ ↔ uh i (r R (E.toBase 1 z)) = fh (E.toBase 1 z) ∧
      ∀ L : E 0 →L[ℝ] F 0, ⇑L = ⇑(scDeriv U ((fun y => fh y - uh i y) ∘ r R) z) → ψ L = q'
    rw [hrz]
    refine and_congr_right fun _ => ⟨fun h L hL => ?_, fun h => h _ rfl⟩
    rw [DFunLike.coe_injective hL]; exact h
  rw [e sh σ, e th τ]
  exact hmass

open Classical in
/-- **Remark 15.1.2 (2017: Remark 15.1), p. 684, on the model**: with positive weights, where the
weighted count of `f̂(y)` is `0` (`Λ(f(y)) = 0`, i.e. `y ∉ supp(Λ ∘ f)`) no `i` has
`ŝᵢ(y) = f̂(y)`, the formal sum is empty and `linSumModel = 0`; so (1) of Theorem 15.1.1 follows
from (2). -/
theorem remark_15_1_2_model (fh : E 0 → F 0) {k : ℕ} (sh : Fin k → E 0 → F 0)
    {σ : Fin k → ℚ≥0} (hσ : ∀ i, 0 < σ i) (z : E 1)
    (h0 : (∑ i, if sh i (E.toBase 1 z) = fh (E.toBase 1 z) then σ i else 0) = 0) :
    linSumModel U R fh sh σ z = 0 := by
  have hnone : ∀ i, sh i (E.toBase 1 z) ≠ fh (E.toBase 1 z) := fun i hi => by
    have := (Finset.sum_eq_zero_iff.1 h0) i (Finset.mem_univ i)
    rw [if_pos hi] at this
    exact (hσ i).ne' this
  unfold linSumModel
  exact Finset.sum_eq_zero fun i _ => if_neg (hnone i)

open Classical in
/-- **The operators occurring in the formal sum** (for Definition 15.2.1): with positive weights,
`ℓ` has a nonzero coefficient in `linSumModel` iff `ℓ = (f̂ − ŝᵢ)'(z)` for some `i` with
`ŝᵢ(y) = f̂(y)`. -/
theorem mem_support_linSumModel_iff (fh : E 0 → F 0) {k : ℕ} (sh : Fin k → E 0 → F 0)
    {σ : Fin k → ℚ≥0} (hσ : ∀ i, 0 < σ i) (z : E 1)
    (ℓ : ↥(rangeS (scDeriv U (r R) z)) →L[ℝ] F 0) :
    ℓ ∈ (linSumModel U R fh sh σ z).support ↔ ∃ i, sh i (E.toBase 1 z) = fh (E.toBase 1 z) ∧
      linAt U R (fun y => fh y - sh i y) z = ℓ := by
  rw [Finsupp.mem_support_iff, linSumModel_apply]
  constructor
  · intro h
    by_contra hne
    exact h (Finset.sum_eq_zero fun i _ => if_neg fun hi => hne ⟨i, hi⟩)
  · rintro ⟨i, hi⟩ h0
    have := (Finset.sum_eq_zero_iff.1 h0) i (Finset.mem_univ i)
    rw [if_pos hi] at this
    exact (hσ i).ne' this

end Linearization15

end Polyfold
