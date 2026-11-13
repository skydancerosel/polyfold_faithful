import Polyfold.Chapter5.BumpFunctions

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, Appendix 5.4.2
(notes on partitions of unity and bump functions, the part not in `BumpFunctions.lean`):
**Definitions 5.5.1, 5.5.4, 5.5.9, 5.5.12, 5.5.14 (preprint 5.28, 5.31, 5.36, 5.39, 5.41), Theorem 5.5.10 (preprint 5.37), Propositions 5.5.11, 5.5.15 (preprint 5.38, 5.42), Corollary
5.44**; Theorems 5.5.13 and 5.5.16 (preprint 5.40 and 5.43) as statements (5.43 an explicit
hypothesis of Corollary 5.5.17 (preprint 5.44) here); since 2026-11-12 Theorems 5.5.5, 5.5.13 and
5.5.16 are proved in `BonicFrampton.lean` (`BonicFrampton.theorem_5_5_5`),
`Torunczyk.lean` (`theorem_5_5_13`) and `WCGPartitionsOfUnity.lean` (`theorem_5_5_16`), and Corollary
5.5.17 holds with no hypothesis (`corollary_5_5_17_unconditional`, `SeparablePartitionsOfUnity.lean`)
*(book 2017: see `BookConcordance.md`)*.

# Sc-smooth partitions of unity

## The text, paraphrased

(Definition 5.5.1 (preprint 5.28)) `X` admits sc-smooth partitions of unity if every open cover has a subordinate
sc-smooth partition of unity.  A classically smooth partition of unity of a Banach space with an
sc-structure is sc-smooth (Corollary 1.2.5 (preprint 1.20)); many Banach spaces have none.  (Definition 5.5.4 (preprint 5.31)) A
Banach space admits a `C^k`-bump function if some `C^k` `f : E → ℝ`, not identically zero, has
bounded support; (Theorem 5.5.5 (preprint 5.32), Bonic–Frampton) the `p`-th power of the `Lᵖ`-norm is `C^∞` (`p`
even), `C^{p−1}` (`p` odd), `C^{[p]}` (`p` not an integer); remark on `W^{1,4}` and `W^{1,3/2}`.
(Definition 5.5.9 (preprint 5.36)) A local model `(O, C, E)` has the sc-smooth approximation property if for every
open `V ⊆ O` with `cl_C(V) ⊆ O`, continuous `f : O → [0, 1]` supported in `V` and `ε > 0` there is
an sc-smooth `g : O → [0, 1]` supported in `V` with `|f − g| ≤ ε` on `O`.  (Theorem 5.5.10 (preprint 5.37)) `X`
admits sc-smooth partitions of unity iff it has an atlas of local models with the approximation
property.  Proof of (i) ⇒ (ii): for a chart `φ : U → O`, "the sc-smooth function `f ∘ φ`" extended
by `0` is a continuous `g` supported in `W = φ⁻¹(V)` "satisfying `cl_X(W) ⊆ U`"; with
`W̃ = {g > ε/4}`, the cover `U₀ = {g < ε/2}`, `U_x` (`x ∈ cl W̃`, `cl U_x ⊆ W`,
`|g − g(x)| < ε/2` on `U_x`) and a subordinate sc-smooth partition of unity `(β₀, β_x)`,
`ĝ = Σ β_x g(x)` approximates `g` within `ε` and is supported in `W`.  Proof of (ii) ⇒ (i): a
locally finite refinement `(W_λ)` "with the same index set" and `cl_X(W_λ) ⊆ U_{τ(λ)}`, a shrinking
`(Q_λ)`, continuous `f_λ = 1` on `Q_λ` supported in `W_λ`, sc-smooth `g_λ` with
`|f_λ ∘ φ⁻¹ − g_λ| < 1/2` "in view of (ii)", `ĝ_λ = g_λ ∘ φ` extended by `0`, and
`γ_λ = ĝ_λ / Σ ĝ`.  (Proposition 5.5.11 (preprint 5.38), "an immediate consequence of Theorem 5.37") If the
sc-Banach space admits smooth partitions of unity, every local model `(O, C, E)` has the
approximation property.  (Definition 5.5.12 (preprint 5.39)) `c₀(Γ)` with the max norm; coordinate-wise `C^k`
homeomorphic embeddings into `c₀(Γ)`; (Theorem 5.5.13 (preprint 5.40), Toruńczyk) `E` admits `C^k` partitions of
unity iff it has one.  (Definition 5.5.14 (preprint 5.41)) `E` is WCG if `E = cl(span K)` for a weakly compact `K`.
(Proposition 5.5.15 (preprint 5.42)) Reflexive or separable spaces are WCG (the unit ball is weakly compact; `{0} ∪
{xₙ/n}` for a dense sequence of the ball).  (Theorem 5.43, [12]) A WCG space with a `C^k`-bump
function admits `C^k` partitions of unity.  (Corollary 5.5.17 (preprint 5.44)) If `E₀` is a Hilbert space, `(O, C, E)`
has the approximation property: a Hilbert space is reflexive, hence WCG, it has smooth bump
functions, so Theorem 5.5.16 (preprint 5.43) and Theorem 5.5.10 (preprint 5.37) apply.

## What is formalized

* **Sc-smooth functions on M-polyfolds** (beyond `BumpFunctions.lean`): sums, differences and
  products (`MPolyfold.IsScSmoothMap.real_add`, `real_sub`, `real_mul`, and on retracts
  `IsScSmoothRetractMap.real_add`, `real_sub`, `real_mul`), finite sums and products
  (`isScSmoothMap_real_finsetSum`, `isScSmoothMap_real_finsetProd`), **locally finite sums**
  (`isScSmoothMap_real_finsum`), locality (`isScSmoothMap_real_of_eventuallyEq`), **extension by
  zero from a chart** (`isScSmoothMap_real_of_chart`), and `MPolyfold.IsScSmoothMap.real_chart_on`.
* **Definition 5.5.1 (preprint 5.28)**: `MPolyfold.IsScSmoothPartitionOfUnity`, `MPolyfold.AdmitsScPartitionsOfUnity`
  (Mathlib's `PartitionOfUnity`, subordinate: `supp ρᵢ ⊆ Uᵢ`).
* **Definition 5.5.9 (preprint 5.36)**: `LocalModel.HasApproxProperty`.
* **Theorem 5.5.10 (preprint 5.37)**: `Polyfold.theorem_5_5_10`, from `hasApproxProperty_restrict` ("(i) ⇒ (ii)" for
  the charts restricted to open `s` with `cl_X(s) ⊆ dom φ`), `exists_isScSmoothMap_urysohn`
  (sc-smooth Urysohn functions from (ii)) and `admitsScPartitionsOfUnity_of_approx` ("(ii) ⇒ (i)");
  the chart lemmas `MChart.isClosed_inter_preimage`, `MChart.exists_small_nhds`,
  `LocalModel.HasApproxProperty.exists_approx` (the approximation property transported to `X`), and
  three facts on convex combinations `Σ ρᵢ cᵢ` (`PartitionOfUnity.abs_sub_finsum_mul_le`,
  `finsum_mul_mem_Icc`, `tsupport_finsum_mul_subset`).
* `AdmitsContDiffPartitionsOfUnity` (`C^k` partitions of unity of a Banach space) and **Proposition
  5.38**: `Polyfold.proposition_5_5_11` (`E₀` admits `C^∞` partitions of unity).
* **Definition 5.5.4 (preprint 5.31)**: `HasContDiffBump`.  **Definition 5.5.12 (preprint 5.39)**: `cZero` (a submodule of `ℓ^∞(Γ)`),
  `mem_cZero_iff` (the text's condition), `norm_cZero`, `IsCoordinatewiseContDiffEmbedding`;
  **Theorem 5.5.13 (preprint 5.40)** as the statement `TorunczykStatement` (not proved, not used).
* **Definition 5.5.14 (preprint 5.41)**: `IsWCG`; `IsReflexive` (`V → V''` onto).  **Proposition 5.5.15 (preprint 5.42)**:
  `proposition_5_5_15_reflexive` (i) and `proposition_5_5_15_separable` (ii).
* **Theorem 5.5.16 (preprint 5.43)** as the statement `GodefroyTroyanskiWhitfieldZizlerStatement V k`.
* **Corollary 5.5.17 (preprint 5.44)**: `Polyfold.corollary_5_5_17` (`E₀` Hilbert, i.e. `‖v‖² = b(v, v)`, and Theorem
  5.43 for `E₀`, `k = ∞`, as an explicit hypothesis), with `isReflexive_of_hilbert` and
  `hasContDiffBump_of_hilbert`; `MPolyfold.admitsScPartitionsOfUnity_of_hilbert` (an M-polyfold on
  sc-Hilbert spaces admits sc-smooth partitions of unity, under the same hypothesis in the charts).
* `MPolyfold.AdmitsScPartitionsOfUnity.admitsBumpFunctions` (partitions of unity give bump
  functions in the sense of Definition 5.3.1 (preprint 5.9); the converse is the open problem the text states).

## What the text leaves implicit, and the choices made

* **Definition 5.5.1 (preprint 5.28).**  A partition of unity is Mathlib's `PartitionOfUnity ι X` (continuous
  `ρᵢ ≥ 0`, locally finite supports, `Σ ρᵢ = 1`), subordinate to `(Uᵢ)` if `cl{ρᵢ ≠ 0} ⊆ Uᵢ`; the
  index type lives in the universe of `X` (every cover can be indexed by a set of subsets of `X`).
* **Definition 5.5.9 (preprint 5.36).**  `V = O ∩ W`, `W` open in `E₀`; `cl_C(V)` is the closure in `E₀` (`C` is
  closed); the supports of `f` and `g` are taken in `O`.
* **Theorem 5.5.10 (preprint 5.37), "(i) ⇒ (ii)": `cl_X(W) ⊆ U` does not follow from `cl_C(V) ⊆ O`, and `f ∘ φ` is
  only continuous.**  For `X = E` with `E₀` a Hilbert space, the chart `φ(u) = u/(1 − |u|₀²)` from
  the open unit ball `U` onto `O = E` (an sc-diffeomorphism), `V = O` and `f ≡ 1`: `cl_C(V) ⊆ O`,
  but `W = U` and `cl_X(W) ⊄ U`; the extension `g` is the indicator of the open ball, not
  continuous, and `U₀ = {g < ε/2}` is not open.  Since (ii) asks only for *an* atlas, the proof here
  uses the charts restricted to open `s` with `cl_X(s) ⊆ dom φ`: then `cl_C(V) ⊆ φ(s)` gives
  `φ⁻¹(cl V)` closed in `X` (`MChart.isClosed_inter_preimage`), so `g` is continuous.  The set
  `W̃` is not needed: the sets `U_x`, `x ∈ φ⁻¹(V)`, need only lie in `φ⁻¹(V)` (subordinate means
  `supp β_x ⊆ U_x`), and the estimate gives `ε/2`.  Whether *every* chart has the approximation
  property under (i) is not settled here (it needs approximations on the open set `dom φ`).
* **Theorem 5.5.10 (preprint 5.37), "(ii) ⇒ (i)".**  (a) A refinement `(W_λ)` with the same index set and each
  `cl_X(W_λ)` inside one chart domain does not exist in general (the cover `{X}`).  (b)
  `cl_C(φ(W_λ)) ⊆ O`, needed to apply (ii), is not arranged: the proof uses small neighbourhoods
  (`MChart.exists_small_nhds`: `cl_X(N) ⊆ dom φ` and `φ(N)` inside half a ball contained in the
  domain of a retraction, whose closure stays in `O` by `closure_inter_ball_subset`).  (c) The
  extension of `g_λ ∘ φ` by `0` is continuous (and sc-smooth) because `cl_X(W_λ) ⊆ dom φ`.  The
  proof here goes through sc-smooth Urysohn functions (`exists_isScSmoothMap_urysohn`: for disjoint
  closed `s, t`, `F = τ(4 Σ ĝ_x − 1)` with the text's `ĝ_x ≥ 1/2` where `f_x = 1`), after which
  Mathlib's `BumpCovering.exists_isSubordinate_of_prop` handles the index set and
  `BumpCovering.toPartitionOfUnity` (`ρᵢ = fᵢ ∏_{j < i}(1 − f_j)`, locally a finite product)
  replaces the quotient `ĝ_λ / Σ ĝ`.  Metrizability is not used, only paracompactness and the
  Hausdorff property.
* **Proposition 5.5.11 (preprint 5.38) is not an immediate consequence of Theorem 5.5.10 (preprint 5.37)**: Theorem 5.5.10 (preprint 5.37) gives some
  atlas, not the given local model, and applying it to the M-polyfold `O` would need sc-smooth
  partitions of unity on the domain of a retraction, an open subset of `C`.  The proof here repeats
  the argument of "(i) ⇒ (ii)" in `E₀`: `A = {x ∈ O | f(x) ≥ ε/2}` is closed in `E₀` because
  `cl(V) ⊆ O`, and the cover of `E₀` by `E₀ ∖ A` and small balls needs only partitions of unity of
  `E₀` itself.  "The sc-Banach space admits smooth partitions of unity" is read as: `E₀` admits
  `C^∞` partitions of unity; `C^∞` functions on `E₀` are sc-smooth by Corollary 1.2.5 (preprint 1.20).
* **Definitions 5.5.12, 5.5.14 (preprint 5.39, 5.41).**  `c₀(Γ)` is the subspace of `ℓ^∞(Γ)` of functions tending to `0`
  along the cofinite filter, equivalent to the text's finiteness condition (`mem_cZero_iff`); its
  norm is the supremum (a maximum for `f ≠ 0`).  "Homeomorphic embedding" is
  `Topology.IsEmbedding`.  "Weakly compact" is compactness in `WeakSpace ℝ V`; "reflexive", not
  defined in the text, is surjectivity of `V → V''`.
* **Proposition 5.5.15 (preprint 5.42).**  (i) Kakutani's theorem is available in Mathlib as
  `NormedSpace.isCompact_closure_of_isBounded` (Banach–Alaoglu in `V''` and the embedding of
  `(V, weak)` into `(V'', weak-*)`); the span of the ball is all of `V`.  (ii) A dense sequence of
  `V`, scaled by `1/((n + 1)(|yₙ| + 1))`, replaces the text's dense sequence of the ball.
* **Corollary 5.5.17 (preprint 5.44).**  "Hilbert space" is `‖v‖² = b(v, v)` as in Proposition 5.5.8 (preprint 5.35); "a Hilbert space
  is reflexive" is proved (`InnerProductSpace.ofNorm` and the Riesz representation); the `C^k`-bump
  Theorem 5.5.16 (preprint 5.43) needs is the classical `τ(1 − |v|²)`.  The proof's "admits sc-smooth partition of
  unity" means `C^∞` partitions of unity of `E₀`, and "in view of Theorem 5.37" means Proposition
  5.38.  Theorem 5.5.16 (preprint 5.43) is an explicit hypothesis.
* **Not in this file**: Theorem 5.5.5 (preprint 5.32) (Bonic–Frampton) and the remarks on `Lᵖ` and Sobolev spaces
  (`W^{k,p}` norms, `W^{1,4}` against `W^{1,3/2}`); Theorems 5.5.13 and 5.5.16 (preprint 5.40 and 5.43) (stated only here);
  nothing on the main line uses partitions of unity (the transversality theorems use bump functions, whose Hilbert
  case, Proposition 5.5.8 (preprint 5.35), is elementary).  Since 2026-11-12 they are proved in the files
  `BonicFrampton.lean`, `SobolevRemarkAbstract–3.lean`, `SobolevCubeVolterra–5.lean`, `Torunczyk.lean`
  and `WCGPartitionsOfUnity.lean`.
-/

open Set Filter Topology Function
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u

/-! ### Sc-smooth functions: sums, products, local finiteness, extension by zero -/

section RetractFunctions

variable {E : ScBanach} {C O : Set (E 0)}

/-- The sum of two sc-smooth functions on a retract is sc-smooth. -/
theorem IsScSmoothRetractMap.real_add {f g : E 0 → ℝ}
    (hf : IsScSmoothRetractMap E C O realSc univ univ f)
    (hg : IsScSmoothRetractMap E C O realSc univ univ g) :
    IsScSmoothRetractMap E C O realSc univ univ fun x => f x + g x :=
  ⟨mapsTo_univ _ _, fun R hR =>
    (hf.comp_isScSmooth R hR).add R.isScDomain (hg.comp_isScSmooth R hR)⟩

/-- The product of two sc-smooth functions on a retract is sc-smooth (the product rule). -/
theorem IsScSmoothRetractMap.real_mul {f g : E 0 → ℝ}
    (hf : IsScSmoothRetractMap E C O realSc univ univ f)
    (hg : IsScSmoothRetractMap E C O realSc univ univ g) :
    IsScSmoothRetractMap E C O realSc univ univ fun x => f x * g x :=
  ⟨mapsTo_univ _ _, fun R hR =>
    (hf.comp_isScSmooth R hR).smul R.isScDomain (hg.comp_isScSmooth R hR)⟩

/-- The difference of two sc-smooth functions on a retract is sc-smooth. -/
theorem IsScSmoothRetractMap.real_sub {f g : E 0 → ℝ}
    (hf : IsScSmoothRetractMap E C O realSc univ univ f)
    (hg : IsScSmoothRetractMap E C O realSc univ univ g) :
    IsScSmoothRetractMap E C O realSc univ univ fun x => f x - g x :=
  ⟨mapsTo_univ _ _, fun R hR =>
    (hf.comp_isScSmooth R hR).sub R.isScDomain (hg.comp_isScSmooth R hR)⟩

end RetractFunctions

section ScFunctions

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

/-- An sc-smooth function read in a chart on an open subset `V` of its domain. -/
theorem MPolyfold.IsScSmoothMap.real_chart_on {f : X → ℝ} (hf : PX.IsScSmoothMap realPolyfold f)
    {φ : MChart X} (hφ : PX.IsChart φ) {V : Set X} (hV : IsOpen V) (hVφ : V ⊆ φ.source) :
    IsScSmoothRetractMap φ.model.E φ.model.C (φ '' V) realSc univ univ (f ∘ φ.symm) :=
  hf.smooth φ realChart hφ isChart_realChart V hV (fun _ hx => ⟨mem_univ _, hVφ hx⟩)
    (mapsTo_univ _ _)

/-- **Sc-smoothness of functions is local**: a function which near every point coincides with an
sc-smooth function is sc-smooth. -/
theorem isScSmoothMap_real_of_eventuallyEq {f : X → ℝ}
    (h : ∀ x, ∃ g : X → ℝ, PX.IsScSmoothMap realPolyfold g ∧ f =ᶠ[𝓝 x] g) :
    PX.IsScSmoothMap realPolyfold f := by
  refine isScSmoothMap_real_of_local fun x => ?_
  obtain ⟨g, hg, hfg⟩ := h x
  obtain ⟨N, hN, hNo, hxN⟩ := eventually_nhds_iff.1 hfg
  obtain ⟨φ, hφ, hxφ⟩ := PX.exists_isChart_mem_source x
  refine ⟨φ, N ∩ φ.source, hφ, hNo.inter φ.isOpen_source, ⟨hxN, hxφ⟩, inter_subset_right, ?_⟩
  refine (hg.real_chart_on hφ (hNo.inter φ.isOpen_source) inter_subset_right).congr ?_
  rintro _ ⟨y, hy, rfl⟩
  simp only [Function.comp_apply, φ.symm_apply_apply hy.2]
  exact (hN y hy.1).symm

/-- The sum of two sc-smooth functions is sc-smooth. -/
theorem MPolyfold.IsScSmoothMap.real_add {f g : X → ℝ} (hf : PX.IsScSmoothMap realPolyfold f)
    (hg : PX.IsScSmoothMap realPolyfold g) :
    PX.IsScSmoothMap realPolyfold fun x => f x + g x := by
  refine isScSmoothMap_real_of_local fun x => ?_
  obtain ⟨φ, hφ, hx⟩ := PX.exists_isChart_mem_source x
  refine ⟨φ, φ.source, hφ, φ.isOpen_source, hx, subset_rfl, ?_⟩
  exact (hf.real_chart_on hφ φ.isOpen_source subset_rfl).real_add
    (hg.real_chart_on hφ φ.isOpen_source subset_rfl)

/-- The product of two sc-smooth functions is sc-smooth. -/
theorem MPolyfold.IsScSmoothMap.real_mul {f g : X → ℝ} (hf : PX.IsScSmoothMap realPolyfold f)
    (hg : PX.IsScSmoothMap realPolyfold g) :
    PX.IsScSmoothMap realPolyfold fun x => f x * g x := by
  refine isScSmoothMap_real_of_local fun x => ?_
  obtain ⟨φ, hφ, hx⟩ := PX.exists_isChart_mem_source x
  refine ⟨φ, φ.source, hφ, φ.isOpen_source, hx, subset_rfl, ?_⟩
  exact (hf.real_chart_on hφ φ.isOpen_source subset_rfl).real_mul
    (hg.real_chart_on hφ φ.isOpen_source subset_rfl)

/-- The difference of two sc-smooth functions is sc-smooth. -/
theorem MPolyfold.IsScSmoothMap.real_sub {f g : X → ℝ} (hf : PX.IsScSmoothMap realPolyfold f)
    (hg : PX.IsScSmoothMap realPolyfold g) :
    PX.IsScSmoothMap realPolyfold fun x => f x - g x := by
  refine isScSmoothMap_real_of_local fun x => ?_
  obtain ⟨φ, hφ, hx⟩ := PX.exists_isChart_mem_source x
  refine ⟨φ, φ.source, hφ, φ.isOpen_source, hx, subset_rfl, ?_⟩
  exact (hf.real_chart_on hφ φ.isOpen_source subset_rfl).real_sub
    (hg.real_chart_on hφ φ.isOpen_source subset_rfl)

/-- A finite sum of sc-smooth functions is sc-smooth. -/
theorem isScSmoothMap_real_finsetSum {ι : Type*} (s : Finset ι) {f : ι → X → ℝ}
    (hf : ∀ i ∈ s, PX.IsScSmoothMap realPolyfold (f i)) :
    PX.IsScSmoothMap realPolyfold fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact isScSmoothMap_real_const 0
  | insert a s ha ih =>
    have h := (hf a (Finset.mem_insert_self a s)).real_add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have heq : (fun x => f a x + ∑ i ∈ s, f i x) = fun x => ∑ i ∈ insert a s, f i x :=
      funext fun x => by rw [Finset.sum_insert ha]
    rwa [heq] at h

/-- A finite product of sc-smooth functions is sc-smooth. -/
theorem isScSmoothMap_real_finsetProd {ι : Type*} (s : Finset ι) {f : ι → X → ℝ}
    (hf : ∀ i ∈ s, PX.IsScSmoothMap realPolyfold (f i)) :
    PX.IsScSmoothMap realPolyfold fun x => ∏ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact isScSmoothMap_real_const 1
  | insert a s ha ih =>
    have h := (hf a (Finset.mem_insert_self a s)).real_mul
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have heq : (fun x => f a x * ∏ i ∈ s, f i x) = fun x => ∏ i ∈ insert a s, f i x :=
      funext fun x => by rw [Finset.prod_insert ha]
    rwa [heq] at h

/-- **A locally finite sum of sc-smooth functions is sc-smooth.** -/
theorem isScSmoothMap_real_finsum {ι : Type*} {f : ι → X → ℝ}
    (hf : ∀ i, PX.IsScSmoothMap realPolyfold (f i)) (hlf : LocallyFinite fun i => support (f i)) :
    PX.IsScSmoothMap realPolyfold fun x => ∑ᶠ i, f i x := by
  refine isScSmoothMap_real_of_eventuallyEq fun x => ?_
  obtain ⟨s, hs⟩ := finsum_eventually_eq_sum hlf x
  exact ⟨fun y => ∑ i ∈ s, f i y, isScSmoothMap_real_finsetSum s fun i _ => hf i, hs⟩

/-- **Extension by zero from a chart**: a function supported in the domain of a chart `φ` of `X`
whose representative `f ∘ φ⁻¹` is sc-smooth on the retract `O` is sc-smooth on `X`. -/
theorem isScSmoothMap_real_of_chart {f : X → ℝ} {φ : MChart X} (hφ : PX.IsChart φ)
    (hsupp : tsupport f ⊆ φ.source)
    (hf : IsScSmoothRetractMap φ.model.E φ.model.C φ.model.O realSc univ univ (f ∘ φ.symm)) :
    PX.IsScSmoothMap realPolyfold f := by
  refine isScSmoothMap_real_of_local fun x => ?_
  by_cases hx : x ∈ φ.source
  · refine ⟨φ, φ.source, hφ, φ.isOpen_source, hx, subset_rfl, ?_⟩
    rw [φ.image_source]
    exact hf
  · obtain ⟨ψ, hψ, hxψ⟩ := PX.exists_isChart_mem_source x
    have hxt : x ∉ tsupport f := fun h => hx (hsupp h)
    have hVo : IsOpen (ψ.source ∩ (tsupport f)ᶜ) :=
      ψ.isOpen_source.inter (isClosed_tsupport f).isOpen_compl
    refine ⟨ψ, ψ.source ∩ (tsupport f)ᶜ, hψ, hVo, ⟨hxψ, hxt⟩, inter_subset_left, ?_⟩
    refine ((isScSmoothMap_real_const (PX := PX) 0).real_chart_on hψ hVo
      inter_subset_left).congr ?_
    rintro _ ⟨y, hy, rfl⟩
    simp only [Function.comp_apply, ψ.symm_apply_apply hy.1]
    exact (image_eq_zero_of_notMem_tsupport hy.2).symm

end ScFunctions

/-! ### Two facts on partitions of unity (pure topology) -/

section POU

variable {Y : Type*} [TopologicalSpace Y] {ι : Type*} (ρ : PartitionOfUnity ι Y)

lemma PartitionOfUnity.finsum_mul_eq_sum (c : ι → ℝ) (y : Y) :
    ∑ᶠ i, ρ i y * c i = ∑ i ∈ ρ.finsupport y, ρ i y * c i :=
  (ρ.sum_finsupport_smul_eq_finsum (x₀ := y) fun i _ => c i).symm

/-- A convex combination `Σ ρᵢ(y) cᵢ` is within `δ` of `F` if every `cᵢ` with `ρᵢ(y) ≠ 0` is. -/
lemma PartitionOfUnity.abs_sub_finsum_mul_le (c : ι → ℝ) (F : ℝ) (y : Y) {δ : ℝ}
    (h : ∀ i, ρ i y ≠ 0 → |F - c i| ≤ δ) : |F - ∑ᶠ i, ρ i y * c i| ≤ δ := by
  rw [PartitionOfUnity.finsum_mul_eq_sum ρ]
  set I := ρ.finsupport y
  have h1 : ∑ i ∈ I, ρ i y = 1 := ρ.sum_finsupport (mem_univ y)
  have h2 : F - ∑ i ∈ I, ρ i y * c i = ∑ i ∈ I, ρ i y * (F - c i) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h1, one_mul]
  rw [h2]
  calc |∑ i ∈ I, ρ i y * (F - c i)| ≤ ∑ i ∈ I, |ρ i y * (F - c i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ I, ρ i y * δ := Finset.sum_le_sum fun i hi => by
        rw [abs_mul, abs_of_nonneg (ρ.nonneg i y)]
        exact mul_le_mul_of_nonneg_left (h i ((ρ.mem_finsupport y).1 hi)) (ρ.nonneg i y)
    _ = δ := by rw [← Finset.sum_mul, h1, one_mul]

/-- A convex combination of numbers in `[0, 1]` lies in `[0, 1]`. -/
lemma PartitionOfUnity.finsum_mul_mem_Icc (c : ι → ℝ) (hc : ∀ i, c i ∈ Icc (0 : ℝ) 1) (y : Y) :
    ∑ᶠ i, ρ i y * c i ∈ Icc (0 : ℝ) 1 := by
  rw [PartitionOfUnity.finsum_mul_eq_sum ρ]
  refine ⟨Finset.sum_nonneg fun i _ => mul_nonneg (ρ.nonneg i y) (hc i).1, ?_⟩
  calc ∑ i ∈ ρ.finsupport y, ρ i y * c i ≤ ∑ i ∈ ρ.finsupport y, ρ i y :=
        Finset.sum_le_sum fun i _ => mul_le_of_le_one_right (ρ.nonneg i y) (hc i).2
    _ = 1 := ρ.sum_finsupport (mem_univ y)

lemma PartitionOfUnity.locallyFinite_mul (c : ι → ℝ) :
    LocallyFinite fun i => support fun y => ρ i y * c i :=
  ρ.locallyFinite.subset fun _ => support_mul_subset_left _ _

/-- The support of `Σ ρᵢ cᵢ` lies in the union of the supports of the `ρᵢ` with `cᵢ ≠ 0`. -/
lemma PartitionOfUnity.tsupport_finsum_mul_subset (c : ι → ℝ) {T : Set Y}
    (hT : ∀ i, c i ≠ 0 → tsupport (ρ i) ⊆ T) :
    tsupport (fun y => ∑ᶠ i, ρ i y * c i) ⊆ T := by
  have hsub : support (fun y => ∑ᶠ i, ρ i y * c i) ⊆ ⋃ i, support fun y => ρ i y * c i := by
    intro y hy
    by_contra h
    simp only [mem_iUnion, not_exists, mem_support, not_not] at h
    exact hy (finsum_eq_zero_of_forall_eq_zero h)
  refine (closure_mono hsub).trans ?_
  rw [(PartitionOfUnity.locallyFinite_mul ρ c).closure_iUnion]
  refine iUnion_subset fun i => ?_
  by_cases hci : c i = 0
  · simp [hci]
  · exact (closure_mono (support_mul_subset_left _ _)).trans (hT i hci)

end POU

/-! ### Definitions 5.5.1 and 5.5.9 (preprint 5.28 and 5.36) -/

section Defs

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)

/-- A partition of unity on `X` consisting of sc-smooth functions. -/
def MPolyfold.IsScSmoothPartitionOfUnity {ι : Type*} (ρ : PartitionOfUnity ι X) : Prop :=
  ∀ i, PX.IsScSmoothMap realPolyfold (ρ i)

/-- **Definition 5.5.1 (preprint 5.28)**: the M-polyfold `X` **admits sc-smooth partitions of unity** if for every
open covering `(U_i)_{i ∈ ι}` of `X` there is a subordinate sc-smooth partition of unity
(Mathlib's `PartitionOfUnity`: continuous `ρᵢ ≥ 0` with locally finite supports and `Σᵢ ρᵢ = 1`;
subordinate: `supp(ρᵢ) ⊆ Uᵢ`). -/
def MPolyfold.AdmitsScPartitionsOfUnity : Prop :=
  ∀ (ι : Type u) (U : ι → Set X), (∀ i, IsOpen (U i)) → ⋃ i, U i = univ →
    ∃ ρ : PartitionOfUnity ι X, ρ.IsSubordinate U ∧ PX.IsScSmoothPartitionOfUnity ρ

end Defs

/-- **Definition 5.5.9 (preprint 5.36)**: the local model `(O, C, E)` has the **sc-smooth approximation property**
if for every open subset `V = O ∩ W` of `O` with `cl_C(V) ⊆ O` (the closure in `E₀`, `C` being
closed), every continuous `f : O → [0, 1]` with support in `V` (the closure of `{f ≠ 0}` in `O`)
and every `ε > 0` there is an sc-smooth `g : O → [0, 1]` with support in `V` and
`|f(x) − g(x)| ≤ ε` for all `x ∈ O`. -/
def LocalModel.HasApproxProperty (M : LocalModel) : Prop :=
  ∀ W : Set (M.E 0), IsOpen W → closure (M.O ∩ W) ⊆ M.O →
    ∀ f : M.E 0 → ℝ, ContinuousOn f M.O → (∀ x ∈ M.O, f x ∈ Icc (0 : ℝ) 1) →
      closure (M.O ∩ support f) ∩ M.O ⊆ W →
      ∀ ε : ℝ, 0 < ε → ∃ g : M.E 0 → ℝ, IsScSmoothRetractMap M.E M.C M.O realSc univ univ g ∧
        (∀ x ∈ M.O, g x ∈ Icc (0 : ℝ) 1) ∧ closure (M.O ∩ support g) ∩ M.O ⊆ W ∧
        ∀ x ∈ M.O, |f x - g x| ≤ ε

/-! ### Charts with small domains -/

section SmallCharts

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

omit [T2Space X] [ParacompactSpace X] in
/-- If `cl_X(s)` lies in the domain of the chart `φ`, then for a closed `A ⊆ φ(s)` the set
`φ⁻¹(A)` is closed in `X` and contained in `s`. -/
lemma MChart.isClosed_inter_preimage (φ : MChart X) {s : Set X} (hcl : closure s ⊆ φ.source)
    {A : Set (φ.model.E 0)} (hA : IsClosed A) (hAs : A ⊆ φ '' s) :
    IsClosed (φ.source ∩ φ ⁻¹' A) ∧ φ.source ∩ φ ⁻¹' A ⊆ s := by
  have hsub : φ.source ∩ φ ⁻¹' A ⊆ s := by
    rintro y ⟨hy, hyA⟩
    obtain ⟨y', hy', hyy'⟩ := hAs hyA
    have := φ.toPartialEquiv.injOn (hcl (subset_closure hy')) hy hyy'
    rwa [this] at hy'
  refine ⟨isClosed_of_closure_subset fun y hy => ?_, hsub⟩
  have hyφ : y ∈ φ.source := hcl (closure_mono hsub hy)
  have hcont : ContinuousAt φ y :=
    φ.continuousOn_toFun.continuousAt (φ.isOpen_source.mem_nhds hyφ)
  refine ⟨hyφ, ?_⟩
  have h1 := mem_closure_image hcont hy
  exact hA.closure_subset_iff.2 (image_subset_iff.2 fun z hz => hz.2) h1

/-- **Small neighbourhoods in a chart**: every point `x` of the domain of a chart `φ` and every
open `U ∋ x` contain an open `N ∋ x` with `cl_X(N) ⊆ dom φ` and `cl_E(φ(N)) ⊆ O` (a ball in `E₀`
around `φ(x)` of half the radius of a ball inside the domain of a retraction onto `O`). -/
lemma MChart.exists_small_nhds (φ : MChart X) {x : X} (hx : x ∈ φ.source) {U : Set X}
    (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ N : Set X, IsOpen N ∧ x ∈ N ∧ N ⊆ U ∩ φ.source ∧ closure N ⊆ φ.source ∧
      closure (φ '' N) ⊆ φ.model.O := by
  set z := φ x with hz
  have hzO : z ∈ φ.model.O := φ.mapsTo_model x hx
  obtain ⟨R₀, hR₀⟩ := φ.model.isScRetract
  obtain ⟨W', hW'o, hW'eq⟩ := R₀.relOpen.relOpen
  have hzW' : z ∈ W' := by
    have : z ∈ R₀.U := R₀.retract_subset (hR₀ ▸ hzO)
    rw [hW'eq] at this; exact this.1
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hW'o z hzW'
  have hclos := closure_inter_ball_subset R₀ hR₀ hW'eq hball
  obtain ⟨t, ht, htc, htsub⟩ :=
    exists_mem_nhds_isClosed_subset ((hU.inter φ.isOpen_source).mem_nhds ⟨hxU, hx⟩)
  refine ⟨interior t ∩ (φ.source ∩ φ ⁻¹' Metric.ball z (r / 2)),
    isOpen_interior.inter (φ.continuousOn_toFun.isOpen_inter_preimage φ.isOpen_source
      Metric.isOpen_ball),
    ⟨mem_interior_iff_mem_nhds.2 ht, hx, Metric.mem_ball_self (by positivity)⟩,
    fun y hy => htsub (interior_subset hy.1), ?_, ?_⟩
  · exact (closure_mono (inter_subset_left.trans interior_subset)).trans
      (htc.closure_subset.trans (htsub.trans inter_subset_right))
  · refine (closure_mono ?_).trans hclos
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨φ.mapsTo_model y hy.2.1, hy.2.2⟩

/-- **The approximation property of a chart, transported to `X`**: for a chart `φ` whose local
model has the sc-smooth approximation property, an open `N` with `cl_X(N) ⊆ dom φ` and
`cl_E(φ(N)) ⊆ O`, and a continuous `f : X → [0, 1]` with `supp(f) ⊆ N`, there is an sc-smooth
`g : X → [0, 1]` with `supp(g) ⊆ N` and `|f − g| ≤ ε` (`g = g₀ ∘ φ` on `dom φ`, `0` outside). -/
theorem LocalModel.HasApproxProperty.exists_approx {φ : MChart X} (hφ : PX.IsChart φ)
    (happ : φ.model.HasApproxProperty) {N : Set X} (hNo : IsOpen N) (hNφ : N ⊆ φ.source)
    (hcl : closure N ⊆ φ.source) (hclO : closure (φ '' N) ⊆ φ.model.O) {f : X → ℝ}
    (hf : Continuous f) (hf01 : ∀ y, f y ∈ Icc (0 : ℝ) 1) (hfsupp : tsupport f ⊆ N) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ g : X → ℝ, PX.IsScSmoothMap realPolyfold g ∧ (∀ y, g y ∈ Icc (0 : ℝ) 1) ∧
      tsupport g ⊆ N ∧ ∀ y, |f y - g y| ≤ ε := by
  obtain ⟨W, hWo, hWeq⟩ := φ.exists_isOpen_image_eq hNφ hNo
  have hWcl : closure (φ.model.O ∩ W) ⊆ φ.model.O := hWeq ▸ hclO
  have hfc : ContinuousOn (f ∘ φ.symm) φ.model.O := hf.comp_continuousOn φ.continuousOn_invFun
  have hfsupp' : closure (φ.model.O ∩ support (f ∘ φ.symm)) ∩ φ.model.O ⊆ W := by
    rintro z ⟨hz, hzO⟩
    have hcw : ContinuousWithinAt φ.symm (φ.model.O ∩ support (f ∘ φ.symm)) z :=
      (φ.continuousOn_invFun z hzO).mono inter_subset_left
    have h1 := hcw.mem_closure_image hz
    have h2 : φ.symm '' (φ.model.O ∩ support (f ∘ φ.symm)) ⊆ support f := by
      rintro _ ⟨z', hz', rfl⟩; exact hz'.2
    have h3 : φ.symm z ∈ N := hfsupp (closure_mono h2 h1)
    have h4 : φ (φ.symm z) ∈ φ '' N := mem_image_of_mem _ h3
    rw [φ.apply_symm_apply hzO, hWeq] at h4
    exact h4.2
  obtain ⟨g₀, hg₀, hg₀01, hg₀supp, hg₀f⟩ := happ W hWo hWcl (f ∘ φ.symm) hfc
    (fun z _ => hf01 _) hfsupp' ε hε
  -- the support of `g₀` read back in `X`
  set K := closure (φ.model.O ∩ support g₀) with hK
  have hKO : φ.model.O ∩ support g₀ ⊆ φ.model.O ∩ W := fun z hz =>
    ⟨hz.1, hg₀supp ⟨subset_closure hz, hz.1⟩⟩
  have hKN : K ⊆ φ '' N := by
    intro z hz
    have hzO : z ∈ φ.model.O := hWcl (closure_mono hKO hz)
    rw [hWeq]
    exact ⟨hzO, hg₀supp ⟨hz, hzO⟩⟩
  obtain ⟨hBc, hBN⟩ := φ.isClosed_inter_preimage hcl isClosed_closure hKN
  set g : X → ℝ := φ.source.indicator (g₀ ∘ φ) with hgdef
  have hgsupp : support g ⊆ φ.source ∩ φ ⁻¹' K := by
    intro y hy
    have hyφ : y ∈ φ.source := by
      by_contra h; exact hy (indicator_of_notMem h _)
    have hgy : g₀ (φ y) ≠ 0 := by
      have := mem_support.1 hy; rwa [hgdef, indicator_of_mem hyφ] at this
    exact ⟨hyφ, subset_closure ⟨φ.mapsTo_model y hyφ, hgy⟩⟩
  have htsupp : tsupport g ⊆ N := (closure_minimal hgsupp hBc).trans hBN
  refine ⟨g, ?_, fun y => ?_, htsupp, fun y => ?_⟩
  · refine isScSmoothMap_real_of_chart hφ (htsupp.trans hNφ) (hg₀.congr fun z hz => ?_)
    simp only [Function.comp_apply, hgdef, indicator_of_mem (φ.symm_mapsTo hz),
      φ.apply_symm_apply hz]
  · by_cases hy : y ∈ φ.source
    · rw [hgdef, indicator_of_mem hy]; exact hg₀01 _ (φ.mapsTo_model y hy)
    · rw [hgdef, indicator_of_notMem hy]; exact ⟨le_rfl, zero_le_one⟩
  · by_cases hy : y ∈ φ.source
    · have := hg₀f (φ y) (φ.mapsTo_model y hy)
      simp only [Function.comp_apply, φ.symm_apply_apply hy] at this
      rwa [hgdef, indicator_of_mem hy]
    · have hfy : f y = 0 := image_eq_zero_of_notMem_tsupport fun h => hy (hNφ (hfsupp h))
      rw [hgdef, indicator_of_notMem hy, hfy, sub_zero, abs_zero]
      exact hε.le

end SmallCharts

/-! ### Theorem 5.5.10 (preprint 5.37): partitions of unity and the approximation property -/

section Theorem537

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

/-- **Theorem 5.5.10 (preprint 5.37) "(ii) ⇒ (i)", the core: sc-smooth Urysohn functions.**  If `X` has an atlas of
local models with the sc-smooth approximation property, then for disjoint closed `s, t ⊆ X` there
is an sc-smooth `F : X → [0, 1]` with `F = 0` on `s` and `F = 1` on `t`.  (The text's construction:
a locally finite refinement `W_x` of small chart neighbourhoods `N_x`, continuous bumps `f_x`
equal to `1` near the points of a cover, sc-smooth approximations `ĝ_x` with `|f_x − ĝ_x| ≤ 1/2`
supported in `W_x`, and `F = τ(4 Σ ĝ_x − 1)`.) -/
theorem exists_isScSmoothMap_urysohn {S : Set (MChart X)} (hS : ∀ φ ∈ S, PX.IsChart φ)
    (hcov : ∀ x, ∃ φ ∈ S, x ∈ φ.source) (happ : ∀ φ ∈ S, φ.model.HasApproxProperty)
    {s t : Set X} (hs : IsClosed s) (ht : IsClosed t) (hst : Disjoint s t) :
    ∃ F : X → ℝ, PX.IsScSmoothMap realPolyfold F ∧ EqOn F 0 s ∧ EqOn F 1 t ∧
      ∀ x, F x ∈ Icc (0 : ℝ) 1 := by
  classical
  choose φ hφS hxφ using hcov
  -- small chart neighbourhoods `N_x` (inside `X ∖ s` for `x ∈ t`) and `N_x = X ∖ t` otherwise
  have hN : ∀ x, ∃ N : Set X, IsOpen N ∧ x ∈ N ∧
      (x ∈ t → N ⊆ sᶜ ∧ N ⊆ (φ x).source ∧ closure N ⊆ (φ x).source ∧
        closure (φ x '' N) ⊆ (φ x).model.O) ∧ (x ∉ t → N ⊆ tᶜ) := by
    intro x
    by_cases hxt : x ∈ t
    · have hxs : x ∈ sᶜ := fun h => hst.ne_of_mem h hxt rfl
      obtain ⟨N, hNo, hxN, hNsub, hNcl, hNO⟩ :=
        (φ x).exists_small_nhds (hxφ x) hs.isOpen_compl hxs
      exact ⟨N, hNo, hxN, fun _ => ⟨fun y hy => (hNsub hy).1, fun y hy => (hNsub hy).2, hNcl,
        hNO⟩, fun h => absurd hxt h⟩
    · exact ⟨tᶜ, ht.isOpen_compl, hxt, fun h => absurd h hxt, fun _ => subset_rfl⟩
  choose N hNo hxN hNt hNnt using hN
  -- a locally finite refinement and a subordinate bump covering
  obtain ⟨W, hWo, hWcov, hWlf, hWN⟩ :=
    precise_refinement N hNo (iUnion_eq_univ_iff.2 fun x => ⟨x, hxN x⟩)
  obtain ⟨f, hf⟩ := BumpCovering.exists_isSubordinate isClosed_univ W hWo (by rw [hWcov])
  -- the sc-smooth approximations
  have hg : ∀ x, ∃ g : X → ℝ, PX.IsScSmoothMap realPolyfold g ∧ (∀ y, g y ∈ Icc (0 : ℝ) 1) ∧
      tsupport g ⊆ W x ∧ (x ∈ t → ∀ y, |f x y - g y| ≤ 1 / 2) ∧ (x ∉ t → ∀ y, g y = 0) := by
    intro x
    by_cases hxt : x ∈ t
    · obtain ⟨-, hNφ, hNcl, hNO⟩ := hNt x hxt
      obtain ⟨g, hg, hg01, hgsupp, hgf⟩ :=
        (happ (φ x) (hφS x)).exists_approx (hS _ (hφS x)) (hWo x) ((hWN x).trans hNφ)
          ((closure_mono (hWN x)).trans hNcl)
          ((closure_mono (image_mono (hWN x))).trans hNO) (f x).continuous
          (fun y => ⟨f.nonneg x y, f.le_one x y⟩) (hf x) (by norm_num : (0 : ℝ) < 1 / 2)
      exact ⟨g, hg, hg01, hgsupp, fun _ => hgf, fun h => absurd hxt h⟩
    · refine ⟨fun _ => 0, isScSmoothMap_real_const 0, fun _ => ⟨le_rfl, zero_le_one⟩, ?_,
        fun h => absurd h hxt, fun _ _ => rfl⟩
      rw [show (fun _ : X => (0 : ℝ)) = 0 from rfl, tsupport_zero]; exact empty_subset _
  choose g hgsc hg01 hgsupp hgf hg0 using hg
  have hglf : LocallyFinite fun x => support (g x) :=
    hWlf.subset fun x => subset_closure.trans (hgsupp x)
  set G : X → ℝ := fun y => ∑ᶠ x, g x y with hGdef
  have hGsc : PX.IsScSmoothMap realPolyfold G := isScSmoothMap_real_finsum hgsc hglf
  have hG0 : ∀ y ∈ s, G y = 0 := by
    intro y hy
    refine finsum_eq_zero_of_forall_eq_zero fun x => ?_
    by_cases hxt : x ∈ t
    · exact image_eq_zero_of_notMem_tsupport fun h =>
        (hNt x hxt).1 (hWN x (hgsupp x h)) hy
    · exact hg0 x hxt y
  have hGt : ∀ y ∈ t, 1 / 2 ≤ G y := by
    intro y hy
    set x₀ := f.ind y (mem_univ y)
    have h1 : f x₀ y = 1 := f.ind_apply y (mem_univ y)
    have h2 : y ∈ N x₀ :=
      hWN x₀ (hf x₀ (subset_closure (by rw [mem_support, h1]; exact one_ne_zero)))
    have hx₀t : x₀ ∈ t := by
      by_contra hx₀
      exact hNnt x₀ hx₀ h2 hy
    have h3 := hgf x₀ hx₀t y
    rw [h1] at h3
    have h4 : 1 / 2 ≤ g x₀ y := by
      have := (abs_le.1 h3).2
      linarith
    exact h4.trans (single_le_finsum x₀ (hglf.point_finite y) fun j => (hg01 j y).1)
  -- `F = τ(4G − 1)`
  set σ : ℝ → ℝ := fun r => Real.smoothTransition (4 * r - 1) with hσ
  have hσc : ContDiff ℝ ∞ σ :=
    (Real.smoothTransition.contDiff (n := ⊤)).comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const)
  refine ⟨σ ∘ G, hGsc.comp_contDiff hσc, fun y hy => ?_, fun y hy => ?_, fun y =>
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩⟩
  · simp only [Function.comp_apply, hσ, hG0 y hy, Pi.zero_apply]
    exact Real.smoothTransition.zero_of_nonpos (by norm_num)
  · simp only [Function.comp_apply, hσ, Pi.one_apply]
    exact Real.smoothTransition.one_of_one_le (by linarith [hGt y hy])

/-- **Theorem 5.5.10 (preprint 5.37) "(ii) ⇒ (i)"**: if `X` has an atlas (a family of charts covering `X`) of local
models with the sc-smooth approximation property, then `X` admits sc-smooth partitions of unity:
by the sc-smooth Urysohn functions (`exists_isScSmoothMap_urysohn`) there is a bump covering
subordinate to the given cover with sc-smooth functions `fᵢ` (Mathlib's
`BumpCovering.exists_isSubordinate_of_prop`), and `ρᵢ = fᵢ ∏_{j < i}(1 − f_j)` is locally a finite
product of sc-smooth functions. -/
theorem admitsScPartitionsOfUnity_of_approx {S : Set (MChart X)} (hS : ∀ φ ∈ S, PX.IsChart φ)
    (hcov : ∀ x, ∃ φ ∈ S, x ∈ φ.source) (happ : ∀ φ ∈ S, φ.model.HasApproxProperty) :
    PX.AdmitsScPartitionsOfUnity := by
  classical
  intro ι V hVo hVcov
  obtain ⟨b, hbp, hb⟩ := BumpCovering.exists_isSubordinate_of_prop
    (fun g : X → ℝ => PX.IsScSmoothMap realPolyfold g) (fun s t hs ht hst => by
      obtain ⟨F, hF, hF0, hF1, hF01⟩ := exists_isScSmoothMap_urysohn hS hcov happ hs ht hst
      exact ⟨⟨F, continuousOn_univ.1 hF.continuousOn⟩, hF, hF0, hF1, hF01⟩)
    isClosed_univ V hVo (by rw [hVcov])
  refine ⟨b.toPartitionOfUnity, hb.toPartitionOfUnity, fun i => ?_⟩
  refine isScSmoothMap_real_of_eventuallyEq fun x => ?_
  obtain ⟨T, hT⟩ := b.exists_finset_toPartitionOfUnity_eventuallyEq i x
  refine ⟨_, ?_, hT⟩
  have h1 : (⇑(b i) * ⇑(∏ j ∈ T with WellOrderingRel j i, (1 - b j))) =
      fun y => b i y * ∏ j ∈ T with WellOrderingRel j i, (1 - b j y) := by
    funext y
    simp [ContinuousMap.coe_prod, Finset.prod_apply]
  rw [h1]
  exact (hbp i).real_mul (isScSmoothMap_real_finsetProd _ fun j _ =>
    (isScSmoothMap_real_const 1).real_sub (hbp j))

/-- **Theorem 5.5.10 (preprint 5.37) "(i) ⇒ (ii)"** for a chart restricted to an open `s` with `cl_X(s) ⊆ dom φ`:
if `X` admits sc-smooth partitions of unity, the local model `(φ(s), C, E)` has the sc-smooth
approximation property.  (The text's argument: `F = f ∘ φ` extended by `0`, the cover of `X` by
`{F < ε/2}` and the sets `U_x = {|F − F(x)| < ε/2} ∩ φ⁻¹(V)`, `x ∈ X`, a subordinate sc-smooth
partition of unity `(β₀, β_x)`, and `ĝ = Σ β_x F(x)`.  The extension `F` is continuous on `X`
because `cl_C(V) ⊆ φ(s)` and `cl_X(s) ⊆ dom φ` give `cl_X(φ⁻¹(V)) ⊆ s`; for the full chart this
fails, see the module docstring.) -/
theorem hasApproxProperty_restrict (h : PX.AdmitsScPartitionsOfUnity) {φ : MChart X}
    (hφ : PX.IsChart φ) {s : Set X} (hs : s ⊆ φ.source) (hso : IsOpen s)
    (hcl : closure s ⊆ φ.source) : (φ.restrict hs hso).model.HasApproxProperty := by
  intro W hW hWcl f hf hf01 hfsupp ε hε
  change closure (φ '' s ∩ W) ⊆ φ '' s at hWcl
  change ContinuousOn f (φ '' s) at hf
  change ∀ x ∈ φ '' s, f x ∈ Icc (0 : ℝ) 1 at hf01
  change closure (φ '' s ∩ support f) ∩ φ '' s ⊆ W at hfsupp
  -- the support of `f` and its preimage in `X`
  set K := closure (φ '' s ∩ support f) with hK
  have hKW : φ '' s ∩ support f ⊆ φ '' s ∩ W := fun z hz =>
    ⟨hz.1, hfsupp ⟨subset_closure hz, hz.1⟩⟩
  have hKs : K ⊆ φ '' s ∩ W := by
    intro z hz
    have hzO : z ∈ φ '' s := hWcl (closure_mono hKW hz)
    exact ⟨hzO, hfsupp ⟨hz, hzO⟩⟩
  obtain ⟨hBc, hBs⟩ := φ.isClosed_inter_preimage hcl isClosed_closure
    (hKs.trans inter_subset_left)
  -- `F = f ∘ φ` on `s`, `0` outside: continuous on `X`
  set F : X → ℝ := s.indicator (f ∘ φ) with hFdef
  have hFsupp : support F ⊆ φ.source ∩ φ ⁻¹' K := by
    intro y hy
    have hys : y ∈ s := by
      by_contra h'; exact hy (indicator_of_notMem h' _)
    have hfy : f (φ y) ≠ 0 := by
      have := mem_support.1 hy; rwa [hFdef, indicator_of_mem hys] at this
    exact ⟨hs hys, subset_closure ⟨mem_image_of_mem φ hys, hfy⟩⟩
  have hFcont : Continuous F := by
    refine continuous_iff_continuousAt.2 fun y => ?_
    by_cases hys : y ∈ s
    · have h1 : ContinuousOn (f ∘ φ) s :=
        hf.comp (φ.continuousOn_toFun.mono hs) fun y hy => mem_image_of_mem φ hy
      refine (h1.continuousAt (hso.mem_nhds hys)).congr ?_
      filter_upwards [hso.mem_nhds hys] with z hz
      rw [hFdef, indicator_of_mem hz]
    · have hyB : y ∉ φ.source ∩ φ ⁻¹' K := fun h' => hys (hBs h')
      refine continuousAt_const.congr (f := fun _ => (0 : ℝ)) ?_
      filter_upwards [hBc.isOpen_compl.mem_nhds hyB] with z hz
      exact (notMem_support.1 fun h' => hz (hFsupp h')).symm
  have hF01 : ∀ y, F y ∈ Icc (0 : ℝ) 1 := fun y => by
    by_cases hys : y ∈ s
    · rw [hFdef, indicator_of_mem hys]; exact hf01 _ (mem_image_of_mem φ hys)
    · rw [hFdef, indicator_of_notMem hys]; exact ⟨le_rfl, zero_le_one⟩
  -- the open cover `{F < ε/2}`, `U_x = T ∩ {|F − F(x)| < ε/2}` with `T = s ∩ φ⁻¹(W)`
  set T := s ∩ φ ⁻¹' W with hT
  have hTo : IsOpen T := (φ.continuousOn_toFun.mono hs).isOpen_inter_preimage hso hW
  let U : Option X → Set X := fun i => match i with
    | none => {y | F y < ε / 2}
    | some x => T ∩ {y | |F y - F x| < ε / 2}
  have hUo : ∀ i, IsOpen (U i) := by
    rintro (_ | x)
    · exact isOpen_lt hFcont continuous_const
    · exact hTo.inter (isOpen_lt ((hFcont.sub continuous_const).abs) continuous_const)
  have hUcov : ⋃ i, U i = univ := by
    refine eq_univ_of_forall fun y => mem_iUnion.2 ?_
    by_cases hy : F y < ε / 2
    · exact ⟨none, hy⟩
    · have hFy : F y ≠ 0 := fun h' => hy (by rw [h']; positivity)
      obtain ⟨hyφ, hyK⟩ := hFsupp hFy
      refine ⟨some y, ⟨hBs ⟨hyφ, hyK⟩, (hKs hyK).2⟩, ?_⟩
      change |F y - F y| < ε / 2
      rw [sub_self, abs_zero]; positivity
  obtain ⟨ρ, hρsub, hρsc⟩ := h (Option X) U hUo hUcov
  -- `ĝ = Σ β_x F(x)`
  let c : Option X → ℝ := fun i => match i with
    | none => 0
    | some x => F x
  have hc01 : ∀ i, c i ∈ Icc (0 : ℝ) 1 := by
    rintro (_ | x)
    · exact ⟨le_rfl, zero_le_one⟩
    · exact hF01 x
  set g : X → ℝ := fun y => ∑ᶠ i, ρ i y * c i with hgdef
  have hgsc : PX.IsScSmoothMap realPolyfold g :=
    isScSmoothMap_real_finsum (fun i => (hρsc i).real_mul (isScSmoothMap_real_const (c i)))
      (PartitionOfUnity.locallyFinite_mul ρ c)
  have hgT : tsupport g ⊆ T := by
    refine PartitionOfUnity.tsupport_finsum_mul_subset ρ c fun i hci => ?_
    rcases i with _ | x
    · exact absurd rfl hci
    · exact (hρsub (some x)).trans inter_subset_left
  have hgF : ∀ y, |F y - g y| ≤ ε / 2 := by
    intro y
    refine PartitionOfUnity.abs_sub_finsum_mul_le ρ c (F y) y fun i hi => ?_
    have hyU : y ∈ U i := hρsub i (subset_closure hi)
    rcases i with _ | x
    · change F y < ε / 2 at hyU
      change |F y - 0| ≤ ε / 2
      rw [sub_zero, abs_of_nonneg (hF01 y).1]; exact hyU.le
    · exact hyU.2.le
  -- back to the local model
  refine ⟨g ∘ φ.symm, (MPolyfold.IsChart.restrict PX hφ hs hso |> hgsc.real_chart), ?_, ?_, ?_⟩
  · intro z _
    exact PartitionOfUnity.finsum_mul_mem_Icc ρ c hc01 _
  · rintro z ⟨hz, hzO⟩
    change z ∈ φ '' s at hzO
    have hzO' : z ∈ φ.model.O := φ.image_subset_model hs hzO
    have hcw : ContinuousWithinAt φ.symm (φ '' s ∩ support (g ∘ φ.symm)) z :=
      (φ.continuousOn_invFun z hzO').mono fun w hw => φ.image_subset_model hs hw.1
    have h1 := hcw.mem_closure_image hz
    have h2 : φ.symm '' (φ '' s ∩ support (g ∘ φ.symm)) ⊆ support g := by
      rintro _ ⟨z', hz', rfl⟩; exact hz'.2
    have h3 : φ.symm z ∈ T := hgT (closure_mono h2 h1)
    have h4 : φ (φ.symm z) ∈ W := h3.2
    rwa [φ.apply_symm_apply hzO'] at h4
  · rintro z ⟨y, hys, rfl⟩
    have h1 := hgF y
    have h2 : F y = f (φ y) := by rw [hFdef, indicator_of_mem hys]; rfl
    change |f (φ y) - g (φ.symm (φ y))| ≤ ε
    rw [φ.symm_apply_apply (hs hys), ← h2]
    linarith [h1]

/-- **Theorem 5.5.10 (preprint 5.37)**: the M-polyfold `X` admits sc-smooth partitions of unity subordinate to any
open cover if and only if it admits an atlas (a family of charts of `X` covering `X`) whose local
models have the sc-smooth approximation property.  For "(i) ⇒ (ii)" the atlas consists of the
charts restricted to open sets `s` with `cl_X(s) ⊆ dom φ` (`hasApproxProperty_restrict`); whether
every chart of `X` has the property is not settled here. -/
theorem theorem_5_5_10 :
    PX.AdmitsScPartitionsOfUnity ↔ ∃ S : Set (MChart X), (∀ φ ∈ S, PX.IsChart φ) ∧
      (∀ x, ∃ φ ∈ S, x ∈ φ.source) ∧ ∀ φ ∈ S, φ.model.HasApproxProperty := by
  constructor
  · intro h
    refine ⟨{ψ | ∃ (φ : MChart X) (s : Set X) (hs : s ⊆ φ.source) (hso : IsOpen s),
      PX.IsChart φ ∧ closure s ⊆ φ.source ∧ ψ = φ.restrict hs hso}, ?_, ?_, ?_⟩
    · rintro ψ ⟨φ, s, hs, hso, hφ, -, rfl⟩
      exact MPolyfold.IsChart.restrict PX hφ hs hso
    · intro x
      obtain ⟨φ, hφ, hx⟩ := PX.exists_isChart_mem_source x
      obtain ⟨N, hNo, hxN, hNsub, hNcl, -⟩ := φ.exists_small_nhds hx isOpen_univ (mem_univ x)
      exact ⟨φ.restrict (hNsub.trans inter_subset_right) hNo,
        ⟨φ, N, hNsub.trans inter_subset_right, hNo, hφ, hNcl, rfl⟩, hxN⟩
    · rintro ψ ⟨φ, s, hs, hso, hφ, hcl, rfl⟩
      exact hasApproxProperty_restrict h hφ hs hso hcl
  · rintro ⟨S, hS, hcov, happ⟩
    exact admitsScPartitionsOfUnity_of_approx hS hcov happ

end Theorem537

/-! ### Banach spaces: `C^k` partitions of unity and bump functions (Definition 5.5.4 (preprint 5.31)) -/

section Banach

variable (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A Banach space **admits `C^k` partitions of unity** (§5.4.2, before Proposition 5.5.11 (preprint 5.38) and in
Theorems 5.5.13, 5.5.16 (preprint 5.40, 5.43)): every open cover of `V` has a subordinate partition of unity consisting of
`C^k` functions (`k ∈ ℕ ∪ {∞}`). -/
def AdmitsContDiffPartitionsOfUnity (k : ℕ∞) : Prop :=
  ∀ (ι : Type u) (U : ι → Set V), (∀ i, IsOpen (U i)) → ⋃ i, U i = univ →
    ∃ ρ : PartitionOfUnity ι V, ρ.IsSubordinate U ∧ ∀ i, ContDiff ℝ k (ρ i)

/-- **Definition 5.5.4 (preprint 5.31)** (`C^k`-bump function): the Banach space `V` admits a `C^k`-bump function if
there is a `C^k` function `f : V → ℝ`, not identically zero, with bounded support
(`k ∈ ℕ ∪ {∞}`). -/
def HasContDiffBump (k : ℕ∞) : Prop :=
  ∃ f : V → ℝ, ContDiff ℝ k f ∧ f ≠ 0 ∧ Bornology.IsBounded (support f)

end Banach

/-! ### Proposition 5.5.11 (preprint 5.38) -/

/-- **Proposition 5.5.11 (preprint 5.38)**: if the `0`-level `E₀` of the sc-Banach space `E` admits smooth (`C^∞`)
partitions of unity, then the local model `(O, C, E)` has the sc-smooth approximation property.
(The text calls it "an immediate consequence of Theorem 5.37"; the proof here is the argument of
"(i) ⇒ (ii)" carried out in `E₀` itself, which needs no partition of unity on open subsets: the
cover of `E₀` by `E₀ ∖ {x ∈ O | f(x) ≥ ε/2}` (closed in `E₀` because `cl(V) ⊆ O`) and by balls
`B(x, r_x) ⊆ W`, `x ∈ V`, on which `f` varies by less than `ε/2` on `O`; then `g = Σ β_x f(x)` is
`C^∞` on `E₀`, hence sc-smooth (Corollary 1.2.5 (preprint 1.20)).) -/
theorem proposition_5_5_11 (M : LocalModel) (hE : AdmitsContDiffPartitionsOfUnity (M.E 0) ⊤) :
    M.HasApproxProperty := by
  intro W hW hWcl f hf hf01 hfsupp ε hε
  -- `A = {x ∈ O | f(x) ≥ ε/2}` is closed in `E₀` and lies in `V = O ∩ W`
  set A : Set (M.E 0) := {z | z ∈ M.O ∧ ε / 2 ≤ f z} with hAdef
  have hAW : A ⊆ M.O ∩ W := fun z hz =>
    ⟨hz.1, hfsupp ⟨subset_closure ⟨hz.1, (lt_of_lt_of_le (half_pos hε) hz.2).ne'⟩, hz.1⟩⟩
  have hAc : IsClosed A := by
    refine isClosed_of_closure_subset fun z hz => ?_
    have hzO : z ∈ M.O := hWcl (closure_mono hAW hz)
    refine ⟨hzO, ?_⟩
    have h1 : ContinuousWithinAt f A z := (hf z hzO).mono fun w hw => hw.1
    have h2 := h1.mem_closure_image hz
    have h3 : f '' A ⊆ Ici (ε / 2) := by rintro _ ⟨w, hw, rfl⟩; exact hw.2
    exact (isClosed_Ici.closure_subset_iff.2 h3) h2
  -- balls around the points of `V`
  have hr : ∀ x : ↥(M.O ∩ W), ∃ r > 0, Metric.ball (x : M.E 0) r ⊆ W ∧
      ∀ y ∈ M.O, dist y x < r → |f y - f x| < ε / 2 := by
    rintro ⟨x, hxO, hxW⟩
    obtain ⟨r₁, hr₁, hb₁⟩ := Metric.isOpen_iff.1 hW x hxW
    obtain ⟨r₂, hr₂, hb₂⟩ := Metric.continuousWithinAt_iff.1 (hf x hxO) (ε / 2) (half_pos hε)
    refine ⟨min r₁ r₂, lt_min hr₁ hr₂, (Metric.ball_subset_ball (min_le_left _ _)).trans hb₁,
      fun y hy hyx => ?_⟩
    have := hb₂ hy (lt_of_lt_of_le hyx (min_le_right _ _))
    rwa [Real.dist_eq] at this
  choose r hr0 hrW hrf using hr
  let U : Option ↥(M.O ∩ W) → Set (M.E 0) := fun i => match i with
    | none => Aᶜ
    | some x => Metric.ball (x : M.E 0) (r x)
  have hUo : ∀ i, IsOpen (U i) := by
    rintro (_ | x)
    · exact hAc.isOpen_compl
    · exact Metric.isOpen_ball
  have hUcov : ⋃ i, U i = univ := by
    refine eq_univ_of_forall fun z => mem_iUnion.2 ?_
    by_cases hz : z ∈ A
    · exact ⟨some ⟨z, hAW hz⟩, Metric.mem_ball_self (hr0 _)⟩
    · exact ⟨none, hz⟩
  obtain ⟨ρ, hρsub, hρ⟩ := hE _ U hUo hUcov
  let c : Option ↥(M.O ∩ W) → ℝ := fun i => match i with
    | none => 0
    | some x => f x
  have hc01 : ∀ i, c i ∈ Icc (0 : ℝ) 1 := by
    rintro (_ | x)
    · exact ⟨le_rfl, zero_le_one⟩
    · exact hf01 _ x.2.1
  set g : M.E 0 → ℝ := fun y => ∑ᶠ i, ρ i y * c i with hgdef
  have hgC : ContDiff ℝ ∞ g := by
    refine contDiff_iff_contDiffAt.2 fun y => ?_
    obtain ⟨T, hT⟩ := finsum_eventually_eq_sum (PartitionOfUnity.locallyFinite_mul ρ c) y
    refine ContDiffAt.congr_of_eventuallyEq ?_ hT
    exact (ContDiff.sum fun i _ => (hρ i).mul contDiff_const).contDiffAt
  have hgsc : IsScSmooth (E := M.E) (F := realSc) univ g :=
    IsScSmooth.of_contDiffOn_finiteDimensional (V := ℝ) (isScDomain_univ _) hgC.contDiffOn
  have hgW : tsupport g ⊆ W := by
    refine PartitionOfUnity.tsupport_finsum_mul_subset ρ c fun i hci => ?_
    rcases i with _ | x
    · exact absurd rfl hci
    · exact (hρsub (some x)).trans (hrW x)
  refine ⟨g, ⟨mapsTo_univ _ _, fun R _ => IsScSmooth.comp R.isScDomain (isScDomain_univ _) hgsc
    R.isScSmooth (mapsTo_univ _ _)⟩, fun z _ => PartitionOfUnity.finsum_mul_mem_Icc ρ c hc01 z,
    fun z hz => hgW (closure_mono inter_subset_right hz.1), fun z hzO => ?_⟩
  refine (PartitionOfUnity.abs_sub_finsum_mul_le ρ c (f z) z fun i hi => ?_).trans
    (half_le_self hε.le)
  have hzU : z ∈ U i := hρsub i (subset_closure hi)
  rcases i with _ | x
  · change z ∉ A at hzU
    change |f z - 0| ≤ ε / 2
    have : f z < ε / 2 := not_le.1 fun h => hzU ⟨hzO, h⟩
    rw [sub_zero, abs_of_nonneg (hf01 z hzO).1]; exact this.le
  · exact (hrf x z hzO hzU).le

/-! ### Definition 5.5.12 (preprint 5.39) and Theorem 5.5.13 (preprint 5.40) (Toruńczyk, cited) -/

section CZero

open scoped ENNReal

/-- **Definition 5.5.12 (preprint 5.39)**: `c₀(Γ)`, the functions `f : Γ → ℝ` for which `{γ | |f(γ)| > ε}` is finite
for every `ε > 0` (`mem_cZero_iff`), with the norm `|f|_{c₀} = sup_γ |f(γ)|` (`norm_cZero`): the
closed subspace of `ℓ^∞(Γ)` of the functions tending to `0` along the cofinite filter. -/
def cZero (Γ : Type*) : Submodule ℝ (lp (fun _ : Γ => ℝ) ∞) where
  carrier := {f | Tendsto (fun γ => f γ) cofinite (𝓝 0)}
  add_mem' {f g} hf hg := by
    change Tendsto (fun γ => (f + g : lp (fun _ : Γ => ℝ) ∞) γ) cofinite (𝓝 0)
    simpa only [lp.coeFn_add, Pi.add_apply, add_zero] using hf.add hg
  zero_mem' := by
    change Tendsto (fun γ => (0 : lp (fun _ : Γ => ℝ) ∞) γ) cofinite (𝓝 0)
    simpa only [lp.coeFn_zero, Pi.zero_apply] using tendsto_const_nhds
  smul_mem' c f hf := by
    change Tendsto (fun γ => (c • f : lp (fun _ : Γ => ℝ) ∞) γ) cofinite (𝓝 0)
    simpa only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_zero] using hf.const_mul c

/-- The defining condition of `c₀(Γ)` in the text's form. -/
theorem mem_cZero_iff {Γ : Type*} {f : lp (fun _ : Γ => ℝ) ∞} :
    f ∈ cZero Γ ↔ ∀ ε > 0, {γ | ε < |f γ|}.Finite := by
  change Tendsto (fun γ => f γ) cofinite (𝓝 0) ↔ _
  rw [Metric.tendsto_nhds]
  simp only [Filter.eventually_cofinite, Real.dist_eq, sub_zero, not_lt]
  constructor
  · intro h ε hε
    exact (h ε hε).subset fun γ (hγ : ε < |f γ|) => show ε ≤ |f γ| from hγ.le
  · intro h ε hε
    exact (h (ε / 2) (half_pos hε)).subset fun γ (hγ : ε ≤ |f γ|) =>
      show ε / 2 < |f γ| from lt_of_lt_of_le (half_lt_self hε) hγ

/-- The norm of `c₀(Γ)`: `|f|_{c₀} = sup_γ |f(γ)|`. -/
theorem norm_cZero {Γ : Type*} (f : cZero Γ) :
    ‖f‖ = ⨆ γ, ‖(f : lp (fun _ : Γ => ℝ) ∞) γ‖ :=
  lp.norm_eq_ciSup _

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Definition 5.5.12 (preprint 5.39)**: a homeomorphic embedding `h : V → c₀(Γ)` is **coordinate-wise `C^k`** if
every coordinate `e ↦ h(e)(γ)` is `C^k`. -/
def IsCoordinatewiseContDiffEmbedding {Γ : Type*} (k : ℕ∞) (h : V → cZero Γ) : Prop :=
  Topology.IsEmbedding h ∧ ∀ γ, ContDiff ℝ k fun e => (h e : lp (fun _ : Γ => ℝ) ∞) γ

variable (V) in
/-- **Theorem 5.5.13 (preprint 5.40)** (Toruńczyk; [9], Theorem 30), **cited, not formalized**: the statement, for
the Banach space `V` and `k`: `V` admits `C^k` partitions of unity if and only if there are a set
`Γ` and a coordinate-wise `C^k` homeomorphic embedding of `V` into `c₀(Γ)`.  It is not used here;
it is proved for every real Banach space as `theorem_5_5_13` (`Torunczyk.lean`, 2026-11-12). -/
def TorunczykStatement (k : ℕ∞) : Prop :=
  AdmitsContDiffPartitionsOfUnity V k ↔
    ∃ (Γ : Type u) (h : V → cZero Γ), IsCoordinatewiseContDiffEmbedding k h

end CZero

/-! ### Definition 5.5.14 (preprint 5.41) and Proposition 5.5.15 (preprint 5.42): weakly compactly generated spaces -/

section WCG

variable (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Definition 5.5.14 (preprint 5.41)**: a Banach space `V` is **weakly compactly generated** (WCG) if there is a
subset `K` compact in the weak topology (`toWeakSpace ℝ V '' K` compact in `WeakSpace ℝ V`) whose
linear span is dense: `V = cl_V(span K)`. -/
def IsWCG : Prop :=
  ∃ K : Set V, IsCompact (toWeakSpace ℝ V '' K) ∧ closure (Submodule.span ℝ K : Set V) = univ

/-- A Banach space is **reflexive** if the canonical map `V → V''` is onto. -/
def IsReflexive : Prop := Surjective (NormedSpace.inclusionInDoubleDual ℝ V)

variable {V}

lemma span_closedBall_eq_top : Submodule.span ℝ (Metric.closedBall (0 : V) 1) = ⊤ := by
  refine eq_top_iff.2 fun v _ => ?_
  rcases eq_or_ne v 0 with rfl | hv
  · exact zero_mem _
  have h1 : ‖v‖⁻¹ • v ∈ Metric.closedBall (0 : V) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 hv)]
  have h2 := Submodule.smul_mem _ ‖v‖ (Submodule.subset_span h1)
  rwa [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hv), one_smul] at h2

/-- **Proposition 5.5.15 (preprint 5.42) (i)**: a reflexive Banach space is WCG.  The text's "the closed unit ball
is compact in the weak topology" (Kakutani's theorem) is Mathlib's
`NormedSpace.isCompact_closure_of_isBounded` (Banach–Alaoglu in `V''` and the embedding of `V`
with its weak topology into `V''` with its weak-* topology): the weak closure of the ball is weakly
compact; its span contains the ball, hence is `V`. -/
theorem proposition_5_5_15_reflexive (h : IsReflexive V) : IsWCG V := by
  set S : Set (WeakSpace ℝ V) := toWeakSpace ℝ V '' Metric.closedBall 0 1 with hS
  have hb : Bornology.IsBounded ((toWeakSpace ℝ V) ⁻¹' S) := by
    rw [hS, Set.preimage_image_eq _ (toWeakSpace ℝ V).injective]
    exact Metric.isBounded_closedBall
  have hrange : closure (NormedSpace.inclusionInDoubleDualWeak ℝ V '' S) ⊆
      range (NormedSpace.inclusionInDoubleDualWeak ℝ V) := by
    intro ψ _
    obtain ⟨y, hy⟩ := h (StrongDual.toWeakDual.symm ψ)
    refine ⟨toWeakSpace ℝ V y, ?_⟩
    refine DFunLike.ext _ _ fun f => ?_
    have h1 := DFunLike.congr_fun hy f
    rw [NormedSpace.dual_def] at h1
    exact h1
  have hK := NormedSpace.isCompact_closure_of_isBounded ℝ V S hb hrange
  set D : Set (WeakSpace ℝ V) := closure S with hD
  refine ⟨(toWeakSpace ℝ V) ⁻¹' D, ?_, ?_⟩
  · rwa [Set.image_preimage_eq _ (toWeakSpace ℝ V).surjective]
  · have hball : Metric.closedBall (0 : V) 1 ⊆ (toWeakSpace ℝ V) ⁻¹' D :=
      fun x hx => (subset_closure : S ⊆ closure S) (mem_image_of_mem _ hx)
    have htop : Submodule.span ℝ ((toWeakSpace ℝ V) ⁻¹' D) = ⊤ :=
      eq_top_iff.2 (span_closedBall_eq_top (V := V) ▸ Submodule.span_mono hball)
    rw [htop, Submodule.top_coe, closure_univ]

/-- **Proposition 5.5.15 (preprint 5.42) (ii)**: a separable Banach space is WCG: for a dense sequence `(yₙ)`,
`K = {0} ∪ {yₙ / ((n + 1)(|yₙ| + 1))}` is norm compact (a null sequence with its limit), hence
weakly compact, and its span contains every `yₙ`. -/
theorem proposition_5_5_15_separable [TopologicalSpace.SeparableSpace V] : IsWCG V := by
  obtain ⟨y, hy⟩ := TopologicalSpace.exists_dense_seq V
  set a : ℕ → ℝ := fun n => ((n + 1 : ℝ) * (‖y n‖ + 1))⁻¹ with ha
  have hapos : ∀ n, 0 < a n := fun n => inv_pos.2 (by positivity)
  set z : ℕ → V := fun n => a n • y n with hz
  have hzlim : Tendsto z atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 : 0 < (n + 1 : ℝ) := by positivity
    have h2 : 0 < ‖y n‖ + 1 := by positivity
    have h3 : ‖z n‖ = (‖y n‖ / (‖y n‖ + 1)) * (1 / (n + 1)) := by
      rw [hz, norm_smul, Real.norm_eq_abs, abs_of_pos (hapos n), ha]
      field_simp
    rw [h3]
    exact mul_le_of_le_one_left (by positivity) ((div_le_one h2).2 (by linarith))
  set K : Set V := insert 0 (range z)
  have hKc : IsCompact K := hzlim.isCompact_insert_range
  refine ⟨K, ?_, ?_⟩
  · have hcont : Continuous (toWeakSpace ℝ V) := by
      have : ⇑(toWeakSpace ℝ V) = ⇑(toWeakSpaceCLM ℝ V) :=
        funext fun x => (toWeakSpaceCLM_eq_toWeakSpace ℝ V x).symm
      rw [this]; exact (toWeakSpaceCLM ℝ V).continuous
    exact hKc.image hcont
  · have hsub : range y ⊆ Submodule.span ℝ K := by
      rintro _ ⟨n, rfl⟩
      have : y n = (a n)⁻¹ • z n := by
        rw [hz, smul_smul, inv_mul_cancel₀ (hapos n).ne', one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_insert_of_mem _ ⟨n, rfl⟩))
    exact eq_univ_of_forall fun v => closure_mono hsub (hy.closure_eq ▸ mem_univ v)

end WCG

/-! ### Hilbert spaces; Theorem 5.5.16 (preprint 5.43) (cited) and Corollary 5.5.17 (preprint 5.44) -/

section Hilbert

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A Banach space whose norm comes from a continuous bilinear form, `‖v‖² = b(v, v)` (a Hilbert
space, stated as in Proposition 5.5.8 (preprint 5.35)), admits a `C^∞`-bump function: `τ(1 − b(v, v))`. -/
theorem hasContDiffBump_of_hilbert (b : V →L[ℝ] V →L[ℝ] ℝ) (hb : ∀ v, ‖v‖ ^ 2 = b v v) :
    HasContDiffBump V ⊤ := by
  refine ⟨fun v => Real.smoothTransition (1 - b v v), ?_, fun h => ?_, ?_⟩
  · exact (Real.smoothTransition.contDiff (n := ⊤)).comp (contDiff_const.sub
      (b.isBoundedBilinearMap.contDiff.comp (contDiff_id.prodMk contDiff_id)))
  · have h0 := congrFun h 0
    simp only [map_zero, sub_zero, Pi.zero_apply] at h0
    exact one_ne_zero ((Real.smoothTransition.one_of_one_le le_rfl).symm.trans h0)
  · refine Metric.isBounded_ball (x := (0 : V)) (r := 1) |>.subset fun v hv => ?_
    have h1 : 0 < 1 - b v v := by
      by_contra h
      exact hv (Real.smoothTransition.zero_of_nonpos (not_lt.1 h))
    have h2 : ‖v‖ ^ 2 < 1 ^ 2 := by rw [hb, one_pow]; linarith
    rw [mem_ball_zero_iff]
    exact lt_of_pow_lt_pow_left₀ 2 zero_le_one h2

/-- **A Hilbert space is reflexive** (the first step of the proof of Corollary 5.5.17 (preprint 5.44)): with the inner
product of the norm (`InnerProductSpace.ofNorm`, the parallelogram law holds because
`‖v‖² = b(v, v)`), every `φ ∈ V''` is `J(y)` for the Riesz representative `y` of
`x ↦ φ(⟨x, ·⟩)`. -/
theorem isReflexive_of_hilbert [CompleteSpace V] (b : V →L[ℝ] V →L[ℝ] ℝ)
    (hb : ∀ v, ‖v‖ ^ 2 = b v v) : IsReflexive V := by
  have hpar : ∀ x y : V, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) := by
    intro x y
    simp only [← sq, hb, map_add, map_sub, add_apply, sub_apply]
    ring
  let _ : InnerProductSpace ℝ V := InnerProductSpace.ofNorm ℝ hpar
  intro φ
  let ψ₀ : V →ₗ[ℝ] ℝ :=
    { toFun := fun x => φ (InnerProductSpace.toDual ℝ V x)
      map_add' := fun x y => by simp only [map_add]
      map_smul' := fun c x => by
        simp only [map_smulₛₗ, RingHom.id_apply, starRingEnd_apply, star_trivial, smul_eq_mul] }
  let ψ : StrongDual ℝ V := ψ₀.mkContinuous ‖φ‖ fun x => by
    change ‖φ (InnerProductSpace.toDual ℝ V x)‖ ≤ ‖φ‖ * ‖x‖
    calc ‖φ (InnerProductSpace.toDual ℝ V x)‖ ≤ ‖φ‖ * ‖InnerProductSpace.toDual ℝ V x‖ :=
          φ.le_opNorm _
      _ = ‖φ‖ * ‖x‖ := by rw [LinearIsometryEquiv.norm_map]
  refine ⟨(InnerProductSpace.toDual ℝ V).symm ψ, ContinuousLinearMap.ext fun f => ?_⟩
  rw [NormedSpace.dual_def]
  set z := (InnerProductSpace.toDual ℝ V).symm f with hz
  have hfz : f = InnerProductSpace.toDual ℝ V z := by
    rw [hz, LinearIsometryEquiv.apply_symm_apply]
  rw [hfz, InnerProductSpace.toDual_apply_apply, real_inner_comm,
    InnerProductSpace.toDual_symm_apply]
  rfl

variable (V) in
/-- **Theorem 5.5.16 (preprint 5.43)** ([12] = Godefroy, Troyanski, Whitfield, Zizler, J. Funct. Anal. 1983; [9],
Theorem 31): the statement, for the Banach space `V` and `k`: if `V` is
WCG and admits a `C^k`-bump function, then it admits `C^k` partitions of unity.  Used as an
explicit hypothesis in Corollary 5.5.17 (preprint 5.44) here; proved for every real Banach space
(`theorem_5_5_16`, `WCGPartitionsOfUnity.lean`, 2026-11-12). -/
def GodefroyTroyanskiWhitfieldZizlerStatement (k : ℕ∞) : Prop :=
  IsWCG V → HasContDiffBump V k → AdmitsContDiffPartitionsOfUnity V k

/-- **Corollary 5.5.17 (preprint 5.44)**: if `E₀` is a Hilbert space (its norm comes from a continuous bilinear form,
`‖v‖² = b(v, v)`, as in Proposition 5.5.8 (preprint 5.35)), then the local model `(O, C, E)` has the sc-smooth
approximation property — **under the explicit hypothesis that Theorem 5.5.16 (preprint 5.43) holds for `E₀` and
`k = ∞`** (a deep result of Banach space geometry, cited from [12]; it is proved since 2026-11-12 as
`theorem_5_5_16`, and the corollary without the hypothesis is `corollary_5_5_17_unconditional`).  The proof
is the text's: `E₀` is reflexive (`isReflexive_of_hilbert`), hence WCG (Proposition 5.5.15 (preprint 5.42) (i)),
and has a `C^∞` bump function (`hasContDiffBump_of_hilbert`); Theorem 5.5.16 (preprint 5.43) gives `C^∞`
partitions of unity on `E₀`, and Proposition 5.5.11 (preprint 5.38) (not Theorem 5.37, as the text says) the
approximation property. -/
theorem corollary_5_5_17 (M : LocalModel)
    (hH : ∃ b : M.E 0 →L[ℝ] M.E 0 →L[ℝ] ℝ, ∀ v, ‖v‖ ^ 2 = b v v)
    (h543 : GodefroyTroyanskiWhitfieldZizlerStatement (M.E 0) ⊤) : M.HasApproxProperty := by
  obtain ⟨b, hb⟩ := hH
  exact proposition_5_5_11 M (h543 (proposition_5_5_15_reflexive (isReflexive_of_hilbert b hb))
    (hasContDiffBump_of_hilbert b hb))

end Hilbert

/-! ### Consequences on M-polyfolds -/

section Consequences

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

/-- **An M-polyfold built on sc-Hilbert spaces admits sc-smooth partitions of unity**, under the
explicit hypothesis that Theorem 5.5.16 (preprint 5.43) holds (`k = ∞`) for the `0`-levels of the local models of
an atlas: Corollary 5.5.17 (preprint 5.44) in the charts and Theorem 5.5.10 (preprint 5.37). -/
theorem MPolyfold.admitsScPartitionsOfUnity_of_hilbert
    (h : ∀ x, ∃ φ : MChart X, PX.IsChart φ ∧ x ∈ φ.source ∧
      (∃ b : φ.model.E 0 →L[ℝ] φ.model.E 0 →L[ℝ] ℝ, ∀ v, ‖v‖ ^ 2 = b v v) ∧
      GodefroyTroyanskiWhitfieldZizlerStatement (φ.model.E 0) ⊤) :
    PX.AdmitsScPartitionsOfUnity := by
  refine theorem_5_5_10.2 ⟨{φ | PX.IsChart φ ∧
    (∃ b : φ.model.E 0 →L[ℝ] φ.model.E 0 →L[ℝ] ℝ, ∀ v, ‖v‖ ^ 2 = b v v) ∧
    GodefroyTroyanskiWhitfieldZizlerStatement (φ.model.E 0) ⊤}, fun φ hφ => hφ.1,
    fun x => ?_, fun φ hφ => corollary_5_5_17 _ hφ.2.1 hφ.2.2⟩
  obtain ⟨φ, hφ, hx, hb, h543⟩ := h x
  exact ⟨φ, ⟨hφ, hb, h543⟩, hx⟩

/-- **Sc-smooth partitions of unity give sc-smooth bump functions** (the easy direction of the
open problem stated after Definition 5.5.2 (preprint 5.29)): for `x ∈ U`, the function of a partition of unity
subordinate to `{U, X ∖ {x}}` attached to `U` equals `1` at `x`. -/
theorem MPolyfold.AdmitsScPartitionsOfUnity.admitsBumpFunctions
    (h : PX.AdmitsScPartitionsOfUnity) : PX.AdmitsBumpFunctions := by
  intro x U hU hx
  let V : ULift Bool → Set X := fun i => if i.down then U else {x}ᶜ
  have hVo : ∀ i, IsOpen (V i) := by
    rintro ⟨_ | _⟩
    · exact isOpen_compl_singleton
    · exact hU
  have hVcov : ⋃ i, V i = univ := by
    refine eq_univ_of_forall fun y => mem_iUnion.2 ?_
    by_cases hy : y = x
    · exact ⟨⟨true⟩, by simp only [V, if_true]; exact hy ▸ hx⟩
    · exact ⟨⟨false⟩, by simpa [V] using hy⟩
  obtain ⟨ρ, hρsub, hρsc⟩ := h _ V hVo hVcov
  refine ⟨ρ ⟨true⟩, hρsc _, ?_, hρsub ⟨true⟩⟩
  have h0 : ρ ⟨false⟩ x = 0 := image_eq_zero_of_notMem_tsupport fun h' =>
    (hρsub ⟨false⟩ h') rfl
  have h1 := ρ.sum_eq_one (mem_univ x)
  rw [finsum_eq_sum_of_support_subset (s := Finset.univ) _ (by simp)] at h1
  have h2 : ∑ i : ULift Bool, ρ i x = ρ ⟨true⟩ x + ρ ⟨false⟩ x := by
    rw [← (Equiv.ulift (α := Bool)).symm.sum_comp]
    simp
  rw [h2, h0, add_zero] at h1
  rw [h1]; exact one_ne_zero

end Consequences

end Polyfold
