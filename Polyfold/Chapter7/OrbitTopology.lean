import Polyfold.Chapter7.Uniformizer
import Polyfold.Chapter7.ProperSubsets
import Polyfold.Chapter7.Michael
import Polyfold.Chapter7.LocConnected
import Mathlib.Topology.Metrizable.Urysohn

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2017, arXiv 1707.08941), Part II, §7.3,
pp. 244–247: **Theorem 7.2** (p. 244), **Lemmas 7.4** (pp. 244–245), **7.5** (p. 245), **7.6**
(pp. 245–246), **7.7** (p. 246), **Corollary 7.1** (p. 247), the remark before Definition 7.14 and
**Corollary 7.2** (p. 247).  There is no 2014 preprint of Part II; numbers and pages are the 2017
text's.  Definition 7.14 (component compact) is in `EpGroupoid.lean` (`IsComponentCompact`).

# Topological properties of the orbit space

## The text, paraphrased

(Theorem 7.2) The orbit space `|X|` of an ep-groupoid is locally metrizable, regular and
Hausdorff; if `|X|` is paracompact it is metrizable (Nagata–Smirnov).  (Lemma 7.4) Every
`z ∈ |X|` has an open metrizable neighbourhood; one can take `|U(x)|` for `U(x)` with the natural
`G_x`-action.  *Proof*: `U` is metrizable with a metric `d`; `ρ(y, y') = max_g d(g ∗ y, g ∗ y')` is
an equivalent `G_x`-invariant metric, `ρ̂([y], [y']) = min{ρ(g ∗ y, h ∗ y') | g, h ∈ G_x}` defines
the quotient topology on `G_x\U`, and Proposition 7.6 carries it to `|U|`.  (Lemma 7.5) Every
`z` has a countable monotone basis of open neighbourhoods; by Lemma 7.4.  (Lemma 7.6) `|X|` is
Hausdorff: otherwise `x_k → x`, `x'_k → x'`, `φ_k : x_k → x'_k`, and properness (3) gives a
subsequence `φ_k → φ₀ : x → x'`.  (Lemma 7.7) `|X|` is regular: for closed `A ∌ z = π(x)` choose
`O ∋ x` with `π(O) ∩ A = ∅` and `t : s⁻¹(cl O) → X` proper, `x ∈ O' ⊂ cl O' ⊂ O`; every
`y ∈ π⁻¹(A)` has `V(y)` with no morphism from `O'` into `V(y)` (else properness gives `φ` with
`s φ ∈ cl O'`, `t φ = y`); `V = π(⋃ V(y)) ⊇ A` and `π(O')` are disjoint.  (Corollary 7.1) If `|X|`
is second countable it is metrizable (Urysohn).  (p. 247) The induced topology on a subset of `|X|`
is again locally metrizable, regular and Hausdorff.  (Corollary 7.2) For a component compact
`K ⊆ |X|` there is an open `U ⊇ K` with `cl U` paracompact; `cl U` is then metrizable, and so is
`U`.  *Proof*: work in a connected component of `K`, so that `K` may be assumed compact; every
`z ∈ K` has an open `U(z)` with metrizable, hence paracompact, closure; finitely many `U(zᵢ)`
cover `K`; `U = ⋃ cl U(zᵢ)` is paracompact, Hausdorff, regular and locally metrizable, hence
metrizable (Nagata–Smirnov), and so is `U = ⋃ U(zᵢ)`.

## What is formalized (namespace `Polyfold.EpGroupoid`)

* **Lemma 7.4**: `metrizableSpace_orbitRel_quotient_naturalRep` (`G_x\U(x)` is metrizable, by the
  text's metrics `ρ` and `ρ̂`), `lemma_7_4_naturalRep` (`|U(x)| = π(U(x))` is metrizable) and
  `lemma_7_4` (every `z` has an open metrizable neighbourhood).  The metrics are the private
  `maxDist` (`ρ`, with `maxDist_smul`: invariance) and `quotDist` (`ρ̂`) for a finite group acting
  by homeomorphisms on a metrizable space (`metrizableSpace_orbitRel_quotient`).
* **Lemma 7.5**: `lemma_7_5` (Proposition 7.2 of `Basic.lean`; the instance
  `proposition_7_2_firstCountableTopology`).
* **Lemma 7.6**: the instance `lemma_7_6 : T2Space X.OrbitSpace`, with `t1Space_orbitSpace`
  (points of `|X|` are closed).
* **Lemma 7.7**: the instance `lemma_7_7 : RegularSpace X.OrbitSpace`.
* **Theorem 7.2**: `theorem_7_2` (the three properties) and `theorem_7_2_metrizable`
  (paracompact `|X|` is metrizable, by Smirnov's theorem `metrizableSpace_of_locally`).
* **Corollary 7.1**: `corollary_7_1` (Urysohn's theorem,
  `TopologicalSpace.metrizableSpace_of_t3_secondCountable`).
* **p. 247, subsets**: `exists_metrizable_nhds_subtype` (every subset of `|X|` is locally
  metrizable; regular and Hausdorff are Mathlib's subtype instances) and
  `metrizableSpace_of_paracompactSpace_subtype` (a paracompact subset of `|X|` is metrizable).
* The instance `locallyPathConnectedSpace_orbitSpace` (`|X|` is locally path connected, hence
  locally connected, and its components are open).
* **Corollary 7.2**: `exists_isOpen_metrizableSpace_closure` (the step "every `z` has an open
  `U(z)` with metrizable closure"), `corollary_7_2_of_isCompact` (the compact case, with
  `cl U ⊆ W` for a given open `W ⊇ K`) and `corollary_7_2`.

## Reading

* **Locally metrizable** is read as: every point has an open neighbourhood which is metrizable in
  the subspace topology (`MetrizableSpace V`).  Regular and Hausdorff are Mathlib's `RegularSpace`
  and `T2Space`; the text's definition of regular (disjoint open sets around a point and a
  nonempty closed set not containing it) is `RegularSpace`.
* **Lemma 7.4.**  `G_x\U(x)` is `MulAction.orbitRel.Quotient` (Proposition 7.6,
  `Uniformizer.lean`).  The metric `d` on `U` is `metrizableSpaceMetric` (Theorem 2.2 [2.16],
  `MPolyfold.metrizableSpace`); `ρ(y, y') = max_g d(g ∗ y, g ∗ y')` is `Finset.sup'` over `G_x`
  (finite, Proposition 7.4).  The text's `ρ̂([y], [y']) = min_{g, h} ρ(g ∗ y, h ∗ y')` is computed
  as `min_h ρ(y, h ∗ y')`, the same number by the invariance of `ρ`.  "`ρ` is equivalent to `d`"
  and "`ρ̂` defines the quotient topology" are used in the form of `MetricSpace.ofDistTopology`:
  a set of `G_x\U` is open in the quotient topology iff it contains a `ρ̂`-ball around each of its
  points (`d ≤ ρ`, and `{y' | ρ(y, y') < ε} = ⋂_g g⁻¹(B_d(g ∗ y, ε))` is open).  `ρ` itself is not
  installed as a metric on `U`.
* **Lemma 7.5** is Proposition 7.2 (`Basic.lean`), proved there from the metrizability of `X` and
  the openness of `π`; the text derives it from Lemma 7.4.  Indices start at `0`.
* **Lemma 7.6** is derived from Lemma 7.7 and the closedness of points (`t1Space_orbitSpace`), a
  regular `T₁` space being Hausdorff.  The closedness of `{|x|}` is Proposition 7.14 (1) for the
  proper set `{x}` (`ProperSubsets.lean`); it replaces the text's extraction of a convergent
  subsequence of `φ_k : x_k → x'_k`, which uses the same properness (3).
* **Lemma 7.7** is proved with a closed neighbourhood basis
  (`RegularSpace.of_exists_mem_nhds_isClosed_subset`): for a neighbourhood `N` of `π(x)`, a closed
  neighbourhood `O'` of `x` inside `π⁻¹(N) ∩ V(x)` (`X` is regular) has `π(O')` closed by
  Proposition 7.3 (`proposition_7_3_of_isProperMap`), a neighbourhood of `π(x)` (Proposition 7.1)
  and inside `N`.  This replaces the text's sets `V(y)`, `V̂`, which use the same properness.
* **Theorem 7.2, the metrizability**: Smirnov's theorem (Part I, `metrizableSpace_of_locally`:
  paracompact, Hausdorff and locally metrizable), with Lemmas 7.4 and 7.6.  The text's
  "Nagata/Smirnov" is this form.  "If in addition `|X|` is paracompact" is the hypothesis
  `ParacompactSpace X.OrbitSpace` (Definition 7.15's `HasParacompactOrbitSpace`); it is
  satisfiable (`hasParacompactOrbitSpace_trivial`).
* **Corollary 7.1** has `SecondCountableTopology X.OrbitSpace` as an instance hypothesis; `T₃` is
  Lemmas 7.6 and 7.7.
* **Corollary 7.2** (PLAN II.6, 5).  "We work in a connected component of `K`" is read as: in a
  connected component `C` of `|X|`, where `K ∩ C` is compact (Definition 7.14).  As we read it,
  this needs the components of `|X|` to be open, which the text does not state: `|X|` is the
  quotient of the locally path connected `X` (`LocConnected.lean`), hence locally connected
  (`locallyPathConnectedSpace_orbitSpace`).  The passage from the compact pieces back to `K` is
  not in the text: the open `U_C ⊇ K ∩ C` are chosen with `cl U_C ⊆ C`; since the components are
  open and pairwise disjoint, `(cl U_C)_C` is locally finite, `cl(⋃ U_C) = ⋃ cl U_C`, and this
  locally finite union of closed paracompact sets is paracompact (Proposition 2.17 [2.57],
  `paracompactSpace_iUnion` of `Michael.lean`).  In the compact case "every `z ∈ K` has an open
  `U(z)` whose closure is metrizable" uses Lemma 7.4 and the regularity of `|X|` (Lemma 7.7);
  "`⋃ cl U(zᵢ)` is paracompact" needs Michael's lemma (Lemma 2.7 [2.56] through Proposition 2.17
  [2.57], `paracompactSpace_biUnion_of_finite`), which the text does not cite.  The text's `U`
  names two sets, `⋃ cl U(zᵢ)` and `⋃ U(zᵢ)` (possible misprint); here `U` is the open `⋃ U(zᵢ)`
  and `cl U = ⋃ cl U(zᵢ)`.  The metrizability of `cl U` is Smirnov's theorem in the subspace
  (`metrizableSpace_of_paracompactSpace_subtype`), which is the remark before Definition 7.14
  (subsets of `|X|` are locally metrizable, regular and Hausdorff).
* **Instances on `X.OrbitSpace`** declared here: `lemma_7_6` (`T2Space`), `lemma_7_7`
  (`RegularSpace`), `locallyPathConnectedSpace_orbitSpace`.
* **Hypotheses.**  No hypothesis "for all …" is added.  The hypotheses `ParacompactSpace
  X.OrbitSpace`, `SecondCountableTopology X.OrbitSpace`, `IsComponentCompact K` and `IsCompact K`
  are satisfiable: the trivial ep-groupoid of an M-polyfold `Z` has paracompact orbit space
  (`hasParacompactOrbitSpace_trivial`), homeomorphic to `Z` (`trivialOrbitHomeomorph`; second
  countable for `Z = ℝⁿ`), and `K = ∅` is compact.
* No possible misprint was found on pp. 244–247 other than Corollary 7.2's `U`.
-/

open Set Filter Topology Function TopologicalSpace

noncomputable section

namespace Polyfold

/-! ### The text's metrics `ρ` and `ρ̂` (Lemma 7.4), for a finite group -/

section QuotientMetric

variable (G : Type*) {U : Type*} [Group G] [Fintype G] [MulAction G U] [PseudoMetricSpace U]

/-- `ρ(y, z) = max_g d(g y, g z)` (Lemma 7.4). -/
private def maxDist (y z : U) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun g : G => dist (g • y) (g • z)

variable {G}

private theorem dist_smul_le_maxDist (g : G) (y z : U) :
    dist (g • y) (g • z) ≤ maxDist G y z :=
  Finset.le_sup' (fun g : G => dist (g • y) (g • z)) (Finset.mem_univ g)

private theorem dist_le_maxDist (y z : U) : dist y z ≤ maxDist G y z := by
  simpa only [one_smul] using dist_smul_le_maxDist (1 : G) y z

private theorem maxDist_lt_iff {y z : U} {ε : ℝ} :
    maxDist G y z < ε ↔ ∀ g : G, dist (g • y) (g • z) < ε := by
  simp only [maxDist, Finset.sup'_lt_iff, Finset.mem_univ, forall_const]

private theorem maxDist_self (y : U) : maxDist G y y = 0 :=
  le_antisymm (Finset.sup'_le _ _ fun _ _ => (dist_self _).le)
    (dist_nonneg.trans (dist_le_maxDist y y))

private theorem maxDist_comm (y z : U) : maxDist G y z = maxDist G z y := by
  simp only [maxDist, dist_comm]

private theorem maxDist_triangle (y z w : U) :
    maxDist G y w ≤ maxDist G y z + maxDist G z w :=
  Finset.sup'_le _ _ fun g _ => (dist_triangle _ (g • z) _).trans
    (add_le_add (dist_smul_le_maxDist g y z) (dist_smul_le_maxDist g z w))

/-- **`ρ` is invariant** (Lemma 7.4): `ρ(h y, h z) = ρ(y, z)`. -/
private theorem maxDist_smul (h : G) (y z : U) : maxDist G (h • y) (h • z) = maxDist G y z := by
  refine le_antisymm (Finset.sup'_le _ _ fun g _ => ?_) (Finset.sup'_le _ _ fun g _ => ?_)
  · rw [smul_smul, smul_smul]
    exact dist_smul_le_maxDist (g * h) y z
  · have := dist_smul_le_maxDist (g * h⁻¹) (h • y) (h • z)
    rwa [smul_smul, smul_smul, inv_mul_cancel_right] at this

variable (G) in
/-- `min_h ρ(y, h z)`, the quotient distance before passing to the quotient. -/
private def quotDistAux (y z : U) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun h : G => maxDist G y (h • z)

private theorem quotDistAux_le (h : G) (y z : U) : quotDistAux G y z ≤ maxDist G y (h • z) :=
  Finset.inf'_le (fun h : G => maxDist G y (h • z)) (Finset.mem_univ h)

private theorem exists_quotDistAux_eq (y z : U) :
    ∃ h : G, quotDistAux G y z = maxDist G y (h • z) := by
  obtain ⟨h, -, hh⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := G))
    fun h : G => maxDist G y (h • z)
  exact ⟨h, hh⟩

private theorem quotDistAux_smul_right (k : G) (y z : U) :
    quotDistAux G y (k • z) = quotDistAux G y z := by
  refine le_antisymm (Finset.le_inf' _ _ fun h _ => ?_) (Finset.le_inf' _ _ fun h _ => ?_)
  · have := quotDistAux_le (h * k⁻¹) y (k • z)
    rwa [smul_smul, inv_mul_cancel_right] at this
  · rw [smul_smul]
    exact quotDistAux_le (h * k) y z

private theorem quotDistAux_smul_left (k : G) (y z : U) :
    quotDistAux G (k • y) z = quotDistAux G y z := by
  refine le_antisymm (Finset.le_inf' _ _ fun h _ => ?_) (Finset.le_inf' _ _ fun h _ => ?_)
  · rw [← maxDist_smul k, smul_smul]
    exact quotDistAux_le (k * h) (k • y) z
  · have := quotDistAux_le (k⁻¹ * h) y z
    rwa [← maxDist_smul k, smul_smul, mul_inv_cancel_left] at this

private theorem quotDistAux_comm_le (y z : U) : quotDistAux G y z ≤ quotDistAux G z y := by
  refine Finset.le_inf' _ _ fun h _ => ?_
  have := quotDistAux_le h⁻¹ y z
  rwa [← maxDist_smul h, smul_inv_smul, maxDist_comm] at this

private theorem quotDistAux_comm (y z : U) : quotDistAux G y z = quotDistAux G z y :=
  le_antisymm (quotDistAux_comm_le y z) (quotDistAux_comm_le z y)

private theorem quotDistAux_triangle (y z w : U) :
    quotDistAux G y w ≤ quotDistAux G y z + quotDistAux G z w := by
  obtain ⟨h, hh⟩ := exists_quotDistAux_eq (G := G) y z
  obtain ⟨k, hk⟩ := exists_quotDistAux_eq (G := G) z w
  rw [hh, hk, ← maxDist_smul h z, smul_smul]
  exact (quotDistAux_le (h * k) y w).trans (maxDist_triangle _ _ _)

variable (G U) in
/-- **The quotient distance** `ρ̂([y], [z]) = min_{g, h} ρ(g y, h z) = min_h ρ(y, h z)` on `G\U`
(Lemma 7.4). -/
private def quotDist :
    MulAction.orbitRel.Quotient G U → MulAction.orbitRel.Quotient G U → ℝ :=
  Quotient.lift₂ (quotDistAux G) <| by
    rintro a₁ b₁ a₂ b₂ ⟨g, rfl⟩ ⟨h, rfl⟩
    exact (quotDistAux_smul_left g _ _).trans (quotDistAux_smul_right h _ _)

private theorem quotDist_mk (y z : U) :
    quotDist G U (Quotient.mk _ y) (Quotient.mk _ z) = quotDistAux G y z := rfl

end QuotientMetric

/-- **The quotient of a metrizable space by a finite group of homeomorphisms is metrizable**, by
the text's metric `ρ̂` (the argument of Lemma 7.4). -/
private theorem metrizableSpace_orbitRel_quotient {G U : Type*} [Group G] [Finite G]
    [MulAction G U] [TopologicalSpace U] [MetrizableSpace U]
    (hc : ∀ g : G, Continuous fun y : U => g • y) :
    MetrizableSpace (MulAction.orbitRel.Quotient G U) := by
  let _ := Fintype.ofFinite G
  let _ := metrizableSpaceMetric U
  have hmk : ∀ q : MulAction.orbitRel.Quotient G U, ∃ y : U, Quotient.mk _ y = q :=
    Quotient.exists_rep
  -- `ρ̂` defines the quotient topology.
  have hH : ∀ s : Set (MulAction.orbitRel.Quotient G U), IsOpen s ↔
      ∀ q ∈ s, ∃ ε > 0, ∀ q', quotDist G U q q' < ε → q' ∈ s := by
    intro s
    rw [← isQuotientMap_quotient_mk'.isOpen_preimage]
    constructor
    · intro hs q hq
      obtain ⟨y, rfl⟩ := hmk q
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hs y hq
      refine ⟨ε, hε, fun q' hq' => ?_⟩
      obtain ⟨z, rfl⟩ := hmk q'
      obtain ⟨h, hh⟩ := exists_quotDistAux_eq (G := G) y z
      rw [quotDist_mk, hh] at hq'
      have hmem : h • z ∈ Quotient.mk (MulAction.orbitRel G U) ⁻¹' s :=
        hball (lt_of_le_of_lt (by rw [dist_comm]; exact dist_le_maxDist _ _) hq')
      have hq : Quotient.mk (MulAction.orbitRel G U) (h • z) = Quotient.mk _ z :=
        Quotient.sound ⟨h, rfl⟩
      rwa [mem_preimage, hq] at hmem
    · intro hs
      refine isOpen_iff_mem_nhds.2 fun y hy => ?_
      obtain ⟨ε, hε, hball⟩ := hs _ hy
      have hN : (⋂ g : G, (fun z => g • z) ⁻¹' Metric.ball (g • y) ε) ∈ 𝓝 y :=
        (isOpen_iInter_of_finite fun g => Metric.isOpen_ball.preimage (hc g)).mem_nhds
          (mem_iInter.2 fun g => Metric.mem_ball_self hε)
      refine mem_of_superset hN fun z hz => hball _ ?_
      have hz' : maxDist G y z < ε := maxDist_lt_iff.2 fun g => by
        rw [dist_comm]
        exact mem_iInter.1 hz g
      have := quotDistAux_le (1 : G) y z
      rw [one_smul] at this
      exact lt_of_le_of_lt this hz'
  let _ : MetricSpace (MulAction.orbitRel.Quotient G U) :=
    MetricSpace.ofDistTopology (quotDist G U) (fun q => ?_) (fun q q' => ?_)
      (fun q q' q'' => ?_) hH fun q q' hqq' => ?_
  · infer_instance
  · obtain ⟨y, rfl⟩ := hmk q
    refine le_antisymm ?_ ?_
    · have := quotDistAux_le (1 : G) y y
      rwa [one_smul, maxDist_self] at this
    · obtain ⟨h, hh⟩ := exists_quotDistAux_eq (G := G) y y
      rw [quotDist_mk, hh]
      exact dist_nonneg.trans (dist_le_maxDist _ _)
  · obtain ⟨y, rfl⟩ := hmk q
    obtain ⟨z, rfl⟩ := hmk q'
    exact quotDistAux_comm y z
  · obtain ⟨y, rfl⟩ := hmk q
    obtain ⟨z, rfl⟩ := hmk q'
    obtain ⟨w, rfl⟩ := hmk q''
    exact quotDistAux_triangle y z w
  · obtain ⟨y, rfl⟩ := hmk q
    obtain ⟨z, rfl⟩ := hmk q'
    obtain ⟨h, hh⟩ := exists_quotDistAux_eq (G := G) y z
    rw [quotDist_mk, hh] at hqq'
    have h0 : dist y (h • z) = 0 :=
      le_antisymm (hqq' ▸ dist_le_maxDist _ _) dist_nonneg
    rw [dist_eq_zero] at h0
    rw [h0]
    exact Quotient.sound ⟨h, rfl⟩

namespace EpGroupoid

universe u

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-! ### Lemma 7.4 -/

variable {X} in
/-- **Lemma 7.4, `G_x\U(x)`**: the quotient `G_x\U(x)` of a natural representation is metrizable,
by the quotient metric `ρ̂` of the `G_x`-invariant metric `ρ(y, y') = max_g d(g ∗ y, g ∗ y')`. -/
theorem metrizableSpace_orbitRel_quotient_naturalRep {x : Obj} (R : X.NaturalRep x) :
    MetrizableSpace (MulAction.orbitRel.Quotient (X.Isotropy x) R.U) := by
  have := X.PObj.metrizableSpace
  exact metrizableSpace_orbitRel_quotient R.continuous_smul'

variable {X} in
/-- **Lemma 7.4, `|U(x)|`**: for `U(x)` with the natural `G_x`-action, `|U(x)| = π(U(x))` is
metrizable (Proposition 7.6 carries `ρ̂` to `|U(x)|`). -/
theorem lemma_7_4_naturalRep {x : Obj} (R : X.NaturalRep x) : MetrizableSpace (X.π '' R.U) :=
  have := metrizableSpace_orbitRel_quotient_naturalRep R
  (proposition_7_6 R).symm.isEmbedding.metrizableSpace

/-- **Lemma 7.4 (local metrizability)**: every `z ∈ |X|` has an open neighbourhood `V(z)` on
which the topology is metrizable (`V(z) = |U(x)|`, `z = |x|`). -/
theorem lemma_7_4 (z : X.OrbitSpace) : ∃ V : Set X.OrbitSpace, IsOpen V ∧ z ∈ V ∧
    MetrizableSpace V := by
  obtain ⟨x, rfl⟩ := X.surjective_π z
  obtain ⟨R, -⟩ := theorem_7_1 X x isOpen_univ (mem_univ x)
  exact ⟨X.π '' R.U, X.proposition_7_1 _ R.isOpen_U, mem_image_of_mem _ R.mem_U,
    lemma_7_4_naturalRep R⟩

/-! ### Lemma 7.5 -/

/-- **Lemma 7.5 (countable neighbourhood bases)**: every `z ∈ |X|` has a countable basis of open
neighbourhoods `z ∈ V_{k+1}(z) ⊆ V_k(z)` (Proposition 7.2). -/
theorem lemma_7_5 (z : X.OrbitSpace) :
    ∃ V : ℕ → Set X.OrbitSpace, (∀ k, IsOpen (V k) ∧ z ∈ V k) ∧ (𝓝 z).HasAntitoneBasis V :=
  X.proposition_7_2 z

/-! ### Lemmas 7.7 and 7.6 -/

/-- **Points of `|X|` are closed**: `{|x|} = π({x})` with `{x}` proper (Proposition 7.14 (1)). -/
theorem t1Space_orbitSpace : T1Space X.OrbitSpace := by
  refine ⟨fun z => ?_⟩
  obtain ⟨x, rfl⟩ := X.surjective_π z
  rw [← image_singleton]
  exact X.proposition_7_14_one (X.isProperSubset_of_isCompact isCompact_singleton)

/-- **Lemma 7.7 (regularity)**: `|X|` is a regular space.  Every neighbourhood `N` of `π(x)`
contains the closed neighbourhood `π(O')`, `O'` a closed neighbourhood of `x` in `π⁻¹(N) ∩ V(x)`
(Proposition 7.3). -/
instance lemma_7_7 : RegularSpace X.OrbitSpace := by
  refine RegularSpace.of_exists_mem_nhds_isClosed_subset fun z N hN => ?_
  obtain ⟨x, rfl⟩ := X.surjective_π z
  obtain ⟨V, hVo, hxV, hV⟩ := X.exists_isProperMap x
  have hN' : X.π ⁻¹' N ∩ V ∈ 𝓝 x :=
    inter_mem (X.continuous_π.continuousAt.preimage_mem_nhds hN) (hVo.mem_nhds hxV)
  obtain ⟨t, ht, htc, hts⟩ := exists_mem_nhds_isClosed_subset hN'
  refine ⟨X.π '' t, ?_, ?_, ?_⟩
  · rw [← X.proposition_7_1_map_nhds x]
    exact image_mem_map ht
  · have h := X.proposition_7_3_of_isProperMap hV
      ((hts.trans inter_subset_right).trans subset_closure)
    rw [htc.closure_eq] at h
    rw [h]
    exact isClosed_closure
  · exact (image_mono (hts.trans inter_subset_left)).trans (image_preimage_subset _ _)

/-- **Lemma 7.6 (Hausdorffness of the orbit space)**: `|X|` is Hausdorff (a regular space whose
points are closed). -/
instance lemma_7_6 : T2Space X.OrbitSpace := by
  have := X.t1Space_orbitSpace
  infer_instance

/-! ### Theorem 7.2 and Corollary 7.1 -/

/-- **Theorem 7.2 (basic topological properties of `|X|`)**: `|X|` is locally metrizable, regular
and Hausdorff. -/
theorem theorem_7_2 :
    (∀ z : X.OrbitSpace, ∃ V : Set X.OrbitSpace, IsOpen V ∧ z ∈ V ∧ MetrizableSpace V) ∧
      RegularSpace X.OrbitSpace ∧ T2Space X.OrbitSpace :=
  ⟨X.lemma_7_4, X.lemma_7_7, X.lemma_7_6⟩

/-- **Theorem 7.2, metrizability**: if `|X|` is paracompact, it is metrizable (Smirnov's theorem,
`metrizableSpace_of_locally`, with Lemmas 7.4 and 7.6). -/
theorem theorem_7_2_metrizable (h : ParacompactSpace X.OrbitSpace) :
    MetrizableSpace X.OrbitSpace :=
  metrizableSpace_of_locally X.lemma_7_4

/-- **Corollary 7.1 (metrizability criterion)**: if `|X|` is second countable, it is metrizable
(Urysohn: a second countable regular Hausdorff space is metrizable). -/
theorem corollary_7_1 [SecondCountableTopology X.OrbitSpace] : MetrizableSpace X.OrbitSpace :=
  metrizableSpace_of_t3_secondCountable X.OrbitSpace

/-! ### Subsets of `|X|` (p. 247) -/

/-- **Subsets of `|X|` are locally metrizable** (p. 247): every point of `S ⊆ |X|` has an open
neighbourhood in `S` which is metrizable.  (Regular and Hausdorff: Mathlib's subtype instances.) -/
theorem exists_metrizable_nhds_subtype (S : Set X.OrbitSpace) (w : S) :
    ∃ W : Set S, IsOpen W ∧ w ∈ W ∧ MetrizableSpace W := by
  obtain ⟨V, hVo, hwV, hV⟩ := X.lemma_7_4 w.1
  refine ⟨Subtype.val ⁻¹' V, hVo.preimage continuous_subtype_val, hwV, ?_⟩
  exact ((IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal).codRestrict V
    fun a => a.2).metrizableSpace

/-- **A paracompact subset of `|X|` is metrizable** (Smirnov's theorem in the subspace). -/
theorem metrizableSpace_of_paracompactSpace_subtype (S : Set X.OrbitSpace) [ParacompactSpace S] :
    MetrizableSpace S :=
  metrizableSpace_of_locally (X.exists_metrizable_nhds_subtype S)

/-! ### Corollary 7.2 -/

/-- **`|X|` is locally path connected**, as a quotient of the locally path connected `X`
(`LocConnected.lean`); in particular its connected components are open. -/
instance locallyPathConnectedSpace_orbitSpace : LocallyPathConnectedSpace X.OrbitSpace :=
  X.PObj.locallyPathConnectedSpace_quotient X.orbitSetoid

/-- Every neighbourhood `W` of `z ∈ |X|` contains the closure of an open neighbourhood `U(z)`
whose closure is metrizable (the first step of the proof of Corollary 7.2: Lemmas 7.4, 7.7). -/
theorem exists_isOpen_metrizableSpace_closure {z : X.OrbitSpace} {W : Set X.OrbitSpace}
    (hW : W ∈ 𝓝 z) :
    ∃ U : Set X.OrbitSpace, IsOpen U ∧ z ∈ U ∧ closure U ⊆ W ∧ MetrizableSpace (closure U) := by
  obtain ⟨V, hVo, hzV, hV⟩ := X.lemma_7_4 z
  obtain ⟨t, ht, htc, htWV⟩ := exists_mem_nhds_isClosed_subset (inter_mem hW (hVo.mem_nhds hzV))
  have hcl : closure (interior t) ⊆ W ∩ V := (closure_minimal interior_subset htc).trans htWV
  exact ⟨interior t, isOpen_interior, mem_interior_iff_mem_nhds.2 ht,
    hcl.trans inter_subset_left,
    (IsEmbedding.inclusion (hcl.trans inter_subset_right)).metrizableSpace⟩

/-- **Corollary 7.2, the compact case** (the text's proof): a compact `K ⊆ |X|` inside an open `W`
has an open neighbourhood `U` with `cl U ⊆ W` paracompact; `cl U` and `U` are metrizable. -/
theorem corollary_7_2_of_isCompact {K W : Set X.OrbitSpace} (hK : IsCompact K) (hW : IsOpen W)
    (hKW : K ⊆ W) :
    ∃ U : Set X.OrbitSpace, IsOpen U ∧ K ⊆ U ∧ closure U ⊆ W ∧ ParacompactSpace (closure U) ∧
      MetrizableSpace (closure U) ∧ MetrizableSpace U := by
  choose U hUo hzU hUW hUm using fun z : K =>
    X.exists_isOpen_metrizableSpace_closure (hW.mem_nhds (hKW z.2))
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun z : K => U z) hUo fun k hk =>
    mem_iUnion.2 ⟨⟨k, hk⟩, hzU _⟩
  have hcl : closure (⋃ z ∈ t, U z) = ⋃ z ∈ t, closure (U z) := Finset.closure_biUnion t U
  have hpc : ParacompactSpace (closure (⋃ z ∈ t, U z)) := by
    rw [hcl]
    exact paracompactSpace_biUnion_of_finite t.finite_toSet (fun z _ => isClosed_closure)
      fun z _ => by
        have := hUm z
        exact paracompactSpace_of_metrizableSpace _
  have hm := X.metrizableSpace_of_paracompactSpace_subtype (closure (⋃ z ∈ t, U z))
  refine ⟨⋃ z ∈ t, U z, isOpen_biUnion fun z _ => hUo z, ht, ?_, hpc, hm,
    (IsEmbedding.inclusion subset_closure).metrizableSpace⟩
  rw [hcl]
  exact iUnion₂_subset fun z _ => hUW z

/-- **Corollary 7.2**: a component compact `K ⊆ |X|` has an open neighbourhood `U` such that
`cl_{|X|}(U)` is paracompact; `cl_{|X|}(U)` and `U` are metrizable. -/
theorem corollary_7_2 {K : Set X.OrbitSpace} (hK : X.IsComponentCompact K) :
    ∃ U : Set X.OrbitSpace, IsOpen U ∧ K ⊆ U ∧ ParacompactSpace (closure U) ∧
      MetrizableSpace (closure U) ∧ MetrizableSpace U := by
  -- In every component `C`, an open `U_C ⊇ K ∩ C` with `cl U_C ⊆ C` paracompact.
  have hC : ∀ C : range (connectedComponent : X.OrbitSpace → Set X.OrbitSpace),
      ∃ U : Set X.OrbitSpace, IsOpen U ∧ K ∩ C.1 ⊆ U ∧ closure U ⊆ C.1 ∧
        ParacompactSpace (closure U) := by
    rintro ⟨_, c, rfl⟩
    obtain ⟨U, hUo, hKU, hUC, hpc, -⟩ :=
      X.corollary_7_2_of_isCompact (hK c) isOpen_connectedComponent inter_subset_right
    exact ⟨U, hUo, hKU, hUC, hpc⟩
  choose U hUo hKU hUC hUp using hC
  -- The components are open and disjoint, so the family `(cl U_C)_C` is locally finite.
  have hlf : LocallyFinite fun C => closure (U C) := by
    intro w
    refine ⟨connectedComponent w, isOpen_connectedComponent.mem_nhds mem_connectedComponent,
      (finite_singleton (⟨connectedComponent w, w, rfl⟩ :
        range (connectedComponent : X.OrbitSpace → Set X.OrbitSpace))).subset ?_⟩
    rintro ⟨_, c, rfl⟩ ⟨a, ha, haw⟩
    have h1 : connectedComponent c = connectedComponent a := connectedComponent_eq (hUC _ ha)
    have h2 : connectedComponent w = connectedComponent a := connectedComponent_eq haw
    exact Subtype.ext (h1.trans h2.symm)
  have hcl : closure (⋃ C, U C) = ⋃ C, closure (U C) :=
    (hlf.subset fun C => subset_closure).closure_iUnion
  have : ∀ C, ParacompactSpace (closure (U C)) := hUp
  have hpc : ParacompactSpace (closure (⋃ C, U C)) := by
    rw [hcl]
    exact paracompactSpace_iUnion (fun C => isClosed_closure) hlf
  have hm := X.metrizableSpace_of_paracompactSpace_subtype (closure (⋃ C, U C))
  refine ⟨⋃ C, U C, isOpen_iUnion hUo, fun k hk => mem_iUnion.2 ⟨⟨_, k, rfl⟩,
    hKU _ ⟨hk, mem_connectedComponent⟩⟩, hpc, hm,
    (IsEmbedding.inclusion subset_closure).metrizableSpace⟩

end EpGroupoid

end Polyfold
