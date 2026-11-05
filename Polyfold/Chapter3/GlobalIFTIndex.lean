import Polyfold.Chapter3.GlobalIFTNearbyOnto

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.1 and §3.6:
**the dimension of the solution set is the Fredholm index**, and the other clauses of Theorems
3.19, 3.54 and 3.56 that the statements of `GlobalIFTTheorems.lean` and `GlobalIFTNearbyOnto.lean`
leave out: the index of `f'(x₀)`, "`ker f'(y) = T_yS`" in a chart, the local constancy of the
index along the solution set, and "good position = surjectivity" when `∂X = ∅`.

# The Fredholm index and the solution set

## The text, paraphrased

(Theorem 3.19, interior case) `d_X ≡ 0`, `f(x₀) = 0`, `f'(x₀)` surjective: (1) `f'(x₀)` is an
sc-Fredholm operator; (2) there is an open neighbourhood `U` of `x₀` such that the local solution
set `S(f, U)` is a sub-M-polyfold "which is a smooth manifold without boundary **whose dimension
agrees with the Fredholm index of `f'(x₀)`**"; (3) at every `y ∈ S(f, U)`, `f'(y)` is surjective
and `ker f'(y) = T_yS(f, U)`.  (Theorem 3.54, proof) "abbreviating `d = dim ker f'(x)`, the
solution set `S ⊆ V` possesses the `d`-dimensional tangent germ property".  (Before Theorem 3.56)
"If `∂X = ∅`, the condition of good position is an empty condition": `(f, x)` is in good position
iff `f'(x)` is surjective.  (Theorem 3.56) `∂X = ∅`, `f'(x)` surjective at every zero: the
solution set is a smooth manifold without boundary.  (Proof of Proposition 6.2) the index is
locally constant along the solution set.

## What is formalized

* `Polyfold.StrongBundle.IsSurjLinOfIndex B f y d`: **"`f'(y)` is surjective, Fredholm, of index
  `d = dim ker f'(y)`"**, chart-intrinsically: in every strong bundle chart `c` of `P` around `y`
  and at the level-`1` point `z` over `ϕ(y)`, the linearization `Lin(z) : T_zO → K_z` (`linAt`,
  `LinearizationCharts.lean`) is surjective, Fredholm, and `ind Lin(z) = dim ker Lin(z) = d`.
  `Polyfold.StrongBundle.IsLinSurjAt B f y`: **"`f'(y)` is surjective"** (in some chart; by
  `linAt_chart_independence` then in every chart).
* `Polyfold.StrongBundle.linAt_index_of_conjugationData_wholeChart`: in the chart of Definition 3.11 at `x₀`
  with conjugation data `dc` of `g − s` to a basic germ, the linearization in **every** chart
  around `x₀` is Fredholm of index `dim dc.Pn − dim dc.Q` (and onto when `(f, x₀)` is in good
  position): Proposition 3.52 in the centred chart (`proposition_3_52_local_index_wholeChart`) carried by
  the chart independence.  `StrongBundle.isSurjLinOfIndex_of_conjugationData_wholeChart`,
  `StrongBundle.IsGoodPositionGermWholeChart.exists_isSurjLinOfIndex`.
* **Dimension = index** (Finding 170): `Polyfold.theorem_3_54_tangentGermChart_index_wholeChart`,
  `theorem_3_54_tangentGermChart_solutionSet_index_wholeChart`, `theorem_3_54_two_index_wholeChart`: the dimension `d`
  of the tangent germ data of the solution set at `x₀` (Definition 3.25 (2)) satisfies
  `IsSurjLinOfIndex f x₀ d`, i.e. `d = dim ker f'(x₀) = ind f'(x₀)` in every chart.  From
  `theorem_3_54_tangentGermChart_proj_conj_wholeChart`, which exposes that `d = dim Pn − dim Q` for the
  conjugation in the chart from which the tangent germ chart is built.
* **The index is locally constant along the solution set** (Finding 171, the text's Proposition
  6.2 along `S`; Finding 188): `Polyfold.theorem_3_54_index_locally_constant_wholeChart` — on an open
  `Vx ∋ x₀`, every zero `y` has `IsSurjLinOfIndex f y d` with the same `d` as `x₀`: the dimension
  of the solution set is locally constant (`theorem_3_54_two_wholeChart`) and equals the index at every zero
  in good position (Theorem 3.54 (1), `theorem_3_54_one'_wholeChart`).  `Polyfold.theorem_3_54_index_wholeChart`:
  Theorem 3.54 (1), (2) with this.
* `Polyfold.theorem_3_23_index_wholeChart`, `Polyfold.theorem_3_19_index_wholeChart`: Theorems 3.23 and 3.19 with the
  text's hypotheses (as `theorem_3_23'_wholeChart`, `theorem_3_19'_wholeChart`), with the dimension `d` of the manifold
  `S(f, U)` equal to the Fredholm index (and to `dim ker f'(y)`) at every `y ∈ S(f, U)`, and with
  the induced structure tame.
* `Polyfold.theorem_3_19_linearization_index_wholeChart`: the first clause of Theorem 3.19 with the index:
  in the chart of Definition 3.53, `Dg(0)` and `Tf̃(0)` are Fredholm, `Tf̃(0)` is onto, and both
  have index `dim d.Pn − dim d.Q = dim ker Tf̃(0)` for every conjugation `d` of `g − s` to a
  basic germ (`proposition_3_52_index_wholeChart` with the surjectivity of Definition 3.53).
* `Polyfold.theorem_3_54_ker_eq_tangent_wholeChart` (**"`ker f'(y) = T_yS`" in a chart**, Finding 172): in
  the strong bundle chart `c` at `x₀` and the conjugating sc-diffeomorphism `ψ` of the proof of
  Theorem 3.54, at every zero `y` near `x₀`, with `ψ(ϕ(y)) = v + σ(v)`, the derivative `Dψ(z)`
  maps `ker Lin(z)` (the kernel of `f'(y)` in the chart `c`) onto the tangent space
  `N_v = {n + Dσ(v)n | n ∈ K}` of the solution graph at `v`.
* **Good position when `d_X(y) = 0`** (Finding 173):
  `Polyfold.isInGoodPositionIn_of_subset` (a subspace of `T` is in good position inside `T` to a
  cone containing `T`), `Polyfold.StrongBundle.isGoodPositionGerm_of_linAt_surj_of_degIndex_eq_zero_wholeChart`
  and `StrongBundle.isGoodPositionGerm_of_isLinSurjAt_wholeChart`: if `d_X(y) = 0`, an sc-Fredholm germ at a
  zero `y` whose linearization is onto in a tame chart is in good position — the partial cone
  `C_yX` is the whole tangent space, so the kernel condition of Definition 3.53 is void;
  `StrongBundle.IsGoodPositionGermWholeChart.isLinSurjAt` and
  `StrongBundle.isGoodPositionGerm_iff_isLinSurjAt_wholeChart` (good position iff surjectivity when
  `d_X(y) = 0`).
* `Polyfold.theorem_3_19_of_surjective_wholeChart`, `Polyfold.theorem_3_56_of_surjective_wholeChart`: **Theorems 3.19 and
  3.56 with the text's hypothesis "`f'(x)` surjective"** (`IsLinSurjAt`) instead of
  `IsGoodPositionGermWholeChart`; `Polyfold.theorem_3_56_tame_wholeChart`, `Polyfold.theorem_3_57_index_wholeChart`: Theorems 3.56
  and 3.57 with the tameness of the induced structure, the regular data of Definition 3.25 (2) at
  every zero, and their dimension equal to the Fredholm index.
* `Polyfold.normal_injective_of_exists_range_scDeriv_eq_ρ`,
  `Polyfold.exists_range_scDeriv_eq_ρ_iff_normal_injective` (Finding 174, the converse in
  Finding 100): at a zero `z₀` of a filler with `ker Dg(z₀) ⊆ T_{z₀}O`, the surjectivity of
  `Tf̃(z₀) : T_{z₀}O → K_{z₀}` implies that `C(z₀) = (1 − ρ(z₀))Dg(z₀)|_{ker Dr(z₀)}` is
  injective (condition (3) of Definition 3.4 at `z₀`); with the converse
  (`exists_range_scDeriv_eq_ρ_of_normal_injective`), the two are equivalent.  With Theorem 3.54
  (1) this gives `Polyfold.isGoodPositionGermFilled_of_isGoodPositionGerm_wholeChart`: the filler condition
  `IsGoodPositionGermFilledWholeChart` (the added hypothesis of `theorem_3_54_one_wholeChart`) follows from good
  position, for the filler of `theorem_3_54_nearby_kernel_wholeChart`.

## What the text leaves implicit, and the choices made (the findings)

* **"The dimension agrees with the Fredholm index"** needs the dimension `d = dim ker D(h + t)(0)`
  of the proof of Theorem 3.54 to be compared with the index of `f'(x₀)`.  `D(h + t)(0)` is
  surjective and Fredholm of index `n − N` (Proposition 3.10, Corollary 3.41), so `d = n − N`;
  and `n − N` is the index of `Tf̃(0)` for the **same** conjugation (Proposition 3.52 with
  `ConjugationData`, `FredholmGermIndex.lean`).  The tangent germ chart of
  `theorem_3_54_tangentGermChart_proj_wholeChart` is built from the chart of Definition 3.53 by destructuring
  an existential, so its `Pn`, `Q` had to be exposed (`theorem_3_54_graph_proj_conj_wholeChart`,
  `theorem_3_54_tangentGermChart_proj_conj_wholeChart`).  The index is then transported to every chart by
  `linAt_chart_independence`.  No hypothesis is added.
* **The index in the interior case**: the text's Theorem 3.19 states `f'(x₀)` sc-Fredholm; as in
  `proposition_3_52_wholeChart`, only the level-`0` Fredholm property and index are formalized.
* **"`ker f'(y) = T_yS(f, U)`"**: `T_yS` as a subspace of `T_yX` (Definition 2.38) is not
  formalized (gap G.13); the chart form is the image of `ker f'(y)` under the derivative of the
  chart `ψ ∘ ϕ` of the tangent germ data, `Dψ(z)(ker Lin(z)) = N_v`.
* **Good position and surjectivity when `∂X = ∅`**: Definition 3.53 is stated in the chart of
  Definition 3.11 with the partial quadrant `C` of the chart, which need not be the whole space
  even if `d_X(y) = 0`; in a tame chart `d_C(ϕ(y)) = d_X(y)` (Proposition 2.36,
  `degIndex_eq_chartDegIndex_of_isTameRetract`), so `d_X(y) = 0` makes the partial quadrant
  `C_{ϕ(y)}` the whole space and the kernel condition automatic.  The tameness of the chart of
  the germ data at `y` (Definition 3.50, `IsScFredholmSectionTameWholeChart`) is used for this; the
  surjectivity, given in some chart, is carried to that chart by `IsLinSurjAt.linAt_surjective`.
* **Tameness** (Definitions 3.50, 3.51; Findings 190–199): the germ at `x₀` is in good position
  in a tame chart (`IsGoodPositionGermTameWholeChart`), the section has tame germ data where the good
  position of the nearby zeros is concluded (`IsScFredholmSectionTameWholeChart`), and the conclusions
  "`(f, y)` in good position" are in tame charts.
-/

open Set Filter Topology Function Module ContinuousLinearMap

noncomputable section

namespace Polyfold

variable {E F : ScBanach}

/-! ### Linear algebra -/

section Linear

/-- A subspace `N` of a subspace `T ⊆ E₀` is in good position inside `T` to every cone `C` that
contains `T` (Definition 3.21 inside `T`): `N ∩ C = N`, and any algebraic complement of `N` in `T`
is a good complement (with any constant, both sides of the condition being true). -/
theorem isInGoodPositionIn_of_subset {T N : Submodule ℝ (E 0)} {C : Set (E 0)} (hNT : N ≤ T)
    (hTC : (T : Set (E 0)) ⊆ C) : IsInGoodPositionIn E T C N := by
  classical
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl (N.comap T.subtype)
  refine ⟨hNT, ?_, Q.map T.subtype, Submodule.map_subtype_le _ _, ?_, ?_, 1, one_pos, ?_⟩
  · have : (Subtype.val ⁻¹' C : Set N) = univ :=
      eq_univ_of_forall fun x => hTC (hNT x.2)
    rw [this, interior_univ]
    exact univ_nonempty
  · rw [eq_bot_iff]
    rintro x ⟨hxN, q, hq, rfl⟩
    have hq' : q ∈ N.comap T.subtype ⊓ Q := ⟨hxN, hq⟩
    rw [hQ.inf_eq_bot, Submodule.mem_bot] at hq'
    rw [hq', map_zero]
    exact Submodule.zero_mem _
  · refine le_antisymm (sup_le hNT (Submodule.map_subtype_le _ _)) fun x hx => ?_
    have hmem : (⟨x, hx⟩ : T) ∈ N.comap T.subtype ⊔ Q := by
      rw [hQ.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hmem
    refine Submodule.mem_sup.2 ⟨a, ha, b, ⟨b, hb, rfl⟩, ?_⟩
    have := congrArg Subtype.val hab
    simpa using this
  · rintro x hx p ⟨q, -, rfl⟩ -
    exact ⟨fun _ => hTC (T.add_mem (hNT hx) q.2), fun _ => hTC (hNT hx)⟩

end Linear

/-! ### Condition (3) of Definition 3.4 at a nearby zero and the surjectivity of `Tf̃(z₀)` -/

section Normal

variable {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

open StrongRetr

/-- **The converse of `exists_range_scDeriv_eq_ρ_of_normal_injective`** (Finding 100's "iff"):
at a point `z₀` of the retract with `ker Dg(z₀) ⊆ T_{z₀}O`, if `Tf̃(z₀) = Dg(z₀)|_{T_{z₀}O}` maps
onto `K_{z₀} = ρ(z₀)F`, then `C(z₀) = (1 − ρ(z₀))Dg(z₀)|_{ker Dr(z₀)}` is injective: for
`b ∈ ker Dr(z₀)` with `ρ(z₀)Dg(z₀)b = Dg(z₀)b` choose `a ∈ T_{z₀}O` with `Dg(z₀)a = Dg(z₀)b`;
then `a − b ∈ ker Dg(z₀) ⊆ T_{z₀}O`, so `b ∈ T_{z₀}O ∩ ker Dr(z₀) = 0`. -/
theorem normal_injective_of_exists_range_scDeriv_eq_ρ (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) {g : E 0 → F 0} {z : E 1}
    (hzO : E.toBase 1 z ∈ r R '' U)
    (hker : LinearMap.ker (scDeriv U g z : E 0 →ₗ[ℝ] F 0) ≤ rangeS (scDeriv U (r R) z))
    (honto : ∀ k : F 0, ∃ x ∈ rangeS (scDeriv U (r R) z),
      scDeriv U g z x = ρ R (E.toBase 1 z) k) :
    ∀ b : E 0, scDeriv U (r R) z b = 0 →
      ρ R (E.toBase 1 z) (scDeriv U g z b) = scDeriv U g z b → b = 0 := by
  intro b hb hρb
  obtain ⟨a, ha, hab⟩ := honto (scDeriv U g z b)
  rw [hρb] at hab
  have hmem : a - b ∈ LinearMap.ker (scDeriv U g z : E 0 →ₗ[ℝ] F 0) := by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, hab, sub_self]
  have hbT : b ∈ rangeS (scDeriv U (r R) z) := by
    have := (rangeS (scDeriv U (r R) z)).sub_mem ha (hker hmem)
    rwa [sub_sub_cancel] at this
  obtain ⟨w, rfl⟩ := hbT
  change scDeriv U (r R) z (scDeriv U (r R) z w) = 0 at hb
  rw [scDeriv_r_idem_at hU hR hzO] at hb
  exact hb

/-- **Finding 100's equivalence**: at a zero `z₀` of `f̂` in `O` with `Dg(z₀)` agreeing with
`D(f̂ ∘ r)(z₀)` on `T_{z₀}O` (`g = f̂` on `O` near `z₀`), `Dg(z₀)` onto and
`ker Dg(z₀) ⊆ T_{z₀}O`: `Tf̃(z₀)` maps onto `K_{z₀}` iff `(1 − ρ(z₀))Dg(z₀)` is injective on
`ker Dr(z₀)` (condition (3) of Definition 3.4 at `z₀`). -/
theorem exists_range_scDeriv_eq_ρ_iff_normal_injective (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) {fb g : E 0 → F 0} (hfr : IsSc1 U (fb ∘ r R))
    (hg : IsSc1 U g) (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ)) {z : E 1}
    (hzO : E.toBase 1 z ∈ r R '' U) (hfz : fb (E.toBase 1 z) = 0)
    (heq : ∀ᶠ x in 𝓝 (E.toBase 1 z), x ∈ r R '' U → fb x = g x)
    (hsurj : Surjective (scDeriv U g z))
    (hker : LinearMap.ker (scDeriv U g z : E 0 →ₗ[ℝ] F 0) ≤ rangeS (scDeriv U (r R) z)) :
    (∀ k : F 0, ∃ x ∈ rangeS (scDeriv U (r R) z), scDeriv U g z x = ρ R (E.toBase 1 z) k) ↔
      ∀ b : E 0, scDeriv U (r R) z b = 0 →
        ρ R (E.toBase 1 z) (scDeriv U g z b) = scDeriv U g z b → b = 0 :=
  ⟨normal_injective_of_exists_range_scDeriv_eq_ρ hU hR hzO hker,
    exists_range_scDeriv_eq_ρ_of_normal_injective hU hR hfr hg hfK hzO hfz heq hsurj⟩

/-- The fibres `ρ(u)F` and `ρ(u')F` over equal points, as isomorphic Banach spaces (the identity;
`ρCLM` depends on the membership proof only through the point). -/
lemma exists_rangeS_ρCLM_equiv (hR : IsStrongBundleRetraction U R) {u u' : E 0} (hu : u ∈ U)
    (hu' : u' ∈ U) (h : u = u') :
    ∃ e : ↥(rangeS (ρCLM hR hu)) ≃L[ℝ] ↥(rangeS (ρCLM hR hu')), ∀ k, (e k : F 0) = k := by
  subst h
  exact ⟨ContinuousLinearEquiv.refl ℝ _, fun _ => rfl⟩

end Normal

/-! ### The index of the linearization at a zero, in every chart -/

section Bundle

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

open StrongRetr

variable (B) in
/-- **`f'(y)` is surjective, Fredholm, of index `d = dim ker f'(y)`**, chart-intrinsically: in
every strong bundle chart `c` of `P` around `y`, at the level-`1` point `z` over `ϕ(y)`, the
linearization `Lin(z) = D(f̂ ∘ r)(z)|_{T_zO} : T_zO → K_z` (`linAt`, with values in `K_z = ρ(z)F`)
is surjective and Fredholm with `ind Lin(z) = dim ker Lin(z) = d`.  (By
`StrongBundle.linAt_chart_independence` it suffices to know this in one chart.) -/
def StrongBundle.IsSurjLinOfIndex (f : X → Y) (y : X) (d : ℕ) : Prop :=
  ∀ c : StrongBundleChart PX P, B.IsChart c → y ∈ c.φ.source →
    ∀ (z : c.φ.model.E 1) (_ : c.φ.model.E.toBase 1 z = c.φ y)
      (hzU : c.φ.model.E.toBase 1 z ∈ c.U)
      (L : ↥(rangeS (scDeriv c.U (r c.R) z)) →L[ℝ] ↥(rangeS (ρCLM c.isRetraction hzU))),
      (∀ x, (L x : c.F 0) = linAt c.U c.R (c.principal f) z x) →
      Surjective L ∧ L.IsFredholm ∧ fredholmIndex L = d ∧
        finrank ℝ (LinearMap.ker (L : ↥(rangeS (scDeriv c.U (r c.R) z)) →ₗ[ℝ]
          ↥(rangeS (ρCLM c.isRetraction hzU)))) = d

variable (B) in
/-- **`f'(y)` is surjective** (the text's hypothesis of Theorems 3.19 and 3.56): in some strong
bundle chart `c` of `P` around `y`, at a level-`1` point `z` over `ϕ(y)`, the linearization
`Lin(z) : T_zO → K_z` maps onto the fibre `K_z = {k | (ϕ(y), k) ∈ K}`.  (By
`StrongBundle.linAt_chart_independence` it is then onto in every chart.) -/
def StrongBundle.IsLinSurjAt (f : X → Y) (y : X) : Prop :=
  ∃ (c : StrongBundleChart PX P) (_ : B.IsChart c) (_ : y ∈ c.φ.source) (z : c.φ.model.E 1),
    c.φ.model.E.toBase 1 z = c.φ y ∧
      ∀ k, (c.φ y, k) ∈ c.K → ∃ x, linAt c.U c.R (c.principal f) z x = k

/-- **The chart independence of `IsLinSurjAt`** ("`f'(y)` surjective"; also that of Definition
5.15): if `f'(y)` is onto in some strong bundle chart (`IsLinSurjAt`), then at every strong bundle
chart `c'` around the zero `y` and every level-`1` point `z'` over `φ'(y)` the linearization
`Lin'(z')` maps onto the fibre `K'_{φ'(y)}` (`linAt_chart_independence`). -/
theorem StrongBundle.IsLinSurjAt.linAt_surjective (hf : B.IsScSmoothSection f) {y : X}
    (hy0 : IsZeroAt P f y) (h : B.IsLinSurjAt f y) {c' : StrongBundleChart PX P}
    (hc' : B.IsChart c') (hyV' : y ∈ c'.φ.source) {z' : c'.φ.model.E 1}
    (hz' : c'.φ.model.E.toBase 1 z' = c'.φ y) :
    ∀ k, (c'.φ y, k) ∈ c'.K → ∃ x, linAt c'.U c'.R (c'.principal f) z' x = k := by
  obtain ⟨c, hc, hyV, z, hz, hs⟩ := h
  obtain ⟨n, Wq, T, hT⟩ := c.φ.model.isPartialQuadrant
  obtain ⟨n', Wq', T', hT'⟩ := c'.φ.model.isPartialQuadrant
  have hzO : c.φ.model.E.toBase 1 z ∈ r c.R '' c.U := by
    rw [c.r_image, hz]; exact c.φ.mapsTo_model y hyV
  have hzO' : c'.φ.model.E.toBase 1 z' ∈ r c'.R '' c'.U := by
    rw [c'.r_image, hz']; exact c'.φ.mapsTo_model y hyV'
  have hzU : c.φ.model.E.toBase 1 z ∈ c.U := mem_U_of_mem_O c.isRetraction hzO
  have hzU' : c'.φ.model.E.toBase 1 z' ∈ c'.U := mem_U_of_mem_O c'.isRetraction hzO'
  obtain ⟨L, L', hL, hL', hsurj, -, -, -⟩ :=
    StrongBundle.linAt_chart_independence hf hc hc' hyV hyV' hy0 hz hz' hzU hzU' T hT T' hT'
  have hLs : Surjective L := by
    rintro ⟨k, hk⟩
    have hkK : (c.φ y, k) ∈ c.K := by
      have := (mem_rangeS_ρCLM_iff c.isRetraction hzO hzU).1 hk
      rwa [hz] at this
    obtain ⟨x, hx⟩ := hs k hkK
    exact ⟨x, Subtype.ext ((hL x).trans hx)⟩
  intro k hk
  have hk' : k ∈ rangeS (ρCLM c'.isRetraction hzU') := by
    rw [mem_rangeS_ρCLM_iff c'.isRetraction hzO' hzU', hz']
    exact hk
  obtain ⟨x, hx⟩ := (hsurj.1 hLs) ⟨k, hk'⟩
  exact ⟨x, (hL' x).symm.trans (congrArg Subtype.val hx)⟩

/-- **Proposition 3.52 in every chart**: let `c` be the chart of Definition 3.11 at the zero `x₀`
(centred, with filled version `g` of `f̂`, sc⁺-section `s`, `s(0) = g(0)`) and `dc` conjugation
data of `g − s` to a basic germ `h : O(C̃ ⊕ W, 0) → ℝᴺ ⊕ W`, `C̃ ⊆ ℝⁿ`.  Then for every strong
bundle chart `c'` around `x₀` and the level-`1` point `z'` over `ϕ'(x₀)`, the linearization
`Lin'(z') : T_{z'}O' → K'_{z'}` is Fredholm of index `n − N = dim dc.Pn − dim dc.Q`, and it is onto
if `(f, x₀)` is in good position in `c` (`IsGoodPositionAt`).  Proposition 3.52 in `c`
(`proposition_3_52_local_index_wholeChart`: `Tf̃(0)` Fredholm of index `n − N`), `Tf̃(0) = Lin(0)`
(`fillerRestrict_eq_linAt`), and the chart independence (`linAt_chart_independence`). -/
theorem StrongBundle.linAt_index_of_conjugationData_wholeChart (hf : B.IsScSmoothSection f) {x₀ : X}
    (hx₀ : IsZeroAt P f x₀) {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (hxV : x₀ ∈ c.φ.source) (hφ0 : c.φ x₀ = 0) (h0 : (0 : c.φ.model.E 0) ∈ c.U)
    {g : c.φ.model.E 0 → c.F 0} {s : c.φ.model.E 0 → c.F 1}
    (hfill : IsFilledVersion c.relOpen c.isRetraction h0 (c.principal f) g)
    (hs : IsScSmooth (F := c.F.shift) c.U s) (hs0 : c.F.toBase 1 (s 0) = g 0)
    (dc : ConjugationData c.U fun u => g u - c.F.toBase 1 (s u))
    {c' : StrongBundleChart PX P} (hc' : B.IsChart c') (hxV' : x₀ ∈ c'.φ.source)
    {z' : c'.φ.model.E 1} (hz' : c'.φ.model.E.toBase 1 z' = c'.φ x₀)
    (hzU' : c'.φ.model.E.toBase 1 z' ∈ c'.U)
    (L' : ↥(rangeS (scDeriv c'.U (r c'.R) z')) →L[ℝ] ↥(rangeS (ρCLM c'.isRetraction hzU')))
    (hL' : ∀ x, (L' x : c'.F 0) = linAt c'.U c'.R (c'.principal f) z' x) :
    L'.IsFredholm ∧ fredholmIndex L' = finrank ℝ dc.Pn - finrank ℝ dc.Q ∧
      (IsGoodPositionAt c.relOpen c.isRetraction h0 g → Surjective L') := by
  classical
  have hU := c.relOpen
  have h0O : (0 : c.φ.model.E 0) ∈ r c.R '' c.U := by
    rw [c.r_image, ← hφ0]; exact c.φ.mapsTo_model x₀ hxV
  have hfb0 : c.principal f 0 = 0 := by
    have := (c.isZeroAt_iff hf.1 hxV).1 hx₀
    rwa [hφ0] at this
  have hfK : ∀ x ∈ r c.R '' c.U, (x, c.principal f x) ∈ c.R '' (c.U ×ˢ univ) := fun x hx =>
    c.principal_mem_K hf.1 (c.r_image ▸ hx)
  obtain ⟨h1, -, -, hTF, hTind⟩ :=
    proposition_3_52_local_index_wholeChart hU c.isRetraction h0 h0O hfill hfb0 hfK hs hs0 dc
  set F₀ := fillerRestrict (scDeriv c.U (r c.R) 0) (ρCLM c.isRetraction h0) (scDeriv c.U g 0) h1
    with hF₀
  -- the chart independence, with `z = 0` in the centred chart
  obtain ⟨n, Wq, T, hT⟩ := c.φ.model.isPartialQuadrant
  obtain ⟨n', Wq', T', hT'⟩ := c'.φ.model.isPartialQuadrant
  have hz : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) = c.φ x₀ := by rw [map_zero, hφ0]
  have hzU : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) ∈ c.U := by rw [map_zero]; exact h0
  obtain ⟨L, L₁, hL, hL₁, hsurjiff, hFiff, hind, -⟩ := StrongBundle.linAt_chart_independence hf
    hc hc' hxV hxV' hx₀ hz hz' hzU hzU' T hT T' hT'
  have hL₁L' : L₁ = L' := by
    ext x
    rw [hL₁, hL']
  subst hL₁L'
  -- `L = Tf̃(0)` up to the identification of the fibres `ρ(0)F = ρ(ι 0)F`
  obtain ⟨e, he⟩ := exists_rangeS_ρCLM_equiv c.isRetraction h0 hzU (map_zero _).symm
  have hfr : IsSc1 c.U (c.principal f ∘ r c.R) := hf.isSc1_principal_comp_r hc
  have hconj : ∀ x, L ((ContinuousLinearEquiv.refl ℝ _) x) = e (F₀ x) := fun x => by
    apply Subtype.ext
    rw [he, ContinuousLinearEquiv.refl_apply, hL, hF₀,
      hfill.fillerRestrict_eq_linAt hU c.isRetraction h0O hfr h1 x]
  have hzO : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) ∈ r c.R '' c.U := by
    rw [map_zero]; exact h0O
  have : CompleteSpace ↥(rangeS (scDeriv c.U (r c.R) 0)) :=
    (isClosed_range_of_idem _ (scDeriv_r_idem_at c.relOpen c.isRetraction hzO)).completeSpace_coe
  have : CompleteSpace ↥(rangeS (ρCLM c.isRetraction h0)) :=
    (isClosed_range_of_idem _ fun k => ρ_ρ c.isRetraction h0O k).completeSpace_coe
  have : CompleteSpace ↥(rangeS (ρCLM c.isRetraction hzU)) :=
    (isClosed_range_of_idem _ fun k => ρ_ρ c.isRetraction hzO k).completeSpace_coe
  have hLF : L.IsFredholm := (isFredholm_iff_of_conj hconj).1.1 hTF
  have hLind : fredholmIndex L = fredholmIndex F₀ := (isFredholm_iff_of_conj hconj).2 hTF
  refine ⟨hFiff.1 hLF, by rw [hind hLF, hLind, hTind], fun hgp => ?_⟩
  exact hsurjiff.1 ((surjective_iff_of_conj hconj).1 (hgp.surjective_fillerRestrict h1))

/-- **The linearization at a zero in good position is onto of index `d = n − N`, in every
chart**: with the data of Definition 3.53 at `x₀` (`linAt_index_of_conjugationData_wholeChart`), for every
`d : ℕ` with `d = dim dc.Pn − dim dc.Q`, `IsSurjLinOfIndex f x₀ d` (the kernel dimension equals the
index because the operator is onto, `finrank_ker_eq_fredholmIndex_of_surjective`). -/
theorem StrongBundle.isSurjLinOfIndex_of_conjugationData_wholeChart (hf : B.IsScSmoothSection f) {x₀ : X}
    (hx₀ : IsZeroAt P f x₀) {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (hxV : x₀ ∈ c.φ.source) (hφ0 : c.φ x₀ = 0) (h0 : (0 : c.φ.model.E 0) ∈ c.U)
    {g : c.φ.model.E 0 → c.F 0} {s : c.φ.model.E 0 → c.F 1}
    (hfill : IsFilledVersion c.relOpen c.isRetraction h0 (c.principal f) g)
    (hs : IsScSmooth (F := c.F.shift) c.U s) (hs0 : c.F.toBase 1 (s 0) = g 0)
    (hgp : IsGoodPositionAt c.relOpen c.isRetraction h0 g)
    (dc : ConjugationData c.U fun u => g u - c.F.toBase 1 (s u)) {d : ℕ}
    (hd : (d : ℤ) = finrank ℝ dc.Pn - finrank ℝ dc.Q) : B.IsSurjLinOfIndex f x₀ d := by
  intro c' hc' hxV' z' hz' hzU' L' hL'
  obtain ⟨hF, hind, hsurj⟩ := StrongBundle.linAt_index_of_conjugationData_wholeChart hf hx₀ hc hxV hφ0 h0
    hfill hs hs0 dc hc' hxV' hz' hzU' L' hL'
  have hs' := hsurj hgp
  refine ⟨hs', hF, by rw [hind, hd], ?_⟩
  have h := finrank_ker_eq_fredholmIndex_of_surjective hF hs'
  rw [hind, ← hd] at h
  exact_mod_cast h

/-- **At a zero in good position, `f'(x₀)` is onto with `ind f'(x₀) = dim ker f'(x₀) = d` in every
chart**, and `d = n − N` for every conjugation to a basic germ in the chart of Definition 3.53. -/
theorem StrongBundle.IsGoodPositionGermWholeChart.exists_isSurjLinOfIndex (hf : B.IsScSmoothSection f)
    {x₀ : X} (hg : B.IsGoodPositionGermWholeChart f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ d : ℕ, B.IsSurjLinOfIndex f x₀ d ∧
      ∃ (c : StrongBundleChart PX P) (_ : B.IsChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
        (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0)
        (s : c.φ.model.E 0 → c.F 1)
        (_ : IsFilledVersion c.relOpen c.isRetraction h0 (c.principal f) g)
        (_ : IsScSmooth (F := c.F.shift) c.U s) (_ : c.F.toBase 1 (s 0) = g 0)
        (_ : IsGoodPositionAt c.relOpen c.isRetraction h0 g),
        Nonempty (ConjugationData c.U fun u => g u - c.F.toBase 1 (s u)) ∧
        ∀ dc : ConjugationData c.U (fun u => g u - c.F.toBase 1 (s u)),
          (d : ℤ) = finrank ℝ dc.Pn - finrank ℝ dc.Q := by
  obtain ⟨-, c, hc, hxV, hφ0, h0, g, s, hfill, hs, hs0, hconj, hgp⟩ := hg
  obtain ⟨dc₀⟩ := isConjugateToBasicGerm_iff_nonempty.1 hconj
  -- the index of `Lin(0)` in the centred chart
  have hz : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) = c.φ x₀ := by rw [map_zero, hφ0]
  have hzU : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) ∈ c.U := by rw [map_zero]; exact h0
  have hzO : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) ∈ r c.R '' c.U := by
    rw [map_zero, c.r_image, ← hφ0]; exact c.φ.mapsTo_model x₀ hxV
  have hmem : ∀ x : ↥(rangeS (scDeriv c.U (r c.R) 0)),
      linAt c.U c.R (c.principal f) 0 x ∈ rangeS (ρCLM c.isRetraction hzU) := fun x =>
    ⟨_, rho_scDeriv_comp_r c.relOpen c.isRetraction (hf.isSc1_principal_comp_r hc)
      (fun x hx => c.principal_mem_K hf.1 (c.r_image ▸ hx)) hzO
      (by rw [hz]; exact (c.isZeroAt_iff hf.1 hxV).1 hx₀) x⟩
  set L := (linAt c.U c.R (c.principal f) 0).codRestrict _ hmem with hLdef
  obtain ⟨hF, hind, hsurj⟩ := StrongBundle.linAt_index_of_conjugationData_wholeChart hf hx₀ hc hxV hφ0 h0
    hfill hs hs0 dc₀ hc hxV hz hzU L fun _ => rfl
  have hk := finrank_ker_eq_fredholmIndex_of_surjective hF (hsurj hgp)
  refine ⟨finrank ℝ (LinearMap.ker (L : ↥(rangeS (scDeriv c.U (r c.R) 0)) →ₗ[ℝ]
    ↥(rangeS (ρCLM c.isRetraction hzU)))), ?_, c, hc, hxV, hφ0, h0, g, s, hfill, hs, hs0, hgp,
    ⟨dc₀⟩, fun dc => ?_⟩
  · exact StrongBundle.isSurjLinOfIndex_of_conjugationData_wholeChart hf hx₀ hc hxV hφ0 h0 hfill hs hs0 hgp
      dc₀ (by rw [hk, hind])
  · rw [hk, (StrongBundle.linAt_index_of_conjugationData_wholeChart hf hx₀ hc hxV hφ0 h0 hfill hs hs0 dc hc
      hxV hz hzU L fun _ => rfl).2.1]

/-- **Definition 3.53 is surjectivity of `f'(y)` plus the kernel condition**: at a zero in good
position, `f'(y)` is onto in the chart of Definition 3.53 (`IsLinSurjAt`; `Tf̃(0) = Lin(0)`). -/
theorem StrongBundle.IsGoodPositionGermWholeChart.isLinSurjAt (hf : B.IsScSmoothSection f) {y : X}
    (hg : B.IsGoodPositionGermWholeChart f y) : B.IsLinSurjAt f y := by
  obtain ⟨-, c, hc, hyV, hφ0, h0, g, s, hfill, hs, hs0, hconj, hgp⟩ := hg
  have h0O : (0 : c.φ.model.E 0) ∈ r c.R '' c.U := by
    rw [c.r_image, ← hφ0]; exact c.φ.mapsTo_model y hyV
  have hz : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) = c.φ y := by rw [map_zero, hφ0]
  refine ⟨c, hc, hyV, 0, hz, fun k hk => ?_⟩
  rw [hφ0] at hk
  obtain ⟨x, hx, hxk⟩ := hgp.surj k ((mem_rangeS_ρCLM_iff c.isRetraction h0O h0).2 hk)
  refine ⟨⟨x, hx⟩, ?_⟩
  rw [linAt_eq_scDeriv c.relOpen c.isRetraction (hf.isSc1_principal_comp_r hc)
    hfill.isScSmooth.isSc1 (by rw [map_zero]; exact h0O)
    (by rw [map_zero]; exact hfill.filler.eq_on)]
  exact hxk

/-- **Good position is surjectivity when `d_X(y) = 0`** (the text before Theorem 3.56: "if
`∂X = ∅` the condition of good position is an empty condition").  Let `(f, y)` be an
sc-Fredholm germ at a zero `y` with `d_X(y) = 0`, and let the linearization `Lin(z)` in a strong
bundle chart `c` with tame base retraction, at the level-`1` point `z` over `ϕ(y)`, map onto
`K_z`.  Then `(f, y)` is in good position: in the tame chart `d_C(ϕ(y)) = d_X(y) = 0`
(`degIndex_eq_chartDegIndex_of_isTameRetract`), so no coordinate of the partial quadrant vanishes
at `ϕ(y)`, the partial quadrant `C_{ϕ(y)}` is the whole space, and the kernel condition holds for
any subspace (`isInGoodPositionIn_of_subset`); then `isGoodPositionGerm_of_linAt_surj_wholeChart`. -/
theorem StrongBundle.isGoodPositionGerm_of_linAt_surj_of_degIndex_eq_zero_wholeChart
    (hf : B.IsScSmoothSection f) {y : X} (hy : B.IsScFredholmGermWholeChart f y) (hy0 : IsZeroAt P f y)
    (hd : PX.degIndex y = 0) {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (hyV : y ∈ c.φ.source) (htame : (c.isRetraction.baseRetraction c.relOpen).IsTame)
    {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z = c.φ y)
    (hsurj : ∀ k, (c.φ y, k) ∈ c.K → ∃ x, linAt c.U c.R (c.principal f) z x = k) :
    B.IsGoodPositionGermWholeChart f y := by
  obtain ⟨n, Wq, T, hT⟩ := c.φ.model.isPartialQuadrant
  have htameO : IsTameRetract c.φ.model.E c.φ.model.C c.φ.model.O :=
    ⟨c.isRetraction.baseRetraction c.relOpen, c.base_retract, htame⟩
  -- `d_C(ϕ(y)) = d_X(y) = 0` in the tame chart: no coordinate vanishes at `ϕ(y)`
  have hdeg : degIndexWith T (c.φ y) = 0 := by
    have h1 := PX.degIndex_eq_chartDegIndex_of_isTameRetract c.isChart htameO hyV
    rw [hd, MPolyfold.chartDegIndex, degIndex_eq T hT (c.φ.apply_mem_C hyV)] at h1
    exact h1.symm
  have hcoord : ∀ i, (T 0 (c.φ y)).1 i ≠ 0 := by
    simp only [degIndexWith, quadrantDeg, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
      Finset.mem_univ, true_implies] at hdeg
    exact hdeg
  have huniv : partialQuadrantAtWith T (c.φ y) = univ :=
    eq_univ_of_forall fun v i hi => absurd hi (hcoord i)
  refine StrongBundle.isGoodPositionGerm_of_linAt_surj_wholeChart hf hy hy0 hc hyV hz T hT hsurj ?_
  rw [huniv]
  exact isInGoodPositionIn_of_subset (Submodule.map_subtype_le _ _) (subset_univ _)

/-- **Good position from "`f'(y)` surjective" when `d_X(y) = 0`**, for an sc-Fredholm section with
tame germ data (`IsScFredholmSectionTameWholeChart`, Definition 3.51; `IsLinSurjAt`, the text's hypothesis of
Theorems 3.19 and 3.56): the surjectivity holds in the tame chart `c` of the germ data at `y`
(`IsLinSurjAt.linAt_surjective`, chart independence), where `d_C(ϕ(y)) = d_X(y) = 0`
(`isGoodPositionGerm_of_linAt_surj_of_degIndex_eq_zero_wholeChart`); the good position is then read in that
tame chart (`IsGoodPositionGermWholeChart.toTame`). -/
theorem StrongBundle.isGoodPositionGerm_of_isLinSurjAt_wholeChart (hf : B.IsScFredholmSectionTameWholeChart f) {y : X}
    (hy0 : IsZeroAt P f y) (hd : PX.degIndex y = 0)
    (hsurj : B.IsLinSurjAt f y) : B.IsGoodPositionGermTameWholeChart f y := by
  have hys := hf.mem_smoothSet_of_isZeroAt hy0
  obtain ⟨-, c, hct, hyV, hφ0, -⟩ := hf.germTame y hys
  have hz : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) = c.φ y := by rw [map_zero, hφ0]
  exact (StrongBundle.isGoodPositionGerm_of_linAt_surj_of_degIndex_eq_zero_wholeChart hf.isScSmooth
    (hf.germ y hys) hy0 hd hct.1 hyV hct.2 hz
    (hsurj.linAt_surjective hf.isScSmooth hy0 hct.1 hyV hz)).toTame hf.isScSmooth
    (hf.germTame y hys) hy0

/-- **"Good position = surjectivity" when `d_X(y) = 0`**: for an sc-Fredholm section with tame
germ data (`IsScFredholmSectionTameWholeChart`) and a zero `y` with `d_X(y) = 0`, `(f, y)` is in good position
in a tame chart iff `f'(y)` is surjective. -/
theorem StrongBundle.isGoodPositionGerm_iff_isLinSurjAt_wholeChart (hf : B.IsScFredholmSectionTameWholeChart f) {y : X}
    (hy0 : IsZeroAt P f y) (hd : PX.degIndex y = 0) :
    B.IsGoodPositionGermTameWholeChart f y ↔ B.IsLinSurjAt f y :=
  ⟨fun hg => hg.isGoodPositionGerm.isLinSurjAt hf.isScSmooth,
    StrongBundle.isGoodPositionGerm_of_isLinSurjAt_wholeChart hf hy0 hd⟩

/-- **Theorem 3.19, the first clause, with the index** (cf. `theorem_3_19_linearization_wholeChart`, whose
index clause is that of `proposition_3_52_wholeChart`, "`n − N` for some natural numbers"): for an
sc-Fredholm section and a zero `x₀` in good position, in the chart of Definition 3.53, `Dg(0)` and
`f'(x₀) = Tf̃(0) = Dg(0)|_{T₀O} : T₀O → K₀` are Fredholm, `Tf̃(0)` is onto, and for **every**
conjugation `d` of `g − s` to a basic germ (`h : O(C̃ ⊕ W, 0) → ℝᴺ ⊕ W`, `C̃ ⊆ ℝⁿ`):
`ind Dg(0) = ind Tf̃(0) = dim ker Tf̃(0) = n − N` (`proposition_3_52_local_index_wholeChart`).  The index in
every other chart is `IsGoodPositionGermWholeChart.exists_isSurjLinOfIndex`. -/
theorem theorem_3_19_linearization_index_wholeChart (hf : B.IsScFredholmSectionWholeChart f) {x₀ : X}
    (hx₀ : IsZeroAt P f x₀) (hg : B.IsGoodPositionGermWholeChart f x₀) :
    ∃ (c : StrongBundleChart PX P) (_ : B.IsChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
      (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0) (s : c.φ.model.E 0 → c.F 1)
      (_ : IsFilledVersion c.relOpen c.isRetraction h0 (c.principal f) g)
      (_ : IsScSmooth (F := c.F.shift) c.U s) (_ : c.F.toBase 1 (s 0) = g 0)
      (_ : Nonempty (ConjugationData c.U fun u => g u - c.F.toBase 1 (s u)))
      (h1 : ∀ x, ρCLM c.isRetraction h0 (scDeriv c.U g 0 (scDeriv c.U (r c.R) 0 x)) =
        scDeriv c.U g 0 (scDeriv c.U (r c.R) 0 x)),
      (scDeriv c.U g 0).IsFredholm ∧
      (fillerRestrict (scDeriv c.U (r c.R) 0) (ρCLM c.isRetraction h0)
        (scDeriv c.U g 0) h1).IsFredholm ∧
      Surjective (fillerRestrict (scDeriv c.U (r c.R) 0) (ρCLM c.isRetraction h0)
        (scDeriv c.U g 0) h1) ∧
      ∀ d : ConjugationData c.U (fun u => g u - c.F.toBase 1 (s u)),
        fredholmIndex (scDeriv c.U g 0) = finrank ℝ d.Pn - finrank ℝ d.Q ∧
        fredholmIndex (fillerRestrict (scDeriv c.U (r c.R) 0) (ρCLM c.isRetraction h0)
          (scDeriv c.U g 0) h1) = finrank ℝ d.Pn - finrank ℝ d.Q ∧
        (finrank ℝ (LinearMap.ker (fillerRestrict (scDeriv c.U (r c.R) 0)
          (ρCLM c.isRetraction h0) (scDeriv c.U g 0) h1 : ↥(rangeS (scDeriv c.U (r c.R) 0)) →ₗ[ℝ]
            ↥(rangeS (ρCLM c.isRetraction h0)))) : ℤ) = finrank ℝ d.Pn - finrank ℝ d.Q := by
  obtain ⟨-, c, hc, hxV, hφ0, h0U, g, s, hfill, hs, hs0, hconj, hgp⟩ := hg
  have hfs : IsSection P f := hf.isScSmooth.1
  have h0O : (0 : c.φ.model.E 0) ∈ r c.R '' c.U := by
    rw [c.r_image, ← hφ0]; exact c.φ.mapsTo_model x₀ hxV
  have hfb0 : c.principal f 0 = 0 := by
    have := (c.isZeroAt_iff hfs hxV).1 hx₀
    rwa [hφ0] at this
  have hfK : ∀ x ∈ r c.R '' c.U, (x, c.principal f x) ∈ c.R '' (c.U ×ˢ univ) := fun x hx =>
    c.principal_mem_K hfs (c.r_image ▸ hx)
  obtain ⟨d₀⟩ := isConjugateToBasicGerm_iff_nonempty.1 hconj
  obtain ⟨h1, hDgF, -, hTF, -⟩ :=
    proposition_3_52_local_index_wholeChart c.relOpen c.isRetraction h0U h0O hfill hfb0 hfK hs hs0 d₀
  have hTs := hgp.surjective_fillerRestrict h1
  refine ⟨c, hc, hxV, hφ0, h0U, g, s, hfill, hs, hs0, ⟨d₀⟩, h1, hDgF, hTF, hTs, fun d => ?_⟩
  obtain ⟨h1', -, hDgind, -, hTind⟩ :=
    proposition_3_52_local_index_wholeChart c.relOpen c.isRetraction h0U h0O hfill hfb0 hfK hs hs0 d
  exact ⟨hDgind, hTind, by rw [finrank_ker_eq_fredholmIndex_of_surjective hTF hTs, hTind]⟩

end Bundle

/-! ### Dimension = index -/

section DimIndex

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

open StrongRetr

/-- **Theorem 3.54 (2) at the centre, with "dimension = Fredholm index"** (the text: "abbreviating
`d = dim ker f'(x)`, the solution set possesses the `d`-dimensional tangent germ property"; Theorem
3.19: "whose dimension agrees with the Fredholm index").  The data of Definition 3.25 (2) for
`S = {y ∈ Vx | f(y) = 0}` at `x₀` of `theorem_3_54_tangentGermChart_proj_wholeChart` have dimension `d` with
`IsSurjLinOfIndex f x₀ d`: in every strong bundle chart around `x₀`, `f'(x₀)` is onto, Fredholm,
and `ind f'(x₀) = dim ker f'(x₀) = d`.  (`theorem_3_54_tangentGermChart_proj_conj_wholeChart`: `d = n − N`
for the conjugation in the chart from which `ψ ∘ ϕ` is built;
`isSurjLinOfIndex_of_conjugationData_wholeChart`.) -/
theorem theorem_3_54_tangentGermChart_index_wholeChart (hf : B.IsScSmoothSection f) {x₀ : X}
    (hg : B.IsGoodPositionGermTameWholeChart f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ (Vx : Set X) (d : ℕ), IsOpen Vx ∧ x₀ ∈ Vx ∧
      (∃ D : PX.TangentGermChart {y ∈ Vx | IsZeroAt P f y} x₀ d,
        ∀ z ∈ D.φ.model.O, (D.π z : D.φ.model.E 0) ∈ D.φ.model.C) ∧
      B.IsSurjLinOfIndex f x₀ d := by
  obtain ⟨Vx, d, hVxo, hx₀Vx, hD, c, hc, hxV, hφ0, h0, g, s, hfill, hs, hs0, hgp, dc, hd⟩ :=
    theorem_3_54_tangentGermChart_proj_conj_wholeChart hf.1 hg hx₀
  exact ⟨Vx, d, hVxo, hx₀Vx, hD,
    StrongBundle.isSurjLinOfIndex_of_conjugationData_wholeChart hf hx₀ hc.1 hxV hφ0 h0 hfill hs hs0 hgp dc hd⟩

/-- **The data of Definition 3.25 (2) for the global solution set at a zero in good position,
with the dimension the Fredholm index** (`theorem_3_54_tangentGermChart_solutionSet_wholeChart` with
`IsSurjLinOfIndex f x₀ d`). -/
theorem theorem_3_54_tangentGermChart_solutionSet_index_wholeChart (hf : B.IsScSmoothSection f) {x₀ : X}
    (hg : B.IsGoodPositionGermTameWholeChart f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ d : ℕ, (∃ D : PX.TangentGermChart (solutionSet P f) x₀ d,
      ∀ z ∈ D.φ.model.O, (D.π z : D.φ.model.E 0) ∈ D.φ.model.C) ∧ B.IsSurjLinOfIndex f x₀ d := by
  obtain ⟨Vx, d, hVxo, hx₀Vx, ⟨D, hπ⟩, hind⟩ :=
    theorem_3_54_tangentGermChart_index_wholeChart hf hg hx₀
  have hs : D.φ.source ∩ Vx ⊆ D.φ.source := inter_subset_left
  have hso : IsOpen (D.φ.source ∩ Vx) := D.φ.isOpen_source.inter hVxo
  have hxs : x₀ ∈ D.φ.source ∩ Vx := ⟨D.mem_source, hx₀Vx⟩
  have himage : D.φ '' (solutionSet P f ∩ (D.φ.source ∩ Vx)) =
      (fun v : D.N => (v : D.φ.model.E 0) + D.δ v) '' D.V := by
    rw [← D.image_eq]
    congr 1
    ext y
    constructor
    · rintro ⟨hyS, hysrc, hyVx⟩; exact ⟨⟨hyVx, hyS⟩, hysrc⟩
    · rintro ⟨⟨hyVx, hyS⟩, hysrc⟩; exact ⟨hyS, hysrc, hyVx⟩
  refine ⟨d, ⟨D.shrink (solutionSet P f) hs hso hxs D.V_relOpen D.zero_mem_V subset_rfl himage,
    fun z hz => ?_⟩, hind⟩
  rw [D.shrink_π]
  exact hπ z (D.φ.image_subset_model hs hz)

/-- **Theorem 3.54 (2) with "dimension = Fredholm index"**: `theorem_3_54_two_wholeChart` with in addition
`IsSurjLinOfIndex f x₀ d` — the dimension `d` of the regular data of Definition 3.25 (2) of the
solution set at `x₀` is `dim ker f'(x₀) = ind f'(x₀)` in every chart. -/
theorem theorem_3_54_two_index_wholeChart (hf : B.IsScSmoothSection f) {x₀ : X}
    (hg : B.IsGoodPositionGermTameWholeChart f x₀) (hx₀ : IsZeroAt P f x₀)
    {Vx₀ : Set X} (hVx₀ : IsOpen Vx₀) (hx₀V : x₀ ∈ Vx₀)
    (hall : ∀ y ∈ Vx₀, IsZeroAt P f y → B.IsGoodPositionGermTameWholeChart f y) :
    ∃ d : ℕ, ∃ D : PX.TangentGermChart (solutionSet P f) x₀ d, D.IsRegular ∧ D.φ.source ⊆ Vx₀ ∧
      (∀ y ∈ solutionSet P f ∩ D.φ.source,
        ∀ (n' : ℕ) (_ : PX.TangentGermChart (solutionSet P f) y n'), n' = d) ∧
      B.IsSurjLinOfIndex f x₀ d := by
  obtain ⟨d, ⟨D, hπ⟩, hind⟩ := theorem_3_54_tangentGermChart_solutionSet_index_wholeChart hf hg hx₀
  have hM : ∀ y ∈ solutionSet P f ∩ Vx₀,
      ∃ n' : ℕ, Nonempty (PX.TangentGermChart (solutionSet P f) y n') := fun y hy => by
    obtain ⟨d', D', -⟩ :=
      theorem_3_54_tangentGermChart_solutionSet_wholeChart hf.1 (hall y hy.2 hy.1) hy.1
    exact ⟨d', ⟨D'⟩⟩
  obtain ⟨D', hreg, hsub, hdim⟩ := D.exists_isRegular_of_locally hπ hVx₀ hx₀V hM
  exact ⟨d, D', hreg, hsub, hdim, hind⟩

/-- At a zero `y` in good position at which every datum of Definition 3.25 (2) of the solution
set has dimension `d`, `f'(y)` is onto of index `d`
(`theorem_3_54_tangentGermChart_solutionSet_index_wholeChart` at `y` gives a datum whose dimension is the
index). -/
theorem isSurjLinOfIndex_of_forall_dim_wholeChart (hf : B.IsScSmoothSection f)
    {y : X} (hgy : B.IsGoodPositionGermTameWholeChart f y) (hy0 : IsZeroAt P f y) {d : ℕ}
    (hdim : ∀ (n' : ℕ) (_ : PX.TangentGermChart (solutionSet P f) y n'), n' = d) :
    B.IsSurjLinOfIndex f y d := by
  obtain ⟨dy, ⟨Dy, -⟩, hindy⟩ := theorem_3_54_tangentGermChart_solutionSet_index_wholeChart hf hgy hy0
  rw [← hdim dy Dy]
  exact hindy

/-- **The Fredholm index is locally constant along the solution set** (Proposition 6.2 of the text
along `S`; Findings 171, 188).  For an sc-Fredholm section with tame germ data
(`IsScFredholmSectionTameWholeChart`), `f(x₀) = 0` and `(f, x₀)` in good position in a tame chart, there
are an open `Vx ∋ x₀` and `d` such
that at every zero `y ∈ Vx`, `f'(y)` is onto with `ind f'(y) = dim ker f'(y) = d`
(`IsSurjLinOfIndex`, in every chart), in particular `ind f'(y) = ind f'(x₀)`.  Proof: Theorem 3.54
(1) (`theorem_3_54_one'_wholeChart`) puts the zeros near `x₀` in good position; the dimension of the solution
set is locally constant (`theorem_3_54_two_wholeChart`) and equals the index at each of them
(`theorem_3_54_tangentGermChart_solutionSet_index_wholeChart`). -/
theorem theorem_3_54_index_locally_constant_wholeChart (hf : B.IsScFredholmSectionTameWholeChart f) {x₀ : X}
    (hg : B.IsGoodPositionGermTameWholeChart f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ (Vx : Set X) (d : ℕ), IsOpen Vx ∧ x₀ ∈ Vx ∧
      ∀ y ∈ Vx, IsZeroAt P f y → B.IsSurjLinOfIndex f y d := by
  obtain ⟨Vx₁, hVx₁o, hx₀Vx₁, hall⟩ := theorem_3_54_one'_wholeChart hf hg hx₀
  obtain ⟨d, D, -, hsub, hdim, -⟩ :=
    theorem_3_54_two_index_wholeChart hf.isScSmooth hg hx₀ hVx₁o hx₀Vx₁ hall
  exact ⟨D.φ.source, d, D.φ.isOpen_source, D.mem_source, fun y hy hy0 =>
    isSurjLinOfIndex_of_forall_dim_wholeChart hf.isScSmooth (hall y (hsub hy) hy0) hy0
      (hdim y ⟨hy0, hy⟩)⟩

/-- **Theorem 3.54 (1) and (2) with the text's hypotheses and the index**: for an sc-Fredholm
section with tame germ data (`IsScFredholmSectionTameWholeChart`), `f(x₀) = 0` and `(f, x₀)` in good
position in a tame chart, there are an open `Vx ∋ x₀` and `d` with: (1) at every zero `y ∈ Vx`,
`(f, y)` is in good position in a tame chart and `f'(y)` is onto with `ind f'(y) = dim ker f'(y) = d` (the index is locally
constant); (2) the solution set has at `x₀` regular data of Definition 3.25 (2) of dimension `d`
on the chart domain `Vx`, every datum at a point of `Vx` having dimension `d`.  (Cf.
`theorem_3_54'_wholeChart`.) -/
theorem theorem_3_54_index_wholeChart (hf : B.IsScFredholmSectionTameWholeChart f) {x₀ : X}
    (hg : B.IsGoodPositionGermTameWholeChart f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ (Vx : Set X) (d : ℕ), IsOpen Vx ∧ x₀ ∈ Vx ∧
      (∀ y ∈ Vx, IsZeroAt P f y → B.IsGoodPositionGermTameWholeChart f y ∧ B.IsSurjLinOfIndex f y d) ∧
      ∃ D : PX.TangentGermChart (solutionSet P f) x₀ d, D.IsRegular ∧ D.φ.source = Vx ∧
        ∀ y ∈ solutionSet P f ∩ D.φ.source,
          ∀ (n' : ℕ) (_ : PX.TangentGermChart (solutionSet P f) y n'), n' = d := by
  obtain ⟨Vx₁, hVx₁o, hx₀Vx₁, hall⟩ := theorem_3_54_one'_wholeChart hf hg hx₀
  obtain ⟨d, D, hreg, hsub, hdim, -⟩ :=
    theorem_3_54_two_index_wholeChart hf.isScSmooth hg hx₀ hVx₁o hx₀Vx₁ hall
  exact ⟨D.φ.source, d, D.φ.isOpen_source, D.mem_source, fun y hy hy0 =>
    ⟨hall y (hsub hy) hy0, isSurjLinOfIndex_of_forall_dim_wholeChart hf.isScSmooth
      (hall y (hsub hy) hy0) hy0 (hdim y ⟨hy0, hy⟩)⟩, D, hreg, rfl, hdim⟩

/-- **Theorem 3.23 with the text's hypotheses, the dimension equal to the Fredholm index**: an
sc-Fredholm section with tame germ data (`IsScFredholmSectionTameWholeChart`), `f(x) = 0`, `(f, x)` in good
position in a tame chart.  Then there are an open `U ∋ x` and `d` such that every zero `y ∈ U` is
in good position in a tame chart with `f'(y)` onto and `ind f'(y) = dim ker f'(y) = d`, `S(f, U)` consists of smooth
points, is a sub-M-polyfold of `X`, and its induced structure is tame and that of a
`d`-dimensional manifold with boundary with corners.  (Cf. `theorem_3_23'_wholeChart`; the proof is that of
`theorem_3_23_of_nearby_wholeChart` with `theorem_3_54_two_index_wholeChart`.) -/
theorem theorem_3_23_index_wholeChart (hf : B.IsScFredholmSectionTameWholeChart f) {x : X} (hx : IsZeroAt P f x)
    (hg : B.IsGoodPositionGermTameWholeChart f x) :
    ∃ (U : Set X) (d : ℕ), IsOpen U ∧ x ∈ U ∧
      (∀ y ∈ U, IsZeroAt P f y → B.IsGoodPositionGermTameWholeChart f y ∧ B.IsSurjLinOfIndex f y d) ∧
      (∀ y ∈ U, IsZeroAt P f y → y ∈ PX.smoothSet) ∧
      ∃ hsub : PX.IsSubMPolyfold {y ∈ U | IsZeroAt P f y},
        haveI := PX.paracompactSpace_subtype {y ∈ U | IsZeroAt P f y}
        (MPolyfold.subPolyfold hsub).IsTame ∧
          (MPolyfold.subPolyfold hsub).IsManifoldWithCorners d := by
  obtain ⟨Vx, hVxo, hxVx, hall⟩ := theorem_3_54_one'_wholeChart hf hg hx
  obtain ⟨d, D, -, hsub, hdim, -⟩ :=
    theorem_3_54_two_index_wholeChart hf.isScSmooth hg hx hVxo hxVx hall
  set U := D.φ.source with hU
  set S' := {y ∈ U | IsZeroAt P f y} with hS'
  -- every point of `S(f, U)` has regular data of Definition 3.25 (2) for `S(f, U)` of dimension `d`
  have hS'reg : ∀ y ∈ S', ∃ d' : PX.TangentGermChart S' y d, d'.IsRegular := by
    intro y hy
    obtain ⟨dy, Dy, hregy, hsuby, -⟩ := theorem_3_54_two_wholeChart hf.isScSmooth.1 (hall y (hsub hy.1) hy.2)
      hy.2 (D.φ.isOpen_source.inter hVxo) ⟨hy.1, hsub hy.1⟩ fun z hz hz0 => hall z hz.2 hz0
    have hdy : dy = d := hdim y ⟨hy.2, hy.1⟩ dy Dy
    subst hdy
    have himage : Dy.φ '' (S' ∩ Dy.φ.source) =
        (fun v : Dy.N => (v : Dy.φ.model.E 0) + Dy.δ v) '' Dy.V := by
      rw [← Dy.image_eq]
      congr 1
      ext z
      constructor
      · rintro ⟨⟨-, hz0⟩, hzsrc⟩; exact ⟨hz0, hzsrc⟩
      · rintro ⟨hz0, hzsrc⟩; exact ⟨⟨(hsuby hzsrc).1, hz0⟩, hzsrc⟩
    exact ⟨Dy.shrink S' subset_rfl Dy.φ.isOpen_source Dy.mem_source Dy.V_relOpen Dy.zero_mem_V
      subset_rfl himage, Dy.shrink_isRegular S' subset_rfl Dy.φ.isOpen_source Dy.mem_source
      Dy.V_relOpen Dy.zero_mem_V subset_rfl himage hregy.isScSmooth hregy.π_mem⟩
  have hne : S'.Nonempty := ⟨x, D.mem_source, hx⟩
  obtain ⟨hsubM, htameS, hman, -⟩ := theorem_3_27 PX hne hS'reg
  exact ⟨U, d, D.φ.isOpen_source, D.mem_source, fun y hy hy0 =>
    ⟨hall y (hsub hy) hy0, isSurjLinOfIndex_of_forall_dim_wholeChart hf.isScSmooth
      (hall y (hsub hy) hy0) hy0 (hdim y ⟨hy0, hy⟩)⟩,
    fun y _ hy => hf.mem_smoothSet_of_isZeroAt hy, hsubM, htameS, hman⟩

/-- **Theorem 3.19 (implicit function theorem, interior case) with the text's hypotheses, the
index and tameness**: for an M-polyfold without boundary, an sc-Fredholm section with tame germ
data (`IsScFredholmSectionTameWholeChart`), `f(x₀) = 0` and `(f, x₀)` in good position in a tame chart, there
are an open `U ∋ x₀` and `d` such that at every zero `y ∈ U`, `(f, y)` is in good position in a
tame chart and `f'(y)` is onto
with `ind f'(y) = dim ker f'(y) = d` (in every chart); `S(f, U)` consists of smooth points and is
a sub-M-polyfold whose induced structure is tame and that of a `d`-dimensional manifold without
boundary — "whose dimension agrees with the Fredholm index of `f'(x₀)`".  "`ker f'(y) = T_yS`" is
`theorem_3_54_ker_eq_tangent_wholeChart` (in a chart); the text's hypothesis "`f'(x₀)` surjective" is
`theorem_3_19_of_surjective_wholeChart`.  (Cf. `theorem_3_19'_wholeChart`.) -/
theorem theorem_3_19_index_wholeChart (hX : PX.IsWithoutBoundary) (hf : B.IsScFredholmSectionTameWholeChart f) {x₀ : X}
    (hx₀ : IsZeroAt P f x₀) (hg : B.IsGoodPositionGermTameWholeChart f x₀) :
    ∃ (U : Set X) (d : ℕ), IsOpen U ∧ x₀ ∈ U ∧
      (∀ y ∈ U, IsZeroAt P f y → B.IsGoodPositionGermTameWholeChart f y ∧ B.IsSurjLinOfIndex f y d) ∧
      (∀ y ∈ U, IsZeroAt P f y → y ∈ PX.smoothSet) ∧
      ∃ hsub : PX.IsSubMPolyfold {y ∈ U | IsZeroAt P f y},
        haveI := PX.paracompactSpace_subtype {y ∈ U | IsZeroAt P f y}
        (MPolyfold.subPolyfold hsub).IsTame ∧
          (MPolyfold.subPolyfold hsub).IsManifoldWithCorners d ∧
          (MPolyfold.subPolyfold hsub).IsWithoutBoundary := by
  obtain ⟨U, d, hUo, hxU, hgood, hsm, hsub, h1, h2⟩ := theorem_3_23_index_wholeChart hf hx₀ hg
  have := PX.paracompactSpace_subtype {y ∈ U | IsZeroAt P f y}
  refine ⟨U, d, hUo, hxU, hgood, hsm, hsub, h1, h2, fun y => ?_⟩
  have := lemma_2_26 hsub y
  rw [hX y.1] at this
  exact Nat.le_zero.1 this

/-- **Theorem 3.19 with the text's hypothesis "`f'(x₀)` surjective"** (`IsLinSurjAt`): for an
M-polyfold without boundary good position is surjectivity
(`isGoodPositionGerm_of_isLinSurjAt_wholeChart`), and `theorem_3_19_index_wholeChart` applies. -/
theorem theorem_3_19_of_surjective_wholeChart (hX : PX.IsWithoutBoundary) (hf : B.IsScFredholmSectionTameWholeChart f)
    {x₀ : X} (hx₀ : IsZeroAt P f x₀) (hsurj : B.IsLinSurjAt f x₀) :
    ∃ (U : Set X) (d : ℕ), IsOpen U ∧ x₀ ∈ U ∧
      (∀ y ∈ U, IsZeroAt P f y → B.IsGoodPositionGermTameWholeChart f y ∧ B.IsSurjLinOfIndex f y d) ∧
      (∀ y ∈ U, IsZeroAt P f y → y ∈ PX.smoothSet) ∧
      ∃ hsub : PX.IsSubMPolyfold {y ∈ U | IsZeroAt P f y},
        haveI := PX.paracompactSpace_subtype {y ∈ U | IsZeroAt P f y}
        (MPolyfold.subPolyfold hsub).IsTame ∧
          (MPolyfold.subPolyfold hsub).IsManifoldWithCorners d ∧
          (MPolyfold.subPolyfold hsub).IsWithoutBoundary :=
  theorem_3_19_index_wholeChart hX hf hx₀
    (StrongBundle.isGoodPositionGerm_of_isLinSurjAt_wholeChart hf hx₀ (hX x₀) hsurj)

/-- **Theorem 3.57 with the index**: `theorem_3_57_wholeChart` with, at every zero `x`, regular data of
Definition 3.25 (2) of a dimension `d` which is constant near `x` along the solution set and equal
to `ind f'(y) = dim ker f'(y)` at every zero `y` of the chart domain. -/
theorem theorem_3_57_index_wholeChart (hf : B.IsScFredholmSectionWholeChart f)
    (hall : ∀ x, IsZeroAt P f x → B.IsGoodPositionGermTameWholeChart f x) (hne : (solutionSet P f).Nonempty) :
    ∃ hsub : PX.IsSubMPolyfold (solutionSet P f),
      haveI := PX.paracompactSpace_subtype (solutionSet P f)
      (MPolyfold.subPolyfold hsub).IsTame ∧
        (MPolyfold.subPolyfold hsub).IsManifoldWithCornersLoc ∧
        ∀ x ∈ solutionSet P f, ∃ d : ℕ, ∃ D : PX.TangentGermChart (solutionSet P f) x d,
          D.IsRegular ∧ (∀ y ∈ solutionSet P f ∩ D.φ.source,
            ∀ (n' : ℕ) (_ : PX.TangentGermChart (solutionSet P f) y n'), n' = d) ∧
          ∀ y ∈ solutionSet P f ∩ D.φ.source, B.IsSurjLinOfIndex f y d := by
  obtain ⟨hsub, h1, h2, -⟩ := theorem_3_57_wholeChart hf hall hne
  refine ⟨hsub, h1, h2, fun x hx => ?_⟩
  obtain ⟨d, D, hreg, -, hdim, -⟩ := theorem_3_54_two_index_wholeChart hf.isScSmooth (hall x hx) hx
    isOpen_univ (mem_univ x) fun y _ hy => hall y hy
  exact ⟨d, D, hreg, hdim, fun y hy =>
    isSurjLinOfIndex_of_forall_dim_wholeChart hf.isScSmooth (hall y hy.1) hy.1 (hdim y hy)⟩

/-- **Theorem 3.56 with the tameness and the regular data** (cf. `theorem_3_56_wholeChart`, which states the
manifold structure and "without boundary" only): for an M-polyfold without boundary and an
sc-Fredholm section in good position in a tame chart at every zero (`IsGoodPositionGermTameWholeChart`),
the solution set is a sub-M-polyfold whose induced structure is tame, that of a manifold
without boundary of locally constant dimension, with regular data of Definition 3.25 (2) at every
zero whose dimension is the Fredholm index (`theorem_3_57_index_wholeChart`, Lemma 2.26). -/
theorem theorem_3_56_tame_wholeChart (hX : PX.IsWithoutBoundary) (hf : B.IsScFredholmSectionWholeChart f)
    (hall : ∀ x, IsZeroAt P f x → B.IsGoodPositionGermTameWholeChart f x) (hne : (solutionSet P f).Nonempty) :
    ∃ hsub : PX.IsSubMPolyfold (solutionSet P f),
      haveI := PX.paracompactSpace_subtype (solutionSet P f)
      (MPolyfold.subPolyfold hsub).IsTame ∧
        (MPolyfold.subPolyfold hsub).IsManifoldWithCornersLoc ∧
        (MPolyfold.subPolyfold hsub).IsWithoutBoundary ∧
        ∀ x ∈ solutionSet P f, ∃ d : ℕ, ∃ D : PX.TangentGermChart (solutionSet P f) x d,
          D.IsRegular ∧ (∀ y ∈ solutionSet P f ∩ D.φ.source,
            ∀ (n' : ℕ) (_ : PX.TangentGermChart (solutionSet P f) y n'), n' = d) ∧
          ∀ y ∈ solutionSet P f ∩ D.φ.source, B.IsSurjLinOfIndex f y d := by
  have := PX.paracompactSpace_subtype (solutionSet P f)
  obtain ⟨hsub, h1, h2, h3⟩ := theorem_3_57_index_wholeChart hf hall hne
  refine ⟨hsub, h1, h2, fun y => ?_, h3⟩
  have := lemma_2_26 hsub y
  rw [hX y.1] at this
  exact Nat.le_zero.1 this

/-- **Theorem 3.56 with the text's hypothesis "`f'(x)` surjective at every zero"**
(`IsLinSurjAt`): for an M-polyfold without boundary good position is surjectivity
(`isGoodPositionGerm_of_isLinSurjAt_wholeChart`), and `theorem_3_56_tame_wholeChart` applies. -/
theorem theorem_3_56_of_surjective_wholeChart (hX : PX.IsWithoutBoundary) (hf : B.IsScFredholmSectionTameWholeChart f)
    (hall : ∀ x, IsZeroAt P f x → B.IsLinSurjAt f x) (hne : (solutionSet P f).Nonempty) :
    ∃ hsub : PX.IsSubMPolyfold (solutionSet P f),
      haveI := PX.paracompactSpace_subtype (solutionSet P f)
      (MPolyfold.subPolyfold hsub).IsTame ∧
        (MPolyfold.subPolyfold hsub).IsManifoldWithCornersLoc ∧
        (MPolyfold.subPolyfold hsub).IsWithoutBoundary ∧
        ∀ x ∈ solutionSet P f, ∃ d : ℕ, ∃ D : PX.TangentGermChart (solutionSet P f) x d,
          D.IsRegular ∧ (∀ y ∈ solutionSet P f ∩ D.φ.source,
            ∀ (n' : ℕ) (_ : PX.TangentGermChart (solutionSet P f) y n'), n' = d) ∧
          ∀ y ∈ solutionSet P f ∩ D.φ.source, B.IsSurjLinOfIndex f y d :=
  theorem_3_56_tame_wholeChart hX hf.toIsScFredholmSectionWholeChart
    (fun x hx => StrongBundle.isGoodPositionGerm_of_isLinSurjAt_wholeChart hf hx (hX x) (hall x hx)) hne

set_option maxHeartbeats 800000 in
-- destructuring the large existential conclusion of `theorem_3_54_nearby_kernel_wholeChart`
/-- **"`ker f'(y) = T_yS`", in a chart** (Theorem 3.19 (3) and Theorem 3.54 (4); Findings 101–103,
172).  For a section of a strong bundle, `f(x₀) = 0` and `(f, x₀)` in good position in a tame
chart (`IsGoodPositionGermTameWholeChart`), there are the tame strong bundle chart `c` centred at `x₀` of
Definition 3.53, the
conjugating sc-diffeomorphism `ψ : U → U' ⊆ C'` (inverse `ψ'`, `ψ(0) = 0`) of the proof of Theorem
3.54, the finite-dimensional kernel `K = ker D(h + t)(0)`, the solution graph `σ : V' → E'` over a
relatively open `V' ∋ 0` of `K ∩ C'` (`C¹`, `σ(0) = 0`, `Dσ(0) = 0`), an open `Vx ∋ x₀` with
`ψ ∘ ϕ({y ∈ Vx | f(y) = 0}) = {v + σ(v) | v ∈ V'}`, and an open `Vx₂ ⊆ Vx` containing `x₀`, such
that for every zero `y ∈ Vx₂`, with `ψ(ϕ(y)) = v + σ(v)`, `v ∈ V'`, and the level-`1` point `z`
over `ϕ(y)`: the derivative `Dψ(z)` maps the kernel of the linearization
`Lin(z) : T_zO → K_z` of `f` at `y` in the chart `c` onto the tangent space
`N_v = {n + Dσ(v)n | n ∈ K}` of the solution graph at `v` — the kernel of `f'(y)` is the tangent
space of the solution set, read in the chart `ψ ∘ ϕ`.  From `theorem_3_54_nearby_kernel_wholeChart`:
`ker Dg(z) = Dψ'(ψ z)(ker D(h + t)(ψ z))`, `ker D(h + t)(ψ z) = N_v`, `ker Dg(z) ⊆ T_zO`, and
`Lin(z) = Dg(z)` on `T_zO` (`linAt_eq_scDeriv`); `Dψ(z)Dψ'(ψ z) = 1`. -/
theorem theorem_3_54_ker_eq_tangent_wholeChart (hf : B.IsScSmoothSection f) {x₀ : X}
    (hg : B.IsGoodPositionGermTameWholeChart f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ (c : StrongBundleChart PX P) (_ : B.IsTameChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
      (E' : ScBanach) (C' U' : Set (E' 0)) (hU' : IsRelOpenInQuadrant E' C' U')
      (ψ : c.φ.model.E 0 → E' 0) (ψ' : E' 0 → c.φ.model.E 0)
      (_ : IsScDiffeoQuadrant c.relOpen hU' ψ ψ') (_ : ψ 0 = 0)
      (K : Submodule ℝ (E' 0)) (_ : FiniteDimensional ℝ K) (V' : Set K) (σ : K → E' 0)
      (Vx Vx₂ : Set X),
      IsOpen Vx ∧ x₀ ∈ Vx ∧ Vx ⊆ c.φ.source ∧
      (∃ O, IsOpen O ∧ V' = O ∩ Subtype.val ⁻¹' C') ∧ (0 : K) ∈ V' ∧
      ContDiffOn ℝ 1 σ V' ∧ σ 0 = 0 ∧ fderivWithin ℝ σ V' 0 = 0 ∧
      (ψ ∘ c.φ) '' {y ∈ Vx | IsZeroAt P f y} = (fun v : K => (v : E' 0) + σ v) '' V' ∧
      IsOpen Vx₂ ∧ x₀ ∈ Vx₂ ∧ Vx₂ ⊆ Vx ∧
      ∀ y ∈ Vx₂, IsZeroAt P f y → ∃ v ∈ V', ψ (c.φ y) = (v : E' 0) + σ v ∧
        ∀ z : c.φ.model.E 1, c.φ.model.E.toBase 1 z = c.φ y →
          (LinearMap.ker (linAt c.U c.R (c.principal f) z :
              ↥(rangeS (scDeriv c.U (r c.R) z)) →ₗ[ℝ] c.F 0)).map
            (((scDeriv c.U ψ z).comp (rangeS (scDeriv c.U (r c.R) z)).subtypeL :
              ↥(rangeS (scDeriv c.U (r c.R) z)) →L[ℝ] E' 0) :
              ↥(rangeS (scDeriv c.U (r c.R) z)) →ₗ[ℝ] E' 0) =
            graphSpace K (fderivWithin ℝ σ V' v) := by
  classical
  obtain ⟨c, hc, hxV, h0, h0U, g, t₀, Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, hCt, U', hU', Ψ, Ψ',
    hΨ, hψ0, 𝒮, h', Bc, hh'𝒮, hsurj, hpos, Yc, V', σ, Vx, n', Wq, T, Vx₂, hfill, ht₀, ht₀0, hconj,
    hgp, hYc, hYcc, hKsm, hV'rel, h0V', hσY, hσ1, hσC, hσ0, hDσ, hsol, hlift, hVxo, hx₀Vx, hVxsub,
    hinj, hzero, himage, hT, hVx₂o, hx₀Vx₂, hVx₂Vx, hker⟩ :=
    theorem_3_54_nearby_kernel_wholeChart hf.1 hg hx₀
  have hKfin : FiniteDimensional ℝ (LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0)) :=
    (𝒮.isFredholm_Dfs hCt hh'𝒮).1.finite_ker
  have hd : IsScDiffeoQuadrant c.relOpen hU' (IsStrongBundleMap.base Ψ)
      (IsStrongBundleMap.base Ψ') :=
    ⟨hΨ.toFun.base_isScSmooth c.relOpen, hΨ.invFun.base_isScSmooth hU',
      fun u hu => hΨ.toFun.base_mem hu, fun u hu => hΨ.invFun.base_mem hu,
      fun u hu => hΨ.base_base hu, fun u' hu' => hΨ.base_base' hu'⟩
  have hfr : IsSc1 c.U (c.principal f ∘ r c.R) := hf.isSc1_principal_comp_r hc.1
  refine ⟨c, hc, hxV, h0, ScBanach.paramProd Pn W, Ct ×ˢ univ, U', hU', IsStrongBundleMap.base Ψ,
    IsStrongBundleMap.base Ψ', hd, hψ0, LinearMap.ker (𝒮.Dfs h' : Pn × W 0 →ₗ[ℝ] Q × W 0), hKfin,
    V', σ, Vx, Vx₂, hVxo, hx₀Vx, hVxsub, hV'rel, h0V', hσC, hσ0, hDσ, himage, hVx₂o, hx₀Vx₂,
    hVx₂Vx, ?_⟩
  intro y hy hy0
  obtain ⟨heqfg, -, v, hv, z₀₁, x₁, hz₀₁, hz₀₁U, -, -, hlev, hveq, -, -, -, hker', -, hkerb, -,
    hcle, -⟩ := hker y hy hy0
  refine ⟨v, hv, hveq, fun z hz => ?_⟩
  have hzz : z = z₀₁ := c.φ.model.E.toBase_injective 1 (hz.trans hz₀₁.symm)
  subst hzz
  have hzO : c.φ.model.E.toBase 1 z ∈ r c.R '' c.U := by
    rw [hz, c.r_image]; exact c.φ.mapsTo_model y (hVxsub (hVx₂Vx hy))
  have heq : ∀ᶠ x in 𝓝 (c.φ.model.E.toBase 1 z), x ∈ r c.R '' c.U → c.principal f x = g x := by
    rw [hz]
    filter_upwards [heqfg] with x hx hxO
    exact hx (c.r_image ▸ hxO)
  have hlin : ∀ x : ↥(rangeS (scDeriv c.U (r c.R) z)),
      linAt c.U c.R (c.principal f) z x = scDeriv c.U g z x :=
    linAt_eq_scDeriv c.relOpen c.isRetraction hfr hfill.isScSmooth.isSc1 hzO heq
  have hinv : ∀ w, scDeriv c.U (IsStrongBundleMap.base Ψ) z
      (scDeriv U' (IsStrongBundleMap.base Ψ') x₁ w) = w := fun w => by
    rw [← hlev]; exact hΨ.scDeriv_base_base_inv c.relOpen hU' hz₀₁U w
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxk : (x : c.φ.model.E 0) ∈
        LinearMap.ker (scDeriv c.U g z : c.φ.model.E 0 →ₗ[ℝ] c.F 0) := by
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ← hlin]
      exact hx
    rw [hkerb] at hxk
    obtain ⟨u, hu, hux⟩ := hxk
    change scDeriv c.U (IsStrongBundleMap.base Ψ) z (x : c.φ.model.E 0) ∈ _
    rw [← hux, ContinuousLinearMap.coe_coe, hinv, hker']
    exact hu
  · intro hw
    rw [hker'] at hw
    have hx'k : scDeriv U' (IsStrongBundleMap.base Ψ') x₁ w ∈
        LinearMap.ker (scDeriv c.U g z : c.φ.model.E 0 →ₗ[ℝ] c.F 0) := by
      rw [hkerb]; exact ⟨w, hw, rfl⟩
    refine ⟨⟨_, hcle hx'k⟩, ?_, ?_⟩
    · change linAt c.U c.R (c.principal f) z ⟨_, hcle hx'k⟩ = 0
      rw [hlin]
      exact hx'k
    · change scDeriv c.U (IsStrongBundleMap.base Ψ) z
        (scDeriv U' (IsStrongBundleMap.base Ψ') x₁ w) = w
      exact hinv w

set_option maxHeartbeats 800000 in
-- destructuring the large existential conclusion of `theorem_3_54_nearby_kernel_wholeChart`
/-- **The filler condition of `IsGoodPositionGermFilledWholeChart` follows from good position** (Finding
174): the added hypothesis of `theorem_3_54_one_wholeChart` is a consequence of the text's hypotheses.  For an
sc-Fredholm section with tame germ data (`IsScFredholmSectionTameWholeChart`) and a zero `x₀` in good
position in a tame chart, the filler `g` in the chart of `theorem_3_54_nearby_kernel_wholeChart` satisfies condition (3) of Definition
3.4 at every zero of `g` in `O` near `0`: such a zero is `z₀ = ϕ(y)` for a zero `y` of `f` near
`x₀`, which is in good position (Theorem 3.54 (1), `theorem_3_54_one'_wholeChart`), so `Lin(z₀) = Tf̃(z₀)`
maps onto `K_{z₀}` in the chart `c` (`IsGoodPositionGermWholeChart.exists_isSurjLinOfIndex`),
`ker Dg(z₀) ⊆ T_{z₀}O` (`theorem_3_54_nearby_kernel_wholeChart` (c)), and the converse direction of Finding
100 (`normal_injective_of_exists_range_scDeriv_eq_ρ`) gives the injectivity of
`(1 − ρ(z₀))Dg(z₀)` on `ker Dr(z₀)`. -/
theorem isGoodPositionGermFilled_of_isGoodPositionGerm_wholeChart (hf : B.IsScFredholmSectionTameWholeChart f) {x₀ : X}
    (hg : B.IsGoodPositionGermTameWholeChart f x₀) (hx₀ : IsZeroAt P f x₀) :
    B.IsGoodPositionGermFilledWholeChart f x₀ := by
  classical
  have hfs : IsSection P f := hf.isScSmooth.1
  obtain ⟨c, hc, hxV, h0, h0U, g, t₀, Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, hCt, U', hU', Ψ, Ψ',
    hΨ, hψ0, 𝒮, h', Bc, hh'𝒮, hsurj, hpos, Yc, V', σ, Vx, n', Wq, T, Vx₂, hfill, ht₀, ht₀0, hconj,
    hgp, hYc, hYcc, hKsm, hV'rel, h0V', hσY, hσ1, hσC, hσ0, hDσ, hsol, hlift, hVxo, hx₀Vx, hVxsub,
    hinj, hzero, himage, hT, hVx₂o, hx₀Vx₂, hVx₂Vx, hker⟩ :=
    theorem_3_54_nearby_kernel_wholeChart hfs hg hx₀
  obtain ⟨Vx₁, hVx₁o, hx₀Vx₁, hall⟩ := theorem_3_54_one'_wholeChart hf hg hx₀
  -- the neighbourhood `N = W₁ ∩ W₂` of `0`: `f̂ = g` on `O ∩ W₁`, `O ∩ W₂ = ϕ(Vx₂ ∩ Vx₁)`
  obtain ⟨W₁, hW₁sub, hW₁o, h0W₁⟩ := mem_nhds_iff.1 hfill.filler.eq_on
  have hsV : Vx₂ ∩ Vx₁ ⊆ c.φ.source := fun y hy => hVxsub (hVx₂Vx hy.1)
  obtain ⟨W₂, hW₂o, hW₂⟩ := c.φ.exists_isOpen_image_eq hsV (hVx₂o.inter hVx₁o)
  have h0W₂ : (0 : c.φ.model.E 0) ∈ W₂ := by
    have : c.φ x₀ ∈ c.φ '' (Vx₂ ∩ Vx₁) := ⟨x₀, ⟨hx₀Vx₂, hx₀Vx₁⟩, rfl⟩
    rw [hW₂, h0] at this
    exact this.2
  refine ⟨hf.mem_smoothSet_of_isZeroAt hx₀, c, hc, hxV, h0, h0U, g, t₀, hfill, ht₀, ht₀0, hconj,
    hgp, W₁ ∩ W₂, hW₁o.inter hW₂o, ⟨h0W₁, h0W₂⟩, ?_⟩
  rintro z₁ ⟨hz₁O, hz₁W₁, hz₁W₂⟩ hgz b hb hρb
  -- the zero `y = ϕ⁻¹(z₀)` of `f`
  obtain ⟨y, ⟨hy₂, hy₁⟩, hyz⟩ : c.φ.model.E.toBase 1 z₁ ∈ c.φ '' (Vx₂ ∩ Vx₁) := by
    rw [hW₂]; exact ⟨hz₁O, hz₁W₂⟩
  have hyV : y ∈ c.φ.source := hsV ⟨hy₂, hy₁⟩
  have hz₁O' : c.φ.model.E.toBase 1 z₁ ∈ r c.R '' c.U := c.r_image ▸ hz₁O
  have hfz : c.principal f (c.φ.model.E.toBase 1 z₁) = 0 := by
    rw [hW₁sub hz₁W₁ hz₁O']; exact hgz
  have hy0 : IsZeroAt P f y := by
    rw [c.isZeroAt_iff hfs hyV, hyz]; exact hfz
  obtain ⟨heqfg, -, v, hv, z₀₁, x₁, hz₀₁, hz₀₁U, -, -, -, -, -, -, -, -, -, -, -, hcle, -⟩ :=
    hker y hy₂ hy0
  have hzz : z₁ = z₀₁ := c.φ.model.E.toBase_injective 1 (hyz.symm.trans hz₀₁.symm)
  subst hzz
  -- `Lin(z₀)` is onto in the chart `c`: `y` is in good position
  obtain ⟨d, hd, -⟩ :=
    StrongBundle.IsGoodPositionGermWholeChart.exists_isSurjLinOfIndex hf.isScSmooth
      (hall y hy₁ hy0).isGoodPositionGerm hy0
  have hzU : c.φ.model.E.toBase 1 z₁ ∈ c.U := mem_U_of_mem_O c.isRetraction hz₁O'
  have hfr : IsSc1 c.U (c.principal f ∘ r c.R) := hf.isScSmooth.isSc1_principal_comp_r hc.1
  have hfK : ∀ x ∈ r c.R '' c.U, (x, c.principal f x) ∈ c.R '' (c.U ×ˢ univ) := fun x hx =>
    c.principal_mem_K hfs (c.r_image ▸ hx)
  have hmem : ∀ x : ↥(rangeS (scDeriv c.U (r c.R) z₁)),
      linAt c.U c.R (c.principal f) z₁ x ∈ rangeS (ρCLM c.isRetraction hzU) := fun x =>
    ⟨_, rho_scDeriv_comp_r c.relOpen c.isRetraction hfr hfK hz₁O' hfz x⟩
  obtain ⟨hLs, -, -, -⟩ := hd c hc.1 hyV z₁ hyz.symm hzU
    ((linAt c.U c.R (c.principal f) z₁).codRestrict _ hmem) fun _ => rfl
  have heq : ∀ᶠ x in 𝓝 (c.φ.model.E.toBase 1 z₁), x ∈ r c.R '' c.U →
      c.principal f x = g x := by
    rw [← hyz]
    filter_upwards [heqfg] with x hx hxO
    exact hx (c.r_image ▸ hxO)
  have hlin := linAt_eq_scDeriv c.relOpen c.isRetraction hfr hfill.isScSmooth.isSc1 hz₁O' heq
  refine normal_injective_of_exists_range_scDeriv_eq_ρ c.relOpen c.isRetraction hz₁O' hcle
    (fun k => ?_) b hb hρb
  obtain ⟨x, hx⟩ := hLs ⟨ρ c.R (c.φ.model.E.toBase 1 z₁) k, ⟨k, rfl⟩⟩
  refine ⟨x, x.2, ?_⟩
  rw [← hlin]
  exact congrArg Subtype.val hx

end DimIndex

end Polyfold
