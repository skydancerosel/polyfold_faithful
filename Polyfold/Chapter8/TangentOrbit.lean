import Polyfold.Chapter8.TangentEp

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2017, arXiv 1707.08941), Part II,
Chapter 8, §8.1, p. 268: **Theorem 8.1.15 (2017: 8.4)** (paracompactness of `|TX|`) with its proof; the sentence
before it recalls Theorem 7.3.1 (2017: 7.2) (`hasParacompactOrbitSpace_iff_metrizableSpace`, `Lift.lean`) and
Theorem 8.1.1 (2017: 8.1) (`TangentEp.lean`).  There is no 2014 preprint of Part II; numbers and pages are the
2017 text's.  Part I items carry their 2017 numbers, with the preprint number of the Lean name in
brackets: Theorem 2.7.1 (2017: 2.5) [2.55] (Smirnov, `metrizableSpace_of_pullback`), Lemma 2.7.3 (2017: 2.7) [2.56] (Michael),
Proposition 2.7.4 (2017: 2.17) [2.57] (`proposition_2_7_4`), Proposition 2.3.15 (2017: 2.5) (3) [2.19 (3)]
(`MPolyfold.metrizableSpace_tangentSpace`).

# The orbit space of the tangent ep-groupoid

## The text, paraphrased

(p. 268) For an ep-groupoid with paracompact orbit space, `|X|` is metrizable (Theorem 7.3.1 (2017: 7.2)), and
`TX` is an ep-groupoid (Theorem 8.1.1 (2017: 8.1)); the paracompactness passes to `|TX|`.  (**Theorem 8.1.15 (2017: 8.4)**) If
`X` has paracompact orbit space `|X|`, then `TX` has paracompact orbit space `|TX|`.  *Proof*:
`|X¹|` is paracompact (Proposition 7.5.3 (2017: 7.12)).  For `z ∈ |X¹|` take a representative `x_z ∈ X₁` and a
neighbourhood `U(x_z)` in `X` with the natural `G_{x_z}`-action, such that `TU(x_z)`, as a bundle
over `U(x_z)¹`, is sc-isomorphic to a local bundle model `TO → O¹` with an sc-smooth bundle action
of `G_{x_z}`; then `|TU(x_z)|` and `|U(x_z)¹|` are metrizable.  The `|U(x_z)¹|` cover `|X¹|`;
take a subordinate locally finite closed cover `(A_z)_{z ∈ Σ}`.  The restriction of `TU(x_z)` to a
`G_{x_z}`-invariant closed subset of `U(x_z)¹`, divided by `G_{x_z}`, gives a closed paracompact
`Ã_z ⊆ |TX|`; `(Ã_z)` is a locally finite cover of `|TX|` by closed paracompact sets, and `|TX|`
is regular Hausdorff (being the orbit space of an ep-groupoid), so `|TX|` is paracompact by
Proposition 2.7.4 (2017: 2.17).

## What is formalized (namespace `Polyfold.EpGroupoid`)

* **The orbit map** `tangentOrbitProj : |TX| → |X¹|` of the projection functor `(p, p) : TX → X¹`
  (`tangentProjFunctor`, Theorem 8.1.1 (2017: 8.1)), `tangentOrbitProj_π`, `continuous_tangentOrbitProj`, and
  `preimage_tangentOrbitProj_image` (`|p|⁻¹(π₁(U ∩ X₁)) = π_T(p⁻¹(U))` for every `U ⊆ X`).
* **The action of `G_x` on `TU(x)`** for a natural representation `U(x)` (Theorem 7.1.13 (2017: 7.1)):
  `NaturalRep.tangentU` (`TU(x) = p⁻¹(U(x))`, open: `isOpen_tangentU`), `NaturalRep.tΦ` (the
  tangent maps `TΦ(g)`), `isScDiffeoOn_tΦ` (sc-diffeomorphisms of `TU(x)` with inverse `TΦ(g⁻¹)`),
  `levelVal_tangentProj_tΦ` (over `Φ(g)`), the action `tangentMulAction` (`tΦ_one`, `tΦ_mul`,
  `tangentSmul_val`) and `continuous_tangentSmul`.
* **The tangent of `Γ`**: `NaturalRep.tΓ` with `tBase_tΓ`, `tSrc_tΓ` (`Ts ∘ TΓ(g) = id`),
  `tTgt_tΓ` (`Tt ∘ TΓ(g) = TΦ(g)`).
* **`G_x\TU(x) ≅ |TU(x)|`**: `tangent_π_smul`, `tangent_π_eq_iff` (the fibres of `π_T` on
  `TU(x)` are the `G_x`-orbits), `tangentOrbitQuotientMap`,
  `isOpenEmbedding_tangentOrbitQuotientMap`, `range_tangentOrbitQuotientMap` (onto
  `|TU(x)| = π_T(TU(x))`), `image_tangentU_eq_preimage` (`|TU(x)| = |p|⁻¹(|U(x)₁|)`),
  `isOpen_image_liftU`.
* **The text's metrizability claims**: `metrizableSpace_image_tangentU` (`|TU(x_z)|`),
  `metrizableSpace_image_liftU` (`|U(x_z)¹|`), and `metrizableSpace_preimage_tangentOrbitProj`.
* **Theorem 8.1.15 (2017: 8.4)**: `metrizableSpace_tangent_orbitSpace` (`|TX|` is even metrizable),
  **`theorem_8_1_15`**, and the witness `hasParacompactOrbitSpace_tangent_trivial`.

## Reading

* **The route differs from the text's.**  The text's route (Lemma 2.7.3 (2017: 2.7) for a locally finite
  closed refinement `(A_z)` of `(|U(x_z)¹|)`, the closed paracompact `Ã_z`, the regularity of
  `|TX|` and Proposition 2.7.4 (2017: 2.17)) is replaced, as for Proposition 7.5.3 (2017: 7.12) in `Lift.lean`, by Smirnov's
  theorem pulled back along `|p| : |TX| → |X¹|` (Part I's `metrizableSpace_of_pullback`):
  `|X¹|` is metrizable (Proposition 7.5.3 (2017: 7.12), `metrizableSpace_liftOne_orbitSpace`), hence paracompact
  and Hausdorff, and every point of `|X¹|` has the open neighbourhood `|U(x)₁| = π₁(U(x)₁)` whose
  preimage `|p|⁻¹(|U(x)₁|) = |TU(x)|` is metrizable.  So `|TX|` is metrizable, hence paracompact
  (Stone).  The step shared with the text is the metrizability of `|TU(x_z)|`.  Neither the
  regularity of `|TX|` (Lemma 7.3.5 (2017: 7.7) for `TX`) nor Proposition 2.7.4 (2017: 2.17) is used; `Michael.lean` has the
  text's tools (`proposition_2_7_4`) but this proof does not need them.
* **`TU(x_z)` and its action.**  `TU(x)` is read as `p⁻¹(U(x)) ⊆ TX` (`tangentPreimage`), an open
  subset of `TX`, and the bundle action of `G_x` as `g ↦ TΦ(g)`, the tangent maps of the natural
  action (`tangentMapOn`; sc-diffeomorphisms of `TU(x)` covering `Φ(g)`).  The sc-isomorphism with
  a local bundle model `TO → O¹` is not used: `TU(x)` is metrizable as a subspace of `TX`
  (Proposition 2.3.15 (2017: 2.5) (3) [2.19 (3)]), and `G_x\TU(x)` by the text's metric `ρ̂` of Lemma 7.3.2 (2017: 7.4)
  (repeated here for a finite group acting by homeomorphisms on a metrizable space, since the
  versions in `OrbitTopology.lean` and `Lift.lean` are private).  The fibrewise linearity of the
  action is not formalized (Part I's `T_xX` carries no linear structure, gap G.7).
* **`|TU(x_z)|` and `|U(x_z)¹|`** are read as the subsets `π_T(TU(x)) ⊆ |TX|` and
  `π₁(U(x)₁) ⊆ |X¹|` with the subspace topologies (`U(x)₁ = U(x) ∩ X₁`, Chapter 7's
  `NaturalRep.liftU`).  That `G_x\TU(x) → |TX|` is an open embedding onto `|TU(x)|` (the argument
  of Proposition 7.1.19 (2017: 7.6) for `TX`) is left implicit in the text: the fibres of `π_T` on `TU(x)` are the
  `G_x`-orbits because a morphism `k : v → w` of `TX` lies over a morphism `p(k)` between points of
  `U(x)`, so `p(k) = Γ(g, s(p k))` (Theorem 7.1.13 (2017: 7.1) (3)), and `k = TΓ(g)(v)` by fibre injectivity of
  `Ts` (`tangent_ext`); conversely `TΓ(g)(v)` is a morphism `v → TΦ(g)(v)`.
  `|TU(x)| = |p|⁻¹(|U(x)₁|)` uses fibre surjectivity of `Ts` (`exists_tSrc_eq`): a vector over a
  point isomorphic in `X¹` to a point of `U(x)₁` is isomorphic in `TX` to a vector over `U(x)₁`.
* **The representatives.**  For `z ∈ |X¹|` with representative `a ∈ X¹`, `U(x)` is a natural
  representation in `X` (Theorem 7.1.13 (2017: 7.1)) at `x = a ∈ X₁` with `G_x` the isotropy group in `X`, as in
  the text ("`U(x_z)` in `X`").
* **Hypotheses.**  No hypothesis "for all …" is added.  `X.HasParacompactOrbitSpace` is
  satisfiable (the trivial ep-groupoid, `hasParacompactOrbitSpace_trivial`); the conclusion then
  holds for its tangent (`hasParacompactOrbitSpace_tangent_trivial`).
* **Universes.**  `TX` and `T𝐗` live in `Type (max u 1)` (Part I's `TangentSpace`), so `|TX|` does
  too; this is an artifact of the formalization.
* **"Subordinate locally finite closed subcover"** (the text's route, not followed here) is read
  as a locally finite closed refinement: the `A_z` are closed subsets of the open `|U(x_z)¹|`, not
  members of the cover (as `Michael.lean` reads p. 51's "subcovering").
* **Possible misprint**, as we read it: the statement of Theorem 8.1.15 (2017: 8.4) writes "parcompact" for
  "paracompact".
-/

open Set Function Topology Filter TopologicalSpace

noncomputable section

namespace Polyfold

universe u

/-! ### The text's metrics `ρ` and `ρ̂` (Lemma 7.3.2 (2017: 7.4)), for a finite group

Repeated from `OrbitTopology.lean` and `Lift.lean`, where they are private; used for
`G_x\TU(x)`. -/

section QuotientMetric

variable (G : Type*) {U : Type*} [Group G] [Fintype G] [MulAction G U] [PseudoMetricSpace U]

/-- `ρ(y, z) = max_g d(g y, g z)` (Lemma 7.3.2 (2017: 7.4)). -/
private def tqMaxDist (y z : U) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun g : G => dist (g • y) (g • z)

variable {G}

private theorem dist_smul_le_tqMaxDist (g : G) (y z : U) :
    dist (g • y) (g • z) ≤ tqMaxDist G y z :=
  Finset.le_sup' (fun g : G => dist (g • y) (g • z)) (Finset.mem_univ g)

private theorem dist_le_tqMaxDist (y z : U) : dist y z ≤ tqMaxDist G y z := by
  simpa only [one_smul] using dist_smul_le_tqMaxDist (1 : G) y z

private theorem tqMaxDist_lt_iff {y z : U} {ε : ℝ} :
    tqMaxDist G y z < ε ↔ ∀ g : G, dist (g • y) (g • z) < ε := by
  simp only [tqMaxDist, Finset.sup'_lt_iff, Finset.mem_univ, forall_const]

private theorem tqMaxDist_self (y : U) : tqMaxDist G y y = 0 :=
  le_antisymm (Finset.sup'_le _ _ fun _ _ => (dist_self _).le)
    (dist_nonneg.trans (dist_le_tqMaxDist y y))

private theorem tqMaxDist_comm (y z : U) : tqMaxDist G y z = tqMaxDist G z y := by
  simp only [tqMaxDist, dist_comm]

private theorem tqMaxDist_triangle (y z w : U) :
    tqMaxDist G y w ≤ tqMaxDist G y z + tqMaxDist G z w :=
  Finset.sup'_le _ _ fun g _ => (dist_triangle _ (g • z) _).trans
    (add_le_add (dist_smul_le_tqMaxDist g y z) (dist_smul_le_tqMaxDist g z w))

/-- **`ρ` is invariant** (Lemma 7.3.2 (2017: 7.4)): `ρ(h y, h z) = ρ(y, z)`. -/
private theorem tqMaxDist_smul (h : G) (y z : U) :
    tqMaxDist G (h • y) (h • z) = tqMaxDist G y z := by
  refine le_antisymm (Finset.sup'_le _ _ fun g _ => ?_) (Finset.sup'_le _ _ fun g _ => ?_)
  · rw [smul_smul, smul_smul]
    exact dist_smul_le_tqMaxDist (g * h) y z
  · have := dist_smul_le_tqMaxDist (g * h⁻¹) (h • y) (h • z)
    rwa [smul_smul, smul_smul, inv_mul_cancel_right] at this

variable (G) in
/-- `min_h ρ(y, h z)`, the quotient distance before passing to the quotient. -/
private def tqQuotDistAux (y z : U) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun h : G => tqMaxDist G y (h • z)

private theorem tqQuotDistAux_le (h : G) (y z : U) : tqQuotDistAux G y z ≤ tqMaxDist G y (h • z) :=
  Finset.inf'_le (fun h : G => tqMaxDist G y (h • z)) (Finset.mem_univ h)

private theorem exists_tqQuotDistAux_eq (y z : U) :
    ∃ h : G, tqQuotDistAux G y z = tqMaxDist G y (h • z) := by
  obtain ⟨h, -, hh⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := G))
    fun h : G => tqMaxDist G y (h • z)
  exact ⟨h, hh⟩

private theorem tqQuotDistAux_smul_right (k : G) (y z : U) :
    tqQuotDistAux G y (k • z) = tqQuotDistAux G y z := by
  refine le_antisymm (Finset.le_inf' _ _ fun h _ => ?_) (Finset.le_inf' _ _ fun h _ => ?_)
  · have := tqQuotDistAux_le (h * k⁻¹) y (k • z)
    rwa [smul_smul, inv_mul_cancel_right] at this
  · rw [smul_smul]
    exact tqQuotDistAux_le (h * k) y z

private theorem tqQuotDistAux_smul_left (k : G) (y z : U) :
    tqQuotDistAux G (k • y) z = tqQuotDistAux G y z := by
  refine le_antisymm (Finset.le_inf' _ _ fun h _ => ?_) (Finset.le_inf' _ _ fun h _ => ?_)
  · rw [← tqMaxDist_smul k, smul_smul]
    exact tqQuotDistAux_le (k * h) (k • y) z
  · have := tqQuotDistAux_le (k⁻¹ * h) y z
    rwa [← tqMaxDist_smul k, smul_smul, mul_inv_cancel_left] at this

private theorem tqQuotDistAux_comm_le (y z : U) : tqQuotDistAux G y z ≤ tqQuotDistAux G z y := by
  refine Finset.le_inf' _ _ fun h _ => ?_
  have := tqQuotDistAux_le h⁻¹ y z
  rwa [← tqMaxDist_smul h, smul_inv_smul, tqMaxDist_comm] at this

private theorem tqQuotDistAux_comm (y z : U) : tqQuotDistAux G y z = tqQuotDistAux G z y :=
  le_antisymm (tqQuotDistAux_comm_le y z) (tqQuotDistAux_comm_le z y)

private theorem tqQuotDistAux_triangle (y z w : U) :
    tqQuotDistAux G y w ≤ tqQuotDistAux G y z + tqQuotDistAux G z w := by
  obtain ⟨h, hh⟩ := exists_tqQuotDistAux_eq (G := G) y z
  obtain ⟨k, hk⟩ := exists_tqQuotDistAux_eq (G := G) z w
  rw [hh, hk, ← tqMaxDist_smul h z, smul_smul]
  exact (tqQuotDistAux_le (h * k) y w).trans (tqMaxDist_triangle _ _ _)

variable (G U) in
/-- **The quotient distance** `ρ̂([y], [z]) = min_{g, h} ρ(g y, h z) = min_h ρ(y, h z)` on `G\U`
(Lemma 7.3.2 (2017: 7.4)). -/
private def tqQuotDist :
    MulAction.orbitRel.Quotient G U → MulAction.orbitRel.Quotient G U → ℝ :=
  Quotient.lift₂ (tqQuotDistAux G) <| by
    rintro a₁ b₁ a₂ b₂ ⟨g, rfl⟩ ⟨h, rfl⟩
    exact (tqQuotDistAux_smul_left g _ _).trans (tqQuotDistAux_smul_right h _ _)

private theorem tqQuotDist_mk (y z : U) :
    tqQuotDist G U (Quotient.mk _ y) (Quotient.mk _ z) = tqQuotDistAux G y z := rfl

end QuotientMetric

/-- **The quotient of a metrizable space by a finite group of homeomorphisms is metrizable**, by
the text's metric `ρ̂` (the argument of Lemma 7.3.2 (2017: 7.4)). -/
private theorem metrizableSpace_quotient_of_finite {G U : Type*} [Group G] [Finite G]
    [MulAction G U] [TopologicalSpace U] [MetrizableSpace U]
    (hc : ∀ g : G, Continuous fun y : U => g • y) :
    MetrizableSpace (MulAction.orbitRel.Quotient G U) := by
  let _ := Fintype.ofFinite G
  let _ := metrizableSpaceMetric U
  have hmk : ∀ q : MulAction.orbitRel.Quotient G U, ∃ y : U, Quotient.mk _ y = q :=
    Quotient.exists_rep
  -- `ρ̂` defines the quotient topology.
  have hH : ∀ s : Set (MulAction.orbitRel.Quotient G U), IsOpen s ↔
      ∀ q ∈ s, ∃ ε > 0, ∀ q', tqQuotDist G U q q' < ε → q' ∈ s := by
    intro s
    rw [← isQuotientMap_quotient_mk'.isOpen_preimage]
    constructor
    · intro hs q hq
      obtain ⟨y, rfl⟩ := hmk q
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hs y hq
      refine ⟨ε, hε, fun q' hq' => ?_⟩
      obtain ⟨z, rfl⟩ := hmk q'
      obtain ⟨h, hh⟩ := exists_tqQuotDistAux_eq (G := G) y z
      rw [tqQuotDist_mk, hh] at hq'
      have hmem : h • z ∈ Quotient.mk (MulAction.orbitRel G U) ⁻¹' s :=
        hball (lt_of_le_of_lt (by rw [dist_comm]; exact dist_le_tqMaxDist _ _) hq')
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
      have hz' : tqMaxDist G y z < ε := tqMaxDist_lt_iff.2 fun g => by
        rw [dist_comm]
        exact mem_iInter.1 hz g
      have := tqQuotDistAux_le (1 : G) y z
      rw [one_smul] at this
      exact lt_of_le_of_lt this hz'
  let _ : MetricSpace (MulAction.orbitRel.Quotient G U) :=
    MetricSpace.ofDistTopology (tqQuotDist G U) (fun q => ?_) (fun q q' => ?_)
      (fun q q' q'' => ?_) hH fun q q' hqq' => ?_
  · infer_instance
  · obtain ⟨y, rfl⟩ := hmk q
    refine le_antisymm ?_ ?_
    · have := tqQuotDistAux_le (1 : G) y y
      rwa [one_smul, tqMaxDist_self] at this
    · obtain ⟨h, hh⟩ := exists_tqQuotDistAux_eq (G := G) y y
      rw [tqQuotDist_mk, hh]
      exact dist_nonneg.trans (dist_le_tqMaxDist _ _)
  · obtain ⟨y, rfl⟩ := hmk q
    obtain ⟨z, rfl⟩ := hmk q'
    exact tqQuotDistAux_comm y z
  · obtain ⟨y, rfl⟩ := hmk q
    obtain ⟨z, rfl⟩ := hmk q'
    obtain ⟨w, rfl⟩ := hmk q''
    exact tqQuotDistAux_triangle y z w
  · obtain ⟨y, rfl⟩ := hmk q
    obtain ⟨z, rfl⟩ := hmk q'
    obtain ⟨h, hh⟩ := exists_tqQuotDistAux_eq (G := G) y z
    rw [tqQuotDist_mk, hh] at hqq'
    have h0 : dist y (h • z) = 0 :=
      le_antisymm (hqq' ▸ dist_le_tqMaxDist _ _) dist_nonneg
    rw [dist_eq_zero] at h0
    rw [h0]
    exact Quotient.sound ⟨h, rfl⟩

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-! ### The orbit map `|p| : |TX| → |X¹|` -/

/-- **The orbit map `|p| : |TX| → |X¹|`** induced by the projection functor
`(p, p) : TX → X¹` (`tangentProjFunctor`, Theorem 8.1.1 (2017: 8.1)), `|a|_T ↦ |p(a)|₁`. -/
def tangentOrbitProj : X.tangentEpGroupoid.OrbitSpace → X.liftOne.OrbitSpace :=
  X.tangentProjFunctor.orbitMap

@[simp]
theorem tangentOrbitProj_π (a : X.PObj.TangentSpace) :
    X.tangentOrbitProj (X.tangentEpGroupoid.π a) = X.liftOne.π (X.PObj.tangentProj a) := rfl

/-- `|p|` is continuous (`p` is continuous and `|TX|` carries the quotient topology). -/
theorem continuous_tangentOrbitProj : Continuous X.tangentOrbitProj :=
  (X.liftOne.continuous_π.comp MPolyfold.continuous_tangentProj).quotient_lift _

/-- **`|p|⁻¹(|U₁|) = |TU|`**: for `U ⊆ X`, the preimage of `π₁(U ∩ X₁)` under `|p|` is
`π_T(TU)`, `TU = p⁻¹(U)`.  A vector `a` with `p(a) ≅ b ∈ U ∩ X₁` in `X¹` is isomorphic in `TX`
to the vector `Tt(k)` over `b`, `k` the lift of `p(a) → b` with `Ts(k) = a`. -/
theorem preimage_tangentOrbitProj_image (U : Set Obj) :
    X.tangentOrbitProj ⁻¹' (X.liftOne.π '' (X.PObj.levelVal 1 ⁻¹' U)) =
      X.tangentEpGroupoid.π '' X.PObj.tangentPreimage U := by
  ext w
  induction w using Quotient.inductionOn with | h a => ?_
  constructor
  · rintro ⟨b, hb, hba⟩
    obtain ⟨φ, hφs, hφt⟩ := (X.liftOne.π_eq_π_iff).1 hba.symm
    have hφs' : X.liftOne.src φ = X.PObj.tangentProj a := hφs
    have hs : X.PObj.levelVal 1 (X.PObj.tangentProj a) = X.src (X.PMor.levelVal 1 φ) := by
      rw [← hφs', liftOne_src_val]
    obtain ⟨k, hkp, hks⟩ := X.exists_tSrc_eq hs
    have hkb : X.tBase k = X.PMor.levelVal 1 φ := by rw [tBase, hkp]
    refine ⟨X.tTgt k, ?_, ?_⟩
    · change X.PObj.levelVal 1 (X.PObj.tangentProj (X.tTgt k)) ∈ U
      rw [levelVal_tangentProj_tTgt, hkb, ← liftOne_tgt_val, hφt]
      exact hb
    · exact ((X.tangentEpGroupoid.π_eq_π_iff).2 ⟨k, hks, rfl⟩).symm
  · rintro ⟨b, hb, hba⟩
    exact ⟨X.PObj.tangentProj b, hb, by rw [← tangentOrbitProj_π, hba]⟩

namespace NaturalRep

variable {X} {x : Obj} (R : X.NaturalRep x)

/-! ### The action of `G_x` on `TU(x)` -/

/-- `TU(x) = p⁻¹(U(x))`, an open subset of `TX` (the text's `TU(x_z)`). -/
def tangentU : Set X.PObj.TangentSpace := X.PObj.tangentPreimage R.U

theorem isOpen_tangentU : IsOpen R.tangentU := MPolyfold.isOpen_tangentPreimage R.isOpen_U

/-- The tangent map `TΦ(g) : TU(x) → TU(x)` of the natural action. -/
def tΦ (g : X.Isotropy x) : X.PObj.TangentSpace → X.PObj.TangentSpace :=
  MPolyfold.tangentMapOn (R.isScDiffeoOn_Φ g).isScSmoothOn

/-- `TΦ(g)` is an sc-diffeomorphism of `TU(x)` with inverse `TΦ(g⁻¹)` (`IsScDiffeoOn.tangent`). -/
theorem isScDiffeoOn_tΦ (g : X.Isotropy x) :
    X.PObj.tangentPolyfold.IsScDiffeoOn X.PObj.tangentPolyfold (R.tΦ g) (R.tΦ g⁻¹) R.tangentU
      R.tangentU :=
  (R.isScDiffeoOn_Φ g).tangent

/-- `p ∘ TΦ(g) = Φ(g) ∘ p` on `TU(x)`: `TΦ(g)` is a bundle map over `Φ(g)`. -/
theorem levelVal_tangentProj_tΦ (g : X.Isotropy x) {v : X.PObj.TangentSpace}
    (hv : v ∈ R.tangentU) :
    X.PObj.levelVal 1 (X.PObj.tangentProj (R.tΦ g v)) =
      R.Φ g (X.PObj.levelVal 1 (X.PObj.tangentProj v)) :=
  MPolyfold.levelVal_tangentProj_tangentMapOn _ hv

theorem tΦ_mem (g : X.Isotropy x) {v : X.PObj.TangentSpace} (hv : v ∈ R.tangentU) :
    R.tΦ g v ∈ R.tangentU :=
  MPolyfold.tangentMapOn_mapsTo _ (R.mapsTo_Φ g) hv

theorem tΦ_one {v : X.PObj.TangentSpace} (hv : v ∈ R.tangentU) : R.tΦ 1 v = v :=
  MPolyfold.tangentMapOn_eqOn_id _ (fun y hy => R.Φ_one y hy) hv

/-- `T(Φ(g h)) = TΦ(g) ∘ TΦ(h)` on `TU(x)` (the chain rule for `Φ(g h) = Φ(g) ∘ Φ(h)`). -/
theorem tΦ_mul (g h : X.Isotropy x) {v : X.PObj.TangentSpace} (hv : v ∈ R.tangentU) :
    R.tΦ (g * h) v = R.tΦ g (R.tΦ h v) := by
  have h1 := MPolyfold.tangentMapOn_comp (R.isScDiffeoOn_Φ g).isScSmoothOn
    (R.isScDiffeoOn_Φ h).isScSmoothOn (R.mapsTo_Φ h) hv
  rw [Function.comp_apply] at h1
  rw [tΦ, tΦ, tΦ, ← h1]
  exact MPolyfold.tangentMapOn_congr _ _ R.isOpen_U subset_rfl subset_rfl
    (fun y hy => R.Φ_mul g h y hy) hv

/-- **The action of `G_x` on `TU(x)`** by the tangent maps `TΦ(g)` (the text's "sc-smooth bundle
action by `G_{x_z}`"). -/
instance tangentMulAction : MulAction (X.Isotropy x) R.tangentU where
  smul g v := ⟨R.tΦ g v, R.tΦ_mem g v.2⟩
  one_smul v := Subtype.ext (R.tΦ_one v.2)
  mul_smul g h v := Subtype.ext (R.tΦ_mul g h v.2)

@[simp]
theorem tangentSmul_val (g : X.Isotropy x) (v : R.tangentU) :
    (g • v : R.tangentU).1 = R.tΦ g v.1 := rfl

/-- `G_x` acts on `TU(x)` by homeomorphisms. -/
theorem continuous_tangentSmul (g : X.Isotropy x) :
    Continuous fun v : R.tangentU => g • v :=
  continuous_induced_rng.2 ((MPolyfold.continuousOn_tangentMapOn _).comp_continuous
    continuous_subtype_val fun v => v.2)

/-! ### The tangent of `Γ` -/

/-- `TΓ(g) : TU(x) → T𝐗`, the tangent of `Γ(g, ·) : U(x) → 𝐗`. -/
def tΓ (g : X.Isotropy x) : X.PObj.TangentSpace → X.PMor.TangentSpace :=
  MPolyfold.tangentMapOn (R.isScSmoothOn_Γ g)

/-- `p(TΓ(g)(v)) = Γ(g, p(v))`. -/
theorem tBase_tΓ (g : X.Isotropy x) {v : X.PObj.TangentSpace} (hv : v ∈ R.tangentU) :
    X.tBase (R.tΓ g v) = R.Γ g (X.PObj.levelVal 1 (X.PObj.tangentProj v)) :=
  MPolyfold.levelVal_tangentProj_tangentMapOn _ hv

/-- `Ts(TΓ(g)(v)) = v` (the chain rule for `s ∘ Γ(g, ·) = id` on `U(x)`). -/
theorem tSrc_tΓ (g : X.Isotropy x) {v : X.PObj.TangentSpace} (hv : v ∈ R.tangentU) :
    X.tSrc (R.tΓ g v) = v := by
  rw [tSrc, tΓ, MPolyfold.tangentMap_tangentMapOn X.isScSmoothMap_src _ hv]
  exact MPolyfold.tangentMapOn_eqOn_id _ (fun y hy => R.src_Γ g y hy) hv

/-- `Tt(TΓ(g)(v)) = TΦ(g)(v)` (the chain rule for `t ∘ Γ(g, ·) = Φ(g)` on `U(x)`). -/
theorem tTgt_tΓ (g : X.Isotropy x) {v : X.PObj.TangentSpace} (hv : v ∈ R.tangentU) :
    X.tTgt (R.tΓ g v) = R.tΦ g v := by
  rw [tTgt, tΓ, MPolyfold.tangentMap_tangentMapOn X.isScSmoothMap_tgt _ hv]
  exact MPolyfold.tangentMapOn_congr _ _ R.isOpen_U subset_rfl subset_rfl
    (fun y hy => R.tgt_Γ g y hy) hv

/-! ### `G_x\TU(x) → |TX|` -/

/-- `|g ∗ v|_T = |v|_T`: `TΓ(g)(v)` is a morphism `v → g ∗ v` of `TX`. -/
theorem tangent_π_smul (g : X.Isotropy x) (v : R.tangentU) :
    X.tangentEpGroupoid.π (g • v : R.tangentU).1 = X.tangentEpGroupoid.π v.1 :=
  ((X.tangentEpGroupoid.π_eq_π_iff).2 ⟨R.tΓ g v.1, R.tSrc_tΓ g v.2, R.tTgt_tΓ g v.2⟩).symm

/-- **`|v|_T = |w|_T` for `v, w ∈ TU(x)` iff `w = g ∗ v`**: a morphism `k : v → w` of `TX` lies
over a morphism `p(k)` between points of `U(x)`, so `p(k) = Γ(g, s(p k))` for some `g`
(Theorem 7.1.13 (2017: 7.1) (3)), and `k = TΓ(g)(v)` by fibre injectivity (`tangent_ext`). -/
theorem tangent_π_eq_iff {v w : R.tangentU} :
    X.tangentEpGroupoid.π v.1 = X.tangentEpGroupoid.π w.1 ↔ ∃ g : X.Isotropy x, g • v = w := by
  constructor
  · intro h
    obtain ⟨k, hks, hkt⟩ := (X.tangentEpGroupoid.π_eq_π_iff).1 h
    have hks' : X.tSrc k = v.1 := hks
    have hkt' : X.tTgt k = w.1 := hkt
    have hs : X.src (X.tBase k) = X.PObj.levelVal 1 (X.PObj.tangentProj v.1) := by
      rw [← levelVal_tangentProj_tSrc, hks']
    have ht : X.tgt (X.tBase k) = X.PObj.levelVal 1 (X.PObj.tangentProj w.1) := by
      rw [← levelVal_tangentProj_tTgt, hkt']
    obtain ⟨g, hg, -⟩ := R.existsUnique_Γ (X.tBase k) (by rw [hs]; exact v.2)
      (by rw [ht]; exact w.2)
    have hk : R.tΓ g v.1 = k :=
      X.tangent_ext (by rw [R.tBase_tΓ g v.2, ← hs, hg]) (by rw [R.tSrc_tΓ g v.2, hks'])
    refine ⟨g, Subtype.ext ?_⟩
    rw [tangentSmul_val, ← R.tTgt_tΓ g v.2, hk, hkt']
  · rintro ⟨g, rfl⟩
    exact (R.tangent_π_smul g v).symm

private theorem tangentOrbitRel_iff (v w : R.tangentU) :
    MulAction.orbitRel (X.Isotropy x) R.tangentU v w ↔
      X.tangentEpGroupoid.π v.1 = X.tangentEpGroupoid.π w.1 := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff, eq_comm, R.tangent_π_eq_iff]

/-- `G_x\TU(x) → |TX|`, `G_x ∗ v ↦ |v|_T`. -/
def tangentOrbitQuotientMap :
    MulAction.orbitRel.Quotient (X.Isotropy x) R.tangentU → X.tangentEpGroupoid.OrbitSpace :=
  Quotient.lift (fun v : R.tangentU => X.tangentEpGroupoid.π v.1) fun v w h =>
    (R.tangentOrbitRel_iff v w).1 h

/-- **`G_x\TU(x) → |TX|` is an open embedding** (the argument of Proposition 7.1.19 (2017: 7.6) for `TX`, with
the `G_x`-action on `TU(x)` in place of a natural representation of `TX`). -/
theorem isOpenEmbedding_tangentOrbitQuotientMap : IsOpenEmbedding R.tangentOrbitQuotientMap := by
  refine .of_continuous_injective_isOpenMap
    ((X.tangentEpGroupoid.continuous_π.comp continuous_subtype_val).quotient_lift _)
    (fun q q' h => ?_) fun S hS => ?_
  · induction q using Quotient.inductionOn with | h v => ?_
    induction q' using Quotient.inductionOn with | h w => ?_
    exact Quotient.sound ((R.tangentOrbitRel_iff v w).2 h)
  · have himage : R.tangentOrbitQuotientMap '' S =
        X.tangentEpGroupoid.π '' (Subtype.val '' (Quotient.mk _ ⁻¹' S)) := by
      ext w
      constructor
      · rintro ⟨q, hq, rfl⟩
        induction q using Quotient.inductionOn with | h v => ?_
        exact ⟨v, ⟨v, hq, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
        exact ⟨Quotient.mk _ v, hv, rfl⟩
    rw [himage]
    exact X.tangentEpGroupoid.proposition_7_1_8 _ (R.isOpen_tangentU.isOpenMap_subtype_val _
      (hS.preimage continuous_quotient_mk'))

/-- The range of `G_x\TU(x) → |TX|` is `|TU(x)| = π_T(TU(x))`. -/
theorem range_tangentOrbitQuotientMap :
    range R.tangentOrbitQuotientMap = X.tangentEpGroupoid.π '' R.tangentU := by
  ext w
  constructor
  · rintro ⟨q, rfl⟩
    induction q using Quotient.inductionOn with | h v => ?_
    exact ⟨v.1, v.2, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨Quotient.mk _ ⟨v, hv⟩, rfl⟩

/-- **`|TU(x)| = |p|⁻¹(|U(x)₁|)`**: `π_T(TU(x))` is the preimage of `π₁(U(x)₁)` under `|p|`. -/
theorem image_tangentU_eq_preimage :
    X.tangentEpGroupoid.π '' R.tangentU = X.tangentOrbitProj ⁻¹' (X.liftOne.π '' R.liftU) :=
  (X.preimage_tangentOrbitProj_image R.U).symm

/-- `|U(x)₁| = π₁(U(x)₁)` is open in `|X¹|` (Proposition 7.1.8 (2017: 7.1) for `X¹`). -/
theorem isOpen_image_liftU : IsOpen (X.liftOne.π '' R.liftU) :=
  X.liftOne.proposition_7_1_8 _ R.isOpen_liftU

/-- **`|TU(x)|` is metrizable** (the text's "`|TU(x_z)|` … metrizable"): `TU(x)` is metrizable as
a subset of `TX` (Proposition 2.3.15 (preprint 2.19) (3)), so is `G_x\TU(x)` (the metric `ρ̂` of Lemma 7.3.2 (2017: 7.4)), and
`G_x\TU(x) → |TX|` is an open embedding onto `|TU(x)|`. -/
theorem metrizableSpace_image_tangentU : MetrizableSpace (X.tangentEpGroupoid.π '' R.tangentU) := by
  have := X.PObj.metrizableSpace_tangentSpace
  have := metrizableSpace_quotient_of_finite R.continuous_tangentSmul
  exact (R.isOpenEmbedding_tangentOrbitQuotientMap.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr R.range_tangentOrbitQuotientMap)).symm.isEmbedding.metrizableSpace

/-- **`|U(x)₁|` is metrizable** (the text's "`|U(x_z)¹|` … metrizable"; Proposition 7.5.3 (2017: 7.12)'s
`metrizableSpace_preimage_orbitIncl`, carried along `|U(x)|₁ = π₁(U(x)₁)`). -/
theorem metrizableSpace_image_liftU : MetrizableSpace (X.liftOne.π '' R.liftU) := by
  have := R.metrizableSpace_preimage_orbitIncl
  exact (Homeomorph.setCongr (X.preimage_orbitIncl_image R.U)).symm.isEmbedding.metrizableSpace

/-- **`|p|⁻¹(|U(x)₁|)` is metrizable**. -/
theorem metrizableSpace_preimage_tangentOrbitProj :
    MetrizableSpace (X.tangentOrbitProj ⁻¹' (X.liftOne.π '' R.liftU)) := by
  have := R.metrizableSpace_image_tangentU
  exact (Homeomorph.setCongr R.image_tangentU_eq_preimage).symm.isEmbedding.metrizableSpace

end NaturalRep

/-! ### Theorem 8.1.15 (2017: 8.4) -/

/-- **`|TX|` is metrizable** if `|X|` is paracompact: `|X¹|` is metrizable (Proposition 7.5.3 (2017: 7.12)),
hence paracompact and Hausdorff, and Smirnov's theorem pulled back along `|p| : |TX| → |X¹|`
(`metrizableSpace_of_pullback`) applies, the preimages `|p|⁻¹(|U(x)₁|) = |TU(x)|` being
metrizable. -/
theorem metrizableSpace_tangent_orbitSpace (h : X.HasParacompactOrbitSpace) :
    MetrizableSpace X.tangentEpGroupoid.OrbitSpace := by
  have := X.metrizableSpace_liftOne_orbitSpace h
  have : ParacompactSpace X.liftOne.OrbitSpace := paracompactSpace_of_metrizableSpace _
  refine metrizableSpace_of_pullback X.tangentOrbitProj X.continuous_tangentOrbitProj fun z => ?_
  obtain ⟨a, rfl⟩ := X.liftOne.surjective_π z
  obtain ⟨R, -⟩ := theorem_7_1_13 X (X.PObj.levelVal 1 a) isOpen_univ (mem_univ _)
  exact ⟨X.liftOne.π '' R.liftU, R.isOpen_image_liftU,
    mem_image_of_mem _ (R.mem_U : a ∈ R.liftU), R.metrizableSpace_preimage_tangentOrbitProj⟩

/-- **Theorem 8.1.15 (2017: 8.4)**: if the ep-groupoid `X` has paracompact orbit space `|X|`, then the tangent
ep-groupoid `TX` (Theorem 8.1.1 (2017: 8.1)) has paracompact orbit space `|TX|`. -/
theorem theorem_8_1_15 (h : X.HasParacompactOrbitSpace) :
    X.tangentEpGroupoid.HasParacompactOrbitSpace :=
  have := X.metrizableSpace_tangent_orbitSpace h
  paracompactSpace_of_metrizableSpace _

/-- **Theorem 8.1.15 (2017: 8.4) is not vacuous**: the trivial ep-groupoid of any M-polyfold `Z` has paracompact
orbit space (`hasParacompactOrbitSpace_trivial`), hence so has its tangent. -/
theorem hasParacompactOrbitSpace_tangent_trivial {Z : Type u} [TopologicalSpace Z] [T2Space Z]
    [ParacompactSpace Z] (P : MPolyfold Z) :
    (trivial P).tangentEpGroupoid.HasParacompactOrbitSpace :=
  (trivial P).theorem_8_1_15 (hasParacompactOrbitSpace_trivial P)

end EpGroupoid

end Polyfold
