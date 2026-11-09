import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_39

/-! Round trip for V9_39 (Definition 9.4.1, 2021 p. 429; 2017: Definition 9.12: the relative
tangent space `T^K_zM` and essential points).

The item lists the definitions `chartImage`, `relTangent`, `essentialSet`, `crossLines`
(vocabulary) and six theorems; `A` is the conjunction of their types, universes at `0`:
`span_tangentConeAt_chartImage_eq_map` (chart independence: the spans of the tangent cones of two
chart images correspond under the derivative of the chart change, for any two charts of the
maximal atlas), `relTangent_eq_map`, `relTangent_eq_top_iff`, `essentialSet_eq`
(`K^e = K ∩ closure{T^K_zM = T_zM}`), and the witnesses `essentialSet_crossLines`,
`nonEssential_crossLines` (in `ℝ²` with the model `𝓘(ℝ, Fin 2 → ℝ)`).  All of them are for an
arbitrary model with corners `I : H → E`, except the witnesses.

`B` (quadrant model `[0, ∞)ⁿ ⊆ EuclideanSpace ℝ (Fin n)`, `C^∞` manifold): (a) the project's
`relTangent` is the span of the text's unit vectors `lim (φ(z_k) − φ(z))/|φ(z_k) − φ(z)|`,
`z_k ∈ K ∖ {z}`, `z_k → z` in `M`, in the preferred chart; (b) chart independence, in the form:
the span computed in any chart `e` of the maximal atlas, mapped by the derivative within
`range I` of `extChartAt z ∘ e⁻¹`, is the one of the preferred chart; (c) the project's
`essentialSet` is `B`'s.

* `A ⇒ B` (`A_to_B`).  The glue lemma `unitVecsB_eq` (proved here, not from `A`): for a chart `e`
  around `z`, `B`'s unit vectors (sequences in `M`, the total map `e.extend I`) are exactly the
  project's `unitDirections` of the chart image `ϕ(V ∩ K)` at `ϕ(z)` (sequences in `E`): a
  sequence `z_k → z` is eventually in `e.source`, where `e.extend I` is injective and continuous,
  and the tail has the same limit direction; conversely `(e.extend I)⁻¹` is continuous on the
  chart target.  With `span_unitDirections` (non-item) this gives (a).  (b) is `A`'s first
  conjunct `span_tangentConeAt_chartImage_eq_map` for `e` and `chartAt z`, after replacing
  `fderivWithin` on the chart-change domain by `fderivWithin` on `range I` (the domain is a
  neighbourhood of `ϕ(z)` in `range I`, and `range I` has unique derivatives).  (c) follows from
  (a).
* `B ⇒ A` fails: `B` concerns only quadrant models and the `C^∞` atlas; `A`'s first four
  conjuncts are stated for every model with corners (any normed `E`, also infinite-dimensional)
  and every `C^k` atlas, `k ≠ 0`, and `essentialSet_eq` and the two `crossLines` witnesses
  (model `𝓘(ℝ, Fin 2 → ℝ)`, sup norm) are facts that `B` does not state at all.  On quadrant
  models `B` does give `A`'s chart independence (`chartIndep_of_B`, `relTangent_eq_map_of_B`,
  section `Quadrant`): `B` (b) relates each chart to the preferred one, and the chain rule for
  chart changes (proved here) relates any two.  So the difference is generality and extra (true)
  content of `A`.
-/

set_option maxSynthPendingDepth 3

namespace RoundTrip.V9_39
open Polyfold Set Filter Topology Manifold
open scoped ContDiff

/-- The project's statements, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.span_tangentConeAt_chartImage_eq_map.{0, 0, 0} ∧
  type_of% @Polyfold.relTangent_eq_map.{0, 0, 0} ∧
  type_of% @Polyfold.relTangent_eq_top_iff.{0, 0, 0} ∧
  type_of% @Polyfold.essentialSet_eq.{0, 0, 0} ∧
  type_of% @Polyfold.essentialSet_crossLines ∧
  type_of% @Polyfold.nonEssential_crossLines

theorem A_holds : A :=
  ⟨@Polyfold.span_tangentConeAt_chartImage_eq_map, @Polyfold.relTangent_eq_map,
    @Polyfold.relTangent_eq_top_iff, @Polyfold.essentialSet_eq, Polyfold.essentialSet_crossLines,
    Polyfold.nonEssential_crossLines⟩

section Glue
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant n) M]

omit [ChartedSpace (EuclideanQuadrant n) M] in
/-- **`B`'s unit vectors are the project's `unitDirections` of the chart image.** -/
theorem unitVecsB_eq (e : OpenPartialHomeomorph M (EuclideanQuadrant n)) {z : M}
    (hz : z ∈ e.source) (K : Set M) :
    unitVecsB (e.extend (Q n)) K z = unitDirections (chartImage (Q n) e K) (e.extend (Q n) z) := by
  ext v
  constructor
  · rintro ⟨u, hu, hlim, hv⟩
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually (e.open_source.mem_nhds hz))
    refine ⟨fun k => e.extend (Q n) (u (k + N)), fun k => ⟨⟨u (k + N),
      ⟨hN _ (by omega), (hu _).1⟩, rfl⟩, fun h => (hu (k + N)).2 ?_⟩, ?_, ?_⟩
    · exact (e.extend (Q n)).injOn (by rw [e.extend_source]; exact hN _ (by omega))
        (by rw [e.extend_source]; exact hz) (mem_singleton_iff.1 h)
    · exact (e.continuousAt_extend hz).tendsto.comp (hlim.comp (tendsto_add_atTop_nat N))
    · exact hv.comp (tendsto_add_atTop_nat N)
  · rintro ⟨w, hw, hlim, hv⟩
    have hwK : ∀ k, (e.extend (Q n)).symm (w k) ∈ e.source ∧
        (e.extend (Q n)).symm (w k) ∈ K ∧
        e.extend (Q n) ((e.extend (Q n)).symm (w k)) = w k := by
      intro k
      obtain ⟨m, hm, hmw⟩ := (hw k).1
      rw [← hmw, e.extend_left_inv hm.1]
      exact ⟨hm.1, hm.2, rfl⟩
    have htgt : ∀ k, w k ∈ (e.extend (Q n)).target := fun k => by
      rw [← (hwK k).2.2]
      exact (e.extend (Q n)).map_source (by rw [e.extend_source]; exact (hwK k).1)
    have hz' : e.extend (Q n) z ∈ (e.extend (Q n)).target :=
      (e.extend (Q n)).map_source (by rw [e.extend_source]; exact hz)
    refine ⟨fun k => (e.extend (Q n)).symm (w k), fun k => ⟨(hwK k).2.1, fun h => ?_⟩, ?_, ?_⟩
    · have h' : (e.extend (Q n)).symm (w k) = z := h
      apply (hw k).2
      rw [mem_singleton_iff, ← (hwK k).2.2, h']
    · have h1 := ((e.continuousOn_extend_symm (I := Q n)) _ hz').tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall htgt⟩)
      rw [e.extend_left_inv hz] at h1
      exact h1
    · refine hv.congr fun k => ?_
      simp only [(hwK k).2.2]

omit [ChartedSpace (EuclideanQuadrant n) M] in
/-- `B`'s span of unit vectors in a chart is the span of the tangent cone of the chart image. -/
theorem relTangentInB_eq (e : OpenPartialHomeomorph M (EuclideanQuadrant n)) {z : M}
    (hz : z ∈ e.source) (K : Set M) :
    relTangentInB (e.extend (Q n)) K z =
      Submodule.span ℝ (tangentConeAt ℝ (chartImage (Q n) e K) (e.extend (Q n) z)) := by
  rw [relTangentInB, unitVecsB_eq e hz K, span_unitDirections]

/-- **`B` (a)**, from glue only. -/
theorem relTangent_eq_relTangentB (K : Set M) (z : M) :
    relTangent (Q n) K z = relTangentB K z := by
  rw [relTangentB, extChartAt, relTangentInB_eq _ (mem_chart_source _ z)]
  rfl

end Glue

theorem A_to_B : A → B := by
  intro hA n M _ _ _ K
  refine ⟨fun z => relTangent_eq_relTangentB K z, fun z e he hze => ?_, ?_⟩
  · -- (b): `A`'s chart independence for `e` and `chartAt z`
    have hc : chartAt (EuclideanQuadrant n) z ∈ IsManifold.maximalAtlas (Q n) ∞ M :=
      IsManifold.chart_mem_maximalAtlas z
    have hzc : z ∈ (chartAt (EuclideanQuadrant n) z).source := mem_chart_source _ z
    have key := hA.1 (n := ∞) (by simp) he hc hze hzc K
    have hp : e.extend (Q n) z ∈
        ((Q n).extendCoordChange e (chartAt (EuclideanQuadrant n) z)).source :=
      extend_mem_extendCoordChange_source hze hzc
    have hD : fderivWithin ℝ (extChartAt (Q n) z ∘ (e.extend (Q n)).symm) (Set.range (Q n))
          (e.extend (Q n) z) =
        fderivWithin ℝ ((Q n).extendCoordChange e (chartAt (EuclideanQuadrant n) z))
          ((Q n).extendCoordChange e (chartAt (EuclideanQuadrant n) z)).source
          (e.extend (Q n) z) :=
      fderivWithin_of_mem_nhdsWithin ((Q n).extendCoordChange_source_mem_nhdsWithin hp)
        ((Q n).uniqueDiffOn _ ⟨e z, rfl⟩)
        (((Q n).contDiffOn_extendCoordChange he hc _ hp).differentiableWithinAt (by simp))
    rw [hD, relTangentInB_eq e hze K, relTangentB, extChartAt,
      relTangentInB_eq _ hzc K, key]
  · -- (c) from (a)
    ext z
    simp only [essentialSet, essentialB, relTangent_eq_relTangentB]


/-! ### `B ⇒ A`, on quadrant models only

`B` gives `A`'s chart independence (`span_tangentConeAt_chartImage_eq_map`, and so
`relTangent_eq_map`) for the quadrant models and the `C^∞` atlas: `B` (b) relates every chart to
the preferred chart `chartAt z`; two charts `e, e'` are related through it by the chain rule for
chart changes (`D(c→e') ∘ D(e→c) = D(e→e')`, `D(e'→e') = id`, proved here). -/

section Quadrant
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant n) M]
  [IsManifold (Q n) ∞ M]

/-- The derivative within `range I` of the chart change `a → b` at `a(z)`. -/
noncomputable abbrev Dq (a b : OpenPartialHomeomorph M (EuclideanQuadrant n)) (z : M) :=
  fderivWithin ℝ ((Q n).extendCoordChange a b) (range (Q n)) (a.extend (Q n) z)

omit [ChartedSpace (EuclideanQuadrant n) M] [IsManifold (Q n) ∞ M] in
theorem source_subset_range (a b : OpenPartialHomeomorph M (EuclideanQuadrant n)) :
    ((Q n).extendCoordChange a b).source ⊆ range (Q n) :=
  fun _ hx => a.extend_target_subset_range hx.1

omit [IsManifold (Q n) ∞ M] in
theorem hasD {a b : OpenPartialHomeomorph M (EuclideanQuadrant n)}
    (ha : a ∈ IsManifold.maximalAtlas (Q n) ∞ M) (hb : b ∈ IsManifold.maximalAtlas (Q n) ∞ M)
    {z : M} (hza : z ∈ a.source) (hzb : z ∈ b.source) :
    HasFDerivWithinAt ((Q n).extendCoordChange a b) (Dq a b z) (range (Q n))
      (a.extend (Q n) z) :=
  (((Q n).contDiffWithinAt_extendCoordChange ha hb
    (extend_mem_extendCoordChange_source hza hzb)).differentiableWithinAt
    (by simp)).hasFDerivWithinAt

omit [IsManifold (Q n) ∞ M] in
/-- `fderivWithin` on the chart-change domain is `Dq`. -/
theorem fderivWithin_source_eq {a b : OpenPartialHomeomorph M (EuclideanQuadrant n)}
    (ha : a ∈ IsManifold.maximalAtlas (Q n) ∞ M) (hb : b ∈ IsManifold.maximalAtlas (Q n) ∞ M)
    {z : M} (hza : z ∈ a.source) (hzb : z ∈ b.source) :
    fderivWithin ℝ ((Q n).extendCoordChange a b) ((Q n).extendCoordChange a b).source
      (a.extend (Q n) z) = Dq a b z :=
  (fderivWithin_of_mem_nhdsWithin
    ((Q n).extendCoordChange_source_mem_nhdsWithin (extend_mem_extendCoordChange_source hza hzb))
    ((Q n).uniqueDiffOn _ ⟨a z, rfl⟩)
    (((Q n).contDiffOn_extendCoordChange ha hb _
      (extend_mem_extendCoordChange_source hza hzb)).differentiableWithinAt (by simp))).symm

omit [IsManifold (Q n) ∞ M] in
/-- **Chain rule for chart changes**: `D(b→c) ∘ D(a→b) = D(a→c)`. -/
theorem Dq_comp {a b c : OpenPartialHomeomorph M (EuclideanQuadrant n)}
    (ha : a ∈ IsManifold.maximalAtlas (Q n) ∞ M) (hb : b ∈ IsManifold.maximalAtlas (Q n) ∞ M)
    (hc : c ∈ IsManifold.maximalAtlas (Q n) ∞ M) {z : M} (hza : z ∈ a.source)
    (hzb : z ∈ b.source) (hzc : z ∈ c.source) :
    (Dq b c z).comp (Dq a b z) = Dq a c z := by
  have hp := extend_mem_extendCoordChange_source (I := Q n) hza hzb
  have hg : HasFDerivWithinAt ((Q n).extendCoordChange b c) (Dq b c z) (range (Q n))
      ((Q n).extendCoordChange a b (a.extend (Q n) z)) := by
    rw [extendCoordChange_apply_of_mem hza]
    exact hasD hb hc hzb hzc
  have h1 := hg.comp (a.extend (Q n) z) ((hasD ha hb hza hzb).mono (source_subset_range a b))
    (fun x _ => ⟨b ((a.extend (Q n)).symm x), rfl⟩)
  have heq : EqOn ((Q n).extendCoordChange a c)
      ((Q n).extendCoordChange b c ∘ (Q n).extendCoordChange a b)
      ((Q n).extendCoordChange a b).source := by
    intro x hx
    have hx' : (a.extend (Q n)).symm x ∈ b.source := by
      have := hx.2
      rwa [mem_preimage, b.extend_source] at this
    change c.extend (Q n) ((a.extend (Q n)).symm x) =
      c.extend (Q n) ((b.extend (Q n)).symm (b.extend (Q n) ((a.extend (Q n)).symm x)))
    rw [b.extend_left_inv hx']
  have h2 := (h1.congr heq (heq hp)).mono_of_mem_nhdsWithin
    ((Q n).extendCoordChange_source_mem_nhdsWithin hp)
  exact (h2.fderivWithin ((Q n).uniqueDiffOn _ ⟨a z, rfl⟩)).symm

omit [ChartedSpace (EuclideanQuadrant n) M] [IsManifold (Q n) ∞ M] in
/-- `D(a→a) = id`. -/
theorem Dq_self {a : OpenPartialHomeomorph M (EuclideanQuadrant n)} {z : M}
    (hza : z ∈ a.source) : Dq a a z = ContinuousLinearMap.id ℝ _ := by
  have hp := extend_mem_extendCoordChange_source (I := Q n) hza hza
  have heq : EqOn ((Q n).extendCoordChange a a) id ((Q n).extendCoordChange a a).source :=
    fun x hx => (a.extend (Q n)).right_inv hx.1
  have h := ((hasFDerivWithinAt_id (𝕜 := ℝ) (a.extend (Q n) z) ((Q n).extendCoordChange a a).source).congr heq (heq hp)).mono_of_mem_nhdsWithin
    ((Q n).extendCoordChange_source_mem_nhdsWithin hp)
  exact h.fderivWithin ((Q n).uniqueDiffOn _ ⟨a z, rfl⟩)

/-- **`A`'s first conjunct on quadrant models, from `B`** (the `C^∞` atlas). -/
theorem chartIndep_of_B (hB : B) {e e' : OpenPartialHomeomorph M (EuclideanQuadrant n)}
    (he : e ∈ IsManifold.maximalAtlas (Q n) ∞ M) (he' : e' ∈ IsManifold.maximalAtlas (Q n) ∞ M)
    {z : M} (hze : z ∈ e.source) (hze' : z ∈ e'.source) (K : Set M) :
    Submodule.span ℝ (tangentConeAt ℝ (chartImage (Q n) e' K) (e'.extend (Q n) z)) =
      (Submodule.span ℝ (tangentConeAt ℝ (chartImage (Q n) e K) (e.extend (Q n) z))).map
        (fderivWithin ℝ ((Q n).extendCoordChange e e') ((Q n).extendCoordChange e e').source
          (e.extend (Q n) z) : _ →ₗ[ℝ] _) := by
  obtain ⟨-, hb, -⟩ := hB n M K
  set ch := chartAt (EuclideanQuadrant n) z
  have hc : ch ∈ IsManifold.maximalAtlas (Q n) ∞ M := IsManifold.chart_mem_maximalAtlas z
  have hzc : z ∈ ch.source := mem_chart_source _ z
  have hbe : (Submodule.span ℝ (tangentConeAt ℝ (chartImage (Q n) e K) (e.extend (Q n) z))).map
      (Dq e ch z : _ →ₗ[ℝ] _) =
      Submodule.span ℝ (tangentConeAt ℝ (chartImage (Q n) ch K) (ch.extend (Q n) z)) := by
    have := hb z e he hze
    rw [relTangentInB_eq e hze K, relTangentB, extChartAt, relTangentInB_eq _ hzc K] at this
    exact this
  have hbe' : (Submodule.span ℝ (tangentConeAt ℝ (chartImage (Q n) e' K) (e'.extend (Q n) z))).map
      (Dq e' ch z : _ →ₗ[ℝ] _) =
      Submodule.span ℝ (tangentConeAt ℝ (chartImage (Q n) ch K) (ch.extend (Q n) z)) := by
    have := hb z e' he' hze'
    rw [relTangentInB_eq e' hze' K, relTangentB, extChartAt, relTangentInB_eq _ hzc K] at this
    exact this
  rw [fderivWithin_source_eq he he' hze hze', ← Dq_comp he hc he' hze hzc hze',
    ContinuousLinearMap.toLinearMap_comp, Submodule.map_comp, hbe, ← hbe', ← Submodule.map_comp,
    ← ContinuousLinearMap.toLinearMap_comp, Dq_comp he' hc he' hze' hzc hze', Dq_self hze',
    ContinuousLinearMap.coe_id, Submodule.map_id]

/-- **`A`'s second conjunct (`relTangent_eq_map`) on quadrant models, from `B`.** -/
theorem relTangent_eq_map_of_B (hB : B) {e' : OpenPartialHomeomorph M (EuclideanQuadrant n)}
    (he' : e' ∈ IsManifold.maximalAtlas (Q n) ∞ M) {z : M} (hze' : z ∈ e'.source) (K : Set M) :
    Submodule.span ℝ (tangentConeAt ℝ (chartImage (Q n) e' K) (e'.extend (Q n) z)) =
      (relTangent (Q n) K z).map
        (fderivWithin ℝ ((Q n).extendCoordChange (chartAt _ z) e')
          ((Q n).extendCoordChange (chartAt _ z) e').source (extChartAt (Q n) z z) :
            _ →ₗ[ℝ] _) :=
  chartIndep_of_B hB (IsManifold.chart_mem_maximalAtlas z) he' (mem_chart_source _ z) hze' K

end Quadrant

#rt_check RoundTrip.V9_39.A_to_B [Polyfold.span_tangentConeAt_chartImage_eq_map,
  Polyfold.relTangent_eq_map, Polyfold.relTangent_eq_top_iff, Polyfold.essentialSet_eq,
  Polyfold.essentialSet_crossLines, Polyfold.nonEssential_crossLines]
#rt_overlap RoundTrip.V9_39.A_to_B [Polyfold.span_tangentConeAt_chartImage_eq_map,
  Polyfold.relTangent_eq_map, Polyfold.relTangent_eq_top_iff, Polyfold.essentialSet_eq,
  Polyfold.essentialSet_crossLines, Polyfold.nonEssential_crossLines]
#print axioms RoundTrip.V9_39.A_to_B

#rt_check RoundTrip.V9_39.chartIndep_of_B [Polyfold.span_tangentConeAt_chartImage_eq_map,
  Polyfold.relTangent_eq_map, Polyfold.relTangent_eq_top_iff, Polyfold.essentialSet_eq,
  Polyfold.essentialSet_crossLines, Polyfold.nonEssential_crossLines]
#rt_check RoundTrip.V9_39.relTangent_eq_map_of_B [Polyfold.span_tangentConeAt_chartImage_eq_map,
  Polyfold.relTangent_eq_map, Polyfold.relTangent_eq_top_iff, Polyfold.essentialSet_eq,
  Polyfold.essentialSet_crossLines, Polyfold.nonEssential_crossLines]
#rt_overlap RoundTrip.V9_39.chartIndep_of_B [Polyfold.span_tangentConeAt_chartImage_eq_map,
  Polyfold.relTangent_eq_map, Polyfold.relTangent_eq_top_iff, Polyfold.essentialSet_eq,
  Polyfold.essentialSet_crossLines, Polyfold.nonEssential_crossLines]
#print axioms RoundTrip.V9_39.chartIndep_of_B

end RoundTrip.V9_39
