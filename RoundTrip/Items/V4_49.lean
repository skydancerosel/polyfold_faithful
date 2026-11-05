import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_49

/-!
Round trip for V4_49 (Theorem 4.22 in a tame centred chart).  `A` is the conjunction of the types
of `Polyfold.sup_minimalSubspaceWith_eq_top`, `Polyfold.sup_minimalSubspaceWith_eq_top_graph` and
`Polyfold.theorem_4_22_chart` (no universe parameters).

B is the text's chart step for an M-polyfold: `X` tame, `A` smooth, in general position at `x`,
data `(V, s)` with `V ⊆ dom φ`, `φ` a chart on a tame retract centred at `x`, `N = T₀(φ(A ∩ V))`;
it asks for an sc-splitting `E = N ⊕ Y` with `Y ⊆ E_0`, the graph description of `φ(A ∩ V)` near
`0`, the chain `d_A(a) = d_{N ∩ C}(p(a)) = d_C(φ a) = d_O(φ a)`, `T_aA + E_0 = E` and general
position along the graph.

`A_to_B` (from the second and third conjuncts), glue:
* the data `(V, s)` is the project's `SubmanifoldData` with `W = V`; `exists_chartRetraction` gives
  the sc⁺-retraction `t` onto `φ(A ∩ V)`, so `N = range Dt(0)` is finite-dimensional, smooth and an
  sc-subspace; the project's general position at `x` holds in the chart `φ`
  (`IsGeneralPositionAt.isGeneralPositionChart`, chart independence);
* `theorem_4_22_chart` gives the closed good complement `Y = ker p ⊆ E_0`, `W₁`, `V'`, `Γ`;
  **B's sc-splitting `E = N ⊕ Y` is new glue** (`isScSplitting_of_proj`: a closed complement of a
  finite-dimensional smooth sc-subspace is an sc-complement, the density argument of V3_82);
  `Vg = V' ⊆ N ∩ C` as a subset of `E₀` (relatively open via the induced topology),
  `δ(v) = Γ(v) − v`;
* `d_A(a) = d_{N ∩ C}(p(φ a))`: the corner chart `p ∘ φ` of `A` (`CornerChartData`, as in the
  project's proof of Theorem 4.22 (2)) is a tame chart of `A`; B computes `d_{N ∩ C}` in the
  sc-space `E.ofSubspace hN`, the project in `ScBanach.const N`: transported along the
  sc-isomorphism `E.ofSubspace hN ≅ const N` (`degIndex_scIso`, both finite-dimensional);
  `d_{N ∩ C}(v) = d_C(Γ v)` is the third conjunct's (2); `d_C = d_O` is Proposition 2.36 (14);
* `T_aA + E_0 = E` is the second conjunct; general position at `a` is the third conjunct's (3).

`B → A` fails: `A` is stated for arbitrary sc-retracts / sc⁺-retractions `t` in an arbitrary
sc-space with a tame retraction (no M-polyfold, no submanifold), and its first two conjuncts are
standalone lemmas (general position at `0` ⇒ `N + E_0 = E`; `N + E_0 = E` propagates along a graph)
with hypotheses B never states.
-/

namespace RoundTrip.V4_49
open Polyfold Set

def A : Prop :=
  type_of% @Polyfold.sup_minimalSubspaceWith_eq_top ∧
    type_of% @Polyfold.sup_minimalSubspaceWith_eq_top_graph ∧
    type_of% @Polyfold.theorem_4_22_chart

theorem A_holds : A :=
  ⟨@Polyfold.sup_minimalSubspaceWith_eq_top, @Polyfold.sup_minimalSubspaceWith_eq_top_graph,
    @Polyfold.theorem_4_22_chart⟩

section Linear

/-- **A closed complement of a finite-dimensional smooth sc-subspace is an sc-complement**: if
`p : E₀ → N` is a continuous projection onto the finite-dimensional `N ⊆ E_∞` with kernel `Y`,
then `E = N ⊕ Y` is an sc-splitting (the density argument of V3_82 / V4_38). -/
theorem isScSplitting_of_proj {E : ScBanach} {N Y : Submodule ℝ (E 0)} [FiniteDimensional ℝ N]
    (hNs : N ≤ E.smooth) (hNsc : E.IsScSubspace N) (hYc : IsClosed (Y : Set (E 0)))
    (p : E 0 →L[ℝ] N) (hpN : ∀ x : N, p x = x) (hpY : ∀ y ∈ Y, p y = 0)
    (hker : ∀ x, p x = 0 → x ∈ Y) : E.IsScSplitting N Y := by
  have hlift : ∀ m, ∀ n : N, ∃ y : E m, E.toBase m y = n := fun m n =>
    (E.mem_smooth_iff.1 (hNs n.2)) m
  -- the continuous lift `L : N → E_m`
  have hL : ∀ m, ∃ L : N →L[ℝ] E m, ∀ n : N, E.toBase m (L n) = n := by
    intro m
    let fN : E.levelSub N m →ₗ[ℝ] N :=
      ((E.toBase m : E m →ₗ[ℝ] E 0).restrict (p := E.levelSub N m) (q := N) fun _ hz => hz)
    have hfN : Function.Bijective fN := by
      refine ⟨fun a b hab => Subtype.ext (E.toBase_injective m ?_), fun n => ?_⟩
      · exact congrArg Subtype.val hab
      · obtain ⟨y, hy⟩ := hlift m n
        exact ⟨⟨y, show E.toBase m y ∈ N by rw [hy]; exact n.2⟩, Subtype.ext hy⟩
    let eN := LinearEquiv.ofBijective fN hfN
    refine ⟨LinearMap.toContinuousLinearMap ((E.levelSub N m).subtype ∘ₗ (eN.symm : N →ₗ[ℝ] _)),
      fun n => ?_⟩
    have := congrArg Subtype.val (eN.apply_symm_apply n)
    exact this
  refine ⟨hNsc, ⟨hYc, fun m x hx => ?_⟩, fun m => ⟨?_, ?_⟩⟩
  · obtain ⟨L, hL⟩ := hL m
    let Φ : E m → E m := fun z => z - L (p (E.toBase m z))
    have hΦc : Continuous Φ :=
      continuous_id.sub (L.continuous.comp (p.continuous.comp (E.toBase m).continuous))
    have hΦx : Φ x = x := by
      have : p (E.toBase m x) = 0 := hpY _ hx
      simp only [Φ, this, map_zero, sub_zero]
    have hΦS : Φ '' (E.smoothLvl m) ⊆ E.levelSub Y m ∩ E.smoothLvl m := by
      rintro _ ⟨u, hus, rfl⟩
      have hb : E.toBase m (Φ u) = E.toBase m u - (p (E.toBase m u) : E 0) := by
        simp only [Φ, map_sub, hL]
      refine ⟨?_, ?_⟩
      · change E.toBase m (Φ u) ∈ Y
        rw [hb]; refine hker _ ?_
        rw [map_sub, hpN, sub_self]
      · change E.toBase m (Φ u) ∈ E.smooth
        rw [hb]; exact E.smooth.sub_mem hus (hNs (p _).2)
    have h1 : x ∈ closure (E.smoothLvl m) := (E.dense_smooth m).closure_eq ▸ mem_univ x
    rw [← hΦx]
    exact closure_mono hΦS (image_closure_subset_closure_image hΦc (mem_image_of_mem Φ h1))
  · rw [Submodule.disjoint_def]
    intro x hxN hxY
    have h1 : E.toBase m x = 0 := by
      have hN' : E.toBase m x ∈ N := hxN
      have := hpN ⟨_, hN'⟩
      have h0 : p (E.toBase m x) = 0 := hpY (E.toBase m x) hxY
      change p (E.toBase m x) = _ at this
      rw [h0] at this
      exact (congrArg Subtype.val this).symm
    exact E.toBase_injective m (by rw [h1, map_zero])
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    obtain ⟨y, hy⟩ := hlift m (p (E.toBase m x))
    have hyN : y ∈ E.levelSub N m := show E.toBase m y ∈ N by rw [hy]; exact (p _).2
    have hxy : x - y ∈ E.levelSub Y m := by
      change E.toBase m (x - y) ∈ Y
      refine hker _ ?_
      rw [map_sub, map_sub, hy, hpN, sub_self]
    have := Submodule.add_mem_sup hyN hxy
    rwa [add_sub_cancel] at this

/-- The degeneracy index is invariant under sc-isomorphisms. -/
theorem degIndex_scIso {E F : ScBanach} (e : ScIso E F) {C' : Set (F 0)}
    (hC' : IsPartialQuadrant F C') {x : E 0} (hx : e 0 x ∈ C') :
    degIndex E (e 0 ⁻¹' C') x = degIndex F C' (e 0 x) := by
  obtain ⟨k, W, Tn, hTn⟩ := hC'
  have hT' : e 0 ⁻¹' C' = (e.trans Tn) 0 ⁻¹' quadrant k W 0 := by rw [hTn]; rfl
  rw [degIndex_eq (e.trans Tn) hT' (show x ∈ e 0 ⁻¹' C' from hx), degIndex_eq Tn hTn hx]
  rfl

/-- The constant sc-structures on linearly equivalent finite-dimensional spaces. -/
noncomputable def constIso {A B : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] (ℓ : A ≃ₗ[ℝ] B) :
    ScIso (ScBanach.const A) (ScBanach.const B) where
  lvl _ := ℓ.toContinuousLinearEquiv
  incl_comm _ _ := rfl

/-- `d_{N ∩ C}` computed in `E.ofSubspace hN` (B) and in `ScBanach.const N` (the project) agree. -/
theorem degIndex_ofSubspace {E : ScBanach} {N : Submodule ℝ (E 0)} [FiniteDimensional ℝ N]
    (hN : E.IsScSubspace N) {C : Set (E 0)}
    (hC : IsPartialQuadrant (ScBanach.const N) (Subtype.val ⁻¹' C))
    (q : (E.ofSubspace hN).lvl 0) (hq : q.1 ∈ C) (hqN : q.1 ∈ N) :
    degIndex (E.ofSubspace hN) {w : (E.ofSubspace hN).lvl 0 | w.1 ∈ C} q =
      degIndex (ScBanach.const N) (Subtype.val ⁻¹' C) ⟨q.1, hqN⟩ := by
  let ℓ : E.levelSub N 0 ≃ₗ[ℝ] N := LinearEquiv.ofEq _ _ (E.levelSub_zero N)
  have : FiniteDimensional ℝ (E.levelSub N 0) := ℓ.symm.finiteDimensional
  have : FiniteDimensional ℝ ((E.ofSubspace hN) 0) := this
  let e : ScIso (E.ofSubspace hN) (ScBanach.const N) :=
    (E.ofSubspace hN).isoConstOfFiniteDimensional.trans (constIso ℓ)
  have he : ∀ w : (E.ofSubspace hN) 0, ((e 0 w : N) : E 0) = w.1 := fun w => rfl
  have hset : {w : (E.ofSubspace hN).lvl 0 | w.1 ∈ C} = e 0 ⁻¹' (Subtype.val ⁻¹' C) := by
    ext w; simp only [mem_ofPred_eq, mem_preimage, he]
  rw [hset, degIndex_scIso e hC (by simp only [mem_preimage, he]; exact hq)]
  congr 1

end Linear

theorem A_to_B : A → B := by
  rintro ⟨-, hgraph, h422⟩ X _ _ _ P S x hP hS hxS hgp V s φ n Wq T N hs himg hxV hφ htr hVφ hT
    hφx hN
  let d : P.SubmanifoldData S := ⟨V, s, hs.isScSmoothOn.isOpen, hs, himg⟩
  have hshrink : d.toSubData.shrink φ = V := by
    ext y
    simp only [MPolyfold.SubData.shrink, mem_inter_iff, mem_preimage]
    constructor
    · exact fun h => h.1.1
    · intro hy
      exact ⟨⟨hy, hVφ hy⟩, hs.mapsTo hy, hVφ (hs.mapsTo hy)⟩
  have hxφ : x ∈ φ.source := hVφ hxV
  obtain ⟨R, hR, hRt⟩ := htr
  have hRT := hRt n Wq T hT
  obtain ⟨t, ht, htp, -⟩ :=
    d.exists_chartRetraction hφ (P.levelMk 1 x (d.mem_levelSet_one hxS hxV)) R hR
  have ht' : t.retract = φ '' (S ∩ V) := by rw [ht, hshrink, inter_comm]
  have htR : t.retract ⊆ R.retract := by
    rw [ht, hR]; exact φ.image_subset_model fun _ hy => d.toSubData.shrink_subset_source φ hy.1
  have h0 : (0 : φ.model.E 0) ∈ t.retract := by rw [ht', ← hφx]; exact ⟨x, ⟨hxS, hxV⟩, rfl⟩
  have h0O : (0 : φ.model.E 0) ∈ R.retract := htR h0
  have h01 : (0 : φ.model.E 1) ∈ φ.model.E.lvlSet t.retract 1 := by
    rw [ScBanach.mem_lvlSet, map_zero]; exact h0
  have hs0 : (0 : φ.model.E 1) ∈ φ.model.E.smoothLvl 1 := by
    change φ.model.E.toBase 1 0 ∈ (φ.model.E.smooth : Set (φ.model.E 0))
    rw [map_zero]; exact φ.model.E.smooth.zero_mem
  have hNt : N = LinearMap.range (scDeriv t.U t 0 : φ.model.E 0 →ₗ[ℝ] φ.model.E 0) := by
    refine SetLike.coe_injective (hN.trans ?_)
    rw [← ht']; exact tangentSpace_eq_coe_submodule t h01
  have : FiniteDimensional ℝ N := by rw [hNt]; exact lemma_4_7_ii htp h01
  have hNsc : φ.model.E.IsScSubspace N := hNt ▸ (t.isScSplitting_range_scDeriv h01 hs0).1
  have hNs : N ≤ φ.model.E.smooth := (φ.model.E.proposition_1_6_iff N).1 hNsc
  have hN' : (N : Set (φ.model.E 0)) = tangentSpace φ.model.E φ.model.C t.retract 0 := by
    rw [ht']; exact hN
  have hz0 : φ.model.E.toBase 1 0 = φ x := by rw [map_zero, hφx]
  have hgp0 : IsGeneralPositionRetractAt φ.model.E φ.model.C R.retract t.retract T 0 := by
    have := hgp.isGeneralPositionChart d hφ T hT hxV hxφ hz0
    rw [MPolyfold.SubmanifoldData.IsGeneralPositionChart, ← hR, ← ht] at this
    exact this
  obtain ⟨hsup, -, Y, p, W₁, V', Γ, hYE, hYc, hYgood, hpN, hpY, hker, hW₁, h0W₁, hV', h0V', -,
    hpΓ, hΓY, hΓV, hΓp, -, hpmap, hΓmap, hdeg, hgen⟩ :=
    h422 T hT hRT h0O t htp htR h0 hN' hgp0
  obtain ⟨O', hO', hV'eq⟩ := hV'.relOpen
  obtain ⟨G, hG, hGO'⟩ := isOpen_induced_iff.1 hO'
  classical
  let δ : φ.model.E 0 → φ.model.E 0 := fun v => if h : v ∈ N then Γ ⟨v, h⟩ - v else 0
  have hδ : ∀ u : N, δ u = Γ u - u := fun u => by simp only [δ, dif_pos u.2]
  have hΓδ : ∀ u : N, (u : φ.model.E 0) + δ u = Γ u := fun u => by rw [hδ]; abel
  refine ⟨hNsc, Y, W₁, Subtype.val '' V', δ,
    isScSplitting_of_proj hNs hNsc hYc p hpN hpY hker, hYE, hW₁, h0W₁, ⟨G, hG, ?_⟩,
    ⟨0, h0V', rfl⟩, ?_, ?_, ?_⟩
  · ext w
    simp only [mem_image, mem_inter_iff, SetLike.mem_coe]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [hV'eq, ← hGO'] at hu
      exact ⟨hu.1, u.2, hu.2⟩
    · rintro ⟨hwG, hwN, hwC⟩
      refine ⟨⟨w, hwN⟩, ?_, rfl⟩
      rw [hV'eq, ← hGO']
      exact ⟨hwG, hwC⟩
  · rintro _ ⟨u, hu, rfl⟩
    rw [hδ]; exact hΓY u hu
  · rw [← ht', ← hΓV, image_image]
    exact image_congr fun u _ => (hΓδ u).symm
  · have hO : φ.model.O.Nonempty := ⟨_, φ.mapsTo_model x hxφ⟩
    have : ParacompactSpace S := P.paracompactSpace_subtype S
    refine ⟨hS.isSubMPolyfold, this, hO, fun a q haV haW hq hφa => ?_⟩
    obtain ⟨u, hu, hqu⟩ := hq
    have hΓu : Γ u = φ a := by rw [hφa, ← hqu, hΓδ]
    have haR : φ a ∈ t.retract ∩ W₁ := ⟨by rw [ht']; exact ⟨a, ⟨a.2, haV⟩, rfl⟩, haW⟩
    have hpa : p (φ a) = u := by rw [← hΓu, hpΓ u hu]
    have hqN : q.1 ∈ N := hqu ▸ u.2
    have hqC : q.1 ∈ φ.model.C := by
      rw [← hqu]; rw [hV'eq] at hu; exact hu.2
    have hqu' : (⟨q.1, hqN⟩ : N) = u := Subtype.ext hqu.symm
    have hCN : IsPartialQuadrant (ScBanach.const N) (Subtype.val ⁻¹' φ.model.C) :=
      hV'.isPartialQuadrant
    have hdq := degIndex_ofSubspace hNsc hCN q hqC hqN
    rw [hqu'] at hdq
    have hdu : degIndex (ScBanach.const N) (Subtype.val ⁻¹' φ.model.C) u =
        degIndex φ.model.E φ.model.C (φ a) := by rw [hdeg u hu, hΓu]
    refine ⟨?_, hdq.trans hdu, fun o ho => ?_, fun z Na hz hNa => ?_, ?_⟩
    · -- `d_A(a) = d_{N ∩ C}(p(φ a))`: the corner chart `p ∘ φ` of `A`
      rw [hdq]
      set χ := MPolyfold.subChart d.toSubData hφ ⟨x, hxS⟩ with hχ
      have hχO : χ.model.O = t.retract := ht.symm
      let N₁ : Submodule ℝ (χ.model.E 0) := N
      have : FiniteDimensional ℝ N₁ := by assumption
      let cd : CornerChartData χ N₁ :=
        { Y := Y
          isGoodComplement := hYgood
          isClosed_Y := hYc
          p := p
          p_N := hpN
          p_Y := hpY
          W := W₁
          isOpen_W := hW₁
          zero_mem_W := h0W₁
          V := V'
          V_relOpen := hV'
          zero_mem_V := h0V'
          Γ := Γ
          p_map := by rw [hχO]; exact hpmap
          Γ_map := by rw [hχO]; exact hΓmap
          Γ_p := by rw [hχO]; exact hΓp
          p_Γ := hpΓ }
      have hcd : (MPolyfold.subPolyfold hS.isSubMPolyfold).IsChart cd.chart :=
        cd.chart_isChart (MPolyfold.subPolyfold_isChart hS.isSubMPolyfold d.toSubData hφ ⟨x, hxS⟩)
      have haχ : a ∈ cd.chart.source :=
        ⟨show (a : X) ∈ d.toSubData.shrink φ by rw [hshrink]; exact haV, haW⟩
      rw [(MPolyfold.subPolyfold hS.isSubMPolyfold).degIndex_eq_chartDegIndex_of_isTameRetract hcd
        cd.chart_isCornerChart.isTameRetract haχ, MPolyfold.chartDegIndex]
      change degIndex (ScBanach.const N) (Subtype.val ⁻¹' φ.model.C) (p (φ a)) = _
      rw [hpa]
    · rw [φ.model.degIndex_toMPolyfold_of_isTameWith hO R hR hT hRT o, ho]
    · refine hgraph T t.isScRetract hsup hYE hpN hker hW₁ hV' hpmap hΓmap hΓp hpΓ hu
        (y := z) (by rw [hz, hΓu]) ?_
      rw [ht']; exact hNa
    · obtain ⟨y, hy, -⟩ :=
        exists_smoothLvl_one_of_mem_smooth (d.apply_mem_smooth hφ a.2 haV (hVφ haV))
      refine ⟨a.2, d, φ, n, Wq, T, y, haV, hφ, hVφ haV, hT, hy, ?_⟩
      have := hgen (φ a) haR y hy
      rw [MPolyfold.SubmanifoldData.IsGeneralPositionChart, ← hR, ← ht]
      exact this

#rt_check RoundTrip.V4_49.A_to_B [Polyfold.sup_minimalSubspaceWith_eq_top,
  Polyfold.sup_minimalSubspaceWith_eq_top_graph, Polyfold.theorem_4_22_chart]

end RoundTrip.V4_49
