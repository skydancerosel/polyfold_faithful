import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_51

/-!
Round trip for V3_51 (Theorem 3.57, the step from the tangent germ property).  `A` is the type of
`Polyfold.theorem_3_6_11_of_tangentGerm`, universes instantiated at `0`.

A is a statement about an arbitrary nonempty solution set with the regular `n`-dimensional
tangent germ property, for one **fixed** `n`, and it has no Fredholm hypothesis at all.  B has the
text's analytic hypotheses (tame strong bundle, sc-Fredholm section, surjectivity and good
position at every zero) and a dimension that may vary along `S`.

Glue for `A → B`:
* A is applied to an arbitrary set `M`: every `M ⊆ X` is the solution set of the section
  `y ↦ (y, 1_{M^c}(y))` of the trivial bundle `X × ℝ → X` (`A_of_set`).
* B's hypothesis `IsSurjGoodPosAt` gives `IsGoodPositionGermTame` at every zero (as in V3_70).
  Then the project's `theorem_3_6_8_two` (Theorem 3.54 (2), not part of A) gives, at every zero
  `y`, a regular datum of dimension `d(y)` on a chart domain `U_y`, along which the dimension is
  constant; so the local piece `S ∩ U_y` has the regular `d(y)`-dimensional tangent germ property
  (shrinking the data as in the project's proof of `theorem_3_1_26_of_nearby`), and **A** makes it a
  sub-M-polyfold whose induced structure is an `d(y)`-dimensional manifold with corners.
* Gluing (`isSubMPolyfold_of_pieces`, `loc_of_pieces`): the pieces `S ∩ U_y` are open in `S`; a
  retraction for a piece restricted to `V ∩ U_y` is one for `S`; and the inclusion
  `S ∩ U_y → S` is an sc-diffeomorphism onto the open set `S ∩ U_y` (both directions are locally
  `i⁻¹ ∘ r ∘ i`, Proposition 2.21), so the corner charts of the pieces transport
  (`transportChart`) to corner charts of the induced structure of `S`.
* `IsManifoldWithCornersLoc` is `HasCornerStructure` (`hasCornerStructure_iff_finiteDimensional`);
  `S = ∅` is handled with the empty atlas.

**Refresh 2026-11-02 (germ reading at HEAD).**  A (`theorem_3_6_11_of_tangentGerm`) is unchanged.
B's `IsScFredholmSectionTame` now denotes the text's germ reading.  The chart change
`isGoodPositionGermTame_of_B` was repaired: the germ form of `isGoodPositionGerm_of_chart` needs a
germ through the centre of the non-centred chart, so the lemma now uses
`isGoodPositionGerm_of_linAt_surj`, whose hypotheses on `Lin(z) = D(f̂ ∘ r)(z)|_{T_zO}` are exactly
B's.  `theorem_3_6_8_two` (glue) is its germ form.  B ⇒ A still fails.
-/

namespace RoundTrip.V3_51
open Polyfold Set

/-- The project's statement: `theorem_3_6_11_of_tangentGerm`, universes at `0`. -/
def A : Prop := type_of% @Polyfold.theorem_3_6_11_of_tangentGerm.{0, 0}

theorem A_holds : A := @Polyfold.theorem_3_6_11_of_tangentGerm.{0, 0}

section Glue

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

/-! ### Every set is a solution set -/

/-- The fibre of the trivial bundle `X × ℝ → X` over `x` is `ℝ`. -/
def fibEquiv (x : X) : ↥((Prod.fst : X × ℝ → X) ⁻¹' {x}) ≃ ℝ where
  toFun p := p.1.2
  invFun r := ⟨(x, r), rfl⟩
  left_inv p := by
    obtain ⟨⟨a, b⟩, h⟩ := p
    simp only [mem_preimage, mem_singleton_iff] at h
    subst h
    rfl
  right_inv _ := rfl

/-- The fibrewise group structure of the trivial bundle. -/
@[instance_reducible] noncomputable def fibGroup : ∀ x : X, AddCommGroup ↥((Prod.fst : X × ℝ → X) ⁻¹' {x}) :=
  fun x => (fibEquiv x).addCommGroup

/-- A, applied to an arbitrary set `M` (the solution set of a section of `X × ℝ → X`). -/
theorem A_of_set (hA : A) {M : Set X} {n : ℕ} (hne : M.Nonempty)
    (hM : ∀ x ∈ M, ∃ d : PX.TangentGermChart M x n, d.IsRegular) :
    ∃ hsub : PX.IsSubMPolyfold M,
      haveI := PX.paracompactSpace_subtype M
      (MPolyfold.subPolyfold hsub).IsTame ∧ (MPolyfold.subPolyfold hsub).IsManifoldWithCorners n := by
  classical
  let _ := fibGroup (X := X)
  let f' : X → X × ℝ := fun y => (y, if y ∈ M then 0 else 1)
  have e : solutionSet (Prod.fst : X × ℝ → X) f' = M := by
    ext y
    change f' y = ((0 : ↥((Prod.fst : X × ℝ → X) ⁻¹' {y})) : X × ℝ) ↔ y ∈ M
    have h0 : ((0 : ↥((Prod.fst : X × ℝ → X) ⁻¹' {y})) : X × ℝ) = (y, 0) := rfl
    rw [h0]
    by_cases hy : y ∈ M <;> simp [f', hy]
  have h := hA (PX := PX) (P := (Prod.fst : X × ℝ → X)) (f := f') (n := n) (e ▸ hne) (e ▸ hM)
  have key : ∀ S : Set X, S = M → (∃ hsub : PX.IsSubMPolyfold S,
      haveI := PX.paracompactSpace_subtype S
      (MPolyfold.subPolyfold hsub).IsTame ∧ (MPolyfold.subPolyfold hsub).IsManifoldWithCorners n) →
      ∃ hsub : PX.IsSubMPolyfold M,
        haveI := PX.paracompactSpace_subtype M
        (MPolyfold.subPolyfold hsub).IsTame ∧
          (MPolyfold.subPolyfold hsub).IsManifoldWithCorners n := by
    rintro S rfl h
    exact h
  exact key _ e h

/-! ### Locality of sc-smoothness -/

theorem isScSmoothOn_of_locally {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
    {Q : MPolyfold Z} {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W]
    {R : MPolyfold W} {f : Z → W} {U : Set Z} (hU : IsOpen U)
    (h : ∀ z ∈ U, ∃ V : Set Z, IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧
      ∃ g : Z → W, Q.IsScSmoothOn R g V ∧ EqOn f g V) :
    Q.IsScSmoothOn R f U := by
  have hloc : ∀ z ∈ U, ∃ V : Set Z, IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧ Q.IsScSmoothOn R f V := by
    intro z hz
    obtain ⟨V, hV, hzV, hVU, g, hg, hfg⟩ := h z hz
    exact ⟨V, hV, hzV, hVU, hg.congr hfg.symm⟩
  have hcont : ContinuousOn f U := by
    refine continuousOn_of_locally_continuousOn fun z hz => ?_
    obtain ⟨V, hV, hzV, -, hfV⟩ := hloc z hz
    exact ⟨V, hV, hzV, hfV.continuousOn.mono inter_subset_right⟩
  refine MPolyfold.IsScSmoothOn.of_exists_charts hU hcont fun z hz => ?_
  obtain ⟨V, hV, hzV, hVU, hfV⟩ := hloc z hz
  obtain ⟨φ, hφ, hzφ⟩ := Q.exists_isChart_mem_source z
  obtain ⟨ψ, hψ, hfzψ⟩ := R.exists_isChart_mem_source (f z)
  have hV₀ : IsOpen ((V ∩ φ.source) ∩ f ⁻¹' ψ.source) :=
    (hfV.continuousOn.mono inter_subset_left).isOpen_inter_preimage (hV.inter φ.isOpen_source)
      ψ.isOpen_source
  exact ⟨φ, ψ, _, hφ, hψ, hV₀, ⟨⟨hzV, hzφ⟩, hfzψ⟩, fun x hx => ⟨hVU hx.1.1, hx.1.2⟩,
    fun x hx => hx.2, hfV.smooth φ ψ hφ hψ _ hV₀ (fun x hx => ⟨hx.1.1, hx.1.2⟩) fun x hx => hx.2⟩

/-! ### An open piece `S ∩ U` of a sub-M-polyfold `S` -/

variable {S : Set X}

/-- The inclusion `S ∩ U → S` is sc-smooth for the induced structures. -/
theorem inclusion_isScSmooth (hS : PX.IsSubMPolyfold S) {U : Set X}
    (hT : PX.IsSubMPolyfold (S ∩ U)) [ParacompactSpace S] [ParacompactSpace ↥(S ∩ U)] :
    (PX.subPolyfold hT).IsScSmoothOn (PX.subPolyfold hS)
      (Set.inclusion (inter_subset_left : S ∩ U ⊆ S)) univ := by
  refine isScSmoothOn_of_locally isOpen_univ fun t _ => ?_
  set d := hS.data t.2.1
  have hVo : IsOpen (Subtype.val ⁻¹' d.V : Set ↥(S ∩ U)) := d.isOpen.preimage continuous_subtype_val
  refine ⟨Subtype.val ⁻¹' d.V, hVo, hS.mem_data_V t.2.1, subset_univ _,
    d.retractInto ⟨t.1, t.2.1⟩ ∘ Subtype.val, ?_, fun t' ht' => ?_⟩
  · exact (MPolyfold.subPolyfold_retraction_isScSmooth hS d _).comp
      ((MPolyfold.subPolyfold_inclusion_isScSmooth hT).mono hVo (subset_univ _)) fun t' ht' => ht'
  · apply Subtype.ext
    change t'.1 = (d.retractInto ⟨t.1, t.2.1⟩ t'.1).1
    rw [d.retractInto_val _ ht', d.apply_eq_self ⟨t'.2.1, ht'⟩]

open scoped Classical in
/-- The inverse of the inclusion on the open set `S ∩ U ⊆ S` (junk value `t₀` elsewhere). -/
noncomputable def toPiece {U : Set X} (t₀ : ↥(S ∩ U)) (y : S) : ↥(S ∩ U) :=
  if h : y.1 ∈ U then ⟨y.1, y.2, h⟩ else t₀

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] in
lemma toPiece_of_mem {U : Set X} (t₀ : ↥(S ∩ U)) {y : S} (hy : y.1 ∈ U) :
    toPiece t₀ y = ⟨y.1, y.2, hy⟩ := by
  rw [toPiece, dif_pos hy]

theorem toPiece_isScSmooth (hS : PX.IsSubMPolyfold S) {U : Set X} (hU : IsOpen U)
    (hT : PX.IsSubMPolyfold (S ∩ U)) [ParacompactSpace S] [ParacompactSpace ↥(S ∩ U)]
    (t₀ : ↥(S ∩ U)) :
    (PX.subPolyfold hS).IsScSmoothOn (PX.subPolyfold hT) (toPiece t₀)
      (Subtype.val ⁻¹' U) := by
  have hUo : IsOpen (Subtype.val ⁻¹' U : Set S) := hU.preimage continuous_subtype_val
  refine isScSmoothOn_of_locally hUo fun y hy => ?_
  set d := hT.data (⟨y.2, hy⟩ : y.1 ∈ S ∩ U)
  have hVo : IsOpen (Subtype.val ⁻¹' U ∩ Subtype.val ⁻¹' d.V : Set S) :=
    hUo.inter (d.isOpen.preimage continuous_subtype_val)
  refine ⟨Subtype.val ⁻¹' U ∩ Subtype.val ⁻¹' d.V, hVo,
    ⟨hy, hT.mem_data_V (⟨y.2, hy⟩ : y.1 ∈ S ∩ U)⟩, inter_subset_left,
    d.retractInto t₀ ∘ Subtype.val, ?_, fun y' hy' => ?_⟩
  · exact (MPolyfold.subPolyfold_retraction_isScSmooth hT d t₀).comp
      ((MPolyfold.subPolyfold_inclusion_isScSmooth hS).mono hVo (subset_univ _))
      fun y' hy' => hy'.2
  · apply Subtype.ext
    change (toPiece t₀ y').1 = (d.retractInto t₀ y'.1).1
    rw [toPiece_of_mem t₀ hy'.1, d.retractInto_val _ hy'.2,
      d.apply_eq_self ⟨⟨y'.2, hy'.1⟩, hy'.2⟩]

/-- The inclusion `S ∩ U → S` is an sc-diffeomorphism onto the open set `S ∩ U` of `S`. -/
theorem piece_diffeo (hS : PX.IsSubMPolyfold S) {U : Set X} (hU : IsOpen U)
    (hT : PX.IsSubMPolyfold (S ∩ U)) [ParacompactSpace S] [ParacompactSpace ↥(S ∩ U)]
    (t₀ : ↥(S ∩ U)) :
    (PX.subPolyfold hS).IsScDiffeoOn (PX.subPolyfold hT) (toPiece t₀)
      (Set.inclusion (inter_subset_left : S ∩ U ⊆ S)) (Subtype.val ⁻¹' U) univ :=
  ⟨toPiece_isScSmooth hS hU hT t₀, inclusion_isScSmooth hS hT, mapsTo_univ _ _,
    fun t _ => t.2.2, fun y hy => by apply Subtype.ext; rw [Set.coe_inclusion, toPiece_of_mem t₀ hy],
    fun t _ => by rw [toPiece_of_mem t₀ t.2.2]⟩

/-- `S` is a sub-M-polyfold if it is one near each of its points. -/
theorem isSubMPolyfold_of_pieces
    (h : ∀ y ∈ S, ∃ U : Set X, IsOpen U ∧ y ∈ U ∧ PX.IsSubMPolyfold (S ∩ U)) :
    PX.IsSubMPolyfold S := by
  intro y hy
  obtain ⟨U, hU, hyU, hT⟩ := h y hy
  obtain ⟨V, hV, hyV, r, hmaps, hsm, hidem, himg⟩ := hT y ⟨hy, hyU⟩
  have hr : ∀ x ∈ V, r x ∈ (S ∩ U) ∩ V := fun x hx => himg ▸ ⟨x, hx, rfl⟩
  refine ⟨V ∩ U, hV.inter hU, ⟨hyV, hyU⟩, r, fun x hx => ⟨(hr x hx.1).2, (hr x hx.1).1.2⟩,
    hsm.mono (hV.inter hU) inter_subset_left, fun x hx => hidem x hx.1, ?_⟩
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(hr x hx.1).1.1, (hr x hx.1).2, (hr x hx.1).1.2⟩
  · rintro ⟨hzS, hzV, hzU⟩
    have : z ∈ r '' V := himg ▸ ⟨⟨hzS, hzU⟩, hzV⟩
    obtain ⟨w, hw, rfl⟩ := this
    exact ⟨r w, ⟨hmaps hw, hzU⟩, hidem w hw⟩

/-- The induced structure of `S` is a manifold with corners (of locally constant dimension) if
the induced structures of open pieces `S ∩ U` covering `S` are. -/
theorem loc_of_pieces (hS : PX.IsSubMPolyfold S) [ParacompactSpace S]
    (h : ∀ y ∈ S, ∃ (U : Set X) (_ : IsOpen U) (_ : y ∈ U) (hT : PX.IsSubMPolyfold (S ∩ U)),
      haveI := PX.paracompactSpace_subtype (S ∩ U)
      (PX.subPolyfold hT).IsManifoldWithCornersLoc) :
    (PX.subPolyfold hS).IsManifoldWithCornersLoc := by
  refine ⟨{ charts := {κ | (PX.subPolyfold hS).IsChart κ ∧
              IsRelOpenInQuadrant κ.model.E κ.model.C κ.model.O ∧ FiniteDimensional ℝ (κ.model.E 0)}
            compatible := fun φ hφ ψ hψ => MPolyfold.IsChart.compatible _ hφ.1 hψ.1
            cover := fun y => ?_ },
    (MAtlas.equiv_iff _ _).2 fun φ hφ ψ hψ => hφ.1 ψ hψ, fun φ hφ => hφ.2⟩
  obtain ⟨U, hU, hyU, hT, hloc⟩ := h y.1 y.2
  have := PX.paracompactSpace_subtype (S ∩ U)
  obtain ⟨A, hA, hcA⟩ := hloc
  let t : ↥(S ∩ U) := ⟨y.1, y.2, hyU⟩
  obtain ⟨χ, hχA, htχ⟩ := A.cover t
  have hχ := (PX.subPolyfold hT).isChart_of_mem_equiv hA hχA
  have hdiff := piece_diffeo hS hU hT t
  refine ⟨MPolyfold.transportChart hdiff χ, ⟨MPolyfold.transportChart_isChart hdiff hχ, ?_,
    (hcA χ hχA).2⟩, hyU, ?_⟩
  · change IsRelOpenInQuadrant χ.model.E χ.model.C (χ '' (univ ∩ χ.source))
    rw [univ_inter, χ.image_source]
    exact (hcA χ hχA).1
  · change toPiece t y ∈ χ.source
    rw [toPiece_of_mem t hyU]
    exact htχ

/-! ### B's hypotheses -/

variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- B's good position (sc-complement, cone `T ∩ C`) gives the project's (algebraic complement,
cone `C`). -/
theorem isInGoodPositionIn_of_sc {E : ScBanach} {T : Submodule ℝ (E 0)} {C : Set (E 0)}
    {N : Submodule ℝ (E 0)} (h : IsInGoodPositionSc E T ((T : Set (E 0)) ∩ C) N) :
    IsInGoodPositionIn E T C N := by
  obtain ⟨hNT, hint, Pc, hPT, -, hsplit, ε, hε, hgood⟩ := h
  have hpre : (Subtype.val ⁻¹' ((T : Set (E 0)) ∩ C) : Set N) = Subtype.val ⁻¹' C := by
    ext ⟨n, hn⟩
    simp only [Set.mem_preimage, Set.mem_inter_iff, SetLike.mem_coe]
    exact ⟨fun h => h.2, fun h => ⟨hNT hn, h⟩⟩
  have h0 := hsplit 0
  simp only [ScBanach.levelSub_zero] at h0
  refine ⟨hNT, hpre ▸ hint, Pc, hPT, h0.1, h0.2, ε, hε, fun n hn p hp hle => ?_⟩
  have h := hgood n hn p hp hle
  have hnT : n ∈ T := hNT hn
  have hnpT : n + p ∈ T := T.add_mem hnT (hPT hp)
  simp only [Set.mem_inter_iff, SetLike.mem_coe] at h
  exact ⟨fun hc => (h.1 ⟨hnT, hc⟩).2, fun hc => (h.2 ⟨hnpT, hc⟩).2⟩

/-- B's hypothesis at a zero gives the project's `IsGoodPositionGermTame` (germ reading): the
chart-change lemma `StrongBundle.isGoodPositionGerm_of_linAt_surj` (hypotheses on
`Lin(z) = D(f̂ ∘ r)(z)|_{T_zO}` in the not necessarily centred chart `c`; its kernel, pushed into
`E₀`, is `ker D(f̂ ∘ r)(z) ∩ T_zO`), then `IsGoodPositionGerm.toTame` with the tame germ data. -/
theorem isGoodPositionGermTame_of_B {Bd : StrongBundle PX P} {f : X → Y}
    (hf : Bd.IsScFredholmSectionTame f) {x : X} (hx : IsZeroAt P f x)
    (h : IsSurjGoodPosAt Bd f x) : Bd.IsGoodPositionGermTame f x := by
  obtain ⟨c, hct, hxV, z₁, hz, hsurj, n, W, Tp, hC, hgp⟩ := h
  have hxs : x ∈ PX.smoothSet := hf.mem_smoothSet_of_isZeroAt hx
  have hker : (LinearMap.ker (linAt c.U c.R (c.principal f) z₁ :
        ↥(rangeS (scDeriv c.U (StrongRetr.r c.R) z₁)) →ₗ[ℝ] c.F 0)).map
          (rangeS (scDeriv c.U (StrongRetr.r c.R) z₁)).subtype =
        LinearMap.ker (scDeriv c.U (c.principal f ∘ StrongRetr.r c.R) z₁ :
          c.φ.model.E 0 →ₗ[ℝ] c.F 0) ⊓ rangeS (scDeriv c.U (StrongRetr.r c.R) z₁) := by
    ext w
    simp only [Submodule.mem_inf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      Submodule.mem_map, Submodule.subtype_apply, linAt_apply]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨hv, v.2⟩
    · rintro ⟨hw, hwT⟩
      exact ⟨⟨w, hwT⟩, hw, rfl⟩
  refine (StrongBundle.isGoodPositionGerm_of_linAt_surj hf.isScSmooth (hf.germ x hxs) hx hct.1
    hxV hz Tp hC (fun k hk => ?_) (hker ▸ isInGoodPositionIn_of_sc hgp)).toTame hf.isScSmooth
    (hf.germTame x hxs) hx
  obtain ⟨v, hv, hvk⟩ := hsurj k hk
  exact ⟨⟨v, hv⟩, hvk⟩

/-- The local pieces: at every zero `y`, a chart domain `U ∋ y` on which `S ∩ U` has the regular
tangent germ property of one dimension (Theorem 3.54 (2), `theorem_3_6_8_two`). -/
theorem local_piece {Bd : StrongBundle PX P} {f : X → Y} (hfs : IsSection P f)
    (hall : ∀ x, IsZeroAt P f x → Bd.IsGoodPositionGermTame f x) {y : X}
    (hy : y ∈ solutionSet P f) :
    ∃ (U : Set X) (_ : IsOpen U) (_ : y ∈ U) (d : ℕ), ∀ z ∈ solutionSet P f ∩ U,
      ∃ D : PX.TangentGermChart (solutionSet P f ∩ U) z d, D.IsRegular := by
  obtain ⟨d, D, -, -, hdim⟩ := theorem_3_6_8_two hfs (hall y hy) hy isOpen_univ (mem_univ y)
    fun z _ hz => hall z hz
  refine ⟨D.φ.source, D.φ.isOpen_source, D.mem_source, d, fun z hz => ?_⟩
  obtain ⟨dz, Dz, hregz, hsubz, -⟩ := theorem_3_6_8_two hfs (hall z hz.1) hz.1 D.φ.isOpen_source
    hz.2 fun w _ hw => hall w hw
  have hdz : dz = d := hdim z hz dz Dz
  subst hdz
  have himage : Dz.φ '' ((solutionSet P f ∩ D.φ.source) ∩ Dz.φ.source) =
      (fun v : Dz.N => (v : Dz.φ.model.E 0) + Dz.δ v) '' Dz.V := by
    rw [← Dz.image_eq]
    congr 1
    ext w
    constructor
    · rintro ⟨⟨hw0, -⟩, hwsrc⟩; exact ⟨hw0, hwsrc⟩
    · rintro ⟨hw0, hwsrc⟩; exact ⟨⟨hw0, hsubz hwsrc⟩, hwsrc⟩
  exact ⟨Dz.shrink _ subset_rfl Dz.φ.isOpen_source Dz.mem_source Dz.V_relOpen Dz.zero_mem_V
    subset_rfl himage, Dz.shrink_isRegular _ subset_rfl Dz.φ.isOpen_source Dz.mem_source
    Dz.V_relOpen Dz.zero_mem_V subset_rfl himage hregz.isScSmooth hregz.π_mem⟩

/-- B's conclusion for an empty set: the empty atlas. -/
theorem empty_case {S : Set X} (hS : ¬ S.Nonempty) :
    ∃ (hsub : PX.IsSubMPolyfold S) (_ : ParacompactSpace S),
      (PX.subPolyfold hsub).HasCornerStructure := by
  have hsub : PX.IsSubMPolyfold S := fun a ha => absurd ⟨a, ha⟩ hS
  have hpc := PX.paracompactSpace_subtype S
  exact ⟨hsub, hpc, ⟨∅, fun φ hφ => absurd hφ (Set.notMem_empty φ), fun y => absurd ⟨y.1, y.2⟩ hS⟩,
      (MAtlas.equiv_iff _ _).2 fun φ hφ => absurd hφ (Set.notMem_empty φ),
      fun φ hφ => absurd hφ (Set.notMem_empty φ)⟩

end Glue

theorem A_to_B : A → B := by
  intro hA X _ _ _ PX Y _ _ _ P _ _ Bd f _ hf hgood
  have hall : ∀ x, IsZeroAt P f x → Bd.IsGoodPositionGermTame f x := fun x hx =>
    isGoodPositionGermTame_of_B hf hx (hgood x hx)
  have hfs : IsSection P f := hf.isScSmooth.1
  by_cases hne : (solutionSet P f).Nonempty
  · -- every point has an open piece which is, by A, a manifold with corners
    have hpieces : ∀ y ∈ solutionSet P f, ∃ (U : Set X) (_ : IsOpen U) (_ : y ∈ U)
        (hT : PX.IsSubMPolyfold (solutionSet P f ∩ U)),
        haveI := PX.paracompactSpace_subtype (solutionSet P f ∩ U)
        (PX.subPolyfold hT).IsManifoldWithCornersLoc := by
      intro y hy
      obtain ⟨U, hU, hyU, d, hreg⟩ := local_piece hfs hall hy
      obtain ⟨hT, -, hman⟩ := A_of_set (PX := PX) (M := solutionSet P f ∩ U) hA ⟨y, hy, hyU⟩ hreg
      have := PX.paracompactSpace_subtype (solutionSet P f ∩ U)
      exact ⟨U, hU, hyU, hT, hman.isManifoldWithCornersLoc⟩
    have hS : PX.IsSubMPolyfold (solutionSet P f) := isSubMPolyfold_of_pieces fun y hy => by
      obtain ⟨U, hU, hyU, hT, -⟩ := hpieces y hy
      exact ⟨U, hU, hyU, hT⟩
    have := PX.paracompactSpace_subtype (solutionSet P f)
    exact ⟨hS, inferInstance,
      MPolyfold.hasCornerStructure_iff_finiteDimensional.2 (loc_of_pieces hS hpieces)⟩
  · exact empty_case hne

#rt_check RoundTrip.V3_51.A_to_B [Polyfold.theorem_3_6_11_of_tangentGerm]

end RoundTrip.V3_51
