import Polyfold.Chapter5.Homotopy

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §5.3:
**Theorem 5.3.10 (preprint 5.18)** (perturbation into general position), **Theorem 5.3.12 (preprint 5.19)** (relative perturbation into
good position), **Theorem 5.25** (perturbation into good position), with the steps their proofs use
without proof: the solution set as a smooth submanifold (Definition 4.2.1 (preprint 4.13)), the chart independence
of Definition 5.3.9 (preprint 5.17), and the openness of general position *(book 2017: Theorems 5.6, 5.7; Theorem 5.25
is absent; see `BookConcordance.md`)*.

# General and good position

## The text, paraphrased

(Theorem 5.3.10 (preprint 5.18)) For a strong bundle over an M-polyfold admitting sc-smooth bump functions, an
sc-Fredholm section `f` with compact solution set and an auxiliary norm `N`, there is an open
`U ⊇ S_f` with `S_{f+s}` compact for `s ∈ Γ^{+,1}_U(P)`, and a dense set of `s ∈ Γ^{+,1}_U(P)` for
which `(f + s, x)` is in general position at every `x ∈ S_{f+s}`; then `S_{f+s}` is a compact
manifold with boundary with corners and `d_{S_{f+s}} = d_X`.  *Proof*: sections `s₁, …, s_m` such
that `F(λ, y) = f(y) + Σ λᵢ sᵢ(y)` satisfies at every `(0, x)`, `x ∈ S_f`: (i) `F'(0, x)` onto,
(ii) `ker F'(0, x)` transversal to `ℝᵐ ⊕ T^R_xX` (spanning sections, and sections spanning
`f'(x)L` for a complement `L` of `T^R_xX`); (i)–(ii) persist when sections are added and at nearby
zeros; by the implicit function theorem `S̃ = F⁻¹(0)` near `{0} × S_f` is a smooth manifold with
corners on which (i)–(ii) hold, and Theorem 4.3.1 (preprint 4.23) gives a full-measure set of `λ`.  (Theorem 5.3.12 (preprint 5.19))
If `(f, x)` is in good position at the zeros on `∂X`, an arbitrarily small `s` vanishing near
`∂X` makes `f + s` transversal and in good position everywhere.  (Theorem 5.25) For `X` tame and
`f` proper, some `s ∈ Γ^{+,1}_U(P)` puts `f + s` in good position at every zero; proof: Theorem
5.18 and Lemma 5.26.

## What is formalized

* **The bridge lemma** (`MPolyfold.TangentGermChart.exists_scPlusRetraction`,
  `exists_isScPlusRetractionOn`, `MPolyfold.isSmoothSubmanifold_of_isRegular`,
  `StrongBundle.isSmoothSubmanifold_solutionSet_inter`): regular data of Definition 3.2.1 (preprint 3.25) (2)
  (`IsRegular`) give an sc⁺-retraction `τ = Γ ∘ π ∘ r` onto the chart image (sc⁺ because `Γ` has a
  finite-dimensional domain, `isScPlus_of_isScSmooth_const`), so a solution set whose zeros are in
  good position is a smooth finite-dimensional submanifold in the sense of Definition 4.2.1 (preprint 4.13).
* **"`T_yS = ker f'(y)`" for the tangent spaces of Definition 4.2.1 (preprint 4.13)**
  (`exists_tangentSpace_eq_linKer`, from `tangentSpace_subset_linKer` and a dimension count:
  `dim ker Lin(z) = d` (`theorem_3_6_8_index`), `d` independent tangent vectors of the bridge
  retraction (`exists_linearIndependent_tangentSpace`) carried to every chart
  (`HasIndepTangent.transport`, `chart_change_of_transport`)).
* **Definition 5.3.9 (preprint 5.17) = Definition 4.2.10 (preprint 4.21) for the solution set** (`exists_isGeneralPositionGerm_iff`;
  the chart independence of Definition 5.3.9 (preprint 5.17)), **openness of general position along the solution
  set** for tame `X` (`exists_isOpen_isGeneralPositionGerm`, via Theorem 4.2.11 (preprint 4.22) (3)), locality of
  Definition 4.2.10 (preprint 4.21) (`IsGeneralPositionAt.congr_nhds`), and **submanifold general position + `f'(y)`
  onto ⟹ good position** (`isGoodPositionGermTame_of_isGeneralPositionAt`).
* **Properties (i)–(ii)** in a chart (`StrongBundleChart.IsParamGP`), preserved when sections are
  added (`IsParamGP.comp`), equivalent to the general position of `F` at `(0, y)`
  (`isGeneralPositionGerm_paramSection_of_isParamGP`, `isParamGP_of_isGeneralPositionGerm`), and
  achieved by finitely many allowable sections (`exists_sections_isParamGP`).
* **Theorem 5.3.10 (preprint 5.18)**: `theorem_5_3_10_of_family` (from a family with (i)–(ii)), `theorem_5_3_10_param` (generic
  form: for almost every small `λ` the conclusions `StrongBundle.SolutionSetInGeneralPosition`),
  `theorem_5_3_10_dense` (the text's dense form, with the pointwise distance `sectionDistAt`).
* **Theorem 5.25**: `theorem_5_25_preprint`.
* **Theorem 5.3.12 (preprint 5.19)**: `theorem_5_3_12_param` (generic form), with `IsGoodPositionGermTame.congr_nhds`.

## What the text leaves implicit, and the choices made

* **`X` tame** is added in Theorem 5.3.10 (preprint 5.18) (and 5.25 states it): the proof uses Theorems 4.2.11 and 4.3.1 (preprint 4.22 and 4.23).
  `f` has tame germ data (`IsScFredholmSectionTame`, Definition 3.6.4 (preprint 3.51)) as in Chapter 3.
* **`S̃` as a submanifold**: Theorem 4.3.1 (preprint 4.23) needs Definition 4.2.1 (preprint 4.13) (sc⁺-retractions), which the text
  never verifies for solution sets; the bridge lemma does.
* **Openness of (i)–(ii)** along `S̃` and at nearby `(0, y)` is used without proof; it is proved
  through `T_yS = ker f'(y)` and Theorem 4.2.11 (preprint 4.22) (3).
* **(i)–(ii) ⟹ general position** needs the good position of `F` first (an algebraic complement
  inside `T^R`), then `ker F'(0, x) = T S̃` (finite-dimensional, smooth) for the sc-complement.
* **Theorem 5.3.12 (preprint 5.19)**: the text's "as before" applies the implicit function theorem to `F` at the
  boundary zeros; there `F` is in general not in good position (`ℝᵐ × ker f'(x)` is in good position
  to `ℝᵐ × C_x` only if `ker f'(x) + E_x ⊇ T_xX`, a general-position condition).  The proof here
  uses the implicit function theorem for `F` only at interior points, and `f + s = f` near the
  boundary zeros.  Tameness of `X` is not used.
* "Dense" and "generic" are read as in Theorem 5.3.5 (preprint 5.13) (pointwise distance; "outside a null set").
* Not formalized: the metric space `(Γ^{+,1}_U(P), ρ)`; a dense form of Theorem 5.3.12 (preprint 5.19) (the generic
  form gives sections `Σ λᵢ tᵢ` with `λ` arbitrarily small).
-/

open Set Filter Topology Function Module ContinuousLinearMap MeasureTheory
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

/-! ### A map on a finite-dimensional constant domain is sc⁺ -/

section ScPlusConst

/-- **An sc-smooth map from a finite-dimensional space with the constant structure is sc⁺**: all
levels of the domain coincide, so `f : U → F_{m+1}` is `C^∞` for every `m` and the lift
`1₀¹ ∘ f : U → F¹` is sc-smooth (the step "`δ` has a finite-dimensional domain" of the bridge
lemma). -/
theorem isScPlus_of_isScSmooth_const {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {F : ScBanach} {U : Set V}
    (hU : IsScDomain (ScBanach.const V) U) {f : V → F 0}
    (hf : IsScSmooth (E := ScBanach.const V) U f) : IsScPlus (E := ScBanach.const V) U f := by
  have hinclK : ∀ m k (x : V), (ScBanach.const V).inclK m k x = x := fun m k x => by
    have h1 := (ScBanach.const V).toBase_inclK m k x
    rwa [ScBanach.const_toBase, ScBanach.const_toBase] at h1
  have hmem : ∀ m, ∀ x ∈ U, f x ∈ range (F.toBase m) := fun m x hx => by
    have := hf.isSc1.isSc0.mem_range m x (by rw [ScBanach.lvlSet_const]; exact hx)
    rwa [ScBanach.const_toBase] at this
  refine ⟨fun x hx => hmem 1 x hx, ?_⟩
  refine IsScSmooth.of_contDiffOn_levels hU (fun m x hx => ?_) (fun m => ?_)
  · rw [ScBanach.lvlSet_const] at hx
    obtain ⟨y, hy⟩ := hmem (m + 1) _ hx
    refine ⟨y, ?_⟩
    rw [Function.comp_apply, ScBanach.const_toBase] at *
    symm
    rw [F.liftOne_eq_iff (hmem 1 _ hx), ← F.shift_toBase]
    exact hy
  · rw [ScBanach.lvlSet_const]
    have hcd : ContDiffOn ℝ ∞ (levelMap (E := ScBanach.const V) f (m + 1)) U := by
      rw [contDiffOn_infty]
      intro k
      have := hf.contDiffOn_levels hU (m + 1) k
      rw [ScBanach.lvlSet_const] at this
      exact this.congr fun x _ => by simp only [Function.comp_apply, hinclK]
    refine hcd.congr fun x hx => ?_
    apply levelMap_eq_of_toBase_eq
    rw [Function.comp_apply, ScBanach.const_toBase]
    symm
    rw [F.liftOne_eq_iff (hmem 1 _ hx), ← F.shift_toBase]
    have h1 := toBase_levelMap (E := ScBanach.const V) (F := F) (f := f) (m := m + 1) (x := x)
      (by rw [ScBanach.const_toBase]; exact hmem (m + 1) x hx)
    rw [ScBanach.const_toBase] at h1
    exact h1

end ScPlusConst

/-! ### The bridge lemma: regular tangent germ data give an sc⁺-retraction -/

namespace MPolyfold.TangentGermChart

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {M : Set X} {x : X} {n : ℕ} (d : P.TangentGermChart M x n)

/-- The graph map `Γ = ι + δ : V → E` is sc⁺ (its domain is finite-dimensional). -/
theorem Γ_isScPlus (hreg : d.IsRegular) : IsScPlus (E := ScBanach.const d.N) d.V d.Γ :=
  isScPlus_of_isScSmooth_const d.V_isRelOpenInQuadrant.isScDomain (d.Γ_isScSmooth hreg)

/-- **The sc⁺-retraction of the bridge lemma, in the chart**: for regular data of Definition 3.2.1 (preprint 3.25)
(2) (`IsRegular`) and a retraction `r` onto the model `O`, the map `τ = t ∘ r = Γ ∘ π ∘ r` on
`{z ∈ dom r | π(r z) ∈ V}` is an **sc⁺-retraction** (`Γ` is sc⁺ on the finite-dimensional `V`,
`π ∘ r` sc-smooth into `N`) with retract in `O`; `φ(x) = 0` lies in its domain, and a point `φ(y)`
of the chart image lies in its retract iff `y ∈ M` and `φ(y)` lies in its domain. -/
theorem exists_scPlusRetraction (hreg : d.IsRegular) :
    ∃ τ : ScRetraction d.φ.model.E d.φ.model.C, τ.IsScPlus ∧ τ.retract ⊆ d.φ.model.O ∧
      d.φ x ∈ τ.U ∧
      (∀ y ∈ d.φ.source, d.φ y ∈ τ.retract ↔ y ∈ M ∧ d.φ y ∈ τ.U) ∧
      ∀ v ∈ d.V, d.Γ v ∈ τ.U ∧ τ (d.Γ v) = d.Γ v := by
  obtain ⟨R, hR⟩ := d.φ.model.isScRetract
  obtain ⟨OV, hOV, hVeq⟩ := d.V_relOpen
  have hcont : ContinuousOn (fun z => d.π (R z)) R.U :=
    d.π.continuous.comp_continuousOn R.isScSmooth.isSc1.isSc0.continuousOn_base
  obtain ⟨G, hGo, hG⟩ := (continuousOn_iff'.1 hcont) OV hOV
  obtain ⟨O', hO', hRU⟩ := R.relOpen.relOpen
  set U₁ := R.U ∩ (fun z => d.π (R z)) ⁻¹' OV with hU₁
  have hU₁rel : IsRelOpenInQuadrant d.φ.model.E d.φ.model.C U₁ := by
    refine ⟨R.relOpen.isPartialQuadrant, O' ∩ G, hO'.inter hGo, ?_⟩
    rw [hU₁, inter_comm R.U, hG, hRU]
    ext z; simp only [mem_inter_iff]; tauto
  have hRO : ∀ z ∈ R.U, R z ∈ d.φ.model.O := fun z hz => hR ▸ R.apply_mem_retract hz
  have hOU : ∀ z ∈ d.φ.model.O, z ∈ R.U := fun z hz => R.retract_subset (hR ▸ hz)
  have hRfix : ∀ z ∈ d.φ.model.O, R z = z := fun z hz => R.apply_eq_self_of_mem_retract (hR ▸ hz)
  have hV : ∀ z ∈ U₁, d.π (R z) ∈ d.V := fun z hz => by
    rw [hVeq]; exact ⟨hz.2, hreg.π_mem _ (hRO z hz.1)⟩
  have hπR : IsScSmooth (F := ScBanach.const d.N) U₁ (d.π ∘ R) :=
    (IsScSmooth.comp R.isScDomain (isScDomain_univ _) d.π_isScSmooth R.isScSmooth
      (mapsTo_univ _ _)).of_subset hU₁rel.isScDomain inter_subset_left
  have hmapsV : MapsTo (d.π ∘ R) U₁ d.V := fun z hz => hV z hz
  have hΓ : ∀ z ∈ U₁, d.Γ (d.π (R z)) ∈ U₁ := fun z hz => by
    have hO := d.Γ_mem_O (hV z hz)
    refine ⟨hOU _ hO, ?_⟩
    change d.π (R (d.Γ (d.π (R z)))) ∈ OV
    rw [hRfix _ hO, d.π_Γ]
    exact hz.2
  let τ : ScRetraction d.φ.model.E d.φ.model.C :=
    { U := U₁
      toFun := fun z => d.Γ (d.π (R z))
      relOpen := hU₁rel
      mapsTo := fun z hz => hΓ z hz
      isScSmooth := IsScSmooth.comp hU₁rel.isScDomain d.V_isRelOpenInQuadrant.isScDomain
        (d.Γ_isScSmooth hreg) hπR hmapsV
      idem := fun z hz => by
        show d.Γ (d.π (R (d.Γ (d.π (R z))))) = d.Γ (d.π (R z))
        rw [hRfix _ (d.Γ_mem_O (hV z hz)), d.π_Γ] }
  have hτO : τ.retract ⊆ d.φ.model.O := by
    rintro _ ⟨z, hz, rfl⟩; exact d.Γ_mem_O (hV z hz)
  refine ⟨τ, ?_, hτO, ?_, fun y hy => ⟨fun h => ?_, fun h => ?_⟩, fun v hv => ?_⟩
  · exact IsScPlus.comp_isScSmooth (E := d.φ.model.E) (F := ScBanach.const d.N)
      hU₁rel.isScDomain d.V_isRelOpenInQuadrant.isScDomain (d.Γ_isScPlus hreg) hπR hmapsV
  · have h0O : d.φ x ∈ d.φ.model.O := d.φ.mapsTo_model x d.mem_source
    refine ⟨hOU _ h0O, ?_⟩
    change d.π (R (d.φ x)) ∈ OV
    rw [hRfix _ h0O, d.φ_zero, map_zero]
    have := d.zero_mem_V
    rw [hVeq] at this
    exact this.1
  · obtain ⟨z, hz, hzy⟩ := h
    have hzy' : d.Γ (d.π (R z)) = d.φ y := hzy
    have hyM : d.φ.symm (d.Γ (d.π (R z))) ∈ M ∩ d.φ.source := d.symm_Γ_mem (hV z hz)
    rw [hzy', d.φ.symm_apply_apply hy] at hyM
    exact ⟨hyM.1, τ.retract_subset ⟨z, hz, hzy⟩⟩
  · obtain ⟨hyM, hyU⟩ := h
    refine ⟨d.φ y, hyU, ?_⟩
    change d.Γ (d.π (R (d.φ y))) = d.φ y
    rw [hRfix _ (d.φ.mapsTo_model y hy)]
    exact (d.exists_eq_Γ ⟨hyM, hy⟩).2.symm
  · have hO := d.Γ_mem_O hv
    have hU : d.Γ v ∈ U₁ := by
      refine ⟨hOU _ hO, ?_⟩
      change d.π (R (d.Γ v)) ∈ OV
      rw [hRfix _ hO, d.π_Γ]
      rw [hVeq] at hv; exact hv.1
    refine ⟨hU, ?_⟩
    show d.Γ (d.π (R (d.Γ v))) = d.Γ v
    rw [hRfix _ hO, d.π_Γ]

/-- **The tangent space of `M` along the graph has dimension at least `n`**: for a retraction `τ`
of the model (`exists_scPlusRetraction`) with `τ ∘ Γ = Γ` on `V`, at the level-`1` point `y` over
`Γ(v)` the tangent space `T_y τ(U)` contains the `n` linearly independent vectors `DΓ(v)bᵢ`
(`bᵢ` a basis of `N`): `Dτ(y) DΓ(v) = D(τ ∘ Γ)(v) = DΓ(v)` and `π ∘ DΓ(v) = 1`. -/
theorem exists_linearIndependent_tangentSpace (hreg : d.IsRegular)
    (τ : ScRetraction d.φ.model.E d.φ.model.C) (hτΓ : ∀ v ∈ d.V, d.Γ v ∈ τ.U ∧ τ (d.Γ v) = d.Γ v)
    {v : d.N} (hv : v ∈ d.V) {y : d.φ.model.E 1} (hy : d.φ.model.E.toBase 1 y = d.Γ v) :
    ∃ L : Fin n → d.φ.model.E 0, LinearIndependent ℝ L ∧
      ∀ i, L i ∈ tangentSpace d.φ.model.E d.φ.model.C τ.retract y := by
  have hVrel := d.V_isRelOpenInQuadrant
  have hΓs := d.Γ_isScSmooth hreg
  have hyR : y ∈ d.φ.model.E.lvlSet τ.retract 1 := by
    rw [ScBanach.mem_lvlSet, hy, ← (hτΓ v hv).2]; exact τ.apply_mem_retract (hτΓ v hv).1
  have hv1 : v ∈ (ScBanach.const d.N).lvlSet d.V 1 := by rw [ScBanach.lvlSet_const]; exact hv
  have hmaps : MapsTo d.Γ d.V τ.U := fun w hw => (hτΓ w hw).1
  -- `τ ∘ Γ = Γ` on `V`
  have hτΓeq : EqOn (τ ∘ d.Γ) d.Γ d.V := fun w hw => (hτΓ w hw).2
  have hcomp1 : IsSc1 (E := ScBanach.const d.N) d.V (τ ∘ d.Γ) :=
    (theorem_1_3_1 hVrel τ.relOpen hΓs.isSc1 τ.isSc1 hmaps).1
  have hlev : levelMap (E := ScBanach.const d.N) d.Γ 1 v = y :=
    levelMap_eq_of_toBase_eq (by rw [hy, ScBanach.const_toBase])
  have hD : ∀ h : d.N, scDeriv τ.U τ y (scDeriv (E := ScBanach.const d.N) d.V d.Γ v h) =
      scDeriv (E := ScBanach.const d.N) d.V d.Γ v h := fun h => by
    have h1 := scDeriv_comp_apply' hVrel τ.relOpen hΓs.isSc1 τ.isSc1 hmaps hv1 h
    rw [hlev] at h1
    rw [h1, scDeriv_eq_of_eqOn_relOpen hVrel hcomp1 hΓs.isSc1 subset_rfl subset_rfl hτΓeq hv1]
  -- `π ∘ DΓ(v) = 1`
  have hπD : ∀ h : d.N, d.π (scDeriv (E := ScBanach.const d.N) d.V d.Γ v h) = h := by
    have d1 := hΓs.isSc1.isSc1With_scDeriv.hasFDerivWithinAt v hv1
    have d2 := d.π.hasFDerivAt.comp_hasFDerivWithinAt v d1
    have d3 : HasFDerivWithinAt (fun w : (ScBanach.const d.N) 1 => w)
        (ContinuousLinearMap.id ℝ d.N) ((ScBanach.const d.N).lvlSet d.V 1) v :=
      hasFDerivWithinAt_id v _
    have d2' : HasFDerivWithinAt (fun w : (ScBanach.const d.N) 1 => w)
        (d.π.comp ((scDeriv (E := ScBanach.const d.N) d.V d.Γ v).comp
          ((ScBanach.const d.N).toBase 1))) ((ScBanach.const d.N).lvlSet d.V 1) v := by
      refine d2.congr (fun w hw => ?_) ?_
      · rw [ScBanach.lvlSet_const] at hw
        simp only [Function.comp_apply]
        exact (d.π_Γ w).symm
      · simp only [Function.comp_apply]
        exact (d.π_Γ v).symm
    have huniq := (hVrel.isScDomain.uniqueDiffWithinAt 1 v hv1).eq d2' d3
    intro h
    have := congrArg (fun T : d.N →L[ℝ] d.N => T h) huniq
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_id',
      id_eq] at this
    rwa [ScBanach.constScale_toBase] at this
  set b := Module.finBasisOfFinrankEq ℝ d.N d.finrank_eq with hb
  refine ⟨fun i => scDeriv (E := ScBanach.const d.N) d.V d.Γ v (b i), ?_, fun i => ?_⟩
  · refine LinearIndependent.of_comp (d.π : d.φ.model.E 0 →ₗ[ℝ] d.N) ?_
    have : (d.π : d.φ.model.E 0 →ₗ[ℝ] d.N) ∘
        (fun i => scDeriv (E := ScBanach.const d.N) d.V d.Γ v (b i)) = b := by
      funext i; exact hπD (b i)
    rw [this]; exact b.linearIndependent
  · rw [tangentSpace_eq_range τ hyR]
    exact ⟨_, hD (b i)⟩

/-- **The bridge lemma** (Theorem 3.2.3 (preprint 3.27)'s retraction is sc⁺; Definition 4.2.1 (preprint 4.13) from Definition 3.2.1 (preprint 3.25)):
regular data of Definition 3.2.1 (preprint 3.25) (2) for `M` at `x` give an open `V ∋ x` inside the chart domain and
an **sc⁺-retraction** `s : V → V` (Definition 4.1.4 (preprint 4.4)) with `s(V) = M ∩ V`: `s = φ⁻¹ ∘ τ ∘ φ` for the
sc⁺-retraction `τ = Γ ∘ π ∘ r` of `exists_scPlusRetraction` (`isScPlusRetractionOn_of_chart`). -/
theorem exists_isScPlusRetractionOn (hreg : d.IsRegular) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ d.φ.source ∧
      ∃ s : X → X, P.IsScPlusRetractionOn s V ∧ s '' V = M ∩ V := by
  obtain ⟨τ, hτ, hτO, hxτ, hiff, -⟩ := d.exists_scPlusRetraction hreg
  obtain ⟨hVo, hs, himg⟩ := MPolyfold.isScPlusRetractionOn_of_chart d.isChart τ hτ hτO
  refine ⟨d.φ.source ∩ d.φ ⁻¹' τ.U, hVo, ⟨d.mem_source, hxτ⟩, inter_subset_left,
    d.φ.symm ∘ τ ∘ d.φ, hs, ?_⟩
  rw [himg]
  ext y
  constructor
  · rintro ⟨hy, hyτ⟩
    exact ⟨((hiff y hy).1 hyτ).1, hy, ((hiff y hy).1 hyτ).2⟩
  · rintro ⟨hyM, hy, hyU⟩
    exact ⟨hy, (hiff y hy).2 ⟨hyM, hyU⟩⟩

end MPolyfold.TangentGermChart

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- **A set with regular tangent germ data at every point is a smooth finite-dimensional
submanifold** (Definition 4.2.1 (preprint 4.13)): the bridge lemma at every point. -/
theorem isSmoothSubmanifold_of_isRegular {M : Set X}
    (hM : ∀ x ∈ M, ∃ n, ∃ d : P.TangentGermChart M x n, d.IsRegular) :
    P.IsSmoothSubmanifold M := by
  intro a ha
  obtain ⟨n, d, hreg⟩ := hM a ha
  obtain ⟨V, hVo, haV, -, s, hs, himg⟩ := d.exists_isScPlusRetractionOn hreg
  exact ⟨V, hVo, haV, s, hs, himg⟩

/-- **Definition 4.2.10 (preprint 4.21) is local**: if two smooth finite-dimensional submanifolds agree near `a`
(`A ∩ G = A' ∩ G`, `G` open), general position of `A` at `a` gives that of `A'` (the tangent
spaces of the chart models agree, `tangentSpace_inter_isOpen`). -/
theorem IsGeneralPositionAt.congr_nhds {A A' : Set X} (hA : P.IsSmoothSubmanifold A)
    (hA' : P.IsSmoothSubmanifold A') {a : X} {G : Set X} (hG : IsOpen G) (haG : a ∈ G)
    (hAG : A ∩ G = A' ∩ G) (h : P.IsGeneralPositionAt A a) : P.IsGeneralPositionAt A' a := by
  have haA : a ∈ A := h.1
  have haA' : a ∈ A' := by
    have : a ∈ A' ∩ G := hAG ▸ ⟨haA, haG⟩
    exact this.1
  refine (isGeneralPositionAt_iff_forall hA' haA').2
    fun d' φ hφ n Wq T hT z ha' haφ hz => ?_
  set d := hA.data haA with hd
  have hgp := h.isGeneralPositionChart d hφ T hT (hA.mem_data_V haA) haφ hz
  set H := d.toSubData.shrink φ ∩ d'.toSubData.shrink φ ∩ G with hH
  have hHo : IsOpen H :=
    ((d.toSubData.isOpen_shrink φ).inter (d'.toSubData.isOpen_shrink φ)).inter hG
  have hHsrc : H ⊆ φ.source := fun x hx => d.toSubData.shrink_subset_source φ hx.1.1
  obtain ⟨K, hKo, hK⟩ := φ.exists_isOpen_image_eq hHsrc hHo
  have haH : a ∈ H := ⟨⟨d.toSubData.mem_shrink φ haA (hA.mem_data_V haA) haφ,
    d'.toSubData.mem_shrink φ haA' ha' haφ⟩, haG⟩
  have hQ := d.toSubData.isScRetract_image φ hφ
  have hQ' := d'.toSubData.isScRetract_image φ hφ
  have e1 : φ '' (H ∩ A) = φ '' (d.toSubData.shrink φ ∩ A) ∩ K :=
    φ.image_inter_eq_inter (d.toSubData.shrink_subset_source φ) (fun x hx => hx.1.1) hK
  have e2 : φ '' (H ∩ A') = φ '' (d'.toSubData.shrink φ ∩ A') ∩ K :=
    φ.image_inter_eq_inter (d'.toSubData.shrink_subset_source φ) (fun x hx => hx.1.2) hK
  have e3 : H ∩ A = H ∩ A' := by
    ext x; constructor
    · rintro ⟨hxH, hxA⟩
      have : x ∈ A' ∩ G := hAG ▸ ⟨hxA, hxH.2⟩
      exact ⟨hxH, this.1⟩
    · rintro ⟨hxH, hxA'⟩
      have : x ∈ A ∩ G := hAG.symm ▸ ⟨hxA', hxH.2⟩
      exact ⟨hxH, this.1⟩
  have hφaK : φ a ∈ K := by
    have : φ a ∈ φ '' H := ⟨a, haH, rfl⟩
    rw [hK] at this; exact this.2
  have hzQ : φ.model.E.toBase 1 z ∈ φ '' (d.toSubData.shrink φ ∩ A) ∩ K :=
    ⟨by rw [hz]; exact ⟨a, ⟨haH.1.1, haA⟩, rfl⟩, by rw [hz]; exact hφaK⟩
  have hzQ' : φ.model.E.toBase 1 z ∈ φ '' (d'.toSubData.shrink φ ∩ A') ∩ K :=
    ⟨by rw [hz]; exact ⟨a, ⟨haH.1.2, haA'⟩, rfl⟩, by rw [hz]; exact hφaK⟩
  have hT1 := tangentSpace_inter_isOpen hQ hKo hzQ
  have hT2 := tangentSpace_inter_isOpen hQ' hKo hzQ'
  rw [← e1] at hT1
  rw [← e2, ← e3] at hT2
  exact hgp.congr (hT1.symm.trans hT2) rfl

end MPolyfold

/-! ### The tangent space of a sub-retract: `n` independent vectors, carried by chart changes -/

section IndepTangent

/-- **The tangent space `T_zQ` contains `n` linearly independent vectors** (a chart-independent
lower bound for `dim T_aA`, `chart_change_of_transport`). -/
def HasIndepTangent (n : ℕ) (E : ScBanach) (C Q : Set (E 0)) (z : E 1) : Prop :=
  ∃ L : Fin n → E 0, LinearIndependent ℝ L ∧ ∀ i, L i ∈ tangentSpace E C Q z

variable {E E' : ScBanach} {C : Set (E 0)} {C' : Set (E' 0)}

/-- `HasIndepTangent` is carried by germs of sc-diffeomorphisms: `D(F ∘ r)(z)` maps `T_zQ` into
`T_{F(z)}Q'` and is injective on `T_zO` (`D(G ∘ r')D(F ∘ r) = Dr(z) = 1` there). -/
theorem HasIndepTangent.transport {n : ℕ} {R : ScRetraction E C} {R' : ScRetraction E' C'}
    {F : E 0 → E' 0} {G : E' 0 → E 0} (h : R.IsDiffeoGerm R' F G)
    (hFs : IsScSmooth R.U (F ∘ R)) {Q : Set (E 0)} {Q' : Set (E' 0)}
    (hQ : IsScRetract E C Q) (hQ' : IsScRetract E' C' Q') (hQR : Q ⊆ R.retract)
    (hFQ : MapsTo F Q Q') {z : E 1} (hz : z ∈ E.lvlSet Q 1)
    (hind : HasIndepTangent n E C Q z) :
    HasIndepTangent n E' C' Q' (levelMap (F ∘ R) 1 z) := by
  obtain ⟨L, hL, hLQ⟩ := hind
  have hzR : z ∈ E.lvlSet R.retract 1 := hQR hz
  refine ⟨fun i => scDeriv R.U (F ∘ R) z (L i), ?_, fun i =>
    scDeriv_mem_tangentSpace_of_subset R hFs hQ hQ' hQR hFQ hz (hLQ i)⟩
  set A' : E' 0 →ₗ[ℝ] E 0 :=
    (scDeriv R'.U (G ∘ R') (levelMap (F ∘ R) 1 z) : E' 0 →ₗ[ℝ] E 0) with hA'
  refine LinearIndependent.of_comp A' ?_
  have : A' ∘ (fun i => scDeriv R.U (F ∘ R) z (L i)) = L := by
    funext i
    change scDeriv R'.U (G ∘ R') (levelMap (F ∘ R) 1 z) (scDeriv R.U (F ∘ R) z (L i)) = L i
    rw [h.deriv_inv_deriv hzR]
    have hLi : L i ∈ tangentSpace E C R.retract z :=
      tangentSpace_subset_of_subset R hQ hQR hz (hLQ i)
    rw [tangentSpace_eq_range R hzR] at hLi
    obtain ⟨w, hw⟩ := hLi
    rw [← hw]
    exact congrArg (fun T : E 0 →L[ℝ] E 0 => T w) (R.scDeriv_comp_self hzR)
  rw [this]; exact hL

end IndepTangent

/-! ### The solution set: a smooth submanifold, and its tangent space is the kernel -/

section SolutionSet

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

open StrongRetr

/-- **The bridge lemma for solution sets**: if every zero of the section `f` in the open set `W` is
in good position in a tame chart, then `S_f ∩ W` is a **smooth finite-dimensional submanifold**
(Definition 4.2.1 (preprint 4.13)): Theorem 3.6.8 (preprint 3.54) (2) (`theorem_3_6_8_two`) gives regular data of Definition 3.2.1 (preprint 3.25) (2)
of `S_f` at every zero, on a chart inside `W`, and the bridge lemma
(`TangentGermChart.exists_isScPlusRetractionOn`) the sc⁺-retraction. -/
theorem StrongBundle.isSmoothSubmanifold_solutionSet_inter (hf : IsSection P f) {W : Set X}
    (hW : IsOpen W) (hall : ∀ y ∈ W, IsZeroAt P f y → B.IsGoodPositionGermTame f y) :
    PX.IsSmoothSubmanifold (solutionSet P f ∩ W) := by
  intro a ha
  obtain ⟨d, D, hreg, hsub, -⟩ := theorem_3_6_8_two hf (hall a ha.2 ha.1) ha.1 hW ha.2 hall
  obtain ⟨V, hVo, haV, hVsrc, s, hs, himg⟩ := D.exists_isScPlusRetractionOn hreg
  refine ⟨V, hVo, haV, s, hs, ?_⟩
  rw [himg]
  ext y
  constructor
  · rintro ⟨hyS, hyV⟩; exact ⟨⟨hyS, hsub (hVsrc hyV)⟩, hyV⟩
  · rintro ⟨⟨hyS, -⟩, hyV⟩; exact ⟨hyS, hyV⟩

omit [T2Space Y] [ParacompactSpace Y] in
/-- Membership in the kernel of the linearization, as a subspace of `E₀`. -/
lemma StrongBundleChart.mem_linKer_iff (c : StrongBundleChart PX P) (f : X → Y)
    (z : c.φ.model.E 1) (v : c.φ.model.E 0) :
    v ∈ c.linKer f z ↔ ∃ hv : v ∈ rangeS (scDeriv c.U (r c.R) z),
      linAt c.U c.R (c.principal f) z ⟨v, hv⟩ = 0 := by
  unfold StrongBundleChart.linKer
  constructor
  · rintro ⟨w, hw, rfl⟩; exact ⟨w.2, hw⟩
  · rintro ⟨hv, h⟩; exact ⟨⟨v, hv⟩, h, rfl⟩

/-- **The tangent space of a sub-retract of the zero set lies in the kernel of the linearization**
(the easy half of "`T_yS = ker f'(y)`"): in a strong bundle chart, for a retract `Q ⊆ O` on which
the principal part `f̂` vanishes, `T_zQ ⊆ ker Lin(z)` at every level-`1` point `z` of `Q`:
`T_zQ = range DS(z)` for a retraction `S` onto `Q`, `T_zQ ⊆ T_zO`, and `f̂ ∘ r ∘ S = 0` gives
`D(f̂ ∘ r)(z) ∘ DS(z) = 0` (chain rule). -/
theorem tangentSpace_subset_linKer (hf : B.IsScSmoothSection f) {c : StrongBundleChart PX P}
    (hc : B.IsChart c) {Q : Set (c.φ.model.E 0)} (hQ : IsScRetract c.φ.model.E c.φ.model.C Q)
    (hQO : Q ⊆ c.φ.model.O) (hQ0 : ∀ u ∈ Q, c.principal f u = 0) {z : c.φ.model.E 1}
    (hz : z ∈ c.φ.model.E.lvlSet Q 1) :
    tangentSpace c.φ.model.E c.φ.model.C Q z ⊆ c.linKer f z := by
  intro v hv
  have hQ' := hQ
  obtain ⟨S, rfl⟩ := hQ
  have hRb := c.base_retract
  have hvO : v ∈ tangentSpace c.φ.model.E c.φ.model.C
      (c.isRetraction.baseRetraction c.relOpen).retract z :=
    tangentSpace_subset_of_subset (c.isRetraction.baseRetraction c.relOpen) hQ'
      (by rw [hRb]; exact hQO) hz hv
  have hzO : z ∈ c.φ.model.E.lvlSet (c.isRetraction.baseRetraction c.relOpen).retract 1 := by
    rw [ScBanach.mem_lvlSet, hRb]; exact hQO hz
  rw [tangentSpace_eq_coe_submodule _ hzO] at hvO
  rw [tangentSpace_eq_range S hz] at hv
  obtain ⟨w, rfl⟩ := hv
  refine (c.mem_linKer_iff f z _).2 ⟨hvO, ?_⟩
  rw [linAt_apply]
  have hmaps : MapsTo S S.U c.U := fun u hu =>
    mem_U_of_mem_O c.isRetraction (c.r_image ▸ hQO (S.apply_mem_retract hu))
  have hfr : IsSc1 c.U (c.principal f ∘ r c.R) := hf.isSc1_principal_comp_r hc
  have hzU : z ∈ c.φ.model.E.lvlSet S.U 1 := S.lvlSet_retract_subset 1 hz
  have hch := scDeriv_comp_apply' S.relOpen c.relOpen S.isSc1 hfr hmaps hzU w
  rw [S.levelMap_one_eq_self hz] at hch
  change scDeriv c.U (c.principal f ∘ r c.R) z (scDeriv S.U S z w) = 0
  rw [hch]
  have hzero : EqOn ((c.principal f ∘ r c.R) ∘ S) (fun _ => 0) S.U := fun u hu => by
    have hSu : S u ∈ c.φ.model.O := hQO (S.apply_mem_retract hu)
    simp only [Function.comp_apply]
    rw [r_eq_self c.isRetraction (c.r_image ▸ hSu)]
    exact hQ0 _ (S.apply_mem_retract hu)
  obtain ⟨hcomp, -⟩ := theorem_1_3_1 S.relOpen c.relOpen S.isSc1 hfr hmaps
  have d1 := hcomp.isSc1With_scDeriv.hasFDerivWithinAt z hzU
  have d2 : HasFDerivWithinAt (((c.principal f ∘ r c.R) ∘ S) ∘ c.φ.model.E.toBase 1)
      ((0 : c.φ.model.E 0 →L[ℝ] c.F 0).comp (c.φ.model.E.toBase 1))
      (c.φ.model.E.lvlSet S.U 1) z := by
    rw [ContinuousLinearMap.zero_comp]
    exact (hasFDerivWithinAt_const (0 : c.F 0) z _).congr (fun y hy => hzero hy) (hzero hzU)
  have := ContinuousLinearMap.ext_of_comp_toBase_one
    ((S.isScDomain.uniqueDiffWithinAt 1 z hzU).eq d1 d2)
  rw [this]; rfl

set_option maxHeartbeats 1600000 in
-- the chart change of `HasIndepTangent` and the kernel dimension
/-- **"`T_yS = ker f'(y)`" for the tangent spaces of Definition 4.2.1 (preprint 4.13)** (Theorem 3.54 (4) in the
form needed to compare Definitions 4.21 and 5.17).  For an sc-Fredholm section with tame germ data,
`f(x₀) = 0` and `(f, x₀)` in good position in a tame chart, there is an open `V ∋ x₀` all of whose
zeros are in good position, such that at every zero `y ∈ V`, in every strong bundle chart `c`
around `y`, for every open `G ⊆ dom φ` containing `y` with `φ(G ∩ S)` a retract (`S` the solution
set in `V`), the tangent space of the retract `φ(G ∩ S)` at the level-`1` point `z` over `φ(y)`
**is** the kernel of `Lin(z)`.  *Proof*: `⊆` is `tangentSpace_subset_linKer`; for `⊇`, the index
form of Theorem 3.6.8 (preprint 3.54) (`theorem_3_6_8_index`) gives regular data `D` of dimension `d` with
`dim ker Lin(z) = d` in every chart (`IsSurjLinOfIndex`), the bridge retraction `τ` of `D` has
`d` independent tangent vectors at the point (`exists_linearIndependent_tangentSpace`), and they
are carried to the chart `c` (`chart_change_of_transport`, `HasIndepTangent.transport`). -/
theorem exists_tangentSpace_eq_linKer (hf : B.IsScFredholmSectionTame f) {x₀ : X}
    (hg : B.IsGoodPositionGermTame f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ V : Set X, IsOpen V ∧ x₀ ∈ V ∧
      (∀ y ∈ V, IsZeroAt P f y → B.IsGoodPositionGermTame f y) ∧
      ∀ y ∈ V, IsZeroAt P f y → ∀ c : StrongBundleChart PX P, B.IsChart c → y ∈ c.φ.source →
        ∀ G : Set X, IsOpen G → G ⊆ c.φ.source → y ∈ G →
        IsScRetract c.φ.model.E c.φ.model.C (c.φ '' (G ∩ (solutionSet P f ∩ V))) →
        ∀ z : c.φ.model.E 1, c.φ.model.E.toBase 1 z = c.φ y →
          tangentSpace c.φ.model.E c.φ.model.C (c.φ '' (G ∩ (solutionSet P f ∩ V))) z =
            c.linKer f z := by
  classical
  obtain ⟨Vx, d, -, -, hall, D, hreg, hDsrc, -⟩ := theorem_3_6_8_index hf hg hx₀
  obtain ⟨τ, hτ, hτO, hxτ, hiff, hτΓ⟩ := D.exists_scPlusRetraction hreg
  obtain ⟨hVo, -, -⟩ := MPolyfold.isScPlusRetractionOn_of_chart D.isChart τ hτ hτO
  set V := D.φ.source ∩ D.φ ⁻¹' τ.U with hVdef
  have hVVx : V ⊆ Vx := fun y hy => hDsrc ▸ hy.1
  refine ⟨V, hVo, ⟨D.mem_source, hxτ⟩, fun y hy hy0 => (hall y (hVVx hy) hy0).1,
    fun y hy hy0 c hc hyc G hG hGc hyG hQ' z hz => ?_⟩
  set A := solutionSet P f ∩ V with hA
  have hyA : y ∈ A := ⟨hy0, hy⟩
  -- the retract of `τ` is `φ_D(V ∩ A)`
  have hτret : τ.retract = D.φ '' (V ∩ A) := by
    ext w
    constructor
    · intro hw
      obtain ⟨y', hy', rfl⟩ : w ∈ D.φ '' D.φ.source := by rw [D.φ.image_source]; exact hτO hw
      have := (hiff y' hy').1 hw
      exact ⟨y', ⟨⟨hy', this.2⟩, this.1, hy', this.2⟩, rfl⟩
    · rintro ⟨y', ⟨hy'V, hy'S, -⟩, rfl⟩
      exact (hiff y' hy'V.1).2 ⟨hy'S, hy'V.2⟩
  have hQ : IsScRetract D.φ.model.E D.φ.model.C (D.φ '' (V ∩ A)) := ⟨τ, hτret⟩
  -- the level-`1` point over `φ_D(y)`, and `d` independent tangent vectors there
  have hyτ : D.φ y ∈ τ.retract := (hiff y hy.1).2 ⟨hy0, hy.2⟩
  obtain ⟨zD, hzD, hzDs⟩ := exists_smoothLvl_one_of_mem_smooth (lemma_4_1_7_i hτ hyτ)
  obtain ⟨hvV, hvΓ⟩ := D.exists_eq_Γ ⟨hy0, hy.1⟩
  obtain ⟨L, hL, hLT⟩ := D.exists_linearIndependent_tangentSpace hreg τ hτΓ hvV
    (hzD.trans hvΓ)
  have hindD : HasIndepTangent d D.φ.model.E D.φ.model.C (D.φ '' (V ∩ A)) zD := by
    rw [← hτret]; exact ⟨L, hL, hLT⟩
  -- carried to the chart `c`
  obtain ⟨nD, WD, TD, hTD⟩ := D.φ.model.isPartialQuadrant
  obtain ⟨nc, Wc, Tc, hTc⟩ := c.φ.model.isPartialQuadrant
  have hindc : HasIndepTangent d c.φ.model.E c.φ.model.C (c.φ '' (G ∩ A)) z :=
    MPolyfold.chart_change_of_transport
      (fun E C _ Q _ _ _ z => HasIndepTangent d E C Q z)
      (fun _ _ _ _ _ _ _ _ _ _ hQeq _ h => by
        obtain ⟨L, hL, hLT⟩ := h; exact ⟨L, hL, fun i => hQeq ▸ hLT i⟩)
      (fun _ _ _ _ R _ _ _ hdg hFs _ _ _ hQ hQ' hQR _ hFQ _ z hz _ _ _ _ _ _ _ _ _ h =>
        HasIndepTangent.transport hdg hFs hQ hQ' hQR hFQ hz h)
      D.isChart c.isChart hVo hG (fun _ h => h.1) hGc hQ hQ' hyA hy hyG hzD hz hzDs TD hTD Tc hTc
      hindD
  -- `T_zQ ⊆ ker Lin(z)`
  have hQO : c.φ '' (G ∩ A) ⊆ c.φ.model.O := by
    rintro _ ⟨y', hy', rfl⟩; exact c.φ.mapsTo_model y' (hGc hy'.1)
  have hQ0 : ∀ u ∈ c.φ '' (G ∩ A), c.principal f u = 0 := by
    rintro _ ⟨y', hy', rfl⟩
    exact (c.isZeroAt_iff hf.isScSmooth.1 (hGc hy'.1)).1 hy'.2.1
  have hzQ : z ∈ c.φ.model.E.lvlSet (c.φ '' (G ∩ A)) 1 := by
    rw [ScBanach.mem_lvlSet, hz]; exact ⟨y, ⟨hyG, hyA⟩, rfl⟩
  have hsub := tangentSpace_subset_linKer hf.isScSmooth hc hQ' hQO hQ0 hzQ
  -- `dim ker Lin(z) = d`
  have hzO : c.φ.model.E.toBase 1 z ∈ r c.R '' c.U := by
    rw [hz, c.r_image]; exact c.φ.mapsTo_model y hyc
  have hzU : c.φ.model.E.toBase 1 z ∈ c.U := mem_U_of_mem_O c.isRetraction hzO
  have hmem : ∀ x : ↥(rangeS (scDeriv c.U (r c.R) z)),
      linAt c.U c.R (c.principal f) z x ∈ rangeS (ρCLM c.isRetraction hzU) := fun x =>
    ⟨_, rho_scDeriv_comp_r c.relOpen c.isRetraction (hf.isScSmooth.isSc1_principal_comp_r hc)
      (fun x hx => c.principal_mem_K hf.isScSmooth.1 (c.r_image ▸ hx)) hzO
      (by rw [hz]; exact (c.isZeroAt_iff hf.isScSmooth.1 hyc).1 hy0) x⟩
  set Lc := (linAt c.U c.R (c.principal f) z).codRestrict _ hmem with hLcdef
  obtain ⟨-, hFred, -, hker⟩ := (hall y (hVVx hy) hy0).2 c hc hyc z hz hzU Lc fun _ => rfl
  have hkerEq : LinearMap.ker (Lc : ↥(rangeS (scDeriv c.U (r c.R) z)) →ₗ[ℝ]
      ↥(rangeS (ρCLM c.isRetraction hzU))) =
      LinearMap.ker (linAt c.U c.R (c.principal f) z :
        ↥(rangeS (scDeriv c.U (r c.R) z)) →ₗ[ℝ] c.F 0) := by
    ext x
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hLcdef]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hfin : FiniteDimensional ℝ (LinearMap.ker (linAt c.U c.R (c.principal f) z :
      ↥(rangeS (scDeriv c.U (r c.R) z)) →ₗ[ℝ] c.F 0)) := by
    rw [← hkerEq]; exact hFred.finite_ker
  have hfinK : FiniteDimensional ℝ (c.linKer f z) := by
    unfold StrongBundleChart.linKer; infer_instance
  have hrankK : finrank ℝ (c.linKer f z) = d := by
    unfold StrongBundleChart.linKer
    rw [← hker, hkerEq]
    exact (Submodule.equivMapOfInjective _ Subtype.val_injective _).finrank_eq.symm
  -- the span of the independent tangent vectors is the kernel
  obtain ⟨L', hL', hL'T⟩ := hindc
  set Nsp := Submodule.span ℝ (range L') with hNsp
  have hNle : Nsp ≤ c.linKer f z := Submodule.span_le.2 fun _ ⟨i, hi⟩ => hi ▸ hsub (hL'T i)
  have hNrank : finrank ℝ Nsp = d := by rw [finrank_span_eq_card hL', Fintype.card_fin]
  have hNeq : Nsp = c.linKer f z :=
    Submodule.eq_of_le_of_finrank_eq hNle (by rw [hNrank, hrankK])
  obtain ⟨S', hS'⟩ := hQ'
  have hzS' : z ∈ c.φ.model.E.lvlSet S'.retract 1 := by rw [hS']; exact hzQ
  refine Set.Subset.antisymm hsub ?_
  rw [← hNeq, ← hS', tangentSpace_eq_coe_submodule S' hzS']
  refine Submodule.span_le.2 fun _ ⟨i, hi⟩ => ?_
  have := hL'T i
  rw [← hS', tangentSpace_eq_coe_submodule S' hzS'] at this
  exact hi ▸ this

omit [T2Space Y] [ParacompactSpace Y] in
/-- The kernel of `Lin(z)` lies in `T_zO`. -/
lemma StrongBundleChart.linKer_le (c : StrongBundleChart PX P) (f : X → Y)
    (z : c.φ.model.E 1) : c.linKer f z ≤ rangeS (scDeriv c.U (r c.R) z) := by
  rintro _ ⟨w, -, rfl⟩; exact w.2

/-- **The linear algebra of "submanifold general position ⟹ good position"**: if `N ≤ K ≤ M`,
`N + B = M` with `B ≤ T ≤ M`, then `K` has a complement `B''` in `M` contained in `T` (a complement
of `K ∩ T` inside `T`). -/
lemma exists_compl_le_of_sup_eq {V : Type*} [AddCommGroup V] [Module ℝ V]
    {N K M B T : Submodule ℝ V} (hNK : N ≤ K) (hKM : K ≤ M) (hBT : B ≤ T) (hTM : T ≤ M)
    (hNB : N ⊔ B = M) : ∃ B'' : Submodule ℝ V, B'' ≤ T ∧ K ⊓ B'' = ⊥ ∧ K ⊔ B'' = M := by
  obtain ⟨Cc, hCc⟩ := Submodule.exists_isCompl ((K ⊓ T).comap T.subtype)
  refine ⟨Cc.map T.subtype, Submodule.map_subtype_le _ _, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro x ⟨hxK, ⟨y, hyC, rfl⟩⟩
    have hy1 : y ∈ (K ⊓ T).comap T.subtype := ⟨hxK, y.2⟩
    have hy0 : y = 0 := by
      have := hCc.inf_eq_bot
      have hmem : y ∈ (K ⊓ T).comap T.subtype ⊓ Cc := ⟨hy1, hyC⟩
      rw [this] at hmem
      exact hmem
    rw [hy0, map_zero]; exact Submodule.zero_mem _
  · refine le_antisymm (sup_le hKM ((Submodule.map_subtype_le _ _).trans hTM)) ?_
    rw [← hNB]
    refine sup_le (hNK.trans le_sup_left) fun b hb => ?_
    have hbT : (⟨b, hBT hb⟩ : T) ∈ (K ⊓ T).comap T.subtype ⊔ Cc := by
      rw [hCc.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨k, hk, c, hc, hkc⟩ := Submodule.mem_sup.1 hbT
    have hb' : b = (k : V) + (c : V) := by rw [← Submodule.coe_add, hkc]
    rw [hb']
    exact Submodule.add_mem_sup hk.1 ⟨c, hc, rfl⟩

/-- **Submanifold general position gives good position of the section** (the form of Lemma 5.26
used at the end of the proofs of Theorems 5.18 and 5.25): let `f` be an sc-Fredholm section with
tame germ data, `y` a zero at which `f'(y)` is onto (`IsLinSurjAt`), and `A ⊆ S_f` a smooth
finite-dimensional submanifold (Definition 4.2.1 (preprint 4.13)) in general position at `y` (Definition 4.2.10 (preprint 4.21)).  Then
`(f, y)` is in good position (Definition 3.6.6 (preprint 3.53), in a tame chart).  *Proof*: in the tame chart of the
germ data, `T_zA ⊆ ker Lin(z)` (`tangentSpace_subset_linKer`) and `T_zA + T^R_zO = T_zO`, so
`ker Lin(z)` has a complement in `T_zO` inside `T^R_zO` (`exists_compl_le_of_sup_eq`), hence is in
good position to the partial cone (`isInGoodPositionIn_of_scComplement_le_reduced`, with the
interior condition), and Definition 3.6.6 (preprint 3.53) follows (`isGoodPositionGerm_of_linAt_surj`). -/
theorem isGoodPositionGermTame_of_isGeneralPositionAt (hf : B.IsScFredholmSectionTame f) {y : X}
    (hy0 : IsZeroAt P f y) (hsurj : B.IsLinSurjAt f y) {A : Set X}
    (hA : PX.IsSmoothSubmanifold A) (hAS : A ⊆ solutionSet P f)
    (hgpA : PX.IsGeneralPositionAt A y) : B.IsGoodPositionGermTame f y := by
  have hys : y ∈ PX.smoothSet := hf.mem_smoothSet_of_isZeroAt hy0
  obtain ⟨-, c, hc, hyV, hφ0, -⟩ := hf.germTame y hys
  have hyA : y ∈ A := hgpA.1
  set d := hA.data hyA with hd
  have hz : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) = c.φ y := by rw [map_zero, hφ0]
  obtain ⟨n, Wq, T, hT⟩ := c.φ.model.isPartialQuadrant
  obtain ⟨N, M, Bs, hN, hM, hBM, -, hsplit⟩ :=
    hgpA.isGeneralPositionChart d c.isChart T hT (hA.mem_data_V hyA) hyV hz
  set R := c.isRetraction.baseRetraction c.relOpen with hRdef
  have hRT : R.IsTameWith T := hc.2 n Wq T hT
  have hyO : c.φ y ∈ c.φ.model.O := c.φ.mapsTo_model y hyV
  have hzR : (0 : c.φ.model.E 1) ∈ c.φ.model.E.lvlSet R.retract 1 := by
    rw [ScBanach.mem_lvlSet, c.base_retract, hz]; exact hyO
  have hzs : (0 : c.φ.model.E 1) ∈ c.φ.model.E.smoothLvl 1 := by
    change c.φ.model.E.toBase 1 0 ∈ c.φ.model.E.smooth
    rw [hz]; exact (PX.mem_smoothSet_iff c.isChart hyV).1 hys
  have hTO : tangentSpace c.φ.model.E c.φ.model.C c.φ.model.O 0 =
      ↑(LinearMap.range (scDeriv R.U R 0 : c.φ.model.E 0 →ₗ[ℝ] c.φ.model.E 0)) := by
    rw [← c.base_retract]; exact tangentSpace_eq_coe_submodule R hzR
  have hMeq : M = LinearMap.range (scDeriv R.U R 0 : c.φ.model.E 0 →ₗ[ℝ] c.φ.model.E 0) :=
    SetLike.coe_injective (hM.trans hTO)
  -- `T_zA ⊆ ker Lin(z)`
  have hQ := d.toSubData.isScRetract_image c.φ c.isChart
  have hQO : c.φ '' (d.toSubData.shrink c.φ ∩ A) ⊆ c.φ.model.O := by
    rintro _ ⟨y', hy', rfl⟩; exact c.φ.mapsTo_model y' (d.toSubData.shrink_subset_source c.φ hy'.1)
  have hQ0 : ∀ u ∈ c.φ '' (d.toSubData.shrink c.φ ∩ A), c.principal f u = 0 := by
    rintro _ ⟨y', hy', rfl⟩
    exact (c.isZeroAt_iff hf.isScSmooth.1 (d.toSubData.shrink_subset_source c.φ hy'.1)).1
      (hAS hy'.2)
  have hzQ : (0 : c.φ.model.E 1) ∈
      c.φ.model.E.lvlSet (c.φ '' (d.toSubData.shrink c.φ ∩ A)) 1 := by
    rw [ScBanach.mem_lvlSet, hz]
    exact ⟨y, ⟨d.toSubData.mem_shrink c.φ hyA (hA.mem_data_V hyA) hyV, hyA⟩, rfl⟩
  have hNK : N ≤ c.linKer f 0 := fun v hv =>
    tangentSpace_subset_linKer hf.isScSmooth hc.1 hQ hQO hQ0 hzQ (by rw [← hN]; exact hv)
  have hKM : c.linKer f 0 ≤ M := by rw [hMeq]; exact c.linKer_le f 0
  have h0 := hsplit 0
  rw [ScBanach.levelSub_zero, ScBanach.levelSub_zero, ScBanach.levelSub_zero] at h0
  have hBT : Bs ≤ reducedTangentSpaceWith R T 0 := by
    rw [reducedTangentSpaceWith, ← hMeq]; exact hBM
  have hTM : reducedTangentSpaceWith R T 0 ≤ M := by
    rw [reducedTangentSpaceWith, ← hMeq]; exact inf_le_left
  obtain ⟨B'', hB''T, hKB, hKBM⟩ := exists_compl_le_of_sup_eq hNK hKM hBT hTM h0.2
  rw [hMeq] at hKBM
  have hker := isInGoodPositionIn_of_scComplement_le_reduced T hRT hzR hzs hB''T hKB hKBM
  rw [hz] at hker
  have hs' := hsurj.linAt_surjective hf.isScSmooth hy0 hc.1 hyV hz
  exact (StrongBundle.isGoodPositionGerm_of_linAt_surj hf.isScSmooth (hf.germ y hys) hy0 hc.1
    hyV hz T hT hs' hker).toTame hf.isScSmooth (hf.germTame y hys) hy0

/-- **Definition 5.3.9 (preprint 5.17) is Definition 4.2.10 (preprint 4.21) for the solution set** (the chart independence of
Definition 5.3.9 (preprint 5.17), through `T_yS = ker f'(y)`): for an sc-Fredholm section with tame germ data and
`(f, x₀)` in good position, there is an open `V ∋ x₀` such that every zero in `V` is in good
position, `S = S_f ∩ V` is a smooth finite-dimensional submanifold (Definition 4.2.1 (preprint 4.13)), and at every
zero `y ∈ V`, **`(f, y)` is in general position (Definition 5.3.9 (preprint 5.17), in some tame chart) iff `S` is in
general position at `y` (Definition 4.2.10 (preprint 4.21), in some chart)**.  Both sides are then chart-independent
(`IsGeneralPositionAt.isGeneralPositionChart`).  *Proof*: `T_zS = ker Lin(z)` in every chart
(`exists_tangentSpace_eq_linKer`), so the sc-complements inside `T^R_zO` are the same objects. -/
theorem exists_isGeneralPositionGerm_iff (hf : B.IsScFredholmSectionTame f) {x₀ : X}
    (hg : B.IsGoodPositionGermTame f x₀) (hx₀ : IsZeroAt P f x₀) :
    ∃ V : Set X, IsOpen V ∧ x₀ ∈ V ∧
      (∀ y ∈ V, IsZeroAt P f y → B.IsGoodPositionGermTame f y) ∧
      PX.IsSmoothSubmanifold (solutionSet P f ∩ V) ∧
      (∀ y ∈ V, IsZeroAt P f y →
        (B.IsGeneralPositionGerm f y ↔ PX.IsGeneralPositionAt (solutionSet P f ∩ V) y)) ∧
      ∀ y ∈ V, IsZeroAt P f y → ∀ c : StrongBundleChart PX P, B.IsChart c → y ∈ c.φ.source →
        ∀ G : Set X, IsOpen G → G ⊆ c.φ.source → y ∈ G →
        IsScRetract c.φ.model.E c.φ.model.C (c.φ '' (G ∩ (solutionSet P f ∩ V))) →
        ∀ z : c.φ.model.E 1, c.φ.model.E.toBase 1 z = c.φ y →
          tangentSpace c.φ.model.E c.φ.model.C (c.φ '' (G ∩ (solutionSet P f ∩ V))) z =
            c.linKer f z := by
  obtain ⟨V, hVo, hx₀V, hall, hid⟩ := exists_tangentSpace_eq_linKer hf hg hx₀
  have hA : PX.IsSmoothSubmanifold (solutionSet P f ∩ V) :=
    StrongBundle.isSmoothSubmanifold_solutionSet_inter hf.isScSmooth.1 hVo hall
  refine ⟨V, hVo, hx₀V, hall, hA, fun y hyV hy0 => ⟨fun h => ?_, fun h => ?_⟩, hid⟩
  · -- Definition 5.3.9 (preprint 5.17) ⟹ Definition 4.2.10 (preprint 4.21)
    obtain ⟨c, hc, hyc, z, hz, -, hgen⟩ := h
    have hyA : y ∈ solutionSet P f ∩ V := ⟨hy0, hyV⟩
    set d := hA.data hyA with hd
    obtain ⟨n, Wq, T, hT⟩ := c.φ.model.isPartialQuadrant
    obtain ⟨Bc, hBc, hBsc, hsplit⟩ := hgen T hT
    have hyG : y ∈ d.toSubData.shrink c.φ :=
      d.toSubData.mem_shrink c.φ hyA (hA.mem_data_V hyA) hyc
    have hTQ := hid y hyV hy0 c hc.1 hyc _ (d.toSubData.isOpen_shrink c.φ)
      (d.toSubData.shrink_subset_source c.φ) hyG (d.toSubData.isScRetract_image c.φ c.isChart)
      z hz
    have hzO : z ∈ c.φ.model.E.lvlSet (c.isRetraction.baseRetraction c.relOpen).retract 1 := by
      rw [ScBanach.mem_lvlSet, c.base_retract, hz]; exact c.φ.mapsTo_model y hyc
    have hTO : tangentSpace c.φ.model.E c.φ.model.C c.φ.model.O z =
        ↑(rangeS (scDeriv c.U (r c.R) z)) := by
      rw [← c.base_retract]; exact tangentSpace_eq_coe_submodule _ hzO
    exact ⟨hyA, d, c.φ, n, Wq, T, z, hA.mem_data_V hyA, c.isChart, hyc, hT, hz,
      c.linKer f z, rangeS (scDeriv c.U (r c.R) z), Bc, hTQ.symm, hTO.symm, hBc, hBsc, hsplit⟩
  · -- Definition 4.2.10 (preprint 4.21) ⟹ Definition 5.3.9 (preprint 5.17)
    have hys : y ∈ PX.smoothSet := hf.mem_smoothSet_of_isZeroAt hy0
    have hgy := hall y hyV hy0
    have hlin := hgy.isGoodPositionGerm.isLinSurjAt hf.isScSmooth
    obtain ⟨-, c, hc, hyc, hφ0, -⟩ := hgy
    have hz : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) = c.φ y := by rw [map_zero, hφ0]
    have hsurj := hlin.linAt_surjective hf.isScSmooth hy0 hc.1 hyc hz
    have hyA : y ∈ solutionSet P f ∩ V := ⟨hy0, hyV⟩
    set d := hA.data hyA with hd
    have hyG : y ∈ d.toSubData.shrink c.φ :=
      d.toSubData.mem_shrink c.φ hyA (hA.mem_data_V hyA) hyc
    have hTQ := hid y hyV hy0 c hc.1 hyc _ (d.toSubData.isOpen_shrink c.φ)
      (d.toSubData.shrink_subset_source c.φ) hyG (d.toSubData.isScRetract_image c.φ c.isChart)
      0 hz
    have hzO : (0 : c.φ.model.E 1) ∈
        c.φ.model.E.lvlSet (c.isRetraction.baseRetraction c.relOpen).retract 1 := by
      rw [ScBanach.mem_lvlSet, c.base_retract, hz]; exact c.φ.mapsTo_model y hyc
    have hTO : tangentSpace c.φ.model.E c.φ.model.C c.φ.model.O 0 =
        ↑(rangeS (scDeriv c.U (r c.R) 0)) := by
      rw [← c.base_retract]; exact tangentSpace_eq_coe_submodule _ hzO
    refine ⟨c, hc, hyc, 0, hz, hsurj, fun {n Wq} T hT => ?_⟩
    obtain ⟨N, M, Bs, hN, hM, hBM, hBsc, hsplit⟩ :=
      h.isGeneralPositionChart d c.isChart T hT (hA.mem_data_V hyA) hyc hz
    have hNeq : N = c.linKer f 0 := SetLike.coe_injective (hN.trans hTQ)
    have hMeq : M = rangeS (scDeriv c.U (r c.R) 0) := SetLike.coe_injective (hM.trans hTO)
    subst hNeq hMeq
    exact ⟨Bs, hBM, hBsc, hsplit⟩

/-- **General position is open along the solution set** (used without proof in Theorems 5.3.10 (preprint 5.18) and
5.25: "the properties (i)–(ii) hold for all `(λ, y) ∈ S̃`"; Findings, Chapter 5 item 73).  For an
sc-Fredholm section with tame germ data over a **tame** M-polyfold `X`, if `(f, x₀)` is in general
position (Definition 5.3.9 (preprint 5.17)), there is an open `W ∋ x₀` such that `S_f ∩ W` is a smooth
finite-dimensional submanifold and at every zero `y ∈ W` the germ `(f, y)` is in good position and
in general position, and `S_f ∩ W` is in general position at `y` (Definition 4.2.10 (preprint 4.21)).  *Proof*: by
Lemma 5.26 `(f, x₀)` is in good position; `exists_isGeneralPositionGerm_iff` turns general position
of the section into general position of the smooth submanifold `S = S_f ∩ V` (Definition 4.2.10 (preprint 4.21)),
which is open along `S` by Theorem 4.2.11 (preprint 4.22) (3) (`theorem_4_2_11_preprint`, for tame `X`), and back. -/
theorem exists_isOpen_isGeneralPositionGerm (hX : PX.IsTame) (hf : B.IsScFredholmSectionTame f)
    {x₀ : X} (hx₀ : IsZeroAt P f x₀) (hgp : B.IsGeneralPositionGerm f x₀) :
    ∃ W : Set X, IsOpen W ∧ x₀ ∈ W ∧ PX.IsSmoothSubmanifold (solutionSet P f ∩ W) ∧
      ∀ y ∈ W, IsZeroAt P f y → B.IsGoodPositionGermTame f y ∧ B.IsGeneralPositionGerm f y ∧
        PX.IsGeneralPositionAt (solutionSet P f ∩ W) y := by
  obtain ⟨V, hVo, hx₀V, hall, hA, hiff, -⟩ :=
    exists_isGeneralPositionGerm_iff hf (hgp.isGoodPositionGermTame hf hx₀) hx₀
  have := PX.paracompactSpace_subtype (solutionSet P f ∩ V)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, U, hUo, hx₀U, -, -, -, -, hgen, -⟩ :=
    MPolyfold.theorem_4_2_11_preprint hX hA ((hiff x₀ hx₀V hx₀).1 hgp)
  have hWo : IsOpen (V ∩ U) := hVo.inter hUo
  have hAW : PX.IsSmoothSubmanifold (solutionSet P f ∩ (V ∩ U)) :=
    StrongBundle.isSmoothSubmanifold_solutionSet_inter hf.isScSmooth.1 hWo
      fun y hy hy0 => hall y hy.1 hy0
  refine ⟨V ∩ U, hWo, ⟨hx₀V, hx₀U⟩, hAW, fun y hy hy0 => ?_⟩
  have hgA : PX.IsGeneralPositionAt (solutionSet P f ∩ V) y := hgen y ⟨hy.2, hy0, hy.1⟩
  refine ⟨hall y hy.1 hy0, (hiff y hy.1 hy0).2 hgA, ?_⟩
  refine MPolyfold.IsGeneralPositionAt.congr_nhds hA hAW hWo hy ?_ hgA
  ext z
  simp only [mem_inter_iff]
  tauto

end SolutionSet

/-! ### Theorem 5.3.10 (preprint 5.18) -/

section Theorem518

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

open StrongRetr

variable (B) in
/-- **The conclusions of Theorem 5.3.10 (preprint 5.18) for a section `h`**: `h` is transversal to the zero section,
`(h, y)` is in general position (Definition 5.3.9 (preprint 5.17)) at every zero, and the solution set `S_h` is
compact, a smooth finite-dimensional submanifold (Definition 4.2.1 (preprint 4.13)) in general position at each of
its points (Definition 4.2.10 (preprint 4.21)), whose induced structure is that of a manifold with boundary with
corners (Definition 4.1.1 (preprint 4.1)) and tame, with `d_{S_h} = d_X` on `S_h`. -/
def StrongBundle.SolutionSetInGeneralPosition (h : X → Y) : Prop :=
  B.IsTransversal h ∧ (∀ y, IsZeroAt P h y → B.IsGeneralPositionGerm h y) ∧
    IsCompact (solutionSet P h) ∧ ∃ hS : PX.IsSmoothSubmanifold (solutionSet P h),
      (∀ y ∈ solutionSet P h, PX.IsGeneralPositionAt (solutionSet P h) y) ∧
      haveI := PX.paracompactSpace_subtype (solutionSet P h)
      (MPolyfold.subPolyfold hS.isSubMPolyfold).HasCornerStructure ∧
      PX.IsTameSubmanifold (solutionSet P h) ∧
      ∀ a : solutionSet P h,
        (MPolyfold.subPolyfold hS.isSubMPolyfold).degIndex a = PX.degIndex a

set_option maxHeartbeats 6400000 in
-- the assembly of the proof: several large existentials are destructured
/-- **Theorem 5.3.10 (preprint 5.18) (perturbation and transversality: general position), from a family satisfying
(i)–(ii).**  Let `P : Y → X` be a strong bundle over a **tame** M-polyfold `X` (the hidden
hypothesis: the proof uses Theorems 4.2.11 and 4.3.1 (preprint 4.22 and 4.23)), `f` an sc-Fredholm section with tame germ data
and compact solution set, `N` an auxiliary norm.  Then there is an open `U ⊇ S_f` such that
(1) `S_{f+s}` is compact for every allowable `s ∈ Γ^{+,1}_U(P)`, and (2) for every sc⁺-section
`s₀` with `supp(s₀) ⊆ U`, `N(s₀) ≤ 1 − ε`, and every family of allowable sc⁺-sections
`t₁, …, t_m` such that the parametrized section `F(λ, y) = f(y) + s₀(y) + Σ λᵢ tᵢ(y)` is in general
position at every `(0, x)`, `x ∈ S_{f+s₀}` (the text's properties (i) `F'(0, x)` onto and (ii)
`ker F'(0, x)` transversal to `ℝᵐ ⊕ T^R_xX`), there are `δ > 0` and a Lebesgue null set `CV` such
that for `|λ| < δ`, `λ ∉ CV`, the perturbation `s_λ = s₀ + Σ λᵢ tᵢ` is allowable and
`f + s_λ` has all the conclusions of the theorem (`SolutionSetInGeneralPosition`): transversal,
in general position at every zero, `S_{f+s_λ}` compact, a smooth submanifold in general position,
a manifold with boundary with corners with `d_S = d_X`.

*Proof* (the text's): general position is open along the parametrized solution set `S̃`
(`exists_isOpen_isGeneralPositionGerm`), so the zeros of `F` in an open `W ⊇ {0} × S_{f+s₀}` are in
good and general position, and for small `δ` the set `A = S̃ ∩ W ∩ {|λ| < δ}` is a smooth
finite-dimensional submanifold (the bridge lemma) in general position (Definition 4.2.10 (preprint 4.21)) with
compact closure (Theorem 5.2.2 (preprint 5.5), Remark 5.3.4 (preprint 5.12); the omitted step `exists_pos_forall_mem_of_isCompact`).
Theorem 4.3.1 (preprint 4.23) (`theorem_4_3_1_of_subset`) gives a full-measure set of `λ` over which the fibre
`A_λ = S_{f+s_λ}` is a smooth submanifold in general and good position; the Sard step of Theorem
5.13 (`exists_null_isLinSurjAt_paramSlice_near`) gives transversality; then
`isGoodPositionGermTame_of_isGeneralPositionAt` and `exists_isGeneralPositionGerm_iff` give the
general position of `(f + s_λ, y)`, Theorem 4.2.7 (preprint 4.18) the corner structure and Theorem 4.2.11 (preprint 4.22) (2)
`d_S = d_X`.  (A family with (i)–(ii) is constructed by `exists_sections_isParamGP`; Finding 84.) -/
theorem theorem_5_3_10_of_family (hX : PX.IsTame) {f : X → Y} (hf : B.IsScFredholmSectionTame f)
    (hS : IsCompact (solutionSet P f)) {N : B.One → ℝ} (hN : B.IsAuxNorm N) :
    ∃ U : Set X, IsOpen U ∧ solutionSet P f ⊆ U ∧
      (∀ s ∈ B.allowableSections N U, IsCompact (solutionSet P (sectionAdd P f s))) ∧
      ∀ (s₀ : X → Y) (hs₀ : B.IsScPlusSection s₀), sectionSupport P s₀ ⊆ U → ∀ ε > 0,
        (∀ x (hx : s₀ x ∈ B.oneSet), N (B.oneMk (s₀ x) hx) ≤ 1 - ε) →
        ∀ (m : ℕ) (t : Fin m → X → Y) (ht : ∀ i, B.IsScPlusSection (t i)),
          (∀ i, sectionSupport P (t i) ⊆ U) →
          (∀ i x (hx : t i x ∈ B.oneSet), N (B.oneMk (t i x) hx) ≤ 1) →
          (∀ y, IsZeroAt P (sectionAdd P f s₀) y →
            haveI := MPolyfold.paracompactSpace_prod (rnPolyfold m) PX
            haveI := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin m → ℝ) × X → X))
              ((rnPolyfold m).prod PX) B
            (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsGeneralPositionGerm
              (paramSection (sectionAdd P f s₀) (hf.isScSmooth.1.sectionAdd hs₀.1) t
                fun i => (ht i).1) (0, y)) →
          ∃ δ > 0, ∃ CV : Set (Fin m → ℝ), volume CV = 0 ∧
            ∀ lam : Fin m → ℝ, ‖lam‖ < δ → lam ∉ CV →
              paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam ∈ B.allowableSections N U ∧
              B.SolutionSetInGeneralPosition
                (sectionAdd P f (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam)) := by
  classical
  have hfs : IsSection P f := hf.isScSmooth.1
  obtain ⟨-, hprop⟩ := theorem_5_2_2_preprint hf.toIsScFredholmSection hS
  obtain ⟨U, hUo, hSU, hK⟩ := hprop N hN
  have hcpt : ∀ s ∈ B.allowableSections N U, IsCompact (solutionSet P (sectionAdd P f s)) := by
    rintro s ⟨hs, hssupp, hsN⟩
    have hsU : ∀ x ∉ U, IsZeroAt P s x := fun x hx =>
      not_not.1 fun hne => hx (hssupp (subset_closure hne))
    have hsN' : ∀ x, B.AuxLe N (s x) 1 := fun x => ⟨hs.mem_oneSet x, hsN x _⟩
    obtain ⟨-, hcl⟩ := remark_5_3_4 hN hfs hSU hK hs.1 hsU hsN'
    exact hcl.of_isClosed_subset
      (isClosed_solutionSet (theorem_3_1_18_preprint hf.toIsScFredholmSection hs).isScSmooth)
      subset_closure
  refine ⟨U, hUo, hSU, hcpt, ?_⟩
  intro s₀ hs₀ hs₀supp ε hε hs₀N m t ht htsupp htN hgp0
  have hgFt : B.IsScFredholmSectionTame (sectionAdd P f s₀) := theorem_3_1_18_tame hf hs₀
  have hgF : B.IsScFredholmSection (sectionAdd P f s₀) := hgFt.toIsScFredholmSection
  have := MPolyfold.paracompactSpace_prod (rnPolyfold m) PX
  have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin m → ℝ) × X → X))
    ((rnPolyfold m).prod PX) B
  have hFt := theorem_3_1_21_tame hgFt ht
  have hXm : ((rnPolyfold m).prod PX).IsTame := prod_rn_isTame hX
  have hz0 : ∀ y, IsZeroAt P (sectionAdd P f s₀) y → IsZeroAt (pullbackProj P Prod.snd)
      (paramSection (sectionAdd P f s₀) hgF.isScSmooth.1 t fun i => (ht i).1) (0, y) :=
    fun y hy => by
      rw [isZeroAt_paramSection_iff]
      change IsZeroAt P (paramSlice (sectionAdd P f s₀) hgF.isScSmooth.1 t
        (fun i => (ht i).1) 0) y
      rw [paramSlice_zero]; exact hy
  -- the open set `W ⊇ {0} × S_g` of zeros of `F` in good and general position
  have hloc : ∀ y : solutionSet P (sectionAdd P f s₀), ∃ W : Set ((Fin m → ℝ) × X), IsOpen W ∧
      ((0 : Fin m → ℝ), (y : X)) ∈ W ∧
      ((rnPolyfold m).prod PX).IsSmoothSubmanifold (solutionSet (pullbackProj P Prod.snd)
        (paramSection (sectionAdd P f s₀) hgF.isScSmooth.1 t fun i => (ht i).1) ∩ W) ∧
      ∀ z ∈ W, IsZeroAt (pullbackProj P Prod.snd)
        (paramSection (sectionAdd P f s₀) hgF.isScSmooth.1 t fun i => (ht i).1) z →
        (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsGoodPositionGermTame
          (paramSection (sectionAdd P f s₀) hgF.isScSmooth.1 t fun i => (ht i).1) z ∧
        (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsGeneralPositionGerm
          (paramSection (sectionAdd P f s₀) hgF.isScSmooth.1 t fun i => (ht i).1) z ∧
        ((rnPolyfold m).prod PX).IsGeneralPositionAt (solutionSet (pullbackProj P Prod.snd)
          (paramSection (sectionAdd P f s₀) hgF.isScSmooth.1 t fun i => (ht i).1) ∩ W) z :=
    fun y => exists_isOpen_isGeneralPositionGerm hXm hFt (hz0 y y.2) (hgp0 y y.2)
  choose Wy hWyo hyWy hWyA hWy using hloc
  set W := ⋃ y, Wy y with hWdef
  have hWo : IsOpen W := isOpen_iUnion hWyo
  have h0W : ∀ y, IsZeroAt P (sectionAdd P f s₀) y → ((0 : Fin m → ℝ), y) ∈ W := fun y hy =>
    mem_iUnion.2 ⟨⟨y, hy⟩, hyWy ⟨y, hy⟩⟩
  have hWgood : ∀ z ∈ W, IsZeroAt (pullbackProj P Prod.snd)
      (paramSection (sectionAdd P f s₀) hgF.isScSmooth.1 t fun i => (ht i).1) z →
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsGoodPositionGermTame
        (paramSection (sectionAdd P f s₀) hgF.isScSmooth.1 t fun i => (ht i).1) z :=
    fun z hz hz0 => by
      obtain ⟨y, hzy⟩ := mem_iUnion.1 hz
      exact (hWy y z hzy hz0).1
  -- the perturbations `s_λ` are allowable for `|λ| ≤ δ₁ = ε/(m + 1)`
  set δ₁ : ℝ := ε / (m + 1) with hδ₁
  have hδ₁pos : 0 < δ₁ := div_pos hε (by positivity)
  have hallow : ∀ lam : Fin m → ℝ, ‖lam‖ ≤ δ₁ →
      ∀ x, B.AuxLe N (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam x) 1 := fun lam hlam x =>
    auxLe_paramSlice hN hs₀ ht hs₀N htN (by
      calc (m : ℝ) * ‖lam‖ ≤ m * δ₁ := mul_le_mul_of_nonneg_left hlam (by positivity)
        _ = ε * (m / (m + 1)) := by rw [hδ₁]; ring
        _ ≤ ε * 1 := mul_le_mul_of_nonneg_left
            ((div_le_one (by positivity)).2 (by linarith)) hε.le
        _ = ε := mul_one ε) x
  have hsuppl : ∀ lam : Fin m → ℝ, ∀ x ∉ U,
      IsZeroAt P (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam) x := fun lam x hx =>
    isZeroAt_paramSlice_of_not_mem_support hs₀.1 _ lam (fun h => hx (hs₀supp h))
      fun i h => hx (htsupp i h)
  have hslice : ∀ lam : Fin m → ℝ, sectionAdd P f (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam) =
      paramSlice (sectionAdd P f s₀) hgF.isScSmooth.1 t (fun i => (ht i).1) lam := fun lam =>
    sectionAdd_paramSlice hfs hs₀.1 _ lam
  -- the zeros of `F` over `|λ| ≤ δ₁` form a compact set `Z`
  set Z : Set ((Fin m → ℝ) × X) := {z | ‖z.1‖ ≤ δ₁ ∧ IsZeroAt (pullbackProj P Prod.snd)
    (paramSection (sectionAdd P f s₀) hgF.isScSmooth.1 t fun i => (ht i).1) z} with hZdef
  have hZsub : Z ⊆ Metric.closedBall (0 : Fin m → ℝ) δ₁ ×ˢ closure {x ∈ U | B.AuxLe N (f x) 1} := by
    rintro ⟨lam, x⟩ ⟨hlam, hz⟩
    refine ⟨mem_closedBall_zero_iff.2 hlam, ?_⟩
    have hx' : IsZeroAt P (paramSlice (sectionAdd P f s₀) hgF.isScSmooth.1 t
        (fun i => (ht i).1) lam) x := (isZeroAt_paramSection_iff (lam, x)).1 hz
    rw [← hslice lam] at hx'
    exact subset_closure ((remark_5_3_4 hN hfs hSU hK (isSection_paramSlice lam) (hsuppl lam)
      (hallow lam hlam)).1 hx')
  have hZclosed : IsClosed Z :=
    (isClosed_le (continuous_norm.comp continuous_fst) continuous_const).inter
      (isClosed_solutionSet (theorem_3_1_21_preprint hgF ht).isScSmooth)
  have hZ : IsCompact Z :=
    ((isCompact_closedBall _ _).prod hK).of_isClosed_subset hZclosed hZsub
  -- the omitted step: `Z ∩ {|λ| < δ₀} ⊆ W`
  obtain ⟨δ₀, hδ₀, hδ₀W⟩ := exists_pos_forall_mem_of_isCompact hZ hWo fun z hz hz1 => by
    have hz2 : IsZeroAt P (sectionAdd P f s₀) z.2 := by
      have := (isZeroAt_paramSection_iff z).1 hz.2
      rw [hz1, paramSlice_zero] at this; exact this
    have hz' : z = (0, z.2) := Prod.ext hz1 rfl
    rw [hz']; exact h0W z.2 hz2
  set δ : ℝ := min δ₀ δ₁ with hδ
  have hδpos : 0 < δ := lt_min hδ₀ hδ₁pos
  -- the submanifold `A = S̃ ∩ W ∩ {|λ| < δ}`
  set Wδ : Set ((Fin m → ℝ) × X) := W ∩ {z | ‖z.1‖ < δ} with hWδ
  have hWδo : IsOpen Wδ := hWo.inter (isOpen_lt (continuous_norm.comp continuous_fst)
    continuous_const)
  set A := solutionSet (pullbackProj P Prod.snd)
    (paramSection (sectionAdd P f s₀) hgF.isScSmooth.1 t fun i => (ht i).1) ∩ Wδ with hAdef
  have hA : ((rnPolyfold m).prod PX).IsSmoothSubmanifold A :=
    StrongBundle.isSmoothSubmanifold_solutionSet_inter hFt.isScSmooth.1 hWδo
      fun z hz hz0 => hWgood z hz.1 hz0
  have hAZ : A ⊆ Z := fun z hz => ⟨(le_of_lt hz.2.2).trans (min_le_right _ _), hz.1⟩
  have hcl : IsCompact (closure A) :=
    hZ.of_isClosed_subset isClosed_closure (closure_minimal hAZ hZclosed)
  have hgpA : ∀ z ∈ A, ((rnPolyfold m).prod PX).IsGeneralPositionAt A z := by
    intro z hz
    obtain ⟨y, hzy⟩ := mem_iUnion.1 hz.2.1
    refine MPolyfold.IsGeneralPositionAt.congr_nhds (hWyA y) hA ((hWyo y).inter hWδo)
      ⟨hzy, hz.2⟩ ?_ (hWy y z hzy hz.1).2.2
    ext w
    simp only [hAdef, mem_inter_iff]
    tauto
  -- Theorem 4.3.1 (preprint 4.23)
  obtain ⟨Sig, -, hSig0, hSig⟩ := theorem_4_3_1_of_subset hX hA hcl hgpA univ
  -- the Sard step on the compact `Z₀ = Z ∩ {|λ| ≤ δ/2}`
  set Z₀ : Set ((Fin m → ℝ) × X) := {z | ‖z.1‖ ≤ δ / 2 ∧ IsZeroAt (pullbackProj P Prod.snd)
    (paramSection (sectionAdd P f s₀) hgF.isScSmooth.1 t fun i => (ht i).1) z} with hZ₀def
  have hZ₀Z : Z₀ ⊆ Z := fun z hz => ⟨hz.1.trans (by linarith [min_le_right δ₀ δ₁]), hz.2⟩
  have hZ₀closed : IsClosed Z₀ :=
    (isClosed_le (continuous_norm.comp continuous_fst) continuous_const).inter
      (isClosed_solutionSet (theorem_3_1_21_preprint hgF ht).isScSmooth)
  have hZ₀ : IsCompact Z₀ := hZ.of_isClosed_subset hZ₀closed hZ₀Z
  have hZ₀W : ∀ z ∈ Z₀, z ∈ W := fun z hz =>
    hδ₀W z (hZ₀Z hz) (by linarith [min_le_left δ₀ δ₁, hz.1])
  have hlocS : ∀ z : Z₀, ∃ W' : Set ((Fin m → ℝ) × X), IsOpen W' ∧ (z : (Fin m → ℝ) × X) ∈ W' ∧
      ∃ CV : Set (Fin m → ℝ), volume CV = 0 ∧
        ∀ z' ∈ W', IsZeroAt (pullbackProj P Prod.snd)
          (paramSection (sectionAdd P f s₀) hgF.isScSmooth.1 t fun i => (ht i).1) z' →
          z'.1 ∉ CV → B.IsLinSurjAt (paramSlice (sectionAdd P f s₀) hgF.isScSmooth.1 t
            (fun i => (ht i).1) z'.1) z'.2 := fun z =>
    exists_null_isLinSurjAt_paramSlice_near hgFt ht z.2.2 (hWgood z (hZ₀W z z.2) z.2.2)
  choose W' hW'o hzW' CV hCV hW'tr using hlocS
  obtain ⟨T', hT'⟩ := hZ₀.elim_finite_subcover W' hW'o
    (fun z hz => mem_iUnion.2 ⟨⟨z, hz⟩, hzW' ⟨z, hz⟩⟩)
  refine ⟨δ / 2, by positivity, (univ \ Sig) ∪ ⋃ z ∈ T', CV z, ?_, fun lam hlam hlamCV => ?_⟩
  · exact measure_union_null hSig0
      ((measure_biUnion_null_iff T'.countable_toSet).2 fun z _ => hCV z)
  -- the conclusions for `λ`
  have hlamSig : lam ∈ Sig := by
    by_contra h; exact hlamCV (Or.inl ⟨mem_univ _, h⟩)
  have hlam₁ : ‖lam‖ ≤ δ₁ := by linarith [min_le_right δ₀ δ₁]
  have hsl : B.IsScPlusSection (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam) :=
    isScPlusSection_paramSlice hs₀ ht lam
  have halw : paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam ∈ B.allowableSections N U := by
    refine ⟨hsl, (sectionSupport_paramSlice_subset hs₀.1 _ lam).trans
      (union_subset hs₀supp (iUnion_subset htsupp)), fun x hx => ?_⟩
    obtain ⟨hx', h⟩ := hallow lam hlam₁ x
    exact h
  set h := sectionAdd P f (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam) with hhdef
  have hhF : B.IsScFredholmSectionTame h := theorem_3_1_18_tame hf hsl
  have htrans : B.IsTransversal h := by
    intro y hy
    rw [hhdef, hslice lam] at hy ⊢
    have hzZ₀ : (lam, y) ∈ Z₀ := ⟨hlam.le, (isZeroAt_paramSection_iff (lam, y)).2 hy⟩
    obtain ⟨z, hzT', hzW'⟩ := mem_iUnion₂.1 (hT' hzZ₀)
    have hlamCV' : lam ∉ CV z := fun h' => hlamCV (Or.inr (mem_iUnion₂.2 ⟨z, hzT', h'⟩))
    exact hW'tr z (lam, y) hzW' ((isZeroAt_paramSection_iff (lam, y)).2 hy) hlamCV'
  -- the fibre of `A` over `λ` is `S_h`
  have hfib : solutionSet P h = fibreSet A lam := by
    ext x
    constructor
    · intro hx
      have hx' : IsZeroAt P (paramSlice (sectionAdd P f s₀) hgF.isScSmooth.1 t
          (fun i => (ht i).1) lam) x := by
        have := hx; change IsZeroAt P h x at this; rw [hhdef, hslice lam] at this; exact this
      have hzF := (isZeroAt_paramSection_iff (lam, x)).2 hx'
      have hlt : ‖lam‖ < δ := by linarith
      refine ⟨hzF, hδ₀W (lam, x) ⟨hlam₁, hzF⟩ (lt_of_lt_of_le hlt (min_le_left _ _)), hlt⟩
    · intro hx
      have hx' := (isZeroAt_paramSection_iff (lam, x)).1 hx.1
      change IsZeroAt P h x
      rw [hhdef, hslice lam]; exact hx'
  obtain ⟨-, hFL⟩ := hSig lam hlamSig
  have hSm : PX.IsSmoothSubmanifold (solutionSet P h) := by
    intro x hx
    rw [hfib] at hx ⊢
    obtain ⟨-, ⟨V, hV, hxV, s, hs, himg⟩, -, -⟩ := hFL x hx
    exact ⟨V, hV, hxV, s, hs, himg⟩
  have hgpS : ∀ y ∈ solutionSet P h, PX.IsGeneralPositionAt (solutionSet P h) y := by
    intro y hy
    rw [hfib] at hy ⊢
    exact (hFL y hy).2.2.1
  have hgoodS : ∀ y ∈ solutionSet P h, PX.IsGoodPositionAt (solutionSet P h) y := by
    intro y hy
    rw [hfib] at hy ⊢
    exact (hFL y hy).2.2.2
  -- general position of the section at every zero
  have hgpGerm : ∀ y, IsZeroAt P h y → B.IsGeneralPositionGerm h y := by
    intro y hy0
    have hgood := isGoodPositionGermTame_of_isGeneralPositionAt hhF hy0 (htrans y hy0) hSm
      subset_rfl (hgpS y hy0)
    obtain ⟨V', hV'o, hyV', -, hA', hiff', -⟩ := exists_isGeneralPositionGerm_iff hhF hgood hy0
    refine (hiff' y hyV' hy0).2 ?_
    refine MPolyfold.IsGeneralPositionAt.congr_nhds hSm hA' hV'o hyV' ?_ (hgpS y hy0)
    ext w; simp only [mem_inter_iff]; tauto
  have := PX.paracompactSpace_subtype (solutionSet P h)
  obtain ⟨hcs, htameS⟩ := MPolyfold.theorem_4_2_7 hX hSm hgoodS
  refine ⟨halw, htrans, hgpGerm, hcpt _ halw, hSm, hgpS, hcs, htameS, fun a => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, Ua, -, haU, -, -, -, hdeg, -, -⟩ :=
    MPolyfold.theorem_4_2_11_preprint hX hSm (hgpS a a.2)
  exact hdeg a haU

end Theorem518

/-! ### Properties (i)–(ii) of the proof of Theorem 5.3.10 (preprint 5.18) in a chart -/

section FrontHalf

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {g : X → Y}

open StrongRetr

/-- **Properties (i)–(ii) of the proof of Theorem 5.3.10 (preprint 5.18) at `(0, y)`, in a strong bundle chart `c`
centred at `y`** (`z = 0`, `T` a presentation of the partial quadrant): (i) `F'(0, y)` is onto,
i.e. `Lin_g(0)(T₀O) + span{t̂ᵢ(0)} = K₀`; (ii) `ker F'(0, y)` is transversal to `ℝᵐ ⊕ T^R_yX`,
i.e. every `w ∈ T₀O` is `u + e` with `e ∈ E_0` and `Lin_g(0)u + Σ aᵢ t̂ᵢ(0) = 0` for some `a`
(`F'(0, y)(a, u) = Lin_g(0)u + Σ aᵢ t̂ᵢ(0)`). -/
def StrongBundleChart.IsParamGP (c : StrongBundleChart PX P) (g : X → Y) {m : ℕ}
    (t : Fin m → X → Y) {n : ℕ} {Wq : ScBanach}
    (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq)) : Prop :=
  (∀ k', ((0 : c.φ.model.E 0), k') ∈ c.K →
    ∃ (u : ↥(rangeS (scDeriv c.U (r c.R) 0))) (a : Fin m → ℝ),
      linAt c.U c.R (c.principal g) 0 u + ∑ i, a i • c.principal (t i) 0 = k') ∧
  ∀ w : ↥(rangeS (scDeriv c.U (r c.R) 0)),
    ∃ (u : ↥(rangeS (scDeriv c.U (r c.R) 0))) (a : Fin m → ℝ),
      linAt c.U c.R (c.principal g) 0 u + ∑ i, a i • c.principal (t i) 0 = 0 ∧
      ((w : c.φ.model.E 0) - u) ∈ minimalSubspaceWith T 0

omit [T2Space Y] [ParacompactSpace Y] in
/-- **Adding sections keeps (i)–(ii)** (the text: "adding more sections, the properties (i)–(ii)
will still hold"): if a subfamily `sᵢ = t_{ι(i)}` satisfies them, so does `t`. -/
theorem StrongBundleChart.IsParamGP.comp {c : StrongBundleChart PX P} {k m : ℕ}
    {s : Fin k → X → Y} {t : Fin m → X → Y} (ι : Fin k → Fin m) (hst : ∀ i, s i = t (ι i))
    {n : ℕ} {Wq : ScBanach} {T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq)}
    (h : c.IsParamGP g s T) : c.IsParamGP g t T := by
  refine ⟨fun k' hk' => ?_, fun w => ?_⟩
  · obtain ⟨u, a, hua⟩ := h.1 k' hk'
    obtain ⟨a', ha'⟩ := exists_sum_comp_eq ι a fun j => c.principal (t j) 0
    refine ⟨u, a', ?_⟩
    rw [ha', ← hua]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [hst i]
  · obtain ⟨u, a, hua, hw⟩ := h.2 w
    obtain ⟨a', ha'⟩ := exists_sum_comp_eq ι a fun j => c.principal (t j) 0
    refine ⟨u, a', ?_, hw⟩
    rw [ha', ← hua]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [hst i]

omit [ParacompactSpace X] in
/-- The minimal subspace of the constant presentation of `ℝᵐ` is everything. -/
lemma minimalSubspaceWith_rnPres {m : ℕ} (a : (rnSc m) 0) :
    minimalSubspaceWith (rnPres m) a = ⊤ := by
  ext v
  simp only [Submodule.mem_top, iff_true]
  rw [mem_minimalSubspaceWith]
  intro i; exact i.elim0

end FrontHalf

section ParamGP

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {g : X → Y} {m : ℕ} [ParacompactSpace ((Fin m → ℝ) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))]

open StrongRetr

/-- The product chart `(r ↦ r) × c` of `ℝᵐ × X`, pulled back from the strong bundle chart `c`
(`PullbackChartData.ofProd c 0`, at the point `q₀`). -/
abbrev pc0 (c : StrongBundleChart PX P) (q₀ : pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X)) :
    StrongBundleChart ((rnPolyfold m).prod PX) (pullbackProj P (Prod.snd : (Fin m → ℝ) × X → X)) :=
  (PullbackChartData.ofProd c 0).toChart q₀

omit [T2Space Y] [ParacompactSpace Y]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))] in
/-- `ℝᵐ × T₀O ⊆ T₀(ℝᵐ × O)` in the product chart (with `ofProd_mem_tangent`, equality). -/
lemma ofProd_mem_rangeS (c : StrongBundleChart PX P)
    (q₀ : pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X)) (h0U : (0 : c.φ.model.E 0) ∈ c.U)
    {w : (Fin m → ℝ) × c.φ.model.E 0} (hw : w.2 ∈ rangeS (scDeriv c.U (r c.R) 0)) :
    w ∈ rangeS (scDeriv (pc0 c q₀).U
      (r (pc0 c q₀).R)
      (0 : (pc0 c q₀).φ.model.E 1)) := by
  obtain ⟨v, hv⟩ := hw
  refine ⟨(w.1, v), ?_⟩
  have := PullbackChartData.ofProd_scDeriv_r c 0 q₀ h0U (w.1, v)
  refine this.trans ?_
  exact Prod.ext rfl hv

set_option maxHeartbeats 3200000 in
-- the product chart and the identification `T S̃ = ker F'`
/-- **(i)–(ii) give general position** (the text: "at this point the combined system of sections
already satisfies (i) and (ii)", i.e. `(F, (0, y))` is in general position): if (i)–(ii) hold in
a tame chart `c` centred at the zero `y` of `g`, the parametrized section
`F(λ, y) = g(y) + Σ λᵢ tᵢ(y)` is in general position at `(0, y)` (Definition 5.3.9 (preprint 5.17), in the tame
product chart `(r ↦ r) × c`).  *Proof*: (i) gives `F'(0, y)` onto; (ii) gives
`ker F'(0, y) + T^R = T(ℝᵐ × O)` (at level `0`), so `ker F'(0, y)` has an algebraic complement
inside `T^R` and `(F, (0, y))` is in good position
(`isInGoodPositionIn_of_scComplement_le_reduced`);
then `ker F'(0, y) = T_{(0, y)}S̃` (`exists_isGeneralPositionGerm_iff`) is finite-dimensional and
smooth, and the sc-complement inside `T^R` exists (`exists_scComplement_le`). -/
theorem isGeneralPositionGerm_paramSection_of_isParamGP (hgFt : B.IsScFredholmSectionTame g)
    {t : Fin m → X → Y} (htp : ∀ i, B.IsScPlusSection (t i)) {y : X} (hy0 : IsZeroAt P g y)
    {c : StrongBundleChart PX P} (hc : B.IsTameChart c) (hyV : y ∈ c.φ.source)
    (hφ0 : c.φ y = 0) {n : ℕ} {Wq : ScBanach}
    (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant n Wq 0) (h : c.IsParamGP g t T) :
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsGeneralPositionGerm
      (paramSection g hgFt.isScSmooth.1 t fun i => (htp i).1) (0, y) := by
  classical
  have hgF := hgFt.toIsScFredholmSection
  have hFt := theorem_3_1_21_tame hgFt htp
  have hz0 : IsZeroAt (pullbackProj P Prod.snd)
      (paramSection g hgFt.isScSmooth.1 t fun i => (htp i).1) (0, y) := by
    rw [isZeroAt_paramSection_iff]
    change IsZeroAt P (paramSlice g hgFt.isScSmooth.1 t (fun i => (htp i).1) 0) y
    rw [paramSlice_zero]; exact hy0
  set q₀ := paramSection g hgFt.isScSmooth.1 t (fun i => (htp i).1) (0, y) with hq₀
  have hc'B : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsChart (pc0 c q₀) :=
    (PullbackChartData.ofProd c 0).isChart_toChart B _ hc.1 q₀
  have hc'T : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsTameChart (pc0 c q₀) :=
    ⟨hc'B, PullbackChartData.ofProd_isTame c 0 q₀ hc.2⟩
  have hyV' : ((0 : Fin m → ℝ), y) ∈ (pc0 c q₀).φ.source := ⟨mem_univ _, hyV⟩
  have hc'0 : (pc0 c q₀).φ (0, y) = 0 := ofProd_apply_eq_zero c 0 q₀ hφ0
  have hz' : (pc0 c q₀).φ.model.E.toBase 1 (0 : (pc0 c q₀).φ.model.E 1) = (pc0 c q₀).φ (0, y) := by
    rw [map_zero, hc'0]
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := hφ0 ▸ c.φ.mapsTo_model y hyV
  have h0U : (0 : c.φ.model.E 0) ∈ c.U := mem_U_of_mem_O c.isRetraction (c.r_image ▸ h0O)
  -- (i): surjectivity
  have hsurjF := isLinSurjAt_paramSection_zero_of_spanning hgF htp hc.1 hyV hφ0 q₀ h.1
  have hsurj' := hsurjF.linAt_surjective hFt.isScSmooth hz0 hc'B hyV' hz'
  -- the presentation of the product quadrant and `E_0 = ℝᵐ × E_0`
  have hT' : (pc0 c q₀).φ.model.C = (prodPresentation (rnPres m) T) 0 ⁻¹'
      quadrant (0 + n) ((ScBanach.const (Fin m → ℝ)).prod Wq) 0 :=
    prod_eq_prodPresentation (rnPres m) T (rnPres_eq (m := m)) hT
  have hmin : minimalSubspaceWith (prodPresentation (rnPres m) T)
      (0 : ((rnSc m).prod c.φ.model.E) 0) =
      (⊤ : Submodule ℝ (Fin m → ℝ)).prod (minimalSubspaceWith T 0) := by
    rw [minimalSubspaceWith_prodPresentation]
    simp only [Prod.fst_zero, Prod.snd_zero, minimalSubspaceWith_rnPres]
  have hb0 : ((rnSc m).prod c.φ.model.E).toBase 1 (0 : ((rnSc m).prod c.φ.model.E) 1) = 0 :=
    map_zero _
  set R' := (pc0 c q₀).isRetraction.baseRetraction (pc0 c q₀).relOpen with hR'
  have hzR : (0 : (pc0 c q₀).φ.model.E 1) ∈ (pc0 c q₀).φ.model.E.lvlSet R'.retract 1 := by
    rw [ScBanach.mem_lvlSet, (pc0 c q₀).base_retract, hz']; exact (pc0 c q₀).φ.mapsTo_model _ hyV'
  have hzs : (0 : (pc0 c q₀).φ.model.E 1) ∈ (pc0 c q₀).φ.model.E.smoothLvl 1 := by
    change (pc0 c q₀).φ.model.E.toBase 1 0 ∈ (pc0 c q₀).φ.model.E.smooth
    rw [map_zero]; exact (pc0 c q₀).φ.model.E.smooth.zero_mem
  -- (ii): `ker F'(0, y) + T^R = T₀(ℝᵐ × O)`
  have hsup : (pc0 c q₀).linKer (paramSection g hgFt.isScSmooth.1 t fun i => (htp i).1) 0 ⊔
      reducedTangentSpaceWith R' (prodPresentation (rnPres m) T) 0 =
        LinearMap.range (scDeriv R'.U R' 0 :
        (pc0 c q₀).φ.model.E 0 →ₗ[ℝ] (pc0 c q₀).φ.model.E 0) := by
    refine le_antisymm (sup_le ((pc0 c q₀).linKer_le _ 0) inf_le_left) fun v hv => ?_
    have hv2 : v.2 ∈ rangeS (scDeriv c.U (r c.R) 0) :=
      PullbackChartData.ofProd_mem_tangent c 0 q₀ h0U hv
    obtain ⟨u, a, hua, hwu⟩ := h.2 ⟨v.2, hv2⟩
    have hk : ((a, (u : c.φ.model.E 0)) : (Fin m → ℝ) × c.φ.model.E 0) ∈
        rangeS (scDeriv (pc0 c q₀).U (r (pc0 c q₀).R) 0) := ofProd_mem_rangeS c q₀ h0U u.2
    have hkK : ((a, (u : c.φ.model.E 0)) : (Fin m → ℝ) × c.φ.model.E 0) ∈
        (pc0 c q₀).linKer (paramSection g hgFt.isScSmooth.1 t fun i => (htp i).1) 0 := by
      refine ((pc0 c q₀).mem_linKer_iff _ 0 _).2 ⟨hk, ?_⟩
      rw [linAt_paramSection_zero hgF htp hc.1 h0O q₀ hk]
      exact hua
    let k : (pc0 c q₀).φ.model.E 0 :=
      ((a, (u : c.φ.model.E 0)) : (Fin m → ℝ) × c.φ.model.E 0)
    have hrest : v - k ∈ reducedTangentSpaceWith R' (prodPresentation (rnPres m) T) 0 := by
      refine ⟨Submodule.sub_mem _ hv hk, ?_⟩
      have hb0' : (pc0 c q₀).φ.model.E.toBase 1
          (0 : (pc0 c q₀).φ.model.E 1) = 0 := map_zero _
      rw [hb0']
      change v - k ∈ minimalSubspaceWith (prodPresentation (rnPres m) T)
        (0 : ((rnSc m).prod c.φ.model.E) 0)
      rw [hmin]
      exact ⟨Submodule.mem_top, hwu⟩
    have : v = k + (v - k) := by abel
    rw [this]
    exact Submodule.add_mem_sup hkK hrest
  -- good position of `(F, (0, y))`
  obtain ⟨B'', hB''T, hKB, hKBM⟩ := exists_compl_le_of_sup_eq le_rfl ((pc0 c q₀).linKer_le _ 0)
    le_rfl inf_le_left hsup
  have hR'T : R'.IsTameWith (prodPresentation (rnPres m) T) :=
    hc'T.2 _ _ (prodPresentation (rnPres m) T) hT'
  have hker := isInGoodPositionIn_of_scComplement_le_reduced (prodPresentation (rnPres m) T) hR'T
    hzR hzs hB''T hKB hKBM
  have hpt : (pc0 c q₀).φ (0, y) =
      ((ScBanach.prodScale (ScBanach.constScale (Fin m → ℝ)) c.φ.model.E.toScScale).toBase 1)
        0 := by
    rw [hc'0]; exact (map_zero _).symm
  have hker' : IsInGoodPositionIn (pc0 c q₀).φ.model.E
      (rangeS (scDeriv (pc0 c q₀).U
        (r (pc0 c q₀).R) 0))
      (partialQuadrantAtWith (prodPresentation (rnPres m) T)
        ((pc0 c q₀).φ (0, y)))
      ((LinearMap.ker (linAt (pc0 c q₀).U
        (pc0 c q₀).R
        ((pc0 c q₀).principal
          (paramSection g hgFt.isScSmooth.1 t fun i => (htp i).1)) 0 :
        ↥(rangeS (scDeriv (pc0 c q₀).U
          (r (pc0 c q₀).R) 0)) →ₗ[ℝ]
          (pc0 c q₀).F 0)).map
        (rangeS (scDeriv (pc0 c q₀).U
          (r (pc0 c q₀).R) 0)).subtype) := by
    rw [hpt]; exact hker
  have hFs : ((0 : Fin m → ℝ), y) ∈ ((rnPolyfold m).prod PX).smoothSet :=
    hFt.mem_smoothSet_of_isZeroAt hz0
  have hgood := (StrongBundle.isGoodPositionGerm_of_linAt_surj hFt.isScSmooth
    (hFt.germ _ hFs) hz0 hc'B hyV' hz' (prodPresentation (rnPres m) T) hT' hsurj' hker').toTame
    hFt.isScSmooth
    (hFt.germTame _ hFs) hz0
  -- `ker F'(0, y) = T_{(0, y)}S̃`: finite-dimensional and smooth
  obtain ⟨V, hVo, h0V, -, hAV, -, hidV⟩ := exists_isGeneralPositionGerm_iff hFt hgood hz0
  have hyA : ((0 : Fin m → ℝ), y) ∈ solutionSet (pullbackProj P Prod.snd)
      (paramSection g hgFt.isScSmooth.1 t fun i => (htp i).1) ∩ V := ⟨hz0, h0V⟩
  set d := hAV.data hyA with hd
  have hyG : ((0 : Fin m → ℝ), y) ∈ d.toSubData.shrink (pc0 c q₀).φ :=
    d.toSubData.mem_shrink (pc0 c q₀).φ hyA (hAV.mem_data_V hyA) hyV'
  have hT0 := hidV _ h0V hz0 (pc0 c q₀) hc'B hyV' _ (d.toSubData.isOpen_shrink (pc0 c q₀).φ)
    (d.toSubData.shrink_subset_source (pc0 c q₀).φ) hyG
    (d.toSubData.isScRetract_image (pc0 c q₀).φ (pc0 c q₀).isChart) 0 hz'
  obtain ⟨t', ht', ht'p⟩ := d.isScPlusRetract_image (pc0 c q₀).isChart
    (((rnPolyfold m).prod PX).levelMk 1 _ (d.mem_levelSet_one hyA (hAV.mem_data_V hyA)))
  have hz0t' : (0 : (pc0 c q₀).φ.model.E 1) ∈ (pc0 c q₀).φ.model.E.lvlSet t'.retract 1 := by
    rw [ScBanach.mem_lvlSet, ht', hz']; exact ⟨_, ⟨hyG, hyA⟩, rfl⟩
  have hKeq : LinearMap.range
      (scDeriv t'.U t' 0 : (pc0 c q₀).φ.model.E 0 →ₗ[ℝ] (pc0 c q₀).φ.model.E 0) =
      (pc0 c q₀).linKer (paramSection g hgFt.isScSmooth.1 t fun i => (htp i).1) 0 := by
    apply SetLike.coe_injective
    rw [← tangentSpace_eq_coe_submodule t' hz0t', ht', hT0]
  have hz0t'' : (pc0 c q₀).φ.model.E.toBase 1 (0 : (pc0 c q₀).φ.model.E 1) ∈ t'.retract := hz0t'
  have hfin : FiniteDimensional ℝ
      ((pc0 c q₀).linKer (paramSection g hgFt.isScSmooth.1 t fun i => (htp i).1) 0) := by
    rw [← hKeq]
    exact lemma_4_1_7_ii ht'p hz0t''
  have hsm : (pc0 c q₀).linKer (paramSection g hgFt.isScSmooth.1 t fun i => (htp i).1) 0 ≤
      (pc0 c q₀).φ.model.E.smooth := by
    have : FiniteDimensional ℝ
        (LinearMap.range
          (scDeriv t'.U t' 0 : (pc0 c q₀).φ.model.E 0 →ₗ[ℝ] (pc0 c q₀).φ.model.E 0)) := by
      rw [hKeq]; exact hfin
    rw [← hKeq]
    exact ((pc0 c q₀).φ.model.E.proposition_1_1_7_iff _).1
      (t'.isScSplitting_range_scDeriv hz0t' hzs).1
  -- Definition 5.3.9 (preprint 5.17)
  refine ⟨(pc0 c q₀), hc'T, hyV', 0, hz', hsurj', fun {n₂ Wq₂} T₂ hT₂ => ?_⟩
  have hR'T₂ : R'.IsTameWith T₂ := hc'T.2 _ _ T₂ hT₂
  obtain ⟨-, hTRsc, -⟩ := proposition_2_5_6_partialCone hT₂ hR'T₂ hzR hzs
  have hred : reducedTangentSpaceWith R' T₂ 0 =
      reducedTangentSpaceWith R' (prodPresentation (rnPres m) T) 0 := by
    unfold reducedTangentSpaceWith
    rw [minimalSubspaceWith_eq T₂ hT₂ (prodPresentation (rnPres m) T) hT' (by
      rw [map_zero, ← hc'0]
      exact (pc0 c q₀).φ.model.O_subset_C ((pc0 c q₀).φ.mapsTo_model _ hyV'))]
  have hM : LinearMap.range
      (scDeriv R'.U R' 0 : (pc0 c q₀).φ.model.E 0 →ₗ[ℝ] (pc0 c q₀).φ.model.E 0) =
      (pc0 c q₀).linKer (paramSection g hgFt.isScSmooth.1 t fun i => (htp i).1) 0 ⊔
        reducedTangentSpaceWith R' T₂ 0 := by rw [hred, hsup]
  obtain ⟨Bc, hBcT, hBcsc, hsplit⟩ := exists_scComplement_le hsm hTRsc hM
  exact ⟨Bc, hBcT, hBcsc, hsplit⟩

set_option maxHeartbeats 3200000 in
-- the product chart and the identification `T S̃ = ker F'`
/-- **General position of `F` at `(0, y)` gives (i)–(ii) in every tame chart centred at `y`**
(the converse of `isGeneralPositionGerm_paramSection_of_isParamGP`): (i) is the surjectivity of
`F'(0, y)` read in the product chart; for (ii), `S̃` is in general position at `(0, y)`
(Definition 4.2.10 (preprint 4.21), `exists_isGeneralPositionGerm_iff`), and in the product chart its tangent space is
`ker F'(0, y)`, which therefore has a complement inside `ℝᵐ × T^R`. -/
theorem isParamGP_of_isGeneralPositionGerm (hgFt : B.IsScFredholmSectionTame g)
    {t : Fin m → X → Y} (htp : ∀ i, B.IsScPlusSection (t i)) {y : X} (hy0 : IsZeroAt P g y)
    {c : StrongBundleChart PX P} (hc : B.IsTameChart c) (hyV : y ∈ c.φ.source)
    (hφ0 : c.φ y = 0) {n : ℕ} {Wq : ScBanach}
    (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant n Wq 0)
    (hgp : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsGeneralPositionGerm
      (paramSection g hgFt.isScSmooth.1 t fun i => (htp i).1) (0, y)) :
    c.IsParamGP g t T := by
  classical
  have hgF := hgFt.toIsScFredholmSection
  have hFt := theorem_3_1_21_tame hgFt htp
  have hz0 : IsZeroAt (pullbackProj P Prod.snd)
      (paramSection g hgFt.isScSmooth.1 t fun i => (htp i).1) (0, y) := by
    rw [isZeroAt_paramSection_iff]
    change IsZeroAt P (paramSlice g hgFt.isScSmooth.1 t (fun i => (htp i).1) 0) y
    rw [paramSlice_zero]; exact hy0
  set q₀ := paramSection g hgFt.isScSmooth.1 t (fun i => (htp i).1) (0, y) with hq₀
  have hc'B : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsChart
      (pc0 c q₀) :=
    (PullbackChartData.ofProd c 0).isChart_toChart B _ hc.1 q₀
  have hyV' : ((0 : Fin m → ℝ), y) ∈ (pc0 c q₀).φ.source :=
    ⟨mem_univ _, hyV⟩
  have hc'0 : (pc0 c q₀).φ (0, y) = 0 :=
    ofProd_apply_eq_zero c 0 q₀ hφ0
  have hz' : (pc0 c q₀).φ.model.E.toBase 1
      (0 : (pc0 c q₀).φ.model.E 1) =
      (pc0 c q₀).φ (0, y) := by rw [map_zero, hc'0]
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := hφ0 ▸ c.φ.mapsTo_model y hyV
  have h0U : (0 : c.φ.model.E 0) ∈ c.U := mem_U_of_mem_O c.isRetraction (c.r_image ▸ h0O)
  have hsurj' := (hgp.isLinSurjAt).linAt_surjective hFt.isScSmooth hz0 hc'B hyV' hz'
  refine ⟨fun k' hk' => ?_, fun w => ?_⟩
  · -- (i)
    have hkχ : ((pc0 c q₀).φ (0, y), k') ∈
        (pc0 c q₀).K := by
      rw [hc'0]; exact (mem_K_ofProd_zero_iff c 0 q₀ h0O k').2 hk'
    obtain ⟨⟨v, hv⟩, hvk⟩ := hsurj' k' hkχ
    rw [linAt_paramSection_zero hgF htp hc.1 h0O q₀ hv] at hvk
    exact ⟨_, v.1, hvk⟩
  · -- (ii)
    have hgood := hgp.isGoodPositionGermTame hFt hz0
    obtain ⟨V, -, h0V, -, hAV, hiff, hidV⟩ := exists_isGeneralPositionGerm_iff hFt hgood hz0
    have hyA : ((0 : Fin m → ℝ), y) ∈ solutionSet (pullbackProj P Prod.snd)
        (paramSection g hgFt.isScSmooth.1 t fun i => (htp i).1) ∩ V := ⟨hz0, h0V⟩
    have hA := (hiff _ h0V hz0).1 hgp
    set d := hAV.data hyA with hd
    have hT' : (pc0 c q₀).φ.model.C =
        (prodPresentation (rnPres m) T) 0 ⁻¹'
          quadrant (0 + n) ((ScBanach.const (Fin m → ℝ)).prod Wq) 0 :=
      prod_eq_prodPresentation (rnPres m) T (rnPres_eq (m := m)) hT
    obtain ⟨N, M, Bs, hN, hM, hBM, -, hsplit⟩ := hA.isGeneralPositionChart d
      (pc0 c q₀).isChart (prodPresentation (rnPres m) T) hT'
      (hAV.mem_data_V hyA) hyV' hz'
    have hyG : ((0 : Fin m → ℝ), y) ∈ d.toSubData.shrink
        (pc0 c q₀).φ :=
      d.toSubData.mem_shrink _ hyA (hAV.mem_data_V hyA) hyV'
    have hT0 := hidV _ h0V hz0 _ hc'B hyV' _ (d.toSubData.isOpen_shrink _)
      (d.toSubData.shrink_subset_source _) hyG
      (d.toSubData.isScRetract_image _ (pc0 c q₀).isChart) 0 hz'
    have hNeq : N = (pc0 c q₀).linKer
        (paramSection g hgFt.isScSmooth.1 t fun i => (htp i).1) 0 :=
      SetLike.coe_injective (hN.trans hT0)
    have hzO : (0 : (pc0 c q₀).φ.model.E 1) ∈
        (pc0 c q₀).φ.model.E.lvlSet
          ((pc0 c q₀).isRetraction.baseRetraction
            (pc0 c q₀).relOpen).retract 1 := by
      rw [ScBanach.mem_lvlSet, (pc0 c q₀).base_retract, hz']
      exact (pc0 c q₀).φ.mapsTo_model _ hyV'
    have hMeq : M = rangeS (scDeriv (pc0 c q₀).U
        (r (pc0 c q₀).R) 0) := by
      apply SetLike.coe_injective
      rw [hM, ← (pc0 c q₀).base_retract]
      exact tangentSpace_eq_coe_submodule _ hzO
    have h0 := hsplit 0
    rw [ScBanach.levelSub_zero, ScBanach.levelSub_zero, ScBanach.levelSub_zero] at h0
    let p : (pc0 c q₀).φ.model.E 0 :=
      (((0 : Fin m → ℝ), (w : c.φ.model.E 0)) : (Fin m → ℝ) × c.φ.model.E 0)
    have hp : p ∈ M := by rw [hMeq]; exact ofProd_mem_rangeS c q₀ h0U w.2
    rw [← h0.2] at hp
    obtain ⟨k, hk, b, hb, hkb⟩ := Submodule.mem_sup.1 hp
    rw [hNeq] at hk
    obtain ⟨hkr, hk0⟩ := ((pc0 c q₀).mem_linKer_iff _ 0 k).1 hk
    rw [linAt_paramSection_zero hgF htp hc.1 h0O q₀ hkr] at hk0
    have hbmin := (hBM hb).2
    have hb0' : (pc0 c q₀).φ.model.E.toBase 1
        (0 : (pc0 c q₀).φ.model.E 1) = 0 := map_zero _
    rw [hb0'] at hbmin
    change b ∈ minimalSubspaceWith (prodPresentation (rnPres m) T)
      (0 : ((rnSc m).prod c.φ.model.E) 0) at hbmin
    rw [minimalSubspaceWith_prodPresentation] at hbmin
    simp only [Prod.fst_zero, Prod.snd_zero, minimalSubspaceWith_rnPres] at hbmin
    have hb2 : (show (Fin m → ℝ) × c.φ.model.E 0 from b).2 ∈ minimalSubspaceWith T 0 :=
      (Submodule.mem_prod.1 hbmin).2
    have hkb2 : (show (Fin m → ℝ) × c.φ.model.E 0 from k).2 +
        (show (Fin m → ℝ) × c.φ.model.E 0 from b).2 = (w : c.φ.model.E 0) :=
      congrArg Prod.snd hkb
    refine ⟨_, (show (Fin m → ℝ) × c.φ.model.E 0 from k).1, hk0, ?_⟩
    rw [← hkb2, add_sub_cancel_left]
    exact hb2

end ParamGP

/-! ### The construction of sections with (i)–(ii) at a zero -/

section Construction

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {g : X → Y}

open StrongRetr

/-- The spanning condition (i) read in a chart `c` centred at `y`, from the surjectivity of
`F'(0, y)` (`IsLinSurjAt`, chart independent). -/
theorem spanning_of_isLinSurjAt {m : ℕ} [ParacompactSpace ((Fin m → ℝ) × X)]
    [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin m → ℝ) × X → X))]
    (hgF : B.IsScFredholmSection g) {t : Fin m → X → Y} (htp : ∀ i, B.IsScPlusSection (t i))
    {y : X} (hy0 : IsZeroAt P g y) {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (hyV : y ∈ c.φ.source) (hφ0 : c.φ y = 0)
    (hsurj : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsLinSurjAt
      (paramSection g hgF.isScSmooth.1 t fun i => (htp i).1) (0, y)) :
    ∀ k', ((0 : c.φ.model.E 0), k') ∈ c.K →
      ∃ (u : ↥(rangeS (scDeriv c.U (r c.R) 0))) (a : Fin m → ℝ),
        linAt c.U c.R (c.principal g) 0 u + ∑ i, a i • c.principal (t i) 0 = k' := by
  have hFsm := (theorem_3_1_21_preprint hgF htp).isScSmooth
  have hz0 : IsZeroAt (pullbackProj P Prod.snd)
      (paramSection g hgF.isScSmooth.1 t fun i => (htp i).1) (0, y) := by
    rw [isZeroAt_paramSection_iff]
    change IsZeroAt P (paramSlice g hgF.isScSmooth.1 t (fun i => (htp i).1) 0) y
    rw [paramSlice_zero]; exact hy0
  set q₀ := paramSection g hgF.isScSmooth.1 t (fun i => (htp i).1) (0, y) with hq₀
  have hc'B : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsChart
      (pc0 c q₀) :=
    (PullbackChartData.ofProd c 0).isChart_toChart B _ hc q₀
  have hyV' : ((0 : Fin m → ℝ), y) ∈ (pc0 c q₀).φ.source :=
    ⟨mem_univ _, hyV⟩
  have hc'0 : (pc0 c q₀).φ (0, y) = 0 :=
    ofProd_apply_eq_zero c 0 q₀ hφ0
  have hz' : (pc0 c q₀).φ.model.E.toBase 1
      (0 : (pc0 c q₀).φ.model.E 1) =
      (pc0 c q₀).φ (0, y) := by rw [map_zero, hc'0]
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := hφ0 ▸ c.φ.mapsTo_model y hyV
  have hsurj' := hsurj.linAt_surjective hFsm hz0 hc'B hyV' hz'
  intro k' hk'
  have hkχ : ((pc0 c q₀).φ (0, y), k') ∈
      (pc0 c q₀).K := by
    rw [hc'0]; exact (mem_K_ofProd_zero_iff c 0 q₀ h0O k').2 hk'
  obtain ⟨⟨v, hv⟩, hvk⟩ := hsurj' k' hkχ
  rw [linAt_paramSection_zero hgF htp hc h0O q₀ hv] at hvk
  exact ⟨_, v.1, hvk⟩

set_option maxHeartbeats 3200000 in
-- the coordinates of the tame chart and Lemma 5.3.3 (preprint 5.11) at finitely many points
/-- **Sections with (i)–(ii) at a zero** (the text: "We take enough sc⁺-sections to obtain the
surjectivity. We take a linear subspace `L` complementing `T^R_xX` in `T_xX` and add sections,
which at `x` span the image `f'(x)L`."): let `X` admit sc-smooth bump functions, `N` be an
auxiliary norm, `g` an sc-Fredholm section with tame germ data, `x` a zero of `g`, `c` a tame
chart centred at `x` (presentation `T`) and `U ∋ x` open.  Then there are finitely many allowable
sc⁺-sections supported in `U` with (i)–(ii) at `(0, x)` in `c` (`IsParamGP`).  *Proof*: the
spanning sections of `exists_spanning_sections` give (i); for (ii), the coordinates `λ_{I(0)}`
map `T₀O` onto `ℝ^{I(0)}` with kernel `T^R_0O` (Proposition 2.5.6 (preprint 2.36)), and onto already on the dense
smooth vectors of `T₀O`, so there are smooth `l_i ∈ T₀O` with `λ(l_i) = e_i`; the sections of
Lemma 5.3.3 (preprint 5.11) through the smooth points `Φ⁻¹(0, Lin_g(0)l_i)`, rescaled to be allowable, span
`Lin_g(0)L` for `L = span{l_i}`. -/
theorem exists_sections_isParamGP (hbump : PX.AdmitsBumpFunctions) {N : B.One → ℝ}
    (hN : B.IsAuxNorm N) (hgFt : B.IsScFredholmSectionTame g) {x : X} (hx0 : IsZeroAt P g x)
    {c : StrongBundleChart PX P} (hc : B.IsTameChart c) (hxV : x ∈ c.φ.source)
    (hφ0 : c.φ x = 0) {n : ℕ} {Wq : ScBanach}
    (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant n Wq 0) {U : Set X} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ (k : ℕ) (s : Fin k → X → Y) (_ : ∀ i, B.IsScPlusSection (s i)),
      (∀ i, sectionSupport P (s i) ⊆ U) ∧
      (∀ i y (hy : s i y ∈ B.oneSet), N (B.oneMk (s i y) hy) ≤ 1) ∧ c.IsParamGP g s T := by
  classical
  have hgF := hgFt.toIsScFredholmSection
  have hxs : x ∈ PX.smoothSet := hgF.mem_smoothSet_of_isZeroAt hx0
  -- (i): the spanning sections, read in `c`
  obtain ⟨k₁, s₁, hs₁, hs₁supp, hs₁N, c₁, hc₁, hxV₁, hφ₁, hspan₁⟩ :=
    exists_spanning_sections hbump hN hgF hx0 hU hxU
  have := MPolyfold.paracompactSpace_prod (rnPolyfold k₁) PX
  have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin k₁ → ℝ) × X → X))
    ((rnPolyfold k₁).prod PX) B
  have hsurj₁ := isLinSurjAt_paramSection_zero_of_spanning hgF hs₁ hc₁ hxV₁ hφ₁
    (paramSection g hgF.isScSmooth.1 s₁ (fun i => (hs₁ i).1) (0, x)) hspan₁
  have hspan := spanning_of_isLinSurjAt hgF hs₁ hx0 hc.1 hxV hφ0 hsurj₁
  -- (ii): the coordinates of the tame chart
  set R := c.isRetraction.baseRetraction c.relOpen with hRdef
  have hRT : R.IsTameWith T := hc.2 n Wq T hT
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := hφ0 ▸ c.φ.mapsTo_model x hxV
  have h0O' : (0 : c.φ.model.E 0) ∈ r c.R '' c.U := c.r_image ▸ h0O
  have h0U : (0 : c.φ.model.E 0) ∈ c.U := mem_U_of_mem_O c.isRetraction h0O'
  have hz : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) = c.φ x := by rw [map_zero, hφ0]
  have hzR : (0 : c.φ.model.E 1) ∈ c.φ.model.E.lvlSet R.retract 1 := by
    rw [ScBanach.mem_lvlSet, c.base_retract, hz]; exact c.φ.mapsTo_model x hxV
  have hzs : (0 : c.φ.model.E 1) ∈ c.φ.model.E.smoothLvl 1 := by
    change c.φ.model.E.toBase 1 0 ∈ c.φ.model.E.smooth
    rw [map_zero]; exact c.φ.model.E.smooth.zero_mem
  set e := c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) with he
  have he0 : e = 0 := map_zero _
  set M := LinearMap.range (scDeriv R.U R 0 : c.φ.model.E 0 →ₗ[ℝ] c.φ.model.E 0) with hMdef
  set I := {i : Fin n // (T 0 e).1 i = 0} with hIdef
  set f : M →ₗ[ℝ] (I → ℝ) := (coordMapL T e : c.φ.model.E 0 →ₗ[ℝ] (I → ℝ)) ∘ₗ M.subtype
    with hf
  have hker : LinearMap.ker f = (reducedTangentSpaceWith R T 0).comap M.subtype := by
    ext ⟨v, hv⟩
    simp only [hf, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.coe_subtype,
      Submodule.mem_comap, reducedTangentSpaceWith, Submodule.mem_inf]
    exact ⟨fun h => ⟨hv, h⟩, fun h => h.2⟩
  have hq := quotDim_reducedTangentSpaceWith_eq hRT hzR hzs
  rw [quotDim, ← hker] at hq
  have hrange : LinearMap.range f = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← (LinearMap.quotKerEquivRange f).finrank_eq, hq, Module.finrank_fintype_fun_eq_card,
      Fintype.card_subtype]
    rfl
  -- smooth preimages
  obtain ⟨hMsc, -, -⟩ := proposition_2_5_6_partialCone hT hRT hzR hzs
  set D : Submodule ℝ (c.φ.model.E 0) := M ⊓ c.φ.model.E.smooth with hD
  set S : Submodule ℝ (I → ℝ) := D.map (coordMapL T e : c.φ.model.E 0 →ₗ[ℝ] (I → ℝ)) with hS
  have hSclosed : IsClosed (S : Set (I → ℝ)) := S.closed_of_finiteDimensional
  have hpre : ∀ v : I → ℝ, ∃ l ∈ D, coordMapL T e l = v := by
    intro v
    have hv : v ∈ LinearMap.range f := by rw [hrange]; exact Submodule.mem_top
    obtain ⟨⟨w, hwM⟩, hwv⟩ := hv
    have hwcl : w ∈ closure ((M : Set (c.φ.model.E 0)) ∩ c.φ.model.E.smoothLvl 0) := by
      have := hMsc.2 0 (show w ∈ c.φ.model.E.levelSub M 0 by
        rw [ScBanach.levelSub_zero]; exact hwM)
      rwa [ScBanach.levelSub_zero] at this
    have hvS : v ∈ S := by
      have h1 : coordMapL T e w ∈ closure ((coordMapL T e) ''
          ((M : Set (c.φ.model.E 0)) ∩ c.φ.model.E.smoothLvl 0)) :=
        image_closure_subset_closure_image (coordMapL T e).continuous ⟨w, hwcl, rfl⟩
      have h2 : closure ((coordMapL T e) ''
          ((M : Set (c.φ.model.E 0)) ∩ c.φ.model.E.smoothLvl 0)) ⊆ (S : Set (I → ℝ)) := by
        refine closure_minimal ?_ hSclosed
        rintro _ ⟨l, ⟨hlM, hls⟩, rfl⟩
        exact ⟨l, ⟨hlM, hls⟩, rfl⟩
      have h3 := h2 h1
      rwa [← hwv]
    obtain ⟨l, hlD, hl⟩ := hvS
    exact ⟨l, hlD, hl⟩
  choose l hlD hlv using fun i : I => hpre (Pi.single i 1)
  -- the smooth fibre points `Φ⁻¹(0, Lin_g(0) lᵢ)`
  have hgr : IsScSmooth c.U (c.principal g ∘ r c.R) :=
    (((hgF.isScSmooth.isScSmoothRetractMap hc.1).comp_isScSmooth
      (c.isRetraction.baseRetraction c.relOpen) c.base_retract).snd c.relOpen.isScDomain).congr
      c.relOpen.isScDomain fun _ _ => rfl
  have hz1U : (0 : c.φ.model.E 1) ∈ c.φ.model.E.lvlSet c.U 1 := by
    rw [ScBanach.mem_lvlSet, map_zero]; exact h0U
  have hop := hgr.isSc1.isSc1With_scDeriv.scOperator_deriv hz1U hzs
  set d : I → c.F 0 := fun i => linAt c.U c.R (c.principal g) 0 ⟨l i, (hlD i).1⟩ with hd
  have hdK : ∀ i, ((0 : c.φ.model.E 0), d i) ∈ c.K := fun i => by
    have hzO : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) ∈ r c.R '' c.U := by
      rw [map_zero]; exact h0O'
    have hmem := rho_scDeriv_comp_r c.relOpen c.isRetraction
      (hgF.isScSmooth.isSc1_principal_comp_r hc.1)
      (fun x hx => c.principal_mem_K hgF.isScSmooth.1 (c.r_image ▸ hx)) hzO
      (by rw [map_zero, ← hφ0]; exact (c.isZeroAt_iff hgF.isScSmooth.1 hxV).1 hx0) (l i)
    have hzU : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) ∈ c.U := by rw [map_zero]; exact h0U
    have : d i ∈ rangeS (ρCLM c.isRetraction hzU) := ⟨_, hmem⟩
    have h2 := (mem_rangeS_ρCLM_iff c.isRetraction hzO hzU).1 this
    rwa [map_zero] at h2
  have hdsm : ∀ i, d i ∈ c.F.smooth := fun i => by
    refine c.F.mem_smooth_iff.2 fun j => ?_
    obtain ⟨Tj, hTj⟩ := hop j
    obtain ⟨lj, hlj⟩ := c.φ.model.E.mem_smooth_iff.1 (hlD i).2 j
    exact ⟨Tj lj, by rw [hTj, hlj]; rfl⟩
  have hφsymm0 : c.φ.symm 0 = x := by rw [← hφ0]; exact c.φ.symm_apply_apply hxV
  set ef : I → Y := fun i => c.toPartialEquiv.symm (0, d i) with hefdef
  have hPe : ∀ i, P (ef i) = x := fun i => by
    change P (c.toPartialEquiv.symm (0, d i)) = x
    rw [c.proj_symm (hdK i)]; exact hφsymm0
  have hesm : ∀ i, ef i ∈ B.toMPolyfold0.smoothSet := fun i =>
    mem_smoothSet_toMPolyfold0_of_chart hc.1 (hdK i) c.φ.model.E.smooth.zero_mem (hdsm i)
  -- Lemma 5.3.3 (preprint 5.11) at each point, rescaled
  have hsec : ∀ i, ∃ he1 : ef i ∈ B.oneSet, ∃ s : X → Y, B.IsScPlusSection s ∧ s x = ef i ∧
      sectionSupport P s ⊆ U ∧
      ∀ y (hy : s y ∈ B.oneSet), N (B.oneMk (s y) hy) < N (B.oneMk (ef i) he1) + 1 :=
    fun i => lemma_5_3_3 hbump hN hxs (hesm i) (hPe i) one_pos hU hxU
  choose he1 s₂ hs₂ hs₂x hs₂supp hs₂N using hsec
  set Mi : I → ℝ := fun i => N (B.oneMk (ef i) (he1 i)) + 1 with hMidef
  have hMpos : ∀ i, 0 < Mi i := fun i => by
    have := hN.nonneg (B.oneMk (ef i) (he1 i))
    simp only [hMidef]; linarith
  set s₂' : I → X → Y := fun i => sectionSmul P (fun _ => (Mi i)⁻¹) (s₂ i) with hs₂'def
  have hs₂'p : ∀ i, B.IsScPlusSection (s₂' i) := fun i =>
    (hs₂ i).smul_left (isScSmoothMap_real_const _)
  have hprin : ∀ i, c.principal (s₂' i) 0 = (Mi i)⁻¹ • d i := fun i => by
    change c.principal (sectionSmul P (fun _ => (Mi i)⁻¹) (s₂ i)) 0 = _
    rw [principal_sectionSmul_const c (hs₂ i).1 _ h0O]
    unfold StrongBundleChart.principal
    rw [hφsymm0, hs₂x i]
    change (Mi i)⁻¹ • (c (c.toPartialEquiv.symm (0, d i))).2 = _
    rw [c.apply_symm (hdK i)]
  -- the united family on `Fin (k₁ + k₂)`
  set k₂ := Fintype.card I with hk₂
  set eI := Fintype.equivFin I with heI
  set s : Fin (k₁ + k₂) → X → Y := Fin.append s₁ (fun j => s₂' (eI.symm j)) with hsdef
  have hsl : ∀ i, s (Fin.castAdd k₂ i) = s₁ i := fun i => Fin.append_left _ _ i
  have hsr : ∀ j, s (Fin.natAdd k₁ (eI j)) = s₂' j := fun j => by
    rw [hsdef, Fin.append_right, Equiv.symm_apply_apply]
  have hsp : ∀ i, B.IsScPlusSection (s i) := by
    refine Fin.addCases (fun i => ?_) (fun j => ?_)
    · rw [hsl]; exact hs₁ i
    · rw [show Fin.natAdd k₁ j = Fin.natAdd k₁ (eI (eI.symm j)) by rw [Equiv.apply_symm_apply],
        hsr]
      exact hs₂'p _
  refine ⟨k₁ + k₂, s, hsp, ?_, ?_, ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun j => ?_)
    · rw [hsl]; exact hs₁supp i
    · rw [show Fin.natAdd k₁ j = Fin.natAdd k₁ (eI (eI.symm j)) by rw [Equiv.apply_symm_apply],
        hsr]
      exact (sectionSupport_sectionSmul_const_subset (hs₂ _).1 _).trans (hs₂supp _)
  · refine Fin.addCases (fun i y hy => ?_) (fun j y hy => ?_)
    · revert hy; rw [hsl]; exact hs₁N i y
    · revert hy
      rw [show Fin.natAdd k₁ j = Fin.natAdd k₁ (eI (eI.symm j)) by rw [Equiv.apply_symm_apply],
        hsr]
      intro hy
      set i := eI.symm j
      rw [hN.oneMk_sectionSmul_const (hs₂ i) _ y hy, abs_of_pos (inv_pos.2 (hMpos i))]
      have := hs₂N i y ((hs₂ i).mem_oneSet y)
      calc (Mi i)⁻¹ * N (B.oneMk (s₂ i y) ((hs₂ i).mem_oneSet y)) ≤ (Mi i)⁻¹ * Mi i :=
            mul_le_mul_of_nonneg_left this.le (inv_pos.2 (hMpos i)).le
        _ = 1 := inv_mul_cancel₀ (hMpos i).ne'
  · -- (i)
    intro k' hk'
    obtain ⟨u, a, hua⟩ := hspan k' hk'
    obtain ⟨a', ha'⟩ := exists_sum_comp_eq (Fin.castAdd k₂) a fun j => c.principal (s j) 0
    refine ⟨u, a', ?_⟩
    rw [ha', ← hua]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [hsl]
  · -- (ii)
    intro w
    set cw : I → ℝ := coordMapL T e w with hcw
    have hlM : ∀ i, l i ∈ M := fun i => (hlD i).1
    set u : ↥(rangeS (scDeriv c.U (r c.R) 0)) :=
      ⟨∑ i, cw i • l i, M.sum_mem fun i _ => M.smul_mem _ (hlM i)⟩ with hu
    have hLu : linAt c.U c.R (c.principal g) 0 u = ∑ i, cw i • d i := by
      have : u = ∑ i, cw i • (⟨l i, hlM i⟩ : ↥(rangeS (scDeriv c.U (r c.R) 0))) := by
        apply Subtype.ext; simp [hu]
      rw [this, map_sum]
      simp only [map_smul]
      rfl
    have hcoord : coordMapL T e (∑ i, cw i • l i) = cw := by
      rw [map_sum]
      simp only [map_smul, hlv]
      ext i
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
        mul_one, mul_zero]
      rw [Finset.sum_eq_single i (fun b _ hb => if_neg (Ne.symm hb))
        (fun h => absurd (Finset.mem_univ i) h), if_pos rfl]
    obtain ⟨a', ha'⟩ := exists_sum_comp_eq (fun i => Fin.natAdd k₁ (eI i))
      (fun i => -(cw i * Mi i)) fun j => c.principal (s j) 0
    refine ⟨u, a', ?_, ?_⟩
    · rw [ha', hLu]
      simp only [hsr, hprin, smul_smul, neg_mul, neg_smul, Finset.sum_neg_distrib]
      rw [← sub_eq_add_neg, sub_eq_zero]
      exact Finset.sum_congr rfl fun i _ => by
        rw [mul_assoc, mul_inv_cancel₀ (hMpos i).ne', mul_one]
    · have hc0 : coordMapL T e ((w : c.φ.model.E 0) - (u : c.φ.model.E 0)) = 0 := by
        rw [map_sub]
        change cw - coordMapL T e (∑ i, cw i • l i) = 0
        rw [hcoord, sub_self]
      rw [← he0, mem_minimalSubspaceWith]
      intro i hi
      have := congrFun hc0 ⟨i, hi⟩
      rwa [coordMapL_apply] at this

end Construction

/-! ### Theorem 5.3.10 (preprint 5.18) -/

section Theorem518Full

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

open StrongRetr

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- A zero of `f + s` outside the support of `s` is a zero of `f`. -/
lemma isZeroAt_of_sectionAdd {f s : X → Y} (hf : IsSection P f) (hs : IsSection P s) {y : X}
    (hy : IsZeroAt P (sectionAdd P f s) y) (hsy : IsZeroAt P s y) : IsZeroAt P f y := by
  have h0 : (⟨s y, hs y⟩ : P ⁻¹' {y}) = 0 := Subtype.ext hsy
  have h1 := hy
  rw [IsZeroAt, sectionAdd_apply hf hs, h0, add_zero] at h1
  exact h1

set_option maxHeartbeats 6400000 in
-- the assembly of the proof: several large existentials are destructured
/-- **Theorem 5.3.10 (preprint 5.18) (perturbation and transversality: general position).**  Let `P : Y → X` be a
strong bundle over a **tame** M-polyfold `X` (the hidden hypothesis: Theorems 4.2.11 and 4.3.1 (preprint 4.22 and 4.23) are
used) which admits sc-smooth bump functions, `f` an sc-Fredholm section with tame germ data and
compact solution set, `N` an auxiliary norm.  Then there is an open `U ⊇ S_f` such that (1) for
every allowable `s ∈ Γ^{+,1}_U(P)` the solution set `S_{f+s}` is compact, and (2) for every
sc⁺-section `s₀` with `supp(s₀) ⊆ U` and `N(s₀(x)) ≤ 1 − ε` there are finitely many allowable
sc⁺-sections `t₁, …, t_m`, a `δ > 0` and a Lebesgue null set `CV ⊆ ℝᵐ` such that for every `λ`
with `|λ| < δ`, `λ ∉ CV`, the perturbation `s_λ = s₀ + Σ λᵢ tᵢ` is allowable and
(`SolutionSetInGeneralPosition`) `f + s_λ` is transversal to the zero section, `(f + s_λ, x)` is
in general position (Definition 5.3.9 (preprint 5.17)) at every `x ∈ S_{f+s_λ}`, and `S_{f+s_λ}` is compact, a
smooth finite-dimensional submanifold in general position (Definition 4.2.10 (preprint 4.21)) whose induced
structure is that of a manifold with boundary with corners, tame, with `d_{S_{f+s_λ}} = d_X`.
"Generic" is made precise as "for `λ` outside a null set", as in Theorem 5.3.5 (preprint 5.13)
(`theorem_5_3_5_generic`).

*Proof* (the text's): at every zero `x` of `g = f + s₀`, sections with (i)–(ii)
(`exists_sections_isParamGP`) make `F_x` general at `(0, x)`
(`isGeneralPositionGerm_paramSection_of_isParamGP`), hence at `(0, y)` for zeros `y` near `x`
(`exists_isOpen_isGeneralPositionGerm`); a finite subcover of `S_g`, and the united family `t`
keeps (i)–(ii) at every `(0, y)` (`isParamGP_of_isGeneralPositionGerm`, `IsParamGP.comp`); then
`theorem_5_3_10_of_family`. -/
theorem theorem_5_3_10_param (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions) {f : X → Y}
    (hf : B.IsScFredholmSectionTame f) (hS : IsCompact (solutionSet P f)) {N : B.One → ℝ}
    (hN : B.IsAuxNorm N) :
    ∃ U : Set X, IsOpen U ∧ solutionSet P f ⊆ U ∧
      (∀ s ∈ B.allowableSections N U, IsCompact (solutionSet P (sectionAdd P f s))) ∧
      ∀ (s₀ : X → Y) (hs₀ : B.IsScPlusSection s₀), sectionSupport P s₀ ⊆ U → ∀ ε > 0,
        (∀ x (hx : s₀ x ∈ B.oneSet), N (B.oneMk (s₀ x) hx) ≤ 1 - ε) →
        ∃ (m : ℕ) (t : Fin m → X → Y) (ht : ∀ i, B.IsScPlusSection (t i)),
          (∀ i, sectionSupport P (t i) ⊆ U) ∧
          (∀ i x (hx : t i x ∈ B.oneSet), N (B.oneMk (t i x) hx) ≤ 1) ∧
          ∃ δ > 0, ∃ CV : Set (Fin m → ℝ), volume CV = 0 ∧
            ∀ lam : Fin m → ℝ, ‖lam‖ < δ → lam ∉ CV →
              paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam ∈ B.allowableSections N U ∧
              B.SolutionSetInGeneralPosition
                (sectionAdd P f (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam)) := by
  classical
  obtain ⟨U, hUo, hSU, hcpt, hmain⟩ := theorem_5_3_10_of_family hX hf hS hN
  refine ⟨U, hUo, hSU, hcpt, fun s₀ hs₀ hs₀supp ε hε hs₀N => ?_⟩
  have hfs : IsSection P f := hf.isScSmooth.1
  have hgFt : B.IsScFredholmSectionTame (sectionAdd P f s₀) := theorem_3_1_18_tame hf hs₀
  have hgF : B.IsScFredholmSection (sectionAdd P f s₀) := hgFt.toIsScFredholmSection
  have hs₀alw : s₀ ∈ B.allowableSections N U :=
    ⟨hs₀, hs₀supp, fun x hx => (hs₀N x hx).trans (by linarith)⟩
  have hSg : IsCompact (solutionSet P (sectionAdd P f s₀)) := hcpt s₀ hs₀alw
  have hSgU : solutionSet P (sectionAdd P f s₀) ⊆ U := by
    intro y hy
    by_contra hyU
    have hs0y : IsZeroAt P s₀ y :=
      not_not.1 fun hne => hyU (hs₀supp (subset_closure hne))
    exact hyU (hSU (isZeroAt_of_sectionAdd hfs hs₀.1 hy hs0y))
  -- a tame chart centred at every zero of `g`, with a presentation
  have hch : ∀ y : solutionSet P (sectionAdd P f s₀), ∃ c : StrongBundleChart PX P,
      B.IsTameChart c ∧ (y : X) ∈ c.φ.source ∧ c.φ y = 0 := fun y => by
    obtain ⟨-, c, hc, hyc, hφ0, -⟩ := hgFt.germTame y (hgF.mem_smoothSet_of_isZeroAt y.2)
    exact ⟨c, hc, hyc, hφ0⟩
  choose c hc hyc hφ0 using hch
  have hpres : ∀ y : solutionSet P (sectionAdd P f s₀), ∃ (n : ℕ) (Wq : ScBanach)
      (T : ScIso (c y).φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq)),
      (c y).φ.model.C = T 0 ⁻¹' quadrant n Wq 0 := fun y => (c y).φ.model.isPartialQuadrant
  choose n Wq T hT using hpres
  -- the local families with (i)–(ii), and the neighbourhoods where `F_x` is general
  have hfam : ∀ x : solutionSet P (sectionAdd P f s₀), ∃ (k : ℕ) (s : Fin k → X → Y)
      (hsp : ∀ i, B.IsScPlusSection (s i)), (∀ i, sectionSupport P (s i) ⊆ U) ∧
      (∀ i y (hy : s i y ∈ B.oneSet), N (B.oneMk (s i y) hy) ≤ 1) ∧
      ∃ Ux : Set X, IsOpen Ux ∧ (x : X) ∈ Ux ∧ ∀ y ∈ Ux, IsZeroAt P (sectionAdd P f s₀) y →
        haveI := MPolyfold.paracompactSpace_prod (rnPolyfold k) PX
        haveI := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin k → ℝ) × X → X))
          ((rnPolyfold k).prod PX) B
        (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold k) PX)).IsGeneralPositionGerm
          (paramSection (sectionAdd P f s₀) hgF.isScSmooth.1 s fun i => (hsp i).1) (0, y) := by
    intro x
    obtain ⟨k, s, hsp, hsupp, hsN, hgpx⟩ := exists_sections_isParamGP hbump hN hgFt x.2 (hc x)
      (hyc x) (hφ0 x) (T x) (hT x) hUo (hSgU x.2)
    have := MPolyfold.paracompactSpace_prod (rnPolyfold k) PX
    have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin k → ℝ) × X → X))
      ((rnPolyfold k).prod PX) B
    have hFt := theorem_3_1_21_tame hgFt hsp
    have hz0 : ∀ y, IsZeroAt P (sectionAdd P f s₀) y → IsZeroAt (pullbackProj P Prod.snd)
        (paramSection (sectionAdd P f s₀) hgF.isScSmooth.1 s fun i => (hsp i).1) (0, y) :=
      fun y hy => by
        rw [isZeroAt_paramSection_iff]
        change IsZeroAt P (paramSlice (sectionAdd P f s₀) hgF.isScSmooth.1 s
          (fun i => (hsp i).1) 0) y
        rw [paramSlice_zero]; exact hy
    have h0 := isGeneralPositionGerm_paramSection_of_isParamGP hgFt hsp x.2 (hc x) (hyc x)
      (hφ0 x) (T x) (hT x) hgpx
    obtain ⟨W, hWo, h0W, -, hW⟩ :=
      exists_isOpen_isGeneralPositionGerm (prod_rn_isTame hX) hFt (hz0 x x.2) h0
    exact ⟨k, s, hsp, hsupp, hsN, Prod.mk 0 ⁻¹' W,
      hWo.preimage (continuous_const.prodMk continuous_id), h0W,
      fun y hy hy0 => (hW (0, y) hy (hz0 y hy0)).2.1⟩
  choose k s hsp hsupp hsN Ux hUxo hxUx hUx using hfam
  -- a finite subcover of the compact `S_g`, and the united family `t`
  obtain ⟨T₀, hT₀⟩ := hSg.elim_finite_subcover Ux hUxo
    (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hxUx ⟨x, hx⟩⟩)
  let e := Fintype.equivFin (Σ x : T₀, Fin (k x.1))
  set m := Fintype.card (Σ x : T₀, Fin (k x.1)) with hm
  set t : Fin m → X → Y := fun j => s (e.symm j).1.1 (e.symm j).2 with htdef
  have ht : ∀ j, B.IsScPlusSection (t j) := fun j => hsp _ _
  have htsupp : ∀ j, sectionSupport P (t j) ⊆ U := fun j => hsupp _ _
  have htN : ∀ j x (hx : t j x ∈ B.oneSet), N (B.oneMk (t j x) hx) ≤ 1 := fun j x hx =>
    hsN _ _ x hx
  have := MPolyfold.paracompactSpace_prod (rnPolyfold m) PX
  have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin m → ℝ) × X → X))
    ((rnPolyfold m).prod PX) B
  -- `F` is in general position at every `(0, y)`
  have hgpAll : ∀ y, IsZeroAt P (sectionAdd P f s₀) y →
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsGeneralPositionGerm
        (paramSection (sectionAdd P f s₀) (hfs.sectionAdd hs₀.1) t fun i => (ht i).1) (0, y) := by
    intro y hy
    obtain ⟨x, hxT, hyUx⟩ := mem_iUnion₂.1 (hT₀ hy)
    have := MPolyfold.paracompactSpace_prod (rnPolyfold (k x)) PX
    have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin (k x) → ℝ) × X → X))
      ((rnPolyfold (k x)).prod PX) B
    have hgx := hUx x y hyUx hy
    have hpx := isParamGP_of_isGeneralPositionGerm hgFt (hsp x) hy (hc ⟨y, hy⟩) (hyc ⟨y, hy⟩)
      (hφ0 ⟨y, hy⟩) (T ⟨y, hy⟩) (hT ⟨y, hy⟩) hgx
    have hpt := hpx.comp (fun i => e ⟨⟨x, hxT⟩, i⟩) (t := t) (fun i => by
      have := congrArg (fun σ : (Σ x : T₀, Fin (k x.1)) => s σ.1.1 σ.2)
        (e.symm_apply_apply ⟨⟨x, hxT⟩, i⟩)
      exact this.symm)
    exact isGeneralPositionGerm_paramSection_of_isParamGP hgFt ht hy (hc ⟨y, hy⟩)
      (hyc ⟨y, hy⟩) (hφ0 ⟨y, hy⟩) (T ⟨y, hy⟩) (hT ⟨y, hy⟩) hpt
  exact ⟨m, t, ht, htsupp, htN,
    hmain s₀ hs₀ hs₀supp ε hε hs₀N m t ht htsupp htN hgpAll⟩

end Theorem518Full

/-! ### Theorem 5.25 -/

section Theorem525

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

/-- The zero section has auxiliary norm `0`. -/
lemma StrongBundle.IsAuxNorm.fiberZero_eq {N : B.One → ℝ} (hN : B.IsAuxNorm N) (x : X)
    (hx : fiberZero P x ∈ B.oneSet) : N (B.oneMk (fiberZero P x) hx) = 0 := by
  have h1 : B.oneMk (fiberZero P x) hx = B.toOne (0 : B.oneFiber x) := rfl
  rw [h1, show (0 : B.oneFiber x) = (0 : ℝ) • (0 : B.oneFiber x) from (zero_smul ℝ _).symm,
    hN.smul, abs_zero, zero_mul]

/-- **Theorem 5.25 (perturbation into good position).**  Let `P : Y → X` be a strong bundle over
a tame M-polyfold `X` admitting sc-smooth bump functions, `f` a proper sc-Fredholm section with
tame germ data, and `N` an auxiliary norm.  Then there are an open `U ⊇ S_f` such that
`S_{f+s}` is compact for every `s ∈ Γ^{+,1}_U(P)`, and an `s ∈ Γ^{+,1}_U(P)` such that
`(f + s, x)` is in good position (Definition 3.6.6 (preprint 3.53), in a tame chart) at every `x ∈ S_{f+s}`; in
particular `S_{f+s}` is compact, and a smooth submanifold whose induced structure is that of a
manifold with boundary with corners (`SolutionSetInGeneralPosition`).  *Proof* (the text's):
Theorem 5.3.10 (preprint 5.18) with `s₀ = 0` gives, for a parameter `λ` outside a null set of a ball (which has
positive measure), the perturbation `s = Σ λᵢ tᵢ` with `f + s` in general position at every
zero, and Lemma 5.26 (`IsGeneralPositionGerm.isGoodPositionGermTame`) turns general into good
position.  The text's "in view of Theorem 3.54 ... in general position" is the openness of general
position (`exists_isOpen_isGeneralPositionGerm`), and "`x ∈ S_f`" there is `x ∈ S_{f+s₀}`. -/
theorem theorem_5_25_preprint (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions) {f : X → Y}
    (hf : B.IsScFredholmSectionTame f) (hP : B.IsProper f) {N : B.One → ℝ}
    (hN : B.IsAuxNorm N) :
    ∃ U : Set X, IsOpen U ∧ solutionSet P f ⊆ U ∧
      (∀ s ∈ B.allowableSections N U, IsCompact (solutionSet P (sectionAdd P f s))) ∧
      ∃ s ∈ B.allowableSections N U,
        (∀ x, IsZeroAt P (sectionAdd P f s) x → B.IsGoodPositionGermTame (sectionAdd P f s) x) ∧
        B.SolutionSetInGeneralPosition (sectionAdd P f s) := by
  classical
  obtain ⟨U, hUo, hSU, hcpt, hgen⟩ := theorem_5_3_10_param hX hbump hf hP.1 hN
  refine ⟨U, hUo, hSU, hcpt, ?_⟩
  have hs₀ : B.IsScPlusSection (fiberZero P) := StrongBundle.isScPlusSection_fiberZero
  have hs₀supp : sectionSupport P (fiberZero P) ⊆ U := by
    have : {x | fiberZero P x ≠ fiberZero P x} = (∅ : Set X) := by ext x; simp
    rw [sectionSupport, this, closure_empty]; exact empty_subset _
  have hs₀N : ∀ x (hx : fiberZero P x ∈ B.oneSet), N (B.oneMk (fiberZero P x) hx) ≤ 1 - 1 / 2 :=
    fun x hx => by rw [hN.fiberZero_eq x hx]; norm_num
  obtain ⟨m, t, ht, -, -, δ, hδ, CV, hCV, hlam⟩ :=
    hgen (fiberZero P) hs₀ hs₀supp (1 / 2) (by norm_num) hs₀N
  obtain ⟨lam, hlamδ, hlamCV⟩ : ∃ lam ∈ Metric.ball (0 : Fin m → ℝ) δ, lam ∉ CV := by
    by_contra h
    have h1 : Metric.ball (0 : Fin m → ℝ) δ ⊆ CV := fun lam hl => by
      by_contra hc
      exact h ⟨lam, hl, hc⟩
    exact (Metric.measure_ball_pos volume (0 : Fin m → ℝ) hδ).ne' (measure_mono_null h1 hCV)
  obtain ⟨halw, hgp⟩ := hlam lam (mem_ball_zero_iff.1 hlamδ) hlamCV
  have hsl : B.IsScPlusSection (paramSlice (fiberZero P) hs₀.1 t (fun i => (ht i).1) lam) :=
    isScPlusSection_paramSlice hs₀ ht lam
  refine ⟨_, halw, fun x hx => ?_, hgp⟩
  exact (hgp.2.1 x hx).isGoodPositionGermTame (theorem_3_1_18_tame hf hsl) hx

end Theorem525

/-! ### Theorem 5.3.10 (preprint 5.18) in the text's dense form -/

section Theorem518Dense

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

set_option maxHeartbeats 1600000 in
-- the fibre arithmetic in `(Y_{0,1})_x` with the destructured generic form (as for Theorem 5.3.5 (preprint 5.13))
/-- **Theorem 5.3.10 (preprint 5.18) (perturbation and transversality: general position)**, the text's dense-set
form.  Let `P : Y → X` be a strong bundle over a **tame** M-polyfold `X` admitting sc-smooth bump
functions, `f` an sc-Fredholm section with tame germ data and compact solution set, `N` an
auxiliary norm.  Then there is an open `U ⊇ S_f` such that `S_{f+s}` is compact for every
`s ∈ Γ^{+,1}_U(P)`, and the allowable `s` for which `(f + s, x)` is in general position at every
`x ∈ S_{f+s}` (with the further conclusions of `SolutionSetInGeneralPosition`: `S_{f+s}` a compact
smooth submanifold, a manifold with boundary with corners with `d_{S_{f+s}} = d_X`) are dense in
`Γ^{+,1}_U(P)` for the distance `ρ(s, s') = sup_x N(s(x) − s'(x))`, read pointwise
(`sectionDistAt`).  *Proof*: that of `theorem_5_3_5_preprint` with `theorem_5_3_10_param` in place of the generic
form of Theorem 5.3.5 (preprint 5.13): `s₀ = (1 − ε'/2)s'` and a parameter `λ` outside the null set in a small
ball. -/
theorem theorem_5_3_10_dense (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions) {f : X → Y}
    (hf : B.IsScFredholmSectionTame f) (hS : IsCompact (solutionSet P f)) {N : B.One → ℝ}
    (hN : B.IsAuxNorm N) :
    ∃ U : Set X, IsOpen U ∧ solutionSet P f ⊆ U ∧
      (∀ s ∈ B.allowableSections N U, IsCompact (solutionSet P (sectionAdd P f s))) ∧
      ∀ (s' : X → Y) (hs' : B.IsScPlusSection s'), s' ∈ B.allowableSections N U → ∀ ε > 0,
        ∃ (s : X → Y) (hs : B.IsScPlusSection s), s ∈ B.allowableSections N U ∧
          (∀ x, B.sectionDistAt N hs hs' x ≤ ε) ∧
          B.SolutionSetInGeneralPosition (sectionAdd P f s) := by
  classical
  obtain ⟨U, hUo, hSU, hcpt, hgen⟩ := theorem_5_3_10_param hX hbump hf hS hN
  refine ⟨U, hUo, hSU, hcpt, fun s' hs' hs'alw ε hε => ?_⟩
  obtain ⟨-, hs'supp, hs'N⟩ := hs'alw
  -- `ε' = min ε 1`, `θ = 1 − ε'/2`, `s₀ = θ s'`
  set ε' : ℝ := min ε 1 with hε'
  have hε'pos : 0 < ε' := lt_min hε one_pos
  have hε'le : ε' ≤ ε := min_le_left _ _
  have hε'le1 : ε' ≤ 1 := min_le_right _ _
  set θ : ℝ := 1 - ε' / 2 with hθ
  have hθpos : 0 < θ := by rw [hθ]; linarith
  set s₀ : X → Y := sectionSmul P (fun _ => θ) s' with hs₀def
  have hs₀ : B.IsScPlusSection s₀ := hs'.smul_left (isScSmoothMap_real_const _)
  have hs₀supp : sectionSupport P s₀ ⊆ U :=
    (sectionSupport_sectionSmul_const_subset hs'.1 θ).trans hs'supp
  have hs₀N : ∀ x (hx : s₀ x ∈ B.oneSet), N (B.oneMk (s₀ x) hx) ≤ 1 - ε' / 2 := fun x hx => by
    rw [hN.oneMk_sectionSmul_const hs' θ x hx, abs_of_pos hθpos]
    calc θ * N (B.oneMk (s' x) (hs'.mem_oneSet x)) ≤ θ * 1 :=
          mul_le_mul_of_nonneg_left (hs'N x _) hθpos.le
      _ = 1 - ε' / 2 := by rw [mul_one]
  obtain ⟨m, t, ht, htsupp, htN, δ, hδ, CV, hCV, hlam⟩ :=
    hgen s₀ hs₀ hs₀supp (ε' / 2) (by positivity) hs₀N
  -- a parameter `λ ∉ CV` with `|λ| < δ` and `m|λ| ≤ ε'/2`
  set r : ℝ := min δ (ε' / (2 * (m + 1))) with hr
  have hrpos : 0 < r := lt_min hδ (by positivity)
  obtain ⟨lam, hlamr, hlamCV⟩ : ∃ lam ∈ Metric.ball (0 : Fin m → ℝ) r, lam ∉ CV := by
    by_contra h
    have h1 : Metric.ball (0 : Fin m → ℝ) r ⊆ CV := fun lam hl => by
      by_contra hc
      exact h ⟨lam, hl, hc⟩
    have h2 := measure_mono_null h1 hCV
    exact (Metric.measure_ball_pos volume (0 : Fin m → ℝ) hrpos).ne' h2
  have hlamδ : ‖lam‖ < δ := lt_of_lt_of_le (mem_ball_zero_iff.1 hlamr) (min_le_left _ _)
  have hlamε : (m : ℝ) * ‖lam‖ ≤ ε' / 2 := by
    have h1 : ‖lam‖ ≤ ε' / (2 * (m + 1)) :=
      (mem_ball_zero_iff.1 hlamr).le.trans (min_le_right _ _)
    calc (m : ℝ) * ‖lam‖ ≤ m * (ε' / (2 * (m + 1))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (ε' / 2) * (m / (m + 1)) := by field_simp
      _ ≤ (ε' / 2) * 1 := mul_le_mul_of_nonneg_left
          ((div_le_one (by positivity)).2 (by linarith)) (by positivity)
      _ = ε' / 2 := mul_one _
  obtain ⟨halw, hgp⟩ := hlam lam hlamδ hlamCV
  have hsl : B.IsScPlusSection (paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam) :=
    isScPlusSection_paramSlice hs₀ ht lam
  refine ⟨_, hsl, halw, fun x => ?_, hgp⟩
  -- the distance: `s(x) − s'(x) = (θ − 1) s'(x) + Σ λᵢ tᵢ(x)` in the fibre
  set u' : B.oneFiber x := ⟨⟨s' x, hs'.1 x⟩, hs'.mem_oneSet x⟩ with hu'
  set w : Fin m → B.oneFiber x := fun i => ⟨⟨t i x, (ht i).1 x⟩, (ht i).mem_oneSet x⟩ with hw
  have hu : (⟨⟨paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam x, hsl.1 x⟩, hsl.mem_oneSet x⟩ :
      B.oneFiber x) = θ • u' + ∑ i, lam i • w i := by
    apply Subtype.ext
    rw [Submodule.coe_add, Submodule.coe_sum]
    simp only [Submodule.coe_smul]
    apply Subtype.ext
    change paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam x = _
    unfold paramSlice
    have h1 : (⟨s₀ x, hs₀.1 x⟩ : P ⁻¹' {x}) = θ • ⟨s' x, hs'.1 x⟩ :=
      Subtype.ext (sectionSmul_apply (f := fun _ => θ) hs'.1 x)
    rw [h1]
    rfl
  have hdiff : (⟨⟨paramSlice s₀ hs₀.1 t (fun i => (ht i).1) lam x, hsl.1 x⟩, hsl.mem_oneSet x⟩ :
      B.oneFiber x) - u' = (θ - 1) • u' + ∑ i, lam i • w i := by
    rw [hu, add_sub_right_comm, hθ]
    simp only [sub_smul, one_smul]
  have hli : ∀ i, |lam i| ≤ ‖lam‖ := fun i => by
    have := norm_le_pi_norm lam i
    rwa [Real.norm_eq_abs] at this
  have hwN : ∀ i, N (B.toOne (w i)) ≤ 1 := fun i => htN i x ((ht i).mem_oneSet x)
  have hu'N : N (B.toOne u') ≤ 1 := hs'N x _
  change N (B.toOne (_ - u')) ≤ ε
  rw [hdiff]
  calc N (B.toOne ((θ - 1) • u' + ∑ i, lam i • w i))
      ≤ N (B.toOne ((θ - 1) • u')) + N (B.toOne (∑ i, lam i • w i)) := (hN.fiber x).add_le _ _
    _ = |θ - 1| * N (B.toOne u') + N (B.toOne (∑ i, lam i • w i)) := by rw [hN.smul]
    _ ≤ (ε' / 2) * 1 + ∑ i, N (B.toOne (lam i • w i)) := by
        refine add_le_add ?_ (hN.toOne_sum_le _ _)
        have hθ1 : |θ - 1| = ε' / 2 := by
          rw [hθ, show (1 - ε' / 2 - 1 : ℝ) = -(ε' / 2) by ring, abs_neg,
            abs_of_pos (by positivity)]
        rw [hθ1]
        exact mul_le_mul_of_nonneg_left hu'N (by positivity)
    _ = ε' / 2 + ∑ i, |lam i| * N (B.toOne (w i)) := by
        rw [mul_one]
        congr 1
        exact Finset.sum_congr rfl fun i _ => hN.smul (w i) (lam i)
    _ ≤ ε' / 2 + ∑ _i : Fin m, ‖lam‖ * 1 :=
        add_le_add le_rfl (Finset.sum_le_sum fun i _ =>
          mul_le_mul (hli i) (hwN i) (hN.nonneg _) (norm_nonneg _))
    _ = ε' / 2 + (m : ℝ) * ‖lam‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    _ ≤ ε := by linarith

end Theorem518Dense

/-! ### Theorem 5.3.12 (preprint 5.19) -/

section Theorem519

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

open StrongRetr

-- `StrongBundle.IsGoodPositionGermTame.congr_nhds` (good position is a property of the germ) now
-- lives in `Chapter3/Chapter5BridgeG.lean`, in the germ reading of Definition 3.1.11 (preprint 3.11).

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- `f + 0 = f`. -/
lemma sectionAdd_fiberZero {f : X → Y} (hf : IsSection P f) :
    sectionAdd P f (fiberZero P) = f := by
  funext x
  rw [sectionAdd_apply hf isSection_fiberZero]
  have : (⟨fiberZero P x, isSection_fiberZero x⟩ : P ⁻¹' {x}) = 0 := rfl
  rw [this, add_zero]

set_option maxHeartbeats 6400000 in
-- the assembly of the proof: several large existentials are destructured
/-- **Theorem 5.3.12 (preprint 5.19) (perturbation and transversality: good position), generic form.**  Let
`P : Y → X` be a strong bundle over an M-polyfold `X` admitting sc-smooth bump functions, `f` an
sc-Fredholm section with tame germ data and compact solution set, `N` an auxiliary norm, and let
`(f, x)` be in good position (in a tame chart) at every zero `x ∈ ∂X`.  Then there is an open
`U ⊇ S_f` such that `S_{f+s}` is compact for every `s ∈ Γ^{+,1}_U(P)`, and finitely many allowable
sc⁺-sections `t₁, …, t_m` **with supports disjoint from `∂X`**, a `δ > 0` and a Lebesgue null set
`CV` such that for every `λ` with `|λ| < δ`, `λ ∉ CV`, the (arbitrarily small, as `λ → 0`) section
`s_λ = Σ λᵢ tᵢ` is allowable, vanishes on the neighbourhood `X ∖ supp(s_λ)` of `∂X`, `f + s_λ` is
transversal to the zero section, `(f + s_λ, x)` is in good position at every zero, `S_{f+s_λ}` is
compact, and, if non-empty, a sub-M-polyfold whose induced structure is tame and that of a
manifold with boundary with corners (Theorem 3.6.11 (preprint 3.57)).

*Proof* (the text's, with the omitted steps): the zeros of `f` near `S_f ∩ ∂X` are in good position
(Theorem 3.6.8 (preprint 3.54) (1), `theorem_3_6_8'`), on an open `Vbd`; sections spanning the cokernels at the zeros
outside `Vbd` are taken with supports in `U ∖ (∂X ∪ cl V₁)` (`S_f ∩ ∂X ⊆ V₁`, `cl V₁ ⊆ Vbd`); the
parametrized section `F` is onto at every `(0, y)`, `y ∈ S_f`, hence in good position at the
points with `y ∉ V₁` (`d = 0` there); the Sard step of Theorem 5.3.5 (preprint 5.13) gives the transversality of
`f + s_λ` at its zeros outside `V₁`, which are interior points, so in good position; on `V₁` the
sections vanish, `f + s_λ = f`, and the good position there is that of `f`
(`IsGoodPositionGermTame.congr_nhds`).  The text's "as before" for `F` hides that `F` is in general
**not** in good position at the boundary zeros `(0, x)`, `x ∈ ∂X` (Findings); the proof avoids the
implicit function theorem for `F` there. -/
theorem theorem_5_3_12_param (hbump : PX.AdmitsBumpFunctions) {f : X → Y}
    (hf : B.IsScFredholmSectionTame f) (hS : IsCompact (solutionSet P f)) {N : B.One → ℝ}
    (hN : B.IsAuxNorm N)
    (hbd : ∀ x ∈ PX.boundary, IsZeroAt P f x → B.IsGoodPositionGermTame f x) :
    ∃ U : Set X, IsOpen U ∧ solutionSet P f ⊆ U ∧
      (∀ s ∈ B.allowableSections N U, IsCompact (solutionSet P (sectionAdd P f s))) ∧
      ∃ (m : ℕ) (t : Fin m → X → Y) (ht : ∀ i, B.IsScPlusSection (t i)),
        (∀ i, sectionSupport P (t i) ⊆ U) ∧ (∀ i, Disjoint (sectionSupport P (t i)) PX.boundary) ∧
        (∀ i x (hx : t i x ∈ B.oneSet), N (B.oneMk (t i x) hx) ≤ 1) ∧
        ∃ δ > 0, ∃ CV : Set (Fin m → ℝ), volume CV = 0 ∧
          ∀ lam : Fin m → ℝ, ‖lam‖ < δ → lam ∉ CV →
            paramSlice (fiberZero P) isSection_fiberZero t (fun i => (ht i).1) lam ∈
              B.allowableSections N U ∧
            Disjoint (sectionSupport P
              (paramSlice (fiberZero P) isSection_fiberZero t (fun i => (ht i).1) lam))
              PX.boundary ∧
            B.IsTransversal (sectionAdd P f
              (paramSlice (fiberZero P) isSection_fiberZero t (fun i => (ht i).1) lam)) ∧
            (∀ x, IsZeroAt P (sectionAdd P f
                (paramSlice (fiberZero P) isSection_fiberZero t (fun i => (ht i).1) lam)) x →
              B.IsGoodPositionGermTame (sectionAdd P f
                (paramSlice (fiberZero P) isSection_fiberZero t (fun i => (ht i).1) lam)) x) ∧
            IsCompact (solutionSet P (sectionAdd P f
              (paramSlice (fiberZero P) isSection_fiberZero t (fun i => (ht i).1) lam))) ∧
            ((solutionSet P (sectionAdd P f
                (paramSlice (fiberZero P) isSection_fiberZero t (fun i => (ht i).1) lam))).Nonempty
              →
              ∃ hsub : PX.IsSubMPolyfold (solutionSet P (sectionAdd P f
                  (paramSlice (fiberZero P) isSection_fiberZero t (fun i => (ht i).1) lam))),
                haveI := PX.paracompactSpace_subtype (solutionSet P (sectionAdd P f
                  (paramSlice (fiberZero P) isSection_fiberZero t (fun i => (ht i).1) lam)))
                (MPolyfold.subPolyfold hsub).IsTame ∧
                  (MPolyfold.subPolyfold hsub).IsManifoldWithCornersLoc) := by
  classical
  have hfs : IsSection P f := hf.isScSmooth.1
  have hfF := hf.toIsScFredholmSection
  have := PX.metrizableSpace
  obtain ⟨-, hprop⟩ := theorem_5_2_2_preprint hfF hS
  obtain ⟨U, hUo, hSU, hK⟩ := hprop N hN
  have hcpt : ∀ s ∈ B.allowableSections N U, IsCompact (solutionSet P (sectionAdd P f s)) := by
    rintro s ⟨hs, hssupp, hsN⟩
    have hsU : ∀ x ∉ U, IsZeroAt P s x := fun x hx =>
      not_not.1 fun hne => hx (hssupp (subset_closure hne))
    have hsN' : ∀ x, B.AuxLe N (s x) 1 := fun x => ⟨hs.mem_oneSet x, hsN x _⟩
    obtain ⟨-, hcl⟩ := remark_5_3_4 hN hfs hSU hK hs.1 hsU hsN'
    exact hcl.of_isClosed_subset
      (isClosed_solutionSet (theorem_3_1_18_preprint hfF hs).isScSmooth) subset_closure
  refine ⟨U, hUo, hSU, hcpt, ?_⟩
  -- `g = f + 0`
  have hs₀ : B.IsScPlusSection (fiberZero P) := StrongBundle.isScPlusSection_fiberZero
  have hg_eq : sectionAdd P f (fiberZero P) = f := sectionAdd_fiberZero hfs
  have hgFt : B.IsScFredholmSectionTame (sectionAdd P f (fiberZero P)) := by rw [hg_eq]; exact hf
  have hgF : B.IsScFredholmSection (sectionAdd P f (fiberZero P)) := hgFt.toIsScFredholmSection
  have hzg : ∀ y, IsZeroAt P (sectionAdd P f (fiberZero P)) y ↔ IsZeroAt P f y := fun y => by
    rw [hg_eq]
  -- `Vbd`: the zeros of `f` near the boundary zeros are in good position
  have hlocB : ∀ x : (solutionSet P f ∩ PX.boundary : Set X), ∃ V : Set X, IsOpen V ∧
      (x : X) ∈ V ∧ ∀ y ∈ V, IsZeroAt P f y → B.IsGoodPositionGermTame f y := fun x =>
    theorem_3_6_8_one' hf (hbd x x.2.2 x.2.1) x.2.1
  choose Vb hVbo hxVb hVb using hlocB
  set Vbd := ⋃ x, Vb x with hVbd
  have hVbdo : IsOpen Vbd := isOpen_iUnion hVbo
  have hVbdgood : ∀ y ∈ Vbd, IsZeroAt P f y → B.IsGoodPositionGermTame f y := fun y hy hy0 => by
    obtain ⟨x, hx⟩ := mem_iUnion.1 hy; exact hVb x y hx hy0
  have hSb : solutionSet P f ∩ PX.boundary ⊆ Vbd := fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hxVb _⟩
  have hbcl : IsClosed PX.boundary := PX.isClosed_boundary
  have hSbcl : IsClosed (solutionSet P f ∩ PX.boundary) := hS.isClosed.inter hbcl
  obtain ⟨V₁, hV₁o, hSbV₁, hclV₁⟩ := normal_exists_closure_subset hSbcl hVbdo hSb
  -- the zeros outside `Vbd` are interior points
  set K₁ := solutionSet P f \ Vbd with hK₁
  have hK₁c : IsCompact K₁ := hS.diff hVbdo
  set G := U ∩ (PX.boundary)ᶜ ∩ (closure V₁)ᶜ with hGdef
  have hGo : IsOpen G := (hUo.inter hbcl.isOpen_compl).inter isClosed_closure.isOpen_compl
  have hK₁G : K₁ ⊆ G := by
    rintro x ⟨hxS, hxV⟩
    refine ⟨⟨hSU hxS, fun hxb => hxV (hSb ⟨hxS, hxb⟩)⟩, fun hxc => hxV (hclV₁ hxc)⟩
  -- spanning sections at the points of `K₁`, supported in `G`
  have hspan : ∀ x : K₁,
      ∃ (k : ℕ) (s : Fin k → X → Y) (hsp : ∀ i, B.IsScPlusSection (s i)),
        (∀ i, sectionSupport P (s i) ⊆ G) ∧
        (∀ i x (hx : s i x ∈ B.oneSet), N (B.oneMk (s i x) hx) ≤ 1) ∧
        ∃ Ux : Set X, IsOpen Ux ∧ (x : X) ∈ Ux ∧ ∀ y ∈ Ux, IsZeroAt P f y →
          haveI := MPolyfold.paracompactSpace_prod (rnPolyfold k) PX
          haveI := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin k → ℝ) × X → X))
            ((rnPolyfold k).prod PX) B
          (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold k) PX)).IsLinSurjAt
            (paramSection (sectionAdd P f (fiberZero P)) hgF.isScSmooth.1 s
              fun i => (hsp i).1) (0, y) := by
    intro x
    obtain ⟨x, hx⟩ := x
    have hx0 : IsZeroAt P (sectionAdd P f (fiberZero P)) x := (hzg x).2 hx.1
    obtain ⟨k, s, hsp, hsupp, hsN, c, hc, hxV, hφ0, hsp_span⟩ :=
      exists_spanning_sections hbump hN hgF hx0 hGo (hK₁G hx)
    have := MPolyfold.paracompactSpace_prod (rnPolyfold k) PX
    have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin k → ℝ) × X → X))
      ((rnPolyfold k).prod PX) B
    have hsurj := isLinSurjAt_paramSection_zero_of_spanning hgF hsp hc hxV hφ0
      (paramSection (sectionAdd P f (fiberZero P)) hgF.isScSmooth.1 s (fun i => (hsp i).1) (0, x))
      hsp_span
    have hF := theorem_3_1_21_tame hgFt hsp
    have hz0 : ∀ y, IsZeroAt P (sectionAdd P f (fiberZero P)) y → IsZeroAt (pullbackProj P Prod.snd)
        (paramSection (sectionAdd P f (fiberZero P)) hgF.isScSmooth.1 s fun i => (hsp i).1)
          (0, y) := fun y hy => by
      rw [isZeroAt_paramSection_iff]
      change IsZeroAt P (paramSlice (sectionAdd P f (fiberZero P)) hgF.isScSmooth.1 s
        (fun i => (hsp i).1) 0) y
      rw [paramSlice_zero]; exact hy
    have hxb : x ∉ PX.boundary := fun hxb => hx.2 (hSb ⟨hx.1, hxb⟩)
    have hd0 : ((rnPolyfold k).prod PX).degIndex ((0 : Fin k → ℝ), x) = 0 := by
      have h1 := MPolyfold.degIndex_prod_le (rnPolyfold k) PX 0 x
      have h2 : PX.degIndex x = 0 := by
        by_contra h; exact hxb (Nat.one_le_iff_ne_zero.2 h)
      rw [rnPolyfold_degIndex, h2] at h1
      exact Nat.le_zero.1 h1
    have hgp := StrongBundle.isGoodPositionGerm_of_isLinSurjAt hF (hz0 x hx0) hd0 hsurj
    obtain ⟨V, hVo, hxV', hall⟩ := theorem_3_6_8_one' hF hgp (hz0 x hx0)
    refine ⟨k, s, hsp, hsupp, hsN, Prod.mk 0 ⁻¹' V,
      hVo.preimage (continuous_const.prodMk continuous_id), hxV', fun y hy hy0 => ?_⟩
    exact (hall (0, y) hy (hz0 y ((hzg y).2 hy0))).isGoodPositionGerm.isLinSurjAt hF.isScSmooth
  choose k s hsp hsupp hsN Ux hUxo hxUx hUx using hspan
  obtain ⟨T, hT⟩ := hK₁c.elim_finite_subcover Ux hUxo
    (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hxUx ⟨x, hx⟩⟩)
  let e := Fintype.equivFin (Σ x : T, Fin (k x.1))
  set m := Fintype.card (Σ x : T, Fin (k x.1)) with hm
  set t : Fin m → X → Y := fun j => s (e.symm j).1.1 (e.symm j).2 with htdef
  have ht : ∀ j, B.IsScPlusSection (t j) := fun j => hsp _ _
  have htG : ∀ j, sectionSupport P (t j) ⊆ G := fun j => hsupp _ _
  have htsupp : ∀ j, sectionSupport P (t j) ⊆ U := fun j x hx => (htG j hx).1.1
  have htbd : ∀ j, Disjoint (sectionSupport P (t j)) PX.boundary := fun j =>
    Set.disjoint_left.2 fun x hx hxb => (htG j hx).1.2 hxb
  have htV₁ : ∀ j, ∀ y ∈ V₁, IsZeroAt P (t j) y := fun j y hy =>
    not_not.1 fun hne => (htG j (subset_closure hne)).2 (subset_closure hy)
  have htN : ∀ j x (hx : t j x ∈ B.oneSet), N (B.oneMk (t j x) hx) ≤ 1 := fun j x hx =>
    hsN _ _ x hx
  have := MPolyfold.paracompactSpace_prod (rnPolyfold m) PX
  have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin m → ℝ) × X → X))
    ((rnPolyfold m).prod PX) B
  have hFt := theorem_3_1_21_tame hgFt ht
  have hz0 : ∀ y, IsZeroAt P (sectionAdd P f (fiberZero P)) y → IsZeroAt (pullbackProj P Prod.snd)
      (paramSection (sectionAdd P f (fiberZero P)) hgF.isScSmooth.1 t fun i => (ht i).1)
        (0, y) := fun y hy => by
    rw [isZeroAt_paramSection_iff]
    change IsZeroAt P (paramSlice (sectionAdd P f (fiberZero P)) hgF.isScSmooth.1 t
      (fun i => (ht i).1) 0) y
    rw [paramSlice_zero]; exact hy
  -- `F` is onto at every `(0, y)`, `y ∈ S_f`
  have hsurjAll : ∀ y, IsZeroAt P f y →
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsLinSurjAt
        (paramSection (sectionAdd P f (fiberZero P)) hgF.isScSmooth.1 t fun i => (ht i).1)
          (0, y) := by
    intro y hy
    by_cases hyV : y ∈ Vbd
    · -- `g'(y)` is onto already; add the sections with zero coefficients
      have hgy : B.IsGoodPositionGermTame (sectionAdd P f (fiberZero P)) y := by
        rw [hg_eq]; exact hVbdgood y hyV hy
      have hlin := hgy.isGoodPositionGerm.isLinSurjAt hgF.isScSmooth
      have hy0 := (hzg y).2 hy
      obtain ⟨-, c, hc, hyc, hφ0, -⟩ := hgFt.germTame y (hgF.mem_smoothSet_of_isZeroAt hy0)
      have hz : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) = c.φ y := by rw [map_zero, hφ0]
      have hs' := hlin.linAt_surjective hgF.isScSmooth hy0 hc.1 hyc hz
      refine isLinSurjAt_paramSection_zero_of_spanning hgF ht hc.1 hyc hφ0
        (paramSection (sectionAdd P f (fiberZero P)) hgF.isScSmooth.1 t (fun i => (ht i).1)
          (0, y)) fun k' hk' => ?_
      rw [hφ0] at hs'
      obtain ⟨u, hu⟩ := hs' k' hk'
      exact ⟨u, 0, by simp [hu]⟩
    · obtain ⟨x, hxT, hyUx⟩ := mem_iUnion₂.1 (hT ⟨hy, hyV⟩)
      have := MPolyfold.paracompactSpace_prod (rnPolyfold (k x)) PX
      have := paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin (k x) → ℝ) × X → X))
        ((rnPolyfold (k x)).prod PX) B
      refine isLinSurjAt_paramSection_zero_of_comp hgF ht (fun i => e ⟨⟨x, hxT⟩, i⟩) (hsp x)
        (fun i => ?_) ((hzg y).2 hy) (hUx x y hyUx hy)
      have := congrArg (fun σ : (Σ x : T, Fin (k x.1)) => s σ.1.1 σ.2)
        (e.symm_apply_apply ⟨⟨x, hxT⟩, i⟩)
      exact this.symm
  -- the open set `W ⊇ {0} × (S_f ∖ V₁)` of zeros of `F` in good position, off `ℝᵐ × ∂X`
  have hlocW : ∀ y : (solutionSet P f \ V₁ : Set X), ∃ W : Set ((Fin m → ℝ) × X), IsOpen W ∧
      ((0 : Fin m → ℝ), (y : X)) ∈ W ∧ W ⊆ {z | z.2 ∉ PX.boundary} ∧
      ∀ z ∈ W, IsZeroAt (pullbackProj P Prod.snd)
        (paramSection (sectionAdd P f (fiberZero P)) hgF.isScSmooth.1 t fun i => (ht i).1) z →
        (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsGoodPositionGermTame
          (paramSection (sectionAdd P f (fiberZero P)) hgF.isScSmooth.1 t fun i => (ht i).1) z := by
    intro y
    obtain ⟨y, hyS, hyV₁⟩ := y
    have hyb : y ∉ PX.boundary := fun hyb => hyV₁ (hSbV₁ ⟨hyS, hyb⟩)
    have hd0 : ((rnPolyfold m).prod PX).degIndex ((0 : Fin m → ℝ), y) = 0 := by
      have h1 := MPolyfold.degIndex_prod_le (rnPolyfold m) PX 0 y
      have h2 : PX.degIndex y = 0 := by
        by_contra h; exact hyb (Nat.one_le_iff_ne_zero.2 h)
      rw [rnPolyfold_degIndex, h2] at h1
      exact Nat.le_zero.1 h1
    have hgp := StrongBundle.isGoodPositionGerm_of_isLinSurjAt hFt (hz0 y ((hzg y).2 hyS)) hd0
      (hsurjAll y hyS)
    obtain ⟨V, hVo, hyV, hall⟩ := theorem_3_6_8_one' hFt hgp (hz0 y ((hzg y).2 hyS))
    refine ⟨V ∩ {z | z.2 ∉ PX.boundary}, hVo.inter (hbcl.isOpen_compl.preimage continuous_snd),
      ⟨hyV, hyb⟩, inter_subset_right, fun z hz hz0' => hall z hz.1 hz0'⟩
  choose Wy hWyo hyWy hWyb hWy using hlocW
  set W := ⋃ y, Wy y with hWdef
  have hWo : IsOpen W := isOpen_iUnion hWyo
  have hWgood : ∀ z ∈ W, IsZeroAt (pullbackProj P Prod.snd)
      (paramSection (sectionAdd P f (fiberZero P)) hgF.isScSmooth.1 t fun i => (ht i).1) z →
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold m) PX)).IsGoodPositionGermTame
        (paramSection (sectionAdd P f (fiberZero P)) hgF.isScSmooth.1 t fun i => (ht i).1) z :=
    fun z hz hz0' => by obtain ⟨y, hzy⟩ := mem_iUnion.1 hz; exact hWy y z hzy hz0'
  have hWb : ∀ z ∈ W, z.2 ∉ PX.boundary := fun z hz => by
    obtain ⟨y, hzy⟩ := mem_iUnion.1 hz; exact hWyb y hzy
  -- the perturbations are allowable for `|λ| ≤ δ₁ = 1/(2(m + 1))`
  have hs₀N : ∀ x (hx : fiberZero P x ∈ B.oneSet), N (B.oneMk (fiberZero P x) hx) ≤ 1 - 1 / 2 :=
    fun x hx => by rw [hN.fiberZero_eq x hx]; norm_num
  set δ₁ : ℝ := (1 / 2) / (m + 1) with hδ₁
  have hδ₁pos : 0 < δ₁ := div_pos (by norm_num) (by positivity)
  have hallow : ∀ lam : Fin m → ℝ, ‖lam‖ ≤ δ₁ →
      ∀ x, B.AuxLe N (paramSlice (fiberZero P) hs₀.1 t (fun i => (ht i).1) lam x) 1 :=
    fun lam hlam x =>
    auxLe_paramSlice hN hs₀ ht hs₀N htN (by
      calc (m : ℝ) * ‖lam‖ ≤ m * δ₁ := mul_le_mul_of_nonneg_left hlam (by positivity)
        _ = (1 / 2) * (m / (m + 1)) := by rw [hδ₁]; ring
        _ ≤ (1 / 2) * 1 := mul_le_mul_of_nonneg_left
            ((div_le_one (by positivity)).2 (by linarith)) (by norm_num)
        _ = 1 / 2 := mul_one _) x
  have hsupp0 : sectionSupport P (fiberZero P) = ∅ := by
    have : {x | fiberZero P x ≠ fiberZero P x} = (∅ : Set X) := by ext x; simp
    rw [sectionSupport, this, closure_empty]
  have hsuppl : ∀ lam : Fin m → ℝ, ∀ x ∉ U,
      IsZeroAt P (paramSlice (fiberZero P) hs₀.1 t (fun i => (ht i).1) lam) x := fun lam x hx =>
    isZeroAt_paramSlice_of_not_mem_support hs₀.1 _ lam (by rw [hsupp0]; exact fun h => h)
      fun i h => hx (htsupp i h)
  have hslice : ∀ lam : Fin m → ℝ,
      sectionAdd P f (paramSlice (fiberZero P) hs₀.1 t (fun i => (ht i).1) lam) =
      paramSlice (sectionAdd P f (fiberZero P)) hgF.isScSmooth.1 t (fun i => (ht i).1) lam :=
    fun lam => sectionAdd_paramSlice hfs hs₀.1 _ lam
  -- the zeros of `F` over `|λ| ≤ δ₁` off `V₁` form a compact set `Z₁`
  set Z : Set ((Fin m → ℝ) × X) := {z | ‖z.1‖ ≤ δ₁ ∧ IsZeroAt (pullbackProj P Prod.snd)
    (paramSection (sectionAdd P f (fiberZero P)) hgF.isScSmooth.1 t fun i => (ht i).1) z}
    with hZdef
  have hZsub : Z ⊆ Metric.closedBall (0 : Fin m → ℝ) δ₁ ×ˢ closure {x ∈ U | B.AuxLe N (f x) 1} := by
    rintro ⟨lam, x⟩ ⟨hlam, hz⟩
    refine ⟨mem_closedBall_zero_iff.2 hlam, ?_⟩
    have hx' : IsZeroAt P (paramSlice (sectionAdd P f (fiberZero P)) hgF.isScSmooth.1 t
        (fun i => (ht i).1) lam) x := (isZeroAt_paramSection_iff (lam, x)).1 hz
    rw [← hslice lam] at hx'
    exact subset_closure ((remark_5_3_4 hN hfs hSU hK (isSection_paramSlice lam) (hsuppl lam)
      (hallow lam hlam)).1 hx')
  have hZclosed : IsClosed Z :=
    (isClosed_le (continuous_norm.comp continuous_fst) continuous_const).inter
      (isClosed_solutionSet (theorem_3_1_21_preprint hgF ht).isScSmooth)
  have hZ : IsCompact Z :=
    ((isCompact_closedBall _ _).prod hK).of_isClosed_subset hZclosed hZsub
  set Z₁ := Z ∩ {z | z.2 ∉ V₁} with hZ₁def
  have hZ₁closed : IsClosed Z₁ :=
    hZclosed.inter (hV₁o.isClosed_compl.preimage continuous_snd)
  have hZ₁ : IsCompact Z₁ := hZ.of_isClosed_subset hZ₁closed inter_subset_left
  obtain ⟨δ₀, hδ₀, hδ₀W⟩ := exists_pos_forall_mem_of_isCompact hZ₁ hWo fun z hz hz1 => by
    have hz2 : IsZeroAt P f z.2 := by
      have := (isZeroAt_paramSection_iff z).1 hz.1.2
      rw [hz1, paramSlice_zero] at this; exact (hzg _).1 this
    have hz' : z = (0, z.2) := Prod.ext hz1 rfl
    rw [hz']; exact mem_iUnion.2 ⟨⟨z.2, hz2, hz.2⟩, hyWy _⟩
  -- the Sard step on `Z₁₀ = Z₁ ∩ {|λ| ≤ δ/2}`
  set δ : ℝ := min δ₀ δ₁ with hδ
  have hδpos : 0 < δ := lt_min hδ₀ hδ₁pos
  set Z₀ : Set ((Fin m → ℝ) × X) := Z₁ ∩ {z | ‖z.1‖ ≤ δ / 2} with hZ₀def
  have hZ₀closed : IsClosed Z₀ :=
    hZ₁closed.inter (isClosed_le (continuous_norm.comp continuous_fst) continuous_const)
  have hZ₀ : IsCompact Z₀ := hZ₁.of_isClosed_subset hZ₀closed inter_subset_left
  have hZ₀W : ∀ z ∈ Z₀, z ∈ W := fun z hz =>
    hδ₀W z hz.1 (by
      have h2 : ‖z.1‖ ≤ δ / 2 := hz.2
      linarith [min_le_left δ₀ δ₁, hδpos])
  have hlocS : ∀ z : Z₀, ∃ W' : Set ((Fin m → ℝ) × X), IsOpen W' ∧ (z : (Fin m → ℝ) × X) ∈ W' ∧
      ∃ CV : Set (Fin m → ℝ), volume CV = 0 ∧
        ∀ z' ∈ W', IsZeroAt (pullbackProj P Prod.snd)
          (paramSection (sectionAdd P f (fiberZero P)) hgF.isScSmooth.1 t
            fun i => (ht i).1) z' →
          z'.1 ∉ CV → B.IsLinSurjAt (paramSlice (sectionAdd P f (fiberZero P))
            hgF.isScSmooth.1 t (fun i => (ht i).1) z'.1) z'.2 := fun z =>
    exists_null_isLinSurjAt_paramSlice_near hgFt ht z.2.1.1.2
      (hWgood z (hZ₀W z z.2) z.2.1.1.2)
  choose W' hW'o hzW' CV hCV hW'tr using hlocS
  obtain ⟨T', hT'⟩ := hZ₀.elim_finite_subcover W' hW'o
    (fun z hz => mem_iUnion.2 ⟨⟨z, hz⟩, hzW' ⟨z, hz⟩⟩)
  refine ⟨m, t, ht, htsupp, htbd, htN, δ / 2, by positivity, ⋃ z ∈ T', CV z,
    (measure_biUnion_null_iff T'.countable_toSet).2 fun z _ => hCV z, fun lam hlam hlamCV => ?_⟩
  have hlam₁ : ‖lam‖ ≤ δ₁ := by linarith [min_le_right δ₀ δ₁]
  have hsl : B.IsScPlusSection (paramSlice (fiberZero P) hs₀.1 t (fun i => (ht i).1) lam) :=
    isScPlusSection_paramSlice hs₀ ht lam
  have hslsupp := sectionSupport_paramSlice_subset hs₀.1 (fun i => (ht i).1) lam
  have halw : paramSlice (fiberZero P) hs₀.1 t (fun i => (ht i).1) lam ∈
      B.allowableSections N U := by
    refine ⟨hsl, hslsupp.trans (union_subset (by rw [hsupp0]; exact empty_subset _)
      (iUnion_subset htsupp)), fun x hx => ?_⟩
    obtain ⟨hx', h⟩ := hallow lam hlam₁ x
    exact h
  have hbd' : Disjoint (sectionSupport P (paramSlice (fiberZero P) hs₀.1 t
      (fun i => (ht i).1) lam)) PX.boundary := by
    refine Set.disjoint_of_subset_left hslsupp ?_
    rw [hsupp0, empty_union]
    exact Set.disjoint_iUnion_left.2 htbd
  set h := sectionAdd P f (paramSlice (fiberZero P) hs₀.1 t (fun i => (ht i).1) lam) with hhdef
  have hhF : B.IsScFredholmSectionTame h := theorem_3_1_18_tame hf hsl
  -- `h = f` on `V₁`
  have hhV₁ : ∀ y ∈ V₁, f y = h y := fun y hy => by
    have hz : IsZeroAt P (paramSlice (fiberZero P) hs₀.1 t (fun i => (ht i).1) lam) y :=
      isZeroAt_paramSlice_of_not_mem_support hs₀.1 _ lam (by rw [hsupp0]; exact fun h => h)
        fun i hi => (htG i hi).2 (subset_closure hy)
    rw [hhdef, sectionAdd_apply hfs (isSection_paramSlice lam)]
    have h0 : (⟨paramSlice (fiberZero P) hs₀.1 t (fun i => (ht i).1) lam y,
        isSection_paramSlice lam y⟩ : P ⁻¹' {y}) = 0 := Subtype.ext hz
    rw [h0, add_zero]
  have hgood : ∀ y, IsZeroAt P h y → B.IsGoodPositionGermTame h y ∧ B.IsLinSurjAt h y := by
    intro y hy0
    by_cases hyV₁ : y ∈ V₁
    · have hfy : IsZeroAt P f y := by
        change f y = fiberZero P y; rw [hhV₁ y hyV₁]; exact hy0
      have hg := (hVbdgood y (hclV₁ (subset_closure hyV₁)) hfy).congr_nhds hV₁o hyV₁ hhV₁
      exact ⟨hg, hg.isGoodPositionGerm.isLinSurjAt hhF.isScSmooth⟩
    · have hy0' : IsZeroAt P (paramSlice (sectionAdd P f (fiberZero P)) hgF.isScSmooth.1 t
          (fun i => (ht i).1) lam) y := by rw [← hslice lam]; exact hy0
      have hzF := (isZeroAt_paramSection_iff (lam, y)).2 hy0'
      have hzZ₀ : (lam, y) ∈ Z₀ := ⟨⟨⟨hlam₁, hzF⟩, hyV₁⟩, hlam.le⟩
      obtain ⟨z, hzT', hzW'⟩ := mem_iUnion₂.1 (hT' hzZ₀)
      have hlamCV' : lam ∉ CV z := fun h' => hlamCV (mem_iUnion₂.2 ⟨z, hzT', h'⟩)
      have hsurj : B.IsLinSurjAt h y := by
        rw [hhdef, hslice lam]; exact hW'tr z (lam, y) hzW' hzF hlamCV'
      have hyb : y ∉ PX.boundary := hWb (lam, y) (hZ₀W _ hzZ₀)
      have hd : PX.degIndex y = 0 := by
        by_contra hne; exact hyb (Nat.one_le_iff_ne_zero.2 hne)
      exact ⟨StrongBundle.isGoodPositionGerm_of_isLinSurjAt hhF hy0 hd hsurj, hsurj⟩
  refine ⟨halw, hbd', fun y hy => (hgood y hy).2, fun y hy => (hgood y hy).1, hcpt _ halw,
    fun hne => ?_⟩
  obtain ⟨hsub, htameS, hloc, -⟩ :=
    theorem_3_6_11 hhF.toIsScFredholmSection (fun y hy => (hgood y hy).1) hne
  exact ⟨hsub, htameS, hloc⟩

end Theorem519

end Polyfold
