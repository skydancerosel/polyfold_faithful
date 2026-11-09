import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_32

/-! Round trip for V9_32 (Lemma 9.3.4, pp. 423–424 of the 2021 book; 2017: Lemma 9.10:
orientations are determined by good points).

`A` is the conjunction of the types of the ten listed theorems, universes instantiated at `0`
where they have one (`B` lives in `Type`): `EpGroupoid.lemma_9_3_4` (general M-polyfolds, for
`n`-dimensional orientations, under the hypothesis `hgood : ∀ x ∈ supp Θ,
HasOrientedGoodPointsAt x n`, the oriented form of Proposition 9.2.8),
`hasOrientedGoodPointsAt_rn_zero`, `hasOrientedGoodPointsAt_rn` (the hypothesis holds on `ℝᵐ`),
`hasContinuousLevelOneOn_rn`, `orientation_eq_iff_frameDet`,
`SubmanifoldOrientation.exists_isOpen_tangent_eq_iff` (relative orientations are locally
constant), `lemma_9_3_4_of_hasGraphBallAt`, `lemma_9_3_4_rn` (on `ℝᵐ` without hypotheses),
`lemma_9_3_4_mixed_dim` and `lemma_9_3_4_mixed_dim_rn` (without equidimensionality the statement
does not hold as we read it).  The definitions (`IsOrientationOfDim`, `HasOrientedGoodPointsAt`,
`HasContinuousLevelOneOn`, `frameDet`, `mixedTheta`) are vocabulary.

* `B` (for every ep-groupoid, every `n`-dimensional branched `Θ`, any two orientations agreeing
  at the good points agree on `X_∞`) is stronger than `A`'s Lemma 9.3.4 conjuncts:
  `B_to_A_core` derives `lemma_9_3_4` (ignoring `hgood`), `lemma_9_3_4_of_hasGraphBallAt` and
  `lemma_9_3_4_rn` from `B`.  Glue: a project orientation is one in `B`'s sense
  (`isOrientationB_of_isOrientation`), an `n`-dimensional orientation makes `Θ` `n`-dimensional,
  and `B`'s good points are the project's (`goodSetB_subset`).
* `B_to_A` then re-proves the other seven conjuncts outright (copies of the project's proofs,
  renamed `…_c`): they are facts about `ℝᵐ`, linear algebra and a counterexample, which `B` does
  not state.
* `A → B` is not proved.  `A`'s general Lemma 9.3.4 needs `hgood` (Proposition 9.2.8 for oriented
  families with locally constant relative orientations) at every point of `supp Θ`; `A` proves it
  only on `ℝᵐ` (`hasOrientedGoodPointsAt_rn`, from the graph-ball representation
  `HasGraphBallAt` and `HasContinuousLevelOneOn`), and the project lists both inputs on general
  M-polyfolds as not formalized (at boundary points only a cone of directions is admissible).
  `hgood` is satisfiable (it holds on all of `ℝᵐ`) but `B` does not supply it.  A second, smaller
  gap: `B`'s orientations may be represented by sheets of any dimension, `A` needs
  representations with all sheets `n`-dimensional (`IsOrientationOfDim`); for an
  `n`-dimensional `Θ` this should hold (the dimensions of sheets through a point of `supp Θ` are
  forced) but is not a project lemma. -/

namespace RoundTrip.V9_32
open Polyfold Polyfold.MPolyfold Polyfold.EpGroupoid Set Module Submodule Filter Topology
open scoped ContDiff

set_option maxSynthPendingDepth 3

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.lemma_9_3_4.{0}) ∧
  (type_of% @Polyfold.hasOrientedGoodPointsAt_rn_zero) ∧
  (type_of% @Polyfold.hasOrientedGoodPointsAt_rn) ∧
  (type_of% @Polyfold.hasContinuousLevelOneOn_rn) ∧
  (type_of% @Polyfold.orientation_eq_iff_frameDet.{0}) ∧
  (type_of% @Polyfold.MPolyfold.SubmanifoldOrientation.exists_isOpen_tangent_eq_iff.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.lemma_9_3_4_of_hasGraphBallAt.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.lemma_9_3_4_rn) ∧
  (type_of% @Polyfold.lemma_9_3_4_mixed_dim) ∧
  (type_of% @Polyfold.lemma_9_3_4_mixed_dim_rn)

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.lemma_9_3_4.{0}, @Polyfold.hasOrientedGoodPointsAt_rn_zero,
    @Polyfold.hasOrientedGoodPointsAt_rn, @Polyfold.hasContinuousLevelOneOn_rn,
    @Polyfold.orientation_eq_iff_frameDet.{0},
    @Polyfold.MPolyfold.SubmanifoldOrientation.exists_isOpen_tangent_eq_iff.{0},
    @Polyfold.EpGroupoid.lemma_9_3_4_of_hasGraphBallAt.{0}, @Polyfold.EpGroupoid.lemma_9_3_4_rn,
    @Polyfold.lemma_9_3_4_mixed_dim, @Polyfold.lemma_9_3_4_mixed_dim_rn⟩

/-! ### Glue -/

section Glue
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Θ : Obj → ℚ}

/-- A project orientation (Definition 9.3.2) is one in `B`'s sense. -/
theorem isOrientationB_of_isOrientation {T : Obj → X.PObj.OrTangent →₀ ℚ}
    (h : X.IsOrientation Θ T) : IsOrientationB X Θ T where
  mem x hx := h.mem x hx
  functor φ hφ := h.natural φ hφ
  lifts x hx := h.lifts x hx
  locRep x hx := by
    obtain ⟨OB, hOB⟩ := h.locallyOriented x hx
    exact ⟨OB.toLocalBranchingStructure, OB.dim, OB.orient, hOB⟩

/-- An `n`-dimensional orientation makes `Θ` `n`-dimensional. -/
theorem isNDimensional_of_isOrientationOfDim {T : Obj → X.PObj.OrTangent →₀ ℚ} {n : ℕ}
    (h : X.IsOrientationOfDim Θ n T) : X.IsNDimensional Θ n := fun x hx => by
  obtain ⟨OB, hd, -⟩ := h.2 x hx
  exact ⟨OB.toLocalBranchingStructure, fun i => hd i ▸ OB.isSubmanifoldOfDim i⟩

/-- `B`'s good points are the project's. -/
theorem goodSetB_subset : goodSetB X Θ ⊆ X.goodSet Θ := by
  rintro y ⟨hs, x, B, hyU, hy, V, hV, hyV, hVU, h⟩
  exact ⟨hs, x, B, hyU, hy, V, hV, hyV, hVU, fun i j hi hj => by
    rw [inter_comm, h i j ⟨hi, hj⟩, inter_comm]⟩

/-- **Lemma 9.3.4 from `B`**, in the project's terms (no `hgood`). -/
theorem lemma_of_B (hB : B) (hΘ : X.IsBranchedEpSubgroupoid Θ) {n : ℕ}
    {T₁ T₂ : Obj → X.PObj.OrTangent →₀ ℚ} (h₁ : X.IsOrientationOfDim Θ n T₁)
    (h₂ : X.IsOrientationOfDim Θ n T₂) (hagree : ∀ y ∈ X.goodSet Θ, T₁ y = T₂ y) :
    ∀ x ∈ X.PObj.smoothSet, T₁ x = T₂ x :=
  hB Obj Mor X Θ hΘ ⟨n, isNDimensional_of_isOrientationOfDim h₁⟩ T₁ T₂
    (isOrientationB_of_isOrientation h₁.1) (isOrientationB_of_isOrientation h₂.1)
    fun y hy => hagree y (goodSetB_subset hy)

end Glue

/-- The Lemma 9.3.4 conjuncts of `A`. -/
def A_core : Prop :=
  (type_of% @Polyfold.EpGroupoid.lemma_9_3_4.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.lemma_9_3_4_of_hasGraphBallAt.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.lemma_9_3_4_rn)

/-- **`B` gives `A`'s Lemma 9.3.4 conjuncts**, without their hypotheses `hgood`, `hG`, `hlev`. -/
theorem B_to_A_core : B → A_core := fun hB =>
  ⟨fun {_ _} _ _ _ _ _ _ {_} {_} hΘ {_} {_} {_} h₁ h₂ _ hagree => lemma_of_B hB hΘ h₁ h₂ hagree,
    fun {_ _} _ _ _ _ _ _ {_} {_} hΘ {_} {_} {_} h₁ h₂ _ _ hagree =>
      lemma_of_B hB hΘ h₁ h₂ hagree,
    fun {_} {_} _ _ _ {_} {_} _ hΘ {_} {_} {_} h₁ h₂ hagree => lemma_of_B hB hΘ h₁ h₂ hagree⟩

/-! ### `B → A`, the remaining conjuncts: copies of the project's proofs (renamed `…_c`)

The chain `orientation_eq_iff_frameDet` ← `frames_eq_iff_frameDet` ←
`exists_isOpen_tangent_eq_iff` ← `hasOrientedGoodPointsAt_of_hasGraphBallAt` (Proposition 9.2.8
for oriented families, from the graph-ball representation) is copied verbatim; the other lemmas
of the project's proofs (`exists_isOpen_sign_eq`, `frameDet_ne_zero_of_basis`,
`continuousOn_chartVec_of_continuousOn`, `norm_le_two_mul_of_approx`, `hasGraphBallAt_rn`,
`zero_not_mem_goodSet_mixed`, …) are not banned and are used as they are. -/

section FrameDetC
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

theorem orientation_eq_iff_frameDet_c {N : Submodule ℝ E} (Λ : E →L[ℝ] (Fin n → ℝ))
    (b₁ b₂ : Basis (Fin n) ℝ N) (hΛ : frameDet Λ (fun i => (b₁ i : E)) ≠ 0) :
    b₁.orientation = b₂.orientation ↔
      (0 < frameDet Λ (fun i => (b₁ i : E)) ↔ 0 < frameDet Λ (fun i => (b₂ i : E))) := by
  set f : N →ₗ[ℝ] (Fin n → ℝ) := (Λ : E →ₗ[ℝ] (Fin n → ℝ)).comp N.subtype with hfdef
  set e := Pi.basisFun ℝ (Fin n)
  have hli : LinearIndependent ℝ (fun i => f (b₁ i)) := by
    rw [frameDet_eq] at hΛ
    exact ((e.is_basis_iff_det).2 (isUnit_iff_ne_zero.2 hΛ)).1
  have hcard : Fintype.card (Fin n) = finrank ℝ (Fin n → ℝ) := by simp
  set c₁ := basisOfLinearIndependentOfCardEqFinrank' (fun i => f (b₁ i)) hli hcard
  have hc₁ : ∀ i, c₁ i = f (b₁ i) := fun i => by
    rw [coe_basisOfLinearIndependentOfCardEqFinrank' (K := ℝ) _ hli hcard]
  let g : N ≃ₗ[ℝ] (Fin n → ℝ) := b₁.equiv c₁ (Equiv.refl _)
  have hgf : ∀ v, g v = f v := fun v => by
    have : (g : N →ₗ[ℝ] (Fin n → ℝ)) = f := b₁.ext fun i => by
      simp only [g, LinearEquiv.coe_coe, Basis.equiv_apply, Equiv.refl_apply, hc₁]
    exact LinearMap.congr_fun this v
  have hmap : ∀ b : Basis (Fin n) ℝ N, ⇑(b.map g) = fun i => Λ (b i : E) := fun b => by
    funext i; rw [Basis.map_apply, hgf]; rfl
  rw [← (Orientation.map (Fin n) g).injective.eq_iff, ← Basis.orientation_map,
    ← Basis.orientation_map, orientation_eq_iff_det_pos_iff, frameDet_eq, frameDet_eq, hmap,
    hmap]


end FrameDetC

section MPC
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

theorem frames_eq_iff_frameDet_c {y : X} {n : ℕ} {L : Set P.TangentSpace}
    {O₁ O₂ : Set (Fin n → P.TangentSpace)} (h₁ : P.IsOrientedAt y ⟨n, L, O₁⟩)
    (h₂ : P.IsOrientedAt y ⟨n, L, O₂⟩) {ψ : MChart X} (hψ : P.IsChart ψ) (hyψ : y ∈ ψ.source)
    (Λ : ψ.model.E 0 →L[ℝ] (Fin n → ℝ)) {v₁ v₂ : Fin n → P.TangentSpace} (hv₁ : v₁ ∈ O₁)
    (hv₂ : v₂ ∈ O₂) (hΛ : frameDet Λ (fun i => chartVec hψ (v₁ i)) ≠ 0) :
    O₁ = O₂ ↔ (0 < frameDet Λ (fun i => chartVec hψ (v₁ i)) ↔
      0 < frameDet Λ (fun i => chartVec hψ (v₂ i))) := by
  obtain ⟨N₁, hN₁, -, -, ω₁, hO₁⟩ := h₁.isChartOrientation hψ hyψ
  obtain ⟨N₂, hN₂, -, -, ω₂, hO₂⟩ := h₂.isChartOrientation hψ hyψ
  have hNN : N₂ = N₁ := SetLike.coe_injective (hN₂.trans hN₁.symm)
  subst hNN
  change O₁ = chartFrames hψ L N₂ ω₁ at hO₁
  change O₂ = chartFrames hψ L N₂ ω₂ at hO₂
  have hv₁' := hv₁
  rw [hO₁] at hv₁'
  obtain ⟨-, b₁, hb₁, hbo₁⟩ := hv₁'
  have hv₂' := hv₂
  rw [hO₂] at hv₂'
  obtain ⟨-, b₂, hb₂, hbo₂⟩ := hv₂'
  have hf₁ : (fun i => chartVec hψ (v₁ i)) = fun i => (b₁ i : ψ.model.E 0) :=
    funext fun i => (hb₁ i).symm
  have hf₂ : (fun i => chartVec hψ (v₂ i)) = fun i => (b₂ i : ψ.model.E 0) :=
    funext fun i => (hb₂ i).symm
  rw [hf₁] at hΛ ⊢
  rw [hf₂, ← orientation_eq_iff_frameDet_c Λ b₁ b₂ hΛ, hbo₁, hbo₂]
  constructor
  · intro hO
    have h1 := hv₁
    rw [hO, hO₂] at h1
    obtain ⟨-, b, hb, hbo⟩ := h1
    have hbb : b = b₁ := Basis.eq_of_apply_eq fun i => Subtype.ext ((hb i).trans (hb₁ i).symm)
    rw [← hbo, hbb, hbo₁]
  · intro hω
    rw [hO₁, hO₂, hω]

theorem SubmanifoldOrientation.exists_isOpen_tangent_eq_iff_c {A₁ A₂ : Set X} {n : ℕ}
    (hn : 0 < n) (o₁ : P.SubmanifoldOrientation A₁ n) (o₂ : P.SubmanifoldOrientation A₂ n)
    (hl₂ : P.HasContinuousLevelOneOn A₂) {x : X} (hx₁ : x ∈ A₁) (hx₂ : x ∈ A₂)
    (hT : P.submanifoldTangent A₁ x = P.submanifoldTangent A₂ x) :
    ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ ∀ z ∈ A₁ ∩ A₂ ∩ O,
      P.submanifoldTangent A₁ z = P.submanifoldTangent A₂ z →
        (o₁.tangent z = o₂.tangent z ↔ o₁.tangent x = o₂.tangent x) := by
  obtain ⟨φ₁, hφ₁, V₁, hV₁, hxV₁, hV₁φ, e₁, he₁, hc₁⟩ := o₁.continuous hn x hx₁
  obtain ⟨φ₂, hφ₂, V₂, hV₂, hxV₂, hV₂φ, e₂, he₂, hc₂⟩ := o₂.continuous hn x hx₂
  set S₂ : Set X := A₂ ∩ (V₂ ∩ φ₁.source) with hS₂
  have hfib₂ : ∀ z ∈ A₂ ∩ V₂, ∀ i, P.levelVal 1 (P.tangentProj (e₂ z i)) = z := fun z hz i =>
    ((o₂.isOrientedAt z hz.1).mem_carrier (he₂ z hz) i).1
  have hc₂' : ContinuousOn (fun z i => chartVec hφ₁ (e₂ z i)) S₂ :=
    continuousOn_pi.2 fun i => continuousOn_chartVec_of_continuousOn hφ₂ hφ₁ (S := S₂)
      (fun z hz => hV₂φ hz.2.1) (fun z hz => hz.2.2)
      ((hl₂ φ₂ hφ₂).mono fun z hz => ⟨hz.1, hV₂φ hz.2.1⟩) (α := fun z => e₂ z i)
      (fun z hz => hfib₂ z ⟨hz.1, hz.2.1⟩ i)
      ((continuousOn_pi.1 hc₂ i).mono fun z hz => ⟨hz.1, hz.2.1⟩)
  -- the map `Λ`
  obtain ⟨N, hN, hfin, hrank, ωx, hO⟩ := (o₁.isOrientedAt x hx₁).isChartOrientation hφ₁
    (hV₁φ hxV₁)
  have := hfin
  obtain ⟨Q', hQ'⟩ := Submodule.ClosedComplemented.of_finiteDimensional N
  let b₀ : Basis (Fin n) ℝ N := Module.finBasisOfFinrankEq ℝ N hrank
  let Λ : φ₁.model.E 0 →L[ℝ] (Fin n → ℝ) :=
    (b₀.equivFunL : N →L[ℝ] (Fin n → ℝ)).comp Q'
  have hΛN : ∀ v : N, Λ v = b₀.equivFun v := fun v => by
    change b₀.equivFunL (Q' v) = _
    rw [hQ' v]; rfl
  set D₁ : X → ℝ := fun z => frameDet Λ (fun i => chartVec hφ₁ (e₁ z i)) with hD₁
  set D₂ : X → ℝ := fun z => frameDet Λ (fun i => chartVec hφ₁ (e₂ z i)) with hD₂
  have hD₁c : ContinuousOn D₁ (A₁ ∩ V₁) := ContinuousOn.frameDet Λ hc₁
  have hD₂c : ContinuousOn D₂ S₂ := ContinuousOn.frameDet Λ hc₂'
  have hD₁x : D₁ x ≠ 0 := by
    have h := he₁ x ⟨hx₁, hxV₁⟩
    change e₁ x ∈ o₁.frames x at h
    rw [show o₁.frames x = chartFrames hφ₁ (P.submanifoldTangent A₁ x) N ωx from hO] at h
    obtain ⟨-, b, hb, -⟩ := h
    have : D₁ x = frameDet Λ (fun i => (b i : φ₁.model.E 0)) := by
      simp only [hD₁, hb]
    rw [this]
    exact frameDet_ne_zero_of_basis b₀ Λ hΛN b
  have hD₂x : D₂ x ≠ 0 := by
    obtain ⟨N₂, hN₂, -, -, ω₂, hO₂⟩ := (o₂.isOrientedAt x hx₂).isChartOrientation hφ₁
      (hV₁φ hxV₁)
    have hNN : N₂ = N := SetLike.coe_injective (by
      rw [hN₂, hN]
      change chartVec hφ₁ '' P.submanifoldTangent A₂ x = chartVec hφ₁ '' P.submanifoldTangent A₁ x
      rw [hT])
    subst hNN
    have h := he₂ x ⟨hx₂, hxV₂⟩
    change e₂ x ∈ o₂.frames x at h
    rw [show o₂.frames x = chartFrames hφ₁ (P.submanifoldTangent A₂ x) N₂ ω₂ from hO₂] at h
    obtain ⟨-, b, hb, -⟩ := h
    have : D₂ x = frameDet Λ (fun i => (b i : φ₁.model.E 0)) := by
      simp only [hD₂, hb]
    rw [this]
    exact frameDet_ne_zero_of_basis b₀ Λ hΛN b
  obtain ⟨U₁, hU₁, hxU₁, hU₁s⟩ := exists_isOpen_sign_eq hD₁c ⟨hx₁, hxV₁⟩ hD₁x
  obtain ⟨U₂, hU₂, hxU₂, hU₂s⟩ := exists_isOpen_sign_eq hD₂c ⟨hx₂, hxV₂, hV₁φ hxV₁⟩ hD₂x
  have key : ∀ y, y ∈ A₁ ∩ V₁ → y ∈ S₂ →
      P.submanifoldTangent A₁ y = P.submanifoldTangent A₂ y → D₁ y ≠ 0 →
        (o₁.tangent y = o₂.tangent y ↔ (0 < D₁ y ↔ 0 < D₂ y)) := by
    intro y hy₁ hy₂ hTy hDy
    rw [SubmanifoldOrientation.tangent_eq_iff o₁ o₂ hTy]
    have h₁ := o₁.isOrientedAt y hy₁.1
    rw [hTy] at h₁
    exact frames_eq_iff_frameDet_c h₁ (o₂.isOrientedAt y hy₂.1) hφ₁ hy₂.2.2 Λ
      (he₁ y hy₁) (he₂ y ⟨hy₂.1, hy₂.2.1⟩) hDy
  refine ⟨U₁ ∩ U₂ ∩ V₁ ∩ V₂, ((hU₁.inter hU₂).inter hV₁).inter hV₂,
    ⟨⟨⟨hxU₁, hxU₂⟩, hxV₁⟩, hxV₂⟩, fun z hz hTz => ?_⟩
  obtain ⟨⟨hzA₁, hzA₂⟩, ⟨⟨hzU₁, hzU₂⟩, hzV₁⟩, hzV₂⟩ := hz
  have hz₁ : z ∈ A₁ ∩ V₁ := ⟨hzA₁, hzV₁⟩
  have hz₂ : z ∈ S₂ := ⟨hzA₂, hzV₂, hV₁φ hzV₁⟩
  obtain ⟨hDz₁, hsz₁⟩ := hU₁s z ⟨hz₁, hzU₁⟩
  obtain ⟨-, hsz₂⟩ := hU₂s z ⟨hz₂, hzU₂⟩
  rw [key z hz₁ hz₂ hTz hDz₁, key x ⟨hx₁, hxV₁⟩ ⟨hx₂, hxV₂, hV₁φ hxV₁⟩ hT hD₁x, hsz₁, hsz₂]


open scoped Classical in
/-- **The good-point input of Lemma 9.3.4 from the graph representation** (Proposition 9.2.8
for oriented families, 2021 p. 413, with the continuity of orientations): if one chart at `x`
represents every `n`-dimensional submanifold through `x` as a graph over a neighbourhood of `0`
in its tangent space (`HasGraphBallAt`), and level-`1` coordinates are continuous along these
submanifolds, then `HasOrientedGoodPointsAt x n` holds.

The sheets `A_k` tangent to `A_{k₀}` are graphs `u ↦ g_k(u)` over `T = T_xA_{k₀}`.  For `u` in a
small ball `S` around `t h₀` (`h₀ ∈ T` off the other tangent spaces) the points `g_k(u)` miss the
other sheets; by `exists_isOpen_subset_inter_eq_empty_or_subset` there is an open `S' ⊆ S` on
which each coincidence set `{g_k = g_{k'}}` is empty or everything.  For `v ∈ S'` the distinct
points among the `g_k(v)` are the `y_e`; near `y_e` the sheets through it coincide (they are the
graphs of the same map over `S'`), and the relative orientations are those at `x` by
`SubmanifoldOrientation.exists_isOpen_tangent_eq_iff_c`. -/
theorem hasOrientedGoodPointsAt_of_hasGraphBallAt_c {x : X} {n : ℕ} (hG : P.HasGraphBallAt x n)
    (hlev : ∀ A : Set X, P.IsSubmanifoldOfDim A n → x ∈ A → P.HasContinuousLevelOneOn A) :
    P.HasOrientedGoodPointsAt x n := by
  intro κ _ A d o hd hA hx k₀ W hW hxW
  obtain rfl : d = fun _ => n := funext hd
  obtain ⟨φ, hφ, hxφ, hGA⟩ := hG
  have hGk : ∀ k, P.IsGraphBallAt hφ (A k) x := fun k => hGA (A k) (hA k) (hx k)
  -- the tangent spaces
  choose N hN hfin using fun k => exists_submodule_chartTangent hφ (hA k).1 (hx k) hxφ
  have hrank : ∀ k, finrank ℝ (N k) = n := fun k =>
    finrank_chartTangent hφ ((hA k).2 x (hx k)) (hA k).1 hxφ (hN k)
  set C : κ → Prop := fun k =>
    P.submanifoldTangent (A k) x = P.submanifoldTangent (A k₀) x with hCdef
  have hC₀ : C k₀ := rfl
  have hCN : ∀ k, C k ↔ N k = N k₀ := fun k => by
    change P.submanifoldTangent (A k) x = P.submanifoldTangent (A k₀) x ↔ _
    rw [← chartTangent_eq_iff hφ hxφ, ← hN k, ← hN k₀, SetLike.coe_set_eq]
  set N₀ := N k₀ with hN₀def
  have : FiniteDimensional ℝ N₀ := hfin k₀
  have hTC : ∀ k, C k → P.chartTangent hφ (A k) x = (N₀ : Set (φ.model.E 0)) := fun k hk => by
    rw [← hN k, (hCN k).1 hk]
  -- the projection `Q` onto `T`
  obtain ⟨Q', hQ'⟩ := Submodule.ClosedComplemented.of_finiteDimensional N₀
  set Q : φ.model.E 0 →L[ℝ] φ.model.E 0 := N₀.subtypeL.comp Q' with hQdef
  have hQN : ∀ v, Q v ∈ N₀ := fun v => (Q' v).2
  have hQid : ∀ v ∈ N₀, Q v = v := fun v hv => congrArg Subtype.val (hQ' ⟨v, hv⟩)
  set η : ℝ := 1 / (2 * (‖Q‖ + 1)) with hηdef
  have hη : 0 < η := by positivity
  -- the direction `h₀` and the distances `ρ k` to the other tangent spaces
  have hnle : ∀ k, ¬ C k → ¬ N₀ ≤ N k := fun k hk hle => by
    have := hfin k
    exact hk ((hCN k).2 (Submodule.eq_of_le_of_finrank_eq hle (by rw [hrank, hrank])).symm)
  have hclosed : ∀ k, IsClosed (N k : Set (φ.model.E 0)) := fun k => by
    have := hfin k
    exact Submodule.closed_of_finiteDimensional _
  obtain ⟨h₀, hh₀N, -, hh₀S⟩ := exists_mem_ball_forall_not_mem (N := N₀) (ι := {k // ¬ C k})
    (fun k => N k.1) (fun k => hclosed k.1) (fun k => hnle k.1 k.2) N₀.zero_mem one_pos
  have hrad : ∀ k, ¬ C k → ∃ ρ > 0, ∀ v ∈ N k, ρ ≤ ‖h₀ - v‖ := fun k hk => by
    have hmem : h₀ ∈ (N k : Set (φ.model.E 0))ᶜ := hh₀S ⟨k, hk⟩
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 (hclosed k).isOpen_compl h₀ hmem
    refine ⟨ρ, hρ, fun v hv => ?_⟩
    by_contra hlt
    push Not at hlt
    exact hball (by rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]; exact hlt) hv
  choose! ρ hρ hρv using hrad
  have hρev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ≤ 1 ∧ ∀ k, ¬ C k → ε ≤ ρ k := by
    refine Filter.Eventually.and ?_ (Filter.eventually_all.2 fun k => ?_)
    · exact ((eventually_lt_nhds one_pos).mono fun _ h => h.le).filter_mono nhdsWithin_le_nhds
    · by_cases hk : ¬ C k
      · exact ((eventually_lt_nhds (hρ k hk)).mono fun _ h _ => h.le).filter_mono
          nhdsWithin_le_nhds
      · exact Filter.Eventually.of_forall fun _ h => (hk h).elim
  obtain ⟨ρ₀, ⟨hρ₀1, hρ₀ρ⟩, hρ₀⟩ := (hρev.and self_mem_nhdsWithin).exists
  have hρ₀ : (0 : ℝ) < ρ₀ := hρ₀
  -- the constants
  set H : ℝ := ‖h₀‖ + 1 with hHdef
  have hH : 0 < H := by positivity
  set τ : ℝ := ρ₀ / 3 with hτdef
  set εg : ℝ := min 1 (ρ₀ / (3 * H)) with hεgdef
  have hεg : 0 < εg := lt_min one_pos (by positivity)
  have hεg1 : εg ≤ 1 := min_le_left _ _
  have hεgH : εg * H ≤ ρ₀ / 3 := by
    calc εg * H ≤ ρ₀ / (3 * H) * H := mul_le_mul_of_nonneg_right (min_le_right _ _) hH.le
      _ = ρ₀ / 3 := by field_simp
  set ε₁ : ℝ := ρ₀ / (6 * H) with hε₁def
  have hε₁ : 0 < ε₁ := by positivity
  -- the graph maps, the approximation radii
  have hgr : ∀ k, C k → ∃ r > 0, ∀ u ∈ N₀, ‖u‖ < r → ∃ a ∈ A k ∩ φ.source,
      Q (φ a - φ x) = u ∧ ‖(φ a - φ x) - u‖ ≤ εg * ‖u‖ := fun k hk => by
    obtain ⟨r, hr, h⟩ := (hGk k).ball Q (fun v => by rw [hTC k hk]; exact hQN v)
      (fun v hv => hQid v (by rw [hTC k hk] at hv; exact hv)) εg hεg
    exact ⟨r, hr, fun u hu hur => h u (by rw [hTC k hk]; exact hu) hur⟩
  choose! r hr hgr using hgr
  choose δ₁ hδ₁ happ₁ using fun k => (hGk k).approx η hη
  choose δ₂ hδ₂ happ₂ using fun k => (hGk k).approx ε₁ hε₁
  have hlip : ∀ k, C k → ∀ a ∈ A k ∩ φ.source, ∀ b ∈ A k ∩ φ.source,
      ‖φ a - φ x‖ < δ₁ k → ‖φ b - φ x‖ < δ₁ k →
        ‖φ a - φ b‖ ≤ 2 * ‖Q (φ a - φ x) - Q (φ b - φ x)‖ := by
    intro k hk a ha b hb hax hbx
    obtain ⟨v, hv, hvab⟩ := happ₁ k a ha b hb hax hbx
    rw [hTC k hk] at hv
    have h := norm_le_two_mul_of_approx hQid hv hvab
    rwa [show Q (φ a - φ b) = Q (φ a - φ x) - Q (φ b - φ x) by
      rw [← map_sub]; congr 1; abel] at h
  -- the orientation neighbourhoods
  have hor : ∀ k k', ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ (0 < n → C k → C k' →
      ∀ z ∈ A k ∩ A k' ∩ O, P.submanifoldTangent (A k) z = P.submanifoldTangent (A k') z →
        ((o k).tangent z = (o k').tangent z ↔ (o k).tangent x = (o k').tangent x)) := by
    intro k k'
    by_cases h : 0 < n ∧ C k ∧ C k'
    · obtain ⟨O, hO, hxO, hOp⟩ := SubmanifoldOrientation.exists_isOpen_tangent_eq_iff_c h.1
        (o k) (o k') (hlev _ (hA k') (hx k')) (hx k) (hx k') (h.2.1.trans h.2.2.symm)
      exact ⟨O, hO, hxO, fun _ _ _ => hOp⟩
    · exact ⟨univ, isOpen_univ, mem_univ x, fun hn hk hk' => (h ⟨hn, hk, hk'⟩).elim⟩
  choose O hO hxO hOp using hor
  set W₁ : Set X := W ∩ ⋂ k, ⋂ k', O k k' with hW₁def
  have hW₁ : IsOpen W₁ := hW.inter (isOpen_iInter_of_finite fun k =>
    isOpen_iInter_of_finite fun k' => hO k k')
  have hxW₁ : x ∈ W₁ := ⟨hxW, mem_iInter.2 fun k => mem_iInter.2 fun k' => hxO k k'⟩
  obtain ⟨ρW, hρW, hρWsub⟩ := exists_pos_forall_mem_of_mem_nhds hxφ (hW₁.mem_nhds hxW₁)
  -- the radius `R` and the parameter `t`
  have hRev : ∀ᶠ R in 𝓝[>] (0 : ℝ), (∀ k, C k → R < r k) ∧ (∀ k, R < δ₁ k) ∧
      (∀ k, R < δ₂ k) ∧ R < ρW := by
    refine (Filter.eventually_all.2 fun k => ?_).and ((Filter.eventually_all.2 fun k => ?_).and
      ((Filter.eventually_all.2 fun k => ?_).and ?_))
    · by_cases hk : C k
      · exact ((eventually_lt_nhds (hr k hk)).mono fun _ h _ => h).filter_mono nhdsWithin_le_nhds
      · exact Filter.Eventually.of_forall fun _ h => (hk h).elim
    · exact (eventually_lt_nhds (hδ₁ k)).filter_mono nhdsWithin_le_nhds
    · exact (eventually_lt_nhds (hδ₂ k)).filter_mono nhdsWithin_le_nhds
    · exact (eventually_lt_nhds hρW).filter_mono nhdsWithin_le_nhds
  obtain ⟨R, ⟨hRr, hRδ₁, hRδ₂, hRW⟩, hR0⟩ := (hRev.and self_mem_nhdsWithin).exists
  have hR0 : (0 : ℝ) < R := hR0
  set t : ℝ := R / (2 * H) with htdef
  have ht : 0 < t := by positivity
  have htH : 2 * (t * H) = R := by rw [htdef]; field_simp
  -- the parameter set `S`
  set S : Set N₀ := {u | ‖(u : φ.model.E 0) - t • h₀‖ < τ * t} with hSdef
  have hSo : IsOpen S := isOpen_lt ((continuous_subtype_val.sub continuous_const).norm)
    continuous_const
  have hSnorm : ∀ u ∈ S, ‖(u : φ.model.E 0)‖ < t * H := fun u hu => by
    have hu' : ‖(u : φ.model.E 0) - t • h₀‖ < τ * t := hu
    have hτ1 : τ ≤ 1 := by rw [hτdef]; linarith
    calc ‖(u : φ.model.E 0)‖ = ‖((u : φ.model.E 0) - t • h₀) + t • h₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖(u : φ.model.E 0) - t • h₀‖ + ‖t • h₀‖ := norm_add_le _ _
      _ < τ * t + t * ‖h₀‖ := by rw [norm_smul, Real.norm_of_nonneg ht.le]; linarith
      _ ≤ t * H := by rw [hHdef]; nlinarith
  have hg : ∀ k, C k → ∀ u : N₀, u ∈ S → ∃ a ∈ A k ∩ φ.source,
      Q (φ a - φ x) = u ∧ ‖(φ a - φ x) - u‖ ≤ εg * ‖(u : φ.model.E 0)‖ := fun k hk u hu =>
    hgr k hk u u.2 ((hSnorm u hu).trans (by linarith [hRr k hk]))
  have : Nonempty X := ⟨x⟩
  choose! g hgA hgQ hgest using hg
  have hgnorm : ∀ k, C k → ∀ u ∈ S, ‖φ (g k u) - φ x‖ ≤ 2 * ‖(u : φ.model.E 0)‖ := by
    intro k hk u hu
    have h1 := hgest k hk u hu
    calc ‖φ (g k u) - φ x‖ = ‖((φ (g k u) - φ x) - u) + u‖ := by rw [sub_add_cancel]
      _ ≤ ‖(φ (g k u) - φ x) - u‖ + ‖(u : φ.model.E 0)‖ := norm_add_le _ _
      _ ≤ 2 * ‖(u : φ.model.E 0)‖ := by nlinarith [norm_nonneg (u : φ.model.E 0)]
  have hgR : ∀ k, C k → ∀ u ∈ S, ‖φ (g k u) - φ x‖ < R := fun k hk u hu => by
    linarith [hgnorm k hk u hu, hSnorm u hu]
  -- uniqueness of the graph point
  have huniq : ∀ k, C k → ∀ u ∈ S, ∀ a ∈ A k ∩ φ.source, ‖φ a - φ x‖ < R →
      Q (φ a - φ x) = u → a = g k u := by
    intro k hk u hu a ha haR hQa
    have h := hlip k hk a ha (g k u) (hgA k hk u hu) (haR.trans (hRδ₁ k))
      ((hgR k hk u hu).trans (hRδ₁ k))
    rw [hQa, hgQ k hk u hu, sub_self, norm_zero, mul_zero] at h
    exact φ.toPartialEquiv.injOn ha.2 (hgA k hk u hu).2 (sub_eq_zero.1 (norm_le_zero_iff.1 h))
  -- the graph points over `S` miss the sheets of the other classes
  have havoid : ∀ j, C j → ∀ u ∈ S, ∀ k, ¬ C k → g j u ∉ A k := by
    intro j hj u hu k hk hjk
    set a := g j u with hadef
    have hxA : x ∈ A k ∩ φ.source := ⟨hx k, hxφ⟩
    obtain ⟨w, hw, hwa⟩ := happ₂ k a ⟨hjk, (hgA j hj u hu).2⟩ x hxA
      ((hgR j hj u hu).trans (hRδ₂ k)) (by rw [sub_self, norm_zero]; exact hδ₂ k)
    rw [← hN k] at hw
    have hu' : ‖(u : φ.model.E 0) - t • h₀‖ < τ * t := hu
    have hun := hSnorm u hu
    have h1 : ‖(φ a - φ x) - w‖ ≤ ε₁ * (2 * (t * H)) := by
      calc ‖(φ a - φ x) - w‖ ≤ ε₁ * ‖φ a - φ x‖ := hwa
        _ ≤ ε₁ * (2 * ‖(u : φ.model.E 0)‖) :=
            mul_le_mul_of_nonneg_left (hgnorm j hj u hu) hε₁.le
        _ ≤ ε₁ * (2 * (t * H)) := by nlinarith
    have h1' : ε₁ * (2 * (t * H)) = ρ₀ / 3 * t := by rw [hε₁def]; field_simp; ring
    have h2 : ‖(φ a - φ x) - u‖ ≤ ρ₀ / 3 * t := by
      calc ‖(φ a - φ x) - u‖ ≤ εg * ‖(u : φ.model.E 0)‖ := hgest j hj u hu
        _ ≤ εg * (t * H) := mul_le_mul_of_nonneg_left hun.le hεg.le
        _ = εg * H * t := by ring
        _ ≤ ρ₀ / 3 * t := mul_le_mul_of_nonneg_right hεgH ht.le
    have h3 : ‖t • h₀ - w‖ < ρ₀ * t := by
      calc ‖t • h₀ - w‖ = ‖(t • h₀ - u) + (u - (φ a - φ x)) + ((φ a - φ x) - w)‖ := by
            congr 1; abel
        _ ≤ ‖t • h₀ - u‖ + ‖(u : φ.model.E 0) - (φ a - φ x)‖ + ‖(φ a - φ x) - w‖ :=
            norm_add₃_le
        _ < τ * t + ρ₀ / 3 * t + ρ₀ / 3 * t := by
            have e1 : ‖t • h₀ - u‖ = ‖(u : φ.model.E 0) - t • h₀‖ := norm_sub_rev _ _
            have e2 : ‖(u : φ.model.E 0) - (φ a - φ x)‖ = ‖(φ a - φ x) - u‖ := norm_sub_rev _ _
            linarith
        _ = ρ₀ * t := by rw [hτdef]; ring
    have hw' : t⁻¹ • w ∈ N k := (N k).smul_mem _ hw
    have h4 := hρv k hk _ hw'
    have h5 : ‖h₀ - t⁻¹ • w‖ = t⁻¹ * ‖t • h₀ - w‖ := by
      have : h₀ - t⁻¹ • w = t⁻¹ • (t • h₀ - w) := by
        rw [smul_sub, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
      rw [this, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le)]
    have h6 : t⁻¹ * ‖t • h₀ - w‖ < ρ₀ := by rw [inv_mul_lt_iff₀ ht]; linarith
    linarith [hρ₀ρ k hk]
  -- continuity of the graph maps on `S`
  have hGc : ∀ k, C k → ContinuousOn (fun u => φ (g k u)) S := by
    intro k hk
    refine Metric.continuousOn_iff.2 fun u hu ε hε => ⟨ε / 2, by positivity, fun u' hu' hd => ?_⟩
    have h := hlip k hk (g k u') (hgA k hk u' hu') (g k u) (hgA k hk u hu)
      ((hgR k hk u' hu').trans (hRδ₁ k)) ((hgR k hk u hu).trans (hRδ₁ k))
    rw [hgQ k hk u' hu', hgQ k hk u hu] at h
    rw [Subtype.dist_eq, dist_eq_norm] at hd
    rw [dist_eq_norm]
    linarith
  -- the shrinking step
  let ι := {p : κ × κ // C p.1 ∧ C p.2}
  let M : ι → Set N₀ := fun p => {u | φ (g p.1.1 u) = φ (g p.1.2 u)}
  have hMo : ∀ p : ι, IsOpen (S \ M p) := fun p => by
    have hc := (hGc p.1.1 p.2.1).sub (hGc p.1.2 p.2.2)
    have h := hc.isOpen_inter_preimage hSo (isOpen_compl_singleton (x := (0 : φ.model.E 0)))
    convert h using 1
    ext u
    simp only [M, Set.mem_sdiff, Set.mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_compl_iff,
      mem_singleton_iff, Pi.sub_apply, sub_eq_zero]
  have hS0 : (⟨t • h₀, N₀.smul_mem t hh₀N⟩ : N₀) ∈ S := by
    change ‖t • h₀ - t • h₀‖ < τ * t
    rw [sub_self, norm_zero]; positivity
  obtain ⟨S', hS'S, hS'o, ⟨v, hvS', -⟩, hS'M⟩ :=
    exists_isOpen_subset_inter_eq_empty_or_subset M hMo hSo subset_rfl
      (Y := univ) ⟨_, hS0, mem_univ _⟩
  have hvS : v ∈ S := hS'S hvS'
  -- the points `y_e`
  set pts : Finset X := (Finset.univ.filter C).image (fun k => g k v) with hptsdef
  have hmem : ∀ k, C k → g k v ∈ pts := fun k hk =>
    Finset.mem_image.2 ⟨k, Finset.mem_filter.2 ⟨Finset.mem_univ k, hk⟩, rfl⟩
  set enum := pts.equivFin with henum
  refine ⟨pts.card, fun k => if hk : C k then enum ⟨g k v, hmem k hk⟩
    else enum ⟨g k₀ v, hmem k₀ hC₀⟩, fun e => (enum.symm e : X), fun e => ?_⟩
  obtain ⟨j, hj, hjv⟩ := Finset.mem_image.1 (enum.symm e).2
  have hjC : C j := (Finset.mem_filter.1 hj).2
  set ye : X := (enum.symm e : X) with hyedef
  have hyeA : ye ∈ A j ∩ φ.source := hjv ▸ hgA j hjC v hvS
  have hyeQ : Q (φ ye - φ x) = v := hjv ▸ hgQ j hjC v hvS
  have hyeR : ‖φ ye - φ x‖ < R := hjv ▸ hgR j hjC v hvS
  have hyeW₁ : ye ∈ W₁ := hρWsub ye hyeA.2 (hyeR.trans hRW)
  -- the sheets through `y_e`
  have hsheet : ∀ k, ye ∈ A k ↔ C k ∧ (if hk : C k then enum ⟨g k v, hmem k hk⟩
      else enum ⟨g k₀ v, hmem k₀ hC₀⟩) = e := by
    intro k
    constructor
    · intro hk
      by_cases hCk : C k
      · have hyk : ye = g k v := huniq k hCk v hvS ye ⟨hk, hyeA.2⟩ hyeR hyeQ
        refine ⟨hCk, ?_⟩
        rw [dif_pos hCk]
        have : (⟨g k v, hmem k hCk⟩ : pts) = enum.symm e := Subtype.ext hyk.symm
        rw [this, Equiv.apply_symm_apply]
      · exact absurd (hjv ▸ hk) (havoid j hjC v hvS k hCk)
    · rintro ⟨hCk, hbk⟩
      rw [dif_pos hCk] at hbk
      have h1 : (⟨g k v, hmem k hCk⟩ : pts) = enum.symm e := by
        rw [← hbk, Equiv.symm_apply_apply]
      have h2 : g k v = ye := congrArg Subtype.val h1
      rw [← h2]
      exact (hgA k hCk v hvS).1
  have hsame : ∀ k, ye ∈ A k → C k ∧ g k v = ye := fun k hk =>
    have hCk := ((hsheet k).1 hk).1
    ⟨hCk, (huniq k hCk v hvS ye ⟨hk, hyeA.2⟩ hyeR hyeQ).symm⟩
  -- the neighbourhood `V` of `y_e`
  obtain ⟨G, hGo, hGS'⟩ := isOpen_induced_iff.1 hS'o
  set G' : Set (φ.model.E 0) := {w | ‖w - φ x‖ < R ∧ Q (w - φ x) ∈ G} with hG'def
  have hG'o : IsOpen G' := (isOpen_lt (continuous_id.sub continuous_const).norm
    continuous_const).inter (hGo.preimage (Q.continuous.comp (continuous_id.sub continuous_const)))
  set V : Set X := φ.source ∩ φ ⁻¹' G' with hVdef
  have hVo : IsOpen V := φ.continuousOn_toFun.isOpen_inter_preimage φ.isOpen_source hG'o
  have hmemS' : ∀ u : N₀, (u : φ.model.E 0) ∈ G ↔ u ∈ S' := fun u => by
    rw [← hGS']; rfl
  have hyeV : ye ∈ V := ⟨hyeA.2, hyeR, by rw [hyeQ]; exact (hmemS' v).2 hvS'⟩
  have hcoinc : ∀ k k', ye ∈ A k → ye ∈ A k' → V ∩ A k ⊆ A k' := by
    intro k k' hk hk' a ⟨haV, hak⟩
    obtain ⟨hCk, hgk⟩ := hsame k hk
    obtain ⟨hCk', hgk'⟩ := hsame k' hk'
    have hM : S' ∩ univ ⊆ M ⟨(k, k'), hCk, hCk'⟩ := by
      rcases hS'M ⟨(k, k'), hCk, hCk'⟩ with h | h
      · exact absurd h (Set.nonempty_iff_ne_empty.1 ⟨v, ⟨hvS', mem_univ _⟩,
          show φ (g k v) = φ (g k' v) by rw [hgk, hgk']⟩)
      · exact h
    set u : N₀ := ⟨Q (φ a - φ x), hQN _⟩
    have huS' : u ∈ S' := (hmemS' u).1 haV.2.2
    have huS : u ∈ S := hS'S huS'
    have ha : a = g k u := huniq k hCk u huS a ⟨hak, haV.1⟩ haV.2.1 rfl
    have hkk' : φ (g k u) = φ (g k' u) := hM ⟨huS', mem_univ _⟩
    have hgg : g k u = g k' u :=
      φ.toPartialEquiv.injOn (hgA k hCk u huS).2 (hgA k' hCk' u huS).2 hkk'
    rw [ha, hgg]
    exact (hgA k' hCk' u huS).1
  have hVeq : ∀ k k', ye ∈ A k → ye ∈ A k' → V ∩ A k = V ∩ A k' := fun k k' hk hk' =>
    Subset.antisymm (fun a ha => ⟨ha.1, hcoinc k k' hk hk' ha⟩)
      (fun a ha => ⟨ha.1, hcoinc k' k hk' hk ha⟩)
  refine ⟨hyeW₁.1, hsheet, ⟨V, hVo, hyeV, hVeq⟩, fun k k' hk hk' => ?_⟩
  -- the relative orientations
  by_cases hn : n = 0
  · have hv0 : (v : φ.model.E 0) = 0 := by
      have : Subsingleton N₀ := Module.finrank_zero_iff.1 ((hrank k₀).trans hn)
      rw [Subsingleton.elim v 0]; rfl
    have hye : ye = x := by
      have h1 := hgest j hjC v hvS
      rw [hv0, norm_zero, mul_zero, sub_zero] at h1
      have h2 := φ.toPartialEquiv.injOn (hgA j hjC v hvS).2 hxφ
        (sub_eq_zero.1 (norm_le_zero_iff.1 h1))
      rw [← hjv]
      exact h2
    change (o k).tangent ye = (o k').tangent ye ↔ _
    rw [hye]
  · have hTye : P.submanifoldTangent (A k) ye = P.submanifoldTangent (A k') ye := by
      rw [← submanifoldTangent_inter_isOpen hVo hyeV, ← submanifoldTangent_inter_isOpen hVo hyeV
        (A := A k'), inter_comm, hVeq k k' hk hk', inter_comm]
    exact hOp k k' (Nat.pos_of_ne_zero hn) (hsame k hk).1 (hsame k' hk').1 ye
      ⟨⟨hk, hk'⟩, mem_iInter.1 (mem_iInter.1 hyeW₁.2 k) k'⟩ hTye


end MPC

theorem hasContinuousLevelOneOn_rn_c {m : ℕ} (A : Set (Fin m → ℝ)) :
    (rnPolyfold m).HasContinuousLevelOneOn A := fun _ hφ =>
  (continuousOn_levelLift_comp MPolyfold.isScSmoothMap_id hφ 1).mono fun _ hz => hz.2

theorem hasOrientedGoodPointsAt_rn_c {m : ℕ} (x : Fin m → ℝ) (n : ℕ) :
    (rnPolyfold m).HasOrientedGoodPointsAt x n :=
  hasOrientedGoodPointsAt_of_hasGraphBallAt_c (hasGraphBallAt_rn x n)
    fun A _ _ => hasContinuousLevelOneOn_rn_c A

theorem hasOrientedGoodPointsAt_rn_zero_c (x : Fin 0 → ℝ) (n : ℕ) :
    (rnPolyfold 0).HasOrientedGoodPointsAt x n := by
  intro κ _ A d o _ _ hx k₀ W _ hxW
  have hA : ∀ k, A k = A k₀ := fun k => Set.ext fun z => by
    rw [Subsingleton.elim z x]; exact iff_of_true (hx k) (hx k₀)
  refine ⟨1, fun _ => 0, fun _ => x, fun e => ⟨hxW, fun k => ?_,
    ⟨univ, isOpen_univ, mem_univ _, fun k k' _ _ => by rw [hA k, hA k']⟩,
    fun k k' _ _ => Iff.rfl⟩⟩
  exact iff_of_true (hx k) ⟨by rw [hA k], Subsingleton.elim _ _⟩


section MixedDim

open scoped Classical in
/-- **Lemma 9.3.4 does not hold as we read it without equidimensionality**: for
`Θ = 1_{ℝ × {0}} + 1_{(0, 0)}` (a branched ep⁺-subgroupoid of `ℝ²`), the two orientations
`T_y(ℝ × {0}, +) + T_y({0}, ±)` agree at every good point but differ at the bad point `(0, 0)`
(given Theorem 9.2.1's independence for `Θ`). -/
theorem lemma_9_3_4_mixed_dim_c
    (hind : (trivial (rnPolyfold 2)).HasIndependentTangentSums mixedTheta) :
    (trivial (rnPolyfold 2)).IsBranchedEpSubgroupoid mixedTheta ∧
    ∃ T₁ T₂ : (Fin 2 → ℝ) → (rnPolyfold 2).OrTangent →₀ ℚ,
      (trivial (rnPolyfold 2)).IsOrientation mixedTheta T₁ ∧
      (trivial (rnPolyfold 2)).IsOrientation mixedTheta T₂ ∧
      (∀ y ∈ (trivial (rnPolyfold 2)).goodSet mixedTheta, T₁ y = T₂ y) ∧ T₁ 0 ≠ T₂ 0 := by
  obtain ⟨O₁, O₂, hne, h₁, h₂⟩ := exists_two_orientations_point (n := 2) 0
  refine ⟨mixedTheta_isBranched, orientedSumRn mixedM (fun _ => 1) (mixedOrient O₁ h₁),
    orientedSumRn mixedM (fun _ => 1) (mixedOrient O₂ h₂),
    isOrientation_sum_rn' mixedM (fun _ => 1) (fun _ => one_pos) mixedM_isSubmanifoldOfDim
      isClosed_mixedM _ rfl hind,
    isOrientation_sum_rn' mixedM (fun _ => 1) (fun _ => one_pos) mixedM_isSubmanifoldOfDim
      isClosed_mixedM _ rfl hind, fun y hy => ?_, fun h => ?_⟩
  · have hy0 : y ∉ mixedM false := fun h => zero_not_mem_goodSet_mixed (h ▸ hy)
    rw [orientedSumRn_bool, orientedSumRn_bool, if_neg hy0, if_neg hy0]
    rfl
  · rw [orientedSumRn_bool, orientedSumRn_bool, if_pos (zero_mem_mixedM true),
      if_pos (zero_mem_mixedM true), if_pos (zero_mem_mixedM false),
      if_pos (zero_mem_mixedM false)] at h
    have h' := (Finsupp.single_left_inj one_ne_zero).1 (add_left_cancel h)
    apply hne
    change (⟨0, (rnPolyfold 2).submanifoldTangent {0} 0, O₁⟩ : (rnPolyfold 2).OrTangent) =
      ⟨0, (rnPolyfold 2).submanifoldTangent {0} 0, O₂⟩ at h'
    simpa using h'


end MixedDim

theorem lemma_9_3_4_mixed_dim_rn_c :
    (trivial (rnPolyfold 2)).IsBranchedEpSubgroupoid mixedTheta ∧
    ∃ T₁ T₂ : (Fin 2 → ℝ) → (rnPolyfold 2).OrTangent →₀ ℚ,
      (trivial (rnPolyfold 2)).IsOrientation mixedTheta T₁ ∧
      (trivial (rnPolyfold 2)).IsOrientation mixedTheta T₂ ∧
      (∀ y ∈ (trivial (rnPolyfold 2)).goodSet mixedTheta, T₁ y = T₂ y) ∧ T₁ 0 ≠ T₂ 0 :=
  lemma_9_3_4_mixed_dim_c (hasIndependentTangentSums_rn rfl _)

/-- **`B → A`**: the Lemma 9.3.4 conjuncts from `B` (`B_to_A_core`), the other seven re-proved
outright. -/
theorem B_to_A : B → A := fun hB =>
  ⟨(B_to_A_core hB).1, @hasOrientedGoodPointsAt_rn_zero_c, @hasOrientedGoodPointsAt_rn_c,
    @hasContinuousLevelOneOn_rn_c, @orientation_eq_iff_frameDet_c,
    @SubmanifoldOrientation.exists_isOpen_tangent_eq_iff_c, (B_to_A_core hB).2.1,
    (B_to_A_core hB).2.2, @lemma_9_3_4_mixed_dim_c, @lemma_9_3_4_mixed_dim_rn_c⟩

#rt_check RoundTrip.V9_32.B_to_A_core [Polyfold.EpGroupoid.lemma_9_3_4,
  Polyfold.hasOrientedGoodPointsAt_rn_zero, Polyfold.hasOrientedGoodPointsAt_rn,
  Polyfold.hasContinuousLevelOneOn_rn, Polyfold.orientation_eq_iff_frameDet,
  Polyfold.MPolyfold.SubmanifoldOrientation.exists_isOpen_tangent_eq_iff,
  Polyfold.EpGroupoid.lemma_9_3_4_of_hasGraphBallAt, Polyfold.EpGroupoid.lemma_9_3_4_rn,
  Polyfold.lemma_9_3_4_mixed_dim, Polyfold.lemma_9_3_4_mixed_dim_rn]
#rt_check RoundTrip.V9_32.B_to_A [Polyfold.EpGroupoid.lemma_9_3_4,
  Polyfold.hasOrientedGoodPointsAt_rn_zero, Polyfold.hasOrientedGoodPointsAt_rn,
  Polyfold.hasContinuousLevelOneOn_rn, Polyfold.orientation_eq_iff_frameDet,
  Polyfold.MPolyfold.SubmanifoldOrientation.exists_isOpen_tangent_eq_iff,
  Polyfold.EpGroupoid.lemma_9_3_4_of_hasGraphBallAt, Polyfold.EpGroupoid.lemma_9_3_4_rn,
  Polyfold.lemma_9_3_4_mixed_dim, Polyfold.lemma_9_3_4_mixed_dim_rn]
#rt_overlap RoundTrip.V9_32.B_to_A [Polyfold.EpGroupoid.lemma_9_3_4,
  Polyfold.hasOrientedGoodPointsAt_rn_zero, Polyfold.hasOrientedGoodPointsAt_rn,
  Polyfold.hasContinuousLevelOneOn_rn, Polyfold.orientation_eq_iff_frameDet,
  Polyfold.MPolyfold.SubmanifoldOrientation.exists_isOpen_tangent_eq_iff,
  Polyfold.EpGroupoid.lemma_9_3_4_of_hasGraphBallAt, Polyfold.EpGroupoid.lemma_9_3_4_rn,
  Polyfold.lemma_9_3_4_mixed_dim, Polyfold.lemma_9_3_4_mixed_dim_rn]

end RoundTrip.V9_32
