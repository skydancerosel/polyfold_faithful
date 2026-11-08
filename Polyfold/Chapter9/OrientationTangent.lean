import Polyfold.Chapter9.Boundary

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.3 "Orientations": the oriented version `Gr̂(X)` of the `Gr(X)`
construction (2021 p. 422; 2017 p. 310) and **Remark 9.3.1** (2021 p. 422; 2017: Remark 9.7).
Numbers and pages are the 2021 text's, the 2017 ones in parentheses.

# Oriented tangent spaces and `Gr̂(X)`

## The text, paraphrased

An oriented finite-dimensional linear space is a pair `(L, o)`, `o` a component of
`Λ^max L ∖ {0}` (`Λ^max {0} = ℝ`); the other component is `-o`.  For smooth `x`, `Gr̂(x)` is the
set of finite formal sums `∑ σ_{L̂} · L̂` of smooth, oriented, finite-dimensional linear subspaces
of `T_xX`, and `Gr̂(X) = ⋃_{x ∈ X_∞} Gr̂(x)` with projection `π̂` to `X_∞`.  It is a category: a
morphism `(L̂, φ)` with `s(φ) = π̂(L̂)` goes from `L̂` to `∑ σ_{(L, o)} · (Tφ(L), Tφ_*(o))`.  The
forgetful functor `f : Gr̂(X) → Gr(X)` is fibrewise 2-1 and sends
`σ_{(L,o)} (L, o) + σ_{(L,-o)} (L, -o)` to `(σ_{(L,o)} + σ_{(L,-o)}) · L`.

(Remark 9.3.1) An earlier notion of orientability (in a paper of the authors, with an erratum)
was too special; its techniques apply to the general approach of this section.

## What is formalized

* `MPolyfold.chartVec hφ α`: the chart vector of a tangent vector (gap G.7: `TX` carries no
  linear structure, so tangent vectors are compared through charts); `chartVec_injOn`,
  `exists_clm_chartVec` (chart changes act by continuous linear maps), `chartVec_tangentMapOn`.
* `MPolyfold.OrTangent` (dimension, underlying set `L`, positive frames), `chartFrames`,
  `IsChartOrientation` (the chart image of `L` is an `n`-dimensional subspace `N`, the frames
  are the positive ones for an orientation of `N`), `IsOrientedAt y` (in some chart at `y`);
  chart independence `IsOrientedAt.isChartOrientation` (orientations are carried by the linear
  isomorphism of the chart change), `isOrientedAt_iff_forall`, `exists_two_orientations`.
* Push-forward: `OrTangent.push`, `IsOrientedAt.push_tangentMapOn`, `isOrientedAt_push_tangentMor`.
* `EpGroupoid.GrHat x` (finitely supported `ℚ`-sums of oriented tangent sets over `x`),
  `grHatPush` (`_comp`, `_unit`), the category `GrHatObj`, `grHatProj`, the forgetful map
  `grForget` (`grForget_single_add_single`: `(L, o) + (L, -o) ↦ 2 · L`), the functor
  `grForgetFunctor` and the commutative square `grForgetFunctor_comp_grProj`.

## What the text leaves implicit, and the choices made

* An orientation of `L` is recorded by its set of positive frames `Fin n → TX` (in a chart: the
  bases of `N` of the given orientation, lifted to `L`) instead of a component of
  `Λ^max L ∖ {0}`; for `L = 0` the two orientations are `{∅-frame}` and `∅`.
* The weights of `Gr̂(x)` are in `ℚ`, as for `Gr(x)` in Chapter9/Tangent.lean.

## Not formalized, and why

* Remark 9.3.1: historical, no formal content.
-/

set_option maxSynthPendingDepth 3

open Set Module Submodule Filter Topology CategoryTheory

noncomputable section

namespace Polyfold

universe u

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}

/-- The chart vector `h` of `α` in the chart `φ`: `Tφ(α) = (φ(y), h)`. -/
def chartVec {φ : MChart X} (hφ : P.IsChart φ) (α : P.TangentSpace) : φ.model.E 0 :=
  (tangentChartMap hφ α).2

variable {φ : MChart X} (hφ : P.IsChart φ)

/-- The chart vector is injective on the fibre `T_yX`. -/
theorem chartVec_injOn {y : X} (hyφ : y ∈ φ.source) :
    InjOn (chartVec hφ) {α : P.TangentSpace | P.levelVal 1 (P.tangentProj α) = y} := by
  intro α hα β hβ h
  have hαφ : α ∈ tangentChartSet φ := by change _ ∈ φ.source; rw [hα]; exact hyφ
  have hβφ : β ∈ tangentChartSet φ := by change _ ∈ φ.source; rw [hβ]; exact hyφ
  refine tangentChartMap_injOn hφ hαφ hβφ (Prod.ext ?_ h)
  rw [tangentChartMap_fst hφ hαφ, tangentChartMap_fst hφ hβφ, show P.levelVal 1
    (P.tangentProj α) = y from hα, show P.levelVal 1 (P.tangentProj β) = y from hβ]

/-- Chart changes act on chart vectors by a continuous linear map. -/
theorem exists_clm_chartVec {ψ : MChart X} (hψ : P.IsChart ψ) {y : X}
    (hyφ : y ∈ φ.source) (hyψ : y ∈ ψ.source) :
    ∃ L : φ.model.E 0 →L[ℝ] ψ.model.E 0, ∀ α : P.TangentSpace,
      P.levelVal 1 (P.tangentProj α) = y → chartVec hψ α = L (chartVec hφ α) := by
  obtain ⟨R, hR⟩ := φ.isScRetract_overlap ψ
  have hf := (hφ.compatible hψ (P := P)).1
  refine ⟨scDeriv R.U (φ.transition ψ ∘ R) (levelLift φ 1 y), fun α hα => ?_⟩
  have hαφ : α ∈ tangentChartSet φ := by change _ ∈ φ.source; rw [hα]; exact hyφ
  have hmem := tangentChartMap_mem hφ hαφ
  have hfst : (tangentChartMap hφ α).1 = levelLift φ 1 y := by
    rw [tangentChartMap_fst hφ hαφ, hα]
  have hy1 : y ∈ P.levelSet 1 := hα ▸ (P.tangentProj α).2
  have hov : (tangentChartMap hφ α) ∈ retractTangent φ.model.E φ.model.C (φ.overlap ψ) := by
    have hsub : φ.source ∩ ψ.source ⊆ φ.source := inter_subset_left
    refine (TangentPre.mem_retractTangent_image_iff hsub (φ.isOpen_source.inter ψ.isOpen_source)
      ?_).2 hmem
    rw [hfst, P.toBase_levelLift hφ hyφ hy1]
    exact ⟨y, ⟨hyφ, hyψ⟩, rfl⟩
  have h1 := tangentChartMap_mk_ofVec_of_mem hφ hψ hmem hov
  rw [mk_ofVec_tangentChartMap hφ hαφ] at h1
  unfold chartVec
  rw [h1, retractTangentMap_apply hf R hR hov, hfst]

/-- **The chart `ψ ∘ f` carries the chart vectors of `Tf`**: for an sc-diffeomorphism
`f : U → U'` and a chart `ψ` around `f(y)`, the chart vector of `Tf(α)` in `ψ` is the chart vector
of `α` in the transported chart `ψ ∘ f` (`transportChart`). -/
theorem chartVec_tangentMapOn {f g : X → X} {U U' : Set X} (hf : P.IsScDiffeoOn P f g U U')
    {ψ : MChart X} (hψ : P.IsChart ψ) {α : P.TangentSpace}
    (hα : P.levelVal 1 (P.tangentProj α) ∈ U ∩ f ⁻¹' ψ.source) :
    chartVec hψ (tangentMapOn hf.isScSmoothOn α) = chartVec (transportChart_isChart hf hψ) α := by
  set χ := transportChart hf ψ with hχdef
  have hχ : P.IsChart χ := transportChart_isChart hf hψ
  have hdom : TangentPre.fdomOn U χ f ψ = χ.source := by
    ext x
    simp only [TangentPre.fdomOn, hχdef, transportChart_source, mem_inter_iff, mem_preimage]
    tauto
  have hαW : α ∈ P.tangentPreimage (TangentPre.fdomOn U χ f ψ) := by
    rw [hdom]; exact hα
  have h1 := tangentChartMap_tangentMapOn hf.isScSmoothOn hχ hψ hαW
  have hαχ : α ∈ tangentChartSet χ := hα
  have hO : IsScRetract χ.model.E χ.model.C (χ '' TangentPre.fdomOn U χ f ψ) :=
    χ.isScRetract_image (TangentPre.fdomOn_subset U χ f ψ)
      (TangentPre.isOpen_fdomOn hf.isScSmoothOn χ ψ)
  have heq : EqOn (ψ ∘ f ∘ χ.symm) id (χ '' TangentPre.fdomOn U χ f ψ) := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [Function.comp_apply, id]
    rw [χ.symm_apply_apply (TangentPre.fdomOn_subset U χ f ψ hx)]
    rfl
  have hmem : tangentChartMap hχ α ∈ retractTangent χ.model.E χ.model.C
      (χ '' TangentPre.fdomOn U χ f ψ) := by
    refine (TangentPre.mem_retractTangent_image_iff (TangentPre.fdomOn_subset U χ f ψ)
      (TangentPre.isOpen_fdomOn hf.isScSmoothOn χ ψ) ?_).2 (tangentChartMap_mem hχ hαχ)
    rw [tangentChartMap_fst hχ hαχ, P.toBase_levelLift hχ hαχ (levelVal_mem _)]
    exact ⟨_, hαW, rfl⟩
  unfold chartVec
  rw [h1]
  exact congrArg Prod.snd (retractTangentMap_id hO heq hmem)

/-! ### Oriented tangent sets -/

variable (P) in
/-- **An oriented tangent set** `L̂ = (L, o)`: a set `L ⊆ TX` (meant to be a finite-dimensional
linear subspace of a fibre `T_yX`), a dimension `n`, and the set `o` of its positively oriented
ordered frames `(α₁, …, αₙ) ∈ Lⁿ`. -/
structure OrTangent where
  /-- The dimension `n`. -/
  dim : ℕ
  /-- The underlying set `L`. -/
  carrier : Set P.TangentSpace
  /-- The positively oriented frames. -/
  frames : Set (Fin dim → P.TangentSpace)

/-- The frames of `L` which, read in the chart `φ`, are bases of the subspace `N` positively
oriented for `ω`. -/
def chartFrames (L : Set P.TangentSpace) (N : Submodule ℝ (φ.model.E 0)) {n : ℕ}
    (ω : Orientation ℝ N (Fin n)) : Set (Fin n → P.TangentSpace) :=
  {v | (∀ i, v i ∈ L) ∧ ∃ b : Basis (Fin n) ℝ N,
    (∀ i, (b i : φ.model.E 0) = chartVec hφ (v i)) ∧ b.orientation = ω}

/-- **An oriented tangent set in the chart `φ`**: the chart image of `L` is an
`n`-dimensional linear subspace `N` of `E₀`, and the frames are those positively oriented for an
orientation `ω` of `N`. -/
def IsChartOrientation (g : OrTangent P) : Prop :=
  ∃ N : Submodule ℝ (φ.model.E 0), (N : Set (φ.model.E 0)) = chartVec hφ '' g.carrier ∧
    FiniteDimensional ℝ N ∧ finrank ℝ N = g.dim ∧
    ∃ ω : Orientation ℝ N (Fin g.dim), g.frames = chartFrames hφ g.carrier N ω

variable (P) in
/-- **An oriented finite-dimensional linear subspace of `T_yX`** (2021 p. 422): `L` lies in the
fibre over `y` and, in some chart `φ` around `y`, is an oriented tangent set
(`IsChartOrientation`); it then is one in every chart (`IsOrientedAt.isChartOrientation`). -/
def IsOrientedAt (y : X) (g : OrTangent P) : Prop :=
  (∀ α ∈ g.carrier, P.levelVal 1 (P.tangentProj α) = y) ∧
    ∃ (φ : MChart X) (hφ : P.IsChart φ), y ∈ φ.source ∧ IsChartOrientation hφ g

omit hφ in
/-- **Chart independence**: an oriented tangent set over `y` is one in every chart around `y`;
the orientation is carried by the linear isomorphism `D(ψ ∘ φ⁻¹)` of the chart change. -/
theorem IsOrientedAt.isChartOrientation {y : X} {g : OrTangent P} (h : P.IsOrientedAt y g)
    {ψ : MChart X} (hψ : P.IsChart ψ) (hyψ : y ∈ ψ.source) : IsChartOrientation hψ g := by
  obtain ⟨hL, φ, hφ, hyφ, N, hN, hfin, hrank, ω, hO⟩ := h
  obtain ⟨Λ, hΛ⟩ := exists_clm_chartVec hφ hψ hyφ hyψ
  obtain ⟨Λ', hΛ'⟩ := exists_clm_chartVec hψ hφ hyψ hyφ
  set N' : Submodule ℝ (ψ.model.E 0) := N.map (Λ : φ.model.E 0 →ₗ[ℝ] ψ.model.E 0) with hN'def
  have hN' : (N' : Set (ψ.model.E 0)) = chartVec hψ '' g.carrier := by
    rw [hN'def, Submodule.map_coe, hN, image_image]
    exact (image_congr fun α hα => (hΛ α (hL α hα)).symm)
  have hmap : ∀ v ∈ N, (Λ : φ.model.E 0 →ₗ[ℝ] ψ.model.E 0) v ∈ N' := fun v hv =>
    Submodule.mem_map_of_mem hv
  have hmap' : ∀ w ∈ N', (Λ' : ψ.model.E 0 →ₗ[ℝ] φ.model.E 0) w ∈ N := by
    intro w hw
    rw [← SetLike.mem_coe, hN'] at hw
    obtain ⟨α, hα, rfl⟩ := hw
    rw [← SetLike.mem_coe, hN]
    exact ⟨α, hα, hΛ' α (hL α hα)⟩
  have hinv : ∀ v ∈ N, Λ' (Λ v) = v := by
    intro v hv
    rw [← SetLike.mem_coe, hN] at hv
    obtain ⟨α, hα, rfl⟩ := hv
    rw [← hΛ α (hL α hα), ← hΛ' α (hL α hα)]
  have hinv' : ∀ w ∈ N', Λ (Λ' w) = w := by
    intro w hw
    rw [← SetLike.mem_coe, hN'] at hw
    obtain ⟨α, hα, rfl⟩ := hw
    rw [← hΛ' α (hL α hα), ← hΛ α (hL α hα)]
  let e : N ≃ₗ[ℝ] N' := LinearEquiv.ofLinearMap
    ((Λ : φ.model.E 0 →ₗ[ℝ] ψ.model.E 0).restrict hmap)
    ((Λ' : ψ.model.E 0 →ₗ[ℝ] φ.model.E 0).restrict hmap')
    (LinearMap.ext fun w => Subtype.ext (hinv' w w.2))
    (LinearMap.ext fun v => Subtype.ext (hinv v v.2))
  have he : ∀ v : N, ((e v : N') : ψ.model.E 0) = Λ v := fun v => rfl
  have he' : ∀ w : N', ((e.symm w : N) : φ.model.E 0) = Λ' w := fun w => rfl
  refine ⟨N', hN', LinearEquiv.finiteDimensional e, by rw [← hrank]; exact e.finrank_eq.symm,
    Orientation.map (Fin g.dim) e ω, ?_⟩
  rw [hO]
  ext v
  constructor
  · rintro ⟨hv, b, hb, hbo⟩
    refine ⟨hv, b.map e, fun i => ?_, ?_⟩
    · rw [Basis.map_apply, he, hb i, ← hΛ _ (hL _ (hv i))]
    · rw [Basis.orientation_map, hbo]
  · rintro ⟨hv, b, hb, hbo⟩
    refine ⟨hv, b.map e.symm, fun i => ?_, ?_⟩
    · rw [Basis.map_apply, he', hb i, ← hΛ' _ (hL _ (hv i))]
    · rw [Basis.orientation_map, hbo, ← Orientation.map_symm, Equiv.symm_apply_apply]

omit hφ in
/-- An oriented tangent set over `y` is oriented in every chart around `y`, and conversely. -/
theorem isOrientedAt_iff_forall {y : X} {g : OrTangent P} :
    P.IsOrientedAt y g ↔ (∀ α ∈ g.carrier, P.levelVal 1 (P.tangentProj α) = y) ∧
      ∀ (ψ : MChart X) (hψ : P.IsChart ψ), y ∈ ψ.source → IsChartOrientation hψ g := by
  refine ⟨fun h => ⟨h.1, fun ψ hψ hyψ => h.isChartOrientation hψ hyψ⟩, fun h => ?_⟩
  obtain ⟨φ, hφ, hyφ⟩ := P.exists_isChart_mem_source y
  exact ⟨h.1, φ, hφ, hyφ, h.2 φ hφ hyφ⟩

/-- The frames of an oriented tangent set lie in its carrier. -/
theorem IsOrientedAt.mem_carrier {y : X} {g : OrTangent P} (h : P.IsOrientedAt y g)
    {v : Fin g.dim → P.TangentSpace} (hv : v ∈ g.frames) (i : Fin g.dim) : v i ∈ g.carrier := by
  obtain ⟨-, φ, hφ, -, N, -, -, -, ω, hO⟩ := h
  rw [hO] at hv
  exact hv.1 i

omit hφ in
theorem IsOrientedAt.levelSet {y : X} {g : OrTangent P} (h : P.IsOrientedAt y g) :
    y ∈ P.levelSet 1 := by
  obtain ⟨hL, φ, hφ, hyφ, N, hN, -⟩ := h
  have h0 : (0 : φ.model.E 0) ∈ (N : Set (φ.model.E 0)) := N.zero_mem
  rw [hN] at h0
  obtain ⟨α, hα, -⟩ := h0
  rw [← hL α hα]
  exact levelVal_mem _

/-- **The two orientations of a linear tangent set** (2021 p. 422: an orientation is a choice of
a component of `Λ^max L ∖ {0}`; for `L = 0`, `Λ^max L = ℝ`): if the chart image of `L ⊆ T_yX`
is an `n`-dimensional linear subspace, `L` has exactly two orientations, and they differ.  For
`n = 0` they are "every (empty) frame is positive" and "no frame is positive". -/
theorem exists_two_orientations {y : X} (hyφ : y ∈ φ.source) {L : Set P.TangentSpace}
    (hL : ∀ α ∈ L, P.levelVal 1 (P.tangentProj α) = y) {N : Submodule ℝ (φ.model.E 0)}
    (hN : (N : Set (φ.model.E 0)) = chartVec hφ '' L) [FiniteDimensional ℝ N] {n : ℕ}
    (hn : finrank ℝ N = n) :
    ∃ O₁ O₂ : Set (Fin n → P.TangentSpace), O₁ ≠ O₂ ∧
      ∀ O, P.IsOrientedAt y ⟨n, L, O⟩ ↔ O = O₁ ∨ O = O₂ := by
  let b₀ : Basis (Fin n) ℝ N := Module.finBasisOfFinrankEq ℝ N hn
  refine ⟨chartFrames hφ L N b₀.orientation, chartFrames hφ L N (-b₀.orientation), ?_, ?_⟩
  · have hlift : ∀ i, ∃ α ∈ L, chartVec hφ α = b₀ i := fun i => by
      have : (b₀ i : φ.model.E 0) ∈ (N : Set (φ.model.E 0)) := (b₀ i).2
      rw [hN] at this
      exact this
    choose v hvL hv using hlift
    intro heq
    have h1 : v ∈ chartFrames hφ L N b₀.orientation := ⟨hvL, b₀, fun i => (hv i).symm, rfl⟩
    rw [heq] at h1
    obtain ⟨-, b, hb, hbo⟩ := h1
    have hbb : b = b₀ := Basis.eq_of_apply_eq fun i => Subtype.ext ((hb i).trans (hv i))
    rw [hbb] at hbo
    exact Module.Ray.ne_neg_self _ hbo
  · intro O
    constructor
    · intro hO
      obtain ⟨N', hN', -, -, ω, hOω⟩ := hO.isChartOrientation hφ hyφ
      have hNN : N' = N := SetLike.coe_injective (hN'.trans hN.symm)
      subst hNN
      change O = chartFrames hφ L N' ω at hOω
      rcases b₀.orientation_eq_or_eq_neg ω with h | h
      · left; rw [hOω, h]
      · right; rw [hOω, h]
    · rintro (rfl | rfl)
      · exact ⟨hL, φ, hφ, hyφ, N, hN, inferInstance, hn, b₀.orientation, rfl⟩
      · exact ⟨hL, φ, hφ, hyφ, N, hN, inferInstance, hn, -b₀.orientation, rfl⟩

/-! ### Images of oriented tangent sets -/

/-- The image `(Tf(L), Tf_*(o))` of an oriented tangent set under `f : TX → TX`: the image
of `L` and the images of the positive frames. -/
def OrTangent.push (f : P.TangentSpace → P.TangentSpace) (g : OrTangent P) : OrTangent P :=
  ⟨g.dim, f '' g.carrier, (fun v => f ∘ v) '' g.frames⟩

@[simp] theorem OrTangent.push_dim (f : P.TangentSpace → P.TangentSpace) (g : OrTangent P) :
    (g.push f).dim = g.dim := rfl

@[simp] theorem OrTangent.push_carrier (f : P.TangentSpace → P.TangentSpace) (g : OrTangent P) :
    (g.push f).carrier = f '' g.carrier := rfl

theorem OrTangent.push_push (f f' : P.TangentSpace → P.TangentSpace) (g : OrTangent P) :
    (g.push f).push f' = g.push (f' ∘ f) := by
  simp only [OrTangent.push, image_image]
  rfl

theorem OrTangent.push_id (g : OrTangent P) : g.push id = g := by
  obtain ⟨n, L, O⟩ := g
  simp only [OrTangent.push, image_id, Function.id_comp, image_id']

theorem OrTangent.push_congr {f f' : P.TangentSpace → P.TangentSpace} {g : OrTangent P}
    (h : ∀ α ∈ g.carrier, f α = f' α) (hfr : ∀ v ∈ g.frames, ∀ i, v i ∈ g.carrier) :
    g.push f = g.push f' := by
  simp only [OrTangent.push]
  congr 1
  · exact image_congr h
  · exact image_congr fun v hv => funext fun i => h _ (hfr v hv i)

omit hφ in
/-- **Oriented tangent sets are carried by sc-diffeomorphisms**: for `f : U → U'` an
sc-diffeomorphism and `y ∈ U`, `Tf` maps an oriented tangent set over `y` to one over `f(y)`
(read in a chart `ψ` around `f(y)` and in the transported chart `ψ ∘ f` around `y`, the two
have the same chart vectors). -/
theorem IsOrientedAt.push_tangentMapOn {f f' : X → X} {U U' : Set X}
    (hf : P.IsScDiffeoOn P f f' U U') {y : X} (hyU : y ∈ U) {g : OrTangent P}
    (h : P.IsOrientedAt y g) :
    P.IsOrientedAt (f y) (g.push (tangentMapOn hf.isScSmoothOn)) := by
  have hL := h.1
  obtain ⟨ψ, hψ, hyψ⟩ := P.exists_isChart_mem_source (f y)
  have hχ := transportChart_isChart hf hψ
  have hyχ : y ∈ (transportChart hf ψ).source := ⟨hyU, hyψ⟩
  obtain ⟨N, hN, hfin, hrank, ω, hO⟩ := h.isChartOrientation hχ hyχ
  have hcv : ∀ α ∈ g.carrier, chartVec hψ (tangentMapOn hf.isScSmoothOn α) = chartVec hχ α :=
    fun α hα => chartVec_tangentMapOn hf hψ (by rw [hL α hα]; exact hyχ)
  refine ⟨?_, ψ, hψ, hyψ, N, ?_, hfin, hrank, ω, ?_⟩
  · rintro _ ⟨α, hα, rfl⟩
    rw [levelVal_tangentProj_tangentMapOn hf.isScSmoothOn
      (show α ∈ P.tangentPreimage U from by change _ ∈ U; rw [hL α hα]; exact hyU), hL α hα]
  · refine hN.trans ?_
    rw [OrTangent.push_carrier, image_image]
    exact image_congr fun α hα => (hcv α hα).symm
  · change (fun v => tangentMapOn hf.isScSmoothOn ∘ v) '' g.frames =
      chartFrames hψ (tangentMapOn hf.isScSmoothOn '' g.carrier) N ω
    rw [hO]
    ext w
    constructor
    · rintro ⟨v, ⟨hv, b, hb, hbo⟩, rfl⟩
      exact ⟨fun i => mem_image_of_mem _ (hv i), b, fun i => (hb i).trans (hcv _ (hv i)).symm,
        hbo⟩
    · rintro ⟨hw, b, hb, hbo⟩
      choose u hu hfu using hw
      refine ⟨u, ⟨hu, b, fun i => (hb i).trans ?_, hbo⟩, funext hfu⟩
      rw [← hfu i]
      exact hcv _ (hu i)

end MPolyfold

/-! ### `Gr̂(x)`, `Gr̂(X)` and the forgetful functor (2021 p. 422) -/

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

/-- **`Tφ` maps oriented tangent sets over `s(φ)` to oriented tangent sets over `t(φ)`**
(`Tφ = Tφ̂` on `T_{s φ}X`, and `φ̂` is an sc-diffeomorphism). -/
theorem isOrientedAt_push_tangentMor {φ : Mor} {g : X.PObj.OrTangent}
    (h : X.PObj.IsOrientedAt (X.src φ) g) :
    X.PObj.IsOrientedAt (X.tgt φ) (g.push (X.tangentMor φ)) := by
  have hφ1 : φ ∈ X.PMor.levelSet 1 := (X.mem_levelSet_src_iff φ 1).1 h.levelSet
  have heq : g.push (X.tangentMor φ) =
      g.push (MPolyfold.tangentMapOn (X.isScDiffeoOn_hat φ).isScSmoothOn) :=
    MPolyfold.OrTangent.push_congr (fun α hα => X.tangentMor_eq_tangentMapOn_hat hφ1 (h.1 α hα))
      fun v hv i => h.mem_carrier hv i
  rw [heq, ← X.hat_src φ]
  exact h.push_tangentMapOn (X.isScDiffeoOn_hat φ) (X.src_mem_sheetAt φ)

variable (X) in
/-- **`Gr̂(x)`** (2021 p. 422): the finite formal sums `∑ σ_{L̂} · L̂`, `σ_{L̂} ∈ ℚ`,
`σ_{L̂} ≥ 0`, of oriented finite-dimensional linear subspaces `L̂ = (L, o)` of `T_xX`. -/
def GrHat (x : Obj) : Set (X.PObj.OrTangent →₀ ℚ) :=
  {w | (∀ g, 0 ≤ w g) ∧ ∀ g ∈ w.support, X.PObj.IsOrientedAt x g}

theorem zero_mem_GrHat (x : Obj) : (0 : X.PObj.OrTangent →₀ ℚ) ∈ X.GrHat x :=
  ⟨fun _ => le_rfl, fun g hg => by simp at hg⟩

variable (X) in
/-- The target `t(L̂, φ) = ∑ σ_{(L, o)} · (Tφ(L), Tφ_*(o))` of a morphism of `Gr̂(X)`. -/
def grHatPush (φ : Mor) (w : X.PObj.OrTangent →₀ ℚ) : X.PObj.OrTangent →₀ ℚ :=
  w.mapDomain (MPolyfold.OrTangent.push (X.tangentMor φ))

theorem grHatPush_mem {φ : Mor} {w : X.PObj.OrTangent →₀ ℚ} (hw : w ∈ X.GrHat (X.src φ)) :
    X.grHatPush φ w ∈ X.GrHat (X.tgt φ) := by
  classical
  refine ⟨fun g => ?_, fun g hg => ?_⟩
  · rw [grHatPush, Finsupp.mapDomain, Finsupp.sum_apply]
    refine Finset.sum_nonneg fun g' _ => ?_
    dsimp only
    rw [Finsupp.single_apply]
    split_ifs
    · exact hw.1 g'
    · exact le_rfl
  · obtain ⟨g', hg', rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hg)
    exact isOrientedAt_push_tangentMor (hw.2 g' hg')

theorem grHatPush_comp {φ ψ : Mor} (hψφ : X.src ψ = X.tgt φ) {w : X.PObj.OrTangent →₀ ℚ}
    (hw : w ∈ X.GrHat (X.src φ)) :
    X.grHatPush (X.comp ψ φ) w = X.grHatPush ψ (X.grHatPush φ w) := by
  rw [grHatPush, grHatPush, grHatPush, ← Finsupp.mapDomain_comp]
  refine Finsupp.mapDomain_congr fun g hg => ?_
  have hg' := hw.2 g hg
  have hφ1 : φ ∈ X.PMor.levelSet 1 := (X.mem_levelSet_src_iff φ 1).1 hg'.levelSet
  rw [Function.comp_apply, MPolyfold.OrTangent.push_push]
  exact MPolyfold.OrTangent.push_congr (fun α hα => X.tangentMor_comp hφ1 hψφ (hg'.1 α hα))
    fun v hv i => hg'.mem_carrier hv i

theorem grHatPush_unit {x : Obj} {w : X.PObj.OrTangent →₀ ℚ} (hw : w ∈ X.GrHat x) :
    X.grHatPush (X.unit x) w = w := by
  rw [grHatPush]
  conv_rhs => rw [← Finsupp.mapDomain_id (v := w)]
  refine Finsupp.mapDomain_congr fun g hg => ?_
  have hg' := hw.2 g hg
  have h1 : g.push (X.tangentMor (X.unit x)) = g.push id :=
    MPolyfold.OrTangent.push_congr (fun α hα => X.tangentMor_unit_of_eq (hg'.1 α hα))
      fun v hv i => hg'.mem_carrier hv i
  rw [h1, MPolyfold.OrTangent.push_id]
  rfl

variable (X) in
/-- **An object of `Gr̂(X) = ⋃_{x ∈ X_∞} Gr̂(x)`** (2021 p. 422). -/
structure GrHatObj where
  /-- The base point `π̂(L̂) = x`. -/
  pt : Obj
  smooth : pt ∈ X.PObj.smoothSet
  /-- The formal sum `L̂ = ∑ σ_{L̂} · L̂`. -/
  sum : X.PObj.OrTangent →₀ ℚ
  mem : sum ∈ X.GrHat pt

/-- **The category `Gr̂(X)`** (2021 p. 422): a morphism `(L̂, φ)` with `s(φ) = π̂(L̂)` goes from
`L̂` to `t(L̂, φ) = ∑ σ_{(L, o)} · (Tφ(L), Tφ_*(o))`. -/
instance : Category.{u} X.GrHatObj where
  Hom a b := {φ : Mor // X.src φ = a.pt ∧ X.tgt φ = b.pt ∧ X.grHatPush φ a.sum = b.sum}
  id a := ⟨X.unit a.pt, X.src_unit _, X.tgt_unit _, X.grHatPush_unit a.mem⟩
  comp {a b c} f g := ⟨X.comp g.1 f.1,
    (X.src_comp _ _ (g.2.1.trans f.2.2.1.symm)).trans f.2.1,
    (X.tgt_comp _ _ (g.2.1.trans f.2.2.1.symm)).trans g.2.2.1, by
      have hw : a.sum ∈ X.GrHat (X.src f.1) := by rw [f.2.1]; exact a.mem
      rw [X.grHatPush_comp (g.2.1.trans f.2.2.1.symm) hw, f.2.2.2, g.2.2.2]⟩
  id_comp f := Subtype.ext (GroupoidStr.comp_unit_of_eq (G := X.toGroupoidStr) f.2.1)
  comp_id f := Subtype.ext (GroupoidStr.unit_comp_of_eq (G := X.toGroupoidStr) f.2.2.1)
  assoc f g h := Subtype.ext (X.comp_assoc _ _ _ (h.2.1.trans g.2.2.1.symm)
    (g.2.1.trans f.2.2.1.symm)).symm

variable (X) in
/-- **The projection functor `π̂ : Gr̂(X) → X_∞`**. -/
def grHatProj : X.GrHatObj ⥤ X.SmoothCat where
  obj a := (⟨a.pt, a.smooth⟩ : X.PObj.smoothSet)
  map {a b} f := ⟨⟨f.1, by rw [f.2.1]; exact a.smooth, by rw [f.2.2.1]; exact b.smooth⟩,
    Subtype.ext f.2.1, Subtype.ext f.2.2.1⟩
  map_id _ := rfl
  map_comp {a b c} f g := by
    apply Subtype.ext
    apply Subtype.ext
    have h : X.src g.1 = X.tgt f.1 := g.2.1.trans f.2.2.1.symm
    change X.comp g.1 f.1 = ((X.toGroupoidStr.fullSub X.PObj.smoothSet).comp _ _).1
    simp only [GroupoidStr.fullSub, dif_pos h]

variable (X) in
/-- **The forgetful map `f : Gr̂(x) → Gr(x)`** (2021 p. 422): `(L, o) ↦ L`, extended linearly;
`σ_{(L,o)} · (L, o) + σ_{(L,−o)} · (L, −o) ↦ (σ_{(L,o)} + σ_{(L,−o)}) · L`. -/
def grForget (w : X.PObj.OrTangent →₀ ℚ) : Set X.PObj.TangentSpace →₀ ℚ :=
  w.mapDomain MPolyfold.OrTangent.carrier

theorem grForget_mem {x : Obj} {w : X.PObj.OrTangent →₀ ℚ} (hw : w ∈ X.GrHat x) :
    X.grForget w ∈ X.Gr x := by
  classical
  refine ⟨fun L => ?_, fun L hL α hα => ?_⟩
  · rw [grForget, Finsupp.mapDomain, Finsupp.sum_apply]
    refine Finset.sum_nonneg fun g' _ => ?_
    dsimp only
    rw [Finsupp.single_apply]
    split_ifs
    · exact hw.1 g'
    · exact le_rfl
  · obtain ⟨g', hg', rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hL)
    exact (hw.2 g' hg').1 α hα

theorem grForget_single (g : X.PObj.OrTangent) (c : ℚ) :
    X.grForget (Finsupp.single g c) = Finsupp.single g.carrier c :=
  Finsupp.mapDomain_single

/-- `σ · (L, o) + σ' · (L, o') ↦ (σ + σ') · L`. -/
theorem grForget_single_add_single {g g' : X.PObj.OrTangent} (h : g.carrier = g'.carrier)
    (c c' : ℚ) :
    X.grForget (Finsupp.single g c + Finsupp.single g' c') = Finsupp.single g.carrier (c + c') := by
  rw [grForget, Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.mapDomain_single, ← h,
    Finsupp.single_add]

/-- The forgetful map commutes with the targets of morphisms. -/
theorem grForget_grHatPush (φ : Mor) (w : X.PObj.OrTangent →₀ ℚ) :
    X.grForget (X.grHatPush φ w) = X.grPush φ (X.grForget w) := by
  rw [grForget, grHatPush, grForget, grPush, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  rfl

/-- A formal sum with nonnegative weights and zero image is zero. -/
theorem eq_zero_of_grForget_eq_zero {w : X.PObj.OrTangent →₀ ℚ} (hw : ∀ g, 0 ≤ w g)
    (h : X.grForget w = 0) : w = 0 := by
  classical
  have hnn : ∀ g' (L : Set X.PObj.TangentSpace), 0 ≤ (Finsupp.single g'.carrier (w g')) L :=
    fun g' L => by rw [Finsupp.single_apply]; split_ifs; exacts [hw g', le_rfl]
  ext g
  have key : w g ≤ (X.grForget w) g.carrier := by
    rw [grForget, Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
    by_cases hg : g ∈ w.support
    · calc w g = (Finsupp.single g.carrier (w g)) g.carrier := by rw [Finsupp.single_eq_same]
        _ ≤ _ := Finset.single_le_sum (f := fun g' => (Finsupp.single g'.carrier (w g')) g.carrier)
          (fun g' _ => hnn g' _) hg
    · rw [Finsupp.notMem_support_iff.1 hg]
      exact Finset.sum_nonneg fun g' _ => hnn g' _
  rw [h, Finsupp.coe_zero, Pi.zero_apply] at key
  exact le_antisymm key (hw g)

variable (X) in
/-- **The forgetful functor `f : Gr̂(X) → Gr(X)`** (2021 p. 422), fibrewise over `X_∞`:
`(x, L̂) ↦ (x, f(L̂))`, `(L̂, φ) ↦ (f(L̂), φ)`. -/
def grForgetFunctor : X.GrHatObj ⥤ X.GrObj where
  obj a := ⟨a.pt, a.smooth, X.grForget a.sum, grForget_mem a.mem⟩
  map {a b} f := ⟨f.1, f.2.1, f.2.2.1, by
    change X.grPush f.1 (X.grForget a.sum) = X.grForget b.sum
    rw [← grForget_grHatPush, f.2.2.2]⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **The square of p. 422 commutes**: `π ∘ f = π̂`. -/
theorem grForgetFunctor_comp_grProj : X.grForgetFunctor ⋙ X.grProj = X.grHatProj := rfl

end EpGroupoid

end Polyfold
