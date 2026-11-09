import Polyfold.Chapter6.LocalDetBundle
import Polyfold.Chapter6.LineBundleOrientation
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.VectorBundle.Constructions
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.4–6.5,
pp. 217–219: **Definition 6.5.6 (preprint 6.22)** (the basis `𝓑`), **Proposition 6.5.7 (preprint 6.23)** (`𝓑` is a basis of a
topology), **Proposition 6.5.8 (preprint 6.24)** (`DET(E,F)` is a topological line bundle), **Lemma 6.5.9 (preprint 6.25)** (the
transition maps are continuous) and **Proposition 6.6.1 (preprint 6.26)** (a line bundle over a convex set of
Fredholm operators, with exactly two orientations) *(book 2017: Definition 6.8, Propositions
6.9–6.10, Lemma 6.11, Proposition 6.11; see `BookConcordance.md`)*.

# The determinant line bundle over the Fredholm operators

## The text, paraphrased

`DET(E,F) = ⋃_{S ∈ F(E,F)} {S} × det(S)` over the space `F(E,F)` of Fredholm operators.  For `T`
Fredholm, Proposition 6.5.4 (preprint 6.20) gives `ε > 0` and `P ∈ Π_T` with the bijection
`γ_(T,P,ε) : DET(E,F)|{‖S − T‖ < ε} → DET(T, P, ε)`, `(S, h) ↦ (S, γ^P_S(h))`, fibrewise linear
over the identity.  (Definition 6.5.6 (preprint 6.22)) `𝓑` is the collection of subsets `B` of `DET(E,F)` with
`γ_(T,P,ε)(B)` open in `DET(T, P, ε)` for some `γ_(T,P,ε)`.  (Proposition 6.5.7 (preprint 6.23)) `𝓑` is a basis of a
topology `𝒯`.  (Proposition 6.5.8 (preprint 6.24)) `DET(E,F)` with the linear structure of its fibres and `𝒯` is a
topological line bundle, and the `γ_(T,P,ε)` are topological bundle isomorphisms.  (Lemma 6.5.9 (preprint 6.25)) The
transition maps `γ_(T',P',ε') ∘ γ_(T,P,ε)⁻¹` are topological isomorphisms: near `S₀` take
`Q ≤ P, P'`; by Corollary 6.4.12 (preprint 6.13) the transition is `(S, h) ↦ (S, (γ^Q_{P'S})⁻¹ γ^Q_{PS}(h))`,
continuous by Lemma 6.5.5 (preprint 6.21).  (Proposition 6.6.1 (preprint 6.26)) For the convex set `Lin(f, x)` of Fredholm operators,
`DET(f, x) = ⋃_{L ∈ Lin(f,x)} {L} × det(L)` is in a natural way a topological line bundle and has
two orientations, the base being contractible.

## What is formalized

* `Polyfold.DetFiber S = det(S)` over `S ∈ FredholmOp E F`, with the topology of a
  finite-dimensional space (`moduleTopology`).
* `LocalDetChart.pretriv c`: `γ_(T,P,ε)` read in the frame of `DET(T, P, ε)` (Proposition 6.5.4 (preprint 6.20)), as
  a pretrivialization `(S, h) ↦ (S, ω(S)*(γ^P_S h))` with model fibre `ℝ`.
* **Lemma 6.5.9 (preprint 6.25)** (`lemma_6_5_9`): the transition `(S, t) ↦ (S, g(S) t)` between two charts has `g`
  continuous and nowhere zero on the common ball.
* `Polyfold.detPrebundle`: Mathlib's `VectorPrebundle` built from all the `γ_(T,P,ε)`; the topology
  of `DET(E,F)` and its `FiberBundle` and `VectorBundle` instances are the ones Mathlib derives.
* **Definition 6.5.6 (preprint 6.22)** (`detBasis`) and **Proposition 6.5.7 (preprint 6.23)** (`proposition_6_5_7`): `𝓑` is a basis of
  the topology of `DET(E,F)` (so the topology `𝒯` it generates is this one).
* **Proposition 6.5.8 (preprint 6.24)** (`proposition_6_5_8`): `DET(E,F)` is a topological vector bundle with model
  fibre `ℝ`, and every `γ_(T,P,ε)` (in frames) is a trivialization of it.
* `Polyfold.DetOn C hC`: the restriction (pull-back) of `DET(E,F)` to a set `C` of Fredholm
  operators; **Proposition 6.6.1 (preprint 6.26)** (`proposition_6_6_1`): over a nonempty convex `C` it is a
  topological line bundle with exactly two orientations.

## Reading

`DET(T, P, ε)` carries the topology of the trivial bundle given by its frame `ω` (Proposition
6.20); a set is in `𝓑` if it lies over the ball of some chart and its image in `ball × ℝ` is open.
Proposition 6.5.7 (preprint 6.23) is stated for the topology of the prebundle; by
`IsTopologicalBasis.eq_generateFrom` it says that `𝓑` generates it.  Proposition 6.6.1 (preprint 6.26) is stated
for any nonempty convex set of Fredholm operators; `Lin(f, x)` is one (`LinSet.lean`).  Its
"contractible" is used through `exists_two_lineOrientation` (`LineBundleOrientation.lean`).
-/

open Module TensorProduct Bundle Topology Set

noncomputable section

namespace Polyfold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The fibre `det(S)` of `DET(E, F)` over a Fredholm operator `S`. -/
def DetFiber (S : FredholmOp E F) : Type _ := fredholmDet S.1

instance (S : FredholmOp E F) : AddCommMonoid (DetFiber S) :=
  inferInstanceAs (AddCommMonoid (fredholmDet S.1))

instance (S : FredholmOp E F) : Module ℝ (DetFiber S) :=
  inferInstanceAs (Module ℝ (fredholmDet S.1))

/-- The fibre `det(S)` carries the topology of a finite-dimensional real vector space. -/
instance (S : FredholmOp E F) : TopologicalSpace (DetFiber S) := moduleTopology ℝ _

instance (S : FredholmOp E F) : IsModuleTopology ℝ (DetFiber S) := ⟨rfl⟩

omit [CompleteSpace E] [CompleteSpace F] in
/-- `det(S)` is a line. -/
theorem finrank_detFiber (S : FredholmOp E F) : finrank ℝ (DetFiber S) = 1 :=
  finrank_fredholmDet S.2

namespace LocalDetChart

variable (c : LocalDetChart E F)

/-- The Fredholm operators in the ball `‖S − T‖ < ε` of the chart. -/
def baseSet : Set (FredholmOp E F) := {S | ‖S.1 - c.T‖ < c.ε}

omit [CompleteSpace E] [CompleteSpace F] in
theorem isOpen_baseSet : IsOpen c.baseSet :=
  isOpen_lt (continuous_subtype_val.sub continuous_const).norm continuous_const

/-- The coordinate `det(S) → ℝ`, `h ↦ ω(S)*(γ^P_S h)`: the coefficient of `γ^P_S(h)` in the frame
`ω(S)` of `DET(T, P, ε)` (and `0` off the ball). -/
def coord (S : FredholmOp E F) : DetFiber S →ₗ[ℝ] ℝ :=
  if hS : ‖S.1 - c.T‖ < c.ε then
    dualVec (c.frame S.1 hS) ∘ₗ (gammaProj S.2 (c.isGoodLeftProj_of_lt S.1 hS)).toLinearMap
  else 0

/-- The inverse coordinate `ℝ → det(S)`, `t ↦ (γ^P_S)⁻¹(t ω(S))` (and `0` off the ball). -/
def coordInv (S : FredholmOp E F) : ℝ →ₗ[ℝ] DetFiber S :=
  if hS : ‖S.1 - c.T‖ < c.ε then
    (gammaProj S.2 (c.isGoodLeftProj_of_lt S.1 hS)).symm.toLinearMap ∘ₗ
      LinearMap.toSpanSingleton ℝ _ (c.frame S.1 hS)
  else 0

/-- The coordinate on the ball: `h ↦ ω(S)*(γ^P_S h)`. -/
theorem coord_apply {S : FredholmOp E F} (hS : ‖S.1 - c.T‖ < c.ε) (h : DetFiber S) :
    c.coord S h =
      dualVec (c.frame S.1 hS) (gammaProj S.2 (c.isGoodLeftProj_of_lt S.1 hS) h) := by
  rw [coord, dif_pos hS]; rfl

/-- The inverse coordinate on the ball: `t ↦ (γ^P_S)⁻¹(t ω(S))`. -/
theorem coordInv_apply {S : FredholmOp E F} (hS : ‖S.1 - c.T‖ < c.ε) (t : ℝ) :
    c.coordInv S t = (gammaProj S.2 (c.isGoodLeftProj_of_lt S.1 hS)).symm (t • c.frame S.1 hS) := by
  rw [coordInv, dif_pos hS]; rfl

theorem coordInv_coord {S : FredholmOp E F} (hS : S ∈ c.baseSet) (h : DetFiber S) :
    c.coordInv S (c.coord S h) = h := by
  have hS' : ‖S.1 - c.T‖ < c.ε := hS
  have h1 := finrank_fredholmDet ((c.isGoodLeftProj_of_lt S.1 hS').isFredholm_comp S.2)
  rw [c.coord_apply hS', c.coordInv_apply hS', dualVec_apply_smul h1 (c.frame_ne_zero S.1 hS')]
  exact LinearEquiv.symm_apply_apply _ (show fredholmDet S.1 from h)

theorem coord_coordInv {S : FredholmOp E F} (hS : S ∈ c.baseSet) (t : ℝ) :
    c.coord S (c.coordInv S t) = t := by
  have hS' : ‖S.1 - c.T‖ < c.ε := hS
  have h1 := finrank_fredholmDet ((c.isGoodLeftProj_of_lt S.1 hS').isFredholm_comp S.2)
  rw [c.coord_apply hS', c.coordInv_apply hS', LinearEquiv.apply_symm_apply, map_smul,
    dualVec_self h1 (c.frame_ne_zero S.1 hS'), smul_eq_mul, mul_one]

/-- **`γ_(T,P,ε)` in the frame of `DET(T, P, ε)`**: the pretrivialization
`(S, h) ↦ (S, ω(S)*(γ^P_S h))` of `DET(E,F)` over the ball, with model fibre `ℝ`. -/
def pretriv : Pretrivialization ℝ (π ℝ (DetFiber (E := E) (F := F))) where
  toFun x := (x.1, c.coord x.1 x.2)
  invFun p := ⟨p.1, c.coordInv p.1 p.2⟩
  source := TotalSpace.proj ⁻¹' c.baseSet
  target := c.baseSet ×ˢ univ
  map_source' _ hx := ⟨hx, mem_univ _⟩
  map_target' _ hp := hp.1
  left_inv' x hx := by
    obtain ⟨S, h⟩ := x
    exact congrArg (TotalSpace.mk S) (c.coordInv_coord hx h)
  right_inv' p hp := Prod.ext rfl (c.coord_coordInv hp.1 p.2)
  open_target := c.isOpen_baseSet.prod isOpen_univ
  baseSet := c.baseSet
  open_baseSet := c.isOpen_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

@[simp] theorem pretriv_apply (x : TotalSpace ℝ (DetFiber (E := E) (F := F))) :
    c.pretriv x = (x.1, c.coord x.1 x.2) := rfl

@[simp] theorem pretriv_baseSet : c.pretriv.baseSet = c.baseSet := rfl

theorem pretriv_isLinear : c.pretriv.IsLinear ℝ :=
  ⟨fun S _ => (c.coord S).isLinear⟩

end LocalDetChart

/-- A local determinant chart centred at a Fredholm operator `T` with any given good
left-projection `P ∈ Π_T` (Lemma 6.5.1 (preprint 6.17) with a topological complement of the finite-dimensional
`ker(P T)`). -/
theorem exists_localDetChart_of_proj {T : E →L[ℝ] F} (hT : T.IsFredholm) {P : F →L[ℝ] F}
    (hP : IsGoodLeftProj T P) : ∃ c : LocalDetChart E F, c.T = T ∧ c.P = P := by
  have := (hP.isFredholm_comp hT).finite_ker
  obtain ⟨Y, hY⟩ := (Submodule.ClosedComplemented.of_finiteDimensional
    (LinearMap.ker ((P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F))).exists_isTopCompl
  obtain ⟨ε, hε, h⟩ := lemma_6_5_1 hP hY
  exact ⟨⟨T, hT, P, hP, Y, hY, ε, hε, fun S hS => (h S hS).1, fun S hS => (h S hS).2⟩, rfl, rfl⟩

/-- Every Fredholm operator `T` is the centre of a local determinant chart (Lemma 6.5.1 (preprint 6.17) with a good
left-projection `P ∈ Π_T` and a topological complement of the finite-dimensional `ker(P T)`). -/
theorem exists_localDetChart (T : FredholmOp E F) : ∃ c : LocalDetChart E F, c.T = T.1 := by
  obtain ⟨P, hP⟩ := exists_isGoodLeftProj T.2
  obtain ⟨c, hc, -⟩ := exists_localDetChart_of_proj T.2 hP
  exact ⟨c, hc⟩

/-- A chart centred at `T`. -/
def localDetChartAt (T : FredholmOp E F) : LocalDetChart E F := (exists_localDetChart T).choose

theorem localDetChartAt_T (T : FredholmOp E F) : (localDetChartAt T).T = T.1 :=
  (exists_localDetChart T).choose_spec

theorem mem_baseSet_localDetChartAt (T : FredholmOp E F) : T ∈ (localDetChartAt T).baseSet := by
  change ‖T.1 - (localDetChartAt T).T‖ < (localDetChartAt T).ε
  rw [localDetChartAt_T, sub_self, norm_zero]
  exact (localDetChartAt T).ε_pos

omit [CompleteSpace E] [CompleteSpace F] in
/-- The linear algebra behind Lemma 6.5.9 (preprint 6.25): if `Λ₁ u = g₁ ω₃`, `Λ₂ (G₂ ω') = g₂ ω₃` and
`Λ₂ ∘ Λ₁₂ = Λ₁` at `u`, then `G₂⁻¹ (Λ₁₂ u) = (g₁ / g₂) ω'`. -/
theorem transition_smul_eq {V₂ W₁ W₂ W : Type*} [AddCommMonoid V₂] [Module ℝ V₂]
    [AddCommMonoid W₁] [Module ℝ W₁] [AddCommMonoid W₂] [Module ℝ W₂] [AddCommMonoid W]
    [Module ℝ W] {G₂ : V₂ ≃ₗ[ℝ] W₂} {Λ₁ : W₁ ≃ₗ[ℝ] W} {Λ₂ : W₂ ≃ₗ[ℝ] W} {Λ₁₂ : W₁ ≃ₗ[ℝ] W₂}
    {u : W₁} {ω' : V₂} {ω₃ : W} {g₁ g₂ : ℝ} (hg₂ : g₂ ≠ 0) (h₁ : Λ₁ u = g₁ • ω₃)
    (h₂ : Λ₂ (G₂ ω') = g₂ • ω₃) (h₁₂ : Λ₂ (Λ₁₂ u) = Λ₁ u) :
    G₂.symm (Λ₁₂ u) = (g₁ / g₂) • ω' := by
  have : Λ₁₂ u = (g₁ / g₂) • G₂ ω' :=
    Λ₂.injective (by rw [h₁₂, h₁, map_smul, h₂, smul_smul, div_mul_cancel₀ _ hg₂])
  rw [this, map_smul, LinearEquiv.symm_apply_apply]

/-- Lemma 6.5.9 (preprint 6.25) near one point `S₀`: with `Q ≤ P, P'` in `Π_{S₀}` (Lemma 6.10) and a chart with
projection `Q` centred at `S₀`, Corollary 6.4.12 (preprint 6.13) and Lemma 6.5.5 (preprint 6.21) write the transition function as a
quotient `g₁ / g₂` of continuous nowhere-zero functions on a neighbourhood of `S₀`. -/
theorem lemma_6_5_9_local (c c' : LocalDetChart E F) {S₀ : FredholmOp E F}
    (hS₀ : S₀ ∈ c.baseSet ∩ c'.baseSet) :
    ∃ N ∈ 𝓝 S₀, ∃ φ : FredholmOp E F → ℝ, ContinuousOn φ N ∧
      ∀ S ∈ N, φ S ≠ 0 ∧ c'.coord S (c.coordInv S 1) = φ S := by
  obtain ⟨Q, hQ, hQP, hQP'⟩ :=
    lemma_6_10_preprint (c.isGoodLeftProj_of_lt S₀.1 hS₀.1) (c'.isGoodLeftProj_of_lt S₀.1 hS₀.2)
  obtain ⟨c₃, hc₃T, rfl⟩ := exists_localDetChart_of_proj S₀.2 hQ
  obtain ⟨g₁, hg₁c, hg₁⟩ := lemma_6_5_5 c c₃ hQP
  obtain ⟨g₂, hg₂c, hg₂⟩ := lemma_6_5_5 c' c₃ hQP'
  have hS₀₃ : S₀ ∈ c₃.baseSet := by
    change ‖S₀.1 - c₃.T‖ < c₃.ε
    rw [hc₃T, sub_self, norm_zero]
    exact c₃.ε_pos
  have hN : c.baseSet ∩ c'.baseSet ∩ c₃.baseSet ∈ 𝓝 S₀ :=
    ((c.isOpen_baseSet.inter c'.isOpen_baseSet).inter c₃.isOpen_baseSet).mem_nhds ⟨hS₀, hS₀₃⟩
  refine ⟨_, hN, fun S => g₁ S.1 / g₂ S.1, ?_, fun S hS => ?_⟩
  · have hm₁ : MapsTo Subtype.val (c.baseSet ∩ c'.baseSet ∩ c₃.baseSet)
        {S | S.IsFredholm ∧ ‖S - c.T‖ < c.ε ∧ ‖S - c₃.T‖ < c₃.ε} :=
      fun S hS => ⟨S.2, hS.1.1, hS.2⟩
    have hm₂ : MapsTo Subtype.val (c.baseSet ∩ c'.baseSet ∩ c₃.baseSet)
        {S | S.IsFredholm ∧ ‖S - c'.T‖ < c'.ε ∧ ‖S - c₃.T‖ < c₃.ε} :=
      fun S hS => ⟨S.2, hS.1.2, hS.2⟩
    exact (hg₁c.comp continuous_subtype_val.continuousOn hm₁).div
      (hg₂c.comp continuous_subtype_val.continuousOn hm₂) fun S hS =>
        (hg₂ S.1 S.2 hS.1.2 hS.2).1
  obtain ⟨⟨hS1, hS2⟩, hS3⟩ := hS
  have hS1' : ‖S.1 - c.T‖ < c.ε := hS1
  have hS2' : ‖S.1 - c'.T‖ < c'.ε := hS2
  have hS3' : ‖S.1 - c₃.T‖ < c₃.ε := hS3
  obtain ⟨hg₁0, hg₁e⟩ := hg₁ S.1 S.2 hS1' hS3'
  obtain ⟨hg₂0, hg₂e⟩ := hg₂ S.1 S.2 hS2' hS3'
  refine ⟨div_ne_zero hg₁0 hg₂0, ?_⟩
  have h1 := finrank_fredholmDet ((c'.isGoodLeftProj_of_lt S.1 hS2').isFredholm_comp S.2)
  have hcor := corollary_6_4_12 S.2 (c₃.isGoodLeftProj_of_lt S.1 hS3')
    (c'.isGoodLeftProj_of_lt S.1 hS2') (c.isGoodLeftProj_of_lt S.1 hS1') hQP hQP'
    (c.frame S.1 hS1')
  have key := transition_smul_eq hg₂0 hg₁e hg₂e (linDetEquivOfEq_trans
    (congrArg (fun A : E →L[ℝ] F => (A : E →ₗ[ℝ] F)) (comp_comp_eq_comp_comp (T := S.1) hQP hQP'))
    _ _)
  rw [c'.coord_apply hS2', c.coordInv_apply hS1', one_smul, ← hcor, key, map_smul,
    dualVec_self h1 (c'.frame_ne_zero S.1 hS2'), smul_eq_mul, mul_one]

/-- **Lemma 6.5.9 (preprint 6.25)**: the transition map `γ_(T',P',ε') ∘ γ_(T,P,ε)⁻¹` between two charts is
`(S, t) ↦ (S, g(S) t)` with `g(S) = ω'(S)*(γ^{P'}_S (γ^P_S)⁻¹ ω(S))` continuous and nowhere zero on
the common ball; so it is a topological isomorphism of line bundles. -/
theorem lemma_6_5_9 (c c' : LocalDetChart E F) :
    ContinuousOn (fun S : FredholmOp E F => c'.coord S (c.coordInv S 1)) (c.baseSet ∩ c'.baseSet) ∧
      ∀ S ∈ c.baseSet ∩ c'.baseSet, c'.coord S (c.coordInv S 1) ≠ 0 := by
  refine ⟨fun S₀ hS₀ => ?_, fun S₀ hS₀ => ?_⟩
  · obtain ⟨N, hN, φ, hφ, hφe⟩ := lemma_6_5_9_local c c' hS₀
    exact ((hφ.continuousAt hN).congr
      (Filter.eventually_of_mem hN fun S hS => (hφe S hS).2.symm)).continuousWithinAt
  · obtain ⟨N, hN, φ, -, hφe⟩ := lemma_6_5_9_local c c' hS₀
    rw [(hφe S₀ (mem_of_mem_nhds hN)).2]
    exact (hφe S₀ (mem_of_mem_nhds hN)).1

variable (E F) in
/-- **`DET(E,F)` as a vector prebundle**: the atlas of all `γ_(T,P,ε)` (in frames), with continuous
coordinate changes by Lemma 6.5.9 (preprint 6.25). -/
def detPrebundle : VectorPrebundle ℝ ℝ (DetFiber (E := E) (F := F)) where
  pretrivializationAtlas := range fun c : LocalDetChart E F => c.pretriv
  pretrivialization_linear' := by
    rintro _ ⟨c, rfl⟩
    exact c.pretriv_isLinear
  pretrivializationAt T := (localDetChartAt T).pretriv
  mem_base_pretrivializationAt T := mem_baseSet_localDetChartAt T
  pretrivialization_mem_atlas T := ⟨_, rfl⟩
  exists_coordChange := by
    rintro _ ⟨c, rfl⟩ _ ⟨c', rfl⟩
    refine ⟨fun S => c'.coord S (c.coordInv S 1) • ContinuousLinearMap.id ℝ ℝ,
      (lemma_6_5_9 c c').1.smul continuousOn_const, fun S hS v => ?_⟩
    rw [c.pretriv.mk_symm hS.1 v]
    change c'.coord S (c.coordInv S 1) * v = c'.coord S (c.coordInv S v)
    have hv : c.coordInv S v = v • c.coordInv S 1 := by rw [← map_smul, smul_eq_mul, mul_one]
    rw [hv, map_smul, smul_eq_mul, mul_comm]
  totalSpaceMk_isInducing T := by
    have hT : T ∈ (localDetChartAt T).baseSet := mem_baseSet_localDetChartAt T
    have := IsModuleTopology.toContinuousAdd ℝ (DetFiber T)
    have hemb : IsEmbedding ((localDetChartAt T).coord T) :=
      Function.LeftInverse.isEmbedding (f := (localDetChartAt T).coordInv T)
        (fun h => (localDetChartAt T).coordInv_coord hT h)
        (IsModuleTopology.continuous_of_linearMap _) (IsModuleTopology.continuous_of_linearMap _)
    exact Topology.isInducing_const_prod.2 hemb.isInducing

/-- The topology `𝒯` of `DET(E,F)`. -/
instance : TopologicalSpace (TotalSpace ℝ (DetFiber (E := E) (F := F))) :=
  (detPrebundle E F).totalSpaceTopology

instance : FiberBundle ℝ (DetFiber (E := E) (F := F)) := (detPrebundle E F).toFiberBundle

instance : VectorBundle ℝ ℝ (DetFiber (E := E) (F := F)) := (detPrebundle E F).toVectorBundle

variable (E F) in
/-- **Definition 6.5.6 (preprint 6.22)**: `𝓑`, the subsets `B` of `DET(E,F)` over the ball of some chart whose image
under `γ_(T,P,ε)` (in frames) is open in `DET(T, P, ε) ≅ ball × ℝ`. -/
def detBasis : Set (Set (TotalSpace ℝ (DetFiber (E := E) (F := F)))) :=
  {B | ∃ c : LocalDetChart E F, B ⊆ c.pretriv.source ∧ IsOpen (c.pretriv '' B)}

/-- **Proposition 6.5.7 (preprint 6.23)**: `𝓑` is a basis of a topology on `DET(E,F)`, namely of the topology `𝒯` of
the prebundle. -/
theorem proposition_6_5_7 : TopologicalSpace.IsTopologicalBasis (detBasis E F) := by
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro B ⟨c, hBs, hBo⟩
    let e := (detPrebundle E F).trivializationOfMemPretrivializationAtlas ⟨c, rfl⟩
    have hB : B = e.source ∩ e ⁻¹' (c.pretriv '' B) := by
      ext x
      refine ⟨fun hx => ⟨hBs hx, x, hx, rfl⟩, ?_⟩
      rintro ⟨hx, y, hy, hyx⟩
      exact (e.toOpenPartialHomeomorph.injOn (hBs hy) hx hyx) ▸ hy
    rw [hB]
    exact e.continuousOn.isOpen_inter_preimage e.open_source hBo
  · intro x O hx hO
    let e := (detPrebundle E F).trivializationOfMemPretrivializationAtlas
      ⟨localDetChartAt x.proj, rfl⟩
    refine ⟨O ∩ (localDetChartAt x.proj).pretriv.source,
      ⟨localDetChartAt x.proj, inter_subset_right, ?_⟩,
      ⟨hx, mem_baseSet_localDetChartAt x.proj⟩, inter_subset_left⟩
    exact e.toOpenPartialHomeomorph.isOpen_image_of_subset_source (hO.inter e.open_source)
      inter_subset_right

/-- **Proposition 6.5.8 (preprint 6.24)**: `DET(E,F)` with the linear structure of its fibres and the topology `𝒯` is
a topological line bundle over the Fredholm operators, and every `γ_(T,P,ε)` (in frames) is a
trivialization of it. -/
theorem proposition_6_5_8 :
    VectorBundle ℝ ℝ (DetFiber (E := E) (F := F)) ∧
      ∀ c : LocalDetChart E F, ∃ e : Trivialization ℝ (π ℝ (DetFiber (E := E) (F := F))),
        MemTrivializationAtlas e ∧ e.baseSet = c.baseSet ∧ ∀ x, e x = c.pretriv x :=
  ⟨inferInstance, fun c => ⟨(detPrebundle E F).trivializationOfMemPretrivializationAtlas ⟨c, rfl⟩,
    ⟨⟨_, ⟨c, rfl⟩, rfl⟩⟩, rfl, fun _ => rfl⟩⟩

/-- The inclusion `C → F(E, F)` of a set of Fredholm operators. -/
def fredholmIncl {C : Set (E →L[ℝ] F)} (hC : ∀ T ∈ C, T.IsFredholm) : C(C, FredholmOp E F) :=
  ⟨fun T => ⟨T.1, hC T.1 T.2⟩, by fun_prop⟩

/-- `⋃_{L ∈ C} {L} × det(L)` for a set `C` of Fredholm operators: the restriction (pull-back) of
`DET(E,F)` to `C`. -/
abbrev DetOn (C : Set (E →L[ℝ] F)) (hC : ∀ T ∈ C, T.IsFredholm) : C → Type _ :=
  (fredholmIncl hC : C → FredholmOp E F) *ᵖ DetFiber

/-- **Proposition 6.6.1 (preprint 6.26)**: for a nonempty convex set `C` of Fredholm operators (such as `Lin(f, x)`),
`DET` over `C` is a topological line bundle (the restriction of `DET(E,F)`) and has exactly two
orientations. -/
theorem proposition_6_6_1 {C : Set (E →L[ℝ] F)} (hconv : Convex ℝ C) (hne : C.Nonempty)
    (hC : ∀ T ∈ C, T.IsFredholm) :
    VectorBundle ℝ ℝ (DetOn C hC) ∧
      ∃ o₁ o₂ : LineOrientation (DetOn C hC), o₁ ≠ o₂ ∧
        ∀ o : LineOrientation (DetOn C hC), o = o₁ ∨ o = o₂ := by
  have : Nonempty C := hne.to_subtype
  have : ContractibleSpace C := hconv.contractibleSpace hne
  have : LocallyPathConnectedSpace C := hconv.locallyPathConnectedSpace
  exact ⟨inferInstance, exists_two_lineOrientation⟩

end Polyfold
