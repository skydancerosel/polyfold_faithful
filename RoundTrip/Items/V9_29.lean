import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_29

set_option maxSynthPendingDepth 3

/-! Round trip for V9_29 (§9.3, p. 422 of the 2021 book; 2017 p. 310, and Remark 9.3.1: the
category `Gr̂(X)` of oriented tangent sums and the forgetful functor `Gr̂(X) → Gr(X)`).

The item lists the definitions `chartVec`, `OrTangent`, `chartFrames`, `IsChartOrientation`,
`IsOrientedAt`, `OrTangent.push`, `GrHat`, `grHatPush`, `GrHatObj`, `grHatProj`, `grForget`,
`grForgetFunctor` (vocabulary) and six theorems.  `A` is the conjunction of the theorems'
types, universes at `0`: `IsOrientedAt.isChartOrientation` (chart independence of an oriented
tangent set), `isOrientedAt_iff_forall`, `exists_two_orientations` (exactly two orientations of
a chart-linear tangent set), `IsOrientedAt.push_tangentMapOn`, `isOrientedAt_push_tangentMor`
(oriented tangent sets are carried by sc-diffeomorphisms and by the morphisms of `X`) and
`grForgetFunctor_comp_grProj` (`π ∘ f = π̂`).

* `B` (a): the project's `Gr̂(x)` is the set of formal sums with weights `≥ 0` of oriented
  tangent sets over `x` (`IsOrientedAt`): this is the definition of `GrHat` (`Iff.rfl`).
  `B` (b): there is a functor `F : Gr̂(X) → Gr(X)` acting as `(x, ∑ σ (L, o)) ↦ (x, ∑ σ L)` on
  objects and as the identity on underlying morphisms, with `F ⋙ π = π̂`.  `A_to_B` takes the
  project's `grForgetFunctor` (its object and morphism maps are those of `B` by `rfl`) and `A`'s
  `grForgetFunctor_comp_grProj`.
* `B_to_A`: `grForgetFunctor_comp_grProj` is obtained from `B` (b): a functor with `B`'s object
  and morphism maps is `grForgetFunctor` (`Functor.hext`; objects of `Gr(X)` are determined by
  `pt` and `sum`, morphisms by their underlying `φ`), so `grForgetFunctor ⋙ π = F ⋙ π = π̂`.
  The five orientation lemmas are general facts about the project's `IsOrientedAt` that `B`
  does not state; they are re-proved outright as copies of the project's proofs (banned lemmas
  replaced by local copies). -/

namespace RoundTrip.V9_29
open Polyfold Set Module Submodule CategoryTheory

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.MPolyfold.IsOrientedAt.isChartOrientation.{0}) ∧
  (type_of% @Polyfold.MPolyfold.isOrientedAt_iff_forall.{0}) ∧
  (type_of% @Polyfold.MPolyfold.exists_two_orientations.{0}) ∧
  (type_of% @Polyfold.MPolyfold.IsOrientedAt.push_tangentMapOn.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isOrientedAt_push_tangentMor.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.grForgetFunctor_comp_grProj.{0})

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.IsOrientedAt.isChartOrientation.{0},
    @Polyfold.MPolyfold.isOrientedAt_iff_forall.{0},
    @Polyfold.MPolyfold.exists_two_orientations.{0},
    @Polyfold.MPolyfold.IsOrientedAt.push_tangentMapOn.{0},
    @Polyfold.EpGroupoid.isOrientedAt_push_tangentMor.{0},
    @Polyfold.EpGroupoid.grForgetFunctor_comp_grProj.{0}⟩

/-! ### `A → B` -/

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X
  exact ⟨fun x w => Iff.rfl, X.grForgetFunctor, fun a => ⟨rfl, rfl⟩, fun a b f => rfl,
    hA.2.2.2.2.2 (X := X)⟩

/-! ### `B → A` -/

section Copies

open MPolyfold

variable {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {P : MPolyfold Z}

/-- Copy of `IsOrientedAt.isChartOrientation`. -/
theorem isChartOrientation' {y : Z} {g : OrTangent P} (h : P.IsOrientedAt y g)
    {ψ : MChart Z} (hψ : P.IsChart ψ) (hyψ : y ∈ ψ.source) : IsChartOrientation hψ g := by
  obtain ⟨hL, φ, hφ, hyφ, N, hN, hfin, hrank, ω, hO⟩ := h
  obtain ⟨Λ, hΛ⟩ := exists_clm_chartVec hφ hψ hyφ hyψ
  obtain ⟨Λ', hΛ'⟩ := exists_clm_chartVec hψ hφ hyψ hyφ
  set N' : Submodule ℝ (ψ.model.E 0) := N.map (Λ : φ.model.E 0 →ₗ[ℝ] ψ.model.E 0) with hN'def
  have hN' : (N' : Set (ψ.model.E 0)) = chartVec hψ '' g.carrier := by
    rw [hN'def, Submodule.map_coe, hN, image_image]
    exact (image_congr fun α hα => (hΛ α (hL α hα)).symm)
  have hmap' : ∀ w ∈ N', (Λ' : ψ.model.E 0 →ₗ[ℝ] φ.model.E 0) w ∈ N := by
    intro w hw
    rw [← SetLike.mem_coe, hN'] at hw
    obtain ⟨α, hα, rfl⟩ := hw
    rw [← SetLike.mem_coe, hN]
    exact ⟨α, hα, hΛ' α (hL α hα)⟩
  have hmap : ∀ v ∈ N, (Λ : φ.model.E 0 →ₗ[ℝ] ψ.model.E 0) v ∈ N' := fun v hv =>
    Submodule.mem_map_of_mem hv
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

/-- Copy of `isOrientedAt_iff_forall`. -/
theorem isOrientedAt_iff_forall' {y : Z} {g : OrTangent P} :
    P.IsOrientedAt y g ↔ (∀ α ∈ g.carrier, P.levelVal 1 (P.tangentProj α) = y) ∧
      ∀ (ψ : MChart Z) (hψ : P.IsChart ψ), y ∈ ψ.source → IsChartOrientation hψ g := by
  refine ⟨fun h => ⟨h.1, fun ψ hψ hyψ => isChartOrientation' h hψ hyψ⟩, fun h => ?_⟩
  obtain ⟨φ, hφ, hyφ⟩ := P.exists_isChart_mem_source y
  exact ⟨h.1, φ, hφ, hyφ, h.2 φ hφ hyφ⟩

/-- Copy of `exists_two_orientations`. -/
theorem exists_two_orientations' {φ : MChart Z} (hφ : P.IsChart φ) {y : Z} (hyφ : y ∈ φ.source)
    {L : Set P.TangentSpace}
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
      obtain ⟨N', hN', -, -, ω, hOω⟩ := isChartOrientation' hO hφ hyφ
      have hNN : N' = N := SetLike.coe_injective (hN'.trans hN.symm)
      subst hNN
      change O = chartFrames hφ L N' ω at hOω
      rcases b₀.orientation_eq_or_eq_neg ω with h | h
      · left; rw [hOω, h]
      · right; rw [hOω, h]
    · rintro (rfl | rfl)
      · exact ⟨hL, φ, hφ, hyφ, N, hN, inferInstance, hn, b₀.orientation, rfl⟩
      · exact ⟨hL, φ, hφ, hyφ, N, hN, inferInstance, hn, -b₀.orientation, rfl⟩

/-- Copy of `IsOrientedAt.push_tangentMapOn`. -/
theorem push_tangentMapOn' {f f' : Z → Z} {U U' : Set Z}
    (hf : P.IsScDiffeoOn P f f' U U') {y : Z} (hyU : y ∈ U) {g : OrTangent P}
    (h : P.IsOrientedAt y g) :
    P.IsOrientedAt (f y) (g.push (tangentMapOn hf.isScSmoothOn)) := by
  have hL := h.1
  obtain ⟨ψ, hψ, hyψ⟩ := P.exists_isChart_mem_source (f y)
  have hχ := transportChart_isChart hf hψ
  have hyχ : y ∈ (transportChart hf ψ).source := ⟨hyU, hyψ⟩
  obtain ⟨N, hN, hfin, hrank, ω, hO⟩ := isChartOrientation' h hχ hyχ
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

end Copies

section CopiesEp

variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

/-- Copy of `isOrientedAt_push_tangentMor`. -/
theorem isOrientedAt_push_tangentMor' {φ : Mor} {g : X.PObj.OrTangent}
    (h : X.PObj.IsOrientedAt (X.src φ) g) :
    X.PObj.IsOrientedAt (X.tgt φ) (g.push (X.tangentMor φ)) := by
  have hφ1 : φ ∈ X.PMor.levelSet 1 := (X.mem_levelSet_src_iff φ 1).1 h.levelSet
  have heq : g.push (X.tangentMor φ) =
      g.push (MPolyfold.tangentMapOn (X.isScDiffeoOn_hat φ).isScSmoothOn) :=
    MPolyfold.OrTangent.push_congr (fun α hα => X.tangentMor_eq_tangentMapOn_hat hφ1 (h.1 α hα))
      fun v hv i => h.mem_carrier hv i
  rw [heq, ← X.hat_src φ]
  exact push_tangentMapOn' (X.isScDiffeoOn_hat φ) (X.src_mem_sheetAt φ) h

/-- Objects of `Gr(X)` are determined by the base point and the formal sum. -/
theorem grObj_ext {c d : X.GrObj} (h1 : c.pt = d.pt) (h2 : c.sum = d.sum) : c = d := by
  obtain ⟨_, _, _, _⟩ := c
  obtain ⟨_, _, _, _⟩ := d
  cases h1; cases h2; rfl

/-- Morphisms of `Gr(X)` between equal objects are determined by the underlying `φ`. -/
theorem grHom_heq {c c' d d' : X.GrObj} (hc : c = c') (hd : d = d') (u : c ⟶ d)
    (v : c' ⟶ d') (h : u.1 = v.1) : HEq u v := by
  subst hc; subst hd
  exact heq_of_eq (Subtype.ext h)

end CopiesEp

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Z _ _ _ P y g h ψ hψ hyψ
    exact isChartOrientation' h hψ hyψ
  · intro Z _ _ _ P y g
    exact isOrientedAt_iff_forall'
  · intro Z _ _ _ P φ hφ y hyφ L hL N hN _ n hn
    exact exists_two_orientations' hφ hyφ hL hN hn
  · intro Z _ _ _ P f f' U U' hf y hyU g h
    exact push_tangentMapOn' hf hyU h
  · intro Obj Mor _ _ _ _ _ _ X φ g h
    exact isOrientedAt_push_tangentMor' h
  · -- `grForgetFunctor_comp_grProj`, from `B` (b)
    intro Obj Mor _ _ _ _ _ _ X
    obtain ⟨-, F, hobj, hmap, hcomp⟩ := hB Obj Mor X
    have hob : ∀ a, F.obj a = X.grForgetFunctor.obj a := fun a =>
      grObj_ext (hobj a).1 (hobj a).2
    have hF : F = X.grForgetFunctor :=
      CategoryTheory.Functor.hext hob fun a b f => grHom_heq (hob a) (hob b) _ _ (hmap a b f)
    rw [← hF]
    exact hcomp

#rt_check RoundTrip.V9_29.A_to_B [Polyfold.MPolyfold.IsOrientedAt.isChartOrientation,
  Polyfold.MPolyfold.isOrientedAt_iff_forall, Polyfold.MPolyfold.exists_two_orientations,
  Polyfold.MPolyfold.IsOrientedAt.push_tangentMapOn,
  Polyfold.EpGroupoid.isOrientedAt_push_tangentMor,
  Polyfold.EpGroupoid.grForgetFunctor_comp_grProj]
#rt_check RoundTrip.V9_29.B_to_A [Polyfold.MPolyfold.IsOrientedAt.isChartOrientation,
  Polyfold.MPolyfold.isOrientedAt_iff_forall, Polyfold.MPolyfold.exists_two_orientations,
  Polyfold.MPolyfold.IsOrientedAt.push_tangentMapOn,
  Polyfold.EpGroupoid.isOrientedAt_push_tangentMor,
  Polyfold.EpGroupoid.grForgetFunctor_comp_grProj]
#rt_overlap RoundTrip.V9_29.B_to_A [Polyfold.MPolyfold.IsOrientedAt.isChartOrientation,
  Polyfold.MPolyfold.isOrientedAt_iff_forall, Polyfold.MPolyfold.exists_two_orientations,
  Polyfold.MPolyfold.IsOrientedAt.push_tangentMapOn,
  Polyfold.EpGroupoid.isOrientedAt_push_tangentMor,
  Polyfold.EpGroupoid.grForgetFunctor_comp_grProj]

end RoundTrip.V9_29
