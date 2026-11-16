import Polyfold.Chapter9.BoundaryOperation
import Polyfold.Chapter9.SubmanifoldTangentImage

/-!
# Boundary operators under tangent maps

The boundary carrier, the boundary operations and the inward, outward and reduced tangent predicates
under tangent maps `tangentMapOn` of sc-diffeomorphisms. The orientation equivalences that use them
are in `Chapter11/BoundaryOrientationEquiv.lean`.
-/

set_option maxSynthPendingDepth 3
open Set Function Module Submodule
noncomputable section
namespace Polyfold
universe u v
namespace MPolyfold
variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}

theorem OrTangent.map_mk (f : P.TangentSpace → Q.TangentSpace) (d : ℕ) (L : Set P.TangentSpace)
    (O : Set (Fin d → P.TangentSpace)) :
    (⟨d, L, O⟩ : OrTangent P).map f = ⟨d, f '' L, (fun v => f ∘ v) '' O⟩ := rfl

theorem boundaryOp_zero (L : Set P.TangentSpace) (O : Set (Fin 0 → P.TangentSpace)) :
    P.boundaryOp ⟨0, L, O⟩ = ⟨0, P.boundaryCarrier L, ∅⟩ := rfl

theorem boundaryOp_succ {m : ℕ} (L : Set P.TangentSpace) (O : Set (Fin (m + 1) → P.TangentSpace)) :
    P.boundaryOp ⟨m + 1, L, O⟩ = ⟨m, P.boundaryCarrier L,
      {a | (∀ i, a i ∈ P.boundaryCarrier L) ∧
        ∀ e ∈ L, P.IsOutwardTangent e → (Fin.cons e a : Fin (m + 1) → P.TangentSpace) ∈ O}⟩ :=
  rfl

/-- `T^R` read through a fibre map that preserves it. -/
theorem boundaryCarrier_image {f : P.TangentSpace → Q.TangentSpace} {L : Set P.TangentSpace}
    (hred : ∀ α ∈ L, Q.IsReducedTangent (f α) ↔ P.IsReducedTangent α) :
    Q.boundaryCarrier (f '' L) = f '' P.boundaryCarrier L := by
  ext β
  constructor
  · rintro ⟨⟨α, hα, rfl⟩, hr⟩
    exact ⟨α, ⟨hα, (hred α hα).1 hr⟩, rfl⟩
  · rintro ⟨α, ⟨hα, hr⟩, rfl⟩
    exact ⟨mem_image_of_mem f hα, (hred α hα).2 hr⟩

/-- **A fibre map moves the boundary operation** if it is injective on `L` and preserves
`T^R` and the outward vectors on `L`: `∂(f_*(L, o)) = f_*(∂(L, o))`. -/
theorem boundaryOp_map {f : P.TangentSpace → Q.TangentSpace} {g : OrTangent P}
    (hfr : ∀ v ∈ g.frames, ∀ i, v i ∈ g.carrier) (hinj : InjOn f g.carrier)
    (hred : ∀ α ∈ g.carrier, Q.IsReducedTangent (f α) ↔ P.IsReducedTangent α)
    (hout : ∀ α ∈ g.carrier, Q.IsOutwardTangent (f α) ↔ P.IsOutwardTangent α) :
    Q.boundaryOp (g.map f) = (P.boundaryOp g).map f := by
  obtain ⟨_ | m, L, O⟩ := g
  · rw [OrTangent.map_mk, boundaryOp_zero, boundaryOp_zero, OrTangent.map_mk, image_empty,
      boundaryCarrier_image hred]
  · rw [OrTangent.map_mk, boundaryOp_succ, boundaryOp_succ, OrTangent.map_mk,
      boundaryCarrier_image hred]
    congr 1
    ext a'
    constructor
    · rintro ⟨ha', hcons⟩
      choose a ha hfa using ha'
      have hfa' : f ∘ a = a' := funext hfa
      refine ⟨a, ⟨ha, fun e he heo => ?_⟩, hfa'⟩
      obtain ⟨b, hb, hbe⟩ := hcons (f e) (mem_image_of_mem f he) ((hout e he).2 heo)
      have hbe' : f ∘ b = f ∘ (Fin.cons e a : Fin (m + 1) → P.TangentSpace) := by
        change f ∘ b = _ at hbe
        rw [hbe, Fin.comp_cons, hfa']
      have hmem : ∀ i, (Fin.cons e a : Fin (m + 1) → P.TangentSpace) i ∈ L := fun i => by
        induction i using Fin.cases with
        | zero => simpa using he
        | succ j => simpa using (ha j).1
      have hbeq : b = Fin.cons e a := funext fun i =>
        hinj (hfr b hb i) (hmem i) (congrFun hbe' i)
      rw [← hbeq]
      exact hb
    · rintro ⟨a, ⟨ha, hcons⟩, rfl⟩
      refine ⟨fun i => mem_image_of_mem f (ha i), ?_⟩
      rintro _ ⟨e, he, rfl⟩ heo
      exact ⟨Fin.cons e a, hcons e he ((hout e he).1 heo), Fin.comp_cons f e a⟩

section Diffeo
variable {f : X → Y} {g : Y → X} {U : Set X} {U' : Set Y}

/-- **The presented chart `ψ ∘ f` at `x`** of a presented chart `ψ` at `f(x)`, `f` an
sc-diffeomorphism (the proof of Proposition 2.24): same model, same presentation. -/
def PresentedChart.transport (hf : P.IsScDiffeoOn Q f g U U') {x : X} (hx : x ∈ U)
    (c : Q.PresentedChart (f x)) : P.PresentedChart x where
  φ := transportChart hf c.φ
  isChart := transportChart_isChart hf c.isChart
  mem_source := ⟨hx, c.mem_source⟩
  n := c.n
  W := c.W
  T := c.T
  hT := c.hT

theorem PresentedChart.vec_transport (hf : P.IsScDiffeoOn Q f g U U') {x : X} (hx : x ∈ U)
    (c : Q.PresentedChart (f x)) {α : P.TangentSpace}
    (hα : P.levelVal 1 (P.tangentProj α) = x) :
    (c.transport hf hx).vec α = c.vec (tangentMapOn hf.isScSmoothOn α) :=
  (chartVec_tangentMapOn_of_isScDiffeoOn hf c.isChart
    (by rw [hα]; exact ⟨hx, c.mem_source⟩)).symm

theorem levelVal_tangentProj_tangentMapOn_eq (hf : P.IsScDiffeoOn Q f g U U') {x : X}
    (hx : x ∈ U) {α : P.TangentSpace} (hα : P.levelVal 1 (P.tangentProj α) = x) :
    Q.levelVal 1 (Q.tangentProj (tangentMapOn hf.isScSmoothOn α)) = f x := by
  rw [levelVal_tangentProj_tangentMapOn hf.isScSmoothOn
    (show α ∈ P.tangentPreimage U from by change _ ∈ U; rw [hα]; exact hx), hα]

/-- **`Tf` preserves `T^R`**: `Tf(α) ∈ T^R_{f(x)}Y ⟺ α ∈ T^R_xX`. -/
theorem isReducedVec_tangentMapOn_iff (hf : P.IsScDiffeoOn Q f g U U') {x : X} (hx : x ∈ U)
    {α : P.TangentSpace} (hα : P.levelVal 1 (P.tangentProj α) = x) :
    Q.IsReducedVec (f x) (tangentMapOn hf.isScSmoothOn α) ↔ P.IsReducedVec x α := by
  obtain ⟨c⟩ := Q.nonempty_presentedChart (f x)
  rw [isReducedVec_iff c (levelVal_tangentProj_tangentMapOn_eq hf hx hα),
    isReducedVec_iff (c.transport hf hx) hα, c.vec_transport hf hx hα]
  exact Iff.rfl

/-- **`Tf` preserves the partial cone**: `Tf(α) ∈ C_{f(x)}Y ⟺ α ∈ C_xX`. -/
theorem isInwardVec_tangentMapOn_iff (hf : P.IsScDiffeoOn Q f g U U') {x : X} (hx : x ∈ U)
    {α : P.TangentSpace} (hα : P.levelVal 1 (P.tangentProj α) = x) :
    Q.IsInwardVec (f x) (tangentMapOn hf.isScSmoothOn α) ↔ P.IsInwardVec x α := by
  obtain ⟨c⟩ := Q.nonempty_presentedChart (f x)
  rw [isInwardVec_iff c (levelVal_tangentProj_tangentMapOn_eq hf hx hα),
    isInwardVec_iff (c.transport hf hx) hα, c.vec_transport hf hx hα]
  exact Iff.rfl

theorem isReducedTangent_tangentMapOn_iff (hf : P.IsScDiffeoOn Q f g U U') {α : P.TangentSpace}
    (hα : α ∈ P.tangentPreimage U) :
    Q.IsReducedTangent (tangentMapOn hf.isScSmoothOn α) ↔ P.IsReducedTangent α := by
  unfold IsReducedTangent
  rw [levelVal_tangentProj_tangentMapOn hf.isScSmoothOn hα]
  exact isReducedVec_tangentMapOn_iff hf hα rfl

theorem isOutwardTangent_tangentMapOn_iff (hf : P.IsScDiffeoOn Q f g U U') {α : P.TangentSpace}
    (hα : α ∈ P.tangentPreimage U) :
    Q.IsOutwardTangent (tangentMapOn hf.isScSmoothOn α) ↔ P.IsOutwardTangent α := by
  unfold IsOutwardTangent
  rw [levelVal_tangentProj_tangentMapOn hf.isScSmoothOn hα]
  exact not_congr (isInwardVec_tangentMapOn_iff hf hα rfl)

/-- **`Tf` preserves the reduced codimension** (the text's "`d_M(x)` is being preserved"). -/
theorem hasReducedCodim_map_tangentMapOn_iff (hf : P.IsScDiffeoOn Q f g U U') {x : X}
    (hx : x ∈ U) {ℓ : ℕ} {o : OrTangent P}
    (ho : ∀ α ∈ o.carrier, P.levelVal 1 (P.tangentProj α) = x) :
    Q.HasReducedCodim (f x) ℓ (o.map (tangentMapOn hf.isScSmoothOn)) ↔
      P.HasReducedCodim x ℓ o := by
  obtain ⟨c⟩ := Q.nonempty_presentedChart (f x)
  have ho' : ∀ β ∈ (o.map (tangentMapOn hf.isScSmoothOn)).carrier,
      Q.levelVal 1 (Q.tangentProj β) = f x := by
    rintro _ ⟨α, hα, rfl⟩
    exact levelVal_tangentProj_tangentMapOn_eq hf hx (ho α hα)
  rw [hasReducedCodim_iff c ho', hasReducedCodim_iff (c.transport hf hx) ho,
    OrTangent.map_carrier, image_image]
  have himg : (fun α => c.vec (tangentMapOn hf.isScSmoothOn α)) '' o.carrier =
      (c.transport hf hx).vec '' o.carrier :=
    image_congr fun α hα => (c.vec_transport hf hx (ho α hα)).symm
  rw [himg]
  exact Iff.rfl

/-- **`Tf` moves the boundary operation of Definition 9.3.8**:
`∂(Tf_*(L, o)) = Tf_*(∂(L, o))` for every oriented tangent set over `x ∈ U`. -/
theorem boundaryOp_map_tangentMapOn (hf : P.IsScDiffeoOn Q f g U U') {x : X} (hx : x ∈ U)
    {o : OrTangent P} (hO : P.IsOrientedAt x o) :
    Q.boundaryOp (o.map (tangentMapOn hf.isScSmoothOn)) =
      (P.boundaryOp o).map (tangentMapOn hf.isScSmoothOn) := by
  have hU : ∀ α ∈ o.carrier, α ∈ P.tangentPreimage U := fun α hα => by
    change _ ∈ U; rw [hO.1 α hα]; exact hx
  exact boundaryOp_map (fun v hv i => hO.mem_carrier hv i) (hf.injOn_tangent.mono hU)
    (fun α hα => isReducedTangent_tangentMapOn_iff hf (hU α hα))
    (fun α hα => isOutwardTangent_tangentMapOn_iff hf (hU α hα))

end Diffeo
end MPolyfold
end Polyfold
end
