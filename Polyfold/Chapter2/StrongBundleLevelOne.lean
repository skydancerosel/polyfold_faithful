import Polyfold.Chapter2.Metrizable

/-!
# Sc-smooth maps on level one

The restriction of an sc-smooth map to level one, the level charts on level one and the level sets
of the shift. The shifted bundle is in `Chapter5/StrongBundleShift.lean`.
-/

open Set Filter Topology Function
noncomputable section
namespace Polyfold
universe u v

/-- `z ∈ E_1` lies in `(E¹)_m` iff `ι z ∈ E_{m+1}`. -/
lemma ScBanach.mem_range_shift_toBase_iff (E : ScBanach) {m : ℕ} (z : E 1) :
    z ∈ range (E.shift.toBase m) ↔ E.toBase 1 z ∈ range (E.toBase (m + 1)) := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w, E.shift_toBase m w⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, E.toBase_injective 1 (by rw [← E.shift_toBase, hw])⟩

namespace MPolyfold
variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

/-- **The levels of the M-polyfold `X¹` are those of `X` shifted by one**: `(X¹)_m = X_{m+1}`
(the paragraph after Definition 2.3.8 (preprint 2.14); part of gap G.6). -/
theorem mem_shift_levelSet_iff {m : ℕ} (x : PX.Level 1) :
    x ∈ PX.shift.levelSet m ↔ PX.levelVal 1 x ∈ PX.levelSet (m + 1) := by
  obtain ⟨φ, hφ, hx⟩ := PX.exists_isChart_mem_source (PX.levelVal 1 x)
  rw [PX.shift.mem_levelSet_iff (PX.shift_isChart hφ x) (show x ∈ (levelChart hφ x).source from hx),
    PX.mem_levelSet_iff hφ hx, levelChart_apply]
  change levelLift φ 1 (PX.levelVal 1 x) ∈ range (φ.model.E.shift.toBase m) ↔ _
  rw [ScBanach.mem_range_shift_toBase_iff, PX.toBase_levelLift hφ hx (levelVal_mem x)]

section LevelMap
variable {Z : Type v} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {Q : MPolyfold Z}
  {f : X → Z} {f₁ : PX.Level 1 → Q.Level 1}

/-- The level chart maps `V ∩ X₁` onto `φ(V)¹ = φ(V) ∩ E₁`. -/
lemma levelChart_image_preimage {φ : MChart X} (hφ : PX.IsChart φ) (x₀ : PX.Level 1) {V : Set X}
    (hVφ : V ⊆ φ.source) :
    levelChart hφ x₀ '' {x | PX.levelVal 1 x ∈ V} = φ.model.E.lvlSet (φ '' V) 1 := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    change φ.model.E.toBase 1 (levelLift φ 1 (PX.levelVal 1 x)) ∈ φ '' V
    rw [PX.toBase_levelLift hφ (hVφ hx) (levelVal_mem x)]
    exact ⟨_, hx, rfl⟩
  · intro hz
    obtain ⟨v, hv, hvz⟩ := hz
    have hzO : φ.model.E.toBase 1 z ∈ φ.model.O := by rw [← hvz]; exact φ.mapsTo_model v (hVφ hv)
    refine ⟨(levelChart hφ x₀).symm z, ?_, (levelChart hφ x₀).apply_symm_apply hzO⟩
    change PX.levelVal 1 ((levelChart hφ x₀).symm z) ∈ V
    rw [levelChart_symm_apply hφ x₀ hzO, ← hvz, φ.symm_apply_apply (hVφ hv)]
    exact hv

/-- The local representative of `f₁` in level charts is the level-`1` map of the local
representative of `f`. -/
lemma levelChart_apply_levelOne (hf₁ : ∀ x, Q.levelVal 1 (f₁ x) = f (PX.levelVal 1 x))
    {φ : MChart X} {ψ : MChart Z} (hφ : PX.IsChart φ) (hψ : Q.IsChart ψ) (x₀ : PX.Level 1)
    (z₀ : Q.Level 1) {x : PX.Level 1} (hx : PX.levelVal 1 x ∈ φ.source)
    (hfx : f (PX.levelVal 1 x) ∈ ψ.source) :
    levelChart hψ z₀ (f₁ x) = levelMap (ψ ∘ f ∘ φ.symm) 1 (levelChart hφ x₀ x) := by
  symm
  apply levelMap_eq_of_toBase_eq
  have hfx' : Q.levelVal 1 (f₁ x) ∈ ψ.source := by rw [hf₁]; exact hfx
  rw [levelChart_apply, levelChart_apply, Q.toBase_levelLift hψ hfx' (levelVal_mem _),
    PX.toBase_levelLift hφ hx (levelVal_mem _), hf₁]
  simp only [Function.comp_apply, φ.symm_apply_apply hx]

/-- **Raising the index of an sc-smooth map** (the text's "a sc-smooth section `f` ... defines,
by raising the index, a sc-smooth section `f^i`", before Corollary 5.2.5 (preprint 5.8); Proposition 1.2.2 (preprint 1.17) in
charts): an sc-smooth map `f : X → Z` between M-polyfolds induces an sc-smooth map
`f₁ : X¹ → Z¹` between the level M-polyfolds (any `f₁` with `f₁(x) = f(x)` as points of `Z`).  In
the level charts the local representative of `f₁` is the level-`1` map of that of `f`. -/
theorem IsScSmoothMap.levelOne (hf : PX.IsScSmoothMap Q f)
    (hf₁ : ∀ x, Q.levelVal 1 (f₁ x) = f (PX.levelVal 1 x)) :
    PX.shift.IsScSmoothMap Q.shift f₁ := by
  have hfc : Continuous f := continuousOn_univ.1 hf.continuousOn
  -- the local data at `x`: charts `φ ∋ x`, `ψ ∋ f(x)`, `V = dom φ ∩ f⁻¹(dom ψ)`
  have data : ∀ x : PX.Level 1, ∃ (φ : MChart X) (ψ : MChart Z) (hφ : PX.IsChart φ)
      (hψ : Q.IsChart ψ), PX.levelVal 1 x ∈ φ.source ∧ f (PX.levelVal 1 x) ∈ ψ.source := by
    intro x
    obtain ⟨φ, hφ, hx⟩ := PX.exists_isChart_mem_source (PX.levelVal 1 x)
    obtain ⟨ψ, hψ, hfx⟩ := Q.exists_isChart_mem_source (f (PX.levelVal 1 x))
    exact ⟨φ, ψ, hφ, hψ, hx, hfx⟩
  have local_ : ∀ {φ : MChart X} {ψ : MChart Z} (hφ : PX.IsChart φ) (hψ : Q.IsChart ψ)
      (x₀ : PX.Level 1) (z₀ : Q.Level 1),
      IsOpen {x : PX.Level 1 | PX.levelVal 1 x ∈ φ.source ∩ f ⁻¹' ψ.source} ∧
      ContinuousOn f₁ {x : PX.Level 1 | PX.levelVal 1 x ∈ φ.source ∩ f ⁻¹' ψ.source} ∧
      IsScSmoothRetractMap (levelChart hφ x₀).model.E (levelChart hφ x₀).model.C
        (levelChart hφ x₀ '' {x : PX.Level 1 | PX.levelVal 1 x ∈ φ.source ∩ f ⁻¹' ψ.source})
        (levelChart hψ z₀).model.E (levelChart hψ z₀).model.C (levelChart hψ z₀).model.O
        (levelChart hψ z₀ ∘ f₁ ∘ (levelChart hφ x₀).symm) := by
    intro φ ψ hφ hψ x₀ z₀
    set V := φ.source ∩ f ⁻¹' ψ.source with hVdef
    have hV : IsOpen V := φ.isOpen_source.inter (ψ.isOpen_source.preimage hfc)
    have hVφ : V ⊆ φ.source := inter_subset_left
    have hsm := hf.smooth φ ψ hφ hψ V hV (fun x hx => ⟨mem_univ _, hx.1⟩) fun x hx => hx.2
    have hO := φ.isScRetract_image hVφ hV
    have hrep : ∀ x : PX.Level 1, PX.levelVal 1 x ∈ V →
        levelChart hψ z₀ (f₁ x) = levelMap (ψ ∘ f ∘ φ.symm) 1 (levelChart hφ x₀ x) :=
      fun x hx => levelChart_apply_levelOne hf₁ hφ hψ x₀ z₀ hx.1 hx.2
    have hmaps : MapsTo (levelChart hφ x₀) {x : PX.Level 1 | PX.levelVal 1 x ∈ V}
        (φ.model.E.lvlSet (φ '' V) 1) := fun x hx => by
      rw [← levelChart_image_preimage hφ x₀ hVφ]; exact ⟨x, hx, rfl⟩
    refine ⟨(continuous_levelVal 1).isOpen_preimage _ hV, ?_, ?_⟩
    · -- `f₁ = (ψ¹)⁻¹ ∘ (ψ ∘ f ∘ φ⁻¹)₁ ∘ φ¹` on `V¹`
      have h1 : ContinuousOn (fun x => (levelChart hψ z₀).symm
          (levelMap (ψ ∘ f ∘ φ.symm) 1 (levelChart hφ x₀ x)))
          {x : PX.Level 1 | PX.levelVal 1 x ∈ V} :=
        (levelChart hψ z₀).continuousOn_invFun.comp
          ((hsm.continuousOn_levelMap hO 1).comp
            ((levelChart hφ x₀).continuousOn_toFun.mono fun x hx => hx.1) hmaps)
          fun x hx => hsm.mapsTo_levelMap hO 1 (hmaps hx)
      refine h1.congr fun x hx => ?_
      have hfx : f₁ x ∈ (levelChart hψ z₀).source := by
        change Q.levelVal 1 (f₁ x) ∈ ψ.source
        rw [hf₁]; exact hx.2
      simp only
      rw [← hrep x hx, (levelChart hψ z₀).symm_apply_apply hfx]
    · rw [levelChart_image_preimage hφ x₀ hVφ]
      refine (hsm.shift hO).congr fun z hz => ?_
      have hzO : φ.model.E.toBase 1 z ∈ φ.model.O := φ.image_subset_model hVφ hz
      have hx : PX.levelVal 1 ((levelChart hφ x₀).symm z) ∈ V := by
        rw [levelChart_symm_apply hφ x₀ hzO]
        obtain ⟨v, hv, hvz⟩ := hz
        rw [← hvz, φ.symm_apply_apply (hVφ hv)]
        exact hv
      have e := hrep _ hx
      rw [(levelChart hφ x₀).apply_symm_apply (z := z) hzO] at e
      exact e.symm
  refine IsScSmoothOn.of_exists_charts isOpen_univ ?_ fun x _ => ?_
  · refine continuousOn_univ.2 (continuous_iff_continuousAt.2 fun x => ?_)
    obtain ⟨φ, ψ, hφ, hψ, hx, hfx⟩ := data x
    obtain ⟨hV1, hcont, -⟩ := local_ hφ hψ x (f₁ x)
    exact hcont.continuousAt (hV1.mem_nhds ⟨hx, hfx⟩)
  · obtain ⟨φ, ψ, hφ, hψ, hx, hfx⟩ := data x
    obtain ⟨hV1, -, hsm⟩ := local_ hφ hψ x (f₁ x)
    refine ⟨levelChart hφ x, levelChart hψ (f₁ x), _, PX.shift_isChart hφ x,
      Q.shift_isChart hψ (f₁ x), hV1, ⟨hx, hfx⟩, fun x' hx' => ⟨mem_univ _, hx'.1⟩,
      fun x' hx' => ?_, hsm⟩
    change Q.levelVal 1 (f₁ x') ∈ ψ.source
    rw [hf₁]; exact hx'.2

end LevelMap
end MPolyfold
end Polyfold
end
