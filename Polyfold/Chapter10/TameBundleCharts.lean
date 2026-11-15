import Polyfold.Chapter10.FredholmEquivalence
import Polyfold.Chapter10.StrongBundleWeakFibredProductPullback
import Polyfold.Chapter3.ParamPerturbation
import Polyfold.Chapter2.TameFaces

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §2.5–§2.6 and
§3.6 (pp. 59–68, 134–136): **tame strong bundle charts over a tame M-polyfold**.

# Tame strong bundle charts

## The statement

A strong bundle chart is tame when its base retraction is tame (`StrongBundle.IsTameChart`).
Every strong bundle `P : Y → X` over a tame M-polyfold has a tame strong bundle chart around every
point of `X` (`StrongBundle.exists_isTameChart`), so a strong bundle over a tame M-polyfold is a
tame strong bundle in the sense of `StrongBundle.IsTameBundle` (Chapter 3).  For a strong bundle
over an ep-groupoid: `SEP.exists_isTameChart` (tame `X`).

## Proof

* Pull-backs (`exists_isTameChart_pullback`): for `π : Z → X` sc-smooth and `Z` tame, the
  pulled-back chart `Φ_π(z, y) = (ψ(z), pr_F Φ(y))` of Proposition 2.6.8 has as base retraction the
  retraction `r_Z` chosen for the base chart `ψ` (`R_g(w, h) = (r_Z(w), Γ(g(r_Z(w)), h))`); in a
  tame chart of `Z`, `r_Z` can be taken tame.
* The identity (`exists_isTameChart`): `P' : id*Y → Y` is a strong bundle isomorphism covering
  the identity (`isStrongBundleIsoOn_pullbackProj'`), and a tame chart of `id*Y` transported along
  its inverse is a tame chart of `Y` with the same model (`LocalIso.isTameChart_transportChart`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

section TameCharts

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {Z : Type*} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {PZ : MPolyfold Z}

/-- **A tame chart inside a given open set, with a tame retraction onto its model**: in a tame
M-polyfold every `z ∈ V` (`V` open) lies in a chart `ψ` of the structure with `dom ψ ⊆ V` and a
tame sc-smooth retraction `r` with `r(U) = O_ψ` (the restriction of a tame chart,
`ScRetraction.IsTameWith.restrict`). -/
theorem MPolyfold.IsTame.exists_tameRetraction_subset (hZ : PZ.IsTame) {V : Set Z}
    (hV : IsOpen V) {z : Z} (hz : z ∈ V) :
    ∃ ψ : MChart Z, PZ.IsChart ψ ∧ z ∈ ψ.source ∧ ψ.source ⊆ V ∧
      ∃ R : ScRetraction ψ.model.E ψ.model.C, R.retract = ψ.model.O ∧ R.IsTame := by
  obtain ⟨φ, hφ, hzφ, R, hRO, hRt⟩ := MPolyfold.IsTame.exists_chart PZ hZ z
  have hs : φ.source ∩ V ⊆ φ.source := inter_subset_left
  have hso : IsOpen (φ.source ∩ V) := φ.isOpen_source.inter hV
  obtain ⟨W₀, hW₀, hWs⟩ := φ.exists_isOpen_image_eq hs hso
  refine ⟨φ.restrict hs hso, hφ.restrict PZ hs hso, ⟨hzφ, hz⟩, inter_subset_right,
    R.restrict hW₀, ?_, fun n W T hT => (hRt n W T hT).restrict hW₀⟩
  have h : (R.restrict hW₀).retract = φ '' (φ.source ∩ V) := by
    rw [R.restrict_retract, hRO, hWs]
  exact h

namespace StrongBundle

variable (B : StrongBundle PX P)

/-- **Pull-backs along sc-smooth maps from tame M-polyfolds have tame strong bundle charts**:
for `π : Z → X` sc-smooth and `Z` tame, every `z ∈ Z` lies in a chart of `π*Y`
(Proposition 2.6.8) whose base retraction is tame. -/
theorem exists_isTameChart_pullback {π : Z → X} [ParacompactSpace (pullbackSpace P π)]
    (hπ : PZ.IsScSmoothMap PX π) (hZ : PZ.IsTame) (z : Z) :
    ∃ c : StrongBundleChart PZ (pullbackProj P π), (B.pullback hπ).IsTameChart c ∧
      z ∈ c.φ.source := by
  obtain ⟨y, hy⟩ := B.surjective (π z)
  obtain ⟨c, hc, hyc⟩ := B.atlas.cover y
  have hπz : π z ∈ c.φ.source := by
    rw [c.source_eq, mem_preimage, hy] at hyc
    exact hyc
  have hπc : Continuous π := continuousOn_univ.1 hπ.continuousOn
  obtain ⟨ψ, hψ, hzψ, hψV, RZ, hRZ, hRt⟩ :=
    MPolyfold.IsTame.exists_tameRetraction_subset hZ (c.φ.isOpen_source.preimage hπc) hπz
  have hψf : MapsTo π ψ.source c.φ.source := fun _ hz => hψV hz
  have hsm := hπ.smooth ψ c.φ hψ c.isChart ψ.source ψ.isOpen_source
    (fun _ hz => ⟨mem_univ _, hz⟩) hψf
  rw [ψ.image_source] at hsm
  let d : PullbackChartData PX P PZ π := ⟨c, ψ, hψ, hψf, RZ, hRZ, hsm⟩
  let q₀ : pullbackSpace P π := ⟨(z, y), hy⟩
  exact ⟨d.toChart q₀, ⟨d.isChart_toChart B hπ (B.isChart_of_mem hc) q₀, hRt⟩, hzψ⟩

/-- **Every strong bundle over a tame M-polyfold has a tame strong bundle chart around every
point** (Definitions 2.5.7, 3.6.3): transport a tame chart of `id*Y`
(`exists_isTameChart_pullback`) along the strong bundle isomorphism `Y ≅ id*Y`. -/
theorem exists_isTameChart (hX : PX.IsTame) (x : X) :
    ∃ c : StrongBundleChart PX P, B.IsTameChart c ∧ x ∈ c.φ.source := by
  have := B.paracompactSpace_pullback PX id
  have hid : PX.IsScSmoothMap PX id := MPolyfold.isScSmoothMap_id
  obtain ⟨c', hc', hx⟩ := B.exists_isTameChart_pullback hid hX x
  have hi := B.isStrongBundleIsoOn_pullbackProj' hid (MPolyfold.isScDiffeoOn_id isOpen_univ) x
  set L := hi.toLocalIso.symm
  refine ⟨L.transportChart c' (subset_univ _), L.isTameChart_transportChart c' (subset_univ _) hc',
    mem_univ _, ?_⟩
  have e : L.ϕ x = x := L.base.left_inv x (mem_univ x)
  change L.ϕ x ∈ c'.φ.source
  rw [e]
  exact hx

end StrongBundle

end TameCharts

/-- **A strong bundle over a tame ep-groupoid has tame strong bundle charts around every
object** (`StrongBundle.exists_isTameChart` for the object M-polyfold). -/
theorem SEP.exists_isTameChart (A : SEP.{u}) (hX : A.X.IsTame) (x : A.Obj) :
    ∃ c : StrongBundleChart A.X.PObj A.P, A.B.IsTameChart c ∧ x ∈ c.φ.source :=
  A.B.exists_isTameChart hX x

end Polyfold
