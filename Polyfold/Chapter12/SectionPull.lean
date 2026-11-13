import Polyfold.Chapter12.ChartPullTwoBundles
import Polyfold.Chapter6.PushTransfer
import Polyfold.Chapter6.OrientableNbhd
import Polyfold.Chapter3.IndexAlongPathsLocalBump

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
p. 594: a step of the proof of the last sentence of **Theorem 12.5.3** (2017: Theorem 12.11).

# Families of sc⁺-sections carried along a local strong bundle isomorphism

Part I's propagation of orientations along a path (`IsPush`) is made from sc⁺-sections of the
pull-back bundle over `ℝ × X`.  To compare the propagation along a path `γ` in `X` with the
propagation along its image `ϕ ∘ γ` under a local strong bundle isomorphism `L : Y|U → Y'|U'`, an
sc⁺-section `S'` of the pull-back of `Y'` is carried to one of the pull-back of `Y`: in the
transported chart `Ψ' ∘ Φ` (`LocalIso.transportChart`) its principal part is that of `S'`, cut
off by an sc-smooth `β` supported in the domain of the chart.

* `LocalIso.exists_pullSection`: for an sc⁺-section `S'` of `pr₂*Y'` and a cut-off `β` on `X`
  with `supp β` in the domain of the transported chart `cT`, there is an sc⁺-section `S` of
  `pr₂*Y` with `cT(S(q, x)) = β(x) · c(S'(q, ϕ(x)))` in the fibre components.  It is the cut-off
  section (`cutoffSection`) of the product chart of `cT` whose local representative is that of
  `S'` in the product chart of `c`; the two product charts have the same model and the same
  local strong bundle retract (`Kg_ofProd_transportChart`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

open StrongRetr

universe u v u' v'

section SectionPull

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {X' : Type u'} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type v'} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle PX' P'}

namespace StrongBundle.LocalIso

variable {U : Set X} {U' : Set X'} (L : LocalIso B B' U U')

variable [ParacompactSpace ((Fin 1 → ℝ) × X)] [ParacompactSpace ((Fin 1 → ℝ) × X')]

/-- The retract of the product chart of the transported chart is that of the product chart of
the original chart. -/
theorem ofProd_transportChart_O (c : StrongBundleChart PX' P') (hsub : c.φ.source ⊆ U')
    (r₀ : Fin 1 → ℝ) :
    (PullbackChartData.ofProd (L.transportChart c hsub) r₀).ψ.model.O =
      (PullbackChartData.ofProd c r₀).ψ.model.O := by
  change (rnChart 1 r₀).model.O ×ˢ (L.transportChart c hsub).φ.model.O =
    (rnChart 1 r₀).model.O ×ˢ c.φ.model.O
  exact congrArg ((rnChart 1 r₀).model.O ×ˢ ·) (L.transportChart_model_O c hsub)

/-- The local strong bundle retracts `K_g` of the two product charts coincide: the maps
`g = φ ∘ pr₂ ∘ ψ⁻¹` agree on the retract (`ϕ ∘ ϕ⁻¹ = id` on `U'`). -/
theorem Kg_ofProd_transportChart (c : StrongBundleChart PX' P') (hsub : c.φ.source ⊆ U')
    (r₀ : Fin 1 → ℝ) :
    (PullbackChartData.ofProd (L.transportChart c hsub) r₀).Kg =
      (PullbackChartData.ofProd c r₀).Kg := by
  set dT := PullbackChartData.ofProd (L.transportChart c hsub) r₀
  set d := PullbackChartData.ofProd c r₀
  have hg : ∀ w ∈ d.RZ.retract, dT.g w = d.g w := by
    intro w hw
    rw [d.RZ_retract] at hw
    have hw2 : w.2 ∈ c.φ.model.O := hw.2
    have hs : c.φ.symm w.2 ∈ c.φ.source := c.φ.symm_mapsTo hw2
    change c.φ (L.ϕ (L.g (c.φ.symm w.2))) = c.φ (c.φ.symm w.2)
    rw [L.base.right_inv _ (hsub hs)]
  ext p
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [← hg p.1 h1]; exact h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [hg p.1 h1]; exact h2⟩

variable [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))]
  [ParacompactSpace (pullbackSpace P' (Prod.snd : (Fin 1 → ℝ) × X' → X'))]

/-- **An sc⁺-section of `pr₂*Y'` carried to `pr₂*Y`** through a local strong bundle isomorphism
`L : Y|U → Y'|U'`, cut off by `β`: for a chart `c` of `Y'` with domain in `U'` and an sc-smooth
`β : X → ℝ` supported in the domain of the transported chart `cT = Ψ' ∘ Φ`, there is an
sc⁺-section `S` of `pr₂*Y` with `cT(S(q, x)) = β(x) · c(S'(q, ϕ(x)))` (fibre components) on the
domain of `cT`. -/
theorem exists_pullSection {c : StrongBundleChart PX' P'} (hc : B'.IsChart c)
    (hsub : c.φ.source ⊆ U') {β : X → ℝ} (hβ : PX.IsScSmoothMap realPolyfold β)
    (hβs : tsupport β ⊆ (L.transportChart c hsub).φ.source)
    {S' : (Fin 1 → ℝ) × X' → pullbackSpace P' (Prod.snd : (Fin 1 → ℝ) × X' → X')}
    (hS' : (B'.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX')).IsScPlusSection S') :
    ∃ S : (Fin 1 → ℝ) × X → pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X),
      (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsScPlusSection S ∧
      ∀ q x, x ∈ (L.transportChart c hsub).φ.source →
        ((L.transportChart c hsub) (pullbackSlice S q x)).2 =
          β x • (c (pullbackSlice S' q (L.ϕ x))).2 := by
  set cT := L.transportChart c hsub with hcTdef
  have hcT : B.IsChart cT := L.isChart_transportChart c hsub hc
  set d := PullbackChartData.ofProd c (0 : Fin 1 → ℝ) with hd
  set dT := PullbackChartData.ofProd cT (0 : Fin 1 → ℝ) with hdT
  set q₀ : pullbackSpace P' (Prod.snd : (Fin 1 → ℝ) × X' → X') := S' (0, c.φ.symm 0)
  set qT₀ : pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X) :=
    ⟨((0, cT.φ.symm 0), fiberZero P (cT.φ.symm 0)), proj_fiberZero P _⟩
  set pc := d.toChart q₀ with hpcdef
  set pcT := dT.toChart qT₀ with hpcTdef
  have hpc : (B'.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX')).IsChart pc :=
    d.isChart_toChart B' _ hc q₀
  have hpcT : (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)).IsChart pcT :=
    dT.isChart_toChart B _ hcT qT₀
  set τ := pc.principalLift S' with hτdef
  have hτ := hS'.isScSmoothRetractMap_one hpc
  have hO : pcT.φ.model.O = pc.φ.model.O := L.ofProd_transportChart_O c hsub 0
  have hK : pcT.K = pc.K := by
    change pullbackRetraction dT.c.R dT.RZ dT.g '' (dT.RZ.U ×ˢ univ) =
      pullbackRetraction d.c.R d.RZ d.g '' (d.RZ.U ×ˢ univ)
    rw [dT.image_eq_Kg, d.image_eq_Kg]
    exact L.Kg_ofProd_transportChart c hsub 0
  have hτ' : IsScSmoothRetractMap pcT.φ.model.E pcT.φ.model.C pcT.φ.model.O
      (pcT.φ.model.E.prod pcT.F.shift) (pcT.φ.model.C ×ˢ univ) (strongShiftOne pcT.K)
      (fun z => (z, τ z)) := by
    rw [hO, hK]; exact hτ
  set β' : (Fin 1 → ℝ) × X → ℝ := β ∘ Prod.snd with hβ'def
  have hβ' : ((rnPolyfold 1).prod PX).IsScSmoothMap realPolyfold β' :=
    hβ.comp (MPolyfold.isScSmoothMap_snd (rnPolyfold 1) PX)
  have hβ's : tsupport β' ⊆ pcT.φ.source := by
    refine (closure_minimal (s := support β') (t := Prod.snd ⁻¹' tsupport β)
      (fun p hp => subset_tsupport β hp) ((isClosed_tsupport β).preimage continuous_snd)).trans ?_
    intro p hp
    exact ⟨mem_univ _, hβs hp⟩
  refine ⟨StrongBundle.cutoffSection pcT β' τ,
    StrongBundle.isScPlusSection_cutoffSection_of_isChart hpcT hβ' hβ's hτ', fun q x hx => ?_⟩
  have hqx : ((q, x) : (Fin 1 → ℝ) × X) ∈ pcT.φ.source := ⟨mem_univ _, hx⟩
  have happ := StrongBundle.apply_cutoffSection (β := β') hτ'.mapsTo hqx
  have h2 := congrArg Prod.snd happ
  change (cT (StrongBundle.cutoffSection pcT β' τ (q, x)).1.2).2 = _ at h2
  change (cT (StrongBundle.cutoffSection pcT β' τ (q, x)).1.2).2 = _
  rw [h2]
  dsimp only
  erw [map_smul]
  have hw : ((q - 0, cT.φ x) : (Fin 1 → ℝ) × c.φ.model.E 0) ∈ pc.φ.model.O := by
    refine ⟨mem_univ _, ?_⟩
    exact c.φ.mapsTo_model _ hx.2
  have hpr := hS'.toBase_principalLift hpc hw
  change β x • c.F.toBase 1
    (τ ((q - 0, cT.φ x) : (Fin 1 → ℝ) × c.φ.model.E 0)) = _
  erw [hpr]
  have hϕx : L.ϕ x ∈ c.φ.source := hx.2
  change β x • (c (S' (pc.φ.symm
    ((q - 0, c.φ (L.ϕ x)) : (Fin 1 → ℝ) × c.φ.model.E 0))).1.2).2 = _
  have hsymm : pc.φ.symm ((q - 0, c.φ (L.ϕ x)) : (Fin 1 → ℝ) × c.φ.model.E 0) =
      (q, L.ϕ x) := by
    change ((q - 0) + 0, c.φ.symm (c.φ (L.ϕ x))) = _
    rw [sub_zero, add_zero, c.φ.symm_apply_apply hϕx]
  rw [hsymm]
  rfl

end StrongBundle.LocalIso

end SectionPull

end Polyfold
