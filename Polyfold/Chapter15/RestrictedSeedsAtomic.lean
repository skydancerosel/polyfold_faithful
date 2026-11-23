import Polyfold.Chapter15.RestrictedSeedsBump
import Polyfold.Chapter13.AtomicMultisection

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, §7.1,
**Theorem 7.1.13** (natural representation, p. 244), and Part III, §13.5 (atomic
sc⁺-multisections, pp. 630–634), on a saturated open subset.

# Natural representations inside a saturated open set

## The text, paraphrased

(Theorem 7.1.13) Every object `x` has arbitrarily small connected open neighbourhoods `U(x)`
with a natural action of `G_x`.  (§13.5) An atomic sc⁺-multisection is built from sc⁺-sections
supported in an invariant open `V(x)` with `cl V(x) ⊆ U(x)`.

## What is formalized (namespace `Polyfold.EpGroupoid`)

For a natural representation `R` on `U(x)` and a saturated open `G ∋ x`, let `U'` be the
connected component of `x` in `U(x) ∩ G`.

* **`exists_naturalRep_component`**: `R` restricts to a natural representation on `U'`, with the
  same `Φ` and `Γ`.
* `closure_inter_component_subset`: for `V` with `cl V ⊆ U(x)`, the closure of `V ∩ U'` meets `G`
  inside `U'` (so `cl_G(V ∩ U') ⊆ U'` in the subspace `G`).
* **`isScSmoothOn_indicator_component`**: a function which is sc-smooth on `G` and vanishes off a
  closed subset of `U(x)` stays sc-smooth on `G` after it is cut off to `U'`.

## Reading

`U(x) ∩ G` need not be connected, and a natural representation has a connected domain; the
component `U'` is open (M-polyfolds are locally connected), invariant under the action, and
closed in `U(x) ∩ G`.  This is the form in which the neighbourhoods of §13.5 pass to the
restriction `X|G`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Filter Topology

noncomputable section

namespace Polyfold

universe u

open MPolyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- `U(x) ∩ G` is invariant under the natural action, for a saturated `G`. -/
theorem NaturalRep.mapsTo_Φ_inter {x : Obj} (R : X.NaturalRep x) {G : Set Obj}
    (hGs : X.IsSaturated G) (g : X.Isotropy x) : MapsTo (R.Φ g) (R.U ∩ G) (R.U ∩ G) := by
  intro y hy
  refine ⟨R.mapsTo_Φ g hy.1, ?_⟩
  have h := X.isSaturated_iff.1 hGs (R.Γ g y) (by rw [R.src_Γ g y hy.1]; exact hy.2)
  rwa [R.tgt_Γ g y hy.1] at h

/-- **A natural representation on the component of `x` in `U(x) ∩ G`** for a saturated open
`G ∋ x` (Theorem 7.1.13, 2021 p. 244), with the same `Φ` and `Γ`. -/
theorem exists_naturalRep_component {x : Obj} (R : X.NaturalRep x) {G : Set Obj}
    (hG : IsOpen G) (hGs : X.IsSaturated G) (hx : x ∈ G) :
    ∃ R' : X.NaturalRep x, R'.U = connectedComponentIn (R.U ∩ G) x ∧ R'.Φ = R.Φ ∧
      R'.Γ = R.Γ := by
  have hWo : IsOpen (R.U ∩ G) := R.isOpen_U.inter hG
  have hxW : x ∈ R.U ∩ G := ⟨R.mem_U, hx⟩
  have hCW : connectedComponentIn (R.U ∩ G) x ⊆ R.U ∩ G := connectedComponentIn_subset _ x
  have hCinv : ∀ g, MapsTo (R.Φ g) (connectedComponentIn (R.U ∩ G) x)
      (connectedComponentIn (R.U ∩ G) x) := fun g y hy => by
    have hpre : IsPreconnected (R.Φ g '' connectedComponentIn (R.U ∩ G) x) :=
      isPreconnected_connectedComponentIn.image _
        ((R.isScDiffeoOn_Φ g).isScSmoothOn.continuousOn.mono (hCW.trans inter_subset_left))
    exact hpre.subset_connectedComponentIn ⟨x, mem_connectedComponentIn hxW, R.Φ_self g⟩
      ((R.mapsTo_Φ_inter X hGs g).mono_left hCW).image_subset ⟨y, hy, rfl⟩
  exact X.exists_naturalRep_restrict R (X.PObj.isOpen_connectedComponentIn hWo x)
    (isConnected_connectedComponentIn_iff.2 hxW) (mem_connectedComponentIn hxW)
    (hCW.trans inter_subset_left) hCinv

include X in
/-- **The component of `x` in an open `W` is closed in `W`**: a point of `W` in the closure of
the component lies in it. -/
theorem mem_component_of_mem_closure {W : Set Obj} (hW : IsOpen W) {x z : Obj}
    (hz : z ∈ W) (hcl : z ∈ closure (connectedComponentIn W x)) :
    z ∈ connectedComponentIn W x := by
  have := X.PObj.locallyConnectedSpace
  have hzo : IsOpen (connectedComponentIn W z) := hW.connectedComponentIn
  obtain ⟨y, hyz, hyx⟩ := mem_closure_iff.1 hcl _ hzo (mem_connectedComponentIn hz)
  rw [connectedComponentIn_eq hyx, ← connectedComponentIn_eq hyz]
  exact mem_connectedComponentIn hz

/-- **`cl(V ∩ U') ∩ G ⊆ U'`** for `cl V ⊆ U(x)` and `U'` the component of `x` in
`U(x) ∩ G`. -/
theorem closure_inter_component_subset {x : Obj} (R : X.NaturalRep x) {G : Set Obj}
    (hG : IsOpen G) {V : Set Obj} (hV : closure V ⊆ R.U) :
    closure (V ∩ connectedComponentIn (R.U ∩ G) x) ∩ G ⊆ connectedComponentIn (R.U ∩ G) x := by
  rintro z ⟨hz, hzG⟩
  have hzU : z ∈ R.U := hV (closure_mono inter_subset_left hz)
  exact X.mem_component_of_mem_closure (R.isOpen_U.inter hG) ⟨hzU, hzG⟩
    (closure_mono inter_subset_right hz)

/-- **A function sc-smooth on `G` and vanishing off a closed subset of `U(x)` stays sc-smooth on
`G` when it is cut off to the component `U'` of `x` in `U(x) ∩ G`.** -/
theorem isScSmoothOn_indicator_component {x : Obj} (R : X.NaturalRep x) {G : Set Obj}
    (hG : IsOpen G) {β : Obj → ℝ} (hβ : X.PObj.IsScSmoothOn realPolyfold β G) {C : Set Obj}
    (hC : IsClosed C) (hβC : support β ⊆ C) (hCU : C ⊆ R.U) :
    X.PObj.IsScSmoothOn realPolyfold ((connectedComponentIn (R.U ∩ G) x).indicator β) G := by
  have hWo : IsOpen (R.U ∩ G) := R.isOpen_U.inter hG
  have hUo : IsOpen (connectedComponentIn (R.U ∩ G) x) :=
    X.PObj.isOpen_connectedComponentIn hWo x
  have hUW : connectedComponentIn (R.U ∩ G) x ⊆ R.U ∩ G := connectedComponentIn_subset _ x
  refine LocalPart.isScSmoothOn_of_nhds hG fun z hz => ?_
  by_cases hzU' : z ∈ connectedComponentIn (R.U ∩ G) x
  · exact ⟨connectedComponentIn (R.U ∩ G) x, hzU',
      (hβ.mono hUo (hUW.trans inter_subset_right)).congr fun y hy =>
        (indicator_of_mem hy β).symm⟩
  by_cases hzU : z ∈ R.U
  · have hzo : IsOpen (connectedComponentIn (R.U ∩ G) z) :=
      X.PObj.isOpen_connectedComponentIn hWo z
    refine ⟨connectedComponentIn (R.U ∩ G) z, mem_connectedComponentIn ⟨hzU, hz⟩,
      (LocalPart.real_const hzo 0).congr fun y hy => ?_⟩
    refine (indicator_of_notMem ?_ β).symm
    intro hyx
    apply hzU'
    rw [connectedComponentIn_eq hyx, ← connectedComponentIn_eq hy]
    exact mem_connectedComponentIn ⟨hzU, hz⟩
  · refine ⟨Cᶜ, fun h => hzU (hCU h), (LocalPart.real_const hC.isOpen_compl 0).congr
      fun y hy => ?_⟩
    by_cases hyU : y ∈ connectedComponentIn (R.U ∩ G) x
    · rw [indicator_of_mem hyU]
      by_contra hne
      exact hy (hβC fun h0 => hne h0.symm)
    · rw [indicator_of_notMem hyU]

end EpGroupoid

end Polyfold
