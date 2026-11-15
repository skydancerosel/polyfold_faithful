import Polyfold.Chapter12.LocalOrientationTransport

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §6.6,
Theorem 6.6.11 (p. 272), Theorem 6.6.13 and its proof (pp. 273–274), Theorem 6.6.17
(pp. 274–275), with Definition 6.2.1 (p. 239) for the linearizations.

# The orientation space of the local orientation sets

## The text, paraphrased

Theorem 6.6.11: for an sc-Fredholm section `f` of a strong bundle over a tame M-polyfold every
smooth point has an open neighbourhood with the local propagation property.  Theorem 6.6.17:
the set `O_f` of pairs `(x, o)`, `x` smooth and `o` an orientation of `DET(f, x)`, has exactly
one Hausdorff topology such that (1) the projection to `X_∞` is a local homeomorphism, (2) near
every smooth point there are precisely two continuous sections, (3) continuous sections along
sc-smooth paths are given by the local propagation.  The linearizations entering `DET(f, x)`
are those of `f − s` for locally defined sc⁺-sections `s` (Definition 6.2.1).

## What is formalized

Both theorems for the local orientation sets `OrxLoc hf x hs`, under the hypotheses "`X` is
tame" and "`f` has tame germ data" only.  The propagation along a path is made in the
restriction of the bundle to an open subset `W` of a chart domain containing the path, where
the sc⁺-sections of Proposition 6.6.3 are written in the chart, and it does not depend on the
subset (`LocalOrientationTransport.lean`).

* `orLocalTransportLoc_good_iff`: a good set is an open set `U` inside a domain `W` (an open
  subset of the base domain of a chart) which, as a subset of `W`, has the local propagation
  property for the restriction `f|W` in a chart of `P|W`.
* `theorem_6_6_11_loc`: **Theorem 6.6.11**, every smooth point has a good open neighbourhood.
* `OrSpaceLoc`, `orTopologyLoc`, `theorem_6_6_17_loc`: **Theorem 6.6.17**, the orientation
  space of the sets `Or_x^f` has exactly one topology with the properties of the theorem.
* `Dom.pushLoc`, `Dom.isContOn_iff`, `Dom.isContOn_carrier_iff`: **continuous orientations are
  those of the restrictions**: over an open subset `U` of a domain `W` a family `o_y ∈ Or_y^f`
  is carried along by the transport iff, read in `W`, it is a continuous orientation of `f|W`
  over `U`.
* `isContOn_univ_iff_forall_dom`: a family is carried along by the transport along all
  sc-smooth paths iff for every domain `W` it is a continuous orientation of `f|W` over `W`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-! ### Theorem 6.6.11 -/

/-- **The good sets**: an open set `U` inside a domain `W` which, as a subset of `W`, has the
local propagation property for `f|W` in a chart of `P|W`. -/
theorem orLocalTransportLoc_good_iff (hX : PX.IsTame) (hf : B.IsScFredholmSectionTame f)
    (U : Set X) :
    (orLocalTransportLoc hX hf).Good U ↔ IsOpen U ∧ ∃ D : B.Dom, U ⊆ D.carrier ∧
      IsPropagationNbhd (D.sec f hf.isScSmooth.1) (D.isFredholm hf).toIsScFredholmSection
        (Subtype.val ⁻¹' U : Set D.carrier) :=
  Iff.rfl

/-- **2021 Theorem 6.6.11**, p. 272, for the local orientation sets, for a tame M-polyfold and a
section with tame germ data: every smooth point `x` has an open neighbourhood `U` which is a
good set, that is `U` lies in an open subset `W` of the base domain of a chart and has the
local propagation property for the restriction of `f` to `W`
(`orLocalTransportLoc_good_iff`). -/
theorem theorem_6_6_11_loc (hX : PX.IsTame) (hf : B.IsScFredholmSectionTame f) {x : X}
    (hx : x ∈ PX.smoothSet) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ (orLocalTransportLoc hX hf).Good U :=
  let ⟨U, hU, hxU⟩ := (orLocalTransportLoc hX hf).exists_good x hx
  ⟨U, hU.1, hxU, hU⟩

/-! ### Theorem 6.6.17 -/

/-- **The orientation space** of the local orientation sets: the pairs `(x, o)` of a smooth
point `x` and `o ∈ Or_x^f`. -/
abbrev OrSpaceLoc (hX : PX.IsTame) (hf : B.IsScFredholmSectionTame f) : Type _ :=
  (orLocalTransportLoc hX hf).Total

/-- **The topology of the orientation space** of the local orientation sets. -/
abbrev orTopologyLoc (hX : PX.IsTame) (hf : B.IsScFredholmSectionTame f) :
    TopologicalSpace (OrSpaceLoc hX hf) :=
  (orLocalTransportLoc hX hf).topology

/-- **2021 Theorem 6.6.17**, pp. 274–275, for the local orientation sets, for a tame M-polyfold
and a section with tame germ data: the orientation space has exactly one topology which is
Hausdorff and has the properties (1) the projection to `X_∞` is a local homeomorphism, (2) near
every smooth point there are precisely two continuous sections, (3) continuous sections along
sc-smooth paths are locally given by the propagation in good sets. -/
theorem theorem_6_6_17_loc (hX : PX.IsTame) (hf : B.IsScFredholmSectionTame f) :
    ∃! t : TopologicalSpace (OrSpaceLoc hX hf),
      (orLocalTransportLoc hX hf).IsOrientationTopology t :=
  (orLocalTransportLoc hX hf).existsUnique_isOrientationTopology fun _ hy =>
    exists_two_orxLoc hf hy

/-- The topology `orTopologyLoc` has the properties of Theorem 6.6.17. -/
theorem isOrientationTopology_orTopologyLoc (hX : PX.IsTame)
    (hf : B.IsScFredholmSectionTame f) :
    (orLocalTransportLoc hX hf).IsOrientationTopology (orTopologyLoc hX hf) := by
  obtain ⟨t, ht, huniq⟩ := theorem_6_6_17_loc hX hf
  have e : orTopologyLoc hX hf = t :=
    LocalTransport.eq_topology_of ht.isLocalHomeomorph ht.propagation ▸ rfl
  exact e ▸ ht

/-! ### Continuous orientations and the restrictions to domains -/

namespace StrongBundle.Dom

variable (D : B.Dom)

/-- **A family `o_y ∈ Or_y^f` read in a domain `W`**: the family `w ↦ o_w ∈ Or_w^{f|W}` for
the smooth points `w` of `W`. -/
def pushLoc (hf : B.IsScFredholmSectionTame f)
    (o : ∀ y (hy : y ∈ PX.smoothSet), OrxLoc hf y hy) (w : D.carrier)
    (hw : w ∈ (PX.restrictOpen D.isOpen).smoothSet) :
    Orx (D.sec f hf.isScSmooth.1) (D.isFredholm hf).toIsScFredholmSection w hw :=
  D.toLoc hf w.1 w.2 ((MPolyfold.mem_smoothSet_restrictOpen_iff D.isOpen w).1 hw)
    (o w.1 ((MPolyfold.mem_smoothSet_restrictOpen_iff D.isOpen w).1 hw))

theorem pushLoc_mk (hf : B.IsScFredholmSectionTame f)
    (o : ∀ y (hy : y ∈ PX.smoothSet), OrxLoc hf y hy) {x : X} (hx : x ∈ D.carrier)
    (hs : x ∈ PX.smoothSet) :
    D.pushLoc hf o ⟨x, hx⟩ (mem_smoothSet hx hs) = D.toLoc hf x hx hs (o x hs) :=
  rfl

/-- **Continuous orientations over an open subset of a domain**: for an open `U` inside a
domain `W`, a family `o_y ∈ Or_y^f` is carried along by the transport along the sc-smooth paths
in `U` iff, read in `W`, it is a continuous orientation of `f|W` over `U`. -/
theorem isContOn_iff (hX : PX.IsTame) (hf : B.IsScFredholmSectionTame f) {U : Set X}
    (hU : IsOpen U) (hUD : U ⊆ D.carrier) (o : ∀ y (hy : y ∈ PX.smoothSet), OrxLoc hf y hy) :
    (orLocalTransportLoc hX hf).IsContOn U o ↔
      IsContOrOn (D.transport hX hf) (Subtype.val ⁻¹' U) (D.pushLoc hf o) := by
  constructor
  · intro h
    refine ⟨hU.preimage continuous_subtype_val, fun γ hγ hγU w₀ w₁ h₀ h₁ hw₀ hw₁ => ?_⟩
    obtain ⟨x₀, hx₀⟩ := w₀
    obtain ⟨x₁, hx₁⟩ := w₁
    have hs₀ := (MPolyfold.mem_smoothSet_restrictOpen_iff D.isOpen ⟨x₀, hx₀⟩).1 hw₀
    have hs₁ := (MPolyfold.mem_smoothSet_restrictOpen_iff D.isOpen ⟨x₁, hx₁⟩).1 hw₁
    have hγX := D.isScSmoothMap_val_comp hγ
    have hγXD : ∀ q, (γ q).1 ∈ D.carrier := fun q => (γ q).2
    have h₀X : (γ (pt1 0)).1 = x₀ := congrArg Subtype.val h₀
    have h₁X : (γ (pt1 1)).1 = x₁ := congrArg Subtype.val h₁
    have e := h.2 (fun q => (γ q).1) hγX (fun s hs => hγU s hs) h₀X h₁X hs₀ hs₁
    have e' := orLocalTransportLoc_transport_eq hX hf D hγX hγXD h₀X h₁X hs₀ hs₁
    have e'' := D.toLoc_transportLoc hX hf hγX hγXD h₀X h₁X hs₀ hs₁ (o x₀ hs₀)
    exact e''.symm.trans (congrArg (D.toLoc hf x₁ hx₁ hs₁)
      ((DFunLike.congr_fun e' (o x₀ hs₀)).symm.trans e))
  · intro h
    refine ⟨hU, fun γ hγ hγU x₀ x₁ h₀ h₁ hs₀ hs₁ => ?_⟩
    have hγ' := isScSmoothMap_smoothTransPath_or hγ
    have hγ'U : ∀ q, smoothTransPath_or γ q ∈ U := smoothTransPath_or_mem hγU
    have hγ'D : ∀ q, smoothTransPath_or γ q ∈ D.carrier := fun q => hUD (hγ'U q)
    have h₀' : smoothTransPath_or γ (pt1 0) = x₀ :=
      (congrArg (fun t => γ (pt1 t)) Real.smoothTransition.zero).trans h₀
    have h₁' : smoothTransPath_or γ (pt1 1) = x₁ :=
      (congrArg (fun t => γ (pt1 t)) Real.smoothTransition.one).trans h₁
    have hx₀ : x₀ ∈ D.carrier := h₀' ▸ hγ'D _
    have hx₁ : x₁ ∈ D.carrier := h₁' ▸ hγ'D _
    have er := (orLocalTransportLoc hX hf).transport_reparam hγ
      Real.smoothTransition.contDiff Real.smoothTransition.zero Real.smoothTransition.one h₀ h₁
      hs₀ hs₁
    have e' := orLocalTransportLoc_transport_eq hX hf D hγ' hγ'D h₀' h₁' hs₀ hs₁
    have hc := h.2 (D.liftPath (smoothTransPath_or γ) hγ'D) (D.isScSmoothMap_liftPath hγ' hγ'D)
      (fun s _ => hγ'U _) (x₀ := ⟨x₀, hx₀⟩) (x₁ := ⟨x₁, hx₁⟩) (Subtype.ext h₀')
      (Subtype.ext h₁') (mem_smoothSet hx₀ hs₀) (mem_smoothSet hx₁ hs₁)
    exact (DFunLike.congr_fun (er.symm.trans e') (o x₀ hs₀)).trans
      ((congrArg (D.toLoc hf x₁ hx₁ hs₁).symm hc).trans
        ((D.toLoc hf x₁ hx₁ hs₁).symm_apply_apply _))

/-- **Continuous orientations over a domain**: a family `o_y ∈ Or_y^f` is carried along by the
transport along the sc-smooth paths in a domain `W` iff, read in `W`, it is a continuous
orientation of `f|W` over all of `W`. -/
theorem isContOn_carrier_iff (hX : PX.IsTame) (hf : B.IsScFredholmSectionTame f)
    (o : ∀ y (hy : y ∈ PX.smoothSet), OrxLoc hf y hy) :
    (orLocalTransportLoc hX hf).IsContOn D.carrier o ↔
      IsContOrOn (D.transport hX hf) univ (D.pushLoc hf o) := by
  have e : (Subtype.val ⁻¹' D.carrier : Set D.carrier) = univ := Subtype.coe_preimage_self _
  have h := D.isContOn_iff hX hf D.isOpen subset_rfl o
  rw [e] at h
  exact h

end StrongBundle.Dom

/-- **A family of orientations is continuous iff it is so in every domain**: a family
`o_y ∈ Or_y^f` is carried along by the transport along all sc-smooth paths in `X` iff for every
domain `W` the family read in `W` is a continuous orientation of `f|W` over `W`. -/
theorem isContOn_univ_iff_forall_dom (hX : PX.IsTame) (hf : B.IsScFredholmSectionTame f)
    (o : ∀ y (hy : y ∈ PX.smoothSet), OrxLoc hf y hy) :
    (orLocalTransportLoc hX hf).IsContOn univ o ↔
      ∀ D : B.Dom, IsContOrOn (D.transport hX hf) univ (D.pushLoc hf o) :=
  ⟨fun h D => (D.isContOn_carrier_iff hX hf o).1 (h.mono D.isOpen (subset_univ _)),
    fun h => LocalTransport.isContOn_of_local isOpen_univ fun x _ _ =>
      ⟨(B.domAt x).carrier, B.mem_domAt x, ((B.domAt x).isContOn_carrier_iff hX hf o).2 (h _)⟩⟩

end Polyfold
